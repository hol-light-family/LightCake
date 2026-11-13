(* ========================================================================= *)
(* pattern_comp: port of HOL4 compiler/backend/pattern_matching/             *)
(* pattern_compScript.sml (CakeML v3479).                                    *)
(* A simple pattern compiler that moves constant patterns upwards, checks    *)
(* for exhaustiveness, and then converts the pattern rows into an            *)
(* if-then-else decision tree.  The exhaustiveness check itself lives in     *)
(* pattern_exh.                                                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 match is pattern_semantics_match, walk is pattern_comp_walk, comp  *)
(*   is pattern_comp_comp (names.tsv).                                       *)
(* - HOL4 states pmatchResult_case_NONE first with K NONE NONE in the last   *)
(*   arm and then exports its K_THM-rewritten form under the same name; the  *)
(*   port proves the rewritten form directly.                                *)
(* - EVERY_take_until_Any has the hypothesis ~(rows = []): HOL Light's TL [] *)
(*   is unspecified (HOL4's is []).                                          *)
(* - match_move_const_up is proved with helper lemmas (prefix IL1AUX_) that  *)
(*   HOL4's proof does inline: rows that fail can be dropped, and the two    *)
(*   cases of the value (a constant Term t [] or not).                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/pattern_matching/pattern_exh.ml";;
needs "semantics/ast.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* moving constant patterns up *)

let is_const_row_def = cake_def
  `(is_const_row (pattern_semantics_Cons _ pats, (x:A)) <=> NULL pats) /\
   (is_const_row (_:pattern_semantics_pat # A) <=> F)`;;

let is_Any_def = cake_def
  `(is_Any pattern_semantics_Any <=> T) /\
   (is_Any (pattern_semantics_Or p1 p2) <=> is_Any p1 \/ is_Any p2) /\
   (is_Any _ <=> F)`;;

let is_Any_ind = cake_ind "is_Any";;

let is_Or_row_def = cake_def
  `(is_Or_row (pattern_semantics_Or p1 p2, (_:A)) <=> T) /\
   (is_Or_row (_:pattern_semantics_pat # A) <=> F)`;;

let take_until_Any_def = cake_def
  `(take_until_Any [] = []:(pattern_semantics_pat # A) list) /\
   (take_until_Any (CONS (p,x) xs) =
      if is_Any p then [(p,x)] else CONS (p,x) (take_until_Any xs))`;;

(* long pattern rows (5 or more, or with an Or pattern) are not changed *)

let move_const_up_def = cake_def
  `move_const_up (rows:(pattern_semantics_pat # A) list) =
     let new_rows = take_until_Any rows in
       if 5 <= LENGTH new_rows \/ EX is_Or_row new_rows then
         new_rows
       else
         APPEND (FILTER is_const_row new_rows)
                (FILTER (\x. ~is_const_row x) new_rows)`;;

let is_Any_pmatch = prove
 (`!p. is_Any p ==> ~(pattern_semantics_pmatch refs p v = PMatchFailure)`,
  MATCH_MP_TAC is_Any_ind THEN REWRITE_TAC[is_Any_def] THEN
  REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  CASES_ON `pattern_semantics_pmatch refs p1 v` THEN
  CASES_ON `pattern_semantics_pmatch refs p2 v` THEN
  CASE_REWRITE_TAC[distinctness "pmatchResult"] THEN
  ASM_MESON_TAC[distinctness "pmatchResult"]);;

let match_take_until_Any = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     pattern_semantics_match refs (take_until_Any rows) v =
     pattern_semantics_match refs rows v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[take_until_Any_def] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REWRITE_TAC[take_until_Any_def] THEN REPEAT DISCH_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_ASSUM (ASSUME_TAC o MATCH_MP is_Any_pmatch); ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[pattern_semantics_match_def]) THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[distinctness "option"; distinctness "pmatchResult"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let match_append = prove
 (CASE_TERM `!xs ys refs v.
     pattern_semantics_match refs (APPEND xs ys) v =
     match pattern_semantics_match refs xs v with
       NONE -> NONE
     | SOME (MatchSuccess e) ->
         if ~(pattern_semantics_match refs ys v = NONE)
         then SOME (MatchSuccess e) else NONE
     | SOME _ -> pattern_semantics_match refs ys v`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; pattern_semantics_match_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM (LABEL_TAC "IH") THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  ASM_REWRITE_TAC[APPEND; pattern_semantics_match_def] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v` THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `a:matchResult` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `pattern_semantics_match refs (ys:(pattern_semantics_pat # num) list) v` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN CASE_REWRITE_TAC[]);;

let pmatchResult_case_NONE = prove
 (CASE_TERM `(match x with
                PMatchSuccess -> NONE
              | PMatchFailure -> NONE
              | PTypeFailure -> NONE) = NONE:A option`,
  CASES_ON `x:pmatchResult` THEN CASE_REWRITE_TAC[]);;

let is_const_row_lemma = prove
 (`(!t. ~(v = Term t [])) /\ is_const_row (p_1,p_2:A) /\
   ~(pattern_semantics_pmatch refs p_1 v = PTypeFailure) ==>
   pattern_semantics_pmatch refs p_1 v = PMatchFailure`,
  REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  STRUCT_CASES_TAC (ISPEC `p_1:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  REWRITE_TAC[is_const_row_def; NULL_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
  REPEAT IL1AUX_SPLIT_TAC THEN
  REWRITE_TAC[injectivity "term"; distinctness "term"; pattern_semantics_pmatch_def;
              distinctness "pmatchResult"; TAUT `~(a /\ b) <=> a ==> ~b`;
              FORALL_UNWIND_THM1; LENGTH] THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; ARITH_RULE `0 = n <=> n = 0`;
              REWRITE_RULE[anys_def] (SPEC `0` pmatch_list_anys)] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[distinctness "pmatchResult"]);;

let not_is_const_row = prove
 (`~is_const_row (p,x:A) /\ ~is_Or_row (p,x) /\ ~is_Any p ==>
   ~(pattern_semantics_pmatch refs p (Term t []) = PMatchSuccess)`,
  STRUCT_CASES_TAC (ISPEC `p:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  REWRITE_TAC[is_const_row_def; is_Or_row_def; is_Any_def; NULL_EQ] THEN
  REPEAT IL1AUX_SPLIT_TAC THEN
  REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"; LENGTH] THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[distinctness "pmatchResult"] THEN
  DISCH_TAC THEN
  MP_TAC (ISPECL [`refs:(num,term)fmap`; `a1:(pattern_semantics_pat)list`;
                  `[]:term list`] pattern_exh_pmatch_list_LENGTH) THEN
  ASM_REWRITE_TAC[distinctness "pmatchResult"; LENGTH]);;

let EVERY_take_until_Any = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(rows = []) ==>
     ALL (\(x,y). ~is_Any x) (TL (REVERSE (take_until_Any rows)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN DISCH_TAC THEN
  REWRITE_TAC[take_until_Any_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REVERSE; APPEND; TL; ALL] THEN
  ASM_CASES_TAC `t:(pattern_semantics_pat # num) list = []` THENL
   [ASM_REWRITE_TAC[take_until_Any_def; REVERSE; APPEND; TL; ALL]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`REVERSE (take_until_Any (t:(pattern_semantics_pat # num) list))`,
           `l:(pattern_semantics_pat # num) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; TL; ALL; ALL_APPEND] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[]);;

let matdch_FILTER_NOT_NONE = prove
 (`!xs:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs xs v = NONE) ==>
     ~(pattern_semantics_match refs (FILTER P xs) v = NONE)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  DISCH_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[pattern_semantics_match_def]) THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[distinctness "option"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  TRY (CASES_ON `pattern_semantics_match refs
                   (FILTER P (t:(pattern_semantics_pat # num) list)) v` THEN
       RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[distinctness "option"]) THEN
  ASM_REWRITE_TAC[distinctness "option"]);;

(* helpers of match_move_const_up: rows that fail can be dropped *)

let IL1AUX_MATCH_CONS_NOT_NONE = prove
 (`!refs v h l. ~(pattern_semantics_match refs (CONS h l) v = NONE) ==>
         ~(pattern_semantics_match refs l v = NONE) /\
         ~(pattern_semantics_pmatch refs (FST h) v = PTypeFailure)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`;
                       `l:(pattern_semantics_pat # num) list`] THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `pattern_semantics_match refs (l:(pattern_semantics_pat # num) list) v` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; distinctness "pmatchResult"]);;

let IL1AUX_MATCH_FILTER_FAIL = prove
 (`!refs v Q xs:(pattern_semantics_pat # num) list.
     ALL (\r. Q r ==> pattern_semantics_pmatch refs (FST r) v = PMatchFailure) xs
     ==> pattern_semantics_match refs (FILTER Q xs) v = SOME MatchFailure`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALL; pattern_semantics_match_def] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN ASM_SIMP_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[pattern_semantics_match_def] THEN
  ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[]);;

let IL1AUX_MATCH_FILTER_SAME = prove
 (`!refs v Q xs:(pattern_semantics_pat # num) list.
     ALL (\r. ~Q r ==> pattern_semantics_pmatch refs (FST r) v = PMatchFailure) xs
     ==> pattern_semantics_match refs (FILTER Q xs) v =
         pattern_semantics_match refs xs v`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; ALL] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  DISCH_THEN (LABEL_TAC "IH") THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "hd") ASSUME_TAC) THEN
  REMOVE_THEN "IH" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[pattern_semantics_match_def] THEN
  REMOVE_THEN "hd" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let IL1AUX_MATCH_SKIP = prove
 (`!refs v xs h ys:(pattern_semantics_pat # num) list.
     pattern_semantics_pmatch refs (FST h) v = PMatchFailure ==>
     pattern_semantics_match refs (APPEND xs (CONS h ys)) v =
     pattern_semantics_match refs (APPEND xs ys) v`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
   [REWRITE_TAC[FORALL_PAIR_THM; FST; pattern_semantics_match_def] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pattern_semantics_match_def] THEN
  ASM_SIMP_TAC[]);;

(* the value is a constant Term t []: the rows before the last one that are *)
(* not constant rows (nor Any or Or rows) cannot match it                    *)

let IL1AUX_MOVE_CONST_TERM = prove
 (`!l (x:pattern_semantics_pat # num).
     ~(pattern_semantics_match refs (APPEND l [x]) (Term t []) = NONE) /\
     ALL (\r. ~is_Any (FST r)) l /\ ~EX is_Or_row l ==>
     pattern_semantics_match refs
       (APPEND (FILTER is_const_row (APPEND l [x]))
               (FILTER (\x. ~is_const_row x) (APPEND l [x]))) (Term t []) =
     pattern_semantics_match refs (APPEND l [x]) (Term t [])`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; FILTER] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  POP_ASSUM (LABEL_TAC "IH") THEN X_GEN_TAC `x:pattern_semantics_pat # num` THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REWRITE_TAC[APPEND; FILTER; ALL; EX; DE_MORGAN_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP IL1AUX_MATCH_CONS_NOT_NONE) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[FST]) THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `x:pattern_semantics_pat # num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND] THENL
   [REWRITE_TAC[pattern_semantics_match_def] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pattern_semantics_pmatch refs p (Term t []) = PMatchFailure`
    ASSUME_TAC THENL
   [MP_TAC (INST [`e:num`,`x:num`] (INST_TYPE [`:num`,`:A`] not_is_const_row)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(pattern_semantics_pmatch refs p (Term t []) = PTypeFailure)` THEN
    CASES_ON `pattern_semantics_pmatch refs p (Term t [])` THEN
    REWRITE_TAC[distinctness "pmatchResult"];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`refs:(num,term)fmap`; `Term t []`;
                  `FILTER is_const_row (APPEND t' [x:pattern_semantics_pat # num])`;
                  `(p:pattern_semantics_pat,e:num)`;
                  `FILTER (\x. ~is_const_row x)
                     (APPEND t' [x:pattern_semantics_pat # num])`]
                 IL1AUX_MATCH_SKIP) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[pattern_semantics_match_def] THEN CASE_REWRITE_TAC[]);;

(* the value is not a constant Term t []: every constant row fails on it *)

let IL1AUX_MOVE_CONST_OTHER = prove
 (`!xs:(pattern_semantics_pat # num) list.
     (!t. ~(v = Term t [])) /\ ~(pattern_semantics_match refs xs v = NONE) ==>
     pattern_semantics_match refs
       (APPEND (FILTER is_const_row xs) (FILTER (\x. ~is_const_row x) xs)) v =
     pattern_semantics_match refs xs v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\r. is_const_row r ==>
                         pattern_semantics_pmatch refs (FST r) v = PMatchFailure)
                    (xs:(pattern_semantics_pat # num) list)` ASSUME_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP match_no_PTypeFailure) THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; FST] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (INST [`p2:num`,`p_2:num`]
                    (INST_TYPE [`:num`,`:A`] is_const_row_lemma)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`p1:pattern_semantics_pat`; `p2:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`refs:(num,term)fmap`; `v:term`; `is_const_row:pattern_semantics_pat # num -> bool`;
                  `xs:(pattern_semantics_pat # num) list`] IL1AUX_MATCH_FILTER_FAIL) THEN
  MP_TAC (ISPECL [`refs:(num,term)fmap`; `v:term`;
                  `\x:pattern_semantics_pat # num. ~is_const_row x`;
                  `xs:(pattern_semantics_pat # num) list`] IL1AUX_MATCH_FILTER_SAME) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[match_append] THEN CASE_REWRITE_TAC[]);;

let match_move_const_up = prove
 (`~(pattern_semantics_match refs rows v = NONE) ==>
   pattern_semantics_match refs (move_const_up rows) v =
   pattern_semantics_match refs rows v`,
  DISCH_TAC THEN
  SUBGOAL_THEN `pattern_semantics_match refs (take_until_Any rows) v =
                pattern_semantics_match refs rows v` (LABEL_TAC "tk") THENL
   [ASM_SIMP_TAC[match_take_until_Any]; ALL_TAC] THEN
  REWRITE_TAC[move_const_up_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN STRIP_TAC THEN
  REMOVE_THEN "tk" (fun th ->
    REWRITE_TAC[GSYM th] THEN
    SUBGOAL_THEN `~(pattern_semantics_match refs (take_until_Any rows) v = NONE)`
      MP_TAC THENL [ASM_REWRITE_TAC[th]; ALL_TAC]) THEN
  ASM_CASES_TAC `rows:(pattern_semantics_pat # num) list = []` THENL
   [ASM_REWRITE_TAC[take_until_Any_def; FILTER; APPEND]; ALL_TAC] THEN
  MP_TAC (ISPEC `rows:(pattern_semantics_pat # num) list` EVERY_take_until_Any) THEN
  REWRITE_TAC[ASSUME `~(rows:(pattern_semantics_pat # num) list = [])`] THEN
  UNDISCH_TAC `~EX is_Or_row (take_until_Any (rows:(pattern_semantics_pat # num) list))` THEN
  SPEC_TAC(`take_until_Any (rows:(pattern_semantics_pat # num) list)`,
           `xx:(pattern_semantics_pat # num) list`) THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `?t. v = Term t []` THENL
   [FIRST_X_ASSUM (X_CHOOSE_THEN `t:num option` SUBST_ALL_TAC);
    MATCH_MP_TAC IL1AUX_MOVE_CONST_OTHER THEN ASM_MESON_TAC[]] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x:pattern_semantics_pat # num`
      (X_CHOOSE_THEN `l:(pattern_semantics_pat # num) list` SUBST_ALL_TAC))
    (ISPEC `xx:(pattern_semantics_pat # num) list` SNOC_CASES) THEN
  REWRITE_TAC[FILTER; APPEND] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[SNOC_APPEND]) THEN REWRITE_TAC[SNOC_APPEND] THEN
  MATCH_MP_TAC IL1AUX_MOVE_CONST_TERM THEN
  RULE_ASSUM_TAC (REWRITE_RULE[EXISTS_APPEND; DE_MORGAN_THM; REVERSE_APPEND;
                               REVERSE; APPEND; TL; EVERY_REVERSE]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> is_comb (concl th) &&
     (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; FST] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let pattern_comp_pmatch_list_LENGTH = prove
 (`!ps vs. ~(pattern_semantics_pmatch_list refs ps vs = PTypeFailure) ==>
           LENGTH vs = LENGTH ps`,
  MESON_TAC[pattern_exh_pmatch_list_LENGTH]);;

(* replace last pattern with Any (used if rows are exhaustive) *)

let insert_Any_def = cake_def
  `(insert_Any [] = []) /\
   (insert_Any [(p,x:A)] = [(pattern_semantics_Any,x)]) /\
   (insert_Any (CONS r xs) = CONS r (insert_Any xs))`;;

let match_insert_Any = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     ~(pattern_semantics_match refs (insert_Any rows) v = NONE) /\
     (~(pattern_semantics_match refs rows v = SOME MatchFailure) ==>
      pattern_semantics_match refs (insert_Any rows) v =
      pattern_semantics_match refs rows v)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[insert_Any_def] THEN
  POP_ASSUM (LABEL_TAC "IH") THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h:pattern_semantics_pat # num`
      (X_CHOOSE_THEN `t':(pattern_semantics_pat # num) list` SUBST_ALL_TAC))
    (ISPEC `t:(pattern_semantics_pat # num) list` list_CASES) THENL
   [REWRITE_TAC[insert_Any_def; pattern_semantics_match_def; pmatch_Any] THEN
    CASES_ON `pattern_semantics_pmatch refs p v` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"; injectivity "option";
                distinctness "matchResult"];
    ALL_TAC] THEN
  REWRITE_TAC[insert_Any_def] THEN
  ONCE_REWRITE_TAC[pattern_semantics_match_def] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(pattern_semantics_match refs
                   (CONS (h:pattern_semantics_pat # num) t') v = NONE) /\
                ~(pattern_semantics_pmatch refs p v = PTypeFailure)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC (ISPECL [`refs:(num,term)fmap`; `v:term`;
                    `(p:pattern_semantics_pat,e:num)`;
                    `CONS (h:pattern_semantics_pat # num) t'`]
                   IL1AUX_MATCH_CONS_NOT_NONE) THEN
    ONCE_REWRITE_TAC[pattern_semantics_match_def] THEN ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  REMOVE_THEN "IH" (MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> is_neg (concl th) &&
    (try is_case_app (lhs (dest_neg (concl th))) with Failure _ -> false))) THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[distinctness "pmatchResult"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`pattern_semantics_match refs
              (insert_Any (CONS (h:pattern_semantics_pat # num) t')) v`,
           `m1:(matchResult)option`) THEN
  SPEC_TAC(`pattern_semantics_match refs (CONS (h:pattern_semantics_pat # num) t') v`,
           `m2:(matchResult)option`) THEN
  REPEAT GEN_TAC THEN
  CASES_ON `m1:(matchResult)option` THEN CASES_ON `m2:(matchResult)option` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN MESON_TAC[]);;

(* turning the pattern rows into code *)

let is_True_def = cake_def
  `(is_True True <=> T) /\
   (is_True (_:dGuard) <=> F)`;;

let mk_Disj_def = cake_def
  `mk_Disj p q = if is_True p \/ is_True q then True else Disj p q`;;

let mk_Conj_def = cake_def
  `mk_Conj p q =
     if is_True p then q else
     if is_True q then p else Conj p q`;;

let mk_If_def = cake_def
  `mk_If g p q = if is_True g then p else pattern_semantics_If g p q`;;

let get_pos_def = cake_def
  `(get_pos [] = EmptyPos) /\
   (get_pos (CONS n ns) = Pos n (get_pos ns))`;;

let pat_to_guard_def = sem1aux_def_wf
  `measure (\x:(num list # pattern_semantics_pat) +
               (num list # num # (pattern_semantics_pat)list).
              sum_CASE x (\(_,p). pattern_semantics_pat_size p)
                         (\(_,k,p). list_size pattern_semantics_pat_size p))`
  SEM1AUX_TC_TAC
  `(pat_to_guard l pattern_semantics_Any = True) /\
   (pat_to_guard l (pattern_semantics_Lit r) =
      PosTest (get_pos (REVERSE l)) (LitEq r)) /\
   (pat_to_guard l (pattern_semantics_Cons NONE pats) = pats_to_guard l 0 pats) /\
   (pat_to_guard l (pattern_semantics_Cons (SOME (t,_)) pats) =
      mk_Conj (PosTest (get_pos (REVERSE l))
                 (pattern_semantics_TagLenEq t (LENGTH pats)))
              (pats_to_guard l 0 pats)) /\
   (pat_to_guard l (pattern_semantics_Or p1 p2) =
      mk_Disj (pat_to_guard l p1) (pat_to_guard l p2)) /\
   (pat_to_guard l (pattern_semantics_Ref p) = pat_to_guard (CONS 0 l) p) /\
   (pats_to_guard l k [] = True) /\
   (pats_to_guard l k [p] = pat_to_guard (CONS k l) p) /\
   (pats_to_guard l k (CONS p ps) =
      mk_Conj (pat_to_guard (CONS k l) p) (pats_to_guard l (k + 1) ps))`;;

let pat_to_guard_ind = cake_ind "pat_to_guard";;

let pats_to_code_def = cake_def
  `(pats_to_code [] = pattern_semantics_Fail) /\
   (pats_to_code (CONS (p,x) rows) =
      mk_If (pat_to_guard [] p) (pattern_semantics_Leaf x) (pats_to_code rows))`;;

let pattern_comp_walk_def = cake_def
  `(pattern_comp_walk [] x refs = SOME x) /\
   (pattern_comp_walk (CONS n ns) x refs =
      match x with
        Term t xs ->
          if n < LENGTH xs then pattern_comp_walk ns (EL n xs) refs else NONE
      | pattern_semantics_RefPtr p ->
          if ~(n = 0) then NONE else
          (match FLOOKUP refs p with
             SOME y -> pattern_comp_walk ns y refs
           | _ -> NONE)
      | _ -> NONE)`;;

let walk_list_def = cake_def
  `walk_list ns x refs =
     match pattern_comp_walk ns x refs with
       SOME (Term _ vs) -> SOME vs
     | _ -> NONE`;;

let app_pos_Pos = prove
 (`!n xs. n < LENGTH xs ==>
          app_pos refs (Pos n x) (Term t xs) = app_pos refs x (EL n xs)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; LT; NOT_SUC; app_pos_def; EL; HD; TL; LT_SUC] THEN
  ASM_SIMP_TAC[]);;

let walk_thm = prove
 (`!l v refs x.
     pattern_comp_walk l v refs = SOME x ==>
     app_pos refs (get_pos l) v = SOME x`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[pattern_comp_walk_def; get_pos_def; app_pos_def;
              injectivity "option"] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
  CASE_REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[app_pos_Pos];
    ALL_TAC] THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o REWRITE_RULE[]) THEN
  CASES_ON `FLOOKUP (refs:(num,term)fmap) a` THEN
  CASE_REWRITE_TAC[distinctness "option"] THEN
  ASM_REWRITE_TAC[app_pos_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let walk_append = prove
 (CASE_TERM `!xs ys v refs.
     pattern_comp_walk (APPEND xs ys) v refs =
     match pattern_comp_walk xs v refs with
       NONE -> NONE
     | SOME v -> pattern_comp_walk ys v refs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; pattern_comp_walk_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (refs:(num,term)fmap) a` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let is_True_thm = prove
 (`!t. is_True t <=> t = True`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `t:dGuard` (nchotomy_of_type `:dGuard`)) THEN
  REWRITE_TAC[is_True_def; distinctness "dGuard"]);;

let dt_eval_guard_mk_Conj = prove
 (`dt_eval_guard refs v (mk_Conj p q) = dt_eval_guard refs v (Conj p q)`,
  REWRITE_TAC[mk_Conj_def; is_True_thm] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[dt_eval_guard_def] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `dt_eval_guard refs v p` THEN CASE_REWRITE_TAC[] THEN
  TRY (CASES_ON `a:bool`) THEN REWRITE_TAC[]);;

(* helpers of dt_eval_guard_pat_to_guard: walking into a constructor *)

let IL1AUX_WALK_LIST_SOME = prove
 (`!ns x refs vs.
     walk_list ns x refs = SOME vs <=>
     ?tg. pattern_comp_walk ns x refs = SOME (Term tg vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[walk_list_def] THEN
  CASES_ON `pattern_comp_walk ns x refs` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  STRUCT_CASES_TAC (ISPEC `a:term` (nchotomy_of_type `:term`)) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              distinctness "term"; injectivity "term"] THEN
  MESON_TAC[]);;

let IL1AUX_WALK_SNOC = prove
 (`!l v refs tg ys h t.
     pattern_comp_walk l v refs = SOME (Term tg (APPEND ys (CONS h t))) ==>
     pattern_comp_walk (APPEND l [LENGTH ys]) v refs = SOME h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[walk_append] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pattern_comp_walk_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n < n + SUC m`] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD; pattern_comp_walk_def]);;

let dt_eval_guard_pat_to_guard = prove
 (`(!l p x.
      ~(pattern_semantics_pmatch refs p x = PTypeFailure) /\
      pattern_comp_walk (REVERSE l) v refs = SOME x ==>
      dt_eval_guard refs v (pat_to_guard l p) =
        SOME (pattern_semantics_pmatch refs p x = PMatchSuccess)) /\
   (!l k ps xs ys.
      ~(pattern_semantics_pmatch_list refs ps xs = PTypeFailure) /\
      LENGTH ys = k /\
      walk_list (REVERSE l) v refs = SOME (APPEND ys xs) /\
      LENGTH xs = LENGTH ps ==>
      dt_eval_guard refs v (pats_to_guard l k ps) =
        SOME (pattern_semantics_pmatch_list refs ps xs = PMatchSuccess))`,
  MATCH_MP_TAC pat_to_guard_ind THEN REPEAT CONJ_TAC THENL
   [(* Any *)
    REWRITE_TAC[pat_to_guard_def; dt_eval_guard_def; pmatch_Any];
    (* Lit *)
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (ISPEC `x:term` (nchotomy_of_type `:term`)) THEN
    REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"] THEN
    REWRITE_TAC[pat_to_guard_def; dt_eval_guard_def] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o MATCH_MP walk_thm)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[dt_test_def] THEN
    REPEAT (COND_CASES_TAC THEN
            ASM_REWRITE_TAC[distinctness "pmatchResult"; injectivity "option"]);
    (* Cons NONE *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:term` THEN
    STRUCT_CASES_TAC (ISPEC `x:term` (nchotomy_of_type `:term`)) THEN
    REPEAT IL1AUX_SPLIT_TAC THEN
    REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"] THEN
    REWRITE_TAC[pat_to_guard_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `[]:term list` THEN
    ASM_REWRITE_TAC[APPEND; LENGTH; IL1AUX_WALK_LIST_SOME] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC pattern_comp_pmatch_list_LENGTH THEN ASM_REWRITE_TAC[];
    (* Cons SOME *)
    MAP_EVERY X_GEN_TAC [`l:num list`; `t:num`; `sibs:((num#num)list)option`;
                         `pats:(pattern_semantics_pat)list`] THEN
    DISCH_TAC THEN X_GEN_TAC `w:term` THEN
    STRUCT_CASES_TAC (ISPEC `w:term` (nchotomy_of_type `:term`)) THEN
    REPEAT IL1AUX_SPLIT_TAC THEN
    REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"] THEN
    REWRITE_TAC[pat_to_guard_def; dt_eval_guard_mk_Conj] THEN
    REWRITE_TAC[dt_eval_guard_def] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
      (fun th -> ASSUME_TAC th THEN ASSUME_TAC (MATCH_MP walk_thm th))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[dt_test_def] THEN
    CASE_REWRITE_TAC[] THEN
    (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `[]:term list` THEN
      ASM_REWRITE_TAC[APPEND; LENGTH; IL1AUX_WALK_LIST_SOME] THEN
      ASM_MESON_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[distinctness "pmatchResult"; injectivity "option"]]);
    (* Or *)
    REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    X_GEN_TAC `w:term` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(pattern_semantics_pmatch refs p1 w = PTypeFailure) /\
                  ~(pattern_semantics_pmatch refs p2 w = PTypeFailure)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(pattern_semantics_pmatch refs (pattern_semantics_Or p1 p2) w =
                     PTypeFailure)` THEN
      REWRITE_TAC[pattern_semantics_pmatch_def] THEN
      CASES_ON `pattern_semantics_pmatch refs p1 w` THEN
      CASES_ON `pattern_semantics_pmatch refs p2 w` THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[distinctness "pmatchResult"];
      ALL_TAC] THEN
    REMOVE_THEN "IH1" (MP_TAC o SPEC `w:term`) THEN
    REMOVE_THEN "IH2" (MP_TAC o SPEC `w:term`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pat_to_guard_def; mk_Disj_def; is_True_thm] THEN
    REWRITE_TAC[pattern_semantics_pmatch_def] THEN
    UNDISCH_TAC `~(pattern_semantics_pmatch refs p2 w = PTypeFailure)` THEN
    UNDISCH_TAC `~(pattern_semantics_pmatch refs p1 w = PTypeFailure)` THEN
    SPEC_TAC(`pattern_semantics_pmatch refs p1 w`,`r1:pmatchResult`) THEN
    SPEC_TAC(`pattern_semantics_pmatch refs p2 w`,`r2:pmatchResult`) THEN
    SPEC_TAC(`pat_to_guard l p1`,`g1:dGuard`) THEN
    SPEC_TAC(`pat_to_guard l p2`,`g2:dGuard`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE[dt_eval_guard_def; injectivity "option"]) THEN
      REWRITE_TAC[dt_eval_guard_def; injectivity "option"];
      ASM_REWRITE_TAC[dt_eval_guard_def] THEN CASE_REWRITE_TAC[]] THEN
    CASES_ON `r1:pmatchResult` THEN CASES_ON `r2:pmatchResult` THEN
    CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[distinctness "pmatchResult"]) THEN
    ASM_REWRITE_TAC[distinctness "pmatchResult"] THEN
    TRY (FIRST_ASSUM CONTR_TAC);
    (* Ref *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `w:term` THEN
    STRUCT_CASES_TAC (ISPEC `w:term` (nchotomy_of_type `:term`)) THEN
    REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"] THEN
    CASES_ON `FLOOKUP (refs:(num,term)fmap) a` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "pmatchResult"] THEN
    STRIP_TAC THEN REWRITE_TAC[pat_to_guard_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REVERSE; walk_append] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[pattern_comp_walk_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[pattern_comp_walk_def];
    (* no patterns *)
    REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[pat_to_guard_def; dt_eval_guard_def; pmatch_list_nil];
    (* one pattern *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (ISPEC `xs:term list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
      (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC))) THEN
    REWRITE_TAC[pat_to_guard_def; IL1AUX_WALK_LIST_SOME] THEN
    REWRITE_TAC[pmatch_list_cons; pmatch_list_nil; pand_simps] THEN
    DISCH_THEN (X_CHOOSE_TAC `tg:num option`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REVERSE] THEN
    MATCH_MP_TAC IL1AUX_WALK_SNOC THEN ASM_MESON_TAC[];
    (* two or more patterns *)
    REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHs") (LABEL_TAC "IHp")) THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (ISPEC `xs:term list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
      (CONJUNCTS_THEN2 (LABEL_TAC "wl") ASSUME_TAC))) THEN
    REWRITE_TAC[pmatch_list_cons; pand_eq_PTypeFailure; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    USE_THEN "wl" (MP_TAC o REWRITE_RULE[IL1AUX_WALK_LIST_SOME]) THEN
    DISCH_THEN (X_CHOOSE_TAC `tg:num option`) THEN
    REMOVE_THEN "IHp" (MP_TAC o SPEC `h:term`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REVERSE] THEN MATCH_MP_TAC IL1AUX_WALK_SNOC THEN
      ASM_MESON_TAC[];
      DISCH_TAC] THEN
    REMOVE_THEN "IHs" (MP_TAC o SPECL [`t:term list`; `APPEND ys [h:term]`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; GSYM APPEND_ASSOC; APPEND] THEN
      REWRITE_TAC[ONE];
      DISCH_TAC] THEN
    REWRITE_TAC[pat_to_guard_def; dt_eval_guard_mk_Conj; dt_eval_guard_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(pattern_semantics_pmatch refs p h = PTypeFailure)` THEN
    UNDISCH_TAC `~(pattern_semantics_pmatch_list refs (CONS v5 v6) t = PTypeFailure)` THEN
    SPEC_TAC(`pattern_semantics_pmatch refs p h`,`r1:pmatchResult`) THEN
    SPEC_TAC(`pattern_semantics_pmatch_list refs (CONS v5 v6) t`,`r2:pmatchResult`) THEN
    REPEAT GEN_TAC THEN
    CASES_ON `r1:pmatchResult` THEN CASES_ON `r2:pmatchResult` THEN
    REWRITE_TAC[pand_def; distinctness "pmatchResult"]]);;

let mk_If_thm = prove
 (`dt_eval refs v (mk_If g p q) = dt_eval refs v (pattern_semantics_If g p q)`,
  REWRITE_TAC[mk_If_def; is_True_thm] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[dt_eval_def; dt_eval_guard_def] THEN CASE_REWRITE_TAC[]);;

let pat_to_code_thm = prove
 (`!rows.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     dt_eval refs v (pats_to_code rows) = pattern_semantics_match refs rows v`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[pats_to_code_def; pattern_semantics_match_def; dt_eval_def] THEN
  POP_ASSUM (LABEL_TAC "IH") THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REWRITE_TAC[pats_to_code_def; mk_If_thm; dt_eval_def] THEN DISCH_TAC THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP IL1AUX_MATCH_CONS_NOT_NONE) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[FST]) THEN
  MP_TAC (SPECL [`[]:num list`; `p:pattern_semantics_pat`; `v:term`]
                (CONJUNCT1 dt_eval_guard_pat_to_guard)) THEN
  ASM_REWRITE_TAC[REVERSE; pattern_comp_walk_def] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THEN REMOVE_THEN "IH" (MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(pattern_semantics_pmatch refs p v = PTypeFailure)` THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "pmatchResult"; dt_eval_def] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v = NONE)` THEN
  CASES_ON `pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

(* plug all the parts together *)

let pattern_comp_comp_def = cake_def
  `pattern_comp_comp (rows:(pattern_semantics_pat # num) list) =
     let rows0 = move_const_up rows in
     let rows1 = (if exh_rows rows0 then insert_Any rows0 else rows0) in
       pats_to_code rows1`;;

let pattern_comp_comp_thm = prove
 (`~(pattern_semantics_match refs rows v = NONE) ==>
   dt_eval refs v (pattern_comp_comp rows) = pattern_semantics_match refs rows v`,
  REWRITE_TAC[pattern_comp_comp_def; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP match_move_const_up) THEN
  SUBGOAL_THEN
    `~(pattern_semantics_match refs (move_const_up rows) v = NONE)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC (INST [`move_const_up (rows:(pattern_semantics_pat # num) list)`,
                  `rows:(pattern_semantics_pat # num) list`] exh_rows_thm) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (ISPEC `move_const_up (rows:(pattern_semantics_pat # num) list)`
                  match_insert_Any) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[pat_to_code_thm];
    ASM_SIMP_TAC[pat_to_code_thm]]);;
