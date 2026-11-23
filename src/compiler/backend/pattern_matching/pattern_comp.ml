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
(* - The two cases of HOL4's proof of match_move_const_up (the value is a    *)
(*   constant Term t [] or not) are the helper lemmas IL1AUX_MOVE_CONST_TERM *)
(*   and IL1AUX_MOVE_CONST_OTHER.                                            *)
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
  MATCH_MP_TAC is_Any_ind THEN FS[is_Any_def] THEN FS[pattern_semantics_pmatch_def] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[]);;

let match_take_until_Any = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     pattern_semantics_match refs (take_until_Any rows) v =
     pattern_semantics_match refs rows v`,
  MATCH_MP_TAC list_INDUCT THEN FS[take_until_Any_def; FORALL_PAIR_THM] THEN
  FS[pattern_semantics_match_def] THEN RW[] THENL [IMP_RES_TAC is_Any_pmatch; ALL_TAC] THEN
  FS[pattern_semantics_match_def] THEN EVERY_CASE_TAC THEN FS[]);;

let match_append = prove
 (CASE_TERM `!xs ys refs v.
     pattern_semantics_match refs (APPEND xs ys) v =
     match pattern_semantics_match refs xs v with
       NONE -> NONE
     | SOME (MatchSuccess e) ->
         if ~(pattern_semantics_match refs ys v = NONE)
         then SOME (MatchSuccess e) else NONE
     | SOME _ -> pattern_semantics_match refs ys v`,
  MATCH_MP_TAC list_INDUCT THEN
  FS[APPEND; pattern_semantics_match_def; FORALL_PAIR_THM] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[]);;

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
  STRIP_TAC THEN QCASES_ON "p_1" THEN GVS[is_const_row_def; NULL_EQ] THEN
  QCASES_ON "v" THEN REPEAT IL1AUX_SPLIT_TAC THEN
  FS[pattern_semantics_pmatch_def; COND_CASE_EQ] THEN
  ASM_MESON_TAC[pmatch_list_nil; list_CASES]);;

let not_is_const_row = prove
 (`~is_const_row (p,x:A) /\ ~is_Or_row (p,x) /\ ~is_Any p ==>
   ~(pattern_semantics_pmatch refs p (Term t []) = PMatchSuccess)`,
  STRIP_TAC THEN QCASES_ON "p" THEN
  FS[pattern_semantics_pmatch_def; is_const_row_def; is_Or_row_def; is_Any_def; NULL_EQ] THEN
  QCASES_ON "a1" THEN REPEAT IL1AUX_SPLIT_TAC THEN FS[pattern_semantics_pmatch_def] THEN
  EVERY_CASE_TAC THEN FS[]);;

let EVERY_take_until_Any = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(rows = []) ==>
     ALL (\(x,y). ~is_Any x) (TL (REVERSE (take_until_Any rows)))`,
  MATCH_MP_TAC list_INDUCT THEN FS[take_until_Any_def; FORALL_PAIR_THM] THEN RW[] THEN
  QCASES_ON "a1" THEN FS[take_until_Any_def] THEN
  RENAME1 "APPEND xs _" THEN QCASES_ON "xs" THEN FS[]);;

let matdch_FILTER_NOT_NONE = prove
 (`!xs:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs xs v = NONE) ==>
     ~(pattern_semantics_match refs (FILTER P xs) v = NONE)`,
  MATCH_MP_TAC list_INDUCT THEN FS[FORALL_PAIR_THM] THEN RW[FILTER] THEN
  FS[pattern_semantics_match_def] THEN EVERY_CASE_TAC THEN FS[]);;

(* the two cases of match_move_const_up: the value is not a constant term, *)
(* so every constant row fails; or it is a constant Term t [], so every     *)
(* row before the last that is not a constant row fails                     *)

let IL1AUX_MOVE_CONST_OTHER = prove
 (`(!t. ~(v = Term t [])) ==>
   !xx:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs xx v = NONE) ==>
     pattern_semantics_match refs (FILTER is_const_row xx) v = SOME MatchFailure /\
     pattern_semantics_match refs (FILTER (\x. ~is_const_row x) xx) v =
     pattern_semantics_match refs xx v`,
  DISCH_TAC THEN MATCH_MP_TAC list_INDUCT THEN FS[FORALL_PAIR_THM] THEN RW[FILTER] THEN
  ASM_CASES_TAC `pattern_semantics_pmatch refs p1 v = PTypeFailure` THEN
  FS[pattern_semantics_match_def] THEN IMP_RES_TAC is_const_row_lemma THEN
  EVERY_CASE_TAC THEN FS[]);;

let IL1AUX_MOVE_CONST_TERM = prove
 (`!(x:pattern_semantics_pat # num) l.
     ~(pattern_semantics_match refs (SNOC x l) (Term t []) = NONE) /\
     ALL (\(x,y). ~is_Any x) l /\ ~EX is_Or_row l ==>
     pattern_semantics_match refs
       (APPEND (FILTER is_const_row (SNOC x l))
               (FILTER (\x. ~is_const_row x) (SNOC x l))) (Term t []) =
     pattern_semantics_match refs (SNOC x l) (Term t [])`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [RW[FILTER; SNOC; APPEND]; ALL_TAC] THEN
  FS[FORALL_PAIR_THM] THEN RW[FILTER; SNOC; APPEND] THEN
  CASES_ON `pattern_semantics_pmatch refs p1 (Term t [])` THEN
  CASES_ON `pattern_semantics_match refs (SNOC x a1) (Term t [])` THEN
  RFS[pattern_semantics_match_def; match_append] THEN
  IMP_RES_TAC not_is_const_row THEN RFS[]);;

let IL1AUX_MOVE_CONST = prove
 (`!xx:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs xx v = NONE) /\ ~EX is_Or_row xx /\
     ALL (\(x,y). ~is_Any x) (TL (REVERSE xx)) ==>
     pattern_semantics_match refs
       (APPEND (FILTER is_const_row xx) (FILTER (\x. ~is_const_row x) xx)) v =
     pattern_semantics_match refs xx v`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `xx:(pattern_semantics_pat # num) list` SNOC_CASES) THEN
  ASM_CASES_TAC `?t. v = Term t []` THEN FS[FILTER; NOT_EXISTS_THM] THEN STRIP_TAC THENL
   [MATCH_MP_TAC IL1AUX_MOVE_CONST_TERM THEN FS[REVERSE_SNOC; EVERY_REVERSE];
    IMP_RES_TAC IL1AUX_MOVE_CONST_OTHER THEN FS[match_append]]);;

let match_move_const_up = prove
 (`~(pattern_semantics_match refs rows v = NONE) ==>
   pattern_semantics_match refs (move_const_up rows) v =
   pattern_semantics_match refs rows v`,
  DISCH_TAC THEN FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP match_take_until_Any) THEN
  RW[move_const_up_def] THEN
  ASM_CASES_TAC `rows:(pattern_semantics_pat # num) list = []` THEN FS[take_until_Any_def] THEN
  MATCH_MP_TAC IL1AUX_MOVE_CONST THEN
  FS[DE_MORGAN_THM; EVERY_take_until_Any; match_take_until_Any]);;

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
  MATCH_MP_TAC list_INDUCT THEN
  FS[pattern_semantics_match_def; insert_Any_def; FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN QCASES_ON "a1" THEN
  FS[insert_Any_def; pattern_semantics_match_def; pmatch_Any] THEN
  CASES_ON `pattern_semantics_pmatch refs p1 v` THEN FS[] THEN EVERY_CASE_TAC THEN FS[]);;

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
  `MEASURE (\x:(num list # pattern_semantics_pat) +
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
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN FS[app_pos_def; EL; LT]);;

let walk_thm = prove
 (`!l v refs x.
     pattern_comp_walk l v refs = SOME x ==>
     app_pos refs (get_pos l) v = SOME x`,
  LIST_INDUCT_TAC THEN FS[pattern_comp_walk_def; get_pos_def; app_pos_def] THEN
  FS[case_eq "option"; COND_CASE_EQ; case_eq "term"] THEN RW[] THEN FS[] THEN RW[] THEN
  FS[app_pos_Pos] THEN FS[app_pos_def]);;

let walk_append = prove
 (CASE_TERM `!xs ys v refs.
     pattern_comp_walk (APPEND xs ys) v refs =
     match pattern_comp_walk xs v refs with
       NONE -> NONE
     | SOME v -> pattern_comp_walk ys v refs`,
  LIST_INDUCT_TAC THEN FS[pattern_comp_walk_def; APPEND] THEN REPEAT GEN_TAC THEN
  QCASES_ON "v" THEN FS[] THEN RW[] THEN CASE_TAC THEN FS[]);;

let is_True_thm = prove
 (`!t. is_True t <=> t = True`,
  GEN_TAC THEN QCASES_ON "t" THEN FS[is_True_def]);;

let dt_eval_guard_mk_Conj = prove
 (`dt_eval_guard refs v (mk_Conj p q) = dt_eval_guard refs v (Conj p q)`,
  RW[mk_Conj_def] THEN FS[is_True_thm; dt_eval_guard_def] THEN
  RVEQ_TAC THEN FS[] THEN EVERY_CASE_TAC THEN FS[]);;

let IL1AUX_WALK_LIST_SOME = prove
 (`!ns x refs vs.
     walk_list ns x refs = SOME vs <=>
     ?tg. pattern_comp_walk ns x refs = SOME (Term tg vs)`,
  RW[walk_list_def] THEN EVERY_CASE_TAC THEN FS[]);;

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
  MATCH_MP_TAC pat_to_guard_ind THEN RW[] THENL
   [(* Any *)
    FS[pattern_semantics_pmatch_def; pat_to_guard_def; dt_eval_guard_def];
    (* Lit *)
    QCASES_ON "x" THEN FS[pattern_semantics_pmatch_def; COND_CASE_EQ] THEN
    FS[pat_to_guard_def; dt_eval_guard_def] THEN IMP_RES_TAC walk_thm THEN FS[dt_test_def];
    (* Cons NONE *)
    QCASES_ON "x" THEN FS[pattern_semantics_pmatch_def] THEN QCASES_ON "a0" THEN
    FS[pattern_semantics_pmatch_def] THEN FS[walk_list_def; pat_to_guard_def] THEN
    IMP_RES_TAC pattern_comp_pmatch_list_LENGTH THEN RFS[];
    (* Cons SOME *)
    QCASES_ON "x'" THEN FS[pattern_semantics_pmatch_def] THEN QCASES_ON "a0" THEN
    FS[pattern_semantics_pmatch_def] THEN FS[walk_list_def; pat_to_guard_def] THEN
    IMP_RES_TAC pattern_comp_pmatch_list_LENGTH THEN RFS[dt_eval_guard_mk_Conj] THEN
    FS[COND_CASE_EQ] THEN RVEQ_TAC THEN FS[dt_eval_guard_def; dt_test_def] THEN
    IMP_RES_TAC walk_thm THEN FS[dt_test_def] THEN COND_CASES_TAC THEN RFS[];
    (* Or *)
    FS[pat_to_guard_def; dt_eval_guard_def; pattern_semantics_pmatch_def] THEN
    CASES_ON `pattern_semantics_pmatch refs p1 x` THEN
    CASES_ON `pattern_semantics_pmatch refs p2 x` THEN RFS[] THEN
    RW[mk_Disj_def; dt_eval_guard_def] THEN RFS[is_True_thm; dt_eval_guard_def];
    (* Ref *)
    QCASES_ON "x" THEN FS[pat_to_guard_def; pattern_semantics_pmatch_def] THEN
    TOP_CASE_TAC THEN FS[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FS[walk_append; pattern_comp_walk_def];
    (* no patterns *)
    FS[pat_to_guard_def; pattern_semantics_pmatch_def; dt_eval_guard_def];
    (* one pattern *)
    QCASES_ON "xs" THEN
    GVS[pattern_semantics_pmatch_def; LENGTH_EQ_NIL; IL1AUX_WALK_LIST_SOME; pat_to_guard_def] THEN
    FIRST_X_ASSUM (QSPEC_THEN "a0" MP_TAC) THEN
    RFS[walk_append; pattern_comp_walk_def; EL_LENGTH_APPEND] THEN TOP_CASE_TAC THEN FS[];
    (* two or more patterns *)
    QCASES_ON "xs" THEN
    FS[pmatch_list_cons; pand_eq_PTypeFailure; DE_MORGAN_THM; IL1AUX_WALK_LIST_SOME] THEN
    FIRST_X_ASSUM (QSPEC_THEN "a0" MP_TAC) THEN
    FIRST_X_ASSUM (QSPECL_THEN ["a1"; "APPEND ys [a0]"] MP_TAC) THEN
    REWRITE_TAC[walk_append; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH] THEN
    RFS[ARITH_ss; pattern_comp_walk_def; EL_LENGTH_APPEND; pat_to_guard_def;
        dt_eval_guard_mk_Conj; dt_eval_guard_def; pand_eq_PMatchSuccess] THEN
    COND_CASES_TAC THEN FS[]]);;

let mk_If_thm = prove
 (`dt_eval refs v (mk_If g p q) = dt_eval refs v (pattern_semantics_If g p q)`,
  RW[mk_If_def] THEN FS[is_True_thm; dt_eval_def; dt_eval_guard_def]);;

let pat_to_code_thm = prove
 (`!rows.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     dt_eval refs v (pats_to_code rows) = pattern_semantics_match refs rows v`,
  MATCH_MP_TAC list_INDUCT THEN
  FS[pattern_semantics_match_def; pats_to_code_def; dt_eval_def; FORALL_PAIR_THM;
     mk_If_thm] THEN
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`[]:num list`; `p1:pattern_semantics_pat`; `v:term`]
                 (CONJUNCT1 dt_eval_guard_pat_to_guard)) THEN
  CASES_ON `pattern_semantics_pmatch refs p1 v` THEN
  CASES_ON `pattern_semantics_match refs a1 v` THEN
  FS[REVERSE; pattern_comp_walk_def; dt_eval_def]);;

(* plug all the parts together *)

let pattern_comp_comp_def = cake_def
  `pattern_comp_comp (rows:(pattern_semantics_pat # num) list) =
     let rows0 = move_const_up rows in
     let rows1 = (if exh_rows rows0 then insert_Any rows0 else rows0) in
       pats_to_code rows1`;;

let pattern_comp_comp_thm = prove
 (`~(pattern_semantics_match refs rows v = NONE) ==>
   dt_eval refs v (pattern_comp_comp rows) = pattern_semantics_match refs rows v`,
  FS[pattern_comp_comp_def] THEN STRIP_TAC THEN
  DRULE match_move_const_up THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN RW[] THEN
  RFS[pat_to_code_thm; match_insert_Any; exh_rows_thm]);;
