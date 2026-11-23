(* ========================================================================= *)
(* bvi_inlineProof: port of HOL4 compiler/backend/proofs/                    *)
(* bvi_inlineProofScript.sml (CakeML v3479).  Correctness of the CPR         *)
(* worker-wrapper BVI inliner.  BVLPROPSAUX_ names are local helpers (not   *)
(* HOL4 names).                                                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

type_invention_error := true;;

(* HOL4 [simp] *)
let inline_exps_LENGTH = prove
 (`!(cs:(num#bvi_exp)spt) es. LENGTH (inline_exps cs es) = LENGTH es`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[inline_exp_def; LENGTH]);;

(* HOL4 [simp] *)
let remove_ticks_exps_LENGTH = prove
 (`!es. LENGTH (remove_ticks_exps es) = LENGTH es`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[remove_ticks_exp_def; LENGTH]);;

(* HOL4 [simp] *)
let inline_exps_CONS = prove
 (`!(cs:(num#bvi_exp)spt) x xs.
     inline_exps cs (CONS x xs) = CONS (inline_exp cs x) (inline_exps cs xs)`,
  REWRITE_TAC[inline_exp_def]);;

let inline_exps_MAP = prove
 (`!(cs:(num#bvi_exp)spt) es. inline_exps cs es = MAP (inline_exp cs) es`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[inline_exp_def; MAP]);;

(* HOL4 [simp] *)
let inline_exps_REVERSE = prove
 (`!(cs:(num#bvi_exp)spt) es.
     inline_exps cs (REVERSE es) = REVERSE (inline_exps cs es)`,
  REWRITE_TAC[inline_exps_MAP; MAP_REVERSE]);;

(* HOL4 [simp] *)
let inline_exps_MAP_Var = prove
 (`!(cs:(num#bvi_exp)spt) ns. inline_exps cs (MAP bvi_Var ns) = MAP bvi_Var ns`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[inline_exp_def; MAP]);;

(* HOL4 [simp]; GENLIST is list_of_seq *)
let inline_exps_GENLIST_Var = prove
 (`!(cs:(num#bvi_exp)spt) n.
     inline_exps cs (list_of_seq bvi_Var n) = list_of_seq bvi_Var n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; inline_exp_def; inline_exps_MAP; MAP_APPEND; MAP] THEN
  ASM_REWRITE_TAC[GSYM inline_exps_MAP]);;

let incremental_wrapper_example = prove
 (`?cs p1 p2.
     bvi_inline_compile_inc LN
       [(10,0,LetCall 0 0 11 [] (bvi_Op (BlockOp (clos_Cons 7)) []))] = (cs,p1) /\
     bvi_inline_compile_inc cs [(12,0,bvi_Call 0 (SOME 10) [] NONE)] = (cs,p2) /\
     p2 = [(12,0,bvi_Let [] (LetCall 0 0 11 [] (bvi_Op (BlockOp (clos_Cons 7)) [])))]`,
  MAP_EVERY EXISTS_TAC
   [`insert 10 (0,LetCall 0 0 11 [] (bvi_Op (BlockOp (clos_Cons 7)) [])) LN`;
    `[(10,0,LetCall 0 0 11 [] (bvi_Op (BlockOp (clos_Cons 7)) []))]`;
    `[(12,0,bvi_Let [] (LetCall 0 0 11 [] (bvi_Op (BlockOp (clos_Cons 7)) [])))]`] THEN
  REWRITE_TAC[bvi_inline_compile_inc_def; inline_all_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[inline_exp_def; wrapper_ok_def; canonical_wrapper_def; list_of_seq;
              REVERSE; LET_DEF; LET_END_DEF; lookup_insert1; LENGTH] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[inline_exp_def; lookup_insert1; lookup_insert; LENGTH; MAP;
              remove_ticks_exp_def; bvi_mk_tick_def; ITER; ONE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[remove_ticks_exp_def; MAP; PAIR_EQ; bvi_mk_tick_def; ITER; ONE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[remove_ticks_exp_def; MAP; PAIR_EQ; canonical_wrapper_def]);;

let canonical_wrapper_thm = prove
 (`!name arity body.
     canonical_wrapper name arity body <=>
     ?rets ticks worker tag.
       ~(worker = name) /\
       body = LetCall rets ticks worker (list_of_seq bvi_Var arity)
                (bvi_Op (BlockOp (clos_Cons tag)) (REVERSE (list_of_seq bvi_Var rets)))`,
  MATCH_MP_TAC canonical_wrapper_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[canonical_wrapper_def] THEN
  REWRITE_TAC(BVLPROPSAUX_both (distinctness "bvi_exp") @
              BVLPROPSAUX_both (distinctness "clos_op") @
              BVLPROPSAUX_both (distinctness "block_op") @
              [injectivity "bvi_exp"; injectivity "clos_op"; injectivity "block_op"]) THEN
  TRY (MESON_TAC[]));;

(* HOL4 [simp] *)
let wrapper_ok_inline_exp = prove
 (`!name arity body (cs:(num#bvi_exp)spt).
     wrapper_ok name arity body ==> inline_exp cs body = body`,
  REWRITE_TAC[wrapper_ok_def; canonical_wrapper_thm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[inline_exp_def; inline_exps_GENLIST_Var; inline_exps_REVERSE]);;

let inline_all_MAP_FST = prove
 (`!(cs:(num#bvi_exp)spt) prog. MAP FST (SND (inline_all cs prog)) = MAP FST prog`,
  SUBGOAL_THEN `!prog (cs:(num#bvi_exp)spt). MAP FST (SND (inline_all cs prog)) = MAP FST prog`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[inline_all_def; MAP; SND] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  GEN_TAC THEN REWRITE_TAC[inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `cs1 = if wrapper_ok name arity (inline_exp (cs:(num#bvi_exp)spt) body)
                    then insert name (arity,inline_exp cs body) cs else cs` THEN
  MP_TAC(ISPEC `inline_all (cs1:(num#bvi_exp)spt) t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[MAP; SND; FST; CONS_11] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cs1:(num#bvi_exp)spt`) THEN ASM_REWRITE_TAC[SND]);;

(* HOL4 [simp] *)
let MAP_FST_remove_ticks_prog = prove
 (CASE_TERM `!prog:(num#num#bvi_exp)list.
     MAP FST (MAP (\p. match p with (name,arity,body) -> (name,arity,remove_ticks_exp body))
                  prog) = MAP FST prog`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[]);;

let compile_inc_MAP_FST = prove
 (`!(cs:(num#bvi_exp)spt) prog cs1 prog1.
     bvi_inline_compile_inc cs prog = (cs1,prog1) ==> MAP FST prog1 = MAP FST prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_inline_compile_inc_def] THEN
  MP_TAC(ISPEC `inline_all (cs:(num#bvi_exp)spt) prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `p2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[MAP_FST_remove_ticks_prog] THEN
  MP_TAC(ISPECL [`cs:(num#bvi_exp)spt`; `prog:(num#num#bvi_exp)list`] inline_all_MAP_FST) THEN
  ASM_REWRITE_TAC[SND]);;

let compile_inc_ALL_DISTINCT = prove
 (`!(cs:(num#bvi_exp)spt) prog cs1 prog1.
     bvi_inline_compile_inc cs prog = (cs1,prog1) /\ ALL_DISTINCT (MAP FST prog) ==>
     ALL_DISTINCT (MAP FST prog1)`,
  MESON_TAC[compile_inc_MAP_FST]);;

let BVLPROPSAUX_BI_LABELS_RWS =
  [bvi_get_code_labels_def; MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY];;

let remove_ticks_get_code_labels = prove
 (`(!e. bvi_get_code_labels (remove_ticks_exp e) = bvi_get_code_labels e) /\
   (!es. UNIONS (set_of_list (MAP bvi_get_code_labels (remove_ticks_exps es))) =
         UNIONS (set_of_list (MAP bvi_get_code_labels es)))`,
  MATCH_MP_TAC remove_ticks_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[remove_ticks_exp_def] THEN
  ASM_REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THEN
  CASES_ON `handler:bvi_exp option` THEN
  ASM_REWRITE_TAC(OPTION_MAP_DEF :: BVLPROPSAUX_BI_LABELS_RWS) THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[]);;

let remove_ticks_prog_code_labels = prove
 (CASE_TERM `!prog:(num#num#bvi_exp)list.
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND)
       (MAP (\p. match p with (name,arity,body) -> (name,arity,remove_ticks_exp body))
            prog))) =
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) prog))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[o_THM; SND; remove_ticks_get_code_labels]);;

let compile_inc_code_labels = prove
 (`!(cs:(num#bvi_exp)spt) prog cs1 prog1.
     bvi_inline_compile_inc cs prog = (cs1,prog1) ==>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) prog1)) =
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND)
       (SND (inline_all cs prog))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_inline_compile_inc_def] THEN
  MP_TAC(ISPEC `inline_all (cs:(num#bvi_exp)spt) prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `p2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[remove_ticks_prog_code_labels; SND]);;

let cache_code_labels_def = cake_def
  `cache_code_labels (cs:(num#bvi_exp)spt) =
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND) (toList cs)))`;;

let lookup_cache_code_labels = prove
 (`!n (cs:(num#bvi_exp)spt) arity body.
     lookup n cs = SOME (arity,body) ==>
     bvi_get_code_labels body SUBSET cache_code_labels cs`,
  REWRITE_TAC[cache_code_labels_def; SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `bvi_get_code_labels body` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(arity:num,body:bvi_exp)` THEN REWRITE_TAC[SND; MEM_toList] THEN
  ASM_MESON_TAC[]);;

let cache_code_labels_insert = prove
 (`!name arity body (cs:(num#bvi_exp)spt).
     cache_code_labels (insert name (arity,body) cs) SUBSET
     bvi_get_code_labels body UNION cache_code_labels cs`,
  REWRITE_TAC[cache_code_labels_def; SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM;
              IN_UNION; MEM_toList; lookup_insert] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `t:num->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:num#bvi_exp` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  UNDISCH_TAC `(if k = name then SOME (arity:num,body:bvi_exp) else lookup k cs) = SOME y` THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"] THEN DISCH_TAC THENL
   [DISJ1_TAC THEN UNDISCH_TAC `(x:num) IN t` THEN
    UNDISCH_TAC `t = bvi_get_code_labels (SND (y:num#bvi_exp))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(arity:num,body:bvi_exp) = y`)) THEN
    REWRITE_TAC[SND] THEN MESON_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `t:num->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:num#bvi_exp` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 [simp] *)
let bvi_mk_tick_get_code_labels = prove
 (`!n e. bvi_get_code_labels (bvi_mk_tick n e) = bvi_get_code_labels e`,
  REWRITE_TAC[bvi_mk_tick_def] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; bvi_get_code_labels_def]);;

let inline_exp_code_labels = prove
 (`(!(cs:(num#bvi_exp)spt) e.
      bvi_get_code_labels (inline_exp cs e) SUBSET
      bvi_get_code_labels e UNION cache_code_labels cs) /\
   (!(cs:(num#bvi_exp)spt) es.
      UNIONS (set_of_list (MAP bvi_get_code_labels (inline_exps cs es))) SUBSET
      UNIONS (set_of_list (MAP bvi_get_code_labels es)) UNION cache_code_labels cs)`,
  SUBGOAL_THEN
   `!(cs:(num#bvi_exp)spt).
      (!e. bvi_get_code_labels (inline_exp cs e) SUBSET
           bvi_get_code_labels e UNION cache_code_labels cs) /\
      (!es. UNIONS (set_of_list (MAP bvi_get_code_labels (inline_exps cs es))) SUBSET
            UNIONS (set_of_list (MAP bvi_get_code_labels es)) UNION cache_code_labels cs) /\
      (!opt h. opt = SOME h ==>
               bvi_get_code_labels (inline_exp cs h) SUBSET
               bvi_get_code_labels h UNION cache_code_labels cs)`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN MATCH_MP_TAC bvi_exp_INDUCT THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[inline_exp_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> try fst (dest_const t) = "bvi_Call" with Failure _ -> false)) w
     then ALL_TAC g
     else (TRY (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                  check (fun th -> is_eq (concl th) && is_var (lhs (concl th))))) THEN
           ASM SET_TAC[]) g) THEN
  CASES_ON `a3:bvi_exp option` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `a:bvi_exp` o check (is_forall o concl)) THEN
    REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  CASES_ON `a1:num option` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CASES_ON `lookup a (cs:(num#bvi_exp)spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `a':num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC(bvi_mk_tick_get_code_labels :: BVLPROPSAUX_BI_LABELS_RWS) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC BVLPROPSAUX_BI_LABELS_RWS THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP lookup_cache_code_labels) THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let inline_all_code_labels = prove
 (`!(cs:(num#bvi_exp)spt) prog.
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (SND (inline_all cs prog))))
     SUBSET UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) prog)) UNION
            cache_code_labels cs`,
  SUBGOAL_THEN
   `!prog (cs:(num#bvi_exp)spt).
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (SND (inline_all cs prog))))
     SUBSET UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) prog)) UNION
            cache_code_labels cs` (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[inline_all_def; SND; MAP; set_of_list; UNIONS_0; EMPTY_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  GEN_TAC THEN REWRITE_TAC[inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `cs1 = if wrapper_ok name arity (inline_exp (cs:(num#bvi_exp)spt) body)
                    then insert name (arity,inline_exp cs body) cs else cs` THEN
  MP_TAC(ISPEC `inline_all (cs1:(num#bvi_exp)spt) t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; SND; o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cs1:(num#bvi_exp)spt`) THEN ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN `cache_code_labels (cs1:(num#bvi_exp)spt) SUBSET
                bvi_get_code_labels body UNION cache_code_labels (cs:(num#bvi_exp)spt)`
    MP_TAC THENL
   [EXPAND_TAC "cs1" THEN COND_CASES_TAC THEN REWRITE_TAC[SUBSET_UNION] THEN
    MP_TAC(ISPECL [`name:num`; `arity:num`; `inline_exp (cs:(num#bvi_exp)spt) body`;
                   `cs:(num#bvi_exp)spt`] cache_code_labels_insert) THEN
    MP_TAC(SPECL [`cs:(num#bvi_exp)spt`; `body:bvi_exp`] (CONJUNCT1 inline_exp_code_labels)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cs:(num#bvi_exp)spt`; `body:bvi_exp`] (CONJUNCT1 inline_exp_code_labels)) THEN
  SET_TAC[]);;

let bvi_inlineProof_compile_prog_code_labels = prove
 (`!prog (cs1:(num#bvi_exp)spt) prog1.
     bvi_inline_compile_prog prog = (cs1,prog1) ==>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) prog1)) SUBSET
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_inline_compile_prog_def] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP compile_inc_code_labels) THEN
  MP_TAC(ISPECL [`LN:(num#bvi_exp)spt`; `prog:(num#num#bvi_exp)list`]
                inline_all_code_labels) THEN
  REWRITE_TAC[cache_code_labels_def; toList_def; toListA_def; MAP; set_of_list;
              UNIONS_0; UNION_EMPTY]);;

let subspt_insert_union_fresh = prove
 (`!(cs:A spt) old name value.
     subspt cs old /\ ~(name IN domain old) ==>
     subspt (insert name value cs) (sptree_union old (insert name value LN))`,
  REWRITE_TAC[subspt_lookup; lookup_insert; lookup_union; GSYM lookup_NONE_domain] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[lookup_rwts] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `lookup x (cs:A spt) = SOME y`)) THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

let inline_all_cache_subspt = prove
 (`!prog (cs:(num#bvi_exp)spt) old final_cache out.
     inline_all cs prog = (final_cache,out) /\ subspt cs old /\
     DISJOINT (set_of_list (MAP FST prog)) (domain old) /\
     ALL_DISTINCT (MAP FST prog) ==>
     subspt final_cache (sptree_union old (fromAList out))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[inline_all_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[fromAList_def; union_LN]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `cs1 = if wrapper_ok name arity (inline_exp (cs:(num#bvi_exp)spt) body)
                    then insert name (arity,inline_exp cs body) cs else cs` THEN
  MP_TAC(ISPEC `inline_all (cs1:(num#bvi_exp)spt) t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; MAP; set_of_list; ALL_DISTINCT; FST] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     is_var (rhs (concl th)) && mem (fst (dest_var (rhs (concl th)))) ["final_cache"; "out"]))) THEN
  REWRITE_TAC[fromAList_def] THEN ONCE_REWRITE_TAC[GSYM union_insert_LN] THEN
  REWRITE_TAC[union_assoc] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `cs1:(num#bvi_exp)spt` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "cs1" THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC subspt_insert_union_fresh THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (name INSERT set_of_list (MAP FST (t:(num#num#bvi_exp)list)))
                            (domain (old:(num#bvi_exp)spt))` THEN SET_TAC[];
      MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC `old:(num#bvi_exp)spt` THEN
      ASM_REWRITE_TAC[subspt_union]];
    REWRITE_TAC[domain_union; domain_insert; domain_def] THEN
    UNDISCH_TAC `DISJOINT (name INSERT set_of_list (MAP FST (t:(num#num#bvi_exp)list)))
                          (domain (old:(num#bvi_exp)spt))` THEN
    UNDISCH_TAC `~MEM name (MAP FST (t:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[]]);;

(* the relation of a source expression to its image under the inlining     *)
(* phase, where c is the transformed target code table; inline is the only *)
(* rule that removes a Call boundary.  OPTREL is registered as monotone   *)
(* for the inductive definition.                                           *)
let () = monotonicity_theorems := OPTREL_MONO :: !monotonicity_theorems;;

let bvi_inlineProof_exp_rel_rules,bvi_inlineProof_exp_rel_ind,
    bvi_inlineProof_exp_rel_cases,bvi_inlineProof_exp_rel_strongind =
  cake_inductive
  `(!(c:(num#bvi_exp)spt) n. bvi_inlineProof_exp_rel c (bvi_Var n) (bvi_Var n)) /\
   (!(c:(num#bvi_exp)spt) loc n.
      bvi_inlineProof_exp_rel c (bvi_Force loc n) (bvi_Force loc n)) /\
   (!(c:(num#bvi_exp)spt) x1 x2 x3 y1 y2 y3.
      bvi_inlineProof_exp_rel c x1 y1 /\ bvi_inlineProof_exp_rel c x2 y2 /\
      bvi_inlineProof_exp_rel c x3 y3 ==>
      bvi_inlineProof_exp_rel c (bvi_If x1 x2 x3) (bvi_If y1 y2 y3)) /\
   (!(c:(num#bvi_exp)spt) xs ys x y.
      ALL2 (bvi_inlineProof_exp_rel c) xs ys /\ bvi_inlineProof_exp_rel c x y ==>
      bvi_inlineProof_exp_rel c (bvi_Let xs x) (bvi_Let ys y)) /\
   (!(c:(num#bvi_exp)spt) x y.
      bvi_inlineProof_exp_rel c x y ==>
      bvi_inlineProof_exp_rel c (bvi_Raise x) (bvi_Raise y)) /\
   (!(c:(num#bvi_exp)spt) x y.
      bvi_inlineProof_exp_rel c x y ==>
      bvi_inlineProof_exp_rel c (bvi_Tick x) (bvi_Tick y)) /\
   (!(c:(num#bvi_exp)spt) op xs ys.
      ALL2 (bvi_inlineProof_exp_rel c) xs ys ==>
      bvi_inlineProof_exp_rel c (bvi_Op op xs) (bvi_Op op ys)) /\
   (!(c:(num#bvi_exp)spt) ticks dest xs ys handler handler1.
      ALL2 (bvi_inlineProof_exp_rel c) xs ys /\
      OPTREL (bvi_inlineProof_exp_rel c) handler handler1 ==>
      bvi_inlineProof_exp_rel c (bvi_Call ticks dest xs handler)
        (bvi_Call ticks dest ys handler1)) /\
   (!(c:(num#bvi_exp)spt) rets ticks dest xs ys x y.
      ALL2 (bvi_inlineProof_exp_rel c) xs ys /\ bvi_inlineProof_exp_rel c x y ==>
      bvi_inlineProof_exp_rel c (LetCall rets ticks dest xs x)
        (LetCall rets ticks dest ys y)) /\
   (!(c:(num#bvi_exp)spt) xs ys.
      ALL2 (bvi_inlineProof_exp_rel c) xs ys ==>
      bvi_inlineProof_exp_rel c (bvi_Return xs) (bvi_Return ys)) /\
   (!(c:(num#bvi_exp)spt) ticks n xs ys arity body.
      ALL2 (bvi_inlineProof_exp_rel c) xs ys /\ lookup n c = SOME (arity,body) /\
      LENGTH ys = arity ==>
      bvi_inlineProof_exp_rel c (bvi_Call ticks (SOME n) xs NONE)
        (bvi_Let ys (bvi_mk_tick (SUC ticks) body)))`;;

let bvi_inlineProof_exp_rel_Var = el 0 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Force = el 1 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_If = el 2 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Let = el 3 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Raise = el 4 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Tick = el 5 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Op = el 6 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Call = el 7 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_LetCall = el 8 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_Return = el 9 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;
let bvi_inlineProof_exp_rel_inline = el 10 (CONJUNCTS bvi_inlineProof_exp_rel_rules);;

(* a local tactic: apply the rule of exp_rel for the shape of the goal *)
let BVLPROPSAUX_BI_RULE_TAC : tactic =
  let rules = CONJUNCTS bvi_inlineProof_exp_rel_rules in
  let imps = filter (fun th -> is_imp (snd (strip_forall (concl th)))) rules in
  FIRST (map MATCH_ACCEPT_TAC rules @ map MATCH_MP_TAC imps);;

let exp_rel_mono = prove
 (`!(c:(num#bvi_exp)spt) x y. bvi_inlineProof_exp_rel c x y ==>
     !c1. subspt c c1 ==> bvi_inlineProof_exp_rel c1 x y`,
  MATCH_MP_TAC bvi_inlineProof_exp_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  BVLPROPSAUX_BI_RULE_TAC THEN TRY (EXISTS_TAC `arity:num`) THEN REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (FIRST_X_ASSUM(MP_TAC o check (fun th -> BVLPROPSAUX_has_const "ALL2" (concl th))) THEN
       MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  TRY (FIRST_X_ASSUM(MP_TAC o check (fun th -> BVLPROPSAUX_has_const "OPTREL" (concl th))) THEN
       MATCH_MP_TAC OPTREL_MONO THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[subspt_lookup]);;

let exp_rel_mono_list = prove
 (`!(c:(num#bvi_exp)spt) c1 xs ys.
     ALL2 (bvi_inlineProof_exp_rel c) xs ys /\ subspt c c1 ==>
     ALL2 (bvi_inlineProof_exp_rel c1) xs ys`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ALL2 (bvi_inlineProof_exp_rel (c:(num#bvi_exp)spt)) xs ys` THEN
  MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[exp_rel_mono]);;

(* HOL4 [local] *)
let exp_rel_evaluate_mono = prove
 (`(!es env (t:(C,FFI)bvi_state) res t1 x y.
      bvi_evaluate (es,env,t) = (res,t1) /\
      bvi_inlineProof_exp_rel (bvi_state_code t) x y ==>
      bvi_inlineProof_exp_rel (bvi_state_code t1) x y) /\
   (!es env (t:(C,FFI)bvi_state) res t1 xs ys.
      bvi_evaluate (es,env,t) = (res,t1) /\
      ALL2 (bvi_inlineProof_exp_rel (bvi_state_code t)) xs ys ==>
      ALL2 (bvi_inlineProof_exp_rel (bvi_state_code t1)) xs ys)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono) THEN
  ASM_MESON_TAC[exp_rel_mono; exp_rel_mono_list]);;

(* HOL4 [simp] *)
let bvi_inlineProof_exp_rel_refl = prove
 (`!(c:(num#bvi_exp)spt) x. bvi_inlineProof_exp_rel c x x`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(!e. bvi_inlineProof_exp_rel (c:(num#bvi_exp)spt) e e) /\
    (!xs. ALL2 (bvi_inlineProof_exp_rel c) xs xs) /\
    (!h. OPTREL (bvi_inlineProof_exp_rel c) h h)` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC bvi_exp_INDUCT THEN REWRITE_TAC[ALL2; OPTREL_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  BVLPROPSAUX_BI_RULE_TAC THEN ASM_REWRITE_TAC[]);;

let inline_call_none_exp_rel = prove
 (`!(cs:(num#bvi_exp)spt) c ticks dest es.
     subspt cs c /\ ALL2 (bvi_inlineProof_exp_rel c) es (inline_exps cs es) ==>
     bvi_inlineProof_exp_rel c (bvi_Call ticks dest es NONE)
       (inline_exp cs (bvi_Call ticks dest es NONE))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[inline_exp_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `dest:num option` THEN CASE_REWRITE_TAC[] THENL
   [MATCH_MP_TAC bvi_inlineProof_exp_rel_Call THEN ASM_REWRITE_TAC[OPTREL_THM]; ALL_TAC] THEN
  CASES_ON `lookup a (cs:(num#bvi_exp)spt)` THEN CASE_REWRITE_TAC[] THENL
   [MATCH_MP_TAC bvi_inlineProof_exp_rel_Call THEN ASM_REWRITE_TAC[OPTREL_THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `a':num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC bvi_inlineProof_exp_rel_inline THEN EXISTS_TAC `arity:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[subspt_lookup];
    MATCH_MP_TAC bvi_inlineProof_exp_rel_Call THEN ASM_REWRITE_TAC[OPTREL_THM]]);;

let inline_exp_rel = prove
 (`!(cs:(num#bvi_exp)spt) c.
     subspt cs c ==>
     (!e. bvi_inlineProof_exp_rel c e (inline_exp cs e)) /\
     (!es. ALL2 (bvi_inlineProof_exp_rel c) es (inline_exps cs es))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!e. bvi_inlineProof_exp_rel c e (inline_exp (cs:(num#bvi_exp)spt) e)) /\
    (!es. ALL2 (bvi_inlineProof_exp_rel c) es (inline_exps cs es)) /\
    (!opt h. opt = SOME h ==> bvi_inlineProof_exp_rel c h (inline_exp cs h))`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC bvi_exp_INDUCT THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]] THEN
  TRY (REWRITE_TAC[inline_exp_def; ALL2] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> try fst (dest_const t) = "bvi_Call" with Failure _ -> false)) w
     then ALL_TAC g
     else (ONCE_REWRITE_TAC[inline_exp_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
           BETA_TAC THEN BVLPROPSAUX_BI_RULE_TAC THEN ASM_REWRITE_TAC[]) g) THEN
  CASES_ON `a3:bvi_exp option` THENL
   [MATCH_MP_TAC inline_call_none_exp_rel THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[inline_exp_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC bvi_inlineProof_exp_rel_Call THEN ASM_REWRITE_TAC[OPTREL_THM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]);;

let evaluate_bvi_mk_tick = prove
 (`!exp env (s:(C,FFI)bvi_state) n.
     bvi_evaluate ([bvi_mk_tick n exp],env,s) =
     if bvi_state_clock s < n then
       (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
     else bvi_evaluate ([exp],env,bvi_dec_clock n s)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[bvi_mk_tick_def] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[ITER; LT; bvi_dec_clock_def; SUB_0] THEN AP_TERM_TAC THEN
    REWRITE_TAC[PAIR_EQ; bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
              bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
  ASM_CASES_TAC `bvi_state_clock (s:(C,FFI)bvi_state) = 0` THEN
  ASM_REWRITE_TAC[LT_0; ARITH_RULE `0 < SUC n`] THEN
  TRY (REWRITE_TAC[PAIR_EQ; bvi_state_component_equality; bvi_state_INFO.ri_accfupds;
                   K_THM] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(c = 0) ==> (c - 1 < n <=> c < SUC n)`;
               ARITH_RULE `c - 1 - n = c - SUC n`]);;

(* a local tactic for evaluate_expand_env (as BVLPROPSAUX_EE_STEP_TAC of   *)
(* bvlProps): split the first evaluation of the original environment,      *)
(* condition or case variable, then simplify with the induction hypotheses *)
let BVLPROPSAUX_BI_EE_STEP_TAC : tactic = fun (asl,w as g) ->
  let env = mk_var("env",`:bvl_v list`) in
  let fw = frees w in
  let ok t = not (vfree_in env t) && subset (frees t) fw in
  let is_ev t = is_comb t && is_const (rator t) &&
                fst(dest_const(rator t)) = "bvi_evaluate" in
  match find_terms (fun t -> is_ev t && ok t) w with
    t::_ ->
      (CASES_ON t THEN
       (fun (asl,w as g) ->
          let eq = find (fun (_,th) -> let c = concl th in is_eq c && lhs c = t) asl in
          let r = lhand (rand (concl (snd eq))) in
          (CASES_ON r THEN FS[]) g)) g
  | [] ->
  match find_terms (fun t -> is_cond t && ok (fst(dest_cond t))) w with
    t::_ ->
      let c = fst(dest_cond t) in
      if can (find_term (fun u -> is_const u &&
                mem (fst (dest_const u)) ["IS_SOME"; "IS_NONE"])) c
      then (ASM_CASES_TAC c THEN ASM_REWRITE_TAC[]) g
      else (ASM_CASES_TAC c THEN FS[]) g
  | [] ->
  match find_terms (fun t -> is_case_app t &&
                       (let _,x,_ = dest_case_app t in is_var x && ok x)) w with
    t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN FS[]) g
  | [] ->
  match find_terms (fun t -> is_case_app t &&
                       (let _,x,_ = dest_case_app t in ok x &&
                          (try fst (dest_const (fst (strip_comb x))) = "bvl_find_code"
                           with Failure _ -> false))) w with
    t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN FS[]) g
  | [] -> failwith "BVLPROPSAUX_BI_EE_STEP_TAC";;

let bvi_inlineProof_evaluate_expand_env = prove
 (`!xs a (s:(C,FFI)bvi_state) env.
     ~(FST (bvi_evaluate (xs,a,s)) = Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate (xs,APPEND a env,s) = bvi_evaluate (xs,a,s)`,
  MATCH_MP_TAC BVLPROPSAUX_bvi_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CHANGED_TAC BVLPROPSAUX_BI_EE_STEP_TAC) THEN
  ASM_SIMP_TAC[EL_APPEND1; LENGTH_APPEND; ARITH_RULE `n < a ==> n < a + b:num`]);;

let bvi_inlineProof_in_cc_def = cake_def
  (CASE_TERM `bvi_inlineProof_in_cc
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) =
     (\(cs,cfg) prog.
        let (cs1,prog1) = inline_all (cs:(num#bvi_exp)spt) prog in
          match cc cfg prog1 with
            NONE -> NONE
          | SOME (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`);;

let bvi_inlineProof_in_co_def = cake_def
  `bvi_inlineProof_in_co (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) =
     (\n. let ((cs,cfg),prog) = co n in
          let (cs1,prog1) = inline_all cs prog in
            (cfg,prog1))`;;

let bvi_inlineProof_in_state_rel_def = cake_def
  `bvi_inlineProof_in_state_rel (s:((num#bvi_exp)spt#C,FFI)bvi_state)
                                (t:(C,FFI)bvi_state) <=>
     bvi_state_refs t = bvi_state_refs s /\
     bvi_state_clock t = bvi_state_clock s /\
     bvi_state_global t = bvi_state_global s /\
     bvi_state_ffi t = bvi_state_ffi s /\
     bvi_state_compile_oracle t = bvi_inlineProof_in_co (bvi_state_compile_oracle s) /\
     subspt (FST (FST (bvi_state_compile_oracle s 0))) (bvi_state_code t) /\
     bvi_state_compile s = bvi_inlineProof_in_cc (bvi_state_compile t) /\
     domain (bvi_state_code t) = domain (bvi_state_code s) /\
     (!k arity exp.
        lookup k (bvi_state_code s) = SOME (arity,exp) ==>
        ?exp1. lookup k (bvi_state_code t) = SOME (arity,exp1) /\
               bvi_inlineProof_exp_rel (bvi_state_code t) exp exp1)`;;

(* HOL4 [local] *)
let in_state_rel_find_code = prove
 (`!(s:((num#bvi_exp)spt#C,FFI)bvi_state) (t:(C,FFI)bvi_state) dest vs args exp.
     bvi_inlineProof_in_state_rel s t /\
     bvl_find_code dest vs (bvi_state_code s) = SOME (args,exp) ==>
     ?exp1. bvl_find_code dest vs (bvi_state_code t) = SOME (args,exp1) /\
            bvi_inlineProof_exp_rel (bvi_state_code t) exp exp1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_inlineProof_in_state_rel_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!loc arity e. lookup loc (bvi_state_code (s:((num#bvi_exp)spt#C,FFI)bvi_state)) =
                    SOME (arity,e) ==>
      ?e2. lookup loc (bvi_state_code (t:(C,FFI)bvi_state)) = SOME (arity,e2) /\
           bvi_inlineProof_exp_rel (bvi_state_code t) e e2` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    BVLPROPSAUX_has_const "bvl_find_code" (concl th))) THEN
  CASES_ON `dest:num option` THEN REWRITE_TAC[bvl_find_code_def] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `LAST (vs:bvl_v list)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `lookup a (bvi_state_code (s:((num#bvi_exp)spt#C,FFI)bvi_state))` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"];
    CASES_ON `lookup a (bvi_state_code (s:((num#bvi_exp)spt#C,FFI)bvi_state))` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"]] THEN
  MP_TAC(ISPEC `a':num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
    `lookup a (bvi_state_code (s:((num#bvi_exp)spt#C,FFI)bvi_state)) = SOME (arity,e)`)) THEN
  STRIP_TAC THEN EXISTS_TAC `e2:bvi_exp` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let inline_all_ALOOKUP = prove
 (`!prog (cs:(num#bvi_exp)spt) old_target final_cache out k wanted_arity wanted_body.
     inline_all cs prog = (final_cache,out) /\ subspt cs old_target /\
     DISJOINT (set_of_list (MAP FST prog)) (domain old_target) /\
     ALL_DISTINCT (MAP FST prog) /\
     ALOOKUP prog k = SOME (wanted_arity,wanted_body) ==>
     ?body1. ALOOKUP out k = SOME (wanted_arity,body1) /\
             bvi_inlineProof_exp_rel (sptree_union old_target (fromAList out)) wanted_body body1`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ALOOKUP_THM; distinctness "option"]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `cs1 = if wrapper_ok name arity (inline_exp (cs:(num#bvi_exp)spt) body)
                    then insert name (arity,inline_exp cs body) cs else cs` THEN
  MP_TAC(ISPEC `inline_all (cs1:(num#bvi_exp)spt) t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; MAP; set_of_list; ALL_DISTINCT; FST; ALOOKUP_THM] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     is_var (rhs (concl th)) && mem (fst (dest_var (rhs (concl th)))) ["final_cache"; "out"]))) THEN
  REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_CASES_TAC `name:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o
      check (fun th -> is_conj (concl th) && is_eq (lhand (concl th)))) THEN
    REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    EXISTS_TAC `inline_exp (cs:(num#bvi_exp)spt) body` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `subspt (cs:(num#bvi_exp)spt)
         (sptree_union old_target (fromAList (CONS (k,arity,inline_exp cs body) prog2)))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC `old_target:(num#bvi_exp)spt` THEN
      ASM_REWRITE_TAC[subspt_union];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o MATCH_MP inline_exp_rel);
    UNDISCH_TAC `(if name = k then SOME (arity:num,body:bvi_exp) else ALOOKUP (t:(num#num#bvi_exp)list) k) =
                  SOME (wanted_arity,wanted_body)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[fromAList_def] THEN ONCE_REWRITE_TAC[GSYM union_insert_LN] THEN
    REWRITE_TAC[union_assoc] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`cs1:(num#bvi_exp)spt`; `cs2:(num#bvi_exp)spt`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "cs1" THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC subspt_insert_union_fresh THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `DISJOINT (name INSERT set_of_list (MAP FST (t:(num#num#bvi_exp)list)))
                              (domain (old_target:(num#bvi_exp)spt))` THEN SET_TAC[];
        MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC `old_target:(num#bvi_exp)spt` THEN
        ASM_REWRITE_TAC[subspt_union]];
      REWRITE_TAC[domain_union; domain_insert; domain_def] THEN
      UNDISCH_TAC `DISJOINT (name INSERT set_of_list (MAP FST (t:(num#num#bvi_exp)list)))
                            (domain (old_target:(num#bvi_exp)spt))` THEN
      UNDISCH_TAC `~MEM name (MAP FST (t:(num#num#bvi_exp)list))` THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[]]]);;

(* HOL4 [local]; the same statement as do_app_cfg_swap of bviProps *)
let do_app_state_swap = prove
 (`!op args (s:(A,FFI)bvi_state) value (s1:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) error.
     ~(op = clos_Install) ==>
     ((bvi_do_app op args s = Rval (value,s1) /\
       domain (bvi_state_code s) SUBSET domain (bvi_state_code t) ==>
       bvi_do_app op args
         (bvi_state_refs_fupd (K (bvi_state_refs s))
           (bvi_state_clock_fupd (K (bvi_state_clock s))
             (bvi_state_global_fupd (K (bvi_state_global s))
               (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) =
       Rval (value,
             bvi_state_refs_fupd (K (bvi_state_refs s1))
               (bvi_state_clock_fupd (K (bvi_state_clock s1))
                 (bvi_state_global_fupd (K (bvi_state_global s1))
                   (bvi_state_ffi_fupd (K (bvi_state_ffi s1)) t))))) /\
      (bvi_do_app op args s = Rerr error /\
       (domain (bvi_state_code t) SUBSET domain (bvi_state_code s) \/
        ~(error = Rabort Rtype_error)) ==>
       bvi_do_app op args
         (bvi_state_refs_fupd (K (bvi_state_refs s))
           (bvi_state_clock_fupd (K (bvi_state_clock s))
             (bvi_state_global_fupd (K (bvi_state_global s))
               (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) = Rerr error))`,
  MATCH_ACCEPT_TAC do_app_cfg_swap);;

(* HOL4 [local] *)
let do_app_state_swap_Rval = prove
 (`!op args (s:(A,FFI)bvi_state) (source_state:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) value.
     ~(op = clos_Install) /\
     bvi_do_app op args s = Rval (value,source_state) /\
     domain (bvi_state_code s) SUBSET domain (bvi_state_code t) ==>
     bvi_do_app op args
       (bvi_state_refs_fupd (K (bvi_state_refs s))
         (bvi_state_clock_fupd (K (bvi_state_clock s))
           (bvi_state_global_fupd (K (bvi_state_global s))
             (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) =
     Rval (value,
           bvi_state_refs_fupd (K (bvi_state_refs source_state))
             (bvi_state_clock_fupd (K (bvi_state_clock source_state))
               (bvi_state_global_fupd (K (bvi_state_global source_state))
                 (bvi_state_ffi_fupd (K (bvi_state_ffi source_state)) t))))`,
  MESON_TAC[do_app_state_swap]);;

(* HOL4 [local] *)
let do_app_state_swap_Rerr = prove
 (`!op args (s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) error.
     ~(op = clos_Install) /\
     bvi_do_app op args s = Rerr error /\
     (domain (bvi_state_code t) SUBSET domain (bvi_state_code s) \/
      ~(error = Rabort Rtype_error)) ==>
     bvi_do_app op args
       (bvi_state_refs_fupd (K (bvi_state_refs s))
         (bvi_state_clock_fupd (K (bvi_state_clock s))
           (bvi_state_global_fupd (K (bvi_state_global s))
             (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) = Rerr error`,
  MESON_TAC[do_app_state_swap]);;

(* HOL4 [local] *)
let inline_all_head_names = prove
 (`!(cs:(num#bvi_exp)spt) name arity body rest final_cache out.
     inline_all cs (CONS (name,arity,body) rest) = (final_cache,out) ==>
     ?tail. out = CONS (name,arity,inline_exp cs body) tail /\
            MAP FST tail = MAP FST rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `cs1 = if wrapper_ok name arity (inline_exp (cs:(num#bvi_exp)spt) body)
                    then insert name (arity,inline_exp cs body) cs else cs` THEN
  MP_TAC(ISPEC `inline_all (cs1:(num#bvi_exp)spt) rest` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog2:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  EXISTS_TAC `prog2:(num#num#bvi_exp)list` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cs1:(num#bvi_exp)spt`; `rest:(num#num#bvi_exp)list`] inline_all_MAP_FST) THEN
  ASM_REWRITE_TAC[SND]);;

(* HOL4 [local] *)
let inline_all_lookup_union = prove
 (`!(cs:(num#bvi_exp)spt) prog final_cache out target source.
     inline_all cs prog = (final_cache,out) /\ subspt cs target /\
     domain target = domain source /\
     (!k arity exp. lookup k source = SOME (arity,exp) ==>
        ?exp1. lookup k target = SOME (arity,exp1) /\
               bvi_inlineProof_exp_rel target exp exp1) /\
     DISJOINT (set_of_list (MAP FST prog)) (domain target) /\
     ALL_DISTINCT (MAP FST prog) ==>
     !k arity exp.
       lookup k (sptree_union source (fromAList prog)) = SOME (arity,exp) ==>
       ?exp1. lookup k (sptree_union target (fromAList out)) = SOME (arity,exp1) /\
              bvi_inlineProof_exp_rel (sptree_union target (fromAList out)) exp exp1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  CASES_ON `lookup k (source:(num#bvi_exp)spt)` THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `lookup k (target:(num#bvi_exp)spt) = NONE` ASSUME_TAC THENL
     [REWRITE_TAC[lookup_NONE_domain] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM lookup_NONE_domain] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC inline_all_ALOOKUP THEN
    MAP_EVERY EXISTS_TAC [`prog:(num#num#bvi_exp)list`; `cs:(num#bvi_exp)spt`;
                          `final_cache:(num#bvi_exp)spt`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[injectivity "option"] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `lookup k (source:(num#bvi_exp)spt) = SOME (arity,exp)`) o
      check (is_forall o concl)) THEN
    STRIP_TAC THEN EXISTS_TAC `exp1:bvi_exp` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_CONJ] o MATCH_MP exp_rel_mono) THEN
    REWRITE_TAC[subspt_union]]);;

(* HOL4 [local] *)
let bvi_inlineProof_do_install_Rerr_type = prove
 (`!args (s:(C,FFI)bvi_state) (err:(E)error_result).
     bvi_do_install args s = Rerr err ==> err = Rabort Rtype_error`,
  MATCH_ACCEPT_TAC bvi_do_install_Rerr_type);;

(* local helpers: the shape of a successful bvi do_install *)
let BVLPROPSAUX_bi_do_install_Rval = prove
 (`!vs (s:(C,FFI)bvi_state) v s'.
     bvi_do_install vs s = (Rval (v,s'):(bvl_v#(C,FFI)bvi_state,E)result) ==>
     ?v1 v2 vl1 vl2 bytes data cfg progs k prog rest cfg'.
       vs = [v1; v2; vl1; vl2] /\ bvl_v_to_bytes v1 = SOME bytes /\
       bvl_v_to_words v2 = SOME data /\
       vl1 = bvl_Number (&(LENGTH bytes)) /\ vl2 = bvl_Number (&(LENGTH data)) /\
       bvi_state_compile_oracle s 0 = (cfg,progs) /\
       DISJOINT (domain (bvi_state_code s)) (set_of_list (MAP FST progs)) /\
       ALL_DISTINCT (MAP FST progs) /\
       bvi_state_compile s cfg progs = SOME (bytes,data,cfg') /\
       progs = CONS (k,prog) rest /\
       FST (bvi_state_compile_oracle s 1) = cfg' /\
       v = bvl_CodePtr k /\
       s' = bvi_state_code_fupd (K (sptree_union (bvi_state_code s) (fromAList progs)))
              (bvi_state_compile_oracle_fupd
                 (K (shift_seq 1 (bvi_state_compile_oracle s))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES; DE_MORGAN_THM]) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[injectivity "option"; injectivity "list"; PAIR_EQ; GSYM CONJ_ASSOC;
                  injectivity "bvl_v"] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_bi_do_install_eq_Rval = prove
 (`!v1 v2 bytes data (s:(C,FFI)bvi_state) cfg k prog rest cfg'.
     bvl_v_to_bytes v1 = SOME bytes /\ bvl_v_to_words v2 = SOME data /\
     bvi_state_compile_oracle s 0 = (cfg,CONS (k,prog) rest) /\
     DISJOINT (domain (bvi_state_code s))
              (set_of_list (MAP FST (CONS (k,prog) rest))) /\
     ALL_DISTINCT (MAP FST (CONS (k,prog) rest)) /\
     bvi_state_compile s cfg (CONS (k,prog) rest) = SOME (bytes,data,cfg') /\
     FST (bvi_state_compile_oracle s 1) = cfg' ==>
     bvi_do_install [v1; v2; bvl_Number (&(LENGTH bytes)); bvl_Number (&(LENGTH data))] s =
       (Rval (bvl_CodePtr k,
              bvi_state_code_fupd
                (K (sptree_union (bvi_state_code s) (fromAList (CONS (k,prog) rest))))
                (bvi_state_compile_oracle_fupd
                   (K (shift_seq 1 (bvi_state_compile_oracle s))) s))
        :(bvl_v#(C,FFI)bvi_state,E)result)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* local helper: a successful inlining compiler call *)
let BVLPROPSAUX_bi_in_cc_SOME = prove
 (`!(cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option)
     (cs:(num#bvi_exp)spt) cfg prog bytes data cfg'.
     bvi_inlineProof_in_cc cc (cs,cfg) prog = SOME (bytes,data,cfg') <=>
     ?cfg1. cc cfg (SND (inline_all cs prog)) = SOME (bytes,data,cfg1) /\
            cfg' = (FST (inline_all cs prog),cfg1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_inlineProof_in_cc_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  MP_TAC(ISPEC `inline_all (cs:(num#bvi_exp)spt) prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog1:(num#num#bvi_exp)list` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`(cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) cfg prog1`,
           `r:(((8)word)list#((64)word)list#C)option`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(((8)word)list#((64)word)list#C)option`
                                       (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MP_TAC(ISPEC `a:((8)word)list#((64)word)list#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:((8)word)list` (X_CHOOSE_THEN
    `r1:((64)word)list#C` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r1:((64)word)list#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((64)word)list` (X_CHOOSE_THEN
    `c1:C` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* local helper: the inlining relation after an Install *)
let BVLPROPSAUX_bi_in_state_rel_install = prove
 (`!(s1:((num#bvi_exp)spt#C,FFI)bvi_state) (t1:(C,FFI)bvi_state) cs cfg progs cs1 prog1.
     bvi_inlineProof_in_state_rel s1 t1 /\
     bvi_state_compile_oracle s1 0 = ((cs,cfg),progs) /\
     inline_all cs progs = (cs1,prog1) /\
     DISJOINT (domain (bvi_state_code s1)) (set_of_list (MAP FST progs)) /\
     ALL_DISTINCT (MAP FST progs) /\
     FST (FST (bvi_state_compile_oracle s1 1)) = cs1 ==>
     bvi_inlineProof_in_state_rel
       (bvi_state_code_fupd (K (sptree_union (bvi_state_code s1) (fromAList progs)))
          (bvi_state_compile_oracle_fupd
             (K (shift_seq 1 (bvi_state_compile_oracle s1))) s1))
       (bvi_state_code_fupd (K (sptree_union (bvi_state_code t1) (fromAList prog1)))
          (bvi_state_compile_oracle_fupd
             (K (shift_seq 1 (bvi_state_compile_oracle t1))) t1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_inlineProof_in_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "bvi_inlineProof_in_state_rel" (concl th))) THEN
  SUBGOAL_THEN `MAP FST (prog1:(num#num#bvi_exp)list) =
                MAP FST (progs:(num#num#bvi_exp)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cs:(num#bvi_exp)spt`; `progs:(num#num#bvi_exp)list`]
                  inline_all_MAP_FST) THEN ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `subspt (cs:(num#bvi_exp)spt) (bvi_state_code (t1:(C,FFI)bvi_state))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `subspt (FST (FST (bvi_state_compile_oracle
       (s1:((num#bvi_exp)spt#C,FFI)bvi_state) 0))) (bvi_state_code (t1:(C,FFI)bvi_state))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (set_of_list (MAP FST (progs:(num#num#bvi_exp)list)))
                         (domain (bvi_state_code (t1:(C,FFI)bvi_state)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_inlineProof_in_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[shift_seq_def; FUN_EQ_THM; bvi_inlineProof_in_co_def];
    REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC inline_all_cache_subspt THEN
    MAP_EVERY EXISTS_TAC [`progs:(num#num#bvi_exp)list`; `cs:(num#bvi_exp)spt`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[domain_union; domain_fromAList] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC inline_all_lookup_union THEN
    MAP_EVERY EXISTS_TAC [`cs:(num#bvi_exp)spt`; `cs1:(num#bvi_exp)spt`] THEN
    ASM_REWRITE_TAC[]]);;

(* local tactic: substitute the assumptions var = t for the given names *)
let BVLPROPSAUX_BI_SUBST_VAR_TAC (names:string list) : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let l = lhs(concl th) in
    if is_var l && mem (fst(dest_var l)) names then SUBST_ALL_TAC th
    else failwith "BVLPROPSAUX_BI_SUBST_VAR_TAC"));;

(* local helper: a successful Install under the inlining relation *)
let BVLPROPSAUX_bi_in_do_install = prove
 (`!vs (s1:((num#bvi_exp)spt#C,FFI)bvi_state) (t1:(C,FFI)bvi_state) v s2.
     bvi_inlineProof_in_state_rel s1 t1 /\
     bvi_do_install vs s1 =
       (Rval (v,s2):(bvl_v#((num#bvi_exp)spt#C,FFI)bvi_state,E)result) ==>
     ?t2. bvi_inlineProof_in_state_rel s2 t2 /\
          bvi_do_install vs t1 = (Rval (v,t2):(bvl_v#(C,FFI)bvi_state,E)result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_bi_do_install_Rval) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v1:bvl_v`; `v2:bvl_v`; `vl1:bvl_v`; `vl2:bvl_v`;
    `bytes:((8)word)list`; `data:((64)word)list`;
    `csc:(num#bvi_exp)spt#C`; `progs:(num#num#bvi_exp)list`; `k:num`; `prog:num#bvi_exp`;
    `rest:(num#num#bvi_exp)list`; `cfg':(num#bvi_exp)spt#C`] THEN
  STRIP_TAC THEN BVLPROPSAUX_BI_SUBST_VAR_TAC ["vs"; "progs"; "v"; "s2"; "vl1"; "vl2"] THEN
  MP_TAC(ISPEC `csc:(num#bvi_exp)spt#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(num#bvi_exp)spt` (X_CHOOSE_THEN `cfg:C` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `prog:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_inlineProof_in_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "bvi_inlineProof_in_state_rel" (concl th))) THEN
  MP_TAC(ISPEC `inline_all (cs:(num#bvi_exp)spt) (CONS (k,arity,body) rest)`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog1:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `vs1:(num#num#bvi_exp)list` STRIP_ASSUME_TAC o
              MATCH_MP inline_all_head_names) THEN
  BVLPROPSAUX_BI_SUBST_VAR_TAC ["prog1"] THEN
  UNDISCH_TAC `bvi_state_compile (s1:((num#bvi_exp)spt#C,FFI)bvi_state) (cs,cfg)
                 (CONS (k,arity,body) rest) = SOME (bytes,data,cfg')` THEN
  ASM_REWRITE_TAC[BVLPROPSAUX_bi_in_cc_SOME; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg1:C` STRIP_ASSUME_TAC) THEN
  BVLPROPSAUX_BI_SUBST_VAR_TAC ["cfg'"] THEN
  SUBGOAL_THEN `FST (bvi_state_compile_oracle (t1:(C,FFI)bvi_state) 1) = cfg1`
    ASSUME_TAC THENL
   [MP_TAC(ISPEC `bvi_state_compile_oracle (s1:((num#bvi_exp)spt#C,FFI)bvi_state) 1`
                 PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1p:(num#bvi_exp)spt#C` (X_CHOOSE_THEN
      `pr1:(num#num#bvi_exp)list` ASSUME_TAC)) THEN
    SUBGOAL_THEN `c1p = (cs1:(num#bvi_exp)spt,cfg1:C)` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[FST]; ALL_TAC] THEN
    ASM_REWRITE_TAC[bvi_inlineProof_in_co_def] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `inline_all (cs1:(num#bvi_exp)spt) pr1` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:(num#bvi_exp)spt` (X_CHOOSE_THEN
      `x2:(num#num#bvi_exp)list` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP FST (CONS (k:num,arity:num,inline_exp (cs:(num#bvi_exp)spt) body) vs1) =
                MAP FST (CONS (k,arity,body:bvi_exp) rest)` ASSUME_TAC THENL
   [REWRITE_TAC[MAP; FST] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v1:bvl_v`; `v2:bvl_v`; `bytes:((8)word)list`; `data:((64)word)list`;
                 `t1:(C,FFI)bvi_state`; `cfg:C`; `k:num`;
                 `(arity:num,inline_exp (cs:(num#bvi_exp)spt) body)`;
                 `vs1:(num#num#bvi_exp)list`; `cfg1:C`]
     (INST_TYPE [`:E`,`:E`] BVLPROPSAUX_bi_do_install_eq_Rval)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REWRITE_TAC[bvi_inlineProof_in_co_def] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  MATCH_MP_TAC BVLPROPSAUX_bi_in_state_rel_install THEN
  MAP_EVERY EXISTS_TAC [`cs:(num#bvi_exp)spt`; `cfg:C`; `cs1:(num#bvi_exp)spt`] THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 [local] *)
let in_state_rel_do_install = prove
 (CASE_TERM `!(s1:((num#bvi_exp)spt#C,FFI)bvi_state) (t1:(C,FFI)bvi_state) a.
    bvi_inlineProof_in_state_rel s1 t1 ==>
    match (bvi_do_install a s1:(bvl_v#((num#bvi_exp)spt#C,FFI)bvi_state,E)result) with
      Rerr err -> (~(err = Rabort Rtype_error) ==>
                   bvi_do_install a t1 = (Rerr err:(bvl_v#(C,FFI)bvi_state,E)result))
    | Rval (v,s2) -> ?t2. bvi_inlineProof_in_state_rel s2 t2 /\
                          bvi_do_install a t1 = (Rval (v,t2):(bvl_v#(C,FFI)bvi_state,E)result)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `bvi_do_install a (s1:((num#bvi_exp)spt#C,FFI)bvi_state):
                  (bvl_v#((num#bvi_exp)spt#C,FFI)bvi_state,E)result` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `a':bvl_v#((num#bvi_exp)spt#C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN
      `s2:((num#bvi_exp)spt#C,FFI)bvi_state` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN MATCH_MP_TAC BVLPROPSAUX_bi_in_do_install THEN
    EXISTS_TAC `s1:((num#bvi_exp)spt#C,FFI)bvi_state` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP bvi_do_install_Rerr_type) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* HOL4 [local] in_do_app_lemma *)
let bvi_inlineProof_in_do_app_lemma = prove
 (CASE_TERM `!op a (s1:((num#bvi_exp)spt#C,FFI)bvi_state) (t1:(C,FFI)bvi_state).
    bvi_inlineProof_in_state_rel s1 t1 ==>
    match bvi_do_app op a s1 with
      Rerr err -> (~(err = Rabort Rtype_error) ==> bvi_do_app op a t1 = Rerr err)
    | Rval (v,s2) -> ?t2. bvi_inlineProof_in_state_rel s2 t2 /\
                          bvi_do_app op a t1 = Rval (v,t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[bvi_do_app_def] THEN
    MATCH_MP_TAC in_state_rel_do_install THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_inlineProof_in_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "bvi_inlineProof_in_state_rel" (concl th))) THEN
  SUBGOAL_THEN
   `bvi_state_refs_fupd (K (bvi_state_refs (s1:((num#bvi_exp)spt#C,FFI)bvi_state)))
      (bvi_state_clock_fupd (K (bvi_state_clock s1))
        (bvi_state_global_fupd (K (bvi_state_global s1))
          (bvi_state_ffi_fupd (K (bvi_state_ffi s1)) (t1:(C,FFI)bvi_state)))) = t1`
    ASSUME_TAC THENL
   [REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_do_app op a (s1:((num#bvi_exp)spt#C,FFI)bvi_state)` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `a':bvl_v#((num#bvi_exp)spt#C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN
      `s2:((num#bvi_exp)spt#C,FFI)bvi_state` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:((num#bvi_exp)spt#C,FFI)bvi_state`;
                   `s2:((num#bvi_exp)spt#C,FFI)bvi_state`; `t1:(C,FFI)bvi_state`;
                   `v:bvl_v`] do_app_state_swap_Rval) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
    FIRST_ASSUM(fun th ->
      if is_eq (concl th) && BVLPROPSAUX_has_const "bvi_do_app" (concl th)
      then STRIP_ASSUME_TAC (MATCH_MP BVLPROPSAUX_bvi_do_app_consts
                              (CONJ th (ASSUME `~(op = clos_Install)`)))
      else NO_TAC) THEN
    REWRITE_TAC[bvi_inlineProof_in_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:((num#bvi_exp)spt#C,FFI)bvi_state`;
                   `t1:(C,FFI)bvi_state`; `a':(exn_or_ret)error_result`]
                  do_app_state_swap_Rerr) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* HOL4 [local,simp] exp_rel_inv (the free variables are quantified) *)
let exp_rel_inv = prove
 (`(!(c:(num#bvi_exp)spt) n y.
      bvi_inlineProof_exp_rel c (bvi_Var n) y <=> y = bvi_Var n) /\
   (!(c:(num#bvi_exp)spt) loc n y.
      bvi_inlineProof_exp_rel c (bvi_Force loc n) y <=> y = bvi_Force loc n) /\
   (!(c:(num#bvi_exp)spt) x1 x2 x3 y.
      bvi_inlineProof_exp_rel c (bvi_If x1 x2 x3) y <=>
      ?y1 y2 y3. y = bvi_If y1 y2 y3 /\ bvi_inlineProof_exp_rel c x1 y1 /\
                 bvi_inlineProof_exp_rel c x2 y2 /\ bvi_inlineProof_exp_rel c x3 y3) /\
   (!(c:(num#bvi_exp)spt) xs x y.
      bvi_inlineProof_exp_rel c (bvi_Let xs x) y <=>
      ?ys y1. y = bvi_Let ys y1 /\ ALL2 (bvi_inlineProof_exp_rel c) xs ys /\
              bvi_inlineProof_exp_rel c x y1) /\
   (!(c:(num#bvi_exp)spt) x y.
      bvi_inlineProof_exp_rel c (bvi_Raise x) y <=>
      ?y1. y = bvi_Raise y1 /\ bvi_inlineProof_exp_rel c x y1) /\
   (!(c:(num#bvi_exp)spt) x y.
      bvi_inlineProof_exp_rel c (bvi_Tick x) y <=>
      ?y1. y = bvi_Tick y1 /\ bvi_inlineProof_exp_rel c x y1) /\
   (!(c:(num#bvi_exp)spt) op xs y.
      bvi_inlineProof_exp_rel c (bvi_Op op xs) y <=>
      ?ys. y = bvi_Op op ys /\ ALL2 (bvi_inlineProof_exp_rel c) xs ys) /\
   (!(c:(num#bvi_exp)spt) xs y.
      bvi_inlineProof_exp_rel c (bvi_Return xs) y <=>
      ?ys. y = bvi_Return ys /\ ALL2 (bvi_inlineProof_exp_rel c) xs ys) /\
   (!(c:(num#bvi_exp)spt) rets ticks target xs x y.
      bvi_inlineProof_exp_rel c (LetCall rets ticks target xs x) y <=>
      ?ys y1. y = LetCall rets ticks target ys y1 /\
              ALL2 (bvi_inlineProof_exp_rel c) xs ys /\ bvi_inlineProof_exp_rel c x y1) /\
   (!(c:(num#bvi_exp)spt) ticks dest xs handler y.
      bvi_inlineProof_exp_rel c (bvi_Call ticks dest xs handler) y <=>
      (?ys handler1. y = bvi_Call ticks dest ys handler1 /\
                     ALL2 (bvi_inlineProof_exp_rel c) xs ys /\
                     OPTREL (bvi_inlineProof_exp_rel c) handler handler1) \/
      (?n ys arity body.
         dest = SOME n /\ handler = NONE /\
         y = bvi_Let ys (bvi_mk_tick (SUC ticks) body) /\
         ALL2 (bvi_inlineProof_exp_rel c) xs ys /\ lookup n c = SOME (arity,body) /\
         LENGTH ys = arity))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [bvi_inlineProof_exp_rel_cases] THEN
  REWRITE_TAC(BVLPROPSAUX_both (distinctness "bvi_exp") @ [injectivity "bvi_exp"]) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[] THEN TRY (MESON_TAC[]));;

(* HOL4 [local] *)
let evaluate_inlined_call = prove
 (`!n (t:(C,FFI)bvi_state) ys body ticks env.
     lookup n (bvi_state_code t) = SOME (LENGTH ys,body) /\
     ~(FST (bvi_evaluate ([bvi_Call ticks (SOME n) ys NONE],env,t)) =
       Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate ([bvi_Let ys (bvi_mk_tick (SUC ticks) body)],env,t) =
     bvi_evaluate ([bvi_Call ticks (SOME n) ys NONE],env,t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC[bvi_evaluate_def] THEN
   REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF] THEN
   MP_TAC(ISPEC `bvi_evaluate (ys,env,t:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(C,FFI)bvi_state`
     ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[evaluate_bvi_mk_tick] THEN
  SUBGOAL_THEN `bvl_find_code (SOME n) a (bvi_state_code (s1:(C,FFI)bvi_state)) =
                 SOME (a,body)` SUBST1_TAC THENL
   [REWRITE_TAC[bvl_find_code_def] THEN
    SUBGOAL_THEN `lookup n (bvi_state_code (s1:(C,FFI)bvi_state)) =
                  SOME (LENGTH (ys:bvi_exp list),body)` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_code_mono o
        check (fun th -> is_eq (concl th) && BVLPROPSAUX_has_const "bvi_evaluate" (concl th))) THEN
      REWRITE_TAC[subspt_lookup] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP bvi_evaluate_IMP_LENGTH o
      check (fun th -> is_eq (concl th) && BVLPROPSAUX_has_const "bvi_evaluate" (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD1] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_evaluate ([body],a,bvi_dec_clock (ticks + 1) (s1:(C,FFI)bvi_state))`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:bvi_result` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):bvi_result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[FST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`[body:bvi_exp]`; `a:bvl_v list`;
                 `bvi_dec_clock (ticks + 1) (s1:(C,FFI)bvi_state)`; `env:bvl_v list`]
                bvi_inlineProof_evaluate_expand_env) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  CASES_ON `r2:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN
  (fun (asl,w as g) ->
     let v = find_term (fun t -> is_var t && type_of t = `:(exn_or_ret)error_result`) w in
     CASES_ON v g) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN
  TRY ((fun (asl,w as g) ->
          let v = find_term (fun t -> is_var t && type_of t = `:exn_or_ret`) w in
          CASES_ON v g) THEN
       CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC(FST :: BVLPROPSAUX_bvi_eval_simps));;

(* local helpers for evaluate_inline: the clock updates *)
let BVLPROPSAUX_bi_in_state_rel_dec_clock = prove
 (`!(s:((num#bvi_exp)spt#C,FFI)bvi_state) (t:(C,FFI)bvi_state) n.
     bvi_inlineProof_in_state_rel s t ==>
     bvi_inlineProof_in_state_rel (bvi_dec_clock n s) (bvi_dec_clock n t)`,
  REWRITE_TAC[bvi_inlineProof_in_state_rel_def; bvi_dec_clock_def;
              bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_bi_in_state_rel_clock0 = prove
 (`!(s:((num#bvi_exp)spt#C,FFI)bvi_state) (t:(C,FFI)bvi_state).
     bvi_inlineProof_in_state_rel s t ==>
     bvi_inlineProof_in_state_rel (bvi_state_clock_fupd (K 0) s)
                                  (bvi_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[bvi_inlineProof_in_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* local tactics for evaluate_inline: invert exp_rel, split the source     *)
(* evaluation, apply the induction hypotheses to the source                *)
(* sub-evaluations, and compute the target evaluation                      *)
let BVLPROPSAUX_bi_src_ty = `:((num#bvi_exp)spt#C,FFI)bvi_state`;;

let BVLPROPSAUX_bi_head (t:term) =
  try fst (dest_const (fst (strip_comb t))) with Failure _ -> "";;

let BVLPROPSAUX_bi_is_ev (t:term) =
  is_comb t && is_const (rator t) && fst (dest_const (rator t)) = "bvi_evaluate";;

let BVLPROPSAUX_bi_ev_state (t:term) = snd (dest_pair (snd (dest_pair (rand t))));;

let BVLPROPSAUX_bi_is_src_ev (t:term) =
  is_eq t && BVLPROPSAUX_bi_is_ev (lhs t) &&
  type_of (BVLPROPSAUX_bi_ev_state (lhs t)) = BVLPROPSAUX_bi_src_ty;;

let BVLPROPSAUX_bi_is_tgt_ev (t:term) =
  is_eq t && BVLPROPSAUX_bi_is_ev (lhs t) &&
  not (type_of (BVLPROPSAUX_bi_ev_state (lhs t)) = BVLPROPSAUX_bi_src_ty);;

let BVLPROPSAUX_bi_is_rel (t:term) = BVLPROPSAUX_bi_head t = "bvi_inlineProof_in_state_rel";;

(* STRIP_ASSUME_TAC with every bound variable renamed to a fresh name *)
let BVLPROPSAUX_BI_FRESH_STRIP_TAC (th:thm) : tactic = fun (asl,w as g) ->
  let used = ref (map (fst o dest_var)
                    (freesl (w :: concl th :: hyp th @
                             flat (map (fun (_,a) -> concl a :: hyp a) asl)))) in
  let rec fresh n = if mem n !used then fresh (n^"'") else (used := n :: !used; n) in
  let rec go t = match t with
      Abs(v,b) -> let n,ty = dest_var v in
                  let n' = fresh n in
                  let v' = mk_var(n',ty) in
                  let b' = if n' = n then b else vsubst [v',v] b in
                  mk_abs(v',go b')
    | Comb(a,b) -> let a' = go a in mk_comb(a',go b)
    | _ -> t in
  let c = concl th in
  let c' = go c in
  STRIP_ASSUME_TAC (EQ_MP (ALPHA c c') th) g;;

let BVLPROPSAUX_BI_INV_TAC : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_BI_FRESH_STRIP_TAC o REWRITE_RULE[LIST_REL_NIL; exp_rel_inv] o
    ONCE_REWRITE_RULE[LIST_REL_CONS1] o
    check (fun th -> let c = concl th in BVLPROPSAUX_bi_head c = "ALL2" &&
             (let _,args = strip_comb c in not (is_var (el 1 args))))) THEN
  TRY RVEQ_TAC;;

let BVLPROPSAUX_BI_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_BI_FRESH_STRIP_TAC o REWRITE_RULE BVLPROPSAUX_bvi_eval_case_eqs o
     BETA_RULE o REWRITE_RULE[LET_DEF; LET_END_DEF; IS_NONE_DEF; IS_SOME_DEF] o
     PURE_ONCE_REWRITE_RULE[bvi_evaluate_def] o
     check (fun th -> let c = concl th in BVLPROPSAUX_bi_is_src_ev c &&
            not (is_var (fst (dest_pair (rand (lhs c))))))) THEN
  TRY RVEQ_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC;;

let rec BVLPROPSAUX_BI_UNDER_FORALL_CONV (conv:conv) (tm:term) =
  if is_forall tm then BINDER_CONV (BVLPROPSAUX_BI_UNDER_FORALL_CONV conv) tm else conv tm;;

let BVLPROPSAUX_bi_is_main (t:term) =
  let vs,b = strip_forall t in
  length vs >= 4 && is_imp b && is_conj (lhand b) &&
  BVLPROPSAUX_bi_is_rel (lhand (lhand b));;

let rec BVLPROPSAUX_bi_discharge (asms:thm list) (depth:int) (th:thm) =
  if BVLPROPSAUX_bi_is_main (concl th) then [th]
  else if depth = 0 then []
  else
    let th' = try CONV_RULE (BVLPROPSAUX_BI_UNDER_FORALL_CONV (REWR_CONV IMP_CONJ)) th
              with Failure _ -> th in
    let rs = mapfilter (fun a -> MATCH_MP th' a) asms in
    let rs = if rs <> [] then rs else
      (try let c = concl th' in
           if is_imp c then
             [MP th' (EQT_ELIM (REWRITE_CONV [IS_SOME_DEF; IS_NONE_DEF] (lhand c)))]
           else []
       with Failure _ -> []) in
    let rs = if rs <> [] then rs else
      (try let th'' = REWRITE_RULE[injectivity "option"; FORALL_UNWIND_THM1;
                                   FORALL_UNWIND_THM2; IS_SOME_DEF; IS_NONE_DEF] th' in
           if concl th'' = concl th' then [] else [th'']
       with Failure _ -> []) in
    flat (map (BVLPROPSAUX_bi_discharge asms (depth - 1)) rs);;

let BVLPROPSAUX_bi_rels (asl:(string*thm) list) =
  filter (fun th -> BVLPROPSAUX_bi_is_rel (concl th)) (map snd asl);;

let BVLPROPSAUX_bi_src_of (r:thm) = rand (rator (concl r));;

let BVLPROPSAUX_BI_DEC_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = BVLPROPSAUX_bi_rels asl in
  let src_of = BVLPROPSAUX_bi_src_of in
  let sts = mapfilter (fun th -> let c = concl th in
              if BVLPROPSAUX_bi_is_src_ev c then BVLPROPSAUX_bi_ev_state (lhs c)
              else failwith "") asms in
  let tac st =
    if exists (fun r -> src_of r = st) rels then failwith "have" else
    let f,args = strip_comb st in
    if not (is_const f && fst (dest_const f) = "bvi_dec_clock") then failwith "dec" else
    let n = hd args and s0 = hd (tl args) in
    let r = find (fun r -> src_of r = s0) rels in
    ASSUME_TAC (SPEC n (MATCH_MP BVLPROPSAUX_bi_in_state_rel_dec_clock r)) in
  EVERY (mapfilter tac (setify sts)) g;;

let BVLPROPSAUX_BI_FC_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = BVLPROPSAUX_bi_rels asl in
  let src_of = BVLPROPSAUX_bi_src_of in
  let fc_parts th = let c = concl th in
    if is_eq c && BVLPROPSAUX_bi_head (lhs c) = "bvl_find_code"
    then strip_comb (lhs c) else failwith "fc" in
  let fcs = filter (fun th -> can fc_parts th &&
              (let _,args = fc_parts th in
               type_of (rand (el 2 args)) = BVLPROPSAUX_bi_src_ty)) asms in
  let tac fc =
    let _,args = fc_parts fc in
    let st = rand (el 2 args) in
    let r = find (fun r -> src_of r = st) rels in
    let tst = rand (concl r) in
    if exists (fun th -> can fc_parts th &&
                 (let _,args' = fc_parts th in el 0 args' = el 0 args &&
                    el 1 args' = el 1 args && rand (el 2 args') = tst)) asms
    then failwith "have" else
    BVLPROPSAUX_BI_FRESH_STRIP_TAC (MATCH_MP in_state_rel_find_code (CONJ r fc)) in
  EVERY (mapfilter tac fcs) g;;

let BVLPROPSAUX_BI_APP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = BVLPROPSAUX_bi_rels asl in
  let src_of = BVLPROPSAUX_bi_src_of in
  let app_parts th = let c = concl th in
    if is_eq c && BVLPROPSAUX_bi_head (lhs c) = "bvi_do_app"
    then strip_comb (lhs c) else failwith "app" in
  let apps = filter (fun th -> can app_parts th &&
               (let _,args = app_parts th in type_of (el 2 args) = BVLPROPSAUX_bi_src_ty))
               asms in
  let tac ap =
    let _,args = app_parts ap in
    let st = el 2 args in
    let r = find (fun r -> src_of r = st) rels in
    let tst = rand (concl r) in
    if exists (fun th -> can app_parts th &&
                 (let _,args' = app_parts th in el 0 args' = el 0 args &&
                    el 1 args' = el 1 args && el 2 args' = tst)) asms
    then failwith "have" else
    let th = MATCH_MP (SPECL [el 0 args; el 1 args; st; tst]
                         bvi_inlineProof_in_do_app_lemma) r in
    let th = CASE_REWRITE_RULE[] (REWRITE_RULE[ap] th) in
    if is_imp (concl th) then
      MP_TAC th THEN ANTS_TAC THENL
       [REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_REWRITE_TAC BVLPROPSAUX_bvi_eval_simps;
        DISCH_TAC]
    else BVLPROPSAUX_BI_FRESH_STRIP_TAC th in
  EVERY (mapfilter tac apps) g;;

let BVLPROPSAUX_BI_IH1_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let ihs = filter (fun th -> let c = concl th in (is_forall c || is_imp c) &&
              BVLPROPSAUX_has_const "bvi_inlineProof_in_state_rel" c &&
              BVLPROPSAUX_has_const "bvi_evaluate" c) asms in
  let mains = flat (map (BVLPROPSAUX_bi_discharge asms 6) ihs) in
  let rels = BVLPROPSAUX_bi_rels asl in
  let src_of = BVLPROPSAUX_bi_src_of in
  let processed st = exists (fun r -> src_of r = st) rels in
  let evs = filter (fun th -> BVLPROPSAUX_bi_is_src_ev (concl th)) asms in
  let tevs = filter (fun th -> BVLPROPSAUX_bi_is_tgt_ev (concl th)) asms in
  let tmonos = mapfilter (MATCH_MP evaluate_code_mono) tevs in
  let erels1 = filter (fun th ->
                 BVLPROPSAUX_bi_head (concl th) = "bvi_inlineProof_exp_rel") asms in
  let erelsl = filter (fun th -> BVLPROPSAUX_bi_head (concl th) = "ALL2") asms in
  let code_c = `bvi_state_code:(C,FFI)bvi_state->(num#bvi_exp)spt` in
  let try_main m =
    let _,b = strip_forall (concl m) in
    let cs = conjuncts (lhand b) in
    let rel_p = el 0 cs and ev_p = el 2 cs in
    let evl = lhs ev_p in
    let e = find (fun e -> lhs (concl e) = evl) evs in
    let r_tm,s'_tm = dest_pair (rhs (concl e)) in
    if processed s'_tm then failwith "processed" else
    let st = rand (rator rel_p) in
    let rel = find (fun r -> src_of r = st) rels in
    let t_tm = rand (concl rel) in
    let xs_tm = fst (dest_pair (rand evl)) in
    let code_t = mk_comb(code_c, t_tm) in
    let single_x =
      try let h,tl = dest_cons xs_tm in
          if tl = `[]:bvi_exp list` then Some h else None
      with Failure _ -> None in
    let er, ys_tm, single =
      match single_x with
        Some x ->
          (try let er = find (fun er -> el 1 (snd (strip_comb (concl er))) = x) erels1 in
               er, mk_list([el 2 (snd (strip_comb (concl er)))], `:bvi_exp`), true
           with Failure _ ->
               let er = find (fun er -> el 1 (snd (strip_comb (concl er))) = xs_tm) erelsl in
               er, el 2 (snd (strip_comb (concl er))), false)
      | None ->
          let er = find (fun er -> el 1 (snd (strip_comb (concl er))) = xs_tm) erelsl in
          er, el 2 (snd (strip_comb (concl er))), false in
    let c_tm = if single then el 0 (snd (strip_comb (concl er)))
               else rand (el 0 (snd (strip_comb (concl er)))) in
    let inst = SPECL [r_tm; s'_tm; t_tm; ys_tm] m in
    let sub_tm = mk_comb(mk_comb(`subspt:(num#bvi_exp)spt->(num#bvi_exp)spt->bool`, c_tm),
                         code_t) in
    let erel_tac =
      SUBGOAL_THEN sub_tm (fun sth ->
        if single then
          REWRITE_TAC[ALL2] THEN ACCEPT_TAC (MP (SPEC code_t (MATCH_MP exp_rel_mono er)) sth)
        else ACCEPT_TAC (MATCH_MP exp_rel_mono_list (CONJ er sth))) THEN
      MAP_EVERY MP_TAC tmonos THEN
      REWRITE_TAC[bvi_dec_clock_code; bvi_state_INFO.ri_accfupds; K_THM] THEN
      MESON_TAC[GEN_ALL subspt_trans; subspt_refl] in
    MP_TAC inst THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ACCEPT_TAC rel;
        erel_tac;
        ACCEPT_TAC e;
        REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_REWRITE_TAC BVLPROPSAUX_bvi_eval_simps];
      DISCH_THEN BVLPROPSAUX_BI_FRESH_STRIP_TAC] in
  let tacs = mapfilter try_main mains in
  if tacs = [] then failwith "BVLPROPSAUX_BI_IH1_TAC" else hd tacs g;;

(* the handler relation: split OPTREL facts with a known first argument; *)
(* for an unknown one, the handlers agree on IS_SOME                       *)
let BVLPROPSAUX_bi_OPTREL_IS_SOME = prove
 (`!(R:A->B->bool) h h1. OPTREL R h h1 ==> (IS_SOME h1 <=> IS_SOME h)`,
  REWRITE_TAC[OPTREL_DEF] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF]);;

let BVLPROPSAUX_BI_OPT_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let opts = filter (fun th -> BVLPROPSAUX_bi_head (concl th) = "OPTREL") asms in
  let tac th =
    let _,args = strip_comb (concl th) in
    let h = el 1 args and h1 = el 2 args in
    if is_var h then
      let eq = MATCH_MP BVLPROPSAUX_bi_OPTREL_IS_SOME th in
      if exists (fun a -> concl a = concl eq) asms then failwith "have" else ASSUME_TAC eq
    else if is_var h1 then
      BVLPROPSAUX_BI_FRESH_STRIP_TAC (REWRITE_RULE[OPTREL_SOME; OPTREL_NONE] th) THEN
      TRY RVEQ_TAC
    else failwith "done" in
  EVERY (mapfilter tac opts) g;;

let BVLPROPSAUX_BI_PREP_TAC : tactic =
  BVLPROPSAUX_BI_OPT_TAC THEN
  BVLPROPSAUX_BI_DEC_TAC THEN BVLPROPSAUX_BI_FC_TAC THEN BVLPROPSAUX_BI_APP_TAC;;

let BVLPROPSAUX_BI_IH_TAC : tactic =
  REPEAT (BVLPROPSAUX_BI_PREP_TAC THEN BVLPROPSAUX_BI_IH1_TAC) THEN
  BVLPROPSAUX_BI_PREP_TAC;;

let BVLPROPSAUX_BI_FIN0_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let simple = filter (fun th -> not (is_imp (snd (strip_forall (concl th))))) asms in
  let rels = BVLPROPSAUX_bi_rels asl in
  let is_st_eq c = let t = concl c in is_eq t &&
    (try mem (fst (dest_const (rator (lhs t))))
           ["bvi_state_clock"; "bvi_state_refs"; "bvi_state_global"; "bvi_state_ffi"]
     with Failure _ -> false) in
  let st_eqs = flat (map (fun r -> filter is_st_eq
      (CONJUNCTS (REWRITE_RULE[bvi_inlineProof_in_state_rel_def] r))) rels) in
  let rws = st_eqs @ simple @ BVLPROPSAUX_bvi_eval_simps in
  (FIRST [CHANGED_TAC (ONCE_REWRITE_TAC[bvi_evaluate_def]);
          ONCE_REWRITE_TAC[bvi_evaluate_CONS]] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; IS_NONE_DEF; IS_SOME_DEF] THEN BETA_TAC THEN
   REPEAT (CHANGED_TAC (REWRITE_TAC rws THEN CASE_REWRITE_TAC[])) THEN
   REWRITE_TAC[PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
   REWRITE_TAC rws THEN
   TRY (MATCH_MP_TAC BVLPROPSAUX_bi_in_state_rel_clock0 THEN REWRITE_TAC rws)) g;;

let BVLPROPSAUX_BI_FIN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF; IS_NONE_DEF]) THEN BVLPROPSAUX_BI_FIN0_TAC;;

(* the inlined call evaluates like the call it replaces *)
let BVLPROPSAUX_bi_inline_goal = prove
 (`!n ticks ys body env (t:(C,FFI)bvi_state) res P.
     lookup n (bvi_state_code t) = SOME (LENGTH ys,body) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     (?t1. bvi_evaluate ([bvi_Call ticks (SOME n) ys NONE],env,t) = (res,t1) /\ P t1) ==>
     ?t1. bvi_evaluate ([bvi_Let ys (bvi_mk_tick (SUC ticks) body)],env,t) = (res,t1) /\
          P t1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `t:(C,FFI)bvi_state`; `ys:bvi_exp list`; `body:bvi_exp`;
                `ticks:num`; `env:bvl_v list`] evaluate_inlined_call) THEN
  ASM_REWRITE_TAC[FST]);;

let BVLPROPSAUX_BI_GEN_CASE_TAC : tactic =
  BVLPROPSAUX_BI_SPLIT_TAC THEN BVLPROPSAUX_BI_IH_TAC THEN BVLPROPSAUX_BI_FIN_TAC;;

let BVLPROPSAUX_BI_CASE_TAC : tactic =
  REPEAT STRIP_TAC THEN BVLPROPSAUX_BI_INV_TAC THEN
  (fun (asl,w as g) ->
     let ev = lhand (lhand (snd (dest_exists w))) in
     let es = fst (dest_pair (rand ev)) in
     if (try BVLPROPSAUX_bi_head (fst (dest_cons es)) = "bvi_Let" &&
             BVLPROPSAUX_has_const "bvi_mk_tick" es &&
             exists (fun (_,th) -> BVLPROPSAUX_bi_head (concl th) = "ALL2" &&
                       BVLPROPSAUX_has_const "bvi_Call" (concl th) = false &&
                       true) asl &&
             exists (fun (_,th) -> let c = concl th in is_eq c &&
                       BVLPROPSAUX_bi_head (lhs c) = "lookup") asl
         with Failure _ -> false)
     then (MATCH_MP_TAC BVLPROPSAUX_bi_inline_goal THEN
           (fun (asl,w as g) ->
              let lk = find (fun th -> let c = concl th in is_eq c &&
                         BVLPROPSAUX_bi_head (lhs c) = "lookup") (map snd asl) in
              EXISTS_TAC (el 0 (snd (strip_comb (lhs (concl lk))))) g) THEN
           CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
           CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
           BVLPROPSAUX_BI_GEN_CASE_TAC) g
     else BVLPROPSAUX_BI_GEN_CASE_TAC g);;

let bvi_inlineProof_evaluate_inline = prove
 (`!es env (s:((num#bvi_exp)spt#C,FFI)bvi_state) res s1 (t:(C,FFI)bvi_state) es1.
     bvi_inlineProof_in_state_rel s t /\
     ALL2 (bvi_inlineProof_exp_rel (bvi_state_code t)) es es1 /\
     bvi_evaluate (es,env,s) = (res,s1) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t1. bvi_evaluate (es1,env,t) = (res,t1) /\ bvi_inlineProof_in_state_rel s1 t1`,
  MATCH_MP_TAC (INST_TYPE [`:(num#bvi_exp)spt#C`,`:C`] BVLPROPSAUX_bvi_evaluate_ind) THEN
  REPEAT CONJ_TAC THEN BVLPROPSAUX_BI_CASE_TAC);;

let clean_prog_def = cake_def
  (CASE_TERM `clean_prog (prog:(num#num#bvi_exp)list) =
     MAP (\p. match p with (name,arity,body) -> (name,arity,remove_ticks_exp body)) prog`);;

let bvi_inlineProof_remove_ticks_cc_def = cake_def
  `bvi_inlineProof_remove_ticks_cc (cc:C->(num#num#bvi_exp)list->D) =
     (\cfg prog. cc cfg (clean_prog prog))`;;

let bvi_inlineProof_remove_ticks_co_def = cake_def
  `bvi_inlineProof_remove_ticks_co = ((I:C->C) ## clean_prog)`;;

let remove_state_rel_def = cake_def
  `remove_state_rel (s:(C,FFI)bvi_state) (t:(C,FFI)bvi_state) <=>
     bvi_state_refs t = bvi_state_refs s /\ bvi_state_clock t = bvi_state_clock s /\
     bvi_state_global t = bvi_state_global s /\ bvi_state_ffi t = bvi_state_ffi s /\
     bvi_state_code t = sptree_map ((I:num->num) ## remove_ticks_exp) (bvi_state_code s) /\
     bvi_state_compile_oracle t =
       bvi_inlineProof_remove_ticks_co o bvi_state_compile_oracle s /\
     bvi_state_compile s = bvi_inlineProof_remove_ticks_cc (bvi_state_compile t)`;;

(* HOL4 [simp] *)
let remove_ticks_exps_NIL = prove
 (`remove_ticks_exps [] = []`,
  REWRITE_TAC[remove_ticks_exp_def]);;

(* HOL4 [local] *)
let remove_state_rel_find_code_eq = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)bvi_state).
     remove_state_rel s t ==>
     !dest vs.
       bvl_find_code dest vs (bvi_state_code t) =
       OPTION_MAP ((I:bvl_v list->bvl_v list) ## remove_ticks_exp)
         (bvl_find_code dest vs (bvi_state_code s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[remove_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  CASES_ON `dest:num option` THEN REWRITE_TAC[bvl_find_code_def; lookup_map] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
    CASES_ON `LAST (vs:bvl_v list)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN
    CASES_ON `lookup a (bvi_state_code (s:(C,FFI)bvi_state))` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN
    MP_TAC(ISPEC `a':num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST1_TAC)) THEN
    REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM];
    CASES_ON `lookup a (bvi_state_code (s:(C,FFI)bvi_state))` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN
    MP_TAC(ISPEC `a':num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST1_TAC)) THEN
    REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]]);;

(* HOL4 [local] *)
let clock_sub_lt = prove
 (`!x k:num. ~(x = 0) /\ x <= k ==> x - 1 < k`,
  ARITH_TAC);;

(* HOL4 [local] *)
let evaluate_add_extra_clock = prove
 (`!xs env (s:(C,FFI)bvi_state) res s1 extra extra'.
     bvi_evaluate (xs,env,bvi_state_clock_fupd (K (extra + bvi_state_clock s)) s) =
       (res,s1) /\
     ~(res = Rerr (Rabort Rtimeout_error)) ==>
     bvi_evaluate (xs,env,bvi_state_clock_fupd (K (extra + extra' + bvi_state_clock s)) s) =
       (res,bvi_state_clock_fupd (K (extra' + bvi_state_clock s1)) s1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `extra':num` o MATCH_MP bvi_evaluate_add_clock o
    CONJ (ASSUME `bvi_evaluate (xs,env,bvi_state_clock_fupd (K (extra + bvi_state_clock s))
                    (s:(C,FFI)bvi_state)) = (res,s1)`)) THEN
  REWRITE_TAC[bvi_inc_clock_def; bvi_state_INFO.ri_accfupds; bvi_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN
  REWRITE_TAC[ARITH_RULE `(e + c) + e' = e + e' + c:num`; ADD_SYM] THEN
  MESON_TAC[ADD_SYM; ADD_AC]);;

(* HOL4 [local,simp] *)
let clean_prog_CONS = prove
 (`clean_prog [] = [] /\
   (!p ps. clean_prog (CONS p ps) =
           CONS (((I:num->num) ## (I:num->num) ## remove_ticks_exp) p) (clean_prog ps))`,
  REWRITE_TAC[clean_prog_def; MAP] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_MAP_THM; I_THM]);;

(* HOL4 [local,simp] *)
let clean_prog_simps = prove
 (`!prog. MAP FST (clean_prog prog) = MAP FST prog /\
          sptree_map ((I:num->num) ## remove_ticks_exp) (fromAList prog) =
          fromAList (clean_prog prog)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clean_prog_CONS; MAP; fromAList_def; sptree_map_def] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `ab:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ab:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `body:bvi_exp` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; FST; fromAList_def; map_insert]);;

(* HOL4 [local] *)
let remove_state_rel_do_install = prove
 (CASE_TERM `!args (s:(C,FFI)bvi_state) t. remove_state_rel s t ==>
  match (bvi_do_install args s:(bvl_v#(C,FFI)bvi_state,E)result) with
    Rval (value,s1) -> ?t1. bvi_do_install args t = (Rval (value,t1):(bvl_v#(C,FFI)bvi_state,E)result) /\
                            remove_state_rel s1 t1
  | Rerr err -> bvi_do_install args t = Rerr err`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[remove_state_rel_def]) THEN
  MP_TAC(ISPEC `bvi_state_compile_oracle (s:(C,FFI)bvi_state) 0` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg:C` (X_CHOOSE_THEN `progs:(num#num#bvi_exp)list`
    ASSUME_TAC)) THEN
  REWRITE_TAC[bvi_do_install_def] THEN
  ASM_REWRITE_TAC[o_THM; domain_map; PAIR_MAP_THM; I_THM; LET_DEF; LET_END_DEF;
                  clean_prog_simps; shift_seq_def; bvi_inlineProof_remove_ticks_co_def;
                  bvi_inlineProof_remove_ticks_cc_def] THEN BETA_TAC THEN
  REWRITE_TAC[o_THM; FST_PAIR_MAP; I_THM; PAIR_MAP_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clean_prog_simps] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `bvi_state_compile_oracle (s:(C,FFI)bvi_state) 0 = (cfg,progs)`)) THEN
  SPEC_TAC(`progs:(num#num#bvi_exp)list`,`progs:(num#num#bvi_exp)list`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `progs:(num#num#bvi_exp)list` list_CASES) THEN
  REWRITE_TAC[clean_prog_CONS] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ae:num#bvi_exp` SUBST1_TAC)) THEN
    MP_TAC(ISPEC `ae:num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST1_TAC)) THEN
    REWRITE_TAC[PAIR_MAP_THM; I_THM]] THEN
  CASE_REWRITE_TAC[] THEN REPEAT CASE_TAC THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[remove_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; map_union] THEN
  REWRITE_TAC[bvi_inlineProof_remove_ticks_co_def; PAIR_MAP_THM; I_THM; ETA_AX] THEN
  REWRITE_TAC[clean_prog_simps; clean_prog_CONS; PAIR_MAP_THM; I_THM]);;

(* HOL4 [local] *)
let remove_state_rel_do_app = prove
 (CASE_TERM `!op args (s:(C,FFI)bvi_state) t. remove_state_rel s t ==>
  match bvi_do_app op args s with
    Rval (value,s1) -> ?t1. bvi_do_app op args t = Rval (value,t1) /\ remove_state_rel s1 t1
  | Rerr err -> bvi_do_app op args t = Rerr err`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[bvi_do_app_def] THEN
    MATCH_MP_TAC remove_state_rel_do_install THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[remove_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "remove_state_rel" (concl th))) THEN
  SUBGOAL_THEN
   `bvi_state_refs_fupd (K (bvi_state_refs (s:(C,FFI)bvi_state)))
      (bvi_state_clock_fupd (K (bvi_state_clock s))
        (bvi_state_global_fupd (K (bvi_state_global s))
          (bvi_state_ffi_fupd (K (bvi_state_ffi s)) (t:(C,FFI)bvi_state)))) = t`
    ASSUME_TAC THENL
   [REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (bvi_state_code (t:(C,FFI)bvi_state)) =
                domain (bvi_state_code (s:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_map]; ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_do_app op args (s:(C,FFI)bvi_state)` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `a:bvl_v#(C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
      SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `args:bvl_v list`; `s:(C,FFI)bvi_state`;
                   `s2:(C,FFI)bvi_state`; `t:(C,FFI)bvi_state`;
                   `v:bvl_v`] do_app_state_swap_Rval) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
    FIRST_ASSUM(fun th ->
      if is_eq (concl th) && BVLPROPSAUX_has_const "bvi_do_app" (concl th)
      then STRIP_ASSUME_TAC (MATCH_MP BVLPROPSAUX_bvi_do_app_consts
                              (CONJ th (ASSUME `~(op = clos_Install)`)))
      else NO_TAC) THEN
    REWRITE_TAC[remove_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`op:clos_op`; `args:bvl_v list`; `s:(C,FFI)bvi_state`;
                   `t:(C,FFI)bvi_state`; `a:(exn_or_ret)error_result`]
                  do_app_state_swap_Rerr) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* local helpers for evaluate_remove_ticks_mutual: the induction on the    *)
(* clock and then the size of the expression list (HOL4 uses               *)
(* completeInduct_on the clock and remove_ticks_exp_ind)                   *)
let BVLPROPSAUX_bi_clock_size_ind = prove
 (`!P. (!xs (t:(C,FFI)bvi_state).
          (!xs' (t':(C,FFI)bvi_state).
             bvi_state_clock t' < bvi_state_clock t \/
             (bvi_state_clock t' = bvi_state_clock t /\
              list_size bvi_exp_size xs' < list_size bvi_exp_size xs) ==> P xs' t')
          ==> P xs t)
       ==> !xs t. P xs t`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\(r1:num,s1:num) (r2,s2). r1 < r2 \/ r1 = r2 /\ s1 < s2`;
                 `\p:bvi_exp list # (C,FFI)bvi_state.
                     (bvi_state_clock (SND p),list_size bvi_exp_size (FST p))`]
                WF_MEASURE_GEN) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`(<):num->num->bool`; `(<):num->num->bool`] WF_LEX) THEN
    REWRITE_TAC[WF_num];
    ALL_TAC] THEN
  REWRITE_TAC[WF_IND] THEN
  DISCH_THEN(MP_TAC o SPEC `\p:bvi_exp list # (C,FFI)bvi_state. P (FST p) (SND p):bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]);;

let BVLPROPSAUX_rt_exps_SING = prove
 (`!x. [remove_ticks_exp x] = remove_ticks_exps [x]`,
  REWRITE_TAC[remove_ticks_exp_def]);;

let BVLPROPSAUX_remove_state_rel_dec_clock = prove
 (`!(s:(C,FFI)bvi_state) t n.
     remove_state_rel s t ==>
     remove_state_rel (bvi_dec_clock n s) (bvi_dec_clock n t)`,
  REWRITE_TAC[remove_state_rel_def; bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_remove_state_rel_clock0 = prove
 (`!(s:(C,FFI)bvi_state) t.
     remove_state_rel s t ==>
     remove_state_rel (bvi_state_clock_fupd (K 0) s) (bvi_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[remove_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_bi_dec_inc_ticks = prove
 (`!ticks c (s:(C,FFI)bvi_state).
     ~(bvi_state_clock s = 0) ==>
     bvi_dec_clock (ticks + 1) (bvi_inc_clock (ticks + c) s) =
     bvi_inc_clock c (bvi_dec_clock 1 s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
              bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BVLPROPSAUX_bi_dec_inc_1 = prove
 (`!k (s:(C,FFI)bvi_state). bvi_dec_clock 1 (bvi_inc_clock (k + 1) s) = bvi_inc_clock k s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
              bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BVLPROPSAUX_bi_find_code_rel = prove
 (`!(s:(C,FFI)bvi_state) t d vs.
     remove_state_rel s t ==>
     (!args e'. bvl_find_code d vs (bvi_state_code t) = SOME (args,e') ==>
                ?e. bvl_find_code d vs (bvi_state_code s) = SOME (args,e) /\
                    e' = remove_ticks_exp e) /\
     (bvl_find_code d vs (bvi_state_code t) = NONE ==>
      bvl_find_code d vs (bvi_state_code s) = NONE)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    REWRITE_TAC[MATCH_MP remove_state_rel_find_code_eq th]) THEN
  STRUCT_CASES_TAC(ISPEC `bvl_find_code d vs (bvi_state_code (s:(C,FFI)bvi_state))`
                         (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `a:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* local tactics for evaluate_remove_ticks_mutual (as for                  *)
(* bvl_inlineProof's evaluate_remove_ticks): split the target evaluation,  *)
(* apply the induction hypothesis to the target sub-evaluations, chain the *)
(* source evaluations with evaluate_add_clock                              *)
let BVLPROPSAUX_bi_size_rws =
  filter (fun th -> exists (fun c -> let c = snd (strip_forall c) in is_eq c &&
            (try fst (dest_const (rator (lhs c))) = "bvi_exp_size" with Failure _ -> false))
            (conjuncts (concl th))) !the_size_defs @
  filter (fun th -> can (find_term (fun t -> is_const t &&
            (let n = fst (dest_const t) in String.length n > 12 &&
                                           String.sub n 0 12 = "bvi_exp_size")))
            (concl th)) (flat (map snd (!the_size_aux_eqs)));;

let BVLPROPSAUX_bi_is_rt_ev (t:term) =
  is_eq t && BVLPROPSAUX_bi_is_ev (lhs t) &&
  BVLPROPSAUX_bi_head (fst (dest_pair (rand (lhs t)))) = "remove_ticks_exps";;

let BVLPROPSAUX_BRT_SPLIT_TAC (cons:bool) : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_BI_FRESH_STRIP_TAC o REWRITE_RULE BVLPROPSAUX_bvi_eval_case_eqs o
     BETA_RULE o REWRITE_RULE[LET_DEF; LET_END_DEF; BVLPROPSAUX_rt_exps_SING] o
     PURE_ONCE_REWRITE_RULE[if cons then bvi_evaluate_CONS else bvi_evaluate_def] o
     (if cons then PURE_ONCE_REWRITE_RULE[remove_ticks_exp_def]
      else PURE_REWRITE_RULE[remove_ticks_exp_def]) o
     check (fun th -> BVLPROPSAUX_bi_is_rt_ev (concl th) &&
            not (is_var (rand (fst (dest_pair (rand (lhs (concl th))))))))) THEN
  TRY RVEQ_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC;;

let BVLPROPSAUX_bi_is_num_fact (t:term) =
  let t = if is_neg t then rand t else t in
  (is_comb t && is_comb (rator t) &&
   (try mem (fst (dest_const (rator (rator t)))) ["<"; "<="] with Failure _ -> false)) ||
  (is_eq t && type_of (lhs t) = `:num`);;

let BVLPROPSAUX_BRT_MEASURE_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_bi_is_ev (lhs c))
              (map snd asl) in
  let cls = mapfilter (MATCH_MP bvi_evaluate_clock) evs in
  let nums = filter (fun th -> BVLPROPSAUX_bi_is_num_fact (concl th)) (map snd asl) in
  (MAP_EVERY MP_TAC (cls @ nums) THEN
   REWRITE_TAC(bvi_dec_clock_def :: bvi_state_INFO.ri_accfupds :: K_THM :: list_size ::
               BVLPROPSAUX_bi_size_rws) THEN
   ARITH_TAC) g;;

let BVLPROPSAUX_BRT_IH1_TAC : tactic = fun (asl,w as g) ->
  let ihth = snd (find (fun (_,th) -> let c = concl th in is_forall c &&
        (let v,b = dest_forall c in type_of v = `:bvi_exp list` &&
          BVLPROPSAUX_has_const "list_size" b)) asl) in
  let rels = filter (fun th -> BVLPROPSAUX_bi_head (concl th) = "remove_state_rel")
                    (map snd asl) in
  let ok th = BVLPROPSAUX_bi_is_rt_ev (concl th) &&
    (let t1 = BVLPROPSAUX_bi_ev_state (lhs (concl th)) in
     exists (fun r -> rand (concl r) = t1) rels) in
  let ev = find ok (map snd asl) in
  let args = rand (lhs (concl ev)) in
  let l = rand (fst (dest_pair args)) in
  let t1 = BVLPROPSAUX_bi_ev_state (lhs (concl ev)) in
  let rel = find (fun r -> rand (concl r) = t1) rels in
  (MP_TAC (SPECL [l; t1] ihth) THEN ANTS_TAC THENL
    [BVLPROPSAUX_BRT_MEASURE_TAC;
     DISCH_THEN(fun th -> BVLPROPSAUX_BI_FRESH_STRIP_TAC (MATCH_MP th (CONJ rel ev))) THEN
     ASSUME_TAC (MATCH_MP bvi_evaluate_clock ev) THEN
     FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = concl ev))]) g;;

let BVLPROPSAUX_BRT_IH_TAC : tactic = REPEAT BVLPROPSAUX_BRT_IH1_TAC;;

(* chain the source evaluations of the induction hypothesis (each with its *)
(* own extra clock) with evaluate_add_clock; the witness is the sum        *)
let BVLPROPSAUX_bi_is_inc (st:term) =
  is_comb st && is_comb (rator st) &&
  (try fst (dest_const (rator (rator st))) = "bvi_inc_clock" with Failure _ -> false) &&
  is_var (rand (rator st));;

let BVLPROPSAUX_BRT_SRC_START (w:term) =
  let ckv,body = dest_exists w in
  let tv,body2 = dest_exists body in
  rand (BVLPROPSAUX_bi_ev_state (lhs (lhand body2)));;

let BVLPROPSAUX_BRT_CHAIN_TAC (final:term option) : tactic = fun (asl,w as g) ->
  let st_of th = BVLPROPSAUX_bi_ev_state (lhs (concl th)) in
  let srcs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_bi_is_ev (lhs c) &&
                       BVLPROPSAUX_bi_is_inc (st_of th)) (map snd asl) in
  let t0 = BVLPROPSAUX_BRT_SRC_START w in
  let rec chain u acc =
    match (try Some (find (fun th -> rand (st_of th) = u) srcs) with Failure _ -> None) with
      Some th -> chain (snd (dest_pair (rhs (concl th)))) (th :: acc)
    | None -> rev acc in
  let ths = chain t0 [] in
  let cks = map (fun th -> rand (rator (st_of th))) ths in
  let rec tots l = match l with
      [] -> []
    | [c] -> [c]
    | c :: rest -> let tr = tots rest in mk_binop `(+):num->num->num` (hd tr) c :: tr in
  let tl = tots cks in
  let shifted =
    let rec go ths tl = match ths, tl with
        [th], [_] -> [th]
      | th :: ths', _ :: (tnext :: _ as tl') ->
          let r = fst (dest_pair (rhs (concl th))) in
          let ntm = mk_neg (mk_eq (r, `Rerr (Rabort Rtimeout_error):bvi_result`)) in
          let nt = EQT_ELIM (REWRITE_CONV BVLPROPSAUX_bvi_eval_simps ntm) in
          let sh = REWRITE_RULE[inc_clock_ADD]
                     (SPEC tnext (MATCH_MP bvi_evaluate_add_clock (CONJ th nt))) in
          sh :: go ths' tl'
      | _ -> [] in
    go ths tl in
  let total = if tl = [] then `0` else hd tl in
  let tfin = match final with Some f -> f | None ->
    if ths = [] then t0 else snd (dest_pair (rhs (concl (last ths)))) in
  (EXISTS_TAC total THEN EXISTS_TAC tfin THEN
   REWRITE_TAC[inc_clock_ZERO] THEN
   MAP_EVERY ASSUME_TAC shifted) g;;

(* the source facts for the target code lookups, and the relation for the *)
(* states of the bodies (idempotent)                                        *)
let BVLPROPSAUX_BRT_PREP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = filter (fun th -> BVLPROPSAUX_bi_head (concl th) = "remove_state_rel") asms in
  let rel_of t = find (fun r -> rand (concl r) = t) rels in
  let is_fc th = let c = concl th in is_eq c &&
    BVLPROPSAUX_bi_head (lhs c) = "bvl_find_code" in
  let fcs = filter is_fc asms in
  let done_fc th =
    let _,args = strip_comb (lhs (concl th)) in
    let d = el 0 args and vs = el 1 args and cd = el 2 args in
    let s = rand (rator (concl (rel_of (rand cd)))) in
    exists (fun th' -> let _,args' = strip_comb (lhs (concl th')) in
                       el 0 args' = d && el 1 args' = vs && rand (el 2 args') = s) fcs in
  let fc_tac th =
    if done_fc th then ALL_TAC else
    let _,args = strip_comb (lhs (concl th)) in
    let d = el 0 args and vs = el 1 args and cd = el 2 args in
    let t = rand cd in
    let r = rel_of t in
    let lem = MATCH_MP (SPECL [rand (rator (concl r)); t; d; vs]
                          BVLPROPSAUX_bi_find_code_rel) r in
    if rhs (concl th) = `NONE:(bvl_v list # bvi_exp)option` then
      ASSUME_TAC (MP (CONJUNCT2 lem) th)
    else
      BVLPROPSAUX_BI_FRESH_STRIP_TAC (MATCH_MP (CONJUNCT1 lem) th) in
  let evs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_bi_is_ev (lhs c))
              asms in
  let dec_states = setify (mapfilter (fun th ->
    let st = BVLPROPSAUX_bi_ev_state (lhs (concl th)) in
    let f,args = strip_comb st in
    if is_const f && fst (dest_const f) = "bvi_dec_clock" then (el 0 args, el 1 args)
    else failwith "") evs) in
  let dec_tac (n,t) =
    let r = rel_of t in
    let th = SPEC n (MATCH_MP BVLPROPSAUX_remove_state_rel_dec_clock r) in
    if exists (fun r' -> concl r' = concl th) rels then failwith "done"
    else ASSUME_TAC th in
  (EVERY (mapfilter fc_tac fcs) THEN TRY RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_rt_exps_SING]) THEN
   EVERY (mapfilter dec_tac dec_states)) g;;

let BVLPROPSAUX_BRT_CASES = [pair_CASE; case_def "result"; case_def "error_result";
  case_def "option"; case_def "bvi_dest_thunk_ret"; case_def "thunk_mode";
  case_def "exn_or_ret"];;

let BVLPROPSAUX_BRT_FIN_TAC : tactic =
  BVLPROPSAUX_BRT_CHAIN_TAC None THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC BVLPROPSAUX_BRT_CASES;;

(* the source do_app of a target do_app *)
let BVLPROPSAUX_rsr_do_app_Rval = prove
 (`!op args (s:(C,FFI)bvi_state) t v t1.
     remove_state_rel s t /\ bvi_do_app op args t = Rval (v,t1) ==>
     ?s1. bvi_do_app op args s = Rval (v,s1) /\ remove_state_rel s1 t1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`op:clos_op`; `args:bvl_v list`; `s:(C,FFI)bvi_state`;
                `t:(C,FFI)bvi_state`] remove_state_rel_do_app) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_do_app op args (s:(C,FFI)bvi_state)` (cases "result")) THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `a:bvl_v#(C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:bvl_v` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
      SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[];
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC BVLPROPSAUX_bvi_eval_simps]);;

let BVLPROPSAUX_rsr_do_app_Rerr = prove
 (`!op args (s:(C,FFI)bvi_state) t err.
     remove_state_rel s t /\ bvi_do_app op args t = Rerr err ==>
     bvi_do_app op args s = Rerr err`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`op:clos_op`; `args:bvl_v list`; `s:(C,FFI)bvi_state`;
                `t:(C,FFI)bvi_state`] remove_state_rel_do_app) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_do_app op args (s:(C,FFI)bvi_state)` (cases "result")) THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `a:bvl_v#(C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:bvl_v` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
      SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC BVLPROPSAUX_bvi_eval_simps;
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN MESON_TAC[]]);;

let BVLPROPSAUX_BRT_st_of th = BVLPROPSAUX_bi_ev_state (lhs (concl th));;

let BVLPROPSAUX_BRT_TICK_TAC : tactic = fun (asl,w as g) ->
  let t0 = BVLPROPSAUX_BRT_SRC_START w in
  let th = find (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_bi_is_ev (lhs c) &&
                   let st = BVLPROPSAUX_BRT_st_of th in
                   BVLPROPSAUX_bi_is_inc st && rand st = t0) (map snd asl) in
  let c = rand (rator (BVLPROPSAUX_BRT_st_of th)) in
  let t1 = snd (dest_pair (rhs (concl th))) in
  (EXISTS_TAC (mk_binop `(+):num->num->num` c `1`) THEN EXISTS_TAC t1 THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
   REWRITE_TAC[inc_clock_eq_0; ARITH_RULE `!c. ~(c + 1 = 0)`;
               BVLPROPSAUX_bi_dec_inc_1] THEN
   ASM_REWRITE_TAC[]) g;;

let BVLPROPSAUX_BRT_OP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let da = find (fun th -> let c = concl th in is_eq c &&
     BVLPROPSAUX_bi_head (lhs c) = "bvi_do_app") asms in
  let _,args = strip_comb (lhs (concl da)) in
  let t1 = el 2 args in
  let rel = find (fun th -> BVLPROPSAUX_bi_head (concl th) = "remove_state_rel" &&
                            rand (concl th) = t1) asms in
  let r = rhs (concl da) in
  let fin = ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
            ASM_REWRITE_TAC BVLPROPSAUX_BRT_CASES in
  if BVLPROPSAUX_bi_head r = "Rval" then
    let th = MATCH_MP BVLPROPSAUX_rsr_do_app_Rval (CONJ rel da) in
    let v = variant (freesl (w :: map concl asms)) `s2:(C,FFI)bvi_state` in
    X_CHOOSE_THEN v (fun th2 -> STRIP_ASSUME_TAC th2 THEN
       BVLPROPSAUX_BRT_CHAIN_TAC (Some v) THEN fin) th g
  else
    (ASSUME_TAC (MATCH_MP BVLPROPSAUX_rsr_do_app_Rerr (CONJ rel da)) THEN
     BVLPROPSAUX_BRT_CHAIN_TAC None THEN fin) g;;

(* the handler of a target call: OPTION_MAP remove_ticks_exp x = SOME y   *)
(* or NONE gives x = SOME z with y = remove_ticks_exp z, or x = NONE        *)
let BVLPROPSAUX_BRT_OMAP_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_MAP; ARITH_RULE `0 + 1 = 1`]) THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
     let c = concl th in
     if is_eq c && BVLPROPSAUX_bi_head (lhs c) = "OPTION_MAP" && is_var (rand (lhs c))
     then BVLPROPSAUX_BI_FRESH_STRIP_TAC
            (REWRITE_RULE[OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE] th)
     else failwith "omap")) THEN
  TRY RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_rt_exps_SING]);;

(* the field equations of remove_state_rel s t for the refs and the clock *)
let BVLPROPSAUX_BRT_FIELDS rel =
  filter (fun th -> let l = lhs (concl th) in
            (try mem (fst (dest_const (rator l))) ["bvi_state_refs"; "bvi_state_clock"]
             with Failure _ -> false))
         (CONJUNCTS (REWRITE_RULE[remove_state_rel_def] rel));;

let BVLPROPSAUX_BRT_SRC_FACT asms (stp:term -> bool) =
  find (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_bi_is_ev (lhs c) &&
          let st = BVLPROPSAUX_BRT_st_of th in
          BVLPROPSAUX_bi_is_inc st && stp (rand st)) asms;;

let BVLPROPSAUX_BRT_FORCE_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let s0 = BVLPROPSAUX_BRT_SRC_START w in
  let rel0 = find (fun th -> BVLPROPSAUX_bi_head (concl th) = "remove_state_rel" &&
                             rand (rator (concl th)) = s0) asms in
  let flds = BVLPROPSAUX_BRT_FIELDS rel0 in
  let dect = mk_comb (mk_comb (`bvi_dec_clock:num->(C,FFI)bvi_state->(C,FFI)bvi_state`,
                               `1`), s0) in
  let res = fst (dest_pair (rhs (lhand (snd (dest_exists (snd (dest_exists w))))))) in
  let wck,wfin =
    try let th = BVLPROPSAUX_BRT_SRC_FACT asms (fun u -> u = dect) in
        rand (rator (BVLPROPSAUX_BRT_st_of th)), snd (dest_pair (rhs (concl th)))
    with Failure _ ->
      if res = `Rerr (Rabort Rtimeout_error):bvi_result`
      then `0`, mk_comb (`bvi_state_clock_fupd (K 0):(C,FFI)bvi_state->(C,FFI)bvi_state`,
                         s0)
      else `0`, s0 in
  (RULE_ASSUM_TAC(REWRITE_RULE flds) THEN
   ASSUME_TAC (MATCH_MP BVLPROPSAUX_remove_state_rel_clock0 rel0) THEN
   EXISTS_TAC wck THEN EXISTS_TAC wfin THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; inc_clock_ZERO] THEN BETA_TAC THEN
   ASM_SIMP_TAC (BVLPROPSAUX_BRT_CASES @ [bvi_inc_clock_refs; bvi_inc_clock_code;
     bvi_inc_clock_clock; bvi_dec_clock_1_inc_clock2; ADD_EQ_0])) g;;

(* Call and LetCall: the source runs the arguments (fact a1), the body    *)
(* (fact a2, at dec_clock 1 of the state after the arguments) and the     *)
(* handler or the continuation (fact a3); the earlier facts are shifted   *)
(* by the extra clock of the later ones and by the ticks of the call      *)
let BVLPROPSAUX_BRT_CALL_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let s0 = BVLPROPSAUX_BRT_SRC_START w in
  let body = snd (dest_exists (snd (dest_exists w))) in
  let ev = lhs (lhand body) in
  let cexp = hd (dest_list (fst (dest_pair (rand ev)))) in
  let cf,cargs = strip_comb cexp in
  let ticks = if fst (dest_const cf) = "LetCall" then el 1 cargs else el 0 cargs in
  let res = fst (dest_pair (rhs (lhand body))) in
  let st_of = BVLPROPSAUX_BRT_st_of in
  let src_at u = BVLPROPSAUX_BRT_SRC_FACT asms (fun v -> v = u) in
  let plus a b = mk_binop `(+):num->num->num` a b in
  let shift th k =
    let r = fst (dest_pair (rhs (concl th))) in
    let nt = EQT_ELIM (REWRITE_CONV BVLPROPSAUX_bvi_eval_simps
               (mk_neg (mk_eq (r, `Rerr (Rabort Rtimeout_error):bvi_result`)))) in
    REWRITE_RULE[inc_clock_ADD] (SPEC k (MATCH_MP bvi_evaluate_add_clock (CONJ th nt))) in
  let fin_tac = ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
     ASM_SIMP_TAC (BVLPROPSAUX_BRT_CASES @ [IS_SOME_DEF; IS_NONE_DEF; bvi_inc_clock_code;
       bvi_inc_clock_clock; BVLPROPSAUX_bi_dec_inc_ticks;
       ARITH_RULE `~(c = 0) ==> ~(c + t + d < t + 1)`;
       ARITH_RULE `c < 1 ==> c < t + 1`]) in
  match (try Some (src_at s0) with Failure _ -> None) with
    None -> (EXISTS_TAC `0` THEN EXISTS_TAC s0 THEN REWRITE_TAC[inc_clock_ZERO] THEN
             RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF; IS_NONE_DEF]) THEN fin_tac) g
  | Some a1 ->
  let c1 = rand (rator (st_of a1)) in
  let s1 = snd (dest_pair (rhs (concl a1))) in
  let rels = filter (fun th -> BVLPROPSAUX_bi_head (concl th) = "remove_state_rel") asms in
  let rel1 = find (fun th -> rand (rator (concl th)) = s1) rels in
  let flds = BVLPROPSAUX_BRT_FIELDS rel1 in
  let dect = mk_comb (mk_comb (`bvi_dec_clock:num->(C,FFI)bvi_state->(C,FFI)bvi_state`,
                               `1`), s1) in
  let ctm = mk_comb (`bvi_state_clock:(C,FFI)bvi_state->num`, s1) in
  let pre = RULE_ASSUM_TAC(REWRITE_RULE (IS_SOME_DEF :: IS_NONE_DEF :: flds)) in
  match (try Some (src_at dect) with Failure _ -> None) with
    None ->
      let fin = if res = `Rerr (Rabort Rtimeout_error):bvi_result`
                then mk_comb (`bvi_state_clock_fupd (K 0):(C,FFI)bvi_state->(C,FFI)bvi_state`,
                              s1)
                else s1 in
      (pre THEN ASSUME_TAC (MATCH_MP BVLPROPSAUX_remove_state_rel_clock0 rel1) THEN
       EXISTS_TAC c1 THEN EXISTS_TAC fin THEN fin_tac) g
  | Some a2 ->
  let c2 = rand (rator (st_of a2)) in
  let s2 = snd (dest_pair (rhs (concl a2))) in
  let nz = SUBGOAL_THEN (mk_neg (mk_eq (ctm, `0`))) ASSUME_TAC THENL
     [REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th -> BVLPROPSAUX_bi_is_num_fact (concl th) &&
                 free_in ctm (concl th)))) THEN ARITH_TAC; ALL_TAC] in
  match (try Some (src_at s2) with Failure _ -> None) with
    None ->
      let k = plus ticks c2 in
      (pre THEN nz THEN ASSUME_TAC (shift a1 k) THEN
       EXISTS_TAC (plus k c1) THEN EXISTS_TAC s2 THEN fin_tac) g
  | Some a3 ->
      let c3 = rand (rator (st_of a3)) in
      let s3 = snd (dest_pair (rhs (concl a3))) in
      let k = plus ticks (plus c3 c2) in
      (pre THEN nz THEN ASSUME_TAC (shift a1 k) THEN ASSUME_TAC (shift a2 c3) THEN
       EXISTS_TAC (plus k c1) THEN EXISTS_TAC s3 THEN fin_tac) g;;

let BVLPROPSAUX_BRT_CASE_TAC : tactic =
  FIRST [BVLPROPSAUX_BRT_FIN_TAC THEN NO_TAC; BVLPROPSAUX_BRT_TICK_TAC THEN NO_TAC;
         BVLPROPSAUX_BRT_OP_TAC THEN NO_TAC; BVLPROPSAUX_BRT_FORCE_TAC THEN NO_TAC;
         BVLPROPSAUX_BRT_CALL_TAC THEN NO_TAC];;

(* the simulation of a run of the code without ticks by a run of the      *)
(* original code with more clock (HOL4 proves evaluate_remove_ticks_mutual *)
(* by completeInduct_on the clock and remove_ticks_exp_ind; here the       *)
(* induction is on the clock and then the size of the expression list)     *)
let BVLPROPSAUX_bi_rt_sim = prove
 (`!xs (t:(C,FFI)bvi_state) env s res t1.
     remove_state_rel s t /\
     bvi_evaluate (remove_ticks_exps xs,env,t) = (res,t1) ==>
     ?ck s1. bvi_evaluate (xs,env,bvi_inc_clock ck s) = (res,s1) /\ remove_state_rel s1 t1`,
  MATCH_MP_TAC BVLPROPSAUX_bi_clock_size_ind THEN
  MAP_EVERY X_GEN_TAC [`xs:bvi_exp list`; `t:(C,FFI)bvi_state`] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`env:bvl_v list`; `s:(C,FFI)bvi_state`;
    `res:bvi_result`; `t1:(C,FFI)bvi_state`] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvi_exp list` list_CASES) THENL
   [ALL_TAC;
    STRUCT_CASES_TAC(ISPEC `t':bvi_exp list` list_CASES) THENL
     [CASES_ON `h:bvi_exp`; ALL_TAC]] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> t = `CONS (h:bvi_exp) (CONS h' t'')`)) w
     then BVLPROPSAUX_BRT_SPLIT_TAC true g else BVLPROPSAUX_BRT_SPLIT_TAC false g) THEN
  BVLPROPSAUX_BRT_OMAP_TAC THEN BVLPROPSAUX_BRT_PREP_TAC THEN BVLPROPSAUX_BRT_IH_TAC THEN
  BVLPROPSAUX_BRT_PREP_TAC THEN BVLPROPSAUX_BRT_IH_TAC THEN
  BVLPROPSAUX_BRT_CASE_TAC);;

(* HOL4 [local]; the clock bound k is not needed by the proof *)
let evaluate_remove_ticks_mutual = prove
 (`!k. (!e env (t:(C,FFI)bvi_state) s res t1.
          remove_state_rel s t /\ bvi_state_clock t <= k /\
          bvi_evaluate ([remove_ticks_exp e],env,t) = (res,t1) ==>
          ?extra s1.
            bvi_evaluate ([e],env,bvi_state_clock_fupd (K (bvi_state_clock s + extra)) s) =
              (res,s1) /\ remove_state_rel s1 t1) /\
       (!es env (t:(C,FFI)bvi_state) s res t1.
          remove_state_rel s t /\ bvi_state_clock t <= k /\
          bvi_evaluate (remove_ticks_exps es,env,t) = (res,t1) ==>
          ?extra s1.
            bvi_evaluate (es,env,bvi_state_clock_fupd (K (bvi_state_clock s + extra)) s) =
              (res,s1) /\ remove_state_rel s1 t1)`,
  REWRITE_TAC[GSYM bvi_inc_clock_def; BVLPROPSAUX_rt_exps_SING] THEN
  MESON_TAC[BVLPROPSAUX_bi_rt_sim]);;

let bvi_inlineProof_evaluate_remove_ticks = prove
 (`!k es env (t:(C,FFI)bvi_state) s res t1.
     remove_state_rel s t /\ bvi_state_clock t = k /\
     bvi_evaluate (remove_ticks_exps es,env,t) = (res,t1) ==>
     ?extra s1.
       bvi_evaluate (es,env,bvi_state_clock_fupd (K (bvi_state_clock s + extra)) s) =
         (res,s1) /\ remove_state_rel s1 t1`,
  REWRITE_TAC[GSYM bvi_inc_clock_def] THEN MESON_TAC[BVLPROPSAUX_bi_rt_sim]);;

(* the oracle combinators of compile_inc *)
let BVLPROPSAUX_bi_PAIR_INLINE_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> BVLPROPSAUX_bi_head t = "inline_all" &&
                              length (snd (strip_comb t)) = 2) w in
  (MP_TAC(ISPEC t PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvi_exp)spt` (X_CHOOSE_THEN
     `prog1:(num#num#bvi_exp)list` SUBST1_TAC)) THEN
   REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[pair_CASE; PAIR_MAP_THM; I_THM]) g;;

let bvi_inlineProof_state_cc_compile_inc_eq = prove
 (`state_cc bvi_inline_compile_inc (cc:C->(num#num#bvi_exp)list->(D#E#G)option) =
   state_cc inline_all (bvi_inlineProof_remove_ticks_cc cc)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[state_cc_def; bvi_inline_compile_inc_def; bvi_inlineProof_remove_ticks_cc_def;
              clean_prog_def; pair_CASE] THEN
  BVLPROPSAUX_bi_PAIR_INLINE_TAC);;

let bvi_inlineProof_state_co_compile_inc_eq = prove
 (`state_co bvi_inline_compile_inc
     (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) =
   bvi_inlineProof_remove_ticks_co o state_co inline_all co`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[state_co_def; bvi_inline_compile_inc_def; bvi_inlineProof_remove_ticks_co_def;
              clean_prog_def] THEN
  MP_TAC(ISPEC `(co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) n` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sc:(num#bvi_exp)spt#C` (X_CHOOSE_THEN
    `progs:(num#num#bvi_exp)list` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `sc:(num#bvi_exp)spt#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(num#bvi_exp)spt` (X_CHOOSE_THEN `cfg:C` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN BVLPROPSAUX_bi_PAIR_INLINE_TAC THEN
  REWRITE_TAC[clean_prog_def]);;

(* HOL4 [local]; in_cc is defined here at the type of the compile field of *)
(* the bvi state (HOL4: polymorphic)                                         *)
let in_cc_eq_state_cc = prove
 (`bvi_inlineProof_in_cc
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) =
   state_cc inline_all cc`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_inlineProof_in_cc_def; state_cc_def; pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN BVLPROPSAUX_bi_PAIR_INLINE_TAC);;

(* HOL4 [local] *)
let in_co_eq_state_co = prove
 (`bvi_inlineProof_in_co (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) =
   state_co inline_all co`,
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[bvi_inlineProof_in_co_def; state_co_def] THEN
  MP_TAC(ISPEC `(co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) n` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sc:(num#bvi_exp)spt#C` (X_CHOOSE_THEN
    `progs:(num#num#bvi_exp)list` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `sc:(num#bvi_exp)spt#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(num#bvi_exp)spt` (X_CHOOSE_THEN `cfg:C` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN BVLPROPSAUX_bi_PAIR_INLINE_TAC);;

(* HOL4 [local] *)
let bvi_inlineProof_evaluate_add_clock_io_events_mono = prove
 (`!exps env (s:(C,FFI)bvi_state) k extra.
     ffi_state_io_events
       (bvi_state_ffi (SND (bvi_evaluate (exps,env,bvi_state_clock_fupd (K k) s)))) <<=
     ffi_state_io_events
       (bvi_state_ffi (SND (bvi_evaluate (exps,env,
          bvi_state_clock_fupd (K (k + extra)) s))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`exps:bvi_exp list`; `env:bvl_v list`;
                 `bvi_state_clock_fupd (K k) (s:(C,FFI)bvi_state)`; `extra:num`]
                bvi_evaluate_add_to_clock_io_events_mono) THEN
  REWRITE_TAC[bvi_inc_clock_def; bvi_state_INFO.ri_accfupds; bvi_state_INFO.ri_fupdfupds;
              K_THM; K_o_THM]);;

(* HOL4 [local] *)
let inline_initial_state_rel = prove
 (`!prog cs1 prog1 (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)
     (ffi:(FFI)ffi_state)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) clk.
     inline_all LN prog = (cs1,prog1) /\ FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) ==>
     bvi_inlineProof_in_state_rel
       (bvi_initial_state ffi (fromAList prog) co (state_cc inline_all cc) clk)
       (bvi_initial_state ffi (fromAList prog1) (state_co inline_all co) cc clk)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP FST (prog1:(num#num#bvi_exp)list) = MAP FST (prog:(num#num#bvi_exp)list)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`LN:(num#bvi_exp)spt`; `prog:(num#num#bvi_exp)list`]
                  inline_all_MAP_FST) THEN
    ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `subspt (cs1:(num#bvi_exp)spt) (fromAList prog1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`prog:(num#num#bvi_exp)list`; `LN:(num#bvi_exp)spt`;
                   `LN:(num#bvi_exp)spt`; `cs1:(num#bvi_exp)spt`;
                   `prog1:(num#num#bvi_exp)list`] inline_all_cache_subspt) THEN
    ASM_REWRITE_TAC[union_LN; subspt_refl; domain_def; DISJOINT_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bvi_inlineProof_in_state_rel_def; bvi_initial_state_simp; domain_fromAList;
                  GSYM in_co_eq_state_co; GSYM in_cc_eq_state_cc] THEN
  REWRITE_TAC[lookup_fromAList] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(num#num#bvi_exp)list`; `LN:(num#bvi_exp)spt`; `LN:(num#bvi_exp)spt`;
                 `cs1:(num#bvi_exp)spt`; `prog1:(num#num#bvi_exp)list`; `k:num`;
                 `arity:num`; `exp:bvi_exp`] inline_all_ALOOKUP) THEN
  ASM_REWRITE_TAC[union_LN; subspt_refl; domain_def; DISJOINT_EMPTY]);;

(* HOL4 [local] *)
let evaluate_inline_compile = prove
 (`!prog cs1 prog1 (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)
     (ffi:(FFI)ffi_state)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) k start r s.
     inline_all LN prog = (cs1,prog1) /\ FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) /\
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
       bvi_initial_state ffi (fromAList prog) co (state_cc inline_all cc) k) = (r,s) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?s2. bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
            bvi_initial_state ffi (fromAList prog1) (state_co inline_all co) cc k) = (r,s2) /\
          bvi_inlineProof_in_state_rel s s2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(num#num#bvi_exp)list`; `cs1:(num#bvi_exp)spt`;
                 `prog1:(num#num#bvi_exp)list`;
                 `co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list`; `ffi:(FFI)ffi_state`;
                 `cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option`;
                 `k:num`] inline_initial_state_rel) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`; `[]:bvl_v list`;
                 `bvi_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)
                    (state_cc inline_all
                      (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option))
                    k`;
                 `r:bvi_result`; `s:((num#bvi_exp)spt#C,FFI)bvi_state`;
                 `bvi_initial_state (ffi:(FFI)ffi_state) (fromAList prog1)
                    (state_co inline_all
                      (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list))
                    (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) k`;
                 `[bvi_Call 0 (SOME start) [] NONE]`] bvi_inlineProof_evaluate_inline) THEN
  ASM_REWRITE_TAC[ALL2; bvi_inlineProof_exp_rel_refl]);;

(* the initial state with more clock *)
let BVLPROPSAUX_bi_inc_initial_state = prove
 (`!ck (ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list) cc k.
     bvi_inc_clock ck (bvi_initial_state ffi code co cc k) =
     bvi_initial_state ffi code co cc (k + ck)`,
  REWRITE_TAC[bvi_inc_clock_def; bvi_initial_state_def; bvi_state_INFO.ri_accessors;
              bvi_state_INFO.ri_fupds; K_THM]);;

(* HOL4 [local] *)
let evaluate_remove_ticks_compile = prove
 (`!prog (co:num->C#(num#num#bvi_exp)list) (ffi:(FFI)ffi_state)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) k start r s.
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
       bvi_initial_state ffi (fromAList (clean_prog prog))
         (bvi_inlineProof_remove_ticks_co o co) cc k) = (r,s) ==>
     ?ck s2.
       bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
         bvi_initial_state ffi (fromAList prog) co (bvi_inlineProof_remove_ticks_cc cc)
           (k + ck)) = (r,s2) /\
       bvi_state_ffi s2 = bvi_state_ffi s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`;
                 `bvi_initial_state (ffi:(FFI)ffi_state) (fromAList (clean_prog prog))
                    (bvi_inlineProof_remove_ticks_co o (co:num->C#(num#num#bvi_exp)list))
                    (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) k`;
                 `[]:bvl_v list`;
                 `bvi_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num->C#(num#num#bvi_exp)list)
                    (bvi_inlineProof_remove_ticks_cc
                      (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option)) k`;
                 `r:bvi_result`; `s:(C,FFI)bvi_state`] BVLPROPSAUX_bi_rt_sim) THEN
  REWRITE_TAC[remove_ticks_exp_def; OPTION_MAP_DEF; BVLPROPSAUX_bi_inc_initial_state] THEN
  ASM_REWRITE_TAC[remove_state_rel_def; bvi_initial_state_simp; clean_prog_simps] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `s2:(C,FFI)bvi_state`] THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let semantics_not_Fail_cond = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvi_semantics ffi code co cc start = Fail) ==>
     ~(?j e. FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                    bvi_initial_state ffi code co cc j)) = Rerr e /\
             ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let semantics_error_cases = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvi_semantics ffi code co cc start = Fail) ==>
     !j e t. bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
               bvi_initial_state ffi code co cc j) = (Rerr e,t) ==>
             e = Rabort Rtimeout_error \/ ?f. e = Rabort (Rffi_error f)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP semantics_not_Fail_cond) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `e:(exn_or_ret)error_result`]) THEN
  ASM_REWRITE_TAC[FST] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let semantics_terminate_unique = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start
     k1 r1 t1 k2 r2 t2.
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
       bvi_initial_state ffi code co cc k1) = (r1,t1) /\
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
       bvi_initial_state ffi code co cc k2) = (r2,t2) /\
     ~(r1 = Rerr (Rabort Rtimeout_error)) /\ ~(r2 = Rerr (Rabort Rtimeout_error)) ==>
     r1 = r2 /\ bvi_state_ffi t1 = bvi_state_ffi t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`; `[]:bvl_v list`;
                 `bvi_initial_state ffi code co cc k1:(C,FFI)bvi_state`; `r1:bvi_result`;
                 `t1:(C,FFI)bvi_state`] bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k2:num`) THEN
  MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`; `[]:bvl_v list`;
                 `bvi_initial_state ffi code co cc k2:(C,FFI)bvi_state`; `r2:bvi_result`;
                 `t2:(C,FFI)bvi_state`] bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k1:num`) THEN
  REWRITE_TAC[BVLPROPSAUX_bi_inc_initial_state] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (MP_TAC o AP_TERM `bvi_state_ffi:(C,FFI)bvi_state->(FFI)ffi_state`)) THEN
  REWRITE_TAC[bvi_inc_clock_ffi] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let semantics_no_type_error = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvi_semantics ffi code co cc start = Fail) ==>
     !j. ~(FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
              bvi_initial_state ffi code co cc j)) = Rerr (Rabort Rtype_error))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP semantics_not_Fail_cond) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `Rabort Rtype_error:(exn_or_ret)error_result`]) THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_simps);;

(* local helpers for compile_prog_semantics: the io events of the runs     *)
(* from an initial state grow with the clock, and the generic semantics    *)
(* argument for a target that is simulated by the source with more clock   *)
let BVLPROPSAUX_bi_init_io_mono = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvi_exp) list) cc k1 k2.
     k1 <= k2 ==>
     ffi_state_io_events
       (bvi_state_ffi (SND (bvi_evaluate (es,env,bvi_initial_state ffi p co cc k1)))) <<=
     ffi_state_io_events
       (bvi_state_ffi (SND (bvi_evaluate (es,env,bvi_initial_state ffi p co cc k2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`es:bvi_exp list`; `env:bvl_v list`;
                 `bvi_initial_state ffi p co cc k1:(C,FFI)bvi_state`; `d:num`]
                bvi_evaluate_add_to_clock_io_events_mono) THEN
  REWRITE_TAC[BVLPROPSAUX_bi_inc_initial_state]);;

let BVLPROPSAUX_bi_init_io_chain = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvi_exp) list) cc.
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (bvi_state_ffi
          (SND (bvi_evaluate (es,env,bvi_initial_state ffi p co cc k)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[BVLPROPSAUX_bi_init_io_mono; LE_CASES]);;

(* the run of the start call; the configuration type is taken from the oracle *)
let BVLPROPSAUX_bi_ev (p:term) (oo:term) (c:term) (k:term) =
  let cty = hd (snd (dest_type (hd (tl (snd (dest_type (type_of oo))))))) in
  let ins = inst [cty,`:C`] in
  vsubst [p,`p:(num#bvi_exp)spt`; oo,ins `co:num -> C # (num#num#bvi_exp) list`;
          c,ins `cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option`;
          k,`k:num`]
   (ins `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[]:bvl_v list,
                  bvi_initial_state (ffi:(FFI)ffi_state) (p:(num#bvi_exp)spt)
                    (co:num -> C # (num#num#bvi_exp) list)
                    (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option)
                    (k:num))`);;

let BVLPROPSAUX_bi_RUN_TAC (p:term) (oo:term) (c:term) (k:term) (r:term) (x:term) : tactic =
  MP_TAC(ISPEC (BVLPROPSAUX_bi_ev p oo c k) PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [r; x] THEN DISCH_TAC;;

(* MP of a labelled implication with its antecedent proved from the        *)
(* assumptions (not ASM_REWRITE_TAC after MP_TAC: the labelled fact itself  *)
(* would rewrite its instance to T)                                         *)
let BVLPROPSAUX_bi_LAB_MP_TAC (lab:string) (tms:term list) : tactic = fun (asl,w as g) ->
  USE_THEN lab (fun th ->
    let th' = SPECL tms th in
    let ant = lhand (concl th') in
    let ath = EQT_ELIM (REWRITE_CONV (FST :: SND :: map snd asl) ant) in
    MP_TAC (MP th' ath)) g;;

(* the source configuration type D and the target one C may differ *)
let BVLPROPSAUX_bi_semantics_back = prove
 (`!(ffi:(FFI)ffi_state) p1 (o1:num -> D # (num#num#bvi_exp) list) c1 p2
     (o2:num -> C # (num#num#bvi_exp) list) c2 start.
     (!k r s. bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                            bvi_initial_state ffi p2 o2 c2 k) = (r,s)
        ==> ?ck s2. bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                                  bvi_initial_state ffi p1 o1 c1 (k + ck)) = (r,s2) /\
                    bvi_state_ffi s2 = bvi_state_ffi s) /\
     ~(bvi_semantics ffi p1 o1 c1 start = Fail)
     ==> bvi_semantics ffi p2 o2 c2 start = bvi_semantics ffi p1 o1 c1 start`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim") ASSUME_TAC) THEN
  let pp1 = `p1:(num#bvi_exp)spt` and oo1 = `o1:num -> D # (num#num#bvi_exp) list`
  and cc1 = `c1:D->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#D)option`
  and pp2 = `p2:(num#bvi_exp)spt` and oo2 = `o2:num -> C # (num#num#bvi_exp) list`
  and cc2 = `c2:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option` in
  let tmo = `Rerr (Rabort Rtimeout_error):bvi_result` in
  let rv = `r:bvi_result` and r0 = `r0:bvi_result` in
  let s1 = `s1:(D,FFI)bvi_state` and t1 = `t1:(C,FFI)bvi_state` in
  let sv = `s:(D,FFI)bvi_state` in
  FIRST_ASSUM(LABEL_TAC "nf" o MATCH_MP semantics_not_Fail_cond) THEN
  REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `e:(exn_or_ret)error_result`
      MP_TAC)) THEN
    BVLPROPSAUX_bi_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
    ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
    BVLPROPSAUX_bi_LAB_MP_TAC "sim" [`k:num`; rv; t1] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
    USE_THEN "nf" (MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPECL [`k + ck:num`; `e:(exn_or_ret)error_result`]) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    USE_THEN "nf" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC option_case_cong THEN REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [BVLPROPSAUX_bi_LAB_MP_TAC "sim" [`k:num`; rv; `s:(C,FFI)bvi_state`] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`k + ck:num`; s1; rv; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN (mk_neg(mk_eq(rv, tmo))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      BVLPROPSAUX_bi_RUN_TAC pp2 oo2 cc2 `k:num` r0 t1 THEN
      BVLPROPSAUX_bi_LAB_MP_TAC "sim" [`k:num`; r0; t1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `s2:(D,FFI)bvi_state`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN (mk_conj(mk_eq(r0,rv),
         mk_eq(mk_comb(`bvi_state_ffi:(C,FFI)bvi_state->(FFI)ffi_state`, t1),
               mk_comb(`bvi_state_ffi:(D,FFI)bvi_state->(FFI)ffi_state`, sv))))
        STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM(fun th -> if rhs (concl th) = mk_pair(rv,sv)
          then MP_TAC (SPEC `ck:num` (MATCH_MP bvi_evaluate_add_clock
                 (CONJ th (ASSUME (mk_neg(mk_eq(rv, tmo)))))))
          else failwith "src") THEN
        REWRITE_TAC[BVLPROPSAUX_bi_inc_initial_state] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[bvi_inc_clock_ffi]) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`k:num`; t1; rv; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REWRITE_TAC[BVLPROPSAUX_bi_init_io_chain] THEN
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THENL
     [BVLPROPSAUX_bi_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
      BVLPROPSAUX_bi_LAB_MP_TAC "sim" [`k:num`; rv; t1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `k + ck:num` THEN
      ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL; SND];
      EXISTS_TAC `k:num` THEN
      BVLPROPSAUX_bi_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
      BVLPROPSAUX_bi_LAB_MP_TAC "sim" [`k:num`; rv; t1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; SND] THEN
      MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`; `[]:bvl_v list`;
                     `ffi:(FFI)ffi_state`; pp1; oo1; cc1; `k:num`; `k + ck:num`]
                    BVLPROPSAUX_bi_init_io_mono) THEN
      ASM_REWRITE_TAC[LE_ADD; SND]];
    REWRITE_TAC[]]);;

(* HOL4 [local] *)
let bvi_inlineProof_evaluate_compile_prog = prove
 (`!prog cs1 prog1 (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)
     (ffi:(FFI)ffi_state)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) k start r s.
     bvi_inline_compile_prog prog = (cs1,prog1) /\ FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) /\
     (!j. ~(FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
              bvi_initial_state ffi (fromAList prog) co
                (state_cc bvi_inline_compile_inc cc) j)) = Rerr (Rabort Rtype_error))) /\
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
       bvi_initial_state ffi (fromAList prog1) (state_co bvi_inline_compile_inc co) cc k) =
       (r,s) ==>
     ?ck s2.
       bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
         bvi_initial_state ffi (fromAList prog) co (state_cc bvi_inline_compile_inc cc)
           (k + ck)) = (r,s2) /\
       bvi_state_ffi s2 = bvi_state_ffi s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_inline_compile_prog_def; bvi_inline_compile_inc_def;
              bvi_inlineProof_state_co_compile_inc_eq;
              bvi_inlineProof_state_cc_compile_inc_eq] THEN
  MP_TAC(ISPEC `inline_all LN (prog:(num#num#bvi_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs2:(num#bvi_exp)spt` (X_CHOOSE_THEN
    `prog2:(num#num#bvi_exp)list` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> rhs (concl th) = `prog1:(num#num#bvi_exp)list`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> lhs (concl th) = `cs2:(num#bvi_exp)spt`)) THEN
  MP_TAC(ISPECL [`prog2:(num#num#bvi_exp)list`;
                 `state_co inline_all (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)`;
                 `ffi:(FFI)ffi_state`;
                 `cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option`;
                 `k:num`; `start:num`; `r:bvi_result`; `s:(C,FFI)bvi_state`]
                evaluate_remove_ticks_compile) THEN
  REWRITE_TAC[clean_prog_def] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
     bvi_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
       (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)
       (state_cc inline_all (bvi_inlineProof_remove_ticks_cc
          (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option)))
       (k + ck))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `src_res:bvi_result` (X_CHOOSE_THEN
    `src_st:((num#bvi_exp)spt#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(src_res = Rerr (Rabort Rtype_error):bvi_result)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k + ck:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prog:(num#num#bvi_exp)list`; `cs1:(num#bvi_exp)spt`;
                 `prog2:(num#num#bvi_exp)list`;
                 `co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list`; `ffi:(FFI)ffi_state`;
                 `bvi_inlineProof_remove_ticks_cc
                    (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option)`;
                 `k + ck:num`; `start:num`; `src_res:bvi_result`;
                 `src_st:((num#bvi_exp)spt#C,FFI)bvi_state`] evaluate_inline_compile) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(src_res:bvi_result,s3:(C,FFI)bvi_state)`)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `src_st:((num#bvi_exp)spt#C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    BVLPROPSAUX_bi_head (concl th) = "bvi_inlineProof_in_state_rel")) THEN
  REWRITE_TAC[bvi_inlineProof_in_state_rel_def] THEN
  DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let bvi_inlineProof_compile_prog_semantics = prove
 (`!prog cs1 prog1 (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)
     (ffi:(FFI)ffi_state)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start.
     bvi_inline_compile_prog prog = (cs1,prog1) /\ FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) ==>
     ~(bvi_semantics ffi (fromAList prog) co (state_cc bvi_inline_compile_inc cc) start =
       Fail) ==>
     bvi_semantics ffi (fromAList prog1) (state_co bvi_inline_compile_inc co) cc start =
     bvi_semantics ffi (fromAList prog) co (state_cc bvi_inline_compile_inc cc) start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP semantics_no_type_error) THEN
  MATCH_MP_TAC BVLPROPSAUX_bi_semantics_back THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC bvi_inlineProof_evaluate_compile_prog THEN
  MAP_EVERY EXISTS_TAC [`cs1:(num#bvi_exp)spt`; `prog1:(num#num#bvi_exp)list`] THEN
  ASM_REWRITE_TAC[]);;

(* the HOL4 [simp] theorems of this theory that are not local, registered  *)
(* for the files that load this one (the proofs above do not rely on them  *)
(* through the simpset)                                                     *)
let _ = cake_add_simps [inline_exps_LENGTH; remove_ticks_exps_LENGTH; inline_exps_CONS;
  inline_exps_REVERSE; inline_exps_MAP_Var; inline_exps_GENLIST_Var; wrapper_ok_inline_exp;
  MAP_FST_remove_ticks_prog; bvi_mk_tick_get_code_labels; bvi_inlineProof_exp_rel_refl;
  remove_ticks_exps_NIL];;
