(* ========================================================================= *)
(* bvl_jumpProof: port of HOL4 compiler/backend/proofs/bvl_jumpProofScript   *)
(* .sml (CakeML v3479).  Correctness proof for bvl_jump.                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;

type_invention_error := true;;

(* HOL4 [local] *)
let evaluate_JumpList = prove
 (`!n xs k (env:bvl_v list) (s:(C,FFI)bvl_state).
     k < LENGTH xs ==>
     bvl_evaluate ([JumpList n xs],CONS (bvl_Number (&(n + k))) env,s) =
     bvl_evaluate ([EL k xs],CONS (bvl_Number (&(n + k))) env,s)`,
  MATCH_MP_TAC JumpList_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[JumpList_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ASM_CASES_TAC `LENGTH (xs:bvl_exp list) = 0` THENL
   [ASM_MESON_TAC[LT]; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `LENGTH (xs:bvl_exp list) = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL]; ASM_REWRITE_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `m = LENGTH (xs:bvl_exp list) DIV 2` THEN
  SUBGOAL_THEN `0 < m /\ m < LENGTH (xs:bvl_exp list)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    UNDISCH_TAC `~(LENGTH (xs:bvl_exp list) = 0)` THEN
    UNDISCH_TAC `~(LENGTH (xs:bvl_exp list) = 1)` THEN
    SPEC_TAC(`LENGTH (xs:bvl_exp list)`,`l:num`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`l:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[bvl_evaluate_def] THENL
   [SUBGOAL_THEN `&0 <= &(n + k):int /\ &(n + k):int <= &1000000 /\ n + m < 1000000`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INT_POS; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  CASE_REWRITE_TAC[LENGTH; LT_0; EL; HD; REVERSE; APPEND; bvl_do_int_app_def] THEN
  ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[HD; bvl_Boolv_11; INT_OF_NUM_LT; LT_ADD_LCANCEL] THEN
  (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `env:bvl_v list`; `s:(C,FFI)bvl_state`] o
                  check (BVLPROPSAUX_has_const "TAKE" o concl)) THEN
    ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE; EL_TAKE];
    FIRST_X_ASSUM(MP_TAC o SPECL [`k - m`; `env:bvl_v list`; `s:(C,FFI)bvl_state`] o
                  check (BVLPROPSAUX_has_const "DROP" o concl)) THEN
    SUBGOAL_THEN `(n + m) + (k - m) = n + k /\ (k - m) + m = k /\
                  k - m < LENGTH (xs:bvl_exp list) - m`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_DROP; EL_DROP; ARITH_RULE `a < l - m ==> a + m < l`]]));;

let evaluate_Jump = prove
 (`!x env (s:(C,FFI)bvl_state) n t xs.
     bvl_evaluate ([x],env,s) = (Rval [bvl_Number (&n)],t) /\ n < LENGTH xs ==>
     bvl_evaluate ([bvl_jump_Jump x xs],env,s) =
     bvl_evaluate ([EL n xs],CONS (bvl_Number (&n)) env,t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_jump_Jump_def; bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; APPEND] THEN
  MP_TAC(SPECL [`0`; `xs:bvl_exp list`; `n:num`; `env:bvl_v list`; `t:(C,FFI)bvl_state`]
               evaluate_JumpList) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let bvl_get_code_labels_JumpList = prove
 (`!n xs. bvl_get_code_labels (JumpList n xs) =
          UNIONS (set_of_list (MAP bvl_get_code_labels xs))`,
  MATCH_MP_TAC JumpList_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[JumpList_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ASM_CASES_TAC `LENGTH (xs:bvl_exp list) = 0` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NIL]) THEN
    ASM_REWRITE_TAC[LENGTH; bvl_get_code_labels_def; assign_get_code_label_def; MAP;
                    set_of_list; UNIONS_0; UNION_EMPTY];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `LENGTH (xs:bvl_exp list) = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `LENGTH (xs:bvl_exp list) = 1`)) THEN
    REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[HD; MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY];
    ASM_REWRITE_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[bvl_get_code_labels_def; assign_get_code_label_def; MAP; set_of_list;
                  UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [GSYM (ISPECL [`LENGTH (xs:bvl_exp list) DIV 2`; `xs:bvl_exp list`] TAKE_DROP)] THEN
  REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION]);;
