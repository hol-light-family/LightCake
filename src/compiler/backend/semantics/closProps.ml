(* ========================================================================= *)
(* closProps: port of HOL4 compiler/backend/semantics/closPropsScript.sml    *)
(* (CakeML v3479).  Properties about closLang and its semantics.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;
(* HOL4: with_same_clock *)
let clos_with_same_clock = prove
 (`!s:(C,FFI)clos_state. clos_state_clock_fupd (K (clos_state_clock s)) s = s`,
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [clos_with_same_clock];;

(* HOL4: dec_clock_code *)
let clos_dec_clock_code = prove
 (`!x (y:(C,FFI)clos_state). clos_state_code (clos_dec_clock x y) = clos_state_code y`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;

(* HOL4: dec_clock_ffi *)
let clos_dec_clock_ffi = prove
 (`!x (y:(C,FFI)clos_state). clos_state_ffi (clos_dec_clock x y) = clos_state_ffi y`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;

let dec_clock_compile_oracle = prove
 (`!n (s:(C,FFI)clos_state).
     clos_state_compile_oracle (clos_dec_clock n s) = clos_state_compile_oracle s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;

let dec_clock_compile = prove
 (`!n (s:(C,FFI)clos_state).
     clos_state_compile (clos_dec_clock n s) = clos_state_compile s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [dec_clock_compile_oracle; dec_clock_compile];;

(* a local helper: a value that v_to_list accepts is a list value *)
let CLOSPROPSAUX_v_to_list_SOME = prove
 (`!x xs. clos_v_to_list x = SOME xs ==> x = clos_list_to_v xs`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[clos_v_to_list_def; clos_list_to_v_def] THEN
  GVS[option_case_eq] THEN RES_TAC THEN ASM_REWRITE_TAC[clos_list_to_v_def]);;

let CLOSPROPSAUX_P_list_to_v = prove
 (`!P. (!t l. P (clos_Block t l) <=> ALL P l) ==>
       !xs. P (clos_list_to_v xs) <=> ALL P xs`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[clos_list_to_v_def; ALL]);;

let list_to_v_EVERY_APPEND = prove
 (`!P (x:clos_v) y xs ys.
     clos_v_to_list x = SOME xs /\
     clos_v_to_list y = SOME ys /\
     (!t l. P (clos_Block t l) <=> ALL P l) /\
     P x /\ P y ==>
       P (clos_list_to_v (APPEND xs ys))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP CLOSPROPSAUX_v_to_list_SOME)) THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP CLOSPROPSAUX_P_list_to_v th]) THEN
                        REWRITE_TAC[MATCH_MP CLOSPROPSAUX_P_list_to_v th]) THEN
  ASM_REWRITE_TAC[ALL_APPEND]);;

(* HOL4 [local] *)
let forall_sum = prove
 (`!P:A+B->bool. (!x. P x) <=> (!a. P (INL a)) /\ (!b. P (INR b))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC sum_INDUCT THEN ASM_REWRITE_TAC[]);;

let evaluate_better_ind = prove
 (`!(P1:clos_exp list->(C,FFI)clos_state->bool) (P2:clos_v list->(C,FFI)clos_state->bool).
   (!xs s1.
      (!ys s2. clos_state_clock s2 <= clos_state_clock s1 /\
               (clos_state_clock s2 = clos_state_clock s1
                ==> clos_exp3_alt_size ys < clos_exp3_alt_size xs) ==> P1 ys s2) ==>
      (!args s2. clos_state_clock s2 <= clos_state_clock s1 /\
                 (clos_state_clock s2 = clos_state_clock s1
                  ==> LENGTH args < clos_exp3_alt_size xs) ==> P2 args s2) ==>
      P1 xs s1) /\
   (!args s1.
      (!ys s2. clos_state_clock s2 <= clos_state_clock s1 /\
               (clos_state_clock s2 = clos_state_clock s1
                ==> clos_exp3_alt_size ys < LENGTH args) ==> P1 ys s2) ==>
      (!args' s2. clos_state_clock s2 <= clos_state_clock s1 /\
                  (clos_state_clock s2 = clos_state_clock s1
                   ==> LENGTH args' < LENGTH args) ==> P2 args' s2) ==>
      P2 args s1)
   ==> (!xs s1. P1 xs s1) /\ (!args s1. P2 args s1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")) THEN
  SUBGOAL_THEN
   `!n m. (!xs (s1:(C,FFI)clos_state).
             clos_state_clock s1 = n /\ clos_exp3_alt_size xs = m
             ==> (P1:clos_exp list->(C,FFI)clos_state->bool) xs s1) /\
          (!(args:clos_v list) (s1:(C,FFI)clos_state).
             clos_state_clock s1 = n /\ LENGTH args = m
             ==> (P2:clos_v list->(C,FFI)clos_state->bool) args s1)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ihn") THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_THEN(LABEL_TAC "ihm") THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [USE_THEN "h1" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]);
    USE_THEN "h2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP])] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[LE_LT]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 [simp] *)
let clos_ref_rel_def = cake_def
  `(clos_ref_rel (R:A->B->bool) (clos_ValueArray vs) (clos_ValueArray ws) <=> ALL2 R vs ws) /\
   (clos_ref_rel R (clos_ByteArray as) (clos_ByteArray bs) <=> as = bs) /\
   (clos_ref_rel R (clos_Thunk ma a) (clos_Thunk mb b) <=> ma = mb /\ R a b) /\
   (clos_ref_rel _ _ _ <=> F)`;;
let _ = cake_add_simps [clos_ref_rel_def];;

let clos_ref_rel_simp = prove
 (`(!(R:A->B->bool) vs y. clos_ref_rel R (clos_ValueArray vs) y <=>
                          ?ws. y = clos_ValueArray ws /\ ALL2 R vs ws) /\
   (!(R:A->B->bool) bs y. clos_ref_rel R (clos_ByteArray bs) y <=> y = clos_ByteArray bs) /\
   (!(R:A->B->bool) m a y. clos_ref_rel R (clos_Thunk m a) y <=>
                           ?b. y = clos_Thunk m b /\ R a b)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `y:(B)clos_ref` THEN
  REWRITE_TAC[clos_ref_rel_def; distinctness "clos_ref"; injectivity "clos_ref"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_ref_rel_simp];;

(* termination of the definitions by the size of an expression list: the  *)
(* size of a Letrec contains the size of MAP SND fns (HOL4:                 *)
(* list_size_pair_size_MAP_FST_SND)                                         *)

let CLOSPROPSAUX_TC_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND; list_size; type_size_def "clos_exp"] @
               size_aux_eqs "clos_exp") THEN
   REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC);;

let code_locs_def = sem1aux_def_wf
  `measure (list_size clos_exp_size)`
  CLOSPROPSAUX_TC_TAC
  `(code_locs [] = []) /\
   (code_locs (CONS x (CONS y xs)) =
      let c1 = code_locs [x] in
      let c2 = code_locs (CONS y xs) in
        APPEND c1 c2) /\
   (code_locs [clos_Var _ v] = []) /\
   (code_locs [clos_If _ x1 x2 x3] =
      let c1 = code_locs [x1] in
      let c2 = code_locs [x2] in
      let c3 = code_locs [x3] in
        APPEND (APPEND c1 c2) c3) /\
   (code_locs [clos_Let _ xs x2] =
      let c1 = code_locs xs in
      let c2 = code_locs [x2] in
        APPEND c1 c2) /\
   (code_locs [clos_Raise _ x1] =
      code_locs [x1]) /\
   (code_locs [clos_Tick _ x1] =
      code_locs [x1]) /\
   (code_locs [clos_Op _ op xs] =
      code_locs xs) /\
   (code_locs [clos_App _ loc_opt x1 xs] =
      let c1 = code_locs [x1] in
      let c2 = code_locs xs in
        APPEND c1 c2) /\
   (code_locs [Fn _ loc_opt vs num_args x1] =
      let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
      let c1 = code_locs [x1] in
        APPEND c1 [loc]) /\
   (code_locs [clos_Letrec _ loc_opt vs fns x1] =
      let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
      let c1 = code_locs (MAP SND fns) in
      let c2 = code_locs [x1] in
        APPEND (APPEND c1 (list_of_seq (\n. loc + 2 * n) (LENGTH fns))) c2) /\
   (code_locs [clos_Handle _ x1 x2] =
      let c1 = code_locs [x1] in
      let c2 = code_locs [x2] in
        APPEND c1 c2) /\
   (code_locs [clos_Call _ ticks dest xs] =
      code_locs xs)`;;

let code_locs_ind = cake_ind "code_locs";;

let code_locs_cons = prove
 (`!x xs. code_locs (CONS x xs) = APPEND (code_locs [x]) (code_locs xs)`,
  REPEAT GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN
  REWRITE_TAC[code_locs_def; APPEND_NIL; LET_DEF; LET_END_DEF]);;

let code_locs_append = prove
 (`!l1 l2. code_locs (APPEND l1 l2) = APPEND (code_locs l1) (code_locs l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; code_locs_def] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN ASM_REWRITE_TAC[APPEND_ASSOC]);;

let code_locs_map = prove
 (`!xs (f:A->clos_exp). code_locs (MAP f xs) = FLAT (MAP (\x. code_locs [f x]) xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; code_locs_def] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [code_locs_cons] THEN ASM_REWRITE_TAC[]);;

let BIGUNION_MAP_code_locs_SND_SND = prove
 (`!xs:(A#B#clos_exp)list.
     UNIONS (set_of_list (MAP (set_of_list o code_locs o (\x. [SND (SND x)])) xs)) =
     set_of_list (code_locs (MAP (SND o SND) xs))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT; code_locs_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [code_locs_cons] THEN
  ASM_REWRITE_TAC[SET_OF_LIST_APPEND; o_THM]);;

let contains_App_SOME_def = sem1aux_def_wf
  `measure (\p:num # clos_exp list. list_size clos_exp_size (SND p))`
  CLOSPROPSAUX_TC_TAC
  `(contains_App_SOME max_app [] <=> F) /\
   (contains_App_SOME max_app (CONS x (CONS y xs)) <=>
      contains_App_SOME max_app [x] \/
      contains_App_SOME max_app (CONS y xs)) /\
   (contains_App_SOME max_app [clos_Var _ v] <=> F) /\
   (contains_App_SOME max_app [clos_If _ x1 x2 x3] <=>
      contains_App_SOME max_app [x1] \/
      contains_App_SOME max_app [x2] \/
      contains_App_SOME max_app [x3]) /\
   (contains_App_SOME max_app [clos_Let _ xs x2] <=>
      contains_App_SOME max_app [x2] \/
      contains_App_SOME max_app xs) /\
   (contains_App_SOME max_app [clos_Raise _ x1] <=>
      contains_App_SOME max_app [x1]) /\
   (contains_App_SOME max_app [clos_Tick _ x1] <=>
      contains_App_SOME max_app [x1]) /\
   (contains_App_SOME max_app [clos_Op _ (clos_ThunkOp ForceThunk) xs] <=>
      max_app < 1 \/
      contains_App_SOME max_app xs) /\
   (contains_App_SOME max_app [clos_Op _ op xs] <=>
      contains_App_SOME max_app xs) /\
   (contains_App_SOME max_app [clos_App _ loc_opt x1 es] <=>
      IS_SOME loc_opt \/ max_app < LENGTH es \/
      contains_App_SOME max_app [x1] \/
      contains_App_SOME max_app es) /\
   (contains_App_SOME max_app [Fn _ loc vs num_args x1] <=>
      contains_App_SOME max_app [x1]) /\
   (contains_App_SOME max_app [clos_Letrec _ loc vs fns x1] <=>
      contains_App_SOME max_app (MAP SND fns) \/
      contains_App_SOME max_app [x1]) /\
   (contains_App_SOME max_app [clos_Handle _ x1 x2] <=>
      contains_App_SOME max_app [x1] \/
      contains_App_SOME max_app [x2]) /\
   (contains_App_SOME max_app [clos_Call _ ticks dest xs] <=>
      contains_App_SOME max_app xs)`;;

let contains_App_SOME_ind = cake_ind "contains_App_SOME";;

let contains_App_SOME_EXISTS = prove
 (`!ls max_app. contains_App_SOME max_app ls <=>
                EX (\x. contains_App_SOME max_app [x]) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[contains_App_SOME_def; EX] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `t:clos_exp list` THEN
  REWRITE_TAC[contains_App_SOME_def; EX] THEN SIMP_TAC[]);;

(* HOL4 [simp] *)
let every_Fn_SOME_def = sem1aux_def_wf
  `measure (list_size clos_exp_size)`
  CLOSPROPSAUX_TC_TAC
  `(every_Fn_SOME [] <=> T) /\
   (every_Fn_SOME (CONS x (CONS y xs)) <=>
      every_Fn_SOME [x] /\
      every_Fn_SOME (CONS y xs)) /\
   (every_Fn_SOME [clos_Var _ v] <=> T) /\
   (every_Fn_SOME [clos_If _ x1 x2 x3] <=>
      every_Fn_SOME [x1] /\
      every_Fn_SOME [x2] /\
      every_Fn_SOME [x3]) /\
   (every_Fn_SOME [clos_Let _ xs x2] <=>
      every_Fn_SOME [x2] /\
      every_Fn_SOME xs) /\
   (every_Fn_SOME [clos_Raise _ x1] <=>
      every_Fn_SOME [x1]) /\
   (every_Fn_SOME [clos_Tick _ x1] <=>
      every_Fn_SOME [x1]) /\
   (every_Fn_SOME [clos_Op _ op xs] <=>
      every_Fn_SOME xs) /\
   (every_Fn_SOME [clos_App _ loc_opt x1 es] <=>
      every_Fn_SOME [x1] /\
      every_Fn_SOME es) /\
   (every_Fn_SOME [Fn _ loc_opt vs num_args x1] <=>
      IS_SOME loc_opt /\
      every_Fn_SOME [x1]) /\
   (every_Fn_SOME [clos_Letrec _ loc_opt vs fns x1] <=>
      IS_SOME loc_opt /\
      every_Fn_SOME (MAP SND fns) /\
      every_Fn_SOME [x1]) /\
   (every_Fn_SOME [clos_Handle _ x1 x2] <=>
      every_Fn_SOME [x1] /\
      every_Fn_SOME [x2]) /\
   (every_Fn_SOME [clos_Call _ ticks dest xs] <=>
      every_Fn_SOME xs)`;;
let _ = cake_add_simps [every_Fn_SOME_def];;

let every_Fn_SOME_ind = cake_ind "every_Fn_SOME";;

let every_Fn_SOME_EVERY = prove
 (`!ls. every_Fn_SOME ls <=> ALL (\x. every_Fn_SOME [x]) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[every_Fn_SOME_def; ALL] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `t:clos_exp list` THEN
  REWRITE_TAC[every_Fn_SOME_def; ALL] THEN SIMP_TAC[]);;

(* HOL4 [simp] *)
let every_Fn_SOME_APPEND = prove
 (`!l1 l2. every_Fn_SOME (APPEND l1 l2) <=> every_Fn_SOME l1 /\ every_Fn_SOME l2`,
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN REWRITE_TAC[ALL_APPEND]);;
let _ = cake_add_simps [every_Fn_SOME_APPEND];;

(* HOL4 [simp] *)
let every_Fn_vs_NONE_def = sem1aux_def_wf
  `measure (list_size clos_exp_size)`
  CLOSPROPSAUX_TC_TAC
  `(every_Fn_vs_NONE [] <=> T) /\
   (every_Fn_vs_NONE (CONS x (CONS y xs)) <=>
      every_Fn_vs_NONE [x] /\
      every_Fn_vs_NONE (CONS y xs)) /\
   (every_Fn_vs_NONE [clos_Var _ v] <=> T) /\
   (every_Fn_vs_NONE [clos_If _ x1 x2 x3] <=>
      every_Fn_vs_NONE [x1] /\
      every_Fn_vs_NONE [x2] /\
      every_Fn_vs_NONE [x3]) /\
   (every_Fn_vs_NONE [clos_Let _ xs x2] <=>
      every_Fn_vs_NONE [x2] /\
      every_Fn_vs_NONE xs) /\
   (every_Fn_vs_NONE [clos_Raise _ x1] <=>
      every_Fn_vs_NONE [x1]) /\
   (every_Fn_vs_NONE [clos_Tick _ x1] <=>
      every_Fn_vs_NONE [x1]) /\
   (every_Fn_vs_NONE [clos_Op _ op xs] <=>
      every_Fn_vs_NONE xs) /\
   (every_Fn_vs_NONE [clos_App _ loc_opt x1 es] <=>
      every_Fn_vs_NONE [x1] /\
      every_Fn_vs_NONE es) /\
   (every_Fn_vs_NONE [Fn _ loc vs_opt num_args x1] <=>
      IS_NONE vs_opt /\
      every_Fn_vs_NONE [x1]) /\
   (every_Fn_vs_NONE [clos_Letrec _ loc vs_opt fns x1] <=>
      IS_NONE vs_opt /\
      every_Fn_vs_NONE (MAP SND fns) /\
      every_Fn_vs_NONE [x1]) /\
   (every_Fn_vs_NONE [clos_Handle _ x1 x2] <=>
      every_Fn_vs_NONE [x1] /\
      every_Fn_vs_NONE [x2]) /\
   (every_Fn_vs_NONE [clos_Call _ ticks dest xs] <=>
      every_Fn_vs_NONE xs)`;;
let _ = cake_add_simps [every_Fn_vs_NONE_def];;

let every_Fn_vs_NONE_ind = cake_ind "every_Fn_vs_NONE";;

let every_Fn_vs_NONE_EVERY = prove
 (`!ls. every_Fn_vs_NONE ls <=> ALL (\x. every_Fn_vs_NONE [x]) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[every_Fn_vs_NONE_def; ALL] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `t:clos_exp list` THEN
  REWRITE_TAC[every_Fn_vs_NONE_def; ALL] THEN SIMP_TAC[]);;

let IMP_every_Fn_vs_NONE_TAKE = prove
 (`!ls n. every_Fn_vs_NONE ls ==> every_Fn_vs_NONE (TAKE n ls)`,
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN REWRITE_TAC[EVERY_TAKE]);;

(* HOL4 [simp] *)
let every_Fn_vs_NONE_APPEND = prove
 (`!l1 l2. every_Fn_vs_NONE (APPEND l1 l2) <=>
           every_Fn_vs_NONE l1 /\ every_Fn_vs_NONE l2`,
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN REWRITE_TAC[ALL_APPEND]);;
let _ = cake_add_simps [every_Fn_vs_NONE_APPEND];;

(* HOL4 [simp] *)
let every_Fn_vs_SOME_def = sem1aux_def_wf
  `measure (list_size clos_exp_size)`
  CLOSPROPSAUX_TC_TAC
  `(every_Fn_vs_SOME [] <=> T) /\
   (every_Fn_vs_SOME (CONS x (CONS y xs)) <=>
      every_Fn_vs_SOME [x] /\
      every_Fn_vs_SOME (CONS y xs)) /\
   (every_Fn_vs_SOME [clos_Var _ v] <=> T) /\
   (every_Fn_vs_SOME [clos_If _ x1 x2 x3] <=>
      every_Fn_vs_SOME [x1] /\
      every_Fn_vs_SOME [x2] /\
      every_Fn_vs_SOME [x3]) /\
   (every_Fn_vs_SOME [clos_Let _ xs x2] <=>
      every_Fn_vs_SOME [x2] /\
      every_Fn_vs_SOME xs) /\
   (every_Fn_vs_SOME [clos_Raise _ x1] <=>
      every_Fn_vs_SOME [x1]) /\
   (every_Fn_vs_SOME [clos_Tick _ x1] <=>
      every_Fn_vs_SOME [x1]) /\
   (every_Fn_vs_SOME [clos_Op _ op xs] <=>
      every_Fn_vs_SOME xs) /\
   (every_Fn_vs_SOME [clos_App _ loc_opt x1 es] <=>
      every_Fn_vs_SOME [x1] /\
      every_Fn_vs_SOME es) /\
   (every_Fn_vs_SOME [Fn _ loc vs_opt num_args x1] <=>
      IS_SOME vs_opt /\
      every_Fn_vs_SOME [x1]) /\
   (every_Fn_vs_SOME [clos_Letrec _ loc vs_opt fns x1] <=>
      IS_SOME vs_opt /\
      every_Fn_vs_SOME (MAP SND fns) /\
      every_Fn_vs_SOME [x1]) /\
   (every_Fn_vs_SOME [clos_Handle _ x1 x2] <=>
      every_Fn_vs_SOME [x1] /\
      every_Fn_vs_SOME [x2]) /\
   (every_Fn_vs_SOME [clos_Call _ ticks dest xs] <=>
      every_Fn_vs_SOME xs)`;;
let _ = cake_add_simps [every_Fn_vs_SOME_def];;

let every_Fn_vs_SOME_ind = cake_ind "every_Fn_vs_SOME";;

let every_Fn_vs_SOME_EVERY = prove
 (`!ls. every_Fn_vs_SOME ls <=> ALL (\x. every_Fn_vs_SOME [x]) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[every_Fn_vs_SOME_def; ALL] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `t:clos_exp list` THEN
  REWRITE_TAC[every_Fn_vs_SOME_def; ALL] THEN SIMP_TAC[]);;

(* HOL4 [simp] *)
let every_Fn_vs_SOME_APPEND = prove
 (`!l1 l2. every_Fn_vs_SOME (APPEND l1 l2) <=>
           every_Fn_vs_SOME l1 /\ every_Fn_vs_SOME l2`,
  ONCE_REWRITE_TAC[every_Fn_vs_SOME_EVERY] THEN REWRITE_TAC[ALL_APPEND]);;
let _ = cake_add_simps [every_Fn_vs_SOME_APPEND];;

(* HOL4: exp3_size (exp3_size is list_size clos_exp_size here) *)
let clos_exp3_size = prove
 (`!xs. list_size clos_exp_size xs = LENGTH xs + SUM (MAP clos_exp_size xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN ARITH_TAC);;

(* HOL4 [simp]; exp1_size is list_size (pair_size (\x. x) clos_exp_size) here *)
let exp1_size_rw = prove
 (`!fbinds. list_size (pair_size (\x. x) clos_exp_size) fbinds =
            list_size clos_exp_size (MAP SND fbinds) + SUM (MAP FST fbinds) + LENGTH fbinds`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM; ADD_CLAUSES] THEN
  SPEC_TAC(`h:num#clos_exp`,`h:num#clos_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_size_THM; FST; SND] THEN ARITH_TAC);;
let _ = cake_add_simps [exp1_size_rw];;

(* a local helper for termination: the size of a function body of a Letrec *)
let CLOSPROPSAUX_MEM_SIZE = prove
 (`!(fns:(num#clos_exp)list) p.
     MEM p fns ==> clos_exp_size (SND p) < list_size (pair_size (\x. x) clos_exp_size) fns`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fns:(num#clos_exp)list`; `FST(p:num#clos_exp)`; `SND(p:num#clos_exp)`]
         exp1_size_lemma) THEN
  ASM_REWRITE_TAC[PAIR]);;

let CLOSPROPSAUX_is_lt tm =
  try let h,args = strip_comb tm in
      fst(dest_const h) = "<" && type_of (hd args) = `:num`
  with Failure _ -> false;;

let CLOSPROPSAUX_TC2_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REPEAT(FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[FST; SND] o
                        MATCH_MP CLOSPROPSAUX_MEM_SIZE)) THEN
   REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND; list_size; type_size_def "clos_exp"] @
               size_aux_eqs "clos_exp") THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_lt o concl))) THEN
   ARITH_TAC);;


let no_mti_def = sem1aux_def_wf
  `measure clos_exp_size`
  CLOSPROPSAUX_TC2_TAC
  `(no_mti (clos_Var t n) <=> T) /\
   (no_mti (clos_If t e1 e2 e3) <=>
      no_mti e1 /\
      no_mti e2 /\
      no_mti e3) /\
   (no_mti (clos_Let t es e) <=>
      ALL no_mti es /\
      no_mti e) /\
   (no_mti (clos_Raise t e) <=>
      no_mti e) /\
   (no_mti (clos_Handle t e1 e2) <=>
      no_mti e1 /\
      no_mti e2) /\
   (no_mti (clos_Tick t e) <=>
      no_mti e) /\
   (no_mti (clos_Call t ticks n es) <=> F) /\
   (no_mti (clos_App t opt e es) <=>
      LENGTH es = 1 /\ opt = NONE /\
      ALL no_mti es /\
      no_mti e) /\
   (no_mti (Fn nm opt1 opt2 num_args e) <=>
      num_args = 1 /\ opt1 = NONE /\ opt2 = NONE /\
      no_mti e) /\
   (no_mti (clos_Letrec nms opt1 opt2 funs e) <=>
      no_mti e /\ opt1 = NONE /\ opt2 = NONE /\
      ALL (\x. FST x = 1 /\ no_mti (SND x)) funs) /\
   (no_mti (clos_Op t op es) <=>
      ALL no_mti es)`;;

let no_mti_ind = cake_ind "no_mti";;

let fv_def = sem1aux_def_wf
  `measure (\p:num # clos_exp list. list_size clos_exp_size (SND p))`
  CLOSPROPSAUX_TC2_TAC
  `(fv n [] <=> F) /\
   (fv n (CONS (x:clos_exp) (CONS y xs)) <=>
      fv n [x] \/ fv n (CONS y xs)) /\
   (fv n [clos_Var _ v] <=> (n = v)) /\
   (fv n [clos_If _ x1 x2 x3] <=>
      fv n [x1] \/ fv n [x2] \/ fv n [x3]) /\
   (fv n [clos_Let _ xs x2] <=>
      fv n xs \/ fv (n + LENGTH xs) [x2]) /\
   (fv n [clos_Raise _ x1] <=> fv n [x1]) /\
   (fv n [clos_Tick _ x1] <=> fv n [x1]) /\
   (fv n [clos_Op _ op xs] <=> fv n xs) /\
   (fv n [clos_App _ loc_opt x1 es] <=>
      fv n [x1] \/ fv n es) /\
   (fv n [Fn _ loc vs num_args x1] <=>
      fv (n + num_args) [x1]) /\
   (fv n [clos_Letrec _ loc vs fns x1] <=>
      EX (\p. match p with
                (num_args, x) -> fv ((n + num_args) + LENGTH fns) [x]) fns \/
      fv (n + LENGTH fns) [x1]) /\
   (fv n [clos_Handle _ x1 x2] <=>
      fv n [x1] \/ fv (n + 1) [x2]) /\
   (fv n [clos_Call _ ticks dest xs] <=> fv n xs)`;;

let fv_ind = cake_ind "fv";;

(* a local helper: fv of a non-empty list *)
let CLOSPROPSAUX_fv_cons = prove
 (`!v x xs. fv v (CONS x xs) <=> fv v [x] \/ fv v xs`,
  REPEAT GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN REWRITE_TAC[fv_def]);;

(* HOL4 [simp] *)
let fv_append = prove
 (`!v l1 l2. fv v (APPEND l1 l2) <=> fv v l1 \/ fv v l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; fv_def] THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_fv_cons] THEN ASM_REWRITE_TAC[DISJ_ASSOC]);;
let _ = cake_add_simps [fv_append];;

(* HOL4 [simp] *)
let fv_nil = prove
 (`!v. fv v [] <=> F`,
  REWRITE_TAC[fv_def]);;
let _ = cake_add_simps [fv_nil];;

let fv1_def = cake_def
  `fv1 v e <=> fv v [e]`;;

(* HOL4 [simp]: fv1_intro = GSYM fv1_def *)
let fv1_intro = prove
 (`!v e. fv v [e] <=> fv1 v e`,
  REWRITE_TAC[fv1_def]);;
let _ = cake_add_simps [fv1_intro];;

(* HOL4: fv1_thm = fv_def |> SIMP_RULE (srw_ss()) [] (the clause for [] *)
(* becomes T by fv_nil and is dropped)                                   *)
let fv1_thm = end_itlist CONJ (tl (CONJUNCTS (REWRITE_RULE[fv1_intro] fv_def)));;

(* HOL4 [simp] *)
let fv_cons = prove
 (`!v x xs. fv v (CONS x xs) <=> fv1 v x \/ fv v xs`,
  REWRITE_TAC[GSYM fv1_intro] THEN MATCH_ACCEPT_TAC CLOSPROPSAUX_fv_cons);;
let _ = cake_add_simps [fv_cons];;

let fv_exists = prove
 (`!v ls. fv v ls <=> EX (fv1 v) ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[fv_nil; fv_cons; EX]);;

let fv_MAPi = prove
 (`!l x (f:num->A->clos_exp).
     fv x (MAPi f l) <=> ?n. n < LENGTH l /\ fv x [f n (EL n l)]`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAPi_DEF; fv_nil; fv_cons; LENGTH; LT] THEN
  REWRITE_TAC[fv1_intro; o_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM LT] THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; LT_0];
      EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[EL; TL; LT_SUC]];
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[EL; HD; TL; LT_SUC] THEN MESON_TAC[]]);;

let fv_GENLIST_Var = prove
 (`!tra v n. fv v (list_of_seq (clos_Var tra) n) <=> v < n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; fv_nil; fv_append; LT] THEN
  REWRITE_TAC[fv1_intro; GSYM fv1_intro; fv_def] THEN MESON_TAC[]);;

(* HOL4 [simp] *)
let fv_REPLICATE = prove
 (`!n m e. fv n (REPLICATE m e) <=> 0 < m /\ fv1 n e`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; fv_nil; fv_cons; LT_REFL; LT_0] THEN MESON_TAC[]);;
let _ = cake_add_simps [fv_REPLICATE];;

(* HOL4: v_ind (the induction theorem of v with EVERY P for the lists) *)
let v_ind = prove
 (`!P. (!i. P (clos_Number i)) /\ (!w. P (clos_Word64 w)) /\
       (!n l. ALL P l ==> P (clos_Block n l)) /\ (!l. P (ByteVector l)) /\
       (!b n. P (clos_RefPtr b n)) /\
       (!o' l l0 n e. ALL P l /\ ALL P l0 ==> P (clos_Closure o' l l0 n e)) /\
       (!o' l l0 l1 n. ALL P l /\ ALL P l0 ==> P (clos_Recclosure o' l l0 l1 n))
       ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:clos_v->bool`; `ALL (P:clos_v->bool)`] clos_v_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

(* HOL4: do_app_err *)
let clos_do_app_err = prove
 (`!op ls (s:(C,FFI)clos_state) e.
     clos_do_app op ls s = Rerr e ==>
     (~(op = BlockOp clos_Equal) ==> ?a. e = Rabort a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"] THEN
  MESON_TAC[]);;

(* HOL4: Boolv_11 [simp] *)
let clos_Boolv_11 = prove
 (`!b1 b2. clos_Boolv b1 = clos_Boolv b2 <=> b1 = b2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_Boolv_def; injectivity "clos_v"] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN
  REWRITE_TAC[true_tag_def; false_tag_def] THEN CONV_TAC NUM_REDUCE_CONV);;
let _ = cake_add_simps [clos_Boolv_11];;

(* HOL4: do_eq_sym *)
let clos_do_eq_sym = prove
 (`(!x y. clos_do_eq x y = clos_do_eq y x) /\
   (!x y. clos_do_eq_list x y = clos_do_eq_list y x)`,
  MATCH_MP_TAC clos_do_eq_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[clos_do_eq_def] THEN
    CASES_ON `x:clos_v` THEN CASES_ON `y:clos_v` THEN
    REWRITE_TAC[case_def "clos_v"; injectivity "eq_result"] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[injectivity "eq_result"; distinctness "eq_result"] THEN
    ASM_MESON_TAC[injectivity "clos_v"];
    REWRITE_TAC[clos_do_eq_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[clos_do_eq_def] THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `clos_do_eq y x` THEN REWRITE_TAC[case_def "eq_result"] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[clos_do_eq_def];
    REWRITE_TAC[clos_do_eq_def]]);;

(* HOL4 ZIP (l1,l2) is ZIP l1 l2; the lengths are hypotheses as in HOL4 *)
let do_eq_list_rel = prove
 (`!l1 l2 l3 l4.
     LENGTH l1 = LENGTH l2 /\ LENGTH l3 = LENGTH l4 /\
     ALL2 (\p1 p2. UNCURRY clos_do_eq p1 = UNCURRY clos_do_eq p2) (ZIP l1 l2) (ZIP l3 l4)
     ==> clos_do_eq_list l1 l2 = clos_do_eq_list l3 l4`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v list_CASES))
    [`l2:clos_v list`; `l3:clos_v list`; `l4:clos_v list`] THEN
  REWRITE_TAC[LENGTH; ZIP; ALL2; NOT_SUC; GSYM NOT_SUC; SUC_INJ; UNCURRY_DEF] THEN
  STRIP_TAC THEN REWRITE_TAC[el 2 (CONJUNCTS clos_do_eq_def)] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':clos_v list`; `t'':clos_v list`; `t''':clos_v list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A local helper: clos_evaluate_ind with the tuple of evaluate split, so    *)
(* that MATCH_MP_TAC applies it to goals (!xs env s. P xs env s) /\          *)
(* (!loc_opt f args s. Q loc_opt f args s).                                   *)
(* ------------------------------------------------------------------------- *)

let CLOSPROPSAUX_evaluate_ind =
  let p = `P:clos_exp list -> clos_v list -> (C,FFI)clos_state -> bool`
  and q = `Q:num option -> clos_v -> clos_v list -> (C,FFI)clos_state -> bool` in
  let th = ISPECL
    [`\t:clos_exp list # clos_v list # (C,FFI)clos_state.
        (P:clos_exp list -> clos_v list -> (C,FFI)clos_state -> bool)
        (FST t) (FST (SND t)) (SND (SND t))`; q] clos_evaluate_ind in
  let th = PURE_REWRITE_RULE[FST; SND] (CONV_RULE (DEPTH_CONV BETA_CONV) th) in
  let hy = lhand (concl th) in
  let goal = mk_imp(hy,
    `(!xs env s. (P:clos_exp list -> clos_v list -> (C,FFI)clos_state -> bool) xs env s) /\
     (!loc_opt f args s.
        (Q:num option -> clos_v -> clos_v list -> (C,FFI)clos_state -> bool)
        loc_opt f args s)`) in
  GENL [p;q] (prove(goal,
    DISCH_TAC THEN MP_TAC(MP th (ASSUME hy)) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND]));;

(* ------------------------------------------------------------------------- *)
(* Local tactics for proofs by induction on evaluate: unfold the evaluate    *)
(* call of the last assumption once, split it with the case equations into   *)
(* the facts about the sub-evaluations, and resolve the induction            *)
(* hypotheses with them.                                                     *)
(* ------------------------------------------------------------------------- *)

let CLOSPROPSAUX_eval_case_eqs =
  [pair_case_eq; COND_CASE_EQ; option_case_eq; list_case_eq; case_eq "result";
   case_eq "app_kind"; case_eq "error_result"; case_eq "clos_dest_thunk_ret";
   case_eq "thunk_mode"; PAIR_EQ; injectivity "result"; distinctness "result"];;

let CLOSPROPSAUX_both th = [th; ONCE_REWRITE_RULE[EQ_SYM_EQ] th];;

let CLOSPROPSAUX_eval_simps =
  flat (map (fun s -> CLOSPROPSAUX_both (distinctness s))
          ["result"; "option"; "list"; "app_kind"; "error_result"; "abort";
           "clos_dest_thunk_ret"; "thunk_mode"]) @
  map injectivity ["result"; "option"; "list"; "app_kind"; "error_result"; "abort";
                   "clos_dest_thunk_ret"] @ [PAIR_EQ];;

let CLOSPROPSAUX_CLEAN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE CLOSPROPSAUX_eval_simps) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN TRY RVEQ_TAC;;

let CLOSPROPSAUX_SPLIT_TAC : tactic =
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC CLOSPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_CLEAN_TAC;;

(* a local resolution tactic (HOL4 res_tac): every implicational assumption, *)
(* curried, is resolved with the other assumptions by MATCH_MP, as far as    *)
(* it goes (the kit's RES_TAC goes through IMP_CURRY_RULE, which fails when  *)
(* an inner quantifier rebinds a variable free in an outer antecedent)       *)
let CLOSPROPSAUX_RES_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results =
    flat (map (fun th -> let th' = curry th in
                 flat (map (resolve 4) (mapfilter (fun a -> MATCH_MP th' a) asms)))
              imps) in
  let results = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) results in
  EVERY (map CAKE_ASSUME_TAC results) gl;;

let CLOSPROPSAUX_evaluate_LENGTH_imp = prove
 (`(!xs env (s:(C,FFI)clos_state) res s1.
      clos_evaluate (xs,env,s) = (Rval res,s1) ==> LENGTH xs = LENGTH res) /\
   (!loc_opt f args (s:(C,FFI)clos_state) res s1.
      evaluate_app loc_opt f args s = (Rval res,s1) ==> LENGTH res = 1)`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN CLOSPROPSAUX_SPLIT_TAC THEN
  REWRITE_TAC[LENGTH] THEN CLOSPROPSAUX_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ONE]);;

(* a local helper: a match on (Rval res,s) with a T default *)
let CLOSPROPSAUX_match_Rval = prove
 (CASE_TERM `!(p:(A,B)result # C) (P:A->bool).
     (match p with (Rval res,s1) -> P res | _ -> T) <=>
     (!res s1. p = (Rval res,s1) ==> P res)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CASES_ON `p1:(A,B)result` THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result";
              distinctness "result"] THEN MESON_TAC[]);;

(* HOL4: evaluate_LENGTH *)
let clos_evaluate_LENGTH = prove
 (CASE_TERM `(!xs env (s:(C,FFI)clos_state).
     match clos_evaluate (xs,env,s) with
       (Rval res,s1) -> LENGTH xs = LENGTH res
     | _ -> T) /\
   (!x1 x2 x3 (x4:(C,FFI)clos_state).
     match evaluate_app x1 x2 x3 x4 with
       (Rval res,s1) -> LENGTH res = 1
     | _ -> T)`,
  REWRITE_TAC[CLOSPROPSAUX_match_Rval] THEN
  MESON_TAC[CLOSPROPSAUX_evaluate_LENGTH_imp]);;

(* HOL4: evaluate_IMP_LENGTH *)
let clos_evaluate_IMP_LENGTH = prove
 (`!xs env (s:(C,FFI)clos_state) res s1.
     clos_evaluate (xs,env,s) = (Rval res,s1) ==> LENGTH xs = LENGTH res`,
  MESON_TAC[CLOSPROPSAUX_evaluate_LENGTH_imp]);;

let evaluate_app_IMP_LENGTH = prove
 (`!x1 x2 x3 (x4:(C,FFI)clos_state) res s1.
     evaluate_app x1 x2 x3 x4 = (Rval res,s1) ==> LENGTH res = 1`,
  MESON_TAC[CLOSPROPSAUX_evaluate_LENGTH_imp]);;

(* HOL4: evaluate_SING *)
let clos_evaluate_SING = prove
 (`!x env (s:(C,FFI)clos_state) r s2.
     clos_evaluate ([x],env,s) = (Rval r,s2) ==> ?r1. r = [r1]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH] THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN STRIP_TAC THEN
  EXISTS_TAC `h:clos_v` THEN ASM_REWRITE_TAC[]);;

(* HOL4: evaluate_CONS *)
let clos_evaluate_CONS = prove
 (CASE_TERM `!x xs env (s:(C,FFI)clos_state).
     clos_evaluate (CONS x xs,env,s) =
     match clos_evaluate ([x],env,s) with
       (Rval v,s2) ->
         (match clos_evaluate (xs,env,s2) with
            (Rval vs,s1) -> (Rval (CONS (HD v) vs),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  MP_TAC(ISPEC `clos_evaluate ([x],env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN REWRITE_TAC[case_def "result"] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) THEN
  ASM_REWRITE_TAC[HD]);;

(* a local helper: case-split a term of type result # state *)
let CLOSPROPSAUX_PAIR_RESULT_TAC (tm:term) (rn:string) (sn:string) : tactic =
  fun (asl,w as gl) ->
    let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b | _ -> failwith "PAIR_RESULT_TAC") in
    let r = mk_var(rn,rty) and s = mk_var(sn,sty) in
    (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s SUBST1_TAC)) THEN
     CASES_ON r THEN REWRITE_TAC[pair_CASE; case_def "result"]) gl;;

(* HOL4: evaluate_APPEND *)
let clos_evaluate_APPEND = prove
 (CASE_TERM `!xs ys env (s:(C,FFI)clos_state).
     clos_evaluate (APPEND xs ys,env,s) =
     match clos_evaluate (xs,env,s) with
       (Rval vs,s2) ->
         (match clos_evaluate (ys,env,s2) with
            (Rval ws,s1) -> (Rval (APPEND vs ws),s1)
          | (Rerr v8,s1) -> (Rerr v8,s1))
     | (Rerr v10,s2) -> (Rerr v10,s2)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[APPEND; clos_evaluate_def; pair_CASE; case_def "result"] THEN
    CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (ys,env,s:(C,FFI)clos_state)` "r" "s1";
    REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
    ASM_REWRITE_TAC[] THEN
    CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate ([h],env,s:(C,FFI)clos_state)` "r" "s1" THEN
    CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (t,env,s1:(C,FFI)clos_state)` "r2" "s2" THEN
    CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (ys,env,s2:(C,FFI)clos_state)` "r3" "s3" THEN
    REWRITE_TAC[APPEND]]);;

(* HOL4: evaluate_SNOC *)
let clos_evaluate_SNOC = prove
 (CASE_TERM `!xs env (s:(C,FFI)clos_state) x.
     clos_evaluate (SNOC x xs,env,s) =
     match clos_evaluate (xs,env,s) with
       (Rval vs,s2) ->
         (match clos_evaluate ([x],env,s2) with
            (Rval v,s1) -> (Rval (APPEND vs v),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SNOC_APPEND; clos_evaluate_APPEND] THEN
  CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state)` "r" "s1" THEN
  CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate ([x],env,s1:(C,FFI)clos_state)` "r2" "s2");;

let do_install_const = prove
 (`!vs (s:(C,FFI)clos_state) res s'.
     clos_do_install vs s = (res,s') ==>
     clos_state_max_app s' = clos_state_max_app s /\
     clos_state_ffi s' = clos_state_ffi s`,
  RW[clos_do_install_def; clos_case_eq_thms] THEN
  TRY PAIRARG_TAC THEN GVS[clos_case_eq_thms; pair_case_eq; COND_CASE_EQ]);;

(* HOL4: evaluate_const_lemma *)
let CLOSPROPSAUX_evaluate_const_lemma = prove
 (`(!xs env (s:(C,FFI)clos_state) res s1.
      clos_evaluate (xs,env,s) = (res,s1) ==>
      clos_state_max_app s1 = clos_state_max_app s) /\
   (!loc_opt f args (s:(C,FFI)clos_state) res s1.
      evaluate_app loc_opt f args s = (res,s1) ==>
      clos_state_max_app s1 = clos_state_max_app s)`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN CLOSPROPSAUX_SPLIT_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN
  IMP_RES_TAC clos_do_app_const THEN IMP_RES_TAC do_install_const THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]);;

let evaluate_const = prove
 (`!xs env (s:(C,FFI)clos_state) res s1.
     clos_evaluate (xs,env,s) = (res,s1) ==>
     clos_state_max_app s1 = clos_state_max_app s`,
  MESON_TAC[CLOSPROPSAUX_evaluate_const_lemma]);;

let evaluate_app_const = prove
 (`!x1 x2 x3 (x4:(C,FFI)clos_state) res s1.
     evaluate_app x1 x2 x3 x4 = (res,s1) ==>
     clos_state_max_app s1 = clos_state_max_app x4`,
  MESON_TAC[CLOSPROPSAUX_evaluate_const_lemma]);;

(* a local helper for evaluate_code: the oracle and code of a later state   *)
(* come from those of an earlier one by installing n programs              *)
let CLOSPROPSAUX_code_inv_def = new_definition
 `CLOSPROPSAUX_code_inv (co:num -> C # clos_prog) (code:(num,num#clos_exp)fmap) co1 code1 <=>
    ?n. co1 = shift_seq n co /\
        let ls = FLAT (MAP (SND o SND) (list_of_seq co n)) in
        code1 = code |++ ls /\ ALL_DISTINCT (MAP FST ls) /\
        DISJOINT (FDOM code) (set_of_list (MAP FST ls))`;;

let CLOSPROPSAUX_code_inv_refl = prove
 (`!(co:num -> C # clos_prog) code. CLOSPROPSAUX_code_inv co code co code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSPROPSAUX_code_inv_def] THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES; ETA_AX; list_of_seq; MAP; FLAT; LET_DEF;
              LET_END_DEF; FUPDATE_LIST_THM; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY]);;

let CLOSPROPSAUX_code_inv_trans = prove
 (`!(co:num -> C # clos_prog) code co1 code1 co2 code2.
     CLOSPROPSAUX_code_inv co code co1 code1 /\
     CLOSPROPSAUX_code_inv co1 code1 co2 code2 ==>
     CLOSPROPSAUX_code_inv co code co2 code2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSPROPSAUX_code_inv_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `n2 + n1:num` THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REWRITE_TAC[GENLIST_APPEND; MAP_APPEND; FLAT_APPEND; FUPDATE_LIST_APPEND;
              ALL_DISTINCT_APPEND'; SET_OF_LIST_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; FDOM_FUPDATE_LIST]) THEN
  ASM_REWRITE_TAC[shift_seq_def; FUN_EQ_THM; ADD_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN ASM_REWRITE_TAC[ETA_AX] THEN
  ASM SET_TAC[]);;

let CLOSPROPSAUX_do_install_code = prove
 (`!vs (s:(C,FFI)clos_state) res s'.
     clos_do_install vs s = (res,s') ==>
     CLOSPROPSAUX_code_inv (clos_state_compile_oracle s) (clos_state_code s)
                           (clos_state_compile_oracle s') (clos_state_code s')`,
  RW[clos_do_install_def; clos_case_eq_thms] THEN
  TRY PAIRARG_TAC THEN GVS[clos_case_eq_thms; pair_case_eq; COND_CASE_EQ] THEN
  REWRITE_TAC[CLOSPROPSAUX_code_inv_refl] THEN
  REWRITE_TAC[CLOSPROPSAUX_code_inv_def] THEN EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[ONE; list_of_seq; APPEND; MAP; FLAT; o_THM; APPEND_NIL; LET_DEF;
                  LET_END_DEF; SND]);;

(* HOL4: evaluate_code_lemma *)
let CLOSPROPSAUX_evaluate_code_lemma = prove
 (`(!xs env (s:(C,FFI)clos_state) res s1.
      clos_evaluate (xs,env,s) = (res,s1) ==>
      CLOSPROPSAUX_code_inv (clos_state_compile_oracle s) (clos_state_code s)
                            (clos_state_compile_oracle s1) (clos_state_code s1)) /\
   (!loc_opt f args (s:(C,FFI)clos_state) res s1.
      evaluate_app loc_opt f args s = (res,s1) ==>
      CLOSPROPSAUX_code_inv (clos_state_compile_oracle s) (clos_state_code s)
                            (clos_state_compile_oracle s1) (clos_state_code s1))`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN CLOSPROPSAUX_SPLIT_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN
  IMP_RES_TAC clos_do_app_const THEN IMP_RES_TAC CLOSPROPSAUX_do_install_code THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM;
                  CLOSPROPSAUX_code_inv_refl] THEN
  ASM_MESON_TAC[CLOSPROPSAUX_code_inv_trans; CLOSPROPSAUX_code_inv_refl]);;

(* HOL4: evaluate_code *)
let clos_evaluate_code = prove
 (`!xs env (s:(C,FFI)clos_state) res s1.
     clos_evaluate (xs,env,s) = (res,s1) ==>
     ?n. clos_state_compile_oracle s1 = shift_seq n (clos_state_compile_oracle s) /\
         let ls = FLAT (MAP (SND o SND) (list_of_seq (clos_state_compile_oracle s) n)) in
         clos_state_code s1 = clos_state_code s |++ ls /\
         ALL_DISTINCT (MAP FST ls) /\
         DISJOINT (FDOM (clos_state_code s)) (set_of_list (MAP FST ls))`,
  REWRITE_TAC[GSYM CLOSPROPSAUX_code_inv_def] THEN
  MESON_TAC[CLOSPROPSAUX_evaluate_code_lemma]);;

let evaluate_app_code = prove
 (`!lopt f args (s:(C,FFI)clos_state) res s1.
     evaluate_app lopt f args s = (res,s1) ==>
     ?n. clos_state_compile_oracle s1 = shift_seq n (clos_state_compile_oracle s) /\
         let ls = FLAT (MAP (SND o SND) (list_of_seq (clos_state_compile_oracle s) n)) in
         clos_state_code s1 = clos_state_code s |++ ls /\
         ALL_DISTINCT (MAP FST ls) /\
         DISJOINT (FDOM (clos_state_code s)) (set_of_list (MAP FST ls))`,
  REWRITE_TAC[GSYM CLOSPROPSAUX_code_inv_def] THEN
  MESON_TAC[CLOSPROPSAUX_evaluate_code_lemma]);;

(* HOL4: evaluate_mono *)
let clos_evaluate_mono = prove
 (`!xs env (s1:(C,FFI)clos_state) vs s2.
     clos_evaluate (xs,env,s1) = (vs,s2) ==>
     clos_state_code s1 SUBMAP clos_state_code s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 CLOSPROPSAUX_evaluate_code_lemma)) THEN
  REWRITE_TAC[CLOSPROPSAUX_code_inv_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DISTINCT_FUPDATE_LIST_UNION; SUBMAP_FUNION_ID]);;

(* a local helper: do_app on an integer operation *)
let CLOSPROPSAUX_do_app_IntOp = prove
 (CASE_TERM `!i vs (s:(C,FFI)clos_state).
     clos_do_app (IntOp i) vs s =
     (match clos_do_int_app i vs with
        SOME res -> Rval (res,s)
      | NONE -> Rerr (Rabort Rtype_error))`,
  REWRITE_TAC[clos_do_app_def; pair_CASE; case_def "clos_op"]);;

let evaluate_MAP_Op_Const = prove
 (`!tra (f:A->int) env (s:(C,FFI)clos_state) ls.
     clos_evaluate (MAP (\x. clos_Op tra (IntOp (clos_Const (f x))) []) ls,env,s) =
     (Rval (MAP (clos_Number o f) ls),s)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ls:A list`,`ls:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; clos_evaluate_def] THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_evaluate_def; pair_CASE; case_def "result"; LET_DEF; LET_END_DEF;
              distinctness "clos_op"; REVERSE; CLOSPROPSAUX_do_app_IntOp;
              clos_do_int_app_def; case_def "option"; HD; o_THM] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"]);;

let lookup_vars_NONE = prove
 (`!vs (env:A list). lookup_vars vs env = NONE <=> ?v. MEM v vs /\ LENGTH env <= v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; MEM; distinctness "option"] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `env:A list`) THEN
    CASES_ON `lookup_vars (t:num list) (env:A list)` THEN
    REWRITE_TAC[case_def "option"; distinctness "option"] THEN DISCH_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `v:num` THEN
      ASM_CASES_TAC `v:num = h` THEN ASM_REWRITE_TAC[NOT_LE] THEN
      ASM_MESON_TAC[NOT_LE]];
    EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[GSYM NOT_LT]]);;

let lookup_vars_SOME = prove
 (`!vs (env:A list) xs. lookup_vars vs env = SOME xs ==> LENGTH vs = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; injectivity "option"] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `lookup_vars (t:num list) (env:A list)` THEN
    REWRITE_TAC[case_def "option"; distinctness "option"; injectivity "option"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 states it with free variables (SPEC_ALL) *)
let lookup_vars_MEM = prove
 (`!ys n x (env2:clos_v list).
     lookup_vars ys env2 = SOME x /\ n < LENGTH ys ==>
     EL n ys < LENGTH env2 /\ EL n x = EL (EL n ys) env2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  CASES_ON `lookup_vars (t:num list) (env2:clos_v list)` THEN
  REWRITE_TAC[case_def "option"; distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; LT_0; LT_SUC] THEN ASM_MESON_TAC[]);;

(* HOL4: clock_lemmas *)
let clos_clock_lemmas = prove
 (`!s:(C,FFI)clos_state. clos_state_clock_fupd (K (clos_state_clock s)) s = s`,
  REWRITE_TAC[clos_with_same_clock]);;

let evaluate_app_rw = prove
 (CASE_TERM `!args loc_opt f (s:(C,FFI)clos_state).
     ~(args = []) ==>
     evaluate_app loc_opt f args s =
     match dest_closure (clos_state_max_app s) loc_opt f args with
       NONE -> (Rerr (Rabort Rtype_error),s)
     | SOME (Partial_app v) ->
         if clos_state_clock s < LENGTH args then
           (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
         else (Rval [v], clos_dec_clock (LENGTH args) s)
     | SOME (Full_app exp env rest_args) ->
         if clos_state_clock s < LENGTH args - LENGTH rest_args then
           (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
         else
           (match clos_evaluate ([exp],env,clos_dec_clock (LENGTH args - LENGTH rest_args) s)
            with
              (Rval [v], s1) -> evaluate_app loc_opt v rest_args s1
            | res -> res)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_evaluate_def]);;

(* local helpers for EVERY_pure_correct: pure operations neither change the *)
(* state nor raise                                                          *)
let CLOSPROPSAUX_pure_do_app = prove
 (`!op vs (s:(C,FFI)clos_state) r.
     clos_pure_op op /\ clos_do_app op vs s = r ==>
     (?v. r = Rval (v,s)) \/ r = Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[clos_pure_op_def; injectivity "result"; distinctness "result"; PAIR_EQ;
              EXISTS_REFL; case_def "clos_op"; case_def "mem_op"; case_def "glob_op"] THEN
  MESON_TAC[]);;

let CLOSPROPSAUX_not_pure_op = prove
 (`~clos_pure_op clos_Install /\ (!t. ~clos_pure_op (clos_ThunkOp t))`,
  REWRITE_TAC[clos_pure_op_def; case_def "clos_op"]);;

let CLOSPROPSAUX_pure_lemma = prove
 (`(!es E (s:(C,FFI)clos_state). ALL pure es ==>
      !res s'. clos_evaluate (es,E,s) = (res,s') ==>
        (?vs. res = Rval vs /\ s' = s /\ LENGTH vs = LENGTH es) \/
        res = Rerr (Rabort Rtype_error)) /\
   (!(n:num option) (v:clos_v) (vl:clos_v list) (s:(C,FFI)clos_state). T)`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN TRY CLOSPROPSAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pure_def; ALL; CLOSPROPSAUX_not_pure_op]) THEN
  CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC CLOSPROPSAUX_pure_do_app THEN CLOSPROPSAUX_CLEAN_TAC THEN
  ASM_REWRITE_TAC[LENGTH; injectivity "result"; distinctness "result"; UNWIND_THM1;
                  UNWIND_THM2; SUC_INJ]);;

(* HOL4: EVERY_pure_correct (after its SIMP_RULE: the trivial second      *)
(* conjunct is dropped and t = (es,E,s) is eliminated)                     *)
(* a local helper: specialise an antecedent !x y. (a,b) = (x,y) ==> P x y *)
let CLOSPROPSAUX_SPEC_PAIR_TAC : tactic =
  DISCH_THEN(fun th ->
    let vs,bd = strip_forall (concl th) in
    let x,s = dest_pair (lhand(fst(dest_imp bd))) in
    MP_TAC (REWRITE_RULE[] (SPECL [x;s] th)));;

let EVERY_pure_correct = prove
 (CASE_TERM `!es E (s:(C,FFI)clos_state).
     ALL pure es ==>
     match clos_evaluate (es,E,s) with
       (Rval vs,s') -> s' = s /\ LENGTH vs = LENGTH es
     | (Rerr (Rraise a),_) -> F
     | (Rerr (Rabort a),_) -> a = Rtype_error`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`es:clos_exp list`; `E:clos_v list`; `s:(C,FFI)clos_state`]
               (CONJUNCT1 CLOSPROPSAUX_pure_lemma)) THEN
  ASM_REWRITE_TAC[] THEN
  CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (es,E,s:(C,FFI)clos_state)` "r" "s1" THEN
  CLOSPROPSAUX_SPEC_PAIR_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; UNWIND_THM1] THEN
  TRY(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[case_def "error_result"]);;

let pure_correct = prove
 (CASE_TERM `!e env (s:(C,FFI)clos_state).
     pure e ==>
     match clos_evaluate ([e],env,s) with
       (Rval vs,s') -> s' = s /\ LENGTH vs = 1
     | (Rerr (Rraise a),_) -> F
     | (Rerr (Rabort a),_) -> a = Rtype_error`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[e:clos_exp]`; `env:clos_v list`; `s:(C,FFI)clos_state`]
               EVERY_pure_correct) THEN
  ASM_REWRITE_TAC[ALL; LENGTH; ONE]);;

let evaluate_pure = prove
 (`!xs env (s:(C,FFI)clos_state) res t.
     clos_evaluate (xs,env,s) = (res,t) /\ ALL pure xs ==>
     ?vs. res = Rval vs /\ t = s \/ res = Rerr (Rabort Rtype_error)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`xs:clos_exp list`; `env:clos_v list`; `s:(C,FFI)clos_state`]
               (CONJUNCT1 CLOSPROPSAUX_pure_lemma)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`res:(clos_v list,clos_v)result`;
                                                     `t:(C,FFI)clos_state`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: pair_lam_lem [local] *)
let clos_pair_lam_lem = prove
 (CASE_TERM `!(f:A->B->C) v z.
     (let (x,y) = z in f x y) = v <=> ?x1 x2. z = (x1,x2) /\ f x1 x2 = v`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4: do_app_split_list *)
let clos_do_app_split_list = prove
 (`!op vs (s:(C,FFI)clos_state) res.
     clos_do_app op vs s = res <=>
     vs = [] /\ clos_do_app op [] s = res \/
     ?v vs1. vs = CONS v vs1 /\ clos_do_app op (CONS v vs1) s = res`,
  REPEAT GEN_TAC THEN CASES_ON `vs:clos_v list` THEN
  REWRITE_TAC[distinctness "list"; injectivity "list"] THEN MESON_TAC[]);;

(* a local tactic for the dest_closure lemmas: split the closure, unfold    *)
(* dest_closure, split its conditions and simplify                          *)
let CLOSPROPSAUX_DC_SIMPS =
  [check_loc_def; DROP_NIL; LENGTH_REVERSE; REVERSE_EQ_EMPTY; SUB_0; LENGTH_DROP;
   distinctness "option"; injectivity "option"; distinctness "app_kind";
   injectivity "app_kind"; LET_DEF; LET_END_DEF; DE_MORGAN_THM];;

let CLOSPROPSAUX_DC_TAC (f:term) : tactic =
  CASES_ON f THEN
  REWRITE_TAC[dest_closure_def; case_def "clos_v"; distinctness "option"] THEN
  TRY PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN REPEAT STRIP_TAC THEN GVS CLOSPROPSAUX_DC_SIMPS;;

let dest_closure_none_loc = prove
 (`!max_app l cl vs v e env rest.
     (dest_closure max_app l cl vs = SOME (Partial_app v) ==> l = NONE) /\
     (dest_closure max_app l cl vs = SOME (Full_app e env rest) /\ ~(rest = [])
      ==> l = NONE)`,
  REPEAT GEN_TAC THEN CASES_ON `l:num option` THEN REWRITE_TAC[distinctness "option"] THEN
  CLOSPROPSAUX_DC_TAC `cl:clos_v`);;

(* HOL4 [simp] *)
let is_closure_def = sem1aux_def
  `(is_closure (clos_Closure _ _ _ _ _) <=> T) /\
   (is_closure (clos_Recclosure _ _ _ _ _) <=> T) /\
   (is_closure _ <=> F)`;;
let _ = cake_add_simps [is_closure_def];;

(* HOL4 [simp] *)
let clo_to_loc_def = sem1aux_def
  `(clo_to_loc (clos_Closure l _ _ _ _) = l) /\
   (clo_to_loc (clos_Recclosure l _ _ _ i) = OPTION_MAP ((+) (2 * i)) l)`;;
let _ = cake_add_simps [clo_to_loc_def];;

(* HOL4 [simp] *)
let clo_to_env_def = sem1aux_def
  `(clo_to_env (clos_Closure _ _ env _ _) = env) /\
   (clo_to_env (clos_Recclosure loc _ env fns _) =
      APPEND (list_of_seq (clos_Recclosure loc [] env fns) (LENGTH fns)) env)`;;
let _ = cake_add_simps [clo_to_env_def];;

(* HOL4 [simp] *)
let clo_to_partial_args_def = sem1aux_def
  `(clo_to_partial_args (clos_Closure _ args _ _ _) = args) /\
   (clo_to_partial_args (clos_Recclosure _ args _ _ _) = args)`;;
let _ = cake_add_simps [clo_to_partial_args_def];;

(* HOL4 [simp] *)
let clo_add_partial_args_def = sem1aux_def
  `(clo_add_partial_args args (clos_Closure x1 args' x2 x3 x4) =
      clos_Closure x1 (APPEND args args') x2 x3 x4) /\
   (clo_add_partial_args args (clos_Recclosure y1 args' y2 y3 y4) =
      clos_Recclosure y1 (APPEND args args') y2 y3 y4)`;;
let _ = cake_add_simps [clo_add_partial_args_def];;

(* HOL4 [simp] *)
let clo_to_num_params_def = sem1aux_def
  `(clo_to_num_params (clos_Closure _ _ _ n _) = n) /\
   (clo_to_num_params (clos_Recclosure _ _ _ fns i) = FST (EL i fns))`;;
let _ = cake_add_simps [clo_to_num_params_def];;

(* HOL4 [simp] *)
let rec_clo_ok_def = sem1aux_def
  `(rec_clo_ok (clos_Recclosure _ _ _ fns i) <=> i < LENGTH fns) /\
   (rec_clo_ok (clos_Closure _ _ _ _ _) <=> T)`;;
let _ = cake_add_simps [rec_clo_ok_def];;

let dest_closure_full_length = prove
 (`!max_app l v vs e args rest.
     dest_closure max_app l v vs = SOME (Full_app e args rest) ==>
     LENGTH (clo_to_partial_args v) < clo_to_num_params v /\
     LENGTH vs + LENGTH (clo_to_partial_args v) = clo_to_num_params v + LENGTH rest /\
     LENGTH args = clo_to_num_params v + LENGTH (clo_to_env v)`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `v:clos_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REVERSE; LENGTH_DROP; FST;
                  LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LENGTH_REVERSE; ARITH_RULE
    `~(a + b < n) /\ b < n ==> n - b <= a`] THEN
  ASM_ARITH_TAC);;
let evaluate_app_clock_less = prove
 (`!loc_opt f args (s1:(C,FFI)clos_state) vs s2.
     ~(args = []) /\ evaluate_app loc_opt f args s1 = (Rval vs,s2) ==>
     clos_state_clock s2 < clos_state_clock s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC CLOSPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC dest_closure_length THEN
  IMP_RES_TAC (CONJUNCT1 clos_evaluate_clock) THEN IMP_RES_TAC (CONJUNCT2 clos_evaluate_clock) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  (SUBGOAL_THEN `~(LENGTH (args:clos_v list) = 0)` MP_TAC THENL
    [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC);;

(* HOL4 [simp] *)
let clo_add_partial_args_nil = prove
 (`!x. is_closure x ==> clo_add_partial_args [] x = x`,
  GEN_TAC THEN CASES_ON `x:clos_v` THEN
  REWRITE_TAC[is_closure_def; clo_add_partial_args_def; APPEND]);;
let _ = cake_add_simps [clo_add_partial_args_nil];;

let clo_can_apply_def = cake_def
  `clo_can_apply loc cl num_args <=>
     LENGTH (clo_to_partial_args cl) < clo_to_num_params cl /\
     rec_clo_ok cl /\
     (~(loc = NONE) ==>
      loc = clo_to_loc cl /\
      num_args = clo_to_num_params cl /\
      clo_to_partial_args cl = [])`;;

let check_closures_def = cake_def
  `check_closures cl cl' <=>
     !loc num_args.
       clo_can_apply loc cl num_args ==> clo_can_apply loc cl' num_args`;;

let dest_closure_partial_is_closure = prove
 (`!max_app l v vs v'.
     dest_closure max_app l v vs = SOME (Partial_app v') ==> is_closure v'`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `v:clos_v` THEN
  REWRITE_TAC[is_closure_def]);;

let is_closure_add_partial_args_nil = prove
 (`!v. is_closure v ==> clo_add_partial_args [] v = v`,
  REWRITE_TAC[clo_add_partial_args_nil]);;

(* closSem's dest_closure_length quantifies an unused so_far *)
let CLOSPROPSAUX_dest_closure_length = prove
 (`!max_app loc_opt f args exp args1 args2.
     dest_closure max_app loc_opt f args = SOME (Full_app exp args1 args2)
     ==> LENGTH args2 < LENGTH args`,
  MESON_TAC[dest_closure_length]);;

let evaluate_app_clock0 = prove
 (`!lopt r args (s0:(C,FFI)clos_state) vs s.
     clos_state_clock s0 = 0 /\ ~(args = []) ==>
     ~(evaluate_app lopt r args s0 = (Rval vs,s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(LENGTH (args:clos_v list) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC CLOSPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC CLOSPROPSAUX_dest_closure_length THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC);;

let evaluate_app_clock0_timeout = prove
 (`!lopt r args (s0:(C,FFI)clos_state) e s.
     clos_state_clock s0 = 0 /\ ~(args = []) /\
     evaluate_app lopt r args s0 = (Rerr e,s) /\
     ~(e = Rabort Rtype_error) ==>
     e = Rabort Rtimeout_error`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SUBGOAL_THEN `~(LENGTH (args:clos_v list) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC CLOSPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC CLOSPROPSAUX_dest_closure_length THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC);;
let evaluate_app_clock_drop = prove
 (`!args f lopt (s0:(C,FFI)clos_state) s vs.
     evaluate_app lopt f args s0 = (Rval vs,s) ==>
     clos_state_clock s + LENGTH args <= clos_state_clock s0`,
  SUBGOAL_THEN
   `!n args f lopt (s0:(C,FFI)clos_state) s vs.
      LENGTH args = n ==>
      evaluate_app lopt f args s0 = (Rval vs,s) ==>
      clos_state_clock s + LENGTH args <= clos_state_clock s0`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ASM_CASES_TAC `args:clos_v list = []` THENL
   [ASM_REWRITE_TAC[evaluate_app_NIL; PAIR_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN REWRITE_TAC[LENGTH; ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC CLOSPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC clos_evaluate_SING THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC CLOSPROPSAUX_dest_closure_length THEN
  IMP_RES_TAC (CONJUNCT1 clos_evaluate_clock) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (a2:clos_v list)`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`a2:clos_v list`; `r1:clos_v`; `lopt:num option`;
                                 `y:(C,FFI)clos_state`; `s:(C,FFI)clos_state`;
                                 `vs:clos_v list`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC);;
let dest_closure_is_closure = prove
 (`!max_app lopt f vs r. dest_closure max_app lopt f vs = SOME r ==> is_closure f`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN
  REWRITE_TAC[is_closure_def; dest_closure_def; case_def "clos_v"; distinctness "option"]);;

let stage_partial_app = prove
 (`!max_app c v rest used.
     is_closure c /\
     dest_closure max_app NONE v (APPEND rest used) =
       SOME (Partial_app (clo_add_partial_args rest c)) ==>
     dest_closure max_app NONE c rest =
       SOME (Partial_app (clo_add_partial_args rest c))`,
  REPEAT GEN_TAC THEN CASES_ON `c:clos_v` THEN REWRITE_TAC[is_closure_def] THEN
  CLOSPROPSAUX_DC_TAC `v:clos_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND_LCANCEL]) THEN
  RVEQ_TAC THEN REWRITE_TAC[LENGTH_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let dest_closure_full_addargs = prove
 (`!max_app c vs b env r more.
     dest_closure max_app NONE c vs = SOME (Full_app b env r) /\
     LENGTH more + LENGTH vs <= max_app ==>
     dest_closure max_app NONE c (APPEND more vs) =
     SOME (Full_app b env (APPEND more r))`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `c:clos_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
  TRY ASM_ARITH_TAC THEN
  ASM_SIMP_TAC[REVERSE_APPEND; TAKE_APPEND1; DROP_APPEND1; LENGTH_REVERSE; REVERSE_REVERSE;
               ARITH_RULE `~(v + a < n) ==> n - a <= v`]);;
(* HOL4: evaluate_append *)
let clos_evaluate_append = prove
 (CASE_TERM `!es1 es2 env (s:(C,FFI)clos_state).
     clos_evaluate (APPEND es1 es2,env,s) =
     match clos_evaluate (es1,env,s) with
       (Rval vs1,s') ->
         (match clos_evaluate (es2,env,s') with
            (Rval vs2,s'') -> (Rval (APPEND vs1 vs2),s'')
          | x -> x)
     | x -> x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_evaluate_APPEND] THEN
  CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (es1,env,s:(C,FFI)clos_state)` "r" "s1" THEN
  CLOSPROPSAUX_PAIR_RESULT_TAC `clos_evaluate (es2,env,s1:(C,FFI)clos_state)` "r2" "s2");;

let evaluate_GENLIST_Var = prove
 (`!tra n env (s:(C,FFI)clos_state).
     clos_evaluate (list_of_seq (clos_Var tra) n,env,s) =
     if n <= LENGTH env then (Rval (TAKE n env),s)
     else (Rerr (Rabort Rtype_error),s)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; clos_evaluate_def; LE_0; TAKE_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[list_of_seq; clos_evaluate_APPEND] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n <= LENGTH (env:clos_v list)` THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; clos_evaluate_def] THENL
   [ASM_CASES_TAC `n < LENGTH (env:clos_v list)` THEN
    ASM_REWRITE_TAC[pair_CASE; case_def "result"; LE_SUC_LT] THEN
    REWRITE_TAC[GSYM SNOC_APPEND] THEN ASM_SIMP_TAC[SNOC_EL_TAKE];
    SUBGOAL_THEN `~(SUC n <= LENGTH (env:clos_v list))` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

let evaluate_length_imp = prove
 (`!es env (s1:(C,FFI)clos_state) vs s2.
     clos_evaluate (es,env,s1) = (Rval vs,s2) ==> LENGTH es = LENGTH vs`,
  REWRITE_TAC[clos_evaluate_IMP_LENGTH]);;

let evaluate_app_length_imp = prove
 (`!l f args (s:(C,FFI)clos_state) vs s2.
     evaluate_app l f args s = (Rval vs,s2) ==> LENGTH vs = 1`,
  REWRITE_TAC[evaluate_app_IMP_LENGTH]);;
let dest_closure_none_append = prove
 (`!max_app (l:A) f args1 args2.
     dest_closure max_app NONE f args2 = NONE ==>
     dest_closure max_app NONE f (APPEND args1 args2) = NONE`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `f:clos_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC);;

let dest_closure_none_append2 = prove
 (`!max_app (l:A) f args1 args2.
     LENGTH args1 + LENGTH args2 <= max_app /\
     dest_closure max_app NONE f (APPEND args1 args2) = NONE ==>
     dest_closure max_app NONE f args2 = NONE`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `f:clos_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC);;

let dest_closure_rest_length = prove
 (`!max_app f args e l rest.
     dest_closure max_app NONE f args = SOME (Full_app e l rest) ==>
     LENGTH rest < LENGTH args`,
  MESON_TAC[CLOSPROPSAUX_dest_closure_length]);;
let CLOSPROPSAUX_rev_take_append = prove
 (`!k (args1:A list) args2.
     LENGTH args2 <= k ==>
     REVERSE (TAKE k (REVERSE (APPEND args1 args2))) =
     APPEND (REVERSE (TAKE (k - LENGTH args2) (REVERSE args1))) args2`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REVERSE_APPEND; TAKE_APPEND2; LENGTH_REVERSE; REVERSE_REVERSE]);;

let CLOSPROPSAUX_rev_drop_append = prove
 (`!k (args1:A list) args2.
     LENGTH args2 <= k ==>
     REVERSE (DROP k (REVERSE (APPEND args1 args2))) =
     REVERSE (DROP (k - LENGTH args2) (REVERSE args1))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REVERSE_APPEND; DROP_APPEND2; LENGTH_REVERSE]);;

let dest_closure_partial_twice = prove
 (`!max_app f args1 args2 cl res.
     LENGTH args1 + LENGTH args2 <= max_app /\
     dest_closure max_app NONE f (APPEND args1 args2) = res /\
     dest_closure max_app NONE f args2 = SOME (Partial_app cl)
     ==> dest_closure max_app NONE cl args1 = res`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC)) THEN
  CLOSPROPSAUX_DC_TAC `f:clos_v` THEN
  REWRITE_TAC[dest_closure_def; case_def "clos_v"; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN BETA_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  REWRITE_TAC[check_loc_def; LENGTH_APPEND] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"; injectivity "app_kind";
     distinctness "option"; distinctness "app_kind"; injectivity "clos_v"; APPEND_ASSOC] THEN
  TRY ASM_ARITH_TAC THEN
  ASM_SIMP_TAC[CLOSPROPSAUX_rev_take_append; CLOSPROPSAUX_rev_drop_append;
               ARITH_RULE `b + a < n ==> b <= n - a`;
               ARITH_RULE `(n:num) - a - b = n - (b + a)`; APPEND_ASSOC] THEN
  ASM_ARITH_TAC);;
let CLOSPROPSAUX_none_append = prove
 (`!max_app f args1 args2.
     dest_closure max_app NONE f args2 = NONE ==>
     dest_closure max_app NONE f (APPEND args1 args2) = NONE`,
  MESON_TAC[ISPEC `ARB:num` (GEN `l:A` (SPEC_ALL dest_closure_none_append))]);;

let CLOSPROPSAUX_none_append2 = prove
 (`!max_app f args1 args2.
     LENGTH args1 + LENGTH args2 <= max_app /\
     dest_closure max_app NONE f (APPEND args1 args2) = NONE ==>
     dest_closure max_app NONE f args2 = NONE`,
  MESON_TAC[ISPEC `ARB:num` (GEN `l:A` (SPEC_ALL dest_closure_none_append2))]);;

(* dec_clock twice; a timeout state after dec_clock *)
let CLOSPROPSAUX_dec_clock_dec_clock = prove
 (`!k1 k2 (s:(C,FFI)clos_state).
     clos_dec_clock k1 (clos_dec_clock k2 s) = clos_dec_clock (k2 + k1) s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let CLOSPROPSAUX_dec_clock_clock0 = prove
 (`!k (s:(C,FFI)clos_state).
     clos_state_clock_fupd (K 0) (clos_dec_clock k s) = clos_state_clock_fupd (K 0) s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM]);;
let CLOSPROPSAUX_max_app_dec_clock = prove
 (`!k (s:(C,FFI)clos_state).
     clos_state_max_app (clos_dec_clock k s) = clos_state_max_app s /\
     clos_state_clock (clos_dec_clock k s) = clos_state_clock s - k`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_app_append_partial = prove
 (`!f args1 args2 (s:(C,FFI)clos_state) cl.
     ~(args2 = []) /\ LENGTH (APPEND args1 args2) <= clos_state_max_app s /\
     dest_closure (clos_state_max_app s) NONE f args2 = SOME (Partial_app cl) ==>
     evaluate_app NONE f (APPEND args1 args2) s =
     (if clos_state_clock s < LENGTH args2
      then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
      else evaluate_app NONE cl args1 (clos_dec_clock (LENGTH args2) s))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `args1:clos_v list = []` THENL
   [ASM_SIMP_TAC[APPEND; evaluate_app_rw; case_def "option"; case_def "app_kind";
                 evaluate_app_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(APPEND args1 args2:clos_v list = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APPEND_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(ISPEC `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) NONE f
                  (APPEND args1 args2)` (cases "option")) THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `f:clos_v`;
                  `args1:clos_v list`; `args2:clos_v list`] CLOSPROPSAUX_none_append2) THEN
    ASM_REWRITE_TAC[GSYM LENGTH_APPEND; distinctness "option"];
    ALL_TAC] THEN
  MP_TAC(SPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `f:clos_v`;
                `args1:clos_v list`; `args2:clos_v list`; `cl:clos_v`;
                `SOME (a:app_kind)`] dest_closure_partial_twice) THEN
  ASM_REWRITE_TAC[GSYM LENGTH_APPEND] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[evaluate_app_rw; CLOSPROPSAUX_max_app_dec_clock; case_def "option"] THEN
  CASES_ON `a:app_kind` THEN REWRITE_TAC[case_def "app_kind"] THENL
   [ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) < LENGTH (args2:clos_v list)` THEN
    ASM_REWRITE_TAC[CLOSPROPSAUX_dec_clock_clock0; CLOSPROPSAUX_dec_clock_dec_clock;
                    LENGTH_APPEND] THEN
    ASM_SIMP_TAC[ARITH_RULE `x < b ==> x < a + b:num`; ADD_SYM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP dest_closure_rest_length) THEN
  ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) < LENGTH (args2:clos_v list)` THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_dec_clock_clock0; CLOSPROPSAUX_dec_clock_dec_clock;
                  LENGTH_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THENL
   [SUBGOAL_THEN `clos_state_clock (s:(C,FFI)clos_state) <
                  (LENGTH (args1:clos_v list) + LENGTH (args2:clos_v list)) - LENGTH (a2:clos_v list)`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (args2:clos_v list) + (LENGTH (args1:clos_v list) - LENGTH (a2:clos_v list)) =
                (LENGTH args1 + LENGTH args2) - LENGTH a2` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `clos_state_clock (s:(C,FFI)clos_state) - LENGTH (args2:clos_v list) <
                LENGTH (args1:clos_v list) - LENGTH (a2:clos_v list) <=>
                clos_state_clock s < (LENGTH args1 + LENGTH args2) - LENGTH a2` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;
let CLOSPROPSAUX_app_append_full = prove
 (CASE_TERM `!f args1 args2 (s:(C,FFI)clos_state) exp env rest.
     ~(args2 = []) /\ LENGTH (APPEND args1 args2) <= clos_state_max_app s /\
     dest_closure (clos_state_max_app s) NONE f args2 = SOME (Full_app exp env rest) ==>
     evaluate_app NONE f (APPEND args1 args2) s =
     (if clos_state_clock s < LENGTH args2 - LENGTH rest
      then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
      else
        match clos_evaluate ([exp],env,clos_dec_clock (LENGTH args2 - LENGTH rest) s) with
          (Rval [v],s1) -> evaluate_app NONE v (APPEND args1 rest) s1
        | res -> res)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(APPEND args1 args2:clos_v list = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APPEND_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(SPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `f:clos_v`; `args2:clos_v list`;
                `exp:clos_exp`; `env:clos_v list`; `rest:clos_v list`; `args1:clos_v list`]
               dest_closure_full_addargs) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ASM_SIMP_TAC[evaluate_app_rw; case_def "option"; case_def "app_kind"] THEN
  REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `(a + b) - (a + c) = b - c:num`]);;
(* a local helper: case-split a term of type result # state, keeping its *)
(* equation as an assumption *)
let CLOSPROPSAUX_PAIR_RESULT_ASM_TAC (tm:term) (rn:string) (sn:string) : tactic =
  fun (asl,w as gl) ->
    let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b
                   | _ -> failwith "PAIR_RESULT_ASM_TAC") in
    let r = mk_var(rn,rty) and s = mk_var(sn,sty) in
    (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
     ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
     CASES_ON r THEN REWRITE_TAC[pair_CASE; case_def "result"] THEN DISCH_TAC) gl;;

let CLOSPROPSAUX_evaluate_app_append = prove
 (CASE_TERM `!n args2 f args1 (s:(C,FFI)clos_state).
     LENGTH args2 = n /\
     LENGTH (APPEND args1 args2) <= clos_state_max_app s ==>
     evaluate_app NONE f (APPEND args1 args2) s =
     match evaluate_app NONE f args2 s with
       (Rval vs1,s1) -> evaluate_app NONE (HD vs1) args1 s1
     | err -> err`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `args2:clos_v list = []` THENL
   [ASM_REWRITE_TAC[APPEND_NIL; evaluate_app_NIL; pair_CASE; case_def "result"; HD];
    ALL_TAC] THEN
  MP_TAC(ISPEC `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) NONE f args2`
               (cases "option")) THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `~(APPEND args1 args2:clos_v list = [])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APPEND_EQ_NIL]; ALL_TAC] THEN
    ASM_SIMP_TAC[evaluate_app_rw; case_def "option"; CLOSPROPSAUX_none_append; pair_CASE;
                 case_def "result"];
    ALL_TAC] THEN
  CASES_ON `a:app_kind` THENL
   [MP_TAC(SPECL [`f:clos_v`; `args1:clos_v list`; `args2:clos_v list`;
                  `s:(C,FFI)clos_state`; `a':clos_v`] CLOSPROPSAUX_app_append_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[evaluate_app_rw; case_def "option"; case_def "app_kind"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[pair_CASE; case_def "result"; HD];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:clos_v`; `args1:clos_v list`; `args2:clos_v list`;
                `s:(C,FFI)clos_state`; `a0:clos_exp`; `a1:clos_v list`; `a2:clos_v list`]
               CLOSPROPSAUX_app_append_full) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[evaluate_app_rw; case_def "option"; case_def "app_kind"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[pair_CASE; case_def "result"] THEN
  CLOSPROPSAUX_PAIR_RESULT_ASM_TAC
    `clos_evaluate ([a0:clos_exp],a1:clos_v list,
                    clos_dec_clock (LENGTH (args2:clos_v list) - LENGTH (a2:clos_v list))
                                   (s:(C,FFI)clos_state))` "r" "s1" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[case_def "list"] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP dest_closure_rest_length) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_const) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSPROPSAUX_max_app_dec_clock]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (a2:clos_v list)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN REWRITE_TAC[LENGTH_APPEND] THEN
  ASM_ARITH_TAC);;

let evaluate_app_append = prove
 (CASE_TERM `!args2 f args1 (s:(C,FFI)clos_state).
     LENGTH (APPEND args1 args2) <= clos_state_max_app s ==>
     evaluate_app NONE f (APPEND args1 args2) s =
     match evaluate_app NONE f args2 s with
       (Rval vs1,s1) -> evaluate_app NONE (HD vs1) args1 s1
     | err -> err`,
  MESON_TAC[CLOSPROPSAUX_evaluate_app_append]);;
(* HOL4 [local] *)
let revnil = prove
 (`!l:A list. [] = REVERSE l <=> l = []`,
  MESON_TAC[REVERSE_EQ_EMPTY]);;

let dest_closure_full_maxapp = prove
 (`!max_app c vs b env r.
     dest_closure max_app NONE c vs = SOME (Full_app b env r) /\ ~(r = []) ==>
     LENGTH vs <= max_app`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `c:clos_v`);;
let CLOSPROPSAUX_split_lemma = prove
 (`!k (vs:A list). k <= LENGTH vs ==>
     APPEND (REVERSE (DROP k (REVERSE vs))) (REVERSE (TAKE k (REVERSE vs))) = vs /\
     LENGTH (REVERSE (TAKE k (REVERSE vs))) = k /\
     REVERSE (TAKE k (REVERSE (REVERSE (TAKE k (REVERSE vs))))) =
       REVERSE (TAKE k (REVERSE vs)) /\
     REVERSE (DROP k (REVERSE (REVERSE (TAKE k (REVERSE vs))))) = []`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM REVERSE_APPEND; TAKE_DROP; REVERSE_REVERSE; LENGTH_REVERSE;
               LENGTH_TAKE; TAKE_TAKE_T; LE_REFL; REVERSE_EQ_EMPTY; DROP_NIL]);;

let dest_closure_full_split' = prove
 (`!max_app loc v vs e env rest.
     dest_closure max_app loc v vs = SOME (Full_app e env rest) ==>
     ?used. vs = APPEND rest used /\
            dest_closure max_app loc v used = SOME (Full_app e env [])`,
  REPEAT GEN_TAC THEN CASES_ON `v:clos_v` THEN
  REWRITE_TAC[dest_closure_def; case_def "clos_v"; distinctness "option"] THEN
  TRY PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; injectivity "app_kind";
              distinctness "app_kind"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ((EXISTS_TAC `REVERSE (TAKE (a3 - LENGTH (a1:clos_v list)) (REVERSE (vs:clos_v list)))` THEN
    SUBGOAL_THEN `a3 - LENGTH (a1:clos_v list) <= LENGTH (vs:clos_v list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC]) ORELSE
   (EXISTS_TAC `REVERSE (TAKE (num_args - LENGTH (a1:clos_v list)) (REVERSE (vs:clos_v list)))` THEN
    SUBGOAL_THEN `num_args - LENGTH (a1:clos_v list) <= LENGTH (vs:clos_v list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC])) THEN
  ASM_SIMP_TAC[CLOSPROPSAUX_split_lemma] THEN
  CASES_ON `loc:num option` THEN RULE_ASSUM_TAC(REWRITE_RULE[check_loc_def]) THEN
  ASM_REWRITE_TAC[check_loc_def] THEN TRY(POP_ASSUM STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[LENGTH_APPEND; SUB_0; ARITH_RULE `a <= b ==> a <= b + c:num`] THEN
  TRY ASM_ARITH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let dest_closure_partial_split = prove
 (`!max_app v1 vs v2 n.
     dest_closure max_app NONE v1 vs = SOME (Partial_app v2) /\ n <= LENGTH vs ==>
     ?v3. dest_closure max_app NONE v1 (DROP n vs) = SOME (Partial_app v3) /\
          v2 = clo_add_partial_args (TAKE n vs) v3`,
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `v1:clos_v` THEN TRY ASM_ARITH_TAC);;

let dest_closure_partial_split' = prove
 (`!max_app n v vs cl.
     dest_closure max_app NONE v vs = SOME (Partial_app cl) /\ n <= LENGTH vs ==>
     ?cl0 used rest.
       vs = APPEND rest used /\ LENGTH rest = n /\
       dest_closure max_app NONE v used = SOME (Partial_app cl0) /\
       cl = clo_add_partial_args rest cl0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`max_app:num`; `v:clos_v`; `vs:clos_v list`; `cl:clos_v`; `n:num`]
               dest_closure_partial_split) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v3:clos_v` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v3:clos_v`; `DROP n (vs:clos_v list)`; `TAKE n (vs:clos_v list)`] THEN
  ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE]);;
let CLOSPROPSAUX_take_rev = prove
 (`!n (l:A list). n = LENGTH l ==>
     TAKE n (REVERSE l) = REVERSE l /\ DROP n (REVERSE l) = []`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[TAKE_LENGTH_TOO_LONG; DROP_NIL; LENGTH_REVERSE; LE_REFL]);;

let dest_closure_NONE_Full_to_Partial = prove
 (`!max_app v l1 l2 b env.
     dest_closure max_app NONE v (APPEND l1 l2) = SOME (Full_app b env []) /\
     ~(l1 = []) ==>
     ?cl. dest_closure max_app NONE v l2 = SOME (Partial_app cl) /\
          dest_closure max_app NONE cl l1 = SOME (Full_app b env [])`,
  let fin n =
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    SUBGOAL_THEN (subst [n,`n:num`]
      `n - (LENGTH (l2:clos_v list) + LENGTH (a1:clos_v list)) = LENGTH (l1:clos_v list) /\
       n - LENGTH a1 = LENGTH (APPEND l1 l2)`) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSPROPSAUX_take_rev; REVERSE_REVERSE; REVERSE; APPEND_ASSOC] in
  REPEAT GEN_TAC THEN CLOSPROPSAUX_DC_TAC `v:clos_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  (SUBGOAL_THEN `~(LENGTH (l1:clos_v list) = 0)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC]) THEN
  TRY ASM_ARITH_TAC THENL
   [fin `a3:num`; fin `num_args:num`]);;

(* HOL4 [simp] *)
let dec_clock_with_clock = prove
 (`!n (s:(C,FFI)clos_state) y.
     clos_state_clock_fupd (K y) (clos_dec_clock n s) = clos_state_clock_fupd (K y) s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [dec_clock_with_clock];;

let do_app_ffi_error_IMP = prove
 (`!op vs (s:(C,FFI)clos_state) f.
     clos_do_app op vs s = Rerr (Rabort (Rffi_error f)) ==> ?i. op = clos_FFI i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; injectivity "error_result";
              distinctness "error_result"; injectivity "abort"; distinctness "abort";
              distinctness "clos_op"; injectivity "clos_op"] THEN
  MESON_TAC[]);;

(* a local helper: do_app ignores the clock (it only copies it) *)
let CLOSPROPSAUX_do_app_clock = prove
 (CASE_TERM `!op vs (s:(C,FFI)clos_state) f.
     clos_do_app op vs (clos_state_clock_fupd f s) =
     map_result (\p. match p with (v,s1) -> (v,clos_state_clock_fupd f s1)) I
                (clos_do_app op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; clos_state_INFO.ri_accfupds] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[map_result_def; map_error_result_I; I_THM; pair_CASE;
              clos_state_INFO.ri_fupdcanon]);;

(* HOL4: do_app_add_to_clock *)
let clos_do_app_add_to_clock = prove
 (CASE_TERM `!op vs (s:(C,FFI)clos_state) extra.
     clos_do_app op vs (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     map_result (\p. match p with
                       (v,s1) -> (v,clos_state_clock_fupd (K (clos_state_clock s1 + extra)) s1))
                I (clos_do_app op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSPROPSAUX_do_app_clock] THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:clos_v list`; `s:(C,FFI)clos_state`]
                clos_do_app_const) THEN
  CASES_ON `clos_do_app op vs (s:(C,FFI)clos_state)` THEN
  REWRITE_TAC[map_result_def] THEN
  CASES_ON `a:clos_v#(C,FFI)clos_state` THEN
  REWRITE_TAC[pair_CASE; injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);;
let do_install_add_to_clock = prove
 (`!vs (s:(C,FFI)clos_state) e s' extra.
     clos_do_install vs s = (Rval e,s') ==>
     clos_do_install vs (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     (Rval e,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  TRY(ASM_ARITH_TAC) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

let do_install_type_error_add_to_clock = prove
 (`!vs (s:(C,FFI)clos_state) t extra.
     clos_do_install vs s = (Rerr (Rabort Rtype_error),t) ==>
     clos_do_install vs (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     (Rerr (Rabort Rtype_error),clos_state_clock_fupd (K (clos_state_clock t + extra)) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result";
              injectivity "error_result"; distinctness "error_result";
              injectivity "abort"; distinctness "abort"] THEN
  TRY(ASM_ARITH_TAC) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 [simp] *)
let do_install_not_Rraise = prove
 (`!vs (s:(C,FFI)clos_state) res t r.
     clos_do_install vs s = (res,t) ==> ~(res = Rerr (Rraise r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result";
              injectivity "error_result"; distinctness "error_result"]);;

(* HOL4 [simp] *)
let do_install_not_Rffi_error = prove
 (`!vs (s:(C,FFI)clos_state) res t f.
     clos_do_install vs s = (res,t) ==> ~(res = Rerr (Rabort (Rffi_error f)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result";
              injectivity "error_result"; distinctness "error_result";
              injectivity "abort"; distinctness "abort"]);;

let CLOSPROPSAUX_do_install_err_add = prove
 (`!vs (s:(C,FFI)clos_state) e t extra.
     clos_do_install vs s = (Rerr e,t) /\ ~(e = Rabort Rtimeout_error) ==>
     clos_do_install vs (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     (Rerr e,clos_state_clock_fupd (K (clos_state_clock t + extra)) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `e:(clos_v)error_result` THENL
   [FIRST_ASSUM(MP_TAC o SPEC `a:clos_v` o MATCH_MP do_install_not_Rraise) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP do_install_not_Rffi_error) THEN
  CASES_ON `a:abort` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "error_result"; injectivity "abort";
                              distinctness "abort"]) THEN
  ASM_MESON_TAC[do_install_type_error_add_to_clock]);;

(* local helpers for evaluate_add_to_clock: states with extra clock *)
let CLOSPROPSAUX_dec_clock_add = prove
 (`!k (s:(C,FFI)clos_state) extra.
     ~(clos_state_clock s < k) ==>
     clos_dec_clock k (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock k s) + extra))
       (clos_dec_clock k s)`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let CLOSPROPSAUX_dec_clock_add1 = prove
 (`!(s:(C,FFI)clos_state) extra.
     ~(clos_state_clock s = 0) ==>
     clos_dec_clock 1 (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock 1 s) + extra))
       (clos_dec_clock 1 s)`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let CLOSPROPSAUX_clock_add_refs = prove
 (`!(s:(C,FFI)clos_state) extra r.
     clos_state_refs_fupd (K r) (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     clos_state_clock_fupd (K (clos_state_clock (clos_state_refs_fupd (K r) s) + extra))
       (clos_state_refs_fupd (K r) s)`,
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_clock_add_0 = prove
 (`!(s:(C,FFI)clos_state) extra.
     clos_state_clock_fupd (K 0) (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     clos_state_clock_fupd (K 0) s`,
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_add_simps =
  [clos_state_INFO.ri_accfupds; K_THM;
   ARITH_RULE `!c k e. ~(c < k) ==> ~(c + e < k:num)`;
   ARITH_RULE `!c e. ~(c = 0) ==> ~(c + e = 0)`;
   CLOSPROPSAUX_dec_clock_add; CLOSPROPSAUX_dec_clock_add1; CLOSPROPSAUX_clock_add_0;
   CLOSPROPSAUX_clock_add_refs; clos_do_app_add_to_clock; map_result_def;
   map_error_result_I; I_THM];;

(* local tactics: split the evaluate equation among the assumptions (not  *)
(* the goal) and simplify the goal with the facts obtained                *)
let CLOSPROPSAUX_is_eval_eq tm =
  is_eq tm &&
  (let h = fst(strip_comb(lhs tm)) in
   is_const h && mem (fst(dest_const h)) ["clos_evaluate"; "evaluate_app"]);;

let CLOSPROPSAUX_SPLIT_ASM_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    if CLOSPROPSAUX_is_eval_eq (concl th) then
      CAKE_STRIP_ASSUME_TAC
        (REWRITE_RULE CLOSPROPSAUX_eval_case_eqs
          (BETA_RULE (REWRITE_RULE[LET_DEF; LET_END_DEF]
            (ONCE_REWRITE_RULE[clos_evaluate_def] th))))
    else NO_TAC) THEN
  RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN CLOSPROPSAUX_CLEAN_TAC;;

let CLOSPROPSAUX_case_defs =
  [pair_CASE; case_def "result"; case_def "list"; case_def "option"; case_def "app_kind";
   case_def "error_result"; case_def "clos_dest_thunk_ret"; case_def "thunk_mode";
   LET_DEF; LET_END_DEF];;

let CLOSPROPSAUX_ADD_TAC =
  REPEAT STRIP_TAC THEN
  CLOSPROPSAUX_SPLIT_ASM_TAC THEN CLOSPROPSAUX_RES_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC do_install_add_to_clock THEN IMP_RES_TAC CLOSPROPSAUX_do_install_err_add THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REPEAT(CHANGED_TAC(ASM_SIMP_TAC (CLOSPROPSAUX_add_simps @ CLOSPROPSAUX_case_defs)));;

let CLOSPROPSAUX_evaluate_add_to_clock = prove
 (`(!xs env (s:(C,FFI)clos_state) r s' extra.
      clos_evaluate (xs,env,s) = (r,s') /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
      clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
      (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s')) /\
   (!loc_opt v rest_args (s:(C,FFI)clos_state) r s' extra.
      evaluate_app loc_opt v rest_args s = (r,s') /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
      evaluate_app loc_opt v rest_args (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
      (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s'))`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN CLOSPROPSAUX_ADD_TAC);;

(* HOL4: evaluate_add_to_clock (HOL4 leaves extra free) *)
let clos_evaluate_add_to_clock = prove
 (`(!p es env (s:(C,FFI)clos_state) r s' extra.
      p = (es,env,s) /\ clos_evaluate (es,env,s) = (r,s') /\
      ~(r = Rerr (Rabort Rtimeout_error)) ==>
      clos_evaluate (es,env,clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
      (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s')) /\
   (!loc_opt v rest_args (s:(C,FFI)clos_state) r s' extra.
      evaluate_app loc_opt v rest_args s = (r,s') /\
      ~(r = Rerr (Rabort Rtimeout_error)) ==>
      evaluate_app loc_opt v rest_args
        (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
      (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s'))`,
  MESON_TAC[CLOSPROPSAUX_evaluate_add_to_clock]);;

(* HOL4: evaluate_add_clock *)
let clos_evaluate_add_clock = prove
 (`!es env (s:(C,FFI)clos_state) r s'.
     clos_evaluate (es,env,s) = (r,s') /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !extra.
       clos_evaluate (es,env,clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
       (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s')`,
  MESON_TAC[CLOSPROPSAUX_evaluate_add_to_clock]);;

(* HOL4: evaluate_add_clock_initial_state *)
let clos_evaluate_add_clock_initial_state = prove
 (`!es env (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k r s'.
     clos_evaluate (es,env,clos_initial_state ffi ma code co cc k) = (r,s') /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !extra.
       clos_evaluate (es,env,clos_initial_state ffi ma code co cc (k + extra)) =
       (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP clos_evaluate_add_clock) THEN
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_fupds; K_THM]);;

(* a local helper: call_FFI only extends the io_events *)
let CLOSPROPSAUX_call_FFI_io_events = prove
 (`!(st:(FFI)ffi_state) s conf bytes t' ws'.
     call_FFI st s conf bytes = FFI_return t' ws' ==>
     ffi_state_io_events st <<= ffi_state_io_events t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "ffi_result"] THENL
   [CASES_ON `ffi_state_oracle (st:(FFI)ffi_state) s (ffi_state_ffi_state st) conf bytes` THEN
    REWRITE_TAC[case_def "oracle_result"; distinctness "ffi_result"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "ffi_result"; injectivity "ffi_result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    REWRITE_TAC[ffi_state_INFO.ri_accfupds; K_THM; IS_PREFIX_APPEND] THEN MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[IS_PREFIX_REFL]]);;

(* HOL4 [local] *)
let clos_do_app_io_events_mono = prove
 (`!op vs (s:(C,FFI)clos_state) v s'.
     clos_do_app op vs s = Rval (v,s') ==>
     ffi_state_io_events (clos_state_ffi s) <<= ffi_state_io_events (clos_state_ffi s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[CLOSPROPSAUX_call_FFI_io_events]);;

(* a local helper: evaluate_io_events_mono in implication form *)
let CLOSPROPSAUX_io_events_mono = prove
 (`(!xs env (s:(C,FFI)clos_state) r s'.
      clos_evaluate (xs,env,s) = (r,s') ==>
      ffi_state_io_events (clos_state_ffi s) <<= ffi_state_io_events (clos_state_ffi s')) /\
   (!loc_opt v rest (s:(C,FFI)clos_state) r s'.
      evaluate_app loc_opt v rest s = (r,s') ==>
      ffi_state_io_events (clos_state_ffi s) <<= ffi_state_io_events (clos_state_ffi s'))`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN CLOSPROPSAUX_SPLIT_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  IMP_RES_TAC clos_do_app_io_events_mono THEN IMP_RES_TAC do_install_const THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL]);;

(* HOL4: evaluate_io_events_mono *)
let clos_evaluate_io_events_mono = prove
 (`(!p:clos_exp list # clos_v list # (C,FFI)clos_state.
      ffi_state_io_events (clos_state_ffi (SND (SND p))) <<=
      ffi_state_io_events (clos_state_ffi (SND (clos_evaluate p)))) /\
   (!loc_opt v rest (s:(C,FFI)clos_state).
      ffi_state_io_events (clos_state_ffi s) <<=
      ffi_state_io_events (clos_state_ffi (SND (evaluate_app loc_opt v rest s))))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[CLOSPROPSAUX_io_events_mono; PAIR]);;

(* HOL4: evaluate_io_events_mono_imp [local] *)
let clos_evaluate_io_events_mono_imp = prove
 (`!es env (s:(C,FFI)clos_state) r s'.
     clos_evaluate (es,env,s) = (r,s') ==>
     ffi_state_io_events (clos_state_ffi s) <<= ffi_state_io_events (clos_state_ffi s')`,
  REWRITE_TAC[CLOSPROPSAUX_io_events_mono]);;

(* HOL4: with_clock_ffi [local] *)
let clos_with_clock_ffi = prove
 (`!(s:(C,FFI)clos_state) k. clos_state_ffi (clos_state_clock_fupd (K k) s) = clos_state_ffi s`,
  REWRITE_TAC[clos_state_INFO.ri_accfupds]);;

(* local tactics for evaluate_add_to_clock_io_events_mono: strip a theorem *)
(* after renaming all its bound variables apart from the goal (HOL Light's  *)
(* CHOOSE fails when a bound name is free in the goal)                      *)
let CLOSPROPSAUX_FRESH_TAC (ttac:thm_tactic) th : tactic = fun (asl,w as g) ->
  let avoid0 = itlist (union o frees o concl o snd) asl
                 (union (frees w) (union (frees (concl th)) (freesl (hyp th)))) in
  let rec rn avoid tm =
    match tm with
      Comb(f,x) -> let f',avoid1 = rn avoid f in
                   let x',avoid2 = rn avoid1 x in mk_comb(f',x'),avoid2
    | Abs(v,b) -> let v' = variant avoid v in
                  let b' = vsubst [v',v] b in
                  let b'',avoid1 = rn (v'::avoid) b' in mk_abs(v',b''),avoid1
    | _ -> tm,avoid in
  let tm',_ = rn avoid0 (concl th) in
  ttac (EQ_MP (ALPHA (concl th) tm') th) g;;

(* split every evaluate equation of the assumptions that unfolds *)
let CLOSPROPSAUX_SPLIT_ASM1_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    if CLOSPROPSAUX_is_eval_eq (concl th) then
      let th1 = ONCE_REWRITE_RULE[clos_evaluate_def] th in
      if concl th1 = concl th then NO_TAC else
      CLOSPROPSAUX_FRESH_TAC STRIP_ASSUME_TAC
        (REWRITE_RULE CLOSPROPSAUX_eval_case_eqs
          (BETA_RULE (REWRITE_RULE[LET_DEF; LET_END_DEF] th1)))
    else NO_TAC) THEN
  RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN CLOSPROPSAUX_CLEAN_TAC;;
let CLOSPROPSAUX_SPLIT_ALL_TAC : tactic = REPEAT CLOSPROPSAUX_SPLIT_ASM1_TAC;;

(* equations with the same left side give an equation of their right sides *)
let CLOSPROPSAUX_MERGE_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun th -> let c = concl th in
                      is_eq c && not (is_var (lhs c)) && not (is_var (rhs c)))
                   (map snd asl) in
  let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in
  let merged = mapfilter (fun (a,b) ->
      if aconv (lhs(concl a)) (lhs(concl b)) && not (aconv (rhs(concl a)) (rhs(concl b)))
      then TRANS (SYM a) b else failwith "merge") (pairs eqs) in
  (MAP_EVERY ASSUME_TAC merged THEN CLOSPROPSAUX_CLEAN_TAC THEN CLOSPROPSAUX_CLEAN_TAC) g;;

let CLOSPROPSAUX_is_head_eq names tm =
  is_eq tm &&
  (let h = fst(strip_comb(lhs tm)) in
   is_const h && mem (fst(dest_const h)) names);;

let CLOSPROPSAUX_NORM_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let facts = filter (fun th -> CLOSSEMAUX_is_num_fact (concl th)) ths in
  let eqs = filter (fun th -> CLOSPROPSAUX_is_head_eq ["clos_do_app"] (concl th)) ths in
  RULE_ASSUM_TAC(fun th ->
    if CLOSSEMAUX_is_num_fact (concl th) then th
    else SIMP_RULE (facts @ filter (fun e -> not (concl e = concl th)) eqs @
                    CLOSPROPSAUX_add_simps @ CLOSPROPSAUX_case_defs) th) g;;

let CLOSPROPSAUX_SPEC_EXTRA_TAC (x:term) : tactic =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_forall c && type_of (fst(dest_forall c)) = `:num` &&
       is_eq (snd(dest_forall c))
    then SPEC x th else th);;

let CLOSPROPSAUX_IOADD_TAC =
  REPEAT STRIP_TAC THEN CLOSPROPSAUX_SPLIT_ALL_TAC THEN
  CLOSPROPSAUX_NORM_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC (CONJUNCT1 CLOSPROPSAUX_evaluate_add_to_clock) THEN
  IMP_RES_TAC (CONJUNCT2 CLOSPROPSAUX_evaluate_add_to_clock) THEN
  IMP_RES_TAC do_install_add_to_clock THEN IMP_RES_TAC CLOSPROPSAUX_do_install_err_add THEN
  CLOSPROPSAUX_CLEAN_TAC THEN CLOSPROPSAUX_SPEC_EXTRA_TAC `extra:num` THEN
  CLOSPROPSAUX_MERGE_TAC THEN CLOSPROPSAUX_NORM_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_MERGE_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC clos_do_app_io_events_mono THEN IMP_RES_TAC do_install_const THEN
  IMP_RES_TAC (CONJUNCT1 CLOSPROPSAUX_io_events_mono) THEN
  IMP_RES_TAC (CONJUNCT2 CLOSPROPSAUX_io_events_mono) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  TRY(REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
      ARITH_TAC);;

let CLOSPROPSAUX_add_to_clock_io_events_mono = prove
 (`(!xs env (s:(C,FFI)clos_state) extra r s' r2 s2.
      clos_evaluate (xs,env,s) = (r,s') /\
      clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock s + extra)) s) = (r2,s2)
      ==> ffi_state_io_events (clos_state_ffi s') <<= ffi_state_io_events (clos_state_ffi s2)) /\
   (!loc_opt v rest (s:(C,FFI)clos_state) extra r s' r2 s2.
      evaluate_app loc_opt v rest s = (r,s') /\
      evaluate_app loc_opt v rest (clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
      (r2,s2)
      ==> ffi_state_io_events (clos_state_ffi s') <<= ffi_state_io_events (clos_state_ffi s2))`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  CLOSPROPSAUX_IOADD_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL]);;

(* HOL4: evaluate_add_to_clock_io_events_mono (HOL4 leaves extra free) *)
let clos_evaluate_add_to_clock_io_events_mono = prove
 (`(!p es env (s:(C,FFI)clos_state) extra.
      p = (es,env,s) ==>
      ffi_state_io_events (clos_state_ffi (SND (clos_evaluate p))) <<=
      ffi_state_io_events (clos_state_ffi (SND (clos_evaluate
        (es,env,clos_state_clock_fupd (K (clos_state_clock s + extra)) s))))) /\
   (!l v r (s:(C,FFI)clos_state) extra.
      ffi_state_io_events (clos_state_ffi (SND (evaluate_app l v r s))) <<=
      ffi_state_io_events (clos_state_ffi (SND (evaluate_app l v r
        (clos_state_clock_fupd (K (clos_state_clock s + extra)) s)))))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(CONJUNCT1 CLOSPROPSAUX_add_to_clock_io_events_mono);
    MATCH_MP_TAC(CONJUNCT2 CLOSPROPSAUX_add_to_clock_io_events_mono)] THEN
  MESON_TAC[PAIR]);;

(* HOL4 [simp] *)
let do_app_never_timesout = prove
 (`!op args (s:(C,FFI)clos_state).
     ~(clos_do_app op args s = Rerr (Rabort Rtimeout_error))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; injectivity "error_result";
              distinctness "error_result"; injectivity "abort"; distinctness "abort"]);;
let _ = cake_add_simps [do_app_never_timesout];;

(* a local helper: do_install times out only with clock 0 *)
let CLOSPROPSAUX_do_install_timeout = prove
 (`!vs (s:(C,FFI)clos_state) s'.
     clos_do_install vs s = (Rerr (Rabort Rtimeout_error),s') ==> clos_state_clock s' = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result";
              injectivity "error_result"; distinctness "error_result";
              injectivity "abort"; distinctness "abort"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let CLOSPROPSAUX_timeout_clocks0 = prove
 (`(!xs env (s0:(C,FFI)clos_state) s.
      clos_evaluate (xs,env,s0) = (Rerr (Rabort Rtimeout_error),s) ==>
      clos_state_clock s = 0) /\
   (!locopt v env (s:(C,FFI)clos_state) s'.
      evaluate_app locopt v env s = (Rerr (Rabort Rtimeout_error),s') ==>
      clos_state_clock s' = 0)`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN CLOSPROPSAUX_SPLIT_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  CLOSPROPSAUX_CLEAN_TAC THEN
  IMP_RES_TAC CLOSPROPSAUX_do_install_timeout THEN
  RULE_ASSUM_TAC(REWRITE_RULE[do_app_never_timesout]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: evaluate_timeout_clocks0 *)
let evaluate_timeout_clocks0 = prove
 (`(!(v:clos_exp list # clos_v list # (C,FFI)clos_state) (s:(C,FFI)clos_state).
      clos_evaluate v = (Rerr (Rabort Rtimeout_error),s) ==> clos_state_clock s = 0) /\
   (!locopt v env (s:(C,FFI)clos_state) s'.
      evaluate_app locopt v env s = (Rerr (Rabort Rtimeout_error),s') ==>
      clos_state_clock s' = 0)`,
  REWRITE_TAC[FORALL_PAIR_THM; CLOSPROPSAUX_timeout_clocks0]);;

(* HOL4: exp_size_MEM (exp3_size is list_size clos_exp_size and exp1_size *)
(* is list_size (pair_size (\x. x) clos_exp_size) here)                    *)
let clos_exp_size_MEM = prove
 (`(!e elist. MEM e elist ==> clos_exp_size e < list_size clos_exp_size elist) /\
   (!x e ealist. MEM (x,e) ealist ==>
                 clos_exp_size e < list_size (pair_size (\x. x) clos_exp_size) ealist)`,
  CONJ_TAC THENL [MESON_TAC[MEM_LIST_SIZE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC exp1_size_lemma THEN
  EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[]);;

(* HOL4 [simp] *)
let evaluate_eq_nil = prove
 (`!es env (s0:(C,FFI)clos_state) s.
     clos_evaluate (es,env,s0) = (Rval [],s) <=> s0 = s /\ es = []`,
  REPEAT GEN_TAC THEN CASES_ON `es:clos_exp list` THEN
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ; injectivity "result"; distinctness "list"] THEN
  DISCH_THEN(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; NOT_SUC]);;
let _ = cake_add_simps [evaluate_eq_nil];;

(* HOL4: op_gbag (finding the SetGlobal operations) *)
let clos_op_gbag_def = sem1aux_def
  `(clos_op_gbag (GlobOp (SetGlobal n)) = BAG_INSERT n EMPTY_BAG) /\
   (clos_op_gbag (_:clos_op) = (EMPTY_BAG:num->num))`;;

(* HOL4 [simp]; exp2_size is pair_size (\x. x) clos_exp_size here *)
let exp2_size_rw = prove
 (`!h. pair_size (\x. x) clos_exp_size h = 1 + FST h + clos_exp_size (SND h)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_size_THM; FST; SND]);;
let _ = cake_add_simps [exp2_size_rw];;

(* HOL4: set_globals_def [simp] *)
let clos_set_globals_def = sem1aux_def_wf
  `measure (\x:clos_exp + clos_exp list.
              sum_CASE x (\e. clos_exp_size e) (\es. list_size clos_exp_size es))`
  CLOSPROPSAUX_TC_TAC
  `(clos_set_globals (clos_Var _ _) = EMPTY_BAG) /\
   (clos_set_globals (clos_If _ e1 e2 e3) =
      BAG_UNION (BAG_UNION (clos_set_globals e1) (clos_set_globals e2))
                (clos_set_globals e3)) /\
   (clos_set_globals (clos_Let _ binds e) =
      BAG_UNION (clos_set_globals e) (clos_elist_globals binds)) /\
   (clos_set_globals (clos_Raise _ e) = clos_set_globals e) /\
   (clos_set_globals (clos_Handle _ e1 e2) =
      BAG_UNION (clos_set_globals e1) (clos_set_globals e2)) /\
   (clos_set_globals (clos_Tick _ e) = clos_set_globals e) /\
   (clos_set_globals (clos_Call _ _ _ args) = clos_elist_globals args) /\
   (clos_set_globals (clos_App _ _ f args) =
      BAG_UNION (clos_set_globals f) (clos_elist_globals args)) /\
   (clos_set_globals (Fn _ _ _ _ bod) = clos_set_globals bod) /\
   (clos_set_globals (clos_Letrec _ _ _ fbinds bod) =
      BAG_UNION (clos_set_globals bod) (clos_elist_globals (MAP SND fbinds))) /\
   (clos_set_globals (clos_Op _ opn args) =
      BAG_UNION (clos_op_gbag opn) (clos_elist_globals args)) /\
   (clos_elist_globals [] = EMPTY_BAG) /\
   (clos_elist_globals (CONS e es) =
      BAG_UNION (clos_set_globals e) (clos_elist_globals es))`;;
let _ = cake_add_simps [clos_set_globals_def];;

let clos_set_globals_ind = cake_ind "clos_set_globals";;

(* HOL4: v_size_lemma; v1_size is list_size clos_v_size here *)
let clos_v_size_lemma = prove
 (`!v vl. MEM (v:clos_v) vl ==> clos_v_size v < list_size clos_v_size vl`,
  MESON_TAC[MEM_LIST_SIZE]);;

(* value is setglobal-closure free; HOL4 rebinds vsgc_free_def to its eta- *)
(* reduced form, which is the form stored here                             *)
let vsgc_free_def = sem1aux_def_wf
  `measure clos_v_size`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP clos_v_size_lemma)) THEN
    REWRITE_TAC(WF_REL_THMS @ [type_size_def "clos_v"] @ size_aux_eqs "clos_v") THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC))
  `(vsgc_free (clos_Closure _ VL1 VL2 _ body) <=>
      clos_set_globals body = EMPTY_BAG /\
      ALL vsgc_free VL1 /\ ALL vsgc_free VL2) /\
   (vsgc_free (clos_Recclosure _ VL1 VL2 bods _) <=>
      clos_elist_globals (MAP SND bods) = EMPTY_BAG /\
      ALL vsgc_free VL1 /\ ALL vsgc_free VL2) /\
   (vsgc_free (clos_Block _ VL1) <=> ALL vsgc_free VL1) /\
   (vsgc_free _ <=> T)`;;
let _ = cake_add_simps [vsgc_free_def];;

let vsgc_free_ind = cake_ind "vsgc_free";;

(* HOL4 [simp] *)
let vsgc_free_Unit = prove
 (`vsgc_free clos_Unit`,
  REWRITE_TAC[clos_Unit_def; vsgc_free_def; ALL]);;
let _ = cake_add_simps [vsgc_free_Unit];;

(* HOL4 [simp] *)
let vsgc_free_Boolv = prove
 (`!b. vsgc_free (clos_Boolv b)`,
  REWRITE_TAC[clos_Boolv_def; vsgc_free_def; ALL]);;
let _ = cake_add_simps [vsgc_free_Boolv];;

(* result is setglobal-closure free; HOL4 [simp] *)
let rsgc_free_def = sem1aux_def
  `(rsgc_free (Rval vs) <=> ALL vsgc_free vs) /\
   (rsgc_free (Rerr (Rabort _)) <=> T) /\
   (rsgc_free (Rerr (Rraise v)) <=> vsgc_free v)`;;
let _ = cake_add_simps [rsgc_free_def];;

(* HOL4: esgc_free_def; HOL4 rebinds it to its eta-reduced form, which is  *)
(* the form stored here                                                     *)
let clos_esgc_free_def = sem1aux_def_wf
  `measure clos_exp_size`
  CLOSPROPSAUX_TC2_TAC
  `(clos_esgc_free (clos_Var _ _) <=> T) /\
   (clos_esgc_free (clos_If _ e1 e2 e3) <=>
      clos_esgc_free e1 /\ clos_esgc_free e2 /\ clos_esgc_free e3) /\
   (clos_esgc_free (clos_Let _ binds e) <=>
      ALL clos_esgc_free binds /\ clos_esgc_free e) /\
   (clos_esgc_free (clos_Raise _ e) <=> clos_esgc_free e) /\
   (clos_esgc_free (clos_Handle _ e1 e2) <=> clos_esgc_free e1 /\ clos_esgc_free e2) /\
   (clos_esgc_free (clos_Tick _ e) <=> clos_esgc_free e) /\
   (clos_esgc_free (clos_Call _ _ _ args) <=> ALL clos_esgc_free args) /\
   (clos_esgc_free (clos_App _ _ e args) <=>
      clos_esgc_free e /\ ALL clos_esgc_free args) /\
   (clos_esgc_free (Fn _ _ _ _ b) <=> clos_set_globals b = EMPTY_BAG) /\
   (clos_esgc_free (clos_Letrec _ _ _ fbinds bod) <=>
      clos_elist_globals (MAP SND fbinds) = EMPTY_BAG /\ clos_esgc_free bod) /\
   (clos_esgc_free (clos_Op _ _ args) <=> ALL clos_esgc_free args)`;;
let _ = cake_add_simps [clos_esgc_free_def];;

let clos_esgc_free_ind = cake_ind "clos_esgc_free";;

(* state is setglobal-closure free *)
let ssgc_free_def = cake_def
  `ssgc_free (s:(C,FFI)clos_state) <=>
     (!n m e. FLOOKUP (clos_state_code s) n = SOME (m,e) ==>
              clos_set_globals e = EMPTY_BAG) /\
     (!n vl. FLOOKUP (clos_state_refs s) n = SOME (clos_ValueArray vl) ==>
             ALL vsgc_free vl) /\
     (!n m v. FLOOKUP (clos_state_refs s) n = SOME (clos_Thunk m v) ==> vsgc_free v) /\
     (!v. MEM (SOME v) (clos_state_globals s) ==> vsgc_free v) /\
     (!n exp aux. SND (clos_state_compile_oracle s n) = (exp,aux) ==>
                  ALL clos_esgc_free exp /\
                  clos_elist_globals (MAP (SND o SND) aux) = EMPTY_BAG)`;;

(* HOL4 [simp] *)
let ssgc_free_clockupd = prove
 (`!f (s:(C,FFI)clos_state). ssgc_free (clos_state_clock_fupd f s) <=> ssgc_free s`,
  REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [ssgc_free_clockupd];;

(* HOL4 [simp] *)
let ssgc_free_dec_clock = prove
 (`!n (s:(C,FFI)clos_state). ssgc_free (clos_dec_clock n s) <=> ssgc_free s`,
  REWRITE_TAC[clos_dec_clock_def; ssgc_free_clockupd]);;
let _ = cake_add_simps [ssgc_free_dec_clock];;

let elglobals_EQ_EMPTY = prove
 (`!l. clos_elist_globals l = EMPTY_BAG <=> !e. MEM e l ==> clos_set_globals e = EMPTY_BAG`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_set_globals_def; MEM; BAG_UNION_EMPTY] THEN
  MESON_TAC[]);;

let set_globals_empty_esgc_free = prove
 (`!e. clos_set_globals e = EMPTY_BAG ==> clos_esgc_free e`,
  MATCH_MP_TAC clos_esgc_free_ind THEN
  REWRITE_TAC[clos_set_globals_def; clos_esgc_free_def; BAG_UNION_EMPTY;
              elglobals_EQ_EMPTY; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4: elist_globals_append *)
let clos_elist_globals_append = prove
 (`!a b. clos_elist_globals (APPEND a b) =
         BAG_UNION (clos_elist_globals a) (clos_elist_globals b)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; clos_set_globals_def; BAG_UNION_EMPTY;
                                       ASSOC_BAG_UNION]);;

(* HOL4: elist_globals_FOLDR (FOLDR f e l is ITLIST f l e) *)
let clos_elist_globals_FOLDR = prove
 (`!es. clos_elist_globals es = ITLIST BAG_UNION (MAP clos_set_globals es) EMPTY_BAG`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_set_globals_def; MAP; ITLIST]);;

let elist_globals_reverse = prove
 (`!ls. clos_elist_globals (REVERSE ls) = clos_elist_globals ls`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; clos_elist_globals_append; clos_set_globals_def;
                  BAG_UNION_EMPTY] THEN
  MATCH_ACCEPT_TAC COMM_BAG_UNION);;

(* generic do_app compile proof *)

(* HOL4: isClos_def [simp] *)
let clos_isClos_def = sem1aux_def
  `(clos_isClos (clos_Closure x1 x2 x3 x4 x5) <=> T) /\
   (clos_isClos (clos_Recclosure y1 y2 y3 y4 y5) <=> T) /\
   (clos_isClos _ <=> F)`;;
let _ = cake_add_simps [clos_isClos_def];;

let isClos_cases = prove
 (`!x. clos_isClos x <=>
       (?x1 x2 x3 x4 x5. x = clos_Closure x1 x2 x3 x4 x5) \/
       (?y1 y2 y3 y4 y5. x = clos_Recclosure y1 y2 y3 y4 y5)`,
  GEN_TAC THEN CASES_ON `x:clos_v` THEN
  REWRITE_TAC[clos_isClos_def; distinctness "clos_v"; injectivity "clos_v"] THEN
  MESON_TAC[]);;

(* HOL4: simple_val_rel_def *)
let clos_simple_val_rel_def = cake_def
  `clos_simple_val_rel (vr:clos_v->clos_v->bool) <=>
     (!x n. vr x (clos_Number n) <=> x = clos_Number n) /\
     (!x p n.
        vr x (clos_Block n p) <=>
        ?xs. x = clos_Block n xs /\ ALL2 vr xs p) /\
     (!x p. vr x (clos_Word64 p) <=> x = clos_Word64 p) /\
     (!x p. vr x (ByteVector p) <=> x = ByteVector p) /\
     (!x p b. vr x (clos_RefPtr b p) <=> x = clos_RefPtr b p) /\
     (!x5 x4 x3 x2 x1 x.
        vr x (clos_Closure x1 x2 x3 x4 x5) ==> clos_isClos x) /\
     (!y5 y4 y3 y2 y1 x.
        vr x (clos_Recclosure y1 y2 y3 y4 y5) ==> clos_isClos x)`;;

(* HOL4 [local] *)
let simple_val_rel_alt = prove
 (`!vr. clos_simple_val_rel vr <=>
     (!x n. vr x (clos_Number n) <=> x = clos_Number n) /\
     (!x p n.
        vr x (clos_Block n p) <=>
        ?xs. x = clos_Block n xs /\ ALL2 vr xs p) /\
     (!x p. vr x (clos_Word64 p) <=> x = clos_Word64 p) /\
     (!x p. vr x (ByteVector p) <=> x = ByteVector p) /\
     (!x p b. vr x (clos_RefPtr b p) <=> x = clos_RefPtr b p) /\
     (!x5 x4 x3 x2 x1 x.
        vr x (clos_Closure x1 x2 x3 x4 x5) ==> clos_isClos x) /\
     (!y5 y4 y3 y2 y1 x.
        vr x (clos_Recclosure y1 y2 y3 y4 y5) ==> clos_isClos x) /\
     (!b1 b2. vr (clos_Boolv b1) (clos_Boolv b2) <=> b1 = b2) /\
     (vr clos_Unit clos_Unit <=> T)`,
  GEN_TAC THEN REWRITE_TAC[clos_simple_val_rel_def] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_Boolv_def; clos_Unit_def] THEN
  ASM_REWRITE_TAC[injectivity "clos_v"; LIST_REL_NIL] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN
  REWRITE_TAC[true_tag_def; false_tag_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[]);;

(* HOL4: simple_state_rel_def *)
let clos_simple_state_rel_def = cake_def
  `clos_simple_state_rel (vr:clos_v->clos_v->bool)
      (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) <=>
     (!s t ptr. FLOOKUP (clos_state_refs t) ptr = NONE /\ sr s t ==>
                FLOOKUP (clos_state_refs s) ptr = NONE) /\
     (!w t s ptr.
        FLOOKUP (clos_state_refs t) ptr = SOME (clos_ByteArray w) /\ sr s t ==>
        FLOOKUP (clos_state_refs s) ptr = SOME (clos_ByteArray w)) /\
     (!w t s ptr.
        FLOOKUP (clos_state_refs t) ptr = SOME (clos_ValueArray w) /\ sr s t ==>
        ?w1. FLOOKUP (clos_state_refs s) ptr = SOME (clos_ValueArray w1) /\
             ALL2 vr w1 w) /\
     (!m v t s ptr.
        FLOOKUP (clos_state_refs t) ptr = SOME (clos_Thunk m v) /\ sr s t ==>
        ?w. FLOOKUP (clos_state_refs s) ptr = SOME (clos_Thunk m w) /\ vr w v) /\
     (!s t. sr s t ==> clos_state_ffi s = clos_state_ffi t /\
                       FDOM (clos_state_refs s) = FDOM (clos_state_refs t) /\
                       ALL2 (OPTREL vr) (clos_state_globals s) (clos_state_globals t)) /\
     (!f s t.
        sr s t ==> sr (clos_state_ffi_fupd (K f) s) (clos_state_ffi_fupd (K f) t)) /\
     (!bs s t p.
        sr s t ==>
        sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_ByteArray bs))) s)
           (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_ByteArray bs))) t)) /\
     (!s t p xs ys.
        sr s t /\ ALL2 vr xs ys ==>
        sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_ValueArray xs))) s)
           (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_ValueArray ys))) t)) /\
     (!s t p m v w.
        sr s t /\ vr v w ==>
        sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_Thunk m v))) s)
           (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_Thunk m w))) t)) /\
     (!s t xs ys.
        sr s t /\ ALL2 (OPTREL vr) xs ys ==>
        sr (clos_state_globals_fupd (K xs) s) (clos_state_globals_fupd (K ys) t))`;;

let simple_state_rel_ffi = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t.
     clos_simple_state_rel vr sr /\ sr s t ==> clos_state_ffi s = clos_state_ffi t`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

let simple_state_rel_fdom = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t.
     clos_simple_state_rel vr sr /\ sr s t ==>
     FDOM (clos_state_refs s) = FDOM (clos_state_refs t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let simple_state_rel_update_ffi = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t f.
     clos_simple_state_rel vr sr /\ sr s t ==>
     sr (clos_state_ffi_fupd (K f) s) (clos_state_ffi_fupd (K f) t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let simple_state_rel_update_bytes = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t p bs.
     clos_simple_state_rel vr sr /\ sr s t ==>
     sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_ByteArray bs))) s)
        (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_ByteArray bs))) t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let simple_state_rel_update_values = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys p.
     clos_simple_state_rel vr sr /\ sr s t /\ ALL2 vr xs ys ==>
     sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_ValueArray xs))) s)
        (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_ValueArray ys))) t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let simple_state_rel_update_thunks = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t v w p m.
     clos_simple_state_rel vr sr /\ sr s t /\ vr v w ==>
     sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_Thunk m v))) s)
        (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_Thunk m w))) t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let simple_state_rel_update_globals = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys.
     clos_simple_state_rel vr sr /\ sr s t /\ ALL2 (OPTREL vr) xs ys ==>
     sr (clos_state_globals_fupd (K xs) s) (clos_state_globals_fupd (K ys) t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let simple_state_rel_get_global = prove
 (CASE_TERM `!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t n x.
     clos_simple_state_rel vr sr /\ sr s t /\
     get_global n (clos_state_globals t) = x ==>
     match x with
       NONE -> get_global n (clos_state_globals s) = NONE
     | SOME NONE -> get_global n (clos_state_globals s) = SOME NONE
     | SOME (SOME y) -> ?x. get_global n (clos_state_globals s) = SOME (SOME x) /\ vr x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_simple_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `ALL2 (OPTREL vr) (clos_state_globals (s:(D,FFI)clos_state))
                                 (clos_state_globals (t:(C,FFI)clos_state))` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`clos_state_globals (s:(D,FFI)clos_state)`,`l1:(clos_v option)list`) THEN
  SPEC_TAC(`clos_state_globals (t:(C,FFI)clos_state)`,`l2:(clos_v option)list`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  REWRITE_TAC[get_global_def] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "option"] THEN
  SUBGOAL_THEN `OPTREL (vr:clos_v->clos_v->bool) (EL n (l1:(clos_v option)list))
                       (EL n (l2:(clos_v option)list))` MP_TAC THENL
   [ASM_MESON_TAC[LIST_REL_EL_EQN]; ALL_TAC] THEN
  CASES_ON `EL n (l2:(clos_v option)list)` THEN
  CASES_ON `EL n (l1:(clos_v option)list)` THEN
  REWRITE_TAC[OPTREL_def; case_def "option"; injectivity "option"; distinctness "option"] THEN
  MESON_TAC[]);;

(* HOL4 [simp] *)
let list_to_v_INJ = prove
 (`!xs ys. clos_list_to_v xs = clos_list_to_v ys <=> xs = ys`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `ys:clos_v list` THEN
  ASM_REWRITE_TAC[clos_list_to_v_def; injectivity "clos_v"; injectivity "list";
                  distinctness "list"; nil_tag_def; cons_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let _ = cake_add_simps [list_to_v_INJ];;

(* HOL4 [local] *)
let isClos_IMP_v_to_list_NONE = prove
 (`!x. clos_isClos x ==> clos_v_to_list x = NONE`,
  GEN_TAC THEN CASES_ON `x:clos_v` THEN REWRITE_TAC[clos_isClos_def; clos_v_to_list_def]);;

(* a local helper: the values that simple_val_rel relates to a basic value *)
let CLOSPROPSAUX_vr_left = prove
 (`!vr. clos_simple_val_rel vr ==>
     (!y n. vr (clos_Number n) y <=> y = clos_Number n) /\
     (!y w. vr (clos_Word64 w) y <=> y = clos_Word64 w) /\
     (!y p. vr (ByteVector p) y <=> y = ByteVector p) /\
     (!y b p. vr (clos_RefPtr b p) y <=> y = clos_RefPtr b p)`,
  GEN_TAC THEN REWRITE_TAC[clos_simple_val_rel_def] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `y:clos_v` THEN
  ASM_REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN
  TRY(EQ_TAC THEN SIMP_TAC[] THEN NO_TAC) THEN
  TRY(MESON_TAC[]) THEN
  ASM_MESON_TAC[clos_isClos_def]);;
(* local helpers (HOL4 v_to_list_SOME and v_to_list_NONE, proved here *)
(* because the lemmas before them in HOL4 use them)                   *)
let CLOSPROPSAUX_v_to_list_SOME = prove
 (`!vr. clos_simple_val_rel vr ==>
     !y ys x. vr x y /\ clos_v_to_list y = SOME ys ==>
              ?xs. ALL2 vr xs ys /\ clos_v_to_list x = SOME xs`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def]) THEN
  MATCH_MP_TAC clos_v_to_list_ind THEN
  REWRITE_TAC[clos_v_to_list_def; distinctness "option"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    STRIP_TAC THEN RVEQ_TAC THEN FS[LIST_REL_NIL] THEN
    ASM_REWRITE_TAC[clos_v_to_list_def; ALL2];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    CASES_ON `clos_v_to_list bt` THEN
    REWRITE_TAC[case_def "option"; distinctness "option"; injectivity "option"] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:clos_v list`; `h'':clos_v`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `CONS (h':clos_v) xs` THEN
    ASM_REWRITE_TAC[clos_v_to_list_def; case_def "option"; ALL2]]);;

let CLOSPROPSAUX_v_to_list_NONE = prove
 (`!vr. clos_simple_val_rel vr ==>
     !y x. vr x y /\ clos_v_to_list y = NONE ==> clos_v_to_list x = NONE`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def]) THEN
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN FS[clos_v_to_list_def; LIST_REL_CONS2; LIST_REL_NIL] THEN
  RVEQ_TAC THEN REWRITE_TAC[clos_v_to_list_def] THEN
  TRY(MATCH_MP_TAC isClos_IMP_v_to_list_NONE THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  FS[COND_CASE_EQ; option_case_eq] THEN RVEQ_TAC THEN ASM_REWRITE_TAC[case_def "option"]);;

(* local helpers: lists of related values *)
let CLOSPROPSAUX_ALL2_MAP_right = prove
 (`!(vr:A->A->bool) (f:C->A).
     (!x y. vr x (f y) <=> x = f y) ==> !ys xs. ALL2 vr xs (MAP f ys) <=> xs = MAP f ys`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; LIST_REL_NIL; LIST_REL_CONS2] THEN
  GEN_TAC THEN MESON_TAC[]);;

let CLOSPROPSAUX_ALL2_MAP_left = prove
 (`!(vr:A->A->bool) (f:C->A).
     (!x y. vr (f x) y <=> y = f x) ==> !xs ys. ALL2 vr (MAP f xs) ys <=> ys = MAP f xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; LIST_REL_NIL; LIST_REL_CONS1] THEN
  GEN_TAC THEN MESON_TAC[]);;

(* HOL4 [local] *)
let v_rel_to_list_ByteVector = prove
 (`!vr. clos_simple_val_rel vr ==>
     !lv x. vr x lv ==>
       !wss. (clos_v_to_list x = SOME (MAP ByteVector wss) <=>
              clos_v_to_list lv = SOME (MAP ByteVector wss))`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[clos_simple_val_rel_def] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP CLOSPROPSAUX_vr_left th)) THEN
  SUBGOAL_THEN `(!ys xs. ALL2 (vr:clos_v->clos_v->bool) xs (MAP ByteVector ys) <=>
                         xs = MAP ByteVector ys) /\
                (!xs ys. ALL2 (vr:clos_v->clos_v->bool) (MAP ByteVector xs) ys <=>
                         ys = MAP ByteVector xs)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSPROPSAUX_ALL2_MAP_right; MATCH_MP_TAC CLOSPROPSAUX_ALL2_MAP_left] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPEC `clos_v_to_list lv` (cases "option")) THEN STRIP_TAC THENL
     [ASM_MESON_TAC[CLOSPROPSAUX_v_to_list_NONE; distinctness "option"]; ALL_TAC] THEN
    MP_TAC(SPECL [`vr:clos_v->clos_v->bool`] CLOSPROPSAUX_v_to_list_SOME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`lv:clos_v`; `a:clos_v list`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`vr:clos_v->clos_v->bool`] CLOSPROPSAUX_v_to_list_SOME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`lv:clos_v`; `MAP ByteVector wss`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
(* HOL4 [local]; HOL4 Number o $& is clos_Number o int_of_num *)
let v_rel_to_list_byte1 = prove
 (`!vr. clos_simple_val_rel vr ==>
     !y x. vr x y ==>
       !ns. (clos_v_to_list x = SOME (MAP (clos_Number o int_of_num) ns) <=>
             clos_v_to_list y = SOME (MAP (clos_Number o int_of_num) ns))`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[clos_simple_val_rel_def] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP CLOSPROPSAUX_vr_left th)) THEN
  SUBGOAL_THEN
   `(!ys xs. ALL2 (vr:clos_v->clos_v->bool) xs (MAP (clos_Number o int_of_num) ys) <=>
             xs = MAP (clos_Number o int_of_num) ys) /\
    (!xs ys. ALL2 (vr:clos_v->clos_v->bool) (MAP (clos_Number o int_of_num) xs) ys <=>
             ys = MAP (clos_Number o int_of_num) xs)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSPROPSAUX_ALL2_MAP_right; MATCH_MP_TAC CLOSPROPSAUX_ALL2_MAP_left] THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPEC `clos_v_to_list y` (cases "option")) THEN STRIP_TAC THENL
     [ASM_MESON_TAC[CLOSPROPSAUX_v_to_list_NONE; distinctness "option"]; ALL_TAC] THEN
    MP_TAC(SPECL [`vr:clos_v->clos_v->bool`] CLOSPROPSAUX_v_to_list_SOME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `a:clos_v list`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`vr:clos_v->clos_v->bool`] CLOSPROPSAUX_v_to_list_SOME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `MAP (clos_Number o int_of_num) ns`;
                               `x:clos_v`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 [local] *)
let v_rel_to_list_byte2 = prove
 (`!vr. clos_simple_val_rel vr ==>
     !y x. vr x y ==>
       !ns. (clos_v_to_list x = SOME (MAP (clos_Number o int_of_num) ns) /\
             ALL (\n. n < 256) ns) <=>
            (clos_v_to_list y = SOME (MAP (clos_Number o int_of_num) ns) /\
             ALL (\n. n < 256) ns)`,
  MESON_TAC[v_rel_to_list_byte1]);;

(* HOL4 [local] *)
let v_to_list_SOME = CLOSPROPSAUX_v_to_list_SOME;;

(* HOL4 [local] *)
let v_to_list_NONE = CLOSPROPSAUX_v_to_list_NONE;;

let CLOSPROPSAUX_is_app name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let CLOSPROPSAUX_ALL2_LENGTH_TAC : tactic =
  ASSUM_LIST(fun thl ->
    MAP_EVERY (ASSUME_TAC o MATCH_MP LIST_REL_LENGTH)
      (filter (CLOSPROPSAUX_is_app "ALL2" o concl) thl));;

let v_rel_do_eq = prove
 (`!vr. clos_simple_val_rel vr ==>
     (!y1 y2 x1 x2. vr x1 y1 /\ vr x2 y2 ==> clos_do_eq x1 x2 = clos_do_eq y1 y2) /\
     (!y1 y2 x1 x2. ALL2 vr x1 y1 /\ ALL2 vr x2 y2 ==>
                    clos_do_eq_list x1 x2 = clos_do_eq_list y1 y2)`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(REWRITE_RULE[clos_simple_val_rel_def] th)) THEN
  MATCH_MP_TAC clos_do_eq_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    CASES_ON `x:clos_v` THEN CASES_ON `y:clos_v` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSPROPSAUX_RES_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[isClos_cases] o
                         check (CLOSPROPSAUX_is_app "clos_isClos" o concl))) THEN
    RVEQ_TAC THEN ONCE_REWRITE_TAC[clos_do_eq_def] THEN
    REWRITE_TAC[case_def "clos_v"] THEN CLOSPROPSAUX_ALL2_LENGTH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a1:clos_v list`; `a1':clos_v list`]) THEN
        ASM_REWRITE_TAC[injectivity "clos_v"] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]);
    REWRITE_TAC[LIST_REL_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LIST_REL_CONS2] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ONCE_REWRITE_TAC[clos_do_eq_def] THEN
    SUBGOAL_THEN `clos_do_eq h' h'' = clos_do_eq x y` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CASES_ON `clos_do_eq x y` THEN REWRITE_TAC[case_def "eq_result"] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS2] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_do_eq_def];
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS2] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_do_eq_def]]);;

let simple_state_rel_FLOOKUP_refs_IMP = prove
 (CASE_TERM `!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t p x.
     clos_simple_state_rel vr sr /\ sr s t /\ FLOOKUP (clos_state_refs t) p = x ==>
     match x with
       NONE -> FLOOKUP (clos_state_refs s) p = NONE
     | SOME (clos_ByteArray bs) -> FLOOKUP (clos_state_refs s) p = SOME (clos_ByteArray bs)
     | SOME (clos_ValueArray vs) ->
         ?xs. FLOOKUP (clos_state_refs s) p = SOME (clos_ValueArray xs) /\ ALL2 vr xs vs
     | SOME (clos_Thunk m w) ->
         ?v. FLOOKUP (clos_state_refs s) p = SOME (clos_Thunk m v) /\ vr v w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_simple_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  CASES_ON `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) p` THEN
  REWRITE_TAC[case_def "option"] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN REWRITE_TAC[case_def "clos_ref"] THEN
  ASM_MESON_TAC[]);;

(* HOL4 [local]: s with <| refs := r; ffi := f |> *)
let refs_ffi_lemma = prove
 (`!(s:(C,FFI)clos_state) refs' ffi'.
     clos_state_refs_fupd (K refs') (clos_state_ffi_fupd (K ffi') s) =
     clos_state_ffi_fupd (K ffi') (clos_state_refs_fupd (K refs') s)`,
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]);;

(* a local helper: related lists give related list values *)
let CLOSPROPSAUX_vr_list_to_v = prove
 (`!vr. clos_simple_val_rel vr ==>
     !xs ys. vr ys (clos_list_to_v xs) <=>
             ?zs. ys = clos_list_to_v zs /\ ALL2 vr zs xs`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_list_to_v_def; LIST_REL_NIL; LIST_REL_CONS2] THEN
  GEN_TAC THEN MESON_TAC[clos_list_to_v_def; injectivity "clos_v"; injectivity "list"]);;

let simple_val_rel_list = prove
 (`!x x1 xs vr.
     clos_simple_val_rel vr /\ vr x x1 /\ clos_v_to_list x1 = SOME xs ==>
     ?xs1. vr (clos_list_to_v xs1) (clos_list_to_v xs) /\ clos_v_to_list x = SOME xs1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `vr:clos_v->clos_v->bool` CLOSPROPSAUX_v_to_list_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x1:clos_v`; `xs:clos_v list`; `x:clos_v`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `xs':clos_v list` THEN
  ASM_SIMP_TAC[CLOSPROPSAUX_vr_list_to_v] THEN ASM_MESON_TAC[]);;

let simple_val_rel_APPEND = prove
 (`!xs1 ys1 xs2 ys2 vr.
     clos_simple_val_rel vr /\
     vr (clos_list_to_v xs1) (clos_list_to_v xs2) /\
     vr (clos_list_to_v ys1) (clos_list_to_v ys2) ==>
     vr (clos_list_to_v (APPEND xs1 ys1)) (clos_list_to_v (APPEND xs2 ys2))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSPROPSAUX_vr_list_to_v th]) THEN
  REWRITE_TAC[list_to_v_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `APPEND (zs:clos_v list) zs'` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[]);;

let vr_list_NONE = prove
 (`!x x1 vr.
     clos_simple_val_rel vr /\ vr x x1 /\ clos_v_to_list x1 = NONE ==>
     clos_v_to_list x = NONE`,
  MESON_TAC[CLOSPROPSAUX_v_to_list_NONE]);;

(* HOL4 leaves vr free *)
let vr_list_to_v = prove
 (`!xs vys vr.
     clos_simple_val_rel vr ==>
     (vr vys (clos_list_to_v xs) <=> ?ys. vys = clos_list_to_v ys /\ ALL2 vr ys xs)`,
  MESON_TAC[CLOSPROPSAUX_vr_list_to_v]);;

(* HOL4: result_rel_Rval2 [local,simp] *)
let clos_result_rel_Rval2 = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) r v.
     result_rel R1 R2 r (Rval v) <=> ?v'. r = Rval v' /\ R1 v' v`,
  REPEAT GEN_TAC THEN CASES_ON `r:(A,C)result` THEN
  REWRITE_TAC[result_rel_def; injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;

(* HOL4 [local,simp] *)
let PAIR_REL_SIMP = prove
 (`(!(R1:A->B->bool) (R2:C->D->bool) n c d.
      (R1 ### R2) n (c,d) <=> ?x y. n = (x,y) /\ R1 x c /\ R2 y d) /\
   (!(R1:A->B->bool) (R2:C->D->bool) a b m.
      (R1 ### R2) (a,b) m <=> ?x y. m = (x,y) /\ R1 a x /\ R2 b y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_REL_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 [local,simp]: case expressions with one constant result *)
let v_case_const = prove
 (CASE_TERM `!x (c:A).
     (match x with
        clos_Number _ -> c | clos_Word64 _ -> c | clos_Block _ _ -> c
      | ByteVector _ -> c | clos_RefPtr _ _ -> c | clos_Closure _ _ _ _ _ -> c
      | clos_Recclosure _ _ _ _ _ -> c) = c`,
  GEN_TAC THEN CASES_ON `x:clos_v` THEN REWRITE_TAC[case_def "clos_v"]);;

let option_case_const = prove
 (CASE_TERM `!(x:B option) (c:A). (match x with NONE -> c | SOME _ -> c) = c`,
  GEN_TAC THEN CASES_ON `x:B option` THEN REWRITE_TAC[case_def "option"]);;

let list_case_const = prove
 (CASE_TERM `!(x:B list) (c:A). (match x with [] -> c | CONS _ _ -> c) = c`,
  GEN_TAC THEN CASES_ON `x:B list` THEN REWRITE_TAC[case_def "list"]);;

let LIST_REL_REFL_EVERY = prove
 (`!(R:A->A->bool) l. ALL2 R l l <=> ALL (\x. R x x) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; ALL]);;

let POS_INT_EQ_NUM = prove
 (`!i:int. &0 <= i <=> ?n. i = &n`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `num_of_int i` THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POS]]);;

let simple_val_rel_Boolv = prove
 (`!vr b v1.
     clos_simple_val_rel vr ==>
     (vr (clos_Boolv b) v1 ==> v1 = clos_Boolv b) /\
     (vr v1 (clos_Boolv b) ==> v1 = clos_Boolv b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def]) THEN
  REWRITE_TAC[clos_Boolv_def] THEN ASM_REWRITE_TAC[LIST_REL_NIL] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CASES_ON `v1:clos_v` THEN
  ASM_REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; LIST_REL_NIL] THEN
  ASM_MESON_TAC[clos_isClos_def; LIST_REL_NIL]);;

(* local helpers for simple_val_rel_do_app_rev: the converses of a simple   *)
(* value relation and a simple state relation are simple again             *)
let CLOSPROPSAUX_ALL2_conv = prove
 (`!(R:A->B->bool) l1 l2. ALL2 (\x y. R y x) l1 l2 <=> ALL2 R l2 l1`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:A list` list_CASES) THEN
  ASM_REWRITE_TAC[ALL2]);;

let CLOSPROPSAUX_OPTREL_conv = prove
 (`!(R:A->B->bool). OPTREL (\x y. R y x) = (\a b. OPTREL R b a)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT(MATCH_MP_TAC option_INDUCT THEN REPEAT STRIP_TAC) THEN
  REWRITE_TAC[OPTREL_def; distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let CLOSPROPSAUX_svr_conv = prove
 (`!vr. clos_simple_val_rel vr ==> clos_simple_val_rel (\x y. vr y x)`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(MATCH_MP CLOSPROPSAUX_vr_left th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[clos_simple_val_rel_def] th)) THEN
  REWRITE_TAC[clos_simple_val_rel_def;
              ISPEC `vr:clos_v->clos_v->bool` CLOSPROPSAUX_ALL2_conv] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `x:clos_v` THEN
  ASM_REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; clos_isClos_def] THEN
  TRY(DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
    `!x5 x4 x3 x2 x1 x. (vr:clos_v->clos_v->bool) x (clos_Closure x1 x2 x3 x4 x5)
                        ==> clos_isClos x`)) THEN REWRITE_TAC[clos_isClos_def] THEN NO_TAC) THEN
  TRY(DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
    `!y5 y4 y3 y2 y1 x. (vr:clos_v->clos_v->bool) x (clos_Recclosure y1 y2 y3 y4 y5)
                        ==> clos_isClos x`)) THEN REWRITE_TAC[clos_isClos_def] THEN NO_TAC) THEN
  MESON_TAC[]);;

let CLOSPROPSAUX_FLK_TAC : tactic =
  MP_TAC(ISPECL [`vr:clos_v->clos_v->bool`; `sr:(D,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `t:(D,FFI)clos_state`; `s:(C,FFI)clos_state`; `ptr:num`;
                 `FLOOKUP (clos_state_refs (s:(C,FFI)clos_state)) ptr`]
                simple_state_rel_FLOOKUP_refs_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[case_def "option"] THEN
  TRY(CASES_ON `a:(clos_v)clos_ref`) THEN REWRITE_TAC[case_def "clos_ref"] THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "option"; injectivity "clos_ref";
                  distinctness "clos_ref"] THEN
  MESON_TAC[];;

let CLOSPROPSAUX_ssr_conv = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool).
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr ==>
     clos_simple_state_rel (\x y. vr y x) (\s t. sr t s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[clos_simple_state_rel_def] th))) THEN
  REWRITE_TAC[clos_simple_state_rel_def;
              ISPEC `vr:clos_v->clos_v->bool` CLOSPROPSAUX_OPTREL_conv] THEN
  REWRITE_TAC[ISPEC `vr:clos_v->clos_v->bool` CLOSPROPSAUX_ALL2_conv;
              ISPEC `OPTREL (vr:clos_v->clos_v->bool)` CLOSPROPSAUX_ALL2_conv] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [CLOSPROPSAUX_FLK_TAC; CLOSPROPSAUX_FLK_TAC; CLOSPROPSAUX_FLK_TAC; CLOSPROPSAUX_FLK_TAC;
    ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
    ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* local helpers for simple_val_rel_do_app_rev: values related to Boolv and *)
(* Unit, the integer and word operations, bad thunk updates, constants     *)
let CLOSPROPSAUX_vr_Boolv = prove
 (`!vr. clos_simple_val_rel vr ==>
     (!x b. vr x (clos_Boolv b) <=> x = clos_Boolv b) /\
     (!x. vr x clos_Unit <=> x = clos_Unit)`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def]) THEN
  ASM_REWRITE_TAC[clos_Boolv_def; clos_Unit_def; LIST_REL_NIL] THEN MESON_TAC[]);;

(* the case-tree definitions made by sem1aux_def (one clause per function) *)
let CLOSPROPSAUX_tree name =
  let th = find (fun th -> try fst(dest_const(lhs(concl th))) = name
                           with Failure _ -> false) (definitions()) in
  let vs = fst(strip_abs(rhs(concl th))) in
  GENL vs (RIGHT_BETAS vs th);;

let CLOSPROPSAUX_vr_rws () =
  let svr = ASSUME `clos_simple_val_rel (vr:clos_v->clos_v->bool)` in
  let cls = CONJUNCTS (EQ_MP (ISPEC `vr:clos_v->clos_v->bool` simple_val_rel_alt) svr) @
            CONJUNCTS (MATCH_MP CLOSPROPSAUX_vr_Boolv svr) in
  filter (fun th -> is_iff (snd (strip_forall (concl th)))) cls;;

(* the shapes of the source values from those of the target values: only *)
(* the facts vr x (C ..) and ALL2 vr xs (CONS ..) or ALL2 vr xs [] are used *)
let CLOSPROPSAUX_SHAPE_TAC : tactic = fun gl ->
  let rws = LIST_REL_CONS2 :: LIST_REL_NIL :: CLOSPROPSAUX_vr_rws () in
  let vrt = `vr:clos_v->clos_v->bool` in
  let is_shape_fact th =
    let c = concl th in
    try let f,args = strip_comb c in
        (f = vrt && length args = 2 && not (is_var (el 1 args))) ||
        (fst(dest_const f) = "ALL2" && length args = 3 && hd args = vrt &&
         not (is_var (el 2 args)))
    with Failure _ -> false in
  (REPEAT (FIRST_X_ASSUM (fun th ->
     if is_shape_fact th then
       let th' = REWRITE_RULE rws th in
       if concl th' = concl th then failwith "SHAPE" else CAKE_STRIP_ASSUME_TAC th'
     else failwith "SHAPE") THEN RVEQ_TAC)) gl;;

(* a leaf: Rval or an FFI error on the target side (an antecedent ~(r = E) *)
(* and r = L); the goal becomes the relation of the source result with L  *)
let CLOSPROPSAUX_LEAF_TAC : tactic =
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    MP_TAC (REWRITE_RULE[SYM th2] th1) THEN SUBST1_TAC (SYM th2))) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result";
              injectivity "error_result"; distinctness "abort"; injectivity "abort"] THEN
  TRY DISCH_TAC;;

let CLOSPROPSAUX_do_int_app_rel = prove
 (`!vr op xs ys r.
     clos_simple_val_rel vr /\ ALL2 vr xs ys /\ clos_do_int_app op ys = SOME r ==>
     clos_do_int_app op xs = SOME r /\ vr r r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_do_int_app"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN CLOSPROPSAUX_SHAPE_TAC THEN
  ASM_REWRITE_TAC(clos_do_int_app_def :: CLOSPROPSAUX_vr_rws ()));;

let CLOSPROPSAUX_do_word_app_rel = prove
 (`!vr op xs ys r.
     clos_simple_val_rel vr /\ ALL2 vr xs ys /\ clos_do_word_app op ys = SOME r ==>
     clos_do_word_app op xs = SOME r /\ vr r r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_do_word_app"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN CLOSPROPSAUX_SHAPE_TAC THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC(clos_do_word_app_def :: CLOSPROPSAUX_vr_rws ()) THEN
                     CASE_REWRITE_TAC[])));;

let CLOSPROPSAUX_bad_thunk_rel = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t x y m.
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr /\ sr s t /\ vr x y ==>
     (clos_bad_thunk_update m x (clos_state_refs s) <=>
      clos_bad_thunk_update m y (clos_state_refs t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[clos_bad_thunk_update_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def] o
    check (fun th -> concl th = `clos_simple_val_rel (vr:clos_v->clos_v->bool)`)) THEN
  CASES_ON `y:clos_v` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator(rator(concl th)) =
                                  `vr:clos_v->clos_v->bool` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[isClos_cases] o
        check (fun th -> try fst(dest_const(rator(concl th))) = "clos_isClos"
                         with Failure _ -> false)) THEN RVEQ_TAC) THEN
  REWRITE_TAC[clos_dest_thunk_def] THEN
  MP_TAC(ISPECL [`vr:clos_v->clos_v->bool`; `sr:(D,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s:(D,FFI)clos_state`; `t:(C,FFI)clos_state`; `a1:num`;
                 `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) a1`]
                simple_state_rel_FLOOKUP_refs_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) a1` THEN
  REWRITE_TAC[case_def "option"] THEN
  TRY(CASES_ON `a:(clos_v)clos_ref`) THEN REWRITE_TAC[case_def "clos_ref"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a0':thunk_mode`) THEN CASE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[]);;

let CLOSPROPSAUX_make_const_rel = prove
 (`!vr. clos_simple_val_rel vr ==> !c. vr (make_const c) (make_const c)`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def]) THEN
  MATCH_MP_TAC make_const_ind THEN ASM_REWRITE_TAC[make_const_def; injectivity "clos_v"] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNWIND_THM1; LIST_REL_REFL_EVERY; ALL_MAP; o_DEF] THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM]);;

let CLOSPROPSAUX_ssr_ffi_bytes = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t p ws f.
     clos_simple_state_rel vr sr /\ sr s t ==>
     sr (clos_state_refs_fupd (K (clos_state_refs s |+ (p,clos_ByteArray ws)))
           (clos_state_ffi_fupd (K f) s))
        (clos_state_refs_fupd (K (clos_state_refs t |+ (p,clos_ByteArray ws)))
           (clos_state_ffi_fupd (K f) t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vr:clos_v->clos_v->bool`; `sr:(D,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `clos_state_ffi_fupd (K (f:(FFI)ffi_state)) (s:(D,FFI)clos_state)`;
                 `clos_state_ffi_fupd (K (f:(FFI)ffi_state)) (t:(C,FFI)clos_state)`;
                 `p:num`; `ws:byte list`] simple_state_rel_update_bytes) THEN
  ASM_SIMP_TAC[simple_state_rel_update_ffi; clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_MESON_TAC[simple_state_rel_update_ffi]);;

let CLOSPROPSAUX_ssr_globals = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t.
     clos_simple_state_rel vr sr /\ sr s t ==>
     ALL2 (OPTREL vr) (clos_state_globals s) (clos_state_globals t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN MESON_TAC[]);;

let CLOSPROPSAUX_num_of_int_lt = prove
 (`!i n. &0 <= i /\ i < &n ==> num_of_int i < n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]);;

(* forward reasoning at a leaf: the source facts from the target facts *)
let CLOSPROPSAUX_SYNC_TAC : tactic = fun (asl,w as gl) ->
  let vrt = `vr:clos_v->clos_v->bool` in
  let svr = ASSUME `clos_simple_val_rel (vr:clos_v->clos_v->bool)` in
  let ssr = ASSUME `clos_simple_state_rel (vr:clos_v->clos_v->bool)
                      (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool)` in
  let srst = ASSUME `(sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t` in
  let refs_t = `clos_state_refs (t:(C,FFI)clos_state)` in
  let globs_t = `clos_state_globals (t:(C,FFI)clos_state)` in
  let asms = map snd asl in
  let headc tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
  let vr_facts = filter (fun th -> try rator(rator(concl th)) = vrt
                                   with Failure _ -> false) asms in
  let find_vr y = find (fun th -> rand(concl th) = y) vr_facts in
  let all2_facts = filter (fun th -> try (let f,args = strip_comb (concl th) in
         fst(dest_const f) = "ALL2" && hd args = vrt) with Failure _ -> false) asms in
  let find_all2 l = find (fun th -> rand(concl th) = l) all2_facts in
  let is_constr_value r =
    headc r = "NONE" || (headc r = "SOME" && not (is_var (rand r))) in
  let derive th =
    let c = concl th in
    if is_eq c then
      let l = lhs c and r = rhs c in
      match headc l with
        "FLOOKUP" when rand(rator l) = refs_t && is_constr_value r ->
          [CASE_REWRITE_RULE []
             (MATCH_MP simple_state_rel_FLOOKUP_refs_IMP (CONJ ssr (CONJ srst th)))]
      | "get_global" when rand l = globs_t && is_constr_value r ->
          [CASE_REWRITE_RULE []
             (MATCH_MP simple_state_rel_get_global (CONJ ssr (CONJ srst th)))]
      | "clos_v_to_list" ->
          let vth = find_vr (rand l) in
          if headc r = "SOME" then
            [MATCH_MP (MATCH_MP CLOSPROPSAUX_v_to_list_SOME svr) (CONJ vth th)]
          else if headc r = "NONE" then
            [MATCH_MP (MATCH_MP CLOSPROPSAUX_v_to_list_NONE svr) (CONJ vth th)]
          else []
      | "clos_do_eq" ->
          let eqth = MATCH_MP (CONJUNCT1 (MATCH_MP v_rel_do_eq svr))
                       (CONJ (find_vr (rand(rator l))) (find_vr (rand l))) in
          [TRANS eqth th]
      | "clos_do_int_app" ->
          [MATCH_MP CLOSPROPSAUX_do_int_app_rel (CONJ svr (CONJ (find_all2 (rand l)) th))]
      | "clos_do_word_app" ->
          [MATCH_MP CLOSPROPSAUX_do_word_app_rel (CONJ svr (CONJ (find_all2 (rand l)) th))]
      | "some" ->
          let y = rand (find_term (fun t -> headc t = "clos_v_to_list") l) in
          let vth = find_vr y in
          let iffs = mapfilter (fun lem -> MATCH_MP (MATCH_MP lem svr) vth)
                       [v_rel_to_list_ByteVector; v_rel_to_list_byte2] in
          [REWRITE_RULE (map GSYM iffs) th]
      | _ -> []
    else
      let c0 = if is_neg c then dest_neg c else c in
      if headc c0 = "clos_bad_thunk_update" then
        let eq = MATCH_MP CLOSPROPSAUX_bad_thunk_rel
                   (CONJ svr (CONJ ssr (CONJ srst (find_vr (rand(rator c0)))))) in
        [REWRITE_RULE [GSYM eq] th]
      else if headc c = "ALL2" then [MATCH_MP LIST_REL_LENGTH th]
      else [] in
  let news = flat (map (fun th -> try derive th with Failure _ -> []) asms) in
  let news = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) news in
  EVERY (map CAKE_STRIP_ASSUME_TAC news) gl;;

(* the facts of the state relation used at every leaf *)
let CLOSPROPSAUX_SSR_FACTS_TAC : tactic =
  let tms = [`vr:clos_v->clos_v->bool`; `sr:(D,FFI)clos_state->(C,FFI)clos_state->bool`;
             `s:(D,FFI)clos_state`; `t:(C,FFI)clos_state`] in
  MP_TAC(ISPECL tms simple_state_rel_ffi) THEN
  MP_TAC(ISPECL tms simple_state_rel_fdom) THEN
  MP_TAC(ISPECL tms CLOSPROPSAUX_ssr_globals) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

(* the lengths of related lists *)
let CLOSPROPSAUX_LENGTH_TAC : tactic = fun (asl,w as gl) ->
  let vrt = `vr:clos_v->clos_v->bool` in
  let asms = map snd asl in
  let news = mapfilter (fun th ->
      let f,args = strip_comb (concl th) in
      if fst(dest_const f) = "ALL2" && hd args = vrt then MATCH_MP LIST_REL_LENGTH th
      else failwith "") asms in
  let news = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) news in
  EVERY (map ASSUME_TAC news) gl;;

(* evaluate the source side *)
let CLOSPROPSAUX_EVAL_TAC : tactic =
  REWRITE_TAC[clos_do_app_def; LET_DEF; LET_END_DEF] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[result_rel_def; exc_rel_def; PAIR_REL_THM];;

(* the target condition of BoolTest: ~(~(v = Boolv T) /\ ~(v = Boolv F)) *)
let CLOSPROPSAUX_BOOL_SPLIT_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT `~(~a /\ ~b) <=> a \/ b`]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RVEQ_TAC;;

let CLOSPROPSAUX_FINISH_TAC : tactic = fun gl ->
  let vrt = `vr:clos_v->clos_v->bool` in
  let svr = ASSUME `clos_simple_val_rel (vr:clos_v->clos_v->bool)` in
  let rws = CLOSPROPSAUX_vr_rws () in
  let vl2v = MATCH_MP CLOSPROPSAUX_vr_list_to_v svr in
  let mc = MATCH_MP CLOSPROPSAUX_make_const_rel svr in
  (CONJ_TAC THENL
    [REWRITE_TAC (injectivity "clos_v" :: list_to_v_INJ :: vl2v :: mc :: rws) THEN
     REWRITE_TAC[UNWIND_THM1; LIST_REL_REFL_EVERY; ALL_MAP; o_DEF] THEN
     ASM_REWRITE_TAC (ALL_T :: rws) THEN
     TRY(MATCH_MP_TAC LIST_REL_APPEND_suff THEN
         ASM_SIMP_TAC[EVERY2_TAKE; EVERY2_DROP] THEN NO_TAC) THEN
     ASM_MESON_TAC[LIST_REL_EL_EQN; CLOSPROPSAUX_num_of_int_lt];
     ASM_REWRITE_TAC[] THEN
     FIRST [MATCH_MP_TAC (ISPEC vrt CLOSPROPSAUX_ssr_ffi_bytes);
            MATCH_MP_TAC (ISPEC vrt simple_state_rel_update_bytes);
            MATCH_MP_TAC (ISPEC vrt simple_state_rel_update_values);
            MATCH_MP_TAC (ISPEC vrt simple_state_rel_update_thunks);
            MATCH_MP_TAC (ISPEC vrt simple_state_rel_update_globals)] THEN
     ASM_REWRITE_TAC[LIST_REL_REPLICATE_same] THEN
     TRY(MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[OPTREL_THM] THEN NO_TAC) THEN
     TRY(MATCH_MP_TAC LIST_REL_APPEND_suff THEN
         ASM_REWRITE_TAC[LIST_REL_REPLICATE_same; OPTREL_THM] THEN NO_TAC) THEN
     ASM_MESON_TAC[]]) gl;;

(* the target is related to the source when it is a value or an FFI error *)
let CLOSPROPSAUX_do_app_rel = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys opp r.
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr /\ sr s t /\ ALL2 vr xs ys /\
     clos_do_app opp ys t = r /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     result_rel (vr ### sr) vr (clos_do_app opp xs s) r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 MP_TAC MP_TAC))))) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN CLOSPROPSAUX_LEAF_TAC THEN
  CLOSPROPSAUX_BOOL_SPLIT_TAC THEN
  CLOSPROPSAUX_SHAPE_TAC THEN CLOSPROPSAUX_SSR_FACTS_TAC THEN
  CLOSPROPSAUX_SYNC_TAC THEN CLOSPROPSAUX_LENGTH_TAC THEN CLOSPROPSAUX_SHAPE_TAC THEN
  CLOSPROPSAUX_EVAL_TAC THEN CLOSPROPSAUX_FINISH_TAC);;

(* the result_rel form (the qsuff_tac of HOL4's proof) *)
let CLOSPROPSAUX_do_app_result_rel = prove
 (`!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys opp.
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr ==>
     sr s t /\ ALL2 vr xs ys ==>
     result_rel (vr ### sr) vr (clos_do_app opp xs s) (clos_do_app opp ys t)`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `clos_do_app opp ys (t:(C,FFI)clos_state) = Rerr (Rabort Rtype_error)` THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSPROPSAUX_do_app_rel THEN
    MAP_EVERY EXISTS_TAC [`t:(C,FFI)clos_state`; `ys:clos_v list`] THEN
    ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `clos_do_app opp xs (s:(D,FFI)clos_state) = Rerr (Rabort Rtype_error)` THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN
  MP_TAC(ISPECL [`\x y. (vr:clos_v->clos_v->bool) y x`;
                 `\s t. (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) t s`;
                 `t:(C,FFI)clos_state`; `s:(D,FFI)clos_state`; `ys:clos_v list`;
                 `xs:clos_v list`; `opp:clos_op`; `clos_do_app opp xs (s:(D,FFI)clos_state)`]
                CLOSPROPSAUX_do_app_rel) THEN
  ASM_SIMP_TAC[CLOSPROPSAUX_svr_conv; CLOSPROPSAUX_ssr_conv;
               ISPEC `vr:clos_v->clos_v->bool` CLOSPROPSAUX_ALL2_conv] THEN
  REWRITE_TAC[result_rel_Rerr1; exc_rel_type_error1] THEN ASM_MESON_TAC[]);;

(* HOL4: simple_val_rel_do_app_rev *)
let simple_val_rel_do_app_rev = prove
 (CASE_TERM `!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys opp.
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr ==>
     sr s t /\ ALL2 vr xs ys ==>
     match clos_do_app opp ys t with
       Rerr err2 -> (?err1. clos_do_app opp xs s = Rerr err1 /\ exc_rel vr err1 err2)
     | Rval (y,t1) -> ?x s1. vr x y /\ sr s1 t1 /\ clos_do_app opp xs s = Rval (x,s1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL CLOSPROPSAUX_do_app_result_rel) THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `clos_do_app opp ys (t:(C,FFI)clos_state)` THEN
  REWRITE_TAC[case_def "result"; clos_result_rel_Rval2; result_rel_Rerr2] THEN
  TRY(CASES_ON `a:clos_v#(C,FFI)clos_state`) THEN
  REWRITE_TAC[case_def "prod"; PAIR_REL_SIMP] THEN MESON_TAC[]);;

(* HOL4: simple_val_rel_do_app *)
let simple_val_rel_do_app = prove
 (CASE_TERM `!vr (sr:(D,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys opp.
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr ==>
     sr s t /\ ALL2 vr xs ys ==>
     match clos_do_app opp xs s with
       Rerr err1 -> (?err2. clos_do_app opp ys t = Rerr err2 /\ exc_rel vr err1 err2)
     | Rval (x,s1) -> ?y t1. vr x y /\ sr s1 t1 /\ clos_do_app opp ys t = Rval (y,t1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL CLOSPROPSAUX_do_app_result_rel) THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `clos_do_app opp xs (s:(D,FFI)clos_state)` THEN
  REWRITE_TAC[case_def "result"; result_rel_Rval; result_rel_Rerr1] THEN
  TRY(CASES_ON `a:clos_v#(D,FFI)clos_state`) THEN
  REWRITE_TAC[case_def "prod"; PAIR_REL_SIMP] THEN MESON_TAC[]);;

(* generic do_install compile proof *)
let simple_compile_state_rel_def = cake_def
  `simple_compile_state_rel (vr:clos_v->clos_v->bool)
      (sr:(C,FFI)clos_state->(C,FFI)clos_state->bool) (comp:clos_prog->clos_prog)
      (cr:clos_exp list->clos_exp list->bool) <=>
     clos_simple_state_rel vr sr /\
     (!(s:(C,FFI)clos_state) (t:(C,FFI)clos_state).
        sr s t ==>
        clos_state_clock t = clos_state_clock s /\
        clos_state_compile s = pure_cc comp (clos_state_compile t) /\
        clos_state_compile_oracle t = pure_co comp o clos_state_compile_oracle s /\
        (!n exps res p aux. SND (clos_state_compile_oracle s n) = (p,aux) ==>
           comp (p,aux) = (exps,res) ==>
           res = [] /\ LENGTH exps = LENGTH p /\ cr p exps) /\
        (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
        (!n. sr (clos_state_clock_fupd (K n)
                  (clos_state_compile_oracle_fupd
                     (K (shift_seq 1 (clos_state_compile_oracle s)))
                     (clos_state_code_fupd (K (clos_state_code s)) s)))
                (clos_state_clock_fupd (K n)
                  (clos_state_compile_oracle_fupd
                     (K (shift_seq 1 (clos_state_compile_oracle t)))
                     (clos_state_code_fupd (K (clos_state_code t)) t)))))`;;

(* HOL4: simple_val_rel_v_to_bytes *)
let clos_simple_val_rel_v_to_bytes = prove
 (`!vr x y. clos_simple_val_rel vr /\ vr x y ==> clos_v_to_bytes x = clos_v_to_bytes y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_v_to_bytes_def] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `ns:byte list` THEN
  REWRITE_TAC[o_ASSOC] THEN ONCE_REWRITE_TAC[MAP_o] THEN
  MP_TAC(SPEC `vr:clos_v->clos_v->bool` v_rel_to_list_byte1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `x:clos_v`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let simple_val_rel_Word64_left = prove
 (`!vr. clos_simple_val_rel vr ==> !x w. vr (clos_Word64 w) x <=> x = clos_Word64 w`,
  MESON_TAC[CLOSPROPSAUX_vr_left]);;

let val_rel_to_words_lemma = prove
 (`!vr. clos_simple_val_rel vr ==>
     !xs ys. ALL2 vr xs ys ==> !ns. xs = MAP clos_Word64 ns <=> ys = MAP clos_Word64 ns`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(REWRITE_RULE[clos_simple_val_rel_def] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP CLOSPROPSAUX_vr_left th)) THEN
  SUBGOAL_THEN `(!ys xs. ALL2 (vr:clos_v->clos_v->bool) xs (MAP clos_Word64 ys) <=>
                         xs = MAP clos_Word64 ys) /\
                (!xs ys. ALL2 (vr:clos_v->clos_v->bool) (MAP clos_Word64 xs) ys <=>
                         ys = MAP clos_Word64 xs)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSPROPSAUX_ALL2_MAP_right; MATCH_MP_TAC CLOSPROPSAUX_ALL2_MAP_left] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4: simple_val_rel_v_to_words (HOL4 leaves vr free) *)
let clos_simple_val_rel_v_to_words = prove
 (`!x y vr. clos_simple_val_rel vr /\ vr x y ==> clos_v_to_words x = clos_v_to_words y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_v_to_words_def] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `ns:int64 list` THEN
  MP_TAC(ISPEC `clos_v_to_list y` (cases "option")) THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`x:clos_v`; `y:clos_v`; `vr:clos_v->clos_v->bool`] vr_list_NONE) THEN
    ASM_REWRITE_TAC[distinctness "option"] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[distinctness "option"];
    MP_TAC(SPEC `vr:clos_v->clos_v->bool` CLOSPROPSAUX_v_to_list_SOME) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `a:clos_v list`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN
    MP_TAC(SPEC `vr:clos_v->clos_v->bool` val_rel_to_words_lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`xs:clos_v list`; `a:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* a local helper: do_install of a list that is not a pair *)
let CLOSPROPSAUX_do_install_not2 = prove
 (`!xs (s:(C,FFI)clos_state).
     (!x1 x2. ~(xs = [x1; x2])) ==> clos_do_install xs s = (Rerr (Rabort Rtype_error),s)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_do_install_def; case_def "list"] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[case_def "list"] THEN
  STRUCT_CASES_TAC(ISPEC `t':clos_v list` list_CASES) THEN
  REWRITE_TAC[case_def "list"; injectivity "list"] THEN MESON_TAC[]);;

(* local helpers for simple_val_rel_do_install: do_install when the oracle *)
(* installs no auxiliary code                                               *)
let CLOSPROPSAUX_code_fupd_same = prove
 (`!f g (s:(C,FFI)clos_state).
     clos_state_code_fupd (K (clos_state_code s))
       (clos_state_compile_oracle_fupd f (clos_state_clock_fupd g s)) =
     clos_state_compile_oracle_fupd f (clos_state_clock_fupd g s)`,
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_do_install_char = prove
 (`!v1 v2 (s:(C,FFI)clos_state) cfg p.
     clos_state_compile_oracle s 0 = (cfg,p,[]) ==>
     clos_do_install [v1; v2] s =
     if (?bytes data cfg'.
           clos_v_to_bytes v1 = SOME bytes /\ clos_v_to_words v2 = SOME data /\
           clos_state_compile s cfg (p,[]) = SOME (bytes,data,cfg') /\
           FST (clos_state_compile_oracle s 1) = cfg') /\ ~(p = [])
     then ((if clos_state_clock s = 0 then Rerr (Rabort Rtimeout_error) else Rval p),
           clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s)))
             (clos_state_clock_fupd (K (clos_state_clock s - 1)) s))
     else (Rerr (Rabort Rtype_error),s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[clos_do_install_def; case_def "list"; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE] THEN
  REWRITE_TAC[MAP; set_of_list; DISJOINT_EMPTY; ALL_DISTINCT; FUPDATE_LIST_THM] THEN
  CASES_ON `clos_v_to_bytes v1` THEN CASES_ON `clos_v_to_words v2` THEN
  REWRITE_TAC[case_def "option"; pair_CASE; distinctness "option"; injectivity "option"] THEN
  CASES_ON `clos_state_compile (s:(C,FFI)clos_state) cfg (p,[])` THEN
  REWRITE_TAC[case_def "option"; pair_CASE; distinctness "option"; injectivity "option"] THEN
  MP_TAC(ISPEC `a'':byte list # int64 list # C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:byte list` (X_CHOOSE_THEN `rest:int64 list # C` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `rest:int64 list # C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int64 list` (X_CHOOSE_THEN `c:C` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ; shift_seq_def; ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[CLOSPROPSAUX_code_fupd_same] THEN
  SUBGOAL_THEN `(?bytes data cfg'.
          (a:byte list) = bytes /\ (a':int64 list) = data /\
          ((b:byte list) = bytes /\ (d:int64 list) = data /\ (c:C) = cfg') /\
          FST (clos_state_compile_oracle (s:(C,FFI)clos_state) 1) = cfg') <=>
          a = b /\ a' = d /\ FST (clos_state_compile_oracle s 1) = c` SUBST1_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let simple_val_rel_do_install = prove
 (CASE_TERM `!comp vr (sr:(C,FFI)clos_state->(C,FFI)clos_state->bool) cr s t xs ys.
     clos_simple_val_rel vr /\ simple_compile_state_rel vr sr comp cr ==>
     sr s t /\ ALL2 vr xs ys ==>
     match clos_do_install xs s with
       (Rerr err1,s1) -> ?err2 t1. clos_do_install ys t = (Rerr err2,t1) /\
                                   exc_rel vr err1 err2 /\ sr s1 t1
     | (Rval exps1,s1) -> ?exps2 t1. sr s1 t1 /\ ~(exps1 = []) /\ cr exps1 exps2 /\
                                     clos_do_install ys t = (Rval exps2,t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_compile_state_rel_def] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?x1 x2 y1 y2. xs = [x1:clos_v; x2] /\ ys = [y1:clos_v; y2] /\
                               vr x1 y1 /\ vr x2 y2) \/
                (!x1 x2. ~(xs = [x1; x2])) /\ (!y1 y2. ~(ys = [y1; y2]))`
    MP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "ALL2" o concl))) THEN
    STRUCT_CASES_TAC (ISPEC `xs:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1; distinctness "list"; injectivity "list"] THEN
    TRY(STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "list"] THEN NO_TAC) THEN
    STRUCT_CASES_TAC (ISPEC `t':clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1; distinctness "list"; injectivity "list"] THEN
    TRY(STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "list"] THEN NO_TAC) THEN
    STRUCT_CASES_TAC (ISPEC `t'':clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1; distinctness "list"; injectivity "list"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "list"; injectivity "list"] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN STRIP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CLOSPROPSAUX_do_install_not2; pair_CASE; case_def "result"] THEN
    MAP_EVERY EXISTS_TAC [`Rabort Rtype_error:(clos_v)error_result`;
                          `t:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[exc_rel_def]] THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `clos_v_to_bytes y1 = clos_v_to_bytes x1 /\
                clos_v_to_words y2 = clos_v_to_words x2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_simple_val_rel_v_to_bytes; clos_simple_val_rel_v_to_words];
    ALL_TAC] THEN
  SUBGOAL_THEN `?cfg p. clos_state_compile_oracle (s:(C,FFI)clos_state) 0 = (cfg,p,[])`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o
      check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) = "n" &&
                           is_eq(snd(dest_forall(concl th))) &&
                           not (is_imp(snd(dest_forall(concl th))))
                       with Failure _ -> false)) THEN
    MESON_TAC[PAIR; FST; SND];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(comp:clos_prog->clos_prog) (p,[])` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `exps':clos_exp list` (X_CHOOSE_THEN `res:(num#num#clos_exp)list`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `res:(num#num#clos_exp)list = [] /\
                LENGTH (exps':clos_exp list) = LENGTH (p:clos_exp list) /\
                (cr:clos_exp list->clos_exp list->bool) p exps'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SND]; ALL_TAC] THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `clos_state_compile_oracle (t:(C,FFI)clos_state) 0 = (cfg,exps',[]) /\
                FST (clos_state_compile_oracle t 1) =
                FST (clos_state_compile_oracle (s:(C,FFI)clos_state) 1) /\
                clos_state_compile t cfg (exps',[]) = clos_state_compile s cfg (p,[]) /\
                (exps' = [] <=> p = [])`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[o_THM; FST_pure_co; pure_cc_def; LET_DEF; LET_END_DEF;
                    GSYM LENGTH_EQ_NIL] THEN
    ASM_REWRITE_TAC[pure_co_def; PAIR_MAP_THM; I_THM];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
     let c = concl th in is_eq c && (is_const (rator (lhs c)) || true) &&
       (lhs c = `clos_state_compile (s:(C,FFI)clos_state)` ||
        lhs c = `clos_state_compile_oracle (t:(C,FFI)clos_state)`)))) THEN
  MP_TAC(SPECL [`x1:clos_v`; `x2:clos_v`; `s:(C,FFI)clos_state`; `cfg:C`; `p:clos_exp list`]
               CLOSPROPSAUX_do_install_char) THEN
  MP_TAC(SPECL [`y1:clos_v`; `y2:clos_v`; `t:(C,FFI)clos_state`; `cfg:C`;
                `exps':clos_exp list`] CLOSPROPSAUX_do_install_char) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[pair_CASE; case_def "result"] THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`Rabort Rtype_error:(clos_v)error_result`;
                          `t:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[exc_rel_def]] THEN
  SUBGOAL_THEN
   `(sr:(C,FFI)clos_state->(C,FFI)clos_state->bool)
      (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s)))
          (clos_state_clock_fupd (K (clos_state_clock s - 1)) (s:(C,FFI)clos_state)))
       (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t)))
          (clos_state_clock_fupd (K (clos_state_clock t - 1)) (t:(C,FFI)clos_state)))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `clos_state_clock (s:(C,FFI)clos_state) - 1` o
      check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) = "n" &&
                           not (is_eq(snd(dest_forall(concl th)))) &&
                           not (is_imp(snd(strip_forall(concl th))))
                       with Failure _ -> false)) THEN
    MATCH_MP_TAC(MESON[] `(a:(C,FFI)clos_state) = c /\ (b:(C,FFI)clos_state) = d ==>
      ((sr:(C,FFI)clos_state->(C,FFI)clos_state->bool) a b ==> sr c d)`) THEN
    REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `clos_state_clock (t:(C,FFI)clos_state) =
                                      clos_state_clock (s:(C,FFI)clos_state)`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[case_def "result"; PAIR_EQ; injectivity "result"; exc_rel_def] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  ASM_MESON_TAC[exc_rel_def]);;

(* after do_install evaluate uses the LAST element, and this helps *)
let LIST_REL_LAST = prove
 (`!(P:A->B->bool) xs ys. ALL2 P xs ys /\ ~(xs = []) ==> P (LAST xs) (LAST ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_TAC THEN REWRITE_TAC[LIST_REL_CONS1] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[LAST] THEN
  ASM_CASES_TAC `t:A list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(t':B list = [])` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[LIST_REL_NIL]; ASM_MESON_TAC[]]]);;

(* a generic semantics preservation lemma *)

(* HOL4: FST_EQ_LEMMA [local] *)
let clos_FST_EQ_LEMMA = prove
 (`!(x:A#B) y. FST x = y <=> ?y1. x = (y,y1)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 [simp] *)
let initial_state_max_app = prove
 (`!(ffi:(FFI)ffi_state) max_app code (co:num -> C # clos_prog) cc k.
     clos_state_max_app (clos_initial_state ffi max_app code co cc k) = max_app`,
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors]);;
let _ = cake_add_simps [initial_state_max_app];;

(* HOL4: eval_sim_def *)
let clos_eval_sim_def = cake_def
  `clos_eval_sim (ffi:(FFI)ffi_state) max_app code1 (co1:num -> A # clos_prog) cc1 es1
                 code2 (co2:num -> B # clos_prog) cc2 es2 rel allow_fail <=>
     !k res1 s2.
       clos_evaluate (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k) = (res1,s2) /\
       (allow_fail \/ ~(res1 = Rerr (Rabort Rtype_error))) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
       ?ck res2 t2.
         clos_evaluate (es2,[],clos_initial_state ffi max_app code2 co2 cc2 (k + ck)) =
         (res2,t2) /\
         result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                    res1 res2 /\
         clos_state_ffi s2 = clos_state_ffi t2`;;

(* HOL4: initial_state_with_clock [local] *)
let clos_initial_state_with_clock = prove
 (`!(ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k ck.
     clos_state_clock_fupd
       (K (clos_state_clock (clos_initial_state ffi ma code co cc k) + ck))
       (clos_initial_state ffi ma code co cc k) =
     clos_initial_state ffi ma code co cc (k + ck)`,
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_fupds; K_THM]);;

(* local helpers for the semantics lemmas: the least upper bounds of two   *)
(* monotone chains of io-event lists that bound each other are equal       *)
let CLOSPROPSAUX_prefix_LNTH = prove
 (`!(l1:A list) l2 n x.
     l1 <<= l2 /\ LNTH n (llist_fromList l1) = SOME x ==>
     LNTH n (llist_fromList l2) = SOME x`,
  REWRITE_TAC[LNTH_fromList; IS_PREFIX_APPEND] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; EL_APPEND] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < a ==> n < a + b:num`]);;

let CLOSPROPSAUX_mono_chain = prove
 (`!f:num->A list.
     (!k1 k2. k1 <= k2 ==> f k1 <<= f k2) ==>
     lprefix_chain (IMAGE (\k. llist_fromList (f k)) (:num))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\k. llist_fromList ((f:num->A list) k)) (:num) =
                IMAGE llist_fromList (IMAGE f (:num))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; FORALL_IN_IMAGE_2; IN_UNIV] THEN
  ASM_MESON_TAC[LE_CASES]);;

let CLOSPROPSAUX_lub_eq = prove
 (`!(f:num->A list) g.
     (!k1 k2. k1 <= k2 ==> f k1 <<= f k2) /\
     (!k1 k2. k1 <= k2 ==> g k1 <<= g k2) /\
     (!k. ?k'. f k <<= g k') /\ (!k. ?k'. g k <<= f k') ==>
     build_lprefix_lub (IMAGE (\k. llist_fromList (f k)) (:num)) =
     build_lprefix_lub (IMAGE (\k. llist_fromList (g k)) (:num))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lprefix_chain (IMAGE (\k. llist_fromList ((f:num->A list) k)) (:num)) /\
                lprefix_chain (IMAGE (\k. llist_fromList ((g:num->A list) k)) (:num))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSPROPSAUX_mono_chain THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `equiv_lprefix_chain (IMAGE (\k. llist_fromList ((f:num->A list) k)) (:num))
                                    (IMAGE (\k. llist_fromList ((g:num->A list) k)) (:num))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[equiv_lprefix_chain_thm] THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THENL
     [MP_TAC(SPEC `x':num` (ASSUME `!k. ?k'. (f:num->A list) k <<= (g:num->A list) k'`)) THEN
      DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN
      EXISTS_TAC `llist_fromList ((g:num->A list) k')`;
      MP_TAC(SPEC `x':num` (ASSUME `!k. ?k'. (g:num->A list) k <<= (f:num->A list) k'`)) THEN
      DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN
      EXISTS_TAC `llist_fromList ((f:num->A list) k')`] THEN
    (CONJ_TAC THENL [MESON_TAC[]; ASM_MESON_TAC[CLOSPROPSAUX_prefix_LNTH]]);
    ALL_TAC] THEN
  MATCH_MP_TAC unique_lprefix_lub THEN
  EXISTS_TAC `IMAGE (\k. llist_fromList ((g:num->A list) k)) (:num)` THEN
  ASM_SIMP_TAC[build_lprefix_lub_thm] THEN
  MATCH_MP_TAC lprefix_lub_new_chain THEN
  EXISTS_TAC `IMAGE (\k. llist_fromList ((f:num->A list) k)) (:num)` THEN
  ASM_SIMP_TAC[build_lprefix_lub_thm]);;

(* local helpers for IMP_semantics_eq *)
let CLOSPROPSAUX_init_add = prove
 (`!es env (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k ck.
     ~(FST (clos_evaluate (es,env,clos_initial_state ffi ma code co cc k)) =
       Rerr (Rabort Rtimeout_error)) ==>
     FST (clos_evaluate (es,env,clos_initial_state ffi ma code co cc (k + ck))) =
     FST (clos_evaluate (es,env,clos_initial_state ffi ma code co cc k)) /\
     clos_state_ffi (SND (clos_evaluate (es,env,clos_initial_state ffi ma code co cc (k + ck)))) =
     clos_state_ffi (SND (clos_evaluate (es,env,clos_initial_state ffi ma code co cc k)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_evaluate (es,env,clos_initial_state (ffi:(FFI)ffi_state) ma code
                                (co:num -> C # clos_prog) cc k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s:(C,FFI)clos_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`es:clos_exp list`; `env:clos_v list`; `ffi:(FFI)ffi_state`; `ma:num`;
                `code:(num,num#clos_exp)fmap`; `co:num -> C # clos_prog`;
                `cc:C -> clos_prog -> (byte list # int64 list # C) option`; `k:num`;
                `r:(clos_v list,clos_v)result`; `s:(C,FFI)clos_state`]
               clos_evaluate_add_clock_initial_state) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FST; SND; clos_state_INFO.ri_accfupds]);;

let CLOSPROPSAUX_init_mono = prove
 (`!es env (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k1 k2.
     k1 <= k2 ==>
     ffi_state_io_events (clos_state_ffi
       (SND (clos_evaluate (es,env,clos_initial_state ffi ma code co cc k1)))) <<=
     ffi_state_io_events (clos_state_ffi
       (SND (clos_evaluate (es,env,clos_initial_state ffi ma code co cc k2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  MP_TAC(ISPECL [`(es:clos_exp list,env:clos_v list,clos_initial_state (ffi:(FFI)ffi_state) ma code
                     (co:num -> C # clos_prog) cc k1)`;
                 `es:clos_exp list`; `env:clos_v list`;
                 `clos_initial_state (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k1`;
                 `d:num`] (CONJUNCT1 clos_evaluate_add_to_clock_io_events_mono)) THEN
  REWRITE_TAC[clos_initial_state_with_clock]);;

(* HOL4 result_rel (\x y. T) (\x y. T) *)
let CLOSPROPSAUX_result_rel_T = prove
 (`!r1 r2. result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T) r1 r2 <=>
           (?a b. r1 = Rval a /\ r2 = Rval b) \/
           (?a b. r1 = Rerr (Rraise a) /\ r2 = Rerr (Rraise b)) \/
           (?a. r1 = Rerr (Rabort a) /\ r2 = Rerr (Rabort a))`,
  REPEAT GEN_TAC THEN CASES_ON `r1:(clos_v list,clos_v)result` THEN
  CASES_ON `r2:(clos_v list,clos_v)result` THEN
  REWRITE_TAC[result_rel_def; injectivity "result"; distinctness "result"] THEN
  TRY(CASES_ON `a:(clos_v)error_result` THEN CASES_ON `a':(clos_v)error_result`) THEN
  REWRITE_TAC[exc_rel_def; injectivity "error_result"; distinctness "error_result"] THEN
  MESON_TAC[]);;

let CLOSPROPSAUX_M_eq = prove
 (CASE_TERM `!r1 r2 outcome.
     result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T) r1 r2 ==>
     ((match r1 with
         Rerr (Rabort Rtimeout_error) -> F
       | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
       | _ -> outcome = Success) <=>
      (match r2 with
         Rerr (Rabort Rtimeout_error) -> F
       | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
       | _ -> outcome = Success))`,
  REWRITE_TAC[CLOSPROPSAUX_result_rel_T] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[case_def "result"; case_def "error_result"]);;

let CLOSPROPSAUX_some_SOME = prove
 (`!P (a:A). (some) P = SOME a ==> P a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]);;

let CLOSPROPSAUX_sem_fail = prove
 (`!(ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc es.
     clos_semantics ffi ma code co cc es = Fail <=>
     ?k. FST (clos_evaluate (es,[],clos_initial_state ffi ma code co cc k)) =
         Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSPROPSAUX_some_SOME) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "behaviour"]);;

let CLOSPROPSAUX_term_pred_eq = prove
 (CASE_TERM `!(E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state)
     (E2:num -> (clos_v list,clos_v)result # (B,FFI)clos_state).
     (!k. ~(FST (E1 k) = Rerr (Rabort Rtype_error))) /\
     (!k. ~(FST (E2 k) = Rerr (Rabort Rtype_error))) /\
     (!k. ?ck. result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                 (FST (E1 k)) (FST (E2 (k + ck))) /\
               clos_state_ffi (SND (E1 k)) = clos_state_ffi (SND (E2 (k + ck)))) /\
     (!k ck. ~(FST (E2 k) = Rerr (Rabort Rtimeout_error)) ==>
             FST (E2 (k + ck)) = FST (E2 k) /\
             clos_state_ffi (SND (E2 (k + ck))) = clos_state_ffi (SND (E2 k)))
     ==> !res. (?k r s outcome.
                  E2 k = (r,s) /\
                  (match r with
                     Rerr (Rabort Rtimeout_error) -> F
                   | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
                   | _ -> outcome = Success) /\
                  res = Terminate outcome (ffi_state_io_events (clos_state_ffi s))) <=>
               (?k r s outcome.
                  E1 k = (r,s) /\
                  (match r with
                     Rerr (Rabort Rtimeout_error) -> F
                   | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
                   | _ -> outcome = Success) /\
                  res = Terminate outcome (ffi_state_io_events (clos_state_ffi s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [(DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s:(B,FFI)clos_state`
        (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
    MP_TAC(ISPEC `(E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k`
                 PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s1:(A,FFI)clos_state` ASSUME_TAC)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
      check (fun th -> is_exists (snd (dest_forall (concl th)))))) THEN
    (SUBGOAL_THEN `~(r = Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"; case_def "error_result";
                                case_def "abort"]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `ck:num`] o
    check (fun th -> is_imp (snd (strip_forall (concl th))))) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T) r1 r /\
                clos_state_ffi (s1:(A,FFI)clos_state) = clos_state_ffi (s:(B,FFI)clos_state)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                   (FST ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k))
                   (FST ((E2:num -> (clos_v list,clos_v)result # (B,FFI)clos_state) (k + ck)))` THEN
    UNDISCH_TAC `clos_state_ffi (SND ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k)) =
                 clos_state_ffi (SND ((E2:num -> (clos_v list,clos_v)result # (B,FFI)clos_state) (k + ck)))` THEN
    ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `r1:(clos_v list,clos_v)result`; `s1:(A,FFI)clos_state`;
                        `outcome:outcome`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`r1:(clos_v list,clos_v)result`; `r:(clos_v list,clos_v)result`;
                `outcome:outcome`] CLOSPROPSAUX_M_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]);
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s:(A,FFI)clos_state`
        (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
    check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
  MP_TAC(ISPEC `(E2:num -> (clos_v list,clos_v)result # (B,FFI)clos_state) (k + ck)`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(B,FFI)clos_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T) r r2 /\
                clos_state_ffi (s:(A,FFI)clos_state) = clos_state_ffi (s2:(B,FFI)clos_state)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                   (FST ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k))
                   (FST ((E2:num -> (clos_v list,clos_v)result # (B,FFI)clos_state) (k + ck)))` THEN
    UNDISCH_TAC `clos_state_ffi (SND ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k)) =
                 clos_state_ffi (SND ((E2:num -> (clos_v list,clos_v)result # (B,FFI)clos_state) (k + ck)))` THEN
    ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k + ck:num`; `r2:(clos_v list,clos_v)result`; `s2:(B,FFI)clos_state`;
                        `outcome:outcome`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`r:(clos_v list,clos_v)result`; `r2:(clos_v list,clos_v)result`;
                `outcome:outcome`] CLOSPROPSAUX_M_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]]);;

let CLOSPROPSAUX_sem_eq = prove
 (`!(ffi:(FFI)ffi_state) max_app code1 (co1:num -> A # clos_prog) cc1 es1
     code2 (co2:num -> B # clos_prog) cc2 es2.
     (!k. ~(FST (clos_evaluate (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k)) =
            Rerr (Rabort Rtype_error))) /\
     (!k. ?ck. result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                 (FST (clos_evaluate (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k)))
                 (FST (clos_evaluate (es2,[],clos_initial_state ffi max_app code2 co2 cc2
                                                (k + ck)))) /\
               clos_state_ffi (SND (clos_evaluate
                 (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k))) =
               clos_state_ffi (SND (clos_evaluate
                 (es2,[],clos_initial_state ffi max_app code2 co2 cc2 (k + ck)))))
     ==> clos_semantics ffi max_app code2 co2 cc2 es2 =
         clos_semantics ffi max_app code1 co1 cc1 es1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. ~(FST (clos_evaluate (es2,[],clos_initial_state (ffi:(FFI)ffi_state)
                         max_app code2 (co2:num -> B # clos_prog) cc2 k)) =
                      Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `k:num`) THEN
    MP_TAC(ISPECL [`es2:clos_exp list`; `[]:clos_v list`; `ffi:(FFI)ffi_state`; `max_app:num`;
                  `code2:(num,num#clos_exp)fmap`; `co2:num -> B # clos_prog`;
                  `cc2:B -> clos_prog -> (byte list # int64 list # B) option`;
                  `k:num`; `ck:num`] CLOSPROPSAUX_init_add) THEN
    ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result"; distinctness "abort"] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    ASM_REWRITE_TAC[CLOSPROPSAUX_result_rel_T; distinctness "result";
                    injectivity "result"; distinctness "error_result";
                    injectivity "error_result"] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state)
                         max_app code1 (co1:num -> A # clos_prog) cc1 k)`;
                 `\k. clos_evaluate (es2,[],clos_initial_state (ffi:(FFI)ffi_state)
                         max_app code2 (co2:num -> B # clos_prog) cc2 k)`]
                CLOSPROPSAUX_term_pred_eq) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CLOSPROPSAUX_init_add]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\k. ffi_state_io_events (clos_state_ffi (SND (clos_evaluate
                         (es2,[],clos_initial_state (ffi:(FFI)ffi_state)
                            max_app code2 (co2:num -> B # clos_prog) cc2 k))))`;
                 `\k. ffi_state_io_events (clos_state_ffi (SND (clos_evaluate
                         (es1,[],clos_initial_state (ffi:(FFI)ffi_state)
                            max_app code1 (co1:num -> A # clos_prog) cc1 k))))`]
                CLOSPROPSAUX_lub_eq) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CLOSPROPSAUX_init_mono] THEN CONJ_TAC THEN X_GEN_TAC `k:num` THENL
     [EXISTS_TAC `k:num` THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
        check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSPROPSAUX_init_mono THEN ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
        check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
      EXISTS_TAC `k + ck:num` THEN ASM_REWRITE_TAC[IS_PREFIX_REFL]];
    DISCH_TAC] THEN
  REWRITE_TAC[clos_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM]);;

(* HOL4: IMP_semantics_eq *)
let clos_IMP_semantics_eq = prove
 (`!(ffi:(FFI)ffi_state) max_app code1 (co1:num -> A # clos_prog) cc1 es1
     code2 (co2:num -> B # clos_prog) cc2 es2 rel.
     clos_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2 rel F /\
     ~(clos_semantics ffi max_app code1 co1 cc1 es1 = Fail) ==>
     rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
     clos_semantics ffi max_app code2 co2 cc2 es2 =
     clos_semantics ffi max_app code1 co1 cc1 es1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_eval_sim_def; CLOSPROPSAUX_sem_fail; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CLOSPROPSAUX_sem_eq THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state) max_app code1
                                (co1:num -> A # clos_prog) cc1 k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(A,FFI)clos_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `r1:(clos_v list,clos_v)result`;
                                `s1:(A,FFI)clos_state`] o
    check (fun th -> is_imp (snd (strip_forall (concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[FST; SND]);;

(* HOL4: IMP_semantics_eq_no_fail *)
let IMP_semantics_eq_no_fail = prove
 (`!(ffi:(FFI)ffi_state) max_app code1 (co1:num -> A # clos_prog) cc1 es1
     code2 (co2:num -> B # clos_prog) cc2 es2 rel.
     clos_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2 rel T ==>
     rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
     clos_semantics ffi max_app code2 co2 cc2 es2 =
     clos_semantics ffi max_app code1 co1 cc1 es1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_eval_sim_def] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. ?ck. result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
               (FST (clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state) max_app
                                             code1 (co1:num -> A # clos_prog) cc1 k)))
               (FST (clos_evaluate (es2,[],clos_initial_state ffi max_app code2
                                             (co2:num -> B # clos_prog) cc2 (k + ck)))) /\
             clos_state_ffi (SND (clos_evaluate
               (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k))) =
             clos_state_ffi (SND (clos_evaluate
               (es2,[],clos_initial_state ffi max_app code2 co2 cc2 (k + ck))))`
    ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state) max_app code1
                                  (co1:num -> A # clos_prog) cc1 k)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s1:(A,FFI)clos_state` ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `r1:(clos_v list,clos_v)result`;
                                  `s1:(A,FFI)clos_state`] o
      check (fun th -> is_imp (snd (strip_forall (concl th))))) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    STRIP_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  ASM_CASES_TAC `?k. FST (clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state)
                     max_app code1 (co1:num -> A # clos_prog) cc1 k)) =
                     Rerr (Rabort Rtype_error)` THENL
   [SUBGOAL_THEN `clos_semantics (ffi:(FFI)ffi_state) max_app code1 (co1:num -> A # clos_prog) cc1 es1 = Fail /\
                  clos_semantics ffi max_app code2 (co2:num -> B # clos_prog) cc2 es2 = Fail`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[CLOSPROPSAUX_sem_fail] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:num`) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[CLOSPROPSAUX_result_rel_T; distinctness "result"; injectivity "result";
                    distinctness "error_result"; injectivity "error_result"] THEN
    MESON_TAC[];
    MATCH_MP_TAC CLOSPROPSAUX_sem_eq THEN ASM_MESON_TAC[]]);;

(* HOL4: adj_orac_rel_def *)
let clos_adj_orac_rel_def = cake_def
  `clos_adj_orac_rel (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
      (s1:(A,FFI)clos_state) (s2:(B,FFI)clos_state) <=>
     (!n x y. clos_state_compile_oracle s1 n = (x,y) ==>
              OPTION_MAP (I ## (I ## f)) (clos_state_compile s1 x y) = cc (f x) y) /\
     s2 = clos_state_REC (clos_state_globals s1) (clos_state_refs s1) (clos_state_ffi s1)
            (clos_state_clock s1) cc ((f ## I) o clos_state_compile_oracle s1)
            (clos_state_code s1) (clos_state_max_app s1)`;;

(* HOL4: do_install_adj_orac *)
let clos_do_install_adj_orac = prove
 (`!xs (z1:(A,FFI)clos_state) (z2:(B,FFI)clos_state) r s1 cc f.
     clos_do_install xs z1 = (r,s1) /\ clos_adj_orac_rel cc f z1 z2 /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?s2. clos_do_install xs z2 = (r,s2) /\ clos_adj_orac_rel cc f s1 s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_adj_orac_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) MP_TAC)) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES]) THEN
  FIRST_ASSUM(fun hyp -> if is_forall (concl hyp) then
    FIRST_ASSUM(fun fact -> MP_TAC (MATCH_MP hyp fact)) else NO_TAC) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  REWRITE_TAC[clos_do_install_def; LET_DEF; LET_END_DEF; clos_state_INFO.ri_accessors; o_THM;
              PAIR_MAP; shift_seq_def; ADD_CLAUSES; clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[FST; SND; I_THM] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_accfupds; K_THM; FUN_EQ_THM; o_THM; PAIR_MAP; I_THM]);;

(* HOL4 [local] (HOL4 leaves cc and f free) *)
let do_app_lemma_simp = prove
 (`(!err1 err2:(clos_v)error_result. exc_rel (=) err1 err2 <=> err1 = err2) /\
   (!xs:clos_v list. ALL2 (=) xs xs) /\
   clos_simple_state_rel (=)
     (clos_adj_orac_rel (cc:B -> clos_prog -> (byte list # int64 list # B) option)
                        (f:A->B) : (A,FFI)clos_state -> (B,FFI)clos_state -> bool) /\
   clos_simple_val_rel (=)`,
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CASES_ON `err1:(clos_v)error_result` THEN
    CASES_ON `err2:(clos_v)error_result` THEN
    REWRITE_TAC[exc_rel_def; distinctness "error_result"; injectivity "error_result"];
    REWRITE_TAC[LIST_REL_eq];
    REWRITE_TAC[clos_simple_state_rel_def; clos_adj_orac_rel_def; LIST_REL_eq; OPTREL_eq] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_state_INFO.ri_accessors]) THEN
    ASM_REWRITE_TAC[clos_state_INFO.ri_accessors; clos_state_INFO.ri_accfupds; K_THM;
                    clos_state_component_equality; injectivity "option"; injectivity "clos_ref";
                    UNWIND_THM1; UNWIND_THM2];
    REWRITE_TAC[clos_simple_val_rel_def; LIST_REL_eq] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_isClos_def] THEN MESON_TAC[]]);;

(* HOL4: val do_app_lemma (the instance of simple_val_rel_do_app) *)
let CLOSPROPSAUX_do_app_lemma_adj = prove
 (CASE_TERM `!op xs (s1:(A,FFI)clos_state) (s2:(B,FFI)clos_state)
     (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A->B).
     clos_adj_orac_rel cc f s1 s2 ==>
     match clos_do_app op xs s1 with
       Rerr err1 -> clos_do_app op xs s2 = Rerr err1
     | Rval (x,z1) -> ?z2. clos_adj_orac_rel cc f z1 z2 /\ clos_do_app op xs s2 = Rval (x,z2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(=):clos_v->clos_v->bool`;
                 `clos_adj_orac_rel (cc:B -> clos_prog -> (byte list # int64 list # B) option)
                                    (f:A->B) : (A,FFI)clos_state -> (B,FFI)clos_state -> bool`;
                 `s1:(A,FFI)clos_state`; `s2:(B,FFI)clos_state`; `xs:clos_v list`;
                 `xs:clos_v list`; `op:clos_op`] simple_val_rel_do_app) THEN
  ASM_REWRITE_TAC[do_app_lemma_simp] THEN
  CASES_ON `clos_do_app op xs (s1:(A,FFI)clos_state)` THEN
  REWRITE_TAC[case_def "result"] THEN TRY(CASES_ON `a:clos_v#(A,FFI)clos_state`) THEN
  REWRITE_TAC[case_def "prod"] THEN MESON_TAC[]);;

(* HOL4: do_app_adj_orac_Rerr (HOL4 leaves cc and f free) *)
let do_app_adj_orac_Rerr = prove
 (`!op xs (s1:(A,FFI)clos_state) (s2:(B,FFI)clos_state) r
     (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A->B).
     clos_do_app op xs s1 = Rerr r /\ clos_adj_orac_rel cc f s1 s2 ==>
     clos_do_app op xs s2 = Rerr r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`op:clos_op`; `xs:clos_v list`] o
                MATCH_MP CLOSPROPSAUX_do_app_lemma_adj) THEN
  ASM_REWRITE_TAC[case_def "result"]);;

(* HOL4: do_app_adj_orac_Rval (HOL4 leaves cc and f free) *)
let do_app_adj_orac_Rval = prove
 (`!op xs (s1:(A,FFI)clos_state) (s2:(B,FFI)clos_state) r z1
     (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A->B).
     clos_do_app op xs s1 = Rval (r,z1) /\ clos_adj_orac_rel cc f s1 s2 ==>
     ?z2. clos_do_app op xs s2 = Rval (r,z2) /\ clos_adj_orac_rel cc f z1 z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`op:clos_op`; `xs:clos_v list`] o
                MATCH_MP CLOSPROPSAUX_do_app_lemma_adj) THEN
  ASM_REWRITE_TAC[case_def "result"; case_def "prod"] THEN MESON_TAC[]);;

(* local helpers for evaluate_adj_orac: the related state is a function of *)
(* the state (CLOSPROPSAUX_adj), under a condition on the oracle           *)
let CLOSPROPSAUX_adj_def = new_definition
 `CLOSPROPSAUX_adj (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (s:(A,FFI)clos_state) =
   clos_state_REC (clos_state_globals s) (clos_state_refs s) (clos_state_ffi s)
     (clos_state_clock s) cc ((f ## I) o clos_state_compile_oracle s)
     (clos_state_code s) (clos_state_max_app s)`;;

let CLOSPROPSAUX_orac_ok_def = new_definition
 `CLOSPROPSAUX_orac_ok (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (s:(A,FFI)clos_state) <=>
   !n x y. clos_state_compile_oracle s n = (x,y) ==>
           OPTION_MAP (I ## (I ## f)) (clos_state_compile s x y) = cc (f x) y`;;

let CLOSPROPSAUX_adj_orac_rel_alt = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (s1:(A,FFI)clos_state) s2.
     clos_adj_orac_rel cc f s1 s2 <=>
     CLOSPROPSAUX_orac_ok cc f s1 /\ s2 = CLOSPROPSAUX_adj cc f s1`,
  REWRITE_TAC[clos_adj_orac_rel_def; CLOSPROPSAUX_orac_ok_def; CLOSPROPSAUX_adj_def]);;

let CLOSPROPSAUX_adj_acc = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (s:(A,FFI)clos_state).
     clos_state_globals (CLOSPROPSAUX_adj cc f s) = clos_state_globals s /\
     clos_state_refs (CLOSPROPSAUX_adj cc f s) = clos_state_refs s /\
     clos_state_ffi (CLOSPROPSAUX_adj cc f s) = clos_state_ffi s /\
     clos_state_clock (CLOSPROPSAUX_adj cc f s) = clos_state_clock s /\
     clos_state_code (CLOSPROPSAUX_adj cc f s) = clos_state_code s /\
     clos_state_max_app (CLOSPROPSAUX_adj cc f s) = clos_state_max_app s`,
  REWRITE_TAC[CLOSPROPSAUX_adj_def; clos_state_INFO.ri_accessors]);;

let CLOSPROPSAUX_adj_clock = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (s:(A,FFI)clos_state) k.
     clos_state_clock_fupd (K k) (CLOSPROPSAUX_adj cc f s) =
     CLOSPROPSAUX_adj cc f (clos_state_clock_fupd (K k) s) /\
     clos_dec_clock k (CLOSPROPSAUX_adj cc f s) =
     CLOSPROPSAUX_adj cc f (clos_dec_clock k s) /\
     (CLOSPROPSAUX_orac_ok cc f (clos_state_clock_fupd (K k) s) <=>
      CLOSPROPSAUX_orac_ok cc f s) /\
     (CLOSPROPSAUX_orac_ok cc f (clos_dec_clock k s) <=> CLOSPROPSAUX_orac_ok cc f s)`,
  REWRITE_TAC[CLOSPROPSAUX_adj_def; CLOSPROPSAUX_orac_ok_def; clos_dec_clock_def;
              clos_state_component_equality; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_do_app_adj = prove
 (`!op xs (s:(A,FFI)clos_state)
     (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B).
     CLOSPROPSAUX_orac_ok cc f s ==>
     (!v s1. clos_do_app op xs s = Rval (v,s1) ==>
             clos_do_app op xs (CLOSPROPSAUX_adj cc f s) = Rval (v,CLOSPROPSAUX_adj cc f s1) /\
             CLOSPROPSAUX_orac_ok cc f s1) /\
     (!e. clos_do_app op xs s = Rerr e ==> clos_do_app op xs (CLOSPROPSAUX_adj cc f s) = Rerr e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`op:clos_op`; `xs:clos_v list`; `s:(A,FFI)clos_state`;
                   `CLOSPROPSAUX_adj (cc:B -> clos_prog -> (byte list # int64 list # B) option)
                                     (f:A -> B) (s:(A,FFI)clos_state)`;
                   `v:clos_v`; `s1:(A,FFI)clos_state`; `cc:B -> clos_prog -> (byte list # int64 list # B) option`;
                   `f:A -> B`] do_app_adj_orac_Rval);
    MP_TAC(ISPECL [`op:clos_op`; `xs:clos_v list`; `s:(A,FFI)clos_state`;
                   `CLOSPROPSAUX_adj (cc:B -> clos_prog -> (byte list # int64 list # B) option)
                                     (f:A -> B) (s:(A,FFI)clos_state)`;
                   `e:(clos_v)error_result`; `cc:B -> clos_prog -> (byte list # int64 list # B) option`;
                   `f:A -> B`] do_app_adj_orac_Rerr)] THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_adj_orac_rel_alt] THEN MESON_TAC[]);;

let CLOSPROPSAUX_do_install_adj = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     xs (s:(A,FFI)clos_state) r s1.
     CLOSPROPSAUX_orac_ok cc f s /\ clos_do_install xs s = (r,s1) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     clos_do_install xs (CLOSPROPSAUX_adj cc f s) = (r,CLOSPROPSAUX_adj cc f s1) /\
     CLOSPROPSAUX_orac_ok cc f s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_v list`; `s:(A,FFI)clos_state`;
                 `CLOSPROPSAUX_adj (cc:B -> clos_prog -> (byte list # int64 list # B) option)
                                   (f:A -> B) (s:(A,FFI)clos_state)`;
                 `r:(clos_exp list,clos_v)result`; `s1:(A,FFI)clos_state`;
                 `cc:B -> clos_prog -> (byte list # int64 list # B) option`; `f:A -> B`]
                clos_do_install_adj_orac) THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_adj_orac_rel_alt] THEN MESON_TAC[]);;

let CLOSPROPSAUX_do_app_adj_Rval = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     op xs (s:(A,FFI)clos_state) v s1.
     CLOSPROPSAUX_orac_ok cc f s /\ clos_do_app op xs s = Rval (v,s1) ==>
     clos_do_app op xs (CLOSPROPSAUX_adj cc f s) = Rval (v,CLOSPROPSAUX_adj cc f s1) /\
     CLOSPROPSAUX_orac_ok cc f s1`,
  MESON_TAC[CLOSPROPSAUX_do_app_adj]);;

let CLOSPROPSAUX_do_app_adj_Rerr = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     op xs (s:(A,FFI)clos_state) e.
     CLOSPROPSAUX_orac_ok cc f s /\ clos_do_app op xs s = Rerr e ==>
     clos_do_app op xs (CLOSPROPSAUX_adj cc f s) = Rerr e`,
  MESON_TAC[CLOSPROPSAUX_do_app_adj]);;

let CLOSPROPSAUX_adj_refs = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (s:(A,FFI)clos_state) r.
     clos_state_refs_fupd (K r) (CLOSPROPSAUX_adj cc f s) =
     CLOSPROPSAUX_adj cc f (clos_state_refs_fupd (K r) s) /\
     (CLOSPROPSAUX_orac_ok cc f (clos_state_refs_fupd (K r) s) <=>
      CLOSPROPSAUX_orac_ok cc f s)`,
  REWRITE_TAC[CLOSPROPSAUX_adj_def; CLOSPROPSAUX_orac_ok_def;
              clos_state_component_equality; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_adj_simps =
  [CLOSPROPSAUX_adj_acc; CLOSPROPSAUX_adj_clock; CLOSPROPSAUX_adj_refs; map_result_def;
   map_error_result_I; I_THM];;

(* a resolution tactic as CLOSPROPSAUX_RES_TAC, with alpha-equivalent results *)
(* counted as duplicates *)
let CLOSPROPSAUX_RES2_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results =
    flat (map (fun th -> let th' = curry th in
                 flat (map (resolve 4) (mapfilter (fun a -> MATCH_MP th' a) asms)))
              imps) in
  let results = map (REWRITE_RULE CLOSPROPSAUX_eval_simps) results in
  let known th l = forall (fun c -> exists (fun a -> aconv (concl a) c) l)
                          (conjuncts (concl th)) in
  let rec dedup acc l = match l with
      [] -> rev acc
    | th::t -> if known th (asms @ acc) then dedup acc t else dedup (th::acc) t in
  EVERY (map CAKE_ASSUME_TAC (dedup [] results)) gl;;

let CLOSPROPSAUX_ADJ_TAC : tactic =
  REPEAT STRIP_TAC THEN
  CLOSPROPSAUX_SPLIT_ASM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSPROPSAUX_adj_clock; CLOSPROPSAUX_adj_refs]) THEN
  MAP_EVERY (fun th -> ASSUME_TAC (ISPECL [`cc:B -> clos_prog -> (byte list # int64 list # B) option`;
                                           `f:A -> B`] th))
    [CLOSPROPSAUX_do_app_adj_Rval; CLOSPROPSAUX_do_app_adj_Rerr; CLOSPROPSAUX_do_install_adj] THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REPEAT(CHANGED_TAC(ASM_SIMP_TAC (CLOSPROPSAUX_adj_simps @ CLOSPROPSAUX_case_defs)));;

(* local helper: evaluate on the related state (a function of the state) *)
let CLOSPROPSAUX_evaluate_adj = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B).
   (!xs env (s:(A,FFI)clos_state) r s'.
      clos_evaluate (xs,env,s) = (r,s') /\ ~(r = Rerr (Rabort Rtype_error)) /\
      CLOSPROPSAUX_orac_ok cc f s ==>
      clos_evaluate (xs,env,CLOSPROPSAUX_adj cc f s) = (r,CLOSPROPSAUX_adj cc f s') /\
      CLOSPROPSAUX_orac_ok cc f s') /\
   (!loc_opt v rest_args (s:(A,FFI)clos_state) r s'.
      evaluate_app loc_opt v rest_args s = (r,s') /\ ~(r = Rerr (Rabort Rtype_error)) /\
      CLOSPROPSAUX_orac_ok cc f s ==>
      evaluate_app loc_opt v rest_args (CLOSPROPSAUX_adj cc f s) = (r,CLOSPROPSAUX_adj cc f s') /\
      CLOSPROPSAUX_orac_ok cc f s')`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  CLOSPROPSAUX_ADJ_TAC);;

(* HOL4: evaluate_adj_orac (HOL4 leaves cc and f free) *)
let clos_evaluate_adj_orac = prove
 (`(!p (z1:(A,FFI)clos_state) r s1 (s2:(B,FFI)clos_state) (z2:(B,FFI)clos_state)
      (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B).
      clos_evaluate p = (r,s1) /\ SND (SND p) = z1 /\ ~(r = Rerr (Rabort Rtype_error)) /\
      clos_adj_orac_rel cc f z1 z2 ==>
      ?s2. clos_evaluate (FST p,FST (SND p),z2) = (r,s2) /\ clos_adj_orac_rel cc f s1 s2) /\
   (!w x y (z1:(A,FFI)clos_state) r s1 (s2:(B,FFI)clos_state) (z2:(B,FFI)clos_state)
      (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B).
      evaluate_app w x y z1 = (r,s1) /\ ~(r = Rerr (Rabort Rtype_error)) /\
      clos_adj_orac_rel cc f z1 z2 ==>
      ?s2. evaluate_app w x y z2 = (r,s2) /\ clos_adj_orac_rel cc f s1 s2)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; CLOSPROPSAUX_adj_orac_rel_alt] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `CLOSPROPSAUX_adj (cc:B -> clos_prog -> (byte list # int64 list # B) option)
                (f:A -> B) (s1:(A,FFI)clos_state)` THEN
  ASM_MESON_TAC[CLOSPROPSAUX_evaluate_adj]);;

let CLOSPROPSAUX_result_rel_T_refl = prove
 (`!r. result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T) r r`,
  REWRITE_TAC[CLOSPROPSAUX_result_rel_T] THEN GEN_TAC THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
  TRY(CASES_ON `a:(clos_v)error_result`) THEN
  REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN MESON_TAC[]);;

let CLOSPROPSAUX_adj_initial_state = prove
 (`!(cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
     (ffi:(FFI)ffi_state) ma code (co:num -> A # clos_prog) cc_x k.
     CLOSPROPSAUX_adj cc f (clos_initial_state ffi ma code co cc_x k) =
     clos_initial_state ffi ma code ((f ## I) o co) cc k /\
     (CLOSPROPSAUX_orac_ok cc f (clos_initial_state ffi ma code co cc_x k) <=>
      !n x y. co n = (x,y) ==> OPTION_MAP (I ## (I ## f)) (cc_x x y) = cc (f x) y)`,
  REWRITE_TAC[CLOSPROPSAUX_adj_def; CLOSPROPSAUX_orac_ok_def; clos_initial_state_def;
              clos_state_INFO.ri_accessors]);;

(* HOL4: semantics_adj_orac *)
let semantics_adj_orac = prove
 (`!(ffi:(FFI)ffi_state) max_app code (co:num -> A # clos_prog)
     (cc_x:A -> clos_prog -> (byte list # int64 list # A) option) es
     (co_x:num -> B # clos_prog) (f:A -> B)
     (cc:B -> clos_prog -> (byte list # int64 list # B) option).
     ~(clos_semantics ffi max_app code co cc_x es = Fail) /\
     co_x = (f ## I) o co /\
     (!n x y. co n = (x,y) ==> cc (f x) y = OPTION_MAP (I ## (I ## f)) (cc_x x y)) ==>
     clos_semantics ffi max_app code co_x cc es = clos_semantics ffi max_app code co cc_x es`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] clos_IMP_semantics_eq) THEN
  EXISTS_TAC `\(a:(num,num#clos_exp)fmap) (b:num -> A # clos_prog)
                (c:A -> clos_prog -> (byte list # int64 list # A) option) (d:clos_exp list)
                (a':(num,num#clos_exp)fmap) (b':num -> B # clos_prog)
                (c':B -> clos_prog -> (byte list # int64 list # B) option) (d':clos_exp list). T` THEN
  ASM_REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`cc:B -> clos_prog -> (byte list # int64 list # B) option`; `f:A -> B`]
                CLOSPROPSAUX_evaluate_adj) THEN
  DISCH_THEN(MP_TAC o SPECL [`es:clos_exp list`; `[]:clos_v list`;
    `clos_initial_state (ffi:(FFI)ffi_state) max_app code (co:num -> A # clos_prog) cc_x k`;
    `res1:(clos_v list,clos_v)result`; `s2:(A,FFI)clos_state`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_adj_initial_state] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`res1:(clos_v list,clos_v)result`;
    `CLOSPROPSAUX_adj (cc:B -> clos_prog -> (byte list # int64 list # B) option) (f:A -> B)
                      (s2:(A,FFI)clos_state)`] THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_adj_acc; CLOSPROPSAUX_result_rel_T_refl]);;

let semantics_CURRY_I_gen = prove
 (`!(ffi:(FFI)ffi_state) max_app code (co:num -> (S#C) # clos_prog)
     (cc_x:S#C -> clos_prog -> (byte list # int64 list # S # C) option)
     (cc:C -> clos_prog -> (byte list # int64 list # C) option) es.
     (!n x y. co n = (x,y) ==> cc_x x y = state_cc (CURRY I) cc x y) ==>
     ~(clos_semantics ffi max_app code co cc_x es = Fail) ==>
     clos_semantics ffi max_app code (state_co (CURRY I) co) cc es =
     clos_semantics ffi max_app code co cc_x es`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC semantics_adj_orac THEN EXISTS_TAC `SND:S#C->C` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; state_co_def; PAIR_MAP] THEN GEN_TAC THEN
    MP_TAC(ISPEC `(co:num -> (S#C) # clos_prog) x` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:S#C` (X_CHOOSE_THEN `p:clos_prog` SUBST1_TAC)) THEN
    MP_TAC(ISPEC `a:S#C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `st:S` (X_CHOOSE_THEN `cfg:C` SUBST1_TAC)) THEN
    REWRITE_TAC[pair_CASE; CURRY_DEF; I_THM; FST; SND];
    REPEAT STRIP_TAC THEN CLOSPROPSAUX_RES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:S#C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `st:S` (X_CHOOSE_THEN `cfg:C` SUBST1_TAC)) THEN
    REWRITE_TAC[state_cc_def; pair_CASE; CURRY_DEF; I_THM; FST; SND] THEN
    CASES_ON `(cc:C -> clos_prog -> (byte list # int64 list # C) option) cfg y` THEN
    REWRITE_TAC[case_def "option"; OPTION_MAP_DEF] THEN
    MP_TAC(ISPEC `a:byte list # int64 list # C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:byte list` (X_CHOOSE_THEN `c2:int64 list # C` SUBST1_TAC)) THEN
    MP_TAC(ISPEC `c2:int64 list # C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c3:int64 list` (X_CHOOSE_THEN `c4:C` SUBST1_TAC)) THEN
    REWRITE_TAC[pair_CASE; PAIR_MAP_THM; I_THM; FST; SND; OPTION_MAP_DEF]]);;

(* HOL4: semantics_CURRY_I *)
let clos_semantics_CURRY_I = prove
 (`!(ffi:(FFI)ffi_state) max_app code (co:num -> (S#C) # clos_prog)
     (cc:C -> clos_prog -> (byte list # int64 list # C) option) es.
     ~(clos_semantics ffi max_app code co (state_cc (CURRY I) cc) es = Fail) ==>
     clos_semantics ffi max_app code (state_co (CURRY I) co) cc es =
     clos_semantics ffi max_app code co (state_cc (CURRY I) cc) es`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] semantics_CURRY_I_gen) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: semantics_nil [simp] *)
let semantics_nil = prove
 (`!(ffi:(FFI)ffi_state) maxapp code (co:num -> C # clos_prog) cc.
     clos_semantics ffi maxapp code co cc [] = Terminate Success (ffi_state_io_events ffi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_semantics_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[FST; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNWIND_THM2;
              case_def "result"; clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
  REWRITE_TAC[some_EQ; case_def "option"]);;
let _ = cake_add_simps [semantics_nil];;

(* HOL4: find_code_SUBMAP *)
let find_code_SUBMAP = prove
 (`!(dest:A) (vs:B list) (code1:(A,num#C)fmap) code2 p.
     clos_find_code dest vs code1 = SOME p /\ code1 SUBMAP code2 ==>
     clos_find_code dest vs code2 = SOME p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_find_code_def] THEN
  CASES_ON `FLOOKUP (code1:(A,num#C)fmap) dest` THEN
  REWRITE_TAC[case_def "option"; distinctness "option"] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (code2:(A,num#C)fmap) dest = SOME a` SUBST1_TAC THENL
   [ASM_MESON_TAC[FLOOKUP_SUBMAP]; ASM_REWRITE_TAC[case_def "option"]]);;

(* HOL4: SUBMAP_rel_def *)
let SUBMAP_rel_def = cake_def
  `SUBMAP_rel (z1:(C,FFI)clos_state) (z2:(C,FFI)clos_state) <=>
     z2 = clos_state_code_fupd (K (clos_state_code z2)) z1 /\
     clos_state_code z1 SUBMAP clos_state_code z2 /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (FDOM (clos_state_code z2))
       (clos_state_compile_oracle z1)`;;

(* HOL4: find_code_SUBMAP_rel *)
let find_code_SUBMAP_rel = prove
 (`!dest (vs:B list) (s1:(C,FFI)clos_state) s2 p.
     clos_find_code dest vs (clos_state_code s1) = SOME p /\ SUBMAP_rel s1 s2 ==>
     clos_find_code dest vs (clos_state_code s2) = SOME p`,
  REWRITE_TAC[SUBMAP_rel_def] THEN MESON_TAC[find_code_SUBMAP]);;

(* HOL4: SUBMAP_rel_EX *)
let SUBMAP_rel_EX = prove
 (`!(z1:(C,FFI)clos_state) z2.
     SUBMAP_rel z1 z2 ==>
     ?code. z2 = clos_state_code_fupd (K code) z1 /\ clos_state_code z1 SUBMAP code`,
  REWRITE_TAC[SUBMAP_rel_def] THEN MESON_TAC[]);;

(* a local helper for do_install_SUBMAP: the oracle stays monotonic after an *)
(* installation                                                              *)
let CLOSPROPSAUX_orac_mono_install = prove
 (`!(co:num -> C # clos_prog) (c:(num,num#clos_exp)fmap) cfg exps aux.
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (FDOM c) co /\
     co 0 = (cfg,exps,aux) ==>
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (FDOM (c |++ aux))
       (shift_seq 1 co)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL oracle_monotonic_shift_seq) THEN
  EXISTS_TAC `FDOM (c:(num,num#clos_exp)fmap)` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[FDOM_FUPDATE_LIST; o_THM; FST; SND] THEN
  SET_TAC[]);;

(* HOL4: do_install_SUBMAP *)
let do_install_SUBMAP = prove
 (`!xs (z1:(C,FFI)clos_state) z2 r s1.
     clos_do_install xs z1 = (r,s1) /\ ~(r = Rerr (Rabort Rtype_error)) /\
     SUBMAP_rel z1 z2 ==>
     ?s2. clos_do_install xs z2 = (r,s2) /\ SUBMAP_rel s1 s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:(num,num#clos_exp)fmap` (SUBST_ALL_TAC o CONJUNCT1) o
              MATCH_MP SUBMAP_rel_EX) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBMAP_rel_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o
              MATCH_MP (REWRITE_RULE[IMP_CONJ] oracle_monotonic_DISJOINT_init)) THEN
  REWRITE_TAC[irreflexive_def; LT_REFL; o_THM] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  REWRITE_TAC[clos_do_install_def; LET_DEF; LET_END_DEF; clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[UNWIND_THM1; SUBMAP_rel_def] THEN
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SUBMAP_mono_FUPDATE_LIST THEN MATCH_MP_TAC SUBMAP_DRESTRICT_MONOTONE THEN
     ASM_REWRITE_TAC[SUBSET_REFL];
     MATCH_MP_TAC CLOSPROPSAUX_orac_mono_install THEN ASM_MESON_TAC[]]));;

(* a local helper: SUBMAP_rel with the code of the second state named *)
let CLOSPROPSAUX_SUBMAP_rel_alt = prove
 (`!(z1:(C,FFI)clos_state) z2.
     SUBMAP_rel z1 z2 <=>
     ?c. z2 = clos_state_code_fupd (K c) z1 /\ clos_state_code z1 SUBMAP c /\
         oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (FDOM c)
           (clos_state_compile_oracle z1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBMAP_rel_def] THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `clos_state_code (z2:(C,FFI)clos_state)` THEN ASM_MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]]);;

(* HOL4: do_app_lemma_simp [local] (a second theorem of that name in HOL4) *)
let CLOSPROPSAUX_do_app_lemma_simp2 = prove
 (`(!err1 err2:(clos_v)error_result. exc_rel (=) err1 err2 <=> err1 = err2) /\
   (!xs:clos_v list. ALL2 (=) xs xs) /\
   clos_simple_state_rel (=) (SUBMAP_rel:(C,FFI)clos_state -> (C,FFI)clos_state -> bool) /\
   clos_simple_val_rel (=)`,
  REWRITE_TAC[do_app_lemma_simp] THEN
  REWRITE_TAC[clos_simple_state_rel_def; CLOSPROPSAUX_SUBMAP_rel_alt; LIST_REL_eq; OPTREL_eq] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; injectivity "option";
                  injectivity "clos_ref"; UNWIND_THM1; UNWIND_THM2] THEN
  TRY(EXISTS_TAC `c:(num,num#clos_exp)fmap` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
      NO_TAC));;

(* HOL4: val do_app_lemma (the instance of simple_val_rel_do_app for SUBMAP_rel) *)
let CLOSPROPSAUX_do_app_lemma_SUBMAP = prove
 (CASE_TERM `!op xs (s1:(C,FFI)clos_state) s2.
     SUBMAP_rel s1 s2 ==>
     match clos_do_app op xs s1 with
       Rerr err1 -> clos_do_app op xs s2 = Rerr err1
     | Rval (x,z1) -> ?z2. SUBMAP_rel z1 z2 /\ clos_do_app op xs s2 = Rval (x,z2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(=):clos_v->clos_v->bool`;
                 `SUBMAP_rel:(C,FFI)clos_state -> (C,FFI)clos_state -> bool`;
                 `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `xs:clos_v list`;
                 `xs:clos_v list`; `op:clos_op`] simple_val_rel_do_app) THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_do_app_lemma_simp2] THEN
  CASES_ON `clos_do_app op xs (s1:(C,FFI)clos_state)` THEN
  REWRITE_TAC[case_def "result"] THEN TRY(CASES_ON `a:clos_v#(C,FFI)clos_state`) THEN
  REWRITE_TAC[case_def "prod"] THEN MESON_TAC[]);;

(* HOL4: do_app_SUBMAP_Rerr *)
let do_app_SUBMAP_Rerr = prove
 (`!op xs (s1:(C,FFI)clos_state) s2 r.
     clos_do_app op xs s1 = Rerr r /\ SUBMAP_rel s1 s2 ==> clos_do_app op xs s2 = Rerr r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`op:clos_op`; `xs:clos_v list`] o
                MATCH_MP CLOSPROPSAUX_do_app_lemma_SUBMAP) THEN
  ASM_REWRITE_TAC[case_def "result"]);;

(* HOL4: do_app_SUBMAP_Rval *)
let do_app_SUBMAP_Rval = prove
 (`!op xs (s1:(C,FFI)clos_state) s2 r z1.
     clos_do_app op xs s1 = Rval (r,z1) /\ SUBMAP_rel s1 s2 ==>
     ?z2. clos_do_app op xs s2 = Rval (r,z2) /\ SUBMAP_rel z1 z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`op:clos_op`; `xs:clos_v list`] o
                MATCH_MP CLOSPROPSAUX_do_app_lemma_SUBMAP) THEN
  ASM_REWRITE_TAC[case_def "result"; case_def "prod"] THEN MESON_TAC[]);;

(* HOL4: SUBMAP_refs_clocks_eqs [local] *)
let SUBMAP_refs_clocks_eqs = prove
 (`!(s1:(C,FFI)clos_state) s2.
     SUBMAP_rel s1 s2 ==>
     clos_state_refs s1 = clos_state_refs s2 /\ clos_state_clock s1 = clos_state_clock s2`,
  REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_alt] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: SUBMAP_dec_clock [local] *)
let SUBMAP_dec_clock = prove
 (`!(s1:(C,FFI)clos_state) s2.
     SUBMAP_rel s1 s2 ==> SUBMAP_rel (clos_dec_clock 1 s1) (clos_dec_clock 1 s2)`,
  REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_alt] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `c:(num,num#clos_exp)fmap` THEN
  ASM_REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM]);;

(* local helpers for evaluate_code_SUBMAP: the second state is the first   *)
(* with a bigger code c (CLOSPROPSAUX_cok c s)                             *)
let CLOSPROPSAUX_cok_def = new_definition
 `CLOSPROPSAUX_cok (c:(num,num#clos_exp)fmap) (s:(C,FFI)clos_state) <=>
    clos_state_code s SUBMAP c /\
    oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (FDOM c)
      (clos_state_compile_oracle s)`;;

let CLOSPROPSAUX_SUBMAP_rel_cok = prove
 (`!(z1:(C,FFI)clos_state) z2.
     SUBMAP_rel z1 z2 <=> ?c. z2 = clos_state_code_fupd (K c) z1 /\ CLOSPROPSAUX_cok c z1`,
  REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_alt; CLOSPROPSAUX_cok_def]);;

let CLOSPROPSAUX_code_upd = prove
 (`!(c:(num,num#clos_exp)fmap) (s:(C,FFI)clos_state) k r.
     clos_state_clock_fupd (K k) (clos_state_code_fupd (K c) s) =
     clos_state_code_fupd (K c) (clos_state_clock_fupd (K k) s) /\
     clos_dec_clock k (clos_state_code_fupd (K c) s) =
     clos_state_code_fupd (K c) (clos_dec_clock k s) /\
     clos_state_refs_fupd (K r) (clos_state_code_fupd (K c) s) =
     clos_state_code_fupd (K c) (clos_state_refs_fupd (K r) s) /\
     (CLOSPROPSAUX_cok c (clos_state_clock_fupd (K k) s) <=> CLOSPROPSAUX_cok c s) /\
     (CLOSPROPSAUX_cok c (clos_dec_clock k s) <=> CLOSPROPSAUX_cok c s) /\
     (CLOSPROPSAUX_cok c (clos_state_refs_fupd (K r) s) <=> CLOSPROPSAUX_cok c s)`,
  REWRITE_TAC[CLOSPROPSAUX_cok_def; clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSPROPSAUX_cok_find_code = prove
 (`!(c:(num,num#clos_exp)fmap) (s:(C,FFI)clos_state) dest (args:B list) p.
     CLOSPROPSAUX_cok c s /\ clos_find_code dest args (clos_state_code s) = SOME p ==>
     clos_find_code dest args c = SOME p`,
  REWRITE_TAC[CLOSPROPSAUX_cok_def] THEN MESON_TAC[find_code_SUBMAP]);;

let CLOSPROPSAUX_do_app_cok_Rval = prove
 (`!(c:(num,num#clos_exp)fmap) op xs (s:(C,FFI)clos_state) v s1.
     CLOSPROPSAUX_cok c s /\ clos_do_app op xs s = Rval (v,s1) ==>
     clos_do_app op xs (clos_state_code_fupd (K c) s) = Rval (v,clos_state_code_fupd (K c) s1) /\
     CLOSPROPSAUX_cok c s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`op:clos_op`; `xs:clos_v list`; `s:(C,FFI)clos_state`;
                 `clos_state_code_fupd (K (c:(num,num#clos_exp)fmap)) (s:(C,FFI)clos_state)`;
                 `v:clos_v`; `s1:(C,FFI)clos_state`] do_app_SUBMAP_Rval) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_cok] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_cok] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP clos_do_app_const) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let CLOSPROPSAUX_do_app_cok_Rerr = prove
 (`!(c:(num,num#clos_exp)fmap) op xs (s:(C,FFI)clos_state) e.
     CLOSPROPSAUX_cok c s /\ clos_do_app op xs s = Rerr e ==>
     clos_do_app op xs (clos_state_code_fupd (K c) s) = Rerr e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC do_app_SUBMAP_Rerr THEN
  EXISTS_TAC `s:(C,FFI)clos_state` THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_cok] THEN ASM_MESON_TAC[]);;

let CLOSPROPSAUX_do_install_cok = prove
 (`!(c:(num,num#clos_exp)fmap) xs (s:(C,FFI)clos_state) r s1.
     CLOSPROPSAUX_cok c s /\ clos_do_install xs s = (r,s1) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?c'. clos_do_install xs (clos_state_code_fupd (K c) s) = (r,clos_state_code_fupd (K c') s1) /\
          CLOSPROPSAUX_cok c' s1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_v list`; `s:(C,FFI)clos_state`;
                 `clos_state_code_fupd (K (c:(num,num#clos_exp)fmap)) (s:(C,FFI)clos_state)`;
                 `r:(clos_exp list,clos_v)result`; `s1:(C,FFI)clos_state`] do_install_SUBMAP) THEN
  ASM_REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_cok] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let CLOSPROPSAUX_cok_simps =
  [clos_state_INFO.ri_accfupds; K_THM; CLOSPROPSAUX_code_upd; map_result_def;
   map_error_result_I; I_THM];;

let CLOSPROPSAUX_COK_TAC : tactic =
  REPEAT STRIP_TAC THEN
  CLOSPROPSAUX_SPLIT_ASM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSPROPSAUX_code_upd]) THEN
  MAP_EVERY (fun th -> ASSUME_TAC (INST_TYPE [`:B`,`:A`] th))
    [CLOSPROPSAUX_do_app_cok_Rval; CLOSPROPSAUX_do_app_cok_Rerr;
     CLOSPROPSAUX_do_install_cok] THEN
  ASSUME_TAC (INST_TYPE [`:clos_v`,`:B`] CLOSPROPSAUX_cok_find_code) THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  CLOSPROPSAUX_RES2_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REPEAT(CHANGED_TAC(ASM_SIMP_TAC (CLOSPROPSAUX_cok_simps @ CLOSPROPSAUX_case_defs))) THEN
  TRY(ASM_MESON_TAC[]);;

(* local helper: evaluate with a bigger code (the functional form) *)
let CLOSPROPSAUX_evaluate_cok = prove
 (`(!xs env (s:(C,FFI)clos_state) r s' c.
      clos_evaluate (xs,env,s) = (r,s') /\ ~(r = Rerr (Rabort Rtype_error)) /\
      CLOSPROPSAUX_cok c s ==>
      ?c'. clos_evaluate (xs,env,clos_state_code_fupd (K c) s) =
           (r,clos_state_code_fupd (K c') s') /\ CLOSPROPSAUX_cok c' s') /\
   (!loc_opt v rest_args (s:(C,FFI)clos_state) r s' c.
      evaluate_app loc_opt v rest_args s = (r,s') /\ ~(r = Rerr (Rabort Rtype_error)) /\
      CLOSPROPSAUX_cok c s ==>
      ?c'. evaluate_app loc_opt v rest_args (clos_state_code_fupd (K c) s) =
           (r,clos_state_code_fupd (K c') s') /\ CLOSPROPSAUX_cok c' s')`,
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN CLOSPROPSAUX_COK_TAC);;

(* HOL4: evaluate_code_SUBMAP *)
let evaluate_code_SUBMAP = prove
 (`(!p x y (z1:(C,FFI)clos_state) r s1 (s2:(C,FFI)clos_state) (z2:(C,FFI)clos_state).
      p = (x,y,z1) /\ clos_evaluate (x,y,z1) = (r,s1) /\
      ~(r = Rerr (Rabort Rtype_error)) /\ SUBMAP_rel z1 z2 ==>
      ?s2. clos_evaluate (x,y,z2) = (r,s2) /\ SUBMAP_rel s1 s2) /\
   (!w x y (z1:(C,FFI)clos_state) r s1 (s2:(C,FFI)clos_state) (z2:(C,FFI)clos_state).
      evaluate_app w x y z1 = (r,s1) /\ ~(r = Rerr (Rabort Rtype_error)) /\
      SUBMAP_rel z1 z2 ==>
      ?s2. evaluate_app w x y z2 = (r,s2) /\ SUBMAP_rel s1 s2)`,
  REWRITE_TAC[CLOSPROPSAUX_SUBMAP_rel_cok] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[CLOSPROPSAUX_evaluate_cok]);;

(* termination with a recursive call on the elements of MAP SND fns *)
let CLOSPROPSAUX_TC3_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN
   REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o
                        check (is_exists o concl))) THEN
   RVEQ_TAC THEN
   REPEAT(FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[FST; SND] o
                        MATCH_MP CLOSPROPSAUX_MEM_SIZE)) THEN
   REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND; list_size; type_size_def "clos_exp"] @
               size_aux_eqs "clos_exp") THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_lt o concl))) THEN
   ARITH_TAC);;

(* HOL4: obeys_max_app_def; HOL4 rebinds it to its eta-reduced form, which  *)
(* is the form stored here (the Letrec list is named fns: one name, one type) *)
let obeys_max_app_def = sem1aux_def_wf
  `measure (\p:num # clos_exp. clos_exp_size (SND p))`
  CLOSPROPSAUX_TC3_TAC
  `(obeys_max_app m (clos_Var _ _) <=> T) /\
   (obeys_max_app m (clos_If _ e1 e2 e3) <=>
      obeys_max_app m e1 /\ obeys_max_app m e2 /\ obeys_max_app m e3) /\
   (obeys_max_app m (clos_Let _ es e) <=> ALL (obeys_max_app m) es /\ obeys_max_app m e) /\
   (obeys_max_app m (clos_Raise _ e) <=> obeys_max_app m e) /\
   (obeys_max_app m (clos_Handle _ e1 e2) <=> obeys_max_app m e1 /\ obeys_max_app m e2) /\
   (obeys_max_app m (clos_Tick _ e) <=> obeys_max_app m e) /\
   (obeys_max_app m (clos_Call _ _ _ es) <=> ALL (obeys_max_app m) es) /\
   (obeys_max_app m (clos_App _ _ e es) <=>
      LENGTH es <= m /\ obeys_max_app m e /\ ALL (obeys_max_app m) es) /\
   (obeys_max_app m (Fn _ _ _ _ e) <=> obeys_max_app m e) /\
   (obeys_max_app m (clos_Letrec _ _ _ fns e) <=>
      ALL (obeys_max_app m) (MAP SND fns) /\ obeys_max_app m e) /\
   (obeys_max_app m (clos_Op _ _ es) <=> ALL (obeys_max_app m) es)`;;
let _ = cake_add_simps [obeys_max_app_def];;

let obeys_max_app_ind = cake_ind "obeys_max_app";;

(* HOL4: no_Labels_def; HOL4 rebinds it to its eta-reduced form, which is    *)
(* the form stored here                                                      *)
let no_Labels_def = sem1aux_def_wf
  `measure clos_exp_size`
  CLOSPROPSAUX_TC3_TAC
  `(no_Labels (clos_Var _ _) <=> T) /\
   (no_Labels (clos_If _ e1 e2 e3) <=> no_Labels e1 /\ no_Labels e2 /\ no_Labels e3) /\
   (no_Labels (clos_Let _ es e) <=> ALL no_Labels es /\ no_Labels e) /\
   (no_Labels (clos_Raise _ e) <=> no_Labels e) /\
   (no_Labels (clos_Handle _ e1 e2) <=> no_Labels e1 /\ no_Labels e2) /\
   (no_Labels (clos_Tick _ e) <=> no_Labels e) /\
   (no_Labels (clos_Call _ _ _ es) <=> ALL no_Labels es) /\
   (no_Labels (clos_App _ _ e es) <=> no_Labels e /\ ALL no_Labels es) /\
   (no_Labels (Fn _ _ _ _ e) <=> no_Labels e) /\
   (no_Labels (clos_Letrec _ _ _ fns e) <=> ALL no_Labels (MAP SND fns) /\ no_Labels e) /\
   (no_Labels (clos_Op _ op es) <=> (!n. ~(op = clos_Label n)) /\ ALL no_Labels es)`;;
let _ = cake_add_simps [no_Labels_def];;

let no_Labels_ind = cake_ind "no_Labels";;

(* HOL4: app_call_dests_def (HOL4 [simp,compute,allow_rebind] = itself) *)
let app_call_dests_def = sem1aux_def_wf
  `measure (\p:bool option # clos_exp list. list_size clos_exp_size (SND p))`
  CLOSPROPSAUX_TC_TAC
  `(app_call_dests opt [] = ({}:num->bool)) /\
   (app_call_dests opt (CONS x (CONS y xs)) =
      let c1 = app_call_dests opt [x] in
      let c2 = app_call_dests opt (CONS y xs) in
        c1 UNION c2) /\
   (app_call_dests opt [clos_Var _ v] = {}) /\
   (app_call_dests opt [clos_If _ x1 x2 x3] =
      let c1 = app_call_dests opt [x1] in
      let c2 = app_call_dests opt [x2] in
      let c3 = app_call_dests opt [x3] in
        (c1 UNION c2) UNION c3) /\
   (app_call_dests opt [clos_Let _ xs x2] =
      let c1 = app_call_dests opt xs in
      let c2 = app_call_dests opt [x2] in
        c1 UNION c2) /\
   (app_call_dests opt [clos_Raise _ x1] =
      app_call_dests opt [x1]) /\
   (app_call_dests opt [clos_Tick _ x1] =
      app_call_dests opt [x1]) /\
   (app_call_dests opt [clos_Op _ op xs] =
      app_call_dests opt xs) /\
   (app_call_dests opt [clos_App _ loc_opt x1 xs] =
      let ll = if opt = SOME T then {} else
                 (match loc_opt with SOME n -> {n} | _ -> {}) in
      let c1 = app_call_dests opt [x1] in
      let c2 = app_call_dests opt xs in
        (ll UNION c1) UNION c2) /\
   (app_call_dests opt [Fn _ loc_opt vs num_args x1] =
      let c1 = app_call_dests opt [x1] in c1) /\
   (app_call_dests opt [clos_Letrec _ loc_opt vs fns x1] =
      let c1 = app_call_dests opt (MAP SND fns) in
      let c2 = app_call_dests opt [x1] in
        c1 UNION c2) /\
   (app_call_dests opt [clos_Handle _ x1 x2] =
      let c1 = app_call_dests opt [x1] in
      let c2 = app_call_dests opt [x2] in
        c1 UNION c2) /\
   (app_call_dests opt [clos_Call _ ticks dest xs] =
      if opt = SOME F then app_call_dests opt xs else
        dest INSERT app_call_dests opt xs)`;;
let _ = cake_add_simps [app_call_dests_def];;

let app_call_dests_ind = cake_ind "app_call_dests";;

(* HOL4: app_call_dests_cons (HOL4 leaves opt free) *)
let app_call_dests_cons = prove
 (`!opt y x. app_call_dests opt (CONS x y) = app_call_dests opt [x] UNION app_call_dests opt y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[app_call_dests_def; UNION_EMPTY; LET_DEF; LET_END_DEF]);;

(* HOL4: any_dest_cons, call_dest_cons, app_dest_cons *)
let any_dest_cons = SPEC `NONE:bool option` app_call_dests_cons;;
let call_dest_cons = SPEC `SOME T` app_call_dests_cons;;
let app_dest_cons = SPEC `SOME F` app_call_dests_cons;;

(* HOL4: app_call_dests_append (HOL4 leaves opt free) *)
let app_call_dests_append = prove
 (`!opt l1 l2. app_call_dests opt (APPEND l1 l2) =
               app_call_dests opt l1 UNION app_call_dests opt l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; app_call_dests_def; UNION_EMPTY] THEN
  ONCE_REWRITE_TAC[app_call_dests_cons] THEN ASM_REWRITE_TAC[UNION_ASSOC]);;

(* HOL4: any_dest_append, call_dest_append, app_dest_append *)
let any_dest_append = SPEC `NONE:bool option` app_call_dests_append;;
let call_dest_append = SPEC `SOME T` app_call_dests_append;;
let app_dest_append = SPEC `SOME F` app_call_dests_append;;

(* HOL4: app_call_dests_map (HOL4 leaves opt and f free) *)
let app_call_dests_map = prove
 (`!opt (f:A->clos_exp) ls.
     app_call_dests opt (MAP f ls) =
     UNIONS (set_of_list (MAP (\x. app_call_dests opt [f x]) ls))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT; app_call_dests_def] THEN
  GEN_REWRITE_TAC LAND_CONV [app_call_dests_cons] THEN ASM_REWRITE_TAC[]);;

(* HOL4: any_dests_call_dests_app_dests *)
let any_dests_call_dests_app_dests = prove
 (`!xs. app_call_dests NONE xs =
        app_call_dests (SOME T) xs UNION app_call_dests (SOME F) xs`,
  MATCH_MP_TAC code_locs_ind THEN
  REWRITE_TAC[app_call_dests_def; LET_DEF; LET_END_DEF; UNION_EMPTY;
              distinctness "option"; injectivity "option"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* HOL4: get_code_labels_def; HOL4 rebinds it to the form with              *)
(* MAP (get_code_labels o SND) (MAP_MAP_o), stored below under the same name *)
(* (the label of Call is named d: one name, one type in a quotation)         *)
let clos_get_code_labels_def = sem1aux_def_wf
  `measure clos_exp_size`
  CLOSPROPSAUX_TC3_TAC
  `(clos_get_code_labels (clos_Var _ _) = ({}:num->bool)) /\
   (clos_get_code_labels (clos_If _ e1 e2 e3) =
      (clos_get_code_labels e1 UNION clos_get_code_labels e2) UNION
      clos_get_code_labels e3) /\
   (clos_get_code_labels (clos_Let _ es e) =
      UNIONS (set_of_list (MAP clos_get_code_labels es)) UNION clos_get_code_labels e) /\
   (clos_get_code_labels (clos_Raise _ e) = clos_get_code_labels e) /\
   (clos_get_code_labels (clos_Handle _ e1 e2) =
      clos_get_code_labels e1 UNION clos_get_code_labels e2) /\
   (clos_get_code_labels (clos_Tick _ e) = clos_get_code_labels e) /\
   (clos_get_code_labels (clos_Call _ _ d es) =
      {d} UNION UNIONS (set_of_list (MAP clos_get_code_labels es))) /\
   (clos_get_code_labels (clos_App _ l e es) =
      ((match l with NONE -> {} | SOME n -> {n}) UNION clos_get_code_labels e) UNION
      UNIONS (set_of_list (MAP clos_get_code_labels es))) /\
   (clos_get_code_labels (Fn _ l _ _ e) =
      (match l with NONE -> {} | SOME n -> {n}) UNION clos_get_code_labels e) /\
   (clos_get_code_labels (clos_Letrec _ l _ fns e) =
      ((match l with
          NONE -> {}
        | SOME n -> IMAGE (\k. n + 2 * k) (count (LENGTH fns))) UNION
       clos_get_code_labels e) UNION
      UNIONS (set_of_list (MAP clos_get_code_labels (MAP SND fns)))) /\
   (clos_get_code_labels (clos_Op _ op es) =
      UNIONS (set_of_list (MAP clos_get_code_labels es)) UNION assign_get_code_label op)`;;

let clos_get_code_labels_ind = cake_ind "clos_get_code_labels";;

let clos_get_code_labels_def = REWRITE_RULE[MAP_MAP_o] clos_get_code_labels_def;;
let _ = cake_add_simps [clos_get_code_labels_def];;

(* a local helper: an operation that is not a label has no code label *)
let CLOSPROPSAUX_assign_get_code_label_empty = prove
 (`!op. (!n. ~(op = clos_Label n)) ==> assign_get_code_label op = {}`,
  MATCH_MP_TAC clos_op_INDUCT THEN
  REWRITE_TAC[assign_get_code_label_def; injectivity "clos_op"] THEN MESON_TAC[]);;

(* HOL4: get_code_labels_code_locs *)
let get_code_labels_code_locs = prove
 (`!xs. ALL no_Labels xs /\ every_Fn_SOME xs ==>
        UNIONS (set_of_list (MAP clos_get_code_labels xs)) =
        set_of_list (code_locs xs) UNION app_call_dests NONE xs`,
  MATCH_MP_TAC code_locs_ind THEN
  REWRITE_TAC[code_locs_def; app_call_dests_def; clos_get_code_labels_def; no_Labels_def;
              every_Fn_SOME_def; ALL; MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
              LET_DEF; LET_END_DEF; UNION_EMPTY; SET_OF_LIST_APPEND; MAP_MAP_o;
              distinctness "option"; injectivity "option"; IS_SOME_EXISTS] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o]) THEN
  ASM_REWRITE_TAC[case_def "option"; LIST_TO_SET_GENLIST; set_of_list] THEN
  TRY(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP CLOSPROPSAUX_assign_get_code_label_empty)) THEN
  SET_TAC[]);;

(* HOL4: initial_state_clock *)
let clos_initial_state_clock = prove
 (`!(ffi:(FFI)ffi_state) max_app f (co:num -> C # clos_prog) cc k k'.
     clos_state_clock (clos_initial_state ffi max_app f co cc k) = k /\
     clos_state_clock_fupd (K k) (clos_initial_state ffi max_app f co cc k') =
     clos_initial_state ffi max_app f co cc k`,
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_fupds; K_THM]);;
