(* ========================================================================= *)
(* bvi_tailrecProof: port of HOL4 compiler/backend/proofs/                   *)
(* bvi_tailrecProofScript.sml (CakeML v3479).                                *)
(* Correctness proof for bvi_tailrec.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The states s of HOL4 (type (num # C, FFI) state) and s1 (type          *)
(*   (C,FFI) state) are written with these types.                            *)
(* - HOL4's Overload in_ns_2 n = (n MOD bvl_to_bvi_namespaces = 2) is        *)
(*   expanded.                                                               *)
(* - BVITAILAUX_ names are local helpers (not HOL4 names).                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/lprefix_lub.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Simple facts about the definitions of bvi_tailrec.                        *)
(* ------------------------------------------------------------------------- *)

let get_bin_args_SOME = prove
 (`!exp q. get_bin_args exp = SOME q <=>
           ?e1 e2 op. q = (e1,e2) /\ exp = bvi_Op op [e1; e2]`,
  GEN_TAC THEN CASES_ON `exp:bvi_exp` THEN REWRITE_TAC[get_bin_args_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN RW[] THEN MESON_TAC[]);;
let _ = cake_add_simps [get_bin_args_SOME];;

let opbinargs_SOME = prove
 (`!exp opr. opbinargs opr exp = SOME q <=>
     ~(opr = Noop) /\ ?x y. q = (x,y) /\ exp = bvi_Op (to_op opr) [x; y]`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `exp:bvi_exp` THEN CASES_ON `opr:assoc_op` THEN
  REWRITE_TAC[opbinargs_def; op_eq_def; to_op_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[get_bin_args_SOME; option_DISTINCT] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;
let _ = cake_add_simps [opbinargs_SOME];;

let decide_ty_simp1 = prove
 (`(decide_ty ty1 ty2 = bvi_tailrec_Int <=>
    ty1 = bvi_tailrec_Int /\ ty2 = bvi_tailrec_Int) /\
   (decide_ty ty1 ty2 = bvi_tailrec_List <=>
    ty1 = bvi_tailrec_List /\ ty2 = bvi_tailrec_List)`,
  CASES_ON `ty1:v_ty` THEN CASES_ON `ty2:v_ty` THEN
  REWRITE_TAC[decide_ty_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [decide_ty_simp1];;

let list_to_v_simp = prove
 (`!xs. bvl_v_to_list (bvl_list_to_v xs) = SOME xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[bvl_list_to_v_def; bvl_v_to_list_def] THEN
  CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [list_to_v_simp];;

let to_op_11 = prove
 (`to_op op1 = to_op op2 <=> op1 = op2`,
  CASES_ON `op1:assoc_op` THEN CASES_ON `op2:assoc_op` THEN
  REWRITE_TAC[to_op_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [to_op_11];;

let to_op_eq_simp = prove
 (`(to_op x = IntOp clos_Add <=> x = Plus) /\
   (to_op x = IntOp Mult <=> x = Times) /\
   (to_op x = IntOp clos_Mod <=> x = Noop) /\
   (to_op x = BlockOp clos_ListAppend <=> x = bvi_tailrec_Append) /\
   (IntOp clos_Add = to_op x <=> x = Plus) /\
   (IntOp Mult = to_op x <=> x = Times) /\
   (BlockOp clos_ListAppend = to_op x <=> x = bvi_tailrec_Append) /\
   (IntOp clos_Mod = to_op x <=> x = Noop)`,
  CASES_ON `x:assoc_op` THEN REWRITE_TAC[to_op_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [to_op_eq_simp];;

let op_eq_simp = prove
 (`(op_eq Plus x <=> ?xs. x = bvi_Op (IntOp clos_Add) xs) /\
   (op_eq Times x <=> ?xs. x = bvi_Op (IntOp Mult) xs) /\
   (op_eq bvi_tailrec_Append x <=> ?xs. x = bvi_Op (BlockOp clos_ListAppend) xs)`,
  CASES_ON `x:bvi_exp` THEN REWRITE_TAC[op_eq_def] THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [op_eq_simp];;

let scan_expr_EVERY_SING = prove
 (`ALL (P:v_ty list # v_ty # bool # assoc_op option -> bool) (scan_expr ts loc [x]) <=>
   P (HD (scan_expr ts loc [x]))`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; ALL; HD]);;
let _ = cake_add_simps [scan_expr_EVERY_SING];;

let try_update_LENGTH = prove
 (`LENGTH (try_update ty idx ts) = LENGTH ts`,
  CASES_ON `idx:num option` THEN REWRITE_TAC[try_update_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE; LENGTH_DROP; LENGTH; LT_IMP_LE] THEN
  ASM_ARITH_TAC);;
let _ = cake_add_simps [try_update_LENGTH];;

let update_context_LENGTH = prove
 (`LENGTH (update_context ty ts x y) = LENGTH ts`,
  REWRITE_TAC[update_context_def; try_update_LENGTH]);;
let _ = cake_add_simps [update_context_LENGTH];;

let decide_ty_simp = prove
 (`decide_ty ty1 ty2 = ty3 /\ ~(ty3 = bvi_tailrec_Any) <=>
   ty1 = ty3 /\ ty2 = ty3 /\ ~(ty3 = bvi_tailrec_Any)`,
  CASES_ON `ty1:v_ty` THEN CASES_ON `ty2:v_ty` THEN CASES_ON `ty3:v_ty` THEN
  REWRITE_TAC[decide_ty_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [decide_ty_simp];;

let ty_rel_def = cake_def
  `ty_rel = ALL2 (\v t. (t = bvi_tailrec_Int ==> ?k. v = bvl_Number k) /\
                        (t = bvi_tailrec_List ==> ?ys. bvl_v_to_list v = SOME ys))`;;

(* HOL4: case_eq_thms = v_ty_cases, assoc_op_cases and bviProps'          *)
(* case_eq_thms (a local val)                                             *)

let BVITAILAUX_case_eq_thms =
  [case_eq "v_ty"; case_eq "assoc_op"; bvi_case_eq_thms];;

let list_to_v_imp = prove
 (`!x xs. bvl_v_to_list x = SOME xs ==> bvl_list_to_v xs = x`,
  MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def] THEN
  CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[bvl_list_to_v_def];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    DISCH_TAC THEN GEN_TAC THEN CASES_ON `bvl_v_to_list bt` THEN
    CASE_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[bvl_list_to_v_def]]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers: the evaluation of the expressions that term_ok accepts.    *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_NOT_FORALL_NEQ = MESON[] `!a:A. (!i. ~(a = i)) <=> F`;;

let BVITAILAUX_EXISTS_EQ = prove(`!a:A. ?x. a = x`, MESON_TAC[]);;

let BVITAILAUX_ANTS_ASM : tactic = ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC];;

(* an assumption get_bin_args e = r *)
let BVITAILAUX_is_gba th =
  let c = concl th in is_eq c && is_comb (lhs c) && rator (lhs c) = `get_bin_args`;;

let BVITAILAUX_do_app_IntOp = prove
 (CASE_TERM
  `!iop vs (s:(C,FFI)bvi_state).
     (!i. ~(iop = clos_Const i)) ==>
     bvi_do_app (IntOp iop) vs s =
     match bvl_do_int_app iop vs with
       SOME v -> Rval (v,s)
     | NONE -> Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `bvi_do_app_aux (IntOp iop) vs (s:(C,FFI)bvi_state) = SOME NONE`
    ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CASES_ON `iop:int_op` THEN
    REWRITE_TAC[distinctness "int_op"; injectivity "int_op"; BVITAILAUX_NOT_FORALL_NEQ] THEN
    REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `bvl_do_int_app iop vs` THEN CASE_REWRITE_TAC[bvl_to_bvi_id]);;

let BVITAILAUX_do_app_ListAppend = prove
 (CASE_TERM
  `!x1 x2 (s:(C,FFI)bvi_state).
     bvi_do_app (BlockOp clos_ListAppend) [x1; x2] s =
     match (bvl_v_to_list x1, bvl_v_to_list x2) with
       (SOME xs, SOME ys) -> Rval (bvl_list_to_v (APPEND xs ys),s)
     | _ -> Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `bvl_v_to_list x1` THEN CASES_ON `bvl_v_to_list x2` THEN
  CASE_REWRITE_TAC[bvl_to_bvi_id]);;

let BVITAILAUX_do_app_Cons = prove
 (`!tag xs (s:(C,FFI)bvi_state).
     bvi_do_app (BlockOp (clos_Cons tag)) xs s = Rval (bvl_Block tag xs,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[bvl_to_bvi_id]);;

let BVITAILAUX_do_app_Const = prove
 (`!i (s:(C,FFI)bvi_state). small_enough_int i ==>
     bvi_do_app (IntOp (clos_Const i)) [] s = Rval (bvl_Number i,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[NULL] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_evaluate_Op2 = prove
 (CASE_TERM
  `!op x y env vx vy (s:(C,FFI)bvi_state).
     bvi_evaluate ([x],env,s) = (Rval [vx],s) /\
     bvi_evaluate ([y],env,s) = (Rval [vy],s) ==>
     bvi_evaluate ([bvi_Op op [x; y]],env,s) =
     match bvi_do_app op [vy; vx] s with
       Rval (v,s') -> (Rval [v],s')
     | Rerr e -> (Rerr e,s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bvi_evaluate_def] THEN
  CASE_REWRITE_TAC[REVERSE; APPEND; HD] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[REVERSE; APPEND; HD]);;

let BVITAILAUX_evaluate_Op0 = prove
 (CASE_TERM
  `!op env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Op op []],env,s) =
     match bvi_do_app op [] s with
       Rval (v,s') -> (Rval [v],s')
     | Rerr e -> (Rerr e,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  CASE_REWRITE_TAC[REVERSE; APPEND; HD]);;

let BVITAILAUX_is_const_eq = prove
 (`!op. bvi_tailrec_is_const op <=> ?i. op = IntOp (clos_Const i) /\ small_enough_int i`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN REWRITE_TAC[bvi_tailrec_is_const_def] THEN
  CASE_REWRITE_TAC[] THEN TRY(CASES_ON `a:int_op`) THEN
  REWRITE_TAC[bvi_tailrec_is_const_def] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let BVITAILAUX_is_arith_eq = prove
 (`!op. is_arith op <=> op = IntOp clos_Add \/ op = IntOp clos_Sub \/ op = IntOp Mult`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN REWRITE_TAC[is_arith_def] THEN
  CASE_REWRITE_TAC[] THEN TRY(CASES_ON `a:int_op`) THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_is_rel_eq = prove
 (`!op. is_rel op <=> op = IntOp clos_Less \/ op = IntOp LessEq \/
                      op = IntOp Greater \/ op = IntOp GreaterEq`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN REWRITE_TAC[is_rel_def] THEN
  CASE_REWRITE_TAC[] THEN TRY(CASES_ON `a:int_op`) THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_ty_rel_EL = prove
 (`!env ts n. ty_rel env ts /\ n < LENGTH ts ==>
     n < LENGTH env /\
     (EL n ts = bvi_tailrec_Int ==> ?k. EL n env = bvl_Number k) /\
     (EL n ts = bvi_tailrec_List ==> ?ys. bvl_v_to_list (EL n env) = SOME ys)`,
  REWRITE_TAC[ty_rel_def; LIST_REL_EL_EQN] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* use the induction hypothesis labelled lab (instantiated with tms) at env *)
let BVITAILAUX_IH_TAC (lab:string) (tms:term list) (env:term) (v:term) : tactic =
  USE_THEN lab (MP_TAC o SPECL tms) THEN REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] ORELSE
         DISCH_THEN(MP_TAC o SPEC env)) THEN
  DISCH_THEN(X_CHOOSE_THEN v STRIP_ASSUME_TAC);;
let BVITAILAUX_term_ok_int_eval = prove
 (`!ts exp. term_ok_int ts exp ==>
     !env. ty_rel env ts ==>
       ?k. !s:(C,FFI)bvi_state. bvi_evaluate ([exp],env,s) = (Rval [bvl_Number k],s)`,
  MATCH_MP_TAC term_ok_int_ind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihx") (LABEL_TAC "ihy")) THEN
  ONCE_REWRITE_TAC[term_ok_int_def] THEN CASES_ON `expr:bvi_exp` THEN CASE_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `env:bvl_v list` THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`env:bvl_v list`; `ts:v_ty list`; `a:num`] BVITAILAUX_ty_rel_EL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `k:int` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def];
    ALL_TAC] THEN
  CASES_ON `get_bin_args (bvi_Op a0 a1)` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[BVITAILAUX_is_const_eq] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `i:int` THEN
    ASM_SIMP_TAC[BVITAILAUX_evaluate_Op0; BVITAILAUX_do_app_Const] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  PAIRARG_TAC THEN STRIP_TAC THEN X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?kx. !s:(C,FFI)bvi_state. bvi_evaluate ([x],env,s) = (Rval [bvl_Number kx],s)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "ihx" (MP_TAC o SPECL [`a0:clos_op`; `a1:bvi_exp list`; `y:bvi_exp`; `x:bvi_exp`]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `env:bvl_v list` o C MP (ASSUME `term_ok_int ts x`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ky. !s:(C,FFI)bvi_state. bvi_evaluate ([y],env,s) = (Rval [bvl_Number ky],s)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "ihy" (MP_TAC o SPECL [`a0:clos_op`; `a1:bvi_exp list`; `x:bvi_exp`; `y:bvi_exp`]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `env:bvl_v list` o C MP (ASSUME `term_ok_int ts y`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[get_bin_args_SOME] o
    check (can (find_term ((=) `get_bin_args`)) o concl)) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "bvi_exp"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[ISPECL [`op:clos_op`; `e1:bvi_exp`; `e2:bvi_exp`; `env:bvl_v list`;
                       `bvl_Number kx`; `bvl_Number ky`] BVITAILAUX_evaluate_Op2] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITAILAUX_is_arith_eq] o
    check (can (find_term ((=) `is_arith`)) o concl)) THEN RVEQ_TAC THEN
  SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN
  REWRITE_TAC[bvl_do_int_app_def] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let term_ok_int_SING = prove
 (`!ts exp env (s:(C,FFI)bvi_state) r t.
     term_ok_int ts exp /\ ty_rel env ts /\ bvi_evaluate ([exp],env,s) = (r,t) ==>
     s = t /\
     ?v. r = Rval [v] /\
         (!s:(C,FFI)bvi_state. bvi_evaluate ([exp],env,s) = (r,s)) /\
         ?k. v = bvl_Number k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ts:v_ty list`; `exp:bvi_exp`] BVITAILAUX_term_ok_int_eval) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `env:bvl_v list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:int`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:(C,FFI)bvi_state`) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[injectivity "result"; CONS_11] THEN
  MESON_TAC[]);;

let BVITAILAUX_term_ok_any_eval = prove
 (`!ts list exp. term_ok_any ts list exp ==>
     !env. ty_rel env ts ==>
       ?v. (!s:(C,FFI)bvi_state. bvi_evaluate ([exp],env,s) = (Rval [v],s)) /\
           (list ==> ?ys. bvl_v_to_list v = SOME ys)`,
  MATCH_MP_TAC term_ok_any_ind THEN REWRITE_TAC[term_ok_any_def] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH (ts:v_ty list)` ASSUME_TAC THENL
     [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REPEAT COND_CASES_TAC THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`env:bvl_v list`; `ts:v_ty list`; `i:num`] BVITAILAUX_ty_rel_EL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `EL i (env:bvl_v list)` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `if ~list then i < LENGTH (ts:v_ty list)
                 else if i < LENGTH ts then EL i ts = bvi_tailrec_List else F` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i1") (CONJUNCTS_THEN2 (LABEL_TAC "i2")
    (CONJUNCTS_THEN2 (LABEL_TAC "i3") (LABEL_TAC "i4")))) THEN
  CASES_ON `get_bin_args (bvi_Op op xs)` THEN CASE_REWRITE_TAC[] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    BOOL_CASES_TAC `list:bool` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
    REWRITE_TAC[BVITAILAUX_evaluate_Op0] THENL
     [RVEQ_TAC THEN REWRITE_TAC[BVITAILAUX_do_app_Cons] THEN CASE_REWRITE_TAC[] THEN
      EXISTS_TAC `bvl_Block 0 []` THEN REWRITE_TAC[bvl_v_to_list_def; nil_tag_def] THEN
      MESON_TAC[];
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITAILAUX_is_const_eq] o
        check (can (find_term ((=) `bvi_tailrec_is_const`)) o concl)) THEN
      RVEQ_TAC THEN ASM_SIMP_TAC[BVITAILAUX_do_app_Const] THEN CASE_REWRITE_TAC[] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  PAIRARG_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[get_bin_args_SOME] o check BVITAILAUX_is_gba) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "bvi_exp"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  COND_CASES_TAC THENL
   [RVEQ_TAC THEN STRIP_TAC THEN X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
    BVITAILAUX_IH_TAC "i3" [`e2:bvi_exp`; `e1:bvi_exp`] `env:bvl_v list` `v1:bvl_v` THEN
    BVITAILAUX_IH_TAC "i4" [`e1:bvi_exp`; `e2:bvi_exp`] `env:bvl_v list` `v2:bvl_v` THEN
    ASM_SIMP_TAC[ISPECL [`op:clos_op`; `e1:bvi_exp`; `e2:bvi_exp`; `env:bvl_v list`;
                         `v1:bvl_v`; `v2:bvl_v`] BVITAILAUX_evaluate_Op2] THEN
    ASM_REWRITE_TAC[BVITAILAUX_do_app_ListAppend] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[list_to_v_simp];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `term_ok_int ts (bvi_Op op' [e1; e2])` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[term_ok_int_def] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`ts:v_ty list`; `bvi_Op op' [e1; e2]`] BVITAILAUX_term_ok_int_eval) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `env:bvl_v list`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`ts:v_ty list`; `e1:bvi_exp`] BVITAILAUX_term_ok_int_eval) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `env:bvl_v list`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k1:int`) THEN
    MP_TAC(SPECL [`ts:v_ty list`; `e2:bvi_exp`] BVITAILAUX_term_ok_int_eval) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `env:bvl_v list`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k2:int`) THEN
    ASM_SIMP_TAC[ISPECL [`op:clos_op`; `e1:bvi_exp`; `e2:bvi_exp`; `env:bvl_v list`;
                         `bvl_Number k1`; `bvl_Number k2`] BVITAILAUX_evaluate_Op2] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITAILAUX_is_rel_eq] o
      check (can (find_term ((=) `is_rel`)) o concl)) THEN RVEQ_TAC THEN
    SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN
    REWRITE_TAC[bvl_do_int_app_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BVITAILAUX_EXISTS_EQ];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  RVEQ_TAC THEN STRIP_TAC THEN X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
  BVITAILAUX_IH_TAC "i2" [`e2:bvi_exp`; `e1:bvi_exp`] `env:bvl_v list` `v1:bvl_v` THEN
  BVITAILAUX_IH_TAC "i1" [`e1:bvi_exp`; `e2:bvi_exp`] `env:bvl_v list` `v2:bvl_v` THEN
  ASM_SIMP_TAC[ISPECL [`op:clos_op`; `e1:bvi_exp`; `e2:bvi_exp`; `env:bvl_v list`;
                       `v1:bvl_v`; `v2:bvl_v`] BVITAILAUX_evaluate_Op2] THEN
  REWRITE_TAC[BVITAILAUX_do_app_Cons] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `bvl_Block 0 [v2; v1]` THEN REWRITE_TAC[bvl_v_to_list_def; cons_tag_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; BVITAILAUX_EXISTS_EQ]);;

let term_ok_any_SING = prove
 (`!ts list exp env (s:(C,FFI)bvi_state) r t.
     term_ok_any ts list exp /\ ty_rel env ts /\ bvi_evaluate ([exp],env,s) = (r,t) ==>
     s = t /\
     ?v. r = Rval [v] /\
         (!s:(C,FFI)bvi_state. bvi_evaluate ([exp],env,s) = (r,s)) /\
         (list ==> ?ys. bvl_v_to_list v = SOME ys)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ts:v_ty list`; `list:bool`; `exp:bvi_exp`] BVITAILAUX_term_ok_any_eval) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `env:bvl_v list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:(C,FFI)bvi_state`) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[injectivity "result"; CONS_11] THEN
  ASM_MESON_TAC[]);;

let term_ok_SING = prove
 (CASE_TERM
  `!ts ty exp env (s:(C,FFI)bvi_state) r t.
     term_ok ts ty exp /\ ty_rel env ts /\ bvi_evaluate ([exp],env,s) = (r,t) ==>
     s = t /\
     ?v. r = Rval [v] /\
         (!s:(C,FFI)bvi_state. bvi_evaluate ([exp],env,s) = (r,s)) /\
         match ty with
           bvi_tailrec_Int -> ?k. v = bvl_Number k
         | bvi_tailrec_List -> ?ys. bvl_v_to_list v = SOME ys
         | _ -> T`,
  REPEAT GEN_TAC THEN CASES_ON `ty:v_ty` THEN REWRITE_TAC[term_ok_def] THEN
  CASE_REWRITE_TAC[] THEN
  MESON_TAC[term_ok_int_SING; term_ok_any_SING]);;

(* ------------------------------------------------------------------------- *)
(* op_id_val, env_rel and code_rel.                                          *)
(* ------------------------------------------------------------------------- *)

let op_id_val_def = cake_def
  `(op_id_val Plus = bvl_Number (&0)) /\
   (op_id_val Times = bvl_Number (&1)) /\
   (op_id_val bvi_tailrec_Append = bvl_Block nil_tag []) /\
   (op_id_val Noop = bvl_Number (&6333))`;;

(* PAIRARG_TAC with the variables of the assumption hypotheses avoided:    *)
(* the kit's PAIRARG_TAC picks names that are free only in hypotheses of   *)
(* assumption theorems (left by earlier splits) and then fails in CHOOSE   *)

let BVITAILAUX_PAIR_TAC : tactic = fun (asl,w as gl) ->
  let whole = list_mk_conj(w :: map (concl o snd) asl) in
  let is_cand t =
    is_case_app t &&
    (let c,x,fs = dest_case_app t in
     fst(dest_const c) = "pair_CASE" && not (is_pair x) && free_in x whole) in
  let t = find_term is_cand whole in
  let _,x,fs = dest_case_app t in
  let f = hd fs in
  let tya,tyb = match dest_type(type_of x) with
      "prod",[a;b] -> a,b | _ -> failwith "BVITAILAUX_PAIR_TAC" in
  let n1,n2 =
    try let a,b = dest_abs f in let b1,_ = dest_abs b in
        fst(dest_var a),fst(dest_var b1)
    with Failure _ -> "p1","p2" in
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  let v1 = variant avoid (mk_var(n1,tya)) in
  let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
  let nch = ISPEC x (nchotomy_of_type (type_of x)) in
  (MP_TAC nch THEN
   DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
     (fun th -> if is_var x then SUBST_ALL_TAC th
                else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
   CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;

let BVITAILAUX_scan_expr_sing_not_Noop = prove
 (`(!exp ts loc tt ty r op.
      scan_expr_sing ts loc exp = (tt,ty,r,SOME op) ==> ~(op = Noop)) /\
   (!l:bvi_exp list. T)`,
  MATCH_MP_TAC BVIPAUX_TR_exp_induct THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; option_DISTINCT; option_INJ]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN RVEQ_TAC THEN
  EVERY_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; option_DISTINCT; PAIR_EQ]) THEN
  RVEQ_TAC THEN ASM_MESON_TAC[]);;

let scan_expr_not_Noop = prove
 (`!exp ts loc tt ty r (ok:A) op.
     scan_expr ts loc [exp] = [(tt,ty,r,SOME op)] ==> ~(op = Noop)`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; CONS_11] THEN
  MESON_TAC[BVITAILAUX_scan_expr_sing_not_Noop]);;

let bvi_tailrecProof_env_rel_def = cake_def
 (CASE_TERM
  `bvi_tailrecProof_env_rel ty opt acc (env1:bvl_v list) env2 <=>
     env1 <<= env2 /\
     (opt ==>
        LENGTH env1 = acc /\ LENGTH env2 > acc /\
        match ty with
          bvi_tailrec_Int -> ?k. EL acc env2 = bvl_Number k
        | bvi_tailrec_List -> ?ys. bvl_v_to_list (EL acc env2) = SOME ys
        | bvi_tailrec_Any -> F)`);;

(* HOL4's local Overload in_ns_2 n = (n MOD bvl_to_bvi_namespaces = 2) is   *)
(* expanded where it is used                                               *)

let bvi_tailrecProof_code_rel_def = cake_def
  `bvi_tailrecProof_code_rel c1 c2 <=>
     !loc arity exp op.
       lookup loc c1 = SOME (arity,exp) ==>
       (check_exp loc arity exp = NONE ==> lookup loc c2 = SOME (arity,exp)) /\
       (check_exp loc arity exp = SOME op ==>
          ?n. !exp_aux exp_opt.
                bvi_tailrec_compile_exp loc n arity exp = SOME (exp_aux,exp_opt) ==>
                lookup loc c2 = SOME (arity,exp_aux) /\
                lookup n c2 = SOME (arity + 1,exp_opt))`;;

let BVITAILAUX_OPTION_CASES_TAC (tm:term) (v:term) : tactic =
  DISJ_CASES_THEN2 (X_CHOOSE_TAC v) ASSUME_TAC (ISPEC tm option_CASES);;

let BVITAILAUX_compile_exp_SOME = prove
 (`!loc n arity exp op. check_exp loc arity exp = SOME op ==>
     ?aux opt. bvi_tailrec_compile_exp loc n arity exp = SOME (aux,opt)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bvi_tailrec_compile_exp_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

let BVITAILAUX_compile_exp_NONE = prove
 (`!loc n arity exp. bvi_tailrec_compile_exp loc n arity exp = NONE <=>
                     check_exp loc arity exp = NONE`,
  REPEAT GEN_TAC THEN CASES_ON `check_exp loc arity exp` THEN
  ASM_REWRITE_TAC[bvi_tailrec_compile_exp_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT]);;

let BVITAILAUX_code_rel_lookup = prove
 (`!c1 c2 loc arity exp.
     bvi_tailrecProof_code_rel c1 c2 /\ lookup loc c1 = SOME (arity,exp) ==>
     ?exp2. lookup loc c2 = SOME (arity,exp2)`,
  REWRITE_TAC[bvi_tailrecProof_code_rel_def] THEN REPEAT STRIP_TAC THEN
  BVITAILAUX_OPTION_CASES_TAC `check_exp loc arity exp` `op:assoc_op` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    MP_TAC(SPECL [`loc:num`; `n:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]
                 BVITAILAUX_compile_exp_SOME) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`aux:bvi_exp`; `opt:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`; `Noop`]) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[]]);;

let code_rel_find_code_SOME = prove
 (`!c1 c2 (args:bvl_v list) a exp.
     bvi_tailrecProof_code_rel c1 c2 /\ bvl_find_code (SOME n) args c1 = SOME (a,exp) ==>
     ~(bvl_find_code (SOME n) args c2 = NONE)`,
  REWRITE_TAC[bvl_find_code_def] THEN REPEAT GEN_TAC THEN
  CASES_ON `lookup n (c1:(num#bvi_exp)spt)` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_PAIR_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:(num#bvi_exp)spt`; `c2:(num#bvi_exp)spt`; `n:num`; `arity:num`;
                `exp':bvi_exp`] BVITAILAUX_code_rel_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let code_rel_find_code_NONE = prove
 (`!c1 c2 (args:bvl_v list) a exp.
     bvi_tailrecProof_code_rel c1 c2 /\ bvl_find_code NONE args c1 = SOME (a,exp) ==>
     ~(bvl_find_code NONE args c2 = NONE)`,
  REWRITE_TAC[bvl_find_code_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `LAST (args:bvl_v list)` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup a' (c1:(num#bvi_exp)spt)` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_PAIR_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:(num#bvi_exp)spt`; `c2:(num#bvi_exp)spt`; `a':num`; `arity:num`;
                `exp':bvi_exp`] BVITAILAUX_code_rel_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let bvi_tailrecProof_code_rel_domain = prove
 (`!c1 c2. bvi_tailrecProof_code_rel c1 c2 ==> domain c1 SUBSET domain c2`,
  REWRITE_TAC[SUBSET; domain_lookup] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_eq o concl)) THEN
  ASM_MESON_TAC[BVITAILAUX_code_rel_lookup; PAIR_SURJECTIVE]);;

let BVITAILAUX_small_01 = prove
 (`small_enough_int (&0) /\ small_enough_int (&1)`,
  REWRITE_TAC[small_enough_int_def] THEN CONV_TAC INT_REDUCE_CONV);;

let evaluate_let_wrap = prove
 (`!x op vs (s:(C,FFI)bvi_state) (r:A) (t:B).
     ~(op = Noop) ==>
     bvi_evaluate ([let_wrap (LENGTH vs) (id_from_op op) x],vs,s) =
     bvi_evaluate ([x],APPEND (APPEND vs [op_id_val op]) vs,s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `vs:bvl_v list`; `LENGTH (vs:bvl_v list)`; `s:(C,FFI)bvi_state`]
    bvi_evaluate_genlist_vars) THEN
  REWRITE_TAC[ADD_CLAUSES; LE_REFL; DROP_0; TAKE_LENGTH_ID; ETA_AX] THEN DISCH_TAC THEN
  REWRITE_TAC[let_wrap_def] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  CASES_ON `op:assoc_op` THEN
  REWRITE_TAC[id_from_op_def; op_id_val_def; distinctness "assoc_op"] THEN
  REWRITE_TAC[BVITAILAUX_evaluate_Op0; BVITAILAUX_do_app_Cons] THEN
  SIMP_TAC[BVITAILAUX_do_app_Const; BVITAILAUX_small_01] THEN
  CASE_REWRITE_TAC[APPEND_ASSOC; APPEND]);;

let evaluate_complete_ind = prove
 (`!P. (!xs (s:(num#C,FFI)bvi_state).
          (!ys t. list_size bvi_exp_size ys < list_size bvi_exp_size xs /\
                  bvi_state_clock t <= bvi_state_clock s \/
                  bvi_state_clock t < bvi_state_clock s ==> P ys t) ==>
          P xs s) ==>
       !xs s. P xs s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n m xs (s:(num#C,FFI)bvi_state).
                  bvi_state_clock s = n /\ list_size bvi_exp_size xs = m ==> P xs s`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[LE_LT]; ASM_MESON_TAC[]]);;

let EVERY_LAST1 = prove
 (`!xs y. ALL (P:A->bool) xs /\ LAST1 xs = SOME y ==> P y`,
  MATCH_MP_TAC LAST1_ind THEN REWRITE_TAC[LAST1_def; ALL; option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[ALL]);;

let BVITAILAUX_scan_expr_sing_LENGTH = prove
 (`(!e ts loc. LENGTH (FST (scan_expr_sing ts loc e)) = LENGTH ts) /\
   (!l ts loc. ALL (\y. LENGTH (FST y) = LENGTH ts) (scan_expr_list ts loc l))`,
  MATCH_MP_TAC BVIPAUX_TR_exp_induct THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF; ALL] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ALL; FST; LISTAUX_LENGTH_MAP2; LENGTH_DROP; LENGTH_APPEND;
                  LENGTH_MAP] THENL
   [BVITAILAUX_OPTION_CASES_TAC `LAST1 (scan_expr_list ts loc a0)`
      `c:v_ty list # v_ty # bool # assoc_op option` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
    MP_TAC(ISPECL [`\y:v_ty list # v_ty # bool # assoc_op option.
                      LENGTH (FST y) = LENGTH (ts:v_ty list)`;
                   `scan_expr_list ts loc a0`;
                   `c:v_ty list # v_ty # bool # assoc_op option`]
                  (GEN `P:A->bool` EVERY_LAST1)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REPEAT(TOP_CASE_TAC THEN TRY(REWRITE_TAC[FST; update_context_LENGTH] THEN NO_TAC)) THEN
    REWRITE_TAC[FST; update_context_LENGTH];
    FIRST_X_ASSUM(MP_TAC o SPECL [`FST (scan_expr_sing ts loc a0)`; `loc:num`]) THEN
    ASM_REWRITE_TAC[]]);;

let scan_expr_LENGTH = prove
 (`!ts loc xs ys.
     scan_expr ts loc xs = ys ==> ALL (\y. LENGTH (FST y) = LENGTH ts) ys`,
  REWRITE_TAC[CONJUNCT2 scan_expr_eq] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[BVITAILAUX_scan_expr_sing_LENGTH]);;

let ty_rel_decide_ty = prove
 (`!ts tt env. (ty_rel env ts \/ ty_rel env tt) /\ LENGTH ts = LENGTH tt ==>
               ty_rel env (MAP2 decide_ty ts tt)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tt:v_ty list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `env:bvl_v list` list_CASES) THEN
  REWRITE_TAC[ty_rel_def; ALL2; MAP2; LENGTH; NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[GSYM ty_rel_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  MAP_EVERY (fun v -> CASES_ON v) [`h:v_ty`; `h':v_ty`] THEN
  REWRITE_TAC[decide_ty_def] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ty_rel_APPEND = prove
 (`!env ts ws vs. ty_rel env ts /\ ty_rel vs ws ==>
                  ty_rel (APPEND vs env) (APPEND ws ts)`,
  REWRITE_TAC[ty_rel_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (vs:bvl_v list) = LENGTH (ws:v_ty list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_EQ]);;

let LAST1_thm = prove
 (`!xs:A list. LAST1 xs = NONE <=> xs = []`,
  MATCH_MP_TAC LAST1_ind THEN REWRITE_TAC[LAST1_def; NOT_CONS_NIL; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let try_update_EL = prove
 (CASE_TERM
  `n < LENGTH ts ==>
   EL n (try_update ty idx ts) =
   match idx with
     NONE -> EL n ts
   | SOME m ->
       if n < m then EL n ts
       else if n > m then EL n ts
       else if EL n ts = bvi_tailrec_Any \/ EL n ts = ty then ty
       else EL n ts`,
  CASES_ON `idx:num option` THEN REWRITE_TAC[try_update_def] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    ASM_CASES_TAC `n < a:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n > a:num` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_CASES_TAC `n < a:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `n > a:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n = a:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[EL_APPEND; LENGTH_APPEND; LENGTH] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
  ASM_CASES_TAC `n < a:num` THEN ASM_SIMP_TAC[EL_TAKE; ARITH_RULE `n < a ==> n < a + SUC 0`] THEN
  ASM_CASES_TAC `n = a:num` THENL
   [ASM_REWRITE_TAC[LT_REFL; GT; ARITH_RULE `a < a + SUC 0`; SUB_REFL; EL; HD];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n < a + SUC 0) /\ n > a` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n - (a + SUC 0)`; `a + 1`; `ts:v_ty list`] EL_DROP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `a + SUC 0 = a + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let try_update_twice = prove
 (CASE_TERM
  `n < LENGTH ts ==>
   EL n (try_update ty idx1 (try_update ty idx2 ts)) =
   match (idx1,idx2) with
     (NONE,NONE) -> EL n ts
   | (NONE,SOME b) ->
       if ~(n = b) then EL n ts
       else if EL n ts = bvi_tailrec_Any then ty
       else EL n ts
   | (SOME a,NONE) ->
       if ~(n = a) then EL n ts
       else if EL n ts = bvi_tailrec_Any then ty
       else EL n ts
   | (SOME a,SOME b) ->
       if ~(n = a) /\ ~(n = b) then EL n ts
       else if EL n ts = bvi_tailrec_Any then ty
       else EL n ts`,
  DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (try_update ty idx2 ts)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[try_update_LENGTH]; ALL_TAC] THEN
  ASM_SIMP_TAC[try_update_EL] THEN
  CASES_ON `idx1:num option` THEN CASES_ON `idx2:num option` THEN CASE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_disj(concl th) then DISJ_CASES_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

let index_of_simp = prove
 (`index_of exp = SOME n <=> exp = bvi_Var n`,
  CASES_ON `exp:bvi_exp` THEN REWRITE_TAC[index_of_def] THEN CASE_REWRITE_TAC[]);;

let _ = cake_add_simps [index_of_simp];;

(* ------------------------------------------------------------------------- *)
(* Local helpers for scan_expr_ty_rel.                                       *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_ty_rel_SING = prove
 (`!v ty. ty_rel [v] [ty] <=>
          (ty = bvi_tailrec_Int ==> ?k. v = bvl_Number k) /\
          (ty = bvi_tailrec_List ==> ?ys. bvl_v_to_list v = SOME ys)`,
  REWRITE_TAC[ty_rel_def; ALL2]);;

let BVITAILAUX_ty_rel_CONS = prove
 (`!v vs ty tys.
     ty_rel (CONS v vs) (CONS ty tys) <=>
     ((ty = bvi_tailrec_Int ==> ?k. v = bvl_Number k) /\
      (ty = bvi_tailrec_List ==> ?ys. bvl_v_to_list v = SOME ys)) /\
     ty_rel vs tys`,
  REWRITE_TAC[ty_rel_def; ALL2]);;

let BVITAILAUX_ty_rel_try_update = prove
 (`!env ts ty idx.
     ty_rel env ts /\
     (!i. idx = SOME i /\ i < LENGTH ts /\ EL i ts = bvi_tailrec_Any ==>
          ty_rel [EL i env] [ty]) ==>
     ty_rel env (try_update ty idx ts)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "h")) THEN
  REWRITE_TAC[ty_rel_def; LIST_REL_EL_EQN; try_update_LENGTH] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (ts:v_ty list)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[try_update_EL] THEN
  CASES_ON `idx:num option` THEN CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `n = a:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [USE_THEN "h" (MP_TAC o SPEC `a:num`) THEN
    REWRITE_TAC[BVITAILAUX_ty_rel_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]]);;

let BVITAILAUX_ty_rel_update_context = prove
 (`!env ts ty x y.
     ty_rel env ts /\
     (!i. x = bvi_Var i /\ i < LENGTH ts ==> ty_rel [EL i env] [ty]) /\
     (!i. y = bvi_Var i /\ i < LENGTH ts ==> ty_rel [EL i env] [ty]) ==>
     ty_rel env (update_context ty ts x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[update_context_def] THEN
  MATCH_MP_TAC BVITAILAUX_ty_rel_try_update THEN
  ASM_SIMP_TAC[index_of_simp; try_update_LENGTH] THEN
  MATCH_MP_TAC BVITAILAUX_ty_rel_try_update THEN ASM_SIMP_TAC[index_of_simp]);;

let BVITAILAUX_ty_rel_DROP = prove
 (`!vs env tu. ty_rel (APPEND vs env) tu ==> ty_rel env (DROP (LENGTH vs) tu)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; DROP_0] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `tu:v_ty list` list_CASES) THEN
  REWRITE_TAC[ty_rel_def; ALL2] THEN REWRITE_TAC[GSYM ty_rel_def] THEN
  STRIP_TAC THEN REWRITE_TAC[DROP_DEF; NOT_SUC; SUC_SUB1] THEN ASM_MESON_TAC[]);;

(* case split on the sub-operation of a clos_op constructor *)
let BVITAILAUX_SUBOP_CASES_TAC : tactic = fun (asl,w as g) ->
  let fv = frees w in
  let pick = filter (fun v -> mem (fst(dest_type(type_of v)))
                         ["int_op"; "block_op"; "glob_op"; "mem_op"; "word_op"]) fv in
  match pick with v::_ -> CASES_ON v g | [] -> ALL_TAC g;;

let BVITAILAUX_option_CASE_Rval = prove
 (CASE_TERM
  `!(x:bvl_v option) (e:(E)error_result) (s:A) v t.
     (match x with NONE -> Rerr e | SOME r -> Rval (r,s)) = Rval (v,t) <=>
     x = SOME v /\ s = t`,
  GEN_TAC THEN CASES_ON `x:bvl_v option` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let BVITAILAUX_do_app_arg_Int = prove
 (`!op vs (s:(C,FFI)bvi_state) v t.
     arg_ty op = bvi_tailrec_Int /\ ~bvi_tailrec_is_const op /\
     bvi_do_app op vs s = Rval (v,t) ==>
     ALL (\w. ?k. w = bvl_Number k) vs`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN
  REWRITE_TAC[arg_ty_def; distinctness "v_ty"] THEN BVITAILAUX_SUBOP_CASES_TAC THEN
  REWRITE_TAC[arg_ty_def; distinctness "v_ty"; bvi_tailrec_is_const_def] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "v_ty"] THEN NO_TAC) THEN
  SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN
  REWRITE_TAC[BVITAILAUX_option_CASE_Rval] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSSEMAUX_do_int_app_some) THEN
  REWRITE_TAC[distinctness "int_op"] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  MESON_TAC[]);;

let BVITAILAUX_do_app_ListAppend_Rval = prove
 (`!vs (s:(C,FFI)bvi_state) v t.
     bvi_do_app (BlockOp clos_ListAppend) vs s = Rval (v,t) ==>
     ?x1 x2 xs ys. vs = [x1; x2] /\ bvl_v_to_list x1 = SOME xs /\
                   bvl_v_to_list x2 = SOME ys /\
                   v = bvl_list_to_v (APPEND xs ys) /\ t = s`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `vs:bvl_v list` list_CASES) THEN
  TRY(STRUCT_CASES_TAC(ISPEC `t:bvl_v list` list_CASES)) THEN
  TRY(STRUCT_CASES_TAC(ISPEC `t':bvl_v list` list_CASES)) THEN
  REWRITE_TAC[BVITAILAUX_do_app_ListAppend] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN CASES_ON `bvl_v_to_list h` THEN CASES_ON `bvl_v_to_list h'` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:bvl_v`; `h':bvl_v`; `a:bvl_v list`; `a':bvl_v list`] THEN
  ASM_REWRITE_TAC[]);;

let BVITAILAUX_do_app_from_op = prove
 (`!op vs (s:(C,FFI)bvi_state) v t.
     ~(from_op op = Noop) /\ bvi_do_app op vs s = Rval (v,t) ==>
     t = s /\ ty_rel [v] [op_type (from_op op)] /\
     ALL (\w. ty_rel [w] [op_type (from_op op)]) vs`,
  GEN_TAC THEN REWRITE_TAC[from_op_def] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[op_type_def; BVITAILAUX_ty_rel_SING; distinctness "assoc_op"] THEN
  REWRITE_TAC[distinctness "v_ty"] THEN RVEQ_TAC THENL
   [ALL_TAC; ALL_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BVITAILAUX_do_app_ListAppend_Rval) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ALL; list_to_v_simp] THEN MESON_TAC[]] THEN
  SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN
  REWRITE_TAC[BVITAILAUX_option_CASE_Rval] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DRULE CLOSSEMAUX_do_int_app_some THEN
  REWRITE_TAC[distinctness "int_op"] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  MESON_TAC[]);;

let BVITAILAUX_evaluate_Var_Rval = prove
 (`!i env (s:(C,FFI)bvi_state) vs t.
     bvi_evaluate ([bvi_Var i],env,s) = (Rval vs,t) ==>
     i < LENGTH env /\ vs = [EL i env] /\ t = s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;

let BVITAILAUX_SPLIT_TAC (tm:term) (r:term) (s:term) : tactic =
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)));;

let BVITAILAUX_evaluate_two = prove
 (`!x y env (s:(C,FFI)bvi_state) vs t.
     bvi_evaluate ([x; y],env,s) = (Rval vs,t) ==>
     ?vx vy. vs = [vx; vy] /\
             (!i. x = bvi_Var i ==> i < LENGTH env /\ vx = EL i env) /\
             (!i. y = bvi_Var i ==> i < LENGTH env /\ vy = EL i env)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([x],env,s:(C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([y],env,s1:(C,FFI)bvi_state)`
    `r2:bvi_result` `s2:(C,FFI)bvi_state` THEN
  CASES_ON `r2:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_evaluate_def; PAIR_EQ; injectivity "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`x:bvi_exp`; `env:bvl_v list`; `s:(C,FFI)bvi_state`; `a:bvl_v list`;
                 `s1:(C,FFI)bvi_state`] evaluate_SING_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `vx:bvl_v` SUBST_ALL_TAC) THEN
  MP_TAC(ISPECL [`y:bvi_exp`; `env:bvl_v list`; `s1:(C,FFI)bvi_state`; `a':bvl_v list`;
                 `t:(C,FFI)bvi_state`] evaluate_SING_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `vy:bvl_v` SUBST_ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC [`vx:bvl_v`; `vy:bvl_v`] THEN REWRITE_TAC[HD] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_evaluate_Var_Rval) THEN
  SIMP_TAC[CONS_11]);;

let BVITAILAUX_ty_rel_decide_ty_SING = prove
 (`!vs t1 t2. ty_rel vs [t1] \/ ty_rel vs [t2] ==> ty_rel vs [decide_ty t1 t2]`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:bvl_v list` list_CASES) THEN
  REWRITE_TAC[ty_rel_def; ALL2] THEN
  TRY(STRUCT_CASES_TAC(ISPEC `t:bvl_v list` list_CASES)) THEN
  REWRITE_TAC[ALL2] THEN REPEAT GEN_TAC THEN
  CASES_ON `t1:v_ty` THEN CASES_ON `t2:v_ty` THEN
  REWRITE_TAC[decide_ty_def] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let BVITAILAUX_USE_IH (lab:string) (tms:term list) : tactic =
  USE_THEN lab (MP_TAC o SPECL tms) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC];;

let BVITAILAUX_ty_rel_Any_TAC : tactic =
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST1_TAC o MATCH_MP evaluate_SING_IMP) THEN
  REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"];;

let BVITAILAUX_evaluate_Force_Rval = prove
 (`!fl n env (s:(C,FFI)bvi_state) vs t.
     bvi_evaluate ([bvi_Force fl n],env,s) = (Rval vs,t) ==>
     n < LENGTH env /\ ?b ptr. EL n env = bvl_RefPtr b ptr`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `EL n (env:bvl_v list)` THEN REWRITE_TAC[bvi_dest_thunk_def] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let BVITAILAUX_ty_rel_RefPtr = prove
 (`!b ptr ty. ty_rel [bvl_RefPtr b ptr] [ty] <=> ty = bvi_tailrec_Any`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ty_rel_SING] THEN
  CASES_ON `ty:v_ty` THEN REWRITE_TAC[distinctness "v_ty"; distinctness "bvl_v"] THEN
  REWRITE_TAC[bvl_v_to_list_def; option_DISTINCT]);;

let BVITAILAUX_do_app_Const_Rval = prove
 (`!i vs (s:(C,FFI)bvi_state) v t.
     bvi_do_app (IntOp (clos_Const i)) vs s = Rval (v,t) ==> v = bvl_Number i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* an assumption bvi_evaluate x = y *)
let BVITAILAUX_is_eval th =
  let c = concl th in
  is_eq c && is_comb (lhs c) && is_const (rator (lhs c)) &&
  fst(dest_const(rator(lhs c))) = "bvi_evaluate";;

let BVITAILAUX_STR_If_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i0") (CONJUNCTS_THEN2 (LABEL_TAC "i1")
    (LABEL_TAC "i2"))) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([a0],env,s:(C,FFI)bvi_state)`
    `r0:bvi_result` `s0:(C,FFI)bvi_state` THEN
  CASES_ON `r0:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  BETA_TAC THEN DISCH_TAC THEN
  BVITAILAUX_USE_IH "i0" [`ts:v_ty list`; `loc:num`; `env:bvl_v list`;
    `s:(C,FFI)bvi_state`; `a:bvl_v list`; `s0:(C,FFI)bvi_state`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`FST (scan_expr_sing ts loc a0)`, `ti:v_ty list`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (FST (scan_expr_sing ti loc a1)) =
                LENGTH (FST (scan_expr_sing ti loc a2))`
    ASSUME_TAC THENL [REWRITE_TAC[BVITAILAUX_scan_expr_sing_LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN DISCH_TAC THENL
   [BVITAILAUX_USE_IH "i1" [`ti:v_ty list`; `loc:num`; `env:bvl_v list`;
      `s0:(C,FFI)bvi_state`; `vs:bvl_v list`; `t:(C,FFI)bvi_state`];
    BVITAILAUX_USE_IH "i2" [`ti:v_ty list`; `loc:num`; `env:bvl_v list`;
      `s0:(C,FFI)bvi_state`; `vs:bvl_v list`; `t:(C,FFI)bvi_state`]] THEN
  STRIP_TAC THEN
  (CONJ_TAC THENL [MATCH_MP_TAC ty_rel_decide_ty THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT TOP_CASE_TAC THEN ASM_MESON_TAC[BVITAILAUX_ty_rel_decide_ty_SING];;

let BVITAILAUX_STR_Let_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i0") (LABEL_TAC "i1")) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (a0,env,s:(C,FFI)bvi_state)`
    `r0:bvi_result` `s0:(C,FFI)bvi_state` THEN
  CASES_ON `r0:bvi_result` THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  BETA_TAC THEN
  BVITAILAUX_USE_IH "i0" [`ts:v_ty list`; `loc:num`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
                          `a:bvl_v list`; `s0:(C,FFI)bvi_state`] THEN STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM `ty_rel env (match LAST1 (scan_expr_list ts loc a0) with
                                         NONE -> ts | SOME c -> FST c)`) MP_TAC THENL
   [BVITAILAUX_OPTION_CASES_TAC `LAST1 (scan_expr_list ts loc a0)`
      `c:v_ty list # v_ty # bool # assoc_op option` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ty_rel env o (FST:v_ty list # v_ty # bool # assoc_op option -> v_ty list)`;
                   `scan_expr_list ts loc a0`;
                   `c:v_ty list # v_ty # bool # assoc_op option`]
                  (GEN `P:A->bool` EVERY_LAST1)) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SPEC_TAC(CASE_TERM `match LAST1 (scan_expr_list ts loc a0) with NONE -> ts | SOME c -> FST c`,
           `tr:v_ty list`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `ty_rel (APPEND a env) (APPEND (MAP (FST o SND) (scan_expr_list ts loc a0)) tr)`
    ASSUME_TAC THENL [MATCH_MP_TAC ty_rel_APPEND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BVITAILAUX_USE_IH "i1" [`APPEND (MAP (FST o SND) (scan_expr_list ts loc a0)) tr`; `loc:num`;
    `APPEND a env:bvl_v list`; `s0:(C,FFI)bvi_state`; `vs:bvl_v list`; `t:(C,FFI)bvi_state`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (scan_expr_list ts loc a0) = LENGTH (a:bvl_v list)` SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ty_rel_def]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP LIST_REL_LENGTH o
      check (fun th -> rand(concl th) = `MAP (FST o SND) (scan_expr_list ts loc a0)`)) THEN
    REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC BVITAILAUX_ty_rel_DROP THEN ASM_REWRITE_TAC[];;

let BVITAILAUX_STR_NoRval_TAC (tm:term) : tactic =
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC tm `r0:bvi_result` `s0:(C,FFI)bvi_state` THEN
  CASES_ON `r0:bvi_result` THEN CASE_REWRITE_TAC[];;

let BVITAILAUX_STR_Tick_TAC : tactic =
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "i0") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN DISCH_TAC THEN
  REWRITE_TAC[scan_expr_sing_def] THEN
  BVITAILAUX_USE_IH "i0" [`ts:v_ty list`; `loc:num`; `env:bvl_v list`;
    `bvi_dec_clock 1 (s:(C,FFI)bvi_state)`; `vs:bvl_v list`; `t:(C,FFI)bvi_state`] THEN
  REWRITE_TAC[];;

let BVITAILAUX_STR_Any_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN REWRITE_TAC[scan_expr_sing_def; BVITAILAUX_ty_rel_SING] THEN
  ASM_REWRITE_TAC[distinctness "v_ty"] THEN BVITAILAUX_ty_rel_Any_TAC;;

let BVITAILAUX_STR_Force_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_evaluate_Force_Rval) THEN
  SUBGOAL_THEN `(if a1 < LENGTH ts then EL a1 ts else bvi_tailrec_Any) = bvi_tailrec_Any`
    SUBST1_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`env:bvl_v list`; `ts:v_ty list`; `a1:num`] BVITAILAUX_ty_rel_EL) THEN
    ASM_REWRITE_TAC[distinctness "bvl_v"; bvl_v_to_list_def; option_DISTINCT] THEN
    CASES_ON `EL a1 (ts:v_ty list)` THEN REWRITE_TAC[distinctness "v_ty"];
    BVITAILAUX_ty_rel_Any_TAC];;

let BVITAILAUX_STR_Op_TAC : tactic =
  GEN_TAC THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (a1,env,s:(C,FFI)bvi_state)`
    `r0:bvi_result` `s0:(C,FFI)bvi_state` THEN
  CASES_ON `r0:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `bvi_do_app a0 (REVERSE a) (s0:(C,FFI)bvi_state)` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_CASES_TAC `from_op a0 = Noop` THENL
   [REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [CASES_ON `get_bin_args (bvi_Op a0 a1)` THEN CASE_REWRITE_TAC[] THENL
       [COND_CASES_TAC THEN ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN
        FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITAILAUX_is_const_eq] o
          check (can (find_term ((=) `bvi_tailrec_is_const`)) o concl)) THEN RVEQ_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP BVITAILAUX_do_app_Const_Rval) THEN MESON_TAC[];
        BVITAILAUX_PAIR_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN
        FIRST_ASSUM(MP_TAC o REWRITE_RULE[get_bin_args_SOME] o check BVITAILAUX_is_gba) THEN
        REWRITE_TAC[PAIR_EQ; injectivity "bvi_exp"] THEN STRIP_TAC THEN RVEQ_TAC THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_evaluate_two o check BVITAILAUX_is_eval) THEN
        STRIP_TAC THEN RVEQ_TAC THEN
        MP_TAC(ISPECL [`op:clos_op`; `REVERSE [vx; vy:bvl_v]`; `s0:(C,FFI)bvi_state`;
                       `v:bvl_v`; `t:(C,FFI)bvi_state`] BVITAILAUX_do_app_arg_Int) THEN
        ASM_REWRITE_TAC[REVERSE; APPEND; ALL] THEN STRIP_TAC THEN
        MATCH_MP_TAC BVITAILAUX_ty_rel_update_context THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "bvi_exp"]) THEN
        ASM_MESON_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"]];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(MP_TAC o check BVITAILAUX_is_eval) THEN
      REWRITE_TAC[bvi_evaluate_def; PAIR_EQ; injectivity "result"] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "bvi_do_app")) (concl th))) THEN
      REWRITE_TAC[BVITAILAUX_do_app_Cons; injectivity "result"; PAIR_EQ; REVERSE] THEN
      STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[bvl_v_to_list_def; nil_tag_def] THEN
      MESON_TAC[]];
    MP_TAC(ISPECL [`a0:clos_op`; `REVERSE (a:bvl_v list)`; `s0:(C,FFI)bvi_state`; `v:bvl_v`;
                   `t:(C,FFI)bvi_state`] BVITAILAUX_do_app_from_op) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
    CASES_ON `from_op a0` THEN RULE_ASSUM_TAC(REWRITE_RULE[distinctness "assoc_op"]) THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN
    CASES_ON `get_bin_args (bvi_Op a0 a1)` THEN
    ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN
    BVITAILAUX_PAIR_TAC THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[get_bin_args_SOME] o check BVITAILAUX_is_gba) THEN
    REWRITE_TAC[PAIR_EQ; injectivity "bvi_exp"] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_evaluate_two o check BVITAILAUX_is_eval) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REVERSE; APPEND; ALL]) THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[GSYM BVITAILAUX_ty_rel_SING]]) THEN
    MATCH_MP_TAC BVITAILAUX_ty_rel_update_context THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "bvi_exp"]) THEN
    ASM_MESON_TAC[]];;

let BVITAILAUX_STR_Nil_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def; scan_expr_sing_def; PAIR_EQ;
    injectivity "result"; ALL; MAP] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ty_rel_def; ALL2];;

let BVITAILAUX_STR_Cons_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i0") (LABEL_TAC "i1")) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([a0],env,s:(C,FFI)bvi_state)`
    `r0:bvi_result` `s0:(C,FFI)bvi_state` THEN
  CASES_ON `r0:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (a1,env,s0:(C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[ALL; MAP; o_THM] THEN
  MP_TAC(ISPECL [`a0:bvi_exp`; `env:bvl_v list`; `s:(C,FFI)bvi_state`; `a:bvl_v list`;
                 `s0:(C,FFI)bvi_state`] evaluate_SING_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC) THEN
  REWRITE_TAC[HD; BVITAILAUX_ty_rel_CONS] THEN
  BVITAILAUX_USE_IH "i0" [`ts:v_ty list`; `loc:num`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
    `[w:bvl_v]`; `s0:(C,FFI)bvi_state`] THEN
  REWRITE_TAC[BVITAILAUX_ty_rel_SING] THEN STRIP_TAC THEN
  BVITAILAUX_USE_IH "i1" [`FST (scan_expr_sing ts loc a0)`; `loc:num`; `env:bvl_v list`;
    `s0:(C,FFI)bvi_state`; `a':bvl_v list`; `t:(C,FFI)bvi_state`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[];;

let BVITAILAUX_STR_Var_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_evaluate_Var_Rval) THEN RVEQ_TAC THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `a < LENGTH (ts:v_ty list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ty_rel_def; LIST_REL_LENGTH]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BVITAILAUX_ty_rel_SING] THEN
  MP_TAC(SPECL [`env:bvl_v list`; `ts:v_ty list`; `a:num`] BVITAILAUX_ty_rel_EL) THEN
  ASM_REWRITE_TAC[];;

let BVITAILAUX_scan_expr_ty_rel = prove
 (`(!e ts loc env (s:(C,FFI)bvi_state) vs t.
      ty_rel env ts /\ bvi_evaluate ([e],env,s) = (Rval vs,t) ==>
      ty_rel env (FST (scan_expr_sing ts loc e)) /\
      ty_rel vs [FST (SND (scan_expr_sing ts loc e))]) /\
   (!l ts loc env (s:(C,FFI)bvi_state) vs t.
      ty_rel env ts /\ bvi_evaluate (l,env,s) = (Rval vs,t) ==>
      ALL (ty_rel env o FST) (scan_expr_list ts loc l) /\
      ty_rel vs (MAP (FST o SND) (scan_expr_list ts loc l)))`,
  MATCH_MP_TAC BVIPAUX_TR_exp_induct THEN REPEAT CONJ_TAC THENL
   [BVITAILAUX_STR_Var_TAC; BVITAILAUX_STR_If_TAC; BVITAILAUX_STR_Let_TAC;
    BVITAILAUX_STR_NoRval_TAC `bvi_evaluate ([a],env,s:(C,FFI)bvi_state)`;
    BVITAILAUX_STR_Tick_TAC; BVITAILAUX_STR_Any_TAC; BVITAILAUX_STR_Force_TAC;
    BVITAILAUX_STR_Op_TAC; BVITAILAUX_STR_Any_TAC;
    BVITAILAUX_STR_NoRval_TAC `bvi_evaluate (a,env,s:(C,FFI)bvi_state)`;
    BVITAILAUX_STR_Nil_TAC; BVITAILAUX_STR_Cons_TAC]);;

let scan_expr_ty_rel = prove
 (`!ts loc xs env ys (s:(C,FFI)bvi_state) vs t.
     ty_rel env ts /\ scan_expr ts loc xs = ys /\
     bvi_evaluate (xs,env,s) = (Rval vs,t) ==>
     ALL (ty_rel env o FST) ys /\ ty_rel vs (MAP (FST o SND) ys)`,
  REWRITE_TAC[CONJUNCT2 scan_expr_eq] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)) THEN
  MATCH_MP_TAC(CONJUNCT2 BVITAILAUX_scan_expr_ty_rel) THEN
  MAP_EVERY EXISTS_TAC [`s:(C,FFI)bvi_state`; `t:(C,FFI)bvi_state`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* check_op, rewrite and scan_expr.                                          *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_try_swap = prove
 (`!loc opr exp.
     try_swap loc opr exp = exp \/
     ?l r. exp = bvi_Op (to_op opr) [l; r] /\ bvi_tailrec_is_rec loc l /\
           try_swap loc opr exp = bvi_Op (to_op opr) [r; l]`,
  REPEAT GEN_TAC THEN CASES_ON `opr:assoc_op` THEN REWRITE_TAC[try_swap_def] THEN
  REPEAT(FIRST [BVITAILAUX_PAIR_TAC; TOP_CASE_TAC]) THEN
  REWRITE_TAC[apply_op_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[opbinargs_SOME; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  TRY(FIRST_X_ASSUM(X_CHOOSE_THEN `x:bvi_exp` (X_CHOOSE_THEN `y:bvi_exp` STRIP_ASSUME_TAC) o
        check (is_exists o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RVEQ_TAC THEN ASM_MESON_TAC[]);;

let check_op_thm = prove
 (`check_op ts opr loc exp = SOME expr ==>
   ?x y. bvi_tailrec_is_rec loc x /\ term_ok ts (op_type opr) y /\
         expr = bvi_Op (to_op opr) [y; x] /\
         (exp = bvi_Op (to_op opr) [x; y] \/ exp = bvi_Op (to_op opr) [y; x])`,
  REWRITE_TAC[check_op_def] THEN
  CASES_ON `opbinargs opr (try_swap loc opr exp)` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_PAIR_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[opbinargs_SOME; PAIR_EQ] o
    check (fun th -> can (find_term ((=) `opbinargs`)) (concl th))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(SPECL [`loc:num`; `opr:assoc_op`; `exp:bvi_exp`] BVITAILAUX_try_swap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`y:bvi_exp`; `x:bvi_exp`] THEN ASM_REWRITE_TAC[apply_op_def];
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "bvi_exp"; CONS_11]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`l:bvi_exp`; `r:bvi_exp`] THEN
    ASM_REWRITE_TAC[apply_op_def]]);;

(* HOL4 proves from_op_to_op further down; it is needed here *)

let from_op_to_op = prove
 (`from_op (to_op opr) = opr`,
  CASES_ON `opr:assoc_op` THEN REWRITE_TAC[from_op_def; to_op_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [from_op_to_op];;

let BVITAILAUX_check_op_SOME = prove
 (`!ts opr loc exp e. check_op ts opr loc exp = SOME e ==>
     ~(opr = Noop) /\ ?xs. exp = bvi_Op (to_op opr) xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[check_op_def] THEN
    CASES_ON `opbinargs opr (try_swap loc opr exp)` THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[opbinargs_SOME] o
      check (fun th -> can (find_term ((=) `opbinargs`)) (concl th))) THEN SIMP_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP check_op_thm) THEN ASM_MESON_TAC[]]);;

let BVITAILAUX_check_op_from_op = prove
 (`!ts opr loc op xs e. check_op ts opr loc (bvi_Op op xs) = SOME e ==> from_op op = opr`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BVITAILAUX_check_op_SOME) THEN
  REWRITE_TAC[injectivity "bvi_exp"] THEN STRIP_TAC THEN ASM_REWRITE_TAC[from_op_to_op]);;

let BVITAILAUX_check_op_NONE = prove
 (`!ts opr loc exp. (!xs. ~(exp = bvi_Op (to_op opr) xs)) ==> check_op ts opr loc exp = NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  BVITAILAUX_OPTION_CASES_TAC `check_op ts opr loc exp` `e:bvi_exp` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_check_op_SOME) THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_RSE_NOTOP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[rewrite_def; scan_expr_sing_def] THEN
  CASE_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
                         (try fst(dest_const(fst(strip_comb t))) = "check_op"
                          with Failure _ -> false)) w in
    SUBGOAL_THEN (mk_eq(t,`NONE:bvi_exp option`)) SUBST1_TAC THENL
     [MATCH_MP_TAC BVITAILAUX_check_op_NONE THEN REWRITE_TAC[distinctness "bvi_exp"];
      CASE_REWRITE_TAC[]]);;

let BVITAILAUX_IS_SOME_NONE_TAC : tactic =
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `IS_SOME:bvi_exp option->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[IS_SOME_DEF];;

let BVITAILAUX_RSE_If_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i3") (LABEL_TAC "i2")) THEN
  DISCH_TAC THEN
  REWRITE_TAC[rewrite_def; scan_expr_sing_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; HD] THEN
  SPEC_TAC(`FST (scan_expr_sing ts loc x1)`, `t1:v_ty list`) THEN GEN_TAC THEN
  REMOVE_THEN "i2" (MP_TAC o SPEC `t1:v_ty list`) THEN
  REMOVE_THEN "i3" (MP_TAC o SPECL [`FST (rewrite loc next opr acc t1 x2)`;
                                 `SND (rewrite loc next opr acc t1 x2)`; `t1:v_ty list`]) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN MESON_TAC[];;

let BVITAILAUX_RSE_Let_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THEN
  REWRITE_TAC[rewrite_def; scan_expr_sing_def; LET_DEF; LET_END_DEF;
              pair_CASE_def; CONJUNCT2 scan_expr_eq] THEN BETA_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let BVITAILAUX_RSE_Tick_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THEN
  REWRITE_TAC[rewrite_def; scan_expr_sing_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let BVITAILAUX_RSE_Op_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rewrite_def; scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
  BVITAILAUX_OPTION_CASES_TAC `check_op ts opr loc (bvi_Op v21 v22)` `e:bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_check_op_from_op) THEN
    SUBGOAL_THEN `?y x. opbinargs opr e = SOME (y,x)` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP check_op_thm) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[opbinargs_SOME; PAIR_EQ; injectivity "bvi_exp"; CONS_11] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN TRY BVITAILAUX_PAIR_TAC THEN
    REWRITE_TAC[] THEN
    CASES_ON `opr:assoc_op` THEN RULE_ASSUM_TAC(REWRITE_RULE[distinctness "assoc_op"]) THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[IS_SOME_DEF] THEN CASE_REWRITE_TAC[];
    CASES_ON `from_op v21` THEN CASE_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN CASE_REWRITE_TAC[]) THEN
    REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[]) THEN
    BVITAILAUX_IS_SOME_NONE_TAC];;

let BVITAILAUX_rewrite_scan_expr = prove
 (CASE_TERM `!x1 x2 x3 x4 x5 x6. ~(x3 = Noop) ==>
     match SND (SND (SND (scan_expr_sing x5 x1 x6))) with
       SOME op1 -> (x3 = op1 ==> FST (rewrite x1 x2 x3 x4 x5 x6))
     | NONE -> ~FST (rewrite x1 x2 x3 x4 x5 x6)`,
  MATCH_MP_TAC rewrite_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rewrite_def; scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[];
    BVITAILAUX_RSE_If_TAC; BVITAILAUX_RSE_Let_TAC; BVITAILAUX_RSE_Tick_TAC;
    REWRITE_TAC[rewrite_def; scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[];
    BVITAILAUX_RSE_NOTOP_TAC; BVITAILAUX_RSE_NOTOP_TAC; BVITAILAUX_RSE_Op_TAC;
    BVITAILAUX_RSE_NOTOP_TAC; BVITAILAUX_RSE_NOTOP_TAC]);;

let rewrite_scan_expr = prove
 (CASE_TERM
  `!loc next op acc ts exp tt ty p exp2 r opr.
     rewrite loc next op acc ts exp = (p,exp2) /\ ~(op = Noop) /\
     scan_expr ts loc [exp] = [(tt,ty,r,opr)] ==>
     match opr with
       SOME op1 -> (op = op1 ==> p)
     | NONE -> ~p`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; CONS_11] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`loc:num`; `next:num`; `op:assoc_op`; `acc:num`; `ts:v_ty list`;
                `exp:bvi_exp`] BVITAILAUX_rewrite_scan_expr) THEN
  ASM_REWRITE_TAC[]);;

let BVITAILAUX_decide_ty_eq = prove
 (`!a b. ~(decide_ty a b = bvi_tailrec_Any) ==> a = decide_ty a b /\ b = decide_ty a b`,
  REPEAT GEN_TAC THEN CASES_ON `a:v_ty` THEN CASES_ON `b:v_ty` THEN
  REWRITE_TAC[decide_ty_def] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_if_op_type = prove
 (CASE_TERM
  `!ot oe ty1 ty2.
     match (match ot with NONE -> oe | SOME a -> ot) with
       SOME op ->
         (~((match (match ot with NONE -> oe | SOME a -> ot) with
               NONE -> decide_ty ty1 ty2
             | SOME opr -> decide_ty ty1 (decide_ty ty2 (op_type opr))) = bvi_tailrec_Any) ==>
          op_type op =
          (match (match ot with NONE -> oe | SOME a -> ot) with
             NONE -> decide_ty ty1 ty2
           | SOME opr -> decide_ty ty1 (decide_ty ty2 (op_type opr))))
     | NONE -> T`,
  REPEAT GEN_TAC THEN CASES_ON `ot:assoc_op option` THEN CASES_ON `oe:assoc_op option` THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[BVITAILAUX_decide_ty_eq]);;

let BVITAILAUX_scan_expr_op_type = prove
 (CASE_TERM
  `(!e ts loc. match SND (SND (SND (scan_expr_sing ts loc e))) with
                 SOME op -> (~(FST (SND (scan_expr_sing ts loc e)) = bvi_tailrec_Any) ==>
                             op_type op = FST (SND (scan_expr_sing ts loc e)))
               | NONE -> T) /\
   (!l ts loc. ALL (\p. match SND (SND (SND p)) with
                          SOME op -> (~(FST (SND p) = bvi_tailrec_Any) ==>
                                      op_type op = FST (SND p))
                        | NONE -> T) (scan_expr_list ts loc l))`,
  MATCH_MP_TAC BVIPAUX_TR_exp_induct THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND; ALL] THEN CASE_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_ACCEPT_TAC BVITAILAUX_if_op_type) THEN
  REPEAT GEN_TAC THEN CASES_ON `from_op a0` THEN CASE_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN CASE_REWRITE_TAC[]) THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[]) THEN REWRITE_TAC[]);;

let scan_expr_op_type = prove
 (CASE_TERM
  `!ts loc xs ys.
     scan_expr ts loc xs = ys ==>
     ALL (\(tt,ty,r,opr). match opr with
                            SOME op -> (~(ty = bvi_tailrec_Any) ==> op_type op = ty)
                          | NONE -> T) ys`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CONJUNCT2 scan_expr_eq] THEN
  MP_TAC(SPECL [`xs:bvi_exp list`; `ts:v_ty list`; `loc:num`]
               (CONJUNCT2 BVITAILAUX_scan_expr_op_type)) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* optimized_code and the properties of compile_each.                        *)
(* ------------------------------------------------------------------------- *)

let optimized_code_def = cake_def
  `optimized_code loc arity exp n c op <=>
     ?exp_aux exp_opt.
       bvi_tailrec_compile_exp loc n arity exp = SOME (exp_aux,exp_opt) /\
       check_exp loc arity exp = SOME op /\
       lookup loc c = SOME (arity,exp_aux) /\
       lookup n c = SOME (arity + 1,exp_opt)`;;

let code_rel_subspt = prove
 (`bvi_tailrecProof_code_rel c1 x1 /\ subspt x1 x2 ==> bvi_tailrecProof_code_rel c1 x2`,
  REWRITE_TAC[bvi_tailrecProof_code_rel_def; subspt_lookup] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let bvi_tailrecProof_compile_each_LENGTH = prove
 (`!n prog. LENGTH (SND (bvi_tailrec_compile_each n prog)) >= LENGTH prog`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvi_tailrec_compile_each_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `p:bvi_exp#bvi_exp` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[LENGTH] THEN RES_TAC THEN ASM_ARITH_TAC);;

let bvi_tailrecProof_free_names_def = cake_def
  `bvi_tailrecProof_free_names n (name:num) <=>
     !k. ~(n + bvl_to_bvi_namespaces * k = name)`;;

(* HOL4 [local] *)
let bvi_tailrecProof_more_free_names = prove
 (`bvi_tailrecProof_free_names n name ==>
   bvi_tailrecProof_free_names (n + bvl_to_bvi_namespaces) name`,
  REWRITE_TAC[bvi_tailrecProof_free_names_def] THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

(* HOL4 [local] *)
let bvi_tailrecProof_is_free_name = prove
 (`bvi_tailrecProof_free_names n name ==> ~(n = name)`,
  REWRITE_TAC[bvi_tailrecProof_free_names_def] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* HOL4 [local] *)
let bvi_tailrecProof_compile_exp_next_addr = prove
 (`bvi_tailrec_compile_exp loc next args exp = NONE ==>
   bvi_tailrec_compile_exp loc (next + bvl_to_bvi_namespaces) args exp = NONE`,
  REWRITE_TAC[BVITAILAUX_compile_exp_NONE]);;

(* assume the conjuncts of an antecedent, keeping the last one in the goal *)
let BVITAILAUX_DISCH_CONJS : tactic =
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC));;

let bvi_tailrecProof_compile_each_untouched = prove
 (`!next prog prog2 loc exp arity.
     bvi_tailrecProof_free_names next loc /\
     lookup loc (fromAList prog) = SOME (arity,exp) /\
     check_exp loc arity exp = NONE /\
     bvi_tailrec_compile_exp loc next arity exp = NONE /\
     bvi_tailrec_compile_each next prog = (next1,prog2) ==>
     lookup loc (fromAList prog2) = SOME (arity,exp)`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[fromAList_def; lookup_def; option_DISTINCT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`next:num`; `loc':num`; `arity':num`; `exp':bvi_exp`;
                       `xs:(num#num#bvi_exp)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "is") (LABEL_TAC "in")) THEN
  MAP_EVERY X_GEN_TAC [`prog2:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                       `arity:num`] THEN
  REWRITE_TAC[fromAList_def; lookup_insert; bvi_tailrec_compile_each_def] THEN
  ASM_CASES_TAC `loc:num = loc'` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN BVITAILAUX_DISCH_CONJS THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN BVITAILAUX_PAIR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[fromAList_def; lookup_insert];
    ALL_TAC] THEN
  BVITAILAUX_DISCH_CONJS THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc' next arity' exp'`
    `p:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[fromAList_def; lookup_insert] THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(loc:num = next)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[bvi_tailrecProof_is_free_name]; ALL_TAC] THEN
    REMOVE_THEN "is" (MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ys:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                               `arity:num`]) THEN
    ASM_SIMP_TAC[bvi_tailrecProof_more_free_names; bvi_tailrecProof_compile_exp_next_addr];
    REMOVE_THEN "in" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ys:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                               `arity:num`]) THEN ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)
let bvi_tailrecProof_EVERY_free_names_SUCSUC = prove
 (`!xs:(num#A)list.
     ALL (bvi_tailrecProof_free_names n o FST) xs ==>
     ALL (bvi_tailrecProof_free_names (n + bvl_to_bvi_namespaces) o FST) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; o_THM] THEN
  ASM_MESON_TAC[bvi_tailrecProof_more_free_names]);;

let bvi_tailrecProof_compile_each_touched = prove
 (`!next prog prog2 loc exp arity.
     ALL_DISTINCT (MAP FST prog) /\
     ALL (bvi_tailrecProof_free_names next o FST) prog /\
     bvi_tailrecProof_free_names next loc /\
     lookup loc (fromAList prog) = SOME (arity,exp) /\
     check_exp loc arity exp = SOME op /\
     bvi_tailrec_compile_each next prog = (next1,prog2) ==>
     ?k. !exp_aux exp_opt.
       bvi_tailrec_compile_exp loc (next + bvl_to_bvi_namespaces * k) arity exp =
         SOME (exp_aux,exp_opt) ==>
       lookup loc (fromAList prog2) = SOME (arity,exp_aux) /\
       lookup (next + bvl_to_bvi_namespaces * k) (fromAList prog2) =
         SOME (arity + 1,exp_opt)`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[fromAList_def; lookup_def; option_DISTINCT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`next:num`; `loc':num`; `arity':num`; `exp':bvi_exp`;
                       `xs:(num#num#bvi_exp)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "is") (LABEL_TAC "in")) THEN
  MAP_EVERY X_GEN_TAC [`prog2:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                       `arity:num`] THEN
  REWRITE_TAC[fromAList_def; lookup_insert; bvi_tailrec_compile_each_def; MAP; ALL;
              ALL_DISTINCT; o_THM] THEN
  ASM_CASES_TAC `loc:num = loc'` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN BVITAILAUX_DISCH_CONJS THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl)) THEN
    MP_TAC(SPECL [`loc':num`; `next:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]
                 BVITAILAUX_compile_exp_SOME) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[fromAList_def; lookup_insert] THEN
    SUBGOAL_THEN `~(next:num = loc')` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[bvi_tailrecProof_is_free_name];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN BVITAILAUX_DISCH_CONJS THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc' next arity' exp'`
    `p:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [REMOVE_THEN "is" (MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ys:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                               `arity:num`]) THEN
    ASM_SIMP_TAC[bvi_tailrecProof_more_free_names;
                 bvi_tailrecProof_EVERY_free_names_SUCSUC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k + 1` THEN
    REWRITE_TAC[fromAList_def; lookup_insert] THEN
    SUBGOAL_THEN `next + bvl_to_bvi_namespaces * (k + 1) =
                  (next + bvl_to_bvi_namespaces) + bvl_to_bvi_namespaces * k`
      SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((next + bvl_to_bvi_namespaces) + bvl_to_bvi_namespaces * k = loc') /\
                  ~((next + bvl_to_bvi_namespaces) + bvl_to_bvi_namespaces * k = next) /\
                  ~(loc = next)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `k + 1` o REWRITE_RULE[bvi_tailrecProof_free_names_def] o
          check (fun th -> concl th = `bvi_tailrecProof_free_names next loc'`)) THEN
        ARITH_TAC;
        REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC;
        ASM_MESON_TAC[bvi_tailrecProof_is_free_name]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "in" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ys:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                               `arity:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN
    REWRITE_TAC[fromAList_def; lookup_insert] THEN
    SUBGOAL_THEN `~(next + bvl_to_bvi_namespaces * k = loc')`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[bvi_tailrecProof_free_names_def]]);;

(* HOL4 [local] *)
let check_exp_NONE_compile_exp = prove
 (`check_exp loc arity exp = NONE ==> bvi_tailrec_compile_exp loc next arity exp = NONE`,
  REWRITE_TAC[BVITAILAUX_compile_exp_NONE]);;

(* HOL4 [local] *)
let check_exp_SOME_compile_exp = prove
 (`check_exp loc arity exp = SOME p ==> ?q. bvi_tailrec_compile_exp loc next arity exp = SOME q`,
  MESON_TAC[BVITAILAUX_compile_exp_SOME]);;

(* HOL4 [local] *)
let bvi_tailrecProof_EVERY_free_names_thm = prove
 (`ALL (bvi_tailrecProof_free_names next o FST) (prog:(num#A)list) /\
   lookup loc (fromAList prog) = SOME x ==>
   bvi_tailrecProof_free_names next loc`,
  REWRITE_TAC[lookup_fromAList; GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(loc,x):num#A`) THEN ASM_REWRITE_TAC[o_THM; FST]);;

let bvi_tailrecProof_compile_each_code_rel = prove
 (`bvi_tailrec_compile_each next prog = (next1,prog2) /\
   ALL_DISTINCT (MAP FST prog) /\
   ALL (bvi_tailrecProof_free_names next o FST) prog ==>
   bvi_tailrecProof_code_rel (fromAList prog) (fromAList prog2)`,
  REWRITE_TAC[bvi_tailrecProof_code_rel_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bvi_tailrecProof_free_names next loc` ASSUME_TAC THEN
  TRY(ASM_MESON_TAC[bvi_tailrecProof_EVERY_free_names_thm] THEN NO_TAC) THENL
   [MATCH_MP_TAC bvi_tailrecProof_compile_each_untouched THEN
    MAP_EVERY EXISTS_TAC [`next:num`; `prog:(num#num#bvi_exp)list`] THEN
    ASM_SIMP_TAC[check_exp_NONE_compile_exp];
    MP_TAC(SPECL [`next:num`; `prog:(num#num#bvi_exp)list`; `prog2:(num#num#bvi_exp)list`;
                  `loc:num`; `exp:bvi_exp`; `arity:num`]
           bvi_tailrecProof_compile_each_touched) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    EXISTS_TAC `next + bvl_to_bvi_namespaces * k` THEN ASM_REWRITE_TAC[]]);;

let bvi_tailrecProof_compile_each_next_mono = prove
 (`!n xs n1 ys. bvi_tailrec_compile_each n xs = (n1,ys) ==>
                ?k. n1 = n + bvl_to_bvi_namespaces * k`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "is") (LABEL_TAC "in")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_each_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `p:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [REMOVE_THEN "is" (MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n1:num`; `ys':(num#num#bvi_exp)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    EXISTS_TAC `k + 1` THEN ARITH_TAC;
    REMOVE_THEN "in" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`n1:num`; `ys':(num#num#bvi_exp)list`]) THEN
    ASM_REWRITE_TAC[]]);;

let bvi_tailrecProof_compile_prog_next_mono = prove
 (`!b n xs n1 ys. bvi_tailrec_compile_prog b n xs = (n1,ys) ==>
                  ?k. n1 = n + bvl_to_bvi_namespaces * k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_prog_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[bvi_tailrecProof_compile_each_next_mono] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC);;

let BVITAILAUX_compile_each_MEM = prove
 (`!n xs n1 ys e.
     bvi_tailrec_compile_each n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
     MEM e (MAP FST xs) \/
     (n <= e /\ e < n1 /\ ?k. e = n + k * bvl_to_bvi_namespaces)`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; MEM]) THEN
    FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "is") (LABEL_TAC "in")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_each_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `p:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; MEM]) THEN REWRITE_TAC[MAP; MEM] THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
     [DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP bvi_tailrecProof_compile_each_next_mono o
        check (fun th -> can (find_term ((=) `bvi_tailrec_compile_each`)) (concl th) &&
                         not (is_forall (concl th)) && not (is_imp (concl th)))) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
       [REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC;
        EXISTS_TAC `0` THEN ARITH_TAC];
      REMOVE_THEN "is" (MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`n1:num`; `ys':(num#num#bvi_exp)list`; `e:num`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN EXISTS_TAC `k + 1` THEN ASM_ARITH_TAC];
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[] THEN
    REMOVE_THEN "in" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`n1:num`; `ys':(num#num#bvi_exp)list`; `e:num`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let bvi_tailrecProof_compile_each_MEM = prove
 (`bvi_tailrec_compile_each n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/
   (n <= e /\ e < n1 /\ ?k. e = n + k * bvl_to_bvi_namespaces)`,
  MESON_TAC[BVITAILAUX_compile_each_MEM]);;

let bvi_tailrecProof_compile_prog_MEM = prove
 (`bvi_tailrec_compile_prog b n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/
   (n <= e /\ e < n1 /\ ?k. e = n + k * bvl_to_bvi_namespaces)`,
  REWRITE_TAC[bvi_tailrec_compile_prog_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[bvi_tailrecProof_compile_each_MEM; PAIR_EQ] THEN MESON_TAC[]);;

let BVITAILAUX_compile_each_intro = prove
 (`!n xs ys n1 name.
     ~MEM name (MAP FST xs) /\ bvi_tailrecProof_free_names n name /\
     bvi_tailrec_compile_each n xs = (n1,ys) ==>
     ~MEM name (MAP FST ys) /\ bvi_tailrecProof_free_names n1 name`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[MAP; MEM];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "is") (LABEL_TAC "in")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_each_def; MAP; MEM; DE_MORGAN_THM] THEN
  BVITAILAUX_DISCH_CONJS THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `p:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP; MEM; DE_MORGAN_THM] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THENL
   [REMOVE_THEN "is" (MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ys':(num#num#bvi_exp)list`; `n1:num`; `name:num`]) THEN
    ASM_SIMP_TAC[bvi_tailrecProof_more_free_names] THEN
    ASM_MESON_TAC[bvi_tailrecProof_is_free_name];
    REMOVE_THEN "in" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ys':(num#num#bvi_exp)list`; `n1:num`; `name:num`]) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)
let bvi_tailrecProof_compile_each_intro = prove
 (`!xs n ys n1 name.
     ~MEM name (MAP FST xs) /\ bvi_tailrecProof_free_names n name /\
     bvi_tailrec_compile_each n xs = (n1,ys) ==>
     ~MEM name (MAP FST ys) /\ bvi_tailrecProof_free_names n1 name`,
  MESON_TAC[BVITAILAUX_compile_each_intro]);;

let BVITAILAUX_compile_each_ALL_DISTINCT = prove
 (`!n xs n1 ys.
     bvi_tailrec_compile_each n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
     ALL (bvi_tailrecProof_free_names n o FST) xs ==>
     ALL_DISTINCT (MAP FST ys) /\ ALL (bvi_tailrecProof_free_names n1 o FST) ys`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[MAP; ALL; ALL_DISTINCT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "is") (LABEL_TAC "in")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_tailrec_compile_each_def; MAP; ALL; ALL_DISTINCT; o_THM] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `p:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT BVITAILAUX_PAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP; ALL; ALL_DISTINCT; o_THM; MEM; DE_MORGAN_THM] THENL
   [REMOVE_THEN "is" (MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`n1:num`; `ys':(num#num#bvi_exp)list`]) THEN
    ASM_SIMP_TAC[bvi_tailrecProof_EVERY_free_names_SUCSUC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`xs:(num#num#bvi_exp)list`; `next + bvl_to_bvi_namespaces`;
                  `ys':(num#num#bvi_exp)list`; `n1:num`; `loc:num`]
                 bvi_tailrecProof_compile_each_intro) THEN
    ASM_SIMP_TAC[bvi_tailrecProof_more_free_names] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `k:num` ASSUME_TAC o
      MATCH_MP bvi_tailrecProof_compile_each_next_mono o
      check (fun th -> can (find_term ((=) `bvi_tailrec_compile_each`)) (concl th) &&
                       not (is_forall (concl th)) && not (is_imp (concl th)))) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(MATCH_MP bvi_tailrecProof_is_free_name
        (ASSUME `bvi_tailrecProof_free_names next loc`)) THEN MESON_TAC[];
      DISCH_TAC THEN
      MP_TAC(SPECL [`next + bvl_to_bvi_namespaces`; `xs:(num#num#bvi_exp)list`; `n1:num`;
                    `ys':(num#num#bvi_exp)list`; `next:num`] BVITAILAUX_compile_each_MEM) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[bvl_to_bvi_namespaces_def; ARITH_RULE `~(n + 4 <= n)`] THEN
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN STRIP_TAC THEN
      UNDISCH_TAC `ALL (bvi_tailrecProof_free_names next o FST) (xs:(num#num#bvi_exp)list)` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(p1,p1',p2):num#num#bvi_exp`) THEN
      ASM_REWRITE_TAC[o_THM; FST] THEN
      DISCH_THEN(MP_TAC o MATCH_MP bvi_tailrecProof_is_free_name) THEN REWRITE_TAC[];
      ASM_REWRITE_TAC[bvi_tailrecProof_free_names_def] THEN
      REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC];
    REMOVE_THEN "in" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`n1:num`; `ys':(num#num#bvi_exp)list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`xs:(num#num#bvi_exp)list`; `next:num`; `ys':(num#num#bvi_exp)list`;
                  `n1:num`; `loc:num`] bvi_tailrecProof_compile_each_intro) THEN
    ASM_REWRITE_TAC[]]);;

let bvi_tailrecProof_compile_each_ALL_DISTINCT = prove
 (`bvi_tailrec_compile_each n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   ALL (bvi_tailrecProof_free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\ ALL (bvi_tailrecProof_free_names n1 o FST) ys`,
  MESON_TAC[BVITAILAUX_compile_each_ALL_DISTINCT]);;

let bvi_tailrecProof_compile_prog_ALL_DISTINCT = prove
 (`bvi_tailrec_compile_prog b n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   ALL (bvi_tailrecProof_free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\ ALL (bvi_tailrecProof_free_names n1 o FST) ys`,
  REWRITE_TAC[bvi_tailrec_compile_prog_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[bvi_tailrecProof_compile_each_ALL_DISTINCT; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* namespace_rel, input_condition and state_rel.                             *)
(* ------------------------------------------------------------------------- *)

let bvi_tailrecProof_namespace_rel_def = cake_def
  `bvi_tailrecProof_namespace_rel (c1:A spt) (c2:A spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==>
          if n MOD bvl_to_bvi_namespaces = 2 then ~(n IN domain c1) else n IN domain c1) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~(n MOD bvl_to_bvi_namespaces = 2)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;

let bvi_tailrecProof_input_condition_def = cake_def
  `bvi_tailrecProof_input_condition next (prog:(num#A)list) <=>
     ALL (bvi_tailrecProof_free_names next o FST) prog /\
     ALL_DISTINCT (MAP FST prog) /\
     ALL ((~) o (\n. n MOD bvl_to_bvi_namespaces = 2) o FST)
         (FILTER ((<=) bvl_num_stubs o FST) prog) /\
     bvl_num_stubs <= next /\ next MOD bvl_to_bvi_namespaces = 2`;;

let bvi_tailrecProof_state_rel_def = cake_def
  `bvi_tailrecProof_state_rel (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) <=>
     bvi_state_refs t = bvi_state_refs s /\
     bvi_state_clock t = bvi_state_clock s /\
     bvi_state_global t = bvi_state_global s /\
     bvi_state_ffi t = bvi_state_ffi s /\
     bvi_state_compile_oracle t =
       state_co bvi_tailrec_compile_each (bvi_state_compile_oracle s) /\
     bvi_state_compile s = state_cc bvi_tailrec_compile_each (bvi_state_compile t) /\
     bvi_tailrecProof_code_rel (bvi_state_code s) (bvi_state_code t) /\
     bvi_tailrecProof_namespace_rel (bvi_state_code s) (bvi_state_code t) /\
     (!n. let ((next,cfg),prog) = bvi_state_compile_oracle s n in
          bvi_tailrecProof_input_condition next prog) /\
     (!n. n IN domain (bvi_state_code t) /\ n MOD bvl_to_bvi_namespaces = 2 ==>
          n < FST (FST (bvi_state_compile_oracle s 0)))`;;

let bvi_tailrecProof_state_rel_const = prove
 (`bvi_tailrecProof_state_rel (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) ==>
   bvi_state_refs t = bvi_state_refs s /\ bvi_state_clock t = bvi_state_clock s /\
   bvi_state_global t = bvi_state_global s /\ bvi_state_ffi t = bvi_state_ffi s`,
  SIMP_TAC[bvi_tailrecProof_state_rel_def]);;

let bvi_tailrecProof_state_rel_with_clock = prove
 (`bvi_tailrecProof_state_rel (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) ==>
   bvi_tailrecProof_state_rel (bvi_state_clock_fupd (K k) s) (bvi_state_clock_fupd (K k) t)`,
  REWRITE_TAC[bvi_tailrecProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

let bvi_tailrecProof_state_rel_code_rel = prove
 (`bvi_tailrecProof_state_rel (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) ==>
   bvi_tailrecProof_code_rel (bvi_state_code s) (bvi_state_code t)`,
  SIMP_TAC[bvi_tailrecProof_state_rel_def]);;

let BVITAILAUX_lookup_union_SOME = prove
 (`!m1 m2 k (v:A). lookup k (sptree_union m1 m2) = SOME v <=>
               lookup k m1 = SOME v \/ (lookup k m1 = NONE /\ lookup k m2 = SOME v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union] THEN
  CASES_ON `lookup k (m1:A spt)` THEN CASE_REWRITE_TAC[]);;

let bvi_tailrecProof_code_rel_union = prove
 (`bvi_tailrecProof_code_rel x y /\ bvi_tailrecProof_code_rel t s /\
   DISJOINT (domain s) (domain y) ==>
   bvi_tailrecProof_code_rel (sptree_union x t) (sptree_union y s)`,
  REWRITE_TAC[bvi_tailrecProof_code_rel_def; BVITAILAUX_lookup_union_SOME;
              IN_DISJOINT; domain_lookup] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "x") (CONJUNCTS_THEN2 (LABEL_TAC "t")
    (LABEL_TAC "d"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [USE_THEN "x" (MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n") (LABEL_TAC "s")) THEN CONJ_TAC THEN
    DISCH_TAC THENL
     [DISJ1_TAC THEN REMOVE_THEN "n" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REMOVE_THEN "s" (MP_TAC o C MP (ASSUME `check_exp loc arity exp = SOME op`)) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `!k v. lookup k (s:(num#bvi_exp)spt) = SOME v ==>
                        lookup k (y:(num#bvi_exp)spt) = NONE` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "d" MP_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
      CASES_ON `lookup k (y:(num#bvi_exp)spt)` THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "t" (MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n") (LABEL_TAC "s")) THEN CONJ_TAC THEN
    DISCH_TAC THENL
     [DISJ2_TAC THEN REMOVE_THEN "n" MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REMOVE_THEN "s" (MP_TAC o C MP (ASSUME `check_exp loc arity exp = SOME op`)) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

let bvi_tailrecProof_namespace_rel_union = prove
 (`bvi_tailrecProof_namespace_rel (x:A spt) y /\ bvi_tailrecProof_namespace_rel t s /\
   DISJOINT (domain s) (domain y) ==>
   bvi_tailrecProof_namespace_rel (sptree_union x t) (sptree_union y s)`,
  REWRITE_TAC[bvi_tailrecProof_namespace_rel_def; domain_union; IN_UNION; IN_DISJOINT] THEN
  MESON_TAC[]);;

let BVITAILAUX_ns_MOD = prove
 (`!next k. (next + k * bvl_to_bvi_namespaces) MOD bvl_to_bvi_namespaces =
            next MOD bvl_to_bvi_namespaces`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let bvi_tailrecProof_compile_each_namespace_rel = prove
 (`bvi_tailrec_compile_each next prog = (next1,prog2) /\
   next MOD bvl_to_bvi_namespaces = 2 /\ bvl_num_stubs <= next /\
   ALL ((~) o (\n. n MOD bvl_to_bvi_namespaces = 2) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) ==>
   bvi_tailrecProof_namespace_rel (fromAList prog) (fromAList prog2)`,
  REWRITE_TAC[bvi_tailrecProof_namespace_rel_def; domain_fromAList; IN_SET_OF_LIST;
               GSYM ALL_MEM; MEM_FILTER; o_THM] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `!n. MEM n (MAP FST (prog2:(num#num#bvi_exp)list)) ==>
                     MEM n (MAP FST (prog:(num#num#bvi_exp)list)) \/
                     (next <= n /\ n < next1 /\ ?k. n = next + k * bvl_to_bvi_namespaces)`
     ASSUME_TAC THENL [ASM_MESON_TAC[bvi_tailrecProof_compile_each_MEM]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. MEM n (MAP FST (prog:(num#num#bvi_exp)list)) /\ bvl_num_stubs <= n ==>
                     ~(n MOD bvl_to_bvi_namespaces = 2)` ASSUME_TAC THENL
    [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `(p1,p1',p2):num#num#bvi_exp` o
       check (fun th -> can (find_term ((=) `bvl_num_stubs`)) (concl th) && is_forall (concl th))) THEN
     ASM_REWRITE_TAC[FST] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REPEAT CONJ_TAC THEN X_GEN_TAC `n:num` THEN STRIP_TAC THENL
    [COND_CASES_TAC THENL
      [ASM_MESON_TAC[];
       FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term ((=) `next1:num`)) (concl th))) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `~(n MOD bvl_to_bvi_namespaces = 2)` THEN ASM_REWRITE_TAC[BVITAILAUX_ns_MOD]];
     ASM_MESON_TAC[];
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term ((=) `next1:num`)) (concl th))) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let BVITAILAUX_state_rel_fupd = prove
 (`!(s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) r g.
     bvi_tailrecProof_state_rel s t ==>
     bvi_tailrecProof_state_rel (bvi_state_refs_fupd (K r) s) (bvi_state_refs_fupd (K r) t) /\
     bvi_tailrecProof_state_rel (bvi_state_global_fupd (K g) s)
                                (bvi_state_global_fupd (K g) t)`,
  REWRITE_TAC[bvi_tailrecProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

let state_rel_do_app_aux = prove
 (`bvi_do_app_aux op vs (s:(num#C,FFI)bvi_state) = res /\
   bvi_tailrecProof_state_rel s (t:(C,FFI)bvi_state) /\
   ~(op = clos_Install) /\ (!n. ~(op = clos_Label n)) ==>
   ?res'. bvi_do_app_aux op vs t = res' /\
          OPTREL (OPTREL ((=) ### bvi_tailrecProof_state_rel)) res res'`,
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const) THEN
  REWRITE_TAC[bvi_do_app_aux_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[OPTREL_THM; PAIR_REL_THM] THEN
  ASM_SIMP_TAC[BVITAILAUX_state_rel_fupd] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "clos_op"; BVITAILAUX_NOT_FORALL_NEQ]) THEN
  FIRST_ASSUM CONTR_TAC);;

let BVITAILAUX_state_rel_t_eq = prove
 (`!(s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state).
     bvi_tailrecProof_state_rel s t ==>
     bvi_state_refs_fupd (K (bvi_state_refs s))
       (bvi_state_clock_fupd (K (bvi_state_clock s))
         (bvi_state_global_fupd (K (bvi_state_global s))
           (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t))) = t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const) THEN
  REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let state_rel_do_app = prove
 (`bvi_do_app op vs (s:(num#C,FFI)bvi_state) = Rval (r,s') /\
   bvi_tailrecProof_state_rel s (t:(C,FFI)bvi_state) /\
   ~(op = clos_Install) /\ (!n. ~(op = clos_Label n)) ==>
   ?t'. bvi_do_app op vs t = Rval (r,t') /\ bvi_tailrecProof_state_rel s' t'`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:bvl_v list`; `s:(num#C,FFI)bvi_state`; `r:bvl_v`;
                 `s':(num#C,FFI)bvi_state`; `t:(C,FFI)bvi_state`;
                 `Rabort Rtype_error:(exn_or_ret)error_result`] do_app_cfg_swap) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[BVITAILAUX_state_rel_t_eq] THEN ANTS_TAC THENL
   [MATCH_MP_TAC bvi_tailrecProof_code_rel_domain THEN
    MATCH_MP_TAC bvi_tailrecProof_state_rel_code_rel THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  EXISTS_TAC `bvi_state_refs_fupd (K (bvi_state_refs (s':(num#C,FFI)bvi_state)))
                (bvi_state_clock_fupd (K (bvi_state_clock s'))
                  (bvi_state_global_fupd (K (bvi_state_global s'))
                    (bvi_state_ffi_fupd (K (bvi_state_ffi s')) (t:(C,FFI)bvi_state))))` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:bvl_v list`; `s:(num#C,FFI)bvi_state`; `r:bvl_v`;
                 `s':(num#C,FFI)bvi_state`] do_app_code) THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:bvl_v list`; `s:(num#C,FFI)bvi_state`; `r:bvl_v`;
                 `s':(num#C,FFI)bvi_state`] do_app_oracle) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `bvi_tailrecProof_state_rel s (t:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[bvi_tailrecProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let BVITAILAUX_bvl_do_app_frame_err = prove
 (`!op vs (s:(A,FFI)bvl_state) g c (cmp:B -> (num # num # bvl_exp) list ->
        (byte list # int64 list # B) option) orc cd e.
     ~(op = clos_Install) /\ (!n. ~(op = clos_Label n)) /\ ~BVLPROPSAUX_is_glob op /\
     bvl_do_app op vs s = Rerr e ==>
     bvl_do_app op vs
       (bvl_state_REC g (bvl_state_refs s) c cmp orc cd (bvl_state_ffi s)) = Rerr e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_is_glob] THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accessors; bvl_state_INFO.ri_fupds;
              K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ;
              distinctness "clos_op"; injectivity "clos_op"; BVITAILAUX_NOT_FORALL_NEQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_accessors; K_THM] THEN
  ASM_MESON_TAC[]);;
let BVITAILAUX_bvl_do_app_frame_err2 = prove
 (`!op vs (s:(A,FFI)bvl_state) g r c (cmp:B -> (num # num # bvl_exp) list ->
        (byte list # int64 list # B) option) orc cd f e.
     ~(op = clos_Install) /\ (!n. ~(op = clos_Label n)) /\ ~BVLPROPSAUX_is_glob op /\
     bvl_do_app op vs s = Rerr e /\ bvl_state_refs s = r /\ bvl_state_ffi s = f ==>
     bvl_do_app op vs (bvl_state_REC g r c cmp orc cd f) = Rerr e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `f:(FFI)ffi_state`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `r:(num,(bvl_v)bvl_ref)fmap`)) THEN
  MATCH_MP_TAC BVITAILAUX_bvl_do_app_frame_err THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_bvi_to_bvl_REC = prove
 (`!(t:(C,FFI)bvi_state).
     bvi_to_bvl t =
     bvl_state_REC (bvl_state_globals (ARB:(C,FFI)bvl_state)) (bvi_state_refs t)
       (bvi_state_clock t) (bvl_state_compile (ARB:(C,FFI)bvl_state))
       (bvl_state_compile_oracle (ARB:(C,FFI)bvl_state))
       (sptree_map (K (ARB:num#bvl_exp)) (bvi_state_code t)) (bvi_state_ffi t)`,
  GEN_TAC THEN REWRITE_TAC[bvi_to_bvl_def; bvl_state_component_equality] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accessors; bvl_state_INFO.ri_accfupds; K_THM]);;

let state_rel_do_app_err = prove
 (`bvi_do_app op vs (s:(num#C,FFI)bvi_state) = Rerr e /\
   bvi_tailrecProof_state_rel s (t:(C,FFI)bvi_state) /\ ~(op = clos_Install) /\
   (!n. ~(op = clos_Label n)) /\ (!n. ~(op = BlockOp (Build n))) ==>
   bvi_do_app op vs t = Rerr e`,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const) THEN
  MP_TAC(INST [`bvi_do_app_aux op vs (s:(num#C,FFI)bvi_state)`,
               `res:((bvl_v#(num#C,FFI)bvi_state)option)option`] state_rel_do_app_aux) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bvi_do_app op vs (s:(num#C,FFI)bvi_state) = Rerr e` THEN
  ASM_REWRITE_TAC[bvi_do_app_def] THEN
  CASES_ON `bvi_do_app_aux op vs (s:(num#C,FFI)bvi_state)` THEN
  REWRITE_TAC[OPTREL_NONE; OPTREL_SOME] THEN CASE_REWRITE_TAC[] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  CASES_ON `a:(bvl_v#(num#C,FFI)bvi_state)option` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[OPTREL_NONE] THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `z:(bvl_v#(C,FFI)bvi_state)option`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVLPROPSAUX_do_app_aux_SOME_NONE) THEN
    UNDISCH_TAC (CASE_TERM
      `(match bvl_do_app op vs (bvi_to_bvl (s:(num#C,FFI)bvi_state)) with
          Rval (v,t) -> Rval (v,bvl_to_bvi t s)
        | Rerr (Rraise v) -> Rerr (Rraise (Exn v))
        | Rerr (Rabort a') -> Rerr (Rabort a')) = Rerr e`) THEN
    CASES_ON `bvl_do_app op vs (bvi_to_bvl (s:(num#C,FFI)bvi_state))` THEN
    CASE_REWRITE_TAC[] THENL
     [BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[distinctness "result"];
      DISCH_TAC THEN
      SUBGOAL_THEN `bvl_do_app op vs (bvi_to_bvl (t:(C,FFI)bvi_state)) = Rerr a'` MP_TAC THENL
       [REWRITE_TAC[BVITAILAUX_bvi_to_bvl_REC] THEN
        MATCH_MP_TAC (INST_TYPE [`:num#C`,`:A`] BVITAILAUX_bvl_do_app_frame_err2) THEN
        EXISTS_TAC `bvi_to_bvl (s:(num#C,FFI)bvi_state)` THEN
        ASM_REWRITE_TAC[bvi_bvi_to_bvl_refs; bvi_to_bvl_ffi];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      POP_ASSUM MP_TAC THEN CASES_ON `a':(bvl_v)error_result` THEN
      CASE_REWRITE_TAC[injectivity "result"] THEN SIMP_TAC[]];
    BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[distinctness "result"]]);;

let do_app_to_op_state = prove
 (`bvi_do_app (to_op op) vs (s:(C,FFI)bvi_state) = Rval (r,t) ==> t = s`,
  CASES_ON `op:assoc_op` THEN REWRITE_TAC[to_op_def] THENL
   [ALL_TAC; ALL_TAC; MESON_TAC[BVITAILAUX_do_app_ListAppend_Rval]; ALL_TAC] THEN
  SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN
  REWRITE_TAC[BVITAILAUX_option_CASE_Rval] THEN SIMP_TAC[]);;

let scan_expr_check_op = prove
 (`scan_expr ts loc [bvi_Op op xs] = [(tt,ty,r,SOME opr)] ==>
   IS_SOME (check_op ts opr loc (bvi_Op op xs))`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; CONS_11] THEN
  REWRITE_TAC[scan_expr_sing_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `from_op op` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ]) THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let scan_expr_op_same = prove
 (`scan_expr ts loc [bvi_Op op xs] = [(tt,ty,r,SOME opr)] ==> op = to_op opr`,
  DISCH_THEN(MP_TAC o MATCH_MP scan_expr_check_op) THEN
  REWRITE_TAC[IS_SOME_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:bvi_exp` (MP_TAC o MATCH_MP BVITAILAUX_check_op_SOME)) THEN
  REWRITE_TAC[injectivity "bvi_exp"] THEN MESON_TAC[]);;

let BVITAILAUX_term_ok_int_extend = prove
 (`!ts exp. term_ok_int ts exp ==> !extra. term_ok_int (APPEND ts extra) exp`,
  MATCH_MP_TAC term_ok_int_ind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihx") (LABEL_TAC "ihy")) THEN
  ONCE_REWRITE_TAC[term_ok_int_def] THEN CASES_ON `expr:bvi_exp` THEN CASE_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN GEN_TAC THEN
    ASM_SIMP_TAC[LENGTH_APPEND; EL_APPEND; ARITH_RULE `a < n ==> a < n + m:num`];
    ALL_TAC] THEN
  CASES_ON `get_bin_args (bvi_Op a0 a1)` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_PAIR_TAC THEN STRIP_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "ihx" (MP_TAC o SPECL [`a0:clos_op`; `a1:bvi_exp list`; `y:bvi_exp`; `x:bvi_exp`]);
    USE_THEN "ihy" (MP_TAC o SPECL [`a0:clos_op`; `a1:bvi_exp list`; `x:bvi_exp`; `y:bvi_exp`])] THEN
  REWRITE_TAC[] THEN ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let term_ok_int_extend = prove
 (`!ts exp extra. term_ok_int ts exp ==> term_ok_int (APPEND ts extra) exp`,
  MESON_TAC[BVITAILAUX_term_ok_int_extend]);;

let BVITAILAUX_term_ok_any_extend = prove
 (`!ts list exp. term_ok_any ts list exp ==> !extra. term_ok_any (APPEND ts extra) list exp`,
  MATCH_MP_TAC term_ok_any_ind THEN REWRITE_TAC[term_ok_any_def] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN GEN_TAC THEN
    ASM_SIMP_TAC[LENGTH_APPEND; EL_APPEND; ARITH_RULE `a < n ==> a < n + m:num`];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i1") (CONJUNCTS_THEN2 (LABEL_TAC "i2")
    (CONJUNCTS_THEN2 (LABEL_TAC "i3") (LABEL_TAC "i4")))) THEN
  CASES_ON `get_bin_args (bvi_Op op xs)` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_PAIR_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  STRIP_TAC THEN GEN_TAC THEN ASM_SIMP_TAC[term_ok_int_extend] THENL
   [CONJ_TAC THENL
     [REMOVE_THEN "i3" (MP_TAC o SPECL [`y:bvi_exp`; `x:bvi_exp`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REMOVE_THEN "i4" (MP_TAC o SPECL [`x:bvi_exp`; `y:bvi_exp`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    CONJ_TAC THENL
     [REMOVE_THEN "i2" (MP_TAC o SPECL [`y:bvi_exp`; `x:bvi_exp`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REMOVE_THEN "i1" (MP_TAC o SPECL [`x:bvi_exp`; `y:bvi_exp`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]]]);;

let term_ok_any_extend = prove
 (`!ts list exp extra. term_ok_any ts list exp ==> term_ok_any (APPEND ts extra) list exp`,
  MESON_TAC[BVITAILAUX_term_ok_any_extend]);;

let term_ok_extend = prove
 (`!ts ty exp extra. term_ok ts ty exp ==> term_ok (APPEND ts extra) ty exp`,
  REPEAT GEN_TAC THEN CASES_ON `ty:v_ty` THEN REWRITE_TAC[term_ok_def] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[term_ok_any_extend; term_ok_int_extend]);;

let decide_ty_imp = prove
 (`~(decide_ty ty1 ty2 = bvi_tailrec_Any) ==>
   ~(ty1 = bvi_tailrec_Any) /\ ~(ty2 = bvi_tailrec_Any)`,
  CASES_ON `ty1:v_ty` THEN CASES_ON `ty2:v_ty` THEN REWRITE_TAC[decide_ty_def] THEN
  CASE_REWRITE_TAC[]);;

let op_type_simp = prove
 (`(bvi_tailrec_List = op_type op <=> op = bvi_tailrec_Append) /\
   (bvi_tailrec_Any = op_type op <=> op = Noop) /\
   (bvi_tailrec_Int = op_type op <=> op = Plus \/ op = Times)`,
  CASES_ON `op:assoc_op` THEN REWRITE_TAC[op_type_def] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_check_op_opbinargs = prove
 (`!ts opr loc exp e. check_op ts opr loc exp = SOME e ==>
     ?y x. opbinargs opr e = SOME (y,x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP BVITAILAUX_check_op_SOME) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP check_op_thm) THEN
  ASM_REWRITE_TAC[opbinargs_SOME; PAIR_EQ] THEN MESON_TAC[]);;

let scan_expr_Op = prove
 (`scan_expr ts loc [bvi_Op op xs] = [(tt,ty,r,SOME opr)] /\
   rewrite loc n op1 acc ts (bvi_Op op xs) = (lr,x) ==>
   op = to_op opr /\ (op1 = opr <=> lr)`,
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP scan_expr_op_same) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP scan_expr_check_op) THEN
  REWRITE_TAC[IS_SOME_EXISTS] THEN DISCH_THEN(X_CHOOSE_TAC `e:bvi_exp`) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rewrite loc n op1 acc ts (bvi_Op op xs) = (lr,x)` THEN
  REWRITE_TAC[rewrite_def] THEN
  ASM_CASES_TAC `op1:assoc_op = opr` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `y:bvi_exp` (X_CHOOSE_THEN `x':bvi_exp` SUBST1_TAC) o
      MATCH_MP BVITAILAUX_check_op_opbinargs) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `check_op ts op1 loc (bvi_Op (to_op opr) xs) = NONE` SUBST1_TAC THENL
   [BVITAILAUX_OPTION_CASES_TAC `check_op ts op1 loc (bvi_Op (to_op opr) xs)` `e':bvi_exp` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_check_op_from_op) THEN
    ASM_REWRITE_TAC[from_op_to_op];
    CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

let is_rec_term_ok = prove
 (`!exp ts loc ty.
     (bvi_tailrec_is_rec loc exp ==> ~term_ok ts ty exp) /\
     (term_ok ts ty exp ==> ~bvi_tailrec_is_rec loc exp)`,
  GEN_TAC THEN CASES_ON `exp:bvi_exp` THEN REWRITE_TAC[bvi_tailrec_is_rec_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN TRY(CASES_ON `a3:bvi_exp option`) THEN
  REWRITE_TAC[bvi_tailrec_is_rec_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `ty:v_ty` THEN REWRITE_TAC[term_ok_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[term_ok_int_def; term_ok_any_def] THEN CASE_REWRITE_TAC[]);;

let op_type_lem = prove
 (`~(op = Noop) <=> ~(op_type op = bvi_tailrec_Any)`,
  CASES_ON `op:assoc_op` THEN REWRITE_TAC[op_type_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [op_type_lem];;

(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail, the main lemma: its statement as a predicate on    *)
(* the expressions and the state, and one lemma per case of the induction   *)
(* (HOL4's suspend/Resume cases).                                            *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_ert_def = new_definition (CASE_TERM
 `BVITAILAUX_ert xs (s:(num#C,FFI)bvi_state) <=>
  !env1 r t opt (s':(C,FFI)bvi_state) acc env2 loc ts ty.
    bvi_evaluate (xs,env1,s) = (r,t) /\
    bvi_tailrecProof_env_rel ty opt acc env1 env2 /\
    bvi_tailrecProof_state_rel s s' /\
    ty_rel env1 ts /\
    (opt ==> LENGTH xs = 1) /\
    ~(r = Rerr (Rabort Rtype_error)) ==>
    ?t'. bvi_evaluate (xs,env2,s') = (r,t') /\ bvi_tailrecProof_state_rel t t' /\
         (opt ==>
          !op n exp arity.
            lookup loc (bvi_state_code s) = SOME (arity,exp) /\
            optimized_code loc arity exp n (bvi_state_code s') op /\
            op_type op = ty /\
            (?op1 tt ty r. scan_expr ts loc [HD xs] = [(tt,ty,r,SOME op1)] /\
                           ~(ty = bvi_tailrec_Any) /\ ~(op1 = Noop) /\
                           op_type op1 = op_type op) ==>
            let (lr,x) = rewrite loc n op acc ts (HD xs) in
            ?rrr t1 t2.
              bvi_evaluate ([x],env2,s') = (rrr,t1) /\
              bvi_evaluate ([apply_op op (bvi_Var acc) (HD xs)],env2,s') = (rrr,t2) /\
              bvi_tailrecProof_state_rel t t1 /\ bvi_tailrecProof_state_rel t t2)`);;

let BVITAILAUX_ertIH_def = new_definition
 `BVITAILAUX_ertIH xs (s:(num#C,FFI)bvi_state) <=>
  !ys (t:(num#C,FFI)bvi_state).
         list_size bvi_exp_size ys < list_size bvi_exp_size xs /\
         bvi_state_clock t <= bvi_state_clock s \/
         bvi_state_clock t < bvi_state_clock s ==> BVITAILAUX_ert ys t`;;

let BVITAILAUX_ert_ind = prove
 (`(!xs (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH xs s ==> BVITAILAUX_ert xs s) ==>
   !xs (s:(num#C,FFI)bvi_state). BVITAILAUX_ert xs s`,
  REWRITE_TAC[BVITAILAUX_ertIH_def] THEN
  DISCH_TAC THEN MATCH_MP_TAC evaluate_complete_ind THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_env_rel_F = prove
 (`!ty opt acc ty' acc' env1 env2.
     bvi_tailrecProof_env_rel ty opt acc env1 env2 ==>
     bvi_tailrecProof_env_rel ty' F acc' env1 env2`,
  REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN MESON_TAC[]);;

(* apply the induction hypothesis "ih" of evaluate_rewrite_tail to ys and *)
(* the state st, with the arguments args of BVITAILAUX_ert                  *)
let BVITAILAUX_ERT_IH_TAC (ys:term) (st:term) (args:term list) : tactic =
  USE_THEN "ih" (MP_TAC o SPECL [ys; st]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[list_size; bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
    TRY(REWRITE_TAC(type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp")) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN DISCH_THEN(MP_TAC o SPECL args);;

let BVITAILAUX_eval_apply_op = prove
 (CASE_TERM
  `!op acc e env (s:(C,FFI)bvi_state).
     acc < LENGTH env ==>
     bvi_evaluate ([apply_op op (bvi_Var acc) e],env,s) =
     match bvi_evaluate ([e],env,s) with
       (Rval vs,s1) ->
         (match bvi_do_app (to_op op) [HD vs; EL acc env] s1 with
            Rval (v,s2) -> (Rval [v],s2)
          | Rerr err -> (Rerr err,s1))
     | (Rerr err,s1) -> (Rerr err,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apply_op_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  ASM_REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([e],env,s:(C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[REVERSE; APPEND; HD] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP) THEN
  REWRITE_TAC[REVERSE; APPEND; HD]);;

let BVITAILAUX_scan_Var = prove
 (`!ts loc n. scan_expr ts loc [bvi_Var n] =
              [(ts,(if n < LENGTH ts then EL n ts else bvi_tailrec_Any),F,NONE)]`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; scan_expr_sing_def; LET_DEF; LET_END_DEF]);;

let BVITAILAUX_scan_simple = prove
 (`!ts loc x t d xs h rets d' y fl n.
     scan_expr ts loc [bvi_Raise x] = [(ts,bvi_tailrec_Any,F,NONE)] /\
     scan_expr ts loc [bvi_Call t d xs h] = [(ts,bvi_tailrec_Any,F,NONE)] /\
     scan_expr ts loc [bvi_Return xs] = [(ts,bvi_tailrec_Any,F,NONE)] /\
     scan_expr ts loc [LetCall rets t d' xs y] = [(ts,bvi_tailrec_Any,F,NONE)] /\
     scan_expr ts loc [bvi_Force fl n] =
       [(ts,(if n < LENGTH ts then EL n ts else bvi_tailrec_Any),F,NONE)] /\
     scan_expr ts loc [bvi_Tick x] = scan_expr ts loc [x]`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; scan_expr_sing_def; LET_DEF; LET_END_DEF]);;

let BVITAILAUX_ert_NIL = prove
 (`!s:(num#C,FFI)bvi_state. BVITAILAUX_ert [] s`,
  REWRITE_TAC[BVITAILAUX_ert_def; bvi_evaluate_def; PAIR_EQ; LENGTH;
              ARITH_RULE `~(0 = 1)`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `s':(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BVITAILAUX_ert_CONS = prove
 (`!x y ys (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH (CONS x (CONS y ys)) s ==>
     BVITAILAUX_ert (CONS x (CONS y ys)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC(SUC n) = 1)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~opt` (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  UNDISCH_TAC `bvi_evaluate (CONS x (CONS y ys),env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([x],env1,s:(num#C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(num#C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    BVITAILAUX_ERT_IH_TAC `[x:bvi_exp]` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rerr a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `t':(C,FFI)bvi_state` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]] THEN
  BVITAILAUX_ERT_IH_TAC `[x:bvi_exp]` `s:(num#C,FFI)bvi_state`
    [`env1:bvl_v list`; `Rval a:bvi_result`; `s1:(num#C,FFI)bvi_state`; `F`;
     `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
     `ty:v_ty`] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o
    check (fun th -> concl th = `bvi_evaluate ([x],env1,s:(num#C,FFI)bvi_state) = (Rval a,s1)`)) THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (CONS y ys,env1,s1:(num#C,FFI)bvi_state)`
    `r2:bvi_result` `s2:(num#C,FFI)bvi_state` THEN
  CASES_ON `r2:bvi_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [BVITAILAUX_ERT_IH_TAC `CONS (y:bvi_exp) ys` `s1:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rval a':bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `t1:(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`];
    BVITAILAUX_ERT_IH_TAC `CONS (y:bvi_exp) ys` `s1:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rerr a':bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `t1:(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`]] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t2:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_ert_Var = prove
 (`!v (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Var v] s ==>
     BVITAILAUX_ert [bvi_Var v] s`,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_scan_Var; CONS_11; PAIR_EQ; option_DISTINCT] THEN
  REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_CASES_TAC `v < LENGTH (env1:bvl_v list)` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[bvi_tailrecProof_env_rel_def]) THEN
  SUBGOAL_THEN `v < LENGTH (env2:bvl_v list) /\ EL v env2 = EL v env1` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP IS_PREFIX_LENGTH) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC is_prefix_el THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `s':(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_ert_Raise = prove
 (`!x (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Raise x] s ==>
     BVITAILAUX_ert [bvi_Raise x] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD; BVITAILAUX_scan_simple; CONS_11; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Raise x],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([x],env1,s:(num#C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(num#C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
   [BVITAILAUX_ERT_IH_TAC `[x:bvi_exp]` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rval a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`];
    BVITAILAUX_ERT_IH_TAC `[x:bvi_exp]` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rerr a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`]] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_ert_Return = prove
 (`!xs (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Return xs] s ==>
     BVITAILAUX_ert [bvi_Return xs] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD; BVITAILAUX_scan_simple; CONS_11; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Return xs],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(num#C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
   [BVITAILAUX_ERT_IH_TAC `xs:bvi_exp list` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rval a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`];
    BVITAILAUX_ERT_IH_TAC `xs:bvi_exp list` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rerr a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`]] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_acc_LT_TAC : tactic =
  SUBGOAL_THEN `acc < LENGTH (env2:bvl_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN
    ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN ARITH_TAC;
    ALL_TAC];;

let BVITAILAUX_ert_Tick = prove
 (`!x (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Tick x] s ==>
     BVITAILAUX_ert [bvi_Tick x] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD; BVITAILAUX_scan_simple] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const) THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Tick x],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `s':(C,FFI)bvi_state` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[rewrite_def; pair_CASE_def] THEN BETA_TAC THEN
    REWRITE_TAC[FST; SND] THEN BVITAILAUX_acc_LT_TAC THEN
    ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`Rerr (Rabort Rtimeout_error):bvi_result`;
                          `s':(C,FFI)bvi_state`; `s':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  BVITAILAUX_ERT_IH_TAC `[x:bvi_exp]` `bvi_dec_clock 1 (s:(num#C,FFI)bvi_state)`
    [`env1:bvl_v list`; `r:bvi_result`; `t:(num#C,FFI)bvi_state`; `opt:bool`;
     `bvi_dec_clock 1 (s':(C,FFI)bvi_state)`; `acc:num`; `env2:bvl_v list`; `loc:num`;
     `ts:v_ty list`; `ty:v_ty`] THEN
  REWRITE_TAC[HD] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH; ONE] THEN REWRITE_TAC[bvi_dec_clock_def] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC bvi_tailrecProof_state_rel_with_clock THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `opt:bool`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`op:assoc_op`; `n:num`; `exp:bvi_exp`; `arity:num`]) THEN
  ASM_REWRITE_TAC[bvi_dec_clock_code] THEN
  ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`op1:assoc_op`; `tt:v_ty list`; `ty':v_ty`; `r':bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rewrite_def; pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[FST; SND] THEN BVITAILAUX_acc_LT_TAC THEN
  ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[]);;

let BVITAILAUX_EL_LENGTH_APPEND_ADD = prove
 (`!(zz:A list) env k. EL (LENGTH zz + k) (APPEND zz env) = EL k env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EL_APPEND] THEN
  REWRITE_TAC[ARITH_RULE `~(n + k < n:num)`; ADD_SUB2]);;

let BVITAILAUX_env_rel_APPEND = prove
 (`!ty opt acc env1 env2 zz.
     bvi_tailrecProof_env_rel ty opt acc env1 env2 ==>
     bvi_tailrecProof_env_rel ty opt (LENGTH zz + acc) (APPEND zz env1) (APPEND zz env2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IS_PREFIX_APPENDS] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `opt:bool`)) THEN
  REWRITE_TAC[LENGTH_APPEND; BVITAILAUX_EL_LENGTH_APPEND_ADD] THEN
  SIMP_TAC[] THEN ARITH_TAC);;

let BVITAILAUX_optimized_code_subspt = prove
 (`!loc arity exp n c c' op.
     optimized_code loc arity exp n c op /\ subspt c c' ==>
     optimized_code loc arity exp n c' op`,
  REWRITE_TAC[optimized_code_def; subspt_lookup] THEN MESON_TAC[]);;

let BVITAILAUX_tuple4_eq = prove
 (`!(p:A#B#C#D) d. SND (SND (SND p)) = d ==> p = (FST p,FST (SND p),FST (SND (SND p)),d)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN MESON_TAC[]);;

(* the goal ?tt ty r. p = (tt,ty,r,SOME op) /\ ... : instantiate with the  *)
(* projections of p                                                        *)
let BVITAILAUX_TUPLE4_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let _,bod = strip_exists w in
  let eqn = fst(dest_conj bod) in
  let p = lhs eqn in
  let fst_t t = mk_icomb(`FST:A#B->A`, t) and snd_t t = mk_icomb(`SND:A#B->B`, t) in
  (MAP_EVERY EXISTS_TAC [fst_t p; fst_t (snd_t p); fst_t (snd_t (snd_t p))] THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC BVITAILAUX_tuple4_eq THEN ASM_REWRITE_TAC[]; ALL_TAC]) g;;


let BVITAILAUX_ert_Let = prove
 (`!xs x (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Let xs x] s ==>
     BVITAILAUX_ert [bvi_Let xs x] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Let xs x],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)`
    `r0:bvi_result` `s2:(num#C,FFI)bvi_state` THEN
  CASES_ON `r0:bvi_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC;
    STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    BVITAILAUX_ERT_IH_TAC `xs:bvi_exp list` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rerr a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN BVITAILAUX_acc_LT_TAC THEN
    REWRITE_TAC[rewrite_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
    BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
    ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`Rerr a:bvi_result`; `t1:(C,FFI)bvi_state`;
                          `t1:(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  BVITAILAUX_ERT_IH_TAC `xs:bvi_exp list` `s:(num#C,FFI)bvi_state`
    [`env1:bvl_v list`; `Rval a:bvi_result`; `s2:(num#C,FFI)bvi_state`; `F`;
     `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
     `ty:v_ty`] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o
    check (fun th -> concl th = `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state) = (Rval a,s2)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH o
    check (fun th -> concl th = `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state) = (Rval a,s2)`)) THEN
  MP_TAC(ISPECL [`ts:v_ty list`; `loc:num`; `xs:bvi_exp list`; `env1:bvl_v list`;
                 `scan_expr ts loc xs`; `s:(num#C,FFI)bvi_state`; `a:bvl_v list`;
                 `s2:(num#C,FFI)bvi_state`] scan_expr_ty_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM
    `ty_rel (APPEND a env1)
       (APPEND (MAP (FST o SND) (scan_expr ts loc xs))
               (match LAST1 (scan_expr ts loc xs) with NONE -> ts | SOME c -> FST c))`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC ty_rel_APPEND THEN ASM_REWRITE_TAC[] THEN
    BVITAILAUX_OPTION_CASES_TAC `LAST1 (scan_expr ts loc xs)`
      `c:v_ty list # v_ty # bool # assoc_op option` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ty_rel env1 o (FST:v_ty list # v_ty # bool # assoc_op option -> v_ty list)`;
                   `scan_expr ts loc xs`;
                   `c:v_ty list # v_ty # bool # assoc_op option`]
                  (GEN `P:A->bool` EVERY_LAST1)) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  BVITAILAUX_ERT_IH_TAC `[x:bvi_exp]` `s2:(num#C,FFI)bvi_state`
    [`APPEND a env1:bvl_v list`; `r:bvi_result`; `t:(num#C,FFI)bvi_state`; `opt:bool`;
     `t0:(C,FFI)bvi_state`; `LENGTH (a:bvl_v list) + acc`; `APPEND a env2:bvl_v list`;
     `loc:num`;
     CASE_TERM `APPEND (MAP (FST o SND) (scan_expr ts loc xs))
               (match LAST1 (scan_expr ts loc xs) with NONE -> ts | SOME c -> FST c)`;
     `ty:v_ty`] THEN
  ASM_SIMP_TAC[BVITAILAUX_env_rel_APPEND; LENGTH; ONE; HD] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(C,FFI)bvi_state` THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `opt:bool`) o
    check (fun th -> is_imp (concl th) && lhand (concl th) = `opt:bool` &&
                     can (find_term ((=) `t0:(C,FFI)bvi_state`)) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`op:assoc_op`; `n:num`; `exp:bvi_exp`; `arity:num`]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono o
    check (fun th -> concl th = `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state) = (Rval a,s2)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono o
    check (fun th -> concl th = `bvi_evaluate (xs,env2,s':(C,FFI)bvi_state) = (Rval a,t0)`)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[subspt_lookup];
      ASM_MESON_TAC[BVITAILAUX_optimized_code_subspt];
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `scan_expr ts loc [bvi_Let xs x] = [(tt,ty',r',SOME op1)]` THEN
    REWRITE_TAC[CONJUNCT1 scan_expr_eq; scan_expr_sing_def; LET_DEF; LET_END_DEF;
                pair_CASE_def; CONS_11; PAIR_EQ] THEN
    BETA_TAC THEN REWRITE_TAC[FST; SND; GSYM(CONJUNCT2 scan_expr_eq)] THEN STRIP_TAC THEN
    EXISTS_TAC `op1:assoc_op` THEN BVITAILAUX_TUPLE4_EXISTS_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rewrite_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `acc + LENGTH (xs:bvi_exp list) = LENGTH (a:bvl_v list) + acc` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  BVITAILAUX_acc_LT_TAC THEN
  SUBGOAL_THEN `LENGTH (a:bvl_v list) + acc < LENGTH (APPEND a env2)` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BVITAILAUX_eval_apply_op; BVITAILAUX_EL_LENGTH_APPEND_ADD] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail: the If case                                        *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_rewrite_If = prove
 (`!loc next opr acc ts x1 x2 x3.
     rewrite loc next opr acc ts (bvi_If x1 x2 x3) =
     let t1 = FST (scan_expr_sing ts loc x1) in
     ((FST (rewrite loc next opr acc t1 x2) \/ FST (rewrite loc next opr acc t1 x3)),
      bvi_If x1
        (if FST (rewrite loc next opr acc t1 x2) then SND (rewrite loc next opr acc t1 x2)
         else apply_op opr (bvi_Var acc) x2)
        (if FST (rewrite loc next opr acc t1 x3) then SND (rewrite loc next opr acc t1 x3)
         else apply_op opr (bvi_Var acc) x3))`,
  REWRITE_TAC[rewrite_def; CONJUNCT1 scan_expr_eq; HD; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN BETA_TAC THEN REWRITE_TAC[]);;

let BVITAILAUX_scan_If = prove
 (CASE_TERM
  `!ts loc x1 x2 x3.
     scan_expr ts loc [bvi_If x1 x2 x3] =
     let ti = FST (scan_expr_sing ts loc x1) in
     let p2 = scan_expr_sing ti loc x2 in
     let p3 = scan_expr_sing ti loc x3 in
     let opo = (match SND (SND (SND p2)) with NONE -> SND (SND (SND p3))
                | SOME a -> SND (SND (SND p2))) in
     [(MAP2 decide_ty (FST p2) (FST p3),
       (match opo with
          NONE -> decide_ty (FST (SND p2)) (FST (SND p3))
        | SOME opr -> decide_ty (FST (SND p2)) (decide_ty (FST (SND p3)) (op_type opr))),
       IS_SOME (SND (SND (SND p3))),opo)]`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; scan_expr_sing_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN BETA_TAC THEN REWRITE_TAC[]);;

let BVITAILAUX_if_types = prove
 (CASE_TERM
  `!ty2 o2 ty3 o3 ty' op1.
     (match (match o2 with NONE -> o3 | SOME a -> o2) with
        NONE -> decide_ty ty2 ty3
      | SOME opr -> decide_ty ty2 (decide_ty ty3 (op_type opr))) = ty' /\
     (match o2 with NONE -> o3 | SOME a -> o2) = SOME op1 /\
     ~(ty' = bvi_tailrec_Any) ==>
     ty2 = ty' /\ ty3 = ty' /\ op_type op1 = ty'`,
  REPEAT GEN_TAC THEN CASES_ON `o2:assoc_op option` THEN
  CASES_ON `o3:assoc_op option` THEN CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  MESON_TAC[decide_ty_simp]);;

let BVITAILAUX_scan_If_types = prove
 (`!ts loc x1 x2 x3 tt ty' r' op1.
     scan_expr ts loc [bvi_If x1 x2 x3] = [(tt,ty',r',SOME op1)] /\
     ~(ty' = bvi_tailrec_Any) ==>
     FST (SND (scan_expr_sing (FST (scan_expr_sing ts loc x1)) loc x2)) = ty' /\
     FST (SND (scan_expr_sing (FST (scan_expr_sing ts loc x1)) loc x3)) = ty' /\
     op_type op1 = ty'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_scan_If; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ] THEN STRIP_TAC THEN
  MATCH_MP_TAC BVITAILAUX_if_types THEN
  EXISTS_TAC `SND (SND (SND (scan_expr_sing (FST (scan_expr_sing ts loc x1)) loc x2)))` THEN
  EXISTS_TAC `SND (SND (SND (scan_expr_sing (FST (scan_expr_sing ts loc x1)) loc x3)))` THEN
  ASM_REWRITE_TAC[]);;

let BVITAILAUX_branch_scan = prove
 (`!loc n op acc ti e.
     ~(op_type op = bvi_tailrec_Any) /\
     FST (SND (scan_expr_sing ti loc e)) = op_type op /\
     FST (rewrite loc n op acc ti e) ==>
     ?op2 tt2 ty2 r2. scan_expr ti loc [e] = [(tt2,ty2,r2,SOME op2)] /\
                      ~(ty2 = bvi_tailrec_Any) /\ ~(op2 = Noop) /\
                      op_type op2 = op_type op`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`loc:num`; `n:num`; `op:assoc_op`; `acc:num`; `ti:v_ty list`; `e:bvi_exp`;
                 `FST (scan_expr_sing ti loc e)`; `FST (SND (scan_expr_sing ti loc e))`;
                 `FST (rewrite loc n op acc ti e)`; `SND (rewrite loc n op acc ti e)`;
                 `FST (SND (SND (scan_expr_sing ti loc e)))`;
                 `SND (SND (SND (scan_expr_sing ti loc e)))`] rewrite_scan_expr) THEN
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; PAIR] THEN ASM_REWRITE_TAC[op_type_lem] THEN
  BVITAILAUX_OPTION_CASES_TAC `SND (SND (SND (scan_expr_sing ti loc e)))` `op2:assoc_op` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `op2:assoc_op` THEN BVITAILAUX_TUPLE4_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `scan_expr ti loc [e] =
     [FST (scan_expr_sing ti loc e),FST (SND (scan_expr_sing ti loc e)),
      FST (SND (SND (scan_expr_sing ti loc e))),SOME op2]` ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1 scan_expr_eq; CONS_11] THEN
    MATCH_MP_TAC BVITAILAUX_tuple4_eq THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP scan_expr_op_type) THEN
  CASE_REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_eval_apply_op_state = prove
 (`!op acc e env (s:(C,FFI)bvi_state) r t.
     acc < LENGTH env /\ bvi_evaluate ([e],env,s) = (r,t) ==>
     ?rr. bvi_evaluate ([apply_op op (bvi_Var acc) e],env,s) = (rr,t)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN
  CASES_ON `r:bvi_result` THEN CASE_REWRITE_TAC[] THENL [ALL_TAC; MESON_TAC[]] THEN
  MP_TAC(ISPEC `bvi_do_app (to_op op) [HD a; EL acc env] (t:(C,FFI)bvi_state)`
           (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_TAC `p:bvl_v#(C,FFI)bvi_state`) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL [ALL_TAC; MESON_TAC[]] THEN
  UNDISCH_TAC `bvi_do_app (to_op op) [HD a; EL acc env] (t:(C,FFI)bvi_state) = Rval p` THEN
  SPEC_TAC(`p:bvl_v#(C,FFI)bvi_state`,`p:bvl_v#(C,FFI)bvi_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP do_app_to_op_state) THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let BVITAILAUX_if_branch = prove
 (`!x2 (s2:(num#C,FFI)bvi_state) env1 r t (u1:(C,FFI)bvi_state) acc env2 loc ti ty op n
    exp arity.
     BVITAILAUX_ert [x2] s2 /\
     bvi_evaluate ([x2],env1,s2) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) /\
     bvi_tailrecProof_env_rel ty T acc env1 env2 /\
     bvi_tailrecProof_state_rel s2 u1 /\ ty_rel env1 ti /\
     lookup loc (bvi_state_code s2) = SOME (arity,exp) /\
     optimized_code loc arity exp n (bvi_state_code u1) op /\
     op_type op = ty /\
     (FST (rewrite loc n op acc ti x2) ==>
        ?op1 tt ty' r'. scan_expr ti loc [x2] = [(tt,ty',r',SOME op1)] /\
                        ~(ty' = bvi_tailrec_Any) /\ ~(op1 = Noop) /\
                        op_type op1 = op_type op) ==>
     ?rrr ta tb.
       bvi_evaluate ([if FST (rewrite loc n op acc ti x2)
                      then SND (rewrite loc n op acc ti x2)
                      else apply_op op (bvi_Var acc) x2],env2,u1) = (rrr,ta) /\
       bvi_evaluate ([apply_op op (bvi_Var acc) x2],env2,u1) = (rrr,tb) /\
       bvi_tailrecProof_state_rel t ta /\ bvi_tailrecProof_state_rel t tb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `acc < LENGTH (env2:bvl_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty T acc env1 env2` THEN
    REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `FST (rewrite loc n op acc ti x2)` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `BVITAILAUX_ert [x2] (s2:(num#C,FFI)bvi_state)` THEN
    REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
    DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r:bvi_result`; `t:(num#C,FFI)bvi_state`;
      `T`; `u1:(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ti:v_ty list`;
      `ty:v_ty`]) THEN
    ASM_REWRITE_TAC[LENGTH; ONE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:(C,FFI)bvi_state` (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
    DISCH_THEN(MP_TAC o SPECL [`op:assoc_op`; `n:num`; `exp:bvi_exp`; `arity:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `FST (rewrite loc n op acc ti x2) ==>
        (?op1 tt ty' r'. scan_expr ti loc [x2] = [(tt,ty',r',SOME op1)] /\
                        ~(ty' = bvi_tailrec_Any) /\ ~(op1 = Noop) /\
                        op_type op1 = op_type op)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  UNDISCH_TAC `BVITAILAUX_ert [x2] (s2:(num#C,FFI)bvi_state)` THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r:bvi_result`; `t:(num#C,FFI)bvi_state`;
    `F`; `u1:(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ti:v_ty list`;
    `ty:v_ty`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`op:assoc_op`; `acc:num`; `x2:bvi_exp`; `env2:bvl_v list`;
                 `u1:(C,FFI)bvi_state`; `r:bvi_result`; `t0:(C,FFI)bvi_state`]
                BVITAILAUX_eval_apply_op_state) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:bvi_result` ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`rr:bvi_result`; `t0:(C,FFI)bvi_state`; `t0:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[]);;

let BVITAILAUX_eval_If_Rval = prove
 (`!x1 x2 x3 env (s:(C,FFI)bvi_state) vs s1.
     bvi_evaluate ([x1],env,s) = (Rval vs,s1) ==>
     bvi_evaluate ([bvi_If x1 x2 x3],env,s) =
     (if bvl_Boolv T = HD vs then bvi_evaluate ([x2],env,s1) else
      if bvl_Boolv F = HD vs then bvi_evaluate ([x3],env,s1) else
      (Rerr (Rabort Rtype_error),s1))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_eval_apply_op_If = prove
 (`!op acc x1 x2 x3 env (s:(C,FFI)bvi_state) vs s1.
     acc < LENGTH env /\ bvi_evaluate ([x1],env,s) = (Rval vs,s1) ==>
     bvi_evaluate ([apply_op op (bvi_Var acc) (bvi_If x1 x2 x3)],env,s) =
     (if bvl_Boolv T = HD vs then bvi_evaluate ([apply_op op (bvi_Var acc) x2],env,s1) else
      if bvl_Boolv F = HD vs then bvi_evaluate ([apply_op op (bvi_Var acc) x3],env,s1) else
      (Rerr (Rabort Rtype_error),s1))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BVITAILAUX_eval_apply_op; BVITAILAUX_eval_If_Rval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_EXISTS_SPLIT = prove
 (`!P Q R. (?x:A. P x /\ Q x /\ R) <=> (?x. P x /\ Q x) /\ R`,
  MESON_TAC[]);;

let BVITAILAUX_IF_BRANCH_TAC (xb:term) : tactic =
  DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC (vsubst [xb,`xb:bvi_exp`] `BVITAILAUX_ert [xb] (s2:(num#C,FFI)bvi_state)`) THEN
    REWRITE_TAC[BVITAILAUX_ert_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r:bvi_result`; `t:(num#C,FFI)bvi_state`;
      `F`; `t0:(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`;
      `FST (scan_expr_sing ts loc x1)`; `ty:v_ty`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN BVITAILAUX_acc_LT_TAC THEN
  SUBGOAL_THEN `bvi_tailrecProof_env_rel ty T acc env1 env2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ts:v_ty list`; `loc:num`; `x1:bvi_exp`; `x2:bvi_exp`; `x3:bvi_exp`;
                 `tt:v_ty list`; `ty':v_ty`; `r':bool`; `op1:assoc_op`]
                BVITAILAUX_scan_If_types) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[BVITAILAUX_rewrite_If; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[MATCH_MP BVITAILAUX_eval_If_Rval
    (ASSUME `bvi_evaluate ([x1],env2,s':(C,FFI)bvi_state) = (Rval a,t0)`)] THEN
  MP_TAC(ISPECL [`op:assoc_op`; `acc:num`; `x1:bvi_exp`; `x2:bvi_exp`; `x3:bvi_exp`;
                 `env2:bvl_v list`; `s':(C,FFI)bvi_state`; `a:bvl_v list`;
                 `t0:(C,FFI)bvi_state`] BVITAILAUX_eval_apply_op_If) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN (vsubst [xb,`xb:bvi_exp`]
    `FST (rewrite loc n op acc (FST (scan_expr_sing ts loc x1)) xb) ==>
     ?op2 tt2 ty2 r2. scan_expr (FST (scan_expr_sing ts loc x1)) loc [xb] =
                      [(tt2,ty2,r2,SOME op2)] /\
                      ~(ty2 = bvi_tailrec_Any) /\ ~(op2 = Noop) /\
                      op_type op2 = op_type op`) ASSUME_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`loc:num`; `n:num`; `op:assoc_op`; `acc:num`;
                         `FST (scan_expr_sing ts loc x1)`; xb] BVITAILAUX_branch_scan) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [xb; `s2:(num#C,FFI)bvi_state`; `env1:bvl_v list`; `r:bvi_result`;
                 `t:(num#C,FFI)bvi_state`; `t0:(C,FFI)bvi_state`; `acc:num`;
                 `env2:bvl_v list`; `loc:num`; `FST (scan_expr_sing ts loc x1)`; `ty:v_ty`;
                 `op:assoc_op`; `n:num`; `exp:bvi_exp`; `arity:num`]
                BVITAILAUX_if_branch) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[subspt_lookup; BVITAILAUX_optimized_code_subspt];
    ALL_TAC] THEN
  MESON_TAC[];;
let BVITAILAUX_ert_If = prove
 (`!x1 x2 x3 (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_If x1 x2 x3] s ==>
     BVITAILAUX_ert [bvi_If x1 x2 x3] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  GEN_REWRITE_TAC I [BVITAILAUX_EXISTS_SPLIT] THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_If x1 x2 x3],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([x1],env1,s:(num#C,FFI)bvi_state)`
    `r1:bvi_result` `s2:(num#C,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC;
    STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    BVITAILAUX_ERT_IH_TAC `[x1:bvi_exp]` `s:(num#C,FFI)bvi_state`
      [`env1:bvl_v list`; `Rerr a:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
       `ty:v_ty`] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN BVITAILAUX_acc_LT_TAC THEN
    REWRITE_TAC[BVITAILAUX_rewrite_If; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
    BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
    ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`Rerr a:bvi_result`; `t1:(C,FFI)bvi_state`;
                          `t1:(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[]] THEN
  BVITAILAUX_ERT_IH_TAC `[x1:bvi_exp]` `s:(num#C,FFI)bvi_state`
    [`env1:bvl_v list`; `Rval a:bvi_result`; `s2:(num#C,FFI)bvi_state`; `F`;
     `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
     `ty:v_ty`] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o
    check (fun th -> concl th = `bvi_evaluate ([x1],env1,s:(num#C,FFI)bvi_state) = (Rval a,s2)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono o
    check (fun th -> concl th = `bvi_evaluate ([x1],env1,s:(num#C,FFI)bvi_state) = (Rval a,s2)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono o
    check (fun th -> concl th = `bvi_evaluate ([x1],env2,s':(C,FFI)bvi_state) = (Rval a,t0)`)) THEN
  SUBGOAL_THEN `ty_rel env1 (FST (scan_expr_sing ts loc x1))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ts:v_ty list`; `loc:num`; `[x1:bvi_exp]`; `env1:bvl_v list`;
                   `scan_expr ts loc [x1]`; `s:(num#C,FFI)bvi_state`; `a:bvl_v list`;
                   `s2:(num#C,FFI)bvi_state`] scan_expr_ty_rel) THEN
    ASM_REWRITE_TAC[CONJUNCT1 scan_expr_eq; ALL; o_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `BVITAILAUX_ert [x2] (s2:(num#C,FFI)bvi_state) /\
                BVITAILAUX_ert [x3] (s2:(num#C,FFI)bvi_state)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN REWRITE_TAC[list_size] THEN
    REWRITE_TAC(type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp") THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `bvl_Boolv T = HD a` THEN ASM_REWRITE_TAC[] THENL
   [BVITAILAUX_IF_BRANCH_TAC `x2:bvi_exp`; ALL_TAC] THEN
  ASM_CASES_TAC `bvl_Boolv F = HD a` THEN ASM_REWRITE_TAC[] THENL
   [BVITAILAUX_IF_BRANCH_TAC `x3:bvi_exp`;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail, the Op case: Install                               *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_do_install_Rval = prove
 (`!vs (s:(A,FFI)bvi_state) v s'.
     bvi_do_install vs s = (Rval (v,s'):(bvl_v#(A,FFI)bvi_state,E)result) ==>
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

let BVITAILAUX_do_install_eq_Rval = prove
 (`!v1 v2 bytes data (s:(A,FFI)bvi_state) cfg k prog rest cfg'.
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
        :(bvl_v#(A,FFI)bvi_state,E)result)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let BVITAILAUX_compile_each_head = prove
 (`!next k (p:num#bvi_exp) rest n1 ys.
     bvi_tailrec_compile_each next (CONS (k,p) rest) = (n1,ys) ==>
     ?p2 rest2. ys = CONS (k,p2) rest2`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_tailrec_compile_each_def] THEN
  BVITAILAUX_OPTION_CASES_TAC
    `bvi_tailrec_compile_exp k next p1 p2` `q:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let BVITAILAUX_input_condition_MEM = prove
 (`!next (progs:(num#A)list) n.
     bvi_tailrecProof_input_condition next progs /\ MEM n (MAP FST progs) /\
     bvl_num_stubs <= n ==> ~(n MOD bvl_to_bvi_namespaces = 2)`,
  REWRITE_TAC[bvi_tailrecProof_input_condition_def; GSYM ALL_MEM; MEM_FILTER; o_THM;
              MEM_MAP] THEN
  MESON_TAC[]);;

let BVITAILAUX_install_disjoint = prove
 (`!next1 progs next2 progs2 (c1:(num#bvi_exp)spt) (c2:(num#bvi_exp)spt).
     bvi_tailrec_compile_each next1 progs = (next2,progs2) /\
     bvi_tailrecProof_input_condition next1 progs /\
     DISJOINT (domain c1) (set_of_list (MAP FST progs)) /\
     bvi_tailrecProof_namespace_rel c1 c2 /\
     (!n. n IN domain c2 /\ n MOD bvl_to_bvi_namespaces = 2 ==> n < next1) ==>
     DISJOINT (domain c2) (set_of_list (MAP FST progs2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; NOT_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MP_TAC(INST [`next1:num`,`n:num`; `progs:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
               `next2:num`,`n1:num`; `progs2:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
               `n:num`,`e:num`] bvi_tailrecProof_compile_each_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `n IN domain (c1:(num#bvi_exp)spt)` MP_TAC THENL
     [UNDISCH_TAC `bvi_tailrecProof_namespace_rel (c1:(num#bvi_exp)spt) c2` THEN
      REWRITE_TAC[bvi_tailrecProof_namespace_rel_def] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`)
        (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `n:num`))) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `bvl_num_stubs <= n` THEN ASM_REWRITE_TAC[GSYM NOT_LE] THEN
      SUBGOAL_THEN `~(n MOD bvl_to_bvi_namespaces = 2)` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(ISPECL [`next1:num`; `progs:(num#num#bvi_exp)list`; `n:num`]
                          BVITAILAUX_input_condition_MEM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (domain (c1:(num#bvi_exp)spt))
                  (set_of_list (MAP FST (progs:(num#num#bvi_exp)list)))` THEN
    REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n MOD bvl_to_bvi_namespaces = 2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_input_condition next1 (progs:(num#num#bvi_exp)list)` THEN
    REWRITE_TAC[bvi_tailrecProof_input_condition_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BVITAILAUX_ns_MOD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let BVITAILAUX_state_co_shift = prove
 (`!(f:S->P->T#Q) (co:num->(S#C)#P).
     shift_seq 1 (state_co f co) = state_co f (shift_seq 1 co)`,
  REWRITE_TAC[shift_seq_def; state_co_def; FUN_EQ_THM]);;

let BVITAILAUX_state_rel_input = prove
 (`!(s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) n.
     bvi_tailrecProof_state_rel s t ==>
     bvi_tailrecProof_input_condition (FST (FST (bvi_state_compile_oracle s n)))
       (SND (bvi_state_compile_oracle s n))`,
  REWRITE_TAC[bvi_tailrecProof_state_rel_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN
  BETA_TAC THEN MESON_TAC[]);;

let BVITAILAUX_install_ns_bound = prove
 (`!next1 progs next2 progs2 (c2:(num#bvi_exp)spt) n.
     bvi_tailrec_compile_each next1 progs = (next2,progs2) /\
     bvi_tailrecProof_input_condition next1 progs /\
     (!n. n IN domain c2 /\ n MOD bvl_to_bvi_namespaces = 2 ==> n < next1) /\
     n IN domain (sptree_union c2 (fromAList progs2)) /\ n MOD bvl_to_bvi_namespaces = 2 ==>
     n < next2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_union; domain_fromAList; IN_UNION; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `kk:num` o MATCH_MP bvi_tailrecProof_compile_each_next_mono) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(INST [`next1:num`,`n:num`; `progs:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
               `next2:num`,`n1:num`; `progs2:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
               `n:num`,`e:num`] bvi_tailrecProof_compile_each_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bvl_num_stubs <= n` THENL
   [MP_TAC(ISPECL [`next1:num`; `progs:(num#num#bvi_exp)list`; `n:num`]
                  BVITAILAUX_input_condition_MEM) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `bvi_tailrecProof_input_condition next1 (progs:(num#num#bvi_exp)list)` THEN
    REWRITE_TAC[bvi_tailrecProof_input_condition_def] THEN ASM_ARITH_TAC]);;

let BVITAILAUX_state_cc_SOME = prove
 (`!(f:S->P->T#Q) (cc:C->Q->(D#E#G)option) st cfg prog code data cfg'.
     state_cc f cc (st,cfg) prog = SOME (code,data,cfg') <=>
     ?cfg1. cc cfg (SND (f st prog)) = SOME (code,data,cfg1) /\
            cfg' = (FST (f st prog),cfg1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_cc_def; pair_CASE_def] THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  BVITAILAUX_OPTION_CASES_TAC `(cc:C->Q->(D#E#G)option) cfg (SND ((f:S->P->T#Q) st prog))`
    `z:D#E#G` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  MP_TAC(ISPEC `z:D#E#G` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:D` (X_CHOOSE_THEN `z2:E#G` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `z2:E#G` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:E` (X_CHOOSE_THEN `z4:G` SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND; PAIR_EQ] THEN MESON_TAC[]);;

let BVITAILAUX_state_rel_do_install = prove
 (`!vs (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) v s1.
     bvi_do_install vs s = (Rval (v,s1):(bvl_v#(num#C,FFI)bvi_state,E)result) /\
     bvi_tailrecProof_state_rel s t ==>
     ?t1. bvi_do_install vs t = (Rval (v,t1):(bvl_v#(C,FFI)bvi_state,E)result) /\
          bvi_tailrecProof_state_rel s1 t1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_do_install_Rval) THEN
  RVEQ_TAC THEN
  MP_TAC(ISPEC `cfg:num#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `next1:num` (X_CHOOSE_THEN `cfg0:C` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_tailrec_compile_each next1 (CONS (k,prog) rest)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `next2:num` (X_CHOOSE_THEN `progs2:(num#num#bvi_exp)list`
    ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p2:num#bvi_exp` (X_CHOOSE_THEN `rest2:(num#num#bvi_exp)list`
    SUBST_ALL_TAC) o MATCH_MP BVITAILAUX_compile_each_head) THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP BVITAILAUX_state_rel_input) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `bvi_tailrecProof_state_rel (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[bvi_tailrecProof_state_rel_def] th)) THEN
  UNDISCH_TAC `bvi_state_compile (s:(num#C,FFI)bvi_state) (next1,cfg0) (CONS (k,prog) rest) =
      SOME (bytes,data,FST (bvi_state_compile_oracle s 1))` THEN
  ASM_REWRITE_TAC[BVITAILAUX_state_cc_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg1:C` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `bvi_state_compile_oracle (t:(C,FFI)bvi_state) 0 = (cfg0,CONS (k,p2) rest2)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[state_co_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST (bvi_state_compile_oracle (t:(C,FFI)bvi_state) 1) = cfg1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FST_state_co]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n IN domain (bvi_state_code (t:(C,FFI)bvi_state)) /\
                    n MOD bvl_to_bvi_namespaces = 2 ==> n < next1` ASSUME_TAC THENL
   [UNDISCH_TAC `!n. n IN domain (bvi_state_code (t:(C,FFI)bvi_state)) /\
                     n MOD bvl_to_bvi_namespaces = 2 ==>
                     n < FST (FST (bvi_state_compile_oracle (s:(num#C,FFI)bvi_state) 0))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`next1:num`; `CONS (k,prog) rest:(num#num#bvi_exp)list`; `next2:num`;
                 `CONS (k,p2) rest2:(num#num#bvi_exp)list`;
                 `bvi_state_code (s:(num#C,FFI)bvi_state)`;
                 `bvi_state_code (t:(C,FFI)bvi_state)`] BVITAILAUX_install_disjoint) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `bvi_tailrecProof_input_condition next1 (CONS (k,prog) rest:(num#num#bvi_exp)list)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[bvi_tailrecProof_input_condition_def] th)) THEN
  MP_TAC(INST [`next1:num`,`n:num`; `CONS (k,prog) rest:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
               `next2:num`,`n1:num`; `CONS (k,p2) rest2:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`]
              bvi_tailrecProof_compile_each_ALL_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `bvi_state_code_fupd
      (K (sptree_union (bvi_state_code (t:(C,FFI)bvi_state)) (fromAList (CONS (k,p2) rest2))))
     (bvi_state_compile_oracle_fupd
      (K (shift_seq 1 (bvi_state_compile_oracle t))) t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`v1:bvl_v`; `v2:bvl_v`; `bytes:((8)word)list`;
                         `data:((64)word)list`; `t:(C,FFI)bvi_state`; `cfg0:C`; `k:num`;
                         `p2:num#bvi_exp`; `rest2:(num#num#bvi_exp)list`; `cfg1:C`]
                        BVITAILAUX_do_install_eq_Rval) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_tailrecProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[BVITAILAUX_state_co_shift] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC bvi_tailrecProof_code_rel_union THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INST [`next1:num`,`next:num`;
                         `CONS (k,prog) rest:(num#num#bvi_exp)list`,`prog:(num#num#bvi_exp)list`;
                         `next2:num`,`next1:num`;
                         `CONS (k,p2) rest2:(num#num#bvi_exp)list`,`prog2:(num#num#bvi_exp)list`]
                        bvi_tailrecProof_compile_each_code_rel) THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[domain_fromAList]];
    MATCH_MP_TAC bvi_tailrecProof_namespace_rel_union THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INST [`next1:num`,`next:num`;
                         `CONS (k,prog) rest:(num#num#bvi_exp)list`,`prog:(num#num#bvi_exp)list`;
                         `next2:num`,`next1:num`;
                         `CONS (k,p2) rest2:(num#num#bvi_exp)list`,`prog2:(num#num#bvi_exp)list`]
                        bvi_tailrecProof_compile_each_namespace_rel) THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[domain_fromAList]];
    ASM_REWRITE_TAC[shift_seq_def];
    REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`next1:num`; `CONS (k,prog) rest:(num#num#bvi_exp)list`; `next2:num`;
                         `CONS (k,p2) rest2:(num#num#bvi_exp)list`;
                         `bvi_state_code (t:(C,FFI)bvi_state)`; `n:num`]
                        BVITAILAUX_install_ns_bound) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail, the Op case: do_app and the optimized tail call    *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_do_app_Label = prove
 (`!n vs (s:(A,FFI)bvi_state).
     bvi_do_app (clos_Label n) vs s =
     (if vs = [] /\ n IN domain (bvi_state_code s) then Rval (bvl_CodePtr n,s)
      else Rerr (Rabort Rtype_error))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `vs:bvl_v list` THEN CASE_REWRITE_TAC[NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_bvl_do_app_Build_err = prove
 (`!n vs (s:(A,FFI)bvl_state) e.
     bvl_do_app (BlockOp (Build n)) vs s = Rerr e ==> e = Rabort Rtype_error`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN
  CASES_ON `vs:bvl_v list` THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"] THEN MESON_TAC[]);;

let BVITAILAUX_do_app_Build_err = prove
 (`!n vs (s:(A,FFI)bvi_state) e.
     bvi_do_app (BlockOp (Build n)) vs s = Rerr e ==> e = Rabort Rtype_error`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:const_part list`; `vs:bvl_v list`;
                 `bvi_to_bvl (s:(A,FFI)bvi_state)`] BVITAILAUX_bvl_do_app_Build_err) THEN
  SPEC_TAC(`bvl_do_app (BlockOp (Build n)) vs (bvi_to_bvl (s:(A,FFI)bvi_state))`,
           `res:(bvl_v#(A,FFI)bvl_state,bvl_v)result`) THEN
  GEN_TAC THEN CASES_ON `res:(bvl_v#(A,FFI)bvl_state,bvl_v)result` THEN
  CASE_REWRITE_TAC[] THENL
   [BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[distinctness "result"];
    DISCH_THEN(MP_TAC o SPEC `a:(bvl_v)error_result`) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[injectivity "result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

let BVITAILAUX_do_app_rel = prove
 (`!op vs (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state).
     bvi_tailrecProof_state_rel s t /\
     ~(bvi_do_app op vs s = Rerr (Rabort Rtype_error)) ==>
     (!v s1. bvi_do_app op vs s = Rval (v,s1) ==>
             ?t1. bvi_do_app op vs t = Rval (v,t1) /\ bvi_tailrecProof_state_rel s1 t1) /\
     (!e. bvi_do_app op vs s = Rerr e ==> bvi_do_app op vs t = Rerr e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bvi_do_app_def]) THEN REWRITE_TAC[bvi_do_app_def] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC BVITAILAUX_state_rel_do_install THEN
      EXISTS_TAC `s:(num#C,FFI)bvi_state` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP bvi_do_install_Rerr_type) THEN
      UNDISCH_TAC `~(bvi_do_install vs (s:(num#C,FFI)bvi_state) =
                     (Rerr (Rabort Rtype_error):(bvl_v#(num#C,FFI)bvi_state,exn_or_ret)result))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?l. op = clos_Label l` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BVITAILAUX_do_app_Label]) THEN
    REWRITE_TAC[BVITAILAUX_do_app_Label] THEN
    SUBGOAL_THEN `vs:bvl_v list = [] /\ l IN domain (bvi_state_code (s:(num#C,FFI)bvi_state))`
      STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
                                              is_cond (lhs (dest_neg (concl th))))) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `l IN domain (bvi_state_code (t:(C,FFI)bvi_state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; bvi_tailrecProof_code_rel_domain;
                    bvi_tailrecProof_state_rel_code_rel];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `t:(C,FFI)bvi_state` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand (concl th) = `s1:(num#C,FFI)bvi_state`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(INST [`v:bvl_v`,`r:bvl_v`; `s1:(num#C,FFI)bvi_state`,`s':(num#C,FFI)bvi_state`]
                state_rel_do_app) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:(exn_or_ret)error_result` THEN DISCH_TAC THEN
  ASM_CASES_TAC `?b. op = BlockOp (Build b)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `b:const_part list` SUBST_ALL_TAC) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP BVITAILAUX_do_app_Build_err) THEN
    UNDISCH_TAC `~(bvi_do_app (BlockOp (Build b)) vs (s:(num#C,FFI)bvi_state) =
                   Rerr (Rabort Rtype_error))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC state_rel_do_app_err THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_eval_Call_SOME = prove
 (CASE_TERM
  `!ticks d xs env (s:(A,FFI)bvi_state).
     bvi_evaluate ([bvi_Call ticks (SOME d) xs NONE],env,s) =
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s1) ->
         (match bvl_find_code (SOME d) vs (bvi_state_code s1) with
            NONE -> (Rerr (Rabort Rtype_error),s1)
          | SOME (args,exp) ->
              if bvi_state_clock s1 < ticks + 1 then
                (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s1)
              else
                (match bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1) s1) with
                   (Rval ws,s2) -> (Rval ws,s2)
                 | (Rerr (Rraise (Exn v)),s2) -> (Rerr (Rraise (Exn v)),s2)
                 | (Rerr (Rraise (Ret w)),s2) -> (Rerr (Rabort Rtype_error),s2)
                 | (Rerr (Rabort a),s2) -> (Rerr (Rabort a),s2)))
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (xs,env,s:(A,FFI)bvi_state)`
    `r1:bvi_result` `s1:(A,FFI)bvi_state` THEN
  CASES_ON `r1:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvl_find_code (SOME d) a (bvi_state_code (s1:(A,FFI)bvi_state))`
    `p:bvl_v list # bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([SND (p:bvl_v list # bvi_exp)],FST p,
                                       bvi_dec_clock (ticks + 1) (s1:(A,FFI)bvi_state))`
    `r2:bvi_result` `s2:(A,FFI)bvi_state` THEN
  CASES_ON `r2:bvi_result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a':(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a'':exn_or_ret` THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_ty_rel_REPLICATE_Any = prove
 (`!vs. ty_rel vs (REPLICATE (LENGTH vs) bvi_tailrec_Any)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; REPLICATE; ty_rel_def; ALL2] THEN
  ASM_REWRITE_TAC[GSYM ty_rel_def; distinctness "v_ty"]);;

let BVITAILAUX_env_rel_SNOC = prove
 (`!ty vs vacc.
     ~(ty = bvi_tailrec_Any) /\
     (ty = bvi_tailrec_Int ==> ?k. vacc = bvl_Number k) /\
     (ty = bvi_tailrec_List ==> ?ys. bvl_v_to_list vacc = SOME ys) ==>
     bvi_tailrecProof_env_rel ty T (LENGTH vs) vs (APPEND vs [vacc])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_tailrecProof_env_rel_def; IS_PREFIX_APPEND3; LENGTH_APPEND; LENGTH] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  CASES_ON `ty:v_ty` THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BVITAILAUX_check_exp_scan = prove
 (`!loc arity exp op.
     check_exp loc arity exp = SOME op ==>
     ?tt r. scan_expr (REPLICATE arity bvi_tailrec_Any) loc [exp] = [(tt,op_type op,r,SOME op)]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[check_exp_def; CONJUNCT1 scan_expr_eq; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  BVITAILAUX_OPTION_CASES_TAC
    `SND (SND (SND (scan_expr_sing (REPLICATE arity bvi_tailrec_Any) loc exp)))`
    `op2:assoc_op` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[CONS_11] THEN
  MAP_EVERY EXISTS_TAC
    [`FST (scan_expr_sing (REPLICATE arity bvi_tailrec_Any) loc exp)`;
     `FST (SND (SND (scan_expr_sing (REPLICATE arity bvi_tailrec_Any) loc exp)))`] THEN
  MATCH_MP_TAC(MESON[PAIR] `!(p:A#B#C#D) b d. FST (SND p) = b /\ SND (SND (SND p)) = d ==>
      p = (FST p,b,FST (SND (SND p)),d)`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BVITAILAUX_compile_exp_opt = prove
 (`!loc n arity exp exp_aux exp_opt op.
     bvi_tailrec_compile_exp loc n arity exp = SOME (exp_aux,exp_opt) /\
     check_exp loc arity exp = SOME op ==>
     exp_opt = SND (rewrite loc n op arity (REPLICATE arity bvi_tailrec_Any) exp) /\
     exp_aux = let_wrap arity (id_from_op op) exp_opt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_exp_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

let BVITAILAUX_RESULT_CASES_TAC (r:term) (vs:term) (e:term) : tactic =
  DISJ_CASES_THEN2 (X_CHOOSE_THEN vs SUBST_ALL_TAC) (X_CHOOSE_THEN e SUBST_ALL_TAC)
    (ISPEC r (cases "result"));;

let BVITAILAUX_tail_call_sim = prove
 (`!ticks loc args env1 env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) rc sc ts op n exp
    arity vacc z.
     BVITAILAUX_ert args s /\
     (!t0:(num#C,FFI)bvi_state. bvi_state_clock t0 < bvi_state_clock s ==>
                                BVITAILAUX_ert [exp] t0) /\
     bvi_evaluate ([bvi_Call ticks (SOME loc) args NONE],env1,s) = (rc,sc) /\
     ~(rc = Rerr (Rabort Rtype_error)) /\
     env1 <<= env2 /\ bvi_tailrecProof_state_rel s s' /\ ty_rel env1 ts /\
     lookup loc (bvi_state_code s) = SOME (arity,exp) /\
     optimized_code loc arity exp n (bvi_state_code s') op /\
     ~(op_type op = bvi_tailrec_Any) /\
     (op_type op = bvi_tailrec_Int ==> ?k. vacc = bvl_Number k) /\
     (op_type op = bvi_tailrec_List ==> ?ys. bvl_v_to_list vacc = SOME ys) /\
     (!t0:(C,FFI)bvi_state. bvi_evaluate ([z],env2,t0) = (Rval [vacc],t0)) ==>
     ?rr t1. bvi_evaluate ([bvi_Call ticks (SOME n) (APPEND args [z]) NONE],env2,s') = (rr,t1) /\
             bvi_tailrecProof_state_rel sc t1 /\
             (!e. rc = Rerr e ==> rr = Rerr e) /\
             (!w u. rc = Rval [w] /\
                    (!t0:(C,FFI)bvi_state. bvi_do_app (to_op op) [w; vacc] t0 = Rval (u,t0)) ==>
                    rr = Rval [u])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Call ticks (SOME loc) args NONE],env1,s:(num#C,FFI)bvi_state) =
               (rc,sc)` THEN
  REWRITE_TAC[BVITAILAUX_eval_Call_SOME] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (args,env1,s:(num#C,FFI)bvi_state)`
    `ra:bvi_result` `sa:(num#C,FFI)bvi_state` THEN
  UNDISCH_TAC `BVITAILAUX_ert args (s:(num#C,FFI)bvi_state)` THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `ra:bvi_result`; `sa:(num#C,FFI)bvi_state`;
    `F`; `s':(C,FFI)bvi_state`; `0`; `env2:bvl_v list`; `loc:num`; `ts:v_ty list`;
    `bvi_tailrec_Any`]) THEN
  ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN
  BVITAILAUX_RESULT_CASES_TAC `ra:bvi_result` `vs:bvl_v list` `ea:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC;
    REWRITE_TAC[distinctness "result"; injectivity "result"] THEN STRIP_TAC THEN STRIP_TAC THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ta:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[bvi_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    MAP_EVERY EXISTS_TAC [`Rerr ea:bvi_result`; `ta:(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `ta:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono o check (fun th ->
    concl th = `bvi_evaluate (args,env1,s:(num#C,FFI)bvi_state) = (Rval vs,sa)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o check (fun th ->
    concl th = `bvi_evaluate (args,env1,s:(num#C,FFI)bvi_state) = (Rval vs,sa)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono o check (fun th ->
    concl th = `bvi_evaluate (args,env2,s':(C,FFI)bvi_state) = (Rval vs,ta)`)) THEN
  SUBGOAL_THEN `lookup loc (bvi_state_code (sa:(num#C,FFI)bvi_state)) = SOME (arity,exp)`
    ASSUME_TAC THENL [ASM_MESON_TAC[subspt_lookup]; ALL_TAC] THEN
  UNDISCH_TAC `optimized_code loc arity exp n (bvi_state_code (s':(C,FFI)bvi_state)) op` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[optimized_code_def] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `exp_aux:bvi_exp` (X_CHOOSE_THEN `exp_opt:bvi_exp`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lookup n (bvi_state_code (ta:(C,FFI)bvi_state)) = SOME (arity + 1,exp_opt)`
    ASSUME_TAC THENL [ASM_MESON_TAC[subspt_lookup]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const o check (fun th ->
    concl th = `bvi_tailrecProof_state_rel (sa:(num#C,FFI)bvi_state) (ta:(C,FFI)bvi_state)`)) THEN
  SUBGOAL_THEN `LENGTH (APPEND vs [vacc:bvl_v]) = arity + 1 <=> LENGTH vs = arity`
    ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_find_code_def; bvi_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH (vs:bvl_v list) = arity` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((rc:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`Rerr (Rabort Rtimeout_error):bvi_result`;
                          `bvi_state_clock_fupd (K 0) (ta:(C,FFI)bvi_state)`] THEN
    ASM_SIMP_TAC[bvi_tailrecProof_state_rel_with_clock; injectivity "result";
                 distinctness "result"];
    ALL_TAC] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([exp],vs,bvi_dec_clock (ticks + 1) (sa:(num#C,FFI)bvi_state))`
    `re:bvi_result` `se:(num#C,FFI)bvi_state` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(re:bvi_result = Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) = `(rc:bvi_result,sc:(num#C,FFI)bvi_state)`)) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((rc:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `bvi_dec_clock (ticks + 1) (sa:(num#C,FFI)bvi_state)` o
    check (fun th -> is_forall (concl th) &&
                     can (find_term (fun t -> is_const t &&
                                      fst (dest_const t) = "BVITAILAUX_ert")) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  DISCH_THEN(MP_TAC o SPECL [`vs:bvl_v list`; `re:bvi_result`; `se:(num#C,FFI)bvi_state`; `T`;
    `bvi_dec_clock (ticks + 1) (ta:(C,FFI)bvi_state)`; `arity:num`;
    `APPEND vs [vacc:bvl_v]`; `loc:num`; `REPLICATE arity bvi_tailrec_Any`; `op_type op`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH; ONE] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`op_type op`; `vs:bvl_v list`; `vacc:bvl_v`] BVITAILAUX_env_rel_SNOC) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[bvi_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC bvi_tailrecProof_state_rel_with_clock THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `LENGTH (vs:bvl_v list) = arity`)) THEN
      REWRITE_TAC[BVITAILAUX_ty_rel_REPLICATE_Any]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`op:assoc_op`; `n:num`; `exp:bvi_exp`; `arity:num`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bvi_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BVITAILAUX_optimized_code_subspt THEN
      EXISTS_TAC `bvi_state_code (s':(C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(X_CHOOSE_THEN `tt0:v_ty list` (X_CHOOSE_TAC `r0:bool`) o
        MATCH_MP BVITAILAUX_check_exp_scan) THEN
      MAP_EVERY EXISTS_TAC [`op:assoc_op`; `tt0:v_ty list`; `op_type op`; `r0:bool`] THEN
      ASM_REWRITE_TAC[op_type_lem]];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(CONJUNCT1(MATCH_MP BVITAILAUX_compile_exp_opt
    (CONJ th (ASSUME `check_exp loc arity exp = SOME op`))))]) o check (fun th ->
      is_eq (concl th) && is_comb (lhs (concl th)) &&
      can (find_term (fun t -> is_const t && fst (dest_const t) = "bvi_tailrec_compile_exp"))
          (lhs (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rrr:bvi_result` (X_CHOOSE_THEN `t1o:(C,FFI)bvi_state`
    (X_CHOOSE_THEN `t2o:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `arity < LENGTH (APPEND vs [vacc:bvl_v]) /\ EL arity (APPEND vs [vacc]) = vacc`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `LENGTH (vs:bvl_v list) = arity`)) THEN
    SIMP_TAC[EL_LENGTH_APPEND; NULL; HD; LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate ([apply_op op (bvi_Var arity) exp],APPEND vs [vacc],
                             bvi_dec_clock (ticks + 1) (ta:(C,FFI)bvi_state)) = (rrr,t2o)` THEN
  ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
    `(rc:bvi_result,sc:(num#C,FFI)bvi_state)`)) THEN
  BVITAILAUX_RESULT_CASES_TAC `re:bvi_result` `ws:bvl_v list` `e3:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP o
      check (fun th -> can (find_term ((=) `vs:bvl_v list`)) (concl th) &&
                       rand (concl th) = `(Rval ws:bvi_result,se:(num#C,FFI)bvi_state)`)) THEN
    REWRITE_TAC[HD] THEN
    MP_TAC(ISPEC `bvi_do_app (to_op op) [w; vacc] (t3:(C,FFI)bvi_state)` (cases "result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:bvl_v#(C,FFI)bvi_state` ASSUME_TAC)
                                (X_CHOOSE_THEN `err:(exn_or_ret)error_result` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [(MP_TAC(ISPEC `p:bvl_v#(C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:bvl_v` (X_CHOOSE_THEN `s4:(C,FFI)bvi_state` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP do_app_to_op_state) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`Rval [u]:bvi_result`; `t1o:(C,FFI)bvi_state`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t3:(C,FFI)bvi_state`) THEN
  ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CASE_REWRITE_TAC[] THEN
      EXISTS_TAC (CASE_TERM `FST (match Rerr err with
             Rval ws -> (Rval ws,t1o)
           | Rerr (Rraise (Exn v)) -> (Rerr (Rraise (Exn v)),t1o)
           | Rerr (Rraise (Ret w)) -> (Rerr (Rabort Rtype_error),t1o)
           | Rerr (Rabort a) -> (Rerr (Rabort a),(t1o:(C,FFI)bvi_state)) : bvi_result # (C,FFI)bvi_state)`) THEN
      EXISTS_TAC `t1o:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
      (CONJ_TAC THENL
   [CASES_ON `err:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
    TRY(CASES_ON `a:exn_or_ret` THEN CASE_REWRITE_TAC[]);
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t3:(C,FFI)bvi_state`) THEN
    ASM_REWRITE_TAC[distinctness "result"]])];
    (DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON `e3:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:exn_or_ret` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  ASM_MESON_TAC[])]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail, the Op case: algebra of the accumulator ops and    *)
(* the evaluation of the operands                                            *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_do_app_int_add_mul = prove
 (`!w v u (s:(C,FFI)bvi_state) (t:(C,FFI)bvi_state).
     (bvi_do_app (IntOp clos_Add) [w; v] s = Rval (u,t) ==>
      ?n1 n2. w = bvl_Number n1 /\ v = bvl_Number n2 /\ u = bvl_Number (n1 + n2) /\ t = s) /\
     (bvi_do_app (IntOp Mult) [w; v] s = Rval (u,t) ==>
      ?n1 n2. w = bvl_Number n1 /\ v = bvl_Number n2 /\ u = bvl_Number (n1 * n2) /\ t = s)`,
  REPEAT GEN_TAC THEN SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN
  CONJ_TAC THENL
   [BVITAILAUX_OPTION_CASES_TAC `bvl_do_int_app clos_Add [w; v]` `r0:bvl_v`;
    BVITAILAUX_OPTION_CASES_TAC `bvl_do_int_app Mult [w; v]` `r0:bvl_v`] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSSEMAUX_do_int_app_some) THEN
  REWRITE_TAC[distinctness "int_op"; CONS_11] THEN MESON_TAC[]);;

let BVITAILAUX_do_app_num = prove
 (`!n1 n2 (s:(C,FFI)bvi_state).
     bvi_do_app (IntOp clos_Add) [bvl_Number n1; bvl_Number n2] s = Rval (bvl_Number (n1 + n2),s) /\
     bvi_do_app (IntOp Mult) [bvl_Number n1; bvl_Number n2] s = Rval (bvl_Number (n1 * n2),s)`,
  SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"; bvl_do_int_app_def] THEN
  CASE_REWRITE_TAC[]);;

let BVITAILAUX_INT_ALG_TAC (lem:thm) : tactic =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && (lhs (concl th) = `v:bvl_v` || lhs (concl th) = `a:bvl_v`)))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP lem) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "bvl_v"]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th))))) THEN
  REWRITE_TAC[BVITAILAUX_do_app_num; injectivity "result"; PAIR_EQ; injectivity "bvl_v"] THEN
  REWRITE_TAC[UNWIND_THM1; injectivity "bvl_v"; BVITAILAUX_do_app_num; injectivity "result";
              PAIR_EQ] THEN
  CONJ_TAC THENL [MESON_TAC[]; CONV_TAC INT_RING];;

let BVITAILAUX_op_algebra = prove
 (`!op v w a u (s:(A,B)bvi_state).
     ~(op = Noop) /\ ty_rel [v] [op_type op] /\ ty_rel [a] [op_type op] /\
     (bvi_do_app (to_op op) [w; v] s = Rval (u,s) \/
      (~(op = bvi_tailrec_Append) /\ bvi_do_app (to_op op) [v; w] s = Rval (u,s))) ==>
     ?vacc. (!t0:(C,FFI)bvi_state. bvi_do_app (to_op op) [v; a] t0 = Rval (vacc,t0)) /\
            ty_rel [vacc] [op_type op] /\
            ?u'. (!t0:(C,FFI)bvi_state. bvi_do_app (to_op op) [w; vacc] t0 = Rval (u',t0)) /\
                 (!t0:(C,FFI)bvi_state. bvi_do_app (to_op op) [u; a] t0 = Rval (u',t0))`,
  GEN_TAC THEN CASES_ON `op:assoc_op` THEN
  REWRITE_TAC[to_op_def; op_type_def; distinctness "assoc_op"; BVITAILAUX_ty_rel_SING;
              distinctness "v_ty"] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [BVITAILAUX_INT_ALG_TAC (GEN_ALL(CONJUNCT1(SPEC_ALL BVITAILAUX_do_app_int_add_mul)));
    BVITAILAUX_INT_ALG_TAC (GEN_ALL(CONJUNCT1(SPEC_ALL BVITAILAUX_do_app_int_add_mul)));
    BVITAILAUX_INT_ALG_TAC (GEN_ALL(CONJUNCT2(SPEC_ALL BVITAILAUX_do_app_int_add_mul)));
    BVITAILAUX_INT_ALG_TAC (GEN_ALL(CONJUNCT2(SPEC_ALL BVITAILAUX_do_app_int_add_mul)));
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_do_app_ListAppend_Rval) THEN
  REWRITE_TAC[CONS_11] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[BVITAILAUX_do_app_ListAppend] THEN ASM_REWRITE_TAC[list_to_v_simp] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNWIND_THM1; list_to_v_simp] THEN CASE_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ys'':bvl_v list = ys` SUBST1_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN MESON_TAC[]);;

let BVITAILAUX_eval_Op_term = prove
 (CASE_TERM
  `!cop x y env (s:(A,FFI)bvi_state) v.
     (!s0:(A,FFI)bvi_state. bvi_evaluate ([y],env,s0) = (Rval [v],s0)) ==>
     bvi_evaluate ([bvi_Op cop [x; y]],env,s) =
       (match bvi_evaluate ([x],env,s) with
          (Rval ws,s1) -> (match bvi_do_app cop [v; HD ws] s1 with
                             Rerr e -> (Rerr e,s1)
                           | Rval (u,s2) -> (Rval [u],s2))
        | (Rerr e,s1) -> (Rerr e,s1)) /\
     bvi_evaluate ([bvi_Op cop [y; x]],env,s) =
       (match bvi_evaluate ([x],env,s) with
          (Rval ws,s1) -> (match bvi_do_app cop [HD ws; v] s1 with
                             Rerr e -> (Rerr e,s1)
                           | Rval (u,s2) -> (Rval [u],s2))
        | (Rerr e,s1) -> (Rerr e,s1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [bvi_evaluate_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bvi_evaluate_CONS] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([x],env,s:(A,FFI)bvi_state)`
    `rx:bvi_result` `sx:(A,FFI)bvi_state` THEN
  BVITAILAUX_RESULT_CASES_TAC `rx:bvi_result` `ws:bvl_v list` `e:(exn_or_ret)error_result` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[REVERSE; APPEND] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP) THEN
  REWRITE_TAC[HD; REVERSE; APPEND]);;


let BVITAILAUX_bvl_do_app_ListAppend_err = prove
 (`!vs (s:(A,FFI)bvl_state) e.
     bvl_do_app (BlockOp clos_ListAppend) vs s = Rerr e ==> e = Rabort Rtype_error`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN MESON_TAC[]);;

let BVITAILAUX_do_app_to_op_err = prove
 (`!op vs (s:(C,FFI)bvi_state) e.
     bvi_do_app (to_op op) vs s = Rerr e ==> e = Rabort Rtype_error`,
  GEN_TAC THEN CASES_ON `op:assoc_op` THEN REWRITE_TAC[to_op_def] THENL
   [ALL_TAC; ALL_TAC;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vs:bvl_v list`; `bvi_to_bvl (s:(C,FFI)bvi_state)`]
                  BVITAILAUX_bvl_do_app_ListAppend_err) THEN
    SPEC_TAC(`bvl_do_app (BlockOp clos_ListAppend) vs (bvi_to_bvl (s:(C,FFI)bvi_state))`,
             `res:(bvl_v#(C,FFI)bvl_state,bvl_v)result`) THEN
    GEN_TAC THEN CASES_ON `res:(bvl_v#(C,FFI)bvl_state,bvl_v)result` THEN
    CASE_REWRITE_TAC[] THENL
     [BVITAILAUX_PAIR_TAC THEN REWRITE_TAC[distinctness "result"];
      DISCH_THEN(MP_TAC o SPEC `a:(bvl_v)error_result`) THEN REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[injectivity "result"] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[BVITAILAUX_do_app_IntOp; distinctness "int_op"] THEN REPEAT GEN_TAC THENL
   [BVITAILAUX_OPTION_CASES_TAC `bvl_do_int_app clos_Add vs` `r0:bvl_v`;
    BVITAILAUX_OPTION_CASES_TAC `bvl_do_int_app Mult vs` `r0:bvl_v`;
    BVITAILAUX_OPTION_CASES_TAC `bvl_do_int_app clos_Mod vs` `r0:bvl_v`] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;

let BVITAILAUX_op_typed = prove
 (`!op v a.
     ~(op = Noop) /\ ty_rel [v] [op_type op] /\ ty_rel [a] [op_type op] ==>
     ?vacc. (!t0:(C,FFI)bvi_state. bvi_do_app (to_op op) [v; a] t0 = Rval (vacc,t0)) /\
            ty_rel [vacc] [op_type op]`,
  GEN_TAC THEN CASES_ON `op:assoc_op` THEN
  REWRITE_TAC[to_op_def; op_type_def; distinctness "assoc_op"; BVITAILAUX_ty_rel_SING;
              distinctness "v_ty"] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BVITAILAUX_do_app_num; BVITAILAUX_do_app_ListAppend] THEN
  CASE_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  REWRITE_TAC[UNWIND_THM1; injectivity "bvl_v"; list_to_v_simp] THEN MESON_TAC[]);;

let BVITAILAUX_env_rel_T = prove
 (`!ty acc env1 env2.
     bvi_tailrecProof_env_rel ty T acc env1 env2 ==>
     env1 <<= env2 /\ LENGTH env1 = acc /\ acc < LENGTH env2 /\
     ~(ty = bvi_tailrec_Any) /\ ty_rel [EL acc env2] [ty]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrecProof_env_rel_def; BVITAILAUX_ty_rel_SING] THEN
  CASES_ON `ty:v_ty` THEN CASE_REWRITE_TAC[distinctness "v_ty"] THEN
  REWRITE_TAC[GT] THEN MESON_TAC[]);;

let BVITAILAUX_ty_case_rel = prove
 (CASE_TERM
  `!ty v. (match ty with
             bvi_tailrec_Int -> ?k. v = bvl_Number k
           | bvi_tailrec_List -> ?ys. bvl_v_to_list v = SOME ys
           | _ -> T) <=> ty_rel [v] [ty]`,
  GEN_TAC THEN CASES_ON `ty:v_ty` THEN
  REWRITE_TAC[BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN CASE_REWRITE_TAC[]);;

let BVITAILAUX_term_ok_values = prove
 (`!y ts ty env1 env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state).
     BVITAILAUX_ert [y] s /\ term_ok ts ty y /\ ty_rel env1 ts /\ env1 <<= env2 /\
     bvi_tailrecProof_state_rel s s' ==>
     ?v. (!s0:(num#C,FFI)bvi_state. bvi_evaluate ([y],env1,s0) = (Rval [v],s0)) /\
         (!t0:(C,FFI)bvi_state. bvi_evaluate ([y],env2,t0) = (Rval [v],t0)) /\
         ty_rel [v] [ty]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `bvi_evaluate ([y],env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(num#C,FFI)bvi_state`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ts:v_ty list`; `ty:v_ty`; `y:bvi_exp`; `env1:bvl_v list`;
                 `s:(num#C,FFI)bvi_state`; `r1:bvi_result`; `s1:(num#C,FFI)bvi_state`]
                term_ok_SING) THEN
  ASM_REWRITE_TAC[BVITAILAUX_ty_case_rel] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (X_CHOOSE_THEN `v:bvl_v` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `r1:bvi_result = Rval [v]`)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `rest:bvl_v list` ASSUME_TAC o REWRITE_RULE[IS_PREFIX_APPEND] o
    check (fun th -> concl th = `(env1:bvl_v list) <<= env2`)) THEN
  SUBGOAL_THEN `ty_rel env2 (APPEND ts (REPLICATE (LENGTH (rest:bvl_v list)) bvi_tailrec_Any))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ty_rel_APPEND THEN
    ASM_REWRITE_TAC[BVITAILAUX_ty_rel_REPLICATE_Any];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([y],env2,s':(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:bvi_result` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`APPEND ts (REPLICATE (LENGTH (rest:bvl_v list)) bvi_tailrec_Any)`; `ty:v_ty`;
                 `y:bvi_exp`; `env2:bvl_v list`;
                 `s':(C,FFI)bvi_state`; `r2:bvi_result`; `s2:(C,FFI)bvi_state`]
                term_ok_SING) THEN
  ASM_SIMP_TAC[term_ok_extend; BVITAILAUX_ty_case_rel] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (X_CHOOSE_THEN `v2:bvl_v` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `r2:bvi_result = Rval [v2]`)) THEN
  UNDISCH_TAC `BVITAILAUX_ert [y] (s:(num#C,FFI)bvi_state)` THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `Rval [v]:bvi_result`;
    `s:(num#C,FFI)bvi_state`; `F`; `s':(C,FFI)bvi_state`; `0`; `env2:bvl_v list`; `0`;
    `ts:v_ty list`; `bvi_tailrec_Any`]) THEN
  ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def; distinctness "result"; IS_PREFIX_APPEND3] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` (MP_TAC o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ; CONS_11] THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT1) THEN
  EXISTS_TAC `v:bvl_v` THEN ASM_REWRITE_TAC[]);;

let BVITAILAUX_ert_Op_main = prove
 (`!cop xs (s:(num#C,FFI)bvi_state) env1 env2 r t (s':(C,FFI)bvi_state) ts.
     BVITAILAUX_ert xs s /\
     bvi_evaluate ([bvi_Op cop xs],env1,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) /\
     env1 <<= env2 /\ bvi_tailrecProof_state_rel s s' /\ ty_rel env1 ts ==>
     ?t'. bvi_evaluate ([bvi_Op cop xs],env2,s') = (r,t') /\ bvi_tailrecProof_state_rel t t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Op cop xs],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)`
    `r0:bvi_result` `s2:(num#C,FFI)bvi_state` THEN
  UNDISCH_TAC `BVITAILAUX_ert xs (s:(num#C,FFI)bvi_state)` THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r0:bvi_result`; `s2:(num#C,FFI)bvi_state`;
    `F`; `s':(C,FFI)bvi_state`; `0`; `env2:bvl_v list`; `0`; `ts:v_ty list`;
    `bvi_tailrec_Any`]) THEN
  ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN
  BVITAILAUX_RESULT_CASES_TAC `r0:bvi_result` `vs:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[distinctness "result"; injectivity "result"] THENL
   [DISCH_THEN(X_CHOOSE_THEN `t0:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cop:clos_op`; `REVERSE (vs:bvl_v list)`; `s2:(num#C,FFI)bvi_state`;
                   `t0:(C,FFI)bvi_state`] BVITAILAUX_do_app_rel) THEN
    MP_TAC(ISPEC `bvi_do_app cop (REVERSE vs) (s2:(num#C,FFI)bvi_state)` (cases "result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:bvl_v#(num#C,FFI)bvi_state` ASSUME_TAC)
                                (X_CHOOSE_THEN `e:(exn_or_ret)error_result` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
      `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `p:bvl_v#(num#C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `s3:(num#C,FFI)bvi_state`
        SUBST_ALL_TAC)) THEN
      CASE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:bvl_v`; `s3:(num#C,FFI)bvi_state`]) THEN REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `e:(exn_or_ret)error_result`) THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN EXISTS_TAC `t0:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[]];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand (concl th) = `r:bvi_result`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand (concl th) = `t:(num#C,FFI)bvi_state`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t0:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let BVITAILAUX_size_Op_Call = prove
 (`!c ticks d args h y.
     list_size bvi_exp_size [y] < list_size bvi_exp_size [bvi_Op c [bvi_Call ticks d args h; y]] /\
     list_size bvi_exp_size args < list_size bvi_exp_size [bvi_Op c [bvi_Call ticks d args h; y]] /\
     list_size bvi_exp_size [y] < list_size bvi_exp_size [bvi_Op c [y; bvi_Call ticks d args h]] /\
     list_size bvi_exp_size args < list_size bvi_exp_size [bvi_Op c [y; bvi_Call ticks d args h]]`,
  REWRITE_TAC[list_size] THEN
  REWRITE_TAC(type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp") THEN
  REWRITE_TAC[list_size] THEN ARITH_TAC);;

let BVITAILAUX_src_do_app = prove
 (CASE_TERM
  `!op l (sc:(num#C,FFI)bvi_state) r t.
     (match bvi_do_app (to_op op) l sc with
        Rval (u,s2) -> (Rval [u],s2)
      | Rerr e -> (Rerr e,sc)) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     ?u. r = Rval [u] /\ t = sc /\ bvi_do_app (to_op op) l sc = Rval (u,sc)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `bvi_do_app (to_op op) l (sc:(num#C,FFI)bvi_state)` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:bvl_v#(num#C,FFI)bvi_state` ASSUME_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `p:bvl_v#(num#C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:bvl_v` (X_CHOOSE_THEN `s2:(num#C,FFI)bvi_state`
      SUBST_ALL_TAC)) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP do_app_to_op_state) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP BVITAILAUX_do_app_to_op_err) THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

let BVITAILAUX_SRC_TAC : tactic =
  FIRST [DISCH_TAC THEN X_GEN_TAC `w:bvl_v` THEN DISCH_THEN SUBST_ALL_TAC THEN
         RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
         FIRST_X_ASSUM(MP_TAC o MATCH_MP BVITAILAUX_src_do_app o
           C CONJ (ASSUME `~((r:bvi_result) = Rerr (Rabort Rtype_error))`) o
           check (fun th -> rand (concl th) = `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
         DISCH_THEN(X_CHOOSE_THEN `u:bvl_v` STRIP_ASSUME_TAC) THEN EXISTS_TAC `u:bvl_v` THEN
         ASM_REWRITE_TAC[];
         REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]];;

let BVITAILAUX_ert_Op_tail = prove
 (`!ticks loc args y op xs (s:(num#C,FFI)bvi_state) env1 env2 r t (s':(C,FFI)bvi_state) t'
    acc ts n exp arity.
     BVITAILAUX_ertIH [bvi_Op (to_op op) xs] s /\
     ((xs = [bvi_Call ticks (SOME loc) args NONE; y] /\ ~(op = bvi_tailrec_Append)) \/
      xs = [y; bvi_Call ticks (SOME loc) args NONE]) /\
     term_ok ts (op_type op) y /\
     bvi_evaluate ([bvi_Op (to_op op) xs],env1,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) /\
     bvi_tailrecProof_env_rel (op_type op) T acc env1 env2 /\
     bvi_tailrecProof_state_rel s s' /\ ty_rel env1 ts /\
     lookup loc (bvi_state_code s) = SOME (arity,exp) /\
     optimized_code loc arity exp n (bvi_state_code s') op /\
     bvi_evaluate ([bvi_Op (to_op op) xs],env2,s') = (r,t') /\ bvi_tailrecProof_state_rel t t' ==>
     ?rrr t1 t2.
       bvi_evaluate ([bvi_Call ticks (SOME n) (APPEND args [apply_op op (bvi_Var acc) y]) NONE],
                     env2,s') = (rrr,t1) /\
       bvi_evaluate ([apply_op op (bvi_Var acc) (bvi_Op (to_op op) xs)],env2,s') = (rrr,t2) /\
       bvi_tailrecProof_state_rel t t1 /\ bvi_tailrecProof_state_rel t t2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih" o REWRITE_RULE[BVITAILAUX_ertIH_def])
    (CONJUNCTS_THEN2 (LABEL_TAC "xs")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_T) THEN
  SUBGOAL_THEN `~(op = Noop)` ASSUME_TAC THENL [ASM_REWRITE_TAC[op_type_lem]; ALL_TAC] THEN
  SUBGOAL_THEN `list_size bvi_exp_size [y] < list_size bvi_exp_size [bvi_Op (to_op op) xs] /\
                list_size bvi_exp_size args < list_size bvi_exp_size [bvi_Op (to_op op) xs]`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "xs" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[BVITAILAUX_size_Op_Call];
    ALL_TAC] THEN
  SUBGOAL_THEN `BVITAILAUX_ert [y] (s:(num#C,FFI)bvi_state) /\
                BVITAILAUX_ert args (s:(num#C,FFI)bvi_state) /\
                (!t0:(num#C,FFI)bvi_state. bvi_state_clock t0 < bvi_state_clock s ==>
                                           BVITAILAUX_ert [exp] t0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY GEN_TAC THEN TRY DISCH_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:bvi_exp`; `ts:v_ty list`; `op_type op`; `env1:bvl_v list`;
                 `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`]
                BVITAILAUX_term_ok_values) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`op:assoc_op`; `v:bvl_v`; `EL acc (env2:bvl_v list)`]
                (INST_TYPE [`:C`,`:C`; `:FFI`,`:FFI`] BVITAILAUX_op_typed)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `vacc:bvl_v` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t0:(C,FFI)bvi_state.
     bvi_evaluate ([apply_op op (bvi_Var acc) y],env2,t0) = (Rval [vacc],t0)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN CASE_REWRITE_TAC[HD] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Call ticks (SOME loc) args NONE],env1,
                              s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rc:bvi_result` (X_CHOOSE_THEN `sc:(num#C,FFI)bvi_state`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(!e. (rc:bvi_result) = Rerr e ==>
                     (r:bvi_result) = Rerr e /\ t = (sc:(num#C,FFI)bvi_state)) /\
                (!w. rc = Rval [w] ==>
                     ?u. r = Rval [u] /\ t = sc /\
                         (bvi_do_app (to_op op) [w; v] sc = Rval (u,sc) \/
                          (~(op = bvi_tailrec_Append) /\
                           bvi_do_app (to_op op) [v; w] sc = Rval (u,sc))))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Op (to_op op) xs],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    MP_TAC(ISPECL [`to_op op`; `bvi_Call ticks (SOME loc) args NONE`; `y:bvi_exp`;
                   `env1:bvl_v list`; `s:(num#C,FFI)bvi_state`; `v:bvl_v`]
                  BVITAILAUX_eval_Op_term) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "xs" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    BVITAILAUX_RESULT_CASES_TAC `rc:bvi_result` `ws:bvl_v list` `ec:(exn_or_ret)error_result` THEN
    CASE_REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
    BVITAILAUX_SRC_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((rc:bvi_result) = Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITAILAUX_ty_rel_SING] o
    check (fun th -> concl th = `ty_rel [vacc] [op_type op]`)) THEN
  MP_TAC(ISPECL [`ticks:num`; `loc:num`; `args:bvi_exp list`; `env1:bvl_v list`;
                 `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
                 `rc:bvi_result`; `sc:(num#C,FFI)bvi_state`; `ts:v_ty list`; `op:assoc_op`;
                 `n:num`; `exp:bvi_exp`; `arity:num`; `vacc:bvl_v`;
                 `apply_op op (bvi_Var acc) y`] BVITAILAUX_tail_call_sim) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:bvi_result` (X_CHOOSE_THEN `t1:(C,FFI)bvi_state`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN
  BVITAILAUX_RESULT_CASES_TAC `rc:bvi_result` `ws:bvl_v list` `ec:(exn_or_ret)error_result` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `ec:(exn_or_ret)error_result` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `sc:(num#C,FFI)bvi_state`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst (dest_const t) = "bvi_do_app"))
             (concl th)))) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result"]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`Rerr ec:bvi_result`; `t1:(C,FFI)bvi_state`; `t':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP o
    check (fun th -> rand (concl th) = `(Rval ws:bvi_result,sc:(num#C,FFI)bvi_state)`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:bvl_v` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst (dest_const t) = "bvi_do_app")) (concl th) &&
    can (find_term ((=) `sc:(num#C,FFI)bvi_state`)) (concl th))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:bvl_v` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`op:assoc_op`; `v:bvl_v`; `w:bvl_v`; `EL acc (env2:bvl_v list)`; `u:bvl_v`;
                 `sc:(num#C,FFI)bvi_state`] BVITAILAUX_op_algebra) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vacc':bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u':bvl_v` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `vacc':bvl_v = vacc` SUBST_ALL_TAC THENL
   [MP_TAC(TRANS (SYM (SPEC `t':(C,FFI)bvi_state` (ASSUME `!t0:(C,FFI)bvi_state.
       bvi_do_app (to_op op) [v; EL acc env2] t0 = Rval (vacc',t0)`)))
      (SPEC `t':(C,FFI)bvi_state` (ASSUME `!t0:(C,FFI)bvi_state.
       bvi_do_app (to_op op) [v; EL acc env2] t0 = Rval (vacc,t0)`))) THEN
    REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:bvl_v`; `u':bvl_v`] o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `rr:bvi_result`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst (dest_const t) = "bvi_do_app")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`Rval [u']:bvi_result`; `t1:(C,FFI)bvi_state`;
                        `t':(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[]);;

let BVITAILAUX_is_rec_Call = prove
 (`!loc x. bvi_tailrec_is_rec loc x <=> ?ticks args. x = bvi_Call ticks (SOME loc) args NONE`,
  REPEAT GEN_TAC THEN CASES_ON `x:bvi_exp` THEN
  REWRITE_TAC[bvi_tailrec_is_rec_def; distinctness "bvi_exp"; injectivity "bvi_exp"] THEN
  CASES_ON `a3:bvi_exp option` THEN
  REWRITE_TAC[bvi_tailrec_is_rec_def; distinctness "option"] THEN MESON_TAC[]);;

let BVITAILAUX_check_op_cases = prove
 (`!ts opr loc exp expr.
     check_op ts opr loc exp = SOME expr ==>
     ?ticks args y. term_ok ts (op_type opr) y /\ ~(opr = Noop) /\
       expr = bvi_Op (to_op opr) [y; bvi_Call ticks (SOME loc) args NONE] /\
       ((exp = bvi_Op (to_op opr) [bvi_Call ticks (SOME loc) args NONE; y] /\
         ~(opr = bvi_tailrec_Append)) \/
        exp = bvi_Op (to_op opr) [y; bvi_Call ticks (SOME loc) args NONE])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP BVITAILAUX_check_op_SOME) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `x:bvi_exp` (X_CHOOSE_THEN `y:bvi_exp` STRIP_ASSUME_TAC) o
    MATCH_MP check_op_thm) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ticks:num` (X_CHOOSE_THEN `args:bvi_exp list` SUBST_ALL_TAC) o
    REWRITE_RULE[BVITAILAUX_is_rec_Call] o
    check (fun th -> can (find_term (fun t -> is_const t &&
                                       fst (dest_const t) = "bvi_tailrec_is_rec")) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`ticks:num`; `args:bvi_exp list`; `y:bvi_exp`] THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~bvi_tailrec_is_rec loc y` ASSUME_TAC THENL
   [ASM_MESON_TAC[is_rec_term_ok]; ALL_TAC] THEN
  UNDISCH_TAC `check_op ts bvi_tailrec_Append loc exp = SOME expr` THEN
  ASM_REWRITE_TAC[check_op_def; try_swap_def] THEN
  SUBGOAL_THEN `opbinargs bvi_tailrec_Append
      (bvi_Op (to_op bvi_tailrec_Append) [bvi_Call ticks (SOME loc) args NONE; y]) =
      SOME (bvi_Call ticks (SOME loc) args NONE,y)` SUBST1_TAC THENL
   [REWRITE_TAC[opbinargs_SOME; distinctness "assoc_op"] THEN MESON_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* the Op case of evaluate_rewrite_tail *)
let BVITAILAUX_ert_Op = prove
 (`!cop xs (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Op cop xs] s ==>
     BVITAILAUX_ert [bvi_Op cop xs] s`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> LABEL_TAC "ihp" th THEN
    LABEL_TAC "ih" (REWRITE_RULE[BVITAILAUX_ertIH_def] th)) THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `BVITAILAUX_ert xs (s:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [USE_THEN "ih" MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL; list_size] THEN
    REWRITE_TAC(type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp") THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(env1:bvl_v list) <<= env2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN
    SIMP_TAC[bvi_tailrecProof_env_rel_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cop:clos_op`; `xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
                 `env1:bvl_v list`; `env2:bvl_v list`; `r:bvi_result`;
                 `t:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`; `ts:v_ty list`]
                BVITAILAUX_ert_Op_main) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvi_tailrecProof_env_rel ty T acc env1 env2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_T) THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[rewrite_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `check_op ts op loc (bvi_Op cop xs)` `e':bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`op:assoc_op`; `acc:num`; `bvi_Op cop xs`; `env2:bvl_v list`;
                   `s':(C,FFI)bvi_state`; `r:bvi_result`; `t':(C,FFI)bvi_state`]
                  BVITAILAUX_eval_apply_op_state) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `rr:bvi_result`) THEN
    MAP_EVERY EXISTS_TAC [`rr:bvi_result`; `t':(C,FFI)bvi_state`; `t':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ticks:num` (X_CHOOSE_THEN `args:bvi_exp list`
    (X_CHOOSE_THEN `y:bvi_exp` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))))) o
    MATCH_MP BVITAILAUX_check_op_cases) THEN
  SUBGOAL_THEN `cop = to_op op` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[injectivity "bvi_exp"] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[injectivity "bvi_exp"] o check (is_disj o concl)) THEN
  SUBGOAL_THEN `opbinargs op (bvi_Op (to_op op) [y; bvi_Call ticks (SOME loc) args NONE]) =
                SOME (y,bvi_Call ticks (SOME loc) args NONE)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[opbinargs_SOME] THEN MESON_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[args_from_def; push_call_def; SND] THEN
  MATCH_MP_TAC BVITAILAUX_ert_Op_tail THEN
  MAP_EVERY EXISTS_TAC [`loc:num`; `s:(num#C,FFI)bvi_state`; `env1:bvl_v list`;
    `r:bvi_result`; `t':(C,FFI)bvi_state`; `ts:v_ty list`; `exp:bvi_exp`; `arity:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `op_type op = ty`)]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail: calls through related code (Force, Call)          *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_op_id = prove
 (`!op w (t0:(C,FFI)bvi_state).
     ~(op = Noop) /\ ty_rel [w] [op_type op] ==>
     bvi_do_app (to_op op) [w; op_id_val op] t0 = Rval (w,t0)`,
  GEN_TAC THEN CASES_ON `op:assoc_op` THEN
  REWRITE_TAC[to_op_def; op_type_def; op_id_val_def; distinctness "assoc_op";
              BVITAILAUX_ty_rel_SING; distinctness "v_ty"] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BVITAILAUX_do_app_num; INT_ADD_RID; INT_MUL_RID;
                  BVITAILAUX_do_app_ListAppend; bvl_v_to_list_def] THEN
  CASE_REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[list_to_v_imp]);;

let BVITAILAUX_env_rel_wrap = prove
 (`!op args. ~(op = Noop) ==>
     bvi_tailrecProof_env_rel (op_type op) T (LENGTH args) args
       (APPEND (APPEND args [op_id_val op]) args)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[bvi_tailrecProof_env_rel_def; IS_PREFIX_APPEND3; LENGTH_APPEND; LENGTH] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `op:assoc_op` THEN
  REWRITE_TAC[op_type_def; op_id_val_def; distinctness "assoc_op"] THEN
  CASE_REWRITE_TAC[bvl_v_to_list_def] THEN MESON_TAC[]);;

let BVITAILAUX_code_rel_call = prove
 (`!loc arity exp args (s0:(num#C,FFI)bvi_state) (t0:(C,FFI)bvi_state) re se.
     BVITAILAUX_ert [exp] s0 /\
     bvi_evaluate ([exp],args,s0) = (re,se) /\ ~(re = Rerr (Rabort Rtype_error)) /\
     lookup loc (bvi_state_code s0) = SOME (arity,exp) /\ LENGTH args = arity /\
     bvi_tailrecProof_state_rel s0 t0 ==>
     ?exp' t1. lookup loc (bvi_state_code t0) = SOME (arity,exp') /\
               bvi_evaluate ([exp'],args,t0) = (re,t1) /\ bvi_tailrecProof_state_rel se t1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tailrecProof_state_rel_code_rel) THEN
  REWRITE_TAC[bvi_tailrecProof_code_rel_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`]) THEN ASM_REWRITE_TAC[] THEN
  BVITAILAUX_OPTION_CASES_TAC `check_exp loc arity exp` `op:assoc_op` THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [ALL_TAC;
    DISCH_TAC THEN
    EXISTS_TAC `exp:bvi_exp` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `BVITAILAUX_ert [exp] (s0:(num#C,FFI)bvi_state)` THEN
    REWRITE_TAC[BVITAILAUX_ert_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`args:bvl_v list`; `re:bvi_result`; `se:(num#C,FFI)bvi_state`;
      `F`; `t0:(C,FFI)bvi_state`; `0`; `args:bvl_v list`; `loc:num`;
      `REPLICATE arity bvi_tailrec_Any`; `bvi_tailrec_Any`]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `LENGTH (args:bvl_v list) = arity`)) THEN
    ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def; IS_PREFIX_REFL; BVITAILAUX_ty_rel_REPLICATE_Any] THEN
    MESON_TAC[]] THEN
  DISCH_THEN(MP_TAC o SPEC `op:assoc_op`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPECL [`loc:num`; `n:num`; `arity:num`; `exp:bvi_exp`; `op:assoc_op`]
                BVITAILAUX_compile_exp_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `exp_aux:bvi_exp` (X_CHOOSE_TAC `exp_opt:bvi_exp`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`loc:num`; `n:num`; `arity:num`; `exp:bvi_exp`; `exp_aux:bvi_exp`;
                 `exp_opt:bvi_exp`; `op:assoc_op`] BVITAILAUX_compile_exp_opt) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tt0:v_ty list` (X_CHOOSE_TAC `r0:bool`) o
    MATCH_MP BVITAILAUX_check_exp_scan) THEN
  SUBGOAL_THEN `~(op = Noop)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP scan_expr_not_Noop); ALL_TAC] THEN
  EXISTS_TAC `exp_aux:bvi_exp` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `LENGTH (args:bvl_v list) = arity`)) THEN
  ASM_SIMP_TAC[evaluate_let_wrap] THEN
  UNDISCH_TAC `BVITAILAUX_ert [exp] (s0:(num#C,FFI)bvi_state)` THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD] THEN
  DISCH_THEN(MP_TAC o SPECL [`args:bvl_v list`; `re:bvi_result`; `se:(num#C,FFI)bvi_state`;
    `T`; `t0:(C,FFI)bvi_state`; `LENGTH (args:bvl_v list)`;
    `APPEND (APPEND args [op_id_val op]) args`; `loc:num`;
    `REPLICATE (LENGTH (args:bvl_v list)) bvi_tailrec_Any`; `op_type op`]) THEN
  ASM_SIMP_TAC[BVITAILAUX_env_rel_wrap; BVITAILAUX_ty_rel_REPLICATE_Any; LENGTH; ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(MP_TAC o SPECL [`op:assoc_op`; `n:num`; `exp:bvi_exp`;
                             `LENGTH (args:bvl_v list)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[optimized_code_def] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`exp_aux:bvi_exp`; `exp_opt:bvi_exp`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`op:assoc_op`; `tt0:v_ty list`; `op_type op`; `r0:bool`] THEN
      ASM_REWRITE_TAC[GSYM op_type_lem]];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `rrr:bvi_result` (X_CHOOSE_THEN `t1:(C,FFI)bvi_state`
    (X_CHOOSE_THEN `t2:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bvi_evaluate ([apply_op op (bvi_Var (LENGTH (args:bvl_v list))) exp],
       APPEND (APPEND args [op_id_val op]) args,(t0:(C,FFI)bvi_state)) = (rrr,t2)` THEN
  SUBGOAL_THEN `LENGTH (args:bvl_v list) < LENGTH (APPEND (APPEND args [op_id_val op]) args) /\
                EL (LENGTH args) (APPEND (APPEND args [op_id_val op]) args) = op_id_val op`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH] THEN
    SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[BVITAILAUX_eval_apply_op] THEN
  BVITAILAUX_RESULT_CASES_TAC `re:bvi_result` `ws:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP o
      check (fun th -> concl th =
        `bvi_evaluate ([exp],args,s0:(num#C,FFI)bvi_state) = (Rval ws,se)`)) THEN
    MP_TAC(ISPECL [`REPLICATE (LENGTH (args:bvl_v list)) bvi_tailrec_Any`; `loc:num`;
                   `[exp:bvi_exp]`; `args:bvl_v list`;
                   `[tt0,op_type op,r0,SOME op]:(v_ty list#v_ty#bool#assoc_op option)list`;
                   `s0:(num#C,FFI)bvi_state`; `[w:bvl_v]`; `se:(num#C,FFI)bvi_state`]
                  scan_expr_ty_rel) THEN
    ASM_REWRITE_TAC[BVITAILAUX_ty_rel_REPLICATE_Any; ALL; MAP; o_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[BVITAILAUX_op_id; HD] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

(* the Force case of evaluate_rewrite_tail *)
let BVITAILAUX_ert_Force = prove
 (`!fl n (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Force fl n] s ==>
     BVITAILAUX_ert [bvi_Force fl n] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD; BVITAILAUX_scan_simple; CONS_11; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(env1:bvl_v list) <<= env2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN
    SIMP_TAC[bvi_tailrecProof_env_rel_def];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `rest:bvl_v list` SUBST_ALL_TAC o REWRITE_RULE[IS_PREFIX_APPEND] o
    check (fun th -> concl th = `(env1:bvl_v list) <<= env2`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const) THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_CASES_TAC `n < LENGTH (env1:bvl_v list)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `n < LENGTH (APPEND env1 rest:bvl_v list) /\
                EL n (APPEND env1 rest) = EL n (env1:bvl_v list)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EL_APPEND; LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  MP_TAC(ISPEC `bvi_dest_thunk (EL n env1) (bvi_state_refs (s:(num#C,FFI)bvi_state))`
           (cases "bvi_dest_thunk_ret")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `md:thunk_mode` (X_CHOOSE_THEN `f:bvl_v` SUBST1_TAC)) THEN
  CASES_ON `md:thunk_mode` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN EXISTS_TAC `s':(C,FFI)bvi_state` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_find_code_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `lookup fl (bvi_state_code (s:(num#C,FFI)bvi_state))`
    `p:num#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `p:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH [EL n env1; f:bvl_v] = arity` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tailrecProof_state_rel_code_rel o check (fun th ->
    concl th = `bvi_tailrecProof_state_rel (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state)`)) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(X_CHOOSE_TAC `exp2:bvi_exp` o MATCH_MP BVITAILAUX_code_rel_lookup o CONJ th o
    check (fun th -> concl th = `lookup fl (bvi_state_code (s:(num#C,FFI)bvi_state)) = SOME (arity,exp)`))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bvi_state_clock (s:(num#C,FFI)bvi_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `bvi_state_clock_fupd (K 0) (s':(C,FFI)bvi_state)` THEN
    ASM_SIMP_TAC[bvi_tailrecProof_state_rel_with_clock];
    ALL_TAC] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([exp],[EL n env1; f],
                                       bvi_dec_clock 1 (s:(num#C,FFI)bvi_state))`
    `re:bvi_result` `se:(num#C,FFI)bvi_state` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(re:bvi_result = Rerr (Rabort Rtype_error)) /\
                (!w. ~(re = Rerr (Rraise (Ret w)))) /\ re = (r:bvi_result) /\
                (se:(num#C,FFI)bvi_state) = t`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
      `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
    BVITAILAUX_RESULT_CASES_TAC `re:bvi_result` `ws:bvl_v list` `e:(exn_or_ret)error_result` THEN
    CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
    TRY(CASES_ON `e:(exn_or_ret)error_result` THEN
        CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"; distinctness "error_result"] THEN
        TRY(CASES_ON `a:exn_or_ret` THEN
            CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
                             distinctness "error_result"; distinctness "exn_or_ret"])) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fl:num`; `arity:num`; `exp:bvi_exp`; `[EL n env1; f:bvl_v]`;
                 `bvi_dec_clock 1 (s:(num#C,FFI)bvi_state)`;
                 `bvi_dec_clock 1 (s':(C,FFI)bvi_state)`; `re:bvi_result`;
                 `se:(num#C,FFI)bvi_state`] BVITAILAUX_code_rel_call) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[bvi_dec_clock_code] THEN CONJ_TAC THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
      REWRITE_TAC[bvi_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC bvi_tailrecProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_dec_clock_code] THEN
  DISCH_THEN(X_CHOOSE_THEN `exp':bvi_exp` (X_CHOOSE_THEN `t1:(C,FFI)bvi_state`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `exp2:bvi_exp = exp'` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `lookup fl (bvi_state_code (s':(C,FFI)bvi_state)) = SOME (arity,exp2)` THEN
    ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN EXISTS_TAC `t1:(C,FFI)bvi_state` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `re:bvi_result = r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `se:(num#C,FFI)bvi_state = t`)) THEN
  ASM_REWRITE_TAC[] THEN
  BVITAILAUX_RESULT_CASES_TAC `r:bvi_result` `ws:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `e:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:exn_or_ret` THEN CASE_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) && is_neg (snd (dest_forall (concl th))))) THEN
  REWRITE_TAC[NOT_FORALL_THM; injectivity "result"; injectivity "error_result";
              injectivity "exn_or_ret"] THEN MESON_TAC[]);;

(* the Call case of evaluate_rewrite_tail *)
let BVITAILAUX_find_code_lookup = prove
 (`!dest vs (c:(num#bvi_exp)spt) args exp.
     bvl_find_code dest vs c = SOME (args,exp) ==>
     ?loc. lookup loc c = SOME (LENGTH args,exp) /\
           !(c':(num#bvi_exp)spt) e'. lookup loc c' = SOME (LENGTH args,e') ==>
                                      bvl_find_code dest vs c' = SOME (args,e')`,
  GEN_TAC THEN CASES_ON `dest:num option` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_find_code_def] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `LAST (vs:bvl_v list)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    BVITAILAUX_OPTION_CASES_TAC `lookup a (c:(num#bvi_exp)spt)` `p:num#bvi_exp` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `p:num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `a:num` THEN
    SUBGOAL_THEN `LENGTH (args:bvl_v list) = ar` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand (concl th) = `args:bvl_v list`)) THEN
      ASM_SIMP_TAC[LENGTH_FRONT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[option_INJ; PAIR_EQ];
    BVITAILAUX_OPTION_CASES_TAC `lookup a (c:(num#bvi_exp)spt)` `p:num#bvi_exp` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `p:num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `a:num` THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let BVITAILAUX_CALL_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  EXISTS_TAC `t2:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[];;

let BVITAILAUX_CALL_TYERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];;

(* case split on a free variable of the given type in the goal *)
let BVITAILAUX_CASES_VAR_TAC (ty:hol_type) : tactic = fun (asl,w as g) ->
  let v = find (fun v -> type_of v = ty) (frees w) in
  CASES_ON v g;;

let BVITAILAUX_HANDLER_TAC : tactic = fun (asl,w as g) ->
  let ev = find_term (fun t -> is_comb t &&
             (try fst(dest_const(rator t)) = "bvi_evaluate" with Failure _ -> false)) (lhand w) in
  let xs,rest = dest_pair (rand ev) in
  let env,st = dest_pair rest in
  let x = hd (dest_list xs) in
  let v = rand (rator env) in
  let cons = `CONS:bvl_v->bvl_v list->bvl_v list` in
  (BVITAILAUX_SPLIT_TAC ev `rh:bvi_result` `sh:(num#C,FFI)bvi_state` THEN
   CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(rh:bvi_result = Rerr (Rabort Rtype_error)) /\
                 (!w. ~(rh = Rerr (Rraise (Ret w)))) /\ rh = (r:bvi_result) /\
                 (sh:(num#C,FFI)bvi_state) = t` STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
       `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
     BVITAILAUX_RESULT_CASES_TAC `rh:bvi_result` `wsh:bvl_v list` `eh:(exn_or_ret)error_result` THEN
     CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
     TRY(CASES_ON `eh:(exn_or_ret)error_result` THEN
         CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
                          distinctness "error_result"] THEN
         TRY(BVITAILAUX_CASES_VAR_TAC `:exn_or_ret` THEN
             CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
                              distinctness "error_result"; distinctness "exn_or_ret"])) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   USE_THEN "ih" (MP_TAC o SPECL [mk_list([x],`:bvi_exp`); `se:(num#C,FFI)bvi_state`]) THEN
   ANTS_TAC THENL
    [DISJ2_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds;
                                                 K_THM]) THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[BVITAILAUX_ert_def] THEN
   DISCH_THEN(MP_TAC o SPECL [mk_comb(mk_comb(cons,v),`env1:bvl_v list`); `rh:bvi_result`;
     `sh:(num#C,FFI)bvi_state`; `F`; `t2:(C,FFI)bvi_state`; `0`;
     mk_comb(mk_comb(cons,v),`env2:bvl_v list`); `0`; `CONS bvi_tailrec_Any ts`;
     `bvi_tailrec_Any`]) THEN
   ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def; isPREFIX_THM; BVITAILAUX_ty_rel_CONS;
                   distinctness "v_ty"] THEN
   DISCH_THEN(X_CHOOSE_THEN `th:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `th:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `rh:bvi_result = r`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sh:(num#C,FFI)bvi_state = t`)) THEN
   ASM_REWRITE_TAC[] THEN
   BVITAILAUX_RESULT_CASES_TAC `r:bvi_result` `wsh:bvl_v list` `eh:(exn_or_ret)error_result` THEN
   CASE_REWRITE_TAC[] THEN
   CASES_ON `eh:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
   TRY(BVITAILAUX_CASES_VAR_TAC `:exn_or_ret` THEN CASE_REWRITE_TAC[]) THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
                                           is_neg (snd (dest_forall (concl th))))) THEN
   REWRITE_TAC[NOT_FORALL_THM; injectivity "result"; injectivity "error_result";
               injectivity "exn_or_ret"] THEN MESON_TAC[]) g;;

let BVITAILAUX_ert_Call = prove
 (`!ticks dest xs h (s:(num#C,FFI)bvi_state). BVITAILAUX_ertIH [bvi_Call ticks dest xs h] s ==>
     BVITAILAUX_ert [bvi_Call ticks dest xs h] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD; BVITAILAUX_scan_simple; CONS_11; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITAILAUX_env_rel_F) THEN
  SUBGOAL_THEN `(env1:bvl_v list) <<= env2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN
    SIMP_TAC[bvi_tailrecProof_env_rel_def];
    ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Call ticks dest xs h],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_CASES_TAC `IS_NONE (dest:num option) /\ IS_SOME (h:bvi_exp option)` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(num#C,FFI)bvi_state` THEN
  USE_THEN "ih" (MP_TAC o SPECL [`xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; list_size] THEN
    REWRITE_TAC(type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp") THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r1:bvi_result`; `s1:(num#C,FFI)bvi_state`;
    `F`; `s':(C,FFI)bvi_state`; `0`; `env2:bvl_v list`; `0`; `ts:v_ty list`;
    `bvi_tailrec_Any`]) THEN
  ASM_REWRITE_TAC[] THEN
  BVITAILAUX_RESULT_CASES_TAC `r1:bvi_result` `vs:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[distinctness "result"; injectivity "result"] THENL
   [ALL_TAC;
    STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const o check (fun th ->
    concl th = `bvi_tailrecProof_state_rel (s1:(num#C,FFI)bvi_state) (t1:(C,FFI)bvi_state)`)) THEN
  BVITAILAUX_OPTION_CASES_TAC `bvl_find_code dest vs (bvi_state_code (s1:(num#C,FFI)bvi_state))`
    `p:bvl_v list # bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `p:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `cl:num` STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_find_code_lookup o
    check (fun th -> concl th =
      `bvl_find_code dest vs (bvi_state_code (s1:(num#C,FFI)bvi_state)) = SOME (args,exp)`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tailrecProof_state_rel_code_rel o check (fun th ->
    concl th = `bvi_tailrecProof_state_rel (s1:(num#C,FFI)bvi_state) (t1:(C,FFI)bvi_state)`)) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(X_CHOOSE_TAC `exp2:bvi_exp` o
    MATCH_MP BVITAILAUX_code_rel_lookup o CONJ th o check (fun th ->
      concl th = `lookup cl (bvi_state_code (s1:(num#C,FFI)bvi_state)) =
                  SOME (LENGTH (args:bvl_v list),exp)`))) THEN
  ASM_CASES_TAC `bvi_state_clock (s1:(num#C,FFI)bvi_state) < ticks + 1` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `bvi_state_clock_fupd (K 0) (t1:(C,FFI)bvi_state)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `lookup cl (bvi_state_code (t1:(C,FFI)bvi_state)) = SOME (LENGTH (args:bvl_v list),exp2)`)]) o
      check (fun th -> is_forall (concl th))) THEN
    CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[bvi_tailrecProof_state_rel_with_clock];
    ALL_TAC] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1)
                                       (s1:(num#C,FFI)bvi_state))`
    `re:bvi_result` `se:(num#C,FFI)bvi_state` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(re:bvi_result = Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
      `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o check (fun th ->
    concl th = `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state) = (Rval vs,s1)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o check (fun th ->
    concl th = `bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1)
                               (s1:(num#C,FFI)bvi_state)) = (re,se)`)) THEN
  MP_TAC(ISPECL [`cl:num`; `LENGTH (args:bvl_v list)`; `exp:bvi_exp`; `args:bvl_v list`;
                 `bvi_dec_clock (ticks + 1) (s1:(num#C,FFI)bvi_state)`;
                 `bvi_dec_clock (ticks + 1) (t1:(C,FFI)bvi_state)`; `re:bvi_result`;
                 `se:(num#C,FFI)bvi_state`] BVITAILAUX_code_rel_call) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[bvi_dec_clock_code] THEN CONJ_TAC THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
      REWRITE_TAC[bvi_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC bvi_tailrecProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_dec_clock_code] THEN
  DISCH_THEN(X_CHOOSE_THEN `exp':bvi_exp` (X_CHOOSE_THEN `t2:(C,FFI)bvi_state`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `lookup cl (bvi_state_code (t1:(C,FFI)bvi_state)) = SOME (LENGTH (args:bvl_v list),exp')`)]) o
      check (fun th -> is_forall (concl th))) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
    `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
  BVITAILAUX_RESULT_CASES_TAC `re:bvi_result` `ws:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `e:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[]) THEN
  TRY(CASES_ON `a:exn_or_ret` THEN CASE_REWRITE_TAC[]) THEN
  TRY(CASES_ON `h:bvi_exp option` THEN CASE_REWRITE_TAC[]) THEN
  TRY(BVITAILAUX_CALL_FIN_TAC THEN NO_TAC) THEN TRY(BVITAILAUX_CALL_TYERR_TAC THEN NO_TAC) THEN
  BVITAILAUX_HANDLER_TAC);;

(* the LetCall case of evaluate_rewrite_tail *)
let BVITAILAUX_LETCALL_RET_TAC : tactic = fun (asl,w as g) ->
  let leq = find_term (fun t -> is_eq t &&
              (try fst(dest_const(rator(lhs t))) = "LENGTH" with Failure _ -> false) &&
              rhs t = `rets:num`) w in
  let rv = rand (lhs leq) in
  let app = `APPEND:bvl_v list->bvl_v list->bvl_v list` in
  let e1 = mk_comb(mk_comb(app,rv),`env1:bvl_v list`) in
  let e2 = mk_comb(mk_comb(app,rv),`env2:bvl_v list`) in
  (ASM_CASES_TAC leq THEN ASM_REWRITE_TAC[] THENL
    [DISCH_TAC THEN
     USE_THEN "ih" (MP_TAC o SPECL [`[y:bvi_exp]`; `se:(num#C,FFI)bvi_state`]) THEN
     ANTS_TAC THENL
      [DISJ2_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds;
                                                   K_THM]) THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     REWRITE_TAC[BVITAILAUX_ert_def] THEN
     DISCH_THEN(MP_TAC o SPECL [e1; `r:bvi_result`; `t:(num#C,FFI)bvi_state`; `F`;
       `t2:(C,FFI)bvi_state`; `0`; e2; `0`;
       mk_comb(mk_comb(`REPLICATE:num->v_ty->v_ty list`,mk_comb(`LENGTH:bvl_v list->num`,e1)),
               `bvi_tailrec_Any`);
       `bvi_tailrec_Any`]) THEN
     ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def; IS_PREFIX_APPENDS;
                     BVITAILAUX_ty_rel_REPLICATE_Any];
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]]) g;;

let BVITAILAUX_ert_LetCall = prove
 (`!rets ticks dest xs y (s:(num#C,FFI)bvi_state).
     BVITAILAUX_ertIH [LetCall rets ticks dest xs y] s ==>
     BVITAILAUX_ert [LetCall rets ticks dest xs y] s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_ertIH_def] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITAILAUX_ert_def; HD; BVITAILAUX_scan_simple; CONS_11; PAIR_EQ;
              option_DISTINCT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(env1:bvl_v list) <<= env2` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tailrecProof_env_rel ty opt acc env1 env2` THEN
    SIMP_TAC[bvi_tailrecProof_env_rel_def];
    ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate ([LetCall rets ticks dest xs y],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)`
    `r1:bvi_result` `s1:(num#C,FFI)bvi_state` THEN
  USE_THEN "ih" (MP_TAC o SPECL [`xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; list_size] THEN
    REWRITE_TAC(type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp") THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r1:bvi_result`; `s1:(num#C,FFI)bvi_state`;
    `F`; `s':(C,FFI)bvi_state`; `0`; `env2:bvl_v list`; `0`; `ts:v_ty list`;
    `bvi_tailrec_Any`]) THEN
  ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def] THEN
  BVITAILAUX_RESULT_CASES_TAC `r1:bvi_result` `vs:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[distinctness "result"; injectivity "result"] THENL
   [ALL_TAC;
    STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1:(C,FFI)bvi_state` THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_state_rel_const o check (fun th ->
    concl th = `bvi_tailrecProof_state_rel (s1:(num#C,FFI)bvi_state) (t1:(C,FFI)bvi_state)`)) THEN
  BVITAILAUX_OPTION_CASES_TAC
    `bvl_find_code (SOME dest) vs (bvi_state_code (s1:(num#C,FFI)bvi_state))`
    `p:bvl_v list # bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `p:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `cl:num` STRIP_ASSUME_TAC o MATCH_MP BVITAILAUX_find_code_lookup o
    check (fun th -> concl th =
      `bvl_find_code (SOME dest) vs (bvi_state_code (s1:(num#C,FFI)bvi_state)) =
       SOME (args,exp)`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tailrecProof_state_rel_code_rel o check (fun th ->
    concl th = `bvi_tailrecProof_state_rel (s1:(num#C,FFI)bvi_state) (t1:(C,FFI)bvi_state)`)) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(X_CHOOSE_TAC `exp2:bvi_exp` o
    MATCH_MP BVITAILAUX_code_rel_lookup o CONJ th o check (fun th ->
      concl th = `lookup cl (bvi_state_code (s1:(num#C,FFI)bvi_state)) =
                  SOME (LENGTH (args:bvl_v list),exp)`))) THEN
  ASM_CASES_TAC `bvi_state_clock (s1:(num#C,FFI)bvi_state) < ticks + 1` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `bvi_state_clock_fupd (K 0) (t1:(C,FFI)bvi_state)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `lookup cl (bvi_state_code (t1:(C,FFI)bvi_state)) = SOME (LENGTH (args:bvl_v list),exp2)`)]) o
      check (fun th -> is_forall (concl th))) THEN
    CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[bvi_tailrecProof_state_rel_with_clock];
    ALL_TAC] THEN
  BVITAILAUX_SPLIT_TAC `bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1)
                                       (s1:(num#C,FFI)bvi_state))`
    `re:bvi_result` `se:(num#C,FFI)bvi_state` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(re:bvi_result = Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
      `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:bvi_result) = Rerr (Rabort Rtype_error))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o check (fun th ->
    concl th = `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state) = (Rval vs,s1)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock o check (fun th ->
    concl th = `bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1)
                               (s1:(num#C,FFI)bvi_state)) = (re,se)`)) THEN
  MP_TAC(ISPECL [`cl:num`; `LENGTH (args:bvl_v list)`; `exp:bvi_exp`; `args:bvl_v list`;
                 `bvi_dec_clock (ticks + 1) (s1:(num#C,FFI)bvi_state)`;
                 `bvi_dec_clock (ticks + 1) (t1:(C,FFI)bvi_state)`; `re:bvi_result`;
                 `se:(num#C,FFI)bvi_state`] BVITAILAUX_code_rel_call) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[bvi_dec_clock_code] THEN CONJ_TAC THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
      REWRITE_TAC[bvi_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC bvi_tailrecProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_dec_clock_code] THEN
  DISCH_THEN(X_CHOOSE_THEN `exp':bvi_exp` (X_CHOOSE_THEN `t2:(C,FFI)bvi_state`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `lookup cl (bvi_state_code (t1:(C,FFI)bvi_state)) = SOME (LENGTH (args:bvl_v list),exp')`)]) o
      check (fun th -> is_forall (concl th))) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> rand (concl th) =
    `(r:bvi_result,t:(num#C,FFI)bvi_state)`)) THEN
  BVITAILAUX_RESULT_CASES_TAC `re:bvi_result` `ws:bvl_v list` `e:(exn_or_ret)error_result` THEN
  CASE_REWRITE_TAC[] THEN
  TRY(BVITAILAUX_CASES_VAR_TAC `:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[]) THEN
  TRY(BVITAILAUX_CASES_VAR_TAC `:exn_or_ret` THEN CASE_REWRITE_TAC[]) THEN
  TRY(BVITAILAUX_CALL_FIN_TAC THEN NO_TAC) THEN TRY(BVITAILAUX_CALL_TYERR_TAC THEN NO_TAC) THEN
  BVITAILAUX_LETCALL_RET_TAC);;

(* ------------------------------------------------------------------------- *)
(* evaluate_rewrite_tail                                                      *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_ert_all = prove
 (`!xs (s:(num#C,FFI)bvi_state). BVITAILAUX_ert xs s`,
  MATCH_MP_TAC BVITAILAUX_ert_ind THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `xs:bvi_exp list` list_CASES) THEN
  REWRITE_TAC[BVITAILAUX_ert_NIL] THEN
  STRUCT_CASES_TAC (ISPEC `t:bvi_exp list` list_CASES) THENL
   [ALL_TAC; MATCH_ACCEPT_TAC BVITAILAUX_ert_CONS] THEN
  STRUCT_CASES_TAC (ISPEC `h:bvi_exp` (CONJUNCT1 (cases "bvi_exp"))) THEN
  FIRST (map MATCH_ACCEPT_TAC
    [BVITAILAUX_ert_Var; BVITAILAUX_ert_Raise; BVITAILAUX_ert_Return; BVITAILAUX_ert_Tick;
     BVITAILAUX_ert_Let; BVITAILAUX_ert_If; BVITAILAUX_ert_Op; BVITAILAUX_ert_Force;
     BVITAILAUX_ert_Call; BVITAILAUX_ert_LetCall]));;

let evaluate_rewrite_tail = prove
 (CASE_TERM
  `!xs (s:(num#C,FFI)bvi_state) env1 r t opt (s':(C,FFI)bvi_state) acc env2 loc ts ty.
     bvi_evaluate (xs,env1,s) = (r,t) /\
     bvi_tailrecProof_env_rel ty opt acc env1 env2 /\
     bvi_tailrecProof_state_rel s s' /\
     ty_rel env1 ts /\
     (opt ==> LENGTH xs = 1) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?t'. bvi_evaluate (xs,env2,s') = (r,t') /\ bvi_tailrecProof_state_rel t t' /\
          (opt ==>
           !op n exp arity.
             lookup loc (bvi_state_code s) = SOME (arity,exp) /\
             optimized_code loc arity exp n (bvi_state_code s') op /\
             op_type op = ty /\
             (?op1 tt ty r. scan_expr ts loc [HD xs] = [(tt,ty,r,SOME op1)] /\
                            ~(ty = bvi_tailrec_Any) /\ ~(op1 = Noop) /\
                            op_type op1 = op_type op) ==>
             let (lr,x) = rewrite loc n op acc ts (HD xs) in
             ?rrr t1 t2.
               bvi_evaluate ([x],env2,s') = (rrr,t1) /\
               bvi_evaluate ([apply_op op (bvi_Var acc) (HD xs)],env2,s') = (rrr,t2) /\
               bvi_tailrecProof_state_rel t t1 /\ bvi_tailrecProof_state_rel t t2)`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC_ALL BVITAILAUX_ert_all) THEN
  REWRITE_TAC[BVITAILAUX_ert_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`env1:bvl_v list`; `r:bvi_result`; `t:(num#C,FFI)bvi_state`;
    `opt:bool`; `s':(C,FFI)bvi_state`; `acc:num`; `env2:bvl_v list`; `loc:num`;
    `ts:v_ty list`; `ty:v_ty`]) THEN
  REWRITE_TAC[]);;

let bvi_tailrecProof_evaluate_compile_each = prove
 (`!next prog (co:num -> (num#C) # (num#num#bvi_exp) list) start (ffi0:(FFI)ffi_state)
    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) k r
    (s:(num#C,FFI)bvi_state).
     bvi_tailrecProof_input_condition next prog /\
     (!n next cfg prog. co n = ((next,cfg),prog) ==>
                        bvi_tailrecProof_input_condition next prog) /\
     (!n. MEM n (MAP FST (SND (bvi_tailrec_compile_each next prog))) /\
          n MOD bvl_to_bvi_namespaces = 2 ==> n < FST (FST (co 0))) /\
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                   bvi_initial_state ffi0 (fromAList prog) co
                     (state_cc bvi_tailrec_compile_each cc) k) = (r,s) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?s2. bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                        bvi_initial_state ffi0 (fromAList (SND (bvi_tailrec_compile_each next prog)))
                          (state_co bvi_tailrec_compile_each co) cc k) = (r,s2) /\
          bvi_tailrecProof_state_rel s s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `bvi_tailrec_compile_each next prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `prog2:(num#num#bvi_exp)list`
    ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "MEM")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_tailrecProof_input_condition_def] o
    check (fun th -> concl th = `bvi_tailrecProof_input_condition next (prog:(num#num#bvi_exp)list)`)) THEN
  SUBGOAL_THEN
   `bvi_tailrecProof_state_rel
      (bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
         (co:num -> (num#C) # (num#num#bvi_exp) list)
         (state_cc bvi_tailrec_compile_each
           (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option)) k)
      (bvi_initial_state ffi0 (fromAList prog2) (state_co bvi_tailrec_compile_each co) cc k)`
    ASSUME_TAC THENL
   [REWRITE_TAC[bvi_tailrecProof_state_rel_def; bvi_initial_state_def;
                bvi_state_INFO.ri_accessors] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def] THEN BETA_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(INST [`next:num`,`next:num`; `prog:(num#num#bvi_exp)list`,`prog:(num#num#bvi_exp)list`;
                         `n2:num`,`next1:num`; `prog2:(num#num#bvi_exp)list`,`prog2:(num#num#bvi_exp)list`]
                        bvi_tailrecProof_compile_each_code_rel) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(INST [`next:num`,`next:num`; `prog:(num#num#bvi_exp)list`,`prog:(num#num#bvi_exp)list`;
                         `n2:num`,`next1:num`; `prog2:(num#num#bvi_exp)list`,`prog2:(num#num#bvi_exp)list`]
                        bvi_tailrecProof_compile_each_namespace_rel) THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `SND (FST ((co:num -> (num#C) # (num#num#bvi_exp) list) n))`] THEN
      REWRITE_TAC[PAIR];
      ASM_REWRITE_TAC[domain_fromAList; IN_SET_OF_LIST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`;
                 `bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
                    (co:num -> (num#C) # (num#num#bvi_exp) list)
                    (state_cc bvi_tailrec_compile_each
                      (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option)) k`;
                 `[]:bvl_v list`; `r:bvi_result`; `s:(num#C,FFI)bvi_state`; `F`;
                 `bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog2)
                    (state_co bvi_tailrec_compile_each
                      (co:num -> (num#C) # (num#num#bvi_exp) list))
                    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) k`;
                 `0`; `[]:bvl_v list`; `0`; `[]:v_ty list`; `bvi_tailrec_Any`]
                evaluate_rewrite_tail) THEN
  ASM_REWRITE_TAC[bvi_tailrecProof_env_rel_def; isPREFIX_THM; ty_rel_def; ALL2] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* semantics                                                                 *)
(* ------------------------------------------------------------------------- *)

(* local helpers for the semantics theorems (copies of the corresponding     *)
(* local helpers of bvi_inlineProof, which is not an ancestor of this theory) *)
(* the initial state with more clock *)
let BVITAILAUX_inc_initial_state = prove
 (`!ck (ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list) cc k.
     bvi_inc_clock ck (bvi_initial_state ffi code co cc k) =
     bvi_initial_state ffi code co cc (k + ck)`,
  REWRITE_TAC[bvi_inc_clock_def; bvi_initial_state_def; bvi_state_INFO.ri_accessors;
              bvi_state_INFO.ri_fupds; K_THM]);;

let BVITAILAUX_init_io_mono = prove
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
  REWRITE_TAC[BVITAILAUX_inc_initial_state]);;

let BVITAILAUX_init_io_chain = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvi_exp) list) cc.
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (bvi_state_ffi
          (SND (bvi_evaluate (es,env,bvi_initial_state ffi p co cc k)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[BVITAILAUX_init_io_mono; LE_CASES]);;

(* the run of the start call; the configuration type is taken from the oracle *)
let BVITAILAUX_ev (p:term) (oo:term) (c:term) (k:term) =
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

let BVITAILAUX_RUN_TAC (p:term) (oo:term) (c:term) (k:term) (r:term) (x:term) : tactic =
  MP_TAC(ISPEC (BVITAILAUX_ev p oo c k) PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [r; x] THEN DISCH_TAC;;

(* MP of a labelled implication with its antecedent proved from the        *)
(* assumptions (not ASM_REWRITE_TAC after MP_TAC: the labelled fact itself  *)
(* would rewrite its instance to T)                                         *)
let BVITAILAUX_LAB_MP_TAC (lab:string) (tms:term list) : tactic = fun (asl,w as g) ->
  USE_THEN lab (fun th ->
    let th' = SPECL tms th in
    let ant = lhand (concl th') in
    let ath = EQT_ELIM (REWRITE_CONV (FST :: SND :: map snd asl) ant) in
    MP_TAC (MP th' ath)) g;;

(* the source configuration type D and the target one C may differ *)
let BVITAILAUX_semantics_back = prove
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
  FIRST_ASSUM(LABEL_TAC "nf" o MATCH_MP CLOSSEMAUX_bvi_semantics_not_Fail_cond) THEN
  REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `e:(exn_or_ret)error_result`
      MP_TAC)) THEN
    BVITAILAUX_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
    ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
    BVITAILAUX_LAB_MP_TAC "sim" [`k:num`; rv; t1] THEN
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
     [BVITAILAUX_LAB_MP_TAC "sim" [`k:num`; rv; `s:(C,FFI)bvi_state`] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`k + ck:num`; s1; rv; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN (mk_neg(mk_eq(rv, tmo))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      BVITAILAUX_RUN_TAC pp2 oo2 cc2 `k:num` r0 t1 THEN
      BVITAILAUX_LAB_MP_TAC "sim" [`k:num`; r0; t1] THEN
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
        REWRITE_TAC[BVITAILAUX_inc_initial_state] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[bvi_inc_clock_ffi]) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`k:num`; t1; rv; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REWRITE_TAC[BVITAILAUX_init_io_chain] THEN
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THENL
     [BVITAILAUX_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
      BVITAILAUX_LAB_MP_TAC "sim" [`k:num`; rv; t1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `k + ck:num` THEN
      ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL; SND];
      EXISTS_TAC `k:num` THEN
      BVITAILAUX_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
      BVITAILAUX_LAB_MP_TAC "sim" [`k:num`; rv; t1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; SND] THEN
      MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`; `[]:bvl_v list`;
                     `ffi:(FFI)ffi_state`; pp1; oo1; cc1; `k:num`; `k + ck:num`]
                    BVITAILAUX_init_io_mono) THEN
      ASM_REWRITE_TAC[LE_ADD; SND]];
    REWRITE_TAC[]]);;


let bvi_tailrecProof_compile_each_semantics = prove
 (`!n prog (co:num -> (num#C) # (num#num#bvi_exp) list) prog2 (ffi:(FFI)ffi_state)
    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) start.
     bvi_tailrecProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==> bvi_tailrecProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ k MOD bvl_to_bvi_namespaces = 2 ==>
          k < FST (FST (co 0))) /\
     SND (bvi_tailrec_compile_each n prog) = prog2 /\
     ~(bvi_semantics ffi (fromAList prog) co (state_cc bvi_tailrec_compile_each cc) start =
       Fail) ==>
     bvi_semantics ffi (fromAList prog) co (state_cc bvi_tailrec_compile_each cc) start =
     bvi_semantics ffi (fromAList prog2) (state_co bvi_tailrec_compile_each co) cc start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC BVITAILAUX_semantics_back THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `r:bvi_result`; `s:(C,FFI)bvi_state`] THEN DISCH_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                  bvi_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num -> (num#C) # (num#num#bvi_exp) list)
                    (state_cc bvi_tailrec_compile_each
                      (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option))
                    k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(num#C,FFI)bvi_state`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r1:bvi_result = Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSSEMAUX_bvi_semantics_not_Fail_cond) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`k:num`;
      `Rabort Rtype_error:(exn_or_ret)error_result`]) THEN
    ASM_REWRITE_TAC[FST] THEN REWRITE_TAC BVLPROPSAUX_bvi_eval_simps;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvi_exp)list`;
                 `co:num -> (num#C) # (num#num#bvi_exp) list`; `start:num`;
                 `ffi:(FFI)ffi_state`;
                 `cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option`;
                 `k:num`; `r1:bvi_result`; `s1:(num#C,FFI)bvi_state`]
                bvi_tailrecProof_evaluate_compile_each) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s1:(num#C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tailrecProof_state_rel_const) THEN SIMP_TAC[]);;

let bvi_tailrecProof_compile_prog_semantics = prove
 (`!b n prog (co:num -> (num#C) # (num#num#bvi_exp) list) prog2 (ffi:(FFI)ffi_state)
    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) start.
     bvi_tailrecProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==> bvi_tailrecProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ k MOD bvl_to_bvi_namespaces = 2 ==>
          k < FST (FST (co 0))) /\
     SND (bvi_tailrec_compile_prog b n prog) = prog2 /\
     ~(bvi_semantics ffi (fromAList prog) co (state_cc (bvi_tailrec_compile_prog b) cc) start =
       Fail) ==>
     bvi_semantics ffi (fromAList prog) co (state_cc (bvi_tailrec_compile_prog b) cc) start =
     bvi_semantics ffi (fromAList prog2) (state_co (bvi_tailrec_compile_prog b) co) cc start`,
  GEN_TAC THEN CASES_ON `b:bool` THENL
   [SUBGOAL_THEN `bvi_tailrec_compile_prog T = bvi_tailrec_compile_each` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; bvi_tailrec_compile_prog_def]; ALL_TAC] THEN
    MATCH_ACCEPT_TAC bvi_tailrecProof_compile_each_semantics;
    SUBGOAL_THEN `bvi_tailrec_compile_prog F = CURRY I` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; bvi_tailrec_compile_prog_def; CURRY_DEF; I_THM]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[CURRY_DEF; I_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      rhs (concl th) = `prog2:(num#num#bvi_exp)list`)) THEN
    REWRITE_TAC[SND] THEN MATCH_MP_TAC bvi_semantics_CURRY_I THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* labels                                                                    *)
(* ------------------------------------------------------------------------- *)

let BVITAILAUX_ns_set = prove
 (`!next n. next + bvl_to_bvi_namespaces <= n ==>
     {next + k * bvl_to_bvi_namespaces | k | next + k * bvl_to_bvi_namespaces < n} =
     next INSERT {(next + bvl_to_bvi_namespaces) + k * bvl_to_bvi_namespaces | k |
                  (next + bvl_to_bvi_namespaces) + k * bvl_to_bvi_namespaces < n}`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN REWRITE_TAC[MULT_CLAUSES] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_ARITH_TAC;
      DISJ2_TAC THEN EXISTS_TAC `n':num` THEN ASM_ARITH_TAC];
    STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_ARITH_TAC;
      EXISTS_TAC `SUC k` THEN REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC]]);;

let compile_each_labels = prove
 (`!next1 code1 next2 code2.
     bvi_tailrec_compile_each next1 code1 = (next2,code2) ==>
     set_of_list (MAP FST code1) UNION
     {next1 + k * bvl_to_bvi_namespaces | k | next1 + k * bvl_to_bvi_namespaces < next2} =
     set_of_list (MAP FST code2) /\
     next1 <= next2`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[MAP; set_of_list; UNION_EMPTY; LE_REFL] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`next:num`; `loc:num`; `arity:num`; `exp:bvi_exp`;
                       `xs:(num#num#bvi_exp)list`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`n2:num`; `c2:(num#num#bvi_exp)list`] THEN
  REWRITE_TAC[bvi_tailrec_compile_each_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `q:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `bvi_tailrec_compile_exp loc next arity exp = NONE`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`FST (bvi_tailrec_compile_each next xs)`;
                               `SND (bvi_tailrec_compile_each next xs)`]) THEN
    REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MAP; set_of_list; FST] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`FST (q:bvi_exp#bvi_exp)`; `SND (q:bvi_exp#bvi_exp)`] o
    check (fun th -> is_forall (concl th))) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST (bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs)`;
                             `SND (bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs)`]) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  ASM_SIMP_TAC[BVITAILAUX_ns_set] THEN
  REWRITE_TAC[MAP; set_of_list; FST] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN SET_TAC[]);;

let bvi_tailrecProof_compile_each_keeps_names = prove
 (`!next xs next' ys.
     bvi_tailrec_compile_each next xs = (next',ys) /\ MEM x (MAP FST xs) ==>
     MEM x (MAP FST ys)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP compile_each_labels) THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[]);;

let bvi_tailrecProof_compile_prog_keeps_names = prove
 (`!b next xs next' ys.
     bvi_tailrec_compile_prog b next xs = (next',ys) /\ MEM x (MAP FST xs) ==>
     MEM x (MAP FST ys)`,
  GEN_TAC THEN CASES_ON `b:bool` THEN REWRITE_TAC[bvi_tailrec_compile_prog_def] THENL
   [MESON_TAC[bvi_tailrecProof_compile_each_keeps_names];
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

let BVITAILAUX_assign_to_op = prove
 (`!opr. assign_get_code_label (to_op opr) = {}`,
  GEN_TAC THEN CASES_ON `opr:assoc_op` THEN
  REWRITE_TAC[to_op_def; assign_get_code_label_def]);;

let BVITAILAUX_labels_apply_op = prove
 (`!opr acc e. bvi_get_code_labels (apply_op opr (bvi_Var acc) e) = bvi_get_code_labels e`,
  REWRITE_TAC[apply_op_def; bvi_get_code_labels_def; BVITAILAUX_assign_to_op; MAP;
              set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

let BVITAILAUX_labels_check_op = prove
 (CASE_TERM
  `!loc next opr acc ts exp.
     bvi_get_code_labels
       (SND (match check_op ts opr loc exp with
               NONE -> (F,apply_op opr (bvi_Var acc) exp)
             | SOME exp' ->
                 (match opbinargs opr exp' with
                    NONE -> (F,apply_op opr (bvi_Var acc) exp')
                  | SOME (xs,f) -> (T,push_call next opr acc xs (args_from f))))) SUBSET
     next INSERT bvi_get_code_labels exp`,
  REPEAT GEN_TAC THEN
  BVITAILAUX_OPTION_CASES_TAC `check_op ts opr loc exp` `e':bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[BVITAILAUX_labels_apply_op] THENL
   [ALL_TAC; SET_TAC[]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ticks:num` (X_CHOOSE_THEN `args:bvi_exp list`
    (X_CHOOSE_THEN `y:bvi_exp` STRIP_ASSUME_TAC)) o MATCH_MP BVITAILAUX_check_op_cases) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `opbinargs opr (bvi_Op (to_op opr) [y; bvi_Call ticks (SOME loc) args NONE]) =
                SOME (y,bvi_Call ticks (SOME loc) args NONE)` SUBST1_TAC THEN
  TRY(ASM_REWRITE_TAC[opbinargs_SOME] THEN MESON_TAC[] THEN NO_TAC) THEN
  CASE_REWRITE_TAC[args_from_def; push_call_def] THEN
  REWRITE_TAC[bvi_get_code_labels_def; BVITAILAUX_labels_apply_op; BVITAILAUX_assign_to_op;
              MAP; MAP_APPEND; set_of_list; SET_OF_LIST_APPEND; UNIONS_INSERT; UNIONS_UNION;
              UNIONS_0; UNION_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN SET_TAC[]);;

let BVITAILAUX_labels_If_step = prove
 (`!loc next opr acc ts x1 x2 x3.
     (!t1. bvi_get_code_labels (SND (rewrite loc next opr acc t1 x2)) SUBSET
           next INSERT bvi_get_code_labels x2) /\
     (!t1. bvi_get_code_labels (SND (rewrite loc next opr acc t1 x3)) SUBSET
           next INSERT bvi_get_code_labels x3) ==>
     bvi_get_code_labels (SND (rewrite loc next opr acc ts (bvi_If x1 x2 x3))) SUBSET
     next INSERT bvi_get_code_labels (bvi_If x1 x2 x3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITAILAUX_rewrite_If; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[SND; bvi_get_code_labels_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `bvi_get_code_labels
      (if FST (rewrite loc next opr acc (FST (scan_expr_sing ts loc x1)) x2)
       then SND (rewrite loc next opr acc (FST (scan_expr_sing ts loc x1)) x2)
       else apply_op opr (bvi_Var acc) x2) SUBSET next INSERT bvi_get_code_labels x2 /\
    bvi_get_code_labels
      (if FST (rewrite loc next opr acc (FST (scan_expr_sing ts loc x1)) x3)
       then SND (rewrite loc next opr acc (FST (scan_expr_sing ts loc x1)) x3)
       else apply_op opr (bvi_Var acc) x3) SUBSET next INSERT bvi_get_code_labels x3`
    MP_TAC THENL
   [CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BVITAILAUX_labels_apply_op] THEN
    SET_TAC[];
    SET_TAC[]]);;

let BVITAILAUX_labels_rewrite = prove
 (`!loc next opr acc ts exp.
     bvi_get_code_labels (SND (rewrite loc next opr acc ts exp)) SUBSET
     next INSERT bvi_get_code_labels exp`,
  MATCH_MP_TAC rewrite_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  TRY(REWRITE_TAC[rewrite_def] THEN MATCH_ACCEPT_TAC BVITAILAUX_labels_check_op THEN NO_TAC) THENL
   [REWRITE_TAC[rewrite_def; SND; bvi_get_code_labels_def; EMPTY_SUBSET];
    MATCH_MP_TAC BVITAILAUX_labels_If_step THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN CONJ_TAC THEN GEN_TAC THENL
     [FIRST_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        is_imp (snd (strip_forall (concl th))))) THEN
      MESON_TAC[PAIR_SURJECTIVE]];
    REWRITE_TAC[rewrite_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
    BETA_TAC THEN REWRITE_TAC[SND; bvi_get_code_labels_def] THEN
    MATCH_MP_TAC(SET_RULE `!a b c n:num. b SUBSET n INSERT c ==>
                                         a UNION b SUBSET n INSERT (a UNION c)`) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    REWRITE_TAC[rewrite_def; LET_DEF; LET_END_DEF; pair_CASE_def] THEN
    BETA_TAC THEN ASM_REWRITE_TAC[SND; bvi_get_code_labels_def];
    REWRITE_TAC[rewrite_def; SND; bvi_get_code_labels_def] THEN SET_TAC[]]);;

let get_code_labels_rewrite = prove
 (`!loc next op arity foo exp bar exp_opt.
     rewrite loc next op arity foo exp = (bar,exp_opt) ==>
     bvi_get_code_labels exp_opt SUBSET next INSERT bvi_get_code_labels exp`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `SND:bool#bvi_exp->bvi_exp`) THEN
  REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BVITAILAUX_labels_rewrite]);;

let BVITAILAUX_labels_vars = prove
 (`!a. UNIONS (set_of_list (MAP bvi_get_code_labels (list_of_seq (\i. bvi_Var i) a))) = {}`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; MAP; MAP_APPEND; set_of_list; SET_OF_LIST_APPEND; UNIONS_UNION;
                  UNIONS_0; UNIONS_INSERT; bvi_get_code_labels_def; UNION_EMPTY]);;

let get_code_labels_let_wrap = prove
 (`!a b c. bvi_get_code_labels (let_wrap a b c) =
           bvi_get_code_labels b UNION bvi_get_code_labels c`,
  REWRITE_TAC[let_wrap_def; bvi_get_code_labels_def; MAP_APPEND; MAP; SET_OF_LIST_APPEND;
              set_of_list; UNIONS_UNION; UNIONS_INSERT; UNIONS_0; UNION_EMPTY;
              BVITAILAUX_labels_vars]);;
let _ = cake_add_simps [get_code_labels_let_wrap];;

let BVITAILAUX_labels_id_from_op = prove
 (`!op. bvi_get_code_labels (id_from_op op) = {}`,
  GEN_TAC THEN CASES_ON `op:assoc_op` THEN
  REWRITE_TAC[id_from_op_def; bvi_tailrec_dummy_def; bvi_get_code_labels_def;
              assign_get_code_label_def; MAP; set_of_list; UNIONS_0; UNION_EMPTY]);;

let get_code_labels_compile_exp = prove
 (`!loc next arity exp exp_aux exp_opt.
     bvi_tailrec_compile_exp loc next arity exp = SOME (exp_aux,exp_opt) ==>
     bvi_get_code_labels exp_aux UNION bvi_get_code_labels exp_opt SUBSET
     next INSERT bvi_get_code_labels exp`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  BVITAILAUX_OPTION_CASES_TAC `check_exp loc arity exp` `op:assoc_op` THENL
   [ALL_TAC;
    UNDISCH_TAC `bvi_tailrec_compile_exp loc next arity exp = SOME (exp_aux,exp_opt)` THEN
    ASM_REWRITE_TAC[bvi_tailrec_compile_exp_def] THEN CASE_REWRITE_TAC[option_DISTINCT]] THEN
  MP_TAC(ISPECL [`loc:num`; `next:num`; `arity:num`; `exp:bvi_exp`; `exp_aux:bvi_exp`;
                 `exp_opt:bvi_exp`; `op:assoc_op`] BVITAILAUX_compile_exp_opt) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[get_code_labels_let_wrap; BVITAILAUX_labels_id_from_op; UNION_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`loc:num`; `next:num`; `op:assoc_op`; `arity:num`;
    `REPLICATE arity bvi_tailrec_Any`; `exp:bvi_exp`] BVITAILAUX_labels_rewrite) THEN
  SET_TAC[]);;


let bvi_tailrecProof_compile_each_good_code_labels = prove
 (`!n c n2 c2.
     bvi_tailrec_compile_each n c = (n2,c2) /\
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c)) SUBSET all /\
     {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n2} SUBSET all ==>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c2)) SUBSET all`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tailrec_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`next:num`; `loc:num`; `arity:num`; `exp:bvi_exp`;
                       `xs:(num#num#bvi_exp)list`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`n2:num`; `c2:(num#num#bvi_exp)list`] THEN
  REWRITE_TAC[bvi_tailrec_compile_each_def] THEN
  BVITAILAUX_OPTION_CASES_TAC `bvi_tailrec_compile_exp loc next arity exp`
    `q:bvi_exp#bvi_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC[PAIR_EQ; MAP; set_of_list; UNIONS_INSERT; o_THM; UNION_SUBSET] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `bvi_tailrec_compile_exp loc next arity exp = NONE`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`FST (bvi_tailrec_compile_each next xs)`;
                               `SND (bvi_tailrec_compile_each next xs)`]) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; o_THM; UNION_SUBSET] THEN
    ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`FST (q:bvi_exp#bvi_exp)`; `SND (q:bvi_exp#bvi_exp)`] o
    check (fun th -> is_forall (concl th))) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST (bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs)`;
                             `SND (bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs)`]) THEN
  REWRITE_TAC[PAIR] THEN
  MP_TAC(ISPECL [`next + bvl_to_bvi_namespaces`; `xs:(num#num#bvi_exp)list`;
                 `FST (bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs)`;
                 `SND (bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs)`]
                compile_each_labels) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`loc:num`; `next:num`; `arity:num`; `exp:bvi_exp`; `FST (q:bvi_exp#bvi_exp)`;
                 `SND (q:bvi_exp#bvi_exp)`] get_code_labels_compile_exp) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in
    is_comb c && rand c = `all:num->bool` && is_comb (lhand c) &&
    (try fst (dest_const (rator (lhand c))) = "GSPEC" with Failure _ -> false))) THEN
  ASM_SIMP_TAC[BVITAILAUX_ns_set] THEN REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; o_THM; UNION_SUBSET] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bvi_get_code_labels (FST (q:bvi_exp#bvi_exp)) UNION
               bvi_get_code_labels (SND q) SUBSET
               next INSERT bvi_get_code_labels exp` THEN
  ASM SET_TAC[]);;

let bvi_tailrecProof_compile_prog_good_code_labels = prove
 (`!b n c n2 c2.
     bvi_tailrec_compile_prog b n c = (n2,c2) /\
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c)) SUBSET all /\
     {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n2} SUBSET all ==>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c2)) SUBSET all`,
  GEN_TAC THEN CASES_ON `b:bool` THEN REWRITE_TAC[bvi_tailrec_compile_prog_def] THENL
   [MESON_TAC[bvi_tailrecProof_compile_each_good_code_labels];
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;
