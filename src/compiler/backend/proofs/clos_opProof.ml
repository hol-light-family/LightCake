(* ========================================================================= *)
(* clos_opProof: port of HOL4 compiler/backend/proofs/clos_opProofScript.sml *)
(* (CakeML v3479).                                                           *)
(* Correctness proof for clos_op.                                            *)
(*                                                                           *)
(* The proofs follow HOL4's, with the kit's HOL4-style tactics.  CLOSP2AUX_  *)
(* names are local helpers: CLOSP2AUX_op_lift_exps_ind replaces HOL4's       *)
(* lift_exps_ind (cake_ind "lift_exps" gives one name to the argument ys and *)
(* to the result of the recursive call on it, which makes its third         *)
(* hypothesis too weak).                                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_op.ml";;

type_invention_error := true;;

(* HOL4: list_split3 [local] *)
let list_split3 = prove
 (`!P. P [] /\ (!x y z zs. P (CONS x (CONS y (CONS z zs)))) /\ (!x. P [x]) /\
       (!x y. P [x; y]) ==>
       !xs:A list. P xs`,
  RW[] THEN QCASES_ON "xs" THEN FS[] THEN QCASES_ON "a1" THEN FS[] THEN
  QCASES_ON "a1'" THEN FS[]);;

(* HOL4: evaluate_MakeBool [local] *)
let evaluate_MakeBool = prove
 (`!b. clos_evaluate ([MakeBool b],vs,s:(C,FFI)clos_state) = (Rval [clos_Boolv b],s)`,
  SIMP[MakeBool_def; clos_evaluate_def; clos_do_app_def; clos_Boolv_def; true_tag_def;
       false_tag_def]);;

(* HOL4: dest_Op_thm *)
let dest_Op_thm = prove
 (`dest_Op (f:clos_op->A option) x = SOME (i,ys) <=>
   ?tra y. x = clos_Op tra y ys /\ f y = SOME i`,
  QCASES_ON "x" THEN GVS(dest_Op_def :: all_case_eqs()) THEN RW[] THEN EQ_TAC THEN RW[]);;

(* HOL4: dest_Op_Nil_thm *)
let dest_Op_Nil_thm = prove
 (`dest_Op_Nil (f:clos_op->A option) x = SOME i <=>
   ?tra y. x = clos_Op tra y [] /\ f y = SOME i`,
  QCASES_ON "x" THEN GVS(dest_Op_Nil_def :: dest_Op_def :: all_case_eqs()) THEN
  MESON_TAC[NULL_EQ; PAIR_EQ]);;

(* HOL4: dest_Const_thm *)
let dest_Const_thm = prove
 (`dest_Const x = SOME i <=> x = IntOp (clos_Const i)`,
  QCASES_ON "x" THEN SIMP[dest_Const_def] THEN QCASES_ON "a" THEN
  SIMP[dest_Const_def]);;

(* HOL4: dest_Constant_thm *)
let dest_Constant_thm = prove
 (`clos_op_dest_Constant x = SOME i <=>
   ?s w j. x = BlockOp (Constant (ConstStr s)) /\ i = clos_Str s \/
           x = BlockOp (Constant (ConstInt j)) /\ i = clos_Int j \/
           x = BlockOp (Constant (ConstWord64 w)) /\ i = clos_W64 w`,
  SIMP[clos_op_dest_Constant_pmatch] THEN REPEAT TOP_CASE_TAC THEN SIMP[] THEN MESON_TAC[]);;

(* HOL4: dest_Cons_thm *)
let dest_Cons_thm = prove
 (`clos_op_dest_Cons x = SOME i <=> x = BlockOp (clos_Cons i)`,
  QCASES_ON "x" THEN SIMP[dest_Cons_pmatch] THEN QCASES_ON "a" THEN SIMP[]);;

(* a local helper: the bytes of strings are injective *)
let CLOSP2AUX_op_bytes_11 = prove
 (`!s1 s2. MAP ((word:num->byte) o ORD) (explode s1) =
           MAP ((word:num->byte) o ORD) (explode s2) <=> s1 = s2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM explode_11] THEN
  MATCH_MP_TAC INJ_MAP_EQ_IFF THEN
  REWRITE_TAC[INJ; IN_UNIV; o_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ORD_BOUND; ORD_11]);;

(* HOL4: eq_direct_thm *)
let eq_direct_thm = prove
 (`!x y env (s:(C,FFI)clos_state) res s1 t z.
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ eq_direct x y = SOME z ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FS[eq_direct_def] THEN
  CASES_ON `eq_direct_const x y` THEN FS[] THENL
   [CASES_ON `eq_direct_constant x y` THEN FS[]; ALL_TAC] THEN
  GVS([eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def; dest_Op_Nil_thm;
       dest_Const_thm; dest_Constant_thm; dest_Cons_thm] @ all_case_eqs()) THEN
  FS[clos_evaluate_def; clos_do_app_def; clos_do_int_app_def] THEN
  TRY (TOP_CASE_TAC THEN TOP_CASE_TAC THEN FS[] THEN IMP_RES_TAC clos_evaluate_SING THEN
       GVS[] THEN QCASES_ON "r1") THEN
  GVS([clos_do_eq_def; evaluate_MakeBool; make_const_def; CLOSP2AUX_op_bytes_11] @
      all_case_eqs()) THEN
  ASM_MESON_TAC[]);;

(* HOL4: dont_lift_thm *)
let dont_lift_thm = prove
 (`dont_lift x <=>
   (?t i. x = clos_Op t (IntOp (clos_Const i)) []) \/
   (?t n. x = clos_Op t (BlockOp (clos_Cons n)) []) \/
   (?t s. x = clos_Op t (BlockOp (Constant (ConstStr s))) []) \/
   (?t i. x = clos_Op t (BlockOp (Constant (ConstInt i))) []) \/
   (?t w. x = clos_Op t (BlockOp (Constant (ConstWord64 w))) [])`,
  SIMP[dont_lift_def] THEN REPEAT TOP_CASE_TAC THEN
  FS[dest_Op_Nil_thm; dest_Const_thm; dest_Cons_thm; dest_Constant_thm] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FS[dest_Op_Nil_def; dest_Op_def; dest_Const_def; dest_Cons_pmatch;
     clos_op_dest_Constant_pmatch]);;

(* HOL4: dont_lift_pure *)
let dont_lift_pure = prove
 (`dont_lift x ==> pure x`,
  RW[dont_lift_thm] THEN SIMP[pure_def; clos_pure_op_def]);;

(* HOL4: dont_lift_Rval *)
let dont_lift_Rval = prove
 (`dont_lift x /\ clos_evaluate ([x],env,s1) = (res,s2:(C,FFI)clos_state) ==>
   ?v. res = Rval [v] /\ s2 = s1`,
  RW[dont_lift_thm] THEN POP_ASSUM MP_TAC THEN
  SIMP[clos_evaluate_def; clos_do_app_def; clos_do_int_app_def] THEN MESON_TAC[]);;

(* HOL4: evaluate_dont_lift *)
let evaluate_dont_lift = prove
 (`clos_evaluate ([x],env,s1) = (Rval [v],s2:(C,FFI)clos_state) /\ dont_lift x ==>
   clos_evaluate ([x],env1,s) = (Rval [v],s:(C,FFI)clos_state)`,
  RW[dont_lift_thm] THEN FS[clos_evaluate_def; clos_do_app_def; clos_do_int_app_def]);;

(* local helpers: an induction theorem for lift_exps (instead of HOL4's     *)
(* lift_exps_ind, see the header) and the first steps of the proofs by it  *)
let CLOSP2AUX_op_lift_exps_ind = prove
 (`!P:clos_exp list -> num -> clos_exp list -> bool.
       (!n binds. P [] n binds) /\
       (!x xs n binds.
          (dont_lift x ==> P xs n binds) /\
          (~dont_lift x /\ dest_Op clos_op_dest_Cons x = NONE
           ==> P xs (n + 1) (APPEND binds [x])) /\
          (!t ys ys1 n1 binds1.
             ~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t,ys) /\
             lift_exps ys n binds = (ys1,n1,binds1) ==> P xs n1 binds1) /\
          (!t ys. ~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t,ys)
                  ==> P ys n binds)
          ==> P (CONS x xs) n binds)
       ==> !xs n binds. P xs n binds`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND] (ISPEC `list_size clos_exp_size` WF_MEASURE)) THEN
  REWRITE_TAC[MEASURE] THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun ih -> REPEAT GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] ih)) THEN
  TRY (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL1AUX_dest_Op_SOME)) THEN RVEQ_TAC THEN TERM_TAC);;

let CLOSP2AUX_OP_LIFT_SPLIT_TAC : tactic =
  MATCH_MP_TAC CLOSP2AUX_op_lift_exps_ind THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN ASM_CASES_TAC `dont_lift x` THENL
     [ALL_TAC;
      CASES_ON `dest_Op clos_op_dest_Cons x` THENL [ALL_TAC; QCASES_ON "a"]] THEN
    SIMP[]];;

let CLOSP2AUX_OP_LIFT_EXPS_TAC : tactic =
  CLOSP2AUX_OP_LIFT_SPLIT_TAC THEN RW[] THEN FS[lift_exps_def] THEN
  REPEAT (PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC;;

(* HOL4: lift_exps_acc *)
let lift_exps_acc = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> ?binds1. binds2 = APPEND binds binds1`,
  CLOSP2AUX_OP_LIFT_EXPS_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[APPEND_NIL]);;

(* a local helper: the counter of lift_exps counts the lifted expressions *)
let CLOSP2AUX_op_lift_exps_count = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> k + LENGTH binds = n + LENGTH binds2`,
  CLOSP2AUX_OP_LIFT_EXPS_TAC THEN FS[LENGTH_APPEND; LENGTH] THEN DECIDE_TAC);;

(* HOL4: lift_exps_n *)
let lift_exps_n = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==> k = LENGTH binds2`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC CLOSP2AUX_op_lift_exps_count THEN DECIDE_TAC);;

(* HOL4: lift_exps_length *)
let lift_exps_length = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> LENGTH xs = LENGTH ys`,
  CLOSP2AUX_OP_LIFT_EXPS_TAC THEN FS[]);;
(* HOL4: lift_exps_thm *)
let lift_exps_thm = prove
 (`!xs n binds env (s0:(C,FFI)clos_state) ys k vs0 binds2 s1 (s2:(C,FFI)clos_state) res0.
     clos_evaluate (binds,env,s0) = (Rval vs0,s1) /\
     clos_evaluate (xs,env,s1) = (res0,s2) /\ n = LENGTH binds /\
     lift_exps xs n binds = (ys,k,binds2) ==>
     ?res. clos_evaluate (binds2,env,s0) = (res,s2) /\
           (!err. res = Rerr err ==> res0 = res) /\
           !ws (s3:(C,FFI)clos_state) bind_vals.
             res = Rval bind_vals ==>
             ?vs. res0 = Rval vs /\ clos_evaluate (ys,APPEND bind_vals ws,s3) = (Rval vs,s3)`,
  let IH_TAC = FIRST_X_ASSUM (DRULE_ALL o check (is_imp o snd o strip_forall o concl)) THEN
               STRIP_TAC in
  let CONS_TAC = QPAT_X_ASSUM "clos_evaluate (CONS x xs,env,s1) = _" MP_TAC THEN
                 ONCE_REWRITE_TAC[clos_evaluate_CONS] in
  CLOSP2AUX_OP_LIFT_SPLIT_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP[lift_exps_def] THENL
   [STRIP_TAC THEN GVS[clos_evaluate_def];
    (* dont_lift x *)
    STRIP_TAC THEN RFS[] THEN REPEAT (PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN CONS_TAC THEN
    TOP_CASE_TAC THEN DRULE_ALL dont_lift_Rval THEN STRIP_TAC THEN GVS[] THEN
    TOP_CASE_TAC THEN RES_TAC THEN TOP_CASE_TAC THEN STRIP_TAC THEN GVS[] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC evaluate_dont_lift THEN SIMP[];
    (* x is lifted into binds *)
    STRIP_TAC THEN RFS[] THEN REPEAT (PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN CONS_TAC THEN
    TOP_CASE_TAC THEN TOP_CASE_TAC THENL
     [IMP_RES_TAC clos_evaluate_SING THEN GVS[] THEN
      FIRST_X_ASSUM (QSPECL_THEN ["env"; "s0"] MP_TAC) THEN
      SIMP[clos_evaluate_APPEND] THEN DISCH_TAC THEN TOP_CASE_TAC THEN RES_TAC THEN
      TOP_CASE_TAC THEN STRIP_TAC THEN GVS[] THEN
      REPEAT STRIP_TAC THEN IMP_RES_TAC lift_exps_acc THEN
      IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN GVS[clos_evaluate_APPEND] THEN
      EVERY_CASE_TAC THEN
      GVS[ARITH_ss; clos_evaluate_def; EL_APPEND; LENGTH_APPEND; LENGTH; EL; HD];
      STRIP_TAC THEN IMP_RES_TAC lift_exps_acc THEN GVS[clos_evaluate_APPEND]];
    (* x = Op t (Cons tag) ys0 *)
    STRIP_TAC THEN CONS_TAC THEN DISCH_TAC THEN RFS[] THEN
    GVS[pair_case_eq; dest_Op_thm; dest_Cons_thm; clos_evaluate_def; clos_do_app_def] THEN
    RENAME1 "lift_exps ys0 (LENGTH binds) binds = (ys1,n1,binds1)" THEN
    RENAME1 "lift_exps xs n1 binds1 = (xs1,k,binds2)" THEN
    RENAME1 "clos_evaluate (ys0,env,s1) = (r0,t1)" THEN
    IH_TAC THEN RENAME1 "clos_evaluate (binds1,env,s0) = (r1,t1)" THEN
    QCASES_ON "r0" THEN QCASES_ON "r1" THEN
    GVS[] THENL
     [RENAME1 "clos_evaluate (ys0,env,s1) = (Rval vs1,sa)" THEN
      QCASES_ON "clos_evaluate (xs,env,sa)" THEN
      RENAME1 "clos_evaluate (xs,env,sa) = (r2,t2)" THEN
      SUBGOAL_THEN `n1 = LENGTH (binds1:clos_exp list)` ASSUME_TAC THENL
       [ASM_MESON_TAC[lift_exps_n]; ALL_TAC] THEN
      IH_TAC THEN QCASES_ON "r2" THEN GVS[] THEN
      REPEAT STRIP_TAC THEN GVS[] THEN IMP_RES_TAC lift_exps_acc THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[clos_evaluate_APPEND]) THEN FS[] THEN
      EVERY_CASE_TAC THEN FS[] THEN GVS[] THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
      SIMP[clos_evaluate_def; clos_do_app_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN SIMP[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      IMP_RES_TAC lift_exps_acc THEN GVS[clos_evaluate_APPEND]]]);;

(* HOL4: lift_exps_Let *)
let lift_exps_Let = prove
 (`lift_exps [x] 0 [] = ([y],n,binds) /\
   clos_evaluate ([x],env,s1) = (res,s2:(C,FFI)clos_state) ==>
   clos_evaluate ([clos_Let backend_common_None binds y],env,s1) = (res,s2)`,
  STRIP_TAC THEN
  QSPECL_THEN ["[x]"; "0"; "[]"; "env"; "s1"] MP_TAC lift_exps_thm THEN
  SIMP[clos_evaluate_def; LENGTH] THEN STRIP_TAC THEN
  QCASES_ON "res'" THEN GVS[] THEN
  FIRST_X_ASSUM(QSPECL_THEN ["env"; "s2"] STRIP_ASSUME_TAC) THEN GVS[]);;

(* HOL4: simple_exp *)
let simple_exp_rules,simple_exp_ind,simple_exp_cases,simple_exp_strongind =
  cake_inductive
  `(!t i. simple_exp (clos_Var t i)) /\
   (!t x y z. simple_exp x /\ simple_exp y /\ simple_exp z ==>
              simple_exp (clos_If t x y z)) /\
   (!t i. simple_exp (clos_Op t (IntOp (clos_Const i)) [])) /\
   (!t i. simple_exp (clos_Op t (BlockOp (Constant (ConstInt i))) [])) /\
   (!t i. simple_exp (clos_Op t (BlockOp (Constant (ConstStr i))) [])) /\
   (!t i. simple_exp (clos_Op t (BlockOp (Constant (ConstWord64 i))) [])) /\
   (!t i xs. ALL simple_exp xs ==> simple_exp (clos_Op t (BlockOp (clos_Cons i)) xs)) /\
   (!t i x. simple_exp x ==> simple_exp (clos_Op t (BlockOp (EqualConst (clos_Int i))) [x])) /\
   (!t i x. simple_exp x ==> simple_exp (clos_Op t (BlockOp (EqualConst (clos_Str i))) [x])) /\
   (!t i x. simple_exp x ==> simple_exp (clos_Op t (BlockOp (EqualConst (clos_W64 i))) [x])) /\
   (!t i x. simple_exp x ==> simple_exp (clos_Op t (BlockOp (ElemAt i)) [x])) /\
   (!t x y. simple_exp x /\ simple_exp y ==> simple_exp (clos_Op t (BlockOp clos_Equal) [x; y])) /\
   (!t l y x. simple_exp x ==> simple_exp (clos_Op t (BlockOp (clos_TagLenEq l y)) [x]))`;;

(* HOL4: simple_exp_pure *)
let simple_exp_pure = prove
 (`!x. simple_exp x ==> pure x`,
  MATCH_MP_TAC simple_exp_ind THEN SIMP[pure_def; clos_pure_op_def]);;

(* HOL4: simple_exp_pure_every *)
let simple_exp_pure_every = prove
 (`ALL simple_exp xs ==> ALL pure xs`,
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[simple_exp_pure]);;

(* HOL4: lift_exps_simple_exp *)
let lift_exps_simple_exp = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> ALL simple_exp ys`,
  CLOSP2AUX_OP_LIFT_EXPS_TAC THEN GVS[dont_lift_thm] THEN SIMP[simple_exp_rules]);;

(* HOL4: evaluate_ConjList_append_F *)
let evaluate_ConjList_append_F = prove
 (`!xs ys.
     clos_evaluate ([ConjList xs],env1,r) = (Rval [clos_Boolv F],r) /\ ALL pure xs ==>
     clos_evaluate ([ConjList (APPEND xs ys)],env1,r) =
     (Rval [clos_Boolv F],r:(C,FFI)clos_state)`,
  LIST_INDUCT_TAC THENL [SIMP[ConjList_def; evaluate_MakeBool]; ALL_TAC] THEN
  QCASES_ON "t" THEN FS[ConjList_def] THEN GEN_TAC THENL
   [QCASES_ON "ys" THEN SIMP[ConjList_def; clos_evaluate_def; evaluate_MakeBool];
    SIMP[clos_evaluate_def] THEN STRIP_TAC THEN
    QSPECL_THEN ["h"; "env1"; "r"] MP_TAC pure_correct THEN
    REPEAT (CASE_TAC THEN FS[]) THEN RW[]]);;

(* HOL4: evaluate_ConjList_append_T *)
let evaluate_ConjList_append_T = prove
 (`!xs ys.
     clos_evaluate ([ConjList xs],env1,r) = (Rval [clos_Boolv T],r) /\ ALL pure xs ==>
     clos_evaluate ([ConjList (APPEND xs ys)],env1,r) =
     clos_evaluate ([ConjList ys],env1,r:(C,FFI)clos_state)`,
  LIST_INDUCT_TAC THENL [SIMP[]; ALL_TAC] THEN
  QCASES_ON "t" THEN FS[ConjList_def] THEN GEN_TAC THENL
   [QCASES_ON "ys" THEN REWRITE_TAC[ConjList_def; evaluate_MakeBool] THENL
     [MESON_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[HD]];
    SIMP[clos_evaluate_def] THEN STRIP_TAC THEN
    QSPECL_THEN ["h"; "env1"; "r"] MP_TAC pure_correct THEN
    REPEAT (CASE_TAC THEN FS[evaluate_MakeBool]) THEN RW[]]);;

(* HOL4: evaluate_ConjList_F *)
let evaluate_ConjList_F = prove
 (`clos_evaluate ([x],env,r) = (Rval [clos_Boolv F],r) ==>
   clos_evaluate ([ConjList (CONS x xs)],env,r) = (Rval [clos_Boolv F],r:(C,FFI)clos_state)`,
  QCASES_ON "xs" THEN SIMP[ConjList_def; clos_evaluate_def; evaluate_MakeBool]);;

(* HOL4: evaluate_ConjList_T *)
let evaluate_ConjList_T = prove
 (`clos_evaluate ([x],env,r) = (Rval [clos_Boolv T],r) /\
   clos_evaluate ([ConjList xs],env,r) = res ==>
   clos_evaluate ([ConjList (CONS x xs)],env,r) =
   (res:(clos_v list,clos_v)result#(C,FFI)clos_state)`,
  QCASES_ON "xs" THEN REWRITE_TAC[ConjList_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[HD] THEN
  ASM_MESON_TAC[evaluate_MakeBool]);;

(* HOL4: eq_direct_simple_exp *)
let eq_direct_simple_exp = prove
 (`eq_direct x y = SOME z /\ simple_exp x /\ simple_exp y ==> simple_exp z`,
  STRIP_TAC THEN
  GVS([eq_direct_def; eq_direct_const_def; eq_direct_nil_def; eq_direct_constant_def;
       dest_Op_Nil_thm; dest_Const_thm; dest_Constant_thm; dest_Cons_thm; MakeBool_def] @
      all_case_eqs()) THEN
  SIMP[simple_exp_rules]);;

(* local helpers: simple_exp of a Cons, and of the pairs that eq_pure_list  *)
(* makes for the elements of a Cons                                        *)
let CLOSP2AUX_op_simple_Cons = prove
 (`!t i xs. simple_exp (clos_Op t (BlockOp (clos_Cons i)) xs) <=> ALL simple_exp xs`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [simple_exp_cases] THEN SIMP[]);;

let CLOSP2AUX_op_simple_MAPi = prove
 (`!xs y. ALL simple_exp xs /\ simple_exp y ==>
     ALL (\(x,y). simple_exp x /\ simple_exp y)
       (MAPi (\i x. x,clos_Op backend_common_None (BlockOp (ElemAt i)) [y]) (REVERSE xs))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_MAPi; LENGTH_REVERSE] THEN
  RW[] THEN SIMP[simple_exp_rules] THEN
  ASM_MESON_TAC[ALL_MEM; MEM_EL; MEM_REVERSE; LENGTH_REVERSE]);;

(* HOL4: simple_exp_eq_pure_list *)
let simple_exp_eq_pure_list = prove
 (`!xs. ALL (\(x,y). simple_exp x /\ simple_exp y) xs ==>
        ALL simple_exp (append (eq_pure_list xs))`,
  MATCH_MP_TAC eq_pure_list_ind THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[eq_pure_list_def] THENL
   [REWRITE_TAC[append_thm; ALL]; ALL_TAC; FS[append_thm; ALL_APPEND]] THEN
  CASES_ON `eq_direct x y` THEN FS[append_thm] THENL
   [ALL_TAC; ASM_MESON_TAC[eq_direct_simple_exp]] THEN
  CASES_ON `dest_Op clos_op_dest_Cons x` THEN CASES_ON `dest_Op clos_op_dest_Cons y` THEN
  FS[append_thm] THENL
   [SIMP[simple_exp_rules];
    QCASES_ON "a" THEN RFS[];
    QCASES_ON "a" THEN RFS[append_thm; ALL_APPEND] THEN
    GVS[dest_Op_thm; dest_Cons_thm; CLOSP2AUX_op_simple_Cons] THEN CONJ_TAC THENL
     [SIMP[simple_exp_rules];
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_simple_MAPi THEN
      ASM_REWRITE_TAC[]];
    QCASES_ON "a" THEN QCASES_ON "a'" THEN RFS[] THEN
    GVS[dest_Op_thm; dest_Cons_thm; CLOSP2AUX_op_simple_Cons] THEN COND_CASES_TAC THEN
    FS[append_thm; MakeBool_def; simple_exp_rules] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    FS[DE_MORGAN_THM] THEN FS[every_zip_split; LENGTH_REVERSE; EVERY_REVERSE]]);;

(* HOL4: evaluate_EL *)
let evaluate_EL = prove
 (`!xs i vs.
     clos_evaluate (xs,env,s) = (Rval vs,s) /\ i < LENGTH xs /\ ALL pure xs ==>
     clos_evaluate ([EL i xs],env,s) = (Rval [EL i vs],s:(C,FFI)clos_state)`,
  LIST_INDUCT_TAC THEN SIMP[CONJUNCT1 LT] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [clos_evaluate_CONS] THEN
  STRIP_TAC THEN GVS(all_case_eqs()) THEN IMP_RES_TAC clos_evaluate_SING THEN
  IMP_RES_TAC evaluate_pure THEN GVS[] THEN QCASES_ON "i" THEN FS[]);;

(* HOL4: simpl_exp_Cons_EL *)
let simpl_exp_Cons_EL = prove
 (`simple_exp (clos_Op tra (BlockOp (clos_Cons n)) xs) /\ i < LENGTH xs ==>
   simple_exp (EL i xs)`,
  REWRITE_TAC[CLOSP2AUX_op_simple_Cons; GSYM ALL_EL] THEN MESON_TAC[]);;

(* local helpers for eq_pure_thm: dest_Op of a Cons without pairs, the     *)
(* value of a Cons, do_eq of singletons, ALL on an element of a reversed   *)
(* list, the values of two pure expressions, and the value of an element  *)
(* of a reversed list                                                      *)
let CLOSP2AUX_op_dest_Cons_SOME = prove
 (`!x p. dest_Op clos_op_dest_Cons x = SOME p <=>
         ?t tag xs. x = clos_Op t (BlockOp (clos_Cons tag)) xs /\ p = (tag,xs)`,
  REWRITE_TAC[FORALL_PAIR_THM; dest_Op_thm; dest_Cons_thm; PAIR_EQ] THEN MESON_TAC[]);;

let CLOSP2AUX_op_eval_Cons = prove
 (CASE_TERM `!t tag xs env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_Op t (BlockOp (clos_Cons tag)) xs],env,s) =
     match clos_evaluate (xs,env,s) with
       (Rval vs,s1) -> (Rval [clos_Block tag (REVERSE vs)],s1)
     | res -> res`,
  REPEAT GEN_TAC THEN SIMP[clos_evaluate_def; clos_do_app_def] THEN REPEAT TOP_CASE_TAC THEN
  SIMP[]);;

let CLOSP2AUX_op_do_eq_list_single = prove
 (`!x y. clos_do_eq_list [x] [y] = clos_do_eq x y`,
  REWRITE_TAC[CONJUNCT2 clos_do_eq_def] THEN REPEAT GEN_TAC THEN REPEAT TOP_CASE_TAC THEN
  SIMP[CONJUNCT2 clos_do_eq_def]);;

let CLOSP2AUX_op_ALL_EL_REVERSE = prove
 (`!P (l:A list) n. ALL P l /\ n < LENGTH l ==> P (EL n (REVERSE l))`,
  REWRITE_TAC[EVERY_EL] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_REVERSE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let CLOSP2AUX_op_eval_pure2 = prove
 (`!x y env (s:(C,FFI)clos_state) h1 h2.
     clos_evaluate ([x; y],env,s) = (Rval [h1; h2],s) /\ pure x /\ pure y ==>
     clos_evaluate ([x],env,s) = (Rval [h1],s) /\ clos_evaluate ([y],env,s) = (Rval [h2],s)`,
  REPEAT GEN_TAC THEN SIMP[clos_evaluate_def] THEN STRIP_TAC THEN
  QSPECL_THEN ["x"; "env"; "s"] MP_TAC pure_correct THEN
  EVERY_CASE_TAC THEN GVS[] THEN
  QSPECL_THEN ["y"; "env"; "s"] MP_TAC pure_correct THEN
  EVERY_CASE_TAC THEN GVS[LENGTH_EQ_NUM_compute] THEN RW[] THEN GVS[]);;

let CLOSP2AUX_op_evaluate_EL_REVERSE = prove
 (`!xs vs i env (s:(C,FFI)clos_state).
     clos_evaluate (xs,env,s) = (Rval vs,s) /\ i < LENGTH xs /\ ALL pure xs ==>
     clos_evaluate ([EL i (REVERSE xs)],env,s) = (Rval [EL i (REVERSE vs)],s)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN
  SUBGOAL_THEN `PRE (LENGTH (xs:clos_exp list) - i) < LENGTH xs /\ i < LENGTH (vs:clos_v list)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DRULE_ALL evaluate_EL THEN ASM_SIMP_TAC[EL_REVERSE]);;

(* HOL4: eq_pure_thm *)
let eq_pure_thm = prove
 (`clos_evaluate ([x1; y1],env1,r) = (Rval [h1; h2],r) /\ simple_exp x1 /\ simple_exp y1 /\
   clos_do_eq h1 h2 = Eq_val b ==>
   clos_evaluate ([eq_pure x1 y1],env1,r) = (Rval [clos_Boolv b],r:(C,FFI)clos_state)`,
  let DO_EQ_LIST = CONJUNCT2 clos_do_eq_def in
  (* GVS on the assumptions only, keeping the induction hypotheses as they are *)
  let KEEP_IH_GVS thl =
    REPEAT (FIRST_X_ASSUM (MP_TAC o
                           check (fun th -> is_forall (concl th) || is_imp (concl th)))) THEN
    REPEAT (CHANGED_TAC (GVS_ONE_PASS thl)) THEN REPEAT DISCH_TAC in
  let ARGS_TAC =
    IMP_RES_TAC simple_exp_pure THEN IMP_RES_TAC CLOSP2AUX_op_eval_pure2 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_op_simple_Cons]) THEN
    KEEP_IH_GVS([CLOSP2AUX_op_eval_Cons; clos_do_eq_def] @ all_case_eqs()) THEN
    IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN IMP_RES_TAC simple_exp_pure_every in
  let ELEM_TAC =
    SIMP[ARITH_ss; EL_ZIP; LENGTH_REVERSE; clos_evaluate_def; clos_do_app_def;
         simple_exp_rules] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_ALL_EL_REVERSE THEN ASM_REWRITE_TAC[] THEN
    DECIDE_TAC in
  REWRITE_TAC[eq_pure_def] THEN
  SUFF_TAC
   `!xs hs b.
      ALL2 (\x h. clos_evaluate ([FST x; SND x],env1,r) = (Rval [FST h; SND h],r) /\
                  simple_exp (FST x) /\ simple_exp (SND x)) xs hs /\
      clos_do_eq_list (MAP FST hs) (MAP SND hs) = Eq_val b /\
      ALL simple_exp (append (eq_pure_list xs)) ==>
      clos_evaluate ([ConjList (append (eq_pure_list xs))],env1,r) =
      (Rval [clos_Boolv b],r:(C,FFI)clos_state)` THENL
   [DISCH_THEN(fun th -> STRIP_TAC THEN QSPECL_THEN ["[x1,y1]"; "[h1,h2]"; "b"] MP_TAC th) THEN
    SIMP[ALL2] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP[DO_EQ_LIST] THEN CONJ_TAC THENL
     [QCASES_ON "b" THEN SIMP[DO_EQ_LIST];
      MATCH_MP_TAC simple_exp_eq_pure_list THEN SIMP[]];
    ALL_TAC] THEN
  MATCH_MP_TAC eq_pure_list_ind THEN REPEAT STRIP_TAC THENL
   [(* [] *)
    ONCE_REWRITE_TAC[eq_pure_list_def] THEN
    GVS[ALL2; append_thm; ConjList_def; evaluate_MakeBool; clos_do_eq_def];
    (* [x,y] *)
    QCASES_ON "hs" THEN FS[ALL2] THEN
    QCASES_ON "a1" THEN FS[ALL2; MAP; CLOSP2AUX_op_do_eq_list_single] THEN
    ONCE_REWRITE_TAC[eq_pure_list_def] THEN
    CASES_ON `eq_direct x y` THEN FS[append_thm; ConjList_def] THENL
     [ALL_TAC;
      QSPECL_THEN ["x"; "y"; "env1"; "r"] MP_TAC eq_direct_thm THEN
      SIMP[clos_evaluate_def; clos_do_app_def] THEN
      ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN SIMP[]] THEN
    CASES_ON `dest_Op clos_op_dest_Cons x` THEN CASES_ON `dest_Op clos_op_dest_Cons y` THEN
    FS[append_thm; ConjList_def] THEN GVS[CLOSP2AUX_op_dest_Cons_SOME] THENL
     [(* neither is a Cons *)
      SIMP[clos_evaluate_def; clos_do_app_def] THEN
      ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN SIMP[];
      (* only y: swap *)
      FIRST_X_ASSUM MATCH_MP_TAC THEN QEXISTS_TAC "[SND a0,FST a0]" THEN
      IMP_RES_TAC simple_exp_pure THEN IMP_RES_TAC CLOSP2AUX_op_eval_pure2 THEN
      ASM_SIMP_TAC[clos_evaluate_def; MAP; CLOSP2AUX_op_do_eq_list_single] THEN
      ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN SIMP[simple_exp_eq_pure_list; ALL];
      (* only x: TagLenEq, then the elements against ElemAt *)
      ARGS_TAC THEN RENAME1 "clos_evaluate (xs,env1,r) = (Rval vs,r)" THEN
      RENAME1 "clos_evaluate ([_],env1,r) = (Rval [clos_Block _ ws],r)" THEN
      FIRST
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC evaluate_ConjList_F THEN
        SIMP[clos_evaluate_def; clos_do_app_def] THEN ASM_MESON_TAC[] THEN NO_TAC;
        MATCH_MP_TAC evaluate_ConjList_T THEN CONJ_TAC THENL
         [SIMP[clos_evaluate_def; clos_do_app_def];
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          QEXISTS_TAC "ZIP (REVERSE vs) ws" THEN
          SIMP[LIST_REL_EL_EQN; LENGTH_MAPi; LENGTH_ZIP; LENGTH_REVERSE; MAP_FST_ZIP;
               MAP_SND_ZIP] THEN
          CONJ_TAC THENL
           [REPEAT STRIP_TAC THEN
            QSPECL_THEN ["xs"; "vs"; "n"; "env1"; "r"] MP_TAC CLOSP2AUX_op_evaluate_EL_REVERSE THEN
            ELEM_TAC;
            MATCH_MP_TAC simple_exp_eq_pure_list THEN MATCH_MP_TAC CLOSP2AUX_op_simple_MAPi THEN
            ASM_REWRITE_TAC[]]]];
      (* both: the elements against each other *)
      ARGS_TAC THEN RENAME1 "clos_evaluate (xs,env1,r) = (Rval vs1,r)" THEN
      RENAME1 "clos_evaluate (xs',env1,r) = (Rval vs2,r)" THEN
      COND_CASES_TAC THEN RFS[append_thm; ConjList_def; evaluate_MakeBool] THEN
      TRY (DECIDE_TAC THEN NO_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      QEXISTS_TAC "ZIP (REVERSE vs1) (REVERSE vs2)" THEN
      SIMP[LIST_REL_EL_EQN; LENGTH_ZIP; LENGTH_REVERSE; MAP_FST_ZIP; MAP_SND_ZIP] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        QSPECL_THEN ["xs"; "vs1"; "n"; "env1"; "r"] MP_TAC CLOSP2AUX_op_evaluate_EL_REVERSE THEN
        QSPECL_THEN ["xs'"; "vs2"; "n"; "env1"; "r"] MP_TAC CLOSP2AUX_op_evaluate_EL_REVERSE THEN
        ELEM_TAC;
        MATCH_MP_TAC simple_exp_eq_pure_list THEN
        SIMP[every_zip_split; LENGTH_REVERSE; EVERY_REVERSE]]];
    (* CONS *)
    REWRITE_TAC[CONJUNCT2 (CONJUNCT2 eq_pure_list_def); append_thm] THEN
    QCASES_ON "hs" THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2; MAP; DO_EQ_LIST]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
                REWRITE_RULE[CONJUNCT2 (CONJUNCT2 eq_pure_list_def); append_thm; ALL_APPEND] o
                check (can (term_match [] `ALL simple_exp (append (eq_pure_list l))`) o concl)) THEN
    IMP_RES_TAC simple_exp_pure_every THEN
    QCASES_ON "clos_do_eq (FST a0) (SND a0)" THEN FS[] THEN
    FIRST_X_ASSUM(QSPECL_THEN ["[a0]"; "a"] MP_TAC) THEN SIMP[MAP; DO_EQ_LIST] THEN
    ASM_CASES_TAC `a:bool` THEN RFS[] THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(QSPECL_THEN ["a1"; "b"] MP_TAC) THEN SIMP[] THEN
      SIMP[evaluate_ConjList_append_T];
      SIMP[evaluate_ConjList_append_F]]]);;

let CLOSP2AUX_op_dest_ops = prove
 (`(!op n. dest_ElemAt op = SOME n <=> op = BlockOp (ElemAt n)) /\
   (!op p. dest_TagLenEq op = SOME p <=>
           ?a b. p = (a,b) /\ op = BlockOp (clos_TagLenEq a b)) /\
   (!op n. dest_TagEq op = SOME n <=> op = BlockOp (TagEq n)) /\
   (!op n. dest_LenEq op = SOME n <=> op = BlockOp (clos_LenEq n))`,
  SIMP[dest_ElemAt_pmatch; dest_TagLenEq_pmatch; dest_TagEq_pmatch; dest_LenEq_pmatch] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT TOP_CASE_TAC THEN SIMP[] THEN
  MESON_TAC[PAIR_SURJECTIVE]);;

(* HOL4: SmartOp_thm *)
let clos_opProof_SmartOp_thm = prove
 (`clos_evaluate ([clos_Op t op xs],env,s) = (res,s1) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
   clos_evaluate ([clos_op_SmartOp t op xs],env,s) = (res,s1:(C,FFI)clos_state)`,
  SIMP[clos_op_SmartOp_def] THEN TOP_CASE_TAC THEN SIMP[] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN SIMP[SmartOp'_def] THEN REPEAT STRIP_TAC THENL
   [(* one argument: cons_op *)
    GVS([dest_Op_thm; dest_Cons_thm; cons_op_def; CLOSP2AUX_op_dest_ops] @ all_case_eqs()) THEN
    GVS([clos_evaluate_def; clos_do_app_def; evaluate_MakeBool] @ all_case_eqs()) THEN
    IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN
    GVS[ARITH_ss; EL_REVERSE; EL_APPEND; LENGTH_APPEND; ARITH_RULE `PRE (m - n) = m - (n + 1)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `dest_Op_Consts x y` THEN FS[] THENL
   [GVS([eq_op_def] @ all_case_eqs()) THENL
     [(* eq_any: the lifted bindings, then eq_pure_thm *)
      GVS([eq_any_def] @ all_case_eqs()) THEN
      MP_TAC(ISPECL [`[x;y]:clos_exp list`; `0`; `[]:clos_exp list`; `env:clos_v list`;
                     `s:(C,FFI)clos_state`] lift_exps_thm) THEN
      REWRITE_TAC[CONJUNCT1 clos_evaluate_def; LENGTH] THEN
      CASES_ON `clos_evaluate ([x;y],env,s:(C,FFI)clos_state)` THEN SIMP[] THEN STRIP_TAC THEN
      QPAT_X_ASSUM "clos_evaluate ([clos_Op _ _ _],_,_) = _" MP_TAC THEN
      ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
      QCASES_ON "res'" THEN FS[] THEN GVS[] THEN
      FIRST_X_ASSUM(QSPECL_THEN ["env"; "y'"] STRIP_ASSUME_TAC) THEN
      IMP_RES_TAC lift_exps_length THEN IMP_RES_TAC lift_exps_simple_exp THEN GVS[] THEN
      FIRST_ASSUM(MP_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH) THEN
      RW[LENGTH_EQ_NUM_compute] THEN GVS([clos_do_app_def] @ all_case_eqs()) THEN
      IRULE eq_pure_thm THEN ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN SIMP[];
      (* eq_direct *)
      DRULE_ALL eq_direct_thm THEN SIMP[]];
    (* two integer constants: int_op *)
    GVS([dest_Op_Consts_def; dest_Op_Nil_thm; dest_Const_thm] @ all_case_eqs()) THEN
    GVS([clos_op_int_op_def; MakeInt_def] @ all_case_eqs()) THEN
    GVS([clos_evaluate_def; clos_do_app_def; clos_do_int_app_def; evaluate_MakeBool;
         clos_do_eq_def; INT_GT; INT_GE] @ all_case_eqs())]);;

(* HOL4: red_rel *)
let red_rel_rules,red_rel_ind,red_rel_cases,red_rel_strongind = cake_inductive
  `(!xs ys t op iop i tag t1 t2 s w n.
      red_rel xs ys /\
      MEM op [IntOp iop;
              BlockOp clos_Equal; BlockOp (clos_Cons tag); BlockOp (ElemAt t1);
              BlockOp (clos_TagLenEq t1 t2); BlockOp (clos_LenEq n); BlockOp (TagEq tag);
              BlockOp (EqualConst (clos_Str s));
              BlockOp (EqualConst (clos_W64 w));
              BlockOp (EqualConst (clos_Int i));
              BlockOp (Constant (ConstInt i));
              BlockOp (Constant (ConstStr s));
              BlockOp (Constant (ConstWord64 w))] ==>
      red_rel [clos_Op t op xs] ys) /\
   red_rel [] [] /\
   (!x. red_rel [x] [x]) /\
   (!v t. red_rel [clos_Var t v] []) /\
   (!x y zs x1 x2.
      red_rel [x] x1 /\ red_rel (CONS y zs) x2 ==>
      red_rel (CONS x (CONS y zs)) (APPEND x1 x2)) /\
   (!xs x x1 t.
      red_rel xs x1 /\ red_rel [x] [] ==>
      red_rel [clos_Let t xs x] x1) /\
   (!x y z x1 x2 x3 t.
      red_rel [x] x1 /\ red_rel [y] x2 /\ red_rel [z] x3 ==>
      red_rel [clos_If t x y z] (APPEND (APPEND x1 x2) x3))`;;

(* HOL4: red_rel_Op, red_rel_multi, red_rel_Let (the named rules) *)
let red_rel_Op = el 0 (CONJUNCTS red_rel_rules);;
let red_rel_multi = el 4 (CONJUNCTS red_rel_rules);;
let red_rel_Let = el 5 (CONJUNCTS red_rel_rules);;

(* HOL4's simp [Once red_rel_cases] *)
let CLOSP2AUX_OP_RED_TAC : tactic =
  ONCE_REWRITE_TAC[red_rel_cases] THEN SIMP[MEM; red_rel_rules];;

(* HOL4: red_rel_nil *)
let red_rel_nil = prove
 (`!ys. red_rel [] ys <=> ys = []`,
  ONCE_REWRITE_TAC[red_rel_cases] THEN SIMP[]);;

(* HOL4: red_rel_ConjList *)
let red_rel_ConjList = prove
 (`!xs. red_rel xs [] ==> red_rel [ConjList xs] []`,
  MATCH_MP_TAC ConjList_ind THEN SIMP[ConjList_def; MakeBool_def] THEN RW[] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[red_rel_cases] THEN SIMP[] THEN RW[] THEN
  CLOSP2AUX_OP_RED_TAC);;

(* HOL4: red_rel_EVERY *)
let red_rel_EVERY = prove
 (`!xs. ALL (\h. red_rel [h] []) xs ==> red_rel xs []`,
  LIST_INDUCT_TAC THEN SIMP[ALL; red_rel_rules] THEN QCASES_ON "t" THEN
  RW[] THEN FS[] THEN CLOSP2AUX_OP_RED_TAC);;

(* HOL4: simple_exp_red_rel *)
let simple_exp_red_rel = prove
 (`!xs. ALL simple_exp xs ==> red_rel xs []`,
  SUBGOAL_THEN `!x. simple_exp x ==> red_rel [x] []` ASSUME_TAC THENL
   [MATCH_MP_TAC simple_exp_ind THEN RW[] THEN CLOSP2AUX_OP_RED_TAC THEN
    TRY (CLOSP2AUX_OP_RED_TAC THEN NO_TAC) THEN MATCH_MP_TAC red_rel_EVERY THEN FS[];
    SIMP[GSYM ALL_MEM] THEN ASM_MESON_TAC[red_rel_EVERY; ALL_MEM]]);;

(* HOL4: red_rel_eq_pure *)
let red_rel_eq_pure = prove
 (`simple_exp x /\ simple_exp y ==> red_rel [eq_pure x y] []`,
  STRIP_TAC THEN REWRITE_TAC[eq_pure_def] THEN MATCH_MP_TAC red_rel_ConjList THEN
  MATCH_MP_TAC simple_exp_red_rel THEN MATCH_MP_TAC simple_exp_eq_pure_list THEN
  ASM_REWRITE_TAC[ALL]);;

(* HOL4: IMP_red_rel_cons_0 *)
let IMP_red_rel_cons_0 = prove
 (`red_rel [x] ys /\ red_rel xs zs ==> red_rel (CONS x xs) (APPEND ys zs)`,
  QCASES_ON "xs" THEN SIMP[red_rel_nil; APPEND_NIL] THEN
  MESON_TAC[red_rel_multi]);;

(* HOL4: red_rel_exists_append *)
let red_rel_exists_append = prove
 (`red_rel (CONS h xs) ys <=>
   ?ys1 ys2. red_rel [h] ys1 /\ red_rel xs ys2 /\ ys = APPEND ys1 ys2`,
  QCASES_ON "xs" THEN SIMP[red_rel_nil; APPEND_NIL] THEN
  GEN_REWRITE_TAC LAND_CONV [red_rel_cases] THEN SIMP[] THEN MESON_TAC[]);;

(* HOL4: IMP_red_rel_append *)
let IMP_red_rel_append = prove
 (`!xs ys xs1 ys1.
     red_rel xs ys /\ red_rel xs1 ys1 ==> red_rel (APPEND xs xs1) (APPEND ys ys1)`,
  LIST_INDUCT_TAC THEN SIMP[red_rel_nil; APPEND] THEN
  ONCE_REWRITE_TAC[red_rel_exists_append] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[APPEND_ASSOC]);;

(* HOL4: IMP_red_rel_cons *)
let IMP_red_rel_cons = prove
 (`red_rel [x] [] /\ red_rel xs ys ==> red_rel (CONS x xs) ys`,
  STRIP_TAC THEN ONCE_REWRITE_TAC[red_rel_exists_append] THEN
  QEXISTS_TAC "[]" THEN QEXISTS_TAC "ys" THEN SIMP[APPEND]);;

(* HOL4: IMP_red_rel_cons_1 *)
let IMP_red_rel_cons_1 = prove
 (`red_rel xs ys ==> red_rel (CONS x xs) (CONS x ys)`,
  DISCH_TAC THEN ONCE_REWRITE_TAC[red_rel_exists_append] THEN QEXISTS_TAC "[x]" THEN
  SIMP[red_rel_rules; APPEND]);;

(* HOL4: red_rel_refl *)
let red_rel_refl = prove
 (`!xs. red_rel xs xs`,
  LIST_INDUCT_TAC THEN SIMP[red_rel_nil; IMP_red_rel_cons_1]);;

(* HOL4: lift_exps_red_rel *)
let lift_exps_red_rel = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==>
     ?zs. red_rel xs zs /\ red_rel (DROP (LENGTH binds) binds2) zs`,
  CLOSP2AUX_OP_LIFT_EXPS_TAC THEN IMP_RES_TAC lift_exps_acc THEN
  GVS[ARITH_ss; DROP_APPEND1; DROP_APPEND2; DROP_LENGTH_APPEND; DROP_0] THENL
   [SIMP[red_rel_nil];
    ASM_EXISTS_TAC THEN MATCH_MP_TAC IMP_red_rel_cons THEN GVS[dont_lift_thm] THEN
    CLOSP2AUX_OP_RED_TAC;
    ASM_MESON_TAC[IMP_red_rel_cons_1];
    GVS[dest_Op_thm; dest_Cons_thm] THEN
    ASM_MESON_TAC[IMP_red_rel_cons_0; IMP_red_rel_append; REWRITE_RULE[MEM] red_rel_Op]]);;

(* HOL4: eq_direct_red_rel *)
let eq_direct_red_rel = prove
 (`eq_direct x y = SOME z ==> ?ys. red_rel [x; y] ys /\ red_rel [z] ys`,
  STRIP_TAC THEN
  GVS([eq_direct_def; eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def;
       MakeBool_def; dest_Op_Nil_thm; dest_Const_thm; dest_Constant_thm; dest_Cons_thm] @
      all_case_eqs()) THEN
  IRULE_AT (Pos last) red_rel_Op THEN SIMP[MEM] THEN IRULE_AT (Pos last) red_rel_refl THEN
  FIRST [MATCH_MP_TAC IMP_red_rel_cons_1; MATCH_MP_TAC IMP_red_rel_cons] THEN
  CLOSP2AUX_OP_RED_TAC);;

(* HOL4: red_rel_exists *)
let red_rel_exists = prove
 (`!t op xs. ?ys. red_rel [clos_Op t op xs] ys /\ red_rel [clos_op_SmartOp t op xs] ys`,
  REPEAT GEN_TAC THEN SIMP[clos_op_SmartOp_def] THEN TOP_CASE_TAC THEN SIMP[] THENL
   [MESON_TAC[red_rel_refl]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN SIMP[SmartOp'_def] THEN REPEAT STRIP_TAC THENL
   [(* one argument: cons_op *)
    GVS([dest_Op_thm; dest_Cons_thm; cons_op_def; CLOSP2AUX_op_dest_ops] @ all_case_eqs()) THEN
    IRULE_AT (Pos hd) red_rel_Op THEN SIMP[MEM] THEN IRULE_AT (Pos hd) red_rel_Op THEN
    SIMP[MEM] THEN IRULE_AT (Pos hd) red_rel_refl THEN MATCH_MP_TAC red_rel_Let THEN
    SIMP[red_rel_refl; MakeBool_def] THEN CLOSP2AUX_OP_RED_TAC;
    ALL_TAC] THEN
  CASES_ON `dest_Op_Consts x y` THEN FS[] THENL
   [GVS([eq_op_def] @ all_case_eqs()) THENL
     [(* eq_any *)
      GVS([eq_any_def] @ all_case_eqs()) THEN IMP_RES_TAC lift_exps_simple_exp THEN
      IMP_RES_TAC lift_exps_red_rel THEN FS[ALL; LENGTH; DROP_0] THEN
      IRULE_AT (Pos hd) red_rel_Op THEN SIMP[MEM] THEN ASM_EXISTS_TAC THEN
      MATCH_MP_TAC red_rel_Let THEN SIMP[red_rel_eq_pure];
      (* eq_direct *)
      IMP_RES_TAC eq_direct_red_rel THEN ASM_EXISTS_TAC THEN IRULE red_rel_Op THEN SIMP[MEM]];
    (* two integer constants: int_op *)
    GVS([dest_Op_Consts_def; dest_Op_Nil_thm; dest_Const_thm] @ all_case_eqs()) THEN
    GVS([clos_op_int_op_def; MakeInt_def; MakeBool_def] @ all_case_eqs()) THEN
    QEXISTS_TAC "[]" THEN CLOSP2AUX_OP_RED_TAC THEN CLOSP2AUX_OP_RED_TAC THEN
    CLOSP2AUX_OP_RED_TAC]);;

(* HOL4: red_rel_pure *)
let red_rel_pure = prove
 (`!xs ys. red_rel xs ys ==> (ALL pure xs <=> ALL pure ys)`,
  MATCH_MP_TAC red_rel_ind THEN SIMP[pure_def; ALL; ALL_APPEND] THEN RW[] THEN
  FS[MEM] THEN SIMP[clos_pure_op_def] THEN MESON_TAC[]);;

(* HOL4: red_rel_elist_globals *)
let red_rel_elist_globals = prove
 (`!xs ys. red_rel xs ys ==> clos_elist_globals xs = clos_elist_globals ys`,
  MATCH_MP_TAC red_rel_ind THEN
  SIMP[clos_set_globals_def; clos_elist_globals_append; BAG_UNION_EMPTY] THEN RW[] THEN
  FS[MEM; clos_op_gbag_def; ASSOC_BAG_UNION; BAG_UNION_EMPTY]);;

(* HOL4: red_rel_esgc_free *)
let red_rel_esgc_free = prove
 (`!xs ys. red_rel xs ys ==> (ALL clos_esgc_free xs <=> ALL clos_esgc_free ys)`,
  MATCH_MP_TAC red_rel_ind THEN SIMP[ALL; ALL_APPEND; clos_esgc_free_def] THEN RW[] THEN
  FS[] THEN MESON_TAC[]);;

(* HOL4: SmartOp_simp *)
let SmartOp_simp = prove
 (`(pure (clos_op_SmartOp t op xs) <=> pure (clos_Op t op xs)) /\
   clos_set_globals (clos_op_SmartOp t op xs) = clos_set_globals (clos_Op t op xs) /\
   (clos_esgc_free (clos_op_SmartOp t op xs) <=> clos_esgc_free (clos_Op t op xs))`,
  QSPECL_THEN ["t"; "op"; "xs"] STRIP_ASSUME_TAC red_rel_exists THEN
  IMP_RES_TAC red_rel_pure THEN IMP_RES_TAC red_rel_elist_globals THEN
  IMP_RES_TAC red_rel_esgc_free THEN FS[ALL; clos_set_globals_def; BAG_UNION_EMPTY]);;

(* SmartOp leaves an operation alone when cons_op, int_op and eq_op do not *)
(* apply to it (HOL4: EVAL_TAC and case splits)                            *)
let CLOSP2AUX_OP_SMART_NONE_TAC : tactic =
  MATCH_MP_TAC list_split3 THEN SIMP[clos_op_SmartOp_def; SmartOp'_def] THEN
  REPEAT STRIP_TAC THEN TOP_CASE_TAC THEN
  GVS([cons_op_def; clos_op_int_op_def; dest_ElemAt_pmatch; dest_TagLenEq_pmatch;
       dest_TagEq_pmatch; dest_LenEq_pmatch] @ all_case_eqs());;

(* HOL4: SmartOp_Const *)
let SmartOp_Const = prove
 (`!xs. clos_op_SmartOp t (IntOp (clos_Const i)) xs = clos_Op t (IntOp (clos_Const i)) xs`,
  CLOSP2AUX_OP_SMART_NONE_TAC);;

(* HOL4: SmartOp_Cons *)
let SmartOp_Cons = prove
 (`!xs. clos_op_SmartOp t (BlockOp (clos_Cons n)) xs = clos_Op t (BlockOp (clos_Cons n)) xs`,
  CLOSP2AUX_OP_SMART_NONE_TAC);;

(* HOL4: SmartOp_Install *)
let SmartOp_Install = prove
 (`clos_op_SmartOp t clos_Install = clos_Op t clos_Install`,
  REWRITE_TAC[FUN_EQ_THM] THEN CLOSP2AUX_OP_SMART_NONE_TAC);;

(* a property tm of lists of expressions that red_rel preserves holds of  *)
(* SmartOp t op xs iff of Op t op xs (HOL4: qsuff_tac, then red_rel_ind)   *)
let CLOSP2AUX_OP_FROM_RED_TAC (tm:term) (thl:thm list) : tactic =
  SUBGOAL_THEN tm (fun th ->
    QSPECL_THEN ["t"; "op"; "xs"]
      (X_CHOOSE_THEN `ys:clos_exp list` (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP th)))
      red_rel_exists THEN FS thl) THEN
  MATCH_MP_TAC red_rel_ind THEN SIMP thl THEN RW[] THEN FS(CONJ_ASSOC :: thl);;

(* HOL4: code_locs_SmartOp *)
let code_locs_SmartOp = prove
 (`LIST_TO_BAG (code_locs [clos_op_SmartOp t op xs]) =
   LIST_TO_BAG (code_locs [clos_Op t op xs])`,
  CLOSP2AUX_OP_FROM_RED_TAC
    `!xs ys. red_rel xs ys ==> LIST_TO_BAG (code_locs xs) = LIST_TO_BAG (code_locs ys)`
    [code_locs_def; code_locs_append; LIST_TO_BAG_APPEND]);;

(* HOL4: every_Fn_SOME_SmartOp *)
let every_Fn_SOME_SmartOp = prove
 (`every_Fn_SOME [clos_op_SmartOp t op xs] <=> every_Fn_SOME [clos_Op t op xs]`,
  CLOSP2AUX_OP_FROM_RED_TAC
    `!xs ys. red_rel xs ys ==> (every_Fn_SOME xs <=> every_Fn_SOME ys)`
    [every_Fn_SOME_def; every_Fn_SOME_APPEND]);;

(* HOL4: every_Fn_vs_NONE_SmartOp *)
let every_Fn_vs_NONE_SmartOp = prove
 (`every_Fn_vs_NONE xs ==> every_Fn_vs_NONE [clos_op_SmartOp t op xs]`,
  CLOSP2AUX_OP_FROM_RED_TAC
    `!xs ys. red_rel xs ys ==> (every_Fn_vs_NONE xs <=> every_Fn_vs_NONE ys)`
    [every_Fn_vs_NONE_def; every_Fn_vs_NONE_APPEND]);;

(* HOL4: no_Labels_SmartOp *)
let no_Labels_SmartOp = prove
 (`no_Labels (clos_op_SmartOp t op xs) <=> no_Labels (clos_Op t op xs)`,
  CLOSP2AUX_OP_FROM_RED_TAC
    `!xs ys. red_rel xs ys ==> (ALL no_Labels xs <=> ALL no_Labels ys)`
    [no_Labels_def; ALL; ALL_APPEND]);;

(* HOL4: obeys_max_app_SmartOp *)
let obeys_max_app_SmartOp = prove
 (`ALL (obeys_max_app k) xs ==> obeys_max_app k (clos_op_SmartOp t op xs)`,
  CLOSP2AUX_OP_FROM_RED_TAC
    `!xs ys. red_rel xs ys ==> (ALL (obeys_max_app k) xs <=> ALL (obeys_max_app k) ys)`
    [obeys_max_app_def; ALL; ALL_APPEND]);;

(* HOL4: lift_exps_fv *)
let lift_exps_fv = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
     k = LENGTH binds2 /\
     (!l. fv l binds2 ==> fv l xs \/ fv l binds) /\
     (!l. fv l ys ==> l < k)`,
  SUFF_TAC
   `!xs n binds ys k binds2.
      lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
      (!l. fv l binds2 ==> fv l xs \/ fv l binds) /\ (!l. fv l ys ==> l < LENGTH binds2)` THENL
   [MESON_TAC[lift_exps_n]; ALL_TAC] THEN
  CLOSP2AUX_OP_LIFT_EXPS_TAC THEN IMP_RES_TAC lift_exps_n THEN IMP_RES_TAC lift_exps_acc THEN
  GVS[dont_lift_thm; dest_Op_thm; dest_Cons_thm; fv1_thm; LENGTH_APPEND] THEN
  RES_TAC THEN FIRST [DECIDE_TAC; ASM_MESON_TAC[]]);;

(* HOL4: fv1_ConjList *)
let fv1_ConjList = prove
 (`!xs. fv1 n (ConjList xs) <=> fv n xs`,
  MATCH_MP_TAC ConjList_ind THEN SIMP[ConjList_def; fv1_thm; MakeBool_def]);;

(* HOL4: fv1_EL *)
let fv1_EL = prove
 (`!xs n k. fv1 n (EL k xs) /\ k < LENGTH xs ==> fv n xs`,
  LIST_INDUCT_TAC THEN SIMP[ARITH_ss; LENGTH] THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP[EL; HD; TL; LT_SUC] THEN ASM_MESON_TAC[]);;

(* a local helper for fv1_eq_pure: fv1_EL on a reversed list *)
let CLOSP2AUX_op_fv_EL_REVERSE = prove
 (`!l i. fv1 n (EL i (REVERSE l)) /\ i < LENGTH l ==> fv n l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC fv1_EL THEN
  QEXISTS_TAC "PRE (LENGTH l - i)" THEN
  ASM_SIMP_TAC[GSYM EL_REVERSE; ARITH_RULE `i < l ==> PRE (l - i) < l`]);;

(* HOL4: fv1_eq_pure *)
let fv1_eq_pure = prove
 (`fv1 n (eq_pure x y) ==> fv1 n x \/ fv1 n y`,
  REWRITE_TAC[eq_pure_def; fv1_ConjList] THEN
  SUFF_TAC `!xs. fv n (append (eq_pure_list xs)) ==> EX (\(x,y). fv1 n x \/ fv1 n y) xs` THENL
   [DISCH_THEN(MP_TAC o SPEC `[x,y]:(clos_exp#clos_exp)list`) THEN SIMP[EX]; ALL_TAC] THEN
  MATCH_MP_TAC eq_pure_list_ind THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[eq_pure_list_def] THEN SIMP[append_thm] THENL
   [CASES_ON `eq_direct x y` THEN SIMP[append_thm] THENL
     [EVERY_CASE_TAC THEN GVS[append_thm; dest_Op_thm; dest_Cons_thm] THEN
      SIMP[fv1_thm; MakeBool_def] THEN STRIP_TAC THEN
      TRY (FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[]) THEN
      FS[GSYM EX_MEM; MEM_MAPi; MEM_ZIP; LENGTH_REVERSE; DE_MORGAN_THM] THEN STRIP_TAC THEN
      GVS[fv1_thm] THEN ASM_MESON_TAC[CLOSP2AUX_op_fv_EL_REVERSE];
      GVS([eq_direct_def; eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def;
           dest_Op_Nil_thm; MakeBool_def] @ all_case_eqs()) THEN SIMP[fv1_thm]];
    RW[] THEN RES_TAC THEN FS[]]);;

(* HOL4: eq_op_fv *)
let eq_op_fv = prove
 (`eq_op x y = SOME z ==> fv n [z] ==> fv n [x] \/ fv n [y]`,
  SIMP[eq_op_def] THEN CASES_ON `eq_direct x y` THEN SIMP[] THEN STRIP_TAC THENL
   [GVS([eq_any_def] @ all_case_eqs()) THEN
    MP_TAC(ISPECL [`[x;y]:clos_exp list`; `0`; `[]:clos_exp list`] lift_exps_fv) THEN
    SIMP[LENGTH; fv1_thm] THEN STRIP_TAC THEN
    ASM_MESON_TAC[fv1_eq_pure; ARITH_RULE `!n k. ~(n + k < k)`];
    GVS([eq_direct_def; eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def;
         dest_Op_Nil_thm; MakeBool_def] @ all_case_eqs()) THEN SIMP[fv1_thm]]);;

(* HOL4: fv1_SmartOp *)
let fv1_SmartOp = prove
 (`fv1 n (clos_op_SmartOp t op xs) ==> fv1 n (clos_Op t op xs)`,
  SIMP[clos_op_SmartOp_def] THEN TOP_CASE_TAC THEN SIMP[] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN SIMP[SmartOp'_def] THEN REPEAT STRIP_TAC THENL
   [GVS([dest_Op_thm; dest_Cons_thm; cons_op_def; CLOSP2AUX_op_dest_ops] @ all_case_eqs()) THEN
    FS[fv1_thm; MakeBool_def] THEN DECIDE_TAC;
    CASES_ON `dest_Op_Consts x y` THEN FS[] THENL
     [IMP_RES_TAC eq_op_fv THEN FS[fv1_thm];
      GVS([dest_Op_Consts_def; dest_Op_Nil_thm; dest_Const_thm] @ all_case_eqs()) THEN
      GVS([clos_op_int_op_def; MakeInt_def; MakeBool_def] @ all_case_eqs()) THEN FS[fv1_thm]]]);;
