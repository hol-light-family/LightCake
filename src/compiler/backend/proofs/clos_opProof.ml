(* ========================================================================= *)
(* clos_opProof: port of HOL4 compiler/backend/proofs/clos_opProofScript.sml *)
(* (CakeML v3479).                                                           *)
(* Correctness proof for clos_op.                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_op.ml";;

type_invention_error := true;;

(* CLOSP2AUX_ names are local helpers. *)

(* HOL4: list_split3 [local] *)
let list_split3 = prove
 (`!P. P [] /\ (!x y z zs. P (CONS x (CONS y (CONS z zs)))) /\ (!x. P [x]) /\
       (!x y. P [x; y]) ==>
       !xs:A list. P xs`,
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `t:A list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `t':A list` list_CASES) THEN ASM_REWRITE_TAC[]);;

(* HOL4: evaluate_MakeBool [local] *)
let evaluate_MakeBool = prove
 (`!b. clos_evaluate ([MakeBool b],vs,s:(C,FFI)clos_state) = (Rval [clos_Boolv b],s)`,
  GEN_TAC THEN
  REWRITE_TAC[MakeBool_def; clos_evaluate_def; clos_Boolv_def; true_tag_def;
              false_tag_def] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"; REVERSE] THEN
  REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4: dest_Op_thm *)
let dest_Op_thm = prove
 (`dest_Op (f:clos_op->A option) x = SOME (i,ys) <=>
   ?tra y. x = clos_Op tra y ys /\ f y = SOME i`,
  CASES_ON `x:clos_exp` THEN
  REWRITE_TAC[dest_Op_def; distinctness "option"; distinctness "clos_exp";
              injectivity "clos_exp"] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CASES_ON `(f:clos_op->A option) a1` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4: dest_Op_Nil_thm *)
let dest_Op_Nil_thm = prove
 (`dest_Op_Nil (f:clos_op->A option) x = SOME i <=>
   ?tra y. x = clos_Op tra y [] /\ f y = SOME i`,
  CASES_ON `x:clos_exp` THEN
  REWRITE_TAC[dest_Op_Nil_def; dest_Op_def; distinctness "option"; distinctness "clos_exp";
              injectivity "clos_exp"] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CASES_ON `(f:clos_op->A option) a1` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN ASM_MESON_TAC[]);;

(* HOL4: dest_Const_thm *)
let dest_Const_thm = prove
 (`dest_Const x = SOME i <=> x = IntOp (clos_Const i)`,
  CASES_ON `x:clos_op` THEN
  REWRITE_TAC[dest_Const_def; distinctness "option"; distinctness "clos_op";
              injectivity "clos_op"] THEN
  CASES_ON `a:int_op` THEN
  REWRITE_TAC[dest_Const_def; distinctness "option"; injectivity "option";
              distinctness "int_op"; injectivity "int_op"] THEN
  MESON_TAC[]);;

(* HOL4: dest_Constant_thm *)
let dest_Constant_thm = prove
 (`clos_op_dest_Constant x = SOME i <=>
   ?s w j. x = BlockOp (Constant (ConstStr s)) /\ i = clos_Str s \/
           x = BlockOp (Constant (ConstInt j)) /\ i = clos_Int j \/
           x = BlockOp (Constant (ConstWord64 w)) /\ i = clos_W64 w`,
  REWRITE_TAC[clos_op_dest_Constant_pmatch] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"; injectivity "block_op";
              distinctness "const"; injectivity "const"] THEN MESON_TAC[]);;

(* HOL4: dest_Cons_thm *)
let dest_Cons_thm = prove
 (`clos_op_dest_Cons x = SOME i <=> x = BlockOp (clos_Cons i)`,
  REWRITE_TAC[dest_Cons_pmatch] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"; injectivity "block_op"] THEN
  MESON_TAC[]);;


(* local helpers: do_app of the operations that clos_op introduces (HOL4:   *)
(* EVAL_TAC, fs [do_app_def])                                                *)
let CLOSP2AUX_op_do_app = prove
 (CASE_TERM `(!xs (s:(C,FFI)clos_state) tag.
      clos_do_app (BlockOp (clos_Cons tag)) xs s = Rval (clos_Block tag xs,s)) /\
   (!(s:(C,FFI)clos_state) i.
      clos_do_app (IntOp (clos_Const i)) [] s = Rval (clos_Number i,s)) /\
   (!(s:(C,FFI)clos_state) c.
      clos_do_app (BlockOp (Constant c)) [] s = Rval (make_const c,s)) /\
   (!(s:(C,FFI)clos_state) x1 x2.
      clos_do_app (BlockOp clos_Equal) [x1; x2] s =
      (match clos_do_eq x1 x2 with
         Eq_val b -> Rval (clos_Boolv b,s)
       | _ -> Rerr (Rabort Rtype_error))) /\
   (!(s:(C,FFI)clos_state) p x1.
      clos_do_app (BlockOp (EqualConst p)) [x1] s =
      (match p with
         clos_Int i ->
           (match x1 with
              clos_Number j -> Rval (clos_Boolv (i = j), s)
            | _ -> Rerr (Rabort Rtype_error))
       | clos_W64 i ->
           (match x1 with
              clos_Word64 j -> Rval (clos_Boolv (i = j), s)
            | _ -> Rerr (Rabort Rtype_error))
       | clos_Str i ->
           (match x1 with
              ByteVector j -> Rval (clos_Boolv (j = MAP (word o ORD) (explode i)), s)
            | _ -> Rerr (Rabort Rtype_error))
       | _ -> Rerr (Rabort Rtype_error))) /\
   (!(s:(C,FFI)clos_state) n tag xs.
      clos_do_app (BlockOp (ElemAt n)) [clos_Block tag xs] s =
      if n < LENGTH xs then Rval (EL n xs, s) else Rerr (Rabort Rtype_error)) /\
   (!(s:(C,FFI)clos_state) n tag xs.
      clos_do_app (BlockOp (TagEq n)) [clos_Block tag xs] s =
      Rval (clos_Boolv (tag = n), s)) /\
   (!(s:(C,FFI)clos_state) l tag xs.
      clos_do_app (BlockOp (clos_LenEq l)) [clos_Block tag xs] s =
      Rval (clos_Boolv (LENGTH xs = l),s)) /\
   (!(s:(C,FFI)clos_state) n l tag xs.
      clos_do_app (BlockOp (clos_TagLenEq n l)) [clos_Block tag xs] s =
      Rval (clos_Boolv (tag = n /\ LENGTH xs = l),s)) /\
   (!(s:(C,FFI)clos_state) op vs.
      clos_do_app (IntOp op) vs s =
      (match clos_do_int_app op vs with
         SOME res -> Rval (res,s)
       | _ -> Rerr (Rabort Rtype_error)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[]);;

(* local helpers: the evaluation of the expressions that clos_op builds *)
let CLOSP2AUX_op_eval_Op = prove
 (CASE_TERM `!t op xs env (s:(C,FFI)clos_state).
     ~(op = clos_Install) /\ ~(op = clos_ThunkOp ForceThunk) ==>
     clos_evaluate ([clos_Op t op xs],env,s) =
     match clos_evaluate (xs,env,s) with
       (Rval vs,s1) ->
         (match clos_do_app op (REVERSE vs) s1 with
            Rval (v,s2) -> (Rval [v],s2)
          | Rerr err -> (Rerr err,s1))
     | res -> res`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN
  MP_TAC(ISPEC `clos_evaluate (xs,env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` SUBST1_TAC)) THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `clos_do_app op (REVERSE a) (s1:(C,FFI)clos_state)` THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `a':clos_v#(C,FFI)clos_state` THEN CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_not_install = prove
 (`(!p. ~(BlockOp p = clos_Install) /\ ~(BlockOp p = clos_ThunkOp ForceThunk)) /\
   (!p. ~(IntOp p = clos_Install) /\ ~(IntOp p = clos_ThunkOp ForceThunk))`,
  REWRITE_TAC[distinctness "clos_op"]);;

let CLOSP2AUX_op_eval_const = prove
 (`(!t i env (s:(C,FFI)clos_state).
      clos_evaluate ([clos_Op t (IntOp (clos_Const i)) []],env,s) =
      (Rval [clos_Number i],s)) /\
   (!t c env (s:(C,FFI)clos_state).
      clos_evaluate ([clos_Op t (BlockOp (Constant c)) []],env,s) =
      (Rval [make_const c],s)) /\
   (!t n env (s:(C,FFI)clos_state).
      clos_evaluate ([clos_Op t (BlockOp (clos_Cons n)) []],env,s) =
      (Rval [clos_Block n []],s))`,
  SIMP_TAC[CLOSP2AUX_op_eval_Op; CLOSP2AUX_op_not_install] THEN
  REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; CLOSP2AUX_op_do_app] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_pair_cases = prove
 (`!p:(A,B)result # C. (?a s. p = (Rval a,s)) \/ (?e s. p = (Rerr e,s))`,
  GEN_TAC THEN MP_TAC(ISPEC `p:(A,B)result # C` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `x:(A,B)result` THEN REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;

(* split the result of an evaluation tm: Rval with the singleton facts, or Rerr *)
let CLOSP2AUX_OP_EVAL_CASES_TAC (tm:term) : tactic =
  DISJ_CASES_THEN STRIP_ASSUME_TAC (ISPEC tm CLOSP2AUX_op_pair_cases) THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th THEN
                      TRY(fun g -> STRIP_ASSUME_TAC(MATCH_MP clos_evaluate_SING th) g)) THEN
  CASE_REWRITE_TAC[];;

let CLOSP2AUX_op_eval_Equal = prove
 (CASE_TERM `!t x y env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) =
     match clos_evaluate ([x],env,s) with
       (Rval v1,s2) ->
         (match clos_evaluate ([y],env,s2) with
            (Rval v2,s3) ->
              (match clos_do_eq (HD v2) (HD v1) with
                 Eq_val b -> (Rval [clos_Boolv b],s3)
               | _ -> (Rerr (Rabort Rtype_error),s3))
          | res -> res)
     | res -> res`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CLOSP2AUX_op_eval_Op; CLOSP2AUX_op_not_install] THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_OP_EVAL_CASES_TAC `clos_evaluate ([x],env,s:(C,FFI)clos_state)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_EVAL_CASES_TAC `clos_evaluate ([y],env,s':(C,FFI)clos_state)` THEN
  ASM_REWRITE_TAC[HD; REVERSE; APPEND; CLOSP2AUX_op_do_app] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `clos_do_eq r1' r1` THEN CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_eval_Op1 = prove
 (CASE_TERM `!t op y env (s:(C,FFI)clos_state).
     ~(op = clos_Install) /\ ~(op = clos_ThunkOp ForceThunk) ==>
     clos_evaluate ([clos_Op t op [y]],env,s) =
     match clos_evaluate ([y],env,s) with
       (Rval v1,s2) ->
         (match clos_do_app op [HD v1] s2 with
            Rval (v,s3) -> (Rval [v],s3)
          | Rerr err -> (Rerr err,s2))
     | res -> res`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLOSP2AUX_op_eval_Op] THEN
  MP_TAC(ISPEC `clos_evaluate ([y],env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` (fun th -> ASSUME_TAC th THEN SUBST1_TAC th))) THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) THEN
  ASM_REWRITE_TAC[HD; REVERSE; APPEND]);;

let CLOSP2AUX_OP_FIN_TAC (thl:thm list) : tactic =
  REWRITE_TAC(PAIR_EQ :: thl) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[injectivity "result"; CONS_11; clos_Boolv_11] THEN
  REWRITE_TAC[EQ_SYM_EQ];;

(* the cases of eq_direct: one or both arguments are constants; the source *)
(* (a test Equal) and the target agree unless the source is a type error   *)
let CLOSP2AUX_OP_EQ_TAC (eval_c:thm list) (vs:term list) : tactic =
  let one v =
    DISCH_TAC THEN REWRITE_TAC(CLOSP2AUX_op_eval_Equal :: eval_c) THEN
    CASE_REWRITE_TAC[] THEN SIMP_TAC[CLOSP2AUX_op_eval_Op1; CLOSP2AUX_op_not_install] THEN
    CLOSP2AUX_OP_EVAL_CASES_TAC
      (mk_comb(`clos_evaluate:clos_exp list#clos_v list#(C,FFI)clos_state->
                 (clos_v list,clos_v)result#(C,FFI)clos_state`,
               mk_pair(mk_list([v],`:clos_exp`),
                       mk_pair(`env:clos_v list`,`s:(C,FFI)clos_state`)))) THEN
    ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THENL
     [CASES_ON `r1:clos_v` THEN REWRITE_TAC eval_c THEN ONCE_REWRITE_TAC[clos_do_eq_def] THEN
      CASE_REWRITE_TAC[CLOSP2AUX_op_do_app] THEN CLOSP2AUX_OP_FIN_TAC eval_c;
      CLOSP2AUX_OP_FIN_TAC eval_c] in
  let both =
    REWRITE_TAC(CLOSP2AUX_op_eval_Equal :: eval_c) THEN
    CASE_REWRITE_TAC[HD] THEN REWRITE_TAC eval_c THEN ONCE_REWRITE_TAC[clos_do_eq_def] THEN
    CASE_REWRITE_TAC[] THEN CLOSP2AUX_OP_FIN_TAC eval_c in
  FIRST (map (fun t -> t THEN NO_TAC) (map one vs @ [both]));;

let CLOSP2AUX_op_eq_direct_const = prove
 (`!x y env (s:(C,FFI)clos_state) res s1 t z.
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ eq_direct_const x y = SOME z ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_direct_const_def] THEN
  CASES_ON `dest_Op_Nil dest_Const x` THEN CASES_ON `dest_Op_Nil dest_Const y` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_Op_Nil_thm; dest_Const_thm]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RVEQ_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[evaluate_MakeBool] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> MP_TAC th)) THEN
  CLOSP2AUX_OP_EQ_TAC [CLOSP2AUX_op_eval_const] [`x:clos_exp`; `y:clos_exp`]);;

(* a local helper: the bytes of strings are injective *)
let CLOSP2AUX_op_bytes_11 = prove
 (`!s1 s2. MAP ((word:num->byte) o ORD) (explode s1) =
           MAP ((word:num->byte) o ORD) (explode s2) <=> s1 = s2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM explode_11] THEN
  MATCH_MP_TAC INJ_MAP_EQ_IFF THEN
  REWRITE_TAC[INJ; IN_UNIV; o_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ORD_BOUND; ORD_11]);;

let CLOSP2AUX_op_eq_direct_constant = prove
 (`!x y env (s:(C,FFI)clos_state) res s1 t z.
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ eq_direct_constant x y = SOME z ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_direct_constant_def] THEN
  CASES_ON `dest_Op_Nil clos_op_dest_Constant x` THEN
  CASES_ON `dest_Op_Nil clos_op_dest_Constant y` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_Op_Nil_thm; dest_Constant_thm]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) || is_disj (concl th)
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RVEQ_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[evaluate_MakeBool] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> MP_TAC th)) THEN
  REWRITE_TAC[injectivity "const_part"; distinctness "const_part"] THEN
  CLOSP2AUX_OP_EQ_TAC [CLOSP2AUX_op_eval_const; make_const_def; CLOSP2AUX_op_bytes_11]
    [`x:clos_exp`; `y:clos_exp`]);;

let CLOSP2AUX_op_do_eq_nil = prove
 (`(!t1 t2 ys. clos_do_eq (clos_Block t1 []) (clos_Block t2 ys) =
               Eq_val (t1 = t2 /\ ys = [])) /\
   (!t1 t2 xs. clos_do_eq (clos_Block t1 xs) (clos_Block t2 []) =
               Eq_val (t1 = t2 /\ xs = []))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[clos_do_eq_def] THEN
  CASE_REWRITE_TAC[] THENL
   [STRUCT_CASES_TAC(ISPEC `ys:clos_v list` list_CASES);
    STRUCT_CASES_TAC(ISPEC `xs:clos_v list` list_CASES)] THEN
  REWRITE_TAC[LENGTH; NOT_CONS_NIL; ARITH_RULE `~(0 = SUC n) /\ ~(SUC n = 0)`] THEN
  ONCE_REWRITE_TAC[clos_do_eq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;

let CLOSP2AUX_op_eq_direct_nil = prove
 (`!x y env (s:(C,FFI)clos_state) res s1 t z.
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ eq_direct_nil x y = SOME z ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_direct_nil_def] THEN
  CASES_ON `dest_Op_Nil clos_op_dest_Cons x` THEN
  CASES_ON `dest_Op_Nil clos_op_dest_Cons y` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_Op_Nil_thm; dest_Cons_thm]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) || is_disj (concl th)
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RVEQ_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[evaluate_MakeBool] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> MP_TAC th)) THEN
  CLOSP2AUX_OP_EQ_TAC [CLOSP2AUX_op_eval_const; CLOSP2AUX_op_do_eq_nil; LENGTH; LENGTH_EQ_NIL]
    [`x:clos_exp`; `y:clos_exp`]);;

(* HOL4: eq_direct_thm *)
let eq_direct_thm = prove
 (`!x y env (s:(C,FFI)clos_state) res s1 t z.
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ eq_direct x y = SOME z ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`x:clos_exp`; `y:clos_exp`; `env:clos_v list`;
      `s:(C,FFI)clos_state`; `res:(clos_v list,clos_v)result`; `s1:(C,FFI)clos_state`;
      `t:tra`; `z:clos_exp`] th))
    [CLOSP2AUX_op_eq_direct_const; CLOSP2AUX_op_eq_direct_constant;
     CLOSP2AUX_op_eq_direct_nil] THEN
  REWRITE_TAC[eq_direct_def] THEN
  CASES_ON `eq_direct_const x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  CASES_ON `eq_direct_constant x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_dont_lift = prove
 (`dont_lift x <=> (?i. dest_Op_Nil dest_Const x = SOME i) \/
                   (?n. dest_Op_Nil clos_op_dest_Cons x = SOME n) \/
                   (?p. dest_Op_Nil clos_op_dest_Constant x = SOME p)`,
  REWRITE_TAC[dont_lift_def] THEN
  CASES_ON `dest_Op_Nil dest_Const x` THEN
  CASES_ON `dest_Op_Nil clos_op_dest_Cons x` THEN
  CASES_ON `dest_Op_Nil clos_op_dest_Constant x` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN MESON_TAC[]);;

(* HOL4: dont_lift_thm *)
let dont_lift_thm = prove
 (`dont_lift x <=>
   (?t i. x = clos_Op t (IntOp (clos_Const i)) []) \/
   (?t n. x = clos_Op t (BlockOp (clos_Cons n)) []) \/
   (?t s. x = clos_Op t (BlockOp (Constant (ConstStr s))) []) \/
   (?t i. x = clos_Op t (BlockOp (Constant (ConstInt i))) []) \/
   (?t w. x = clos_Op t (BlockOp (Constant (ConstWord64 w))) [])`,
  REWRITE_TAC[CLOSP2AUX_op_dont_lift; dest_Op_Nil_thm; dest_Const_thm; dest_Cons_thm;
              dest_Constant_thm] THEN
  MESON_TAC[]);;

(* HOL4: dont_lift_pure *)
let dont_lift_pure = prove
 (`dont_lift x ==> pure x`,
  REWRITE_TAC[dont_lift_thm] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pure_def; ALL; clos_pure_op_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4: dont_lift_Rval *)
let dont_lift_Rval = prove
 (`dont_lift x /\ clos_evaluate ([x],env,s1) = (res,s2:(C,FFI)clos_state) ==>
   ?v. res = Rval [v] /\ s2 = s1`,
  REWRITE_TAC[dont_lift_thm] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_op_eval_const; PAIR_EQ]) THEN
  ASM_MESON_TAC[]);;

(* HOL4: evaluate_dont_lift *)
let evaluate_dont_lift = prove
 (`clos_evaluate ([x],env,s1) = (Rval [v],s2:(C,FFI)clos_state) /\ dont_lift x ==>
   clos_evaluate ([x],env1,s) = (Rval [v],s:(C,FFI)clos_state)`,
  REWRITE_TAC[dont_lift_thm] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_op_eval_const; PAIR_EQ; injectivity "result";
                              CONS_11]) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_op_eval_const]);;

(* a local helper: the induction theorem of lift_exps (HOL4 lift_exps_ind;   *)
(* cake_ind "lift_exps" of clos_op.ml uses one name for the argument ys and  *)
(* the lifted ys of the recursive call, which makes its third hypothesis     *)
(* too weak for these proofs)                                                *)
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
  SUBGOAL_THEN `!m xs n binds. list_size clos_exp_size xs = m ==>
                (P:clos_exp list -> num -> clos_exp list -> bool) xs n binds`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (MESON[]
    `(!m'. m' < m ==> !xs n binds. list_size clos_exp_size xs = m' ==>
             (P:clos_exp list -> num -> clos_exp list -> bool) xs n binds) ==>
     (!xs n binds. list_size clos_exp_size xs < m ==> P xs n binds)`)) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:clos_exp list` list_CASES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
                             can (find_term (fun t -> try fst(dest_const t) = "dont_lift"
                                                     with Failure _ -> false)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
                             can (find_term (fun t -> try fst(dest_const t) = "<"
                                                     with Failure _ -> false)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
                                     is_var (rhs (concl th)))) THEN
  TRY (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL1AUX_dest_Op_SOME)) THEN
  RVEQ_TAC THEN TERM_TAC);;

(* local tactics and the properties of lift_exps (HOL4 proves the three    *)
(* theorems below separately, with the same steps)                          *)
let CLOSP2AUX_OP_RES_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let rec resolve depth th =
    let c = snd (strip_forall (concl th)) in
    if not (is_imp c) then [th] else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    flat (map (resolve (depth-1)) rs) in
  let ihs = filter (fun th -> is_imp (snd (strip_forall (concl th)))) asms in
  let res = flat (map (fun th -> resolve 5 (REWRITE_RULE[IMP_CONJ] th)) ihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY (fun th -> STRIP_ASSUME_TAC th) res gl;;

let CLOSP2AUX_op_counter = ref 0;;

let CLOSP2AUX_OP_WIT_TAC : tactic =
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  (fun (asl,w as gl) ->
     let v,bod = dest_exists w in
     let c1 = lhand bod in
     (EXISTS_TAC (rand (lhs c1)) THEN REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN
      ASM_ARITH_TAC) gl);;

(* name the first closed lift_exps call or pair scrutinee of the goal's     *)
(* antecedent, without rewriting the assumptions (PAIRARG_TAC rewrites      *)
(* them, which spoils the induction hypotheses)                              *)
let CLOSP2AUX_OP_NAME_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let is_cand t = (is_comb t && (try fst(dest_const(fst(strip_comb t))) = "lift_exps"
                                 with Failure _ -> false) &&
                   length (snd (strip_comb t)) = 3) in
  let rec find bvs tm =
    (if is_cand tm && not (exists (fun v -> vfree_in v tm) bvs) then [tm] else []) @
    (match tm with
       Comb(f,x) -> find bvs f @ find bvs x
     | Abs(v,b) -> find (v::bvs) b
     | _ -> []) in
  let tm = hd (find [] ant) in
  let ty = type_of tm in
  let ta,tbc = (match dest_type ty with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  let tb,tc = (match dest_type tbc with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP2AUX_op_counter;
  let k = string_of_int (!CLOSP2AUX_op_counter) in
  let a = mk_var("la"^k, ta) and p = mk_var("lp"^k, tbc)
  and b = mk_var("lb"^k, tb) and c = mk_var("lc"^k, tc) in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN p ASSUME_TAC)) THEN
   MP_TAC(ISPEC p PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN b (X_CHOOSE_THEN c SUBST_ALL_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN CASE_REWRITE_TAC[]) gl;;
let CLOSP2AUX_op_lift_exps_props = prove
 (`!xs n binds ys k binds2. lift_exps xs n binds = (ys,k,binds2) ==>
     LENGTH ys = LENGTH xs /\ ?binds1. binds2 = APPEND binds binds1 /\ k = n + LENGTH binds1`,
  MATCH_MP_TAC CLOSP2AUX_op_lift_exps_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[lift_exps_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[] THEN EXISTS_TAC `[]:clos_exp list` THEN
    REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[lift_exps_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [ALL_TAC;
      MP_TAC(ISPEC `a:num#clos_exp list` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:num` (X_CHOOSE_THEN `ys0:clos_exp list`
        SUBST_ALL_TAC)) THEN CASE_REWRITE_TAC[]]] THEN
   REPEAT CLOSP2AUX_OP_NAME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   STRIP_TAC THEN
   CLOSP2AUX_OP_RES_TAC THEN CLOSP2AUX_OP_RES_TAC THEN RVEQ_TAC THEN
   ASM_REWRITE_TAC[LENGTH] THEN CLOSP2AUX_OP_WIT_TAC);;

(* HOL4: lift_exps_acc *)
let lift_exps_acc = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> ?binds1. binds2 = APPEND binds binds1`,
  MESON_TAC[CLOSP2AUX_op_lift_exps_props]);;

(* HOL4: lift_exps_n *)
let lift_exps_n = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==> k = LENGTH binds2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_op_lift_exps_props) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND]);;

(* HOL4: lift_exps_length *)
let lift_exps_length = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> LENGTH xs = LENGTH ys`,
  MESON_TAC[CLOSP2AUX_op_lift_exps_props]);;

(* local helpers for lift_exps_thm: the evaluation of appended lists *)
let CLOSP2AUX_op_eval_APPEND_Rval = prove
 (`!xs ys env (s:(C,FFI)clos_state) vs s'.
     clos_evaluate (APPEND xs ys,env,s) = (Rval vs,s') <=>
     ?vs1 vs2 s1. clos_evaluate (xs,env,s) = (Rval vs1,s1) /\
                  clos_evaluate (ys,env,s1) = (Rval vs2,s') /\ vs = APPEND vs1 vs2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_evaluate_APPEND] THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (ISPEC `clos_evaluate (xs,env,s:(C,FFI)clos_state)` CLOSP2AUX_op_pair_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  TRY (DISJ_CASES_THEN STRIP_ASSUME_TAC
         (ISPEC `clos_evaluate (ys,env,s'':(C,FFI)clos_state)` CLOSP2AUX_op_pair_cases) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"]) THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_eval_APPEND_Rerr = prove
 (`!xs ys env (s:(C,FFI)clos_state) vs s1 r s'.
     clos_evaluate (xs,env,s) = (Rval vs,s1) /\
     clos_evaluate (ys,env,s1) = (Rerr r,s') ==>
     clos_evaluate (APPEND xs ys,env,s) = (Rerr r,s')`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_eval_APPEND_Rerr1 = prove
 (`!xs ys env (s:(C,FFI)clos_state) r s'.
     clos_evaluate (xs,env,s) = (Rerr r,s') ==>
     clos_evaluate (APPEND xs ys,env,s) = (Rerr r,s')`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* local helpers for lift_exps_thm: its statement as a predicate of xs, n   *)
(* and binds (instantiated with vsubst), and one lemma per case of          *)
(* CLOSP2AUX_op_lift_exps_ind                                               *)
let CLOSP2AUX_op_lift_P =
 `!env (s0:(C,FFI)clos_state) ys k vs0 binds2 s1 (s2:(C,FFI)clos_state) res0.
     clos_evaluate (binds,env,s0) = (Rval vs0,s1) /\
     clos_evaluate (xs,env,s1) = (res0,s2) /\ n = LENGTH binds /\
     lift_exps xs n binds = (ys,k,binds2) ==>
     ?res. clos_evaluate (binds2,env,s0) = (res,s2) /\
           (!err. res = Rerr err ==> res0 = res) /\
           !ws (s3:(C,FFI)clos_state) bind_vals.
             res = Rval bind_vals ==>
             ?vs. res0 = Rval vs /\ clos_evaluate (ys,APPEND bind_vals ws,s3) = (Rval vs,s3)`;;

let CLOSP2AUX_op_lp (xs:term) (n:term) (b:term) : term =
  vsubst [xs,`xs:clos_exp list`; n,`n:num`; b,`binds:clos_exp list`] CLOSP2AUX_op_lift_P;;

(* name the components of the triple tm by the variables a, b and c *)
let CLOSP2AUX_OP_PAIR3_TAC (tm:term) (a:term) (b:term) (c:term) : tactic =
  let ty = type_of tm in
  let tbc = (match dest_type ty with (_,[_;bc]) -> bc | _ -> failwith "PAIR3") in
  let p = genvar tbc in
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN p ASSUME_TAC)) THEN
  MP_TAC(ISPEC p PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN b (X_CHOOSE_THEN c SUBST_ALL_TAC));;

let CLOSP2AUX_op_dont_lift_eval = prove
 (`!x. dont_lift x ==> ?v. !env (s:(C,FFI)clos_state). clos_evaluate ([x],env,s) = (Rval [v],s)`,
  REWRITE_TAC[dont_lift_thm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSP2AUX_op_eval_const] THEN MESON_TAC[]);;

let CLOSP2AUX_op_eval_Cons_op = prove
 (CASE_TERM `!t tag ys env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_Op t (BlockOp (clos_Cons tag)) ys],env,s) =
     match clos_evaluate (ys,env,s) with
       (Rval vs,s1) -> (Rval [clos_Block tag (REVERSE vs)],s1)
     | res -> res`,
  SIMP_TAC[CLOSP2AUX_op_eval_Op; CLOSP2AUX_op_not_install] THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (ISPEC `clos_evaluate (ys,env,s:(C,FFI)clos_state)` CLOSP2AUX_op_pair_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSP2AUX_op_do_app] THEN CASE_REWRITE_TAC[]);;

(* resolve the implication th against the assumptions; add the result *)
let CLOSP2AUX_OP_RESOLVE_TAC (th:thm) : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rec resolve depth th =
    let c = snd (strip_forall (concl th)) in
    if not (is_imp c) then [th] else if depth = 0 then [] else
    let rs = mapfilter (fun a -> REWRITE_RULE[] (MATCH_MP th a)) asms in
    flat (map (resolve (depth-1)) rs) in
  match resolve 6 (REWRITE_RULE[IMP_CONJ] th) with
    r::_ -> ASSUME_TAC r g
  | [] -> failwith "CLOSP2AUX_OP_RESOLVE_TAC";;

(* use the assumption selected by p (an induction hypothesis) on the other  *)
(* assumptions, naming the witness of its conclusion v                      *)
let CLOSP2AUX_OP_USE_TAC (p:thm->bool) (v:term) : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rec resolve depth th =
    let c = snd (strip_forall (concl th)) in
    if not (is_imp c) then [th] else if depth = 0 then [] else
    let rs = mapfilter (fun a -> REWRITE_RULE[] (MATCH_MP th a)) asms in
    flat (map (resolve (depth-1)) rs) in
  FIRST_X_ASSUM(fun ih -> if p ih then
     (match resolve 6 (REWRITE_RULE[IMP_CONJ] ih) with
        th::_ -> X_CHOOSE_THEN v STRIP_ASSUME_TAC th
      | [] -> failwith "CLOSP2AUX_OP_USE_TAC")
   else failwith "CLOSP2AUX_OP_USE_TAC") g;;

let CLOSP2AUX_op_res_Rval = prove
 (`!(r:(A,B)result) v. (!err. r = Rerr err ==> Rval v = r) ==> ?w. r = Rval w`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,B)result` (cases "result")) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"] THEN MESON_TAC[]);;

let CLOSP2AUX_op_res_Rerr = prove
 (`!(r:(A,B)result) e. (!err. r = Rerr err ==> Rerr e = r) ==> r = Rerr e \/ ?w. r = Rval w`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,B)result` (cases "result")) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"] THEN MESON_TAC[]);;

(* the end of each case: the witness res of the induction hypothesis; pre   *)
(* adds the evaluations of the lifted expressions                           *)
let CLOSP2AUX_OP_LIFT_FINP_TAC (pre:tactic) : tactic =
  EXISTS_TAC `res:(clos_v list,clos_v)result` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
     if length (fst (strip_forall w)) = 1 then
       (X_GEN_TAC `err:(clos_v)error_result` THEN DISCH_THEN SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `err:(clos_v)error_result` o check (fun th ->
          is_forall (concl th) && free_in `err:(clos_v)error_result` (concl th))) THEN
        REWRITE_TAC[distinctness "result"; injectivity "result"] THEN MESON_TAC[]) g
     else
    (REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
       lhs (concl th) = `res:(clos_v list,clos_v)result`)) THEN
     pre THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`ws:clos_v list`; `s3:(C,FFI)clos_state`;
                                   `bind_vals:clos_v list`] o
                   check (fun th -> free_in `bind_vals:clos_v list` (concl th))) THEN
     ASM_REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
     DISCH_THEN(X_CHOOSE_THEN `vs1:clos_v list` STRIP_ASSUME_TAC) THEN
     REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[HD] THEN TRY(CASE_REWRITE_TAC[]))) THEN
     REWRITE_TAC[PAIR_EQ; injectivity "result"; HD] THEN MESON_TAC[]) g);;

let CLOSP2AUX_OP_LIFT_FIN_TAC = CLOSP2AUX_OP_LIFT_FINP_TAC ALL_TAC;;

let CLOSP2AUX_op_lift_dont = prove
 (mk_imp(`dont_lift x`,
     mk_imp(CLOSP2AUX_op_lp `xs:clos_exp list` `n:num` `binds:clos_exp list`,
            CLOSP2AUX_op_lp `CONS (x:clos_exp) xs` `n:num` `binds:clos_exp list`)),
  DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[lift_exps_def] THEN ASM_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs n binds`
    `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `v:clos_v` o MATCH_MP CLOSP2AUX_op_dont_lift_eval) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `CONS (x:clos_exp) xs`)) (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD] THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (ISPEC `clos_evaluate (xs,env,s1:(C,FFI)clos_state)` CLOSP2AUX_op_pair_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN CLOSP2AUX_OP_RES_TAC THEN CLOSP2AUX_OP_LIFT_FIN_TAC);;

(* split the evaluation tm of one expression: Rval [v] at state s, or Rerr e *)
let CLOSP2AUX_OP_SING_SPLIT_TAC (tm:term) (v:term) (s:term) (e:term) : tactic =
  let a = genvar `:clos_v list` in
  DISJ_CASES_THEN2
   (X_CHOOSE_THEN a (X_CHOOSE_THEN s (fun th ->
      ASSUME_TAC th THEN X_CHOOSE_THEN v SUBST_ALL_TAC (MATCH_MP clos_evaluate_SING th))))
   (X_CHOOSE_THEN e (X_CHOOSE_THEN s ASSUME_TAC))
   (ISPEC tm CLOSP2AUX_op_pair_cases) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = tm then REWRITE_TAC[th]
                        else NO_TAC) THEN CASE_REWRITE_TAC[];;

(* split the evaluation tm: Rval a at state s, or Rerr e *)
let CLOSP2AUX_OP_SPLIT_TAC (tm:term) (a:term) (s:term) (e:term) : tactic =
  DISJ_CASES_THEN2
   (X_CHOOSE_THEN a (X_CHOOSE_THEN s ASSUME_TAC))
   (X_CHOOSE_THEN e (X_CHOOSE_THEN s ASSUME_TAC))
   (ISPEC tm CLOSP2AUX_op_pair_cases) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = tm then REWRITE_TAC[th]
                        else NO_TAC) THEN CASE_REWRITE_TAC[];;

(* two evaluations of the same expressions give the same result *)
let CLOSP2AUX_OP_DET_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun th -> is_eq (concl th) && is_pair (rhs (concl th))) (map snd asl) in
  let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in
  let ps = filter (fun (a,b) -> lhs (concl a) = lhs (concl b) &&
                                not (rhs (concl a) = rhs (concl b))) (pairs eqs) in
  MAP_EVERY (fun (a,b) -> STRIP_ASSUME_TAC
    (REWRITE_RULE[PAIR_EQ; injectivity "result"; distinctness "result"] (TRANS (SYM a) b))) ps g;;

let CLOSP2AUX_op_lift_var = prove
 (`!binds x b env (s0:(C,FFI)clos_state) vs0 v s1 t1 bv t2 ws (s3:(C,FFI)clos_state) tr.
     clos_evaluate (binds,env,s0) = (Rval vs0,s1) /\
     clos_evaluate (APPEND binds [x],env,s0) = (Rval (APPEND vs0 [v]),t1) /\
     clos_evaluate (APPEND (APPEND binds [x]) b,env,s0) = (Rval bv,t2) ==>
     clos_evaluate ([clos_Var tr (LENGTH binds)],APPEND bv ws,s3) = (Rval [v],s3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[CLOSP2AUX_op_eval_APPEND_Rval] THEN STRIP_TAC THEN
  CLOSP2AUX_OP_DET_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> lhand (concl th) = `clos_evaluate (binds,env,s0:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL;
              EL; HD] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let CLOSP2AUX_op_lift_none = prove
 (mk_imp(`~dont_lift x /\ dest_Op clos_op_dest_Cons x = NONE`,
     mk_imp(CLOSP2AUX_op_lp `xs:clos_exp list` `n + 1` `APPEND binds [x:clos_exp]`,
            CLOSP2AUX_op_lp `CONS (x:clos_exp) xs` `n:num` `binds:clos_exp list`)),
  DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[lift_exps_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs (n + 1) (APPEND binds [x])`
    `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `CONS (x:clos_exp) xs`)) (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  CLOSP2AUX_OP_SING_SPLIT_TAC `clos_evaluate ([x],env,s1:(C,FFI)clos_state)`
    `v:clos_v` `t1:(C,FFI)clos_state` `e:(clos_v)error_result` THENL
   [SUBGOAL_THEN `clos_evaluate (APPEND binds [x],env,s0) =
                  (Rval (APPEND vs0 [v]),t1:(C,FFI)clos_state)` ASSUME_TAC THENL
     [REWRITE_TAC[CLOSP2AUX_op_eval_APPEND_Rval] THEN
      MAP_EVERY EXISTS_TAC [`vs0:clos_v list`; `[v:clos_v]`; `s1:(C,FFI)clos_state`] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (binds:clos_exp list) + 1 = LENGTH (APPEND binds [x:clos_exp])`
      ASSUME_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[HD] THEN
    CLOSP2AUX_OP_SPLIT_TAC `clos_evaluate (xs,env,t1:(C,FFI)clos_state)`
      `a2:clos_v list` `t2:(C,FFI)clos_state` `e2:(clos_v)error_result` THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_OP_USE_TAC (fun th -> is_forall (concl th) &&
      can (find_term ((=) `lift_exps xs`)) (concl th)) `res:(clos_v list,clos_v)result` THEN
    FIRST_ASSUM(X_CHOOSE_THEN `b1:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc) THEN
    CLOSP2AUX_OP_LIFT_FINP_TAC (CLOSP2AUX_OP_RESOLVE_TAC CLOSP2AUX_op_lift_var);
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `b1:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc) THEN
    EXISTS_TAC `Rerr e:(clos_v list,clos_v)result` THEN REWRITE_TAC[distinctness "result"] THEN
    MATCH_MP_TAC CLOSP2AUX_op_eval_APPEND_Rerr1 THEN
    MATCH_MP_TAC CLOSP2AUX_op_eval_APPEND_Rerr THEN ASM_MESON_TAC[]]);;

let CLOSP2AUX_op_lift_cons_bv = prove
 (`!binds1 b3 env (s0:(C,FFI)clos_state) bv1 t1 bind_vals t2 ys1 a1 ws (s3:(C,FFI)clos_state).
     clos_evaluate (binds1,env,s0) = (Rval bv1,t1) /\
     clos_evaluate (APPEND binds1 b3,env,s0) = (Rval bind_vals,t2) /\
     (!ws (s3:(C,FFI)clos_state). clos_evaluate (ys1,APPEND bv1 ws,s3) = (Rval a1,s3)) ==>
     clos_evaluate (ys1,APPEND bind_vals ws,s3) = (Rval a1,s3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSP2AUX_op_eval_APPEND_Rval] THEN STRIP_TAC THEN
  CLOSP2AUX_OP_DET_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[GSYM APPEND_ASSOC]);;

let CLOSP2AUX_op_lift_some = prove
 (mk_imp(`~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t,ys0)`,
   mk_imp(CLOSP2AUX_op_lp `ys0:clos_exp list` `n:num` `binds:clos_exp list`,
   mk_imp(list_mk_forall([`ys1:clos_exp list`; `n1:num`; `binds1:clos_exp list`],
            mk_imp(`lift_exps ys0 n binds = (ys1,n1,binds1)`,
                   CLOSP2AUX_op_lp `xs:clos_exp list` `n1:num` `binds1:clos_exp list`)),
          CLOSP2AUX_op_lp `CONS (x:clos_exp) xs` `n:num` `binds:clos_exp list`))),
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[lift_exps_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps ys0 n binds`
    `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs n1 binds1`
    `xs1:clos_exp list` `n2:num` `binds3:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o CONJUNCT2 o
    check (fun th -> is_conj (concl th) && is_neg (lhand (concl th)))) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res0:(clos_v list,clos_v)result, s2:(C,FFI)clos_state)`)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN REWRITE_TAC[CLOSP2AUX_op_eval_Cons_op] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP lift_exps_n o
    (fun th -> CONJ th (REFL `LENGTH (binds:clos_exp list)`)) o
    check (fun th -> is_eq (concl th) &&
                     lhs (concl th) = `lift_exps ys0 (LENGTH binds) binds`)) THEN
  CLOSP2AUX_OP_SPLIT_TAC `clos_evaluate (ys0,env,s1:(C,FFI)clos_state)`
    `a1:clos_v list` `t1:(C,FFI)clos_state` `e1:(clos_v)error_result` THEN
  CLOSP2AUX_OP_USE_TAC (fun th -> is_forall (concl th) &&
    not (can (find_term ((=) `xs:clos_exp list`)) (concl th)) &&
    can (find_term ((=) `ys0:clos_exp list`)) (concl th))
    `r4:(clos_v list,clos_v)result` THENL
   [(* the arguments evaluate to a1 *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `bv1:clos_v list` SUBST_ALL_TAC o
                  MATCH_MP CLOSP2AUX_op_res_Rval) THEN
    SUBGOAL_THEN `!ws (s3:(C,FFI)clos_state). clos_evaluate (ys1,APPEND bv1 ws,s3) = (Rval a1,s3)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
        length (fst (strip_forall (concl th))) = 3 && free_in `bv1:clos_v list` (concl th))) THEN
      DISCH_TAC THEN REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`ws:clos_v list`; `s3:(C,FFI)clos_state`;
                                    `bv1:clos_v list`]) THEN
      REWRITE_TAC[injectivity "result"] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CLOSP2AUX_OP_SPLIT_TAC `clos_evaluate (xs,env,t1:(C,FFI)clos_state)`
      `a2:clos_v list` `t2:(C,FFI)clos_state` `e2:(clos_v)error_result` THEN
    REWRITE_TAC[PAIR_EQ; HD] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_OP_USE_TAC (fun th -> is_forall (concl th) &&
      can (find_term ((=) `lift_exps ys0`)) (concl th)) `res:(clos_v list,clos_v)result` THEN
    FIRST_ASSUM(X_CHOOSE_THEN `b3:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc o
      check (fun th -> is_eq (concl th) && can (find_term ((=) `lift_exps xs`)) (lhs (concl th)))) THEN
    CLOSP2AUX_OP_LIFT_FINP_TAC (CLOSP2AUX_OP_RESOLVE_TAC CLOSP2AUX_op_lift_cons_bv);
    (* the arguments raise e1 *)
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `w:clos_v list` SUBST_ALL_TAC) o
      MATCH_MP CLOSP2AUX_op_res_Rerr) THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      FIRST_ASSUM(X_CHOOSE_THEN `b3:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc o
        check (fun th -> is_eq (concl th) &&
                         can (find_term ((=) `lift_exps xs`)) (lhs (concl th)))) THEN
      EXISTS_TAC `Rerr e1:(clos_v list,clos_v)result` THEN REWRITE_TAC[distinctness "result"] THEN
      MATCH_MP_TAC CLOSP2AUX_op_eval_APPEND_Rerr1 THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`[]:clos_v list`; `s0:(C,FFI)clos_state`; `w:clos_v list`] o
        check (fun th -> is_forall (concl th) && length (fst (strip_forall (concl th))) = 3)) THEN
      REWRITE_TAC[distinctness "result"]]]);;

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
  MATCH_MP_TAC CLOSP2AUX_op_lift_exps_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[lift_exps_def; clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN EXISTS_TAC `Rval vs0:(clos_v list,clos_v)result` THEN
    ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2")
    (CONJUNCTS_THEN2 (LABEL_TAC "H3") (LABEL_TAC "H4")))) THEN
  ASM_CASES_TAC `dont_lift x` THENL
   [MATCH_MP_TAC (MATCH_MP CLOSP2AUX_op_lift_dont (ASSUME `dont_lift x`)) THEN
    USE_THEN "H1" (fun h1 -> ACCEPT_TAC (MATCH_MP h1 (ASSUME `dont_lift x`)));
    ALL_TAC] THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num#clos_exp list` ASSUME_TAC)) THENL
   [SUBGOAL_THEN `~dont_lift x /\ dest_Op clos_op_dest_Cons x = NONE` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC (MATCH_MP CLOSP2AUX_op_lift_none
      (ASSUME `~dont_lift x /\ dest_Op clos_op_dest_Cons x = NONE`)) THEN
    USE_THEN "H2" (fun h2 -> ACCEPT_TAC (MATCH_MP h2
      (ASSUME `~dont_lift x /\ dest_Op clos_op_dest_Cons x = NONE`)));
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:num#clos_exp list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:num` (X_CHOOSE_THEN `ys0:clos_exp list` SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP CLOSP2AUX_op_lift_some
    (ASSUME `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)`)) THEN
  USE_THEN "H4" (fun h4 -> DISCH_THEN(fun th -> MATCH_MP_TAC (MATCH_MP th (MATCH_MP h4
    (ASSUME `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)`))))) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t0:num`; `ys0:clos_exp list`; `ys1:clos_exp list`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: lift_exps_Let *)
let lift_exps_Let = prove
 (`lift_exps [x] 0 [] = ([y],n,binds) /\
   clos_evaluate ([x],env,s1) = (res,s2:(C,FFI)clos_state) ==>
   clos_evaluate ([clos_Let backend_common_None binds y],env,s1) = (res,s2)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`[x:clos_exp]`; `0`; `[]:clos_exp list`; `env:clos_v list`;
                 `s1:(C,FFI)clos_state`; `[y:clos_exp]`; `n:num`; `[]:clos_v list`;
                 `binds:clos_exp list`; `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`] lift_exps_thm) THEN
  ASM_REWRITE_TAC[clos_evaluate_def; LENGTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[clos_evaluate_def] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `bv:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(clos_v)error_result` SUBST_ALL_TAC)
    (ISPEC `r:(clos_v list,clos_v)result` (cases "result")) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`env:clos_v list`; `s2:(C,FFI)clos_state`; `bv:clos_v list`] o
      check (fun th -> length (fst (strip_forall (concl th))) = 3)) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `e:(clos_v)error_result` o
      check (fun th -> length (fst (strip_forall (concl th))) = 1)) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

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
  MATCH_MP_TAC simple_exp_ind THEN REWRITE_TAC[pure_def; ALL; clos_pure_op_def] THEN
  CASE_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* HOL4: simple_exp_pure_every *)
let simple_exp_pure_every = prove
 (`ALL simple_exp xs ==> ALL pure xs`,
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[simple_exp_pure]);;

let CLOSP2AUX_op_dont_lift_simple = prove
 (`!x. dont_lift x ==> simple_exp x`,
  REWRITE_TAC[dont_lift_thm] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[simple_exp_rules; ALL]);;

(* HOL4: lift_exps_simple_exp *)
let lift_exps_simple_exp = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==> ALL simple_exp ys`,
  MATCH_MP_TAC CLOSP2AUX_op_lift_exps_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[lift_exps_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[lift_exps_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [ALL_TAC;
      MP_TAC(ISPEC `a:num#clos_exp list` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:num` (X_CHOOSE_THEN `ys0:clos_exp list`
        SUBST_ALL_TAC)) THEN CASE_REWRITE_TAC[]]] THEN
  REPEAT CLOSP2AUX_OP_NAME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN
  CLOSP2AUX_OP_RES_TAC THEN CLOSP2AUX_OP_RES_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[ALL; simple_exp_rules; CLOSP2AUX_op_dont_lift_simple]);;

(* local helpers: the evaluation of If and of pure expressions *)
let CLOSP2AUX_op_eval_If = prove
 (`(!t x1 x2 x3 env (s:(C,FFI)clos_state) v s1.
      clos_evaluate ([x1],env,s) = (Rval [v],s1) ==>
      clos_evaluate ([clos_If t x1 x2 x3],env,s) =
      if clos_Boolv T = v then clos_evaluate ([x2],env,s1)
      else if clos_Boolv F = v then clos_evaluate ([x3],env,s1)
      else (Rerr (Rabort Rtype_error),s1)) /\
   (!t x1 x2 x3 env (s:(C,FFI)clos_state) e s1.
      clos_evaluate ([x1],env,s) = (Rerr e,s1) ==>
      clos_evaluate ([clos_If t x1 x2 x3],env,s) = (Rerr e,s1))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[HD]);;

let CLOSP2AUX_op_pure_eval = prove
 (`!h env (s:(C,FFI)clos_state). pure h ==>
     (?v. clos_evaluate ([h],env,s) = (Rval [v],s)) \/
     (?s1. clos_evaluate ([h],env,s) = (Rerr (Rabort Rtype_error),s1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `clos_evaluate ([h],env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`[h:clos_exp]`; `env:clos_v list`; `s:(C,FFI)clos_state`;
                 `r1:(clos_v list,clos_v)result`; `s1:(C,FFI)clos_state`] evaluate_pure) THEN
  ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) THEN RVEQ_TAC THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* rewrite the If expressions whose guards have known evaluations *)
let CLOSP2AUX_OP_IF_TAC : tactic =
  ASSUM_LIST(fun l -> REWRITE_TAC(mapfilter (MATCH_MP (CONJUNCT1 CLOSP2AUX_op_eval_If)) l @
                                  mapfilter (MATCH_MP (CONJUNCT2 CLOSP2AUX_op_eval_If)) l));;

(* HOL4: evaluate_ConjList_append_F *)
let evaluate_ConjList_append_F = prove
 (`!xs ys.
     clos_evaluate ([ConjList xs],env1,r) = (Rval [clos_Boolv F],r) /\ ALL pure xs ==>
     clos_evaluate ([ConjList (APPEND xs ys)],env1,r) =
     (Rval [clos_Boolv F],r:(C,FFI)clos_state)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ConjList_def; evaluate_MakeBool; PAIR_EQ; injectivity "result"; CONS_11;
                clos_Boolv_11];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `t1:clos_exp` (X_CHOOSE_THEN `t2:clos_exp list` SUBST_ALL_TAC))
    (ISPEC `t:clos_exp list` list_CASES) THEN
  REWRITE_TAC[ALL; APPEND; ConjList_def] THEN GEN_TAC THEN STRIP_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `y1:clos_exp` (X_CHOOSE_THEN `y2:clos_exp list` SUBST_ALL_TAC))
      (ISPEC `ys:clos_exp list` list_CASES) THEN
    ASM_REWRITE_TAC[ConjList_def] THEN CLOSP2AUX_OP_IF_TAC THEN
    REWRITE_TAC[clos_Boolv_11; evaluate_MakeBool];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:clos_exp`; `env1:clos_v list`; `r:(C,FFI)clos_state`]
    CLOSP2AUX_op_pure_eval) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_TAC `v:clos_v`) (X_CHOOSE_TAC `s1:(C,FFI)clos_state`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "clos_If" with Failure _ -> false))
      (lhs (concl th)))) THEN
  CLOSP2AUX_OP_IF_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ys:clos_exp list`) THEN
  ASM_REWRITE_TAC[ALL; APPEND]);;

(* HOL4: evaluate_ConjList_append_T *)
let evaluate_ConjList_append_T = prove
 (`!xs ys.
     clos_evaluate ([ConjList xs],env1,r) = (Rval [clos_Boolv T],r) /\ ALL pure xs ==>
     clos_evaluate ([ConjList (APPEND xs ys)],env1,r) =
     clos_evaluate ([ConjList ys],env1,r:(C,FFI)clos_state)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `t1:clos_exp` (X_CHOOSE_THEN `t2:clos_exp list` SUBST_ALL_TAC))
    (ISPEC `t:clos_exp list` list_CASES) THEN
  REWRITE_TAC[ALL; APPEND; ConjList_def] THEN GEN_TAC THEN STRIP_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `y1:clos_exp` (X_CHOOSE_THEN `y2:clos_exp list` SUBST_ALL_TAC))
      (ISPEC `ys:clos_exp list` list_CASES) THEN
    ASM_REWRITE_TAC[ConjList_def; evaluate_MakeBool] THEN CLOSP2AUX_OP_IF_TAC THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:clos_exp`; `env1:clos_v list`; `r:(C,FFI)clos_state`]
    CLOSP2AUX_op_pure_eval) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_TAC `v:clos_v`) (X_CHOOSE_TAC `s1:(C,FFI)clos_state`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "clos_If" with Failure _ -> false))
      (lhs (concl th)))) THEN
  CLOSP2AUX_OP_IF_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ys:clos_exp list`) THEN
    ASM_REWRITE_TAC[ALL; APPEND];
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[evaluate_MakeBool; PAIR_EQ; distinctness "result"; injectivity "result";
                    CONS_11; clos_Boolv_11]]);;

(* HOL4: evaluate_ConjList_F *)
let evaluate_ConjList_F = prove
 (`clos_evaluate ([x],env,r) = (Rval [clos_Boolv F],r) ==>
   clos_evaluate ([ConjList (CONS x xs)],env,r) = (Rval [clos_Boolv F],r:(C,FFI)clos_state)`,
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `y1:clos_exp` (X_CHOOSE_THEN `y2:clos_exp list` SUBST_ALL_TAC))
    (ISPEC `xs:clos_exp list` list_CASES) THEN
  REWRITE_TAC[ConjList_def] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CLOSP2AUX_OP_IF_TAC THEN
  REWRITE_TAC[clos_Boolv_11; evaluate_MakeBool]);;

(* HOL4: evaluate_ConjList_T *)
let evaluate_ConjList_T = prove
 (`clos_evaluate ([x],env,r) = (Rval [clos_Boolv T],r) /\
   clos_evaluate ([ConjList xs],env,r) = res ==>
   clos_evaluate ([ConjList (CONS x xs)],env,r) = (res:(clos_v list,clos_v)result#(C,FFI)clos_state)`,
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `y1:clos_exp` (X_CHOOSE_THEN `y2:clos_exp list` SUBST_ALL_TAC))
    (ISPEC `xs:clos_exp list` list_CASES) THEN
  REWRITE_TAC[ConjList_def; evaluate_MakeBool] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CLOSP2AUX_OP_IF_TAC THEN ASM_MESON_TAC[]);;

(* local helpers for eq_direct_simple_exp: its three cases *)
let CLOSP2AUX_op_simple_MakeBool = prove
 (`!b. simple_exp (MakeBool b)`,
  SIMP_TAC[MakeBool_def; simple_exp_rules; ALL]);;

let CLOSP2AUX_op_simple_direct = prove
 (`(eq_direct_const x y = SOME z /\ simple_exp x /\ simple_exp y ==> simple_exp z) /\
   (eq_direct_constant x y = SOME z /\ simple_exp x /\ simple_exp y ==> simple_exp z) /\
   (eq_direct_nil x y = SOME z /\ simple_exp x /\ simple_exp y ==> simple_exp z)`,
  REWRITE_TAC[eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def] THEN
  REPEAT CONJ_TAC THENL
   [CASES_ON `dest_Op_Nil dest_Const x` THEN CASES_ON `dest_Op_Nil dest_Const y`;
    CASES_ON `dest_Op_Nil clos_op_dest_Constant x` THEN
    CASES_ON `dest_Op_Nil clos_op_dest_Constant y`;
    CASES_ON `dest_Op_Nil clos_op_dest_Cons x` THEN
    CASES_ON `dest_Op_Nil clos_op_dest_Cons y`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_Op_Nil_thm; dest_Constant_thm]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) || is_disj (concl th)
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[CLOSP2AUX_op_simple_MakeBool; simple_exp_rules]);;

(* HOL4: eq_direct_simple_exp *)
let eq_direct_simple_exp = prove
 (`eq_direct x y = SOME z /\ simple_exp x /\ simple_exp y ==> simple_exp z`,
  MP_TAC CLOSP2AUX_op_simple_direct THEN REWRITE_TAC[eq_direct_def] THEN
  CASES_ON `eq_direct_const x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  CASES_ON `eq_direct_constant x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_simple_Cons = prove
 (`!t i xs. simple_exp (clos_Op t (BlockOp (clos_Cons i)) xs) <=> ALL simple_exp xs`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [simple_exp_cases] THEN
  REWRITE_TAC[distinctness "clos_exp"; injectivity "clos_exp"; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"; injectivity "block_op"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_simple_dest_Cons = prove
 (`!x t xs. dest_Op clos_op_dest_Cons x = SOME (t,xs) /\ simple_exp x ==> ALL simple_exp xs`,
  REWRITE_TAC[dest_Op_thm; dest_Cons_thm] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[CLOSP2AUX_op_simple_Cons]);;

let CLOSP2AUX_op_simple_MAPi = prove
 (`!xs y. ALL simple_exp xs /\ simple_exp y ==>
          ALL (\(x,y). simple_exp x /\ simple_exp y)
            (MAPi (\i x. x,clos_Op backend_common_None (BlockOp (ElemAt i)) [y])
                  (REVERSE xs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAPi; LENGTH_REVERSE] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ALL simple_exp xs` THEN
    ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] THEN REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_REVERSE];
    ASM_SIMP_TAC[simple_exp_rules]]);;

(* HOL4: simple_exp_eq_pure_list *)
let simple_exp_eq_pure_list = prove
 (`!xs. ALL (\(x,y). simple_exp x /\ simple_exp y) xs ==>
        ALL simple_exp (append (eq_pure_list xs))`,
  MATCH_MP_TAC eq_pure_list_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[eq_pure_list_def; append_thm; ALL];
    ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[CONJUNCT2 (CONJUNCT2 eq_pure_list_def)] THEN
    REWRITE_TAC[append_thm; ALL_APPEND] THEN ONCE_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL]] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1")
    (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))) THEN
  REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[CONJUNCT1 (CONJUNCT2 eq_pure_list_def)] THEN
  CASES_ON `eq_direct x y` THEN CASE_REWRITE_TAC[append_thm; ALL] THENL
   [ALL_TAC; ASM_MESON_TAC[eq_direct_simple_exp]] THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p1:num#clos_exp list` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons y` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p2:num#clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[append_thm; ALL] THENL
   [ASM_SIMP_TAC[simple_exp_rules; ALL];
    MP_TAC(ISPEC `p2:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `ys2:clos_exp list` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    USE_THEN "H1" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
                   SPECL [`t2:num`; `ys2:clos_exp list`]) THEN
    ASM_REWRITE_TAC[ALL];
    MP_TAC(ISPEC `p1:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[append_thm; ALL_APPEND; ALL] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[simple_exp_rules]; ALL_TAC] THEN
    USE_THEN "H2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
                   SPECL [`t1:num`; `xs1:clos_exp list`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSP2AUX_op_simple_MAPi THEN
    ASM_MESON_TAC[CLOSP2AUX_op_simple_dest_Cons];
    MP_TAC(ISPEC `p1:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `p2:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `ys2:clos_exp list` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[append_thm; ALL; CLOSP2AUX_op_simple_MakeBool]; ALL_TAC] THEN
    USE_THEN "H3" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
                   SPECL [`t1:num`; `t2:num`; `xs1:clos_exp list`; `ys2:clos_exp list`]) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    MP_TAC(ISPECL [`REVERSE xs1:clos_exp list`; `REVERSE ys2:clos_exp list`;
                   `simple_exp`; `simple_exp`] every_zip_split) THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE; EVERY_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[CLOSP2AUX_op_simple_dest_Cons]]);;

(* HOL4: evaluate_EL *)
let evaluate_EL = prove
 (`!xs i vs.
     clos_evaluate (xs,env,s) = (Rval vs,s) /\ i < LENGTH xs /\ ALL pure xs ==>
     clos_evaluate ([EL i xs],env,s) = (Rval [EL i vs],s:(C,FFI)clos_state)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:clos_exp`; `env:clos_v list`; `s:(C,FFI)clos_state`]
    CLOSP2AUX_op_pure_eval) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_CONS] o
    check (fun th -> is_eq (concl th) &&
                     lhs (concl th) = `clos_evaluate (CONS h t,env,s:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  CLOSP2AUX_OP_SPLIT_TAC `clos_evaluate (t,env,s:(C,FFI)clos_state)`
    `a2:clos_v list` `t2:(C,FFI)clos_state` `e2:(clos_v)error_result` THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; HD] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)
    (SPEC `i:num` num_CASES) THEN ASM_REWRITE_TAC[EL; HD; TL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LT_SUC]) THEN ASM_REWRITE_TAC[]);;

(* HOL4: simpl_exp_Cons_EL *)
let simpl_exp_Cons_EL = prove
 (`simple_exp (clos_Op tra (BlockOp (clos_Cons n)) xs) /\ i < LENGTH xs ==>
   simple_exp (EL i xs)`,
  REWRITE_TAC[CLOSP2AUX_op_simple_Cons; GSYM ALL_EL] THEN MESON_TAC[]);;

(* rewrite with the assumptions and reduce the exposed cases, repeatedly *)
let CLOSP2AUX_OP_EVAL_RW_TAC (thl:thm list) : tactic =
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC thl THEN TRY(CASE_REWRITE_TAC thl)));;

(* local helpers for eq_pure_thm *)
let CLOSP2AUX_op_eval_pair_pure = prove
 (`!x y env (s:(C,FFI)clos_state) h1 h2.
     pure x /\ pure y /\ clos_evaluate ([x; y],env,s) = (Rval [h1; h2],s) ==>
     clos_evaluate ([x],env,s) = (Rval [h1],s) /\ clos_evaluate ([y],env,s) = (Rval [h2],s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:clos_exp`; `env:clos_v list`; `s:(C,FFI)clos_state`]
    CLOSP2AUX_op_pure_eval) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_CONS] o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate ([x; y],env,s:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  MP_TAC(ISPECL [`y:clos_exp`; `env:clos_v list`; `s:(C,FFI)clos_state`]
    CLOSP2AUX_op_pure_eval) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"; CONS_11; HD] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_op_eval_two = prove
 (`!x y env (s:(C,FFI)clos_state) h1 h2.
     clos_evaluate ([x],env,s) = (Rval [h1],s) /\ clos_evaluate ([y],env,s) = (Rval [h2],s) ==>
     clos_evaluate ([x; y],env,s) = (Rval [h1; h2],s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  CLOSP2AUX_OP_EVAL_RW_TAC[HD]);;

let CLOSP2AUX_op_do_eq_list_sing = prove
 (`!h1 h2 b. clos_do_eq_list [h1] [h2] = Eq_val b <=> clos_do_eq h1 h2 = Eq_val b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 clos_do_eq_def] THEN
  CASES_ON `clos_do_eq h1 h2` THEN CASE_REWRITE_TAC[] THEN
  TRY (COND_CASES_TAC) THEN
  REWRITE_TAC[CONJUNCT2 clos_do_eq_def; injectivity "eq_result"; distinctness "eq_result"] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_op_eval_Equal_val = prove
 (`!x y env (s:(C,FFI)clos_state) h1 h2 b t.
     clos_evaluate ([x],env,s) = (Rval [h1],s) /\ clos_evaluate ([y],env,s) = (Rval [h2],s) /\
     clos_do_eq h1 h2 = Eq_val b ==>
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (Rval [clos_Boolv b],s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSP2AUX_op_eval_Equal] THEN
  CLOSP2AUX_OP_EVAL_RW_TAC[HD] THEN
  ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN CLOSP2AUX_OP_EVAL_RW_TAC[]);;

let CLOSP2AUX_op_epq_pair = prove
 (`!x y hs b.
     ALL2 (\p q. clos_evaluate ([FST p; SND p],env1,r) = (Rval [FST q; SND q],r) /\
                 simple_exp (FST p) /\ simple_exp (SND p)) [x,y] hs /\
     clos_do_eq_list (MAP FST hs) (MAP SND hs) = Eq_val b ==>
     ?h1 h2. hs = [h1,h2] /\ clos_evaluate ([x],env1,r) = (Rval [h1],r) /\
             clos_evaluate ([y],env1,r) = (Rval [h2],r:(C,FFI)clos_state) /\
             simple_exp x /\ simple_exp y /\ clos_do_eq h1 h2 = Eq_val b`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `hs:(clos_v#clos_v)list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
  STRUCT_CASES_TAC(ISPEC `t:(clos_v#clos_v)list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
  STRUCT_CASES_TAC(ISPEC `h:clos_v#clos_v` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[MAP; FST; SND; CLOSP2AUX_op_do_eq_list_sing] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x':clos_v`; `y':clos_v`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSP2AUX_op_eval_pair_pure THEN ASM_SIMP_TAC[simple_exp_pure]);;

let CLOSP2AUX_op_eval_Cons_val = prove
 (`!tra t1 xs env (s:(C,FFI)clos_state) h1 s1.
     clos_evaluate ([clos_Op tra (BlockOp (clos_Cons t1)) xs],env,s) = (Rval [h1],s1) <=>
     ?vs. clos_evaluate (xs,env,s) = (Rval vs,s1) /\ h1 = clos_Block t1 (REVERSE vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSP2AUX_op_eval_Cons_op] THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (ISPEC `clos_evaluate (xs,env,s:(C,FFI)clos_state)` CLOSP2AUX_op_pair_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; CONS_11] THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_do_eq_Block = prove
 (`!t1 l1 h2 b.
     clos_do_eq (clos_Block t1 l1) h2 = Eq_val b <=>
     ?t2 l2. h2 = clos_Block t2 l2 /\
             (if t1 = t2 /\ LENGTH l1 = LENGTH l2 then clos_do_eq_list l1 l2 = Eq_val b
              else b = F)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CONJUNCT1 clos_do_eq_def] THEN
  CASES_ON `h2:clos_v` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "eq_result"; distinctness "clos_v"; injectivity "clos_v"] THEN
  REWRITE_TAC[UNWIND_THM1; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "eq_result"] THEN MESON_TAC[]);;

let CLOSP2AUX_op_eval_EL_REVERSE = prove
 (`!xs vs n env (s:(C,FFI)clos_state).
     clos_evaluate (xs,env,s) = (Rval vs,s) /\ ALL pure xs /\ n < LENGTH xs ==>
     clos_evaluate ([EL n (REVERSE xs)],env,s) = (Rval [EL n (REVERSE vs)],s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_evaluate_IMP_LENGTH) THEN
  ASM_SIMP_TAC[EL_REVERSE] THEN
  SUBGOAL_THEN `PRE (LENGTH (vs:clos_v list) - n) < LENGTH (xs:clos_exp list)` ASSUME_TAC THENL
   [UNDISCH_TAC `n < LENGTH (xs:clos_exp list)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (vs:clos_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_REVERSE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `LENGTH (xs:clos_exp list)`)) THEN
  MATCH_MP_TAC evaluate_EL THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `n < LENGTH (xs:clos_exp list)` THEN ARITH_TAC);;

let CLOSP2AUX_op_eval_ElemAt = prove
 (`!y n env (s:(C,FFI)clos_state) t2 l2 tr.
     clos_evaluate ([y],env,s) = (Rval [clos_Block t2 l2],s) /\ n < LENGTH l2 ==>
     clos_evaluate ([clos_Op tr (BlockOp (ElemAt n)) [y]],env,s) = (Rval [EL n l2],s)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CLOSP2AUX_op_eval_Op1; CLOSP2AUX_op_not_install] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; CLOSP2AUX_op_do_app] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_epq_MAPi_rel = prove
 (`!xs vs y l2 t2.
     clos_evaluate (xs,env1,r) = (Rval vs,r) /\ ALL simple_exp xs /\ simple_exp y /\
     clos_evaluate ([y],env1,r) = (Rval [clos_Block t2 l2],r:(C,FFI)clos_state) /\
     LENGTH l2 = LENGTH xs ==>
     ALL2 (\p q. clos_evaluate ([FST p; SND p],env1,r) = (Rval [FST q; SND q],r) /\
                 simple_exp (FST p) /\ simple_exp (SND p))
       (MAPi (\i x. x,clos_Op backend_common_None (BlockOp (ElemAt i)) [y]) (REVERSE xs))
       (ZIP (REVERSE vs) l2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (xs,env1,r:(C,FFI)clos_state)`)) THEN
  SUBGOAL_THEN `LENGTH (REVERSE (vs:clos_v list)) = LENGTH (l2:clos_v list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REVERSE]; ALL_TAC] THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAPi; LENGTH_REVERSE] THEN
  ASM_SIMP_TAC[LENGTH_ZIP] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAPi; LENGTH_REVERSE; EL_ZIP] THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSP2AUX_op_eval_two THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSP2AUX_op_eval_EL_REVERSE THEN ASM_SIMP_TAC[simple_exp_pure_every];
      MATCH_MP_TAC CLOSP2AUX_op_eval_ElemAt THEN EXISTS_TAC `t2:num` THEN
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `ALL simple_exp (xs:clos_exp list)` THEN
    ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] THEN REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_REVERSE];
    ASM_SIMP_TAC[simple_exp_rules]]);;

let CLOSP2AUX_op_epq_ZIP_rel = prove
 (`!xs ys vs1 vs2.
     clos_evaluate (xs,env1,r) = (Rval vs1,r) /\ ALL simple_exp xs /\
     clos_evaluate (ys,env1,r) = (Rval vs2,r:(C,FFI)clos_state) /\ ALL simple_exp ys /\
     LENGTH xs = LENGTH ys ==>
     ALL2 (\p q. clos_evaluate ([FST p; SND p],env1,r) = (Rval [FST q; SND q],r) /\
                 simple_exp (FST p) /\ simple_exp (SND p))
       (ZIP (REVERSE xs) (REVERSE ys)) (ZIP (REVERSE vs1) (REVERSE vs2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (xs,env1,r:(C,FFI)clos_state)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (ys,env1,r:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_REVERSE] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ZIP; LENGTH_REVERSE] THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSP2AUX_op_eval_two THEN CONJ_TAC THEN
    MATCH_MP_TAC CLOSP2AUX_op_eval_EL_REVERSE THEN ASM_SIMP_TAC[simple_exp_pure_every];
    UNDISCH_TAC `ALL simple_exp (xs:clos_exp list)` THEN
    ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] THEN REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_REVERSE];
    UNDISCH_TAC `ALL simple_exp (ys:clos_exp list)` THEN
    ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] THEN REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_REVERSE]]);;

(* the generalisation of eq_pure_thm that HOL4 proves by eq_pure_list_ind *)
(* (its statement as a predicate of xs), and one lemma per case             *)
let CLOSP2AUX_op_epq_P =
 `!hs b.
     ALL2 (\p q. clos_evaluate ([FST p; SND p],env1,r) = (Rval [FST q; SND q],r) /\
                 simple_exp (FST p) /\ simple_exp (SND p)) xs hs /\
     clos_do_eq_list (MAP FST hs) (MAP SND hs) = Eq_val b /\
     ALL simple_exp (append (eq_pure_list xs)) ==>
     clos_evaluate ([ConjList (append (eq_pure_list xs))],env1,r) =
     (Rval [clos_Boolv b],r:(C,FFI)clos_state)`;;

let CLOSP2AUX_op_epq (xs:term) : term =
  vsubst [xs,`xs:(clos_exp#clos_exp)list`] CLOSP2AUX_op_epq_P;;

let CLOSP2AUX_op_epq_nil = prove
 (CLOSP2AUX_op_epq `[]:(clos_exp#clos_exp)list`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `hs:(clos_v#clos_v)list` list_CASES) THEN
  REWRITE_TAC[ALL2; MAP; eq_pure_list_def; append_thm; ConjList_def; evaluate_MakeBool;
              CONJUNCT2 clos_do_eq_def; injectivity "eq_result"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_op_do_eq_list_cons = prove
 (`!h1 h2 l1 l2 b. clos_do_eq_list (CONS h1 l1) (CONS h2 l2) = Eq_val b <=>
     clos_do_eq h1 h2 = Eq_val T /\ clos_do_eq_list l1 l2 = Eq_val b \/
     clos_do_eq h1 h2 = Eq_val F /\ b = F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 clos_do_eq_def] THEN
  CASES_ON `clos_do_eq h1 h2` THEN CASE_REWRITE_TAC[] THEN
  TRY (COND_CASES_TAC) THEN
  ASM_REWRITE_TAC[injectivity "eq_result"; distinctness "eq_result"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_epq_cons = prove
 (mk_imp(mk_conj(CLOSP2AUX_op_epq `CONS (v5:clos_exp#clos_exp) v6`,
                 CLOSP2AUX_op_epq `[v3:clos_exp,v4:clos_exp]`),
         CLOSP2AUX_op_epq `CONS (v3:clos_exp,v4:clos_exp) (CONS v5 v6)`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHR") (LABEL_TAC "IHL")) THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[CONJUNCT2 (CONJUNCT2 eq_pure_list_def)] THEN
  REWRITE_TAC[append_thm; ALL_APPEND] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `q1:clos_v#clos_v` (X_CHOOSE_THEN `qs:(clos_v#clos_v)list` SUBST_ALL_TAC))
    (ISPEC `hs:(clos_v#clos_v)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN
  MP_TAC(ISPEC `q1:clos_v#clos_v` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:clos_v` (X_CHOOSE_THEN `h2:clos_v` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[MAP; FST; SND; CLOSP2AUX_op_do_eq_list_cons] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `clos_evaluate ([ConjList (append (eq_pure_list [v3,v4]))],env1,r) =
                  (Rval [clos_Boolv T],r:(C,FFI)clos_state)` ASSUME_TAC THENL
     [USE_THEN "IHL" MATCH_MP_TAC THEN EXISTS_TAC `[h1,h2]:(clos_v#clos_v)list` THEN
      ASM_REWRITE_TAC[ALL2; MAP; FST; SND; CLOSP2AUX_op_do_eq_list_sing]; ALL_TAC] THEN
    SUBGOAL_THEN
      `clos_evaluate ([ConjList (APPEND (append (eq_pure_list [v3,v4]))
                                        (append (eq_pure_list (CONS v5 v6))))],env1,r) =
       clos_evaluate ([ConjList (append (eq_pure_list (CONS v5 v6)))],env1,
                      r:(C,FFI)clos_state)` SUBST1_TAC THENL
     [MATCH_MP_TAC evaluate_ConjList_append_T THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC simple_exp_pure_every THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    USE_THEN "IHR" MATCH_MP_TAC THEN EXISTS_TAC `qs:(clos_v#clos_v)list` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `clos_evaluate ([ConjList (append (eq_pure_list [v3,v4]))],env1,r) =
                  (Rval [clos_Boolv F],r:(C,FFI)clos_state)` ASSUME_TAC THENL
     [USE_THEN "IHL" MATCH_MP_TAC THEN EXISTS_TAC `[h1,h2]:(clos_v#clos_v)list` THEN
      ASM_REWRITE_TAC[ALL2; MAP; FST; SND; CLOSP2AUX_op_do_eq_list_sing]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC evaluate_ConjList_append_F THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC simple_exp_pure_every THEN ASM_REWRITE_TAC[]]]);;

(* the start of the cases of a pair [x,y]: unfold eq_pure_list [x,y] with  *)
(* the case facts and name the values of x and y                           *)
let CLOSP2AUX_OP_EPQ_START_TAC : tactic =
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[CONJUNCT1 (CONJUNCT2 eq_pure_list_def)] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[append_thm; APPEND; ALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:clos_exp`; `y:clos_exp`; `hs:(clos_v#clos_v)list`; `b:bool`]
    CLOSP2AUX_op_epq_pair) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:clos_v` (X_CHOOSE_THEN `h2:clos_v` STRIP_ASSUME_TAC));;

let CLOSP2AUX_op_epq_direct = prove
 (mk_imp(`eq_direct x y = SOME z`, CLOSP2AUX_op_epq `[x:clos_exp,y:clos_exp]`),
  DISCH_TAC THEN CLOSP2AUX_OP_EPQ_START_TAC THEN REWRITE_TAC[ConjList_def] THEN
  MATCH_MP_TAC eq_direct_thm THEN
  MAP_EVERY EXISTS_TAC [`x:clos_exp`; `y:clos_exp`; `backend_common_None`] THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  MATCH_MP_TAC CLOSP2AUX_op_eval_Equal_val THEN
  MAP_EVERY EXISTS_TAC [`h1:clos_v`; `h2:clos_v`] THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_op_epq_none = prove
 (mk_imp(`eq_direct x y = NONE /\ dest_Op clos_op_dest_Cons x = NONE /\
          dest_Op clos_op_dest_Cons y = NONE`, CLOSP2AUX_op_epq `[x:clos_exp,y:clos_exp]`),
  DISCH_TAC THEN CLOSP2AUX_OP_EPQ_START_TAC THEN REWRITE_TAC[ConjList_def] THEN
  MATCH_MP_TAC CLOSP2AUX_op_eval_Equal_val THEN
  MAP_EVERY EXISTS_TAC [`h1:clos_v`; `h2:clos_v`] THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_op_epq_swap = prove
 (mk_imp(`eq_direct x y = NONE /\ dest_Op clos_op_dest_Cons x = NONE /\
          dest_Op clos_op_dest_Cons y = SOME (t1,ys)`,
   mk_imp(CLOSP2AUX_op_epq `[y:clos_exp,x:clos_exp]`, CLOSP2AUX_op_epq `[x:clos_exp,y:clos_exp]`)),
  DISCH_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN CLOSP2AUX_OP_EPQ_START_TAC THEN
  USE_THEN "IH" MATCH_MP_TAC THEN EXISTS_TAC `[h2,h1]:(clos_v#clos_v)list` THEN
  ASM_REWRITE_TAC[ALL2; MAP; FST; SND; CLOSP2AUX_op_do_eq_list_sing] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSP2AUX_op_eval_two THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN ASM_REWRITE_TAC[]]);;

let CLOSP2AUX_op_eval_TagLenEq = prove
 (`!y n l env (s:(C,FFI)clos_state) t2 l2 tr.
     clos_evaluate ([y],env,s) = (Rval [clos_Block t2 l2],s) ==>
     clos_evaluate ([clos_Op tr (BlockOp (clos_TagLenEq n l)) [y]],env,s) =
     (Rval [clos_Boolv (t2 = n /\ LENGTH l2 = l)],s)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CLOSP2AUX_op_eval_Op1; CLOSP2AUX_op_not_install] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; CLOSP2AUX_op_do_app]);;

let CLOSP2AUX_op_epq_cons_nil = prove
 (mk_imp(`eq_direct x y = NONE /\ dest_Op clos_op_dest_Cons x = SOME (t1,xs) /\
          dest_Op clos_op_dest_Cons y = NONE`,
   mk_imp(CLOSP2AUX_op_epq
           `MAPi (\i x. x,clos_Op backend_common_None (BlockOp (ElemAt i)) [y:clos_exp])
                 (REVERSE (xs:clos_exp list))`,
          CLOSP2AUX_op_epq `[x:clos_exp,y:clos_exp]`)),
  DISCH_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN CLOSP2AUX_OP_EPQ_START_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o
    check (fun th -> is_conj (concl th) &&
      can (find_term ((=) `SOME (t1:num,xs:clos_exp list)`)) (concl th))) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(Rval [h1]:(clos_v list,clos_v)result,r:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_Cons_val] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:clos_v list` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `clos_do_eq`)) (lhs (concl th)))) THEN
  REWRITE_TAC[CLOSP2AUX_op_do_eq_Block] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `l2:clos_v list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (xs,env1,r:(C,FFI)clos_state)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[CLOSP2AUX_op_simple_Cons] o
    check (fun th -> can (find_term ((=) `clos_Cons`)) (concl th) &&
                     can (find_term ((=) `simple_exp`)) (concl th) &&
                     not (is_forall (concl th)))) THEN
  MP_TAC(ISPECL [`y:clos_exp`; `t1:num`; `LENGTH (xs:clos_exp list)`; `env1:clos_v list`;
                 `r:(C,FFI)clos_state`; `t2:num`; `l2:clos_v list`; `backend_common_None`]
    CLOSP2AUX_op_eval_TagLenEq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(t1:num) = t2 /\ LENGTH (REVERSE (vs:clos_v list)) = LENGTH (l2:clos_v list)`
  THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
      lhand (concl th) = `(t1:num) = t2`)) THEN
    RVEQ_TAC THEN
    SUBGOAL_THEN `LENGTH (l2:clos_v list) = LENGTH (xs:clos_exp list)` ASSUME_TAC THENL
     [UNDISCH_TAC `LENGTH (REVERSE (vs:clos_v list)) = LENGTH (l2:clos_v list)` THEN
      ASM_REWRITE_TAC[LENGTH_REVERSE] THEN DISCH_THEN(ACCEPT_TAC o SYM); ALL_TAC] THEN
    MATCH_MP_TAC evaluate_ConjList_T THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                               can (find_term ((=) `clos_TagLenEq`)) (lhs (concl th))
                            then REWRITE_TAC[th] else NO_TAC) THEN
      ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11; clos_Boolv_11];
      USE_THEN "IH" MATCH_MP_TAC THEN
      EXISTS_TAC `ZIP (REVERSE (vs:clos_v list)) (l2:clos_v list)` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSP2AUX_op_epq_MAPi_rel THEN EXISTS_TAC `t2:num` THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP];
        FIRST_ASSUM ACCEPT_TAC]];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC evaluate_ConjList_F THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                             can (find_term ((=) `clos_TagLenEq`)) (lhs (concl th))
                          then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11; clos_Boolv_11] THEN
    UNDISCH_TAC `~((t1:num) = t2 /\ LENGTH (REVERSE (vs:clos_v list)) = LENGTH (l2:clos_v list))` THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE] THEN MESON_TAC[]]);;

let CLOSP2AUX_op_do_eq_Block2 = prove
 (`!t1 l1 t2 l2.
     clos_do_eq (clos_Block t1 l1) (clos_Block t2 l2) =
     if t1 = t2 /\ LENGTH l1 = LENGTH l2 then clos_do_eq_list l1 l2 else Eq_val F`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 clos_do_eq_def] THEN
  CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_epq_cons_cons = prove
 (mk_imp(`eq_direct x y = NONE /\ dest_Op clos_op_dest_Cons x = SOME (t1,xs) /\
          dest_Op clos_op_dest_Cons y = SOME (t2,ys)`,
   mk_imp(mk_imp(`~(~((t1:num) = t2) \/ ~(LENGTH (xs:clos_exp list) = LENGTH (ys:clos_exp list)))`,
                 CLOSP2AUX_op_epq `ZIP (REVERSE (xs:clos_exp list)) (REVERSE (ys:clos_exp list))`),
          CLOSP2AUX_op_epq `[x:clos_exp,y:clos_exp]`)),
  DISCH_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN CLOSP2AUX_OP_EPQ_START_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o
    check (fun th -> is_conj (concl th) &&
      can (find_term ((=) `SOME (t1:num,xs:clos_exp list)`)) (concl th))) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(Rval [h1]:(clos_v list,clos_v)result,r:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_Cons_val] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs1:clos_v list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(Rval [h2]:(clos_v list,clos_v)result,r:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_Cons_val] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs2:clos_v list` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (xs,env1,r:(C,FFI)clos_state)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (ys,env1,r:(C,FFI)clos_state)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_op_simple_Cons]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `clos_do_eq`)) (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_op_do_eq_Block2; LENGTH_REVERSE] THEN
  ASM_CASES_TAC `(t1:num) = t2 /\ LENGTH (xs:clos_exp list) = LENGTH (ys:clos_exp list)` THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
      lhand (concl th) = `(t1:num) = t2`)) THEN
    RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      can (find_term ((=) `simple_exp`)) (concl th) &&
      can (find_term (fun t -> is_cond t)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "IH" (MP_TAC o REWRITE_RULE[ASSUME `LENGTH (xs:clos_exp list) = LENGTH (ys:clos_exp list)`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `ZIP (REVERSE (vs1:clos_v list)) (REVERSE (vs2:clos_v list))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSP2AUX_op_epq_ZIP_rel THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `LENGTH (REVERSE (vs1:clos_v list)) = LENGTH (REVERSE (vs2:clos_v list))`
        ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH_REVERSE]; ALL_TAC] THEN
      ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP];
      FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[injectivity "eq_result"] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      is_conj (dest_neg (concl th)))) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[append_thm; ConjList_def; evaluate_MakeBool]]);;

let CLOSP2AUX_op_eq_pure_gen = prove
 (mk_forall(`xs:(clos_exp#clos_exp)list`, CLOSP2AUX_op_epq `xs:(clos_exp#clos_exp)list`),
  MATCH_MP_TAC eq_pure_list_ind THEN REPEAT CONJ_TAC THENL
   [ACCEPT_TAC CLOSP2AUX_op_epq_nil;
    ALL_TAC;
    REPEAT GEN_TAC THEN ACCEPT_TAC CLOSP2AUX_op_epq_cons] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2")
    (LABEL_TAC "H3"))) THEN
  MP_TAC(ISPEC `eq_direct x y` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:clos_exp` ASSUME_TAC)) THENL
   [ALL_TAC; FIRST_ASSUM(ACCEPT_TAC o MATCH_MP CLOSP2AUX_op_epq_direct)] THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p1:num#clos_exp list` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons y` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p2:num#clos_exp list` ASSUME_TAC)) THEN
  TRY(MP_TAC(ISPEC `p1:num#clos_exp list` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs:clos_exp list` SUBST_ALL_TAC))) THEN
  TRY(MP_TAC(ISPEC `p2:num#clos_exp list` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `ys:clos_exp list` SUBST_ALL_TAC))) THENL
   [MATCH_MP_TAC CLOSP2AUX_op_epq_none THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (INST [`t2:num`,`t1:num`] CLOSP2AUX_op_epq_swap)) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "H1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t2:num`; `ys:clos_exp list`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] CLOSP2AUX_op_epq_cons_nil) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "H2" MATCH_MP_TAC THEN
    EXISTS_TAC `t1:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] CLOSP2AUX_op_epq_cons_cons) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t1:num`; `t2:num`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4: eq_pure_thm *)
let eq_pure_thm = prove
 (`clos_evaluate ([x1; y1],env1,r) = (Rval [h1; h2],r) /\ simple_exp x1 /\ simple_exp y1 /\
   clos_do_eq h1 h2 = Eq_val b ==>
   clos_evaluate ([eq_pure x1 y1],env1,r) = (Rval [clos_Boolv b],r:(C,FFI)clos_state)`,
  STRIP_TAC THEN REWRITE_TAC[eq_pure_def] THEN
  MATCH_MP_TAC CLOSP2AUX_op_eq_pure_gen THEN EXISTS_TAC `[h1,h2]:(clos_v#clos_v)list` THEN
  ASM_REWRITE_TAC[ALL2; MAP; FST; SND; CLOSP2AUX_op_do_eq_list_sing] THEN
  MATCH_MP_TAC simple_exp_eq_pure_list THEN ASM_REWRITE_TAC[ALL]);;

(* local helpers for SmartOp_thm: the cases of cons_op, int_op and eq_op *)
let CLOSP2AUX_op_dest_ops = prove
 (`(!op n. dest_ElemAt op = SOME n <=> op = BlockOp (ElemAt n)) /\
   (!op p. dest_TagLenEq op = SOME p <=>
           ?a b. p = (a,b) /\ op = BlockOp (clos_TagLenEq a b)) /\
   (!op n. dest_TagEq op = SOME n <=> op = BlockOp (TagEq n)) /\
   (!op n. dest_LenEq op = SOME n <=> op = BlockOp (clos_LenEq n))`,
  REWRITE_TAC[dest_ElemAt_pmatch; dest_TagLenEq_pmatch; dest_TagEq_pmatch;
              dest_LenEq_pmatch] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"; injectivity "block_op";
              PAIR_EQ] THEN
  MESON_TAC[PAIR_SURJECTIVE]);;

let CLOSP2AUX_op_eval_Let = prove
 (CASE_TERM `!t xs e env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_Let t xs e],env,s) =
     match clos_evaluate (xs,env,s) with
       (Rval vs,s1) -> clos_evaluate ([e],APPEND vs env,s1)
     | res -> res`,
  REWRITE_TAC[clos_evaluate_def]);;

let CLOSP2AUX_op_EL_REVERSE_APPEND = prove
 (`!n (vs:A list) env l. n < l /\ LENGTH vs = l ==>
     l - (n + 1) < LENGTH (APPEND vs env) /\
     EL (l - (n + 1)) (APPEND vs env) = EL n (REVERSE vs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_REVERSE; EL_APPEND; ARITH_RULE `n < l ==> l - (n + 1) < l`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let CLOSP2AUX_OP_SMART_CONS_TAC : tactic =
  CASE_REWRITE_TAC[] THEN TRY(COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res:(clos_v list,clos_v)result, s1:(C,FFI)clos_state)`)) THEN
  SIMP_TAC[CLOSP2AUX_op_eval_Op1; CLOSP2AUX_op_not_install; CLOSP2AUX_op_eval_Let] THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_Cons_op] THEN
  CLOSP2AUX_OP_SPLIT_TAC `clos_evaluate (xs1,env,s:(C,FFI)clos_state)`
    `vs:clos_v list` `s2:(C,FFI)clos_state` `e:(clos_v)error_result` THEN
  REWRITE_TAC[HD; CLOSP2AUX_op_do_app; evaluate_MakeBool] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_evaluate (xs1,env,s:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[LENGTH_REVERSE] THEN TRY(REWRITE_TAC[EQ_SYM_EQ] THEN NO_TAC) THEN
  TRY(CASE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[clos_evaluate_def; CLOSP2AUX_op_EL_REVERSE_APPEND] THEN NO_TAC);;

let CLOSP2AUX_op_smart_cons = prove
 (`!op t1 xs1 z t tra env (s:(C,FFI)clos_state) res s1.
     cons_op op t1 xs1 = SOME z /\
     clos_evaluate ([clos_Op t op [clos_Op tra (BlockOp (clos_Cons t1)) xs1]],env,s) =
     (res,s1) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cons_op_def] THEN
  MP_TAC(ISPEC `dest_ElemAt op` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `dest_TagLenEq op` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num#num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `dest_TagEq op` (cases "option")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
       [MP_TAC(ISPEC `dest_LenEq op` (cases "option")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[distinctness "option"];
        ALL_TAC];
      ALL_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_op_dest_ops]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN CLOSP2AUX_OP_SMART_CONS_TAC);;

let CLOSP2AUX_op_dest_Op_Consts = prove
 (`!x y i j. dest_Op_Consts x y = SOME (i,j) <=>
             (?tx. x = clos_Op tx (IntOp (clos_Const i)) []) /\
             (?ty. y = clos_Op ty (IntOp (clos_Const j)) [])`,
  SUBGOAL_THEN `!x y i j. dest_Op_Consts x y = SOME (i,j) <=>
                  dest_Op_Nil dest_Const x = SOME i /\ dest_Op_Nil dest_Const y = SOME j`
    (fun th -> REWRITE_TAC[th; dest_Op_Nil_thm; dest_Const_thm] THEN MESON_TAC[]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_Op_Consts_def] THEN
  CASES_ON `dest_Op_Nil dest_Const x` THEN CASES_ON `dest_Op_Nil dest_Const y` THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ]);;

let CLOSP2AUX_op_eval_consts2 = prove
 (`!tx ty i j env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_Op tx (IntOp (clos_Const i)) []; clos_Op ty (IntOp (clos_Const j)) []],
                    env,s) = (Rval [clos_Number i; clos_Number j],s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_eval_two THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_const]);;

let CLOSP2AUX_op_eval_MakeInt = prove
 (`!i env (s:(C,FFI)clos_state). clos_evaluate ([MakeInt i],env,s) = (Rval [clos_Number i],s)`,
  REWRITE_TAC[MakeInt_def; CLOSP2AUX_op_eval_const]);;

let CLOSP2AUX_op_do_eq_Number = prove
 (`!a b. clos_do_eq (clos_Number a) (clos_Number b) = Eq_val (a = b)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 clos_do_eq_def] THEN
  CASE_REWRITE_TAC[]);;

let CLOSP2AUX_op_smart_int = prove
 (`!op x y i j z t env (s:(C,FFI)clos_state) res s1.
     dest_Op_Consts x y = SOME (i,j) /\ clos_op_int_op op i j = SOME z /\
     clos_evaluate ([clos_Op t op [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSP2AUX_op_dest_Op_Consts] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `clos_op_int_op`)) (lhs (concl th)))) THEN
  REWRITE_TAC[clos_op_int_op_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"; distinctness "option"]) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res:(clos_v list,clos_v)result, s1:(C,FFI)clos_state)`)) THEN
  SIMP_TAC[CLOSP2AUX_op_eval_Op; CLOSP2AUX_op_not_install] THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_consts2] THEN CASE_REWRITE_TAC[REVERSE; APPEND] THEN
  REWRITE_TAC[CLOSP2AUX_op_do_app; clos_do_int_app_def; CLOSP2AUX_op_do_eq_Number] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_MakeInt; evaluate_MakeBool; INT_GT; INT_GE] THEN
  ASM_REWRITE_TAC[] THEN TRY(CASE_REWRITE_TAC[]) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN REWRITE_TAC[]);;

let CLOSP2AUX_op_eval_nil = prove
 (`!env (s:(C,FFI)clos_state). clos_evaluate ([],env,s) = (Rval [],s)`,
  REWRITE_TAC[clos_evaluate_def]);;

let CLOSP2AUX_op_LENGTH2 = prove
 (`!l:A list. LENGTH l = 2 <=> ?a b. l = [a; b]`,
  GEN_TAC THEN REWRITE_TAC[TWO; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let CLOSP2AUX_op_smart_eq_any = prove
 (`!x y z t env (s:(C,FFI)clos_state) res s1.
     eq_any x y = SOME z /\
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_any_def] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps [x; y] 0 []`
    `ys:clos_exp list` `k:num` `binds:clos_exp list` THEN
  FIRST_ASSUM(MP_TAC o SYM o MATCH_MP lift_exps_length) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`; CLOSP2AUX_op_LENGTH2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:clos_exp` (X_CHOOSE_THEN `y1:clos_exp` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ALL] o MATCH_MP lift_exps_simple_exp) THEN
  MP_TAC(ISPEC `clos_evaluate ([x; y],env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`[x; y]:clos_exp list`; `0`; `[]:clos_exp list`; `env:clos_v list`;
                 `s:(C,FFI)clos_state`; `[x1; y1]:clos_exp list`; `k:num`; `[]:clos_v list`;
                 `binds:clos_exp list`; `s:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `q:(clos_v list,clos_v)result`] lift_exps_thm) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_op_eval_nil; LENGTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:(clos_v list,clos_v)result` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[CLOSP2AUX_op_eval_Let] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res:(clos_v list,clos_v)result, s1:(C,FFI)clos_state)`)) THEN
  SIMP_TAC[CLOSP2AUX_op_eval_Op; CLOSP2AUX_op_not_install] THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `bv:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(clos_v)error_result` SUBST_ALL_TAC)
    (ISPEC `r4:(clos_v list,clos_v)result` (cases "result")) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`env:clos_v list`; `s2:(C,FFI)clos_state`; `bv:clos_v list`] o
      check (fun th -> length (fst (strip_forall (concl th))) = 3)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `vs:clos_v list` STRIP_ASSUME_TAC) THEN
    RVEQ_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o
      check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `clos_evaluate ([x1; y1],APPEND bv env,s2:(C,FFI)clos_state)`)) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`] THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[CLOSP2AUX_op_LENGTH2] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:clos_v` (X_CHOOSE_THEN `w2:clos_v` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[REVERSE; APPEND; CLOSP2AUX_op_do_app] THEN
    MP_TAC(ISPEC `clos_do_eq w2 w1` (cases "eq_result")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN
    MATCH_MP_TAC (INST [`w1:clos_v`,`h1:clos_v`; `w2:clos_v`,`h2:clos_v`] eq_pure_thm) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 clos_do_eq_sym] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `e:(clos_v)error_result` o
      check (fun th -> length (fst (strip_forall (concl th))) = 1)) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN CASE_REWRITE_TAC[]]);;

let CLOSP2AUX_op_smart_eq = prove
 (`!x y z t env (s:(C,FFI)clos_state) res s1.
     eq_op x y = SOME z /\
     clos_evaluate ([clos_Op t (BlockOp clos_Equal) [x; y]],env,s) = (res,s1) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     clos_evaluate ([z],env,s) = (res,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_op_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  CASES_ON `eq_direct x y` THEN CASE_REWRITE_TAC[] THENL
   [MESON_TAC[CLOSP2AUX_op_smart_eq_any];
    REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MATCH_MP_TAC eq_direct_thm THEN
    MAP_EVERY EXISTS_TAC [`x:clos_exp`; `y:clos_exp`; `t:tra`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4: SmartOp_thm *)
let clos_opProof_SmartOp_thm = prove
 (`clos_evaluate ([clos_Op t op xs],env,s) = (res,s1) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
   clos_evaluate ([clos_op_SmartOp t op xs],env,s) = (res,s1:(C,FFI)clos_state)`,
  REWRITE_TAC[clos_op_SmartOp_def] THEN
  MP_TAC(ISPEC `SmartOp' (t:tra) op xs` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN
                                         MESON_TAC[])
                              (X_CHOOSE_THEN `z:clos_exp` (fun th -> REWRITE_TAC[th] THEN
                                 MP_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN REWRITE_TAC[SmartOp'_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THEN CONJ_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                (X_CHOOSE_THEN `p:num#clos_exp list` ASSUME_TAC)) THEN
    CASE_REWRITE_TAC[distinctness "option"] THEN
    MP_TAC(ISPEC `p:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm]) THEN
    RVEQ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_smart_cons THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `dest_Op_Consts x y` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                (X_CHOOSE_THEN `p:int#int` ASSUME_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN RVEQ_TAC THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_smart_eq THEN ASM_MESON_TAC[];
      MP_TAC(ISPEC `p:int#int` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `j:int` SUBST_ALL_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_smart_int THEN ASM_MESON_TAC[]]]);;

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

(* HOL4: red_rel_nil *)
let red_rel_nil = prove
 (`!ys. red_rel [] ys <=> ys = []`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [red_rel_cases] THEN
  REWRITE_TAC[NOT_NIL_CONS; distinctness "list"] THEN MESON_TAC[]);;

(* local helpers: red_rel of lists of two or more expressions, the rules If *)
(* and multi with empty results, and the rule Op                            *)
let CLOSP2AUX_op_red_rel_cons2 = prove
 (`!x y zs ys. red_rel (CONS x (CONS y zs)) ys <=>
     ?x1 x2. red_rel [x] x1 /\ red_rel (CONS y zs) x2 /\ ys = APPEND x1 x2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [red_rel_cases] THEN
  REWRITE_TAC[CONS_11; NOT_CONS_NIL; distinctness "list"] THEN MESON_TAC[]);;

let CLOSP2AUX_op_red_If_nil = prove
 (`!x y z t. red_rel [x] [] /\ red_rel [y] [] /\ red_rel [z] [] ==>
             red_rel [clos_If t x y z] []`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:clos_exp`; `y:clos_exp`; `z:clos_exp`; `[]:clos_exp list`;
                `[]:clos_exp list`; `[]:clos_exp list`; `t:tra`]
    (el 6 (CONJUNCTS red_rel_rules))) THEN
  ASM_REWRITE_TAC[APPEND]);;

let CLOSP2AUX_op_red_multi_nil = prove
 (`!x y zs. red_rel [x] [] /\ red_rel (CONS y zs) [] ==> red_rel (CONS x (CONS y zs)) []`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:clos_exp`; `y:clos_exp`; `zs:clos_exp list`; `[]:clos_exp list`;
                `[]:clos_exp list`] red_rel_multi) THEN
  ASM_REWRITE_TAC[APPEND]);;

let CLOSP2AUX_OP_RED_OP_TAC (thl:thm list) : tactic =
  MATCH_MP_TAC red_rel_Op THEN REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC(red_rel_rules :: thl);;

(* HOL4: red_rel_ConjList *)
let red_rel_ConjList = prove
 (`!xs. red_rel xs [] ==> red_rel [ConjList xs] []`,
  MATCH_MP_TAC ConjList_ind THEN REWRITE_TAC[ConjList_def] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MakeBool_def] THEN CLOSP2AUX_OP_RED_OP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[CLOSP2AUX_op_red_rel_cons2] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_comb (rhs (concl th)))) THEN
    REWRITE_TAC[APPEND_EQ_NIL] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MATCH_MP_TAC CLOSP2AUX_op_red_If_nil THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[MakeBool_def] THEN CLOSP2AUX_OP_RED_OP_TAC[]]);;

(* HOL4: red_rel_EVERY *)
let red_rel_EVERY = prove
 (`!xs. ALL (\h. red_rel [h] []) xs ==> red_rel xs []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; red_rel_rules] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `y:clos_exp` (X_CHOOSE_THEN `zs:clos_exp list` SUBST_ALL_TAC))
    (ISPEC `t:clos_exp list` list_CASES) THEN
  ASM_SIMP_TAC[CLOSP2AUX_op_red_multi_nil]);;

(* HOL4: simple_exp_red_rel *)
let simple_exp_red_rel = prove
 (`!xs. ALL simple_exp xs ==> red_rel xs []`,
  SUBGOAL_THEN `!x. simple_exp x ==> red_rel [x] []` ASSUME_TAC THENL
   [MATCH_MP_TAC simple_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    TRY STRIP_TAC THEN
    TRY (MATCH_ACCEPT_TAC (el 3 (CONJUNCTS red_rel_rules))) THEN
    TRY (MATCH_MP_TAC CLOSP2AUX_op_red_If_nil THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    CLOSP2AUX_OP_RED_OP_TAC[red_rel_EVERY; CLOSP2AUX_op_red_multi_nil];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC red_rel_EVERY THEN
    UNDISCH_TAC `ALL simple_exp xs` THEN MATCH_MP_TAC MONO_ALL THEN ASM_REWRITE_TAC[]]);;

(* HOL4: red_rel_eq_pure *)
let red_rel_eq_pure = prove
 (`simple_exp x /\ simple_exp y ==> red_rel [eq_pure x y] []`,
  STRIP_TAC THEN REWRITE_TAC[eq_pure_def] THEN MATCH_MP_TAC red_rel_ConjList THEN
  MATCH_MP_TAC simple_exp_red_rel THEN MATCH_MP_TAC simple_exp_eq_pure_list THEN
  ASM_REWRITE_TAC[ALL]);;

(* HOL4: IMP_red_rel_cons_0 *)
let IMP_red_rel_cons_0 = prove
 (`red_rel [x] ys /\ red_rel xs zs ==> red_rel (CONS x xs) (APPEND ys zs)`,
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `h:clos_exp` (X_CHOOSE_THEN `t:clos_exp list` SUBST1_TAC))
    (ISPEC `xs:clos_exp list` list_CASES) THEN
  REWRITE_TAC[red_rel_nil] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[APPEND_NIL]; MATCH_ACCEPT_TAC red_rel_multi]);;

(* HOL4: red_rel_exists_append *)
let red_rel_exists_append = prove
 (`red_rel (CONS h xs) ys <=>
   ?ys1 ys2. red_rel [h] ys1 /\ red_rel xs ys2 /\ ys = APPEND ys1 ys2`,
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:clos_exp` (X_CHOOSE_THEN `zs:clos_exp list` SUBST1_TAC))
    (ISPEC `xs:clos_exp list` list_CASES) THEN
  REWRITE_TAC[red_rel_nil; CLOSP2AUX_op_red_rel_cons2] THEN MESON_TAC[APPEND_NIL]);;

(* HOL4: IMP_red_rel_append *)
let IMP_red_rel_append = prove
 (`!xs ys xs1 ys1.
     red_rel xs ys /\ red_rel xs1 ys1 ==> red_rel (APPEND xs xs1) (APPEND ys ys1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[red_rel_nil; APPEND] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[APPEND];
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[red_rel_exists_append] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a1:clos_exp list`
      (X_CHOOSE_THEN `a2:clos_exp list` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`a1:clos_exp list`; `APPEND a2 ys1:clos_exp list`] THEN
    ASM_REWRITE_TAC[APPEND_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4: IMP_red_rel_cons *)
let IMP_red_rel_cons = prove
 (`red_rel [x] [] /\ red_rel xs ys ==> red_rel (CONS x xs) ys`,
  STRIP_TAC THEN ONCE_REWRITE_TAC[red_rel_exists_append] THEN
  MAP_EVERY EXISTS_TAC [`[]:clos_exp list`; `ys:clos_exp list`] THEN
  ASM_REWRITE_TAC[APPEND]);;

(* HOL4: IMP_red_rel_cons_1 *)
let IMP_red_rel_cons_1 = prove
 (`red_rel xs ys ==> red_rel (CONS x xs) (CONS x ys)`,
  ONCE_REWRITE_TAC[red_rel_exists_append] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`[x:clos_exp]`; `ys:clos_exp list`] THEN
  ASM_REWRITE_TAC[red_rel_rules; APPEND]);;

(* HOL4: lift_exps_red_rel *)
let lift_exps_red_rel = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) ==>
     ?zs. red_rel xs zs /\ red_rel (DROP (LENGTH binds) binds2) zs`,
  MATCH_MP_TAC CLOSP2AUX_op_lift_exps_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[lift_exps_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `[]:clos_exp list` THEN REWRITE_TAC[red_rel_nil; DROP_LENGTH_NIL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2")
    (CONJUNCTS_THEN2 (LABEL_TAC "H3") (LABEL_TAC "H4")))) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[lift_exps_def] THEN
  ASM_CASES_TAC `dont_lift x` THEN ASM_REWRITE_TAC[] THENL
   [CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs n binds`
      `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    USE_THEN "H1" (MP_TAC o SPECL [`ys1:clos_exp list`; `k:num`; `binds2:clos_exp list`] o
                   C MATCH_MP (ASSUME `dont_lift x`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zs:clos_exp list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `zs:clos_exp list` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMP_red_rel_cons THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC simple_exp_red_rel THEN ASM_SIMP_TAC[ALL; CLOSP2AUX_op_dont_lift_simple];
    ALL_TAC] THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num#clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs (n + 1) (APPEND binds [x])`
      `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    USE_THEN "H2" (MP_TAC o SPECL [`ys1:clos_exp list`; `k:num`; `binds2:clos_exp list`] o
      C MATCH_MP (CONJ (ASSUME `~dont_lift x`)
                       (ASSUME `dest_Op clos_op_dest_Cons x = NONE`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zs:clos_exp list` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `b:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc) THEN
    EXISTS_TAC `CONS (x:clos_exp) zs` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DROP_LENGTH_APPEND]) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; DROP_LENGTH_APPEND] THEN
    CONJ_TAC THEN MATCH_MP_TAC IMP_red_rel_cons_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:num#clos_exp list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:num` (X_CHOOSE_THEN `ys0:clos_exp list` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps ys0 n binds`
    `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs n1 binds1`
    `xs1:clos_exp list` `n2:num` `binds3:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "H4" (MP_TAC o SPECL [`ys1:clos_exp list`; `n1:num`; `binds1:clos_exp list`] o
    C MATCH_MP (ASSUME `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zs1:clos_exp list` STRIP_ASSUME_TAC) THEN
  USE_THEN "H3" (MP_TAC o SPECL [`xs1:clos_exp list`; `k:num`; `binds2:clos_exp list`] o
    C MATCH_MP (end_itlist CONJ [ASSUME `~dont_lift x`;
                           ASSUME `dest_Op clos_op_dest_Cons x = SOME (t0,ys0)`;
                           ASSUME `lift_exps ys0 n binds = (ys1,n1,binds1)`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zs2:clos_exp list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b1:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc o
    check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `lift_exps ys0`)) (lhs (concl th)))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b3:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc o
    check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `lift_exps xs`)) (lhs (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DROP_LENGTH_APPEND]) THEN
  EXISTS_TAC `APPEND zs1 zs2:clos_exp list` THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; DROP_LENGTH_APPEND] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMP_red_rel_cons_0 THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o
      check (fun th -> is_conj (concl th) && is_neg (lhand (concl th)))) THEN
    RVEQ_TAC THEN CLOSP2AUX_OP_RED_OP_TAC[];
    MATCH_MP_TAC IMP_red_rel_append THEN ASM_REWRITE_TAC[]]);;

(* local helpers for eq_direct_red_rel: constants reduce to nothing *)
let CLOSP2AUX_op_red_const = prove
 (`(!t i. red_rel [clos_Op t (IntOp (clos_Const i)) []] []) /\
   (!t s. red_rel [clos_Op t (BlockOp (Constant (ConstStr s))) []] []) /\
   (!t i. red_rel [clos_Op t (BlockOp (Constant (ConstInt i))) []] []) /\
   (!t w. red_rel [clos_Op t (BlockOp (Constant (ConstWord64 w))) []] []) /\
   (!t n. red_rel [clos_Op t (BlockOp (clos_Cons n)) []] [])`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CLOSP2AUX_OP_RED_OP_TAC[]);;

(* the witness of red_rel [x; y] ys /\ red_rel [z] ys: [] when z is a     *)
(* constant, [e] when z tests the argument e                                *)
let CLOSP2AUX_OP_RED_DIRECT_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let z = hd (dest_list (lhand (rand bod))) in
  let xy = dest_list (lhand (lhand bod)) in
  let a = el 0 xy and b = el 1 xy in
  let nil = `[]:clos_exp list` in
  let wit,w1,w2 =
    (match snd (strip_comb z) with
       [_;_;l] when is_list l && length (dest_list l) = 1 ->
         let e = hd (dest_list l) in
         if e = a then l,l,nil else l,nil,mk_list([b],`:clos_exp`)
     | _ -> nil,nil,nil) in
  (EXISTS_TAC wit THEN CONJ_TAC THENL
    [ONCE_REWRITE_TAC[red_rel_exists_append] THEN MAP_EVERY EXISTS_TAC [w1; w2] THEN
     REWRITE_TAC[APPEND; APPEND_NIL; red_rel_rules; red_rel_nil; CLOSP2AUX_op_red_const];
     REWRITE_TAC[MakeBool_def] THEN CLOSP2AUX_OP_RED_OP_TAC[]]) g;;

let CLOSP2AUX_op_red_direct = prove
 (`(eq_direct_const x y = SOME z ==> ?ys. red_rel [x; y] ys /\ red_rel [z] ys) /\
   (eq_direct_constant x y = SOME z ==> ?ys. red_rel [x; y] ys /\ red_rel [z] ys) /\
   (eq_direct_nil x y = SOME z ==> ?ys. red_rel [x; y] ys /\ red_rel [z] ys)`,
  REWRITE_TAC[eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def] THEN
  REPEAT CONJ_TAC THENL
   [CASES_ON `dest_Op_Nil dest_Const x` THEN CASES_ON `dest_Op_Nil dest_Const y`;
    CASES_ON `dest_Op_Nil clos_op_dest_Constant x` THEN
    CASES_ON `dest_Op_Nil clos_op_dest_Constant y`;
    CASES_ON `dest_Op_Nil clos_op_dest_Cons x` THEN
    CASES_ON `dest_Op_Nil clos_op_dest_Cons y`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_Op_Nil_thm; dest_Constant_thm; dest_Const_thm;
                              dest_Cons_thm]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) || is_disj (concl th)
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  STRIP_TAC THEN RVEQ_TAC THEN CLOSP2AUX_OP_RED_DIRECT_TAC);;

(* HOL4: eq_direct_red_rel *)
let eq_direct_red_rel = prove
 (`eq_direct x y = SOME z ==> ?ys. red_rel [x; y] ys /\ red_rel [z] ys`,
  MP_TAC CLOSP2AUX_op_red_direct THEN REWRITE_TAC[eq_direct_def] THEN
  CASES_ON `eq_direct_const x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  CASES_ON `eq_direct_constant x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  MESON_TAC[]);;

(* HOL4: red_rel_refl *)
let red_rel_refl = prove
 (`!xs. red_rel xs xs`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[red_rel_nil; IMP_red_rel_cons_1]);;

(* local helpers for red_rel_exists: the cases of SmartOp' *)
let CLOSP2AUX_op_red_Cons = prove
 (`!tra t1 xs1. red_rel [clos_Op tra (BlockOp (clos_Cons t1)) xs1] xs1`,
  REPEAT GEN_TAC THEN CLOSP2AUX_OP_RED_OP_TAC[red_rel_refl]);;

let CLOSP2AUX_op_red_cons_op = prove
 (`!op t1 xs1 z t tra. cons_op op t1 xs1 = SOME z ==>
     ?ys. red_rel [clos_Op t op [clos_Op tra (BlockOp (clos_Cons t1)) xs1]] ys /\
          red_rel [z] ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cons_op_def] THEN
  MP_TAC(ISPEC `dest_ElemAt op` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `dest_TagLenEq op` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num#num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `dest_TagEq op` (cases "option")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
       [MP_TAC(ISPEC `dest_LenEq op` (cases "option")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[distinctness "option"];
        ALL_TAC];
      ALL_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_op_dest_ops]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN TRY(COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  (EXISTS_TAC `xs1:clos_exp list` THEN CONJ_TAC THENL
    [CLOSP2AUX_OP_RED_OP_TAC[CLOSP2AUX_op_red_Cons];
     MATCH_MP_TAC red_rel_Let THEN REWRITE_TAC[red_rel_refl; red_rel_rules; MakeBool_def] THEN
     REWRITE_TAC[CLOSP2AUX_op_red_const]]));;

let CLOSP2AUX_op_red_Op2 = prove
 (`!xs ys t op.
     red_rel xs ys /\
     (?iop i tag t1 t2 s w n.
        MEM op [IntOp iop;
                BlockOp clos_Equal; BlockOp (clos_Cons tag); BlockOp (ElemAt t1);
                BlockOp (clos_TagLenEq t1 t2); BlockOp (clos_LenEq n); BlockOp (TagEq tag);
                BlockOp (EqualConst (clos_Str s));
                BlockOp (EqualConst (clos_W64 w));
                BlockOp (EqualConst (clos_Int i));
                BlockOp (Constant (ConstInt i));
                BlockOp (Constant (ConstStr s));
                BlockOp (Constant (ConstWord64 w))]) ==>
     red_rel [clos_Op t op xs] ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC red_rel_Op THEN
  MAP_EVERY EXISTS_TAC [`iop:int_op`; `i:int`; `tag:num`; `t1:num`; `t2:num`;
                        `s:mlstring`; `w:int64`; `n:num`] THEN
  ASM_REWRITE_TAC[]);;

let CLOSP2AUX_op_red_int_op = prove
 (`!op x y i j z t. dest_Op_Consts x y = SOME (i,j) /\ clos_op_int_op op i j = SOME z ==>
     ?ys. red_rel [clos_Op t op [x; y]] ys /\ red_rel [z] ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSP2AUX_op_dest_Op_Consts; clos_op_int_op_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:clos_exp list` THEN
  POP_ASSUM MP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"; distinctness "option"]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN RVEQ_TAC THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC CLOSP2AUX_op_red_Op2 THEN CONJ_TAC THENL
      [MATCH_MP_TAC CLOSP2AUX_op_red_multi_nil THEN REWRITE_TAC[CLOSP2AUX_op_red_const];
       REWRITE_TAC[MEM] THEN MESON_TAC[]];
     REWRITE_TAC[MakeInt_def; MakeBool_def; CLOSP2AUX_op_red_const]]));;

let CLOSP2AUX_op_red_eq_op = prove
 (`!x y z t. eq_op x y = SOME z ==>
     ?ys. red_rel [clos_Op t (BlockOp clos_Equal) [x; y]] ys /\ red_rel [z] ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_op_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  CASES_ON `eq_direct x y` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[eq_any_def] THEN
    CLOSP2AUX_OP_PAIR3_TAC `lift_exps [x; y] 0 []`
      `ys:clos_exp list` `k:num` `binds:clos_exp list` THEN
    FIRST_ASSUM(MP_TAC o SYM o MATCH_MP lift_exps_length) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`; CLOSP2AUX_op_LENGTH2] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:clos_exp` (X_CHOOSE_THEN `y1:clos_exp` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ALL] o MATCH_MP lift_exps_simple_exp) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `zs:clos_exp list` STRIP_ASSUME_TAC o
      REWRITE_RULE[LENGTH; DROP] o MATCH_MP lift_exps_red_rel) THEN
    EXISTS_TAC `zs:clos_exp list` THEN CONJ_TAC THENL
     [CLOSP2AUX_OP_RED_OP_TAC[];
      MATCH_MP_TAC red_rel_Let THEN ASM_SIMP_TAC[red_rel_eq_pure]];
    REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `zs:clos_exp list` STRIP_ASSUME_TAC o
      MATCH_MP eq_direct_red_rel) THEN
    EXISTS_TAC `zs:clos_exp list` THEN ASM_REWRITE_TAC[] THEN CLOSP2AUX_OP_RED_OP_TAC[]]);;

(* HOL4: red_rel_exists *)
let red_rel_exists = prove
 (`!t op xs. ?ys. red_rel [clos_Op t op xs] ys /\ red_rel [clos_op_SmartOp t op xs] ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_op_SmartOp_def] THEN
  MP_TAC(ISPEC `SmartOp' (t:tra) op xs` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN
                                         MESON_TAC[red_rel_refl])
                              (X_CHOOSE_THEN `z:clos_exp` (fun th -> REWRITE_TAC[th] THEN
                                 MP_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN REWRITE_TAC[SmartOp'_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THEN CONJ_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                (X_CHOOSE_THEN `p:num#clos_exp list` ASSUME_TAC)) THEN
    CASE_REWRITE_TAC[distinctness "option"] THEN
    MP_TAC(ISPEC `p:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm]) THEN
    RVEQ_TAC THEN REWRITE_TAC[CLOSP2AUX_op_red_cons_op];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `dest_Op_Consts x y` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                (X_CHOOSE_THEN `p:int#int` ASSUME_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN RVEQ_TAC THEN
      REWRITE_TAC[CLOSP2AUX_op_red_eq_op];
      MP_TAC(ISPEC `p:int#int` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `j:int` SUBST_ALL_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC CLOSP2AUX_op_red_int_op THEN
      MAP_EVERY EXISTS_TAC [`i:int`; `j:int`] THEN ASM_REWRITE_TAC[]]]);;

(* the operations of the rule Op of red_rel *)
let CLOSP2AUX_OP_RED_MEM_TAC (thl:thm list) : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    try fst(dest_const t) = "MEM" with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[MEM] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC thl THEN CASE_REWRITE_TAC thl;;

(* HOL4: red_rel_pure *)
let red_rel_pure = prove
 (`!xs ys. red_rel xs ys ==> (ALL pure xs <=> ALL pure ys)`,
  MATCH_MP_TAC red_rel_ind THEN REWRITE_TAC[ALL; ALL_APPEND; pure_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(CLOSP2AUX_OP_RED_MEM_TAC[clos_pure_op_def] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALL_APPEND]) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* HOL4: red_rel_elist_globals *)
let red_rel_elist_globals = prove
 (`!xs ys. red_rel xs ys ==> clos_elist_globals xs = clos_elist_globals ys`,
  MATCH_MP_TAC red_rel_ind THEN
  REWRITE_TAC[clos_set_globals_def; clos_elist_globals_append; BAG_UNION_EMPTY] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(CLOSP2AUX_OP_RED_MEM_TAC[clos_op_gbag_def; BAG_UNION_EMPTY] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_set_globals_def; clos_elist_globals_append;
                              BAG_UNION_EMPTY]) THEN
  ASM_REWRITE_TAC[BAG_UNION_EMPTY; ASSOC_BAG_UNION]);;

(* HOL4: red_rel_esgc_free *)
let red_rel_esgc_free = prove
 (`!xs ys. red_rel xs ys ==> (ALL clos_esgc_free xs <=> ALL clos_esgc_free ys)`,
  MATCH_MP_TAC red_rel_ind THEN REWRITE_TAC[ALL; ALL_APPEND; clos_esgc_free_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALL_APPEND]) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* HOL4: SmartOp_simp *)
let SmartOp_simp = prove
 (`(pure (clos_op_SmartOp t op xs) <=> pure (clos_Op t op xs)) /\
   clos_set_globals (clos_op_SmartOp t op xs) = clos_set_globals (clos_Op t op xs) /\
   (clos_esgc_free (clos_op_SmartOp t op xs) <=> clos_esgc_free (clos_Op t op xs))`,
  X_CHOOSE_THEN `ys:clos_exp list` (CONJUNCTS_THEN ASSUME_TAC)
    (SPECL [`t:tra`; `op:clos_op`; `xs:clos_exp list`] red_rel_exists) THEN
  REPEAT CONJ_TAC THEN
  MAP_EVERY (fun th -> MAP_EVERY (fun tm -> MP_TAC(MATCH_MP th (ASSUME tm)))
               [`red_rel [clos_Op t op xs] ys`; `red_rel [clos_op_SmartOp t op xs] ys`])
    [red_rel_pure; red_rel_elist_globals; red_rel_esgc_free] THEN
  REWRITE_TAC[ALL; clos_set_globals_def; BAG_UNION_EMPTY] THEN MESON_TAC[]);;

(* local helpers: SmartOp leaves an operation alone when cons_op, int_op and *)
(* eq_op do not apply to it                                                  *)
let CLOSP2AUX_op_SmartOp1_NONE = prove
 (`!op tra xs. (!t xs. cons_op op t xs = NONE) /\ (!i j. clos_op_int_op op i j = NONE) /\
               ~(op = BlockOp clos_Equal) ==> SmartOp' (tra:tra) op xs = NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN REWRITE_TAC[SmartOp'_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [CASES_ON `dest_Op clos_op_dest_Cons x` THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a:num#clos_exp list` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    CASES_ON `dest_Op_Consts x y` THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a:int#int` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let CLOSP2AUX_OP_SMART_NONE_TAC : tactic =
  REWRITE_TAC[clos_op_SmartOp_def] THEN REPEAT GEN_TAC THEN
  W(fun (asl,w) ->
    let tm = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "SmartOp'"
                                 with Failure _ -> false) w in
    SUBGOAL_THEN (mk_eq(tm, `NONE:clos_exp option`)) SUBST1_TAC) THENL
   [MATCH_MP_TAC CLOSP2AUX_op_SmartOp1_NONE THEN
    REWRITE_TAC[cons_op_def; dest_ElemAt_def; dest_TagLenEq_def; dest_TagEq_def;
                dest_LenEq_def; clos_op_int_op_def; distinctness "clos_op";
                injectivity "clos_op"; distinctness "int_op"; distinctness "block_op"] THEN
    CASE_REWRITE_TAC[];
    CASE_REWRITE_TAC[]];;

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

(* the induction on red_rel for the properties of SmartOp below, and the   *)
(* use of the result on red_rel_exists                                      *)
let CLOSP2AUX_OP_RED_IND_TAC (thl:thm list) : tactic =
  MATCH_MP_TAC red_rel_ind THEN REWRITE_TAC thl THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(CLOSP2AUX_OP_RED_MEM_TAC(distinctness "clos_op" :: thl) THEN NO_TAC) THEN
  ASM_REWRITE_TAC thl THEN RULE_ASSUM_TAC(REWRITE_RULE thl) THEN ASM_REWRITE_TAC thl THEN
  TRY(CONV_TAC TAUT);;

let CLOSP2AUX_OP_SMART_FROM_RED_TAC (thl:thm list) (th:thm) : tactic =
  X_CHOOSE_THEN `ys:clos_exp list` (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP th))
    (SPECL [`t:tra`; `op:clos_op`; `xs:clos_exp list`] red_rel_exists) THEN
  RULE_ASSUM_TAC(REWRITE_RULE thl) THEN ASM_REWRITE_TAC thl;;

(* HOL4: code_locs_SmartOp *)
let code_locs_SmartOp = prove
 (`LIST_TO_BAG (code_locs [clos_op_SmartOp t op xs]) =
   LIST_TO_BAG (code_locs [clos_Op t op xs])`,
  SUBGOAL_THEN `!xs ys. red_rel xs ys ==>
                  LIST_TO_BAG (code_locs xs) = LIST_TO_BAG (code_locs ys)`
    (CLOSP2AUX_OP_SMART_FROM_RED_TAC[code_locs_def]) THEN
  CLOSP2AUX_OP_RED_IND_TAC[code_locs_def; LET_DEF; LET_END_DEF; code_locs_append;
                           LIST_TO_BAG_APPEND; LIST_TO_BAG_def; BAG_UNION_EMPTY]);;

(* HOL4: every_Fn_SOME_SmartOp *)
let every_Fn_SOME_SmartOp = prove
 (`every_Fn_SOME [clos_op_SmartOp t op xs] <=> every_Fn_SOME [clos_Op t op xs]`,
  SUBGOAL_THEN `!xs ys. red_rel xs ys ==> (every_Fn_SOME xs <=> every_Fn_SOME ys)`
    (CLOSP2AUX_OP_SMART_FROM_RED_TAC[every_Fn_SOME_def]) THEN
  CLOSP2AUX_OP_RED_IND_TAC[every_Fn_SOME_def; every_Fn_SOME_APPEND]);;

(* HOL4: every_Fn_vs_NONE_SmartOp *)
let every_Fn_vs_NONE_SmartOp = prove
 (`every_Fn_vs_NONE xs ==> every_Fn_vs_NONE [clos_op_SmartOp t op xs]`,
  SUBGOAL_THEN `!xs ys. red_rel xs ys ==> (every_Fn_vs_NONE xs <=> every_Fn_vs_NONE ys)`
    (CLOSP2AUX_OP_SMART_FROM_RED_TAC[every_Fn_vs_NONE_def]) THEN
  CLOSP2AUX_OP_RED_IND_TAC[every_Fn_vs_NONE_def; every_Fn_vs_NONE_APPEND]);;

(* HOL4: no_Labels_SmartOp *)
let no_Labels_SmartOp = prove
 (`no_Labels (clos_op_SmartOp t op xs) <=> no_Labels (clos_Op t op xs)`,
  SUBGOAL_THEN `!xs ys. red_rel xs ys ==> (ALL no_Labels xs <=> ALL no_Labels ys)`
    (CLOSP2AUX_OP_SMART_FROM_RED_TAC[ALL]) THEN
  CLOSP2AUX_OP_RED_IND_TAC[no_Labels_def; ALL; ALL_APPEND]);;

(* HOL4: obeys_max_app_SmartOp *)
let obeys_max_app_SmartOp = prove
 (`ALL (obeys_max_app k) xs ==> obeys_max_app k (clos_op_SmartOp t op xs)`,
  SUBGOAL_THEN `!xs ys. red_rel xs ys ==>
                  (ALL (obeys_max_app k) xs <=> ALL (obeys_max_app k) ys)`
    (CLOSP2AUX_OP_SMART_FROM_RED_TAC[ALL; obeys_max_app_def]) THEN
  CLOSP2AUX_OP_RED_IND_TAC[obeys_max_app_def; ALL; ALL_APPEND]);;

let CLOSP2AUX_op_dont_lift_fv = prove
 (`!x l. dont_lift x ==> ~fv1 l x`,
  REWRITE_TAC[dont_lift_thm] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[fv1_def; fv_def]);;

(* HOL4: lift_exps_fv *)
let lift_exps_fv = prove
 (`!xs n binds ys k binds2.
     lift_exps xs n binds = (ys,k,binds2) /\ n = LENGTH binds ==>
     k = LENGTH binds2 /\
     (!l. fv l binds2 ==> fv l xs \/ fv l binds) /\
     (!l. fv l ys ==> l < k)`,
  MATCH_MP_TAC CLOSP2AUX_op_lift_exps_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[lift_exps_def; PAIR_EQ; fv_def] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fv_def]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2")
    (CONJUNCTS_THEN2 (LABEL_TAC "H3") (LABEL_TAC "H4")))) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[lift_exps_def] THEN
  ASM_CASES_TAC `dont_lift x` THEN ASM_REWRITE_TAC[] THENL
   [CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs n binds`
      `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    USE_THEN "H1" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `lift_exps xs (LENGTH (binds:clos_exp list)) binds = (ys1,k,binds2)`)
      (REFL `LENGTH (binds:clos_exp list)`)) o
      SPECL [`ys1:clos_exp list`; `k:num`; `binds2:clos_exp list`] o
      C MATCH_MP (ASSUME `dont_lift x`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[fv_cons] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP2AUX_op_dont_lift_fv) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num#clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs (n + 1) (APPEND binds [x])`
      `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `LENGTH (binds:clos_exp list) + 1 = LENGTH (APPEND binds [x:clos_exp])`
      ASSUME_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "H2" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `lift_exps xs (LENGTH (binds:clos_exp list) + 1) (APPEND binds [x]) =
               (ys1,k,binds2)`)
      (ASSUME `LENGTH (binds:clos_exp list) + 1 = LENGTH (APPEND binds [x:clos_exp])`)) o
      SPECL [`ys1:clos_exp list`; `k:num`; `binds2:clos_exp list`] o
      C MATCH_MP (CONJ (ASSUME `~dont_lift x`)
                       (ASSUME `dest_Op clos_op_dest_Cons x = NONE`))) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `b:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc o
      check (fun th -> is_eq (concl th) &&
        can (find_term ((=) `lift_exps xs`)) (lhs (concl th)))) THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THENL
     [DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[fv_append; fv_cons; fv_def] THEN CONV_TAC TAUT;
      REWRITE_TAC[fv_cons; fv1_def; fv_def] THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
        FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:num#clos_exp list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:num` (X_CHOOSE_THEN `ys0:clos_exp list` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps ys0 n binds`
    `ys1:clos_exp list` `n1:num` `binds1:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_OP_PAIR3_TAC `lift_exps xs n1 binds1`
    `xs1:clos_exp list` `n2:num` `binds3:clos_exp list` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "H4" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `lift_exps ys0 (LENGTH (binds:clos_exp list)) binds = (ys1,n1,binds1)`)
      (REFL `LENGTH (binds:clos_exp list)`)) o
    SPECL [`ys1:clos_exp list`; `n1:num`; `binds1:clos_exp list`] o
    C MATCH_MP (ASSUME `~dont_lift x /\ dest_Op clos_op_dest_Cons x = SOME (t0,ys0)`)) THEN
  STRIP_TAC THEN
  USE_THEN "H3" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `lift_exps xs n1 binds1 = (xs1,k,binds2)`)
      (ASSUME `n1 = LENGTH (binds1:clos_exp list)`)) o
    SPECL [`xs1:clos_exp list`; `k:num`; `binds2:clos_exp list`] o
    C MATCH_MP (end_itlist CONJ
      [ASSUME `~dont_lift x`; ASSUME `dest_Op clos_op_dest_Cons x = SOME (t0,ys0)`;
       ASSUME `lift_exps ys0 (LENGTH (binds:clos_exp list)) binds = (ys1,n1,binds1)`])) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[fv_cons] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o
    check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `clos_op_dest_Cons`)) (lhs (concl th)))) THEN
  RVEQ_TAC THEN REWRITE_TAC[fv1_def; fv_def] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b3:clos_exp list` SUBST_ALL_TAC o MATCH_MP lift_exps_acc o
    check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `lift_exps xs`)) (lhs (concl th)))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN REWRITE_TAC[LENGTH_APPEND] THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (K ALL_TAC)) ["H1"; "H2"; "H3"; "H4"] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `fv l (ys1:clos_exp list)`))) THEN
    ARITH_TAC;
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `fv l (xs1:clos_exp list)`))) THEN
    ARITH_TAC]);;

(* HOL4: fv1_ConjList *)
let fv1_ConjList = prove
 (`!xs. fv1 n (ConjList xs) <=> fv n xs`,
  MATCH_MP_TAC ConjList_ind THEN REWRITE_TAC[ConjList_def; fv1_def; fv_def; MakeBool_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* HOL4: fv1_EL *)
let fv1_EL = prove
 (`!xs n k. fv1 n (EL k xs) /\ k < LENGTH xs ==> fv n xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT; fv_cons] THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j:num` SUBST1_TAC) (SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0] THEN ASM_MESON_TAC[]);;

(* local helpers for fv1_eq_pure *)
let CLOSP2AUX_op_fv_REVERSE = prove
 (`!l. fv n (REVERSE l) <=> fv n l`,
  REWRITE_TAC[fv_exists; GSYM EX_MEM; MEM_REVERSE]);;

let CLOSP2AUX_op_fv_EL_REVERSE = prove
 (`!l i. fv1 n (EL i (REVERSE l)) /\ i < LENGTH l ==> fv n l`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CLOSP2AUX_op_fv_REVERSE] THEN
  MATCH_MP_TAC fv1_EL THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[LENGTH_REVERSE]);;

let CLOSP2AUX_op_direct_fv = prove
 (`(eq_direct_const x y = SOME z /\ fv1 n z ==> fv1 n x \/ fv1 n y) /\
   (eq_direct_constant x y = SOME z /\ fv1 n z ==> fv1 n x \/ fv1 n y) /\
   (eq_direct_nil x y = SOME z /\ fv1 n z ==> fv1 n x \/ fv1 n y)`,
  REWRITE_TAC[eq_direct_const_def; eq_direct_constant_def; eq_direct_nil_def] THEN
  REPEAT CONJ_TAC THENL
   [CASES_ON `dest_Op_Nil dest_Const x` THEN CASES_ON `dest_Op_Nil dest_Const y`;
    CASES_ON `dest_Op_Nil clos_op_dest_Constant x` THEN
    CASES_ON `dest_Op_Nil clos_op_dest_Constant y`;
    CASES_ON `dest_Op_Nil clos_op_dest_Cons x` THEN
    CASES_ON `dest_Op_Nil clos_op_dest_Cons y`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fv1_def; fv_def; MakeBool_def]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[fv1_def]);;

let CLOSP2AUX_op_eq_direct_fv = prove
 (`eq_direct x y = SOME z /\ fv1 n z ==> fv1 n x \/ fv1 n y`,
  MP_TAC CLOSP2AUX_op_direct_fv THEN REWRITE_TAC[eq_direct_def] THEN
  CASES_ON `eq_direct_const x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  CASES_ON `eq_direct_constant x y` THEN CASE_REWRITE_TAC[injectivity "option"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_op_fv_eq_pure_list = prove
 (`!xs. fv n (append (eq_pure_list xs)) ==> EX (\(x,y). fv1 n x \/ fv1 n y) xs`,
  MATCH_MP_TAC eq_pure_list_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[eq_pure_list_def; append_thm; fv_nil];
    ALL_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHR") (LABEL_TAC "IHL")) THEN
    ONCE_REWRITE_TAC[CONJUNCT2 (CONJUNCT2 eq_pure_list_def)] THEN
    REWRITE_TAC[append_thm; fv_append] THEN ONCE_REWRITE_TAC[EX] THEN STRIP_TAC THENL
     [USE_THEN "IHL" (MP_TAC o C MATCH_MP (ASSUME
        `fv n (append (eq_pure_list [v3:clos_exp,v4:clos_exp]))`)) THEN
      REWRITE_TAC[EX] THEN CONV_TAC TAUT;
      USE_THEN "IHR" (MP_TAC o C MATCH_MP (ASSUME
        `fv n (append (eq_pure_list (CONS (v5:clos_exp#clos_exp) v6)))`)) THEN
      CONV_TAC TAUT]] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1")
    (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))) THEN
  REWRITE_TAC[EX] THEN
  ONCE_REWRITE_TAC[CONJUNCT1 (CONJUNCT2 eq_pure_list_def)] THEN
  CASES_ON `eq_direct x y` THEN CASE_REWRITE_TAC[append_thm] THENL
   [ALL_TAC;
    REWRITE_TAC[fv_cons; fv_nil] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP2AUX_op_eq_direct_fv)) THEN
    CONV_TAC TAUT] THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p1:num#clos_exp list` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `dest_Op clos_op_dest_Cons y` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p2:num#clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[append_thm] THENL
   [REWRITE_TAC[fv_cons; fv_nil; fv1_thm];
    MP_TAC(ISPEC `p2:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `ys2:clos_exp list` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME
        `fv n (append (eq_pure_list [y:clos_exp,x:clos_exp]))`) o
      C MATCH_MP (end_itlist CONJ [REFL `NONE:clos_exp option`;
        ASSUME `dest_Op clos_op_dest_Cons x = NONE`;
        ASSUME `dest_Op clos_op_dest_Cons y = SOME (t2,ys2)`]) o
      SPECL [`t2:num`; `ys2:clos_exp list`]) THEN
    REWRITE_TAC[EX] THEN CONV_TAC TAUT;
    MP_TAC(ISPEC `p1:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[append_thm] THEN REWRITE_TAC[APPEND; fv_cons; fv_nil; fv1_thm] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "H2" (MP_TAC o C MATCH_MP (ASSUME
        `fv n (append (eq_pure_list (MAPi (\i x. x,clos_Op backend_common_None
             (BlockOp (ElemAt i)) [y:clos_exp]) (REVERSE (xs1:clos_exp list)))))`) o
      C MATCH_MP (end_itlist CONJ [REFL `NONE:clos_exp option`;
        ASSUME `dest_Op clos_op_dest_Cons x = SOME (t1,xs1)`;
        ASSUME `dest_Op clos_op_dest_Cons y = NONE`]) o
      SPECL [`t1:num`; `xs1:clos_exp list`]) THEN
    REWRITE_TAC[GSYM EX_MEM; MEM_MAPi; LENGTH_REVERSE] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fv_cons; fv_nil; fv1_thm]) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o
      check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `dest_Op clos_op_dest_Cons x`)) THEN
    RVEQ_TAC THEN REWRITE_TAC[fv1_thm] THEN
    MATCH_MP_TAC CLOSP2AUX_op_fv_EL_REVERSE THEN EXISTS_TAC `n':num` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `p1:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `p2:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `ys2:clos_exp list` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[append_thm; fv_cons; fv_nil; fv1_thm; MakeBool_def]; ALL_TAC] THEN
    DISCH_TAC THEN
    USE_THEN "H3" (MP_TAC o C MATCH_MP (ASSUME
        `fv n (append (eq_pure_list (ZIP (REVERSE (xs1:clos_exp list))
                                         (REVERSE (ys2:clos_exp list)))))`) o
      C MATCH_MP (end_itlist CONJ [REFL `NONE:clos_exp option`;
        ASSUME `dest_Op clos_op_dest_Cons x = SOME (t1,xs1)`;
        ASSUME `dest_Op clos_op_dest_Cons y = SOME (t2,ys2)`;
        ASSUME `~(~((t1:num) = t2) \/ ~(LENGTH (xs1:clos_exp list) = LENGTH (ys2:clos_exp list)))`]) o
      SPECL [`t1:num`; `t2:num`; `xs1:clos_exp list`; `ys2:clos_exp list`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[GSYM EX_MEM; MEM_ZIP; LENGTH_REVERSE] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    MAP_EVERY (fun tm -> FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm] o
      check (fun th -> is_eq (concl th) && lhs (concl th) = tm)))
      [`dest_Op clos_op_dest_Cons x`; `dest_Op clos_op_dest_Cons y`] THEN
    RVEQ_TAC THEN REWRITE_TAC[fv1_thm] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th))) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_fv_EL_REVERSE THEN EXISTS_TAC `n':num` THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_fv_EL_REVERSE THEN EXISTS_TAC `n':num` THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4: fv1_eq_pure *)
let fv1_eq_pure = prove
 (`fv1 n (eq_pure x y) ==> fv1 n x \/ fv1 n y`,
  REWRITE_TAC[eq_pure_def; fv1_ConjList] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSP2AUX_op_fv_eq_pure_list) THEN REWRITE_TAC[EX]);;

(* HOL4: eq_op_fv *)
let eq_op_fv = prove
 (`eq_op x y = SOME z ==> fv n [z] ==> fv n [x] \/ fv n [y]`,
  REWRITE_TAC[eq_op_def] THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  CASES_ON `eq_direct x y` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[eq_any_def] THEN
    CLOSP2AUX_OP_PAIR3_TAC `lift_exps [x; y] 0 []`
      `ys:clos_exp list` `k:num` `binds:clos_exp list` THEN
    FIRST_ASSUM(MP_TAC o SYM o MATCH_MP lift_exps_length) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`; CLOSP2AUX_op_LENGTH2] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:clos_exp` (X_CHOOSE_THEN `y1:clos_exp` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP lift_exps_fv o
      (fun th -> CONJ th (prove(`0 = LENGTH ([]:clos_exp list)`, REWRITE_TAC[LENGTH]))) o
      check (fun th -> is_eq (concl th) &&
        can (find_term ((=) `lift_exps`)) (lhs (concl th)))) THEN
    REWRITE_TAC[fv_cons; fv_nil; fv1_thm] THEN
    STRIP_TAC THEN RVEQ_TAC THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP fv1_eq_pure) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n + LENGTH (binds:clos_exp list)` o
        check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `x1:clos_exp`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[fv_cons; fv_nil] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP2AUX_op_eq_direct_fv)) THEN
    CONV_TAC TAUT]);;

(* local helpers for fv1_SmartOp *)
let CLOSP2AUX_op_fv_cons_op = prove
 (`!op t1 xs1 z. cons_op op t1 xs1 = SOME z /\ fv1 n z ==> fv n xs1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cons_op_def] THEN
  MP_TAC(ISPEC `dest_ElemAt op` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `dest_TagLenEq op` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num#num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `dest_TagEq op` (cases "option")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:num` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
       [MP_TAC(ISPEC `dest_LenEq op` (cases "option")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:num` ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[distinctness "option"];
        ALL_TAC];
      MP_TAC(ISPEC `p:num#num` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRY(COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[fv1_thm; fv_cons; fv_nil; MakeBool_def] THEN
  TRY(DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
  REWRITE_TAC[]);;

let CLOSP2AUX_op_fv_int_op = prove
 (`!op i j z. clos_op_int_op op i j = SOME z ==> ~fv1 n z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_op_int_op_def] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; distinctness "option"]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MakeInt_def; MakeBool_def; fv1_thm; fv_nil]);;

(* HOL4: fv1_SmartOp *)
let fv1_SmartOp = prove
 (`fv1 n (clos_op_SmartOp t op xs) ==> fv1 n (clos_Op t op xs)`,
  REWRITE_TAC[clos_op_SmartOp_def] THEN
  MP_TAC(ISPEC `SmartOp' (t:tra) op xs` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
                              (X_CHOOSE_THEN `z:clos_exp` (fun th -> REWRITE_TAC[th] THEN
                                 MP_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  MATCH_MP_TAC list_split3 THEN REWRITE_TAC[SmartOp'_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THEN CONJ_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `dest_Op clos_op_dest_Cons x` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                (X_CHOOSE_THEN `p:num#clos_exp list` ASSUME_TAC)) THEN
    CASE_REWRITE_TAC[distinctness "option"] THEN
    MP_TAC(ISPEC `p:num#clos_exp list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `xs1:clos_exp list` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dest_Op_thm; dest_Cons_thm]) THEN
    RVEQ_TAC THEN REWRITE_TAC[fv1_thm; fv_cons; fv_nil] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSP2AUX_op_fv_cons_op THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `dest_Op_Consts x y` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                (X_CHOOSE_THEN `p:int#int` ASSUME_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN RVEQ_TAC THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IMP_IMP] o MATCH_MP eq_op_fv) THEN
      ASM_REWRITE_TAC[GSYM fv1_def] THEN REWRITE_TAC[fv1_thm; fv_cons; fv_nil];
      MP_TAC(ISPEC `p:int#int` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `j:int` SUBST_ALL_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[CLOSP2AUX_op_fv_int_op]]]);;
