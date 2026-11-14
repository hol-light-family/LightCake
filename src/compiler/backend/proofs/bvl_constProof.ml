(* ========================================================================= *)
(* bvl_constProof: port of HOL4 compiler/backend/proofs/bvl_constProofScript *)
(* .sml (CakeML v3479).  Correctness proof for bvl_const.                    *)
(* BVLPROPSAUX_ names are local helpers (not HOL4 names).                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;

type_invention_error := true;;

(* HOL4: v_rel (:'c) (:'ffi) and env_rel (:'c) (:'ffi) take the types as  *)
(* arguments: here the arguments are universes (:C) and (:FFI), as for     *)
(* word_shift; the definitions are bvl_constProof_v_rel_DEF and            *)
(* bvl_constProof_env_rel_DEF and the HOL4 statements bvl_constProof_v_rel *)
(* _def and bvl_constProof_env_rel_def.  HOL4 LLOOKUP l n is oEL n l.      *)
let bvl_constProof_v_rel_DEF = cake_def
  `bvl_constProof_v_rel (c:C->bool) (ff:FFI->bool) a (x:bvl_v) y (xs:bvl_v list) ys <=>
     match a with
       bvl_Var n -> oEL n ys = SOME x
     | bvl_Op _ _ ->
         x = y /\ (!(s:(C,FFI)bvl_state) env. bvl_evaluate ([a],env,s) = (Rval [x],s))
     | _ -> F`;;

let bvl_constProof_v_rel_def = prove
 (CASE_TERM
  `!a x y xs ys. bvl_constProof_v_rel (:C) (:FFI) a x y xs ys <=>
     match a with
       bvl_Var n -> oEL n ys = SOME x
     | bvl_Op _ _ ->
         x = y /\ (!(s:(C,FFI)bvl_state) env. bvl_evaluate ([a],env,s) = (Rval [x],s))
     | _ -> F`,
  REWRITE_TAC[bvl_constProof_v_rel_DEF]);;

let bvl_constProof_env_rel_DEF = sem1aux_def
  `(bvl_constProof_env_rel (c:C->bool) (ff:FFI->bool) [] (e1:bvl_v list) e2 <=>
      e1 = e2) /\
   (bvl_constProof_env_rel c ff (CONS NONE rest) (CONS x e1) (CONS y e2) <=>
      x = y /\ bvl_constProof_env_rel c ff rest e1 e2) /\
   (bvl_constProof_env_rel c ff (CONS (SOME a) rest) (CONS x e1) (CONS y e2) <=>
      bvl_constProof_v_rel c ff a x y (CONS x e1) (CONS y e2) /\
      bvl_constProof_env_rel c ff rest e1 e2) /\
   (bvl_constProof_env_rel _ _ _ _ _ <=> F)`;;

let bvl_constProof_env_rel_def = end_itlist CONJ
  (map (SPECL [`(:C)`; `(:FFI)`]) (CONJUNCTS bvl_constProof_env_rel_DEF));;

let bvl_constProof_env_rel_length = prove
 (`!ax env env2. bvl_constProof_env_rel (:C) (:FFI) ax env env2 ==>
                 LENGTH env2 = LENGTH env`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `env:bvl_v list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `env2:bvl_v list` list_CASES) THEN
  REWRITE_TAC[bvl_constProof_env_rel_def; LENGTH; NOT_CONS_NIL; SUC_INJ; CONS_11] THEN
  TRY (MESON_TAC[]) THEN
  STRUCT_CASES_TAC(ISPEC `h:bvl_exp option` (cases "option")) THEN
  REWRITE_TAC[bvl_constProof_env_rel_def] THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)
let bvl_constProof_env_rel_LLOOKUP_NONE = prove
 (`!ax env env2 n.
     bvl_constProof_env_rel (:C) (:FFI) ax env env2 /\
     (oEL n ax = NONE \/ oEL n ax = SOME NONE) ==>
     EL n env2 = EL n env`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `env:bvl_v list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `env2:bvl_v list` list_CASES) THEN
  REWRITE_TAC[bvl_constProof_env_rel_def; NOT_CONS_NIL; CONS_11] THEN
  TRY (MESON_TAC[]) THEN
  STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
  REWRITE_TAC[oEL_def; NOT_SUC; SUC_SUB1; EL; HD; TL; option_INJ; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `h:bvl_exp option` (cases "option")) THEN
  REWRITE_TAC[bvl_constProof_env_rel_def; option_DISTINCT] THEN ASM_MESON_TAC[]);;

(* a local helper: case splits on the free variables of type bvl_exp option *)
let BVLPROPSAUX_OPT_CASES_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> type_of v = `:bvl_exp option`) (frees w) in
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "option"))) vs g;;

(* HOL4 [local] *)
let bvl_constProof_env_rel_LOOKUP_SOME = prove
 (`!env env2 ax x n.
     bvl_constProof_env_rel (:C) (:FFI) ax env env2 /\ oEL n ax = SOME (SOME x) ==>
     bvl_constProof_v_rel (:C) (:FFI) x (EL n env) (EL n env2) (DROP n env)
       (DROP n env2)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `env2:bvl_v list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `ax:(bvl_exp option) list` list_CASES) THEN
  BVLPROPSAUX_OPT_CASES_TAC THEN
  STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
  REWRITE_TAC[bvl_constProof_env_rel_def; NOT_CONS_NIL; oEL_def; option_DISTINCT;
              NOT_SUC; SUC_SUB1; EL; HD; TL; DROP; option_INJ] THEN
  TRY (DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN MESON_TAC[]) THEN
  ASM_MESON_TAC[]);;

let bvl_constProof_evaluate_delete_var_Rerr_SING = prove
 (`!x (s:(C,FFI)bvl_state) r e env2.
     bvl_evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error) ==>
     bvl_evaluate ([bvl_const_delete_var x],env2,s) = (Rerr e,r)`,
  MATCH_MP_TAC bvl_const_delete_var_ind THEN REWRITE_TAC[bvl_const_delete_var_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY (MESON_TAC[]) THEN
  REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN MESON_TAC[]);;

(* a local helper: delete_var keeps the state of a successful evaluation *)
let BVLPROPSAUX_evaluate_delete_var_Rval_SING = prove
 (`!x (s:(C,FFI)bvl_state) v r env2.
     bvl_evaluate ([x],env2,s) = (Rval v,r) ==>
     ?w. bvl_evaluate ([bvl_const_delete_var x],env2,s) = (Rval w,r)`,
  MATCH_MP_TAC bvl_const_delete_var_ind THEN REWRITE_TAC[bvl_const_delete_var_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY (MESON_TAC[]) THEN
  REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[REVERSE; bvl_do_int_app_def] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let bvl_constProof_evaluate_delete_var_Rerr = prove
 (`!xs (s:(C,FFI)bvl_state) r e env2.
     bvl_evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error) ==>
     bvl_evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rerr e,r)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; bvl_evaluate_def; PAIR_EQ; distinctness "result"] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  MP_TAC(ISPEC `bvl_evaluate ([h],env2,s:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result"] THENL
   [MP_TAC(ISPEC `bvl_evaluate (t,env2,s1:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
      (X_CHOOSE_THEN `s2:(C,FFI)bvl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `r2:(bvl_v list,bvl_v)result` THEN
    REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result";
                distinctness "result"] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_evaluate_delete_var_Rval_SING o
                check (fun th -> lhs (concl th) = `bvl_evaluate ([h],env2,s:(C,FFI)bvl_state)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; case_def "result"] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(C,FFI)bvl_state`; `r:(C,FFI)bvl_state`;
                                  `e:(bvl_v)error_result`; `env2:bvl_v list`] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pair_CASE; case_def "result"];
    STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPECL [`h:bvl_exp`; `s:(C,FFI)bvl_state`; `r:(C,FFI)bvl_state`;
                   `e:(bvl_v)error_result`; `env2:bvl_v list`]
                  bvl_constProof_evaluate_delete_var_Rerr_SING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pair_CASE; case_def "result"]]);;

(* local helpers for evaluate_delete_var_Rval: the results of extract *)
let BVLPROPSAUX_extract_SOME = prove
 (`!h (ys:A list) x.
     bvl_const_extract h ys = SOME x <=>
     (?i. h = bvl_Var i /\ x = bvl_Var (i + LENGTH ys + 1)) \/
     (?c xs. h = bvl_Op (IntOp (clos_Const c)) xs /\ x = bvl_Op (IntOp (clos_Const c)) []) \/
     (?tg. h = bvl_Op (BlockOp (clos_Cons tg)) [] /\ x = bvl_Op (BlockOp (clos_Cons tg)) [])`,
  SUBGOAL_THEN
   `!h (ys:A list). !x.
     bvl_const_extract h ys = SOME x <=>
     (?i. h = bvl_Var i /\ x = bvl_Var (i + LENGTH ys + 1)) \/
     (?c xs. h = bvl_Op (IntOp (clos_Const c)) xs /\ x = bvl_Op (IntOp (clos_Const c)) []) \/
     (?tg. h = bvl_Op (BlockOp (clos_Cons tg)) [] /\ x = bvl_Op (BlockOp (clos_Cons tg)) [])`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC (BVLPAUX_case_ind bvl_const_extract_def) THEN
  REWRITE_TAC[bvl_const_extract_def; option_DISTINCT; option_INJ; distinctness "bvl_exp";
              injectivity "bvl_exp"; distinctness "clos_op"; injectivity "clos_op";
              distinctness "int_op"; injectivity "int_op"; distinctness "block_op";
              injectivity "block_op"; NOT_CONS_NIL] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; NULL_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let BVLPROPSAUX_extract_NONE = prove
 (`!h (ys:A list). bvl_const_extract h ys = NONE ==> bvl_const_delete_var h = h`,
  MATCH_MP_TAC bvl_const_delete_var_ind THEN
  REWRITE_TAC[bvl_const_delete_var_def; bvl_const_extract_def; option_DISTINCT]);;

(* local helpers: do_app of an integer operation, and evaluation of a     *)
(* constant                                                                *)
let BVLPROPSAUX_do_app_IntOp = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvl_state).
     bvl_do_app (IntOp op) vs s =
     match bvl_do_int_app op vs with
       SOME res -> Rval (res,s)
     | NONE -> Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `bvl_do_int_app op vs` THEN CASE_REWRITE_TAC[]);;

let BVLPROPSAUX_evaluate_Const = prove
 (`(!c env (s:(C,FFI)bvl_state).
      bvl_evaluate ([bvl_Op (IntOp (clos_Const c)) []],env,s) =
      (Rval [bvl_Number c],s)) /\
   (!c xs env (s:(C,FFI)bvl_state) w s1.
      bvl_evaluate ([bvl_Op (IntOp (clos_Const c)) xs],env,s) = (Rval w,s1) ==>
      w = [bvl_Number c])`,
  CONJ_TAC THENL
   [REWRITE_TAC[bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp] THEN
    CASE_REWRITE_TAC[REVERSE; bvl_do_int_app_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp] THEN
  BVLPROPSAUX_PAIR_RESULT_TAC `bvl_evaluate (xs,env,s:(C,FFI)bvl_state)` "r1" "s2" THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  CASES_ON `bvl_do_int_app (clos_Const c) (REVERSE (a:bvl_v list))` THEN
  REWRITE_TAC[case_def "option"; case_def "result"; pair_CASE; PAIR_EQ;
              injectivity "result"; distinctness "result"] THEN
  FIRST_X_ASSUM(SUBST1_TAC o CONJUNCT2 o MATCH_MP (CONJUNCT1 (SPEC_ALL do_int_app_eq_some))) THEN
  MESON_TAC[]);;

let BVLPROPSAUX_evaluate_Cons_nil = prove
 (`!tg env (s:(C,FFI)bvl_state).
     bvl_evaluate ([bvl_Op (BlockOp (clos_Cons tg)) []],env,s) =
     (Rval [bvl_Block tg []],s)`,
  REWRITE_TAC[bvl_evaluate_def; REVERSE; bvl_do_app_Cons] THEN
  CASE_REWRITE_TAC[REVERSE; bvl_do_app_Cons]);;

(* a local helper: two runs of the same evaluation give the same value *)
let BVLPROPSAUX_SAME_EVAL_TAC (v0:term) : tactic =
  FIRST_X_ASSUM(fun th5 -> let c = concl th5 in
    if is_eq c && free_in v0 c && is_comb (lhs c) then MP_TAC th5 else NO_TAC) THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM);;

(* HOL4 [local] *)
let bvl_constProof_evaluate_delete_var_Rval = prove
 (`!xs env2 (s:(C,FFI)bvl_state) a r ax env.
     bvl_evaluate (xs,env2,s) = (Rval a,r) /\
     bvl_constProof_env_rel (:C) (:FFI) ax env env2 ==>
     ?b. bvl_evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rval b,r) /\
         bvl_constProof_env_rel (:C) (:FFI) (APPEND (bvl_const_extract_list xs) ax)
           (APPEND a env) (APPEND b env2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; bvl_evaluate_def; PAIR_EQ; injectivity "result";
                bvl_const_extract_list_def; APPEND] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:bvl_v list` THEN
    ASM_REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  MP_TAC(ISPEC `bvl_evaluate ([h],env2,s:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result";
              distinctness "result"] THEN
  MP_TAC(ISPEC `bvl_evaluate (t,env2,s1:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r2:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result";
              distinctness "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`env2:bvl_v list`; `s1:(C,FFI)bvl_state`; `a'':bvl_v list`;
     `r:(C,FFI)bvl_state`; `ax:(bvl_exp option) list`; `env:bvl_v list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:bvl_v list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_evaluate_delete_var_Rval_SING o
    check (fun th -> lhs (concl th) = `bvl_evaluate ([h],env2,s:(C,FFI)bvl_state)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w':bvl_v list` ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w0:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
    check (fun th -> lhs (concl th) =
                     `bvl_evaluate ([bvl_const_delete_var h],env2,s:(C,FFI)bvl_state)`)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
    check (fun th -> lhs (concl th) = `bvl_evaluate ([h],env2,s:(C,FFI)bvl_state)`)) THEN
  EXISTS_TAC `CONS (w0:bvl_v) b` THEN
  REWRITE_TAC[MAP] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; HD; bvl_const_extract_list_def; APPEND] THEN
  SUBGOAL_THEN `LENGTH (b:bvl_v list) = LENGTH (t:bvl_exp list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH o
      check (fun th -> lhs (concl th) =
                       `bvl_evaluate (MAP bvl_const_delete_var t,env2,s1:(C,FFI)bvl_state)`)) THEN
    REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:bvl_exp`; `t:bvl_exp list`] BVLPROPSAUX_extract_SOME) THEN
  MP_TAC(ISPECL [`h:bvl_exp`; `t:bvl_exp list`] BVLPROPSAUX_extract_NONE) THEN
  CASES_ON `bvl_const_extract h (t:bvl_exp list)` THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; bvl_constProof_env_rel_def] THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `bvl_evaluate ([h],env2,s:(C,FFI)bvl_state) = (Rval [w],s1)` THEN
    ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `a:bvl_exp`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[bvl_const_delete_var_def]) THEN
  REWRITE_TAC[bvl_constProof_v_rel_def] THEN CASE_REWRITE_TAC[] THENL
   [UNDISCH_TAC `bvl_evaluate ([bvl_Var i],env2,s:(C,FFI)bvl_state) = (Rval [w],s1)` THEN
    REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; CONS_11] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[oEL_def; ARITH_RULE `~(i + n + 1 = 0) /\ (i + n + 1) - 1 = i + n`;
                    oEL_THM; LENGTH_APPEND; EL_APPEND;
                    ARITH_RULE `(i + n < n + m <=> i < m) /\ ~(i + n < n) /\ (i + n) - n = i`];
    BVLPROPSAUX_SAME_EVAL_TAC `w0:bvl_v` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 BVLPROPSAUX_evaluate_Const)) THEN
    REWRITE_TAC[CONS_11] THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[BVLPROPSAUX_evaluate_Const];
    BVLPROPSAUX_SAME_EVAL_TAC `w0:bvl_v` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_evaluate_Cons_nil; PAIR_EQ; injectivity "result";
                                CONS_11]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC o
                  check (fun th -> is_conj (concl th) && free_in `w:bvl_v` (concl th))) THEN
    REWRITE_TAC[BVLPROPSAUX_evaluate_Cons_nil]]);;

let evaluate_EQ_NIL = prove
 (`!xs env (s:(C,FFI)bvl_state) t.
     bvl_evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH) THEN
    REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[bvl_evaluate_def; PAIR_EQ] THEN MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[bvl_evaluate_def]]);;

(* HOL4 [local] *)
let dest_simple_eq = prove
 (`!h y. dest_simple h = SOME y <=> h = bvl_Op (IntOp (clos_Const y)) []`,
  MATCH_MP_TAC dest_simple_ind THEN
  REWRITE_TAC[dest_simple_def; option_DISTINCT; distinctness "bvl_exp";
              injectivity "bvl_exp"; distinctness "clos_op"; injectivity "clos_op";
              distinctness "int_op"; injectivity "int_op"] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[NULL; option_INJ; option_DISTINCT; NOT_CONS_NIL] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let case_op_const_eq = prove
 (`!exp x. case_op_const exp = SOME x <=>
     (?op x1 n2. x = (op,x1,n2) /\
                 exp = bvl_Op op [x1; bvl_Op (IntOp (clos_Const n2)) []])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[case_op_const_pmatch] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; injectivity "bvl_exp"; distinctness "bvl_exp";
              CONS_11; NOT_CONS_NIL; injectivity "clos_op"; distinctness "clos_op";
              injectivity "int_op"; distinctness "int_op"] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A local tactic for the SmartOp theorems: symbolic evaluation of both      *)
(* sides.  The goal is                                                        *)
(*   evaluate ([OLD],env,s) = (res,s2) ==> evaluate ([NEW],env,s) = (res,s2)  *)
(* with the assumption ~(res = Rerr (Rabort Rtype_error)); the evaluation of *)
(* OLD is split into cases (on the evaluations of its unknown subterms and   *)
(* the results of the integer operations), then NEW is evaluated in each.    *)
(* ------------------------------------------------------------------------- *)

let BVLPROPSAUX_SYMEX_RWS =
  [bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp; REVERSE; APPEND; HD; LET_DEF; LET_END_DEF];;

(* evaluations of one expression give one value *)
let BVLPROPSAUX_SING_TAC : tactic =
  let is_sing_eval c =
    is_eq c && BVLPROPSAUX_is_ev (lhs c) && is_pair (rand c) &&
    (let r = fst (dest_pair (rand c)) in
     is_comb r && is_const (rator r) && fst (dest_const (rator r)) = "Rval" &&
     is_var (rand r)) &&
    (let xs = fst (dest_pair (rand (lhs c))) in
     is_comb xs && is_comb (rator xs) && rand xs = `[]:bvl_exp list`) in
  let step (asl,w as g) =
    let th = snd (find (fun (_,th) -> is_sing_eval (concl th)) asl) in
    let avoid = freesl (w :: map (concl o snd) asl) in
    let d = variant avoid (mk_var("d",`:bvl_v`)) in
    X_CHOOSE_THEN d SUBST_ALL_TAC (MATCH_MP bvl_evaluate_SING th) g in
  REPEAT step;;

(* STRIP_ASSUME_TAC with every bound variable of the theorem renamed to a   *)
(* fresh name (also apart from the other bound variables)                   *)
let BVLPROPSAUX_FRESH_STRIP_TAC (th:thm) : tactic = fun (asl,w as g) ->
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

(* the results of the integer operations *)
let BVLPROPSAUX_INT_APP_TAC : tactic =
  let imps = map GEN_ALL (CONJUNCTS (SPEC_ALL do_int_app_eq_some)) in
  let is_int_app c =
    is_eq c && (let f,_ = strip_comb (lhs c) in
                is_const f && fst (dest_const f) = "bvl_do_int_app") &&
    is_comb (rand c) && is_const (rator (rand c)) &&
    fst (dest_const (rator (rand c))) = "SOME" in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_int_app (concl th) then
      BVLPROPSAUX_FRESH_STRIP_TAC (hd (mapfilter (fun i -> MATCH_MP i th) imps))
    else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; injectivity "bvl_v"]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY RVEQ_TAC;;

let BVLPROPSAUX_SYMEX_GEN_TAC (rws:thm list) (once:thm list) (simps:thm list) : tactic =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE BVLPROPSAUX_eval_case_eqs o
                CASE_REWRITE_RULE ([REVERSE; APPEND; HD; bvl_do_int_app_def] @ rws) o
                REWRITE_RULE (BVLPROPSAUX_SYMEX_RWS @ rws) o
                check (fun th -> let c = concl th in
                                 is_eq c && BVLPROPSAUX_is_ev (lhs c))) THEN
  DISCH_THEN BVLPROPSAUX_FRESH_STRIP_TAC THEN TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  BVLPROPSAUX_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE; APPEND; HD]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE once) THEN
  BVLPROPSAUX_INT_APP_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  REWRITE_TAC (BVLPROPSAUX_SYMEX_RWS @ rws) THEN
  REPEAT (CHANGED_TAC (ASM_SIMP_TAC simps THEN
                       CASE_REWRITE_TAC[REVERSE; APPEND; HD; bvl_do_int_app_def])) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11; injectivity "bvl_v";
              bvl_Boolv_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "bvl_v"; CONS_11]) THEN
  TRY RVEQ_TAC THEN
  TRY (FIRST [CONV_TAC INT_RING; ASM_INT_ARITH_TAC]);;

let BVLPROPSAUX_SYMEX_TAC = BVLPROPSAUX_SYMEX_GEN_TAC [] [] [];;

(* HOL4 [local] *)
let SmartOp_flip_thm = prove
 (`!op' x1' x2' op x1 x2 env (s:(C,FFI)bvl_state) res s2.
     (op',x1',x2') = SmartOp_flip op x1 x2 /\
     bvl_evaluate ([bvl_Op op [x1; x2]],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([bvl_Op op' [x1'; x2']],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp_flip_def] THEN
  CASES_ON `dest_simple x1` THEN REWRITE_TAC[case_def "option"] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_simple_eq]) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[MEM] THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN BVLPROPSAUX_SYMEX_TAC;
      ALL_TAC])
    [`op = IntOp clos_Add`; `op = IntOp Mult`; `op = IntOp clos_Sub`] THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* local helpers for SmartOp2_thm: the shapes recognised by dest_simple and *)
(* case_op_const, and the BlockOp and MemOp operations SmartOp2 rewrites    *)
let BVLPROPSAUX_exp_shape = prove
 (`!x. (?n. x = bvl_Op (IntOp (clos_Const n)) []) \/
       (?op y n. x = bvl_Op op [y; bvl_Op (IntOp (clos_Const n)) []]) \/
       (dest_simple x = NONE /\ case_op_const x = NONE)`,
  GEN_TAC THEN CASES_ON `dest_simple x` THENL
   [CASES_ON `case_op_const x` THENL
     [ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[case_op_const_eq]) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
      DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[dest_simple_eq]) THEN DISJ1_TAC THEN
    ASM_MESON_TAC[]]);;

let BVLPROPSAUX_do_app_Equal_Number = prove
 (`!a b (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp clos_Equal) [bvl_Number a; bvl_Number b] s =
     Rval (bvl_Boolv (a = b),s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[bvl_do_eq_def]);;

let BVLPROPSAUX_do_app_EqualConst = prove
 (`!i v (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (EqualConst (clos_Int i))) [v] s =
     bvl_do_app (BlockOp clos_Equal) [v; bvl_Number i] s /\
     bvl_do_app (BlockOp (EqualConst (clos_Int i))) [v] s =
     bvl_do_app (BlockOp clos_Equal) [bvl_Number i; v] s`,
  REPEAT GEN_TAC THEN CASES_ON `v:bvl_v` THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[bvl_do_eq_def] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let BVLPROPSAUX_do_app_El_ElemAt = prove
 (`!i v (s:(C,FFI)bvl_state).
     &0 <= i ==>
     bvl_do_app (BlockOp (ElemAt (num_of_int i))) [v] s =
     bvl_do_app (MemOp clos_El) [v; bvl_Number i] s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASES_ON `v:bvl_v` THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]);;

let BVLPROPSAUX_do_app_El_ElemAt' = prove
 (`!i v (s:(C,FFI)bvl_state).
     ~(i < &0) ==>
     bvl_do_app (BlockOp (ElemAt (num_of_int i))) [v] s =
     bvl_do_app (MemOp clos_El) [v; bvl_Number i] s`,
  REWRITE_TAC[INT_NOT_LT; BVLPROPSAUX_do_app_El_ElemAt]);;

let BVLPROPSAUX_do_app_Equal_sym = prove
 (`!i v (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp clos_Equal) [bvl_Number i; v] s =
     bvl_do_app (BlockOp clos_Equal) [v; bvl_Number i] s`,
  MESON_TAC[BVLPROPSAUX_do_app_EqualConst]);;

let BVLPROPSAUX_dest_simple_CONS = prove
 (`!op a l. dest_simple (bvl_Op op (CONS a l)) = NONE`,
  MATCH_MP_TAC clos_op_INDUCT THEN REWRITE_TAC[dest_simple_def] THEN
  MATCH_MP_TAC int_op_INDUCT THEN REWRITE_TAC[dest_simple_def; NULL]);;

(* split an expression into the shapes of BVLPROPSAUX_exp_shape *)
let BVLPROPSAUX_SHAPE_TAC (x:term) (nm:string) : tactic = fun (asl,w as g) ->
  let avoid = freesl (w :: map (concl o snd) asl) in
  let mk n ty = variant avoid (mk_var(n,ty)) in
  let n = mk ("n"^nm) `:int` and opv = mk ("op"^nm) `:clos_op`
  and y = mk ("x"^nm^"1") `:bvl_exp` and m = mk ("n"^nm^"2") `:int` in
  (DISJ_CASES_THEN2
     (X_CHOOSE_THEN n SUBST_ALL_TAC)
     (DISJ_CASES_THEN2
        (X_CHOOSE_THEN opv (X_CHOOSE_THEN y (X_CHOOSE_THEN m SUBST_ALL_TAC)))
        STRIP_ASSUME_TAC)
     (SPEC x BVLPROPSAUX_exp_shape)) g;;

let BVLPROPSAUX_SHAPE_SIMP_TAC : tactic =
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BVLPROPSAUX_dest_simple_CONS; dest_simple_def; NULL] THEN
  CASE_REWRITE_TAC[case_op_const_def; NULL; BVLPROPSAUX_dest_simple_CONS;
                   dest_simple_def];;

let BVLPROPSAUX_CONDS_TAC : tactic =
  REPEAT (COND_CASES_TAC THEN
          REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
          TRY RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_OPCASES_TAC : tactic =
  REPEAT (COND_CASES_TAC THEN
          TRY (FIRST_X_ASSUM (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o
                check (fun th -> let c = concl th in
                                 is_disj c || (is_eq c && is_var (lhs c))))));;

(* HOL4 [local] *)
let SmartOp2_thm = prove
 (`!op x1 x2 env (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate ([bvl_Op op [x1; x2]],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SmartOp2_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MEM] THEN
  BVLPROPSAUX_OPCASES_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  BVLPROPSAUX_SHAPE_TAC `x1:bvl_exp` "1" THEN BVLPROPSAUX_SHAPE_TAC `x2:bvl_exp` "2" THEN
  BVLPROPSAUX_SHAPE_SIMP_TAC THEN BVLPROPSAUX_CONDS_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  BVLPROPSAUX_SYMEX_GEN_TAC [bvl_evaluate_Bool; BVLPROPSAUX_do_app_Equal_Number]
    [BVLPROPSAUX_do_app_Equal_sym]
    [CONJUNCT1 (SPEC_ALL BVLPROPSAUX_do_app_EqualConst); BVLPROPSAUX_do_app_El_ElemAt']);;

(* a local helper: the operations recognised by dest_EqualInt *)
let BVLPROPSAUX_dest_EqualInt_SOME = prove
 (`!op i. dest_EqualInt op = SOME i <=> op = BlockOp (EqualConst (clos_Int i))`,
  MATCH_MP_TAC (BVLPAUX_case_ind dest_EqualInt_def) THEN
  REWRITE_TAC[dest_EqualInt_def; option_DISTINCT; option_INJ; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"; injectivity "block_op";
              distinctness "const_part"; injectivity "const_part"] THEN
  MESON_TAC[]);;

let SmartOp1_thm = prove
 (`!op x env (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate ([bvl_Op op [x]],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([SmartOp1 op x],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SmartOp1_def] THEN
  CASES_ON `dest_EqualInt op` THEN ASM_REWRITE_TAC[case_def "option"] THEN
  CASES_ON `dest_simple x` THEN ASM_REWRITE_TAC[case_def "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_simple_eq; BVLPROPSAUX_dest_EqualInt_SOME]) THEN
  RVEQ_TAC THEN
  BVLPROPSAUX_SYMEX_GEN_TAC
    [bvl_evaluate_Bool; CONJUNCT1 (SPEC_ALL BVLPROPSAUX_do_app_EqualConst);
     BVLPROPSAUX_do_app_Equal_Number] [] [] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let bvl_constProof_SmartOp_thm = prove
 (`!op xs env (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate ([bvl_Op op xs],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([bvl_const_SmartOp op xs],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp_pmatch] THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_exp list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [MESON_TAC[SmartOp1_thm]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t':bvl_exp list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `SmartOp_flip op h h'` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `op':clos_op` (X_CHOOSE_THEN `p:bvl_exp # bvl_exp`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `p:bvl_exp # bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:bvl_exp` (X_CHOOSE_THEN `y2:bvl_exp` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SmartOp2_thm THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SmartOp_flip_thm THEN
  MAP_EVERY EXISTS_TAC [`op:clos_op`; `h:bvl_exp`; `h':bvl_exp`] THEN
  ASM_REWRITE_TAC[]);;

(* local tactics for evaluate_env_rel: resolution with simplification, and *)
(* the split of the evaluation of the source expression                    *)
let BVLPROPSAUX_RES4_TAC (simps:thm list) : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let simp th = curry (REWRITE_RULE simps th) in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let rs = mapfilter (fun a -> simp (MATCH_MP th a)) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results = flat (map (fun th -> resolve 6 (curry th)) imps) in
  let known th l = forall (fun c -> exists (fun a -> aconv (concl a) c) l)
                          (conjuncts (concl th)) in
  let rec dedup acc l = match l with
      [] -> rev acc
    | th::t -> if known th (asms @ acc) then dedup acc t else dedup (th::acc) t in
  match dedup [] results with
    [] -> failwith "BVLPROPSAUX_RES4_TAC"
  | ths -> EVERY (map CAKE_ASSUME_TAC ths) gl;;

let BVLPROPSAUX_ER_START_TAC : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
     is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
     not (BVLPROPSAUX_has_const "bvl_const_compile" c))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC BVLPROPSAUX_eval_case_eqs THEN
  DISCH_THEN BVLPROPSAUX_FRESH_STRIP_TAC THEN TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  BVLPROPSAUX_CLEAN_TAC THEN
  REPEAT (BVLPROPSAUX_RES4_TAC BVLPROPSAUX_eval_simps THEN BVLPROPSAUX_CLEAN_TAC);;

(* a local helper: Force reads the environment only at its index *)
let BVLPROPSAUX_evaluate_Force_env = prove
 (`!loc n n' env env' (s:(C,FFI)bvl_state).
     n < LENGTH env /\ n' < LENGTH env' /\ EL n' env' = EL n env ==>
     bvl_evaluate ([bvl_Force loc n'],env',s) = bvl_evaluate ([bvl_Force loc n],env,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[]);;

(* a local helper: evaluate_env_rel without the vacuous variable ys *)
let BVLPROPSAUX_evaluate_env_rel = prove
 (`!xs env1 (s1:(C,FFI)bvl_state) ax env2 res s2.
     bvl_evaluate (xs,env1,s1) = (res,s2) /\
     bvl_constProof_env_rel (:C) (:FFI) ax env1 env2 /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (bvl_const_compile ax xs,env2,s1) = (res,s2)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THENL
  [(REWRITE_TAC[bvl_const_compile_def; bvl_evaluate_def] THEN MESON_TAC[]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def] THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN REWRITE_TAC[bvl_const_compile_HD_SING] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"]);
   (* next case *)
   ((BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_constProof_env_rel_length) THEN
  CASES_ON `oEL n (ax:(bvl_exp option) list)` THEN CASE_REWRITE_TAC[]) THENL
   [(REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ax:(bvl_exp option) list`; `env1:bvl_v list`; `env2:bvl_v list`; `n:num`]
         bvl_constProof_env_rel_LLOOKUP_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);
    (CASES_ON `a:bvl_exp option` THEN CASE_REWRITE_TAC[]) THENL
    [(REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ax:(bvl_exp option) list`; `env1:bvl_v list`; `env2:bvl_v list`; `n:num`]
         bvl_constProof_env_rel_LLOOKUP_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);
     (MP_TAC(ISPECL [`env1:bvl_v list`; `env2:bvl_v list`; `ax:(bvl_exp option) list`;
                 `a':bvl_exp`; `n:num`] bvl_constProof_env_rel_LOOKUP_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `a':bvl_exp` THEN REWRITE_TAC[bvl_constProof_v_rel_def] THEN CASE_REWRITE_TAC[]) THENL [(REWRITE_TAC[oEL_DROP] THEN REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bvl_evaluate_def]); (STRIP_TAC THEN ASM_REWRITE_TAC[])]]]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  MAP_EVERY (fun b ->
    ASM_CASES_TAC (subst [b,`b:bool`] `HD (bvl_const_compile ax [x1]) = bvl_Bool b`) THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (subst [b,`b:bool`] `bvl_const_compile ax [x1] = [bvl_Bool b]`) ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (subst [b,`b:bool`] `bvl_const_compile ax [x1] = [bvl_Bool b]`);
                                  bvl_evaluate_Bool]) THEN
      BVLPROPSAUX_CLEAN_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD; bvl_Boolv_11]) THEN
      BVLPROPSAUX_CLEAN_TAC THEN
      ASM_REWRITE_TAC[bvl_const_compile_HD_SING];
      ALL_TAC]) [`T`; `F`] THEN
  REWRITE_TAC[bvl_evaluate_def; bvl_const_compile_HD_SING] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"]);
   (* next case *)
   (REPEAT STRIP_TAC THEN
  UNDISCH_TAC `bvl_evaluate ([bvl_Let xs x2],env1,s1:(C,FFI)bvl_state) = (res,s2)` THEN
  REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate (xs,env1,s1:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t1:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THEN
  DISCH_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[bvl_evaluate_def] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`ax:(bvl_exp option) list`; `env2:bvl_v list`;
      `Rval a:(bvl_v list,bvl_v)result`; `t1:(C,FFI)bvl_state`] o
      check (fun th -> is_forall (concl th) &&
                       not (can (find_term (fun t -> t = `x2:bvl_exp`)) (concl th)))) THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`bvl_const_compile ax xs`; `env2:bvl_v list`; `s1:(C,FFI)bvl_state`;
                   `a:bvl_v list`; `t1:(C,FFI)bvl_state`; `ax:(bvl_exp option) list`;
                   `env1:bvl_v list`] bvl_constProof_evaluate_delete_var_Rval) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:bvl_v list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[pair_CASE; case_def "result"; bvl_const_compile_HD_SING] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:bvl_v list`; `t1:(C,FFI)bvl_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM) o
                  check (is_conj o concl)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ax:(bvl_exp option) list`; `env2:bvl_v list`;
      `Rerr a:(bvl_v list,bvl_v)result`; `t1:(C,FFI)bvl_state`] o
      check (fun th -> is_forall (concl th) &&
                       not (can (find_term (fun t -> t = `x2:bvl_exp`)) (concl th)))) THEN
    ASM_REWRITE_TAC[injectivity "result"] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`bvl_const_compile ax xs`; `s1:(C,FFI)bvl_state`; `t1:(C,FFI)bvl_state`;
                   `a:(bvl_v)error_result`; `env2:bvl_v list`]
                  bvl_constProof_evaluate_delete_var_Rerr) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pair_CASE; case_def "result"]]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; bvl_evaluate_def; bvl_const_compile_HD_SING] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; bvl_evaluate_def; bvl_const_compile_HD_SING] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; case_def "error_result"] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  ASM_REWRITE_TAC[bvl_constProof_env_rel_def]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def] THEN MATCH_MP_TAC bvl_constProof_SmartOp_thm THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; pair_CASE; case_def "result"; injectivity "result";
                  distinctness "result"]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; bvl_evaluate_def; bvl_const_compile_HD_SING] THEN
  ASM_REWRITE_TAC[]);
   (* next case *)
   (REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n < LENGTH (env1:bvl_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result)` THEN
    UNDISCH_TAC `bvl_evaluate ([bvl_Force force_loc n],env1,s1:(C,FFI)bvl_state) = (res,s2)` THEN
    REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_constProof_env_rel_length) THEN
  REWRITE_TAC[bvl_const_compile_def] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> let c = concl th in
     is_eq c && BVLPROPSAUX_is_ev (lhs c))) THEN
  CASES_ON `oEL n (ax:(bvl_exp option) list)` THEN CASE_REWRITE_TAC[] THENL
   [MATCH_MP_TAC BVLPROPSAUX_evaluate_Force_env THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[bvl_constProof_env_rel_LLOOKUP_NONE];
    ALL_TAC] THEN
  CASES_ON `a:bvl_exp option` THEN CASE_REWRITE_TAC[] THENL
   [MATCH_MP_TAC BVLPROPSAUX_evaluate_Force_env THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[bvl_constProof_env_rel_LLOOKUP_NONE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`env1:bvl_v list`; `env2:bvl_v list`; `ax:(bvl_exp option) list`;
                 `a':bvl_exp`; `n:num`] bvl_constProof_env_rel_LOOKUP_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `a':bvl_exp` THEN REWRITE_TAC[bvl_constProof_v_rel_def] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[oEL_DROP] THEN REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
    MATCH_MP_TAC BVLPROPSAUX_evaluate_Force_env THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC BVLPROPSAUX_evaluate_Force_env THEN ASM_REWRITE_TAC[]]);
   (* next case *)
   (BVLPROPSAUX_ER_START_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; case_def "option"])
  ]);;

(* HOL4 quantifies an unused variable ys (of HOL4 type 'a) *)
let bvl_constProof_evaluate_env_rel = prove
 (`!xs env1 (s1:(C,FFI)bvl_state) ax env2 res s2 (ys:A).
     bvl_evaluate (xs,env1,s1) = (res,s2) /\
     bvl_constProof_env_rel (:C) (:FFI) ax env1 env2 /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (bvl_const_compile ax xs,env2,s1) = (res,s2)`,
  REWRITE_TAC[BVLPROPSAUX_evaluate_env_rel]);;

(* HOL4: evaluate_env_rel specialised to xs, env, s1, [], env, generalised  *)
(* and simplified with env_rel_def                                          *)
let bvl_constProof_compile_thm = prove
 (`!xs env (s1:(C,FFI)bvl_state) res s2 (ys:A).
     bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (bvl_const_compile [] xs,env,s1) = (res,s2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVLPROPSAUX_evaluate_env_rel THEN
  EXISTS_TAC `env:bvl_v list` THEN ASM_REWRITE_TAC[bvl_constProof_env_rel_def]);;

let bvl_constProof_evaluate_compile_exp = prove
 (`!d env (s:(C,FFI)bvl_state) r t.
     bvl_evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([bvl_const_compile_exp d],env,s) = (r,t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_const_compile_exp_def] THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_const_compile_HD_SING] THEN
  MP_TAC(ISPECL [`[d:bvl_exp]`; `env:bvl_v list`; `s:(C,FFI)bvl_state`;
                 `r:(bvl_v list,bvl_v)result`; `t:(C,FFI)bvl_state`]
                (INST_TYPE [`:bool`,`:A`] bvl_constProof_compile_thm)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 [simp] *)
let delete_var_code_labels = prove
 (`!x. bvl_get_code_labels (bvl_const_delete_var x) = bvl_get_code_labels x`,
  MATCH_MP_TAC bvl_const_delete_var_ind THEN
  REWRITE_TAC[bvl_const_delete_var_def; bvl_get_code_labels_def;
              assign_get_code_label_def; MAP; set_of_list; UNIONS_0; UNION_EMPTY]);;
let _ = cake_add_simps [delete_var_code_labels];;

let dest_simple_SOME_code_labels = prove
 (`!x y. dest_simple x = SOME y ==> bvl_get_code_labels x = {}`,
  REWRITE_TAC[dest_simple_eq] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[bvl_get_code_labels_def; assign_get_code_label_def; MAP; set_of_list;
                  UNIONS_0; UNION_EMPTY]);;

let BVLPROPSAUX_LABELS_RWS =
  [bvl_get_code_labels_def; assign_get_code_label_def; MAP; set_of_list; UNIONS_INSERT;
   UNIONS_0; UNION_EMPTY; bvl_Bool_def];;

(* HOL4 [simp] *)
let SmartOp2_code_labels = prove
 (`!op x1 x2.
     bvl_get_code_labels (SmartOp2 (op,x1,x2)) =
     (assign_get_code_label op UNION bvl_get_code_labels x1) UNION
     bvl_get_code_labels x2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SmartOp2_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MEM] THEN
  BVLPROPSAUX_OPCASES_TAC THEN
  BVLPROPSAUX_SHAPE_TAC `x1:bvl_exp` "1" THEN BVLPROPSAUX_SHAPE_TAC `x2:bvl_exp` "2" THEN
  BVLPROPSAUX_SHAPE_SIMP_TAC THEN BVLPROPSAUX_CONDS_TAC THEN
  REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN SET_TAC[]);;
let _ = cake_add_simps [SmartOp2_code_labels];;

let SmartOp1_code_labels = prove
 (`!op x. bvl_get_code_labels (SmartOp1 op x) = bvl_get_code_labels (bvl_Op op [x])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp1_def] THEN
  CASES_ON `dest_EqualInt op` THEN ASM_REWRITE_TAC[case_def "option"] THEN
  CASES_ON `dest_simple x` THEN ASM_REWRITE_TAC[case_def "option"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_simple_eq; BVLPROPSAUX_dest_EqualInt_SOME]) THEN
  ASM_REWRITE_TAC BVLPROPSAUX_LABELS_RWS);;

(* HOL4 [simp] *)
let SmartOp_code_labels = prove
 (`!op xs.
     bvl_get_code_labels (bvl_const_SmartOp op xs) =
     assign_get_code_label op UNION UNIONS (set_of_list (MAP bvl_get_code_labels xs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp_pmatch] THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC BVLPROPSAUX_LABELS_RWS; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_exp list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC(SmartOp1_code_labels :: BVLPROPSAUX_LABELS_RWS); ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t':bvl_exp list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC BVLPROPSAUX_LABELS_RWS] THEN
  REWRITE_TAC[SmartOp_flip_def] THEN
  CASES_ON `dest_simple h` THEN ASM_REWRITE_TAC[case_def "option"] THENL
   [REWRITE_TAC(SmartOp2_code_labels :: BVLPROPSAUX_LABELS_RWS) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP dest_simple_SOME_code_labels) THEN
  REWRITE_TAC[MEM] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl))) THEN
  REWRITE_TAC(SmartOp2_code_labels :: BVLPROPSAUX_LABELS_RWS) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;
let _ = cake_add_simps [SmartOp_code_labels];;

let MEM_extract_list_code_labels = prove
 (`!xs x. MEM (SOME x) (bvl_const_extract_list xs) ==> bvl_get_code_labels x = {}`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bvl_const_extract_list_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[BVLPROPSAUX_extract_SOME] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC BVLPROPSAUX_LABELS_RWS);;

(* local helpers for compile_code_labels *)
let BVLPROPSAUX_MEM_SOME_labels = prove
 (`!env x. MEM (SOME x) env ==>
           bvl_get_code_labels x SUBSET
           UNIONS (set_of_list (MAP (bvl_get_code_labels o THE) (FILTER IS_SOME env)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE `(s:A->bool) IN t ==> s SUBSET UNIONS t`) THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; MEM_FILTER; o_THM] THEN
  EXISTS_TAC `SOME (x:bvl_exp)` THEN ASM_REWRITE_TAC[IS_SOME_DEF; THE_DEF]);;

let BVLPROPSAUX_extract_list_labels = prove
 (`!ys. UNIONS (set_of_list (MAP (bvl_get_code_labels o THE)
                  (FILTER IS_SOME (bvl_const_extract_list ys)))) = {}`,
  GEN_TAC THEN
  SUBGOAL_THEN `!p. MEM p (bvl_const_extract_list ys) /\ IS_SOME p ==>
                    bvl_get_code_labels (THE p) = {}` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `p:bvl_exp option` (cases "option")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; THE_DEF] THEN
    MESON_TAC[MEM_extract_list_code_labels];
    ALL_TAC] THEN
  REWRITE_TAC[EMPTY_UNIONS; IN_SET_OF_LIST; MEM_MAP; MEM_FILTER; o_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let BVLPROPSAUX_labels_MAP_delete_var = prove
 (`!ys. MAP bvl_get_code_labels (MAP bvl_const_delete_var ys) =
        MAP bvl_get_code_labels ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; delete_var_code_labels]);;

let BVLPROPSAUX_CL_RWS =
  [MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; MAP_APPEND; SET_OF_LIST_APPEND;
   UNIONS_UNION; bvl_get_code_labels_def; SmartOp_code_labels; FILTER; IS_SOME_DEF;
   FILTER_APPEND; BVLPROPSAUX_extract_list_labels; BVLPROPSAUX_labels_MAP_delete_var;
   EMPTY_SUBSET];;

let BVLPROPSAUX_oEL_MEM = prove
 (`!n (l:A list) x. oEL n l = SOME x ==> MEM x l`,
  REWRITE_TAC[oEL_EQ_EL] THEN MESON_TAC[MEM_EL]);;

let BVLPROPSAUX_SUBSET_SET_TAC : tactic = fun (asl,w as g) ->
  let is_sub th = let c = snd (strip_forall (concl th)) in
                  is_comb c && is_comb (rator c) && is_const (rator (rator c)) &&
                  fst (dest_const (rator (rator c))) = "SUBSET" in
  let ths = filter is_sub (map snd asl) in
  (MAP_EVERY MP_TAC ths THEN SET_TAC[]) g;;

let bvl_constProof_compile_code_labels = prove
 (`!x y. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_const_compile x y))) SUBSET
         UNIONS (set_of_list (MAP bvl_get_code_labels y)) UNION
         UNIONS (set_of_list (MAP (bvl_get_code_labels o THE) (FILTER IS_SOME x)))`,
  MATCH_MP_TAC bvl_const_compile_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM bvl_const_compile_HD_SING]) THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN
  RULE_ASSUM_TAC(REWRITE_RULE (HD :: BVLPROPSAUX_CL_RWS)) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC (HD :: BVLPROPSAUX_CL_RWS) THENL
   [(* CONS *) BVLPROPSAUX_SUBSET_SET_TAC;
    (* Var *)
    CASES_ON `oEL v (env:(bvl_exp option) list)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC BVLPROPSAUX_CL_RWS THEN
    CASES_ON `a:bvl_exp option` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC BVLPROPSAUX_CL_RWS THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_MEM_SOME_labels o
                MATCH_MP BVLPROPSAUX_oEL_MEM o
                check (fun th -> is_eq (concl th) && is_comb (rand (concl th)))) THEN
    CASES_ON `a':bvl_exp` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC BVLPROPSAUX_CL_RWS;
    (* If *)
    REPEAT COND_CASES_TAC THEN REWRITE_TAC BVLPROPSAUX_CL_RWS THEN
    BVLPROPSAUX_SUBSET_SET_TAC;
    (* Let *)
    FIRST_X_ASSUM(ASSUME_TAC o SPEC `bvl_const_compile env xs` o
                  check (is_forall o concl)) THEN
    BVLPROPSAUX_SUBSET_SET_TAC;
    (* Handle *) BVLPROPSAUX_SUBSET_SET_TAC;
    (* Raise *) BVLPROPSAUX_SUBSET_SET_TAC;
    (* Op *) BVLPROPSAUX_SUBSET_SET_TAC;
    (* Tick *) BVLPROPSAUX_SUBSET_SET_TAC;
    (* Force *)
    CASES_ON `oEL v (env:(bvl_exp option) list)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC BVLPROPSAUX_CL_RWS THENL
     [REWRITE_TAC[SUBSET_UNION];
      CASES_ON `a:bvl_exp option` THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC (SUBSET_UNION :: BVLPROPSAUX_CL_RWS) THEN
      CASES_ON `a':bvl_exp` THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC (SUBSET_UNION :: BVLPROPSAUX_CL_RWS)];
    (* Call *) BVLPROPSAUX_SUBSET_SET_TAC]);;

let bvl_constProof_compile_exp_code_labels = prove
 (`!e. bvl_get_code_labels (bvl_const_compile_exp e) SUBSET bvl_get_code_labels e`,
  GEN_TAC THEN REWRITE_TAC[bvl_const_compile_exp_def] THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`[]:(bvl_exp option) list`; `[e:bvl_exp]`]
               bvl_constProof_compile_code_labels) THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN
  REWRITE_TAC[HD; MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; FILTER]);;
