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
  CASES_ON `env:bvl_v list` THEN CASES_ON `env2:bvl_v list` THEN
  TRY (CASES_ON `h:bvl_exp option`) THEN FS[bvl_constProof_env_rel_def] THEN
  ASM_MESON_TAC[]);;

(* HOL4 [local] *)
let bvl_constProof_env_rel_LLOOKUP_NONE = prove
 (`!ax env env2 n.
     bvl_constProof_env_rel (:C) (:FFI) ax env env2 /\
     (oEL n ax = NONE \/ oEL n ax = SOME NONE) ==>
     EL n env2 = EL n env`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `env:bvl_v list` THEN CASES_ON `env2:bvl_v list` THEN
  TRY (CASES_ON `h:bvl_exp option`) THEN CASES_ON `n:num` THEN
  FS[bvl_constProof_env_rel_def; oEL_def; EL; HD; TL; SUC_SUB1] THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)
let bvl_constProof_env_rel_LOOKUP_SOME = prove
 (`!env env2 ax x n.
     bvl_constProof_env_rel (:C) (:FFI) ax env env2 /\ oEL n ax = SOME (SOME x) ==>
     bvl_constProof_v_rel (:C) (:FFI) x (EL n env) (EL n env2) (DROP n env)
       (DROP n env2)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `ax:(bvl_exp option) list` THEN TRY (CASES_ON `a0:bvl_exp option`) THEN
  CASES_ON `env2:bvl_v list` THEN CASES_ON `n:num` THEN
  FS[bvl_constProof_env_rel_def; oEL_def; EL; HD; TL; DROP; SUC_SUB1] THEN
  ASM_MESON_TAC[]);;

let bvl_constProof_evaluate_delete_var_Rerr_SING = prove
 (`!x (s:(C,FFI)bvl_state) r e env2.
     bvl_evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error) ==>
     bvl_evaluate ([bvl_const_delete_var x],env2,s) = (Rerr e,r)`,
  GEN_TAC THEN CASES_ON `x:bvl_exp` THEN SIMP[bvl_const_delete_var_def] THEN
  SIMP[bvl_evaluate_def; COND_CASE_EQ] THEN MESON_TAC[]);;

(* a local helper (also used by bvl_handleProof): do_app of an integer op  *)
let BVLPROPSAUX_do_app_IntOp = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvl_state).
     bvl_do_app (IntOp op) vs s =
     match bvl_do_int_app op vs with
       SOME res -> Rval (res,s)
     | NONE -> Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `bvl_do_int_app op vs` THEN CAKE_REWRITE_TAC[]);;

(* HOL4 [local] *)
let bvl_constProof_evaluate_delete_var_Rerr = prove
 (`!xs (s:(C,FFI)bvl_state) r e env2.
     bvl_evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error) ==>
     bvl_evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rerr e,r)`,
  LIST_INDUCT_TAC THEN SIMP[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[] THEN RVEQ_TAC THEN
  TRY (DRULE bvl_constProof_evaluate_delete_var_Rerr_SING THEN FS[] THEN NO_TAC) THEN
  FIRST_X_ASSUM DRULE THEN FS[] THEN
  CASES_ON `h:bvl_exp` THEN GVS[bvl_const_delete_var_def] THEN
  GVS[bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp; bvl_do_int_app_def; COND_CASE_EQ]);;

(* HOL4 [local] *)
let bvl_constProof_evaluate_delete_var_Rval = prove
 (`!xs env2 (s:(C,FFI)bvl_state) a r ax env.
     bvl_evaluate (xs,env2,s) = (Rval a,r) /\
     bvl_constProof_env_rel (:C) (:FFI) ax env env2 ==>
     ?b. bvl_evaluate (MAP bvl_const_delete_var xs,env2,s) = (Rval b,r) /\
         bvl_constProof_env_rel (:C) (:FFI) (APPEND (bvl_const_extract_list xs) ax)
           (APPEND a env) (APPEND b env2)`,
  LIST_INDUCT_TAC THEN SIMP[bvl_evaluate_def; bvl_const_extract_list_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN RW[] THEN EVERY_CASE_TAC THEN GVS[] THEN
  (ASM_CASES_TAC `?i. h = bvl_Var i` THEN FS[] THENL
   [GVS[bvl_const_delete_var_def; bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp;
        bvl_do_int_app_def; COND_CASE_EQ] THEN
    RES_TAC THEN GVS[bvl_const_extract_def; bvl_constProof_env_rel_def;
                     bvl_constProof_v_rel_def; oEL_def] THEN
    IMP_RES_TAC bvl_evaluate_IMP_LENGTH THEN
    FS[LENGTH_MAP; oEL_THM; LENGTH_APPEND; EL_APPEND; ARITH_RULE
       `(i + n + 1) - 1 = i + n /\ (i + n < n + m <=> i < m) /\ ~(i + n < n) /\
        (i + n) - n = i`];
    SUBGOAL_THEN `bvl_const_delete_var h = h` ASSUME_TAC THENL
     [CASES_ON `h:bvl_exp` THEN FS[bvl_const_delete_var_def]; ALL_TAC] THEN
    GVS[] THEN RES_TAC THEN GVS[] THEN
    CASES_ON `bvl_const_extract h (t:bvl_exp list)` THEN
    GVS(bvl_constProof_env_rel_def :: extract_pmatch :: all_case_eqs()) THEN
    GVS([bvl_constProof_v_rel_def; bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp;
         bvl_do_int_app_def] @ all_case_eqs()) THEN
    MAP_EVERY IMP_RES_TAC (CONJUNCTS (SPEC_ALL do_int_app_eq_some)) THEN GVS[]]));;

let evaluate_EQ_NIL = prove
 (`!xs env (s:(C,FFI)bvl_state) t.
     bvl_evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN RW[bvl_evaluate_def] THEN
  IMP_RES_TAC bvl_evaluate_IMP_LENGTH THEN GVS[LENGTH_EQ_NIL; bvl_evaluate_def]);;

(* HOL4 [local] *)
let dest_simple_eq = prove
 (`!h y. dest_simple h = SOME y <=> h = bvl_Op (IntOp (clos_Const y)) []`,
  MATCH_MP_TAC dest_simple_ind THEN RW[NULL_EQ] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let case_op_const_eq = prove
 (`!exp x. case_op_const exp = SOME x <=>
     (?op x1 n2. x = (op,x1,n2) /\
                 exp = bvl_Op op [x1; bvl_Op (IntOp (clos_Const n2)) []])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[case_op_const_pmatch] THEN EVERY_CASE_TAC THEN
  SIMP[] THEN MESON_TAC[]);;

(* HOL4 [local].  The SmartOp theorems evaluate both sides symbolically:   *)
(* the evaluations of the source and the target are unfolded and their     *)
(* case expressions split in lockstep (EVERY_CASE_TAC), instead of HOL4's   *)
(* gvs[evaluate_def, AllCaseEqs()] on the source (a DNF of all the paths,   *)
(* which blows up in the kit, see the report)                               *)
let SmartOp_flip_thm = prove
 (`!op' x1' x2' op x1 x2 env (s:(C,FFI)bvl_state) res s2.
     (op',x1',x2') = SmartOp_flip op x1 x2 /\
     bvl_evaluate ([bvl_Op op [x1; x2]],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([bvl_Op op' [x1'; x2']],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp_flip_def] THEN
  REPEAT TOP_CASE_TAC THEN STRIP_TAC THEN GVS[dest_simple_eq] THEN
  GVS[bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp; bvl_case_eq_thms; case_eq "result"] THEN
  IMP_RES_TAC bvl_evaluate_SING THEN GVS[bvl_do_int_app_def] THEN
  MAP_EVERY IMP_RES_TAC (CONJUNCTS (SPEC_ALL do_int_app_eq_some)) THEN
  GVS[bvl_do_int_app_def; INT_ADD_SYM; INT_MUL_SYM] THEN INT_ARITH_TAC);;

(* HOL4 [local] *)
let SmartOp2_thm = prove
 (`!op x1 x2 env (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate ([bvl_Op op [x1; x2]],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)`,
  let ev = [bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp; REVERSE; APPEND; HD;
            bvl_do_int_app_def] in
  let num_of_int_lt = prove
   (`!i n. &0 <= i ==> (num_of_int i < n <=> i < &n)`,
    SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp2_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT TOP_CASE_TAC THEN STRIP_TAC THEN
  GVS[dest_simple_eq; case_op_const_eq] THEN
  RULE_ASSUM_TAC(REWRITE_RULE ev) THEN REWRITE_TAC ev THEN EVERY_CASE_TAC THEN
  IMP_RES_TAC bvl_evaluate_SING THEN GVS[bvl_do_int_app_def] THEN
  MAP_EVERY IMP_RES_TAC (CONJUNCTS (SPEC_ALL do_int_app_eq_some)) THEN
  GVS[bvl_do_int_app_def] THEN TRY (ASM_INT_ARITH_TAC ORELSE CONV_TAC INT_RING) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[bvl_do_app_def]) THEN TRY(CASES_ON `d1:bvl_v`) THEN
  GVS[bvl_do_eq_def; INT_NOT_LT; num_of_int_lt] THEN REWRITE_TAC[EQ_SYM_EQ]);;

let SmartOp1_thm = prove
 (`!op x env (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate ([bvl_Op op [x]],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([SmartOp1 op x],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp1_def] THEN REPEAT TOP_CASE_TAC THEN STRIP_TAC THEN
  GVS(dest_simple_eq :: dest_EqualInt_pmatch :: all_case_eqs()) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[bvl_do_app_def; bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp;
                                   REVERSE; APPEND; HD; bvl_do_int_app_def]) THEN
  GVS[bvl_do_eq_def] THEN REWRITE_TAC[EQ_SYM_EQ]);;

let bvl_constProof_SmartOp_thm = prove
 (`!op xs env (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate ([bvl_Op op xs],env,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([bvl_const_SmartOp op xs],env,s) = (res,s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_const_SmartOp_def] THEN REPEAT TOP_CASE_TAC THEN
  SIMP[SmartOp1_thm] THEN STRIP_TAC THEN CASES_ON `SmartOp_flip op a0 a0'` THEN
  CASES_ON `y:bvl_exp#bvl_exp` THEN ASM_MESON_TAC[SmartOp_flip_thm; SmartOp2_thm]);;

(* helpers kept for bvl_handleProof and bvl_inlineProof (not used here)    *)

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

(* resolution of the implicational assumptions with simplification *)
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

(* HOL4 quantifies an unused variable ys (of HOL4 type 'a) *)
let bvl_constProof_evaluate_env_rel = prove
 (`!xs env1 (s1:(C,FFI)bvl_state) ax env2 res s2 (ys:A).
     bvl_evaluate (xs,env1,s1) = (res,s2) /\
     bvl_constProof_env_rel (:C) (:FFI) ax env1 env2 /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (bvl_const_compile ax xs,env2,s1) = (res,s2)`,
  let gen = REWRITE_TAC[bvl_evaluate_APPEND] THEN EVERY_CASE_TAC THEN FS[] THEN RVEQ_TAC THEN
    REPEAT (FIRST_X_ASSUM DRULE) THEN FS[] THEN RW[] THEN
    REPEAT (FIRST_X_ASSUM DRULE) THEN FS[] THEN RW[] THEN
    IMP_RES_TAC bvl_evaluate_SING THEN GVS[] in
  let var = IMP_RES_TAC bvl_constProof_env_rel_length THEN REPEAT TOP_CASE_TAC THEN
    DRULE bvl_constProof_env_rel_LLOOKUP_NONE THEN
    IMP_RES_TAC bvl_constProof_env_rel_LOOKUP_SOME THEN
    GVS[bvl_constProof_v_rel_def; oEL_DROP; COND_CASE_EQ] THEN
    GVS[oEL_EQ_EL; bvl_evaluate_def] in
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT STRIP_TAC THEN
  FS[bvl_const_compile_def; bvl_evaluate_def; bvl_const_compile_HD_SING] THENL
   [(* CONS *) gen;
    (* Var *) var;
    (* If *)
    gen THEN IMP_RES_TAC (MESON[] `!x y:bvl_exp. x = y ==> [x] = [y]`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bvl_const_compile_HD_SING]) THEN
    GVS[bvl_evaluate_def; bvl_const_compile_HD_SING] THEN FS[bvl_Bool_def];
    (* Let *)
    EVERY_CASE_TAC THEN FS[] THEN RVEQ_TAC THEN REPEAT (FIRST_X_ASSUM DRULE) THEN
    FS[] THEN RW[] THEN IMP_RES_TAC bvl_constProof_evaluate_delete_var_Rerr THEN
    IMP_RES_TAC bvl_constProof_evaluate_delete_var_Rval THEN GVS[];
    (* Raise *) gen;
    (* Handle *) gen THEN GVS[bvl_constProof_env_rel_def];
    (* Op *)
    MATCH_MP_TAC bvl_constProof_SmartOp_thm THEN ASM_REWRITE_TAC[bvl_evaluate_def] THEN gen;
    (* Tick *) gen;
    (* Force *) var;
    (* Call *) gen]);;

(* HOL4: evaluate_env_rel specialised to xs, env, s1, [], env, generalised  *)
(* and simplified with env_rel_def                                          *)
let bvl_constProof_compile_thm = prove
 (`!xs env (s1:(C,FFI)bvl_state) res s2 (ys:A).
     bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (bvl_const_compile [] xs,env,s1) = (res,s2)`,
  MESON_TAC[bvl_constProof_evaluate_env_rel; bvl_constProof_env_rel_def]);;

let bvl_constProof_evaluate_compile_exp = prove
 (`!d env (s:(C,FFI)bvl_state) r t.
     bvl_evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([bvl_const_compile_exp d],env,s) = (r,t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_const_compile_exp_def] THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN SIMP[] THEN
  ONCE_REWRITE_TAC[bvl_const_compile_HD_SING] THEN
  MATCH_MP_TAC bvl_constProof_compile_thm THEN ASM_REWRITE_TAC[]);;

(* HOL4 [simp] *)
let delete_var_code_labels = prove
 (`!x. bvl_get_code_labels (bvl_const_delete_var x) = bvl_get_code_labels x`,
  GEN_TAC THEN CASES_ON `x:bvl_exp` THEN
  SIMP[bvl_const_delete_var_def; assign_get_code_label_def; set_of_list; UNIONS_0;
       UNION_EMPTY]);;
let _ = cake_add_simps [delete_var_code_labels];;

let dest_simple_SOME_code_labels = prove
 (`!x y. dest_simple x = SOME y ==> bvl_get_code_labels x = {}`,
  SIMP[dest_simple_eq; assign_get_code_label_def; set_of_list; UNIONS_0; UNION_EMPTY]);;

(* kept for bvl_handleProof and bvl_inlineProof; used below *)
let BVLPROPSAUX_LABELS_RWS =
  [bvl_get_code_labels_def; assign_get_code_label_def; MAP; set_of_list; UNIONS_INSERT;
   UNIONS_0; UNION_EMPTY; bvl_Bool_def];;

(* HOL4 [simp] *)
let SmartOp2_code_labels = prove
 (`!op x1 x2.
     bvl_get_code_labels (SmartOp2 (op,x1,x2)) =
     (assign_get_code_label op UNION bvl_get_code_labels x1) UNION
     bvl_get_code_labels x2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp2_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT TOP_CASE_TAC THEN
  GVS(dest_simple_eq :: case_op_const_eq :: BVLPROPSAUX_LABELS_RWS) THEN SET_TAC[]);;
let _ = cake_add_simps [SmartOp2_code_labels];;

let SmartOp1_code_labels = prove
 (`!op x. bvl_get_code_labels (SmartOp1 op x) = bvl_get_code_labels (bvl_Op op [x])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartOp1_def] THEN REPEAT TOP_CASE_TAC THEN
  GVS(dest_simple_eq :: dest_EqualInt_pmatch :: all_case_eqs()) THEN
  SIMP BVLPROPSAUX_LABELS_RWS);;

(* HOL4 [simp] *)
let SmartOp_code_labels = prove
 (`!op xs.
     bvl_get_code_labels (bvl_const_SmartOp op xs) =
     assign_get_code_label op UNION UNIONS (set_of_list (MAP bvl_get_code_labels xs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_const_SmartOp_def; SmartOp_flip_def] THEN
  REPEAT TOP_CASE_TAC THEN IMP_RES_TAC dest_simple_SOME_code_labels THEN
  SIMP(SmartOp1_code_labels :: BVLPROPSAUX_LABELS_RWS) THEN SET_TAC[]);;
let _ = cake_add_simps [SmartOp_code_labels];;

let MEM_extract_list_code_labels = prove
 (`!xs x. MEM (SOME x) (bvl_const_extract_list xs) ==> bvl_get_code_labels x = {}`,
  LIST_INDUCT_TAC THEN RW[bvl_const_extract_list_def] THEN RES_TAC THEN
  CASES_ON `bvl_const_extract h (t:bvl_exp list)` THEN
  GVS(extract_pmatch :: all_case_eqs()) THEN SIMP BVLPROPSAUX_LABELS_RWS);;

let bvl_constProof_compile_code_labels = prove
 (`!x y. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_const_compile x y))) SUBSET
         UNIONS (set_of_list (MAP bvl_get_code_labels y)) UNION
         UNIONS (set_of_list (MAP (bvl_get_code_labels o THE) (FILTER IS_SOME x)))`,
  let rws = [MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION; set_of_list; UNIONS_INSERT;
             UNIONS_0; UNION_EMPTY; FILTER; FILTER_APPEND; IS_SOME_DEF; o_THM; THE_DEF] in
  let var = SUBGOAL_THEN `!x. oEL v env = SOME (SOME x) ==> bvl_get_code_labels x SUBSET
      UNIONS (set_of_list (MAP (bvl_get_code_labels o THE) (FILTER IS_SOME env)))`
    MP_TAC THENL
     [REWRITE_TAC[oEL_EQ_EL; SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; MEM_FILTER] THEN
      MESON_TAC[MEM_EL; IS_SOME_DEF; THE_DEF; o_THM];
      REPEAT TOP_CASE_TAC THEN FS rws] in
  MATCH_MP_TAC bvl_const_compile_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_const_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM bvl_const_compile_HD_SING]) THEN
  FS rws THENL
   [(* CONS *) ASM SET_TAC[];
    (* Var *) var;
    (* If *) REPEAT TOP_CASE_TAC THEN FS rws THEN ASM SET_TAC[];
    (* Let *)
    SUBGOAL_THEN `!ys. UNIONS (set_of_list (MAP (bvl_get_code_labels o THE)
                     (FILTER IS_SOME (bvl_const_extract_list ys)))) = {}` ASSUME_TAC THENL
     [REWRITE_TAC[EMPTY_UNIONS; IN_SET_OF_LIST; MEM_MAP; MEM_FILTER; IS_SOME_EXISTS] THEN
      REPEAT STRIP_TAC THEN GVS[o_THM; THE_DEF] THEN
      ASM_MESON_TAC[MEM_extract_list_code_labels];
      FIRST_X_ASSUM (MP_TAC o SPEC `bvl_const_compile env xs`) THEN
      FS[MAP_MAP_o; o_DEF; delete_var_code_labels; ETA_AX] THEN ASM SET_TAC[]];
    (* Handle *) ASM SET_TAC[];
    (* Op *) ASM SET_TAC[];
    (* Force *) var;
    (* Call *) ASM SET_TAC[]]);;

let bvl_constProof_compile_exp_code_labels = prove
 (`!e. bvl_get_code_labels (bvl_const_compile_exp e) SUBSET bvl_get_code_labels e`,
  GEN_TAC THEN REWRITE_TAC[bvl_const_compile_exp_def] THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN
  MP_TAC(SPECL [`[]:(bvl_exp option) list`; `[e:bvl_exp]`]
               bvl_constProof_compile_code_labels) THEN
  ONCE_REWRITE_TAC[GSYM bvl_const_compile_HD_SING] THEN
  SIMP[set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; FILTER]);;
