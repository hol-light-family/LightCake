(* ========================================================================= *)
(* bvi_letProof: port of HOL4 compiler/backend/proofs/bvi_letProofScript.sml *)
(* (CakeML v3479).  Correctness proof for bvi_let.  BVLPROPSAUX_ names are   *)
(* local helpers (not HOL4 names).                                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bviProps.ml";;

type_invention_error := true;;

(* HOL4 LLOOKUP l n is oEL n l; y and xs are unused (of unconstrained types  *)
(* in HOL4, as here)                                                          *)
let bvi_letProof_v_rel_def = cake_def
  `bvi_letProof_v_rel a (x:A) (y:B) (xs:C) ys <=> oEL a ys = SOME x`;;

let bvi_letProof_env_rel_def = sem1aux_def
  `(bvi_letProof_env_rel [] d (e1:A list) e2 <=> e1 = DROP d e2) /\
   (bvi_letProof_env_rel (CONS a rest) d (CONS x e1) (CONS y e2) <=>
      bvi_letProof_v_rel a x y (CONS x e1) (CONS y e2) /\
      bvi_letProof_env_rel rest d e1 e2) /\
   (bvi_letProof_env_rel _ _ _ _ <=> F)`;;


(* HOL4 leaves d free *)
let bvi_letProof_env_rel_length = prove
 (`!ax (env:A list) env2 d.
     bvi_letProof_env_rel ax d env env2 ==> LENGTH env <= LENGTH env2`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[bvi_letProof_env_rel_def] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_DROP] THEN ARITH_TAC;
    STRUCT_CASES_TAC(ISPEC `env:A list` list_CASES) THEN
    STRUCT_CASES_TAC(ISPEC `env2:A list` list_CASES) THEN
    REWRITE_TAC[bvi_letProof_env_rel_def; LENGTH; LE_SUC; LE_0] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 [local] *)
let bvi_letProof_env_rel_LLOOKUP_NONE = prove
 (`!ax (env:A list) env2 n d.
     bvi_letProof_env_rel ax d env env2 /\ oEL n ax = NONE /\ n < LENGTH env ==>
     n + d < LENGTH env2 /\ EL (n + d) env2 = EL n env`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[bvi_letProof_env_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_DROP]) THEN
    SUBGOAL_THEN `n + d < LENGTH (env2:A list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_DROP];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `env:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `env2:A list` list_CASES) THEN
  REWRITE_TAC[bvi_letProof_env_rel_def; LENGTH; oEL_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':A list`; `t'':A list`; `n - 1`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_CONS; ARITH_RULE `~(n = 0) ==> ~(n + d = 0)`;
               ARITH_RULE `~(n = 0) ==> (n + d) - 1 = (n - 1) + d`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 [local] *)
let bvi_letProof_env_rel_LOOKUP_SOME = prove
 (`!(env:A list) env2 ax x n d.
     bvi_letProof_env_rel ax d env env2 /\ oEL n ax = SOME x ==>
     bvi_letProof_v_rel x (EL n env) (EL n env2) (DROP n env) (DROP n env2)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `env2:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `ax:num list` list_CASES) THEN
  REWRITE_TAC[bvi_letProof_env_rel_def; oEL_DEF; option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THENL
   [RVEQ_TAC THEN ASM_REWRITE_TAC[EL; HD; DROP_0];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':A list`; `t'':num list`; `x:num`; `n - 1`;
                                  `d:num`]) THEN
    ASM_REWRITE_TAC[EL_CONS; DROP_DEF]]);;

(* local helpers: the constant 0 (HOL4 evaluates it with EVAL), and        *)
(* delete_var keeps a value result and its state                          *)
let BVLPROPSAUX_bvi_evaluate_Const0 = prove
 (`!env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Op (IntOp (clos_Const (&0))) []],env,s) =
     (Rval [bvl_Number (&0)],s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"] THEN
  REWRITE_TAC[bvi_do_app_aux_def; REVERSE; NULL] THEN CAKE_REWRITE_TAC[REVERSE; NULL] THEN
  REWRITE_TAC[small_enough_int_def] THEN CONV_TAC INT_REDUCE_CONV THEN CAKE_REWRITE_TAC[]);;

let BVLPROPSAUX_delete_var_Rval = prove
 (`!h env (s:(C,FFI)bvi_state) a s1.
     bvi_evaluate ([h],env,s) = (Rval a,s1) ==>
     ?b. bvi_evaluate ([bvi_let_delete_var h],env,s) = (Rval b,s1)`,
  GEN_TAC THEN CASES_ON `h:bvi_exp` THEN REWRITE_TAC[bvi_let_delete_var_def] THEN
  TRY (MESON_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN
  REWRITE_TAC[bvi_evaluate_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
  MESON_TAC[]);;

let bvi_letProof_evaluate_delete_var_Rerr_SING = prove
 (`!x (s:(C,FFI)bvi_state) r e env2.
     bvi_evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error) ==>
     bvi_evaluate ([bvi_let_delete_var x],env2,s) = (Rerr e,r)`,
  GEN_TAC THEN CASES_ON `x:bvi_exp` THEN REWRITE_TAC[bvi_let_delete_var_def] THEN
  TRY (MESON_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN
  REWRITE_TAC[bvi_evaluate_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let bvi_letProof_evaluate_delete_var_Rerr = prove
 (`!xs (s:(C,FFI)bvi_state) r e env2.
     bvi_evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error) ==>
     bvi_evaluate (MAP bvi_let_delete_var xs,env2,s) = (Rerr e,r)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; bvi_evaluate_def; PAIR_EQ; distinctness "result"] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  MP_TAC(ISPEC `bvi_evaluate ([h],env2,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvi_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:bvi_result` THEN REWRITE_TAC[case_def "result"] THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `b:bvl_v list` ASSUME_TAC o
                MATCH_MP BVLPROPSAUX_delete_var_Rval) THEN
    ASM_REWRITE_TAC[pair_CASE; case_def "result"] THEN
    MP_TAC(ISPEC `bvi_evaluate (t,env2,s1:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:bvi_result`
      (X_CHOOSE_THEN `s2:(C,FFI)bvi_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    CASES_ON `r2:bvi_result` THEN
    REWRITE_TAC[case_def "result"; PAIR_EQ; distinctness "result";
                injectivity "result"] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `bvi_evaluate (MAP bvi_let_delete_var t,env2,s1:(C,FFI)bvi_state) =
                  (Rerr e,r)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[pair_CASE; case_def "result"]];
    REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:bvi_exp`; `s:(C,FFI)bvi_state`; `s1:(C,FFI)bvi_state`;
                   `a:exn_or_ret error_result`; `env2:bvl_v list`]
                  bvi_letProof_evaluate_delete_var_Rerr_SING) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE; case_def "result"]]);;

(* local helpers: split an evaluation into named result parts, keeping its *)
(* equation; delete_var and extract off variables                         *)
let BVLPROPSAUX_bvi_EVSPLIT_TAC (tm:term) (rn:string) (sn:string)
                                (vn:string) (en:string) : tactic =
  fun (asl,w as gl) ->
    let rty,sty = (match dest_type (type_of tm) with
                     (_,[a;b]) -> a,b | _ -> failwith "BVLPROPSAUX_bvi_EVSPLIT_TAC") in
    let vty,ety = (match dest_type rty with
                     (_,[a;b]) -> a,mk_type("error_result",[b])
                   | _ -> failwith "BVLPROPSAUX_bvi_EVSPLIT_TAC") in
    let r = mk_var(rn,rty) and s = mk_var(sn,sty) in
    let v = mk_var(vn,vty) and e = mk_var(en,ety) in
    (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
     DISJ_CASES_THEN2 (X_CHOOSE_THEN v SUBST_ALL_TAC) (X_CHOOSE_THEN e SUBST_ALL_TAC)
       (ISPEC r (cases "result")) THEN
     ASM_REWRITE_TAC[pair_CASE; case_def "result"]) gl;;

let BVLPROPSAUX_delete_var_not_Var = prove
 (`!h. ~(?i. h = bvi_Var i) ==>
       bvi_let_delete_var h = h /\ !ys:bvi_exp list. bvi_let_extract h ys = 0`,
  GEN_TAC THEN CASES_ON `h:bvi_exp` THEN
  REWRITE_TAC[bvi_let_delete_var_def; bvi_let_extract_def; injectivity "bvi_exp";
              distinctness "bvi_exp"] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let bvi_letProof_evaluate_delete_var_Rval = prove
 (`!xs env2 (s:(C,FFI)bvi_state) a r ax env d.
     bvi_evaluate (xs,env2,s) = (Rval a,r) /\ bvi_letProof_env_rel ax d env env2 ==>
     ?b. bvi_evaluate (MAP bvi_let_delete_var xs,env2,s) = (Rval b,r) /\
         bvi_letProof_env_rel (APPEND (bvi_let_extract_list xs) ax) d
           (APPEND a env) (APPEND b env2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; bvi_evaluate_def; PAIR_EQ; injectivity "result";
                bvi_let_extract_list_def; APPEND] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:bvl_v list` THEN
    ASM_REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  BVLPROPSAUX_bvi_EVSPLIT_TAC `bvi_evaluate ([h],env2,s:(C,FFI)bvi_state)`
    "r1" "s1" "v1" "e1" THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP) THEN
  BVLPROPSAUX_bvi_EVSPLIT_TAC `bvi_evaluate (t,env2,s1:(C,FFI)bvi_state)`
    "r2" "s2" "v2" "e2" THEN
  REWRITE_TAC(HD :: BVLPROPSAUX_bvi_eval_simps) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun ih ->
    let ih' = REWRITE_RULE[IMP_CONJ] ih in
    FIRST_ASSUM(fun th -> let ih2 = MATCH_MP ih' th in
      FIRST_ASSUM(fun th2 -> X_CHOOSE_THEN `b:bvl_v list` STRIP_ASSUME_TAC
                                (MATCH_MP ih2 th2)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) &&
                     BVLPROPSAUX_has_const "bvi_let_delete_var" (lhs (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  REWRITE_TAC[MAP; bvi_let_extract_list_def; APPEND] THEN
  ASM_CASES_TAC `?i. h = bvi_Var i` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        concl th = `bvi_evaluate ([bvi_Var i],env2,s:(C,FFI)bvi_state) =
                    (Rval [w],s1)`)) THEN
    REWRITE_TAC[bvi_evaluate_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `CONS (bvl_Number (&0)) b` THEN
    ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
    ASM_REWRITE_TAC[bvi_let_delete_var_def; BVLPROPSAUX_bvi_evaluate_Const0; pair_CASE;
                    case_def "result"; HD; APPEND; bvi_letProof_env_rel_def;
                    bvi_letProof_v_rel_def; bvi_let_extract_def] THEN
    REWRITE_TAC[oEL_DEF; ARITH_RULE `~(i + l + 1 = 0)`;
                ARITH_RULE `(i + l + 1) - 1 = l + i`] THEN
    REWRITE_TAC[oEL_THM; LENGTH_APPEND] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < e ==> l + i < l + e`; EL_APPEND2; LE_ADD;
                 ARITH_RULE `(l + i) - l = i`];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVLPROPSAUX_delete_var_not_Var) THEN
    EXISTS_TAC `CONS (w:bvl_v) b` THEN
    ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
    ASM_REWRITE_TAC[pair_CASE; case_def "result"; HD; APPEND; bvi_letProof_env_rel_def;
                    bvi_letProof_v_rel_def; oEL_DEF]]);;

let evaluate_SNOC_Rval = prove
 (`!x y env (s:(C,FFI)bvi_state) a r.
     bvi_evaluate (SNOC x y,env,s) = (Rval a,r) ==>
     ?a1 a2 r1. a = SNOC a1 a2 /\ LENGTH y = LENGTH a2 /\
                bvi_evaluate (y,env,s) = (Rval a2,r1) /\
                bvi_evaluate ([x],env,r1) = (Rval [a1],r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_SNOC] THEN
  BVLPROPSAUX_bvi_EVSPLIT_TAC `bvi_evaluate (y,env,s:(C,FFI)bvi_state)`
    "r2" "s2" "v2" "e2" THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN
  BVLPROPSAUX_bvi_EVSPLIT_TAC `bvi_evaluate ([x],env,s2:(C,FFI)bvi_state)`
    "r3" "s3" "v3" "e3" THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_simps THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP evaluate_SING_IMP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH o
    check (fun th -> fst (dest_pair (rand (lhs (concl th)))) = `y:bvi_exp list`)) THEN
  MAP_EVERY EXISTS_TAC [`w:bvl_v`; `v2:bvl_v list`; `s2:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[SNOC_APPEND]);;

let compile_CONS = prove
 (`!ax d x xs. bvi_let_compile ax d (CONS x xs) =
               APPEND (bvi_let_compile ax d [x]) (bvi_let_compile ax d xs)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:bvi_exp list` list_CASES) THEN
  REWRITE_TAC[bvi_let_compile_def; APPEND_NIL]);;

let compile_APPEND = prove
 (`!xs ys ax d. bvi_let_compile ax d (APPEND xs ys) =
                APPEND (bvi_let_compile ax d xs) (bvi_let_compile ax d ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; bvi_let_compile_def] THEN
  ONCE_REWRITE_TAC[compile_CONS] THEN ASM_REWRITE_TAC[APPEND_ASSOC]);;

let IMP_COMM = prove
 (`!b1 b2 b3. (b1 ==> b2 ==> b3) <=> (b2 ==> b1 ==> b3)`,
  MESON_TAC[]);;

(* HOL4 exp2_size is list_size bvi_exp_size (bvi_let's exp2_size_APPEND is *)
(* the same fact)                                                           *)
let exp_size_APPEND = prove
 (`!xs ys. list_size bvi_exp_size (APPEND xs ys) =
           list_size bvi_exp_size xs + list_size bvi_exp_size ys`,
  REWRITE_TAC[exp2_size_APPEND]);;

(* a local helper: oEL past a prefix *)
let BVLPROPSAUX_oEL_APPEND_LENGTH = prove
 (`!(a:A list) l h. oEL (LENGTH a + h) (APPEND a l) = oEL h l`,
  REWRITE_TAC[oEL_THM; LENGTH_APPEND; LT_ADD_LCANCEL] THEN
  SIMP_TAC[EL_APPEND2; LE_ADD; ADD_SUB2]);;

let env_rel_MAP = prove
 (`!ax (env1:A list) env2 d a.
     bvi_letProof_env_rel ax d env1 env2 ==>
     bvi_letProof_env_rel (MAP ((+) (LENGTH a)) ax) (d + LENGTH a) env1
       (APPEND a env2)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[bvi_letProof_env_rel_def; MAP] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[DROP_APPEND2; ARITH_RULE `l <= d + l`; ADD_SUB];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `env1:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `env2:A list` list_CASES) THEN
  REWRITE_TAC[bvi_letProof_env_rel_def] THEN STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a:A list` list_CASES) THENL
   [SUBGOAL_THEN `((+) (LENGTH ([]:A list))) = (\x:num. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MAP_ID; APPEND; LENGTH; ADD_CLAUSES; bvi_letProof_env_rel_def];
    ALL_TAC] THEN
  REWRITE_TAC[MAP; APPEND; bvi_letProof_env_rel_def] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> BVLPROPSAUX_has_const "bvi_letProof_v_rel"
                                              (concl th))) THEN
    REWRITE_TAC[bvi_letProof_v_rel_def] THEN
    MP_TAC(ISPECL [`CONS (h''':A) t'''`; `CONS (h'':A) t''`; `h:num`]
             BVLPROPSAUX_oEL_APPEND_LENGTH) THEN
    REWRITE_TAC[APPEND] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':A list`; `t'':A list`; `d:num`;
                                  `APPEND (t''':A list) [h'']`]) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; GSYM APPEND_ASSOC; APPEND] THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* HOL4 [local] *)
let env_rel_REPLICATE_0 = prove
 (`!(vs:A list) ax d env1 env2.
     bvi_letProof_env_rel ax d env1 env2 ==>
     bvi_letProof_env_rel (APPEND (REPLICATE (LENGTH vs) 0) ax) d (APPEND vs env1)
       (APPEND vs env2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; REPLICATE; APPEND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[bvi_letProof_env_rel_def; bvi_letProof_v_rel_def; oEL_DEF]);;

(* local helpers for evaluate_env_rel: HOL4's completeInduct_on on the size *)
(* of the expression list, and Force reads the environment at its index    *)
let BVLPROPSAUX_bvi_size_ind = prove
 (`!P. (!xs. (!ys. list_size bvi_exp_size ys < list_size bvi_exp_size xs ==> P ys)
             ==> P xs) ==> !xs. P xs`,
  GEN_TAC THEN MP_TAC(ISPEC `list_size bvi_exp_size` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN MESON_TAC[]);;

let BVLPROPSAUX_bvi_evaluate_Force_env = prove
 (`!loc n n' env env' (s:(C,FFI)bvi_state).
     n < LENGTH env /\ n' < LENGTH env' /\ EL n' env' = EL n env ==>
     bvi_evaluate ([bvi_Force loc n'],env',s) = bvi_evaluate ([bvi_Force loc n],env,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[]);;

(* local tactics for evaluate_env_rel (HOL4 proves it by completeInduct_on   *)
(* with a case analysis on the expression): STRIP_ASSUME_TAC with globally  *)
(* fresh names, the split of the source evaluation, the instances of the    *)
(* induction hypothesis for the compiled parts of the goal (with their size *)
(* facts), and the evaluation of the compiled expression                   *)
let BVLPROPSAUX_bvi_FRESH_STRIP_TAC (th:thm) : tactic = fun (asl,w as g) ->
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

let BVLPROPSAUX_bvi_is_ev t = is_comb t && is_const (rator t) &&
                              fst (dest_const (rator t)) = "bvi_evaluate";;

let BVLPROPSAUX_LET_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_bvi_FRESH_STRIP_TAC o
     REWRITE_RULE BVLPROPSAUX_bvi_eval_case_eqs o BETA_RULE o
     REWRITE_RULE[LET_DEF; LET_END_DEF] o ONCE_REWRITE_RULE[bvi_evaluate_def] o
     check (fun th -> let c = concl th in
       is_eq c && BVLPROPSAUX_bvi_is_ev (lhs c) &&
       not (BVLPROPSAUX_has_const "bvi_let_compile" c))) THEN
  TRY RVEQ_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC;;

let BVLPROPSAUX_bvi_size_rws =
  filter (fun th -> exists (fun c -> let c = snd (strip_forall c) in is_eq c &&
            (try fst (dest_const (rator (lhs c))) = "bvi_exp_size" with Failure _ -> false))
            (conjuncts (concl th))) !the_size_defs @
  filter (fun th -> can (find_term (fun t -> is_const t &&
            (let n = fst (dest_const t) in String.length n > 12 &&
                                           String.sub n 0 12 = "bvi_exp_size")))
            (concl th)) (flat (map snd (!the_size_aux_eqs)));;

let BVLPROPSAUX_LET_SIZE_TAC : tactic = fun (asl,w as g) ->
  let has c t = is_comb t && is_const(rator t) && fst(dest_const(rator t)) = c in
  let bls = find_terms (has "BUTLAST") w and ls = find_terms (has "LAST") w in
  (MAP_EVERY (fun t -> ASSUME_TAC
      (ISPECL [`bvi_exp_size`; rand t] BVIPAUX_LET_list_size_BUTLAST)) bls THEN
   MAP_EVERY (fun t -> MP_TAC
      (REWRITE_RULE[GSYM LENGTH_EQ_NIL]
         (ISPECL [`bvi_exp_size`; rand t] BVIPAUX_LET_list_size_LAST))) ls THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC(list_size :: SNOC_APPEND :: exp2_size_APPEND :: BVLPROPSAUX_bvi_size_rws) THEN
   RULE_ASSUM_TAC(REWRITE_RULE(list_size :: SNOC_APPEND :: exp2_size_APPEND ::
                               BVLPROPSAUX_bvi_size_rws)) THEN
   ASM_ARITH_TAC) g;;

let BVLPROPSAUX_LET_IH_TAC : tactic = fun (asl,w as g) ->
  let is_ih th = let c = concl th in is_forall c &&
    (let v,b = dest_forall c in type_of v = `:bvi_exp list` && is_imp b &&
       BVLPROPSAUX_has_const "list_size" (lhand b)) in
  let ih = snd (find (fun (_,th) -> is_ih th) asl) in
  let is_comp t = let f,args = strip_comb t in
    is_const f && fst (dest_const f) = "bvi_let_compile" && length args = 3 in
  let ls = setify (map rand (find_terms is_comp w)) in
  MAP_EVERY (fun l -> MP_TAC (SPEC l ih) THEN ANTS_TAC THENL
                       [BVLPROPSAUX_LET_SIZE_TAC; DISCH_TAC]) ls g;;

let BVLPROPSAUX_LET_FIN_TAC : tactic =
  REPEAT (BVLPROPSAUX_bvi_RES3_TAC BVLPROPSAUX_bvi_eval_simps THEN
          BVLPROPSAUX_bvi_CLEAN_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[bvi_let_compile_HD_SING] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF; IS_NONE_DEF]) THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; case_def "option";
                  case_def "error_result"; case_def "exn_or_ret";
                  IS_SOME_DEF; IS_NONE_DEF; bvi_let_compile_HD_SING];;

let BVLPROPSAUX_LET_GEN_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_let_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  BVLPROPSAUX_LET_IH_TAC THEN BVLPROPSAUX_LET_SPLIT_TAC THEN BVLPROPSAUX_LET_FIN_TAC;;

let BVLPROPSAUX_LET_CONS_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_let_compile_def] THEN BVLPROPSAUX_LET_IH_TAC THEN
  BVLPROPSAUX_LET_SPLIT_TAC THEN
  REPEAT (BVLPROPSAUX_bvi_RES3_TAC BVLPROPSAUX_bvi_eval_simps THEN
          BVLPROPSAUX_bvi_CLEAN_TAC) THEN
  ONCE_REWRITE_TAC[GSYM bvi_let_compile_HD_SING] THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[bvi_let_compile_HD_SING] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"];;

let BVLPROPSAUX_LET_VAR_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN BVLPROPSAUX_LET_SPLIT_TAC THEN
  REWRITE_TAC[bvi_let_compile_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_letProof_env_rel_length) THEN
  CASES_ON `oEL a (ax:num list)` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_evaluate_def] THENL
   [MP_TAC(ISPECL [`ax:num list`; `env1:bvl_v list`; `env2:bvl_v list`; `a:num`; `d:num`]
             bvi_letProof_env_rel_LLOOKUP_NONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`env1:bvl_v list`; `env2:bvl_v list`; `ax:num list`; `a':num`; `a:num`;
                   `d:num`] bvi_letProof_env_rel_LOOKUP_SOME) THEN
    ASM_REWRITE_TAC[bvi_letProof_v_rel_def; oEL_DROP] THEN REWRITE_TAC[oEL_EQ_EL] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[]];;

let BVLPROPSAUX_LET_FORCE_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a1 < LENGTH (env1:bvl_v list)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                            BVLPROPSAUX_bvi_is_ev (lhs (concl th)))) THEN
    PURE_ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_let_compile_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_letProof_env_rel_length) THEN
  CASES_ON `oEL a1 (ax:num list)` THEN CAKE_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`ax:num list`; `env1:bvl_v list`; `env2:bvl_v list`; `a1:num`; `d:num`]
             bvi_letProof_env_rel_LLOOKUP_NONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a0:num`; `a1:num`; `a1 + d`; `env1:bvl_v list`; `env2:bvl_v list`;
                   `s1:(C,FFI)bvi_state`] BVLPROPSAUX_bvi_evaluate_Force_env) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`env1:bvl_v list`; `env2:bvl_v list`; `ax:num list`; `a:num`; `a1:num`;
                   `d:num`] bvi_letProof_env_rel_LOOKUP_SOME) THEN
    ASM_REWRITE_TAC[bvi_letProof_v_rel_def; oEL_DROP] THEN REWRITE_TAC[oEL_EQ_EL] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`a0:num`; `a1:num`; `a1 + a`; `env1:bvl_v list`; `env2:bvl_v list`;
                   `s1:(C,FFI)bvi_state`] BVLPROPSAUX_bvi_evaluate_Force_env) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];;

(* local helpers for the Call and LetCall cases: the environment relation *)
(* for a handler (one more variable) and after a call (the returned       *)
(* values, by env_rel_REPLICATE_0)                                         *)
let BVLPROPSAUX_env_rel_CONS0 = prove
 (`!ax d (env1:A list) env2 v.
     bvi_letProof_env_rel ax d env1 env2 ==>
     bvi_letProof_env_rel (CONS 0 ax) d (CONS v env1) (CONS v env2)`,
  REWRITE_TAC[bvi_letProof_env_rel_def; bvi_letProof_v_rel_def; oEL_DEF]);;

let BVLPROPSAUX_LET_ENV_TAC : tactic = fun (asl,w as g) ->
  let is_er c = (try fst (dest_const (fst (strip_comb c))) = "bvi_letProof_env_rel"
                 with Failure _ -> false) in
  let r = snd (find (fun (_,th) -> let c = concl th in
     is_er c && el 2 (snd (strip_comb c)) = `env1:bvl_v list`) asl) in
  let envs = setify (mapfilter (fun (_,th) -> let c = concl th in
     if is_eq c && BVLPROPSAUX_bvi_is_ev (lhs c) then
       fst (dest_pair (snd (dest_pair (rand (lhs c)))))
     else failwith "") asl) in
  let lens = filter (fun th -> let c = concl th in is_eq c &&
     (try fst (dest_const (rator (lhs c))) = "LENGTH" with Failure _ -> false))
     (map snd asl) in
  let fact e =
    let f,args = strip_comb e in
    if is_const f && fst (dest_const f) = "CONS" && el 1 args = `env1:bvl_v list` then
      SPEC (el 0 args) (MATCH_MP BVLPROPSAUX_env_rel_CONS0 r)
    else if is_const f && fst (dest_const f) = "APPEND" &&
            el 1 args = `env1:bvl_v list` then
      REWRITE_RULE lens (SPEC (el 0 args) (MATCH_MP env_rel_REPLICATE_0 r))
    else failwith "" in
  MAP_EVERY ASSUME_TAC (mapfilter fact envs) g;;

let BVLPROPSAUX_LET_CALL_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_let_compile_def] THEN
  CASES_ON `a3:bvi_exp option` THEN CAKE_REWRITE_TAC[] THEN
  BVLPROPSAUX_LET_IH_TAC THEN BVLPROPSAUX_LET_SPLIT_TAC THEN
  BVLPROPSAUX_LET_ENV_TAC THEN BVLPROPSAUX_LET_FIN_TAC;;

let BVLPROPSAUX_LET_LETCALL_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_let_compile_def] THEN
  BVLPROPSAUX_LET_IH_TAC THEN BVLPROPSAUX_LET_SPLIT_TAC THEN
  BVLPROPSAUX_LET_ENV_TAC THEN BVLPROPSAUX_LET_FIN_TAC;;

(* local helpers for the Let case: the last of the bound values, and the *)
(* three branches of the compiled Let                                     *)
let BVLPROPSAUX_EL_LENGTH_SNOC = prove
 (`!(a2:A list) w l. LENGTH a2 < LENGTH (APPEND (APPEND a2 [w]) l) /\
                     EL (LENGTH a2) (APPEND (APPEND a2 [w]) l) = w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a2:A list`; `LENGTH (a2:A list)`] EL_APPEND2) THEN
  REWRITE_TAC[LE_REFL; SUB_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EL; HD]);;

let BVLPROPSAUX_bvi_evaluate_Var = el 2 (CONJUNCTS bvi_evaluate_def);;

let BVLPROPSAUX_LET_SNOC_TAC : tactic =
  TRY (FIRST_ASSUM(fun th -> let c = concl th in
     if is_eq c && lhs c = `bvi_evaluate (y,env1,s1:(C,FFI)bvi_state)` &&
        (let r = fst (dest_pair (rhs c)) in is_comb r &&
         fst (dest_const (rator r)) = "Rval") then
       let a2 = rand (fst (dest_pair (rhs c))) in
       let lth = MATCH_MP bvi_evaluate_IMP_LENGTH th in
       let er = MATCH_MP env_rel_MAP
                  (ASSUME `bvi_letProof_env_rel ax d env1 (env2:bvl_v list)`) in
       ASSUME_TAC lth THEN ASSUME_TAC (SPEC a2 er) THEN
       TRY (FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o
                        MATCH_MP evaluate_SING_IMP)) THEN
       RULE_ASSUM_TAC(fun th' ->
         if BVLPROPSAUX_has_const "bvi_Var" (concl th') && is_eq (concl th') &&
            BVLPROPSAUX_bvi_is_ev (lhs (concl th'))
         then REWRITE_RULE[lth; BVLPROPSAUX_bvi_evaluate_Var; BVLPROPSAUX_EL_LENGTH_SNOC] th'
         else th') THEN
       BVLPROPSAUX_bvi_CLEAN_TAC
     else NO_TAC)) THEN
  BVLPROPSAUX_LET_FIN_TAC;;

let BVLPROPSAUX_LET_DV_TAC : tactic =
  BVLPROPSAUX_LET_IH_TAC THEN BVLPROPSAUX_LET_SPLIT_TAC THEN
  REPEAT (BVLPROPSAUX_bvi_RES3_TAC BVLPROPSAUX_bvi_eval_simps THEN
          BVLPROPSAUX_bvi_CLEAN_TAC) THEN
  IMP_RES_TAC bvi_letProof_evaluate_delete_var_Rval THEN
  IMP_RES_TAC bvi_letProof_evaluate_delete_var_Rerr THEN
  REPEAT (FIRST_X_ASSUM(BVLPROPSAUX_bvi_FRESH_STRIP_TAC o check (is_exists o concl))) THEN
  BVLPROPSAUX_LET_FIN_TAC;;

let BVLPROPSAUX_LET_LET_TAC : tactic =
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_let_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NIL]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a0:bvi_exp list = []`)) THEN
    BVLPROPSAUX_LET_IH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       BVLPROPSAUX_bvi_is_ev (lhs (concl th)) &&
       not (BVLPROPSAUX_has_const "bvi_let_compile" (concl th)))) THEN
    PURE_ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    REWRITE_TAC[bvi_evaluate_def; pair_CASE; case_def "result"; APPEND] THEN DISCH_TAC THEN
    REPEAT (BVLPROPSAUX_bvi_RES3_TAC BVLPROPSAUX_bvi_eval_simps THEN
            BVLPROPSAUX_bvi_CLEAN_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                  lhs (concl th) = `a1:bvi_exp`)) THEN
    MP_TAC(ISPEC `a0:bvi_exp list` SNOC_CASES) THEN ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:bvi_exp` (X_CHOOSE_THEN `y:bvi_exp list` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[FRONT_SNOC; LAST_SNOC; LENGTH_SNOC; SUC_SUB1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_SNOC; SUC_SUB1]) THEN
    BVLPROPSAUX_LET_IH_TAC THEN
    FIRST_X_ASSUM(BVLPROPSAUX_bvi_FRESH_STRIP_TAC o
      REWRITE_RULE BVLPROPSAUX_bvi_eval_case_eqs o
      REWRITE_RULE[bvi_evaluate_SNOC] o PURE_ONCE_REWRITE_RULE[bvi_evaluate_def] o
      check (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_bvi_is_ev (lhs c) &&
                       not (BVLPROPSAUX_has_const "bvi_let_compile" c))) THEN
    TRY RVEQ_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN
    BVLPROPSAUX_LET_SNOC_TAC;
    BVLPROPSAUX_LET_DV_TAC];;

(* a local helper: evaluate_env_rel without the vacuous variable ys *)
let BVLPROPSAUX_bvi_let_env_rel = prove
 (`!xs env1 (s1:(C,FFI)bvi_state) ax env2 res s2 d.
     bvi_evaluate (xs,env1,s1) = (res,s2) /\
     bvi_letProof_env_rel ax d env1 env2 /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate (bvi_let_compile ax d xs,env2,s1) = (res,s2)`,
  MATCH_MP_TAC BVLPROPSAUX_bvi_size_ind THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvi_exp list` list_CASES) THENL
   [REWRITE_TAC[bvi_let_compile_def; bvi_evaluate_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:bvi_exp list` list_CASES) THENL
   [CASES_ON `h:bvi_exp` THENL
     [BVLPROPSAUX_LET_VAR_TAC; BVLPROPSAUX_LET_GEN_TAC; BVLPROPSAUX_LET_LET_TAC;
      BVLPROPSAUX_LET_GEN_TAC; BVLPROPSAUX_LET_GEN_TAC; BVLPROPSAUX_LET_CALL_TAC;
      BVLPROPSAUX_LET_FORCE_TAC; BVLPROPSAUX_LET_GEN_TAC; BVLPROPSAUX_LET_LETCALL_TAC;
      BVLPROPSAUX_LET_GEN_TAC];
    BVLPROPSAUX_LET_CONS_TAC]);;

(* HOL4 also quantifies a vacuous ys (of an unconstrained type) *)
let bvi_letProof_evaluate_env_rel = prove
 (`!xs env1 (s1:(C,FFI)bvi_state) ax env2 res s2 (ys:A) d.
     bvi_evaluate (xs,env1,s1) = (res,s2) /\
     bvi_letProof_env_rel ax d env1 env2 /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate (bvi_let_compile ax d xs,env2,s1) = (res,s2)`,
  MESON_TAC[BVLPROPSAUX_bvi_let_env_rel]);;

(* HOL4: evaluate_env_rel specialised to xs, env, s1, [], env, res, s2, ys, *)
(* 0, generalised and simplified with env_rel_def                           *)
let bvi_letProof_compile_thm = prove
 (`!xs env (s1:(C,FFI)bvi_state) res s2.
     bvi_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate (bvi_let_compile [] 0 xs,env,s1) = (res,s2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVLPROPSAUX_bvi_let_env_rel THEN
  EXISTS_TAC `env:bvl_v list` THEN ASM_REWRITE_TAC[bvi_letProof_env_rel_def; DROP_0]);;

let bvi_letProof_evaluate_compile_exp = prove
 (`!d env (s:(C,FFI)bvi_state) r t.
     bvi_evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate ([bvi_let_compile_exp d],env,s) = (r,t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_let_compile_exp_def] THEN
  ONCE_REWRITE_TAC[GSYM bvi_let_compile_HD_SING] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_let_compile_HD_SING] THEN MATCH_MP_TAC bvi_letProof_compile_thm THEN
  ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_BVI_LABELS_RWS =
  [bvi_get_code_labels_def; assign_get_code_label_def; MAP; set_of_list; UNIONS_INSERT;
   UNIONS_0; UNION_EMPTY];;

(* HOL4 [simp] *)
let dest_var_code_labels = prove
 (`!x. bvi_get_code_labels (bvi_let_delete_var x) = bvi_get_code_labels x`,
  GEN_TAC THEN CASES_ON `x:bvi_exp` THEN
  REWRITE_TAC(bvi_let_delete_var_def :: BVLPROPSAUX_BVI_LABELS_RWS));;
let _ = cake_add_simps [dest_var_code_labels];;

(* local helpers for compile_code_labels: the labels of a compiled          *)
(* singleton, of a deleted list, and of a list split into BUTLAST and LAST  *)
let BVLPROPSAUX_gcl_HD_compile = prove
 (`!env d x. bvi_get_code_labels (HD (bvi_let_compile env d [x])) =
             UNIONS (set_of_list (MAP bvi_get_code_labels (bvi_let_compile env d [x])))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM bvi_let_compile_HD_SING] THEN
  REWRITE_TAC[HD; MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

let BVLPROPSAUX_MAP_gcl_delete_var = prove
 (`!l. MAP bvi_get_code_labels (MAP bvi_let_delete_var l) = MAP bvi_get_code_labels l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; dest_var_code_labels]);;

let BVLPROPSAUX_UNIONS_BUTLAST_LAST = prove
 (`!xs. ~(xs = []) ==>
        UNIONS (set_of_list (MAP bvi_get_code_labels xs)) =
        UNIONS (set_of_list (MAP bvi_get_code_labels (BUTLAST xs))) UNION
        bvi_get_code_labels (LAST xs)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                          [GSYM (MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION; MAP; set_of_list;
              UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

let bvi_letProof_compile_code_labels = prove
 (`!x y z. UNIONS (set_of_list (MAP bvi_get_code_labels (bvi_let_compile x y z))) =
           UNIONS (set_of_list (MAP bvi_get_code_labels z))`,
  MATCH_MP_TAC bvi_let_compile_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[bvi_let_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NIL]) THEN
  REWRITE_TAC(MAP_APPEND :: SET_OF_LIST_APPEND :: UNIONS_UNION :: BVLPROPSAUX_gcl_HD_compile ::
              BVLPROPSAUX_MAP_gcl_delete_var :: case_def "option" ::
              BVLPROPSAUX_BVI_LABELS_RWS) THEN
  ASM_SIMP_TAC BVLPROPSAUX_BVI_LABELS_RWS THEN
  ASM_SIMP_TAC(BVLPROPSAUX_UNIONS_BUTLAST_LAST :: BVLPROPSAUX_BVI_LABELS_RWS) THEN
  ASM_REWRITE_TAC(LENGTH :: BVLPROPSAUX_BVI_LABELS_RWS));;

(* HOL4 [simp] *)
let bvi_letProof_compile_exp_code_labels = prove
 (`!x. bvi_get_code_labels (bvi_let_compile_exp x) = bvi_get_code_labels x`,
  GEN_TAC THEN REWRITE_TAC[bvi_let_compile_exp_def] THEN
  ONCE_REWRITE_TAC[GSYM bvi_let_compile_HD_SING] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[BVLPROPSAUX_gcl_HD_compile; bvi_letProof_compile_code_labels] THEN
  REWRITE_TAC BVLPROPSAUX_BVI_LABELS_RWS);;
let _ = cake_add_simps [bvi_letProof_compile_exp_code_labels];;
