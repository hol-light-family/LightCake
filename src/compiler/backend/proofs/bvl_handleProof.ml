(* ========================================================================= *)
(* bvl_handleProof: port of HOL4 compiler/backend/proofs/                    *)
(* bvl_handleProofScript.sml (CakeML v3479).  Correctness proof for          *)
(* bvl_handle.  BVLPROPSAUX_ names are local helpers (not HOL4 names).       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;

type_invention_error := true;;

(* HOL4 leaves a and r free (and binds s twice); here a and r are bound   *)
(* in each conjunct.  HOL4 shows that do_app never raises with do_app_def *)
(* and do_install_def; here bvl_do_app_err (bvlProps) says it            *)
let can_raise_thm = prove
 (`(!e env (s:(A,B)bvl_state) (a:bvl_v) r.
      bvl_evaluate ([e],env,s) = (Rerr (Rraise a),r) ==> can_raise e) /\
   (!es env (s:(A,B)bvl_state) (a:bvl_v) r.
      bvl_evaluate (es,env,s) = (Rerr (Rraise a),r) ==> can_raise1 es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN FS([can_raise_def; bvl_evaluate_def] @ all_case_eqs()) THEN
  RW[] THEN RES_TAC THEN FS[] THEN
  POP_ASSUM MP_TAC THEN SIMP([ONCE bvl_evaluate_CONS] @ all_case_eqs()) THEN
  RW[] THEN RES_TAC THEN FS[] THEN IMP_RES_TAC bvl_do_app_err THEN FS[]);;

(* HOL4 [simp] *)
let handle_adj_vars_0 = prove
 (`(!x l. handle_adj_vars l 0 x = x) /\ (!x l. handle_adj_vars1 l 0 x = x)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN FS[handle_adj_vars_def]);;
let _ = cake_add_simps [handle_adj_vars_0];;

let evaluate_handle_adj_vars_lemma = prove
 (`(!x xs a env (r:(A,B)bvl_state).
      bvl_evaluate ([handle_adj_vars (LENGTH xs) (LENGTH a) x],
                    APPEND xs (APPEND a env),r) =
      bvl_evaluate ([x],APPEND xs env,r)) /\
   (!x xs a env (r:(A,B)bvl_state).
      bvl_evaluate (handle_adj_vars1 (LENGTH xs) (LENGTH a) x,
                    APPEND xs (APPEND a env),r) =
      bvl_evaluate (x,APPEND xs env,r))`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REPEAT STRIP_TAC THEN
  FS[bvl_evaluate_def; handle_adj_vars_def] THENL
   [(* Var *) RW[] THEN FS[ARITH_ss; EL_APPEND; SUB_ADD_RCANCEL];
    (* Let *)
    REPEAT (CASE_TAC THEN FS[]) THEN FIRST_X_ASSUM (QSPEC_THEN "APPEND a' xs" MP_TAC) THEN
    IMP_RES_TAC bvl_evaluate_IMP_LENGTH THEN FS[ADD_SYM];
    (* Handle *)
    REPEAT (CASE_TAC THEN FS[]) THEN FIRST_X_ASSUM (QSPEC_THEN "CONS a'' xs" MP_TAC) THEN
    FS[ADD1];
    (* Force *) RW[] THEN FS[ARITH_ss; EL_APPEND; SUB_ADD_RCANCEL];
    (* CONS *) ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN FS[]]);;

(* HOL4 leaves x2 free *)
let evaluate_handle_adj_vars = prove
 (`!x2 xs l a env (r:(A,B)bvl_state).
     l <= LENGTH env ==>
     bvl_evaluate ([handle_adj_vars (LENGTH xs) (l + LENGTH a) x2],
                   APPEND xs (APPEND a env),r) =
     bvl_evaluate ([handle_adj_vars (LENGTH xs) l x2],APPEND xs env,r)`,
  RW[] THEN IMP_RES_TAC LESS_EQ_LENGTH THEN GVS[] THEN
  QSPECL_THEN ["x2"; "xs"; "APPEND a ys1"; "ys2"; "r"] MP_TAC
    (CONJUNCT1 evaluate_handle_adj_vars_lemma) THEN
  QSPECL_THEN ["x2"; "xs"; "ys1"; "ys2"; "r"] MP_TAC
    (CONJUNCT1 evaluate_handle_adj_vars_lemma) THEN
  FS[ADD_SYM]);;

(* HOL4 leaves x1, x2, r, d, l, env free *)
let handle_adj_vars_evaluate = prove
 (`!x1 x2 (r:(A,B)bvl_state) d l env.
     (!env. bvl_evaluate ([x1],env,r) = bvl_evaluate ([x2],env,r)) /\
     d + l <= LENGTH env ==>
     bvl_evaluate ([handle_adj_vars d l x1],env,r) =
     bvl_evaluate ([handle_adj_vars d l x2],env,r)`,
  RW[] THEN IMP_RES_TAC LESS_EQ_LENGTH THEN GVS[] THEN GVS[LENGTH_EQ_SUM] THEN
  QSPECL_THEN ["x1"; "l1"; "l2"; "ys2"; "r"] MP_TAC
    (CONJUNCT1 evaluate_handle_adj_vars_lemma) THEN
  QSPECL_THEN ["x2"; "l1"; "l2"; "ys2"; "r"] MP_TAC
    (CONJUNCT1 evaluate_handle_adj_vars_lemma) THEN
  FS[]);;

(* HOL4 splits on dest_handle_Raise, _Let and _If with one_line_ify and    *)
(* AllCaseEqs; here BVLPAUX_dest_handle_Raise_eq, _Let_eq and _If_eq      *)
(* (bvl_handle) invert them                                                *)
let evaluate_handle_simp = prove
 (`(!x env (s:(A,B)bvl_state).
      bvl_evaluate ([handle_simp x],env,s) = bvl_evaluate ([x],env,s)) /\
   (!xs env (s:(A,B)bvl_state).
      bvl_evaluate (handle_simp_list xs,env,s) = bvl_evaluate (xs,env,s)) /\
   (!x1 x2 l env (s:(A,B)bvl_state).
      l <= LENGTH env ==>
      bvl_evaluate ([make_handle x1 x2 l],env,s) =
      bvl_evaluate ([bvl_Handle x1 (handle_adj_vars 1 l x2)],env,s))`,
  MATCH_MP_TAC handle_simp_ind THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[handle_simp_def] THEN
  TRY (FS[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN FS[] THEN NO_TAC) THEN
  CASES_ON `dest_handle_Raise x` THEN FS[] THENL
   [ALL_TAC;
    GVS[BVLPAUX_dest_handle_Raise_eq] THEN SIMP[bvl_evaluate_def] THEN
    TOP_CASE_TAC THEN TOP_CASE_TAC THEN FS[] THEN IMP_RES_TAC bvl_evaluate_SING THEN GVS[] THEN
    TRY (IRULE handle_adj_vars_evaluate THEN FS[ARITH_ss]) THEN
    TOP_CASE_TAC THEN FS[] THEN IMP_RES_TAC can_raise_thm THEN FS[]] THEN
  CASES_ON `dest_handle_Let x` THEN FS[] THENL
   [ALL_TAC;
    GVS[BVLPAUX_dest_handle_Let_eq] THEN GVS[bvl_evaluate_def] THEN
    TOP_CASE_TAC THEN TOP_CASE_TAC THEN FS[] THENL
     [TOP_CASE_TAC THEN TOP_CASE_TAC THEN IMP_RES_TAC bvl_evaluate_IMP_LENGTH THEN
      RFS[ARITH_ss] THEN TOP_CASE_TAC THEN FS[] THEN IMP_RES_TAC can_raise_thm THEN FS[] THEN
      IRULE (REWRITE_RULE[LENGTH; APPEND; GSYM ONE]
               (SPECL [`x2:bvl_exp`; `[v:bvl_v]`] evaluate_handle_adj_vars)) THEN FS[];
      TOP_CASE_TAC THEN FS[] THEN IMP_RES_TAC can_raise_thm THEN FS[]]] THEN
  CASES_ON `dest_handle_If x` THEN FS[] THENL
   [FS[bvl_evaluate_def] THEN REPEAT (TOP_CASE_TAC THEN FS[]) THEN
    IRULE handle_adj_vars_evaluate THEN FS[ARITH_ss];
    FS[BVLPAUX_dest_handle_If_eq] THEN RVEQ_TAC THEN FS[] THEN SIMP[bvl_evaluate_def] THEN
    CASE_TAC THEN TOP_CASE_TAC THEN FS[] THEN
    TRY (TOP_CASE_TAC THEN FS[] THEN IMP_RES_TAC can_raise_thm THEN FS[] THEN NO_TAC) THEN
    IMP_RES_TAC bvl_evaluate_SING THEN GVS[] THEN
    RW[] THEN REPEAT (TOP_CASE_TAC THEN FS[]) THEN IMP_RES_TAC can_raise_thm THEN FS[]]);;

(* HOL4 [simp] *)
let evaluate_SmartLet = prove
 (`!xs x env (s:(A,B)bvl_state).
     bvl_evaluate ([SmartLet xs x],env,s) = bvl_evaluate ([bvl_Let xs x],env,s)`,
  RW[SmartLet_def] THEN FS[NULL_EQ; bvl_evaluate_def]);;
let _ = cake_add_simps [evaluate_SmartLet];;

let let_ok_def = sem1aux_def
  `(let_ok (bvl_Let xs b) <=> ALL isVar xs /\ bVarBound (LENGTH xs) [b]) /\
   (let_ok _ <=> F)`;;

(* HOL4: Termination WF_REL_TAC with measure exp1_size *)
let handle_ok_def = sem1aux_def_wf
  `MEASURE (list_size bvl_exp_size)`
  SEM1AUX_TC_TAC
  `(handle_ok [] <=> T) /\
   (handle_ok (CONS (x:bvl_exp) (CONS y xs)) <=>
      handle_ok [x] /\ handle_ok (CONS y xs)) /\
   (handle_ok [bvl_Var v] <=> T) /\
   (handle_ok [bvl_If x1 x2 x3] <=>
      handle_ok [x1] /\ handle_ok [x2] /\ handle_ok [x3]) /\
   (handle_ok [bvl_Let xs x2] <=>
      if LENGTH xs = 0 then
        let_ok x2 /\ (!ys y. x2 = bvl_Let ys y ==> handle_ok [y])
      else
        handle_ok xs /\ handle_ok [x2]) /\
   (handle_ok [bvl_Raise x1] <=> handle_ok [x1]) /\
   (handle_ok [bvl_Tick x1] <=> handle_ok [x1]) /\
   (handle_ok [bvl_Op op xs] <=> handle_ok xs) /\
   (handle_ok [bvl_Handle x1 x2] <=>
      match x1 with
        bvl_Let xs b ->
          ALL isVar xs /\ bVarBound (LENGTH xs) [b] /\
          handle_ok [b] /\ handle_ok [x2]
      | _ -> F) /\
   (handle_ok [bvl_Force loc n] <=> T) /\
   (handle_ok [bvl_Call ticks dest xs] <=> handle_ok xs)`;;

let handle_ok_ind = cake_ind "handle_ok";;

(* HOL4: evaluate_genlist_vars specialised to 0, env ++ ys, LENGTH env, s *)
(* and simplified with TAKE_APPEND1 *)
let evaluate_GENLIST = prove
 (`!env ys (s:(C,FFI)bvl_state).
     bvl_evaluate (list_of_seq bvl_Var (LENGTH env),APPEND env ys,s) = (Rval env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`0`; `APPEND (env:bvl_v list) ys`; `LENGTH (env:bvl_v list)`;
                 `s:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
  REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; LE_ADD; DROP; ETA_AX; TAKE_LENGTH_APPEND]);;

let bvl_handleProof_env_rel_def = cake_def
  `bvl_handleProof_env_rel l (env:bvl_v list) env1 <=>
     LIST_RELi (\i v1 v2. has_var i l ==> v1 = v2) env env1`;;

let env_rel_mk_Union = prove
 (`!env env1 lx ly.
     bvl_handleProof_env_rel (mk_Union lx ly) env env1 <=>
     bvl_handleProof_env_rel lx env env1 /\ bvl_handleProof_env_rel ly env env1`,
  FS[LIST_RELi_EL_EQN; bvl_handleProof_env_rel_def; has_var_mk_Union] THEN MESON_TAC[]);;

let bvl_handleProof_env_rel_length = prove
 (`!l env env1. bvl_handleProof_env_rel l env env1 ==> LENGTH env1 = LENGTH env`,
  FS[LIST_RELi_EL_EQN; bvl_handleProof_env_rel_def]);;

let env_rel_MAPi = prove
 (`!l1 env.
     bvl_handleProof_env_rel l1 env
       (MAPi (\i v. if has_var i l1 then v else bvl_Number (&0)) env)`,
  FS[LIST_RELi_EL_EQN; bvl_handleProof_env_rel_def; LENGTH_MAPi; EL_MAPi]);;

let IMP_EL_SING = prove
 (`!k xs (x:A) ys. k = LENGTH xs ==> EL k (APPEND (APPEND xs [x]) ys) = x`,
  RW[] THEN FS[ARITH_ss; EL_APPEND]);;

let ALOOKUP_MAPi_SWAP = prove
 (`!n k (xs:A list).
     ~(n = k) ==>
     ALOOKUP (MAPi (\i x. (x,i)) (APPEND xs [k])) n = ALOOKUP (MAPi (\i x. (x,i)) xs) n`,
  MP_TAC(prove
   (`!(xs:A list) z n k. ~(n = k) ==>
       ALOOKUP (MAPi (\i x. (x,i + z)) (APPEND xs [k])) n =
       ALOOKUP (MAPi (\i x. (x,i + z)) xs) n`,
    LIST_INDUCT_TAC THEN FS[MAPi_DEF; o_DEF; ADD1; GSYM ADD_ASSOC])) THEN
  DISCH_THEN(MP_TAC o GEN `xs:A list` o SPECL [`xs:A list`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[]);;

let ALOOKUP_MAPi_APPEND2 = prove
 (`!(xs:A list) k.
     ~MEM k xs ==>
     ALOOKUP (MAPi (\i x. (x,i)) (APPEND xs [k])) k = SOME (LENGTH xs)`,
  MP_TAC(prove
   (`!(xs:A list) z k. ~MEM k xs ==>
       ALOOKUP (MAPi (\i x. (x,i + z)) (APPEND xs [k])) k = SOME (LENGTH xs + z)`,
    LIST_INDUCT_TAC THEN RW[MAPi_DEF; o_DEF; ADD1; GSYM ADD_ASSOC] THEN ARITH_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `xs:A list` o SPECL [`xs:A list`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let IS_SOME_lookup_db_to_set = prove
 (`!n l. IS_SOME (lookup n (db_to_set l)) <=> has_var n l`,
  RW[lookup_db_to_set; IS_SOME_EXISTS] THEN MESON_TAC[one]);;

(* a local helper for evaluate_LetLet (HOL4 proves it inline, by an        *)
(* induction on env with SNOC_INDUCT): the list of LetLet evaluates to the  *)
(* variables of zs in env, numbers 0 elsewhere                              *)
let BVLPROPSAUX_evaluate_long_list = prove
 (CASE_TERM `!zs env ex (s:(A,B)bvl_state) n.
     ALL (\i. i < LENGTH env) zs ==>
     bvl_evaluate (list_of_seq (\n. match ALOOKUP (MAPi (\i x. (x,i)) zs) n with
                     NONE -> bvl_Op (IntOp (clos_Const (&0))) [] | SOME k -> bvl_Var k) n,
                   APPEND (MAP (\i. EL i env) zs) ex,s) =
     (Rval (list_of_seq (\n. if MEM n zs then EL n env else bvl_Number (&0)) n),s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  FS[list_of_seq; bvl_evaluate_def; bvl_evaluate_APPEND] THEN
  QCASES_ON "ALOOKUP (MAPi (\\i x. (x,i)) zs) n" THEN
  FS[bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp; bvl_do_int_app_def] THENL
   [RFS[ALOOKUP_NONE; MAP_MAPi; o_DEF; MAPi_EQ_MAP; MAP_ID];
    IMP_RES_TAC ALOOKUP_MEM THEN GVS[MEM_MAPi; EL_APPEND; EL_MAP; MEM_EL; ARITH_ss]]);;

let evaluate_LetLet = prove
 (`!y env env1 extra l1 (s1:(A,B)bvl_state) res.
     (!env2 extra. bvl_handleProof_env_rel l1 env env2 ==>
                   bvl_evaluate ([y],APPEND env2 extra,s1) = res) /\
     bvl_handleProof_env_rel l1 env env1 ==>
     bvl_evaluate ([LetLet (LENGTH env) (db_to_set l1) y],APPEND env1 extra,s1) = res`,
  REPEAT STRIP_TAC THEN FS[LetLet_def; IS_SOME_lookup_db_to_set] THEN
  ABBREV_TAC `qs = FILTER (\n. has_var n l1) (list_of_seq I (LENGTH (env:bvl_v list)))` THEN
  SUBGOAL_THEN `!n. MEM n qs <=> has_var n l1 /\ n < LENGTH (env:bvl_v list)` ASSUME_TAC THENL
   [EXPAND_TAC "qs" THEN FS[MEM_FILTER; MEM_GENLIST] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate (MAP bvl_Var qs,APPEND env1 extra,s1:(A,B)bvl_state) =
                (Rval (MAP (\i. EL i env) qs),s1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `ALL (\n. has_var n l1 /\ n < LENGTH (env:bvl_v list)) qs` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM ALL_MEM]; ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
    SPEC_TAC(`qs:num list`,`qs:num list`) THEN LIST_INDUCT_TAC THEN
    FS[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN RW[] THEN
    IMP_RES_TAC bvl_handleProof_env_rel_length THEN FS[bvl_evaluate_def; EL_APPEND; ARITH_ss] THEN
    RFS[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN];
    ALL_TAC] THEN
  FS[bvl_evaluate_def] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[BVLPROPSAUX_evaluate_long_list; GSYM ALL_MEM] THEN
  CASE_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FS[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let env_rel_refl = prove
 (`!l env. bvl_handleProof_env_rel l env env`,
  REWRITE_TAC[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN]);;

(* HOL4 [local] *)
let opt_lemma = prove
 (`!x y:(1)option. x = y <=> (x = SOME one <=> y = SOME one)`,
  REPEAT GEN_TAC THEN CASES_ON `x:(1)option` THEN CASES_ON `y:(1)option` THEN
  FS[] THEN MESON_TAC[one]);;

(* a local helper: the liveness of OptionalLetLet (HOL4 shows that          *)
(* db_to_set (vars_flatten lx) = db_to_set lx with spt_eq_thm and           *)
(* opt_lemma)                                                               *)
let BVLPROPSAUX_env_rel_flatten = prove
 (`!lx env env1.
     bvl_handleProof_env_rel (vars_from_list (MAP FST (toAList (db_to_set lx)))) env env1 <=>
     bvl_handleProof_env_rel lx env env1`,
  REWRITE_TAC[GSYM vars_to_list_def; GSYM vars_flatten_def; bvl_handleProof_env_rel_def;
              has_var_vars_flatten]);;

(* HOL4 [local] *)
let OptionalLetLet_IMP = prove
 (`!ys l s' nr' y env lx s1 limit nr (s:(A,B)bvl_state) res env1 b extra.
     (ys,l,s',nr') = OptionalLetLet y (LENGTH env) lx s1 limit nr /\
     (!env2 extra. bvl_handleProof_env_rel l env env2 ==>
                   bvl_evaluate ([y],APPEND env2 extra,s) = res) /\
     bvl_handleProof_env_rel l env env1 /\ b ==>
     bvl_evaluate (ys,APPEND env1 extra,s) = res /\ b`,
  RW[OptionalLetLet_def; bvl_evaluate_def] THEN FS[BVLPROPSAUX_env_rel_flatten] THEN
  MATCH_MP_TAC evaluate_LetLet THEN ASM_REWRITE_TAC[]);;

let OptionalLetLet_limit = prove
 (`!ys l s' nr' e env lx s1 limit nr env1.
     (ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr /\
     bvl_handleProof_env_rel l env env1 ==> bvl_handleProof_env_rel lx env env1`,
  RW[OptionalLetLet_def] THEN FS[BVLPROPSAUX_env_rel_flatten]);;

let OptionalLetLet_nr = prove
 (`!ys l s' nr' e (env:bvl_v list) lx s1 limit nr.
     (ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr ==> nr' = nr`,
  RW[OptionalLetLet_def]);;

(* local helpers for compile_correct: the environments of a Let body and of *)
(* a handler (HOL4 proves them inline)                                      *)
let BVLPROPSAUX_env_rel_Shift = prove
 (`!a l2 env env2.
     bvl_handleProof_env_rel (db_vars_Shift (LENGTH a) l2) env env2 ==>
     bvl_handleProof_env_rel l2 (APPEND a env) (APPEND a env2)`,
  REWRITE_TAC[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; LENGTH_APPEND; has_var_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EL_APPEND] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i < a) ==> (i - a) + a = i`] THEN ASM_ARITH_TAC);;

let BVLPROPSAUX_env_rel_CONS = prove
 (`!v l2 env env1. bvl_handleProof_env_rel (db_vars_Shift 1 l2) env env1 ==>
                   bvl_handleProof_env_rel l2 (CONS v env) (CONS v env1)`,
  MESON_TAC[REWRITE_RULE[LENGTH; APPEND; GSYM ONE] (ISPEC `[v:bvl_v]` BVLPROPSAUX_env_rel_Shift)]);;

(* HOL4's first compile_correct, before its specialisation; the last        *)
(* conjunct is HOL4's nr ==> !e. res <> Rerr (Rraise e), stated so that the *)
(* induction hypotheses give no rewrite of every equation res = Rerr        *)
(* (Rraise e) (FS was ten times slower with it)                             *)
let BVLPROPSAUX_compile_correct_gen = prove
 (`!xs env (s1:(A,B)bvl_state) ys env1 res s2 extra l sz nr.
     bvl_handle_compile limit (LENGTH env) xs = (ys,l,sz,nr) /\
     bvl_handleProof_env_rel l env env1 /\
     bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (ys,APPEND env1 extra,s1) = (res,s2) /\
     ((?e. res = Rerr (Rraise e)) ==> ~nr)`,
  let ceqs = env_rel_mk_Union :: all_case_eqs() in
  let gvs thl = FS thl THEN RVEQ_TAC THEN RFS[] in
  let oll_tac extra =
    DRULE OptionalLetLet_IMP THEN DISCH_THEN IRULE THEN FS[] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC OptionalLetLet_limit THEN IMP_RES_TAC OptionalLetLet_nr THEN
    gvs ceqs THEN extra THEN RES_TAC THEN FS[bvl_evaluate_def] in
  SIMP[ONCE EQ_SYM_EQ] THEN REC_IND_TAC (cake_ind "bvl_evaluate") THEN REPEAT CONJ_TAC THEN
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  FS[bvl_handle_compile_def; bvl_evaluate_def] THEN REPEAT PAIRARG_TAC THEN RVEQ_TAC THEN
  FS[env_rel_mk_Union] THEN IMP_RES_TAC bvl_handle_compile_sing THEN RVEQ_TAC THEN
  IMP_RES_TAC bvl_handleProof_env_rel_length THENL
   [(* Cons *) gvs ceqs THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN RES_TAC THEN FS[];
    (* Var *)
    GVS ceqs THEN FS[bvl_evaluate_def; EL_APPEND; ARITH_ss] THEN
    RFS[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; has_var_def];
    (* If *) oll_tac ALL_TAC;
    (* Let *)
    CASES_ON `NULL (xs:bvl_exp list)` THEN FS[NULL_EQ] THEN RVEQ_TAC THENL
     [gvs[bvl_evaluate_def] THEN RES_TAC THEN FS[];
      oll_tac (IMP_RES_TAC bvl_evaluate_IMP_LENGTH THEN RFS[ADD_SYM] THEN
               IMP_RES_TAC BVLPROPSAUX_env_rel_Shift) THEN ASM_MESON_TAC[]];
    (* Raise *) oll_tac ALL_TAC;
    (* Handle *)
    ASM_CASES_TAC `nr1:bool` THEN RFS[ADD1] THEN RVEQ_TAC THENL
     [gvs ceqs THEN RES_TAC THEN FS[];
      SUBGOAL_THEN `~(x:(bvl_v list,bvl_v)result = Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
       [STRIP_TAC THEN gvs[]; RFS[]] THEN
      DRULE evaluate_LetLet THEN
      DISCH_THEN (fun th -> FS[th; bvl_evaluate_def; env_rel_mk_Union]) THEN
      gvs ceqs THEN RES_TAC THEN FS[] THEN ASM_MESON_TAC[BVLPROPSAUX_env_rel_CONS; APPEND]];
    (* Op *)
    CASES_ON `op = clos_ThunkOp ForceThunk` THEN FS[] THENL
     [gvs ceqs THEN RES_TAC THEN FS[bvl_evaluate_def];
      oll_tac ALL_TAC THEN IMP_RES_TAC bvl_do_app_err THEN FS[]];
    (* Tick *) gvs ceqs THEN RES_TAC THEN FS[bvl_evaluate_def];
    (* Force *)
    FS[COND_CASE_EQ] THEN RVEQ_TAC THEN FS[] THEN RFS[bvl_evaluate_def; EL_APPEND; ARITH_ss] THEN
    RVEQ_TAC THEN RFS[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; has_var_def; IMP_IMP] THEN
    FS[];
    (* Call *) oll_tac ALL_TAC]);;

(* HOL4 binds compile_correct three times (allow_rebind): the first is     *)
(* BVLPROPSAUX_compile_correct_gen, the second its instance for env1 = env  *)
(* and extra = [] (used here directly), this is the last                    *)
let bvl_handleProof_compile_correct = prove
 (`!x env (s1:(A,B)bvl_state) res s2 k l.
     bvl_evaluate ([x],env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     k = LENGTH env ==>
     bvl_evaluate ([bvl_handle_compile_exp l k x],env,s1) = (res,s2)`,
  RW[bvl_handle_compile_exp_def] THEN
  QCASES_ON "bvl_handle_compile l (LENGTH env) [handle_simp (bvl_const_compile_exp x)]" THEN
  PAIR_CASES_ON `y:db_var_set#num#bool` THEN IMP_RES_TAC bvl_handle_compile_sing THEN
  RVEQ_TAC THEN DRULE bvl_constProof_evaluate_compile_exp THEN FS[] THEN
  POP_ASSUM MP_TAC THEN SIMP[ONCE (GSYM (CONJUNCT1 evaluate_handle_simp))] THEN STRIP_TAC THEN
  DRULE BVLPROPSAUX_compile_correct_gen THEN
  DISCH_THEN(QSPECL_THEN ["s1"; "env"; "res"; "s2"; "[]"] MP_TAC) THEN FS[env_rel_refl]);;

let dest_Seq_thm = prove
 (`!x y0 y1. bvl_handle_dest_Seq x = SOME (y0,y1) <=> x = bvl_Let [y0; y1] (bvl_Var 1)`,
  REWRITE_TAC[BVLPAUX_dest_Seq_eq; PAIR_EQ] THEN MESON_TAC[]);;

let compile_seqs_correct = prove
 (CASE_TERM `!l x acc (s1:(A,B)bvl_state) s2 s3 res res3.
     bvl_evaluate ([x],[],s1) = (res,s2) /\
     (!y r. acc = SOME y /\ res = Rval r ==>
            ~(res3 = Rerr (Rabort Rtype_error)) /\ bvl_evaluate ([y],[],s2) = (res3,s3)) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([compile_seqs l x acc],[],s1) =
     if acc = NONE then (res,s2) else
       match res with Rval _ -> (res3,s3) | _ -> (res,s2)`,
  (* GVS on the assumptions but the induction hypotheses, which are put   *)
  (* aside meanwhile (GVS simplifies every assumption in each of its      *)
  (* passes: 35 times slower with them here)                              *)
  let gvs_noih thl (asl,w as g) =
    let n = length (filter (fun (_,th) -> is_forall (concl th)) asl) in
    (REPEAT (FIRST_X_ASSUM (MP_TAC o check (is_forall o concl))) THEN
     REPEAT (CHANGED_TAC (GVS_ONE_PASS thl)) THEN EVERY (replicate DISCH_TAC n)) g in
  MATCH_MP_TAC compile_seqs_ind THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN FS[] THENL
   [CASE_TAC THEN FS[] THENL
     [MATCH_MP_TAC bvl_handleProof_compile_correct THEN FS[];
      FS[bvl_evaluate_def] THEN DRULE bvl_handleProof_compile_correct THEN FS[] THEN RW[] THEN
      TOP_CASE_TAC THEN FS[] THEN
      MP_TAC(ISPECL [`[a:bvl_exp]`; `[]:bvl_v list`; `s2:(A,B)bvl_state`]
                    bvl_evaluate_expand_env) THEN FS[]];
    PAIR_CASES_ON `a:bvl_exp#bvl_exp` THEN FS[dest_Seq_thm] THEN RVEQ_TAC THEN
    gvs_noih(bvl_evaluate_def :: all_case_eqs()) THEN IMP_RES_TAC bvl_evaluate_SING THEN
    gvs_noih[] THEN FIRST_X_ASSUM DRULE THEN TRY (FIRST_X_ASSUM DRULE) THEN
    CASES_ON `acc:bvl_exp option` THEN FS[]]);;

(* HOL4 leaves x, env, s1, res, s2, k, split_seq and l free *)
let compile_any_correct = prove
 (`!x env (s1:(A,B)bvl_state) res s2 k split_seq l.
     bvl_evaluate ([x],env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     k = LENGTH env ==>
     bvl_evaluate ([compile_any split_seq l k x],env,s1) = (res,s2)`,
  RW[compile_any_def; bvl_handleProof_compile_correct] THEN FS[LENGTH_EQ_NIL] THEN RW[] THEN
  DRULE compile_seqs_correct THEN DISCH_THEN (QSPECL_THEN ["l"; "NONE"] MP_TAC) THEN FS[]);;

let compile_IMP_LENGTH = prove
 (`!l n xs ys l1 (s1:num#bool).
     bvl_handle_compile l n xs = (ys,l1,s1) ==> LENGTH ys = LENGTH xs`,
  RW[] THEN MP_TAC(SPEC_ALL bvl_handle_compile_length) THEN ASM_SIMP_TAC[]);;

let bVarBound_CONS = prove
 (`!m x xs. bVarBound m [x] /\ bVarBound m xs ==> bVarBound m (CONS x xs)`,
  REPEAT GEN_TAC THEN CASES_ON `xs:bvl_exp list` THEN FS[]);;

let bVarBound_MEM = prove
 (`!n xs. bVarBound n xs <=> !x. MEM x xs ==> bVarBound n [x]`,
  FS[ONCE bVarBound_EVERY; GSYM ALL_MEM]);;

let bEvery_MEM = prove
 (`!p xs. bEvery p xs <=> !x. MEM x xs ==> bEvery p [x]`,
  FS[ONCE bEvery_EVERY; GSYM ALL_MEM]);;

let bVarBound_LESS_EQ = prove
 (`!m xs n. bVarBound m xs /\ m <= n ==> bVarBound n xs`,
  MATCH_MP_TAC bVarBound_ind THEN RW[] THEN FS[ARITH_ss]);;

(* HOL4 also quantifies a vacuous i (of an unconstrained type) and leaves n *)
(* free                                                                      *)
let ALOOKUP_MAPi = prove
 (`!(xs:A list) (i:B) (x:num) (n:A).
     ALOOKUP (MAPi (\i x. (x,i)) xs) n = SOME x ==> x < LENGTH xs`,
  RW[] THEN IMP_RES_TAC ALOOKUP_MEM THEN FS[MEM_MAPi]);;

(* HOL4 [simp] *)
let bVarBound_SmartLet = prove
 (`!m x xs. bVarBound m [SmartLet x xs] <=> bVarBound m [bvl_Let x xs]`,
  RW[SmartLet_def] THEN FS[NULL_EQ]);;
let _ = cake_add_simps [bVarBound_SmartLet];;

let bVarBound_LetLet = prove
 (`!m y n (l1:num_set). bVarBound m [y] /\ n <= m ==> bVarBound m [LetLet n l1 y]`,
  FS[LetLet_def] THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bVarBound_MEM] THEN
  FS[MEM_MAP; MEM_GENLIST; MEM_FILTER; PULL_EXISTS] THEN RW[] THEN EVERY_CASE_TAC THEN
  FS[ARITH_ss] THEN TRY (MATCH_MP_TAC bVarBound_LESS_EQ THEN ASM_EXISTS_TAC) THEN
  IMP_RES_TAC ALOOKUP_MAPi THEN FS[ARITH_ss]);;

let bVarBound_OptionalLetLet = prove
 (`!m e n l s limit nr.
     bVarBound m [e] /\ n <= m ==> bVarBound m (FST (OptionalLetLet e n l s limit nr))`,
  RW[OptionalLetLet_def; bVarBound_LetLet]);;

let bVarBound_compile = prove
 (`!l n xs m. n <= m ==> bVarBound m (FST (bvl_handle_compile l n xs))`,
  MATCH_MP_TAC bvl_handle_compile_ind THEN RW[] THEN FS[bvl_handle_compile_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN IMP_RES_TAC bvl_handle_compile_sing THEN
  RW[] THEN RES_TAC THEN IMP_RES_TAC bVarBound_CONS THEN FS[] THEN TRY DECIDE_TAC THEN
  TRY (MATCH_MP_TAC bVarBound_OptionalLetLet ORELSE MATCH_MP_TAC bVarBound_LetLet) THEN
  IMP_RES_TAC compile_IMP_LENGTH THEN RFS[] THEN TRY DECIDE_TAC THEN
  FIRST_X_ASSUM (QSPECL_THEN ["LENGTH xs"; "m + LENGTH xs"] MP_TAC) THEN FS[] THEN
  DECIDE_TAC);;

let compile_IMP_bVarBound = prove
 (`!l n xs ys l2 (s2:num#bool).
     bvl_handle_compile l n xs = (ys,l2,s2) ==> bVarBound n ys`,
  RW[] THEN MP_TAC(SPECL [`l:num`; `n:num`; `xs:bvl_exp list`; `n:num`] bVarBound_compile) THEN
  ASM_REWRITE_TAC[LE_REFL]);;

let compile_exp_bVarBound = prove
 (`!n l x. bVarBound n [bvl_handle_compile_exp l n x]`,
  RW[bvl_handle_compile_exp_def] THEN
  QCASES_ON "bvl_handle_compile l n [handle_simp (bvl_const_compile_exp x)]" THEN
  PAIR_CASES_ON `y:db_var_set#num#bool` THEN IMP_RES_TAC bvl_handle_compile_sing THEN
  IMP_RES_TAC compile_IMP_bVarBound THEN FS[]);;

let compile_seqs_bVarBound = prove
 (`!l x acc. (!y. acc = SOME y ==> bVarBound 0 [y]) ==>
             bVarBound 0 [compile_seqs l x acc]`,
  MATCH_MP_TAC compile_seqs_ind THEN RW[] THEN ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN FS[] THENL
   [CASE_TAC THEN FS[compile_exp_bVarBound] THEN MATCH_MP_TAC bVarBound_LESS_EQ THEN
    ASM_EXISTS_TAC THEN FS[];
    PAIR_CASES_ON `a:bvl_exp#bvl_exp` THEN FS[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FS[]]);;

let bEvery_CONS = prove
 (`!p x xs. bEvery p [x] /\ bEvery p xs ==> bEvery p (CONS x xs)`,
  REPEAT GEN_TAC THEN CASES_ON `xs:bvl_exp list` THEN FS[]);;

let handle_ok_Var_Const_list = prove
 (`!xs. ALL (\x. ?v i. x = bvl_Var v \/ x = bvl_Op (IntOp (clos_Const i)) []) xs ==>
        handle_ok xs`,
  LIST_INDUCT_TAC THEN FS[handle_ok_def; PULL_EXISTS] THEN RW[] THEN
  CASES_ON `t:bvl_exp list` THEN FS[handle_ok_def]);;

let handle_ok_SmartLet = prove
 (`!xs x. handle_ok [SmartLet xs x] <=> handle_ok xs /\ handle_ok [x]`,
  RW[SmartLet_def; handle_ok_def] THEN FS[NULL_EQ; LENGTH_EQ_NIL; handle_ok_def]);;

(* a local helper: LetLet makes a Let of variables whose body only uses the *)
(* bound variables (HOL4 proves it inline, in handle_ok_OptionalLetLet and  *)
(* in compile_handle_ok)                                                    *)
let BVLPROPSAUX_LetLet_handle_ok = prove
 (`!n (fvs:A spt) e.
     handle_ok [e] /\ bVarBound n [e] ==>
     ?xs b. LetLet n fvs e = bvl_Let xs b /\ ALL isVar xs /\
            bVarBound (LENGTH xs) [b] /\ handle_ok [b]`,
  RW[LetLet_def; handle_ok_SmartLet] THEN REPEAT CONJ_TAC THENL
   [FS[ALL_MAP; o_DEF; isVar_def; ALL_T];
    ONCE_REWRITE_TAC[bVarBound_MEM] THEN FS[MEM_GENLIST; PULL_EXISTS] THEN RW[] THEN
    EVERY_CASE_TAC THEN FS[] THEN IMP_RES_TAC ALOOKUP_MAPi THEN FS[];
    MATCH_MP_TAC bVarBound_LESS_EQ THEN ASM_EXISTS_TAC THEN DECIDE_TAC;
    MATCH_MP_TAC handle_ok_Var_Const_list THEN RW[GSYM ALL_MEM; MEM_GENLIST] THEN
    EVERY_CASE_TAC THEN MESON_TAC[]]);;

let handle_ok_OptionalLetLet = prove
 (`!e n lx s l nr. handle_ok [e] /\ bVarBound n [e] ==>
                   handle_ok (FST (OptionalLetLet e n lx s l nr))`,
  RW[OptionalLetLet_def] THEN
  MP_TAC(ISPECL [`n:num`; `db_to_set lx`; `e:bvl_exp`] BVLPROPSAUX_LetLet_handle_ok) THEN
  RW[] THEN FS[handle_ok_def; let_ok_def]);;

let compile_handle_ok = prove
 (`!l n xs. handle_ok (FST (bvl_handle_compile l n xs))`,
  MATCH_MP_TAC bvl_handle_compile_ind THEN RW[] THEN FS[bvl_handle_compile_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN IMP_RES_TAC bvl_handle_compile_sing THEN
  RW[] THEN RES_TAC THEN FS[handle_ok_def] THEN
  TRY (CASES_ON `dy:bvl_exp list` THEN FS[handle_ok_def] THEN NO_TAC) THEN
  IMP_RES_TAC compile_IMP_bVarBound THEN IMP_RES_TAC compile_IMP_LENGTH THEN
  TRY (MATCH_MP_TAC handle_ok_OptionalLetLet THEN RFS[handle_ok_def; NULL_EQ; LENGTH_EQ_NIL]) THENL
   [(* Let *)
    FIRST_X_ASSUM (QSPEC_THEN "LENGTH xs" MP_TAC) THEN RW[] THEN FS[] THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM `LENGTH:bvl_exp list->num`) THEN FS[LENGTH_EQ_NIL];
    (* Handle *)
    MP_TAC(ISPECL [`n:num`; `db_to_set l1`; `y':bvl_exp`] BVLPROPSAUX_LetLet_handle_ok) THEN
    RW[] THEN FS[]]);;

let compile_exp_handle_ok = prove
 (`!l n x. handle_ok [bvl_handle_compile_exp l n x]`,
  RW[bvl_handle_compile_exp_def] THEN
  QCASES_ON "bvl_handle_compile l n [handle_simp (bvl_const_compile_exp x)]" THEN
  PAIR_CASES_ON `y:db_var_set#num#bool` THEN IMP_RES_TAC bvl_handle_compile_sing THEN
  MP_TAC(SPECL [`l:num`; `n:num`; `[handle_simp (bvl_const_compile_exp x)]`]
               compile_handle_ok) THEN FS[]);;

(* HOL4 rewrites with handle_ok_def in fs; SIMP with handle_ok_def overflows *)
(* the stack on handle_ok [Let [b] (Let [] (Let [] a))], so REWRITE_TAC     *)
let compile_seqs_handle_ok = prove
 (`!l x acc. (!y. acc = SOME y ==> handle_ok [y] /\ bVarBound 0 [y]) ==>
             handle_ok [compile_seqs l x acc]`,
  MATCH_MP_TAC compile_seqs_ind THEN RW[] THEN ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN FS[] THENL
   [CASE_TAC THEN REWRITE_TAC[handle_ok_def; compile_exp_handle_ok; LENGTH; NOT_SUC] THEN
    FS[let_ok_def];
    PAIR_CASES_ON `a:bvl_exp#bvl_exp` THEN FS[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FS[compile_seqs_bVarBound]]);;

let compile_any_handle_ok = prove
 (`!split_seq l n x. handle_ok [compile_any split_seq l n x]`,
  RW[compile_any_def; compile_exp_handle_ok] THEN MATCH_MP_TAC compile_seqs_handle_ok THEN
  FS[]);;

let handle_ok_CONS = prove
 (`!x xs. handle_ok (CONS x xs) <=> handle_ok [x] /\ handle_ok xs`,
  REPEAT GEN_TAC THEN CASES_ON `xs:bvl_exp list` THEN FS[handle_ok_def]);;

let handle_ok_EVERY = prove
 (`!xs. handle_ok xs <=> ALL (\x. handle_ok [x]) xs`,
  LIST_INDUCT_TAC THEN FS[handle_ok_def] THEN SIMP[ONCE handle_ok_CONS] THEN FS[]);;

(* HOL4 [simp] *)
let LetLet_code_labels = prove
 (`!x (y:A spt) z. bvl_get_code_labels (LetLet x y z) = bvl_get_code_labels z`,
  SUBGOAL_THEN (CASE_TERM `!opt. bvl_get_code_labels (match opt with
      NONE -> bvl_Op (IntOp (clos_Const (&0))) [] | SOME (k:num) -> bvl_Var k) = {}`)
    ASSUME_TAC THENL [GEN_TAC THEN CASES_ON `opt:num option` THEN FS BVLPROPSAUX_LABELS_RWS;
                      ALL_TAC] THEN
  RW[LetLet_def; SmartLet_def] THEN
  SIMP([MAP_MAP_o; o_DEF; MAP_GENLIST; ONCE EXTENSION; IN_UNION; IN_UNIONS; IN_SET_OF_LIST;
        MEM_MAP; MEM_GENLIST; NOT_IN_EMPTY; PULL_EXISTS] @ BVLPROPSAUX_LABELS_RWS));;
let _ = cake_add_simps [LetLet_code_labels];;

let bvl_handleProof_compile_code_labels = prove
 (`!a b c. UNIONS (set_of_list (MAP bvl_get_code_labels (FST (bvl_handle_compile a b c))))
           SUBSET UNIONS (set_of_list (MAP bvl_get_code_labels c))`,
  MATCH_MP_TAC bvl_handle_compile_ind THEN RW[bvl_handle_compile_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN IMP_RES_TAC bvl_handle_compile_sing THEN RVEQ_TAC THEN
  FS[NULL_EQ] THEN RW[OptionalLetLet_def] THEN
  FS([UNIONS_UNION; UNIONS_1; MAP_APPEND; SET_OF_LIST_APPEND] @ BVLPROPSAUX_LABELS_RWS) THEN
  TRY (FIRST_X_ASSUM (QSPEC_THEN "LENGTH xs" MP_TAC) THEN RFS[]) THEN
  FS[SUBSET; IN_UNION] THEN RW[] THEN RES_TAC THEN FS[]);;

(* HOL4 [local] *)
let get_code_labels_dest_handle_Raise = prove
 (`!c x. dest_handle_Raise c = SOME x ==> bvl_get_code_labels c = bvl_get_code_labels x`,
  RW[BVLPAUX_dest_handle_Raise_eq] THEN FS BVLPROPSAUX_LABELS_RWS);;

(* HOL4 [local] *)
let get_code_labels_handle_adj_vars = prove
 (`(!x d l. bvl_get_code_labels (handle_adj_vars d l x) = bvl_get_code_labels x) /\
   (!x d l. MAP bvl_get_code_labels (handle_adj_vars1 d l x) =
            MAP bvl_get_code_labels x)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN FS(handle_adj_vars_def :: BVLPROPSAUX_LABELS_RWS));;

let get_code_labels_handle_simp = prove
 (`(!c. bvl_get_code_labels (handle_simp c) SUBSET bvl_get_code_labels c) /\
   (!c. UNIONS (set_of_list (MAP bvl_get_code_labels (handle_simp_list c))) SUBSET
        UNIONS (set_of_list (MAP bvl_get_code_labels c))) /\
   (!c d l. bvl_get_code_labels (make_handle c d l) SUBSET
            bvl_get_code_labels c UNION bvl_get_code_labels d)`,
  let lbls = get_code_labels_handle_adj_vars :: BVLPROPSAUX_LABELS_RWS in
  let fin = FS[SUBSET; IN_UNION] THEN RW[] THEN RES_TAC THEN FS[] in
  MATCH_MP_TAC handle_simp_ind THEN RW[] THEN ONCE_REWRITE_TAC[handle_simp_def] THEN
  FS BVLPROPSAUX_LABELS_RWS THENL [fin; fin; fin; fin; fin; ALL_TAC] THEN
  CASES_ON `dest_handle_Raise c` THEN FS[] THENL
   [ALL_TAC; FS[BVLPAUX_dest_handle_Raise_eq] THEN RVEQ_TAC THEN FS lbls THEN fin] THEN
  CASES_ON `dest_handle_Let c` THEN FS[] THENL
   [ALL_TAC; FS[BVLPAUX_dest_handle_Let_eq] THEN RVEQ_TAC THEN FS lbls THEN fin] THEN
  CASES_ON `dest_handle_If c` THEN FS[] THEN
  TRY (FS[BVLPAUX_dest_handle_If_eq] THEN RVEQ_TAC) THEN FS lbls THEN fin);;

let bvl_handleProof_compile_exp_code_labels = prove
 (`!a b c. bvl_get_code_labels (bvl_handle_compile_exp a b c) SUBSET
           bvl_get_code_labels c`,
  RW[bvl_handle_compile_exp_def] THEN
  QCASES_ON "bvl_handle_compile a b [handle_simp (bvl_const_compile_exp c)]" THEN
  PAIR_CASES_ON `y:db_var_set#num#bool` THEN IMP_RES_TAC bvl_handle_compile_sing THEN RVEQ_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`; `[handle_simp (bvl_const_compile_exp c)]`]
               bvl_handleProof_compile_code_labels) THEN
  MP_TAC(SPEC `bvl_const_compile_exp c` (CONJUNCT1 get_code_labels_handle_simp)) THEN
  MP_TAC(SPEC `c:bvl_exp` bvl_constProof_compile_exp_code_labels) THEN
  FS BVLPROPSAUX_LABELS_RWS THEN MESON_TAC[SUBSET_TRANS]);;

let compile_seqs_code_labels = prove
 (CASE_TERM `!cut e acc.
     bvl_get_code_labels (compile_seqs cut e acc) SUBSET
     bvl_get_code_labels e UNION
     (match acc with NONE -> {} | SOME r -> bvl_get_code_labels r)`,
  MATCH_MP_TAC compile_seqs_ind THEN RW[] THEN ONCE_REWRITE_TAC[compile_seqs_def] THEN
  REPEAT TOP_CASE_TAC THEN FS[dest_Seq_thm] THEN RW[] THEN
  MP_TAC(SPECL [`cut_size:num`; `0`; `e:bvl_exp`] bvl_handleProof_compile_exp_code_labels) THEN
  FS(SUBSET :: IN_UNION :: BVLPROPSAUX_LABELS_RWS) THEN ASM_MESON_TAC[]);;
