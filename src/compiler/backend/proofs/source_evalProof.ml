(* ========================================================================= *)
(* source_evalProof: port of HOL4 compiler/backend/proofs/                   *)
(* source_evalProofScript.sml (CakeML v3479).  Proofs that the eval mode of  *)
(* the source semantics can be switched to one that includes an oracle.     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 removes getOpClass_def from its simpset for this theory           *)
(*   (temp_delsimps); the kit has no file-local deletion (cake_del_simps     *)
(*   acts everywhere), so the proofs here live with it.                      *)
(* - The type variable of compiler_instance (HOL4 config) is C.              *)
(* - HOL4 paired lambdas over tuples are written as matches (pair_CASE).    *)
(* - SEVPAUX_ names are local helpers.                                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/string4.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semantics.ml";;

type_invention_error := true;;

(* The things the translator is expected to produce from the compiler       *)
(* definition etc.                                                           *)

let compiler_instance_INFO = cake_record "compiler_instance"
  ["compiler_fun","(num#num)#C#dec list->(C#byte list#int64 list)option";
   "config_v","C->v";
   "config_dom","C->bool";
   "decs_v","dec list->v";
   "decs_dom","dec list->bool";
   "init_state","C"];;

let compiler_instance_component_equality =
  compiler_instance_INFO.ri_component_equality;;

(* HOL4: v_rel_abs *)
let v_fun_abs_def = cake_def
  `v_fun_abs (fun_dom:A->bool) (fun_v:A->v) v = (some x. fun_v x = v /\ x IN fun_dom)`;;

let mk_compiler_fun_from_ci_def = cake_def
  `mk_compiler_fun_from_ci (ci:(C)compiler_instance) (env_id,cfg_v,decs) =
     OPTION_BIND (v_fun_abs (compiler_instance_config_dom ci)
                    (compiler_instance_config_v ci) cfg_v)
       (\cfg. OPTION_BIND (compiler_instance_compiler_fun ci (env_id,cfg,decs))
                (\p. match p with
                       (cfg2,bs,ws) -> SOME (compiler_instance_config_v ci cfg2,bs,ws)))`;;

let mk_init_eval_state_def = cake_def
  `mk_init_eval_state (ci:(C)compiler_instance) =
     EvalDecs (eval_decs_state_REC (mk_compiler_fun_from_ci ci)
                 (compiler_instance_config_v ci (compiler_instance_init_state ci))
                 (0,0,1)
                 (v_fun_abs (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci)))`;;

(* an instance of custom_do_eval that behaves as much as possible like the  *)
(* no-oracle semantics                                                       *)

let v_to_nat_def = cake_def
  `v_to_nat v =
     match v with
       Litv (IntLit i) -> (if &0 <= i then SOME (num_of_int i) else NONE)
     | _ -> NONE`;;

let v_to_env_id_def = cake_def
  `v_to_env_id v =
     match v with
       Conv NONE [gen_id_v; id_v] ->
         (match (v_to_nat gen_id_v,v_to_nat id_v) with
            (SOME gen_id,SOME eid) -> SOME (gen_id,eid)
          | _ -> NONE)
     | _ -> NONE`;;

let do_eval_record_def = cake_def
  `do_eval_record (ci:(C)compiler_instance) vs (orac:eval_oracle_fun) =
     match vs with
       [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] ->
         (match orac 0 with
            ((i,_),st,_) ->
              (match (v_to_env_id env_id_v,
                      v_fun_abs (compiler_instance_decs_dom ci)
                        (compiler_instance_decs_v ci) decs_v) with
                 (SOME env_id,SOME decs) ->
                   if compiler_agrees (mk_compiler_fun_from_ci ci)
                        (env_id,st_v,decs) (st_v2,bs_v,ws_v) /\ st_v = st
                   then
                     let orac' = \j. if j = 0 then ((i + 1,0),st_v2,[])
                                     else if j = SUC i then (env_id,st,decs)
                                     else orac j in
                     SOME (env_id,orac',decs)
                   else NONE
               | _ -> NONE))
     | _ -> NONE`;;

(* a somewhat generic env rel *)

let source_evalProof_env_rel_def = cake_def
  `source_evalProof_env_rel (v_rel:v->v->bool) (env:v sem_env) env' <=>
     sem_env_c env = sem_env_c env' /\
     nsDom (sem_env_v env) = nsDom (sem_env_v env') /\
     nsDomMod (sem_env_v env) = nsDomMod (sem_env_v env') /\
     (!nm x y. nsLookup (sem_env_v env) nm = SOME x /\
               nsLookup (sem_env_v env') nm = SOME y ==> v_rel x y)`;;

let env_rel_mono_rel = prove
 (`(!y z. R y z ==> R' y z) ==>
   source_evalProof_env_rel R env env' ==> source_evalProof_env_rel R' env env'`,
  REWRITE_TAC[source_evalProof_env_rel_def] THEN MESON_TAC[]);;

(* HOL4 IndDefLib.add_mono_thm *)
let () = monotonicity_theorems := env_rel_mono_rel :: !monotonicity_theorems;;

(* local: does a theorem mention the constant named s *)
let SEVPAUX_has_const s th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = s)) (concl th);;
let env_rel_add_nsBind = prove
 (`source_evalProof_env_rel R (sem_env_v_fupd (K ev) env) (sem_env_v_fupd (K ev') env') /\
   R x y ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsBind n x ev)) env)
     (sem_env_v_fupd (K (nsBind n y ev')) env')`,
  RW[source_evalProof_env_rel_def] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "nsBind"))) THEN
  ASM_CASES_TAC `nm = Short n:(mlstring,mlstring)id` THEN
  ASM_SIMP_TAC[nsLookup_nsBind; option_INJ] THEN ASM_MESON_TAC[]);;

let env_rel_add_nsBindList = prove
 (`!(xs:(mlstring#v)list) ys.
     source_evalProof_env_rel R (sem_env_v_fupd (K ev) env) (sem_env_v_fupd (K ev') env') /\
     ALL2 ((=) ### R) xs ys ==>
     source_evalProof_env_rel R (sem_env_v_fupd (K (nsBindList xs ev)) env)
       (sem_env_v_fupd (K (nsBindList ys ev')) env')`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; nsBindList_def; ITLIST] THEN
  REWRITE_TAC[GSYM nsBindList_def] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`h':mlstring#v`; `h:mlstring#v`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_REL_THM; pair_CASE] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC env_rel_add_nsBind THEN
  ASM_MESON_TAC[]);;


let env_rel_nsLift = prove
 (`source_evalProof_env_rel R (sem_env_v_fupd (K v) (sem_env_c_fupd (K c) env))
     (sem_env_v_fupd (K v') (sem_env_c_fupd (K c') env')) ==>
   source_evalProof_env_rel R
     (sem_env_v_fupd (K (nsLift mn v)) (sem_env_c_fupd (K (nsLift mn c)) env))
     (sem_env_v_fupd (K (nsLift mn v')) (sem_env_c_fupd (K (nsLift mn c')) env'))`,
  RW[source_evalProof_env_rel_def; nsDom_nsLift; nsDomMod_nsLift] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "nsLift"))) THEN
  REWRITE_TAC[nsLookup_nsLift] THEN EVERY_CASE_TAC THEN ASM_MESON_TAC[]);;

let env_rel_nsEmpty = prove
 (`(!env'. source_evalProof_env_rel R (sem_env_v_fupd (K nsEmpty) x) env' <=>
           sem_env_c x = sem_env_c env' /\
           nsDom (nsEmpty:(mlstring,mlstring,v)namespace) = nsDom (sem_env_v env') /\
           nsDomMod (nsEmpty:(mlstring,mlstring,v)namespace) =
           nsDomMod (sem_env_v env')) /\
   (source_evalProof_env_rel R x (sem_env_v_fupd (K nsEmpty) y) <=>
      sem_env_c x = sem_env_c y /\
      nsDom (sem_env_v x) = nsDom (nsEmpty:(mlstring,mlstring,v)namespace) /\
      nsDomMod (sem_env_v x) = nsDomMod (nsEmpty:(mlstring,mlstring,v)namespace))`,
  REWRITE_TAC[source_evalProof_env_rel_def; sem_env_INFO.ri_accfupds; K_THM;
              nsLookup_nsEmpty; option_DISTINCT]);;
let _ = cake_add_simps (CONJUNCTS env_rel_nsEmpty);;

let env_rel_nsAppend = prove
 (`source_evalProof_env_rel R (sem_env_v_fupd (K a) env) (sem_env_v_fupd (K c) env') /\
   source_evalProof_env_rel R (sem_env_v_fupd (K b) env) (sem_env_v_fupd (K d) env') ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsAppend a b)) env)
     (sem_env_v_fupd (K (nsAppend c d)) env')`,
  RW[source_evalProof_env_rel_def] THEN
  TRY(MP_TAC(ISPECL [`a:(mlstring,mlstring,v)namespace`; `b:(mlstring,mlstring,v)namespace`;
                     `c:(mlstring,mlstring,v)namespace`; `d:(mlstring,mlstring,v)namespace`]
                    nsDom_nsAppend_equal) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "nsAppend"))) THEN
  REWRITE_TAC[nsLookup_nsAppend_some] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `nm:(mlstring,mlstring)id` o
    REWRITE_RULE[EXTENSION; nsLookup_nsDom] o
    check (fun th -> concl th = `nsDom (a:(mlstring,mlstring,v)namespace) =
                                 nsDom (c:(mlstring,mlstring,v)namespace)`)) THEN
  ASM_MESON_TAC[option_DISTINCT]);;

let env_rel_extend_dec_env = prove
 (`source_evalProof_env_rel R env1 env2 /\ source_evalProof_env_rel R env3 env4 ==>
   source_evalProof_env_rel R (extend_dec_env env1 env3) (extend_dec_env env2 env4)`,
  STRIP_TAC THEN REWRITE_TAC[extend_dec_env_def] THEN
  MP_TAC(INST [`sem_env_v (env1:v sem_env)`,`a:(mlstring,mlstring,v)namespace`;
               `sem_env_v (env3:v sem_env)`,`b:(mlstring,mlstring,v)namespace`;
               `sem_env_v (env2:v sem_env)`,`c:(mlstring,mlstring,v)namespace`;
               `sem_env_v (env4:v sem_env)`,`d:(mlstring,mlstring,v)namespace`;
               `sem_env_REC (ARB:(mlstring,mlstring,v)namespace)
                  (nsAppend (sem_env_c (env1:v sem_env)) (sem_env_c (env3:v sem_env)))`,`env:v sem_env`;
               `sem_env_REC (ARB:(mlstring,mlstring,v)namespace)
                  (nsAppend (sem_env_c (env2:v sem_env)) (sem_env_c (env4:v sem_env)))`,`env':v sem_env`]
          env_rel_nsAppend) THEN
  REWRITE_TAC[sem_env_INFO.ri_fupds; K_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[source_evalProof_env_rel_def; sem_env_INFO.ri_accfupds;
              sem_env_INFO.ri_accessors; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let env_rel_nsLookup_v = prove
 (`source_evalProof_env_rel R env env' /\ nsLookup (sem_env_v env) eid = SOME v ==>
   ?v'. nsLookup (sem_env_v env') eid = SOME v' /\ R v v'`,
  REWRITE_TAC[source_evalProof_env_rel_def; EXTENSION; nsLookup_nsDom] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let env_rel_nsLookup_c = prove
 (`source_evalProof_env_rel R env env' /\ nsLookup (sem_env_c env) eid = r ==>
   sem_env_c env' = sem_env_c env`,
  SIMP_TAC[source_evalProof_env_rel_def]);;

(* various trivia *)

(* HOL4 [local] *)
let alist_to_ns_to_bind2 = prove
 (`!l:(N#V)list. alist_to_ns l = nsBindList l (nsEmpty:(M,N,V)namespace)`,
  REWRITE_TAC[GSYM nsAppend_to_nsBindList; nsAppend_nsEmpty]);;

(* HOL4 [local] *)
let nsSing_eq_bind = prove
 (`!(n:N) (x:V). nsSing n x = nsBind n x (nsEmpty:(M,N,V)namespace)`,
  REWRITE_TAC[nsSing_def; nsBind_def; nsEmpty_def]);;

(* HOL4 [local] *)
let pair_CASE_eq_pairarg = prove
 (`pair_CASE (p:A#B) (f:A->B->C) = (\(x,y). f x y) p`,
  SPEC_TAC(`p:A#B`,`p:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* first step: switch over to recording semantics and move envs out of Env *)
(* values and into the state                                                *)

let source_evalProof_v_rel_rules,source_evalProof_v_rel_ind,
    source_evalProof_v_rel_cases,source_evalProof_v_rel_strongind = cake_inductive
  `(!es env eid v. (!env'. v_to_env_id v = SOME eid /\ lookup_env es eid = SOME env' /\
                          source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
                          source_evalProof_v_rel es (Env env eid) v)) /\
   (!es xs ys. ALL2 (source_evalProof_v_rel es) xs ys ==>
               source_evalProof_v_rel es (Vectorv xs) (Vectorv ys)) /\
   (!es xs ys stmp. ALL2 (source_evalProof_v_rel es) xs ys ==>
                    source_evalProof_v_rel es (Conv stmp xs) (Conv stmp ys)) /\
   (!es env env' nm x. source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
                       source_evalProof_v_rel es (Closure env nm x) (Closure env' nm x)) /\
   (!es env env' funs nm. source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
                          source_evalProof_v_rel es (Recclosure env funs nm)
                            (Recclosure env' funs nm)) /\
   (!es l. source_evalProof_v_rel es (Litv l) (Litv l)) /\
   (!es br n. source_evalProof_v_rel es (Loc br n) (Loc br n))`;;

let v_rel_l_simps = prove
 (`(!es l v. source_evalProof_v_rel es (Litv l) v <=> v = Litv l) /\
   (!es cn vs v. source_evalProof_v_rel es (Conv cn vs) v <=>
                 ?ys. v = Conv cn ys /\ ALL2 (source_evalProof_v_rel es) vs ys) /\
   (!es b l v. source_evalProof_v_rel es (Loc b l) v <=> v = Loc b l) /\
   (!es vs v. source_evalProof_v_rel es (Vectorv vs) v <=>
              ?ys. v = Vectorv ys /\ ALL2 (source_evalProof_v_rel es) vs ys) /\
   (!es e eid v. source_evalProof_v_rel es (Env e eid) v <=>
                ?env'. v_to_env_id v = SOME eid /\ lookup_env es eid = SOME env' /\
                       source_evalProof_env_rel (source_evalProof_v_rel es) e env') /\
   (!es env funs nm v. source_evalProof_v_rel es (Recclosure env funs nm) v <=>
                ?env'. v = Recclosure env' funs nm /\
                       source_evalProof_env_rel (source_evalProof_v_rel es) env env') /\
   (!es env nm x v. source_evalProof_v_rel es (Closure env nm x) v <=>
                ?env'. v = Closure env' nm x /\
                       source_evalProof_env_rel (source_evalProof_v_rel es) env env')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [source_evalProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "v"; injectivity "v"] THEN MESON_TAC[]);;

let source_evalProof_v_rel_Boolv = prove
 (`source_evalProof_v_rel es (Boolv b) v <=> v = Boolv b`,
  REWRITE_TAC[semanticPrimitives_Boolv_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[v_rel_l_simps; ALL2_DEF] THEN MESON_TAC[]);;

let _ = cake_add_simps [v_rel_l_simps; source_evalProof_v_rel_Boolv];;

let recorded_orac_wf_def = cake_def
  `recorded_orac_wf (compiler:compiler_args->(v#B)option) (orac:eval_oracle_fun) <=>
     (0 < FST (FST (orac 0)) ==>
      ?r. compiler (orac (FST (FST (orac 0)))) = SOME r /\
          FST (SND (orac 0)) = FST r) /\
     (!j. j < FST (FST (orac 0)) /\ 0 < j ==>
          ?r. compiler (orac j) = SOME r /\ FST (SND (orac (j + 1))) = FST r)`;;

(* the bound oracle state is oracle_s (HOL4 orac_s; orac_s is a constant   *)
(* defined below)                                                          *)
let source_evalProof_s_rel_def = cake_def
  `source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) s' <=>
     ?dec_s oracle_s refs'.
       s' = state_refs_fupd (K refs')
              (state_eval_state_fupd (K (SOME (EvalOracle oracle_s))) s) /\
       ALL2 (sv_rel (source_evalProof_v_rel oracle_s)) (state_refs s) refs' /\
       state_eval_state s = SOME (EvalDecs dec_s) /\
       eval_oracle_state_custom_do_eval oracle_s = do_eval_record ci /\
       eval_decs_state_compiler_state dec_s =
         FST (SND (eval_oracle_state_oracle oracle_s 0)) /\
       eval_decs_state_decode_decs dec_s =
         v_fun_abs (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci) /\
       eval_decs_state_compiler dec_s = mk_compiler_fun_from_ci ci /\
       (0 = FST (FST (eval_oracle_state_oracle oracle_s 0)) ==>
        eval_decs_state_compiler_state dec_s =
          compiler_instance_config_v ci (compiler_instance_init_state ci)) /\
       (0 < FST (FST (eval_oracle_state_oracle oracle_s 0)) ==>
        FST (SND (eval_oracle_state_oracle oracle_s 1)) =
          compiler_instance_config_v ci (compiler_instance_init_state ci)) /\
       eval_decs_state_env_id_counter dec_s =
         (eval_oracle_state_generation oracle_s,
          LENGTH (EL (eval_oracle_state_generation oracle_s)
                     (eval_oracle_state_envs oracle_s)),
          LENGTH (eval_oracle_state_envs oracle_s)) /\
       eval_oracle_state_generation oracle_s < LENGTH (eval_oracle_state_envs oracle_s) /\
       recorded_orac_wf (mk_compiler_fun_from_ci ci) (eval_oracle_state_oracle oracle_s)`;;

let orac_s_def = cake_def
  `(orac_s (SOME (EvalOracle es)) = es) /\
   (orac_s _ = ARB "not EvalOracle")`;;
let _ = cake_add_simps [orac_s_def];;

let es_forward_def = cake_def
  `es_forward es es' <=>
     LENGTH (eval_oracle_state_envs es) <= LENGTH (eval_oracle_state_envs es') /\
     (!env_id env. lookup_env es env_id = SOME env ==>
                   lookup_env es' env_id = SOME env)`;;

let es_forward_refl = prove
 (`es_forward es es`,
  SIMP[es_forward_def]);;

let es_forward_trans = prove
 (`es_forward es es' /\ es_forward es' es'' ==> es_forward es es''`,
  REWRITE_TAC[es_forward_def] THEN MESON_TAC[LE_TRANS]);;


let SEVPAUX_MONO_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "ALL2")) THEN
      MATCH_MP_TAC MONO_ALL2 THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "source_evalProof_env_rel")) THEN
      MATCH_MP_TAC env_rel_mono_rel THEN ASM_SIMP_TAC[] THEN NO_TAC);;

let v_rel_forward = prove
 (`!x y. source_evalProof_v_rel es x y ==> es_forward es es' ==>
         source_evalProof_v_rel es' x y`,
  SUBGOAL_THEN
   `!es x y. source_evalProof_v_rel es x y ==>
             (es_forward es es' ==> source_evalProof_v_rel es' x y)`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC source_evalProof_v_rel_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[v_rel_l_simps; injectivity "v"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(EXISTS_TAC `env':v sem_env` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[es_forward_def]; SEVPAUX_MONO_TAC] THEN NO_TAC) THEN
  SEVPAUX_MONO_TAC);;

let forward_rules = prove
 (`(source_evalProof_v_rel es x y /\ es_forward es es' ==>
    source_evalProof_v_rel es' x y) /\
   (ALL2 (source_evalProof_v_rel es) xs ys /\ es_forward es es' ==>
    ALL2 (source_evalProof_v_rel es') xs ys) /\
   (source_evalProof_env_rel (source_evalProof_v_rel es) env env' /\ es_forward es es' ==>
    source_evalProof_env_rel (source_evalProof_v_rel es') env env') /\
   (!xs ys. ALL2 (sv_rel (source_evalProof_v_rel es)) xs ys /\ es_forward es es' ==>
            ALL2 (sv_rel (source_evalProof_v_rel es')) xs ys)`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[v_rel_forward];
    FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "ALL2")) THEN
    MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[v_rel_forward];
    FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "source_evalProof_env_rel")) THEN
    MATCH_MP_TAC env_rel_mono_rel THEN ASM_MESON_TAC[v_rel_forward];
    FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "ALL2")) THEN
    MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN MATCH_MP_TAC sv_rel_mono THEN
    ASM_MESON_TAC[v_rel_forward]]);;

(* a stronger notion that applies end-to-end over evaluate/evaluate_decs,  *)
(* where the generation stack will match at either end and the previous    *)
(* generations will be untouched                                           *)

let es_stack_forward_def = cake_def
  `es_stack_forward es es' <=>
     eval_oracle_state_generation es' = eval_oracle_state_generation es /\
     (!j. j < eval_oracle_state_generation es ==>
          EL j (eval_oracle_state_envs es') = EL j (eval_oracle_state_envs es))`;;

let es_stack_forward_refl = prove
 (`es_stack_forward es es`,
  SIMP[es_stack_forward_def]);;

let es_stack_forward_trans = prove
 (`es_stack_forward es1 es2 /\ es_stack_forward es2 es3 ==> es_stack_forward es1 es3`,
  SIMP[es_stack_forward_def]);;

let source_evalProof_match_result_rel_def = cake_def
  `source_evalProof_match_result_rel nerr (R:A->B->bool) mr1 mr2 <=>
     match mr1 with
       No_match -> mr2 = No_match
     | Match_type_error -> nerr \/ mr2 = Match_type_error
     | Match x -> ?y. mr2 = Match y /\ R x y`;;

let store_lookup_rel = prove
 (`ALL2 (sv_rel (R:A->B->bool)) refs refs' ==>
   OPTREL (sv_rel R) (store_lookup i refs) (store_lookup i refs')`,
  REWRITE_TAC[store_lookup_def; LIST_REL_EL_EQN] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[OPTREL_THM]);;

let s_rel_store_lookup = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\ j = i /\
   es = orac_s (state_eval_state t) ==>
   OPTREL (sv_rel (source_evalProof_v_rel es)) (store_lookup i (state_refs s))
     (store_lookup j (state_refs t))`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def] THEN
  MATCH_MP_TAC store_lookup_rel THEN ASM_REWRITE_TAC[]);;

let v_to_nat_SOME = prove
 (`v_to_nat v = SOME n ==> v = nat_to_v n`,
  REWRITE_TAC[v_to_nat_def; nat_to_v_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; injectivity "v"; injectivity "lit"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let v_to_env_id_SOME = prove
 (`v_to_env_id v = SOME eid ==> v = Conv NONE [nat_to_v (FST eid); nat_to_v (SND eid)]`,
  REWRITE_TAC[v_to_env_id_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FST; SND] THEN ASM_MESON_TAC[v_to_nat_SOME]);;

let SEVPAUX_is_var_eq th =
  let c = concl th in is_eq c && is_var(lhs c) && not (fst(dest_var(lhs c)) = "es");;

let SEVPAUX_mrr_T = prove
 (`source_evalProof_match_result_rel T (R:A->B->bool) a b <=>
   (a = No_match ==> b = No_match) /\ (!x. a = Match x ==> ?y. b = Match y /\ R x y)`,
  STRUCT_CASES_TAC(ISPEC `a:(A)match_result` (cases "match_result")) THEN
  REWRITE_TAC[source_evalProof_match_result_rel_def; distinctness "match_result";
              injectivity "match_result"] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let SEVPAUX_pm_cons = prove
 (CASE_TERM `!(R:A->B->bool) a1 b1 (f:A->(A)match_result) (g:B->(B)match_result) e1 e2.
     source_evalProof_match_result_rel T R a1 b1 /\
     (a1 = No_match ==> source_evalProof_match_result_rel T R (f e1) (g e2)) /\
     (!x y. a1 = Match x /\ R x y ==> source_evalProof_match_result_rel T R (f x) (g y))
     ==> source_evalProof_match_result_rel T R
           (match a1 with
              No_match -> (match f e1 with No_match -> No_match
                                         | Match_type_error -> Match_type_error
                                         | Match v1 -> No_match)
            | Match_type_error -> Match_type_error
            | Match x -> f x)
           (match b1 with
              No_match -> (match g e2 with No_match -> No_match
                                         | Match_type_error -> Match_type_error
                                         | Match v1 -> No_match)
            | Match_type_error -> Match_type_error
            | Match y -> g y)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:(A)match_result` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `b1:(B)match_result` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `(f:A->(A)match_result) e1` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `(g:B->(B)match_result) e2` (cases "match_result")) THEN
  REWRITE_TAC[SEVPAUX_mrr_T; distinctness "match_result"; injectivity "match_result"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "match_result"; injectivity "match_result"] THEN
  MESON_TAC[]);;

let SEVPAUX_PM_PREP_TAC : tactic =
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check SEVPAUX_is_var_eq)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_l_simps; LIST_REL_NIL; LIST_REL_CONS1]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check SEVPAUX_is_var_eq));;

let SEVPAUX_PM_TYERR_TAC : tactic =
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [pmatch_def] THEN
  REWRITE_TAC[source_evalProof_match_result_rel_def] THEN CASE_REWRITE_TAC[] THEN NO_TAC;;

let SEVPAUX_PM_FIN_TAC : tactic =
  REWRITE_TAC[SEVPAUX_mrr_T; distinctness "match_result"; injectivity "match_result"] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1; UNWIND_THM1; ALL2; PAIR_REL_THM] THEN
  ASM_REWRITE_TAC[] THEN NO_TAC;;

let SEVPAUX_PM_CASE_TAC : tactic =
  ONCE_REWRITE_TAC[pmatch_def] THEN IMP_RES_TAC LIST_REL_LENGTH THEN ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN TRY SEVPAUX_PM_FIN_TAC THEN ASM_MESON_TAC[];;

let source_evalProof_pmatch = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   es = orac_s (state_eval_state t) /\
   source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
   (!env_c s_refs p x binds y binds'.
      s_refs = state_refs s /\ env_c = sem_env_c env /\
      source_evalProof_v_rel es x y /\
      ALL2 ((=) ### source_evalProof_v_rel es) binds binds' ==>
      source_evalProof_match_result_rel T (ALL2 ((=) ### source_evalProof_v_rel es))
        (pmatch env_c s_refs p x binds)
        (pmatch (sem_env_c env') (state_refs t) p y binds')) /\
   (!env_c s_refs ps xs binds ys binds'.
      s_refs = state_refs s /\ env_c = sem_env_c env /\
      ALL2 (source_evalProof_v_rel es) xs ys /\
      ALL2 ((=) ### source_evalProof_v_rel es) binds binds' ==>
      source_evalProof_match_result_rel T (ALL2 ((=) ### source_evalProof_v_rel es))
        (pmatch_list env_c s_refs ps xs binds)
        (pmatch_list (sem_env_c env') (state_refs t) ps ys binds'))`,
  STRIP_TAC THEN
  SUBGOAL_THEN `sem_env_c (env':v sem_env) = sem_env_c (env:v sem_env)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[source_evalProof_env_rel_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
  MATCH_MP_TAC pmatch_ind THEN REPEAT CONJ_TAC THEN SEVPAUX_PM_PREP_TAC THEN
  TRY SEVPAUX_PM_TYERR_TAC THENL
   [(* Pany *)
    ONCE_REWRITE_TAC[pmatch_def] THEN SEVPAUX_PM_FIN_TAC;
    (* Pvar *)
    ONCE_REWRITE_TAC[pmatch_def] THEN SEVPAUX_PM_FIN_TAC;
    (* Plit *)
    ONCE_REWRITE_TAC[pmatch_def] THEN ASM_CASES_TAC `l:lit = l'` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `lit_same_type l l'` THEN ASM_REWRITE_TAC[] THEN SEVPAUX_PM_FIN_TAC;
    (* Pcon (SOME n) *)
    SEVPAUX_PM_CASE_TAC;
    (* Pcon NONE *)
    SEVPAUX_PM_CASE_TAC;
    (* Pref *)
    ONCE_REWRITE_TAC[pmatch_def] THEN
    MP_TAC(INST [`lnum:num`,`j:num`; `lnum:num`,`i:num`;
                 `orac_s (state_eval_state (t:(FFI)state))`,`es:eval_oracle_state`]
             s_rel_store_lookup) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `store_lookup lnum (state_refs (s:(FFI)state))` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_THM; OPTREL_SOME] THEN CASE_REWRITE_TAC[] THEN
    TRY SEVPAUX_PM_FIN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `z:(v)store_v` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    CASES_ON `a:(v)store_v` THEN CASES_ON `z:(v)store_v` THEN
    REWRITE_TAC[sv_rel_def; distinctness "store_v"] THEN CASE_REWRITE_TAC[] THEN
    TRY SEVPAUX_PM_FIN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a':v` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* Pas *)
    ONCE_REWRITE_TAC[pmatch_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`(i:mlstring,y:v)`; `binds':(mlstring#v)list`] THEN
    ASM_REWRITE_TAC[PAIR_REL_THM];
    (* Ptannot *)
    ONCE_REWRITE_TAC[pmatch_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* pmatch_list [] [] *)
    ONCE_REWRITE_TAC[pmatch_def] THEN SEVPAUX_PM_FIN_TAC;
    (* pmatch_list CONS CONS *)
    ONCE_REWRITE_TAC[pmatch_def] THEN MATCH_MP_TAC SEVPAUX_pm_cons THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let pmatch_drule_form = prove
 (`pmatch (sem_env_c env) (state_refs s) p x [] = res /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s (state_eval_state t))) env env' /\
   source_evalProof_v_rel (orac_s (state_eval_state t)) x y ==>
   source_evalProof_match_result_rel T
     (ALL2 ((=) ### source_evalProof_v_rel (orac_s (state_eval_state t))))
     res (pmatch (sem_env_c env') (state_refs t) p y [])`,
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(INST [`orac_s (state_eval_state (t:(FFI)state))`,`es:eval_oracle_state`]
           source_evalProof_pmatch) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[ALL2]);;

let can_pmatch_all = prove
 (`can_pmatch_all (sem_env_c env) (state_refs s) pats x /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s (state_eval_state t))) env env' /\
   source_evalProof_v_rel (orac_s (state_eval_state t)) x y ==>
   can_pmatch_all (sem_env_c env') (state_refs t) pats y`,
  STRIP_TAC THEN UNDISCH_TAC
   `can_pmatch_all (sem_env_c (env:v sem_env)) (state_refs (s:(FFI)state)) pats x` THEN
  SPEC_TAC(`pats:pat list`,`pats:pat list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[can_pmatch_all_def] THEN
  MP_TAC(INST [`h:pat`,`p:pat`;
               `pmatch (sem_env_c (env:v sem_env)) (state_refs (s:(FFI)state)) h x []`,`res:((mlstring#v)list)match_result`]
           pmatch_drule_form) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `pmatch (sem_env_c (env:v sem_env)) (state_refs (s:(FFI)state)) h x []`
           (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[source_evalProof_match_result_rel_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "match_result"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "match_result"]);;

let source_evalProof_Num_11 = prove
 (`&0 <= i /\ &0 <= j ==> (num_of_int i = num_of_int j <=> i = j)`,
  MESON_TAC[INT_OF_NUM_OF_INT]);;

let SEVPAUX_EQ_PREP_TAC : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_l_simps; LIST_REL_NIL; LIST_REL_CONS1]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check SEVPAUX_is_var_eq)) THEN
  IMP_RES_TAC v_to_env_id_SOME THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check SEVPAUX_is_var_eq)) THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[do_eq_def] o
    check (fun th -> is_eq(concl th) && SEVPAUX_has_const "Eq_val" th &&
                     (SEVPAUX_has_const "do_eq" th || SEVPAUX_has_const "do_eq_list" th))) THEN
  REWRITE_TAC[distinctness "eq_result"; injectivity "eq_result"; FST; SND] THEN
  ONCE_REWRITE_TAC[do_eq_def];;


let source_evalProof_do_eq = prove
 (`(!x y x' y' b. do_eq x y = Eq_val b /\
                  source_evalProof_v_rel es x x' /\ source_evalProof_v_rel es y y' ==>
                  do_eq x' y' = Eq_val b) /\
   (!xs ys xs' ys' b. do_eq_list xs ys = Eq_val b /\
                      ALL2 (source_evalProof_v_rel es) xs xs' /\
                      ALL2 (source_evalProof_v_rel es) ys ys' ==>
                      do_eq_list xs' ys' = Eq_val b)`,
  MATCH_MP_TAC do_eq_ind THEN REPEAT CONJ_TAC THEN SEVPAUX_EQ_PREP_TAC THENL
   [REWRITE_TAC[];
    REWRITE_TAC[];
    IMP_RES_TAC LIST_REL_LENGTH THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `cn1:stamp option = cn2 /\ LENGTH (vs1:v list) = LENGTH (vs2:v list)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    IMP_RES_TAC LIST_REL_LENGTH THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `LENGTH (vs1:v list) = LENGTH (vs2:v list)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    SIMP_TAC[injectivity "eq_result"];
    SIMP_TAC[injectivity "eq_result"];
    SIMP_TAC[injectivity "eq_result"];
    SIMP_TAC[injectivity "eq_result"];
    REWRITE_TAC[LENGTH; do_eq_def; nat_to_v_def; lit_same_type_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "lit"; INT_OF_NUM_EQ] THEN
    ASM_CASES_TAC `gen1:num = gen2` THEN ASM_REWRITE_TAC[injectivity "eq_result"] THEN
    CONV_TAC TAUT;
    SIMP_TAC[injectivity "eq_result"];
    MP_TAC(ISPEC `do_eq v1 v2` (cases "eq_result")) THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "eq_result"] THEN
    SUBGOAL_THEN `do_eq h'' h' = Eq_val a` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN ASM_CASES_TAC `a:bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    SIMP_TAC[injectivity "eq_result"];
    SIMP_TAC[injectivity "eq_result"]]);;

let SEVPAUX_same_type_rel = prove
 (`!(R:A->B->bool) a b sv sv'.
     store_v_same_type a sv /\ sv_rel R a b /\ sv_rel R sv sv' ==> store_v_same_type b sv'`,
  REPEAT GEN_TAC THEN
  CASES_ON `a:A store_v` THEN CASES_ON `b:B store_v` THEN
  CASES_ON `sv:A store_v` THEN CASES_ON `sv':B store_v` THEN
  REWRITE_TAC[sv_rel_def; store_v_same_type_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN EVERY_CASE_TAC THEN ASM_MESON_TAC[]);;

let store_assign = prove
 (`store_assign lnum sv refs = SOME refs2 /\
   ALL2 (sv_rel (R:A->B->bool)) refs refs3 /\
   sv_rel R sv sv' ==>
   ?refs4. ALL2 (sv_rel R) refs2 refs4 /\ store_assign lnum sv' refs3 = SOME refs4`,
  REWRITE_TAC[store_assign_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `LUPDATE (sv':B store_v) lnum refs3` THEN
  ASM_SIMP_TAC[EVERY2_LUPDATE_same] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_EL_EQN] o
    check (SEVPAUX_has_const "ALL2")) THEN
  SUBGOAL_THEN `lnum < LENGTH (refs3:(B store_v)list) /\
                store_v_same_type (EL lnum refs3) (sv':B store_v)`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[SEVPAUX_same_type_rel]);;

let store_lookup = prove
 (`ALL2 (sv_rel (R:A->B->bool)) refs refs' /\ store_lookup n refs = SOME sv ==>
   ?sv'. sv_rel R sv sv' /\ store_lookup n refs' = SOME sv'`,
  REWRITE_TAC[store_lookup_def; LIST_REL_EL_EQN] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[]);;

let SEVPAUX_v_rel_Conv = prove
 (`source_evalProof_v_rel es (Conv cn xs) (Conv cn' ys) <=>
   cn = cn' /\ ALL2 (source_evalProof_v_rel es) xs ys`,
  REWRITE_TAC[v_rel_l_simps; injectivity "v"] THEN MESON_TAC[]);;

let v_rel_list_to_v = prove
 (`!xs ys. source_evalProof_v_rel es (list_to_v xs) (list_to_v ys) <=>
           ALL2 (source_evalProof_v_rel es) xs ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_v_def; SEVPAUX_v_rel_Conv; ALL2]);;

let SEVPAUX_VREL_PREP_TAC : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_l_simps; LIST_REL_NIL; LIST_REL_CONS1]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check SEVPAUX_is_var_eq));;

let source_evalProof_v_to_list = prove
 (`!x y xs. v_to_list x = SOME xs /\ source_evalProof_v_rel es x y ==>
            ?ys. v_to_list y = SOME ys /\ ALL2 (source_evalProof_v_rel es) xs ys`,
  MATCH_MP_TAC v_to_list_ind THEN REPEAT CONJ_TAC THEN SEVPAUX_VREL_PREP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[v_to_list_def] o
    check (fun th -> is_eq(concl th) && SEVPAUX_has_const "v_to_list" th)) THEN
  ONCE_REWRITE_TAC[v_to_list_def] THEN REWRITE_TAC[option_DISTINCT] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
  ASM_MESON_TAC[ALL2; option_DISTINCT; injectivity "option"]);;

let source_evalProof_v_to_char_list = prove
 (`!x y xs. v_to_char_list x = SOME xs /\ source_evalProof_v_rel es x y ==>
            v_to_char_list y = SOME xs`,
  MATCH_MP_TAC v_to_char_list_ind THEN REPEAT CONJ_TAC THEN SEVPAUX_VREL_PREP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[v_to_char_list_def] o
    check (fun th -> is_eq(concl th) && SEVPAUX_has_const "v_to_char_list" th)) THEN
  ONCE_REWRITE_TAC[v_to_char_list_def] THEN REWRITE_TAC[option_DISTINCT] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
  ASM_MESON_TAC[option_DISTINCT; injectivity "option"]);;

let source_evalProof_vs_to_string = prove
 (`!xs ys s. vs_to_string xs = SOME s /\ ALL2 (source_evalProof_v_rel es) xs ys ==>
             vs_to_string ys = SOME s`,
  MATCH_MP_TAC vs_to_string_ind THEN REPEAT CONJ_TAC THEN SEVPAUX_VREL_PREP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[vs_to_string_def] o
    check (fun th -> is_eq(concl th) && SEVPAUX_has_const "vs_to_string" th)) THEN
  ONCE_REWRITE_TAC[vs_to_string_def] THEN REWRITE_TAC[option_DISTINCT] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
  ASM_MESON_TAC[option_DISTINCT; injectivity "option"]);;

let sv_rel_l_cases = prove
 (`(!R rv v. sv_rel (R:A->B->bool) (Refv rv) v <=> ?v2. v = Refv v2 /\ R rv v2) /\
   (!R xs v. sv_rel (R:A->B->bool) (W8array xs) v <=> v = W8array xs) /\
   (!R vs v. sv_rel (R:A->B->bool) (Varray vs) v <=> ?vs2. v = Varray vs2 /\ ALL2 R vs vs2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[sv_rel_cases] THEN
  REWRITE_TAC[distinctness "store_v"; injectivity "store_v"] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let source_evalProof_v_rel_check_type = prove
 (`source_evalProof_v_rel x v1 v2 ==>
   (check_type ty v1 <=> check_type ty v2) /\ dest_Litv v1 = dest_Litv v2`,
  GEN_REWRITE_TAC LAND_CONV [source_evalProof_v_rel_cases] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP v_to_env_id_SOME)) THEN
  CASES_ON `ty:prim_type` THEN TRY(CASES_ON `a:word_size`) THEN
  REWRITE_TAC[check_type_def; dest_Litv_def; semanticPrimitives_Boolv_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "v"; injectivity "v"] THEN
  TRY(COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "v"; injectivity "v"] THEN
  ASM_MESON_TAC[LIST_REL_NIL]);;

(* HOL4 [local] *)
let LIST_REL_v_rel_check_type = prove
 (`ALL2 (source_evalProof_v_rel x) vs1 vs2 ==>
   (ALL (check_type ty) vs1 <=> ALL (check_type ty) vs2)`,
  SPEC_TAC(`vs2:v list`,`vs2:v list`) THEN SPEC_TAC(`vs1:v list`,`vs1:v list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; ALL] THEN
  ASM_MESON_TAC[source_evalProof_v_rel_check_type]);;

(* local helpers for do_app_sim: the relations of the auxiliary functions  *)
(* of do_app on related arguments                                          *)

(* values of a primitive type are related only to themselves *)
let SEVPAUX_check_type_eq = prove
 (`check_type ty v /\ source_evalProof_v_rel es v w ==> w = v`,
  CASES_ON `ty:prim_type` THEN TRY(CASES_ON `a:word_size`) THEN
  REWRITE_TAC[check_type_def] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_l_simps; source_evalProof_v_rel_Boolv]) THEN
  ASM_REWRITE_TAC[]);;

let SEVPAUX_check_type_ALL_eq = prove
 (`!vs ws. ALL (check_type ty) vs /\ ALL2 (source_evalProof_v_rel es) vs ws ==> ws = vs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ALL2; NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[SEVPAUX_check_type_eq]);;

(* the results of do_arith and do_conversion: literals, Booleans and       *)
(* exceptions without arguments                                            *)
let SEVPAUX_do_arith_res = prove
 (`do_arith a ty vs = SOME r ==>
   r = INL div_exn_v \/ (?l. r = INR (Litv l)) \/ (?b. r = INR (Boolv b))`,
  CASES_ON `ty:prim_type` THEN TRY(CASES_ON `a':word_size`) THEN
  REWRITE_TAC[do_arith_def] THEN CASE_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[injectivity "sum"; distinctness "sum"] THEN
  TRY(REPEAT DISJ2_TAC THEN EXISTS_TAC `~the_Boolv a0` THEN REFL_TAC) THEN
  MESON_TAC[]);;

let SEVPAUX_do_conversion_res = prove
 (`do_conversion v ty1 ty2 = SOME r ==> r = INL chr_exn_v \/ (?l. r = INR (Litv l))`,
  CASES_ON `ty1:prim_type` THEN TRY(CASES_ON `a:word_size`) THEN
  CASES_ON `ty2:prim_type` THEN TRY(CASES_ON `a:word_size`) THEN
  REWRITE_TAC[do_conversion_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[injectivity "sum"; distinctness "sum"] THEN MESON_TAC[]);;

let SEVPAUX_do_test_rel = prove
 (`do_test tst ty v1 v2 = Eq_val b /\ source_evalProof_v_rel es v1 w1 /\
   source_evalProof_v_rel es v2 w2 ==> do_test tst ty w1 w2 = Eq_val b`,
  STRIP_TAC THEN
  SUBGOAL_THEN `dest_Litv w1 = dest_Litv v1 /\ dest_Litv w2 = dest_Litv v2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[source_evalProof_v_rel_check_type]; ALL_TAC] THEN
  ASM_CASES_TAC `check_type ty v1 /\ check_type ty v2` THENL
   [SUBGOAL_THEN `w1:v = v1 /\ w2:v = v2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[SEVPAUX_check_type_eq]; ASM_REWRITE_TAC[]];
    UNDISCH_TAC `do_test tst ty v1 v2 = Eq_val b` THEN
    CASES_ON `tst:test` THEN ASM_REWRITE_TAC[do_test_def; distinctness "eq_result"]]);;

let SEVPAUX_dest_thunk_rel = prove
 (`source_evalProof_v_rel es v w /\ ALL2 (sv_rel (source_evalProof_v_rel es)) s s' ==>
   (dest_thunk [v] s = NotThunk <=> dest_thunk [w] s' = NotThunk)`,
  CASES_ON `v:v` THEN REWRITE_TAC[v_rel_l_simps] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[dest_thunk_def] THEN
  TRY(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP v_to_env_id_SOME) THEN
      REWRITE_TAC[dest_thunk_def] THEN NO_TAC) THEN
  FIRST_ASSUM(MP_TAC o INST [`a1:num`,`i:num`] o MATCH_MP store_lookup_rel) THEN
  SPEC_TAC(`store_lookup a1 (s':(v store_v)list)`,`o2:(v store_v)option`) THEN
  SPEC_TAC(`store_lookup a1 (s:(v store_v)list)`,`o1:(v store_v)option`) THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `o1:(v store_v)option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `o2:(v store_v)option` (cases "option")) THEN
  REWRITE_TAC[OPTREL_THM; option_DISTINCT; option_INJ] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[sv_rel_cases] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `m:thunk_mode`) THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "dest_thunk_ret"]);;

let SEVPAUX_bad_thunk_update_rel = prove
 (`source_evalProof_v_rel es v w /\ ALL2 (sv_rel (source_evalProof_v_rel es)) s s' ==>
   (bad_thunk_update m v s <=> bad_thunk_update m w s')`,
  REWRITE_TAC[bad_thunk_update_def] THEN MESON_TAC[SEVPAUX_dest_thunk_rel]);;

(* thunk_op (s,t) th vs = SOME (st',v) as a disjunction over the cases *)
let SEVPAUX_thunk_op_cases =
  EVALAUX_RENAME_APART_RULE
   (CAKE_SIMP_CONV ([thunk_op_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                     pair_lam_lem; store_alloc_def] @ EVALAUX_do_app_eqs @
                    [case_eq "thunk_op"])
     `thunk_op (s,t:(A)ffi_state) th vs = SOME (st',v:(v,v)result)`);;

let SEVPAUX_sv_rel_Thunk = prove
 (`!R m v y. sv_rel (R:A->B->bool) (Thunk m v) y <=> ?v2. y = Thunk m v2 /\ R v v2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sv_rel_cases; distinctness "store_v"; injectivity "store_v"] THEN
  MESON_TAC[]);;

let SEVPAUX_store_assign_v = prove
 (`store_assign lnum sv refs = SOME refs2 /\
   ALL2 (sv_rel (source_evalProof_v_rel es)) refs refs3 /\
   sv_rel (source_evalProof_v_rel es) sv sv' ==>
   ?refs4. ALL2 (sv_rel (source_evalProof_v_rel es)) refs2 refs4 /\
           store_assign lnum sv' refs3 = SOME refs4`,
  MATCH_ACCEPT_TAC store_assign);;

(* for a goal term store_assign n sv' refs3 and an assumption              *)
(* store_assign n sv refs = SOME refs2: the related update of refs3        *)
let SEVPAUX_STORE_ASSIGN_TAC : tactic = fun (asl,w as gl) ->
  let is_sa t = let h,args = strip_comb t in
                is_const h && fst(dest_const h) = "store_assign" && length args = 3 in
  let gts = find_terms is_sa w in
  let ths = filter (fun th -> let c = concl th in is_eq c && is_sa (lhs c)) (map snd asl) in
  let try_pair t th =
    let _,targs = strip_comb t in
    let n = el 0 targs and sv' = el 1 targs and refs3 = el 2 targs in
    let _,aargs = strip_comb (lhs (concl th)) in
    let n0 = el 0 aargs and sv = el 1 aargs and refs = el 2 aargs in
    if n <> n0 then failwith "SEVPAUX_STORE_ASSIGN_TAC" else
    let refs2 = rand (rhs (concl th)) in
    let lem = INST [n,`lnum:num`; sv,`sv:v store_v`; refs,`refs:(v store_v)list`;
                    refs2,`refs2:(v store_v)list`; refs3,`refs3:(v store_v)list`;
                    sv',`sv':v store_v`] SEVPAUX_store_assign_v in
    MP_TAC lem THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[sv_rel_def] THEN
      TRY(MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
      DISCH_THEN CAKE_STRIP_ASSUME_TAC] in
  FIRST (flat (map (fun t -> map (try_pair t) ths) gts)) gl;;

(* instantiate the first existential of the goal with the other side of an *)
(* equation conjunct                                                       *)
let SEVPAUX_EX_WITNESS_TAC : tactic = fun (asl,w as gl) ->
  let vs,b = strip_exists w in
  let v = hd vs in
  let ok t = not (exists (fun u -> free_in u t) vs) in
  let rec find_eq tm =
    if is_conj tm then (try find_eq (lhand tm) with Failure _ -> find_eq (rand tm))
    else if is_eq tm then
      let l,r = dest_eq tm in
      if l = v && ok r then r
      else if r = v && ok l then l
      else failwith "find_eq"
    else failwith "find_eq" in
  EXISTS_TAC (find_eq b) gl;;

let SEVPAUX_STRIPS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_exists c || is_conj c || is_disj c then CAKE_STRIP_ASSUME_TAC th else NO_TAC));;

let SEVPAUX_thunk_op_sim = prove
 (`thunk_op (refs,ffi:(FFI)ffi_state) th vs = SOME ((refs1,ffi1),r:(v,v)result) /\
   ALL2 (sv_rel (source_evalProof_v_rel es)) refs refs' /\
   ALL2 (source_evalProof_v_rel es) vs ws ==>
   ?refs1' r'. thunk_op (refs',ffi) th ws = SOME ((refs1',ffi1),r') /\
               ALL2 (sv_rel (source_evalProof_v_rel es)) refs1 refs1' /\
               result_rel (source_evalProof_v_rel es) (source_evalProof_v_rel es) r r'`,
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[SEVPAUX_thunk_op_cases]) THEN
  REPEAT DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_l_simps]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC SEVPAUX_bad_thunk_update_rel THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) then RULE_ASSUM_TAC(REWRITE_RULE[th])
                          else NO_TAC) THEN
  ASM_REWRITE_TAC[thunk_op_def; store_alloc_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  TRY SEVPAUX_STORE_ASSIGN_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; GSYM CONJ_ASSOC] THEN
  REPEAT SEVPAUX_EX_WITNESS_TAC THEN
  ASM_SIMP_TAC[result_rel_def; v_rel_l_simps; ALL2; LIST_REL_APPEND_EQ; sv_rel_def;
               injectivity "v"; UNWIND_THM1; UNWIND_THM2]);;

let SEVPAUX_ALL2_MAP_Char = prove
 (`!l. ALL2 (source_evalProof_v_rel es) (MAP (\c. Litv (Char c)) l)
          (MAP (\c. Litv (Char c)) l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2; v_rel_l_simps]);;

let SEVPAUX_ALL2_EL = prove
 (`ALL2 (R:A->B->bool) l1 l2 /\ n < LENGTH l1 ==> R (EL n l1) (EL n l2)`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[]);;

(* for the assumptions ALL2 R l1 l2: LENGTH l2 = LENGTH l1 *)
let SEVPAUX_LEN_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> let c = concl th in
     let h,args = strip_comb c in
     if is_const h && fst(dest_const h) = "ALL2" && length args = 3 then
       GSYM (MATCH_MP LIST_REL_LENGTH th) else failwith "") asl in
  let ths' = filter (fun th -> let c = concl th in not (lhs c = rhs c) &&
                       not (exists (fun (_,a) -> aconv (concl a) c ||
                                     aconv (concl a) (mk_eq(rhs c,lhs c))) asl)) ths in
  MAP_EVERY ASSUME_TAC ths' gl;;

(* for the assumptions ~(x >= y): x < y *)
let SEVPAUX_GE_FACTS_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> let c = concl th in
     if is_neg c && is_comb (rand c) &&
        (let h,_ = strip_comb (rand c) in is_const h && fst(dest_const h) = ">=")
     then REWRITE_RULE[GE; NOT_LE] th else failwith "") asl in
  MAP_EVERY ASSUME_TAC ths gl;;

(* the cases of the do_app simulation: split the hypothesis by do_app_cases, *)
(* determine the shapes of the related arguments and store entries, then     *)
(* evaluate the goal's do_app                                                *)
let SEVPAUX_DAS_SPLIT_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[do_app_cases]);;

let SEVPAUX_DAS_PREP_TAC : tactic =
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; store_alloc_def; case_eq "ffi_result"; option_case_eq;
                              sum_case_eq; option_INJ; option_DISTINCT]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  REPEAT(CHANGED_TAC(
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; v_rel_l_simps;
                                source_evalProof_v_rel_Boolv]) THEN
    SEVPAUX_STRIPS_TAC THEN RVEQ_TAC));;

let SEVPAUX_DAS_REL_TAC : tactic =
  IMP_RES_TAC store_lookup THEN
  IMP_RES_TAC source_evalProof_v_to_list THEN
  IMP_RES_TAC source_evalProof_v_to_char_list THEN
  IMP_RES_TAC (CONJUNCT1 source_evalProof_do_eq) THEN
  IMP_RES_TAC SEVPAUX_do_test_rel THEN
  IMP_RES_TAC SEVPAUX_do_arith_res THEN
  IMP_RES_TAC SEVPAUX_do_conversion_res THEN
  IMP_RES_TAC SEVPAUX_thunk_op_sim THEN
  IMP_RES_TAC SEVPAUX_check_type_eq THEN
  IMP_RES_TAC SEVPAUX_check_type_ALL_eq THEN
  IMP_RES_TAC v_to_env_id_SOME THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "sum"; distinctness "sum"]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC source_evalProof_vs_to_string THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sv_rel_l_cases; SEVPAUX_sv_rel_Thunk]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall (concl th) ||
                                                     (is_imp (concl th))))) THEN
  SEVPAUX_LEN_TAC THEN SEVPAUX_GE_FACTS_TAC;;

let SEVPAUX_REL_FIN_TAC : tactic =
  ASM_SIMP_TAC[result_rel_def; exc_rel_def; v_rel_l_simps; source_evalProof_v_rel_Boolv;
               sub_exn_v_def; div_exn_v_def; chr_exn_v_def; ALL2; LIST_REL_APPEND_EQ;
               sv_rel_def; injectivity "v"; UNWIND_THM1; UNWIND_THM2; nat_to_v_def;
               LIST_REL_REPLICATE_same; v_rel_list_to_v; SEVPAUX_ALL2_MAP_Char;
               SEVPAUX_ALL2_EL];;

let SEVPAUX_DAS_GOAL_TAC : tactic =
  REWRITE_TAC[do_app_def; store_alloc_def; LET_DEF; LET_END_DEF; I_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY SEVPAUX_STORE_ASSIGN_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; GSYM CONJ_ASSOC] THEN
  REPEAT SEVPAUX_EX_WITNESS_TAC THEN
  SEVPAUX_REL_FIN_TAC;;

let SEVPAUX_DAS_TAC : tactic =
  SEVPAUX_DAS_PREP_TAC THEN SEVPAUX_DAS_REL_TAC THEN SEVPAUX_DAS_GOAL_TAC;;

(* the simulation of do_app on related stores and arguments *)
let SEVPAUX_do_app_sim = prove
 (`!refs (ffi:(FFI)ffi_state) op vs refs1 ffi1 r refs' ws.
    do_app (refs,ffi) op vs = SOME ((refs1,ffi1),r) /\
    ALL2 (sv_rel (source_evalProof_v_rel es)) refs refs' /\
    ALL2 (source_evalProof_v_rel es) vs ws /\
    ~(r = Rerr (Rabort Rtype_error)) ==>
    ?refs1' r'. do_app (refs',ffi) op ws = SOME ((refs1',ffi1),r') /\
                ALL2 (sv_rel (source_evalProof_v_rel es)) refs1 refs1' /\
                result_rel (source_evalProof_v_rel es) (source_evalProof_v_rel es) r r'`,
  SEVPAUX_DAS_SPLIT_TAC THEN SEVPAUX_DAS_TAC);;

(* HOL4's statement has an unused existential ref1 (left out here) *)
let do_app_sim = prove
 (`do_app (state_refs s,state_ffi s) op (REVERSE xs) = SOME ((refs,ffi),r) /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   ALL2 (source_evalProof_v_rel (orac_s (state_eval_state t))) xs ys /\
   ~(r = Rerr (Rabort Rtype_error)) ==>
   ?refs' r' es.
     es = orac_s (state_eval_state t) /\
     do_app (state_refs t,state_ffi t) op (REVERSE ys) = SOME ((refs',ffi),r') /\
     ALL2 (sv_rel (source_evalProof_v_rel es)) refs refs' /\
     result_rel (source_evalProof_v_rel es) (source_evalProof_v_rel es) r r'`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                 lhs (concl th) = `t:(FFI)state`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; orac_s_def]) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def; UNWIND_THM2] THEN
  MATCH_MP_TAC (INST [`oracle_s:eval_oracle_state`,`es:eval_oracle_state`] SEVPAUX_do_app_sim) THEN
  MAP_EVERY EXISTS_TAC [`state_refs (s:(FFI)state)`; `REVERSE xs:v list`] THEN
  ASM_SIMP_TAC[EVERY2_REVERSE]);;

let pairarg_to_pair_map = prove
 (`(\(x,y). ((f:A->C) x,(g:B->D) y)) = (f ## g)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let s_rel_clock = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   state_clock s = state_clock t /\
   source_evalProof_s_rel ci (dec_clock s) (dec_clock t)`,
  REWRITE_TAC[source_evalProof_s_rel_def; dec_clock_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  MAP_EVERY EXISTS_TAC [`dec_s:eval_decs_state`; `oracle_s:eval_oracle_state`;
                        `refs':(v store_v)list`] THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; state_component_equality;
                  state_INFO.ri_fupdcanon]);;

let SEVPAUX_SUBST_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(lhs c) && not (fst(dest_var(lhs c)) = "es") &&
       not (free_in (lhs c) (rhs c)) then SUBST_ALL_TAC th
    else if is_eq c && is_var(rhs c) && not (fst(dest_var(rhs c)) = "es") &&
       not (free_in (rhs c) (lhs c)) then SUBST_ALL_TAC (SYM th)
    else failwith ""));;

(* concrete_v by constructor, with concrete_v_list as ALL concrete_v *)
let SEVPAUX_concrete_v_list = prove
 (`!vs. concrete_v_list vs <=> ALL concrete_v vs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[concrete_v_def; ALL]);;

let SEVPAUX_concrete_v_thm = prove
 (`(!l. concrete_v (Litv l) <=> T) /\
   (!c vs. concrete_v (Conv c vs) <=> ALL concrete_v vs) /\
   (!e n x. concrete_v (Closure e n x) <=> F) /\
   (!e f n. concrete_v (Recclosure e f n) <=> F) /\
   (!b n. concrete_v (Loc b n) <=> T) /\
   (!vs. concrete_v (Vectorv vs) <=> ALL concrete_v vs) /\
   (!e i. concrete_v (Env e i) <=> F)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 concrete_v_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SEVPAUX_concrete_v_list]);;

let concrete_v_rel = prove
 (`!x y. source_evalProof_v_rel es x y ==> concrete_v x ==> y = x`,
  SUBGOAL_THEN `!es x y. source_evalProof_v_rel es x y ==> (concrete_v x ==> y = x)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC source_evalProof_v_rel_ind THEN
  REWRITE_TAC[SEVPAUX_concrete_v_thm; injectivity "v"] THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; ALL; CONS_11] THEN
  ASM_MESON_TAC[]);;

let v_to_list_concrete = prove
 (`!x xs. v_to_list x = SOME xs ==> (concrete_v x <=> ALL concrete_v xs)`,
  MATCH_MP_TAC v_to_list_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[v_to_list_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN REPEAT(DISCH_TAC ORELSE GEN_TAC) THEN
  EVERY_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; injectivity "option"]) THEN
  SEVPAUX_SUBST_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; injectivity "option"]) THEN
  ASM_REWRITE_TAC[SEVPAUX_concrete_v_thm; ALL] THEN ASM_MESON_TAC[]);;

let source_evalProof_maybe_all_list_SOME = prove
 (`!(xs:(A option)list) ys. maybe_all_list xs = SOME ys ==> xs = MAP SOME ys`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[maybe_all_list_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; option_DISTINCT] THENL
   [MESON_TAC[MAP]; ALL_TAC] THEN
  GEN_TAC THEN CASES_ON `h:A option` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MAP; CONS_11] THEN ASM_MESON_TAC[]);;

let maybe_all_list_EVERY = prove
 (`maybe_all_list (xs:(A option)list) = SOME ys ==> ALL (\x. ~(x = NONE)) xs`,
  DISCH_THEN(SUBST1_TAC o MATCH_MP source_evalProof_maybe_all_list_SOME) THEN
  REWRITE_TAC[ALL_MAP; o_DEF; option_DISTINCT; ALL_T]);;

let v_to_word8_list_concrete = prove
 (`v_to_word8_list x = SOME xs ==> concrete_v x`,
  REWRITE_TAC[v_to_word8_list_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP maybe_all_list_EVERY) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP v_to_list_concrete) THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN MATCH_MP_TAC MONO_ALL THEN
  GEN_TAC THEN REWRITE_TAC[v_to_word8_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[SEVPAUX_concrete_v_thm]);;

let v_to_word64_list_concrete = prove
 (`v_to_word64_list x = SOME xs ==> concrete_v x`,
  REWRITE_TAC[v_to_word64_list_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP maybe_all_list_EVERY) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP v_to_list_concrete) THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN MATCH_MP_TAC MONO_ALL THEN
  GEN_TAC THEN REWRITE_TAC[v_to_word64_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[SEVPAUX_concrete_v_thm]);;

let compiler_agrees = prove
 (`compiler_agrees f (eid,st_v,decs) (st_v2,bs_v,ws_v) ==>
   concrete_v st_v /\ concrete_v st_v2 /\ concrete_v bs_v /\ concrete_v ws_v`,
  REWRITE_TAC[compiler_agrees_def] THEN EVERY_CASE_TAC THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[v_to_word8_list_concrete; v_to_word64_list_concrete]);;

let recorded_orac_wf_step = prove
 (`recorded_orac_wf (compiler:compiler_fun) orac /\
   compiler_agrees compiler args (st_v2,bs_v,ws_v) /\
   (0 < FST (FST (orac 0)) ==> FST (SND args) = FST (SND (orac 0)))
   ==> recorded_orac_wf compiler
         (\j. if j = 0 then ((FST (FST (orac 0)) + 1,0),st_v2,[])
              else if j = SUC (FST (FST (orac 0))) then args
              else orac j)`,
  REWRITE_TAC[recorded_orac_wf_def; compiler_agrees_def] THEN
  REWRITE_TAC[ARITH_RULE `~(n + 1 = 0) /\ n + 1 = SUC n /\ 0 < SUC n`; NOT_SUC] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FST];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(j = 0) /\ ~(j = SUC (FST (FST ((orac:eval_oracle_fun) 0))))`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `j = FST (FST ((orac:eval_oracle_fun) 0))` THEN
    ASM_REWRITE_TAC[FST; SND] THENL
     [SUBGOAL_THEN `0 < FST (FST ((orac:eval_oracle_fun) 0))` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `j < FST (FST ((orac:eval_oracle_fun) 0))` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]]]);;

let SEVPAUX_WITNESS_TAC : tactic = fun (asl,w as gl) ->
  if not (is_exists w) then failwith "SEVPAUX_WITNESS_TAC" else
  let v,_ = dest_exists w in
  let _,body = strip_exists w in
  let rec find_eq t =
    if is_conj t then (try find_eq (lhand t) with Failure _ -> find_eq (rand t))
    else if is_eq t && rand t = v && not (free_in v (lhand t)) then lhand t
    else if is_eq t && lhand t = v && not (free_in v (rand t)) then rand t
    else failwith "find_eq" in
  EXISTS_TAC (find_eq body) gl;;
let SEVPAUX_envs_forward = prove
 (`eval_oracle_state_envs es1 = eval_oracle_state_envs es2 ==> es_forward es1 es2`,
  SIMP_TAC[es_forward_def; FORALL_PAIR_THM; lookup_env_def; LE_REFL]);;

let SEVPAUX_v_rel_envs = prove
 (`eval_oracle_state_envs es1 = eval_oracle_state_envs es2 ==>
   source_evalProof_v_rel es1 = source_evalProof_v_rel es2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_MESON_TAC[v_rel_forward; SEVPAUX_envs_forward]);;

let SEVPAUX_lookup_env = prove
 (`lookup_env es (i,j) = SOME env <=>
   i < LENGTH (eval_oracle_state_envs es) /\
   j < LENGTH (EL i (eval_oracle_state_envs es)) /\
   env = EL j (EL i (eval_oracle_state_envs es))`,
  REWRITE_TAC[lookup_env_def; oEL_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let SEVPAUX_forward_append = prove
 (`eval_oracle_state_envs es' = APPEND (eval_oracle_state_envs es) l ==>
   es_forward es es'`,
  DISCH_TAC THEN ASM_REWRITE_TAC[es_forward_def; FORALL_PAIR_THM; SEVPAUX_lookup_env;
                                 LENGTH_APPEND; LE_ADD; EL_APPEND_EQN] THEN
  SIMP_TAC[] THEN ARITH_TAC);;

let SEVPAUX_forward_lupdate = prove
 (`g < LENGTH (eval_oracle_state_envs es) /\
   eval_oracle_state_envs es' =
     LUPDATE (APPEND (EL g (eval_oracle_state_envs es)) l) g (eval_oracle_state_envs es) ==>
   es_forward es es'`,
  STRIP_TAC THEN ASM_REWRITE_TAC[es_forward_def; FORALL_PAIR_THM; SEVPAUX_lookup_env;
                                 LENGTH_LUPDATE; LE_REFL; EL_LUPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; EL_APPEND_EQN] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN SIMP_TAC[] THEN ARITH_TAC);;

let SEVPAUX_env_forward = prove
 (`!es es' env env'.
     source_evalProof_env_rel (source_evalProof_v_rel es) env env' /\ es_forward es es' ==>
     source_evalProof_env_rel (source_evalProof_v_rel es') env env'`,
  MESON_TAC[forward_rules]);;

let SEVPAUX_refs_forward = prove
 (`!es es' (xs:(v store_v)list) ys.
     ALL2 (sv_rel (source_evalProof_v_rel es)) xs ys /\ es_forward es es' ==>
     ALL2 (sv_rel (source_evalProof_v_rel es')) xs ys`,
  MESON_TAC[forward_rules]);;

let SEVPAUX_do_eval_EvalDecs =
  CAKE_SIMP_CONV ([do_eval_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] @
                  EVALAUX_do_app_eqs @ [case_eq "eval_state"])
  `do_eval vs (SOME (EvalDecs s)) = SOME (env,decs,es)`;;


let SEVPAUX_reset_sim = prove
 (`!(ci:(C)compiler_instance) dec_s oracle_s o2 (s2:(A)state) t2.
     eval_decs_state_env_id_counter dec_s =
       (eval_oracle_state_generation oracle_s,
        LENGTH (EL (eval_oracle_state_generation oracle_s) (eval_oracle_state_envs oracle_s)),
        LENGTH (eval_oracle_state_envs oracle_s)) /\
     eval_oracle_state_generation oracle_s < LENGTH (eval_oracle_state_envs oracle_s) /\
     eval_oracle_state_envs o2 = APPEND (eval_oracle_state_envs oracle_s) [[]] /\
     eval_oracle_state_generation o2 = LENGTH (eval_oracle_state_envs oracle_s) /\
     source_evalProof_s_rel ci s2 t2 /\
     es_forward o2 (orac_s (state_eval_state t2)) /\
     es_stack_forward o2 (orac_s (state_eval_state t2))
     ==> es_forward (orac_s (state_eval_state t2))
           (orac_s (reset_env_generation (SOME (EvalOracle oracle_s)) (state_eval_state t2))) /\
         source_evalProof_s_rel ci
           (state_eval_state_fupd
              (K (reset_env_generation (SOME (EvalDecs dec_s)) (state_eval_state s2))) s2)
           (state_eval_state_fupd
              (K (reset_env_generation (SOME (EvalOracle oracle_s)) (state_eval_state t2))) t2) /\
         es_stack_forward oracle_s
           (orac_s (reset_env_generation (SOME (EvalOracle oracle_s)) (state_eval_state t2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[source_evalProof_s_rel_def] o
    check (SEVPAUX_has_const "source_evalProof_s_rel")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; orac_s_def]) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def; reset_env_generation_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[orac_s_def] THEN
  SUBGOAL_THEN `!j. j < LENGTH (eval_oracle_state_envs oracle_s) ==>
                    EL j (eval_oracle_state_envs oracle_s') = EL j (eval_oracle_state_envs oracle_s)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `es_stack_forward o2 oracle_s'` THEN
    ASM_REWRITE_TAC[es_stack_forward_def; EL_APPEND_EQN] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (eval_oracle_state_envs oracle_s) <
                LENGTH (eval_oracle_state_envs oracle_s')` ASSUME_TAC THENL
   [UNDISCH_TAC `es_forward o2 oracle_s'` THEN
    ASM_REWRITE_TAC[es_forward_def; LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `source_evalProof_v_rel (eval_oracle_state_generation_fupd
                  (K (eval_oracle_state_generation oracle_s)) oracle_s') =
                source_evalProof_v_rel oracle_s'` ASSUME_TAC THENL
   [MATCH_MP_TAC SEVPAUX_v_rel_envs THEN REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SEVPAUX_envs_forward THEN REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds];
    REWRITE_TAC[source_evalProof_s_rel_def] THEN
    MAP_EVERY EXISTS_TAC
     [`eval_decs_state_env_id_counter_fupd
         (K (eval_oracle_state_generation oracle_s,
             LENGTH (EL (eval_oracle_state_generation oracle_s)
                        (eval_oracle_state_envs oracle_s)),
             LENGTH (eval_oracle_state_envs oracle_s'))) dec_s'`;
      `eval_oracle_state_generation_fupd (K (eval_oracle_state_generation oracle_s))
         oracle_s'`;
      `refs':(v store_v)list`] THEN
    ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; state_INFO.ri_fupdcanon; K_o_THM;
                    state_INFO.ri_accfupds; K_THM; eval_decs_state_INFO.ri_accfupds;
                    eval_oracle_state_INFO.ri_accfupds; PAIR_EQ] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th o
        check (fun t -> is_imp(concl t) && lhand(concl t) = concl th))) THEN
      ASM_REWRITE_TAC[];
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LT_TRANS THEN
      EXISTS_TAC `LENGTH (eval_oracle_state_envs oracle_s)` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[es_stack_forward_def; eval_oracle_state_INFO.ri_accfupds; K_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `eval_oracle_state_generation oracle_s` THEN ASM_REWRITE_TAC[]]);;

let do_eval_sim = prove
 (`do_eval (REVERSE xs) (state_eval_state s) = SOME (env,decs,es) /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(A)state) t /\
   ALL2 (source_evalProof_v_rel (orac_s (state_eval_state t))) xs ys ==>
   ?env' es'.
     es_forward (orac_s (state_eval_state t)) (orac_s es') /\
     do_eval (REVERSE ys) (state_eval_state t) = SOME (env',decs,es') /\
     source_evalProof_env_rel (source_evalProof_v_rel (orac_s es')) env env' /\
     source_evalProof_s_rel ci (state_eval_state_fupd (K es) s)
       (state_eval_state_fupd (K es') t) /\
     (!s2 t2. source_evalProof_s_rel ci (s2:(A)state) t2 /\
              es_forward (orac_s es') (orac_s (state_eval_state t2)) /\
              es_stack_forward (orac_s es') (orac_s (state_eval_state t2)) ==>
              es_forward (orac_s (state_eval_state t2))
                (orac_s (reset_env_generation (state_eval_state t) (state_eval_state t2))) /\
              source_evalProof_s_rel ci
                (state_eval_state_fupd
                   (K (reset_env_generation (state_eval_state s) (state_eval_state s2))) s2)
                (state_eval_state_fupd
                   (K (reset_env_generation (state_eval_state t) (state_eval_state t2))) t2) /\
              es_stack_forward (orac_s (state_eval_state t))
                (orac_s (reset_env_generation (state_eval_state t) (state_eval_state t2))))`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[source_evalProof_s_rel_def] o
    check (SEVPAUX_has_const "source_evalProof_s_rel")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; orac_s_def]) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "do_eval")) THEN
  ASM_REWRITE_TAC[SEVPAUX_do_eval_EvalDecs] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[GSYM LIST_REL_REVERSE_EQ] o
    check (fun th -> SEVPAUX_has_const "ALL2" th && not (SEVPAUX_has_const "sv_rel" th))) THEN
  ASM_REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL; v_rel_l_simps] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
                        fst(dest_var(lhs(concl th))) <> "es"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compiler_agrees) THEN
  IMP_RES_TAC concrete_v_rel THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
                        fst(dest_var(lhs(concl th))) <> "es"))) THEN
  SUBGOAL_THEN `?i i' st d. eval_oracle_state_oracle oracle_s 0 = ((i,i'),st,d)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq; FST; SND]) THEN ASSUME_TAC eq) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  ONCE_REWRITE_TAC[do_eval_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[do_eval_record_def] THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; GSYM CONJ_ASSOC] THEN
  REPEAT SEVPAUX_WITNESS_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `es:eval_state option`)) THEN
  REWRITE_TAC[orac_s_def] THEN
  ABBREV_TAC `o2 = add_env_generation (eval_oracle_state_oracle_fupd
     (K (\j. if j = 0 then ((i + 1,0),a0'',[]) else if j = SUC i then (a1,st,decs)
             else eval_oracle_state_oracle oracle_s j)) oracle_s)` THEN
  SUBGOAL_THEN `eval_oracle_state_envs o2 = APPEND (eval_oracle_state_envs oracle_s) [[]] /\
                eval_oracle_state_generation o2 = LENGTH (eval_oracle_state_envs oracle_s) /\
                eval_oracle_state_oracle o2 =
                  (\j. if j = 0 then ((i + 1,0),a0'',[]) else if j = SUC i then (a1,st,decs)
                       else eval_oracle_state_oracle oracle_s j) /\
                eval_oracle_state_custom_do_eval o2 = eval_oracle_state_custom_do_eval oracle_s`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "o2" THEN
    REWRITE_TAC[add_env_generation_def; eval_oracle_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `es_forward oracle_s o2` ASSUME_TAC THENL
   [MATCH_MP_TAC(GEN_ALL SEVPAUX_forward_append) THEN
    EXISTS_TAC `[[]]:((v sem_env)list)list` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SEVPAUX_env_forward THEN EXISTS_TAC `oracle_s:eval_oracle_state` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[source_evalProof_s_rel_def] THEN
    MAP_EVERY EXISTS_TAC
     [`add_decs_generation (eval_decs_state_compiler_state_fupd (K (a0'':v)) dec_s)`;
      `o2:eval_oracle_state`; `refs':(v store_v)list`] THEN
    REWRITE_TAC[state_INFO.ri_fupdfupds; state_INFO.ri_fupdcanon; K_o_THM;
                state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[add_decs_generation_def; eval_decs_state_INFO.ri_accfupds; K_THM] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[eval_decs_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[ARITH_RULE `~(i + 1 = 0) /\ 0 < i + 1`; LENGTH_APPEND; LENGTH; EL_APPEND_EQN;
                LT_REFL; SUB_REFL; EL; HD; ADD_CLAUSES; LT_SUC_LE; LE_REFL; FST; SND] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC;
      MATCH_MP_TAC SEVPAUX_refs_forward THEN EXISTS_TAC `oracle_s:eval_oracle_state` THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      MP_TAC(INST [`mk_compiler_fun_from_ci (ci:(C)compiler_instance)`,`compiler:compiler_fun`;
                   `eval_oracle_state_oracle oracle_s`,`orac:eval_oracle_fun`;
                   `(a1:num#num,st:v,decs:dec list)`,`args:compiler_args`;
                   `a0'':v`,`st_v2:v`; `a0''':v`,`bs_v:v`; `a0'''':v`,`ws_v:v`]
              recorded_orac_wf_step) THEN
      ASM_REWRITE_TAC[FST; SND] THEN NO_TAC;
      ASM_CASES_TAC `i = 0` THENL
       [ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0) /\ 1 = SUC 0`; FST; SND] THEN
        UNDISCH_TAC `0 = i ==> eval_decs_state_compiler_state dec_s =
                     compiler_instance_config_v (ci:(C)compiler_instance)
                       (compiler_instance_init_state ci)` THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `~(1 = SUC i) /\ 0 < i` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`] THEN
        UNDISCH_TAC `0 < i ==> FST (SND (eval_oracle_state_oracle oracle_s 1)) =
                     compiler_instance_config_v (ci:(C)compiler_instance)
                       (compiler_instance_init_state ci)` THEN
        ASM_REWRITE_TAC[]]];
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SEVPAUX_reset_sim THEN
  EXISTS_TAC `o2:eval_oracle_state` THEN ASM_REWRITE_TAC[])]);;

let SEVPAUX_v_to_nat_nat = prove
 (`!n. v_to_nat (nat_to_v n) = SOME n`,
  REWRITE_TAC[v_to_nat_def; nat_to_v_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_POS; NUM_OF_INT_OF_NUM]);;

let SEVPAUX_v_to_env_id_nat = prove
 (`!a b. v_to_env_id (Conv NONE [nat_to_v a; nat_to_v b]) = SOME (a,b)`,
  REWRITE_TAC[v_to_env_id_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SEVPAUX_v_to_nat_nat] THEN CASE_REWRITE_TAC[]);;
let SEVPAUX_declare_env_EvalDecs =
  CAKE_SIMP_CONV ([declare_env_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] @
                  EVALAUX_do_app_eqs @ [case_eq "eval_state"])
  `declare_env (SOME (EvalDecs s)) env = SOME (v,es)`;;

let declare_env_sim = prove
 (`declare_env (state_eval_state s) env = SOME (v,es) /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(A)state) t /\
   source_evalProof_env_rel (source_evalProof_v_rel (orac_s (state_eval_state t))) env env' ==>
   ?v' es2.
     es_forward (orac_s (state_eval_state t)) (orac_s es2) /\
     declare_env (state_eval_state t) env' = SOME (v',es2) /\
     source_evalProof_v_rel (orac_s es2) v v' /\
     source_evalProof_s_rel ci (state_eval_state_fupd (K es) s)
       (state_eval_state_fupd (K es2) t) /\
     es_stack_forward (orac_s (state_eval_state t)) (orac_s es2)`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[source_evalProof_s_rel_def] o
    check (SEVPAUX_has_const "source_evalProof_s_rel")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; orac_s_def]) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "declare_env")) THEN
  ASM_REWRITE_TAC[SEVPAUX_declare_env_EvalDecs] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SEVPAUX_SUBST_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `es:eval_state option`)) THEN
  REWRITE_TAC[declare_env_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[oEL_THM] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; GSYM CONJ_ASSOC] THEN
  REPEAT SEVPAUX_WITNESS_TAC THEN REWRITE_TAC[orac_s_def] THEN
  ABBREV_TAC `o2 = eval_oracle_state_envs_fupd
     (K (LUPDATE (APPEND (EL (eval_oracle_state_generation oracle_s)
                              (eval_oracle_state_envs oracle_s)) [env'])
                 (eval_oracle_state_generation oracle_s) (eval_oracle_state_envs oracle_s)))
     oracle_s` THEN
  SUBGOAL_THEN `eval_oracle_state_envs o2 =
                  LUPDATE (APPEND (EL (eval_oracle_state_generation oracle_s)
                                      (eval_oracle_state_envs oracle_s)) [env'])
                          (eval_oracle_state_generation oracle_s)
                          (eval_oracle_state_envs oracle_s) /\
                eval_oracle_state_generation o2 = eval_oracle_state_generation oracle_s /\
                eval_oracle_state_oracle o2 = eval_oracle_state_oracle oracle_s /\
                eval_oracle_state_custom_do_eval o2 = eval_oracle_state_custom_do_eval oracle_s`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "o2" THEN REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `es_forward oracle_s o2` ASSUME_TAC THENL
   [MATCH_MP_TAC(GEN_ALL SEVPAUX_forward_lupdate) THEN
    MAP_EVERY EXISTS_TAC [`[env']:(v sem_env)list`;
                          `eval_oracle_state_generation oracle_s`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[v_rel_l_simps; SEVPAUX_v_to_env_id_nat] THEN
    EXISTS_TAC `env':v sem_env` THEN
    ASM_REWRITE_TAC[SEVPAUX_lookup_env; LENGTH_LUPDATE; EL_LUPDATE; LENGTH_APPEND; LENGTH;
                    EL_APPEND_EQN; LT_REFL; SUB_REFL; EL; HD; ARITH_RULE `n < n + SUC 0`] THEN
    MATCH_MP_TAC SEVPAUX_env_forward THEN EXISTS_TAC `oracle_s:eval_oracle_state` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[source_evalProof_s_rel_def] THEN
    MAP_EVERY EXISTS_TAC
     [`eval_decs_state_env_id_counter_fupd
         (K (eval_oracle_state_generation oracle_s,
             LENGTH (EL (eval_oracle_state_generation oracle_s)
                        (eval_oracle_state_envs oracle_s)) + 1,
             LENGTH (eval_oracle_state_envs oracle_s))) dec_s`;
      `o2:eval_oracle_state`; `refs':(v store_v)list`] THEN
    ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; state_INFO.ri_fupdcanon; K_o_THM;
                    state_INFO.ri_accfupds; K_THM; eval_decs_state_INFO.ri_accfupds;
                    LENGTH_LUPDATE; EL_LUPDATE; LENGTH_APPEND; LENGTH; ADD1] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEVPAUX_refs_forward THEN EXISTS_TAC `oracle_s:eval_oracle_state` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th o
        check (fun t -> is_imp(concl t) && lhand(concl t) = concl th))) THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[es_stack_forward_def; EL_LUPDATE] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(j = eval_oracle_state_generation oracle_s)` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let source_evalProof_abort_def = cake_def
  `source_evalProof_abort (r:(A,B)result) <=>
     match r with Rerr (Rabort a) -> T | _ -> F`;;

let source_evalProof_abort_simps = prove
 (`(source_evalProof_abort (Rerr (Rabort a):(A,B)result) <=> T) /\
   (source_evalProof_abort (Rerr (Rraise e):(A,B)result) <=> F) /\
   (source_evalProof_abort (Rval v:(A,B)result) <=> F)`,
  REWRITE_TAC[source_evalProof_abort_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [source_evalProof_abort_simps];;

(* HOL4 [local] *)
let abort_imp_intro = prove
 (`(!v. x = Rval v ==> P) /\ (!e. x = Rerr (Rraise e) ==> P) ==>
   (~source_evalProof_abort (x:(A,B)result) ==> P)`,
  CASES_ON `x:(A,B)result` THEN TRY(CASES_ON `a:(B)error_result`) THEN
  REWRITE_TAC[source_evalProof_abort_simps; distinctness "result"; injectivity "result";
              distinctness "error_result"; injectivity "error_result"] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let env_rel_imp_c = prove
 (`source_evalProof_env_rel x env env' ==> sem_env_c env' = sem_env_c env`,
  SIMP_TAC[source_evalProof_env_rel_def]);;

(* ---- helper lemmas for eval_simulation ---- *)
let SEVPAUX_sem_env_v_fupd_id = prove
 (`!e:v sem_env. sem_env_v_fupd (K (sem_env_v e)) e = e`,
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accfupds; K_THM]);;

let SEVPAUX_env_rel_bind = prove
 (`source_evalProof_env_rel R env env' /\ R x y ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsBind n x (sem_env_v env))) env)
     (sem_env_v_fupd (K (nsBind n y (sem_env_v env'))) env')`,
  STRIP_TAC THEN MATCH_MP_TAC env_rel_add_nsBind THEN
  ASM_REWRITE_TAC[SEVPAUX_sem_env_v_fupd_id]);;

let SEVPAUX_env_rel_optbind = prove
 (`source_evalProof_env_rel R env env' /\ R x y ==>
   source_evalProof_env_rel R (sem_env_v_fupd (K (nsOptBind xo x (sem_env_v env))) env)
     (sem_env_v_fupd (K (nsOptBind xo y (sem_env_v env'))) env')`,
  CASES_ON `xo:mlstring option` THEN REWRITE_TAC[nsOptBind_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SEVPAUX_sem_env_v_fupd_id] THEN MESON_TAC[SEVPAUX_env_rel_bind]);;

let SEVPAUX_env_rel_bindlist = prove
 (`source_evalProof_env_rel R env env' /\ ALL2 ((=) ### R) xs ys ==>
   source_evalProof_env_rel R
     (sem_env_v_fupd (K (nsAppend (alist_to_ns xs) (sem_env_v env))) env)
     (sem_env_v_fupd (K (nsAppend (alist_to_ns ys) (sem_env_v env'))) env')`,
  REWRITE_TAC[nsAppend_to_nsBindList] THEN STRIP_TAC THEN
  MATCH_MP_TAC env_rel_add_nsBindList THEN ASM_REWRITE_TAC[SEVPAUX_sem_env_v_fupd_id]);;

let SEVPAUX_ALL2_recclosures = prove
 (CASE_TERM
  `!l:(mlstring#mlstring#exp)list.
     source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
       ALL2 ((=) ### source_evalProof_v_rel es)
         (MAP (\fne:mlstring#mlstring#exp. match fne with
                                             (f,n,e) -> (f,Recclosure env funs f)) l)
         (MAP (\fne:mlstring#mlstring#exp. match fne with
                                             (f,n,e) -> (f,Recclosure env' funs f)) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PAIR_REL_THM; v_rel_l_simps; injectivity "v"; UNWIND_THM1; UNWIND_THM2;
                  GSYM CONJ_ASSOC]);;

let SEVPAUX_env_rel_rec_env = prove
 (`source_evalProof_env_rel (source_evalProof_v_rel es) env1 env1' /\
   source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
   source_evalProof_env_rel (source_evalProof_v_rel es)
     (sem_env_v_fupd (K (build_rec_env funs env1 (sem_env_v env))) env)
     (sem_env_v_fupd (K (build_rec_env funs env1' (sem_env_v env'))) env')`,
  STRIP_TAC THEN REWRITE_TAC[build_rec_env_merge] THEN
  MATCH_MP_TAC SEVPAUX_env_rel_bindlist THEN ASM_SIMP_TAC[SEVPAUX_ALL2_recclosures]);;

let SEVPAUX_build_conv_sim = prove
 (`build_conv envc cn vs = SOME v /\ ALL2 (source_evalProof_v_rel es) vs ws ==>
   ?w. build_conv envc cn ws = SOME w /\ source_evalProof_v_rel es v w`,
  REWRITE_TAC[build_conv_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[v_rel_l_simps; injectivity "v"; UNWIND_THM1; UNWIND_THM2]);;

let SEVPAUX_nsLookup_sim = prove
 (`nsLookup (sem_env_v env) eid = SOME v /\ source_evalProof_env_rel R env env' ==>
   ?v'. nsLookup (sem_env_v env') eid = SOME v' /\ R v v'`,
  MESON_TAC[env_rel_nsLookup_v]);;

(* instantiate all the existentials of the goal by equations among the     *)
(* conjuncts of its body                                                  *)
let SEVPAUX_EXS_TAC : tactic = fun (asl,w as gl) ->
  let vs,b = strip_exists w in
  if vs = [] then failwith "SEVPAUX_EXS_TAC" else
  let eqs = flat (map (fun c ->
      if is_eq c then
        let l,r = dest_eq c in
        (if mem l vs && not (free_in l r) then [(l,r)] else []) @
        (if mem r vs && not (free_in r l) then [(r,l)] else [])
      else []) (conjuncts b)) in
  let rec resolve assigned =
    let progress = filter (fun (v,t) -> not (can (assoc v) assigned) &&
                     forall (fun u -> not (free_in u t) || can (assoc u) assigned) vs) eqs in
    match progress with
      [] -> assigned
    | (v,t)::_ -> resolve ((v, vsubst (map (fun (u,s) -> (s,u)) assigned) t)::assigned) in
  (* the remaining variables: by matching conjuncts against assumptions *)
  let rec by_match assigned =
    let assigned = resolve assigned in
    let todo = filter (fun v -> not (can (assoc v) assigned)) vs in
    if todo = [] then assigned else
    let sub = map (fun (u,s) -> (s,u)) assigned in
    let cs = filter (fun c -> exists (fun v -> free_in v c) todo)
               (map (vsubst sub) (conjuncts b)) in
    let try_c c =
      tryfind (fun (_,a) ->
        let (_,ti,tyi) = term_match [] c (concl a) in
        if tyi <> [] then failwith "" else
        if forall (fun (t,v) -> mem v todo) ti && ti <> [] then ti else failwith "") asl in
    let ti = tryfind try_c cs in
    by_match (map (fun (t,v) -> (v,t)) ti @ assigned) in
  let assigned = by_match [] in
  let wits = map (fun v -> try assoc v assigned with Failure _ -> failwith "SEVPAUX_EXS_TAC") vs in
  MAP_EVERY EXISTS_TAC wits gl;;

let SEVPAUX_do_opapp_sim = prove
 (`do_opapp vs = SOME (env1,e) /\ ALL2 (source_evalProof_v_rel es) vs ws ==>
   ?env2. do_opapp ws = SOME (env2,e) /\
          source_evalProof_env_rel (source_evalProof_v_rel es) env1 env2`,
  REWRITE_TAC[do_opapp_cases] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_l_simps]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[do_opapp_cases; CONS_11; injectivity "v"; distinctness "v"; RIGHT_AND_EXISTS_THM;
              LEFT_AND_EXISTS_THM] THEN
  SEVPAUX_EXS_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC SEVPAUX_env_rel_bind THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC env_rel_add_nsBind THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SEVPAUX_env_rel_rec_env THEN ASM_REWRITE_TAC[]]);;

let SEVPAUX_do_log_sim = prove
 (`do_log lop v e = SOME r /\ source_evalProof_v_rel es v w ==> do_log lop w e = SOME r`,
  REWRITE_TAC[do_log_def] THEN STRIP_TAC THEN
  ASM_CASES_TAC `v = Boolv T` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[source_evalProof_v_rel_Boolv; semanticPrimitivesProps_Boolv_11]) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[semanticPrimitivesProps_Boolv_11];
    ASM_CASES_TAC `v = Boolv F` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[source_evalProof_v_rel_Boolv; semanticPrimitivesProps_Boolv_11]) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[semanticPrimitivesProps_Boolv_11];
      FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "Andalso")) THEN
      ASM_REWRITE_TAC[option_DISTINCT]]]);;

let SEVPAUX_do_if_sim = prove
 (`do_if v e1 e2 = SOME e /\ source_evalProof_v_rel es v w ==> do_if w e1 e2 = SOME e`,
  REWRITE_TAC[do_if_def] THEN STRIP_TAC THEN
  ASM_CASES_TAC `v = Boolv T` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[source_evalProof_v_rel_Boolv; semanticPrimitivesProps_Boolv_11]) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[semanticPrimitivesProps_Boolv_11];
    ASM_CASES_TAC `v = Boolv F` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[source_evalProof_v_rel_Boolv; semanticPrimitivesProps_Boolv_11]) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[semanticPrimitivesProps_Boolv_11];
      FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "COND")) THEN
      ASM_REWRITE_TAC[option_DISTINCT]]]);;

let SEVPAUX_s_rel_fields = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   state_clock t = state_clock s /\ state_ffi t = state_ffi s /\
   state_next_type_stamp t = state_next_type_stamp s /\
   state_next_exn_stamp t = state_next_exn_stamp s /\
   (!f. source_evalProof_s_rel ci (state_next_type_stamp_fupd f s)
          (state_next_type_stamp_fupd f t)) /\
   (!f. source_evalProof_s_rel ci (state_next_exn_stamp_fupd f s)
          (state_next_exn_stamp_fupd f t))`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THEN GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`dec_s:eval_decs_state`; `oracle_s:eval_oracle_state`;
                        `refs':(v store_v)list`] THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; state_component_equality;
                  state_INFO.ri_fupdcanon]);;

let SEVPAUX_s_rel_refs = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   ALL2 (sv_rel (source_evalProof_v_rel (orac_s (state_eval_state t)))) refs refs' ==>
   source_evalProof_s_rel ci (state_refs_fupd (K refs) s) (state_refs_fupd (K refs') t) /\
   (!ffi. source_evalProof_s_rel ci (state_refs_fupd (K refs) (state_ffi_fupd (K ffi) s))
            (state_refs_fupd (K refs') (state_ffi_fupd (K ffi) t)))`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                 lhs (concl th) = `t:(FFI)state`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; orac_s_def]) THEN
  CONJ_TAC THEN TRY GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`dec_s:eval_decs_state`; `oracle_s:eval_oracle_state`;
                        `refs':(v store_v)list`] THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; state_component_equality;
                  state_INFO.ri_fupdcanon]);;

let SEVPAUX_list_result_rel = prove
 (`result_rel (source_evalProof_v_rel es) (source_evalProof_v_rel es) r r' ==>
   result_rel (ALL2 (source_evalProof_v_rel es)) (source_evalProof_v_rel es)
     (list_result r) (list_result r')`,
  CASES_ON `r:(v,v)result` THEN CASES_ON `r':(v,v)result` THEN
  REWRITE_TAC[result_rel_def; list_result_def; ALL2]);;

let SEVPAUX_env_rel_alist = prove
 (`ALL2 ((=) ### R) xs ys ==>
   source_evalProof_env_rel R (sem_env_REC (alist_to_ns xs) c) (sem_env_REC (alist_to_ns ys) c)`,
  STRIP_TAC THEN
  MP_TAC(INST [`sem_env_REC nsEmpty c:v sem_env`,`env:v sem_env`;
               `sem_env_REC nsEmpty c:v sem_env`,`env':v sem_env`] SEVPAUX_env_rel_bindlist) THEN
  ASM_REWRITE_TAC[sem_env_INFO.ri_accessors; sem_env_INFO.ri_fupds; K_THM; nsAppend_nsEmpty] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[source_evalProof_env_rel_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
              option_DISTINCT]);;

let SEVPAUX_env_rel_empty_v = prove
 (`source_evalProof_env_rel R (sem_env_REC nsEmpty c) (sem_env_REC nsEmpty c)`,
  REWRITE_TAC[source_evalProof_env_rel_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
              option_DISTINCT]);;

let SEVPAUX_env_rel_rec_env2 = prove
 (`source_evalProof_env_rel (source_evalProof_v_rel es) env env' ==>
   source_evalProof_env_rel (source_evalProof_v_rel es)
     (sem_env_REC (build_rec_env funs env nsEmpty) nsEmpty)
     (sem_env_REC (build_rec_env funs env' nsEmpty) nsEmpty)`,
  STRIP_TAC THEN REWRITE_TAC[build_rec_env_merge; nsAppend_nsEmpty] THEN
  MATCH_MP_TAC SEVPAUX_env_rel_alist THEN ASM_SIMP_TAC[SEVPAUX_ALL2_recclosures]);;

let SEVPAUX_env_rel_sing = prove
 (`R x y ==>
   source_evalProof_env_rel R (sem_env_REC (nsSing n x) nsEmpty)
     (sem_env_REC (nsSing n y) nsEmpty)`,
  DISCH_TAC THEN REWRITE_TAC[nsSing_eq_bind] THEN
  MP_TAC(INST [`sem_env_REC nsEmpty nsEmpty:v sem_env`,`env:v sem_env`;
               `sem_env_REC nsEmpty nsEmpty:v sem_env`,`env':v sem_env`;
               `nsEmpty:(mlstring,mlstring,v)namespace`,`ev:(mlstring,mlstring,v)namespace`;
               `nsEmpty:(mlstring,mlstring,v)namespace`,`ev':(mlstring,mlstring,v)namespace`]
            env_rel_add_nsBind) THEN
  ASM_REWRITE_TAC[sem_env_INFO.ri_fupds; K_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SEVPAUX_env_rel_empty_v]);;

let SEVPAUX_sem_env_fupds_REC = prove
 (`!a b e:v sem_env. sem_env_v_fupd (K a) (sem_env_c_fupd (K b) e) = sem_env_REC a b`,
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accfupds; sem_env_INFO.ri_accessors;
              K_THM]);;

let SEVPAUX_env_rel_lift = prove
 (`source_evalProof_env_rel R e e' ==>
   source_evalProof_env_rel R
     (sem_env_REC (nsLift mn (sem_env_v e)) (nsLift mn (sem_env_c e)))
     (sem_env_REC (nsLift mn (sem_env_v e')) (nsLift mn (sem_env_c e')))`,
  DISCH_TAC THEN
  MP_TAC(INST [`e:v sem_env`,`env:v sem_env`; `e':v sem_env`,`env':v sem_env`;
               `sem_env_v (e:v sem_env)`,`v:(mlstring,mlstring,v)namespace`;
               `sem_env_v (e':v sem_env)`,`v':(mlstring,mlstring,v)namespace`;
               `sem_env_c (e:v sem_env)`,`c:(mlstring,mlstring,num#stamp)namespace`;
               `sem_env_c (e':v sem_env)`,`c':(mlstring,mlstring,num#stamp)namespace`]
            env_rel_nsLift) THEN
  REWRITE_TAC[SEVPAUX_sem_env_fupds_REC] THEN
  SUBGOAL_THEN `!x:v sem_env. sem_env_REC (sem_env_v x) (sem_env_c x) = x`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accessors]);;

let SEVPAUX_combine_dec_result_rel = prove
 (`result_rel (source_evalProof_env_rel R) R r r' /\ source_evalProof_env_rel R e e' ==>
   result_rel (source_evalProof_env_rel R) R (combine_dec_result e r) (combine_dec_result e' r')`,
  CASES_ON `r:(v sem_env,v)result` THEN CASES_ON `r':(v sem_env,v)result` THEN
  REWRITE_TAC[result_rel_def; combine_dec_result_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[result_rel_def; GSYM extend_dec_env_def] THEN MESON_TAC[env_rel_extend_dec_env]);;

let SEVPAUX_dest_thunk_IsThunk = prove
 (`dest_thunk vs st = IsThunk m v <=>
   ?n. vs = [Loc F n] /\ store_lookup n st = SOME (Thunk m v)`,
  EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[]] THEN
  STRUCT_CASES_TAC(ISPEC `vs:v list` list_CASES) THEN
  REWRITE_TAC[dest_thunk_def; distinctness "dest_thunk_ret"] THEN
  CASES_ON `h:v` THEN
  REWRITE_TAC[dest_thunk_def; distinctness "dest_thunk_ret"] THEN
  STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
  REWRITE_TAC[dest_thunk_def; distinctness "dest_thunk_ret"] THEN
  REWRITE_TAC[CONS_11; injectivity "v"; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1;
              NOT_CONS_NIL] THEN
  MP_TAC(ISPEC `store_lookup a1 (st:(v store_v)list)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "dest_thunk_ret"; option_INJ] THEN
  CASES_ON `a:(v)store_v` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "dest_thunk_ret"; distinctness "store_v"; injectivity "store_v"] THEN
  TRY(CASES_ON `a0':thunk_mode`) THEN CASE_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `a0:bool` THEN
  REWRITE_TAC[distinctness "dest_thunk_ret"; injectivity "dest_thunk_ret"] THEN
  MESON_TAC[]);;

let SEVPAUX_update_thunk_SOME = prove
 (`update_thunk vs st vs2 = SOME st2 <=>
   ?n v. vs = [Loc F n] /\ vs2 = [v] /\ dest_thunk [v] st = NotThunk /\
         store_assign n (Thunk Evaluated v) st = SOME st2`,
  EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[update_thunk_def] THEN CASE_REWRITE_TAC[]] THEN
  STRUCT_CASES_TAC(ISPEC `vs:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  CASES_ON `h:v` THEN REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `vs2:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  REWRITE_TAC[CONS_11; injectivity "v"; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1;
              NOT_CONS_NIL] THEN
  BOOL_CASES_TAC `a0:bool` THEN REWRITE_TAC[option_DISTINCT] THEN
  (fun (asl,w as gl) ->
     let t = find_term (fun t -> EVPROPSAUX_is_const_app ["dest_thunk"] t) w in
     MP_TAC(ISPEC t (cases "dest_thunk_ret")) gl) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; distinctness "dest_thunk_ret"]);;

(* ---- machinery for eval_simulation ---- *)

(* the facts name a b among the assumptions *)
let SEVPAUX_bin_facts name asl =
  mapfilter (fun (_,th) -> let c = concl th in
     let h,args = strip_comb c in
     if is_const h && fst(dest_const h) = name && length args = 2
     then (el 0 args, el 1 args, th) else failwith "") asl;;

(* name a c for a preorder name (reflexivity refl, transitivity trans) from *)
(* the facts among the assumptions, by breadth first search               *)
let SEVPAUX_preorder_prove name refl trans asl a c =
  if aconv a c then INST [a,`es:eval_oracle_state`] refl else
  let facts = SEVPAUX_bin_facts name asl in
  let rec bfs frontier visited =
    if frontier = [] then failwith "SEVPAUX_preorder_prove" else
    match filter (fun (n,_) -> aconv n c) frontier with
      (_,th)::_ -> th
    | [] ->
      let next = flat (map (fun (n,th) ->
          mapfilter (fun (x,y,fth) ->
            if aconv x n && not (exists (aconv y) visited)
            then (y, MATCH_MP trans (CONJ th fth)) else failwith "") facts) frontier) in
      let next = itlist (fun (y,th) acc -> if exists (fun (z,_) -> aconv y z) acc then acc
                                           else (y,th)::acc) next [] in
      bfs next (map fst next @ visited) in
  bfs (mapfilter (fun (x,y,fth) -> if aconv x a then (y,fth) else failwith "") facts) [a];;

let SEVPAUX_es_fwd asl a c =
  SEVPAUX_preorder_prove "es_forward" es_forward_refl es_forward_trans asl a c;;

let SEVPAUX_es_stack_fwd asl a c =
  SEVPAUX_preorder_prove "es_stack_forward" es_stack_forward_refl
    es_stack_forward_trans asl a c;;

let SEVPAUX_exc_rel_forward = prove
 (`exc_rel (source_evalProof_v_rel es) e e' /\ es_forward es es' ==>
   exc_rel (source_evalProof_v_rel es') e e'`,
  CASES_ON `e:(v)error_result` THEN CASES_ON `e':(v)error_result` THEN
  REWRITE_TAC[exc_rel_def] THEN MESON_TAC[v_rel_forward]);;

let SEVPAUX_result_rel_forward = prove
 (`(result_rel (ALL2 (source_evalProof_v_rel es)) (source_evalProof_v_rel es) r r' /\
    es_forward es es' ==>
    result_rel (ALL2 (source_evalProof_v_rel es')) (source_evalProof_v_rel es') r r') /\
   (result_rel (source_evalProof_env_rel (source_evalProof_v_rel es))
      (source_evalProof_v_rel es) r2 r2' /\
    es_forward es es' ==>
    result_rel (source_evalProof_env_rel (source_evalProof_v_rel es'))
      (source_evalProof_v_rel es') r2 r2')`,
  CONJ_TAC THENL
   [CASES_ON `r:(v list,v)result` THEN CASES_ON `r':(v list,v)result`;
    CASES_ON `r2:(v sem_env,v)result` THEN CASES_ON `r2':(v sem_env,v)result`] THEN
  REWRITE_TAC[result_rel_def] THEN MESON_TAC[forward_rules; SEVPAUX_exc_rel_forward]);;

let SEVPAUX_FWD_RULES =
  map SPEC_ALL (CONJUNCTS forward_rules @ [SEVPAUX_exc_rel_forward] @
                CONJUNCTS SEVPAUX_result_rel_forward);;

(* the versions of the relational fact th forwarded to the oracle state c *)
let SEVPAUX_fwd_to asl c th =
  mapfilter (fun rule ->
    let ant = lhand (concl rule) in
    let p = lhand ant in
    let i = term_match [] p (concl th) in
    let rule' = INSTANTIATE i rule in
    let a = lhand (rand (lhand (concl rule'))) in
    let rule'' = INST [c, rand (rand (lhand (concl rule')))] rule' in
    MATCH_MP rule'' (CONJ th (SEVPAUX_es_fwd asl a c))) SEVPAUX_FWD_RULES;;

let SEVPAUX_is_tyerr t =
  try let r,a = dest_comb t in
      fst(dest_const r) = "Rerr" &&
      (let r2,a2 = dest_comb a in fst(dest_const r2) = "Rabort" &&
                                  fst(dest_const a2) = "Rtype_error")
  with Failure _ -> false;;

let SEVPAUX_NOT_TYERR_RW =
  [distinctness "result"; injectivity "result"; distinctness "error_result";
   injectivity "error_result"; distinctness "abort"];;

(* ~(r = Rerr (Rabort Rtype_error)) from the like facts of the assumptions *)
let SEVPAUX_prove_not_tyerr asl tm =
  if not (is_neg tm && is_eq (rand tm) && SEVPAUX_is_tyerr (rand (rand tm)))
  then failwith "SEVPAUX_prove_not_tyerr" else
  let hs = filter (fun th -> let c = concl th in
                   is_neg c && is_eq (rand c) && SEVPAUX_is_tyerr (rand (rand c))) (map snd asl) in
  let hs' = map (REWRITE_RULE SEVPAUX_NOT_TYERR_RW) hs in
  EQT_ELIM (REWRITE_CONV (SEVPAUX_NOT_TYERR_RW @ hs @ hs') tm);;

let SEVPAUX_es_subterm vs tm =
  find_term (fun t -> type_of t = `:eval_oracle_state` &&
                      not (exists (fun v -> free_in v t) vs)) tm;;

(* instantiate the variables of slem by i (from matching the pattern pat) *)
(* and generalize those that do not occur in pat                          *)
let SEVPAUX_inst_gen pat i slem =
  let (_,_,tyi) = i in
  let pvs = frees pat in
  let rest = filter (fun v -> not (mem v pvs)) (frees (concl slem)) in
  let th = INSTANTIATE i slem in
  let rest' = filter (fun v -> mem v (frees (concl th))) (map (inst tyi) rest) in
  GENL rest' th;;

(* lemmas used backwards in the discharge: curried, with conclusions        *)
(* R a b whose last argument may be determined by the discharge            *)
let SEVPAUX_BACK_LEMMAS = ref ([]:thm list);;

(* discharge the antecedents of th (curried, universally quantified) by the *)
(* assumptions, reflexivity for an equation that defines a quantified       *)
(* variable, the type error facts, forwarded relational facts and the       *)
(* backward lemmas; all the complete discharges (with backtracking)         *)
let SEVPAUX_NORM_RULE = CONV_RULE (REWRITE_CONV[state_INFO.ri_accfupds; K_THM]);;

(* MATCH_MP that instantiates only the universally quantified variables of *)
(* th (the free variables of th are kept); the uninstantiated ones are     *)
(* generalized again                                                      *)
let SEVPAUX_MATCH_MP th a =
  let vs,body = strip_forall (concl th) in
  if not (is_imp body) then failwith "SEVPAUX_MATCH_MP" else
  (* a quick test first: the antecedent must match (renaming vs does not   *)
  (* change that)                                                          *)
  let ant0 = lhand body in
  let _ = term_match (subtract (frees ant0) vs) ant0 (concl a) in
  let avoid = frees (concl a) @ freesl (hyp a) @ freesl (hyp th) @ frees (concl th) in
  let vs' = itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs) [] in
  let vs' = rev vs' in
  let th1 = SPECL vs' th in
  let ant = lhand (concl th1) in
  let lcs = subtract (frees ant) vs' in
  let i = term_match lcs ant (concl a) in
  let th2 = INSTANTIATE i th1 in
  let th3 = MP th2 a in
  let (_,ti,tyi) = i in
  let rem = filter (fun v -> not (exists (fun (_,x) -> x = v) ti)) vs' in
  let rem' = filter (fun v -> mem v (frees (concl th3))) (map (inst tyi) rem) in
  GENL rem' th3;;

(* rename the leading existentially bound variables of th to names that   *)
(* are not used elsewhere in the current case (a counter suffix), so that  *)
(* stripping never reuses the name of an eliminated variable              *)
let SEVPAUX_name_counter = ref 0;;

let SEVPAUX_fresh_name v =
  let n,ty = dest_var v in
  let base = try String.sub n 0 (String.index n '_') with Not_found -> n in
  incr SEVPAUX_name_counter;
  mk_var(base^"_"^string_of_int !SEVPAUX_name_counter,ty);;

(* the universally quantified implications among the assumptions (not    *)
(* induction hypotheses), with their conclusions split into conjuncts      *)
let SEVPAUX_local_lemmas asl =
  flat (mapfilter (fun (_,th) ->
    let c = concl th in
    if is_forall c && not (can (find_term (fun t -> is_exists t)) c) then
      let vs,b = strip_forall c in
      if not (is_imp b) then failwith "" else
      let th1 = SPEC_ALL th in
      let ants,cn = splitlist dest_imp (concl th1) in
      let cs = conjuncts cn in
      if length cs = 1 then [th] else
      let th2 = funpow (length ants) UNDISCH th1 in
      mapfilter (fun cj -> GENL vs (itlist DISCH ants cj)) (CONJUNCTS th2)
    else failwith "") asl);;

(* instances of the local lemmas where the quantified states are updated   *)
(* in their eval_state (state_eval_state_fupd (K e) s0), normalized         *)
let SEVPAUX_es_opt_ty = `:(eval_state)option`;;
let SEVPAUX_K_es = `K:(eval_state)option->(eval_state)option->(eval_state)option`;;
let SEVPAUX_REC_RW_CONV = REWRITE_CONV EVPROPSAUX_REC_RW;;

let SEVPAUX_local_inst_lemmas asl =
  flat (mapfilter (fun th ->
    let vs,_ = strip_forall (concl th) in
    let svs = filter (fun v -> try fst(dest_type(type_of v)) = "state" with Failure _ -> false) vs in
    if svs = [] then failwith "" else
    let th1 = SPEC_ALL th in
    let insts = map (fun v ->
        let n,ty = dest_var v in
        let e = SEVPAUX_fresh_name (mk_var(n^"_es",SEVPAUX_es_opt_ty)) in
        let v0 = SEVPAUX_fresh_name (mk_var(n^"_0",ty)) in
        (mk_icomb(mk_icomb(mk_const("state_eval_state_fupd",[]),
                           mk_icomb(SEVPAUX_K_es, e)),
                  v0), v)) svs in
    let th2 = CONV_RULE SEVPAUX_REC_RW_CONV (INST insts th1) in
    [GEN_ALL th2]) (SEVPAUX_local_lemmas asl));;

(* the local lemmas and their instances, memoised for the last assumption *)
(* list (the discharge asks for them at every level of its search)         *)
let SEVPAUX_locals_last = ref ([] : ((string * thm) list * thm list) list);;
let SEVPAUX_locals asl =
  match !SEVPAUX_locals_last with
    (a,r)::_ when a == asl -> r
  | _ -> let r = SEVPAUX_local_lemmas asl @ SEVPAUX_local_inst_lemmas asl in
         SEVPAUX_locals_last := [asl,r]; r;;

let rec SEVPAUX_discharge_d d asl th0 =
  let th = SEVPAUX_NORM_RULE th0 in
  let vs,body = strip_forall (concl th) in
  if not (is_imp body) then [th] else
  let ant = lhand body in
  let key t = let h,args = strip_comb t in
              if is_const h then
                (let n = fst(dest_const h) in
                 if n = "=" && args <> [] then
                   (let h2,_ = strip_comb (hd args) in
                    if is_const h2 then "=" ^ fst(dest_const h2) else "=")
                 else n)
              else "" in
  let ka = key ant in
  let pre = if ka = "" || ka = "=" then asl
            else filter (fun (_,a) -> let kb = key (concl a) in kb = ka || kb = "") asl in
  let direct = mapfilter (fun (_,a) -> SEVPAUX_MATCH_MP th a) pre in
  let r1 = flat (map (SEVPAUX_discharge_d d asl) direct) in
  if r1 <> [] then r1 else
  let others =
    (try [let l,r = dest_eq ant in
          if mem l vs && not (exists (fun v -> free_in v r) vs) then SEVPAUX_MATCH_MP th (REFL r)
          else failwith ""] with Failure _ -> []) @
    (try [if vs = [] then MP th (SEVPAUX_prove_not_tyerr asl ant) else failwith ""]
     with Failure _ -> []) @
    (try [if vs = [] then
            let h,args = strip_comb ant in
            if is_const h && fst(dest_const h) = "es_forward" && length args = 2 then
              MP th (SEVPAUX_es_fwd asl (el 0 args) (el 1 args))
            else if is_const h && fst(dest_const h) = "es_stack_forward" && length args = 2 then
              MP th (SEVPAUX_es_stack_fwd asl (el 0 args) (el 1 args))
            else failwith ""
          else failwith ""] with Failure _ -> []) in
  let r2 = flat (map (SEVPAUX_discharge_d d asl) others) in
  if r2 <> [] then r2 else
  let r3 =
    try
      let hd_of t = let h,_ = strip_comb t in if is_const h then fst(dest_const h) else "" in
      let ha = hd_of ant in
      if not (mem ha ["source_evalProof_v_rel"; "ALL2"; "source_evalProof_env_rel";
                      "exc_rel"; "result_rel"]) then failwith "" else
      let cc = SEVPAUX_es_subterm vs ant in
      let cands = filter (fun (_,a) -> hd_of (concl a) = ha) asl in
      let fwd = flat (mapfilter (fun (_,a) ->
                  mapfilter (fun fa -> SEVPAUX_MATCH_MP th fa) (SEVPAUX_fwd_to asl cc a)) cands) in
      flat (map (SEVPAUX_discharge_d d asl) fwd)
    with Failure _ -> [] in
  if r3 <> [] || d = 0 then r3 else
  let back = flat (mapfilter (fun lem ->
      let c = snd (splitlist dest_imp (snd (strip_forall (concl lem)))) in
      let pat,i = try c, term_match [] c ant with Failure _ ->
              if is_comb ant && mem (rand ant) vs then rator c, term_match [] (rator c) (rator ant)
              else failwith "" in
      let slem = SPEC_ALL lem in
      let lem'' = SEVPAUX_inst_gen pat i slem in
      mapfilter (fun lth -> SEVPAUX_MATCH_MP th lth)
        (SEVPAUX_discharge_d (d - 1) asl lem''))
      (!SEVPAUX_BACK_LEMMAS @ SEVPAUX_locals asl)) in
  flat (map (SEVPAUX_discharge_d d asl) back);;

let SEVPAUX_discharge_all asl th = SEVPAUX_discharge_d 3 asl th;;

(* the curried form of a lemma A1 /\ .. /\ An ==> C *)
let SEVPAUX_CURRY th = GEN_ALL (REWRITE_RULE[IMP_CONJ] (SPEC_ALL th));;

let SEVPAUX_FRESH_EXISTS th =
  let rec go tm =
    if is_exists tm then
      let v,b = dest_exists tm in
      let v' = SEVPAUX_fresh_name v in
      mk_exists(v', go (vsubst [v',v] b))
    else if is_conj tm then mk_conj(go (lhand tm), go (rand tm))
    else if is_disj tm then mk_disj(go (lhand tm), go (rand tm))
    else tm in
  let c = concl th in
  let c' = go c in
  if c' = c then th else EQ_MP (ALPHA c c') th;;

(* the conclusions added so far by SEVPAUX_LEMMA_RES_TAC in the current   *)
(* case (reset by SEVPAUX_ES_PREP_TAC)                                    *)
let SEVPAUX_produced = ref ([]:term list);;

(* add the conclusions of the complete discharges of the lemmas *)
let SEVPAUX_LEMMA_RES_TAC lems : tactic = fun (asl,w as gl) ->
  let ths = flat (map (fun l -> try SEVPAUX_discharge_d 1 asl l with Failure _ -> []) lems) in
  let ths' = itlist (fun th acc ->
      if exists (fun (_,a) -> aconv (concl a) (concl th)) asl ||
         exists (aconv (concl th)) !SEVPAUX_produced ||
         exists (fun a -> aconv (concl a) (concl th)) acc then acc else th::acc) ths [] in
  if ths' = [] then failwith "SEVPAUX_LEMMA_RES_TAC" else
  (SEVPAUX_produced := map concl ths' @ !SEVPAUX_produced;
   MAP_EVERY (CAKE_STRIP_ASSUME_TAC o SEVPAUX_FRESH_EXISTS) ths' gl);;

(* a closed goal by the discharge of a backward lemma *)
let SEVPAUX_BACK_TAC : tactic = fun (asl,w as gl) ->
  let th = tryfind (fun lem ->
      let c = snd (splitlist dest_imp (snd (strip_forall (concl lem)))) in
      let i = term_match [] c w in
      let lem' = SEVPAUX_inst_gen c i (SPEC_ALL lem) in
      let th = hd (SEVPAUX_discharge_d 2 asl lem') in
      if aconv (concl th) w then th else failwith "")
      (!SEVPAUX_BACK_LEMMAS @ SEVPAUX_locals asl) in
  ACCEPT_TAC th gl;;

(* ---- the induction hypotheses ---- *)

let SEVPAUX_is_ih th =
  let rec strip c = if is_forall c then strip (snd(dest_forall c))
                    else if is_imp c then strip (rand c) else c in
  let c = strip (concl th) in
  is_exists c && can (find_term (fun t -> is_const t &&
                     fst(dest_const t) = "source_evalProof_s_rel")) c &&
  (is_forall (concl th) || is_imp (concl th));;

let SEVPAUX_IH_STEP_TAC : tactic = fun (asl,w as gl) ->
  let ihs = filter (fun (_,th) -> SEVPAUX_is_ih th) asl in
  let rec try_ihs = function
      [] -> failwith "SEVPAUX_IH_STEP_TAC"
    | (_,ih)::rest ->
        (match (try SEVPAUX_discharge_all asl ih with Failure _ -> []) with
           th::_ when is_exists (concl th) ->
             if exists (aconv (concl th)) !SEVPAUX_produced then
               (UNDISCH_THEN (concl ih) (K ALL_TAC)) gl
             else
              (SEVPAUX_produced := concl th :: !SEVPAUX_produced;
               (UNDISCH_THEN (concl ih) (K ALL_TAC) THEN
                CAKE_STRIP_ASSUME_TAC (SEVPAUX_FRESH_EXISTS th)) gl)
         | _ -> try_ihs rest) in
  try_ihs ihs;;

(* the general induction hypotheses (instantiated by RES_TAC already) *)
let SEVPAUX_is_general_ih th =
  let c = concl th in
  is_forall c &&
  (let vs,b = strip_forall c in
   is_imp b && EVPROPSAUX_is_eval_eq (lhand b) &&
   exists (fun v -> free_in v (rhs (lhand b))) vs);;

let SEVPAUX_DROP_GENERAL_IH_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check SEVPAUX_is_general_ih));;

(* a variable whose name differs from those of the free variables of avoid *)
let SEVPAUX_name_variant avoid v =
  let names = map (fst o dest_var) (filter is_var (flat (map frees avoid))) in
  let n,ty = dest_var v in
  let rec go n = if mem n names then go (n^"'") else n in
  mk_var(go n,ty);;

(* evaluate s env [e] = (s',Rval vs) with vs a variable: vs = [v] *)
let SEVPAUX_SING_TAC : tactic =
  REPEAT(fun (asl,w as gl) ->
    let avoid = itlist (union o frees o concl o snd) asl (frees w) in
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if EVPROPSAUX_is_eval_eq c && EVPROPSAUX_is_const_app ["evaluate"] (lhs c) &&
         (let r = snd(dest_pair(rhs c)) in
          EVPROPSAUX_is_const_app ["Rval"] r && is_var (rand r)) &&
         (let l = el 2 (snd(strip_comb(lhs c))) in
          is_list l && length (dest_list l) = 1)
      then (ASSUME_TAC th THEN
            X_CHOOSE_THEN (SEVPAUX_fresh_name `v:v`) SUBST_ALL_TAC
              (MATCH_MP evaluate_sing th))
      else NO_TAC) gl);;

(* the dec_clock relation of the base state relations *)
let SEVPAUX_SREL_CLOCK_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if EVPROPSAUX_is_const_app ["source_evalProof_s_rel"] c &&
         not (EVPROPSAUX_is_const_app ["state_clock_fupd"] (lhand c))
      then REWRITE_RULE[dec_clock_def] (CONJUNCT2 (MATCH_MP s_rel_clock th))
      else failwith "") asl in
  let ths' = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl)) ths in
  MAP_EVERY ASSUME_TAC ths' gl;;

(* the equations of the fields of the target states with those of the     *)
(* source states (kept in SEVPAUX_feqs for the current case, reset by       *)
(* SEVPAUX_ES_PREP_TAC); the assumptions are rewritten with them            *)
let SEVPAUX_feqs = ref ([]:thm list);;

let SEVPAUX_FIELDS_TAC : tactic = fun (asl,w as gl) ->
  let ths = flat (mapfilter (fun (_,th) ->
      let c = concl th in
      if EVPROPSAUX_is_const_app ["source_evalProof_s_rel"] c &&
         not (EVPROPSAUX_is_const_app ["state_clock_fupd"] (lhand c)) then
        let fs = CONJUNCTS (MATCH_MP SEVPAUX_s_rel_fields th) in
        filter (fun f -> is_eq (concl f) && not (lhs (concl f) = rhs (concl f))) fs
      else if EVPROPSAUX_is_const_app ["source_evalProof_env_rel"] c then
        let f = MATCH_MP env_rel_imp_c th in
        if lhs (concl f) = rhs (concl f) then failwith "" else [f]
      else failwith "") asl) in
  let new_ths = itlist (fun th acc ->
      if exists (fun f -> aconv (concl f) (concl th)) (!SEVPAUX_feqs @ acc) then acc
      else th::acc) ths [] in
  SEVPAUX_feqs := new_ths @ !SEVPAUX_feqs;
  if new_ths = [] then ALL_TAC gl else
  RULE_ASSUM_TAC (REWRITE_RULE !SEVPAUX_feqs) gl;;

let SEVPAUX_FSTRIPS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_exists c || is_conj c || is_disj c
    then CAKE_STRIP_ASSUME_TAC (SEVPAUX_FRESH_EXISTS th) else NO_TAC));;

(* abort of an error result, independently of the type of the values *)
let SEVPAUX_abort_Rerr = prove
 (`!e. source_evalProof_abort (Rerr e:(A,B)result) <=> ?a. e = Rabort a`,
  GEN_TAC THEN CASES_ON `e:(B)error_result` THEN
  REWRITE_TAC[source_evalProof_abort_simps; distinctness "error_result";
              injectivity "error_result"] THEN MESON_TAC[]);;

let SEVPAUX_abort_combine = prove
 (`!env r. source_evalProof_abort (combine_dec_result env (r:(v sem_env,A)result)) <=>
           source_evalProof_abort r`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `r:(v sem_env,A)result` THEN
  REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[source_evalProof_abort_simps]);;

let SEVPAUX_ES_NORM_RW =
  [state_INFO.ri_accfupds; K_THM; orac_s_def; REVERSE_EQ_SING; REVERSE; APPEND;
   SEVPAUX_dest_thunk_IsThunk; SEVPAUX_update_thunk_SOME; source_evalProof_abort_simps;
   SEVPAUX_abort_Rerr; SEVPAUX_abort_combine; SEVPAUX_sv_rel_Thunk; sv_rel_l_cases;
   distinctness "error_result"; injectivity "error_result"; CONS_11; injectivity "v";
   option_INJ; injectivity "store_v";
   ALL2; HD; TL; LIST_REL_CONS1; LIST_REL_NIL; v_rel_l_simps; source_evalProof_v_rel_Boolv;
   SEVPAUX_mrr_T; distinctness "match_result"; injectivity "match_result";
   FORALL_UNWIND_THM1; FORALL_UNWIND_THM2];;

(* substitutions after a step: oracle state variables, results, singleton *)
(* lists; then the simplification of the assumptions                       *)
(* for two assumptions l = r1 and l = r2 (r1, r2 different): r1 = r2 *)
let SEVPAUX_FUNC_TAC : tactic = fun (asl,w as gl) ->
  let eqs = filter (fun (_,th) -> let c = concl th in
                      is_eq c && not (is_var (lhs c)) && type_of (lhs c) <> bool_ty) asl in
  let rec pairs = function
      [] -> []
    | (_,th)::rest ->
        mapfilter (fun (_,th2) ->
          if aconv (lhs (concl th)) (lhs (concl th2)) &&
             not (aconv (rhs (concl th)) (rhs (concl th2)))
          then TRANS (SYM th) th2 else failwith "") rest @ pairs rest in
  let news = pairs eqs in
  let news' = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl)) news in
  MAP_EVERY ASSUME_TAC news' gl;;

(* for an assumption A <=> B and an assumption A: the assumption B *)
let SEVPAUX_IFF_MP_TAC : tactic = fun (asl,w as gl) ->
  let iffs = filter (fun (_,th) -> let c = concl th in
                       is_eq c && type_of (lhs c) = bool_ty && not (is_var (lhs c))) asl in
  let news = flat (map (fun (_,ith) ->
      mapfilter (fun (_,a) -> if aconv (concl a) (lhs (concl ith)) then EQ_MP ith a
                              else failwith "") asl) iffs) in
  let news' = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl)) news in
  MAP_EVERY ASSUME_TAC news' gl;;

let SEVPAUX_POST_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_var (lhs c) && type_of (lhs c) = `:eval_oracle_state` &&
       not (free_in (lhs c) (rhs c)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; exc_rel_raise1;
                              exc_rel_type_error1]) THEN
  SEVPAUX_FSTRIPS_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_var (lhs c) && not (free_in (lhs c) (rhs c)) &&
       (try mem (fst(dest_type(type_of(lhs c)))) ["result"; "error_result"; "list"]
        with Failure _ -> false)
    then SUBST_ALL_TAC th else NO_TAC)) THEN
  (fun gl -> RULE_ASSUM_TAC(REWRITE_RULE (SEVPAUX_ES_NORM_RW @ !SEVPAUX_feqs)) gl) THEN
  SEVPAUX_FSTRIPS_TAC THEN RVEQ_TAC THEN SEVPAUX_IFF_MP_TAC THEN
  SEVPAUX_FUNC_TAC THEN
  (fun gl -> RULE_ASSUM_TAC(REWRITE_RULE (SEVPAUX_ES_NORM_RW @ !SEVPAUX_feqs)) gl) THEN
  SEVPAUX_FSTRIPS_TAC THEN RVEQ_TAC;;

(* ---- the goal ---- *)

(* ~abort r ==> P: the conditional facts with the same condition *)
let SEVPAUX_ABORT_DISCH_TAC : tactic = fun (asl,w as gl) ->
  if is_imp w && is_neg (lhand w) then
    (DISCH_THEN(fun th ->
       let ths = mapfilter (fun (_,a) -> MP a th) asl in
       MAP_EVERY ASSUME_TAC (th::ths))) gl
  else failwith "SEVPAUX_ABORT_DISCH_TAC";;

(* a relational fact from the assumptions: exactly, by the preorders, or *)
(* forwarded                                                              *)
let SEVPAUX_rel_prove asl w =
  try find (fun th -> aconv (concl th) w) (map snd asl) with Failure _ ->
  let h,args = strip_comb w in
  if is_const h && fst(dest_const h) = "es_forward" && length args = 2 then
    SEVPAUX_es_fwd asl (el 0 args) (el 1 args)
  else if is_const h && fst(dest_const h) = "es_stack_forward" && length args = 2 then
    SEVPAUX_es_stack_fwd asl (el 0 args) (el 1 args)
  else
    let cc = SEVPAUX_es_subterm [] w in
    tryfind (fun (_,a) -> find (fun th -> aconv (concl th) w) (SEVPAUX_fwd_to asl cc a)) asl;;

let SEVPAUX_REL_TAC : tactic = fun (asl,w as gl) ->
  ACCEPT_TAC (SEVPAUX_rel_prove asl w) gl;;

let SEVPAUX_ES_FIN_RW =
  [result_rel_def; exc_rel_def; ALL2; HD; TL; source_evalProof_abort_simps;
   SEVPAUX_abort_Rerr; SEVPAUX_abort_combine;
   v_rel_l_simps; source_evalProof_v_rel_Boolv; injectivity "v"; UNWIND_THM1;
   UNWIND_THM2; state_INFO.ri_accfupds; K_THM; orac_s_def; list_result_def];;

let SEVPAUX_ES_FIN_TAC : tactic =
  REWRITE_TAC SEVPAUX_ES_FIN_RW THEN
  REPEAT CONJ_TAC THEN TRY SEVPAUX_ABORT_DISCH_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE SEVPAUX_REL_TAC ORELSE SEVPAUX_BACK_TAC);;

let SEVPAUX_ES_EVAL_THL =
  [dec_clock_def; PAIR_EQ; HD; TL; do_eval_res_def; store_alloc_def; REVERSE; APPEND;
   state_INFO.ri_accfupds; K_THM; dest_thunk_def; update_thunk_def];;

let SEVPAUX_ES_GOAL_TAC : tactic =
  TRY(fun (asl,w as gl) ->
        SEVPAUX_LEMMA_RES_TAC (SEVPAUX_locals asl) gl) THEN
  SEVPAUX_POST_TAC THEN
  ONCE_REWRITE_TAC[full_evaluate_def] THEN
  (fun gl -> REPEAT(CHANGED_TAC(ASM_REWRITE_TAC (SEVPAUX_ES_EVAL_THL @ !SEVPAUX_feqs) THEN
                                CASE_REWRITE_TAC[])) gl) THEN
  SEVPAUX_EXS_TAC THEN REWRITE_TAC[] THEN SEVPAUX_ES_FIN_TAC;;

(* ---- the lemmas ---- *)

let SEVPAUX_do_log_Val = prove
 (`do_log lop v e = SOME (Val w) ==> w = v /\ (v = Boolv T \/ v = Boolv F)`,
  REWRITE_TAC[do_log_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; injectivity "exp_or_val"; distinctness "exp_or_val"] THEN
  ASM_MESON_TAC[]);;

let SEVPAUX_list_result_tyerr = prove
 (`~(list_result r = (Rerr (Rabort Rtype_error):(A list,B)result)) ==>
   ~(r = (Rerr (Rabort Rtype_error):(A,B)result))`,
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[list_result_def]);;

let SEVPAUX_combine_tyerr = prove
 (`~(combine_dec_result env (r:(v sem_env,A)result) = Rerr (Rabort Rtype_error)) ==>
   ~(r = Rerr (Rabort Rtype_error))`,
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[]);;

let SEVPAUX_v_rel_bind_exn = prove
 (`source_evalProof_v_rel es bind_exn_v bind_exn_v`,
  REWRITE_TAC[bind_exn_v_def; v_rel_l_simps; injectivity "v"; UNWIND_THM1; ALL2]);;

let SEVPAUX_env_rel_lift2 = prove
 (`source_evalProof_env_rel R e e' ==>
   source_evalProof_env_rel R
     (sem_env_REC (nsLift mn (sem_env_v e)) (nsLift mn (sem_env_c e)))
     (sem_env_REC (nsLift mn (sem_env_v e')) (nsLift mn (sem_env_c e)))`,
  DISCH_TAC THEN FIRST_ASSUM(fun th ->
    CONV_TAC (RAND_CONV (REWRITE_CONV [SYM (MATCH_MP env_rel_imp_c th)]))) THEN
  MATCH_MP_TAC SEVPAUX_env_rel_lift THEN ASM_REWRITE_TAC[]);;

let SEVPAUX_s_rel_type_stamp = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   source_evalProof_s_rel ci (state_next_type_stamp_fupd f s) (state_next_type_stamp_fupd f t)`,
  MESON_TAC[SEVPAUX_s_rel_fields]);;

let SEVPAUX_s_rel_exn_stamp = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   source_evalProof_s_rel ci (state_next_exn_stamp_fupd f s) (state_next_exn_stamp_fupd f t)`,
  MESON_TAC[SEVPAUX_s_rel_fields]);;

let SEVPAUX_s_rel_refs_rel = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   ALL2 (sv_rel (source_evalProof_v_rel (orac_s (state_eval_state t))))
     (state_refs s) (state_refs t)`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def]);;

let SEVPAUX_s_rel_store_lookup = prove
 (`store_lookup n (state_refs (s:(FFI)state)) = SOME (sv:v store_v) /\
   source_evalProof_s_rel (ci:(C)compiler_instance) s t ==>
   ?sv'. store_lookup n (state_refs t) = SOME sv' /\
         sv_rel (source_evalProof_v_rel (orac_s (state_eval_state t))) sv sv'`,
  MESON_TAC[SEVPAUX_s_rel_refs_rel; store_lookup]);;

let SEVPAUX_sv_rel_Thunk_intro = prove
 (`R v w ==> sv_rel (R:A->B->bool) (Thunk m v) (Thunk m w)`,
  REWRITE_TAC[sv_rel_def]);;

let SEVPAUX_ALL2_CONS_intro = prove
 (`(R:A->B->bool) x y ==> ALL2 R xs ys ==> ALL2 R (CONS x xs) (CONS y ys)`,
  REWRITE_TAC[ALL2] THEN MESON_TAC[]);;

let SEVPAUX_ALL2_NIL_intro = prove
 (`ALL2 (R:A->B->bool) [] []`,
  REWRITE_TAC[ALL2]);;

let SEVPAUX_v_rel_unit = prove
 (`source_evalProof_v_rel es (Conv NONE []) (Conv NONE [])`,
  REWRITE_TAC[v_rel_l_simps; injectivity "v"; UNWIND_THM1; ALL2]);;

let SEVPAUX_do_opapp_force_sim = prove
 (`do_opapp [v; Conv NONE []] = SOME (env1,e) /\ source_evalProof_v_rel es v w ==>
   ?env2. do_opapp [w; Conv NONE []] = SOME (env2,e) /\
          source_evalProof_env_rel (source_evalProof_v_rel es) env1 env2`,
  STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL SEVPAUX_do_opapp_sim) THEN
  EXISTS_TAC `[v; Conv NONE []]:v list` THEN
  ASM_REWRITE_TAC[ALL2; SEVPAUX_v_rel_unit]);;

let SEVPAUX_build_conv_sim_rev = prove
 (`build_conv envc cn (REVERSE vs) = SOME v /\ ALL2 (source_evalProof_v_rel es) vs ws ==>
   ?w. build_conv envc cn (REVERSE ws) = SOME w /\ source_evalProof_v_rel es v w`,
  MESON_TAC[SEVPAUX_build_conv_sim; EVERY2_REVERSE]);;

let SEVPAUX_do_opapp_sim_rev = prove
 (`do_opapp (REVERSE vs) = SOME (env1,e) /\ ALL2 (source_evalProof_v_rel es) vs ws ==>
   ?env2. do_opapp (REVERSE ws) = SOME (env2,e) /\
          source_evalProof_env_rel (source_evalProof_v_rel es) env1 env2`,
  MESON_TAC[SEVPAUX_do_opapp_sim; EVERY2_REVERSE]);;

let SEVPAUX_ES_FWD_LEMMAS = map SEVPAUX_CURRY
  [can_pmatch_all; pmatch_drule_form; SEVPAUX_build_conv_sim; SEVPAUX_nsLookup_sim;
   SEVPAUX_build_conv_sim_rev; SEVPAUX_do_opapp_sim_rev; SEVPAUX_do_opapp_force_sim;
   SEVPAUX_do_opapp_sim; SEVPAUX_do_log_sim; SEVPAUX_do_if_sim; do_app_sim; do_eval_sim;
   declare_env_sim; SEVPAUX_dest_thunk_rel; SEVPAUX_do_log_Val;
   SEVPAUX_list_result_tyerr; SEVPAUX_combine_tyerr; SEVPAUX_s_rel_store_lookup;
   SEVPAUX_s_rel_refs_rel; SEVPAUX_store_assign_v];;

let () = SEVPAUX_BACK_LEMMAS := map SEVPAUX_CURRY
  [SEVPAUX_env_rel_bind; SEVPAUX_env_rel_optbind; SEVPAUX_env_rel_bindlist;
   SEVPAUX_env_rel_rec_env; env_rel_extend_dec_env; env_rel_add_nsBind;
   SEVPAUX_env_rel_alist; SEVPAUX_env_rel_empty_v; SEVPAUX_env_rel_rec_env2;
   SEVPAUX_env_rel_sing; SEVPAUX_env_rel_lift; SEVPAUX_combine_dec_result_rel;
   SEVPAUX_list_result_rel; SEVPAUX_v_rel_bind_exn; SEVPAUX_env_rel_lift2;
   SEVPAUX_s_rel_type_stamp; SEVPAUX_s_rel_exn_stamp; SEVPAUX_sv_rel_Thunk_intro;
   SEVPAUX_ALL2_CONS_intro; SEVPAUX_ALL2_NIL_intro; SEVPAUX_v_rel_unit;
   DISCH_ALL (CONJUNCT1 (UNDISCH (SPEC_ALL SEVPAUX_s_rel_refs)));
   DISCH_ALL (SPEC_ALL (CONJUNCT2 (UNDISCH (SPEC_ALL SEVPAUX_s_rel_refs))))];;

(* ---- the cases ---- *)

let SEVPAUX_TYERR_CONTR_TAC : tactic =
  TRY(FIRST_ASSUM(fun th ->
        let th' = REWRITE_RULE SEVPAUX_NOT_TYERR_RW th in
        if concl th' = `F` then CONTR_TAC th' else NO_TAC));;

let SEVPAUX_ROUND_TAC : tactic =
  SEVPAUX_POST_TAC THEN SEVPAUX_SING_TAC THEN SEVPAUX_POST_TAC THEN
  SEVPAUX_SREL_CLOCK_TAC THEN SEVPAUX_FIELDS_TAC THEN
  REPEAT((fun (asl,w as gl) ->
            SEVPAUX_LEMMA_RES_TAC SEVPAUX_ES_FWD_LEMMAS gl)
         THEN SEVPAUX_POST_TAC THEN
         SEVPAUX_SING_TAC THEN SEVPAUX_SREL_CLOCK_TAC THEN SEVPAUX_FIELDS_TAC THEN
         SEVPAUX_POST_TAC);;

let SEVPAUX_ES_PREP_TAC : tactic =
  (fun gl -> SEVPAUX_produced := []; SEVPAUX_feqs := []; SEVPAUX_name_counter := 0;
             ALL_TAC gl) THEN
  REPEAT DISCH_TAC THEN SEVPAUX_TYERR_CONTR_TAC THEN
  SEVPAUX_DROP_GENERAL_IH_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_imp (concl th) || is_forall (concl th)
                           then REWRITE_RULE[IMP_CONJ] th else th) THEN
  SEVPAUX_ROUND_TAC;;

let SEVPAUX_ES_IHS_TAC : tactic =
  REPEAT(SEVPAUX_IH_STEP_TAC THEN SEVPAUX_ROUND_TAC);;

let SEVPAUX_ES_TAC : tactic =
  SEVPAUX_ES_PREP_TAC THEN SEVPAUX_ES_IHS_TAC THEN SEVPAUX_ES_GOAL_TAC;;

let eval_simulation = prove
 (`(!(s:(FFI)state) env exps s' res (es:eval_oracle_state) t env'.
      evaluate s env exps = (s',res) /\
      source_evalProof_s_rel (ci:(C)compiler_instance) s t /\
      source_evalProof_env_rel (source_evalProof_v_rel (orac_s (state_eval_state t))) env env' /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      ?es' t' res'.
        evaluate t env' exps = (t',res') /\
        source_evalProof_s_rel ci s' t' /\
        es' = orac_s (state_eval_state t') /\
        result_rel (ALL2 (source_evalProof_v_rel es')) (source_evalProof_v_rel es') res res' /\
        es_forward (orac_s (state_eval_state t)) es' /\
        (~source_evalProof_abort res' ==> es_stack_forward (orac_s (state_eval_state t)) es')) /\
   (!(s:(FFI)state) env x pes err_x s' res es t env' y err_y.
      evaluate_match s env x pes err_x = (s',res) /\
      source_evalProof_s_rel ci s t /\
      es = orac_s (state_eval_state t) /\
      source_evalProof_env_rel (source_evalProof_v_rel es) env env' /\
      source_evalProof_v_rel es x y /\
      source_evalProof_v_rel es err_x err_y /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      ?es' t' res'.
        evaluate_match t env' y pes err_y = (t',res') /\
        source_evalProof_s_rel ci s' t' /\
        es' = orac_s (state_eval_state t') /\
        result_rel (ALL2 (source_evalProof_v_rel es')) (source_evalProof_v_rel es') res res' /\
        es_forward es es' /\
        (~source_evalProof_abort res' ==> es_stack_forward es es')) /\
   (!(s:(FFI)state) env decs s' res t env'.
      evaluate_decs s env decs = (s',res) /\
      source_evalProof_s_rel ci s t /\
      source_evalProof_env_rel (source_evalProof_v_rel (orac_s (state_eval_state t))) env env' /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      ?es' t' res'.
        evaluate_decs t env' decs = (t',res') /\
        source_evalProof_s_rel ci s' t' /\
        es' = orac_s (state_eval_state t') /\
        result_rel (source_evalProof_env_rel (source_evalProof_v_rel es'))
          (source_evalProof_v_rel es') res res' /\
        es_forward (orac_s (state_eval_state t)) es' /\
        (~source_evalProof_abort res' ==> es_stack_forward (orac_s (state_eval_state t)) es'))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  SEVPAUX_ES_TAC);;

let source_evalProof_check_dup_ctors_thm = prove
 (`check_dup_ctors (tvs,tn,condefs) <=> ALL_DISTINCT (MAP FST condefs)`,
  REWRITE_TAC[check_dup_ctors_def; LET_DEF; LET_END_DEF] THEN AP_TERM_TAC THEN
  SPEC_TAC(`condefs:(mlstring#ast_t list)list`,`l:(mlstring#ast_t list)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAP] THEN
  SPEC_TAC(`h:mlstring#ast_t list`,`h:mlstring#ast_t list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let do_eval_oracle_def = cake_def
  `do_eval_oracle (f:compiler_fun) (g:dec list->dec list) vs (orac:eval_oracle_fun) =
     match vs with
       [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] ->
         (match orac 0 with
            (env_id,st,decs) ->
              (match (f (env_id,st,decs),v_to_word8_list bs_v,v_to_word64_list ws_v) with
                 (SOME (st_v2,c_bs,c_ws),SOME bs,SOME ws) ->
                   if bs = c_bs /\ ws = c_ws /\ st_v2 = FST (SND (orac 1))
                   then SOME (env_id,shift_seq 1 orac,g decs)
                   else NONE
               | _ -> NONE))
     | _ -> NONE`;;

let insert_gen_oracle_def = cake_def
  `insert_gen_oracle (ci:(C)compiler_instance) g (shift_f:compiler_args->num)
                     (orac:eval_oracle_fun) es =
     match es with
       SOME (EvalOracle s) ->
         SOME (EvalOracle
                 (eval_oracle_state_custom_do_eval_fupd
                    (K (do_eval_oracle (mk_compiler_fun_from_ci ci) g))
                    (eval_oracle_state_oracle_fupd
                       (K (shift_seq (shift_f (eval_oracle_state_oracle s 0)) orac)) s)))
     | _ -> es`;;

let orac_agrees_def = cake_def
  `orac_agrees (orac:eval_oracle_fun) es <=>
     match es with
       SOME (EvalOracle s) ->
         (!j. j < FST (FST (eval_oracle_state_oracle s 0)) ==>
              orac j = eval_oracle_state_oracle s (j + 1))
     | _ -> F`;;

(* the infinite extension of an oracle is still well-formed with respect to *)
(* the compiler function                                                     *)
let orac_extended_wf_def = cake_def
  `orac_extended_wf (f:compiler_args->(v#B)option) (orac:eval_oracle_fun) <=>
     (!i x. f (orac i) = SOME x ==> FST x = FST (SND (orac (SUC i))))`;;

let record_forward_def = cake_def
  `record_forward es es' <=>
     match es with
       SOME (EvalOracle s) ->
         ?s'. es' = SOME (EvalOracle s') /\
              FST (FST (eval_oracle_state_oracle s 0)) <=
                FST (FST (eval_oracle_state_oracle s' 0)) /\
              (!j. 0 < j /\ j < FST (FST (eval_oracle_state_oracle s 0)) + 1 ==>
                   eval_oracle_state_oracle s' j = eval_oracle_state_oracle s j)
     | _ -> (match es' with SOME (EvalOracle _) -> F | _ -> T)`;;

let record_forward_refl = prove
 (`record_forward es es`,
  REWRITE_TAC[record_forward_def] THEN EVERY_CASE_TAC THEN MESON_TAC[LE_REFL]);;

let record_forward_trans = prove
 (`record_forward es1 es2 /\ record_forward es2 es3 ==> record_forward es1 es3`,
  REWRITE_TAC[record_forward_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[injectivity "option"; injectivity "eval_state"; distinctness "option";
              distinctness "eval_state"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s2:eval_oracle_state` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `s3:eval_oracle_state` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
                                                 is_var(rhs(concl th)))) THEN
  EXISTS_TAC `s3:eval_oracle_state` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LE_TRANS];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j < FST (FST (eval_oracle_state_oracle s2 0)) + 1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let orac_agrees_backward = prove
 (`orac_agrees orac es2 /\ record_forward es1 es2 ==> orac_agrees orac es1`,
  ASM_CASES_TAC `?s1. es1 = SOME (EvalOracle s1)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `s1:eval_oracle_state` SUBST_ALL_TAC) THEN
    REWRITE_TAC[record_forward_def] THEN CASE_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
      (X_CHOOSE_THEN `s2:eval_oracle_state` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[orac_agrees_def] THEN CASE_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j < FST (FST (eval_oracle_state_oracle s2 0)) /\ 0 < j + 1 /\
                  j + 1 < FST (FST (eval_oracle_state_oracle s1 0)) + 1`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[orac_agrees_def; record_forward_def] THEN
    EVERY_CASE_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "eval_state";
      distinctness "option"; distinctness "eval_state"] THEN MESON_TAC[]]);;

let is_record_def = cake_def
  `is_record (ci:(C)compiler_instance) es <=>
     match es with
       SOME (EvalOracle s) -> eval_oracle_state_custom_do_eval s = do_eval_record ci
     | _ -> F`;;

let is_record_IMP = prove
 (`is_record (ci:(C)compiler_instance) es ==> ?orac_st. es = SOME (EvalOracle orac_st)`,
  REWRITE_TAC[is_record_def] THEN EVERY_CASE_TAC THEN MESON_TAC[]);;

let SEVPAUX_do_eval_EvalOracle =
  CAKE_SIMP_CONV ([do_eval_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] @
                  EVALAUX_do_app_eqs @ [case_eq "eval_state"])
  `do_eval vs (SOME (EvalOracle s)) = SOME (env,decs,es)`;;

let SEVPAUX_do_eval_record_SOME =
  CAKE_SIMP_CONV ([do_eval_record_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                   LET_DEF; LET_END_DEF] @ EVALAUX_do_app_eqs)
  `do_eval_record (ci:(C)compiler_instance) vs orac = SOME (env_id,orac',decs)`;;

let SEVPAUX_compiler_agrees_SOME = prove
 (`compiler_agrees f args (st_v,bs_v,ws_v) ==>
   ?bs ws. f args = SOME (st_v,bs,ws) /\ v_to_word8_list bs_v = SOME bs /\
           v_to_word64_list ws_v = SOME ws`,
  REWRITE_TAC[compiler_agrees_def] THEN EVERY_CASE_TAC THEN MESON_TAC[]);;

let SEVPAUX_recorded_orac_wf_step = prove
 (`!compiler orac args st_v2 bs_v ws_v n.
     FST (FST (orac 0)) = n /\ recorded_orac_wf (compiler:compiler_fun) orac /\
     compiler_agrees compiler args (st_v2,bs_v,ws_v) /\
     (0 < n ==> FST (SND args) = FST (SND (orac 0)))
     ==> recorded_orac_wf compiler
           (\j. if j = 0 then ((n + 1,0),st_v2,[])
                else if j = SUC n then args else orac j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC recorded_orac_wf_step THEN ASM_REWRITE_TAC[]);;

let SEVPAUX_lookup_env_fupds = prove
 (`(!f s. lookup_env (eval_oracle_state_custom_do_eval_fupd f s) = lookup_env s) /\
   (!f s. lookup_env (eval_oracle_state_oracle_fupd f s) = lookup_env s) /\
   (!f s. lookup_env (eval_oracle_state_generation_fupd f s) = lookup_env s)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; lookup_env_def;
              eval_oracle_state_INFO.ri_accfupds]);;

let insert_do_eval = prove
 (`do_eval vs es = SOME (env,decs,es') /\ is_record (ci:(C)compiler_instance) es ==>
   is_record ci es' /\
   record_forward es es' /\
   (orac_agrees orac es' /\ orac_extended_wf (mk_compiler_fun_from_ci ci) orac ==>
    do_eval vs (insert_gen_oracle ci I (FST o FST) orac es) =
    SOME (env,decs,insert_gen_oracle ci I (FST o FST) orac es')) /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (eval_oracle_state_oracle (orac_s es)) ==>
    recorded_orac_wf (mk_compiler_fun_from_ci ci) (eval_oracle_state_oracle (orac_s es')))`,
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `s:eval_oracle_state` SUBST_ALL_TAC o MATCH_MP is_record_IMP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_record_def]) THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "do_eval")) THEN
  ASM_REWRITE_TAC[SEVPAUX_do_eval_EvalOracle; SEVPAUX_do_eval_record_SOME] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `es':eval_state option`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && is_abs(lhs(concl th)))) THEN
  REWRITE_TAC[is_record_def; record_forward_def; insert_gen_oracle_def; orac_s_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[add_env_generation_def; eval_oracle_state_INFO.ri_accfupds; K_THM;
              injectivity "option"; injectivity "eval_state"; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[ARITH_RULE `x <= x + 1`; FST; o_THM] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < j ==> ~(j = 0)`; ARITH_RULE `j < n + 1 ==> ~(j = SUC n)`];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x'':num` o CASE_REWRITE_RULE[orac_agrees_def] o
      check (SEVPAUX_has_const "orac_agrees")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[ARITH_RULE `x < x + 1 /\ ~(x + 1 = 0) /\ x + 1 = SUC x`] THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `bs:byte list` (X_CHOOSE_THEN `ws:int64 list` STRIP_ASSUME_TAC) o
      MATCH_MP SEVPAUX_compiler_agrees_SOME) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x'':num` o REWRITE_RULE[orac_extended_wf_def] o
      check (SEVPAUX_has_const "orac_extended_wf")) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(a0''':v,bs:byte list,ws:int64 list)`) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[do_eval_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM; do_eval_oracle_def] THEN
    CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[shift_seq_def; ADD_CLAUSES; I_THM] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REPEAT(CHANGED_TAC(CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; I_THM; eval_oracle_state_INFO.ri_accfupds; K_THM] THEN
      CASE_REWRITE_TAC[])) THEN
    REWRITE_TAC[ARITH_RULE `1 + x = SUC x`] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SEVPAUX_lookup_env_fupds] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ; injectivity "eval_state"] THEN
    REWRITE_TAC[eval_oracle_state_component_equality; add_env_generation_def;
                eval_oracle_state_INFO.ri_accfupds; K_THM; FUN_EQ_THM] THEN
    REWRITE_TAC[ARITH_RULE `(i + 1) + x = SUC (i + x)`];
    DISCH_TAC THEN MATCH_MP_TAC SEVPAUX_recorded_orac_wf_step THEN
    ASM_REWRITE_TAC[FST; SND] THEN REWRITE_TAC[ETA_AX] THEN
    MAP_EVERY EXISTS_TAC [`a0'''':v`; `a0''''':v`] THEN ASM_REWRITE_TAC[]]);;

let insert_declare_env = prove
 (`declare_env es1 env = SOME (x,es2) /\ is_record (ci:(C)compiler_instance) es1 ==>
   is_record ci es2 /\
   record_forward es1 es2 /\
   (orac_agrees orac es2 ==>
    declare_env (insert_gen_oracle ci I (FST o FST) orac es1) env =
    SOME (x,insert_gen_oracle ci I (FST o FST) orac es2)) /\
   (recorded_orac_wf (mk_compiler_fun_from_ci ci) (eval_oracle_state_oracle (orac_s es1)) ==>
    recorded_orac_wf (mk_compiler_fun_from_ci ci) (eval_oracle_state_oracle (orac_s es2)))`,
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `s:eval_oracle_state` SUBST_ALL_TAC o MATCH_MP is_record_IMP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_record_def]) THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (SEVPAUX_has_const "declare_env")) THEN
  REWRITE_TAC[declare_env_def; oEL_THM] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[is_record_def; record_forward_def; insert_gen_oracle_def; orac_s_def] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM; injectivity "option";
                  injectivity "eval_state"; UNWIND_THM1; LE_REFL] THEN
  REWRITE_TAC[declare_env_def; oEL_THM] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; injectivity "eval_state";
              eval_oracle_state_component_equality; eval_oracle_state_INFO.ri_accfupds;
              K_THM]);;

let reset_env_generation_orac_eqs = prove
 (`(is_record (ci:(C)compiler_instance) (reset_env_generation es2 es3) <=> is_record ci es3) /\
   (record_forward es1 (reset_env_generation es2 es3) <=> record_forward es1 es3) /\
   (orac_agrees orac (reset_env_generation es2 es3) <=> orac_agrees orac es3) /\
   (reset_env_generation (insert_gen_oracle ci I (FST o FST) orac es1) es2 =
    reset_env_generation es1 es2) /\
   (reset_env_generation es1 (insert_gen_oracle ci I (FST o FST) orac es2) =
    insert_gen_oracle ci I (FST o FST) orac (reset_env_generation es1 es2)) /\
   (eval_oracle_state_oracle (orac_s (reset_env_generation es2 es3)) =
    eval_oracle_state_oracle (orac_s es3))`,
  REWRITE_TAC[is_record_def; reset_env_generation_def; insert_gen_oracle_def] THEN
  EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[record_forward_def; orac_agrees_def; orac_s_def;
                  eval_oracle_state_INFO.ri_accfupds; K_THM; injectivity "option";
                  injectivity "eval_state"; eval_oracle_state_INFO.ri_fupdcanon;
                  eval_oracle_state_INFO.ri_accfupds] THEN
  CASE_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM; injectivity "option";
                   injectivity "eval_state"] THEN
  REWRITE_TAC[UNWIND_THM1; eval_oracle_state_INFO.ri_accfupds]);;

(* HOL4 [local] *)
let record_forward_trans_sym = prove
 (`record_forward es2 es3 /\ record_forward es1 es2 ==> record_forward es1 es3`,
  MESON_TAC[record_forward_trans]);;

let SEVPAUX_DEDUP_TAC : tactic = fun (asl,w) ->
  let rec dedup seen = function
      [] -> []
    | (l,th)::rest -> if exists (aconv (concl th)) seen then dedup seen rest
                      else (l,th)::dedup (concl th::seen) rest in
  (null_meta,[dedup [] asl,w],fun i ths -> hd ths);;

(* the closure of the assumptions under modus ponens (with the non-       *)
(* quantified implications among them), conjunctions split                  *)
let SEVPAUX_MP_SAT_TAC : tactic = fun (asl,w as gl) ->
  let dedup l = itlist (fun th acc -> if exists (fun t -> aconv (concl t) (concl th)) acc
                                      then acc else th::acc) l [] in
  let rec go facts acc =
    let news = flat (map (fun th ->
        let c = concl th in
        if is_imp c then
          match filter (fun f -> aconv (concl f) (lhand c)) facts with
            f::_ -> CONJUNCTS (MP th f)
          | [] -> []
        else []) facts) in
    let news = dedup (filter (fun t -> not (exists (fun f -> aconv (concl f) (concl t)) facts))
                       news) in
    if news = [] then acc else go (news @ facts) (news @ acc) in
  let facts = flat (map (CONJUNCTS o snd) asl) in
  MAP_EVERY ASSUME_TAC (rev (go facts [])) gl;;

(* record_forward from the record_forward facts among the assumptions *)
let SEVPAUX_RF_TAC : tactic = fun (asl,w as gl) ->
  let rfs = filter (fun th -> let c = concl th in
               is_comb c && is_comb(rator c) && is_const(rator(rator c)) &&
               fst(dest_const(rator(rator c))) = "record_forward") (map snd asl) in
  MESON_TAC(record_forward_refl :: record_forward_trans :: rfs) gl;;

(* the goals of evaluate_is_record_forward from the facts of the runs *)
let SEVPAUX_REC_FIN_TAC : tactic =
  REPEAT CONJ_TAC THEN REPEAT DISCH_TAC THEN SEVPAUX_MP_SAT_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; SEVPAUX_RF_TAC;
         ASM_MESON_TAC[record_forward_refl; record_forward_trans]];;

(* the closing tactic of evaluate_is_record_forward: chain the facts of the  *)
(* runs among the assumptions (induction hypotheses, insert_do_eval,         *)
(* insert_declare_env) by transitivity                                       *)
let SEVPAUX_REC_CLOSE_TAC : tactic =
  REPEAT STRIP_TAC THEN RES_TAC THEN SEVPAUX_DEDUP_TAC THEN RES_TAC THEN SEVPAUX_DEDUP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM]) THEN
  RES_TAC THEN SEVPAUX_DEDUP_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  TRY(IMP_RES_TAC insert_do_eval) THEN TRY(IMP_RES_TAC insert_declare_env) THEN
  RULE_ASSUM_TAC SPEC_ALL THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM]) THEN
  RES_TAC THEN SEVPAUX_DEDUP_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[reset_env_generation_orac_eqs; state_INFO.ri_accfupds; K_THM] THEN
  SEVPAUX_REC_FIN_TAC;;

let evaluate_is_record_forward = prove
 (`(!(s:(FFI)state) env exps s' res.
      evaluate s env exps = (s',res) /\ is_record (ci:(C)compiler_instance) (state_eval_state s) ==>
      is_record ci (state_eval_state s') /\
      record_forward (state_eval_state s) (state_eval_state s') /\
      (recorded_orac_wf (mk_compiler_fun_from_ci ci)
         (eval_oracle_state_oracle (orac_s (state_eval_state s))) ==>
       recorded_orac_wf (mk_compiler_fun_from_ci ci)
         (eval_oracle_state_oracle (orac_s (state_eval_state s'))))) /\
   (!(s:(FFI)state) env x pes err_x s' res.
      evaluate_match s env x pes err_x = (s',res) /\ is_record ci (state_eval_state s) ==>
      is_record ci (state_eval_state s') /\
      record_forward (state_eval_state s) (state_eval_state s') /\
      (recorded_orac_wf (mk_compiler_fun_from_ci ci)
         (eval_oracle_state_oracle (orac_s (state_eval_state s))) ==>
       recorded_orac_wf (mk_compiler_fun_from_ci ci)
         (eval_oracle_state_oracle (orac_s (state_eval_state s'))))) /\
   (!(s:(FFI)state) env decs s' res.
      evaluate_decs s env decs = (s',res) /\ is_record ci (state_eval_state s) ==>
      is_record ci (state_eval_state s') /\
      record_forward (state_eval_state s) (state_eval_state s') /\
      (recorded_orac_wf (mk_compiler_fun_from_ci ci)
         (eval_oracle_state_oracle (orac_s (state_eval_state s))) ==>
       recorded_orac_wf (mk_compiler_fun_from_ci ci)
         (eval_oracle_state_oracle (orac_s (state_eval_state s')))))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  SEVPAUX_REC_CLOSE_TAC);;

(* the inductions over evaluate below use evaluateProps' EVPROPSAUX_HYP_SPLIT2_TAC, *)
(* EVPROPSAUX_IH_DISCH_TAC and EVPROPSAUX_GOAL_EVAL_TAC                          *)

let SEVPAUX_RECFWD_TAC : tactic =
  let rules = CONJUNCTS evaluate_is_record_forward @ [insert_do_eval; insert_declare_env] in
  let spec_free th =
    let c = concl th in
    if is_forall c then
      let v,_ = dest_forall c in
      let n = fst(dest_var v) in
      if n = "orac" || n = "ci" then SPEC v th else th
    else th in
  let isrec_res : tactic = fun (asl,w as gl) ->
    let ths = map snd asl in
    let facts = filter (fun th -> let c = concl th in
       is_comb c && is_comb(rator c) && is_const(rator(rator c)) &&
       fst(dest_const(rator(rator c))) = "is_record") ths in
    let res = flat (map (fun th -> let c = concl th in
       if is_imp c then mapfilter (fun f -> if aconv (concl f) (lhand c) then MP th f
                                            else failwith "") facts
       else []) ths) in
    MAP_EVERY CAKE_STRIP_ASSUME_TAC res gl in
  let step = EVERY (map IMP_RES_TAC rules) THEN
             RULE_ASSUM_TAC (spec_free o spec_free) THEN
             RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM;
                                         reset_env_generation_orac_eqs]) THEN
             isrec_res THEN
             REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
             SEVPAUX_DEDUP_TAC in
  step THEN step THEN step THEN step;;

(* orac_agrees for the earlier states: back along record_forward            *)
let SEVPAUX_AGREES_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let rfs = filter (fun th -> let c = concl th in
               is_comb c && is_comb(rator c) && is_const(rator(rator c)) &&
               fst(dest_const(rator(rator c))) = "record_forward") ths in
  let ags0 = filter (fun th -> let c = concl th in
               is_comb c && is_comb(rator c) && is_const(rator(rator c)) &&
               fst(dest_const(rator(rator c))) = "orac_agrees") ths in
  let rec close ags =
    let news = flat (map (fun ag -> mapfilter (fun rf ->
        let th = MATCH_MP orac_agrees_backward (CONJ ag rf) in
        if exists (fun a -> aconv (concl a) (concl th)) ags then failwith "old" else th) rfs) ags) in
    if news = [] then ags else close (news @ ags) in
  let ags = close ags0 in
  MAP_EVERY ASSUME_TAC (filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) ags0)) ags) gl;;

let SEVPAUX_IOC_TAC : tactic =
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (list_result_eq_Rerr :: combine_dec_result_eq_Rerr ::
                               EVPROPSAUX_REC_RW)) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SEVPAUX_RECFWD_TAC THEN SEVPAUX_AGREES_TAC THEN
  EVPROPSAUX_IH_DISCH_TAC THEN EVPROPSAUX_IH_DISCH_TAC THEN EVPROPSAUX_IH_DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  EVPROPSAUX_GOAL_EVAL_TAC [do_eval_res_def; reset_env_generation_orac_eqs; o_THM];;

let insert_oracle_correct = prove
 (`(!(s:(FFI)state) env exps s' res.
      evaluate s env exps = (s',res) /\ is_record (ci:(C)compiler_instance) (state_eval_state s) /\
      orac_agrees orac (state_eval_state s') /\
      orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      evaluate (state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac) s) env exps =
      (state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac) s',res)) /\
   (!(s:(FFI)state) env x pes err_x s' res.
      evaluate_match s env x pes err_x = (s',res) /\ is_record ci (state_eval_state s) /\
      orac_agrees orac (state_eval_state s') /\
      orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      evaluate_match (state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac) s)
        env x pes err_x =
      (state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac) s',res)) /\
   (!(s:(FFI)state) env decs s' res.
      evaluate_decs s env decs = (s',res) /\ is_record ci (state_eval_state s) /\
      orac_agrees orac (state_eval_state s') /\
      orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      evaluate_decs (state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac) s) env decs =
      (state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac) s',res))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  SEVPAUX_IOC_TAC);;

let v_rel_concrete_v = prove
 (`(!v. concrete_v v ==> source_evalProof_v_rel es v v) /\
   (!vs. concrete_v_list vs ==> ALL2 (source_evalProof_v_rel es) vs vs)`,
  MATCH_MP_TAC concrete_v_ind THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN CASES_ON `v:v` THEN
    REWRITE_TAC[distinctness "v"; injectivity "v"; SEVPAUX_concrete_v_thm; v_rel_l_simps] THEN
    REWRITE_TAC[GSYM SEVPAUX_concrete_v_list] THEN MESON_TAC[];
    REWRITE_TAC[ALL2];
    REWRITE_TAC[concrete_v_def; ALL2] THEN MESON_TAC[]]);;

let env_rel_concrete_v = prove
 (`nsAll (K concrete_v) (sem_env_v env) ==>
   source_evalProof_env_rel (source_evalProof_v_rel es) env env`,
  REWRITE_TAC[source_evalProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y:v = x` SUBST1_TAC THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  MATCH_MP_TAC (CONJUNCT1 v_rel_concrete_v) THEN
  MP_TAC(ISPECL [`sem_env_v (env:v sem_env)`; `nm:(mlstring,mlstring)id`;
                 `K concrete_v:(mlstring,mlstring)id->v->bool`; `x:v`] nsLookup_nsAll) THEN
  ASM_REWRITE_TAC[K_THM]);;

(* HOL4 [local] *)
let neq_IMP_to_cases = prove
 (`!y:A. (~(x = y) ==> P) ==> x = y \/ ~(x = y)`,
  MESON_TAC[]);;

(* HOL4 [local] *)
let less_sub_1_cases = prove
 (`k <= clock /\ (k <= clock - 1 ==> P) ==> k = clock \/ k <= clock - 1`,
  ARITH_TAC);;

(* tactics for evaluate_record_suffix *)
let SEVPAUX_ERS_STEP_TAC : tactic =
  EVPROPSAUX_IH_DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_disj c || is_exists c || is_conj c then CAKE_STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW);;

(* terms used by the clock tactics, parsed once *)
let SEVPAUX_k = `k:num` and SEVPAUX_0 = `0` and SEVPAUX_1 = `1`
and SEVPAUX_minus = `(-):num->num->num` and SEVPAUX_le = `(<=):num->num->bool`
and SEVPAUX_num = `:num`;;

(* the facts about clocks among the assumptions *)
let SEVPAUX_is_arith_fact tm =
  let t = if is_neg tm then rand tm else tm in
  (is_eq t && type_of (lhs t) = SEVPAUX_num) ||
  (is_comb t && is_comb (rator t) && is_const (rator (rator t)) &&
   mem (fst(dest_const(rator(rator t)))) ["<="; "<"] &&
   type_of (rand t) = SEVPAUX_num);;

(* the atoms of a linear fact *)
let rec SEVPAUX_num_atoms tm =
  match tm with
    Comb(Comb(Const(("+"|"-"|"*"|"<="|"<"|"="),_),a),b) ->
      union (SEVPAUX_num_atoms a) (SEVPAUX_num_atoms b)
  | Comb(Const("~",_),a) -> SEVPAUX_num_atoms a
  | _ -> if is_numeral tm then [] else [tm];;

(* prove tm (a fact about numbers) from the arithmetic assumptions connected *)
(* to it through atoms other than k; the ARITH_RULE results are memoised      *)
let SEVPAUX_arith_cache = ref ([] : (term * thm option) list);;
let SEVPAUX_try_arith asl tm =
  let fths = filter (fun th -> SEVPAUX_is_arith_fact (concl th)) (map snd asl) in
  let fat = map (fun th -> th, subtract (SEVPAUX_num_atoms (concl th)) [SEVPAUX_k]) fths in
  let rec grow ats =
    let ats' = itlist (fun (_,a) acc -> if intersect a acc <> [] then union a acc else acc)
                 fat ats in
    if length ats' = length ats then ats else grow ats' in
  let ats = grow (subtract (SEVPAUX_num_atoms tm) [SEVPAUX_k]) in
  let fths = map fst (filter (fun (_,a) -> a = [] || intersect a ats <> []) fat) in
  let fths = itlist (fun th acc -> if exists (fun t -> aconv (concl t) (concl th)) acc
                                   then acc else th::acc) fths [] in
  let imp = itlist (fun f t -> mk_imp(concl f,t)) fths tm in
  let th = match filter (fun (t,_) -> aconv t imp) (!SEVPAUX_arith_cache) with
      (_,Some th)::_ -> th
    | (_,None)::_ -> failwith "SEVPAUX_try_arith"
    | [] -> (try let th = ARITH_RULE imp in
                 SEVPAUX_arith_cache := (imp,Some th) :: !SEVPAUX_arith_cache; th
             with e -> (SEVPAUX_arith_cache := (imp,None) :: !SEVPAUX_arith_cache; raise e)) in
  rev_itlist (fun f th -> MP th f) fths th;;

(* the clocks t tested by the original run (assumptions t = 0 or ~(t = 0)) *)
let SEVPAUX_clocks asl =
  mapfilter (fun (_,th) -> let c = concl th in
      let c' = if is_neg c then rand c else c in
      if is_eq c' && rhs c' = SEVPAUX_0 && is_comb (lhs c') && is_const(rator(lhs c')) &&
         fst(dest_const(rator(lhs c'))) = "state_clock" then lhs c' else failwith "") asl;;

(* for each tested clock t: the facts t - k = 0 and k <= t - 1 or their    *)
(* negations, when they follow from the arithmetic assumptions             *)
let SEVPAUX_CLOCK_FACTS_TAC : tactic = fun (asl,w as gl) ->
  let ts = setify (SEVPAUX_clocks asl) in
  let known tm = exists (fun (_,th) -> aconv (concl th) tm) asl in
  let cands = flat (map (fun t ->
      let tk = mk_eq(mk_binop SEVPAUX_minus t SEVPAUX_k, SEVPAUX_0) in
      let k1 = mk_binop SEVPAUX_le SEVPAUX_k (mk_binop SEVPAUX_minus t SEVPAUX_1) in
      if known tk || known (mk_neg tk) then
        (if known k1 || known (mk_neg k1) then [] else [k1; mk_neg k1])
      else if known k1 || known (mk_neg k1) then [tk; mk_neg tk]
      else [tk; mk_neg tk; k1; mk_neg k1]) ts) in
  let ths = mapfilter (SEVPAUX_try_arith asl) cands in
  MAP_EVERY ASSUME_TAC ths gl;;

(* case split on t - k = 0 for the first tested clock t where it is open *)
let SEVPAUX_CLOCK_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let ts = setify (SEVPAUX_clocks asl) in
  let undecided = filter (fun t ->
      let tk = mk_eq(mk_binop SEVPAUX_minus t SEVPAUX_k, SEVPAUX_0) in
      not (exists (fun (_,th) -> aconv (concl th) tk || aconv (concl th) (mk_neg tk)) asl)) ts in
  match undecided with
    [] -> failwith "SEVPAUX_CLOCK_SPLIT_TAC"
  | t::_ -> ASM_CASES_TAC (mk_eq(mk_binop SEVPAUX_minus t SEVPAUX_k, SEVPAUX_0)) gl;;

let SEVPAUX_SUB1_K = ARITH_RULE `!a. (a - 1) - k = (a - k) - 1`;;

let SEVPAUX_ERS_THL = [do_eval_res_def; combine_dec_result_def; SEVPAUX_SUB1_K; SUB_0];;

let SEVPAUX_FIN_CLOSE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun (asl,w as gl) -> ACCEPT_TAC (SEVPAUX_try_arith asl w) gl) ORELSE
   SEVPAUX_RF_TAC) THEN NO_TAC;;

(* the goal's run evaluated with the assumptions: either the same result    *)
(* (first disjunct) or a timeout whose state is record_forward (second)     *)
let SEVPAUX_ERS_FIN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[SEVPAUX_SUB1_K]) THEN
  EVPROPSAUX_GOAL_EVAL_TAC SEVPAUX_ERS_THL THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; state_INFO.ri_accfupds; K_THM;
              reset_env_generation_orac_eqs] THEN
  FIRST [SEVPAUX_FIN_CLOSE_TAC;
         DISJ1_TAC THEN SEVPAUX_FIN_CLOSE_TAC;
         DISJ2_TAC THEN SEVPAUX_FIN_CLOSE_TAC];;

let SEVPAUX_ERS_ROUND_TAC : tactic = SEVPAUX_CLOCK_FACTS_TAC THEN SEVPAUX_ERS_STEP_TAC;;

let SEVPAUX_ERS_TAC : tactic =
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (list_result_eq_Rerr :: combine_dec_result_eq_Rerr ::
                               EVPROPSAUX_REC_RW)) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SEVPAUX_RECFWD_TAC THEN
  SEVPAUX_ERS_STEP_TAC THEN SEVPAUX_ERS_ROUND_TAC THEN
  TRY SEVPAUX_CLOCK_SPLIT_TAC THEN
  SEVPAUX_ERS_ROUND_TAC THEN SEVPAUX_ERS_ROUND_TAC THEN
  TRY SEVPAUX_CLOCK_SPLIT_TAC THEN
  SEVPAUX_ERS_ROUND_TAC THEN SEVPAUX_CLOCK_FACTS_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  SEVPAUX_ERS_FIN_TAC;;

let evaluate_record_suffix = prove
 (`(!(s:(FFI)state) env exps s' res.
      evaluate s env exps = (s',res) /\ is_record (ci:(C)compiler_instance) (state_eval_state s) /\
      k <= state_clock s ==>
      let ev = evaluate (state_clock_fupd (\c. c - k) s) env exps in
      (k <= state_clock s' /\ ev = (state_clock_fupd (\c. c - k) s',res)) \/
      (?s''. ev = (s'',Rerr (Rabort Rtimeout_error)) /\
             record_forward (state_eval_state s'') (state_eval_state s'))) /\
   (!(s:(FFI)state) env x pes err_x s' res.
      evaluate_match s env x pes err_x = (s',res) /\ is_record ci (state_eval_state s) /\
      k <= state_clock s ==>
      let ev = evaluate_match (state_clock_fupd (\c. c - k) s) env x pes err_x in
      (k <= state_clock s' /\ ev = (state_clock_fupd (\c. c - k) s',res)) \/
      (?s''. ev = (s'',Rerr (Rabort Rtimeout_error)) /\
             record_forward (state_eval_state s'') (state_eval_state s'))) /\
   (!(s:(FFI)state) env decs s' res.
      evaluate_decs s env decs = (s',res) /\ is_record ci (state_eval_state s) /\
      k <= state_clock s ==>
      let ev = evaluate_decs (state_clock_fupd (\c. c - k) s) env decs in
      (k <= state_clock s' /\ ev = (state_clock_fupd (\c. c - k) s',res)) \/
      (?s''. ev = (s'',Rerr (Rabort Rtimeout_error)) /\
             record_forward (state_eval_state s'') (state_eval_state s')))`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  SEVPAUX_ERS_TAC);;

(* Constructs the oracle from an evaluation by using the recorded events,  *)
(* padding with null events if necessary.                                  *)

let extract_oracle_def = cake_def
  `extract_oracle (s:(FFI)state) env decs n =
     match (OLEAST k. ?s' (res:(v sem_env,v)result).
              evaluate_decs (state_clock_fupd (K k) s) env decs = (s',res) /\
              n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s')) 0))) with
       NONE -> NONE
     | SOME k ->
         (match evaluate_decs (state_clock_fupd (K k) s) env decs with
            (s',_) -> SOME (eval_oracle_state_oracle (orac_s (state_eval_state s')) (n + 1)))`;;

(* local: setting the clock to k is decreasing it by clock - k *)
let SEVPAUX_clock_fupd_K = prove
 (`!(s:(FFI)state) k. k <= state_clock s ==>
     state_clock_fupd (\c. c - (state_clock s - k)) s = state_clock_fupd (K k) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_ARITH_TAC);;

let SEVPAUX_clock_fupd_id = prove
 (`!(s:(FFI)state). state_clock_fupd (K (state_clock s)) s = s`,
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

(* local: the common prefix property when the second run has less clock *)
let SEVPAUX_clock_record_common_prefix = prove
 (`!(s:(FFI)state) env decs s' res k s'' res'.
     evaluate_decs s env decs = (s',res) /\
     evaluate_decs (state_clock_fupd (K k) s) env decs = (s'',res') /\
     is_record (ci:(C)compiler_instance) (state_eval_state s) /\ k <= state_clock s /\
     j < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s')) 0)) /\
     j < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s'')) 0)) ==>
     eval_oracle_state_oracle (orac_s (state_eval_state s')) (j + 1) =
     eval_oracle_state_oracle (orac_s (state_eval_state s'')) (j + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(FFI)state`; `env:v sem_env`; `decs:dec list`; `s':(FFI)state`;
                `res:(v sem_env,v)result`]
    (CONJUNCT2(CONJUNCT2(INST [`state_clock (s:(FFI)state) - k`,`k:num`]
       evaluate_record_suffix)))) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; ARITH_RULE `a - k <= a`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[SEVPAUX_clock_fupd_K; PAIR_EQ] THEN
  STRIP_TAC THENL [ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `is_record (ci:(C)compiler_instance) (state_eval_state (s''':(FFI)state)) /\
                is_record ci (state_eval_state (s':(FFI)state))`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[evaluate_is_record_forward; state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP is_record_IMP o
         check (fun th -> SEVPAUX_has_const "is_record" th &&
                          not (can (find_term ((=) `s:(FFI)state`)) (concl th))))) THEN
  UNDISCH_TAC `record_forward (state_eval_state (s''':(FFI)state))
                 (state_eval_state (s':(FFI)state))` THEN
  UNDISCH_TAC `j < FST (FST (eval_oracle_state_oracle
                 (orac_s (state_eval_state (s''':(FFI)state))) 0))` THEN
  ASM_REWRITE_TAC[record_forward_def; orac_s_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; injectivity "eval_state"] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let evaluate_decs_clock_record_common_prefix = prove
 (`evaluate_decs (s:(FFI)state) env decs = (s',res) /\
   evaluate_decs (state_clock_fupd (K k) s) env decs = (s'',res') /\
   is_record (ci:(C)compiler_instance) (state_eval_state s) /\
   j < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s')) 0)) /\
   j < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s'')) 0)) ==>
   eval_oracle_state_oracle (orac_s (state_eval_state s')) (j + 1) =
   eval_oracle_state_oracle (orac_s (state_eval_state s'')) (j + 1)`,
  STRIP_TAC THEN ASM_CASES_TAC `k <= state_clock (s:(FFI)state)` THENL
   [MATCH_MP_TAC SEVPAUX_clock_record_common_prefix THEN
    MAP_EVERY EXISTS_TAC [`s:(FFI)state`; `env:v sem_env`; `decs:dec list`;
                          `res:(v sem_env,v)result`; `k:num`; `res':(v sem_env,v)result`] THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SEVPAUX_clock_record_common_prefix THEN
    MAP_EVERY EXISTS_TAC [`state_clock_fupd (K k) (s:(FFI)state)`; `env:v sem_env`;
                          `decs:dec list`; `res':(v sem_env,v)result`;
                          `state_clock (s:(FFI)state)`; `res:(v sem_env,v)result`] THEN
    ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; SEVPAUX_clock_fupd_id;
                    state_INFO.ri_accfupds; K_THM] THEN
    ASM_ARITH_TAC]);;

let recorded_orac_wf_defined = prove
 (`recorded_orac_wf (compiler:compiler_args->(v#B)option) orac /\
   i <= FST (FST (orac 0)) /\ 0 < i ==>
   ~(compiler (orac i) = NONE)`,
  REWRITE_TAC[recorded_orac_wf_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = FST (FST ((orac:eval_oracle_fun) 0)) \/ i < FST (FST (orac 0))`
    STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[option_DISTINCT];
    ASM_MESON_TAC[option_DISTINCT]]);;

(* local: a run that records more than n compilations gives the n-th entry *)
let SEVPAUX_extract_oracle_SOME = prove
 (`!(t:(FFI)state) env decs n k t1 (res1:(v sem_env,v)result).
     evaluate_decs (state_clock_fupd (K k) t) env decs = (t1,res1) /\
     n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state t1)) 0)) ==>
     ?k0 t0 (res0:(v sem_env,v)result).
       extract_oracle t env decs n =
         SOME (eval_oracle_state_oracle (orac_s (state_eval_state t0)) (n + 1)) /\
       evaluate_decs (state_clock_fupd (K k0) t) env decs = (t0,res0) /\
       n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state t0)) 0)) /\
       k0 <= k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[extract_oracle_def] THEN
  SUBGOAL_THEN
   `?k0. (OLEAST k. ?s' (res:(v sem_env,v)result).
            evaluate_decs (state_clock_fupd (K k) (t:(FFI)state)) env decs = (s',res) /\
            n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s')) 0))) =
         SOME k0`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OLEAST_DEF] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[OLEAST_EQ_SOME]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t0:(FFI)state` (X_CHOOSE_THEN `res0:(v sem_env,v)result`
       STRIP_ASSUME_TAC)) (MP_TAC o SPEC `k:num`)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`k0:num`; `t0:(FFI)state`; `res0:(v sem_env,v)result`] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let extract_oracle_agrees = prove
 (`evaluate_decs (state_clock_fupd (K k) (t:(FFI)state)) env decs = (t',res) /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   (!i r. extract_oracle t env decs i = SOME r /\
          ~(mk_compiler_fun_from_ci ci r = NONE) ==> orac i = r) ==>
   orac_agrees orac (state_eval_state t')`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `state_eval_state (t:(FFI)state) = SOME (EvalOracle oracle_s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
                                             lhs (concl th) = `t:(FFI)state`)) THEN
  SUBGOAL_THEN `is_record (ci:(C)compiler_instance)
                  (state_eval_state (state_clock_fupd (K k) (t:(FFI)state)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; is_record_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`state_clock_fupd (K k) (t:(FFI)state)`; `env:v sem_env`; `decs:dec list`;
                `t':(FFI)state`; `res:(v sem_env,v)result`]
           (CONJUNCT2(CONJUNCT2 evaluate_is_record_forward))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[orac_s_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `os1:eval_oracle_state` o MATCH_MP is_record_IMP) THEN
  ASM_REWRITE_TAC[orac_agrees_def] THEN CASE_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:(FFI)state`; `env:v sem_env`; `decs:dec list`; `j:num`; `k:num`;
                `t':(FFI)state`; `res:(v sem_env,v)result`] SEVPAUX_extract_oracle_SOME) THEN
  ASM_REWRITE_TAC[orac_s_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `eval_oracle_state_oracle (orac_s (state_eval_state (t':(FFI)state))) (j + 1) =
    eval_oracle_state_oracle (orac_s (state_eval_state (t0:(FFI)state))) (j + 1)`
   MP_TAC THENL
   [MATCH_MP_TAC(INST [`state_clock_fupd (K k) (t:(FFI)state)`,`s:(FFI)state`;
                       `t':(FFI)state`,`s':(FFI)state`; `t0:(FFI)state`,`s'':(FFI)state`;
                       `k0:num`,`k:num`; `res0:(v sem_env,v)result`,`res':(v sem_env,v)result`]
                 evaluate_decs_clock_record_common_prefix) THEN
    ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; orac_s_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[orac_s_def] THEN DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `eval_oracle_state_oracle os1 (j + 1)`)) THEN
  MATCH_MP_TAC recorded_orac_wf_defined THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> SEVPAUX_has_const "recorded_orac_wf" th &&
                                 can (find_term ((=) `t':(FFI)state`)) (concl th))) THEN
  ASM_REWRITE_TAC[orac_s_def] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `j < FST (FST (eval_oracle_state_oracle os1 0))` THEN ARITH_TAC);;

let get_oracle_def = cake_def
  `get_oracle (ci:(C)compiler_instance) (s:(FFI)state) env decs =
     let es_record = EvalOracle (eval_oracle_state_REC
                       (K ((0,0),compiler_instance_config_v ci (compiler_instance_init_state ci),
                           []))
                       (do_eval_record ci) [[]] 0) in
     extract_oracle (state_eval_state_fupd (K (SOME es_record)) s) env decs`;;

let put_oracle_def = cake_def
  `put_oracle (ci:(C)compiler_instance) orac =
     insert_gen_oracle ci I (FST o FST) orac
       (SOME (EvalOracle (eval_oracle_state_REC
          (K ((0,0),compiler_instance_config_v ci (compiler_instance_init_state ci),[]))
          (do_eval_record ci) [[]] 0)))`;;

let result_rel_IMP_cases = prove
 (`result_rel (r_rel:A->C->bool) (e_rel:B->D->bool) r r' ==>
   (?x. r = Rval x) \/ (?y. r = Rerr (Rraise y)) \/ (?a. r = Rerr (Rabort a))`,
  DISCH_TAC THEN MESON_TAC[cases "result"; cases "error_result"]);;

let s_rel_clock2 = prove
 (`!k. source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
       source_evalProof_s_rel ci (state_clock_fupd (K k) s) (state_clock_fupd (K k) t)`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  MAP_EVERY EXISTS_TAC [`dec_s:eval_decs_state`; `oracle_s:eval_oracle_state`;
                        `refs':(v store_v)list`] THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; state_component_equality;
                  state_INFO.ri_fupdcanon]);;

let precond_eval_state_def = cake_def
  `precond_eval_state orac (ci:(C)compiler_instance) (s:(FFI)state) env decs <=>
     match state_eval_state s with
       NONE -> T
     | SOME (EvalDecs eds) ->
         EvalDecs eds = mk_init_eval_state ci /\
         orac_extended_wf (mk_compiler_fun_from_ci ci) orac /\
         (!i r x. get_oracle ci s env decs i = SOME r /\
                  mk_compiler_fun_from_ci ci r = SOME x ==> orac i = r)
     | SOME (EvalOracle _) -> F`;;

(* local: extract_oracle is defined at n iff some run records more than n *)
(* compilations                                                           *)
let SEVPAUX_extract_oracle_IS_SOME = prove
 (`!(s:(FFI)state) env decs n.
     IS_SOME (extract_oracle s env decs n) <=>
     ?k t1 (res1:(v sem_env,v)result).
       evaluate_decs (state_clock_fupd (K k) s) env decs = (t1,res1) /\
       n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state t1)) 0))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[extract_oracle_def] THEN
    SUBGOAL_THEN
     `(OLEAST k. ?s' (res:(v sem_env,v)result).
         evaluate_decs (state_clock_fupd (K k) (s:(FFI)state)) env decs = (s',res) /\
         n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state s')) 0))) = NONE`
     SUBST1_TAC THENL
     [REWRITE_TAC[OLEAST_EQ_NONE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[IS_SOME_DEF];
    STRIP_TAC THEN
    MP_TAC(SPECL [`s:(FFI)state`; `env:v sem_env`; `decs:dec list`; `n:num`; `k:num`;
                  `t1:(FFI)state`; `res1:(v sem_env,v)result`]
             SEVPAUX_extract_oracle_SOME) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF]]);;

let extract_oracle_SOME_SUC = prove
 (`IS_SOME (extract_oracle (s:(FFI)state) env decs (SUC i)) ==>
   IS_SOME (extract_oracle s env decs i)`,
  REWRITE_TAC[SEVPAUX_extract_oracle_IS_SOME] THEN
  MESON_TAC[ARITH_RULE `SUC i < n ==> i < n`]);;

(* evaluate_prog_with_clock without its pair_CASE (as semanticsProps'        *)
(* helper; semanticsProps is not an ancestor of this theory)                  *)
let SEVPAUX_evaluate_prog_with_clock = prove
 (`!(st:(FFI)state) env k (prog:dec list).
     evaluate_prog_with_clock st env k prog =
     (state_ffi (FST (evaluate_decs (state_clock_fupd (K k) st) env prog)),
      SND (evaluate_decs (state_clock_fupd (K k) st) env prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_prog_with_clock_def] THEN
  SPEC_TAC(`evaluate_decs (state_clock_fupd (K k) (st:(FFI)state)) env prog`,
           `q:(FFI)state#(v sem_env,v)result`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let SEVPAUX_not_fail = prove
 (`~semantics_prog (s:(FFI)state) env decs Fail ==>
   !k. ~(SND (evaluate_decs (state_clock_fupd (K k) s) env decs) = Rerr (Rabort Rtype_error))`,
  REWRITE_TAC[semantics_prog_def; SEVPAUX_evaluate_prog_with_clock; NOT_EXISTS_THM; SND]);;

let SEVPAUX_decs_sim_clock = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   nsAll (K concrete_v) (sem_env_v env) /\ ~semantics_prog s env decs Fail /\
   evaluate_decs (state_clock_fupd (K k) s) env decs = (s1,r1) ==>
   ?t1 r1'. evaluate_decs (state_clock_fupd (K k) t) env decs = (t1,r1') /\
            source_evalProof_s_rel ci s1 t1 /\
            result_rel
              (source_evalProof_env_rel (source_evalProof_v_rel (orac_s (state_eval_state t1))))
              (source_evalProof_v_rel (orac_s (state_eval_state t1))) r1 r1'`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`state_clock_fupd (K k) (s:(FFI)state)`; `env:v sem_env`; `decs:dec list`;
                `s1:(FFI)state`; `r1:(v sem_env,v)result`; `state_clock_fupd (K k) (t:(FFI)state)`;
                `env:v sem_env`] (CONJUNCT2 (CONJUNCT2 eval_simulation))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[s_rel_clock2; env_rel_concrete_v] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP SEVPAUX_not_fail) THEN
    ASM_REWRITE_TAC[SND];
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`t':(FFI)state`; `res':(v sem_env,v)result`] THEN
    ASM_MESON_TAC[]]);;

let SEVPAUX_extract_oracle_cases = prove
 (`extract_oracle (t:(FFI)state) env decs n = SOME r ==>
   ?k t0 (res0:(v sem_env,v)result).
     evaluate_decs (state_clock_fupd (K k) t) env decs = (t0,res0) /\
     n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state t0)) 0)) /\
     r = eval_oracle_state_oracle (orac_s (state_eval_state t0)) (n + 1)`,
  DISCH_TAC THEN
  SUBGOAL_THEN `IS_SOME (extract_oracle (t:(FFI)state) env decs n)` MP_TAC THENL
   [ASM_REWRITE_TAC[IS_SOME_DEF]; ALL_TAC] THEN
  REWRITE_TAC[SEVPAUX_extract_oracle_IS_SOME] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:(FFI)state`; `env:v sem_env`; `decs:dec list`; `n:num`; `k:num`;
                `t1:(FFI)state`; `res1:(v sem_env,v)result`] SEVPAUX_extract_oracle_SOME) THEN
  ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k0:num`; `t0:(FFI)state`; `res0:(v sem_env,v)result`] THEN
  ASM_REWRITE_TAC[]);;

let extract_oracle_0_st = prove
 (`extract_oracle (t:(FFI)state) env decs 0 = SOME r /\
   ~semantics_prog (s:(FFI)state) env decs Fail /\
   source_evalProof_s_rel (ci:(C)compiler_instance) s t /\
   nsAll (K concrete_v) (sem_env_v env) ==>
   FST (SND r) = compiler_instance_config_v ci (compiler_instance_init_state ci)`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SEVPAUX_extract_oracle_cases) THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (K k) (s:(FFI)state)) env decs`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_TAC `r1:(v sem_env,v)result`)) THEN
  MP_TAC(INST [`r1:(v sem_env,v)result`,`r1:(v sem_env,v)result`] SEVPAUX_decs_sim_clock) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1:(FFI)state = t0` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
  UNDISCH_TAC `source_evalProof_s_rel (ci:(C)compiler_instance) (s1:(FFI)state) (t0:(FFI)state)` THEN
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                 lhs (concl th) = `t0:(FFI)state`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; orac_s_def; ADD_CLAUSES]) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def; ADD_CLAUSES] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


let orac_agrees_s_rel_IMP = prove
 (`orac_agrees orac (state_eval_state (t:(FFI)state)) ==>
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   i < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state t)) 0)) ==>
   orac i = eval_oracle_state_oracle (orac_s (state_eval_state t)) (i + 1)`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `orac_agrees orac (state_eval_state (t:(FFI)state))` THEN
  UNDISCH_TAC `i < FST (FST (eval_oracle_state_oracle
                 (orac_s (state_eval_state (t:(FFI)state))) 0))` THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_agrees_def; orac_s_def] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let SEVPAUX_extract_oracle_run = prove
 (`evaluate_decs (state_clock_fupd (K k) (t:(FFI)state)) env decs = (t1,res1) /\
   is_record (ci:(C)compiler_instance) (state_eval_state t) /\
   n < FST (FST (eval_oracle_state_oracle (orac_s (state_eval_state t1)) 0)) ==>
   extract_oracle t env decs n =
     SOME (eval_oracle_state_oracle (orac_s (state_eval_state t1)) (n + 1))`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`t:(FFI)state`; `env:v sem_env`; `decs:dec list`; `n:num`; `k:num`;
                `t1:(FFI)state`; `res1:(v sem_env,v)result`] SEVPAUX_extract_oracle_SOME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(INST [`state_clock_fupd (K k) (t:(FFI)state)`,`s:(FFI)state`;
                     `t1:(FFI)state`,`s':(FFI)state`; `t0:(FFI)state`,`s'':(FFI)state`;
                     `k0:num`,`k:num`; `res1:(v sem_env,v)result`,`res:(v sem_env,v)result`;
                     `res0:(v sem_env,v)result`,`res':(v sem_env,v)result`; `n:num`,`j:num`]
               evaluate_decs_clock_record_common_prefix) THEN
  ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM]);;

let SEVPAUX_s_rel_is_record = prove
 (`source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t ==>
   is_record ci (state_eval_state t)`,
  REWRITE_TAC[source_evalProof_s_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM; is_record_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let extract_oracle_SUC_st = prove
 (`IS_SOME (extract_oracle (t:(FFI)state) env decs (SUC i)) /\
   source_evalProof_s_rel (ci:(C)compiler_instance) (s:(FFI)state) t /\
   nsAll (K concrete_v) (sem_env_v env) /\
   ~semantics_prog s env decs Fail ==>
   ?r r' x. extract_oracle t env decs (SUC i) = SOME r' /\
            extract_oracle t env decs i = SOME r /\
            mk_compiler_fun_from_ci ci r = SOME x /\
            FST (SND r') = FST x`,
  REWRITE_TAC[SEVPAUX_extract_oracle_IS_SOME] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEVPAUX_s_rel_is_record) THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (K k) (s:(FFI)state)) env decs`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_TAC `r1:(v sem_env,v)result`)) THEN
  MP_TAC(INST [`r1:(v sem_env,v)result`,`r1:(v sem_env,v)result`] SEVPAUX_decs_sim_clock) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1':(FFI)state = t1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `extract_oracle (t:(FFI)state) env decs (SUC i) =
      SOME (eval_oracle_state_oracle (orac_s (state_eval_state (t1:(FFI)state))) (SUC i + 1)) /\
    extract_oracle t env decs i =
      SOME (eval_oracle_state_oracle (orac_s (state_eval_state t1)) (i + 1))`
   (fun th -> REWRITE_TAC[th; option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC (INST [`k:num`,`k:num`; `res1:(v sem_env,v)result`,
                                        `res1:(v sem_env,v)result`] SEVPAUX_extract_oracle_run) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `SUC i < FST (FST (eval_oracle_state_oracle
                   (orac_s (state_eval_state (t1:(FFI)state))) 0))` THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `source_evalProof_s_rel (ci:(C)compiler_instance) (s1:(FFI)state) (t1:(FFI)state)` THEN
  REWRITE_TAC[source_evalProof_s_rel_def; recorded_orac_wf_def] THEN STRIP_TAC THEN
  UNDISCH_TAC `SUC i < FST (FST (eval_oracle_state_oracle
                 (orac_s (state_eval_state (t1:(FFI)state))) 0))` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                 lhs (concl th) = `t1:(FFI)state`)) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_s_def] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC i + 1 = (i + 1) + 1`] THEN MESON_TAC[]);;

let SEVPAUX_s_rel_get_oracle = prove
 (`state_refs (s:(FFI)state) = [] /\
   state_eval_state s = SOME (mk_init_eval_state (ci:(C)compiler_instance)) ==>
   source_evalProof_s_rel ci s
     (state_eval_state_fupd
        (K (SOME (EvalOracle (eval_oracle_state_REC
           (K ((0,0),compiler_instance_config_v ci (compiler_instance_init_state ci),[]))
           (do_eval_record ci) [[]] 0)))) s)`,
  STRIP_TAC THEN REWRITE_TAC[source_evalProof_s_rel_def] THEN
  MAP_EVERY EXISTS_TAC
   [`eval_decs_state_REC (mk_compiler_fun_from_ci (ci:(C)compiler_instance))
       (compiler_instance_config_v ci (compiler_instance_init_state ci)) (0,0,1)
       (v_fun_abs (compiler_instance_decs_dom ci) (compiler_instance_decs_v ci))`;
    `eval_oracle_state_REC
       (K ((0,0),compiler_instance_config_v (ci:(C)compiler_instance)
                   (compiler_instance_init_state ci),[]))
       (do_eval_record ci) [[]] 0`;
    `[]:(v store_v)list`] THEN
  ASM_REWRITE_TAC[GSYM mk_init_eval_state_def; ALL2; recorded_orac_wf_def;
                  eval_oracle_state_INFO.ri_accessors; eval_decs_state_INFO.ri_accessors;
                  K_THM; FST; SND; LT_REFL; CONJUNCT1 LT; EL; HD; LENGTH; ARITH] THEN
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let get_oracle_props = prove
 (`nsAll (K concrete_v) (sem_env_v env) /\
   state_refs (s:(FFI)state) = [] /\
   state_eval_state s = SOME (mk_init_eval_state (ci:(C)compiler_instance)) /\
   ~semantics_prog s env decs Fail ==>
   (!r. get_oracle ci s env decs 0 = SOME r ==>
        FST (SND r) = compiler_instance_config_v ci (compiler_instance_init_state ci)) /\
   (!i r'. get_oracle ci s env decs (SUC i) = SOME r' ==>
           ?r x. get_oracle ci s env decs i = SOME r /\
                 mk_compiler_fun_from_ci ci r = SOME x /\ FST (SND r') = FST x)`,
  STRIP_TAC THEN REWRITE_TAC[get_oracle_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC SEVPAUX_s_rel_get_oracle THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tt = state_eval_state_fupd
        (K (SOME (EvalOracle (eval_oracle_state_REC
           (K ((0,0),compiler_instance_config_v (ci:(C)compiler_instance)
                       (compiler_instance_init_state ci),[]))
           (do_eval_record ci) [[]] 0)))) (s:(FFI)state)` THEN
  DISCH_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(INST [`tt:(FFI)state`,`t:(FFI)state`] extract_oracle_0_st) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(INST [`tt:(FFI)state`,`t:(FFI)state`] extract_oracle_SUC_st) THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; option_INJ] THEN MESON_TAC[]]);;

let SEVPAUX_result_rel_KKT = prove
 (`result_rel (R1:A->B->bool) (R2:C->D->bool) r r' ==>
   result_rel (K (K T):A->B->bool) (K (K T):C->D->bool) r r'`,
  CASES_ON `r:(A,C)result` THEN CASES_ON `r':(B,D)result` THEN
  REWRITE_TAC[result_rel_def; K_THM] THEN
  TRY(CASES_ON `a:(C)error_result`) THEN TRY(CASES_ON `a':(D)error_result`) THEN
  REWRITE_TAC[exc_rel_def; K_THM]);;

let SEVPAUX_result_rel_not_tyerr = prove
 (`result_rel (R1:A->B->bool) (R2:C->D->bool) r r' /\ ~(r = Rerr (Rabort Rtype_error)) ==>
   ~(r' = Rerr (Rabort Rtype_error))`,
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[result_rel_Rerr2; exc_rel_type_error2] THEN MESON_TAC[]);;

let SEVPAUX_result_rel_KKT_refl = prove
 (`result_rel (K (K T):A->A->bool) (K (K T):B->B->bool) r r`,
  CASES_ON `r:(A,B)result` THEN REWRITE_TAC[result_rel_def; K_THM] THEN
  CASES_ON `a:(B)error_result` THEN REWRITE_TAC[exc_rel_def; K_THM]);;

let evaluate_prog_with_clock_put_oracle = prove
 (`precond_eval_state orac (ci:(C)compiler_instance) (s1:(FFI)state) env decs /\
   evaluate_prog_with_clock s1 env k decs = (ffi,res) /\
   ~(res = Rerr (Rabort Rtype_error)) /\
   state_refs s1 = [] /\
   nsAll (K concrete_v) (sem_env_v env) /\
   ~semantics_prog s1 env decs Fail ==>
   ?res'. evaluate_prog_with_clock (state_eval_state_fupd (K (put_oracle ci orac)) s1) env k decs =
            (ffi,res') /\
          result_rel (K (K T):v sem_env->v sem_env->bool) (K (K T):v->v->bool) res res'`,
  REWRITE_TAC[SEVPAUX_evaluate_prog_with_clock; PAIR_EQ] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (K k) (s1:(FFI)state)) env decs`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_TAC `r2:(v sem_env,v)result`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && EVPROPSAUX_is_eval_eq (concl th)
                        then RULE_ASSUM_TAC(fun a -> if a = th then a
                                                     else REWRITE_RULE[th; FST; SND] a)
                        else NO_TAC) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `precond_eval_state orac (ci:(C)compiler_instance) (s1:(FFI)state) env decs` THEN
  REWRITE_TAC[precond_eval_state_def] THEN
  MP_TAC(ISPEC `state_eval_state (s1:(FFI)state)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [(* no eval state: the oracle is not consulted *)
    MP_TAC(SPECL [`state_clock_fupd (K k) (s1:(FFI)state)`; `env:v sem_env`; `decs:dec list`;
                  `s2:(FFI)state`; `res:(v sem_env,v)result`]
             (INST [`put_oracle (ci:(C)compiler_instance) orac`,`es:(eval_state)option`]
                (CONJUNCT2 (CONJUNCT2 eval_no_eval_simulation)))) THEN
    ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[state_INFO.ri_fupdcanon] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_fupdcanon]) THEN
    ASM_REWRITE_TAC[FST; SND; state_INFO.ri_accfupds; K_THM] THEN
    EXISTS_TAC `res:(v sem_env,v)result` THEN REWRITE_TAC[SEVPAUX_result_rel_KKT_refl];
    ALL_TAC] THEN
  (* the initial eval state: simulation by the recording state, then insertion *)
  CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `state_eval_state (s1:(FFI)state) = SOME (mk_init_eval_state (ci:(C)compiler_instance))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(INST [`s1:(FFI)state`,`s:(FFI)state`] SEVPAUX_s_rel_get_oracle) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tt = state_eval_state_fupd
        (K (SOME (EvalOracle (eval_oracle_state_REC
           (K ((0,0),compiler_instance_config_v (ci:(C)compiler_instance)
                       (compiler_instance_init_state ci),[]))
           (do_eval_record ci) [[]] 0)))) (s1:(FFI)state)` THEN
  DISCH_TAC THEN
  MP_TAC(INST [`s1:(FFI)state`,`s:(FFI)state`; `tt:(FFI)state`,`t:(FFI)state`;
               `s2:(FFI)state`,`s1:(FFI)state`; `res:(v sem_env,v)result`,`r1:(v sem_env,v)result`]
           SEVPAUX_decs_sim_clock) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `orac_agrees orac (state_eval_state (t1:(FFI)state))` ASSUME_TAC THENL
   [MATCH_MP_TAC (INST [`tt:(FFI)state`,`t:(FFI)state`; `t1:(FFI)state`,`t':(FFI)state`;
                        `r1':(v sem_env,v)result`,`res:(v sem_env,v)result`;
                        `s1:(FFI)state`,`s:(FFI)state`] extract_oracle_agrees) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `r:compiler_args`] o
      check (fun th -> is_forall (concl th) && SEVPAUX_has_const "get_oracle" th)) THEN
    REWRITE_TAC[get_oracle_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cases "option"];
    ALL_TAC] THEN
  MP_TAC(SPECL [`state_clock_fupd (K k) (tt:(FFI)state)`; `env:v sem_env`; `decs:dec list`;
                `t1:(FFI)state`; `r1':(v sem_env,v)result`]
         (CONJUNCT2 (CONJUNCT2 insert_oracle_correct))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
    ASM_MESON_TAC[SEVPAUX_s_rel_is_record; SEVPAUX_result_rel_not_tyerr];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `state_clock_fupd (K k) (state_eval_state_fupd (K (put_oracle (ci:(C)compiler_instance) orac)) s1) =
    state_eval_state_fupd (insert_gen_oracle ci I (FST o FST) orac)
      (state_clock_fupd (K k) (tt:(FFI)state))` SUBST1_TAC THENL
   [EXPAND_TAC "tt" THEN
    REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM; put_oracle_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FST; SND; state_INFO.ri_accfupds; K_THM] THEN
  EXISTS_TAC `r1':(v sem_env,v)result` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(MATCH_MP SEVPAUX_s_rel_fields
      (ASSUME `source_evalProof_s_rel (ci:(C)compiler_instance) (s2:(FFI)state) (t1:(FFI)state)`)) THEN
    SIMP_TAC[];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SEVPAUX_result_rel_KKT o
                check (SEVPAUX_has_const "result_rel"))]);;

let SEVPAUX_put_oracle_runs = prove
 (`~semantics_prog (s1:(FFI)state) env decs Fail /\
   precond_eval_state orac (ci:(C)compiler_instance) s1 env decs /\
   state_refs s1 = [] /\
   nsAll (K concrete_v) (sem_env_v env) ==>
   !k. FST (evaluate_prog_with_clock (state_eval_state_fupd (K (put_oracle ci orac)) s1)
              env k decs) =
       FST (evaluate_prog_with_clock s1 env k decs) /\
       result_rel (K (K T):v sem_env->v sem_env->bool) (K (K T):v->v->bool)
         (SND (evaluate_prog_with_clock s1 env k decs))
         (SND (evaluate_prog_with_clock (state_eval_state_fupd (K (put_oracle ci orac)) s1)
                 env k decs))`,
  STRIP_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `evaluate_prog_with_clock (s1:(FFI)state) env k decs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ffi1:(FFI)ffi_state` (X_CHOOSE_TAC `r1:(v sem_env,v)result`)) THEN
  MP_TAC(INST [`ffi1:(FFI)ffi_state`,`ffi:(FFI)ffi_state`; `r1:(v sem_env,v)result`,
               `res:(v sem_env,v)result`] evaluate_prog_with_clock_put_oracle) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~semantics_prog (s1:(FFI)state) env decs Fail` THEN
    REWRITE_TAC[semantics_prog_def; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[SND];
    STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND]]);;

let SEVPAUX_result_rel_KKT_abort = prove
 (`result_rel (K (K T):A->B->bool) (K (K T):C->D->bool) r r' ==>
   (!a. r = Rerr (Rabort a) <=> r' = Rerr (Rabort a))`,
  CASES_ON `r:(A,C)result` THEN CASES_ON `r':(B,D)result` THEN
  REWRITE_TAC[result_rel_def; distinctness "result"; injectivity "result"] THEN
  TRY(CASES_ON `a:(C)error_result`) THEN TRY(CASES_ON `a':(D)error_result`) THEN
  REWRITE_TAC[exc_rel_def; distinctness "error_result"; injectivity "error_result"] THEN
  MESON_TAC[]);;

let SEVPAUX_terminate_transfer = prove
 (CASE_TERM
  `result_rel (K (K T):v sem_env->v sem_env->bool) (K (K T):v->v->bool) r1 r ==>
   ((match r with
       Rerr (Rabort (Rffi_error outcome')) -> outcome = FFI_outcome outcome'
     | r -> ~(r = Rerr (Rabort Rtimeout_error)) /\ outcome = Success) <=>
    (match r1 with
       Rerr (Rabort (Rffi_error outcome')) -> outcome = FFI_outcome outcome'
     | r -> ~(r = Rerr (Rabort Rtimeout_error)) /\ outcome = Success))`,
  CASES_ON `r1:(v sem_env,v)result` THEN CASES_ON `r:(v sem_env,v)result` THEN
  REWRITE_TAC[result_rel_def; K_THM] THEN
  TRY(CASES_ON `a:(v)error_result`) THEN TRY(CASES_ON `a':(v)error_result`) THEN
  REWRITE_TAC[exc_rel_def; K_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "result"; distinctness "error_result"] THEN
  TRY(DISCH_THEN SUBST1_TAC THEN REFL_TAC));;

let SEVPAUX_ex_pair_snd = prove
 (`!(p:A#B) b. (?x. p = (x,b)) <=> SND p = b`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let oracle_semantics_prog = prove
 (`~semantics_prog (s1:(FFI)state) env decs Fail /\
   semantics_prog (state_eval_state_fupd (K (put_oracle (ci:(C)compiler_instance) orac)) s1)
     env decs outcome /\
   precond_eval_state orac ci s1 env decs /\
   state_refs s1 = [] /\
   nsAll (K concrete_v) (sem_env_v env) ==>
   semantics_prog s1 env decs outcome`,
  STRIP_TAC THEN
  MP_TAC(INST [`s1:(FFI)state`,`s1:(FFI)state`] SEVPAUX_put_oracle_runs) THEN
  ASM_REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `semantics_prog (state_eval_state_fupd (K (put_oracle (ci:(C)compiler_instance) orac))
                 (s1:(FFI)state)) env decs outcome` THEN
  STRUCT_CASES_TAC(ISPEC `outcome:behaviour` (cases "behaviour")) THEN
  ASM_REWRITE_TAC[semantics_prog_def] THENL
   [(* Diverge: every clock times out in both runs, with the same io events *)
    REWRITE_TAC[SEVPAUX_ex_pair_snd] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl))) THEN
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SEVPAUX_result_rel_KKT_abort o
                  check (SEVPAUX_has_const "result_rel")) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `Rtimeout_error`) THEN REWRITE_TAC[];
    (* Terminate: the same clock *)
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ffi:(FFI)ffi_state`
       (X_CHOOSE_THEN `r:(v sem_env,v)result` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `FST (evaluate_prog_with_clock (s1:(FFI)state) env k decs)`;
                          `SND (evaluate_prog_with_clock (s1:(FFI)state) env k decs)`] THEN
    REWRITE_TAC[PAIR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
                                                    SEVPAUX_has_const "result_rel" th)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP SEVPAUX_terminate_transfer th)]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~semantics_prog (s1:(FFI)state) env decs Fail` THEN
    REWRITE_TAC[semantics_prog_def; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[];
    (* Fail: impossible *)
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Rtype_error` o MATCH_MP SEVPAUX_result_rel_KKT_abort o
                  SPEC `k:num` o check (fun th -> is_forall (concl th) &&
                                                   SEVPAUX_has_const "result_rel" th)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `~semantics_prog (s1:(FFI)state) env decs Fail` THEN
    REWRITE_TAC[semantics_prog_def; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[]]);;

(* for use in source-to-source phases, a proof that the oracle can be       *)
(* adjusted by any stateless compiler                                       *)

let adjust_oracle_def = cake_def
  `adjust_oracle (ci:(C)compiler_instance) (f:dec list->dec list) es =
     match es with
       NONE -> es
     | SOME (EvalDecs _) -> es
     | SOME (EvalOracle o_s) ->
         SOME (EvalOracle
                 (eval_oracle_state_custom_do_eval_fupd
                    (K (do_eval_oracle (mk_compiler_fun_from_ci ci) f)) o_s))`;;

let adjust_oracle_insert_gen_oracle = prove
 (`adjust_oracle (ci:(C)compiler_instance) f (insert_gen_oracle ci g shift_f orac es) =
   insert_gen_oracle ci f shift_f orac es`,
  REWRITE_TAC[insert_gen_oracle_def; adjust_oracle_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[injectivity "option"; injectivity "eval_state";
              eval_oracle_state_INFO.ri_fupdfupds; K_o_THM;
              eval_oracle_state_INFO.ri_fupdcanon] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"; distinctness "eval_state"]) THEN
  ASM_REWRITE_TAC[]);;

let is_insert_oracle_def = cake_def
  `is_insert_oracle (ci:(C)compiler_instance) f es <=>
     ?es' shift_f orac. es = insert_gen_oracle ci f shift_f orac es'`;;

(* HOL4 [local] *)
let is_insert_decs = prove
 (`is_insert_oracle (ci:(C)compiler_instance) f (SOME (EvalDecs eds))`,
  REWRITE_TAC[is_insert_oracle_def] THEN
  MAP_EVERY EXISTS_TAC [`SOME (EvalDecs eds)`; `(FST o FST):compiler_args->num`;
                        `orac:eval_oracle_fun`] THEN
  REWRITE_TAC[insert_gen_oracle_def] THEN CASE_REWRITE_TAC[]);;

let SEVPAUX_is_insert_EvalOracle = prove
 (`is_insert_oracle (ci:(C)compiler_instance) f (SOME (EvalOracle s)) <=>
   eval_oracle_state_custom_do_eval s = do_eval_oracle (mk_compiler_fun_from_ci ci) f`,
  REWRITE_TAC[is_insert_oracle_def] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `es':eval_state option` MP_TAC) THEN
    REWRITE_TAC[insert_gen_oracle_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[injectivity "option"; injectivity "eval_state"; distinctness "option";
                distinctness "eval_state"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM];
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`SOME (EvalOracle s)`; `(\x. 0):compiler_args->num`;
                          `eval_oracle_state_oracle s`] THEN
    REWRITE_TAC[insert_gen_oracle_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"; injectivity "eval_state";
                eval_oracle_state_component_equality; eval_oracle_state_INFO.ri_accfupds;
                K_THM; shift_seq_def; ADD_CLAUSES; ETA_AX] THEN
    ASM_REWRITE_TAC[]]);;

let SEVPAUX_is_insert_NONE = prove
 (`is_insert_oracle (ci:(C)compiler_instance) f NONE`,
  REWRITE_TAC[is_insert_oracle_def] THEN
  MAP_EVERY EXISTS_TAC [`NONE:eval_state option`; `(FST o FST):compiler_args->num`;
                        `orac:eval_oracle_fun`] THEN
  REWRITE_TAC[insert_gen_oracle_def] THEN CASE_REWRITE_TAC[]);;

let SEVPAUX_do_eval_oracle_SOME = prove
 (`do_eval_oracle (cf:compiler_fun) f vs orac = SOME (a,b,c) ==>
   ?c0. c = f c0 /\ (!g. do_eval_oracle cf g vs orac = SOME (a,b,g c0))`,
  REWRITE_TAC[do_eval_oracle_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_DISTINCT; injectivity "option"; PAIR_EQ] THEN
  STRIP_TAC THEN SEVPAUX_SUBST_TAC THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let do_eval_adjust = prove
 (`do_eval vs es = SOME (env1,decs,es1) /\ is_insert_oracle (ci:(C)compiler_instance) f es ==>
   (do_eval vs (adjust_oracle ci (g o f) es) =
      SOME (env1,g decs,adjust_oracle ci (g o f) es1) \/
    do_eval vs (adjust_oracle ci (g o f) es) =
      SOME (env1,decs,adjust_oracle ci (g o f) es1)) /\
   is_insert_oracle ci f es1`,
  MP_TAC(ISPEC `es:eval_state option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `a:eval_state` SUBST1_TAC)) THENL
   [REWRITE_TAC[do_eval_def] THEN CASE_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
  CASES_ON `a:eval_state` THENL
   [STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SEVPAUX_do_eval_EvalDecs] o
      check (SEVPAUX_has_const "do_eval")) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `es1:eval_state option`)) THEN
    REWRITE_TAC[adjust_oracle_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[is_insert_decs];
    REWRITE_TAC[SEVPAUX_is_insert_EvalOracle] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SEVPAUX_do_eval_EvalOracle] o
      check (SEVPAUX_has_const "do_eval")) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `env_id:num#num` (X_CHOOSE_THEN `o1:eval_oracle_fun`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `es1:eval_state option`)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d0:dec list` STRIP_ASSUME_TAC o
      MATCH_MP SEVPAUX_do_eval_oracle_SOME) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[adjust_oracle_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[do_eval_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM; o_THM] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[SEVPAUX_lookup_env_fupds] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[SEVPAUX_is_insert_EvalOracle; add_env_generation_def;
                eval_oracle_state_INFO.ri_accfupds; K_THM; injectivity "option";
                injectivity "eval_state"; PAIR_EQ;
                eval_oracle_state_INFO.ri_fupdcanon; eval_oracle_state_INFO.ri_fupdfupds;
                K_o_THM] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)
let declare_env_adjust = prove
 (CASE_TERM `declare_env (adjust_oracle (ci:(C)compiler_instance) f es) env =
   (match declare_env es env with
      NONE -> NONE
    | SOME (x,es2) -> SOME (x,adjust_oracle ci f es2))`,
  MP_TAC(ISPEC `es:eval_state option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `a:eval_state` SUBST1_TAC)) THEN
  TRY(CASES_ON `a:eval_state`) THEN
  REWRITE_TAC[adjust_oracle_def; declare_env_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[adjust_oracle_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; PAIR_EQ; injectivity "eval_state";
              eval_oracle_state_INFO.ri_fupdcanon]);;

(* HOL4 [local] *)
let adjust_oracle_reset = prove
 (`adjust_oracle (ci:(C)compiler_instance) f (reset_env_generation es1 es2) =
   reset_env_generation (adjust_oracle ci f es1) (adjust_oracle ci f es2)`,
  REWRITE_TAC[adjust_oracle_def; reset_env_generation_def] THEN EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM; injectivity "option";
                  injectivity "eval_state"; eval_oracle_state_INFO.ri_fupdcanon] THEN
  CASE_REWRITE_TAC[eval_oracle_state_INFO.ri_accfupds; K_THM; injectivity "option";
                   injectivity "eval_state"; eval_oracle_state_INFO.ri_fupdcanon]);;

(* HOL4 [local] *)
let is_insert_related = prove
 (`is_insert_oracle (ci:(C)compiler_instance) f (SOME (EvalOracle es)) ==>
   eval_oracle_state_custom_do_eval es2 = eval_oracle_state_custom_do_eval es /\
   eval_oracle_state_oracle es2 = eval_oracle_state_oracle es ==>
   is_insert_oracle ci f (SOME (EvalOracle es2))`,
  SIMP_TAC[SEVPAUX_is_insert_EvalOracle]);;

(* HOL4 [local] *)
let is_insert_reset = prove
 (`is_insert_oracle (ci:(C)compiler_instance) f (reset_env_generation es1 es2) <=>
   is_insert_oracle ci f es2`,
  REWRITE_TAC[reset_env_generation_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[SEVPAUX_is_insert_EvalOracle; eval_oracle_state_INFO.ri_accfupds; is_insert_decs]);;

(* HOL4 [local] *)
let declare_env_is_insert = prove
 (`declare_env es env = SOME (x,es2) /\ is_insert_oracle (ci:(C)compiler_instance) f es ==>
   is_insert_oracle ci f es2`,
  REWRITE_TAC[declare_env_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_DISTINCT; injectivity "option"; PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `es2:eval_state option`)) THEN
  ASM_REWRITE_TAC[is_insert_decs] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SEVPAUX_is_insert_EvalOracle]) THEN
  ASM_REWRITE_TAC[SEVPAUX_is_insert_EvalOracle; eval_oracle_state_INFO.ri_accfupds]);;

let SEVPAUX_ADJFWD_TAC : tactic =
  let spec_g th =
    let c = concl th in
    if is_forall c then
      let v,_ = dest_forall c in
      if fst(dest_var v) = "g" && type_of v = `:dec list->dec list`
      then SPEC `compile_decs:dec list->dec list` th else th
    else th in
  IMP_RES_TAC do_eval_adjust THEN IMP_RES_TAC declare_env_is_insert THEN
  RULE_ASSUM_TAC spec_g THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_INFO.ri_accfupds; K_THM; is_insert_reset]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SEVPAUX_DEDUP_TAC;;

let SEVPAUX_COMPILE_RES_TAC : tactic = fun (asl,w as gl) ->
  IMP_RES_TAC (snd (last asl)) gl;;

let SEVPAUX_ADJ_TAC : tactic =
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (list_result_eq_Rerr :: combine_dec_result_eq_Rerr ::
                               EVPROPSAUX_REC_RW)) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  EVPROPSAUX_IH_DISCH_TAC THEN SEVPAUX_ADJFWD_TAC THEN
  EVPROPSAUX_IH_DISCH_TAC THEN SEVPAUX_ADJFWD_TAC THEN
  EVPROPSAUX_IH_DISCH_TAC THEN SEVPAUX_ADJFWD_TAC THEN
  TRY SEVPAUX_COMPILE_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (distinctness "result" :: distinctness "error_result" ::
                               injectivity "result" :: EVPROPSAUX_REC_RW)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) &&
       can (find_term (fun t -> is_var t && fst(dest_var t) = "compile_decs")) (concl th)
    then MP_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[distinctness "result"; distinctness "error_result"; injectivity "result";
                  injectivity "error_result"] THEN
  REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as gl) ->
     if EVPROPSAUX_is_eval_eq w
     then EVPROPSAUX_GOAL_EVAL_TAC [do_eval_res_def; adjust_oracle_reset; declare_env_adjust;
                                   o_THM] gl
     else ASM_REWRITE_TAC (is_insert_reset :: EVPROPSAUX_REC_RW) gl);;

let adjust_oracle_evaluate = prove
 (`(!(s:(FFI)state) env ds s' res.
      evaluate_decs s env ds = (s',res) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      evaluate_decs s env (compile_decs ds) = (s',res)) ==>
   (!(s:(FFI)state) env exps s' res.
      evaluate s env exps = (s',res) /\
      is_insert_oracle (ci:(C)compiler_instance) f (state_eval_state s) /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      is_insert_oracle ci f (state_eval_state s') /\
      evaluate (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s) env exps =
      (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s',res)) /\
   (!(s:(FFI)state) env x pes err_x s' res.
      evaluate_match s env x pes err_x = (s',res) /\
      is_insert_oracle ci f (state_eval_state s) /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      is_insert_oracle ci f (state_eval_state s') /\
      evaluate_match (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s)
        env x pes err_x =
      (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s',res)) /\
   (!(s:(FFI)state) env ds s' res.
      evaluate_decs s env ds = (s',res) /\
      is_insert_oracle ci f (state_eval_state s) /\
      ~(res = Rerr (Rabort Rtype_error)) ==>
      is_insert_oracle ci f (state_eval_state s') /\
      evaluate_decs (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s) env ds =
      (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s',res))`,
  DISCH_TAC THEN MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  SEVPAUX_ADJ_TAC);;

(* HOL4 [local]: the evaluate_decs part of adjust_oracle_evaluate at a clock *)
let adjust_oracle_ev_decs = prove
 (`(!(s:(FFI)state) env ds s' res.
      evaluate_decs s env ds = (s',res) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      evaluate_decs s env (compile_decs ds) = (s',res)) ==>
   !env ds s' res.
     evaluate_decs (state_clock_fupd (K k) (s:(FFI)state)) env ds = (s',res) /\
     is_insert_oracle (ci:(C)compiler_instance) f (state_eval_state s) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     is_insert_oracle ci f (state_eval_state s') /\
     evaluate_decs (state_eval_state_fupd (adjust_oracle ci (compile_decs o f))
                      (state_clock_fupd (K k) s)) env ds =
     (state_eval_state_fupd (adjust_oracle ci (compile_decs o f)) s',res)`,
  DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2 o MATCH_MP adjust_oracle_evaluate) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds]);;


let adjust_oracle_semantics_prog = prove
 (`!compile f.
     (!(s:(FFI)state) env ds s' res.
        evaluate_decs s env ds = (s',res) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
        evaluate_decs s env (compile ds) = (s',res)) ==>
     is_insert_oracle (ci:(C)compiler_instance) f (state_eval_state (s:(FFI)state)) /\
     ~semantics_prog s env prog Fail /\
     semantics_prog s env prog outcome ==>
     semantics_prog (state_eval_state_fupd (adjust_oracle ci (compile o f)) s) env prog
       outcome`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `k:num` o MATCH_MP (INST [`compile:dec list->dec list`,
    `compile_decs:dec list->dec list`] adjust_oracle_ev_decs)) THEN
  SUBGOAL_THEN
   `!k. ~(SND (evaluate_prog_with_clock (s:(FFI)state) env k prog) = Rerr (Rabort Rtype_error))
        /\ is_insert_oracle (ci:(C)compiler_instance) f (state_eval_state s)
        ==> evaluate_prog_with_clock
              (state_eval_state_fupd (adjust_oracle ci ((compile:dec list->dec list) o
                 (f:dec list->dec list))) s) env k prog =
            evaluate_prog_with_clock s env k prog`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[SEVPAUX_evaluate_prog_with_clock] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (K k) (s:(FFI)state)) env prog`
             PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    FIRST_X_ASSUM(fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq; SND]) THEN ASSUME_TAC eq) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `env:v sem_env`; `prog:dec list`;
                                  `s1:(FFI)state`; `r1:(v sem_env,v)result`] o
      check (fun th -> is_forall(concl th) && SEVPAUX_has_const "adjust_oracle" th)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `state_clock_fupd (K k)
                    (state_eval_state_fupd (adjust_oracle (ci:(C)compiler_instance)
                       ((compile:dec list->dec list) o (f:dec list->dec list))) (s:(FFI)state)) =
                  state_eval_state_fupd (adjust_oracle ci (compile o f))
                    (state_clock_fupd (K k) s)` SUBST1_TAC THENL
     [REWRITE_TAC[state_INFO.ri_fupdcanon]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[state_INFO.ri_accfupds];
    ALL_TAC] THEN
  STRIP_TAC THEN UNDISCH_TAC `semantics_prog (s:(FFI)state) env prog outcome` THEN
  CASES_ON `outcome:behaviour` THENL
   [REWRITE_TAC[semantics_prog_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!k. evaluate_prog_with_clock (state_eval_state_fupd
                        (adjust_oracle (ci:(C)compiler_instance)
                           ((compile:dec list->dec list) o (f:dec list->dec list)))
                        (s:(FFI)state)) env k prog =
                      evaluate_prog_with_clock s env k prog`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    X_GEN_TAC `kk:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `ffi:(FFI)ffi_state` o SPEC `kk:num`) THEN
    ASM_REWRITE_TAC[SND; injectivity "result"; injectivity "error_result";
                    distinctness "abort"];
    REWRITE_TAC[semantics_prog_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `kk:num` (X_CHOOSE_THEN `ffi:(FFI)ffi_state`
      (X_CHOOSE_THEN `r:(v sem_env,v)result` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`kk:num`; `ffi:(FFI)ffi_state`; `r:(v sem_env,v)result`] THEN
    SUBGOAL_THEN `evaluate_prog_with_clock (state_eval_state_fupd
                        (adjust_oracle (ci:(C)compiler_instance)
                           ((compile:dec list->dec list) o (f:dec list->dec list)))
                        (s:(FFI)state)) env kk prog =
                  evaluate_prog_with_clock s env kk prog`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SND];
    ASM_REWRITE_TAC[]]);;
