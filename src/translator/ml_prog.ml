(* ========================================================================= *)
(* ml_prog: port of HOL4 translator/ml_progScript.sml (CakeML v3479).        *)
(* Definitions and theorems supporting ml_progLib, which constructs a        *)
(* CakeML program and its semantic environment.                              *)
(* ========================================================================= *)

needs "translator/evaluate_dec.ml";;
needs "hol4/alist_tree.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/semantics.ml";;

type_invention_error := true;;

(* --- env operators --- *)

(* Functions write, write_cons, write_mod, empty_env, merge_env should     *)
(* never be expanded by EVAL and are therefore defined using nocompute.    *)
(* These should never be exanded by EVAL because that would cause very     *)
(* slow appends.                                                            *)

let ml_write_def = cake_def
  `ml_write name (v:v) (env:v sem_env) =
     sem_env_v_fupd (K (nsBind name v (sem_env_v env))) env`;;

let ml_write_cons_def = cake_def
  `ml_write_cons n d (env:v sem_env) =
     sem_env_c_fupd (K (nsAppend (nsSing n d) (sem_env_c env))) env`;;

let empty_env_def = cake_def
  `(empty_env:v sem_env) = sem_env_REC nsEmpty nsEmpty`;;

let ml_write_mod_def = cake_def
  `ml_write_mod mn (env:v sem_env) env2 =
     sem_env_c_fupd (K (nsAppend (nsLift mn (sem_env_c env)) (sem_env_c env2)))
       (sem_env_v_fupd (K (nsAppend (nsLift mn (sem_env_v env)) (sem_env_v env2))) env2)`;;

let merge_env_def = cake_def
  `merge_env (env2:v sem_env) env1 =
     sem_env_REC (nsAppend (sem_env_v env2) (sem_env_v env1))
                 (nsAppend (sem_env_c env2) (sem_env_c env1))`;;

(* the components of nsLookup are 'nicer' partial functions *)

let nsLookup_Short_def = cake_def
  `nsLookup_Short (ns:(M,N,V)namespace) nm = nsLookup ns (Short nm)`;;

let nsLookup_Mod1_def = cake_def
  `nsLookup_Mod1 (ns:(M,N,V)namespace) = match ns with Bind _ ms -> ALOOKUP ms`;;

let nsLookup_eq = prove
 (CASE_TERM `nsLookup (ns:(M,N,V)namespace) (Short nm) = nsLookup_Short ns nm /\
   nsLookup ns (Long mnm id) =
     (match nsLookup_Mod1 ns mnm with NONE -> NONE | SOME ns2 -> nsLookup ns2 id)`,
  REWRITE_TAC[nsLookup_Short_def] THEN QCASES_ON "ns" THEN
  SIMP[nsLookup_Mod1_def; nsLookup_def]);;

(* base facts about the partial functions *)

let option_choice_f_apply = prove
 (`option_choice_f f g x = OPTION_CHOICE (f x) ((g:A->B option) x)`,
  REWRITE_TAC[option_choice_f_def]);;

let nsLookup_Short_Bind = prove
 (`nsLookup_Short (Bind ss ms:(M,N,V)namespace) = ALOOKUP ss`,
  REWRITE_TAC[nsLookup_Short_def; nsLookup_def; FUN_EQ_THM]);;

let nsLookup_Short_nsAppend = prove
 (`nsLookup_Short (nsAppend ns1 ns2:(M,N,V)namespace) =
   option_choice_f (nsLookup_Short ns1) (nsLookup_Short ns2)`,
  QCASES_ON "ns1" THEN QCASES_ON "ns2" THEN
  REWRITE_TAC[nsLookup_Short_Bind; nsAppend_def; alookup_append_option_choice_f]);;

let nsLookup_Mod1_Bind = prove
 (`nsLookup_Mod1 (Bind ss ms:(M,N,V)namespace) nm = ALOOKUP ms nm`,
  SIMP[nsLookup_Mod1_def]);;

let nsLookup_Mod1_nsAppend = prove
 (`nsLookup_Mod1 (nsAppend ns1 ns2:(M,N,V)namespace) =
   option_choice_f (nsLookup_Mod1 ns1) (nsLookup_Mod1 ns2)`,
  QCASES_ON "ns1" THEN QCASES_ON "ns2" THEN
  SIMP[nsLookup_Mod1_def; nsAppend_def; alookup_append_option_choice_f; ETA_AX]);;

let nsLookup_Short_nsLift = prove
 (`nsLookup_Short (nsLift mnm ns:(M,N,V)namespace) = ALOOKUP []`,
  QCASES_ON "ns" THEN REWRITE_TAC[nsLift_def; nsLookup_Short_Bind]);;

let nsLookup_Mod1_nsLift = prove
 (`nsLookup_Mod1 (nsLift mnm ns:(M,N,V)namespace) = ALOOKUP [(mnm, ns)]`,
  QCASES_ON "ns" THEN SIMP[nsLift_def; nsLookup_Mod1_def; ETA_AX]);;

let nsLookup_pf_nsBind = prove
 (`nsLookup_Short (nsBind n v ns:(M,N,V)namespace) =
     option_choice_f (ALOOKUP [(n, v)]) (nsLookup_Short ns) /\
   nsLookup_Mod1 (nsBind n v ns) = nsLookup_Mod1 ns`,
  QCASES_ON "ns" THEN
  SIMP[nsLookup_Short_def; nsLookup_Mod1_def; FUN_EQ_THM; nsLookup_def; nsBind_def;
       option_choice_f_def; ALOOKUP_def] THEN
  GEN_TAC THEN COND_CASES_TAC THEN SIMP[OPTION_CHOICE_DEF]);;

(* equalities on these partial functions for the various env operators *)

let nsLookup_write_eqs = prove
 (`nsLookup_Short (sem_env_c (ml_write n v env)) = nsLookup_Short (sem_env_c env) /\
   nsLookup_Mod1 (sem_env_c (ml_write n v env)) = nsLookup_Mod1 (sem_env_c env) /\
   nsLookup_Mod1 (sem_env_v (ml_write n v env)) = nsLookup_Mod1 (sem_env_v env) /\
   nsLookup_Short (sem_env_v (ml_write n v env)) =
     option_choice_f (ALOOKUP [(n, v)]) (nsLookup_Short (sem_env_v env))`,
  SIMP[ml_write_def; nsLookup_pf_nsBind]);;

let nsLookup_write_cons_eqs = prove
 (`nsLookup_Short (sem_env_v (ml_write_cons n v env)) = nsLookup_Short (sem_env_v env) /\
   nsLookup_Mod1 (sem_env_v (ml_write_cons n v env)) = nsLookup_Mod1 (sem_env_v env) /\
   nsLookup_Mod1 (sem_env_c (ml_write_cons n v env)) = nsLookup_Mod1 (sem_env_c env) /\
   nsLookup_Short (sem_env_c (ml_write_cons n v env)) =
     option_choice_f (ALOOKUP [(n, v)]) (nsLookup_Short (sem_env_c env))`,
  SIMP[ml_write_cons_def; nsAppend_nsSing; nsLookup_pf_nsBind]);;

let nsLookup_merge_env_eqs = prove
 (`nsLookup_Short (sem_env_v (merge_env env env2)) =
     option_choice_f (nsLookup_Short (sem_env_v env)) (nsLookup_Short (sem_env_v env2)) /\
   nsLookup_Mod1 (sem_env_v (merge_env env env2)) =
     option_choice_f (nsLookup_Mod1 (sem_env_v env)) (nsLookup_Mod1 (sem_env_v env2)) /\
   nsLookup_Short (sem_env_c (merge_env env env2)) =
     option_choice_f (nsLookup_Short (sem_env_c env)) (nsLookup_Short (sem_env_c env2)) /\
   nsLookup_Mod1 (sem_env_c (merge_env env env2)) =
     option_choice_f (nsLookup_Mod1 (sem_env_c env)) (nsLookup_Mod1 (sem_env_c env2))`,
  SIMP[merge_env_def; nsLookup_Short_nsAppend; nsLookup_Mod1_nsAppend]);;

let nsLookup_write_mod_eqs = prove
 (`nsLookup_Short (sem_env_v (ml_write_mod mnm env env2)) =
     nsLookup_Short (sem_env_v env2) /\
   nsLookup_Mod1 (sem_env_v (ml_write_mod mnm env env2)) =
     option_choice_f (ALOOKUP [(mnm, sem_env_v env)]) (nsLookup_Mod1 (sem_env_v env2)) /\
   nsLookup_Short (sem_env_c (ml_write_mod mnm env env2)) =
     nsLookup_Short (sem_env_c env2) /\
   nsLookup_Mod1 (sem_env_c (ml_write_mod mnm env env2)) =
     option_choice_f (ALOOKUP [(mnm, sem_env_c env)]) (nsLookup_Mod1 (sem_env_c env2))`,
  SIMP[ml_write_mod_def; nsLookup_Short_nsAppend; nsLookup_Mod1_nsAppend;
       nsLookup_Short_nsLift; nsLookup_Mod1_nsLift; alookup_empty_option_choice_f]);;

let nsLookup_empty_eqs = prove
 (`nsLookup_Short (sem_env_v (empty_env:v sem_env)) = ALOOKUP [] /\
   nsLookup_Mod1 (sem_env_v (empty_env:v sem_env)) = ALOOKUP [] /\
   nsLookup_Short (sem_env_c (empty_env:v sem_env)) = ALOOKUP [] /\
   nsLookup_Mod1 (sem_env_c (empty_env:v sem_env)) = ALOOKUP []`,
  SIMP[empty_env_def; nsEmpty_def; nsLookup_Short_Bind; nsLookup_Mod1_def; ETA_AX]);;

(* nonsense theorem instantiated when env's are defined *)

let nsLookup_eq_format = prove
 (`!env:v sem_env.
     (nsLookup_Short (sem_env_v env) = nsLookup_Short (sem_env_v env)) /\
     (nsLookup_Short (sem_env_c env) = nsLookup_Short (sem_env_c env)) /\
     (nsLookup_Mod1 (sem_env_v env) = nsLookup_Mod1 (sem_env_v env)) /\
     (nsLookup_Mod1 (sem_env_c env) = nsLookup_Mod1 (sem_env_c env))`,
  REWRITE_TAC[]);;

(* some shorthands that are allowed to EVAL are below *)

let ml_write_rec_def = cake_def
  `ml_write_rec (funs:(varN#varN#exp)list) (env1:v sem_env) (env:v sem_env) =
     ITLIST (\f env. ml_write (FST f) (Recclosure env1 funs (FST f)) env) funs env`;;

let write_rec_thm = prove
 (`ml_write_rec funs env1 env =
   sem_env_v_fupd (K (build_rec_env funs env1 (sem_env_v env))) env`,
  REWRITE_TAC[ml_write_rec_def; build_rec_env_def] THEN
  SPEC_TAC (`Recclosure env1 funs`,`hh:varN->v`) THEN
  SPEC_TAC (`env:v sem_env`,`env:v sem_env`) THEN
  SPEC_TAC (`funs:(varN#varN#exp)list`,`l:(varN#varN#exp)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST] THENL
   [SIMP[RECORD_SELFID_ss]; ALL_TAC] THEN
  PAIR_CASES_ON `h:varN#varN#exp` THEN SIMP[ml_write_def]);;

let ml_write_conses_def = cake_def
  `(ml_write_conses [] (env:v sem_env) = env) /\
   (ml_write_conses (CONS (n,y) xs) env = ml_write_cons n y (ml_write_conses xs env))`;;

let ml_write_tdefs_def = cake_def
  `(ml_write_tdefs n ([]:type_def) (env:v sem_env) = env) /\
   (ml_write_tdefs n (CONS (x,(_:typeN),condefs) (tds:type_def)) env =
      ml_write_tdefs (n+1) tds (ml_write_conses (REVERSE (build_constrs n condefs)) env))`;;

(* HOL4 [local] *)
let write_conses_v = prove
 (`!xs (env:v sem_env). sem_env_v (ml_write_conses xs env) = sem_env_v env`,
  LIST_INDUCT_TAC THEN TRY (PAIR_CASES_ON `h:mlstring#num#stamp`) THEN
  FS[ml_write_conses_def; ml_write_cons_def]);;

(* helper: the constructor part of ml_write_conses *)
let MLPROGAUX_write_conses_c = prove
 (`!xs (env:v sem_env).
     sem_env_c (ml_write_conses xs env) = nsAppend (alist_to_ns xs) (sem_env_c env)`,
  LIST_INDUCT_TAC THEN TRY (PAIR_CASES_ON `h:mlstring#num#stamp`) THEN
  FS[ml_write_conses_def; ml_write_cons_def; nsAppend_nsSing; alist_to_ns_cons;
           nsAppend_nsBind]);;

(* HOL4 [local] *)
let write_tdefs_lemma = prove
 (`!tds (env:v sem_env) n.
     ml_write_tdefs n tds env =
     merge_env (sem_env_REC nsEmpty (build_tdefs n tds)) env`,
  LIST_INDUCT_TAC THENL
   [SIMP[ml_write_tdefs_def; build_tdefs_def; merge_env_def; sem_env_component_equality];
    ALL_TAC] THEN
  PAIR_CASES_ON `h:tvarN list # typeN # (conN # ast_t list) list` THEN
  FS[ml_write_tdefs_def; build_tdefs_def; merge_env_def; write_conses_v;
           MLPROGAUX_write_conses_c; sem_env_component_equality; nsAppend_assoc]);;

let write_tdefs_thm = prove
 (`ml_write_tdefs n tds (empty_env:v sem_env) =
   sem_env_REC nsEmpty (build_tdefs n tds)`,
  SIMP[write_tdefs_lemma; empty_env_def; merge_env_def]);;

(* HOL4 [local]; HOL4 also quantifies a variable env that does not occur *)
let merge_env_write_conses = prove
 (`!xs. merge_env (ml_write_conses xs env1) (env2:v sem_env) =
        ml_write_conses xs (merge_env env1 env2)`,
  LIST_INDUCT_TAC THEN TRY (PAIR_CASES_ON `h:mlstring#num#stamp`) THEN
  FS[ml_write_conses_def; ml_write_cons_def; merge_env_def;
           sem_env_component_equality; nsAppend_assoc]);;

(* HOL4 [local] *)
let merge_env_write_tdefs = prove
 (`!tds n env1 (env2:v sem_env).
     merge_env (ml_write_tdefs n tds env1) env2 =
     ml_write_tdefs n tds (merge_env env1 env2)`,
  LIST_INDUCT_TAC THEN TRY (PAIR_CASES_ON `h:tvarN list # typeN # (conN # ast_t list) list`) THEN
  FS[ml_write_tdefs_def; merge_env_write_conses]);;

(* it's not clear if these are still needed, but ml_progComputeLib and     *)
(* cfTacticsLib want them to be present.                                    *)

(* HOL4 [compute] *)
let nsLookup_nsAppend_Short = prove
 (CASE_TERM `nsLookup (nsAppend e1 e2:(M,N,V)namespace) (Short id) =
   match nsLookup e1 (Short id) with
     NONE -> nsLookup e2 (Short id)
   | SOME v -> SOME v`,
  QCASES_ON "e1" THEN QCASES_ON "e2" THEN
  SIMP[nsAppend_def; nsLookup_def; ALOOKUP_APPEND]);;

(* HOL4 [compute] *)
let write_simp = prove
 (`sem_env_c (ml_write n v env) = sem_env_c env /\
   nsLookup (sem_env_v (ml_write n v env)) (Short q) =
     if n = q then SOME v else nsLookup (sem_env_v env) (Short q)`,
  COND_CASES_TAC THEN FS[ml_write_def; nsLookup_nsBind] THEN
  MATCH_MP_TAC (CONJUNCT2 nsLookup_nsBind) THEN FS[]);;

(* HOL4 [compute] *)
let write_cons_simp = prove
 (`sem_env_v (ml_write_cons n v env) = sem_env_v env /\
   nsLookup (sem_env_c (ml_write_cons n v env)) (Short q) =
     if n = q then SOME v else nsLookup (sem_env_c env) (Short q)`,
  COND_CASES_TAC THEN FS[ml_write_cons_def; nsAppend_nsSing; nsLookup_nsBind] THEN
  MATCH_MP_TAC (CONJUNCT2 nsLookup_nsBind) THEN FS[]);;

(* HOL4 [compute] *)
let write_mod_simp = prove
 (`(nsLookup (sem_env_v (ml_write_mod mn env env2)) (Short q) =
    nsLookup (sem_env_v env2) (Short q)) /\
   (nsLookup (sem_env_c (ml_write_mod mn env env2)) (Short c) =
    nsLookup (sem_env_c env2) (Short c)) /\
   (nsLookup (sem_env_v (ml_write_mod mn env env2)) (Long mn' r) =
    if mn = mn' then nsLookup (sem_env_v env) r
    else nsLookup (sem_env_v env2) (Long mn' r)) /\
   (nsLookup (sem_env_c (ml_write_mod mn env env2)) (Long mn' s) =
    if mn = mn' then nsLookup (sem_env_c env) s
    else nsLookup (sem_env_c env2) (Long mn' s))`,
  REWRITE_TAC[ml_write_mod_def] THEN
  QCASES_ON "sem_env_v (env2:v sem_env)" THEN QCASES_ON "sem_env_c (env2:v sem_env)" THEN
  SIMP[nsLift_def; nsAppend_def; nsLookup_def; ALOOKUP_def; APPEND] THEN
  REPEAT CONJ_TAC THEN COND_CASES_TAC THEN FS[]);;

(* HOL4 [compute] *)
let empty_simp = prove
 (`nsLookup (sem_env_v (empty_env:v sem_env)) q = NONE /\
   nsLookup (sem_env_c (empty_env:v sem_env)) q = NONE`,
  SIMP[empty_env_def; nsLookup_nsEmpty]);;

(* --- declarations --- *)

let ml_Decls_def = cake_def
  `Decls (env:v sem_env) (s1:(FFI)state) ds env2 s2 <=>
     state_clock s1 = state_clock s2 /\
     ?ck1 ck2. evaluate_dec_list (state_clock_fupd (K ck1) s1) env ds =
               (state_clock_fupd (K ck2) s2,Rval env2)`;;

let ml_Prog_def = cake_def
  `Prog (env:v sem_env) (s1:(FFI)state) ds env2 s2 <=>
     state_clock s1 = state_clock s2 /\
     ?ck1 ck2. evaluate_decs (state_clock_fupd (K ck1) s1) env ds =
               (state_clock_fupd (K ck2) s2,Rval env2)`;;

let Decls_Dtype = prove
 (`!env (s:(FFI)state) tds env2 s2 locs.
     Decls env s [Dtype locs tds] env2 s2 <=>
     ALL check_dup_ctors tds /\
     s2 = state_next_type_stamp_fupd (K (state_next_type_stamp s + LENGTH tds)) s /\
     env2 = ml_write_tdefs (state_next_type_stamp s) tds empty_env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; write_tdefs_thm] THEN
  ASM_CASES_TAC `ALL check_dup_ctors (tds:type_def)` THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [GVS[state_component_equality];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["state_clock s"; "state_clock s"] THEN
    SIMP[state_component_equality]]);;

let Decls_Dexn = prove
 (`!env (s:(FFI)state) n l env2 s2 locs.
     Decls env s [Dexn locs n l] env2 s2 <=>
     s2 = state_next_exn_stamp_fupd (K (state_next_exn_stamp s + 1)) s /\
     env2 = ml_write_cons n (LENGTH l,ExnStamp (state_next_exn_stamp s)) empty_env`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; ml_write_cons_def; empty_env_def] THEN
  SIMP[nsAppend_nsEmpty; nsAppend_nsSing; nsSing_def; nsBind_def; nsEmpty_def] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [GVS[state_component_equality];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["state_clock s"; "state_clock s"] THEN
    SIMP[state_component_equality]]);;

let Decls_Dtabbrev = prove
 (`!env (s:(FFI)state) x y z env2 s2 locs.
     Decls env s [Dtabbrev locs x y z] env2 s2 <=> s2 = s /\ env2 = empty_env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; empty_env_def] THEN
  SIMP[] THEN EQ_TAC THEN STRIP_TAC THENL
   [GVS[state_component_equality];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["state_clock s"; "state_clock s"] THEN
    SIMP[state_component_equality]]);;

let eval_rel_def = cake_def
  `eval_rel (s1:(FFI)state) env e (s2:(FFI)state) (x:v) <=>
     state_clock s1 = state_clock s2 /\
     ?ck1 ck2.
       evaluate (state_clock_fupd (K ck1) s1) env [e] =
       (state_clock_fupd (K ck2) s2,Rval [x])`;;

let eval_rel_alt = prove
 (`eval_rel (s1:(FFI)state) env e s2 x <=>
   state_clock s2 = state_clock s1 /\
   ?ck. evaluate (state_clock_fupd (K ck) s1) env [e] = (s2,Rval [x])`,
  REWRITE_TAC[eval_rel_def] THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC (ISPECL [`state_clock_fupd (K ck1) (s1:(FFI)state)`; `env:v sem_env`; `[e:exp]`;
                    `state_clock_fupd (K ck2) (s2:(FFI)state)`;
                    `Rval [x]:(v list,v)result`] evaluate_set_clock) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN
    DISCH_THEN (X_CHOOSE_TAC `ck:num` o SPEC `state_clock (s2:(FFI)state)`) THEN
    QEXISTS_TAC "ck" THEN FS[RECORD_SELFID_ss];
    SUBGOAL_THEN `state_clock_fupd (K (state_clock s2)) (s2:(FFI)state) = s2` ASSUME_TAC THENL
     [SIMP[RECORD_SELFID_ss]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `state_clock (s2:(FFI)state)`] THEN ASM_REWRITE_TAC[]]);;

let eval_list_rel_def = cake_def
  `eval_list_rel (s1:(FFI)state) env e (s2:(FFI)state) (x:v list) <=>
     state_clock s1 = state_clock s2 /\
     ?ck1 ck2.
       evaluate (state_clock_fupd (K ck1) s1) env e =
       (state_clock_fupd (K ck2) s2,Rval x)`;;

let eval_match_rel_def = cake_def
  `eval_match_rel (s1:(FFI)state) env v pats err_v (s2:(FFI)state) (x:v) <=>
     state_clock s1 = state_clock s2 /\
     ?ck1 ck2.
       evaluate_match (state_clock_fupd (K ck1) s1) env v pats err_v =
       (state_clock_fupd (K ck2) s2,Rval [x])`;;

(* Delays the write *)
let Decls_Dlet = prove
 (`!env (s1:(FFI)state) v e s2 env2 locs.
     Decls env s1 [Dlet locs (Pvar v) e] env2 s2 <=>
     ?x. eval_rel s1 env e s2 x /\ env2 = ml_write v x empty_env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; eval_rel_def] THEN
  SIMP[pat_bindings_def; pmatch_def] THEN EQ_TAC THEN STRIP_TAC THENL
   [GVS[pair_case_eq; case_eq "result"] THEN
    FIRST_ASSUM (X_CHOOSE_THEN `y:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
    EXISTS_TAC `y:v` THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`ck1:num`; `ck2:num`] THEN ASM_REWRITE_TAC[];
      SIMP[ml_write_def; empty_env_def; HD]];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["ck1"; "ck2"] THEN
    ASM_REWRITE_TAC[] THEN SIMP[ml_write_def; empty_env_def; HD]]);;

(* HOL4 [local] *)
let FOLDR_LEMMA = prove
 (CASE_TERM `!xs ys.
     APPEND (ITLIST (\x x4. match x with (x1,x2,x3) -> CONS (x1,f x1 x2 x3) x4) xs []) ys =
     ITLIST (\x x4. match x with (x1,x2,x3) -> CONS (x1,(f:A->B->C->D) x1 x2 x3) x4) xs ys`,
  LIST_INDUCT_TAC THEN TRY (PAIR_CASES_ON `h:A#B#C`) THEN FS[ITLIST; APPEND]);;

(* Delays the write in build_rec_env *)
let Decls_Dletrec = prove
 (CASE_TERM `!env (s1:(FFI)state) funs s2 env2 locs.
     Decls env s1 [Dletrec locs funs] env2 s2 <=>
     s2 = s1 /\ ALL_DISTINCT (MAP (\xyz. match xyz with (x,y,z) -> x) funs) /\
     env2 = ml_write_rec funs env empty_env`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; write_rec_thm; empty_env_def] THEN
  ASM_CASES_TAC (CASE_TERM `ALL_DISTINCT (MAP (\xyz. match xyz with (x,y,z) -> x)
                   (funs:(varN#varN#exp)list))`) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN EQ_TAC THEN STRIP_TAC THENL
   [GVS[state_component_equality];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["state_clock s1"; "state_clock s1"] THEN
    SIMP[state_component_equality]]);;

let Decls_Dmod = prove
 (`Decls env1 (s1:(FFI)state) [Dmod mn ds] env2 s2 <=>
   ?s env. Decls env1 s1 ds env s /\ s2 = s /\ env2 = ml_write_mod mn env empty_env`,
  REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; ml_write_mod_def; empty_env_def] THEN
  SIMP[nsAppend_nsEmpty] THEN EQ_TAC THEN STRIP_TAC THENL
   [GVS[pair_case_eq; case_eq "result"] THEN
    QEXISTS_TAC "a" THEN CONJ_TAC THENL
     [MAP_EVERY QEXISTS_TAC ["ck1"; "ck2"] THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN MAP_EVERY QEXISTS_TAC ["ck1"; "ck2"] THEN ASM_REWRITE_TAC[] THEN
    SIMP[]]);;

let Decls_Dlocal = prove
 (`Decls env (st:(FFI)state) lds env2 st2
   ==> Decls (merge_env env2 env) st2 ds env3 st3
   ==> Decls env st [Dlocal lds ds] env3 st3`,
  REWRITE_TAC[ml_Decls_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`state_clock_fupd (K ck1) (st:(FFI)state)`; `env:v sem_env`;
                  `lds:dec list`; `state_clock_fupd (K ck2) (st2:(FFI)state)`;
                  `Rval env2:(v sem_env,v)result`] evaluate_dec_list_set_clock) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN (X_CHOOSE_TAC `c1:num` o SPEC `ck1':num`) THEN
  MAP_EVERY EXISTS_TAC [`c1:num`; `ck2':num`] THEN
  SUBGOAL_THEN `merge_env env2 env = extend_dec_env env2 (env:v sem_env)`
    (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th])) THENL
   [REWRITE_TAC[merge_env_def; extend_dec_env_def]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let Decls_Denv = prove
 (`!env (s1:(FFI)state) v s2 env2.
     Decls env s1 [Denv v] env2 s2 <=>
     ?env1 es.
       declare_env (state_eval_state s1) env = SOME (env1,es) /\
       s2 = state_eval_state_fupd (K es) s1 /\
       env2 = ml_write v env1 empty_env`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; ml_write_def; empty_env_def] THEN
  SIMP[] THEN QCASES_ON "declare_env (state_eval_state s1) env" THEN SIMP[] THEN
  PAIR_CASES_ON `a:v#(eval_state)option` THEN
  SIMP[nsSing_def; nsBind_def; nsEmpty_def] THEN EQ_TAC THEN STRIP_TAC THENL
   [GVS[state_component_equality];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["state_clock s1"; "state_clock s1"] THEN
    SIMP[state_component_equality]]);;

(* HOL4 also quantifies two variables n l that do not occur *)
let Decls_NIL = prove
 (`!env (s:(FFI)state) env2 s2.
     Decls env s [] env2 s2 <=> s2 = s /\ env2 = empty_env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_Decls_def; evaluate_dec_list_def; empty_env_def] THEN
  SIMP[] THEN EQ_TAC THEN STRIP_TAC THENL
   [GVS[state_component_equality];
    GVS[] THEN MAP_EVERY QEXISTS_TAC ["state_clock s"; "state_clock s"] THEN
    SIMP[state_component_equality]]);;

(* HOL4 also quantifies a variable ds1 that does not occur *)
let Decls_CONS = prove
 (`!(s1:(FFI)state) s3 env1 d ds2 env3.
     Decls env1 s1 (CONS d ds2) env3 s3 <=>
     ?envA envB s2.
       Decls env1 s1 [d] envA s2 /\
       Decls (merge_env envA env1) s2 ds2 envB s3 /\
       env3 = merge_env envB envA`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ml_Decls_def] THEN
  SUBGOAL_THEN `!envA:v sem_env. merge_env envA env1 = extend_dec_env envA env1`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[merge_env_def; extend_dec_env_def]; ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE[evaluate_dec_list_cons]) THEN
    MP_TAC (ISPEC `evaluate_dec_list (state_clock_fupd (K ck1) (s1:(FFI)state)) env1 [d]`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `sa:(FFI)state` (X_CHOOSE_THEN `ra:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "ra" THEN SIMP[] THEN
    MP_TAC (ISPEC `evaluate_dec_list (sa:(FFI)state) (extend_dec_env a env1) ds2`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `sb:(FFI)state` (X_CHOOSE_THEN `rb:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "rb" THEN SIMP[combine_dec_result_def] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:v sem_env`; `a':v sem_env`;
      `state_clock_fupd (K (state_clock (s3:(FFI)state))) (sa:(FFI)state)`] THEN
    REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`ck1:num`; `state_clock (sa:(FFI)state)`] THEN
      ASM_REWRITE_TAC[] THEN SIMP[RECORD_SELFID_ss];
      MAP_EVERY EXISTS_TAC [`state_clock (sa:(FFI)state)`; `ck2:num`] THEN
      SIMP[RECORD_SELFID_ss] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[merge_env_def] THEN ASM_MESON_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC (ISPECL [`state_clock_fupd (K ck1) (s1:(FFI)state)`; `env1:v sem_env`;
                    `[d:dec]`; `state_clock_fupd (K ck2) (s2:(FFI)state)`;
                    `Rval envA:(v sem_env,v)result`] evaluate_dec_list_set_clock) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN
    DISCH_THEN (X_CHOOSE_TAC `c1:num` o SPEC `ck1':num`) THEN
    MAP_EVERY EXISTS_TAC [`c1:num`; `ck2':num`] THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_cons] THEN ASM_REWRITE_TAC[] THEN
    SIMP[combine_dec_result_def; merge_env_def]]);;

let merge_env_empty_env = prove
 (`merge_env env empty_env = env /\ merge_env empty_env env = (env:v sem_env)`,
  SIMP[merge_env_def; empty_env_def; nsAppend_nsEmpty; sem_env_component_equality]);;

let merge_env_assoc = prove
 (`merge_env env1 (merge_env env2 env3) = merge_env (merge_env env1 env2) (env3:v sem_env)`,
  SIMP[merge_env_def; nsAppend_assoc]);;

let Decls_APPEND = prove
 (`!(s1:(FFI)state) s3 env1 ds1 ds2 env3.
     Decls env1 s1 (APPEND ds1 ds2) env3 s3 <=>
     ?envA envB s2.
       Decls env1 s1 ds1 envA s2 /\
       Decls (merge_env envA env1) s2 ds2 envB s3 /\
       env3 = merge_env envB envA`,
  INDUCT_ON `ds1:dec list` THENL
   [SIMP[APPEND; Decls_NIL; merge_env_empty_env]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[Decls_CONS] THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [DISCH_THEN (X_CHOOSE_THEN `eA:v sem_env` (X_CHOOSE_THEN `eB:v sem_env`
      (X_CHOOSE_THEN `t2:(FFI)state` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eA2:v sem_env` (X_CHOOSE_THEN `eB2:v sem_env`
      (X_CHOOSE_THEN `t3:(FFI)state` STRIP_ASSUME_TAC))) ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`merge_env eA2 eA:v sem_env`; `eB2:v sem_env`; `t3:(FFI)state`] THEN
    ASM_REWRITE_TAC[GSYM merge_env_assoc] THEN
    MAP_EVERY EXISTS_TAC [`eA:v sem_env`; `eA2:v sem_env`; `t2:(FFI)state`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN (X_CHOOSE_THEN `eA:v sem_env` (X_CHOOSE_THEN `eB:v sem_env`
      (X_CHOOSE_THEN `t2:(FFI)state` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eA2:v sem_env` (X_CHOOSE_THEN `eB2:v sem_env`
      (X_CHOOSE_THEN `t3:(FFI)state` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC)))) THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    MAP_EVERY EXISTS_TAC [`eA2:v sem_env`; `merge_env eB eB2:v sem_env`; `t3:(FFI)state`] THEN
    ASM_REWRITE_TAC[GSYM merge_env_assoc] THEN
    MAP_EVERY EXISTS_TAC [`eB2:v sem_env`; `eB:v sem_env`; `t2:(FFI)state`] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[GSYM merge_env_assoc]) THEN ASM_REWRITE_TAC[]]);;

let Decls_SNOC = prove
 (`!(s1:(FFI)state) s3 env1 ds1 d env3.
     Decls env1 s1 (SNOC d ds1) env3 s3 <=>
     ?envA envB s2.
       Decls env1 s1 ds1 envA s2 /\
       Decls (merge_env envA env1) s2 [d] envB s3 /\
       env3 = merge_env envB envA`,
  REWRITE_TAC[SNOC_APPEND; Decls_APPEND]);;

let ml_Decls_set_eval_state = prove
 (`Decls env1 (s1:(FFI)state) ds env2 s2 /\ state_eval_state s1 = NONE ==>
   !es. Decls env1 (state_eval_state_fupd (K es) s1) ds env2
                   (state_eval_state_fupd (K es) s2)`,
  REWRITE_TAC[ml_Decls_def] THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC (INST [`es:(eval_state)option`,`es:(eval_state)option`]
    (ISPECL [`state_clock_fupd (K ck1) (s1:(FFI)state)`; `env1:v sem_env`; `ds:dec list`;
             `state_clock_fupd (K ck2) (s2:(FFI)state)`; `Rval env2:(v sem_env,v)result`]
            eval_dec_list_no_eval_simulation)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY QEXISTS_TAC ["ck1"; "ck2"] THEN
  FIRST_X_ASSUM (MP_TAC o check (is_eq o concl)) THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN SIMP[]);;

(* The translator and CF tools use the following definition of ML_code to   *)
(* build (and verify) an ML program within the logic. The goal is to prove *)
(* 'Decls' of the completed list of declarations. The program is           *)
(* constructed one statement at a time, with facts about the resulting     *)
(* environment built over time. There is a list of currently open blocks   *)
(* (e.g. struct and local constructs) so that the contents of modules and  *)
(* local objects can also be built up one statement at a time.             *)

let ML_code_env_def = cake_def
  `(ML_code_env (env:v sem_env) ([]:(A#B#C#v sem_env)list) = env) /\
   (ML_code_env env (CONS ((comm:A),(st:B),(decls:C),res_env) bls) =
      merge_env res_env (ML_code_env env bls))`;;

let ML_code_def = cake_def
  `(ML_code (env:v sem_env) [] (res_st:(FFI)state) <=> T) /\
   (ML_code env (CONS ((comment:mlstring#mlstring),st,(decls:dec list),res_env) bls)
            res_st <=>
      ML_code env bls st /\ Decls (ML_code_env env bls) st decls res_env res_st)`;;

(* retreive the Decls from a toplevel ML_code *)
let ML_code_Decls = prove
 (`ML_code env1 [(comm, st1, prog, env2)] (st2:(FFI)state) ==>
   Decls env1 st1 prog env2 st2`,
  SIMP[ML_code_def; ML_code_env_def]);;

(* an empty program *)

(* HOL4: init_env and init_state are the components of prim_sem_env, as  *)
(* EVAL computes them (primSemEnv's prim_sem_env_eq)                      *)
let MLPROGAUX_prim_sem_env_THE = prove
 (`THE (prim_sem_env (ffi:(FFI)ffi_state)) =
   (FST (THE (prim_sem_env ffi)),SND (THE (prim_sem_env ffi)))`,
  REWRITE_TAC[PAIR]);;

let MLPROGAUX_prim_sem_env_eq =
  CONV_RULE (RAND_CONV (REWRITE_CONV[prim_sem_env_eq; THE_DEF; FST; SND]))
    MLPROGAUX_prim_sem_env_THE;;

(* init_env_def should not be unpacked by EVAL.  Queries will be handled    *)
(* by the nsLookup_conv apparatus, which will use the pfun_eqs thm below.   *)
let ml_init_env_def =
  cake_def (mk_eq(`ml_init_env:v sem_env`,
                  rand(rand(concl MLPROGAUX_prim_sem_env_eq))));;

let ml_init_state_def =
  cake_def (mk_eq(`(ml_init_state:(FFI)ffi_state->(FFI)state) ffi`,
                  lhand(rand(concl MLPROGAUX_prim_sem_env_eq))));;

let init_state_env_thm = prove
 (`THE (prim_sem_env (ffi:(FFI)ffi_state)) = (ml_init_state ffi,ml_init_env)`,
  REWRITE_TAC[prim_sem_env_eq; THE_DEF; ml_init_state_def; ml_init_env_def]);;

let nsLookup_init_env_pfun_eqs =
  end_itlist CONJ
    (map (CAKE_SIMP_CONV[ml_init_env_def; nsLookup_Short_Bind; nsLookup_Mod1_def;
                         ETA_AX])
         [`nsLookup_Short (sem_env_c ml_init_env)`;
          `nsLookup_Short (sem_env_v ml_init_env)`;
          `nsLookup_Mod1 (sem_env_c ml_init_env)`;
          `nsLookup_Mod1 (sem_env_v ml_init_env)`]);;

let ML_code_NIL = prove
 (`ML_code ml_init_env
     [((implode "Toplevel",implode ""),ml_init_state (ffi:(FFI)ffi_state),[],empty_env)]
     (ml_init_state ffi)`,
  SIMP[ML_code_def; ML_code_env_def; Decls_NIL]);;

(* opening and closing of modules *)

let ML_code_new_block = prove
 (`!comm2. ML_code inp_env (CONS (comm,st,decls,env) bls) (st2:(FFI)state) ==>
     let env2 = ML_code_env inp_env (CONS (comm,st,decls,env) bls) in
     ML_code inp_env (CONS (comm2,st2,[],empty_env) (CONS (comm,st,decls,env) bls)) st2`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SIMP[ML_code_def; Decls_NIL]);;

let ML_code_close_module = prove
 (`ML_code inp_env (CONS ((implode "Module",mn),m_i_st,m_decls,m_env)
                      (CONS (comm,st,decls,env) bls)) (st2:(FFI)state)
   ==> let env2 = ml_write_mod mn m_env env in
       ML_code inp_env (CONS (comm,st,SNOC (Dmod mn m_decls) decls,env2) bls) st2`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; ML_code_env_def] THEN
  REWRITE_TAC[SNOC_APPEND; Decls_APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env:v sem_env`; `ml_write_mod mn m_env empty_env`;
                        `m_i_st:(FFI)state`] THEN
  ASM_REWRITE_TAC[Decls_Dmod] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`st2:(FFI)state`; `m_env:v sem_env`] THEN ASM_REWRITE_TAC[];
    SIMP[ml_write_mod_def; merge_env_def; empty_env_def; nsAppend_nsEmpty;
         sem_env_component_equality]]);;

let ML_code_close_local = prove
 (`ML_code inp_env (CONS ((implode "Local",ln2),l2_i_st,l2_decls,l2_env)
                    (CONS ((implode "Local",ln1),l1_i_st,l1_decls,l1_env)
                     (CONS (comm,st,decls,env) bls))) (st2:(FFI)state)
   ==> let env2 = merge_env l2_env env in
       ML_code inp_env
         (CONS (comm,st,SNOC (Dlocal l1_decls l2_decls) decls,env2) bls) st2`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; ML_code_env_def] THEN
  REWRITE_TAC[SNOC_APPEND; Decls_APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env:v sem_env`; `l2_env:v sem_env`; `l1_i_st:(FFI)state`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (GEN_ALL (REWRITE_RULE[IMP_IMP] Decls_Dlocal)) THEN
  MAP_EVERY EXISTS_TAC [`l1_env:v sem_env`; `l2_i_st:(FFI)state`] THEN
  ASM_REWRITE_TAC[]);;

(* appending a Dtype *)

let ML_code_Dtype = prove
 (`!tds locs. ML_code inp_env (CONS (comm,s1,prog,env2) bls) (s2:(FFI)state) ==>
     ALL check_dup_ctors tds ==>
     let nts = state_next_type_stamp s2 in
     let s3 = state_next_type_stamp_fupd (K (nts + LENGTH tds)) s2 in
     let env3 = ml_write_tdefs nts tds env2 in
     ML_code inp_env (CONS (comm,s1,SNOC (Dtype locs tds) prog,env3) bls) s3`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; SNOC_APPEND; Decls_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env2:v sem_env`;
    `ml_write_tdefs (state_next_type_stamp (s2:(FFI)state)) tds empty_env`;
    `s2:(FFI)state`] THEN
  ASM_REWRITE_TAC[Decls_Dtype; merge_env_write_tdefs; merge_env_empty_env]);;

(* appending a Dexn *)

let ML_code_Dexn = prove
 (`!n l locs. ML_code inp_env (CONS (comm,s1,prog,env2) bls) (s2:(FFI)state) ==>
     let nes = state_next_exn_stamp s2 in
     let s3 = state_next_exn_stamp_fupd (K (nes + 1)) s2 in
     let env3 = ml_write_cons n (LENGTH l,ExnStamp nes) env2 in
     ML_code inp_env (CONS (comm,s1,SNOC (Dexn locs n l) prog,env3) bls) s3`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; SNOC_APPEND; Decls_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env2:v sem_env`;
    `ml_write_cons n (LENGTH (l:ast_t list),ExnStamp (state_next_exn_stamp (s2:(FFI)state)))
       empty_env`;
    `s2:(FFI)state`] THEN
  ASM_REWRITE_TAC[Decls_Dexn] THEN
  SIMP[ml_write_cons_def; merge_env_def; empty_env_def; nsAppend_nsEmpty;
       sem_env_component_equality; nsAppend_assoc]);;

(* appending a Dtabbrev *)

let ML_code_Dtabbrev = prove
 (`!x y z locs. ML_code inp_env (CONS (comm,s1,prog,env2) bls) (s2:(FFI)state) ==>
     ML_code inp_env (CONS (comm,s1,SNOC (Dtabbrev locs x y z) prog,env2) bls) s2`,
  REWRITE_TAC[ML_code_def; SNOC_APPEND; Decls_APPEND; Decls_Dtabbrev] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env2:v sem_env`; `empty_env:v sem_env`; `s2:(FFI)state`] THEN
  ASM_REWRITE_TAC[merge_env_empty_env]);;

(* appending a Letrec *)

(* HOL4 [local] *)
let build_rec_env_APPEND = prove
 (`nsAppend (build_rec_env funs cl_env nsEmpty) add_to_env =
   build_rec_env funs cl_env add_to_env`,
  REWRITE_TAC[build_rec_env_def] THEN
  SPEC_TAC (`Recclosure cl_env funs`,`hh:varN->v`) THEN
  SPEC_TAC (`add_to_env:(mlstring,mlstring,v)namespace`,`xs:(mlstring,mlstring,v)namespace`) THEN
  SPEC_TAC (`funs:(varN#varN#exp)list`,`l:(varN#varN#exp)list`) THEN
  LIST_INDUCT_TAC THEN TRY (PAIR_CASES_ON `h:varN#varN#exp`) THEN
  FS[ITLIST; nsAppend_nsEmpty; nsAppend_nsBind]);;

let ML_code_Dletrec = prove
 (CASE_TERM `!fns locs. ML_code env0 (CONS (comm,s1,prog,env2) bls) (s2:(FFI)state) ==>
     ALL_DISTINCT (MAP (\xyz. match xyz with (x,y,z) -> x) fns) ==>
     let code_env = ML_code_env env0 (CONS (comm,s1,prog,env2) bls) in
     let env3 = ml_write_rec fns code_env env2 in
     ML_code env0 (CONS (comm,s1,SNOC (Dletrec locs fns) prog,env3) bls) s2`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; ML_code_env_def; SNOC_APPEND;
              Decls_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env2:v sem_env`;
    `ml_write_rec fns (merge_env env2 (ML_code_env env0
       (bls:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list))) empty_env`;
    `s2:(FFI)state`] THEN
  ASM_REWRITE_TAC[Decls_Dletrec] THEN
  SIMP[write_rec_thm; merge_env_def; empty_env_def; nsAppend_nsEmpty;
       build_rec_env_APPEND; sem_env_component_equality]);;

(* appending a Let *)

let ML_code_Dlet_var = prove
 (`!cenv e s3 x n locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) (s2:(FFI)state) ==>
     eval_rel s2 cenv e s3 x ==>
     cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) ==>
     let env2 = ml_write n x env1 in let s3_abbrev = s3 in
     ML_code env0 (CONS (comm,s1,SNOC (Dlet locs (Pvar n) e) prog,env2) bls) s3_abbrev`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; ML_code_env_def; SNOC_APPEND;
              Decls_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `ml_write n x empty_env`; `s2:(FFI)state`] THEN
  ASM_REWRITE_TAC[Decls_Dlet] THEN CONJ_TAC THENL
   [EXISTS_TAC `x:v` THEN FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    ASM_REWRITE_TAC[];
    SIMP[ml_write_def; merge_env_def; empty_env_def; nsAppend_nsEmpty; nsAppend_nsBind;
         sem_env_component_equality]]);;

let ML_code_Dlet_var_lit = prove
 (`!loc name l. ML_code env0 (CONS (comm,s1,prog,env1) bls) (s2:(FFI)state) ==>
     let env2 = ml_write name (Litv l) env1 in let s3_abbrev = s2 in
     ML_code env0 (CONS (comm,s1,SNOC (Dlet loc (Pvar name) (Lit l)) prog,env2) bls)
       s3_abbrev`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`ML_code_env env0 (CONS ((comm:mlstring#mlstring),(s1:(FFI)state),
                    (prog:dec list),(env1:v sem_env))
                   (bls:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list))`;
                 `Lit l`;
                 `s2:(FFI)state`; `Litv l`; `name:varN`; `loc:locs`] ML_code_Dlet_var) THEN
  ASM_REWRITE_TAC[eval_rel_def; evaluate_def] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`0`; `0`] THEN REWRITE_TAC[]; REWRITE_TAC[]]);;

let ML_code_Dlet_Fun = prove
 (`!n v e locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) (s2:(FFI)state) ==>
     let code_env = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) in
     let v_abbrev = Closure code_env v e in
     let env2 = ml_write n v_abbrev env1 in
     ML_code env0 (CONS (comm,s1,SNOC (Dlet locs (Pvar n) (Fun v e)) prog,env2) bls) s2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  MP_TAC (REWRITE_RULE[LET_DEF; LET_END_DEF]
    (SPECL [`ML_code_env env0 (CONS ((comm:mlstring#mlstring),(s1:(FFI)state),
                (prog:dec list),(env1:v sem_env))
               (bls:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list))`;
            `Fun v e`; `s2:(FFI)state`;
            `Closure (ML_code_env env0 (CONS ((comm:mlstring#mlstring),(s1:(FFI)state),
                (prog:dec list),(env1:v sem_env))
               (bls:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list))) v e`;
            `n:varN`; `locs:locs`] ML_code_Dlet_var)) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[eval_rel_def; evaluate_def] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`0`; `0`] THEN REWRITE_TAC[]; REWRITE_TAC[]]);;

let ML_code_Dlet_Var_Var = prove
 (`!n vname locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) (s2:(FFI)state) ==>
     let cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) in
     !x. nsLookup (sem_env_v cenv) vname = SOME x ==>
     let env2 = ml_write n x env1 in
     ML_code env0 (CONS (comm,s1,SNOC (Dlet locs (Pvar n) (Var vname)) prog,env2) bls) s2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (REWRITE_RULE[LET_DEF; LET_END_DEF]
    (SPECL [`ML_code_env env0 (CONS ((comm:mlstring#mlstring),(s1:(FFI)state),
                (prog:dec list),(env1:v sem_env))
               (bls:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list))`;
            `Var vname`; `s2:(FFI)state`; `x:v`; `n:varN`; `locs:locs`]
           ML_code_Dlet_var)) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[eval_rel_def; evaluate_def] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`0`; `0`] THEN SIMP[]; REWRITE_TAC[]]);;

let ML_code_Dlet_Var_Ref_Var = prove
 (`!n vname locs. ML_code env0 (CONS (comm,s1,prog,env1) bls) (s2:(FFI)state) ==>
     let cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) in
     !x. nsLookup (sem_env_v cenv) vname = SOME x ==>
     let len = LENGTH (state_refs s2) in
     let loc = Loc T len in
     let env2 = ml_write n loc env1 in
     let s2_abbrev = state_refs_fupd (K (APPEND (state_refs s2) [Refv x])) s2 in
     ML_code env0
       (CONS (comm,s1,SNOC (Dlet locs (Pvar n) (App Opref [Var vname])) prog,env2) bls)
       s2_abbrev`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (REWRITE_RULE[LET_DEF; LET_END_DEF]
    (SPECL [`ML_code_env env0 (CONS ((comm:mlstring#mlstring),(s1:(FFI)state),
                (prog:dec list),(env1:v sem_env))
               (bls:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list))`;
            `App Opref [Var vname]`;
            `state_refs_fupd (K (APPEND (state_refs s2) [Refv x])) (s2:(FFI)state)`;
            `Loc T (LENGTH (state_refs (s2:(FFI)state)))`; `n:varN`; `locs:locs`]
           ML_code_Dlet_var)) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN MAP_EVERY EXISTS_TAC [`0`; `0`] THEN
  FS[evaluate_def; do_app_def; store_alloc_def; list_result_def; RECORD_SELFID_ss]);;

(* appending an environment *)

let declare_env_rel_def = cake_def
  `declare_env_rel (s2:(FFI)state) (env1:v sem_env) s3 envv <=>
     ?es. declare_env (state_eval_state s2) env1 = SOME (envv,es) /\
          s3 = state_eval_state_fupd (K es) s2`;;

let ML_code_Denv = prove
 (`!n cenv s3 envv.
     ML_code env0 (CONS (comm,s1,prog,env1) bls) (s2:(FFI)state) ==>
     declare_env_rel s2 cenv s3 envv ==>
     cenv = ML_code_env env0 (CONS (comm,s1,prog,env1) bls) ==>
     let env2 = ml_write n envv env1 in
     let s3_abbrev = s3 in
     ML_code env0 (CONS (comm,s1,SNOC (Denv n) prog,env2) bls) s3_abbrev`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; ML_code_def; ML_code_env_def; SNOC_APPEND;
              Decls_APPEND; declare_env_rel_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`env1:v sem_env`; `ml_write n envv empty_env`; `s2:(FFI)state`] THEN
  ASM_REWRITE_TAC[Decls_Denv] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`envv:v`; `es:(eval_state)option`] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN ASM_REWRITE_TAC[];
    SIMP[ml_write_def; merge_env_def; empty_env_def; nsAppend_nsEmpty; nsAppend_nsBind;
         sem_env_component_equality]]);;

(* setting the eval_state *)

(* only supported at the top-level for simplicity *)
let ML_code_set_eval_state = prove
 (`ML_code env0 [(comm,s1,prog,env1)] (s2:(FFI)state) ==>
   state_eval_state s1 = NONE ==>
   !es. ML_code env0 [(comm,state_eval_state_fupd (K (SOME es)) s1,prog,env1)]
                     (state_eval_state_fupd (K (SOME es)) s2)`,
  REWRITE_TAC[ML_code_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`ML_code_env env0
                    ([]:((mlstring#mlstring)#(FFI)state#dec list#v sem_env)list)`;
                  `s1:(FFI)state`; `prog:dec list`; `env1:v sem_env`; `s2:(FFI)state`]
                 (GEN_ALL ml_Decls_set_eval_state)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `SOME es:(eval_state)option`) THEN
  REWRITE_TAC[]);;

(* lookup function definitions *)

let ml_lookup_var_def = cake_def
  `ml_lookup_var name (env:v sem_env) = nsLookup (sem_env_v env) (Short name)`;;

let ml_lookup_cons_def = cake_def
  `ml_lookup_cons name (env:v sem_env) = nsLookup (sem_env_c env) name`;;

(* the old lookup formulation worked via nsLookup/mod_defined, and          *)
(* mod_defined is still used in various characteristic scripts so we supply *)
(* an eval theorem that maps to the new approach.                           *)

let mod_defined_def = cake_def
  `mod_defined (env:(M,N,V)namespace) (n:(M,N)id) <=>
     ?p1 p2 e3. ~(p1 = []) /\ id_to_mods n = APPEND p1 p2 /\
                nsLookupMod env p1 = SOME e3`;;

(* HOL4 [compute] *)
let mod_defined_nsLookup_Mod1 = prove
 (CASE_TERM `mod_defined (env:(M,N,V)namespace) id <=>
   (match id with
      Short _ -> F
    | Long mn _ -> (match nsLookup_Mod1 env mn with NONE -> F | _ -> T))`,
  QCASES_ON "id" THEN SIMP[mod_defined_def; id_to_mods_def] THEN
  QCASES_ON "env" THEN SIMP[nsLookup_Mod1_def] THEN EQ_TAC THENL
   [DISCH_THEN (X_CHOOSE_THEN `p1:M list` MP_TAC) THEN
    QCASES_ON "p1" THEN SIMP[APPEND; nsLookupMod_def] THEN
    STRIP_TAC THEN QPAT_X_ASSUM "a0 = _" (SUBST_ALL_TAC o SYM) THEN
    QPAT_X_ASSUM "_ = SOME e3" MP_TAC THEN CASE_TAC THEN SIMP[];
    CASE_TAC THEN SIMP[] THEN
    MAP_EVERY EXISTS_TAC [`[a0:M]`; `id_to_mods (a1:(M,N)id)`] THEN
    ASM_SIMP_TAC[APPEND; NOT_CONS_NIL; nsLookupMod_def] THEN SIMP[]]);;

(* theorems about old lookup functions *)
(* FIXME: everything below this line is unlikely to be needed. *)

(* HOL4 [local] *)
let nsLookupMod_nsBind = prove
 (`~(p = []) ==> nsLookupMod (nsBind k v env:(M,N,V)namespace) p = nsLookupMod env p`,
  QCASES_ON "env" THEN QCASES_ON "p" THEN SIMP[nsBind_def; nsLookupMod_def]);;

let nsLookup_write = prove
 (`(nsLookup (sem_env_v (ml_write n v env)) (Short name) =
     if n = name then SOME v else nsLookup (sem_env_v env) (Short name)) /\
   (nsLookup (sem_env_v (ml_write n v env)) (Long mn lname) =
     nsLookup (sem_env_v env) (Long mn lname)) /\
   (nsLookup (sem_env_c (ml_write n v env)) a = nsLookup (sem_env_c env) a) /\
   (mod_defined (sem_env_v (ml_write n v env)) x = mod_defined (sem_env_v env) x) /\
   (mod_defined (sem_env_c (ml_write n v env)) y = mod_defined (sem_env_c env) y)`,
  REWRITE_TAC[write_simp] THEN SIMP[ml_write_def] THEN
  REWRITE_TAC[mod_defined_def] THEN MESON_TAC[nsLookupMod_nsBind]);;

let nsLookup_write_cons = prove
 (`(nsLookup (sem_env_v (ml_write_cons n v env)) a = nsLookup (sem_env_v env) a) /\
   (nsLookup (sem_env_c (ml_write_cons n d env)) (Short name) =
     if name = n then SOME d else nsLookup (sem_env_c env) (Short name)) /\
   (mod_defined (sem_env_v (ml_write_cons n d env)) x = mod_defined (sem_env_v env) x) /\
   (mod_defined (sem_env_c (ml_write_cons n d env)) y = mod_defined (sem_env_c env) y) /\
   (nsLookup (sem_env_c (ml_write_cons n d env)) (Long mn lname) =
    nsLookup (sem_env_c env) (Long mn lname))`,
  REWRITE_TAC[write_cons_simp] THEN SIMP[ml_write_cons_def; nsAppend_nsSing] THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ;
    REWRITE_TAC[mod_defined_def] THEN MESON_TAC[nsLookupMod_nsBind]]);;

let nsLookup_empty = prove
 (`(nsLookup (sem_env_v (empty_env:v sem_env)) a = NONE) /\
   (nsLookup (sem_env_c (empty_env:v sem_env)) b = NONE) /\
   (mod_defined (sem_env_v (empty_env:v sem_env)) x <=> F) /\
   (mod_defined (sem_env_c (empty_env:v sem_env)) y <=> F)`,
  REWRITE_TAC[empty_simp] THEN
  REWRITE_TAC[empty_env_def; mod_defined_def; sem_env_INFO.ri_accessors] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN QCASES_ON "p1" THEN FS[nsLookupMod_nsEmpty]);;

let nsLookup_write_mod = prove
 (`(nsLookup (sem_env_v (ml_write_mod mn env1 env2)) (Short n) =
    nsLookup (sem_env_v env2) (Short n)) /\
   (nsLookup (sem_env_c (ml_write_mod mn env1 env2)) (Short n) =
    nsLookup (sem_env_c env2) (Short n)) /\
   (mod_defined (sem_env_v (ml_write_mod mn env1 env2)) (Long mn' r) <=>
     (mn = mn') \/ mod_defined (sem_env_v env2) (Long mn' r)) /\
   (mod_defined (sem_env_c (ml_write_mod mn env1 env2)) (Long mn' r) <=>
     if mn = mn' then T else mod_defined (sem_env_c env2) (Long mn' r)) /\
   (nsLookup (sem_env_v (ml_write_mod mn env1 env2)) (Long mn1 ln) =
    if mn = mn1 then nsLookup (sem_env_v env1) ln
    else nsLookup (sem_env_v env2) (Long mn1 ln)) /\
   (nsLookup (sem_env_c (ml_write_mod mn env1 env2)) (Long mn1 ln) =
    if mn = mn1 then nsLookup (sem_env_c env1) ln
    else nsLookup (sem_env_c env2) (Long mn1 ln))`,
  REWRITE_TAC[write_mod_simp] THEN
  REWRITE_TAC[mod_defined_nsLookup_Mod1; nsLookup_write_mod_eqs; option_choice_f_apply;
              ALOOKUP_def] THEN
  SIMP[] THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_CHOICE_DEF] THEN
  SIMP[]);;

(* helpers: lookups in nsAppend through Long names, and mod_defined *)
let MLPROGAUX_mod_defined_nsAppend = prove
 (`!(e1:(M,N,V)namespace) e2 x.
     mod_defined (nsAppend e1 e2) x <=> mod_defined e1 x \/ mod_defined e2 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mod_defined_nsLookup_Mod1] THEN QCASES_ON "x" THEN
  SIMP[nsLookup_Mod1_nsAppend; option_choice_f_apply] THEN
  QCASES_ON "nsLookup_Mod1 e1 a0" THEN QCASES_ON "nsLookup_Mod1 e2 a0" THEN
  ASM_REWRITE_TAC[OPTION_CHOICE_DEF] THEN SIMP[]);;

let MLPROGAUX_nsLookup_nsAppend_Long = prove
 (CASE_TERM `!(e1:(M,N,V)namespace) e2 mn ln.
     nsLookup (nsAppend e1 e2) (Long mn ln) =
     match nsLookup e1 (Long mn ln) with
       NONE -> if mod_defined e1 (Long mn ln) then NONE else nsLookup e2 (Long mn ln)
     | SOME x -> SOME x`,
  REPEAT GEN_TAC THEN QCASES_ON "e1" THEN QCASES_ON "e2" THEN
  REWRITE_TAC[mod_defined_nsLookup_Mod1; nsAppend_def] THEN
  SIMP[nsLookup_def; nsLookup_Mod1_def; ALOOKUP_APPEND] THEN
  CASE_TAC THEN SIMP[] THEN CASE_TAC THEN SIMP[]);;

let nsLookup_merge_env = prove
 (CASE_TERM `(nsLookup (sem_env_v (merge_env e1 e2)) (Short n) =
      match nsLookup (sem_env_v e1) (Short n) with
        NONE -> nsLookup (sem_env_v e2) (Short n)
      | SOME x -> SOME x) /\
   (nsLookup (sem_env_c (merge_env e1 e2)) (Short n) =
      match nsLookup (sem_env_c e1) (Short n) with
        NONE -> nsLookup (sem_env_c e2) (Short n)
      | SOME x -> SOME x) /\
   (nsLookup (sem_env_v (merge_env e1 e2)) (Long mn ln) =
      match nsLookup (sem_env_v e1) (Long mn ln) with
        NONE -> if mod_defined (sem_env_v e1) (Long mn ln) then NONE
                else nsLookup (sem_env_v e2) (Long mn ln)
      | SOME x -> SOME x) /\
   (nsLookup (sem_env_c (merge_env e1 e2)) (Long mn ln) =
      match nsLookup (sem_env_c e1) (Long mn ln) with
        NONE -> if mod_defined (sem_env_c e1) (Long mn ln) then NONE
                else nsLookup (sem_env_c e2) (Long mn ln)
      | SOME x -> SOME x) /\
   (mod_defined (sem_env_v (merge_env e1 e2)) x <=>
      mod_defined (sem_env_v e1) x \/ mod_defined (sem_env_v e2) x) /\
   (mod_defined (sem_env_c (merge_env e1 e2)) x <=>
      mod_defined (sem_env_c e1) x \/ mod_defined (sem_env_c e2) x)`,
  SIMP[merge_env_def; nsLookup_nsAppend_Short; MLPROGAUX_nsLookup_nsAppend_Long;
       MLPROGAUX_mod_defined_nsAppend]);;

(* HOL4 [compute] *)
let nsLookup_nsBind_compute = prove
 (`(nsLookup (nsBind n v e:(M,N,V)namespace) (Short n1) =
    if n = n1 then SOME v else nsLookup e (Short n1)) /\
   (nsLookup (nsBind n v e) (Long l1 l2) = nsLookup e (Long l1 l2))`,
  CONJ_TAC THENL [COND_CASES_TAC; ALL_TAC] THEN ASM_SIMP_TAC[nsLookup_nsBind] THEN
  MATCH_MP_TAC (CONJUNCT2 nsLookup_nsBind) THEN SIMP[]);;

(* HOL4 [compute]: nsLookup_merge_env on the components of two sem_env     *)
(* records, simplified                                                       *)
let nsLookup_nsAppend =
  CONV_RULE (CAKE_SIMP_CONV[merge_env_def])
    (INST [`sem_env_REC e1v e1c:v sem_env`,`e1:v sem_env`;
           `sem_env_REC e2v e2c:v sem_env`,`e2:v sem_env`] nsLookup_merge_env);;

(* Base case for mod_defined (?) *)
(* HOL4 [compute] *)
let mod_defined_base = prove
 (`mod_defined (Bind (a:(N#V)list) [] :(M,N,V)namespace) (x:(M,N)id) <=> F`,
  REWRITE_TAC[mod_defined_nsLookup_Mod1] THEN QCASES_ON "x" THEN
  SIMP[nsLookup_Mod1_Bind; ALOOKUP_def]);;

(* --- the rest of this file might be unused junk --- *)

(* misc theorems about lookup functions *)

(* No idea why this is sparated out *)
let lookup_var_write = prove
 (`(ml_lookup_var v (ml_write w x env) =
     if v = w then SOME x else ml_lookup_var v env) /\
   (nsLookup (sem_env_v (ml_write w x env)) (Short v) =
     if v = w then SOME x else nsLookup (sem_env_v env) (Short v)) /\
   (nsLookup (sem_env_v (ml_write w x env)) (Long mn lname) =
     nsLookup (sem_env_v env) (Long mn lname)) /\
   (ml_lookup_cons name (ml_write w x env) = ml_lookup_cons name env)`,
  REWRITE_TAC[ml_lookup_var_def; ml_lookup_cons_def; nsLookup_write] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);;

let lookup_var_write_mod = prove
 (`(ml_lookup_var v (ml_write_mod mn e1 env) = ml_lookup_var v env) /\
   (ml_lookup_cons (Long mn1 (Short name)) (ml_write_mod mn2 e1 env) =
     if mn1 = mn2 then ml_lookup_cons (Short name) e1
     else ml_lookup_cons (Long mn1 (Short name)) env) /\
   (ml_lookup_cons (Short name) (ml_write_mod mn2 e1 env) =
     ml_lookup_cons (Short name) env)`,
  REWRITE_TAC[ml_lookup_var_def; ml_lookup_cons_def; nsLookup_write_mod] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);;

let lookup_var_write_cons = prove
 (`(ml_lookup_var v (ml_write_cons n d env) = ml_lookup_var v env) /\
   (ml_lookup_cons (Short name) (ml_write_cons n d env) =
     if name = n then SOME d else ml_lookup_cons (Short name) env) /\
   (ml_lookup_cons (Long l full_name) (ml_write_cons n d env) =
     ml_lookup_cons (Long l full_name) env) /\
   (nsLookup (sem_env_v (ml_write_cons n d env)) x = nsLookup (sem_env_v env) x)`,
  REWRITE_TAC[ml_lookup_var_def; ml_lookup_cons_def; nsLookup_write_cons]);;

let lookup_var_empty_env = prove
 (`(ml_lookup_var v (empty_env:v sem_env) = NONE) /\
   (nsLookup (sem_env_v (empty_env:v sem_env)) (Short k) = NONE) /\
   (nsLookup (sem_env_v (empty_env:v sem_env)) (Long mn m) = NONE) /\
   (ml_lookup_cons name (empty_env:v sem_env) = NONE)`,
  REWRITE_TAC[ml_lookup_var_def; ml_lookup_cons_def; empty_simp]);;

let prog_syntax_ok_def = cake_def
  `prog_syntax_ok prog <=> IS_SOME (check_cons_dec_list (sem_env_c ml_init_env) prog)`;;

let prog_syntax_ok_isPREFIX = prove
 (`!p1 p2. prog_syntax_ok p1 /\ isPREFIX p2 p1 ==> prog_syntax_ok p2`,
  REWRITE_TAC[prog_syntax_ok_def; IS_SOME_EXISTS] THEN
  MESON_TAC[check_cons_dec_list_isPREFIX]);;

let Decls_IMP_Prog = prove
 (`Decls ml_init_env (s1:(FFI)state) ds env2 s2 ==>
   prog_syntax_ok ds ==>
   Prog ml_init_env s1 ds env2 s2`,
  REWRITE_TAC[ml_Decls_def; ml_Prog_def; prog_syntax_ok_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`ck1:num`; `ck2:num`] THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC evaluate_dec_list_eq_evaluate_decs THEN
  ASM_REWRITE_TAC[state_INFO.ri_accfupds]);;

let prog_syntax_ok_semantics = prove
 (`prog_syntax_ok prog ==>
   semantics_dec_list (st:(FFI)state) ml_init_env prog =
   semantics_prog st ml_init_env prog`,
  REWRITE_TAC[FUN_EQ_THM] THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `!k. evaluate_dec_list_with_clock (st:(FFI)state) ml_init_env k prog =
                    evaluate_prog_with_clock st ml_init_env k prog` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_with_clock_def;
                             evaluate_prog_with_clock_def] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC evaluate_dec_list_eq_evaluate_decs THEN
    ASM_REWRITE_TAC[GSYM prog_syntax_ok_def];
    ALL_TAC] THEN
  QCASES_ON "x" THEN ASM_REWRITE_TAC[semantics_prog_def; semantics_dec_list_def]);;
