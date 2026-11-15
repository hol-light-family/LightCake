(* ========================================================================= *)
(* source_letProof: port of HOL4 compiler/backend/proofs/                    *)
(* source_letProofScript.sml (CakeML v3479).  Correctness of the source_let  *)
(* pass, which lifts the lets of top-level declarations into Dlocal.         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - evaluate_lift_start is stated directly in the form that HOL4 obtains    *)
(*   by specialising evaluate_lift_lets to the empty list and simplifying.   *)
(* - lift_lets_mod_local is HOL4 [local,simp]: it is not registered with     *)
(*   cake_add_simps (descendants do not see it in HOL4); it is used          *)
(*   explicitly.                                                             *)
(* - SLETPAUX_ names are local helpers.                                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semantics.ml";;
needs "compiler/backend/source_let.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;

type_invention_error := true;;

let env_c_lemma = prove
 (`sem_env_c (extend_dec_env (sem_env_REC (build_rec_env q env env1) nsEmpty) (env:v sem_env)) =
   sem_env_c env`,
  REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors; nsAppend_nsEmpty]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers for evaluate_lift_let: normal forms of the environments     *)
(* built by the evaluation of a Let or Letrec and of its lifted form.        *)
(* ------------------------------------------------------------------------- *)

let SLETPAUX_REC_fupd = prove
 (`!v e:v sem_env. sem_env_REC v (sem_env_c e) = sem_env_v_fupd (K v) e`,
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accessors; sem_env_INFO.ri_accfupds;
              K_THM]);;

let SLETPAUX_alist_sing = prove
 (`!(a:N) (x:V) (e:(M,N,V)namespace). nsAppend (alist_to_ns [(a,x)]) e = nsBind a x e`,
  REWRITE_TAC[nsAppend_to_nsBindList; nsBindList_def; ITLIST] THEN CASE_REWRITE_TAC[]);;

let SLETPAUX_ENV_RW =
  [sem_env_INFO.ri_accessors; nsAppend_nsEmpty; unchanged_env; alist_to_ns_nil;
   SLETPAUX_alist_sing; SLETPAUX_REC_fupd; build_rec_env_merge;
   SEVPAUX_sem_env_v_fupd_id];;

(* one pass over the case-split evaluation facts: normalise, resolve the    *)
(* equal function applications, substitute                                   *)
let SLETPAUX_CORE_TAC : tactic =
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o CONV_RULE(DEPTH_CONV BETA_CONV) o
                 REWRITE_RULE SLETPAUX_ENV_RW) THEN
  SEVPAUX_FUNC_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE([PAIR_EQ; injectivity "result"; distinctness "result";
                              injectivity "match_result"; distinctness "match_result"; MEM] @
                              SLETPAUX_ENV_RW)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[];;

let SLETPAUX_CLOSE_TAC : tactic =
  SLETPAUX_CORE_TAC THEN SLETPAUX_CORE_TAC THEN SLETPAUX_CORE_TAC THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  TRY(ASM_MESON_TAC[] THEN NO_TAC);;

(* the declaration is Dlet of a Let *)
let SLETPAUX_LET_TAC : tactic =
  CASES_ON `a0':mlstring option` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> EVPROPSAUX_is_eval_eq (concl th))) THEN
  REWRITE_TAC[evaluate_decs_def] THEN ONCE_REWRITE_TAC[full_evaluate_def] THEN
  REWRITE_TAC([every_exp_def; one_con_check_def; pat_bindings_def; ALL_DISTINCT; nsOptBind_def;
              pmatch_def; extend_dec_env_def] @ SLETPAUX_ENV_RW) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC SLETPAUX_ENV_RW THEN CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC([injectivity "result"; distinctness "result"; PAIR_EQ] @ SLETPAUX_ENV_RW) THEN
  SLETPAUX_CLOSE_TAC;;

(* the declaration is Dlet of a Letrec *)
let SLETPAUX_LETREC_TAC : tactic =
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> EVPROPSAUX_is_eval_eq (concl th))) THEN
  REWRITE_TAC[evaluate_decs_def] THEN ONCE_REWRITE_TAC[full_evaluate_def] THEN
  REWRITE_TAC([every_exp_def; one_con_check_def; pat_bindings_def; ALL_DISTINCT;
               extend_dec_env_def] @ SLETPAUX_ENV_RW) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC SLETPAUX_ENV_RW THEN CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC([injectivity "result"; distinctness "result"; PAIR_EQ] @ SLETPAUX_ENV_RW) THEN
  SLETPAUX_CLOSE_TAC;;

let evaluate_lift_let = prove
 (`evaluate_decs (s:(FFI)state) env [d] = (s',res) /\ ~(res = Rerr (Rabort Rtype_error)) /\
   lift_let d = SOME (d1,d2) ==> evaluate_decs s env [Dlocal [d1] [d2]] = (s',res)`,
  STRUCT_CASES_TAC (ISPEC `d:dec` (nchotomy_of_type `:dec`)) THEN
  REWRITE_TAC[lift_let_def; distinctness "option"] THEN
  W (fun (_,w) ->
       let v = find_term (fun t -> is_var t && type_of t = `:exp`) w in
       STRUCT_CASES_TAC (ISPEC v (nchotomy_of_type `:exp`))) THEN
  REWRITE_TAC[dest_Let_def; dest_Letrec_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THENL [SLETPAUX_LET_TAC; SLETPAUX_LETREC_TAC]);;

let lift_lets_is_prefix = prove
 (`!ds d ds1 ds2. lift_lets ds d = SOME (ds1,ds2) ==> REVERSE ds <<= ds1`,
  MATCH_MP_TAC lift_lets_ind THEN X_GEN_TAC `sofar:dec list` THEN X_GEN_TAC `d:dec` THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[lift_lets_def] THEN
  MP_TAC(ISPEC `lift_let d` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:dec#dec` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THENL
   [STRUCT_CASES_TAC (ISPEC `sofar:dec list` list_CASES) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IS_PREFIX_REFL];
    MP_TAC(ISPEC `p:dec#dec` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:dec` (X_CHOOSE_THEN `d2:dec` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ds1:dec list`; `ds2:dec`] o
                  C MP (REFL `SOME (d1:dec,d2:dec)`) o SPECL [`d1:dec`; `d2:dec`]) THEN
    ASM_REWRITE_TAC[REVERSE] THEN
    MESON_TAC[isPREFIX_TRANS; IS_PREFIX_APPEND]]);;

let evaluate_lift_lets = prove
 (`!ds d s env s1 env1 s2 res ds1 ds2.
     evaluate_decs (s:(FFI)state) env (REVERSE ds) = (s1,Rval env1) /\
     evaluate_decs s1 (extend_dec_env env1 env) [d] = (s2,res) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     lift_lets ds d = SOME (ds1,ds2) ==>
     evaluate_decs s env [Dlocal ds1 [ds2]] = (s2,res)`,
  MATCH_MP_TAC lift_lets_ind THEN X_GEN_TAC `ds:dec list` THEN X_GEN_TAC `d:dec` THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `lift_lets ds d = SOME (ds1:dec list,ds2:dec)` THEN
  ONCE_REWRITE_TAC[lift_lets_def] THEN
  MP_TAC(ISPEC `lift_let d` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:dec#dec` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [(* no let to lift: the declarations so far form the local part *)
    MP_TAC(ISPEC `ds:dec list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `h:dec` (X_CHOOSE_THEN `t:dec list` SUBST_ALL_TAC))) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[evaluate_decs_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a let is lifted *)
  MP_TAC(ISPEC `p:dec#dec` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:dec` (X_CHOOSE_THEN `d2:dec` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(INST [`s1:(FFI)state`,`s:(FFI)state`; `extend_dec_env env1 env:v sem_env`,`env:v sem_env`;
               `s2:(FFI)state`,`s':(FFI)state`] evaluate_lift_let) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[evaluate_decs_def] THEN
  MP_TAC(ISPEC `evaluate_decs (s1:(FFI)state) (extend_dec_env env1 env) [d1:dec]`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v sem_env,v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r3:(v sem_env,v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `env3:v sem_env` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e3:(v)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THENL
   [(* the lifted declaration succeeds: induction hypothesis *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:(FFI)state`; `env:v sem_env`; `s3:(FFI)state`;
       `extend_dec_env env3 env1:v sem_env`; `s2:(FFI)state`; `res:(v sem_env,v)result`;
       `ds1:dec list`; `ds2:dec`] o
       C MP (ASSUME `lift_let d = SOME (d1:dec,d2:dec)`) o SPECL [`d1:dec`; `d2:dec`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REVERSE; evaluate_decs_append] THEN
        REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
        REWRITE_TAC[combine_dec_result_def; extend_dec_env_def] THEN CASE_REWRITE_TAC[];
        ASM_REWRITE_TAC[GSYM extend_dec_env_assoc];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[evaluate_decs_def]];
    (* the lifted declaration fails: the prefix of the local part fails *)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP lift_lets_is_prefix o
                check (fun th -> SEVPAUX_has_const "lift_lets" th)) THEN
    REWRITE_TAC[IS_PREFIX_APPEND; REVERSE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[evaluate_decs_append] THEN
    REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
    REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 [local,simp]: not registered (descendants do not see it in HOL4)     *)
let lift_lets_mod_local = prove
 (`(!ds1 ds2. lift_lets [] (Dlocal ds1 ds2) = NONE) /\
   (!mn ds. lift_lets [] (Dmod mn ds) = NONE)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[lift_lets_def] THEN
  REWRITE_TAC[lift_let_def] THEN CASE_REWRITE_TAC[]);;

let evaluate_lift_start = prove
 (`!d s env s2 res ds1 ds2.
     evaluate_decs (s:(FFI)state) env [d] = (s2,res) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     lift_lets [] d = SOME (ds1,ds2) ==>
     evaluate_decs s env [Dlocal ds1 [ds2]] = (s2,res)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC evaluate_lift_lets THEN
  MAP_EVERY EXISTS_TAC [`[]:dec list`; `d:dec`; `s:(FFI)state`;
                        `sem_env_REC nsEmpty nsEmpty:v sem_env`] THEN
  ASM_REWRITE_TAC[REVERSE; evaluate_decs_def; extend_dec_env_def; sem_env_INFO.ri_accessors;
                  nsAppend_nsEmpty; unchanged_env]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers for compile_decs_correct.                                   *)
(* ------------------------------------------------------------------------- *)

(* the compilation of a list of declarations is that of each *)
let SLETPAUX_compile_cons = prove
 (`!d ds. source_let_compile_decs (CONS d ds) =
          APPEND (source_let_compile_decs [d]) (source_let_compile_decs ds)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_let_compile_decs_def] THEN
  MP_TAC(ISPEC `lift_lets [] d` (cases "option")) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THENL
   [STRUCT_CASES_TAC (ISPEC `d:dec` (nchotomy_of_type `:dec`)) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND];
    MP_TAC(ISPEC `a:dec list#dec` PAIR_SURJECTIVE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND]]);;

(* a single declaration other than Dmod and Dlocal *)
let SLETPAUX_SINGLE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[source_let_compile_decs_def] THEN
  (fun (asl,w as gl) ->
     let t = find_term (fun t -> EVPROPSAUX_is_const_app ["lift_lets"] t) w in
     MP_TAC(ISPEC t (cases "option")) gl) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TRY(MP_TAC(ISPEC `a:dec list#dec` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MATCH_MP_TAC evaluate_lift_start THEN
      FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                               EVPROPSAUX_is_const_app ["lift_lets"] (lhs (concl th))
                            then EXISTS_TAC (rand (lhs (concl th))) else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[];;

let SLETPAUX_no_ext th =
  not (can (find_term (fun t -> EVPROPSAUX_is_const_app ["extend_dec_env"] t)) (concl th));;

let source_letProof_compile_decs_correct = prove
 (`!s env ds s' res.
     evaluate_decs (s:(FFI)state) env ds = (s',res) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     evaluate_decs s env (source_let_compile_decs ds) = (s',res)`,
  MATCH_MP_TAC evaluate_decs_ind THEN REPEAT CONJ_TAC THENL
   [(* [] *)
    SIMP_TAC[source_let_compile_decs_def];
    (* d1::d2::ds *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[SLETPAUX_compile_cons] THEN REWRITE_TAC[evaluate_decs_append] THEN
    UNDISCH_TAC `evaluate_decs (st:(FFI)state) env (CONS d1 (CONS d2 ds)) = s',res` THEN
    REWRITE_TAC[evaluate_decs_def] THEN
    MP_TAC(ISPEC `evaluate_decs (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r1:(v sem_env,v)result` (cases "result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `env1:v sem_env` SUBST_ALL_TAC)
                                (X_CHOOSE_THEN `e1:(v)error_result` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(FFI)state`; `Rval env1:(v sem_env,v)result`] o
                    check (fun th -> is_forall (concl th) &&
                             not (can (find_term ((=) `d2:dec`)) (concl th)))) THEN
      ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `evaluate_decs (s1:(FFI)state) (extend_dec_env env1 env) (CONS d2 ds)`
               PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(FFI)state`; `env1:v sem_env`] o
                    check (fun th -> is_forall (concl th) &&
                             can (find_term ((=) `d2:dec`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[SEVPAUX_combine_tyerr]; DISCH_THEN SUBST1_TAC] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s':(FFI)state`; `Rerr e1:(v sem_env,v)result`] o
                    check (fun th -> is_forall (concl th) &&
                             not (can (find_term ((=) `d2:dec`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]];
    (* Dlet, Dletrec, Dtype, Dtabbrev, Denv, Dexn *)
    SLETPAUX_SINGLE_TAC; SLETPAUX_SINGLE_TAC; SLETPAUX_SINGLE_TAC; SLETPAUX_SINGLE_TAC;
    SLETPAUX_SINGLE_TAC; SLETPAUX_SINGLE_TAC;
    (* Dmod *)
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[source_let_compile_decs_def; lift_lets_mod_local] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[evaluate_decs_def] THEN
     MP_TAC(ISPEC `evaluate_decs (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC) THEN
    SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v sem_env,v)result)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(FFI)state`; `r1:(v sem_env,v)result`] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[PAIR_EQ];
    (* Dlocal *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC[source_let_compile_decs_def; lift_lets_mod_local] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[evaluate_decs_def] THEN
     MP_TAC(ISPEC `evaluate_decs (st:(FFI)state) env lds` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result` ASSUME_TAC)) THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPEC `r1:(v sem_env,v)result` (cases "result")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `env1:v sem_env` SUBST_ALL_TAC)
                                 (X_CHOOSE_THEN `e1:(v)error_result` SUBST_ALL_TAC)) THEN
     CASE_REWRITE_TAC[] THEN STRIP_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(FFI)state`; `Rval env1:(v sem_env,v)result`] o
                    check (fun th -> is_forall (concl th) && SLETPAUX_no_ext th)) THEN
      ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(FFI)state`; `env1:v sem_env`] o
                    check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`s':(FFI)state`; `res:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s1:(FFI)state = s'`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `Rerr e1:(v sem_env,v)result = res`)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s':(FFI)state`; `Rerr e1:(v sem_env,v)result`] o
                    check (fun th -> is_forall (concl th) && SLETPAUX_no_ext th)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]]);;

(* local: without Fail, the compiled program runs as the original for every *)
(* clock                                                                     *)
let SLETPAUX_runs = prove
 (`~semantics_prog (s:(FFI)state) env prog Fail ==>
   !k. evaluate_prog_with_clock s env k (source_let_compile_decs prog) =
       evaluate_prog_with_clock s env k prog`,
  DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP SEVPAUX_not_fail) THEN
  REWRITE_TAC[SEVPAUX_evaluate_prog_with_clock] THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (K k) (s:(FFI)state)) env prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_TAC `r1:(v sem_env,v)result`)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`state_clock_fupd (K k) (s:(FFI)state)`; `env:v sem_env`; `prog:dec list`;
                `s1:(FFI)state`; `r1:(v sem_env,v)result`] source_letProof_compile_decs_correct) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND]);;

let source_letProof_compile_semantics = prove
 (`~semantics_prog (s:(FFI)state) env prog Fail /\ semantics_prog s env prog outcome ==>
   semantics_prog s env (source_let_compile_decs prog) outcome`,
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SLETPAUX_runs) THEN
  UNDISCH_TAC `semantics_prog (s:(FFI)state) env prog outcome` THEN
  STRUCT_CASES_TAC(ISPEC `outcome:behaviour` (cases "behaviour")) THEN
  ASM_REWRITE_TAC[semantics_prog_def]);;

let source_letProof_compile_semantics_oracle = prove
 (`!f. is_insert_oracle (ci:(C)compiler_instance) f (state_eval_state (s:(FFI)state)) /\
       ~semantics_prog s env prog Fail /\
       semantics_prog s env prog outcome ==>
       semantics_prog
         (state_eval_state_fupd (adjust_oracle ci (source_let_compile_decs o f)) s)
         env prog outcome`,
  GEN_TAC THEN MATCH_ACCEPT_TAC
    (MP (SPECL [`source_let_compile_decs`; `f:dec list->dec list`] adjust_oracle_semantics_prog)
        source_letProof_compile_decs_correct));;
