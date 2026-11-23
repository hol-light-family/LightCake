(* ========================================================================= *)
(* type_eDeterm: port of HOL4                                                *)
(* compiler/inference/proofs/type_eDetermScript.sml (CakeML v3479).          *)
(* Determinism lemmas about the type inferencer.                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;

type_invention_error := true;;

let type_eDeterm_sub_completion_empty = prove
 (`!m n s s'.
     sub_completion m n s [] s' <=>
     pred_set_count n SUBSET FDOM s' /\
     (!uv. uv IN FDOM s' ==> check_t m {} (t_walkstar s' (Infer_Tuvar uv))) /\ s = s'`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_def] THEN MESON_TAC[]);;

let type_p_pat_bindings = prove
 (`(!tvs tenv p t new_bindings.
      type_p tvs tenv p t new_bindings ==> MAP FST new_bindings = pat_bindings p) /\
   (!tvs tenv ps ts new_bindings.
      type_ps tvs tenv ps ts new_bindings ==> MAP FST new_bindings = pats_bindings ps)`,
  MATCH_MP_TAC type_p_ind THEN
  REWRITE_TAC[pat_bindings_def; MAP; MAP_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* the inferred and the typed bindings of a pattern, under a completion *)
let INFER1AUX_simp_tenv_invC_convert = prove
 (CASE_TERM `!s tvs (nb:(mlstring#infer_t)list) (tenv1:(mlstring#t)list).
     simp_tenv_invC s tvs nb tenv1 /\ MAP FST nb = MAP FST tenv1 /\ ALL_DISTINCT (MAP FST nb)
     ==> ALL (\(n,t). check_t tvs {} (t_walkstar s t)) nb /\ convert_env s nb = tenv1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simp_tenv_invC_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (nb:(mlstring#infer_t)list) = LENGTH (tenv1:(mlstring#t)list)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:mlstring list->num` o check (fun th ->
      concl th = `MAP FST (nb:(mlstring#infer_t)list) = MAP FST (tenv1:(mlstring#t)list)`)) THEN
    REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (tenv1:(mlstring#t)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL_DISTINCT (MAP FST (nb:(mlstring#infer_t)list))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* each binding: its type in tenv1 and its approximation *)
  SUBGOAL_THEN
    `!k. k < LENGTH (nb:(mlstring#infer_t)list)
         ==> FST (EL k (tenv1:(mlstring#t)list)) = FST (EL k nb) /\
             check_freevars tvs [] (SND (EL k (tenv1:(mlstring#t)list))) /\
             unconvert_t (SND (EL k tenv1)) = t_walkstar s (SND (EL k nb))`
    ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k < LENGTH (tenv1:(mlstring#t)list)` ASSUME_TAC THENL
     [UNDISCH_TAC `k < LENGTH (nb:(mlstring#infer_t)list)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `FST (EL k (tenv1:(mlstring#t)list)) = FST (EL k (nb:(mlstring#infer_t)list))`
      ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o AP_TERM `EL k:mlstring list->mlstring` o check (fun th ->
        concl th = `MAP FST (nb:(mlstring#infer_t)list) = MAP FST (tenv1:(mlstring#t)list)`)) THEN
      ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ALOOKUP (tenv1:(mlstring#t)list) (FST (EL k (nb:(mlstring#infer_t)list))) =
                  SOME (SND (EL k tenv1))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `FST (EL k (tenv1:(mlstring#t)list)) = FST (EL k (nb:(mlstring#infer_t)list))`)) THEN
      REWRITE_TAC[PAIR] THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALOOKUP (nb:(mlstring#infer_t)list) (FST (EL k nb)) = SOME (SND (EL k nb))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[PAIR] THEN
      MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`FST (EL k (nb:(mlstring#infer_t)list))`;
                                  `SND (EL k (tenv1:(mlstring#t)list))`] o
      check (fun th -> is_forall(concl th) &&
        (try free_in `tenv1:(mlstring#t)list` (fst(dest_imp(snd(strip_forall(concl th)))))
         with Failure _ -> false))) THEN
    ASM_REWRITE_TAC[injectivity "option"; UNWIND_THM1];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `EL k (nb:(mlstring#infer_t)list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:mlstring` (X_CHOOSE_THEN `b:infer_t` SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `unconvert_t (SND (EL k (tenv1:(mlstring#t)list))) = t_walkstar s b`)) THEN
    MATCH_MP_TAC check_freevars_to_check_t THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[convert_env_def; LIST_EQ; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `EL k (nb:(mlstring#infer_t)list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:mlstring` (X_CHOOSE_THEN `b:infer_t` SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `EL k (tenv1:(mlstring#t)list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a':mlstring` (X_CHOOSE_THEN `b':t` SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `unconvert_t b' = t_walkstar s b`)) THEN
    MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN
    EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[]]);;

let infer_pe_complete = prove
 (`!loc ienv tenv tvs p e t1 tenv1 ss.
     ienv_ok {} ienv /\
     env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty) /\
     ALL_DISTINCT (pat_bindings p) /\
     type_p tvs tenv p t1 tenv1 /\
     type_e tenv (bind_tvar tvs Empty) e t1
     ==> ?t t' new_bindings st st' s constrs s'.
           infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
           infer_p loc ienv p st = (M_success (t',new_bindings),st') /\
           t_unify (infer_st_subst st') t t' = SOME s /\
           sub_completion tvs (infer_st_next_uvar st') s constrs s' /\
           FDOM s' = pred_set_count (infer_st_next_uvar st') /\
           t1 = convert_t (t_walkstar s' t') /\
           t1 = convert_t (t_walkstar s' t) /\
           t_wfs s /\
           ALL (\(n,t). check_t tvs {} (t_walkstar s' t)) new_bindings /\
           convert_env s' new_bindings = tenv1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar (init_infer_state ss) = 0 /\
                infer_st_subst (init_infer_state ss) = FEMPTY` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv /\ inf_env_inf_c ienv = type_env_c tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_complete_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ienv_val_ok (pred_set_count 0) (inf_env_inf_v ienv) /\
                tenv_ctor_ok (type_env_c tenv) /\ tenv_abbrev_ok (type_env_t tenv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN ASM_REWRITE_TAC[ienv_ok_def; COUNT_ZERO] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tenv:type_env`; `bind_tvar tvs Empty`; `e:exp`; `t1:t`]
    (CONJUNCT1 infer_e_complete)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`loc:loc_err_info`; `FEMPTY:(num,infer_t)fmap`; `ienv:inf_env`;
                             `init_infer_state ss`; `[]:(infer_t#infer_t)list`]) THEN
  ASM_REWRITE_TAC[COUNT_ZERO; t_wfs_FEMPTY; FDOM_FEMPTY; EMPTY_SUBSET; type_eDeterm_sub_completion_empty;
                  NOT_IN_EMPTY; bind_tvar_rewrites; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:infer_t` (X_CHOOSE_THEN `st:infer_st`
    (X_CHOOSE_THEN `s1:(num,infer_t)fmap` (X_CHOOSE_THEN `cs1:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st)) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_complete)
    (ASSUME `type_p tvs tenv p t1 tenv1`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`loc:loc_err_info`; `s1:(num,infer_t)fmap`; `ienv:inf_env`;
                             `st:infer_st`; `cs1:(infer_t#infer_t)list`]) THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:infer_t` (X_CHOOSE_THEN `nb:(mlstring#infer_t)list`
    (X_CHOOSE_THEN `st2:infer_st` (X_CHOOSE_THEN `s2:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st2)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `tp:infer_t`; `nb:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_check_t)
    (ASSUME `infer_p loc ienv p st = (M_success (tp,nb),st2)`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s1 t)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st`; `infer_st_subst st`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s2 tp)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st2`; `infer_st_subst st2`;
                          `cs2:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_compat s2 (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_refl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s2 t = unconvert_t t1 /\ t_walkstar s2 tp = unconvert_t t1`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INFER1AUX_walk_unconvert THENL
     [MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `tvs:num`];
      MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `tvs:num`]] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `check_freevars tvs [] t1` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_convert_check THEN
    MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `tp:infer_t`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`tvs:num`; `infer_st_next_uvar st2`; `infer_st_subst st2`;
                `cs2:(infer_t#infer_t)list`; `s2:(num,infer_t)fmap`;
                `[t:infer_t,tp:infer_t]`] INFER1AUX_cs_core) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs3:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `t_unify (infer_st_subst st2) t tp = SOME s3` ASSUME_TAC THENL
   [UNDISCH_TAC `pure_add_constraints (infer_st_subst st2) [t,tp] s3` THEN
    REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\(n:mlstring,t). check_t tvs {} (t_walkstar si t)) nb /\
                convert_env si (nb:(mlstring#infer_t)list) = tenv1`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_simp_tenv_invC_convert THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC simp_tenv_invC_more THEN EXISTS_TAC `s2:(num,infer_t)fmap` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(MATCH_MP (CONJUNCT1 infer_p_bindings)
        (ASSUME `infer_p loc ienv p st = (M_success (tp,nb),st2)`)) THEN
      MP_TAC(MATCH_MP (CONJUNCT1 type_p_pat_bindings)
        (ASSUME `type_p tvs tenv p t1 tenv1`)) THEN
      MESON_TAC[];
      MP_TAC(MATCH_MP (CONJUNCT1 infer_p_bindings)
        (ASSUME `infer_p loc ienv p st = (M_success (tp,nb),st2)`)) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `t1 = convert_t (t_walkstar s1 t)`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `t1 = convert_t (t_walkstar s2 tp)`)) THEN
  MAP_EVERY EXISTS_TAC [`t:infer_t`; `tp:infer_t`; `nb:(mlstring#infer_t)list`;
    `st:infer_st`; `st2:infer_st`; `s3:(num,infer_t)fmap`; `cs3:(infer_t#infer_t)list`;
    `si:(num,infer_t)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN
    EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN
    EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC pure_add_constraints_wfs THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st2`; `[t:infer_t,tp:infer_t]`] THEN
    ASM_REWRITE_TAC[]]);;

let unconvert_11 = prove
 (`!t1 t2. check_freevars 0 [] t1 /\ check_freevars 0 [] t2
           ==> (unconvert_t t1 = unconvert_t t2 <=> t1 = t2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `convert_t`) THEN
  ASM_MESON_TAC[check_freevars_empty_convert_unconvert_id]);;

let infer_e_type_pe_determ = prove
 (CASE_TERM `!loc ienv p e st st' t t' tenv' s tenv ss.
     ALL_DISTINCT (MAP FST tenv') /\
     ienv_ok {} ienv /\
     env_rel_complete FEMPTY ienv tenv Empty /\
     infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
     infer_p loc ienv p st = (M_success (t',tenv'),st') /\
     t_unify (infer_st_subst st') t t' = SOME s /\
     ALL (\(n:mlstring,t). check_t 0 {} (t_walkstar s t)) tenv'
     ==> type_pe_determ tenv Empty p e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[type_pe_determ_def] THEN
  MAP_EVERY X_GEN_TAC [`t1:t`; `tenv1:(mlstring#t)list`; `t2:t`; `tenv2:(mlstring#t)list`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (pat_bindings p)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (CONJUNCT1 infer_p_bindings)
      (ASSUME `infer_p loc ienv p st = (M_success (t',tenv'),st')`)) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tx tenvx. type_p 0 tenv p tx tenvx /\ type_e tenv Empty e tx
                           ==> ?sx csx. sub_completion 0 (infer_st_next_uvar st') s csx sx /\
                                        convert_env sx tenv' = tenvx`
    (fun th -> MP_TAC(SPECL [`t1:t`; `tenv1:(mlstring#t)list`] th) THEN
               MP_TAC(SPECL [`t2:t`; `tenv2:(mlstring#t)list`] th)) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `0`; `p:pat`; `e:exp`;
                  `tx:t`; `tenvx:(mlstring#t)list`; `ss:infer_st`] infer_pe_complete) THEN
    ASM_REWRITE_TAC[bind_tvar_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `ta:infer_t` (X_CHOOSE_THEN `tpa:infer_t`
      (X_CHOOSE_THEN `nba:(mlstring#infer_t)list` (X_CHOOSE_THEN `sta:infer_st`
      (X_CHOOSE_THEN `sta':infer_st` (X_CHOOSE_THEN `sa:(num,infer_t)fmap`
      (X_CHOOSE_THEN `csa:(infer_t#infer_t)list` (X_CHOOSE_THEN `sa':(num,infer_t)fmap`
       STRIP_ASSUME_TAC)))))))) THEN
    UNDISCH_TAC `(M_success t,st):(infer_t,locs option#mlstring)exc#infer_st =
                 (M_success ta,sta)` THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `infer_p loc ienv p st = (M_success (tpa,nba),sta')` THEN
    ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `t_unify (infer_st_subst st') t t' = SOME sa` THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`sa':(num,infer_t)fmap`; `csa:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sb:(num,infer_t)fmap` (X_CHOOSE_THEN `csb:(infer_t#infer_t)list`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `sa:(num,infer_t)fmap` (X_CHOOSE_THEN `csa:(infer_t#infer_t)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_unify_wfs THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'`; `t:infer_t`; `t':infer_t`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `tenv':(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM; t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_compat s (sa:(num,infer_t)fmap) /\ t_compat s (sb:(num,infer_t)fmap)`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && INFER1AUX_ec_is_app "convert_env" (lhs(concl th)) &&
      rand(rator(lhs(concl th))) = v)))
    [`sa:(num,infer_t)fmap`; `sb:(num,infer_t)fmap`] THEN
  REWRITE_TAC[convert_env_def; MAP_EQ_f; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `t0:infer_t`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `check_t 0 {} (t_walkstar s t0)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\(n:mlstring,t). check_t 0 {} (t_walkstar s t)) tenv'` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(x:mlstring,t0:infer_t)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. t_compat s s' ==> t_walkstar s' t0 = t_walkstar s t0`
    (fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[t_compat_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `t0:infer_t` th)]) THEN
  MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]);;

let t_vars_check_t = prove
 (`(!t. ~check_t 0 {} t /\ check_t 0 s t ==> ?n'. n' IN s /\ n' IN t_vars t) /\
   (!ts x. MEM x ts ==> ~check_t 0 {} x /\ check_t 0 s x
                        ==> ?n'. n' IN s /\ n' IN t_vars x)`,
  SUBGOAL_THEN `!t. ~check_t 0 {} t /\ check_t 0 s t ==> ?n'. n' IN s /\ n' IN t_vars t`
    (fun th -> REWRITE_TAC[th] THEN MESON_TAC[th]) THEN
  MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[check_t_def; t_vars_eqn; LT; NOT_IN_EMPTY; IN_SING; UNWIND_THM2] THEN
  REWRITE_TAC[GSYM ALL_MEM; NOT_FORALL_THM; NOT_IMP; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `MEM (x:infer_t) l`) o
      check (fun th -> is_forall(concl th) &&
      (try is_imp(snd(dest_imp(snd(dest_forall(concl th))))) with Failure _ -> false))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN EXISTS_TAC `n':num` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t_vars x` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:infer_t` THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]]);;

let t_walkstar_diff = prove
 (`!s1 s2 n.
     t_wfs s1 /\ t_wfs s2 /\ ~(t_walkstar s1 (Infer_Tuvar n) = t_walkstar s2 (Infer_Tuvar n))
     ==> (!t. n IN t_vars t ==> ~(t_walkstar s1 t = t_walkstar s2 t)) /\
         (!ts x. MEM x ts ==> n IN t_vars x ==> ~(t_walkstar s1 x = t_walkstar s2 x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. n IN t_vars t ==> ~(t_walkstar s1 t = t_walkstar s2 t)`
    (fun th -> REWRITE_TAC[th] THEN MESON_TAC[th]) THEN
  MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[t_vars_eqn; NOT_IN_EMPTY; IN_SING] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `n IN UNIONS (set_of_list (MAP t_vars l))` THEN
    REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `vs:num->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:infer_t` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `t_walkstar s1 (Infer_Tapp l t) = t_walkstar s2 (Infer_Tapp l t)` THEN
    ASM_SIMP_TAC[t_walkstar_eqn1; injectivity "infer_t"; MAP_EQ_f] THEN
    DISCH_THEN(MP_TAC o SPEC `x:infer_t`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let env_rel_sound_weaken = prove
 (`!ienv tenv tenvE s.
     env_rel_sound FEMPTY ienv tenv tenvE /\ t_wfs s ==> env_rel_sound s ienv tenv tenvE`,
  REWRITE_TAC[env_rel_sound_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:(mlstring,mlstring)id`; `ts:num#infer_t`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tvs':num`; `t':t`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC tscheme_approx_weakening THEN
  MAP_EVERY EXISTS_TAC [`num_tvs tenvE`; `FEMPTY:(num,infer_t)fmap`] THEN
  ASM_REWRITE_TAC[SUBMAP_FEMPTY; LE_REFL]);;

(* unifying a fresh unification variable with a type constant *)
let INFER1AUX_t_unify_fresh_const = prove
 (`!s h tc. t_wfs s /\ ~(h IN FDOM s)
            ==> t_unify s (Infer_Tuvar h) (Infer_Tapp [] tc) =
                SOME (s |+ (h,Infer_Tapp [] tc))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[t_unify_eqn; t_walk_eqn] THEN
  SUBGOAL_THEN `t_vwalk s h = Infer_Tuvar h` SUBST1_TAC THENL
   [PURE_ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`)] THEN
    ASM_REWRITE_TAC[FLOOKUP_DEF] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[t_ext_s_check_eqn] THEN
  PURE_ONCE_REWRITE_TAC[MATCH_MP t_oc_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`)] THEN
  REWRITE_TAC[t_walk_eqn] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[EX]);;

let INFER1AUX_pac_fresh_list = prove
 (`!tc l s.
     t_wfs s /\ ALL_DISTINCT l /\ (!m. MEM m l ==> ~(m IN FDOM s))
     ==> pure_add_constraints s (MAP (\m. (Infer_Tuvar m,Infer_Tapp [] tc)) l)
           (s |++ MAP (\m. (m,Infer_Tapp [] tc)) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; pure_add_constraints_def; FUPDATE_LIST_THM; ALL_DISTINCT; MEM] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `(s:(num,infer_t)fmap) |+ (h,Infer_Tapp [] tc)` THEN
  SUBGOAL_THEN `t_unify s (Infer_Tuvar h) (Infer_Tapp [] tc) = SOME (s |+ (h,Infer_Tapp [] tc))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_t_unify_fresh_const THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN ASM_MESON_TAC[]);;

(* completing a substitution by mapping its unconstrained variables to a constant *)
let INFER1AUX_const_completion = prove
 (`!s n l tc.
     t_wfs s /\ check_s 0 (pred_set_count n) s /\
     set_of_list l = pred_set_count n DIFF FDOM s /\ ALL_DISTINCT l
     ==> sub_completion 0 n s (MAP (\m. (Infer_Tuvar m,Infer_Tapp [] tc)) l)
           (s |++ MAP (\m. (m,Infer_Tapp [] tc)) l) /\
         check_s 0 (pred_set_count n) (s |++ MAP (\m. (m,Infer_Tapp [] tc)) l) /\
         (!m. MEM m l
              ==> t_walkstar (s |++ MAP (\m. (m,Infer_Tapp [] tc)) l) (Infer_Tuvar m) =
                  Infer_Tapp [] tc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. MEM m l ==> m < n /\ ~(m IN FDOM (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[IN_DIFF; IN_COUNT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tc:num`; `l:num list`; `s:(num,infer_t)fmap`] INFER1AUX_pac_fresh_list) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `s1 = (s:(num,infer_t)fmap) |++ MAP (\m. (m,Infer_Tapp [] tc)) l` THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (s1:(num,infer_t)fmap) = FDOM (s:(num,infer_t)fmap) UNION set_of_list l` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN REWRITE_TAC[FDOM_FUPDATE_LIST; MAP_MAP_o; o_DEF; ETA_AX] THEN
    REWRITE_TAC[MAP_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `pred_set_count n SUBSET FDOM (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count n) (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_check_s THEN
    MAP_EVERY EXISTS_TAC [`s:(num,infer_t)fmap`;
                          `MAP (\m. (Infer_Tuvar m,Infer_Tapp [] tc)) l`] THEN
    ASM_REWRITE_TAC[ALL_MAP; o_DEF] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REWRITE_TAC[check_t_def; ALL; IN_COUNT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sub_completion_def] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `uv:num` THEN DISCH_TAC THEN MATCH_MP_TAC t_walkstar_check THEN
    ASM_REWRITE_TAC[UNION_EMPTY; check_t_def] THEN
    MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count n` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`s:(num,infer_t)fmap`; `MAP (\m. (Infer_Tuvar m,Infer_Tapp [] tc)) l`;
                  `s1:(num,infer_t)fmap`] pure_add_constraints_apply) THEN
    ASM_REWRITE_TAC[MAP_EQ_f; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(Infer_Tuvar m,Infer_Tapp [] tc)`) THEN
    REWRITE_TAC[MEM_MAP; FST; SND] THEN ANTS_TAC THENL
     [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[t_walkstar_eqn1; MAP]]]);;

let type_pe_determ_infer_e = prove
 (`!loc ienv p e st st' t t' new_bindings s tenv ss.
     ALL_DISTINCT (MAP FST new_bindings) /\
     env_rel_sound FEMPTY ienv tenv Empty /\
     ienv_ok {} ienv /\
     infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
     infer_p loc ienv p st = (M_success (t',new_bindings),st') /\
     t_unify (infer_st_subst st') t t' = SOME s /\
     type_pe_determ tenv Empty p e
     ==> ALL (\(n:mlstring,t). check_t 0 {} (t_walkstar s t)) new_bindings`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar (init_infer_state ss) = 0 /\
                infer_st_subst (init_infer_state ss) = FEMPTY` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `ienv_val_ok (pred_set_count 0) (inf_env_inf_v ienv) /\
                tenv_ctor_ok (inf_env_inf_c ienv) /\ tenv_abbrev_ok (inf_env_inf_t ienv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN REWRITE_TAC[ienv_ok_def; COUNT_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv /\ inf_env_inf_c ienv = type_env_c tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_sound_def]; ALL_TAC] THEN
  (* well-formedness and closedness of the inferred substitutions and types *)
  SUBGOAL_THEN `t_wfs (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `new_bindings:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `infer_st_next_uvar st <= infer_st_next_uvar st'` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_next_uvar_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st)) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st)) (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY; check_s_def; FDOM_FEMPTY; NOT_IN_EMPTY; COUNT_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st')) (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `new_bindings:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_check_t)
    (ASSUME `infer_p loc ienv p st = (M_success (t',new_bindings),st')`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more4)
      (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st)) t`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st')) s` ASSUME_TAC THENL
   [MATCH_MP_TAC t_unify_check_s THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'`; `t:infer_t`; `t':infer_t`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s t = t_walkstar s t'` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_unifier]; ALL_TAC] THEN
  (* the unconstrained variables, and two completions instantiating them differently *)
  SUBGOAL_THEN `?l. set_of_list l = pred_set_count (infer_st_next_uvar st') DIFF FDOM (s:(num,infer_t)fmap) /\
                    ALL_DISTINCT l` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `list_of_set (pred_set_count (infer_st_next_uvar st') DIFF FDOM (s:(num,infer_t)fmap))` THEN
    SIMP_TAC[SET_OF_LIST_OF_SET; FMAPAUX_ALL_DISTINCT_LIST_OF_SET; FINITE_DIFF; FINITE_COUNT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `infer_st_next_uvar st'`; `l:num list`; `Tbool_num`]
    INFER1AUX_const_completion) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s1 = (s:(num,infer_t)fmap) |++ MAP (\m. (m,Infer_Tapp [] Tbool_num)) l` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `infer_st_next_uvar st'`; `l:num list`; `Tint_num`]
    INFER1AUX_const_completion) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s2 = (s:(num,infer_t)fmap) |++ MAP (\m. (m,Infer_Tapp [] Tint_num)) l` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap) /\ t_wfs (s2:(num,infer_t)fmap) /\
                t_compat s s1 /\ t_compat s s2` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  (* the soundness of inference for any completion of s *)
  SUBGOAL_THEN
    `!sx csx. sub_completion 0 (infer_st_next_uvar st') s csx sx
              ==> type_e tenv Empty e (convert_t (t_walkstar sx t)) /\
                  type_p 0 tenv p (convert_t (t_walkstar sx t)) (convert_env sx new_bindings)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `t_wfs (sx:(num,infer_t)fmap) /\ t_compat s sx` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
      ASM_MESON_TAC[pure_add_constraints_success];
      ALL_TAC] THEN
    SUBGOAL_THEN `t_walkstar sx t = t_walkstar sx t'` ASSUME_TAC THENL
     [UNDISCH_TAC `t_compat s (sx:(num,infer_t)fmap)` THEN REWRITE_TAC[t_compat_def] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sub_completion 0 (infer_st_next_uvar st') (infer_st_subst st')
                    (CONS (t,t') csx) sx` ASSUME_TAC THENL
     [MATCH_MP_TAC sub_completion_unify2 THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP (CONJUNCT1 infer_p_constraints)
      (ASSUME `infer_p loc ienv p st = (M_success (t',new_bindings),st')`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `ts:(infer_t#infer_t)list`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 infer_e_sound) THEN
      MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `init_infer_state ss`;
                            `st:infer_st`; `APPEND ts (CONS (t:infer_t,t':infer_t) csx)`] THEN
      ASM_REWRITE_TAC[COUNT_ZERO; t_wfs_FEMPTY; num_tvs_def] THEN CONJ_TAC THENL
       [MATCH_MP_TAC env_rel_sound_weaken THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC sub_completion_add_constraints THEN
      EXISTS_TAC `infer_st_subst st'` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `sub_completion 0 (infer_st_next_uvar st') (infer_st_subst st')
                     (CONS (t,t') csx) sx` THEN
      REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `t_walkstar sx t = t_walkstar sx t'`)) THEN
      MATCH_MP_TAC(CONJUNCT1 infer_p_sound) THEN
      MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `st:infer_st`; `st':infer_st`;
                            `CONS (t:infer_t,t':infer_t) csx`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the two typings, and determinism *)
  SUBGOAL_THEN `convert_env s1 (new_bindings:(mlstring#infer_t)list) = convert_env s2 new_bindings` ASSUME_TAC THENL
   [FIRST_ASSUM(fun ih ->
      if is_forall(concl ih) &&
         (try fst(dest_var(fst(dest_forall(concl ih)))) = "sx" with Failure _ -> false)
      then MAP_EVERY (fun v -> FIRST_ASSUM(fun sc ->
             if INFER1AUX_ec_is_app "sub_completion" (concl sc) && rand(concl sc) = v &&
                rand(rator(rator(concl sc))) = `s:(num,infer_t)fmap`
             then MP_TAC(MATCH_MP ih sc) else failwith ""))
             [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`]
      else failwith "") THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[type_pe_determ_def] o
      check (fun th -> INFER1AUX_ec_is_app "type_pe_determ" (concl th))) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`convert_t (t_walkstar s1 t)`; `convert_t (t_walkstar s2 t)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `tt:infer_t`] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_CASES_TAC `check_t 0 {} (t_walkstar s tt)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (pred_set_count (infer_st_next_uvar st')) t)
                     new_bindings` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(x:mlstring,tt:infer_t)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) (t_walkstar s tt)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_walkstar_check THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt`)) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `t_walkstar s tt` (CONJUNCT1 (INST [`pred_set_count (infer_st_next_uvar st')`,`s:num->bool`]
    t_vars_check_t))) THEN
  ASM_REWRITE_TAC[IN_COUNT] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `MEM (n':num) l` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[IN_DIFF; IN_COUNT] THEN
    MATCH_MP_TAC(MATCH_MP t_walkstar_vars_notin (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
    EXISTS_TAC `tt:infer_t` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`; `n':num`] t_walkstar_diff) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[injectivity "infer_t"; typeSystem_Tbool_num_def; typeSystem_Tint_num_def] THEN
    ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `t_walkstar s tt` o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!sx. t_compat s sx ==> t_walkstar sx (t_walkstar s tt) = t_walkstar sx tt`
    (fun th -> ASM_SIMP_TAC[th]) THENL
   [SIMP_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `!sx csx. sub_completion 0 (infer_st_next_uvar st') s csx sx /\
                         check_s 0 (pred_set_count (infer_st_next_uvar st')) sx
                         ==> check_t 0 {} (t_walkstar sx tt)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN
    MATCH_MP_TAC t_walkstar_check THEN REWRITE_TAC[UNION_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[pure_add_constraints_wfs];
      MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt`)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 {} (t_walkstar s1 tt) /\ check_t 0 {} (t_walkstar s2 tt)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convert_t (t_walkstar s1 tt) = convert_t (t_walkstar s2 tt)` MP_TAC THENL
   [UNDISCH_TAC `convert_env s1 (new_bindings:(mlstring#infer_t)list) = convert_env s2 new_bindings` THEN
    REWRITE_TAC[convert_env_def; MAP_EQ_f] THEN
    DISCH_THEN(MP_TAC o SPEC `(x:mlstring,tt:infer_t)`) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `unconvert_t`) THEN
  MP_TAC(SPECL [`t_walkstar s1 tt`; `0`] check_t_empty_unconvert_convert_id) THEN
  MP_TAC(SPECL [`t_walkstar s2 tt`; `0`] check_t_empty_unconvert_convert_id) THEN
  ASM_SIMP_TAC[]);;

(* env_rel_complete is preserved by binding type variables at the top *)
let INFER1AUX_erc_bind_tvar = prove
 (`!s ienv tenv tvs.
     env_rel_complete s ienv tenv Empty /\ t_wfs s
     ==> env_rel_complete s ienv tenv (bind_tvar tvs Empty)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_rel_complete_def; bind_tvar_rewrites] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `!x. lookup_var x (bind_tvar tvs Empty) tenv = lookup_var x Empty tenv`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN
    MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[bind_tvar_rewrites; tveLookup_def];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `tvs':num`; `t:t`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:(mlstring,mlstring)id`; `tvs':num`; `t:t`]) THEN
  ASM_REWRITE_TAC[num_tvs_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `tvs'':num` (X_CHOOSE_THEN `t':infer_t` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`tvs'':num`; `t':infer_t`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC tscheme_approx_weakening THEN
  MAP_EVERY EXISTS_TAC [`0`; `s:(num,infer_t)fmap`] THEN
  ASM_REWRITE_TAC[SUBMAP_REFL; LE_0]);;

(* ALL over a ZIP of two lists *)
let INFER1AUX_ALL_ZIP = prove
 (`!(P:A->bool) (Q:B->bool) l1 l2.
     LENGTH l1 = LENGTH l2 /\ ALL P l1 /\ ALL Q l2 ==> ALL (\(x,y). P x /\ Q y) (ZIP l1 l2)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ZIP; ALL; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let infer_funs_complete = prove
 (CASE_TERM `!loc ienv tenv tvs funs bindings ss.
     ienv_ok {} ienv /\ tenv_ok tenv /\ env_rel_complete FEMPTY ienv tenv Empty /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings
     ==> ?funs_ts st st' constr s.
           infer_funs loc
             (inf_env_inf_v_fupd
                (K (nsAppend
                      (alist_to_ns
                         (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                            (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                      (inf_env_inf_v ienv))) ienv)
             funs
             (infer_st_next_uvar_fupd
                (K (infer_st_next_uvar (init_infer_state ss) + LENGTH funs))
                (init_infer_state ss)) =
             (M_success funs_ts,st) /\
           infer_st_next_uvar st = infer_st_next_uvar st' /\
           infer_st_next_id st = infer_st_next_id st' /\
           pure_add_constraints (infer_st_subst st)
             (ZIP (MAP (\n. Infer_Tuvar (infer_st_next_uvar (init_infer_state ss) + n))
                       (COUNT_LIST (LENGTH funs))) funs_ts)
             (infer_st_subst st') /\
           check_s 0 (pred_set_count (infer_st_next_uvar st')) (infer_st_subst st') /\
           sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st') constr s /\
           FDOM s = pred_set_count (infer_st_next_uvar st') /\
           MAP SND bindings = MAP (convert_t o t_walkstar s) funs_ts`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar (init_infer_state ss) = 0 /\
                infer_st_subst (init_infer_state ss) = FEMPTY` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[num_tvs_bind_var_list; bind_tvar_rewrites; ADD_CLAUSES] o
    MATCH_MP INFER1AUX_type_funs_facts o
    check (fun th -> INFER1AUX_ec_is_app "type_funs" (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_tvs_def]) THEN
  SUBGOAL_THEN `LENGTH (bindings:(mlstring#t)list) = LENGTH (funs:(mlstring#mlstring#exp)list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:mlstring list->num` o check (fun th ->
      concl th = `MAP FST (bindings:(mlstring#t)list) = MAP FST (funs:(mlstring#mlstring#exp)list)`)) THEN
    REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`init_infer_state ss`; `[]:(infer_t#infer_t)list`; `FEMPTY:(num,infer_t)fmap`;
                 `MAP SND (bindings:(mlstring#t)list)`; `tvs:num`] extend_multi_props) THEN
  ASM_REWRITE_TAC[t_wfs_FEMPTY; pure_add_constraints_def; FDOM_FEMPTY; NOT_IN_EMPTY;
                  COUNT_ZERO] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; APPEND; LENGTH_MAP] THEN REWRITE_TAC[MAP_ID] THEN
  STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
  ABBREV_TAC `s0 = (FEMPTY:(num,infer_t)fmap) |++
                   ZIP (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))
                       (MAP unconvert_t (MAP SND (bindings:(mlstring#t)list)))` THEN
  ABBREV_TAC `nc = ZIP (MAP Infer_Tuvar (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))
                       (MAP unconvert_t (MAP SND (bindings:(mlstring#t)list)))` THEN
  ABBREV_TAC `us = MAP Infer_Tuvar (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))` THEN
  SUBGOAL_THEN `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`
    ASSUME_TAC THENL
   [EXPAND_TAC "us" THEN REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]; ALL_TAC] THEN
  ASM_SIMP_TAC[INFER1AUX_MAP2_funs] THEN
  SUBGOAL_THEN `simp_tenv_invC s0 tvs
                  (ZIP (MAP FST (funs:(mlstring#mlstring#exp)list)) us) bindings`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_simp_tenv_invC_funs THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `EL k (us:infer_t list) = Infer_Tuvar k` SUBST1_TAC THENL
     [EXPAND_TAC "us" THEN ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s0:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM
    `ienv_ok (pred_set_count (LENGTH (funs:(mlstring#mlstring#exp)list)))
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t)))
                                  (ZIP (MAP FST funs) us)))
                (inf_env_inf_v ienv))) ienv) /\
     env_rel_complete s0
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t)))
                                  (ZIP (MAP FST funs) us)))
                (inf_env_inf_v ienv))) ienv)
       tenv (bind_var_list 0 bindings (bind_tvar tvs Empty))`) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o check (fun th ->
        concl th = `ienv_ok {} ienv`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_pes THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN EXPAND_TAC "us" THEN
        REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; MEM_COUNT_LIST] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[check_t_def; IN_COUNT];
        MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN EXISTS_TAC `0` THEN
        ASM_REWRITE_TAC[COUNT_ZERO; LE_0]];
      MATCH_MP_TAC INFER1AUX_env_rel_complete_pat THEN
      MAP_EVERY EXISTS_TAC [`FEMPTY:(num,infer_t)fmap`; `s0:(num,infer_t)fmap`] THEN
      ASM_SIMP_TAC[SUBMAP_t_compat; t_compat_refl; FDOM_FEMPTY; EMPTY_SUBSET;
                   bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
      MATCH_MP_TAC INFER1AUX_erc_bind_tvar THEN ASM_REWRITE_TAC[t_wfs_FEMPTY]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT2(CONJUNCT2 infer_e_complete))
    (ASSUME `type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings`)) THEN
  REWRITE_TAC[num_tvs_bind_var_list; bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
  INFER1AUX_LETREC_ENV_TAC (fun ie ->
    DISCH_THEN(MP_TAC o SPECL [`loc:loc_err_info`; `s0:(num,infer_t)fmap`; ie;
      `infer_st_next_uvar_fupd (K (LENGTH (funs:(mlstring#mlstring#exp)list)))
         (init_infer_state ss)`; `nc:(infer_t#infer_t)list`])) THEN
  REWRITE_TAC[infer_st_rewrs] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[sub_completion_def; t_wfs_FEMPTY; FDOM_FEMPTY; EMPTY_SUBSET; SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `env1:infer_t list` (X_CHOOSE_THEN `st2:infer_st`
    (X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `cs3:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `MAP SND (bindings:(mlstring#t)list) = MAP (convert_t o t_walkstar s3) env1`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] o
    check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th) &&
                     free_in `funs:(mlstring#mlstring#exp)list` (concl th))) THEN
  INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_wfs)))) THEN
  ASM_REWRITE_TAC[infer_st_rewrs; t_wfs_FEMPTY] THEN DISCH_TAC THEN
  INFER1AUX_IFN_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_uvar_mono))) THEN
  REWRITE_TAC[infer_st_rewrs] THEN DISCH_TAC THEN
  INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_t)))) THEN
  ASM_REWRITE_TAC[infer_st_rewrs; inf_env_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st2)) (infer_st_subst st2)` ASSUME_TAC THENL
   [INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_s)))) THEN
    ASM_REWRITE_TAC[infer_st_rewrs; t_wfs_FEMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[check_s_def; FDOM_FEMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t tvs {}) (MAP (t_walkstar s3) env1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground_list THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st2`; `infer_st_subst st2`;
                          `cs3:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (env1:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:t list->num` o check (fun th ->
      concl th = `MAP (convert_t o t_walkstar s3) env1 = MAP SND (bindings:(mlstring#t)list)`)) THEN
    ASM_REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar s3) env1 = MAP unconvert_t (MAP SND (bindings:(mlstring#t)list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `MAP (convert_t o t_walkstar s3) env1 =
                            MAP SND (bindings:(mlstring#t)list)`); MAP_o] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_unconvert_convert_list THEN
    EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar s3) us = MAP unconvert_t (MAP SND (bindings:(mlstring#t)list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k < LENGTH (bindings:(mlstring#t)list) /\ k < LENGTH (us:infer_t list)`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP] THEN
    SUBGOAL_THEN `EL k (us:infer_t list) = Infer_Tuvar k` SUBST1_TAC THENL
     [EXPAND_TAC "us" THEN ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `tvs:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        is_forall(concl th) &&
        (try INFER1AUX_ec_is_app "EL" (rhs(snd(dest_imp(snd(dest_forall(concl th))))))
         with Failure _ -> false))) THEN
      ASM_SIMP_TAC[EL_MAP; LENGTH_MAP];
      MATCH_MP_TAC check_freevars_to_check_t THEN
      UNDISCH_TAC `ALL (check_freevars tvs []) (MAP SND (bindings:(mlstring#t)list))` THEN
      REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
      ASM_SIMP_TAC[EL_MAP]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tvs:num`; `infer_st_next_uvar st2`; `infer_st_subst st2`;
                `cs3:(infer_t#infer_t)list`; `s3:(num,infer_t)fmap`;
                `ZIP (us:infer_t list) (env1:infer_t list)`] INFER1AUX_cs_core) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_ALL_ZIP_MAP_EQ THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs4:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`env1:infer_t list`; `st2:infer_st`;
    `infer_st_subst_fupd (K s4) st2`; `cs4:(infer_t#infer_t)list`; `si:(num,infer_t)fmap`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs; infer_st_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_check_s THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st2`; `ZIP (us:infer_t list) (env1:infer_t list)`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`check_t 0 (pred_set_count (infer_st_next_uvar st2))`;
                   `check_t 0 (pred_set_count (infer_st_next_uvar st2))`;
                   `us:infer_t list`; `env1:infer_t list`] INFER1AUX_ALL_ZIP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "us" THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; MEM_COUNT_LIST] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ASM_ARITH_TAC;
      DISCH_THEN ACCEPT_TAC];
    REWRITE_TAC[MAP_EQ_f; o_THM] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `MAP (convert_t o t_walkstar s3) env1 = MAP SND (bindings:(mlstring#t)list)`)) THEN
    REWRITE_TAC[MAP_EQ_f; o_THM] THEN ASM_REWRITE_TAC[]]);;
