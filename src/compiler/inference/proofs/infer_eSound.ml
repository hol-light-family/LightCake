(* ========================================================================= *)
(* infer_eSound: port of HOL4 compiler/inference/proofs/infer_eSoundScript.sml *)
(* (CakeML v3479).  Soundness of the type inferencer at the expression      *)
(* level.                                                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Records: st.next_uvar is infer_st_next_uvar st, ienv.inf_v is          *)
(*   inf_env_inf_v ienv, tenv.c is type_env_c tenv.                          *)
(* - HOL4 EVERY is ALL, LIST_REL is ALL2, ZIP (l1,l2) is ZIP l1 l2.          *)
(* - The free variables of a HOL4 statement are universally quantified.      *)
(* - HOL4 [local] theorems are kept (they are ordinary theorems here).       *)
(* - Helper lemmas that are not HOL4 theorems are INFER1AUX_.                *)
(* ------------------------------------------------------------------------- *)
(* ---------- sub_completion ---------- *)

let sub_completion_unify = prove
 (`!st t1 t2 s1 n ts s2.
     t_unify (infer_st_subst st) t1 t2 = SOME s1 /\
     sub_completion n (infer_st_next_uvar st + 1) s1 ts s2
     ==> sub_completion n (infer_st_next_uvar st) (infer_st_subst st) (CONS (t1,t2) ts) s2`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_def; count_add1] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]; ASM_MESON_TAC[]]);;

let sub_completion_unify2 = prove
 (`!t1 t2 s1 ts s2 n s3 next_uvar.
     t_unify s1 t1 t2 = SOME s2 /\ sub_completion n next_uvar s2 ts s3
     ==> sub_completion n next_uvar s1 (CONS (t1,t2) ts) s3`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_def] THEN MESON_TAC[]);;

let sub_completion_infer = prove
 (`!l ienv e st1 t st2 n ts2 s.
     infer_e l ienv e st1 = (M_success t,st2) /\
     sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2 s
     ==> ?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst st1)
                 (APPEND ts1 ts2) s`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_append] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_e_constraints)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_e_next_uvar_mono)) THEN
  EXISTS_TAC `ts:(infer_t#infer_t)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `infer_st_subst st2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `count (infer_st_next_uvar st2)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;

let sub_completion_add_constraints = prove
 (`!s1 ts1 s2 n next_uvar s3 ts2.
     pure_add_constraints s1 ts1 s2 /\ sub_completion n next_uvar s2 ts2 s3
     ==> sub_completion n next_uvar s1 (APPEND ts1 ts2) s3`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_append] THEN MESON_TAC[]);;

let sub_completion_more_vars = prove
 (`!m n1 n2 s1 ts s2. sub_completion m (n1 + n2) s1 ts s2 ==> sub_completion m n1 s1 ts s2`,
  REWRITE_TAC[sub_completion_def; SUBSET; IN_COUNT] THEN
  MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + n2:num`]);;

let sub_completion_infer_es = prove
 (`!l cenv es st1 t st2 n ts2 s.
     infer_es l cenv es st1 = (M_success t,st2) /\
     sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2 s
     ==> ?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst st1)
                 (APPEND ts1 ts2) s`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_append] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 (CONJUNCT2 infer_e_constraints))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT1 (CONJUNCT2 infer_e_next_uvar_mono))) THEN
  EXISTS_TAC `ts:(infer_t#infer_t)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `infer_st_subst st2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `count (infer_st_next_uvar st2)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;

let INFER1AUX_sub_completion_back = prove
 (`!st1 st2 n ts2 s.
     (?ts. pure_add_constraints (infer_st_subst st1) ts (infer_st_subst st2)) /\
     infer_st_next_uvar st1 <= infer_st_next_uvar st2 /\
     sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2 s
     ==> ?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst st1)
                 (APPEND ts1 ts2) s`,
  REWRITE_TAC[sub_completion_def; pure_add_constraints_append] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `ts:(infer_t#infer_t)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `infer_st_subst st2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `count (infer_st_next_uvar st2)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;

let sub_completion_infer_p = prove
 (`(!l cenv p st t env st' tvs extra_constraints s.
      infer_p l cenv p st = (M_success (t,env),st') /\
      sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st') extra_constraints s
      ==> ?ts. sub_completion tvs (infer_st_next_uvar st) (infer_st_subst st)
                 (APPEND ts extra_constraints) s) /\
   (!l cenv ps st ts env st' tvs extra_constraints s.
      infer_ps l cenv ps st = (M_success (ts,env),st') /\
      sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st') extra_constraints s
      ==> ?ts. sub_completion tvs (infer_st_next_uvar st) (infer_st_subst st)
                 (APPEND ts extra_constraints) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFER1AUX_sub_completion_back THEN
  EXISTS_TAC `st':infer_st` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[infer_p_constraints; infer_p_next_uvar_mono]);;

let sub_completion_infer_pes = prove
 (`!l ienv pes t1 t2 st1 (t:A) st2 n ts2 s.
     infer_pes l ienv pes t1 t2 st1 = (M_success one,st2) /\
     sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2 s
     ==> ?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst st1)
                 (APPEND ts1 ts2) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFER1AUX_sub_completion_back THEN
  EXISTS_TAC `st2:infer_st` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[infer_e_constraints; infer_e_next_uvar_mono]);;

let sub_completion_infer_funs = prove
 (`!l ienv funs st1 t st2 n ts2 s.
     infer_funs l ienv funs st1 = (M_success t,st2) /\
     sub_completion n (infer_st_next_uvar st2) (infer_st_subst st2) ts2 s
     ==> ?ts1. sub_completion n (infer_st_next_uvar st1) (infer_st_subst st1)
                 (APPEND ts1 ts2) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFER1AUX_sub_completion_back THEN
  EXISTS_TAC `st2:infer_st` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[infer_e_constraints; infer_e_next_uvar_mono]);;

let sub_completion_apply = prove
 (`!n uvars s1 ts s2 t1 t2.
     t_wfs s1 /\ t_walkstar s1 t1 = t_walkstar s1 t2 /\ sub_completion n uvars s1 ts s2
     ==> t_walkstar s2 t1 = t_walkstar s2 t2`,
  REWRITE_TAC[sub_completion_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC pure_add_constraints_append2 THEN
  MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `ts:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[]);;

let sub_completion_apply_list = prove
 (`!n uvars s1 ts s2 ts1 ts2.
     t_wfs s1 /\ MAP (t_walkstar s1) ts1 = MAP (t_walkstar s1) ts2 /\
     sub_completion n uvars s1 ts s2
     ==> MAP (t_walkstar s2) ts1 = MAP (t_walkstar s2) ts2`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[sub_completion_apply]);;

let sub_completion_check = prove
 (`!tvs m s uvar s' extra_constraints.
     sub_completion m (uvar + tvs) s' extra_constraints s
     ==> ALL (\n. check_freevars m [] (convert_t (t_walkstar s (Infer_Tuvar (uvar + n)))))
             (COUNT_LIST tvs)`,
  REWRITE_TAC[sub_completion_def; every_count_list; SUBSET; IN_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC check_t_to_check_freevars THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ---------- Soundness ---------- *)

(* apply the first rule of a conjunction of inductive rules that fits the goal *)
let INFER1AUX_ES_RULE_TAC rules : tactic =
  FIRST (map (fun th g -> try MATCH_MP_TAC th g with Failure _ -> MATCH_ACCEPT_TAC th g)
             (CONJUNCTS rules));;

(* the type abbreviations of typeSystem *)
let INFER1AUX_ES_tydefs =
  [typeSystem_Tarray_def; typeSystem_Tbool_def; typeSystem_Tchar_def; typeSystem_Texn_def;
   typeSystem_Tfn_def; typeSystem_Tint_def; typeSystem_Tlist_def; typeSystem_Tref_def;
   typeSystem_Tstring_def; typeSystem_Ttup_def; typeSystem_Tvector_def;
   typeSystem_Tword64_def; typeSystem_Tword8_def; typeSystem_Tword8array_def;
   typeSystem_Tdouble_def];;

let INFER1AUX_tannot_type = prove
 (`!s s1 t' tenvT t ec n uvars.
     t_wfs s1 /\
     t_walkstar s1 t' = t_walkstar s1 (infer_type_subst [] (type_name_subst tenvT t)) /\
     sub_completion n uvars s1 ec s /\
     tenv_abbrev_ok tenvT /\ check_freevars_ast [] t /\ check_type_names tenvT t
     ==> convert_t (t_walkstar s t') = type_name_subst tenvT t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_walkstar s t' = t_walkstar s (infer_type_subst [] (type_name_subst tenvT t))`
    SUBST1_TAC THENL [ASM_MESON_TAC[sub_completion_apply]; ALL_TAC] THEN
  SUBGOAL_THEN `check_freevars 0 [] (type_name_subst tenvT t)` ASSUME_TAC THENL
   [MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs s` ASSUME_TAC THENL [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_type_subst_empty_check)) THEN
  SUBGOAL_THEN `t_walkstar s (infer_type_subst [] (type_name_subst tenvT t)) =
                infer_type_subst [] (type_name_subst tenvT t)` SUBST1_TAC THENL
   [MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 (SPEC `0` infer_type_subst_nil)) th]) THEN
  MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[]);;

(* t_wfs of the completing substitution, from the sub_completion assumption *)
let INFER1AUX_SC_WFS_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if (try fst(dest_const(fst(strip_comb c))) = "sub_completion" with Failure _ -> false)
    then
      let s1 = el 2 (snd(strip_comb c)) in
      SUBGOAL_THEN (mk_comb(`t_wfs:(num,infer_t)fmap->bool`, s1))
        (fun wth -> ASSUME_TAC(MATCH_MP sub_completion_wfs (CONJ wth th))) THENL
       [ASM_REWRITE_TAC[infer_st_rewrs]; ALL_TAC]
    else failwith "INFER1AUX_SC_WFS_TAC");;

let INFER1AUX_IPS_PVAR_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN INFER1AUX_SC_WFS_TAC THEN
  REWRITE_TAC[convert_env_def; MAP] THEN CASE_REWRITE_TAC[] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN
  MATCH_MP_TAC check_t_to_check_freevars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs; sub_completion_def; SUBSET; IN_COUNT]) THEN
  ASM_MESON_TAC[ARITH_RULE `n < n + 1`];;

let INFER1AUX_IPS_LIT_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN INFER1AUX_SC_WFS_TAC THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def; convert_env_def; MAP] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules);;
let INFER1AUX_SC_WFS_TAC_WITH thl =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if (try fst(dest_const(fst(strip_comb c))) = "sub_completion" with Failure _ -> false)
    then
      let s1 = el 2 (snd(strip_comb c)) in
      SUBGOAL_THEN (mk_comb(`t_wfs:(num,infer_t)fmap->bool`, s1))
        (fun wth -> ASSUME_TAC(MATCH_MP sub_completion_wfs (CONJ wth th))) THENL
       [ASM_REWRITE_TAC[infer_st_rewrs] THEN ASM_MESON_TAC thl; ALL_TAC]
    else failwith "INFER1AUX_SC_WFS_TAC_WITH");;

let INFER1AUX_IPS_PREF_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN INFER1AUX_SC_WFS_TAC_WITH [infer_p_wfs] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def; MAP] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];;

let INFER1AUX_IPS_PAS_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN INFER1AUX_SC_WFS_TAC_WITH [infer_p_wfs] THEN
  REWRITE_TAC[convert_env_def; MAP_APPEND; MAP] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM convert_env_def] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];;

let INFER1AUX_IPS_PTANNOT_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs]) THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st''')` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s':(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `convert_t (t_walkstar s t') = type_name_subst (type_env_t tenv) t`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_tannot_type THEN
    MAP_EVERY EXISTS_TAC [`s':(num,infer_t)fmap`; `extra_constraints:(infer_t#infer_t)list`;
                          `tvs:num`; `infer_st_next_uvar st'''`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inf_env_inf_t ienv = type_env_t tenv`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[t_unify_apply];
    ALL_TAC] THEN
  SUBGOAL_THEN `type_p tvs tenv p (convert_t (t_walkstar s t')) (convert_env s env)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`st:infer_st`; `st''':infer_st`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[sub_completion_unify2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `inf_env_inf_t ienv = type_env_t tenv`]) THEN
  ASM_REWRITE_TAC[];;

let INFER1AUX_IPS_NIL_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MAP; convert_env_def] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules);;

let INFER1AUX_IPS_CONS_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  REWRITE_TAC[MAP; o_THM; convert_env_def; MAP_APPEND] THEN REWRITE_TAC[GSYM convert_env_def] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(
       snd(dest_imp(snd(strip_forall(concl th)))))))) = "type_p" with Failure _ -> false)) THEN
    MAP_EVERY EXISTS_TAC [`st:infer_st`; `st'':infer_st`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`l:loc_err_info`; `ienv:inf_env`; `ps:pat list`; `st'':infer_st`;
                  `p1':infer_t list`; `p2':(mlstring#infer_t)list`; `st':infer_st`; `tvs:num`;
                  `extra_constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`]
                 (CONJUNCT2 sub_completion_infer_p)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`st'':infer_st`; `st':infer_st`;
                          `extra_constraints:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[infer_p_wfs]];;

let INFER1AUX_IPS_PCON_NONE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"; injectivity "option"]) THEN
  INFER1AUX_SC_WFS_TAC_WITH [infer_p_wfs] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def; MAP_MAP_o] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];;

let INFER1AUX_IPS_PCON_SOME_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs; distinctness "option"; injectivity "option";
                              LENGTH_MAP; LENGTH_COUNT_LIST; FORALL_UNWIND_THM1;
                              FORALL_UNWIND_THM2]) THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st''')` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def] THEN
  INFER1AUX_ES_RULE_TAC (REWRITE_RULE INFER1AUX_ES_tydefs type_p_rules) THEN
  MAP_EVERY EXISTS_TAC [`p1':t list`; `p1:mlstring list`] THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST] THEN
  SUBGOAL_THEN `nsLookup (type_env_c tenv) cn = SOME (p1,p1',p2)` (fun th -> REWRITE_TAC[th])
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL_MAP; o_DEF] THEN
    MATCH_MP_TAC sub_completion_check THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'`; `extra_constraints:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar (infer_st_subst st')) p1'' =
                MAP (t_walkstar (infer_st_subst st'))
                  (MAP (infer_type_subst (ZIP p1
                     (MAP (\n. Infer_Tuvar (infer_st_next_uvar st''' + n))
                          (COUNT_LIST (LENGTH p1))))) p1')` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`infer_st_subst st'''`;
      `ZIP (p1'':infer_t list) (MAP (infer_type_subst (ZIP p1
         (MAP (\n. Infer_Tuvar (infer_st_next_uvar st''' + n)) (COUNT_LIST (LENGTH p1))))) p1')`;
      `infer_st_subst st'`] pure_add_constraints_apply) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (p1'':infer_t list) =
                  LENGTH (MAP (infer_type_subst (ZIP p1
                    (MAP (\n. Infer_Tuvar (infer_st_next_uvar st''' + n))
                         (COUNT_LIST (LENGTH p1))))) p1')` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
    ASM_SIMP_TAC[GEN_ALL MAP_ZIP; LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar s) p1'' =
                MAP (t_walkstar s)
                  (MAP (infer_type_subst (ZIP p1
                     (MAP (\n. Infer_Tuvar (infer_st_next_uvar st''' + n))
                          (COUNT_LIST (LENGTH p1))))) p1')` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_apply_list THEN
    MAP_EVERY EXISTS_TAC [`tvs:num`; `infer_st_next_uvar st'`; `infer_st_subst st'`;
                          `extra_constraints:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_freevars 0 p1) (p1':t list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[tenv_ctor_ok_lookup]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (convert_t o t_walkstar s) p1'' =
    MAP (type_subst (alist_to_fmap (ZIP p1 (MAP convert_t (MAP (t_walkstar s)
      (MAP (\n. Infer_Tuvar (infer_st_next_uvar st''' + n)) (COUNT_LIST (LENGTH p1))))))))
      p1'` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[GSYM MAP_MAP_o] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CONJUNCT2 subst_infer_subst_swap] THEN
    REWRITE_TAC[MAP_MAP_o; o_DEF] THEN
    MP_TAC(ISPECL [`p1':t list`; `p1:mlstring list`;
       `MAP (\n. t_walkstar s (Infer_Tuvar (infer_st_next_uvar st''' + n)))
            (COUNT_LIST (LENGTH (p1:mlstring list)))`] (CONJUNCT2 convert_t_subst)) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; MAP_MAP_o; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(
       snd(dest_imp(snd(strip_forall(concl th)))))))) = "type_ps" with Failure _ -> false)) THEN
  MAP_EVERY EXISTS_TAC [`st'':infer_st`; `st''':infer_st`] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `APPEND (ZIP (p1'':infer_t list) (MAP (infer_type_subst (ZIP p1
         (MAP (\n. Infer_Tuvar (infer_st_next_uvar st''' + n)) (COUNT_LIST (LENGTH p1))))) p1'))
         (extra_constraints:(infer_t#infer_t)list)` THEN
  MATCH_MP_TAC sub_completion_more_vars THEN EXISTS_TAC `LENGTH (p1:mlstring list)` THEN
  MATCH_MP_TAC sub_completion_add_constraints THEN
  EXISTS_TAC `infer_st_subst st'` THEN ASM_REWRITE_TAC[];;
let infer_p_sound = prove
 (`(!l ienv p st t tenv env st' tvs extra_constraints s.
      infer_p l ienv p st = (M_success (t,env),st') /\
      t_wfs (infer_st_subst st) /\
      tenv_ctor_ok (type_env_c tenv) /\
      inf_env_inf_c ienv = type_env_c tenv /\
      inf_env_inf_t ienv = type_env_t tenv /\
      tenv_abbrev_ok (type_env_t tenv) /\
      sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st') extra_constraints s
      ==> type_p tvs tenv p (convert_t (t_walkstar s t)) (convert_env s env)) /\
   (!l ienv ps st ts tenv env st' tvs extra_constraints s.
      infer_ps l ienv ps st = (M_success (ts,env),st') /\
      t_wfs (infer_st_subst st) /\
      tenv_ctor_ok (type_env_c tenv) /\
      inf_env_inf_c ienv = type_env_c tenv /\
      inf_env_inf_t ienv = type_env_t tenv /\
      tenv_abbrev_ok (type_env_t tenv) /\
      sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st') extra_constraints s
      ==> type_ps tvs tenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env))`,
  MATCH_MP_TAC infer_p_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try mem (fst(dest_const(fst(strip_comb(lhs(concl th)))))) ["infer_p"; "infer_ps"]
      with Failure _ -> false)) THEN
  REWRITE_TAC[infer_p_def; success_eqns; EXISTS_PAIR_THM; pair_CASE; PAIR_EQ] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[success_eqns; EXISTS_PAIR_THM; pair_CASE; PAIR_EQ] THENL
   [INFER1AUX_IPS_PVAR_TAC; INFER1AUX_IPS_PVAR_TAC; INFER1AUX_IPS_LIT_TAC;
    INFER1AUX_IPS_LIT_TAC; INFER1AUX_IPS_LIT_TAC; INFER1AUX_IPS_LIT_TAC;
    INFER1AUX_IPS_LIT_TAC;
    STRIP_TAC THEN RVEQ_TAC THENL [INFER1AUX_IPS_PCON_NONE_TAC; INFER1AUX_IPS_PCON_SOME_TAC];
    INFER1AUX_IPS_PREF_TAC; INFER1AUX_IPS_PAS_TAC; INFER1AUX_IPS_PTANNOT_TAC;
    INFER1AUX_IPS_NIL_TAC; INFER1AUX_IPS_CONS_TAC]);;

let INFER1AUX_letrec_lemma_u = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) funs_ts s u.
     MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (u + n)))) (COUNT_LIST (LENGTH funs)) =
     MAP (\t. convert_t (t_walkstar s t)) funs_ts
     ==> MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
              (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (u + n))))
                   (COUNT_LIST (LENGTH funs))) =
         MAP2 (\xyz t. match xyz with (x,y,z) -> (x,convert_t (t_walkstar s t))) funs funs_ts`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `funs_ts:infer_t list` list_CASES) THEN
  REWRITE_TAC[LENGTH; COUNT_LIST_def; MAP; MAP2; NOT_CONS_NIL; CONS_11] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':infer_t list`; `s:(num,infer_t)fmap`; `u + 1`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o; o_DEF]) THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; ARITH_RULE `(u + 1) + n = u + SUC n`] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN ACCEPT_TAC);;

let letrec_lemma = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) funs_ts s st.
     MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (infer_st_next_uvar st + n))))
         (COUNT_LIST (LENGTH funs)) =
     MAP (\t. convert_t (t_walkstar s t)) funs_ts
     ==> MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
              (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (infer_st_next_uvar st + n))))
                   (COUNT_LIST (LENGTH funs))) =
         MAP2 (\xyz t. match xyz with (x,y,z) -> (x,convert_t (t_walkstar s t))) funs funs_ts`,
  REWRITE_TAC[INFER1AUX_letrec_lemma_u]);;

let map_zip_lem = prove
 (`!s (funs:(mlstring#mlstring#exp)list) ts.
     LENGTH funs = LENGTH ts
     ==> MAP (\x. FST ((\((x',y,z),t). (x',convert_t (t_walkstar s t))) x)) (ZIP funs ts) =
         MAP FST funs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ts:infer_t list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; CONS_11] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let word_tc_cases = prove
 (`!wz. (word_tc wz = Tword8_num <=> wz = W8) /\ (word_tc wz = Tword64_num <=> wz = W64)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `wz:word_size` (cases "word_size")) THEN
  REWRITE_TAC[word_tc_def; distinctness "word_size"] THEN
  REWRITE_TAC[typeSystem_Tword8_num_def; typeSystem_Tword64_num_def] THEN ARITH_TAC);;

let constrain_op_sub_completion = prove
 (`!tenv st extra_constraints s l op ts st' t.
     sub_completion (num_tvs tenv) (infer_st_next_uvar st) (infer_st_subst st)
       extra_constraints s /\
     constrain_op l op ts st' = (M_success t,st)
     ==> ?c. sub_completion (num_tvs tenv) (infer_st_next_uvar st') (infer_st_subst st') c s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TYSYS2AUX_constrain_op_state) THEN
  MP_TAC(ISPECL [`st':infer_st`; `st:infer_st`; `num_tvs tenv`;
                 `extra_constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`]
                INFER1AUX_sub_completion_back) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

(* convert_t of the inferencer's type of a primitive type *)
let INFER1AUX_convert_t_num_of = prove
 (`!ty. convert_t (Infer_Tapp [] (t_num_of ty)) = t_of ty`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC([convert_t_def; MAP; t_num_of_def; t_of_def] @ INFER1AUX_ES_tydefs));;

(* HOL4's binop_tac for constrain_op_sound: the unifications of the        *)
(* constraint chain are pulled back to the start substitution              *)
(* (sub_completion_unify2), the completing substitution then equates both  *)
(* sides of each constraint (pure_add_constraints_apply), and type_op is   *)
(* evaluated on the resulting types.                                       *)

let INFER1AUX_is_app name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let INFER1AUX_SC_BACK_TAC : tactic =
  let sc_subst th = el 2 (snd(strip_comb(concl th))) in
  let step (asl,w as gl) =
    let ths = map snd asl in
    let scs = filter (fun th -> INFER1AUX_is_app "sub_completion" (concl th)) ths in
    let have = map sc_subst scs in
    let unifs = filter (fun th -> is_eq(concl th) &&
                                  INFER1AUX_is_app "t_unify" (lhs(concl th))) ths in
    let try_pair u sc =
      let r = MATCH_MP sub_completion_unify2 (CONJ u sc) in
      if mem (sc_subst r) have then failwith "INFER1AUX_SC_BACK_TAC" else r in
    ASSUME_TAC (tryfind (fun u -> tryfind (try_pair u) scs) unifs) gl in
  REPEAT step;;

let INFER1AUX_SC_EQS_TAC : tactic =
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let wfss = filter (fun th -> INFER1AUX_is_app "t_wfs" (concl th)) ths in
    let scs = filter (fun th -> INFER1AUX_is_app "sub_completion" (concl th)) ths in
    let pick sc =
      let s1 = el 2 (snd(strip_comb(concl sc))) in
      (find (fun th -> rand(concl th) = s1) wfss, sc) in
    let (wf,sc) = tryfind pick scs in
    let pac = CONJUNCT1 (REWRITE_RULE[sub_completion_def] sc) in
    let eqs = MATCH_MP pure_add_constraints_apply (CONJ wf pac) in
    (ASSUME_TAC (MATCH_MP sub_completion_wfs (CONJ wf sc)) THEN
     STRIP_ASSUME_TAC (REWRITE_RULE[MAP; o_THM; CONS_11] eqs)) gl;;

let INFER1AUX_WS_CASES_TAC : tactic =
  fun (asl,w as gl) ->
    let vs = filter (fun v -> type_of v = `:word_size`) (frees w) in
    MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "word_size"))) vs gl;;

let INFER1AUX_COS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs]) THEN
  INFER1AUX_SC_BACK_TAC THEN INFER1AUX_SC_EQS_TAC THEN
  REWRITE_TAC[MAP; o_THM] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP] THEN
  REWRITE_TAC[INFER1AUX_convert_t_num_of] THEN REWRITE_TAC[convert_t_def; MAP] THEN
  INFER1AUX_WS_CASES_TAC THEN
  REWRITE_TAC[type_op_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC(word_tc_def :: INFER1AUX_ES_tydefs) THEN ASM_REWRITE_TAC[];;

(* the Arith case of constrain_op_sound (add_constraints with REPLICATE) *)
let INFER1AUX_constrain_op_sound_arith = prove
 (`!st tenv st' c s l a ty ts t.
     t_wfs (infer_st_subst st) /\
     sub_completion (num_tvs tenv) (infer_st_next_uvar st') (infer_st_subst st') c s /\
     constrain_op l (Arith a ty) ts st = (M_success t,st')
     ==> type_op (Arith a ty) (MAP (convert_t o t_walkstar s) ts) (convert_t (t_walkstar s t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[constrain_op_success] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[add_constraints_success] o
    check (fun th -> INFER1AUX_is_app "add_constraints" (lhs(concl th)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar s) ts =
                MAP (t_walkstar s) (REPLICATE a' (Infer_Tapp [] (t_num_of ty)))` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_apply_list THEN
    MAP_EVERY EXISTS_TAC [`num_tvs tenv`; `infer_st_next_uvar st'`; `infer_st_subst st'`;
                          `c:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`infer_st_subst st`;
                   `ZIP (ts:infer_t list) (REPLICATE a' (Infer_Tapp [] (t_num_of ty)))`;
                   `infer_st_subst st'`] pure_add_constraints_apply) THEN
    ASM_REWRITE_TAC[MAP_o] THEN ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP];
    ALL_TAC] THEN
  REWRITE_TAC[MAP_o] THEN ASM_REWRITE_TAC[map_replicate] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP; INFER1AUX_convert_t_num_of; map_replicate] THEN
  REWRITE_TAC[type_op_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[EVERY_REPLICATE; LENGTH_REPLICATE]);;

let constrain_op_sound = prove
 (`!st tenv st' c s l op ts t.
     t_wfs (infer_st_subst st) /\
     sub_completion (num_tvs tenv) (infer_st_next_uvar st') (infer_st_subst st') c s /\
     constrain_op l op ts st = (M_success t,st')
     ==> type_op op (MAP (convert_t o t_walkstar s) ts) (convert_t (t_walkstar s t))`,
  REPEAT GEN_TAC THEN CASES_ON `op:op` THEN
  TRY(MATCH_ACCEPT_TAC INFER1AUX_constrain_op_sound_arith) THEN
  REWRITE_TAC[constrain_op_success] THEN STRIP_TAC THEN INFER1AUX_COS_TAC THEN
  MESON_TAC[]);;

let infer_deBruijn_subst_walkstar = prove
 (`!ts t s.
     t_wfs s
     ==> t_walkstar s (infer_deBruijn_subst (MAP (t_walkstar s) ts) t) =
         t_walkstar s (infer_deBruijn_subst ts t)`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_subst_alt; LENGTH_MAP] THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MAP; t_walkstar_idempotent];
    ASM_SIMP_TAC[t_walkstar_eqn1; injectivity "infer_t"; MAP_MAP_o; MAP_EQ_f; o_THM]]);;


(* ---------- infer_e_sound: proof automation and case lemmas ---------- *)

(* normal form of state projections *)
let INFER1AUX_tm_nuv = `infer_st_next_uvar:infer_st->num`;;

(* next_uvar Y = e, from a run that keeps next_uvar: used from right to left *)
let INFER1AUX_is_nuv_eq th =
  let c = concl th in
  is_eq c &&
  (try let r = rhs c in
       rator r = INFER1AUX_tm_nuv && is_var (rand r) && not (free_in r (lhs c))
   with Failure _ -> false);;

let INFER1AUX_nuv_eqs ths = map SYM (filter INFER1AUX_is_nuv_eq ths);;

let INFER1AUX_NORM_CONV_WITH eqs =
  REWRITE_CONV([infer_st_rewrs; num_tvs_def; num_tvs_bind_var_list] @ eqs);;
let INFER1AUX_NORM_CONV = INFER1AUX_NORM_CONV_WITH [];;
let INFER1AUX_norm tm = rhs(concl(INFER1AUX_NORM_CONV tm));;

(* a run of the inferencer: infer_X ... X = (M_success r,Y), gives (X,Y) *)
let INFER1AUX_run_states th =
  let l,r = dest_eq(concl th) in
  let f,args = strip_comb l in
  if mem (fst(dest_const f))
       ["infer_e"; "infer_es"; "infer_pes"; "infer_funs"; "infer_p"; "infer_ps";
        "constrain_op"]
  then (last args, rand r) else failwith "INFER1AUX_run_states";;

let INFER1AUX_wfs_lemmas = CONJUNCTS infer_e_wfs @ CONJUNCTS infer_p_wfs @ [constrain_op_wfs];;

let INFER1AUX_tm_wfs = `t_wfs:(num,infer_t)fmap->bool`;;
let INFER1AUX_tm_subst = `infer_st_subst:infer_st->(num,infer_t)fmap`;;

(* t_wfs of every substitution reached from a t_wfs one *)
let INFER1AUX_WFS_FWD_TAC : tactic =
  let step (asl,w as gl) =
    let ths = map snd asl in
    let concls = map concl ths in
    let conv = INFER1AUX_NORM_CONV_WITH (INFER1AUX_nuv_eqs ths) in
    let norm tm = rhs(concl(conv tm)) in
    let known tm = mem (norm tm) concls in
    let get tm =
      let eq = conv tm in
      EQ_MP (SYM eq) (find (fun t -> concl t = rhs(concl eq)) ths) in
    let try_run th =
      let (x,y) = INFER1AUX_run_states th in
      let goal_wf = mk_comb(INFER1AUX_tm_wfs, mk_comb(INFER1AUX_tm_subst, y)) in
      if known goal_wf then failwith "known" else
      let pre_th = get (mk_comb(INFER1AUX_tm_wfs, mk_comb(INFER1AUX_tm_subst, x))) in
      let r = tryfind (fun lem -> try MATCH_MP lem (CONJ th pre_th)
                                  with Failure _ -> MATCH_MP lem (CONJ pre_th th))
                      INFER1AUX_wfs_lemmas in
      CONV_RULE conv r in
    let try_unify th =
      let l,r = dest_eq(concl th) in
      if not (INFER1AUX_is_app "t_unify" l) then failwith "try_unify" else
      if known (mk_comb(INFER1AUX_tm_wfs, rand r)) then failwith "known" else
      let wf = get (mk_comb(INFER1AUX_tm_wfs, hd(snd(strip_comb l)))) in
      MATCH_MP t_unify_wfs (CONJ wf th) in
    let try_pac th =
      if not (INFER1AUX_is_app "pure_add_constraints" (concl th)) then failwith "try_pac" else
      let args = snd(strip_comb(concl th)) in
      if known (mk_comb(INFER1AUX_tm_wfs, el 2 args)) then failwith "known" else
      let wf = get (mk_comb(INFER1AUX_tm_wfs, hd args)) in
      MATCH_MP pure_add_constraints_wfs (CONJ th wf) in
    let try_one th = try try_run th with Failure _ ->
                     try try_unify th with Failure _ -> try_pac th in
    ASSUME_TAC (tryfind try_one ths) gl in
  REPEAT step;;

(* sub_completion pulled back to the start state of every run *)
let INFER1AUX_constrain_op_sc = prove
 (`!l op ts st t st' tenv ec s.
     constrain_op l op ts st = (M_success t,st') /\
     sub_completion (num_tvs tenv) (infer_st_next_uvar st') (infer_st_subst st') ec s
     ==> ?c. sub_completion (num_tvs tenv) (infer_st_next_uvar st) (infer_st_subst st) c s`,
  MESON_TAC[constrain_op_sub_completion]);;

let INFER1AUX_sc_lemmas =
  [sub_completion_infer; sub_completion_infer_es; sub_completion_infer_pes;
   sub_completion_infer_funs; INFER1AUX_constrain_op_sc] @ CONJUNCTS sub_completion_infer_p;;

let INFER1AUX_SC_BWD_TAC : tactic =
  let sc_key th = let a = snd(strip_comb(concl th)) in (el 1 a, el 2 a) in
  let step (asl,w as gl) =
    let ths = map snd asl in
    let conv = INFER1AUX_NORM_CONV_WITH (INFER1AUX_nuv_eqs ths) in
    let norm tm = rhs(concl(conv tm)) in
    let scs = filter (fun th -> INFER1AUX_is_app "sub_completion" (concl th)) ths in
    let have = map sc_key scs in
    let finish r =
      let r' = CONV_RULE conv r in
      let r'' = if is_exists(concl r') then r' else r' in
      let key = let b = snd(strip_comb(snd(strip_exists(concl r'')))) in (el 1 b, el 2 b) in
      if mem key have then failwith "have" else r'' in
    (* an sc with next_uvar m0 and subst s0, possibly by more_vars *)
    let find_sc m0 s0 =
      tryfind (fun sc ->
        let (m,s) = sc_key sc in
        if s <> s0 then failwith "subst" else
        if m = m0 then sc else
        let r = MATCH_MP sub_completion_more_vars sc in
        if fst(sc_key r) = m0 then r else failwith "more_vars") scs in
    let try_run th =
      let (x,y) = INFER1AUX_run_states th in
      let m0 = norm (mk_comb(INFER1AUX_tm_nuv, y)) in
      let s0 = norm (mk_comb(INFER1AUX_tm_subst, y)) in
      let sc = find_sc m0 s0 in
      let a = snd(strip_comb(concl sc)) in
      let target = list_mk_comb(`sub_completion`,
                     [el 0 a; mk_comb(INFER1AUX_tm_nuv, y); mk_comb(INFER1AUX_tm_subst, y);
                      el 3 a; el 4 a]) in
      let sc' = EQ_MP (SYM (conv target)) sc in
      let r = finish (tryfind (fun lem -> MATCH_MP lem (CONJ th sc')) INFER1AUX_sc_lemmas) in
      if mem (concl sc) (map concl ths) then r else CONJ sc r in
    let try_unify th =
      let l,r = dest_eq(concl th) in
      if not (INFER1AUX_is_app "t_unify" l) then failwith "try_unify" else
      finish (tryfind (fun sc -> MATCH_MP sub_completion_unify2 (CONJ th sc)) scs) in
    let try_pac th =
      if not (INFER1AUX_is_app "pure_add_constraints" (concl th)) then failwith "try_pac" else
      finish (tryfind (fun sc -> MATCH_MP sub_completion_add_constraints (CONJ th sc)) scs) in
    let try_one th = try try_run th with Failure _ ->
                     try try_unify th with Failure _ -> try_pac th in
    STRIP_ASSUME_TAC (tryfind try_one ths) gl in
  REPEAT step;;
(* discharge all antecedents of a (universally quantified) implication with *)
(* facts, up to the normal form of state projections                       *)
let INFER1AUX_DISCH_ALL (facts:thm list) (th:thm) : thm =
  let avoid = freesl (map concl facts) in
  let conv = INFER1AUX_NORM_CONV_WITH (INFER1AUX_nuv_eqs facts) in
  let rec go vars th =
    let c = concl th in
    if is_forall c then
      let v,_ = dest_forall c in
      let v' = variant (vars @ avoid @ frees c @ freesl (hyp th)) v in
      go (v'::vars) (SPEC v' th)
    else if not (is_imp c) then th else
    let a = fst(dest_imp c) in
    if is_conj a then
      let a1,a2 = dest_conj a in
      go vars (DISCH a1 (DISCH a2 (MP th (CONJ (ASSUME a1) (ASSUME a2)))))
    else
      let eq = conv a in
      let na = rhs(concl eq) in
      let fixed = subtract (union (frees c) (freesl (hyp th))) vars in
      tryfind (fun f ->
        let i = term_match fixed na (concl f) in
        let th' = INSTANTIATE i th and eq' = INSTANTIATE i eq in
        go vars (MP th' (EQ_MP (SYM eq') f))) facts in
  go [] th;;

let INFER1AUX_is_ih th =
  let rec concl_of t =
    let t' = snd(strip_forall t) in
    if is_imp t' then concl_of (snd(dest_imp t')) else t' in
  let c = snd(strip_forall(concl th)) in
  is_imp c &&
  mem (try fst(dest_const(fst(strip_comb(concl_of c)))) with Failure _ -> "")
      ["type_e"; "type_es"; "type_pes"; "type_funs"];;

(* every induction hypothesis whose antecedents are all among the facts *)
let INFER1AUX_IH_TAC : tactic =
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let ihs = filter INFER1AUX_is_ih ths in
    let facts = filter (not o INFER1AUX_is_ih) ths in
    let res = mapfilter (INFER1AUX_DISCH_ALL facts) ihs in
    MAP_EVERY ASSUME_TAC res gl;;

let INFER1AUX_constrain_op_uvar = prove
 (`!l op ts st v st'.
     constrain_op l op ts st = (M_success v,st')
     ==> infer_st_next_uvar st <= infer_st_next_uvar st'`,
  MESON_TAC[TYSYS2AUX_constrain_op_state]);;

(* next_uvar monotonicity of every run *)
let INFER1AUX_UVAR_TAC : tactic =
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let lems = CONJUNCTS infer_e_next_uvar_mono @ CONJUNCTS infer_p_next_uvar_mono @
               [INFER1AUX_constrain_op_uvar] in
    let conv = INFER1AUX_NORM_CONV_WITH (INFER1AUX_nuv_eqs ths) in
    let res = mapfilter (fun th ->
       let _ = INFER1AUX_run_states th in
       CONV_RULE conv (tryfind (fun lem -> MATCH_MP lem th) lems)) ths in
    MAP_EVERY ASSUME_TAC res gl;;

(* ienv_ok at the start of every run, from an ienv_ok fact for its environment *)
let INFER1AUX_IENV_TAC : tactic =
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let conv = INFER1AUX_NORM_CONV_WITH (INFER1AUX_nuv_eqs ths) in
    let ienv_oks = filter (fun th -> INFER1AUX_is_app "ienv_ok" (concl th)) ths in
    let runs = mapfilter (fun th ->
       let (x,_) = INFER1AUX_run_states th in
       let ie = el 1 (snd(strip_comb(lhs(concl th)))) in
       if type_of ie = `:inf_env` then (x,ie) else failwith "") ths in
    let tms = mapfilter (fun (x,ie) ->
       let base = find (fun th -> rand(concl th) = ie) ienv_oks in
       let tm = rhs(concl(conv (list_mk_comb(`ienv_ok`,
                  [mk_comb(`count`, mk_comb(INFER1AUX_tm_nuv, x)); ie])))) in
       (tm,base)) runs in
    let tms = filter (fun (tm,_) -> not (mem tm (map concl ths))) tms in
    MAP_EVERY (fun (tm,base) ->
       let n = rand(rand(rator(concl base))) in
       TRY (SUBGOAL_THEN tm ASSUME_TAC THENL
         [MATCH_MP_TAC ienv_ok_more THEN EXISTS_TAC n THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC; ALL_TAC])) tms gl;;

(* the completing substitution satisfies every unification of the run *)
let INFER1AUX_UNIFY_EQS_TAC : tactic =
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let wfss = filter (fun th -> INFER1AUX_is_app "t_wfs" (concl th)) ths in
    let scs = filter (fun th -> INFER1AUX_is_app "sub_completion" (concl th)) ths in
    let one th =
      let l,r = dest_eq(concl th) in
      if not (INFER1AUX_is_app "t_unify" l) then failwith "" else
      let s1 = hd(snd(strip_comb l)) in
      let wf = find (fun w -> rand(concl w) = s1) wfss in
      let ap = MATCH_MP t_unify_apply (CONJ wf th) in
      let wf2 = MATCH_MP t_unify_wfs (CONJ wf th) in
      tryfind (fun sc -> MATCH_MP sub_completion_apply (CONJ wf2 (CONJ ap sc))) scs in
    MAP_EVERY ASSUME_TAC (mapfilter one ths) gl;;

(* add the conclusion of th, all of whose antecedents are among the facts *)
let INFER1AUX_FWD_TAC (th:thm) : tactic = fun (asl,w as gl) ->
  ASSUME_TAC (INFER1AUX_DISCH_ALL (map snd asl) th) gl;;
let INFER1AUX_tm_walk = `t_walkstar:(num,infer_t)fmap->infer_t->infer_t`;;

(* t_wfs of the completing substitution *)
(* the completing substitution: the last argument of the sub_completion facts *)
let INFER1AUX_comp_subst ths =
  rand(concl(find (fun th -> INFER1AUX_is_app "sub_completion" (concl th)) ths));;

let INFER1AUX_WFS_S_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let s = INFER1AUX_comp_subst ths in
  if mem (mk_comb(INFER1AUX_tm_wfs, s)) (map concl ths) then ALL_TAC gl else
  let wfss = filter (fun th -> INFER1AUX_is_app "t_wfs" (concl th)) ths in
  let scs = filter (fun th -> INFER1AUX_is_app "sub_completion" (concl th) &&
                              rand(concl th) = s) ths in
  let r = tryfind (fun sc ->
            let s1 = el 2 (snd(strip_comb(concl sc))) in
            let wf = find (fun w -> rand(concl w) = s1) wfss in
            MATCH_MP sub_completion_wfs (CONJ wf sc)) scs in
  ASSUME_TAC r gl;;

let INFER1AUX_is_type_fact tm =
  mem (try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "")
      ["type_e"; "type_es"; "type_pes"; "type_funs"; "type_p"; "type_ps"];;

(* rewrite the types of the typing facts and of the goal with the        *)
(* equations t_walkstar s a = t_walkstar s b, then evaluate t_walkstar s *)
(* and convert_t on type constructors                                     *)
let INFER1AUX_WALK_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let s = INFER1AUX_comp_subst ths in
  let ws = mk_comb(INFER1AUX_tm_walk, s) in
  let eqs = filter (fun th -> let c = concl th in is_eq c &&
               (try rator(lhs c) = ws && rator(rhs c) = ws with Failure _ -> false)) ths in
  let wf = find (fun th -> concl th = mk_comb(INFER1AUX_tm_wfs, s)) ths in
  let walk = [MATCH_MP t_walkstar_eqn1 wf; MAP; convert_t_def] in
  let rule = REWRITE_RULE walk o REWRITE_RULE eqs in
  (RULE_ASSUM_TAC (fun th -> if INFER1AUX_is_type_fact (concl th) then rule th else th) THEN
   REWRITE_TAC eqs THEN REWRITE_TAC walk) gl;;

let INFER1AUX_type_e_rules = REWRITE_RULE INFER1AUX_ES_tydefs type_e_rules;;

let INFER1AUX_sc_uvar_check = prove
 (`!n m s1 ec s. sub_completion n m s1 ec s
     ==> !u. u < m ==> check_freevars n [] (convert_t (t_walkstar s (Infer_Tuvar u)))`,
  REWRITE_TAC[sub_completion_def; SUBSET; IN_COUNT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC check_t_to_check_freevars THEN ASM_MESON_TAC[]);;

(* check_freevars of the completion of a unification variable below a     *)
(* sub_completion bound                                                    *)
let INFER1AUX_UVAR_CHECK_TAC : tactic =
  FIRST_ASSUM(fun sc -> MATCH_MP_TAC (MATCH_MP INFER1AUX_sc_uvar_check sc) THEN ASM_ARITH_TAC);;
let INFER1AUX_ienv_ok_upd = prove
 (`!uvs E ienv.
     ienv_ok uvs (inf_env_inf_v_fupd (K E) ienv) <=>
     ienv_val_ok uvs E /\ tenv_ctor_ok (inf_env_inf_c ienv) /\
     tenv_abbrev_ok (inf_env_inf_t ienv)`,
  REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM]);;

let INFER1AUX_ienv_ok_bind = prove
 (`!n m x t ienv.
     ienv_ok (count n) ienv /\ n <= m /\ check_t 0 (count m) t
     ==> ienv_ok (count m)
           (inf_env_inf_v_fupd (K (nsBind x (0,t) (inf_env_inf_v ienv))) ienv)`,
  REWRITE_TAC[INFER1AUX_ienv_ok_upd; ienv_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_nsBind THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN ASM_MESON_TAC[]);;

let INFER1AUX_ienv_ok_optbind = prove
 (`!n m xo t ienv.
     ienv_ok (count n) ienv /\ n <= m /\ check_t 0 (count m) t
     ==> ienv_ok (count m)
           (inf_env_inf_v_fupd (K (nsOptBind xo (0,t) (inf_env_inf_v ienv))) ienv)`,
  REWRITE_TAC[INFER1AUX_ienv_ok_upd; ienv_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_nsOptBind THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN ASM_MESON_TAC[]);;

let INFER1AUX_sc_in_fdom = prove
 (`!n m s1 ec s. sub_completion n m s1 ec s ==> !u. u < m ==> u IN FDOM s`,
  REWRITE_TAC[sub_completion_def; SUBSET; IN_COUNT] THEN MESON_TAC[]);;

let INFER1AUX_sc_walk_check = prove
 (`!n m s1 ec s.
     sub_completion n m s1 ec s
     ==> !uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))`,
  REWRITE_TAC[sub_completion_def] THEN MESON_TAC[]);;

(* u IN FDOM s, from a sub_completion bound above u *)
let INFER1AUX_IN_FDOM_TAC : tactic =
  FIRST_ASSUM(fun sc -> MATCH_MP_TAC (MATCH_MP INFER1AUX_sc_in_fdom sc) THEN ASM_ARITH_TAC);;

(* the completion check of the uvars in FDOM s *)
let INFER1AUX_WALK_CHECK_TAC : tactic =
  FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP INFER1AUX_sc_walk_check);;
(* check_freevars of the completion of a type whose uvars are below a     *)
(* sub_completion bound                                                    *)
let INFER1AUX_sc_check_freevars = prove
 (`!n m s1 ec s k t.
     sub_completion n m s1 ec s /\ t_wfs s /\ check_t 0 (count k) t /\ k <= m
     ==> check_freevars n [] (convert_t (t_walkstar s t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC check_t_to_check_freevars THEN
  MATCH_MP_TAC (CONJUNCT1 check_t_walkstar) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_is_app "sub_completion" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] (CONJUNCT1 check_t_more5)) THEN
  EXISTS_TAC `count k` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`t:infer_t`; `0`; `count k`] (CONJUNCT1 check_t_more2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[ADD_CLAUSES];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count m` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;
let INFER1AUX_ienv_fupd_id = prove
 (`!ienv. inf_env_inf_v_fupd (K (inf_env_inf_v ienv)) ienv = ienv`,
  REWRITE_TAC[inf_env_INFO.ri_component_equality; inf_env_INFO.ri_accfupds; K_THM]);;

(* check_t over FDOM s of a type whose uvars are below a sub_completion bound *)
let INFER1AUX_sc_check_t_fdom = prove
 (`!n m s1 ec s k t.
     sub_completion n m s1 ec s /\ check_t 0 (count k) t /\ k <= m
     ==> check_t n (FDOM s) t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_is_app "sub_completion" (concl th))) THEN
  MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] (CONJUNCT1 check_t_more5)) THEN
  EXISTS_TAC `count k` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`t:infer_t`; `0`; `count k`] (CONJUNCT1 check_t_more2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[ADD_CLAUSES];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count m` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;

(* check_t over FDOM s of types whose uvars are below a sub_completion bound *)
let INFER1AUX_sc_all_check_t_fdom = prove
 (`!n m s1 ec s k tvs ts.
     sub_completion n m s1 ec s /\ ALL (check_t tvs (count k)) ts /\ k <= m
     ==> ALL (check_t tvs (FDOM s)) ts`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] (CONJUNCT2 check_t_more5)) THEN
  EXISTS_TAC `count k` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count m` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[sub_completion_def]]);;

(* the conclusion of th, all of whose antecedents are among the facts, stripped *)
let INFER1AUX_FWDS_TAC (th:thm) : tactic = fun (asl,w as gl) ->
  STRIP_ASSUME_TAC (INFER1AUX_DISCH_ALL (map snd asl) th) gl;;
(* the type of a type annotation, completed *)
let INFER1AUX_tannot_type2 = prove
 (`!s tenvT t.
     t_wfs s /\ tenv_abbrev_ok tenvT /\ check_freevars_ast [] t /\ check_type_names tenvT t
     ==> convert_t (t_walkstar s (infer_type_subst [] (type_name_subst tenvT t))) =
         type_name_subst tenvT t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `check_freevars 0 [] (type_name_subst tenvT t)` ASSUME_TAC THENL
   [MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_type_subst_empty_check)) THEN
  SUBGOAL_THEN `t_walkstar s (infer_type_subst [] (type_name_subst tenvT t)) =
                infer_type_subst [] (type_name_subst tenvT t)` SUBST1_TAC THENL
   [MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 (SPEC `0` infer_type_subst_nil)) th]) THEN
  MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[]);;
(* the names of a typed function list *)
let INFER1AUX_map_fst_map2 = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) ts s.
     LENGTH funs = LENGTH ts
     ==> MAP FST (MAP2 (\xyz t. match xyz with (x,y,z) -> (x,convert_t (t_walkstar s t)))
                   funs ts) =
         MAP FST funs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ts:infer_t list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MAP; CONS_11] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[]);;
let INFER1AUX_is_run th =
  try mem (fst(dest_const(fst(strip_comb(lhs(concl th))))))
          ["infer_e"; "infer_es"; "infer_pes"; "infer_funs"]
  with Failure _ -> false;;

let INFER1AUX_IES_EXPAND_TAC (extra:thm list) : tactic =
  FIRST_X_ASSUM(MP_TAC o check INFER1AUX_is_run) THEN
  REWRITE_TAC(infer_e_def :: extra) THEN
  REWRITE_TAC[success_eqns; EXISTS_PAIR_THM; pair_CASE; PAIR_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC([success_eqns; EXISTS_PAIR_THM; pair_CASE; PAIR_EQ] @ extra);;

(* variables of type :1 are one *)
let INFER1AUX_ONE_TAC : tactic = fun (asl,w as gl) ->
  let vs = filter (fun v -> type_of v = `:1`)
             (union (frees w) (freesl (map (concl o snd) asl))) in
  MAP_EVERY (fun v -> SUBST_ALL_TAC (ISPEC v one)) vs gl;;

(* a run that keeps next_uvar gives next_uvar Y = e: rewrite with it *)
let INFER1AUX_NUV_EQ_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let eqs = INFER1AUX_nuv_eqs ths in
  if eqs = [] then ALL_TAC gl else
  (RULE_ASSUM_TAC (fun th -> if INFER1AUX_is_nuv_eq th then th else REWRITE_RULE eqs th) THEN
   REWRITE_TAC eqs) gl;;

let INFER1AUX_IES_REST1_TAC =
  STRIP_TAC THEN RVEQ_TAC THEN INFER1AUX_ONE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs]) THEN INFER1AUX_NUV_EQ_TAC THEN
  INFER1AUX_WFS_FWD_TAC THEN INFER1AUX_SC_BWD_TAC THEN
  INFER1AUX_UVAR_TAC THEN INFER1AUX_IENV_TAC THEN INFER1AUX_WFS_S_TAC;;

let INFER1AUX_IES_REST2_TAC =
  INFER1AUX_IH_TAC THEN
  INFER1AUX_UNIFY_EQS_TAC THEN REWRITE_TAC[infer_st_rewrs] THEN
  INFER1AUX_WALK_TAC;;

let INFER1AUX_IES_REST_TAC = INFER1AUX_IES_REST1_TAC THEN INFER1AUX_IES_REST2_TAC;;

let INFER1AUX_IES_GEN_TAC =
  REPEAT STRIP_TAC THEN INFER1AUX_IES_EXPAND_TAC [] THEN INFER1AUX_IES_REST_TAC;;

(* Handle and Mat: the empty case fails *)
let INFER1AUX_IES_NONEMPTY_TAC =
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `pes:(pat#exp)list = []` THENL
   [FIRST_X_ASSUM(MP_TAC o check INFER1AUX_is_run) THEN
    ASM_REWRITE_TAC[infer_e_def; failwith_def; PAIR_EQ; distinctness "exc"];
    INFER1AUX_IES_EXPAND_TAC [ASSUME `~(pes:(pat#exp)list = [])`] THEN
    INFER1AUX_IES_REST_TAC];;
let INFER1AUX_ies_var = prove
 (`!s ienv tenv tenvE id n0 tvs t s1 ec.
     env_rel_sound s ienv tenv tenvE /\ t_wfs s /\
     nsLookup (inf_env_inf_v ienv) id = SOME (tvs,t) /\
     sub_completion (num_tvs tenvE) (n0 + tvs) s1 ec s
     ==> type_e tenv tenvE (Var id)
           (convert_t (t_walkstar s (infer_deBruijn_subst
              (MAP (\n. Infer_Tuvar (n0 + n)) (COUNT_LIST tvs)) t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`id:(mlstring,mlstring)id`; `(tvs:num,t:infer_t)`; `s:(num,infer_t)fmap`;
                 `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`]
         env_rel_sound_lookup_some) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs':num` (X_CHOOSE_THEN `t':t` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`unconvert_t t'`; `num_tvs tenvE`; `s:(num,infer_t)fmap`; `tvs:num`;
                 `tvs':num`; `t:infer_t`] tscheme_approx_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
    `MAP (t_walkstar s) (MAP (\n. Infer_Tuvar (n0 + n)) (COUNT_LIST tvs))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; ALL_MAP; o_DEF; every_count_list] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def; SUBSET; IN_COUNT] o
      check (fun th -> INFER1AUX_is_app "sub_completion" (concl th))) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subst':infer_t list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`MAP (\n. Infer_Tuvar (n0 + n)) (COUNT_LIST tvs)`; `t:infer_t`;
                 `s:(num,infer_t)fmap`] infer_deBruijn_subst_walkstar) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t':t`; `tvs' + num_tvs tenvE`; `s:(num,infer_t)fmap`; `subst':infer_t list`]
         db_subst_infer_subst_swap3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN EXISTS_TAC `tvs':num` THEN
  ASM_REWRITE_TAC[LENGTH_MAP; ALL_MAP; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) && 
    (try fst(dest_const(rator(rator(concl th)))) = "ALL" with Failure _ -> false))) THEN
  MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC check_t_to_check_freevars THEN
  MATCH_MP_TAC (CONJUNCT1 check_t_walkstar) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_is_app "sub_completion" (concl th))) THEN
  ASM_REWRITE_TAC[]);;
(* the Con (SOME cn) case of infer_e_sound *)
let INFER1AUX_ies_con_some = prove
 (`!s s1 s2 uvs ienv tenv tenvE cn es tvs ts tn ts1 u ec.
     t_wfs s1 /\ ienv_ok uvs ienv /\ env_rel_sound s ienv tenv tenvE /\
     nsLookup (inf_env_inf_c ienv) cn = SOME (tvs,ts,tn) /\
     LENGTH ts1 = LENGTH ts /\
     pure_add_constraints s1
       (ZIP ts1 (MAP (infer_type_subst
          (ZIP tvs (MAP (\n. Infer_Tuvar (u + n)) (COUNT_LIST (LENGTH tvs))))) ts)) s2 /\
     sub_completion (num_tvs tenvE) (u + LENGTH tvs) s2 ec s /\
     type_es tenv tenvE es (MAP (convert_t o t_walkstar s) ts1)
     ==> type_e tenv tenvE (Con (SOME cn) es)
           (Tapp (MAP convert_t (MAP (t_walkstar s)
              (MAP (\n. Infer_Tuvar (u + n)) (COUNT_LIST (LENGTH tvs))))) tn)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  ABBREV_TAC `U = MAP (\n. Infer_Tuvar (u + n)) (COUNT_LIST (LENGTH (tvs:mlstring list)))` THEN
  SUBGOAL_THEN `MAP (t_walkstar s) ts1 =
                MAP (t_walkstar s) (MAP (infer_type_subst (ZIP tvs U)) ts)` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_apply_list THEN
    MAP_EVERY EXISTS_TAC [`num_tvs tenvE`; `u + LENGTH (tvs:mlstring list)`;
                          `s2:(num,infer_t)fmap`; `ec:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP pure_add_constraints_apply o
      CONJ (ASSUME `t_wfs (s1:(num,infer_t)fmap)`)) THEN
    REWRITE_TAC[MAP_o] THEN ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_freevars 0 tvs) ts` ASSUME_TAC THENL
   [MATCH_MP_TAC tenv_ctor_ok_lookup THEN
    MAP_EVERY EXISTS_TAC [`inf_env_inf_c ienv`; `cn:(mlstring,mlstring)id`; `tn:num`] THEN
    ASM_MESON_TAC[ienv_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (convert_t o t_walkstar s) ts1 =
                MAP (type_subst (alist_to_fmap
                  (ZIP tvs (MAP convert_t (MAP (t_walkstar s) U))))) ts`
   ASSUME_TAC THENL
   [REWRITE_TAC[MAP_o] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MAP (t_walkstar s) U =
                  MAP (\n. t_walkstar s (Infer_Tuvar (u + n)))
                      (COUNT_LIST (LENGTH (tvs:mlstring list)))`
      SUBST1_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[MAP_MAP_o; o_DEF]; ALL_TAC] THEN
    EXPAND_TAC "U" THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 subst_infer_subst_swap) th]) THEN
    MATCH_MP_TAC (CONJUNCT2 convert_t_subst) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST];
    ALL_TAC] THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
  MAP_EVERY EXISTS_TAC [`tvs:mlstring list`; `ts:t list`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "MAP" with Failure _ -> false)) THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
    MATCH_MP_TAC sub_completion_check THEN ASM_MESON_TAC[];
    EXPAND_TAC "U" THEN REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[env_rel_sound_def]]);;
(* the last step of the Letrec case of infer_e_sound *)
let INFER1AUX_ies_letrec_final = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) funs_ts e t tenv tenvE s u s5 s6 n m ec.
     t_wfs s5 /\ LENGTH funs = LENGTH funs_ts /\
     pure_add_constraints s5
       (ZIP (MAP (\n. Infer_Tuvar (u + n)) (COUNT_LIST (LENGTH funs))) funs_ts) s6 /\
     sub_completion n m s6 ec s /\
     type_funs tenv
       (bind_var_list 0
          (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
             (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (u + n))))
                (COUNT_LIST (LENGTH funs)))) tenvE)
       funs
       (MAP2 (\xyz t. match xyz with (x,y,z) -> (x,(convert_t o t_walkstar s) t))
          funs funs_ts) /\
     type_e tenv
       (bind_var_list 0
          (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
             (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (u + n))))
                (COUNT_LIST (LENGTH funs)))) tenvE)
       e t
     ==> type_e tenv tenvE (Letrec funs e) t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s6:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN
    `MAP (t_walkstar s) (MAP (\n. Infer_Tuvar (u + n))
       (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))) =
     MAP (t_walkstar s) (funs_ts:infer_t list)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_apply_list THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `m:num`; `s6:(num,infer_t)fmap`;
                          `ec:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP pure_add_constraints_apply o
      CONJ (ASSUME `t_wfs (s5:(num,infer_t)fmap)`)) THEN
    REWRITE_TAC[MAP_o] THEN
    ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (u + n))))
       (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))) =
     MAP (\t. convert_t (t_walkstar s t)) (funs_ts:infer_t list)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `MAP convert_t`) THEN
    REWRITE_TAC[MAP_MAP_o; o_DEF];
    ALL_TAC] THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
  EXISTS_TAC (CASE_TERM
    `MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
       (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (u + n))))
          (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))`) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> let eq = MATCH_MP INFER1AUX_letrec_lemma_u th in
      GEN_REWRITE_TAC RAND_CONV [eq]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> INFER1AUX_is_app "type_funs" (concl th))) THEN
    REWRITE_TAC[o_THM];
    FIRST_X_ASSUM ACCEPT_TAC]);;
let INFER1AUX_IES_RAISE_TAC =
  INFER1AUX_IES_GEN_TAC THEN INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
  ASM_REWRITE_TAC[] THEN INFER1AUX_UVAR_CHECK_TAC;;

let INFER1AUX_IES_HANDLE_TAC =
  INFER1AUX_IES_NONEMPTY_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[type_pes_def]) THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN ASM_REWRITE_TAC[];;

let INFER1AUX_IES_LIT_TAC =
  INFER1AUX_IES_GEN_TAC THEN INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules;;

let INFER1AUX_IES_VAR_TAC =
  INFER1AUX_IES_GEN_TAC THEN MATCH_MP_TAC INFER1AUX_ies_var THEN ASM_MESON_TAC[];;

let INFER1AUX_IES_CON_TAC =
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `cn_opt:((mlstring,mlstring)id)option` (cases "option")) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; FORALL_UNWIND_THM1;
              FORALL_UNWIND_THM2] THEN
  INFER1AUX_IES_GEN_TAC THENL
   [REWRITE_TAC[GSYM MAP_o] THEN INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INFER1AUX_ies_con_some THEN ASM_MESON_TAC[]];;

let INFER1AUX_IES_FUN_TAC =
  REPEAT STRIP_TAC THEN INFER1AUX_IES_EXPAND_TAC [] THEN INFER1AUX_IES_REST1_TAC THEN
  SUBGOAL_THEN `ienv_ok (count (infer_st_next_uvar st + 1))
                  (inf_env_inf_v_fupd (K (nsBind x (0,Infer_Tuvar (infer_st_next_uvar st))
                     (inf_env_inf_v ienv))) ienv)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ienv_ok_bind THEN EXISTS_TAC `infer_st_next_uvar st` THEN
    ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `env_rel_sound s
                  (inf_env_inf_v_fupd (K (nsBind x (0,Infer_Tuvar (infer_st_next_uvar st))
                     (inf_env_inf_v ienv))) ienv) tenv
                  (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar (infer_st_next_uvar st))))
                     tenvE)` ASSUME_TAC THENL
   [MATCH_MP_TAC env_rel_sound_extend0 THEN ASM_REWRITE_TAC[check_t_def] THEN
    CONJ_TAC THENL [INFER1AUX_IN_FDOM_TAC; INFER1AUX_WALK_CHECK_TAC];
    ALL_TAC] THEN
  INFER1AUX_IES_REST2_TAC THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN ASM_REWRITE_TAC[] THEN
  INFER1AUX_UVAR_CHECK_TAC;;

let INFER1AUX_IES_APP_TAC =
  INFER1AUX_IES_GEN_TAC THEN
  INFER1AUX_FWD_TAC constrain_op_sound THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
    check (fun th -> INFER1AUX_is_app "ienv_ok" (concl th))) THEN
  INFER1AUX_FWD_TAC (CONJUNCT1 (CONJUNCT2 infer_e_check_t)) THEN
  INFER1AUX_FWD_TAC constrain_op_check_t THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
  FIRST_ASSUM(fun th -> if INFER1AUX_is_app "type_es" (concl th)
                        then EXISTS_TAC (rand(concl th)) else failwith "") THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INFER1AUX_sc_check_freevars THEN ASM_MESON_TAC[LE_REFL];;

let INFER1AUX_IES_RULE_CLOSE_TAC =
  INFER1AUX_IES_GEN_TAC THEN INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
  ASM_REWRITE_TAC[];;

let INFER1AUX_IES_MAT_TAC =
  INFER1AUX_IES_NONEMPTY_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[type_pes_def]) THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if INFER1AUX_is_app "type_e" c && rand(rator c) = `e:exp`
    then EXISTS_TAC (rand c) else failwith "") THEN
  ASM_REWRITE_TAC[];;

let INFER1AUX_IES_LET_TAC =
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `xo:mlstring option` (cases "option")) THEN
  REWRITE_TAC[nsOptBind_def; opt_bind_name_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[INFER1AUX_ienv_fupd_id] THEN
  REPEAT STRIP_TAC THEN INFER1AUX_IES_EXPAND_TAC [nsOptBind_def; INFER1AUX_ienv_fupd_id] THEN
  INFER1AUX_IES_REST1_TAC THENL
   [INFER1AUX_IES_REST2_TAC THEN INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
    FIRST_ASSUM(fun th -> let c = concl th in
      if INFER1AUX_is_app "type_e" c && rand(rator c) = `e1:exp`
      then EXISTS_TAC (rand c) else failwith "") THEN
    REWRITE_TAC[opt_bind_name_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
      check (fun th -> concl th = `ienv_ok (count (infer_st_next_uvar st)) ienv`)) THEN
    INFER1AUX_FWD_TAC (CONJUNCT1 infer_e_check_t) THEN
    SUBGOAL_THEN `ienv_ok (count (infer_st_next_uvar st''))
                    (inf_env_inf_v_fupd (K (nsBind a (0,v') (inf_env_inf_v ienv))) ienv)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INFER1AUX_ienv_ok_bind THEN EXISTS_TAC `infer_st_next_uvar st` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `env_rel_sound s
                    (inf_env_inf_v_fupd (K (nsBind a (0,v') (inf_env_inf_v ienv))) ienv) tenv
                    (Bind_name a 0 (convert_t (t_walkstar s v')) tenvE)` ASSUME_TAC THENL
     [MATCH_MP_TAC env_rel_sound_extend0 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INFER1AUX_sc_check_t_fdom THEN ASM_MESON_TAC[LE_REFL];
        INFER1AUX_WALK_CHECK_TAC];
      ALL_TAC] THEN
    INFER1AUX_IES_REST2_TAC THEN INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN
    EXISTS_TAC `convert_t (t_walkstar s v')` THEN
    REWRITE_TAC[opt_bind_name_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];;

let INFER1AUX_IES_LETREC_TAC =
  REPEAT STRIP_TAC THEN INFER1AUX_IES_EXPAND_TAC [] THEN INFER1AUX_IES_REST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
    check (fun th -> concl th = `ienv_ok (count (infer_st_next_uvar st)) ienv`)) THEN
  (fun (asl,w as gl) ->
    let ths = map snd asl in
    let run = find (fun th -> try INFER1AUX_is_app "infer_funs" (lhs(concl th))
                              with Failure _ -> false) ths in
    let ie = el 1 (snd(strip_comb(lhs(concl run)))) in
    let g1 = vsubst [ie, `IE:inf_env`]
      `ienv_ok (count (infer_st_next_uvar st + LENGTH (funs:(mlstring#mlstring#exp)list))) IE` in
    let g3 = vsubst [ie, `IE:inf_env`] (CASE_TERM
      `env_rel_sound s IE tenv
         (bind_var_list 0
            (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
               (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (infer_st_next_uvar st + n))))
                  (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))) tenvE)`) in
    (SUBGOAL_THEN g1 ASSUME_TAC THENL
      [REWRITE_TAC[INFER1AUX_ienv_ok_upd] THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_letrec THEN ASM_REWRITE_TAC[LE_REFL];
       ALL_TAC] THEN
     SUBGOAL_THEN g3 ASSUME_TAC THENL
      [MATCH_MP_TAC env_rel_e_sound_letrec_merge0 THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
        [INFER1AUX_WALK_CHECK_TAC;
         REWRITE_TAC[SUBSET; IN_COUNT] THEN REPEAT STRIP_TAC THEN INFER1AUX_IN_FDOM_TAC];
       ALL_TAC]) gl) THEN
  INFER1AUX_IENV_TAC THEN INFER1AUX_IES_REST2_TAC THEN
  INFER1AUX_FWD_TAC infer_funs_length THEN
  INFER1AUX_FWD_TAC INFER1AUX_ies_letrec_final THEN FIRST_ASSUM ACCEPT_TAC;;

let INFER1AUX_IES_TANNOT_TAC =
  INFER1AUX_IES_GEN_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
    check (fun th -> concl th = `ienv_ok (count (infer_st_next_uvar st)) ienv`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[env_rel_sound_def] o
    check (fun th -> INFER1AUX_is_app "env_rel_sound" (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> concl th = `inf_env_inf_t ienv = type_env_t tenv`)) THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `type_env_t tenv`; `t:ast_t`] INFER1AUX_tannot_type2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN REWRITE_TAC[eq]) THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN ASM_REWRITE_TAC[];;

let INFER1AUX_IES_ESCONS_TAC =
  INFER1AUX_IES_GEN_TAC THEN REWRITE_TAC[o_THM] THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN ASM_REWRITE_TAC[];;

let INFER1AUX_IES_PESNIL_TAC =
  INFER1AUX_IES_GEN_TAC THEN REWRITE_TAC[type_pes_def; MEM];;

let INFER1AUX_IES_FUNSNIL_TAC =
  INFER1AUX_IES_GEN_TAC THEN REWRITE_TAC[MAP2] THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules;;

let INFER1AUX_IES_PESCONS_TAC =
  REPEAT STRIP_TAC THEN INFER1AUX_IES_EXPAND_TAC [] THEN INFER1AUX_IES_REST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
    check (fun th -> concl th = `ienv_ok (count (infer_st_next_uvar st)) ienv`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[env_rel_sound_def] o
    check (fun th -> INFER1AUX_is_app "env_rel_sound" (concl th))) THEN
  INFER1AUX_FWDS_TAC (CONJUNCT1 infer_p_check_t) THEN
  INFER1AUX_FWDS_TAC (CONJUNCT1 infer_p_bindings) THEN
  (fun (asl,w as gl) ->
    let ths = map snd asl in
    let prun = find (fun th -> try INFER1AUX_is_app "infer_p" (lhs(concl th))
                               with Failure _ -> false) ths in
    let r = rhs(concl prun) in
    let env = rand(rand(rand(rator r))) and sto = rand r in
    let erun = find (fun th -> try INFER1AUX_is_app "infer_e" (lhs(concl th))
                               with Failure _ -> false) ths in
    let ie = el 1 (snd(strip_comb(lhs(concl erun)))) in
    let g1 = vsubst [ie, `IE:inf_env`; sto, `STO:infer_st`]
      `ienv_ok (count (infer_st_next_uvar STO)) IE` in
    let g2 = vsubst [ie, `IE:inf_env`; env, `ENV:(mlstring#infer_t)list`]
      `env_rel_sound s IE tenv (bind_var_list 0 (convert_env s ENV) tenvE)` in
    (SUBGOAL_THEN g1 ASSUME_TAC THENL
      [REWRITE_TAC[INFER1AUX_ienv_ok_upd] THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_pes THEN
       ASM_REWRITE_TAC[GSYM every_shim] THEN
       MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN
       EXISTS_TAC `infer_st_next_uvar st` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN g2 ASSUME_TAC THENL
      [MATCH_MP_TAC env_rel_sound_merge0 THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
        [INFER1AUX_WALK_CHECK_TAC;
         REWRITE_TAC[every_shim; ETA_AX] THEN
         MATCH_MP_TAC INFER1AUX_sc_all_check_t_fdom THEN
         RULE_ASSUM_TAC(REWRITE_RULE[every_shim; ETA_AX]) THEN
         ASM_MESON_TAC[LE_REFL]];
       ALL_TAC]) gl) THEN
  INFER1AUX_IENV_TAC THEN INFER1AUX_IES_REST2_TAC THEN
  SUBGOAL_THEN `tenv_ctor_ok (type_env_c tenv) /\ tenv_abbrev_ok (type_env_t tenv)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  INFER1AUX_FWDS_TAC (CONJUNCT1 infer_p_sound) THEN
  REWRITE_TAC[type_pes_cons] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_ASSUM(fun th -> if INFER1AUX_is_app "type_p" (concl th)
                          then EXISTS_TAC (rand(concl th)) else failwith "") THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];;

let INFER1AUX_IES_FUNSCONS_TAC =
  REPEAT STRIP_TAC THEN INFER1AUX_IES_EXPAND_TAC [] THEN INFER1AUX_IES_REST1_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[MAP; ALL_DISTINCT; FST] o
    check (fun th -> INFER1AUX_is_app "ALL_DISTINCT" (concl th))) THEN
  SUBGOAL_THEN `ienv_ok (count (infer_st_next_uvar st + 1))
                  (inf_env_inf_v_fupd (K (nsBind x (0,Infer_Tuvar (infer_st_next_uvar st))
                     (inf_env_inf_v ienv))) ienv)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ienv_ok_bind THEN EXISTS_TAC `infer_st_next_uvar st` THEN
    ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `env_rel_sound s
                  (inf_env_inf_v_fupd (K (nsBind x (0,Infer_Tuvar (infer_st_next_uvar st))
                     (inf_env_inf_v ienv))) ienv) tenv
                  (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar (infer_st_next_uvar st))))
                     tenvE)` ASSUME_TAC THENL
   [MATCH_MP_TAC env_rel_sound_extend0 THEN ASM_REWRITE_TAC[check_t_def] THEN
    CONJ_TAC THENL [INFER1AUX_IN_FDOM_TAC; INFER1AUX_WALK_CHECK_TAC];
    ALL_TAC] THEN
  INFER1AUX_IES_REST2_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
    check (fun th -> concl th = `ienv_ok (count (infer_st_next_uvar st + 1))
                  (inf_env_inf_v_fupd (K (nsBind x (0,Infer_Tuvar (infer_st_next_uvar st))
                     (inf_env_inf_v ienv))) ienv)`)) THEN
  INFER1AUX_FWD_TAC (CONJUNCT1 infer_e_check_t) THEN
  INFER1AUX_FWD_TAC infer_funs_length THEN
  REWRITE_TAC[MAP2] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP; convert_t_def] THEN
  INFER1AUX_ES_RULE_TAC INFER1AUX_type_e_rules THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[check_freevars_def; ALL] THEN CONJ_TAC THENL
     [INFER1AUX_UVAR_CHECK_TAC;
      MATCH_MP_TAC INFER1AUX_sc_check_freevars THEN ASM_MESON_TAC[LE_REFL]];
    REWRITE_TAC[ALOOKUP_NONE] THEN ASM_SIMP_TAC[INFER1AUX_map_fst_map2]];;

let infer_e_sound = prove
 (CASE_TERM
 `(!l ienv e st st' tenv tenvE t extra_constraints s.
     infer_e l ienv e st = (M_success t,st') /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\
     env_rel_sound s ienv tenv tenvE /\
     t_wfs (infer_st_subst st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s
     ==> type_e tenv tenvE e (convert_t (t_walkstar s t))) /\
  (!l ienv es st st' tenv tenvE ts extra_constraints s.
     infer_es l ienv es st = (M_success ts,st') /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\
     env_rel_sound s ienv tenv tenvE /\
     t_wfs (infer_st_subst st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s
     ==> type_es tenv tenvE es (MAP (convert_t o t_walkstar s) ts)) /\
  (!l ienv pes t1 t2 st st' tenv tenvE extra_constraints s.
     infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\
     env_rel_sound s ienv tenv tenvE /\
     t_wfs (infer_st_subst st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s
     ==> type_pes (num_tvs tenvE) 0 tenv tenvE pes (convert_t (t_walkstar s t1))
           (convert_t (t_walkstar s t2))) /\
  (!l ienv funs st st' tenv tenvE extra_constraints s ts.
     infer_funs l ienv funs st = (M_success ts,st') /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\
     env_rel_sound s ienv tenv tenvE /\
     t_wfs (infer_st_subst st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
       extra_constraints s /\
     ALL_DISTINCT (MAP FST funs)
     ==> type_funs tenv tenvE funs
           (MAP2 (\xyz t. match xyz with (x,y,z) -> (x,(convert_t o t_walkstar s) t))
              funs ts))`,
  MATCH_MP_TAC infer_e_ind THEN REPEAT CONJ_TAC THENL
   [INFER1AUX_IES_RAISE_TAC; INFER1AUX_IES_HANDLE_TAC;
    INFER1AUX_IES_LIT_TAC; INFER1AUX_IES_LIT_TAC; INFER1AUX_IES_LIT_TAC;
    INFER1AUX_IES_LIT_TAC; INFER1AUX_IES_LIT_TAC; INFER1AUX_IES_LIT_TAC;
    INFER1AUX_IES_VAR_TAC; INFER1AUX_IES_CON_TAC; INFER1AUX_IES_FUN_TAC;
    INFER1AUX_IES_APP_TAC; INFER1AUX_IES_RULE_CLOSE_TAC; INFER1AUX_IES_RULE_CLOSE_TAC;
    INFER1AUX_IES_MAT_TAC; INFER1AUX_IES_LET_TAC; INFER1AUX_IES_LETREC_TAC;
    INFER1AUX_IES_TANNOT_TAC; INFER1AUX_IES_RULE_CLOSE_TAC;
    INFER1AUX_IES_RULE_CLOSE_TAC; INFER1AUX_IES_ESCONS_TAC;
    INFER1AUX_IES_PESNIL_TAC; INFER1AUX_IES_PESCONS_TAC;
    INFER1AUX_IES_FUNSNIL_TAC; INFER1AUX_IES_FUNSCONS_TAC]);;
