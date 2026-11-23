(* ========================================================================= *)
(* envRel: port of HOL4 compiler/inference/proofs/envRelScript.sml (CakeML   *)
(* v3479).  Relating inference and type system environments.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
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

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Records: ienv.inf_v is inf_env_inf_v ienv, tenv.v is type_env_v tenv,   *)
(*   r with f := v is R_f_fupd (K v) r, record literals are R_REC.           *)
(* - HOL4 EVERY is ALL, set is set_of_list, ZIP (l1,l2) is ZIP l1 l2.        *)
(* - The free variables of a HOL4 statement are universally quantified.      *)
(* - HOL4 infer_t_induction and t_induction (mutual induction over types     *)
(*   and type lists) are infer_t_INDUCT and t_INDUCT.                        *)
(* - Helper lemmas that are not HOL4 theorems are INFER1AUX_.                *)
(* ------------------------------------------------------------------------- *)

(* ---------- Converting infer types and envs to type system ones ---------- *)

let convert_t_def = cake_def
  `(convert_t (Infer_Tvar_db n) = Tvar_db n) /\
   (convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc)`;;

let convert_t_ind = cake_ind "convert_t";;

let convert_env_def = cake_def
  `convert_env (s:(num,infer_t)fmap) (env:(A#infer_t)list) =
     MAP (\p. match p with (x,t) -> (x,convert_t (t_walkstar s t))) env`;;

let check_convert_freevars = prove
 (`!tvs (uvs:num->bool) t.
     check_t tvs uvs t ==> uvs = {} ==> check_freevars tvs [] (convert_t t)`,
  MATCH_MP_TAC check_t_ind THEN
  RW[check_freevars_def; check_t_def; convert_t_def] THEN
  FS[EVERY_MEM; MEM_MAP] THEN ASM_METIS_TAC[]);;

let check_t_to_check_freevars = prove
 (`!tvs (n:num->bool) t. check_t tvs {} t ==> check_freevars tvs [] (convert_t t)`,
  MATCH_MP_TAC check_t_ind THEN
  RW[check_t_def; check_freevars_def; convert_t_def; EVERY_MAP] THEN
  FS[EVERY_MEM]);;

let convert_inc = prove
 (`!t tvs tvs'.
     check_t tvs' {} t
     ==> convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (convert_t t)`,
  MATCH_MP_TAC convert_t_ind THEN
  RW[check_t_def; convert_t_def; infer_deBruijn_inc_def; deBruijn_inc_def; LT] THEN
  FS[MAP_MAP_o; MAP_EQ_f; EVERY_MEM; o_THM] THEN ASM_METIS_TAC[]);;

let db_subst_infer_subst_swap = prove
 (`(!t (s:(num,infer_t)fmap) tvs uvar n.
     t_wfs s /\
     pred_set_count (uvar + tvs) SUBSET FDOM s /\
     (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
     check_t tvs (FDOM s) t
     ==> convert_t (t_walkstar s (infer_deBruijn_subst
                    (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)) t)) =
         deBruijn_subst 0 (MAP (convert_t o t_walkstar s)
                             (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
           (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t))) /\
   (!ts (s:(num,infer_t)fmap) tvs uvar n.
     t_wfs s /\
     pred_set_count (uvar + tvs) SUBSET FDOM s /\
     (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
     ALL (\t. check_t tvs (FDOM s) t) ts
     ==> MAP (convert_t o t_walkstar s o
              infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) ts =
         MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s)
                (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) o
              convert_t o t_walkstar (infer_deBruijn_inc tvs o_f s)) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `t_wfs (infer_deBruijn_inc tvs o_f (s:(num,infer_t)fmap))` ASSUME_TAC
   THENL [ASM_MESON_TAC[inc_wfs]; ALL_TAC]) THENL
  [FS[check_t_def; t_walkstar_eqn1; infer_deBruijn_subst_alt; convert_t_def; LT;
      deBruijn_subst_def; LENGTH_MAP; LENGTH_COUNT_LIST; el_map_count; EL_MAP;
      MAP_MAP_o; o_THM];
   RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o]) THEN
   ASM_SIMP_TAC[t_walkstar_eqn1; infer_deBruijn_subst_alt; convert_t_def;
                deBruijn_subst_def; MAP_MAP_o; injectivity "t"] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[check_t_def]) THEN ASM_REWRITE_TAC[ETA_AX];
   REWRITE_TAC[infer_deBruijn_subst_alt] THEN ASM_SIMP_TAC[walkstar_inc2] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[check_t_def]) THEN
   SUBGOAL_THEN `check_t n {} (t_walkstar (s:(num,infer_t)fmap) (Infer_Tuvar a))`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP convert_inc th]) THEN
   MP_TAC(ISPECL [`convert_t (t_walkstar (s:(num,infer_t)fmap) (Infer_Tuvar a))`;
                  `MAP (convert_t o t_walkstar (s:(num,infer_t)fmap))
                     (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))`; `0`]
                 (CONJUNCT1 subst_inc_cancel)) THEN
   REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; ADD_CLAUSES; deBruijn_inc0] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]);
   REWRITE_TAC[MAP];
   REWRITE_TAC[MAP; CONS_11; o_THM] THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
   ASM_MESON_TAC[]]);;

let inc_convert_t = prove
 (`(!t tvs' tvs. check_t tvs' {} t ==> deBruijn_inc tvs' tvs (convert_t t) = convert_t t) /\
   (!ts tvs' tvs. ALL (check_t tvs' {}) ts
                  ==> MAP (deBruijn_inc tvs' tvs o convert_t) ts = MAP convert_t ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; convert_t_def; deBruijn_inc_def; NOT_IN_EMPTY; MAP; ALL;
              o_THM; CONS_11; injectivity "t"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MAP_MAP_o]);;

let convert_t_subst = prove
 (`(!t tvs ts'.
      LENGTH tvs = LENGTH ts' /\ check_freevars 0 tvs t
      ==> convert_t (infer_type_subst (ZIP tvs ts') t) =
          type_subst (alist_to_fmap (ZIP tvs (MAP convert_t ts'))) t) /\
   (!ts tvs ts'.
      LENGTH tvs = LENGTH ts' /\ ALL (check_freevars 0 tvs) ts
      ==> MAP convert_t (MAP (infer_type_subst (ZIP tvs ts')) ts) =
          MAP (type_subst (alist_to_fmap (ZIP tvs (MAP convert_t ts')))) ts)`,
  MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[check_freevars_def; convert_t_def; type_subst_def; infer_type_subst_alt;
              MAP; ALL; CONS_11; injectivity "t"] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
  [ASM_SIMP_TAC[ALOOKUP_EQ_FLOOKUP; ALOOKUP_ZIP_MAP_SND; o_THM] THEN
   CASES_ON `ALOOKUP (ZIP (tvs:mlstring list) (ts':infer_t list)) a` THEN
   CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALOOKUP_NONE]) THEN ASM_SIMP_TAC[MAP_ZIP];
   ASM_SIMP_TAC[];
   ASM_SIMP_TAC[]]);;

let deBruijn_subst_convert = prove
 (`!n subst.
     (!t. check_t n {} t
          ==> deBruijn_subst 0 (MAP convert_t subst) (convert_t t) =
              convert_t (infer_deBruijn_subst subst t)) /\
     (!ts. ALL (check_t n {}) ts
           ==> MAP (deBruijn_subst 0 (MAP convert_t subst) o convert_t) ts =
               MAP (convert_t o infer_deBruijn_subst subst) ts)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; NOT_IN_EMPTY; MAP; ALL; CONS_11; o_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[convert_t_def; deBruijn_subst_def; infer_deBruijn_subst_alt; LT;
               ADD_CLAUSES; SUB_0; LENGTH_MAP; injectivity "t"] THENL
  [COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MAP; convert_t_def];
   ASM_SIMP_TAC[MAP_MAP_o]]);;

let check_freevars_empty_convert_unconvert_id = prove
 (`!n t. check_freevars n [] t ==> convert_t (unconvert_t t) = t`,
  GEN_TAC THEN MATCH_MP_TAC unconvert_t_ind THEN
  RW[unconvert_t_def; convert_t_def; check_freevars_def] THEN
  FS[MAP_MAP_o; MAP_EQ_ID; EVERY_MEM; o_THM]);;

let check_t_empty_unconvert_convert_id = prove
 (`!t n. check_t n {} t ==> unconvert_t (convert_t t) = t`,
  MATCH_MP_TAC convert_t_ind THEN
  RW[unconvert_t_def; convert_t_def; check_t_def] THEN
  FS[MAP_MAP_o; MAP_EQ_ID; EVERY_MEM; o_THM] THEN ASM_METIS_TAC[]);;

let check_freevars_to_check_t = prove
 (`!n t (z:A). check_freevars n [] t ==> check_t n {} (unconvert_t t)`,
  GEN_TAC THEN MATCH_MP_TAC unconvert_t_ind THEN
  RW[unconvert_t_def; check_freevars_def; check_t_def] THEN
  FS[EVERY_MAP; EVERY_MEM]);;

let infer_type_subst_nil = prove
 (`!n. (!t. check_freevars n [] t ==> infer_type_subst [] t = unconvert_t t) /\
       (!ts. ALL (check_freevars n []) ts
             ==> MAP (infer_type_subst []) ts = MAP unconvert_t ts)`,
  GEN_TAC THEN MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[infer_type_subst_alt; unconvert_t_def; check_freevars_def; MEM;
              MAP; ALL; CONS_11; injectivity "infer_t"] THEN
  MESON_TAC[]);;

(* ---------- relating inference and type system environments ---------- *)

(* tscheme_approx max_tvs s (tvs,t) (tvs',t') holds iff (tvs',t') is more   *)
(* general than (tvs,t) under the substitution s constraining unification   *)
(* variables (see the long comment of the HOL4 script).                     *)

let tscheme_approx_def = cake_def
  `tscheme_approx (max_tvs:num) (s:(num,infer_t)fmap) ((tvs:num),(t:infer_t))
                  ((tvs':num),(t':infer_t)) <=>
     ?subst'.
       LENGTH subst' = tvs' /\
       ALL (check_t (max_tvs + tvs) (FDOM s)) subst' /\
       !subst.
         LENGTH subst = tvs
         ==> t_walkstar s (infer_deBruijn_subst subst t) =
             t_walkstar s (infer_deBruijn_subst (MAP (infer_deBruijn_subst subst) subst') t')`;;

let tscheme_approx_thm = prove
 (`!t' max_tvs (s:(num,infer_t)fmap) tvs tvs' t.
     t_wfs s
     ==> tscheme_approx max_tvs s (tvs,t) (tvs',t')
         ==> !subst.
               LENGTH subst = tvs /\ ALL (check_t max_tvs {}) subst
               ==> ?subst'.
                     LENGTH subst' = tvs' /\
                     ALL (check_t max_tvs (FDOM s)) subst' /\
                     t_walkstar s (infer_deBruijn_subst subst t) =
                     t_walkstar s (infer_deBruijn_subst subst' t')`,
  REWRITE_TAC[tscheme_approx_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `MAP (infer_deBruijn_subst subst) (subst':infer_t list)` THEN
  ASM_SIMP_TAC[LENGTH_MAP; EVERY_MAP] THEN
  UNDISCH_TAC `ALL (check_t (max_tvs + tvs) (FDOM (s:(num,infer_t)fmap))) subst'` THEN
  REWRITE_TAC[EVERY_MEM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC check_t_infer_deBruijn_subst THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(MATCH_MP (CONJUNCT2 check_t_more5)
    (ASSUME `ALL (check_t max_tvs {}) (subst:infer_t list)`)) THEN
  REWRITE_TAC[EMPTY_SUBSET]);;

let tscheme_approx_refl = prove
 (`!max_tvs (s:(num,infer_t)fmap) tvs t. tscheme_approx max_tvs s (tvs,t) (tvs,t)`,
  REWRITE_TAC[tscheme_approx_def] THEN REPEAT GEN_TAC THEN
  EXISTS_TAC `MAP Infer_Tvar_db (COUNT_LIST tvs)` THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; EVERY_MAP; every_count_list; check_t_def] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; EL_MAP; EL_COUNT_LIST;
               infer_deBruijn_subst_alt]);;

(* HOL4 comment: should be able to use max_tvs in place of 0 *)
let tscheme_approx_trans = prove
 (`!max_tvs (s:(num,infer_t)fmap) tvs1 t1 tvs2 t2 tvs3 t3.
     tscheme_approx max_tvs s (tvs1,t1) (tvs2,t2) /\
     tscheme_approx 0 s (tvs2,t2) (tvs3,t3)
     ==> tscheme_approx max_tvs s (tvs1,t1) (tvs3,t3)`,
  REWRITE_TAC[tscheme_approx_def; ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `MAP (infer_deBruijn_subst subst') (subst'':infer_t list)` THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EVERY_MAP] THEN
    UNDISCH_TAC `ALL (check_t tvs2 (FDOM (s:(num,infer_t)fmap))) subst''` THEN
    MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC `y:infer_t` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC check_t_infer_deBruijn_subst THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `max_tvs + tvs1` o MATCH_MP (CONJUNCT1 check_t_more2)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `MAP (infer_deBruijn_subst subst) (subst':infer_t list)`) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MAP_MAP_o] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(GSYM(CONJUNCT2(ISPECL [`subst:infer_t list`; `subst':infer_t list`;
    `FDOM (s:(num,infer_t)fmap)`] infer_deBruijn_subst_twice))) THEN
  ASM_REWRITE_TAC[]);;

let unconvert_db_subst = prove
 (`!t subst (fvs:A) l.
     check_freevars l [] t
     ==> unconvert_t (deBruijn_subst 0 subst t) =
         infer_deBruijn_subst (MAP unconvert_t subst) (unconvert_t t)`,
  MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[deBruijn_subst_def; unconvert_t_def; infer_deBruijn_subst_alt;
              check_freevars_def; MEM; LT; ADD_CLAUSES; SUB_0; LENGTH_MAP] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MAP; unconvert_t_def];
    DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[unconvert_t_def; MAP_MAP_o; injectivity "infer_t"] THEN
    REWRITE_TAC[MAP_EQ_f; o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN ASM_MESON_TAC[]]);;

let tscheme_inst_to_approx = prove
 (`!tvs t tvs' t'.
     tscheme_inst (tvs,t) (tvs',t')
     ==> tscheme_approx 0 FEMPTY (tvs,unconvert_t t) (tvs',unconvert_t t')`,
  REWRITE_TAC[tscheme_inst_def; tscheme_approx_def; t_walkstar_FEMPTY; FDOM_FEMPTY;
              ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `MAP unconvert_t (subst:t list)` THEN
  ASM_REWRITE_TAC[LENGTH_MAP; EVERY_MAP] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ALL (check_freevars tvs []) (subst:t list)` THEN
    MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_MESON_TAC[check_freevars_to_check_t];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "t" THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP unconvert_db_subst th]) THEN
  SUBGOAL_THEN `check_t (LENGTH (MAP unconvert_t (subst:t list))) {} (unconvert_t t')`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_MESON_TAC[check_freevars_to_check_t];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONJUNCT1(ISPECL [`subst':infer_t list`; `MAP unconvert_t (subst:t list)`;
                                 `{}:num->bool`] infer_deBruijn_subst_twice)] THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF]);;

let env_rel_sound_def = cake_def
  `env_rel_sound (s:(num,infer_t)fmap) (ienv:inf_env) (tenv:type_env)
                 (tenvE:tenv_val_exp) <=>
     inf_env_inf_t ienv = type_env_t tenv /\
     inf_env_inf_c ienv = type_env_c tenv /\
     !x ts.
       nsLookup (inf_env_inf_v ienv) x = SOME ts
       ==> ?tvs' t'.
             check_freevars (tvs' + num_tvs tenvE) [] t' /\
             lookup_var x tenvE tenv = SOME (tvs',t') /\
             tscheme_approx (num_tvs tenvE) s ts (tvs',unconvert_t t')`;;

let env_rel_sound_lookup_none = prove
 (`!ienv tenv (s:(num,infer_t)fmap) tenvE id.
     env_rel_sound s ienv tenv tenvE /\ lookup_var id tenvE tenv = NONE
     ==> nsLookup (inf_env_inf_v ienv) id = NONE`,
  REWRITE_TAC[env_rel_sound_def] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[option_DISTINCT; cases "option"]);;

let env_rel_sound_lookup_some = prove
 (`!id ts (s:(num,infer_t)fmap) ienv tenv tenvE.
     nsLookup (inf_env_inf_v ienv) id = SOME ts /\ env_rel_sound s ienv tenv tenvE
     ==> ?tvs' t'.
           check_freevars (tvs' + num_tvs tenvE) [] t' /\
           lookup_var id tenvE tenv = SOME (tvs',t') /\
           tscheme_approx (num_tvs tenvE) s ts (tvs',unconvert_t t')`,
  REWRITE_TAC[env_rel_sound_def] THEN MESON_TAC[]);;

let db_subst_infer_subst_swap3 = prove
 (`!t tvs (s:(num,infer_t)fmap) subst.
     t_wfs s /\ check_freevars tvs [] t
     ==> convert_t (t_walkstar s (infer_deBruijn_subst subst (unconvert_t t))) =
         deBruijn_subst 0 (MAP (convert_t o t_walkstar s) subst) t`,
  MATCH_MP_TAC unconvert_t_ind THEN
  REWRITE_TAC[unconvert_t_def; check_freevars_def; MEM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN
    REWRITE_TAC[infer_deBruijn_subst_alt; deBruijn_subst_def; LT; ADD_CLAUSES; SUB_0;
                LENGTH_MAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MAP; o_THM; t_walkstar_eqn1; convert_t_def];
    DISCH_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[infer_deBruijn_subst_alt; deBruijn_subst_def; t_walkstar_eqn1;
                 convert_t_def; injectivity "t"; MAP_MAP_o] THEN
    REWRITE_TAC[MAP_EQ_f; o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MEM]) THEN ASM_MESON_TAC[]]);;

let tscheme_approx_weakening = prove
 (`!tvs tvs' (s1:(num,infer_t)fmap) s2 ts1 ts2.
     tscheme_approx tvs s1 ts1 ts2 /\ t_wfs s2 /\ s1 SUBMAP s2 /\ tvs <= tvs'
     ==> tscheme_approx tvs' s2 ts1 ts2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `ts1:num#infer_t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:infer_t` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ts2:num#infer_t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q':num` (X_CHOOSE_THEN `r':infer_t` SUBST1_TAC)) THEN
  REWRITE_TAC[tscheme_approx_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `subst':infer_t list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `tvs' + q = (tvs' - tvs) + (tvs + q)` SUBST1_TAC THENL
     [UNDISCH_TAC `tvs <= tvs':num` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(MATCH_MP (CONJUNCT2 check_t_more5) (SPEC `tvs' - tvs`
      (MATCH_MP (CONJUNCT2 check_t_more2)
        (ASSUME `ALL (check_t (tvs + q) (FDOM (s1:(num,infer_t)fmap))) subst'`)))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[SUBMAP_FDOM_SUBSET];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `subst:infer_t list`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[t_walkstar_SUBMAP]]);;

let INFER1AUX_lookup_varE_bind_tvar_Empty = prove
 (`!(y:(mlstring,mlstring)id) n.
     lookup_varE y (bind_tvar n Empty) = NONE /\ lookup_varE y Empty = NONE`,
  MATCH_MP_TAC id_INDUCT THEN REWRITE_TAC[lookup_varE_def; bind_tvar_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[tveLookup_def]);;

let env_rel_sound_extend_tvs = prove
 (`!(s:(num,infer_t)fmap) ienv tenv (bindings:A) tvs.
     t_wfs s /\ env_rel_sound s ienv tenv Empty
     ==> env_rel_sound s ienv tenv (bind_tvar tvs Empty)`,
  REWRITE_TAC[env_rel_sound_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:(mlstring,mlstring)id`; `ts:num#infer_t`]) THEN
  ASM_REWRITE_TAC[num_tvs_def; ADD_CLAUSES] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tvs':num`; `t':t`] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[lookup_var_def; INFER1AUX_lookup_varE_bind_tvar_Empty]) THEN
  CASE_REWRITE_TAC[lookup_var_def; INFER1AUX_lookup_varE_bind_tvar_Empty] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC;
    MATCH_MP_TAC tscheme_approx_weakening THEN
    MAP_EVERY EXISTS_TAC [`0`; `s:(num,infer_t)fmap`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL; LE_0]]);;

let tscheme_approx0 = prove
 (`!tvs (s:(num,infer_t)fmap) t. t_wfs s ==> tscheme_approx tvs s (0,t) (0,t_walkstar s t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tscheme_approx_def] THEN
  EXISTS_TAC `[]:infer_t list` THEN
  REWRITE_TAC[LENGTH; ALL; LENGTH_NIL; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[infer_deBruijn_subst_id] THEN ASM_SIMP_TAC[t_walkstar_idempotent]);;

let INFER1AUX_lookup_var_Bind_name_other = prove
 (`!(y:(mlstring,mlstring)id) x tvs t tenvE tenv.
     ~(y = Short x)
     ==> lookup_var y (Bind_name x tvs t tenvE) tenv = lookup_var y tenvE tenv`,
  MATCH_MP_TAC id_INDUCT THEN
  REWRITE_TAC[lookup_var_def; lookup_varE_def; tveLookup_def; injectivity "id"] THEN
  CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let env_rel_sound_extend0 = prove
 (`!(s:(num,infer_t)fmap) x t ienv tenv tenvE.
     env_rel_sound s ienv tenv tenvE /\ t_wfs s /\
     check_t (num_tvs tenvE) (FDOM s) t /\
     (!uv. uv IN FDOM s ==> check_t (num_tvs tenvE) {} (t_walkstar s (Infer_Tuvar uv)))
     ==> env_rel_sound s
           (inf_env_inf_v_fupd (K (nsBind x (0,t) (inf_env_inf_v ienv))) ienv)
           tenv (Bind_name x 0 (convert_t (t_walkstar s t)) tenvE)`,
  REWRITE_TAC[env_rel_sound_def; inf_env_INFO.ri_accfupds; K_THM; num_tvs_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:(mlstring,mlstring)id`; `ts:num#infer_t`] THEN
  ASM_CASES_TAC `(y:(mlstring,mlstring)id) = Short x` THENL
   [ASM_REWRITE_TAC[nsLookup_nsBind; injectivity "option"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `check_t (num_tvs tenvE) {} (t_walkstar (s:(num,infer_t)fmap) t)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 check_t_walkstar) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`0`; `convert_t (t_walkstar (s:(num,infer_t)fmap) t)`] THEN
    REWRITE_TAC[lookup_var_def; lookup_varE_def; tveLookup_def; deBruijn_inc0] THEN
    CASE_REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP check_t_empty_unconvert_convert_id th]) THEN
    ASM_SIMP_TAC[check_t_to_check_freevars; tscheme_approx0];
    ASM_SIMP_TAC[nsLookup_nsBind; INFER1AUX_lookup_var_Bind_name_other]]);;

let env_rel_sound_merge0 = prove
 (CASE_TERM `!(s:(num,infer_t)fmap) ienv (bindings:(mlstring#infer_t)list) tenv tenvE.
     t_wfs s /\
     (!uv. uv IN FDOM s ==> check_t (num_tvs tenvE) {} (t_walkstar s (Infer_Tuvar uv))) /\
     ALL (\(x,t). check_t 0 (FDOM s) t) bindings /\
     env_rel_sound s ienv tenv tenvE
     ==> env_rel_sound s
           (inf_env_inf_v_fupd
              (K (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) bindings))
                           (inf_env_inf_v ienv))) ienv)
           tenv (bind_var_list 0 (convert_env s bindings) tenvE)`,
  REWRITE_TAC[env_rel_sound_def; inf_env_INFO.ri_accfupds; K_THM; num_tvs_bind_var_list] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:(mlstring,mlstring)id`; `ts:num#infer_t`] THEN
  REWRITE_TAC[nsLookup_nsAppend_some; nsLookup_alist_to_ns_some; nsLookup_alist_to_ns_none;
              NSPAUX_ALOOKUP_MAP; OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE] THEN
  STRIP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    SUBGOAL_THEN `check_t (num_tvs tenvE) {} (t_walkstar (s:(num,infer_t)fmap) z)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 check_t_walkstar) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
      UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (FDOM (s:(num,infer_t)fmap)) t) bindings` THEN
      REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM] THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      DISCH_THEN(MP_TAC o SPEC `num_tvs tenvE` o MATCH_MP (CONJUNCT1 check_t_more2)) THEN
      REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`0`; `convert_t (t_walkstar (s:(num,infer_t)fmap) z)`] THEN
    REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[tveLookup_bvl; convert_env_def; NSPAUX_ALOOKUP_MAP] THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[deBruijn_inc0; ADD_CLAUSES] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP check_t_empty_unconvert_convert_id th]) THEN
    ASM_SIMP_TAC[check_t_to_check_freevars; tscheme_approx0];
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:(mlstring,mlstring)id`; `ts:num#infer_t`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`tvs':num`; `t':t`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lookup_var y tenvE tenv = SOME (tvs':num,t':t)` THEN
    UNDISCH_TAC `!x':mlstring. (y:(mlstring,mlstring)id) = Short x' ==> ALOOKUP (bindings:(mlstring#infer_t)list) x' = NONE` THEN
    SPEC_TAC(`y:(mlstring,mlstring)id`,`y:(mlstring,mlstring)id`) THEN
    MATCH_MP_TAC id_INDUCT THEN
    REWRITE_TAC[lookup_var_def; lookup_varE_def; tveLookup_bvl; convert_env_def;
                NSPAUX_ALOOKUP_MAP; injectivity "id"; distinctness "id"] THEN
    CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

let env_rel_e_sound_letrec_merge0 = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) ienv tenv tenvE (s:(num,infer_t)fmap) uvs.
     t_wfs s /\
     (!uv. uv IN FDOM s ==> check_t (num_tvs tenvE) {} (t_walkstar s (Infer_Tuvar uv))) /\
     pred_set_count (uvs + LENGTH funs) SUBSET FDOM s /\
     env_rel_sound s ienv tenv tenvE
     ==> env_rel_sound s
           (inf_env_inf_v_fupd
              (K (nsAppend
                    (alist_to_ns
                       (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar)))
                          funs (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH funs)))))
                    (inf_env_inf_v ienv))) ienv)
           tenv
           (bind_var_list 0
              (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) funs
                 (MAP (\n. convert_t (t_walkstar s (Infer_Tuvar (uvs + n))))
                    (COUNT_LIST (LENGTH funs))))
              tenvE)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; COUNT_LIST_def; MAP; MAP2; alist_to_ns_nil; nsAppend_nsEmpty;
                bind_var_list_def; ienv_unchanged] THEN MESON_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:mlstring`; `x:mlstring`; `e:exp`] THEN
  REWRITE_TAC[LENGTH; COUNT_LIST_def; MAP; MAP2] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[alist_to_ns_cons; nsAppend_nsBind; bind_var_list_def; MAP_MAP_o; o_DEF;
              ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
                                `s:(num,infer_t)fmap`; `SUC uvs`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(MP_TAC o SPECL [`f:mlstring`; `Infer_Tuvar uvs`] o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] env_rel_sound_extend0)) THEN
  SUBGOAL_THEN `uvs IN FDOM (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_COUNT; ARITH_RULE `uvs < SUC (uvs + n)`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[num_tvs_bind_var_list; check_t_def; inf_env_INFO.ri_accfupds;
                  inf_env_INFO.ri_fupdfupds; K_o_THM; K_THM]);;

let env_rel_complete_def = cake_def
  `env_rel_complete (s:(num,infer_t)fmap) (ienv:inf_env) (tenv:type_env)
                    (tenvE:tenv_val_exp) <=>
     inf_env_inf_t ienv = type_env_t tenv /\
     inf_env_inf_c ienv = type_env_c tenv /\
     !x tvs t.
       lookup_var x tenvE tenv = SOME (tvs,t)
       ==> (?n. check_freevars n [] t) /\
           ?tvs' t'.
             nsLookup (inf_env_inf_v ienv) x = SOME (tvs',t') /\
             tscheme_approx (num_tvs tenvE) s (tvs,unconvert_t t) (tvs',t')`;;

let env_rel_complete_lookup_none = prove
 (`!ienv tenv (s:(num,infer_t)fmap) tenvE x.
     env_rel_complete s ienv tenv tenvE /\ nsLookup (inf_env_inf_v ienv) x = NONE
     ==> nsLookup (type_env_v tenv) x = NONE`,
  REWRITE_TAC[env_rel_complete_def; lookup_var_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(mlstring,mlstring)id`) THEN
  CASES_ON `lookup_varE (x:(mlstring,mlstring)id) tenvE` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `nsLookup (type_env_v tenv) (x:(mlstring,mlstring)id)` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a:num#t` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x':num`; `y:t`]) THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let env_rel_e_sound_empty_to = prove
 (`!(s:(num,infer_t)fmap) ienv tenv tenvE.
     t_wfs s /\ ienv_ok {} ienv /\ env_rel_sound FEMPTY ienv tenv tenvE
     ==> env_rel_sound s ienv tenv tenvE`,
  REWRITE_TAC[env_rel_sound_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:(mlstring,mlstring)id`; `ts:num#infer_t`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tvs':num`; `t':t`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC tscheme_approx_weakening THEN
  MAP_EVERY EXISTS_TAC [`num_tvs tenvE`; `FEMPTY:(num,infer_t)fmap`] THEN
  ASM_REWRITE_TAC[SUBMAP_FEMPTY; LE_REFL]);;

(* Environment relation at infer_d and above *)

let envRel_env_rel_def = cake_def
  `envRel_env_rel (tenv:type_env) (ienv:inf_env) <=>
     ienv_ok {} ienv /\
     tenv_ok tenv /\
     (!x. nsLookupMod (inf_env_inf_v ienv) x = NONE <=>
          nsLookupMod (type_env_v tenv) x = NONE) /\
     env_rel_sound FEMPTY ienv tenv Empty /\
     env_rel_complete FEMPTY ienv tenv Empty`;;

let lookup_varE_empty = prove
 (`!x. lookup_varE x Empty = NONE`,
  REWRITE_TAC[INFER1AUX_lookup_varE_bind_tvar_Empty]);;
let _ = cake_add_simps [lookup_varE_empty];;

let INFER1AUX_lookup_var_Empty = prove
 (`!x tenv. lookup_var x Empty tenv = nsLookup (type_env_v tenv) x`,
  REWRITE_TAC[lookup_var_def; lookup_varE_empty] THEN CASE_REWRITE_TAC[]);;

let INFER1AUX_EXISTS_SOME = prove
 (`!x:A option. (?e. x = SOME e) <=> ~(x = NONE)`,
  MESON_TAC[cases "option"; option_DISTINCT]);;

let INFER1AUX_env_rel_lookup_none = prove
 (`!tenv ienv x.
     envRel_env_rel tenv ienv
     ==> (nsLookup (inf_env_inf_v ienv) x = NONE <=> nsLookup (type_env_v tenv) x = NONE)`,
  REWRITE_TAC[envRel_env_rel_def; env_rel_sound_def; env_rel_complete_def;
              INFER1AUX_lookup_var_Empty] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_MESON_TAC[option_DISTINCT; cases "option"; PAIR_SURJECTIVE]);;

let env_rel_extend = prove
 (`!tenv1 ienv1 tenv2 ienv2.
     envRel_env_rel tenv1 ienv1 /\ envRel_env_rel tenv2 ienv2
     ==> envRel_env_rel (extend_dec_tenv tenv1 tenv2) (extend_dec_ienv ienv1 ienv2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tenv1:type_env`; `ienv1:inf_env`] INFER1AUX_env_rel_lookup_none) THEN
  MP_TAC(SPECL [`tenv2:type_env`; `ienv2:inf_env`] INFER1AUX_env_rel_lookup_none) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `envRel_env_rel tenv1 ienv1` THEN UNDISCH_TAC `envRel_env_rel tenv2 ienv2` THEN
  REWRITE_TAC[envRel_env_rel_def] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[env_rel_sound_def; env_rel_complete_def;
                              INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[env_rel_sound_def; env_rel_complete_def;
                              INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES]) THEN
  ASM_SIMP_TAC[ienv_ok_extend_dec_ienv; extend_dec_tenv_ok] THEN
  REWRITE_TAC[env_rel_sound_def; env_rel_complete_def; extend_dec_tenv_def;
              extend_dec_ienv_def; inf_env_INFO.ri_accessors; type_env_INFO.ri_accessors;
              INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:mlstring list` THEN
    REWRITE_TAC[nsLookupMod_nsAppend_none; RIGHT_EXISTS_AND_THM; INFER1AUX_EXISTS_SOME] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[nsLookup_nsAppend_some] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:(mlstring,mlstring)id`; `ts:num#infer_t`]) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      SUBGOAL_THEN `?tvs' t'. check_freevars tvs' [] t' /\
                     nsLookup (type_env_v tenv2) x = SOME (tvs',t') /\
                     tscheme_approx 0 FEMPTY ts (tvs',unconvert_t t')` STRIP_ASSUME_TAC
      THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`tvs':num`; `t':t`] THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN ASM_MESON_TAC[]];
    REWRITE_TAC[nsLookup_nsAppend_some] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:(mlstring,mlstring)id`; `tvs:num`; `t:t`]) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      SUBGOAL_THEN `(?n. check_freevars n [] t) /\
                    ?tvs' t'. nsLookup (inf_env_inf_v ienv2) x = SOME (tvs',t') /\
                              tscheme_approx 0 FEMPTY (tvs,unconvert_t t) (tvs',t')`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`tvs':num`; `t':infer_t`] THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN ASM_MESON_TAC[]]]);;

let env_rel_empty = prove
 (`envRel_env_rel (type_env_REC nsEmpty nsEmpty nsEmpty) (inf_env_REC nsEmpty nsEmpty nsEmpty)`,
  REWRITE_TAC[envRel_env_rel_def; ienv_ok_def; ienv_val_ok_def; env_rel_sound_def;
              env_rel_complete_def; INFER1AUX_lookup_var_Empty; inf_env_INFO.ri_accessors;
              type_env_INFO.ri_accessors; nsLookup_nsEmpty; nsAll_nsEmpty; tenv_ok_empty;
              tenv_ctor_ok_nsEmpty; tenv_abbrev_ok_nsEmpty; option_DISTINCT] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[nsLookupMod_def; nsLookupMod_nsEmpty; option_DISTINCT]);;
let _ = cake_add_simps [env_rel_empty];;
let env_rel_lift = prove
 (`!tenv ienv mn.
     envRel_env_rel tenv ienv ==> envRel_env_rel (tenvLift mn tenv) (lift_ienv mn ienv)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[envRel_env_rel_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ienv_ok_lift] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[env_rel_sound_def; env_rel_complete_def;
                              INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES]) THEN
  REWRITE_TAC[env_rel_sound_def; env_rel_complete_def; tenvLift_def; lift_ienv_def;
              inf_env_INFO.ri_accessors; type_env_INFO.ri_accessors;
              INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `tenv_ok tenv` THEN
    REWRITE_TAC[tenv_ok_def; tenv_val_ok_def; tenv_ctor_ok_def; tenv_abbrev_ok_def;
                type_env_INFO.ri_accessors; nsAll_nsLift];
    LIST_INDUCT_TAC THEN REWRITE_TAC[nsLookupMod_nsLift] THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC id_INDUCT THEN REWRITE_TAC[nsLookup_nsLift] THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
    MATCH_MP_TAC id_INDUCT THEN REWRITE_TAC[nsLookup_nsLift] THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]]);;

let ienv_to_tenv_def = cake_def
  `ienv_to_tenv (ienv:inf_env) =
     type_env_REC (nsMap (\p. match p with (tvs,t) -> (tvs,convert_t t)) (inf_env_inf_v ienv))
                  (inf_env_inf_c ienv)
                  (inf_env_inf_t ienv)`;;

let ienv_to_tenv_extend = prove
 (`!ienv1 ienv2.
     ienv_to_tenv (extend_dec_ienv ienv2 ienv1) =
     extend_dec_tenv (ienv_to_tenv ienv2) (ienv_to_tenv ienv1)`,
  REWRITE_TAC[ienv_to_tenv_def; extend_dec_tenv_def; extend_dec_ienv_def; nsMap_nsAppend;
              inf_env_INFO.ri_accessors; type_env_INFO.ri_accessors]);;

let ienv_to_tenv_lift = prove
 (`!mn ienv. ienv_to_tenv (lift_ienv mn ienv) = tenvLift mn (ienv_to_tenv ienv)`,
  REWRITE_TAC[ienv_to_tenv_def; lift_ienv_def; tenvLift_def; nsLift_nsMap;
              inf_env_INFO.ri_accessors; type_env_INFO.ri_accessors]);;

let INFER1AUX_ienv_ok_lookup = prove
 (`!ienv x tvs t.
     ienv_ok {} ienv /\ nsLookup (inf_env_inf_v ienv) x = SOME (tvs,t) ==> check_t tvs {} t`,
  REWRITE_TAC[ienv_ok_def; ienv_val_ok_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inf_env_inf_v ienv`; `x:(mlstring,mlstring)id`] nsLookup_nsAll) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] th))) THEN
  DISCH_THEN(MP_TAC o SPEC `(tvs:num,t:infer_t)`) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let INFER1AUX_nsAll_mono = prove
 (`!P Q (e:(M,N,V)namespace). nsAll P e ==> (!id x. P id x ==> Q id x) ==> nsAll Q e`,
  MESON_TAC[nsAll_mono]);;

let env_rel_ienv_to_tenv = prove
 (`!ienv. ienv_ok {} ienv ==> envRel_env_rel (ienv_to_tenv ienv) ienv`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[envRel_env_rel_def; env_rel_sound_def; env_rel_complete_def; ienv_to_tenv_def;
              type_env_INFO.ri_accessors; INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES;
              nsLookupMod_nsMap; OPTION_MAP_EQ_NONE; nsLookup_nsMap; OPTION_MAP_EQ_SOME] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN
    REWRITE_TAC[ienv_ok_def; tenv_ok_def; tenv_val_ok_def; type_env_INFO.ri_accessors;
                ienv_val_ok_def; nsAll_nsMap] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP INFER1AUX_nsAll_mono) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC check_t_to_check_freevars THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `ts:num#infer_t`] THEN
    SPEC_TAC(`ts:num#infer_t`,`ts:num#infer_t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`tvs:num`; `t:infer_t`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `check_t tvs {} (t:infer_t)` ASSUME_TAC THENL
     [ASM_MESON_TAC[INFER1AUX_ienv_ok_lookup]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`tvs:num`; `convert_t t`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP check_t_empty_unconvert_convert_id th]) THEN
    ASM_SIMP_TAC[check_t_to_check_freevars; tscheme_approx_refl] THEN
    EXISTS_TAC `(tvs:num,t:infer_t)` THEN CASE_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `z:num#infer_t` MP_TAC) THEN
    MP_TAC(ISPEC `z:num#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:infer_t` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `check_t q {} (r:infer_t)` ASSUME_TAC THENL
     [ASM_MESON_TAC[INFER1AUX_ienv_ok_lookup]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP check_t_empty_unconvert_convert_id th]) THEN
    REWRITE_TAC[tscheme_approx_refl] THEN CONJ_TAC THENL
     [EXISTS_TAC `q:num` THEN MATCH_MP_TAC check_t_to_check_freevars THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`q:num`; `r:infer_t`] THEN REWRITE_TAC[tscheme_approx_refl]]]);;

let tenv_to_ienv_def = cake_def
  `tenv_to_ienv (tenv:type_env) =
     inf_env_REC (nsMap (\p. match p with (tvs,t) -> (tvs,unconvert_t t)) (type_env_v tenv))
                 (type_env_c tenv)
                 (type_env_t tenv)`;;

let tenv_to_ienv_extend = prove
 (`!tenv1 tenv2.
     tenv_to_ienv (extend_dec_tenv tenv2 tenv1) =
     extend_dec_ienv (tenv_to_ienv tenv2) (tenv_to_ienv tenv1)`,
  REWRITE_TAC[tenv_to_ienv_def; extend_dec_tenv_def; extend_dec_ienv_def; nsMap_nsAppend;
              inf_env_INFO.ri_accessors; type_env_INFO.ri_accessors]);;

let INFER1AUX_tenv_ok_lookup = prove
 (`!tenv x tvs t.
     tenv_ok tenv /\ nsLookup (type_env_v tenv) x = SOME (tvs,t) ==> check_freevars tvs [] t`,
  REWRITE_TAC[tenv_ok_def; tenv_val_ok_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`type_env_v tenv`; `x:(mlstring,mlstring)id`] nsLookup_nsAll) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] th))) THEN
  DISCH_THEN(MP_TAC o SPEC `(tvs:num,t:t)`) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let env_rel_tenv_to_ienv = prove
 (`!tenv. tenv_ok tenv ==> envRel_env_rel tenv (tenv_to_ienv tenv)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[envRel_env_rel_def; env_rel_sound_def; env_rel_complete_def; tenv_to_ienv_def;
              inf_env_INFO.ri_accessors; INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES;
              nsLookupMod_nsMap; OPTION_MAP_EQ_NONE; nsLookup_nsMap; OPTION_MAP_EQ_SOME] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `tenv_ok tenv` THEN
    REWRITE_TAC[ienv_ok_def; tenv_ok_def; tenv_val_ok_def; inf_env_INFO.ri_accessors;
                ienv_val_ok_def; nsAll_nsMap] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP INFER1AUX_nsAll_mono) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC check_freevars_to_check_t THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `z:num#t` MP_TAC) THEN
    MP_TAC(ISPEC `z:num#t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:t` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`q:num`; `r:t`] THEN ASM_REWRITE_TAC[tscheme_approx_refl] THEN
    ASM_MESON_TAC[INFER1AUX_tenv_ok_lookup];
    REPEAT STRIP_TAC THENL
     [EXISTS_TAC `tvs:num` THEN ASM_MESON_TAC[INFER1AUX_tenv_ok_lookup];
      MAP_EVERY EXISTS_TAC [`tvs:num`; `unconvert_t t`] THEN
      REWRITE_TAC[tscheme_approx_refl] THEN
      EXISTS_TAC `(tvs:num,t:t)` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]]);;

let tenv_to_ienv_lift = prove
 (`!mn tenv. tenv_to_ienv (tenvLift mn tenv) = lift_ienv mn (tenv_to_ienv tenv)`,
  REWRITE_TAC[tenv_to_ienv_def; lift_ienv_def; tenvLift_def; nsLift_nsMap;
              inf_env_INFO.ri_accessors; type_env_INFO.ri_accessors]);;
