(* ========================================================================= *)
(* infer_eComplete: port of HOL4                                             *)
(* compiler/inference/proofs/infer_eCompleteScript.sml (CakeML v3479).       *)
(* Completeness of the type inferencer at the expression level.              *)
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

(* ---------- pure_add_constraints ---------- *)

let pure_add_constraints_success = prove
 (`!s constraints s'.
     t_wfs s /\ pure_add_constraints s constraints s'
     ==> s SUBMAP s' /\ FDOM s SUBSET FDOM s' /\ t_compat s s' /\ t_wfs s'`,
  SUBGOAL_THEN
    `!constraints s s'.
       t_wfs s /\ pure_add_constraints s constraints s'
       ==> s SUBMAP s' /\ FDOM s SUBSET FDOM s' /\ t_compat s s' /\ t_wfs s'`
    (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBMAP_REFL; SUBSET_REFL] THEN ASM_MESON_TAC[t_compat_refl];
    ALL_TAC] THEN
  SPEC_TAC(`h:infer_t#infer_t`,`h:infer_t#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pure_add_constraints_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP t_unify_unifier o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s2:(num,infer_t)fmap`; `s':(num,infer_t)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:(num,infer_t)fmap) SUBMAP s'` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBMAP_TRANS]; ALL_TAC] THEN
  ASM_MESON_TAC[SUBMAP_FDOM_SUBSET; SUBMAP_t_compat]);;

let t_compat_pure_add_constraints_1 = prove
 (`!ls s sx.
     t_compat s sx /\ ALL (\(x,y). t_walkstar sx x = t_walkstar sx y) ls
     ==> ?si. pure_add_constraints s ls si /\ t_compat si sx`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:infer_t#infer_t`,`h:infer_t#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pure_add_constraints_def; ALL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `p1:infer_t`; `p2:infer_t`; `sx:(num,infer_t)fmap`]
         t_compat_eqs_t_unify) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

let t_compat_pure_add_constraints_2 = prove
 (`!ls s sx.
     t_wfs s /\ pure_add_constraints s ls sx
     ==> ALL (\(x,y). t_walkstar sx x = t_walkstar sx y) ls`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ALL]; ALL_TAC] THEN
  SPEC_TAC(`h:infer_t#infer_t`,`h:infer_t#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pure_add_constraints_def; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP t_unify_unifier o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MP_TAC(ISPECL [`s2:(num,infer_t)fmap`; `t:(infer_t#infer_t)list`; `sx:(num,infer_t)fmap`]
         pure_add_constraints_success) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_MESON_TAC[t_walkstar_SUBMAP]);;

let pure_add_constraints_functional = prove
 (`!constraints s s' s''.
     t_wfs s /\ pure_add_constraints s constraints s' /\
     pure_add_constraints s constraints s''
     ==> s' = s''`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:infer_t#infer_t`,`h:infer_t#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pure_add_constraints_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s2':(num,infer_t)fmap = s2` SUBST_ALL_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(rhs(concl th)) = `s2':(num,infer_t)fmap`)) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[t_unify_wfs]);;

let pure_add_constraints_swap_lemma = prove
 (`!s a b sx.
     t_wfs s /\ pure_add_constraints s (APPEND a b) sx
     ==> ?si. pure_add_constraints s (APPEND b a) si /\ t_compat si sx`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP t_compat_pure_add_constraints_2 o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  REWRITE_TAC[ALL_APPEND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pure_add_constraints_success o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  REWRITE_TAC[pure_add_constraints_append] THEN
  MP_TAC(ISPECL [`b:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`; `sx:(num,infer_t)fmap`]
         t_compat_pure_add_constraints_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`; `sx:(num,infer_t)fmap`]
         t_compat_pure_add_constraints_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s3:(num,infer_t)fmap` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s3:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `s1:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[]);;

let pure_add_constraints_swap = prove
 (`!s a b sx.
     t_wfs s /\ pure_add_constraints s (APPEND a b) sx
     ==> ?si. pure_add_constraints s (APPEND b a) si /\ t_compat si sx /\ t_compat sx si`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP pure_add_constraints_swap_lemma o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `si:(num,infer_t)fmap` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `si:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP pure_add_constraints_swap_lemma o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `sj:(num,infer_t)fmap` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sj:(num,infer_t)fmap = sx` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_functional]; ASM_REWRITE_TAC[]]);;
(* ---------- extending a substitution ---------- *)

let extend_t_vR_WF = prove
 (`!lim n s uvar.
     check_t lim {} n /\ WF (t_vR s) ==> WF (t_vR (s |+ (uvar,n)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_SUBSET THEN
  EXISTS_TAC `t_vR (s:(num,infer_t)fmap)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[t_vR_eqn; FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP check_t_t_vars) THEN SET_TAC[]);;

let INFER1AUX_ec_is_app name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let not_t_oc = prove
 (`(!t s v lim. t_wfs s /\ check_t lim {} t ==> ~t_oc s t v) /\
   (!ts s (t:infer_t) v lim.
      t_wfs s /\ ALL (check_t lim {}) ts ==> ~EX (\t. t_oc s t v) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[check_t_def; EX; ALL; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> INFER1AUX_ec_is_app "t_oc" (concl th))) THEN
      FIRST_ASSUM(fun wf -> PURE_ONCE_REWRITE_TAC[MATCH_MP t_oc_eqn wf]) THEN
      REWRITE_TAC[t_walk_eqn] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]) THEN
  ASM_MESON_TAC[]);;

let FDOM_extend = prove
 (`!s next_uvar (n:infer_t).
     FDOM s = count next_uvar ==> FDOM (s |+ (next_uvar,n)) = count (SUC next_uvar)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FDOM_FUPDATE; EXTENSION; IN_INSERT; IN_COUNT] THEN
  ARITH_TAC);;
let pure_add_constraints_exists = prove
 (`!s ts next_uvar lim.
     t_wfs s /\ FDOM s = count next_uvar /\ ALL (check_freevars lim []) ts
     ==> let tys = MAP (\n. next_uvar + n) (COUNT_LIST (LENGTH ts)) in
         let targs = MAP unconvert_t ts in
         let constraints = ZIP (MAP Infer_Tuvar tys) targs in
         let extension = ZIP tys targs in
         pure_add_constraints s constraints (s |++ extension)`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `!ts s next_uvar lim.
      t_wfs s /\ FDOM s = count next_uvar /\ ALL (check_freevars lim []) ts
      ==> pure_add_constraints s
            (ZIP (MAP Infer_Tuvar (MAP (\n. next_uvar + n) (COUNT_LIST (LENGTH ts))))
                 (MAP unconvert_t ts))
            (s |++ ZIP (MAP (\n. next_uvar + n) (COUNT_LIST (LENGTH ts)))
                       (MAP unconvert_t ts))`
    (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; COUNT_LIST_DEF; MAP; ZIP; FUPDATE_LIST_THM;
                pure_add_constraints_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  REWRITE_TAC[LENGTH; COUNT_LIST_DEF; MAP; ZIP; FUPDATE_LIST_THM;
              pure_add_constraints_def; ADD_CLAUSES] THEN
  SUBGOAL_THEN `check_t lim {} (unconvert_t h)` ASSUME_TAC THENL
   [MATCH_MP_TAC check_freevars_to_check_t THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(s:(num,infer_t)fmap) |+ (next_uvar,unconvert_t h)` THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_unify_eqn th]) THEN
    SUBGOAL_THEN `FLOOKUP (s:(num,infer_t)fmap) next_uvar = NONE` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[flookup_thm; IN_COUNT; LT_REFL]; ALL_TAC] THEN
    REWRITE_TAC[t_walk_eqn] THEN
    FIRST_ASSUM(fun th -> PURE_ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn th]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~t_oc s (unconvert_t h) next_uvar` ASSUME_TAC THENL
     [MATCH_MP_TAC (CONJUNCT1 not_t_oc) THEN EXISTS_TAC `lim:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `h:t` (CONJUNCT1 (cases "t"))) THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[unconvert_t_def; check_t_def; check_freevars_def; MEM;
                                NOT_IN_EMPTY]) THEN
    TRY(FIRST_X_ASSUM CONTR_TAC) THEN
    ASM_REWRITE_TAC[unconvert_t_def; t_walk_eqn; t_ext_s_check_eqn] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[t_ext_s_check_eqn];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(s:(num,infer_t)fmap) |+ (next_uvar,unconvert_t h)`;
                                `SUC next_uvar`; `lim:num`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[t_wfs_eqn] THEN MATCH_MP_TAC extend_t_vR_WF THEN
      EXISTS_TAC `lim:num` THEN ASM_REWRITE_TAC[GSYM t_wfs_eqn];
      MATCH_MP_TAC FDOM_extend THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; ADD_CLAUSES]);;

(* ---------- walks and checks ---------- *)

let check_t_t_walkstar = prove
 (`!s. t_wfs s
       ==> !tvs (uvars:num->bool) t.
             check_t tvs {} (t_walkstar s t) ==> check_t tvs (FDOM s) t`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[t_walkstar_eqn1; check_t_def];
    REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC[t_walkstar_eqn1; check_t_def; ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `v:num` THEN REWRITE_TAC[check_t_def] THEN
    ASM_CASES_TAC `(v:num) IN FDOM (s:(num,infer_t)fmap)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`s:(num,infer_t)fmap`; `v:num`] t_walkstar_tuvar_props) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[check_t_def; NOT_IN_EMPTY]]);;

let t_walkstar_ignore_inc = prove
 (`!s tvs.
     t_wfs s
     ==> (!t. (!uv. uv IN FDOM s ==> check_t 0 {} (t_walkstar s (Infer_Tuvar uv)))
              ==> t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t) /\
         (!ts. !t:infer_t.
                 (!uv. uv IN FDOM s ==> check_t 0 {} (t_walkstar s (Infer_Tuvar uv)))
                 ==> ALL (\t. t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t)
                         ts)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_deBruijn_inc tvs o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[inc_wfs]; ALL_TAC] THEN
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[t_walkstar_eqn1];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[t_walkstar_eqn1; injectivity "infer_t"] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Infer_Tvar_db 0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[walkstar_inc2] THEN
    ASM_CASES_TAC `(n:num) IN FDOM (s:(num,infer_t)fmap)` THENL
     [MATCH_MP_TAC check_t_deBruijn_inc THEN
      MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] (CONJUNCT1 check_t_more)) THEN
      ASM_SIMP_TAC[];
      MP_TAC(SPECL [`s:(num,infer_t)fmap`; `n:num`] t_walkstar_tuvar_props) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[infer_deBruijn_inc_def]];
    REWRITE_TAC[ALL];
    REPEAT STRIP_TAC THEN REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]]);;
let SUBMAP_FUPDATE_LIST_NON_EXIST = prove
 (`!(ls:(A#B)list) (s:(A,B)fmap).
     set_of_list (MAP FST ls) INTER FDOM s = {} ==> s SUBMAP (s |++ ls)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE_LIST; IN_UNION] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FUPDATE_LIST_APPLY_NOT_MEM THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM SET_TAC[]);;

let t_vwalk_o_f_id = prove
 (`!s. t_wfs s ==> !t. t_vwalk (infer_deBruijn_inc 0 o_f s) t = t_vwalk s t`,
  REWRITE_TAC[infer_deBruijn_inc0_id; o_f_id]);;

let t_walkstar_o_f_id = prove
 (`!s. t_wfs s ==> !t. t_walkstar (infer_deBruijn_inc 0 o_f s) t = t_walkstar s t`,
  REWRITE_TAC[infer_deBruijn_inc0_id; o_f_id]);;

let infer_eComplete_deBruijn_subst_id = prove
 (`(!t. deBruijn_subst 0 [] t = t) /\ (!ts. MAP (deBruijn_subst 0 []) ts = ts)`,
  MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[deBruijn_subst_def; MAP; LENGTH; ADD_CLAUSES; LT; SUB_0] THEN
  SIMP_TAC[]);;

let tscheme_approx_weakening2 = prove
 (`!tvs s s' t1 t2.
     tscheme_approx tvs s t1 t2 /\ t_compat s s' /\ FDOM s SUBSET FDOM s'
     ==> tscheme_approx tvs s' t1 t2`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[tscheme_approx_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `subst':infer_t list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] (CONJUNCT2 check_t_more5)) THEN
    EXISTS_TAC `FDOM (s:(num,infer_t)fmap)` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `subst:infer_t list`) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[t_compat_def]) THEN
    MESON_TAC[]]);;

let env_rel_complete_t_compat = prove
 (`!s s' ienv tenv tenvE.
     t_compat s s' /\ FDOM s SUBSET FDOM s' /\ t_wfs s' /\
     env_rel_complete s ienv tenv tenvE
     ==> env_rel_complete s' ienv tenv tenvE`,
  REWRITE_TAC[env_rel_complete_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[tscheme_approx_weakening2]]);;

let infer_eComplete_NOT_SOME_NONE = prove
 (`!(a:A option). (!x. ~(a = SOME x)) ==> a = NONE`,
  MESON_TAC[cases "option"]);;
let t_walk_submap_walkstar = prove
 (`!s s'.
     s SUBMAP s' /\ t_wfs s /\ t_wfs s'
     ==> (!h. t_walk s (t_walkstar s' h) = t_walkstar s' h) /\
         (!hs. MAP ((t_walk s) o t_walkstar s') hs = MAP (t_walkstar s') hs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[t_walkstar_eqn1; t_walk_eqn];
    ASM_SIMP_TAC[t_walkstar_eqn1; t_walk_eqn];
    X_GEN_TAC `n:num` THEN
    REWRITE_TAC[MATCH_MP t_walkstar_eqn (ASSUME `t_wfs (s':(num,infer_t)fmap)`)] THEN
    REWRITE_TAC[t_walk_eqn] THEN
    MP_TAC(ISPEC `t_vwalk (s':(num,infer_t)fmap) n` (CONJUNCT1 (cases "infer_t"))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[t_walk_eqn] THEN
    SUBGOAL_THEN `~((a:num) IN FDOM (s':(num,infer_t)fmap))` ASSUME_TAC THENL
     [ASM_MESON_TAC[t_vwalk_to_var]; ALL_TAC] THEN
    SUBGOAL_THEN `FLOOKUP (s:(num,infer_t)fmap) a = NONE` ASSUME_TAC THENL
     [REWRITE_TAC[flookup_thm] THEN ASM_MESON_TAC[SUBMAP_DEF]; ALL_TAC] THEN
    PURE_ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`)] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    REWRITE_TAC[MAP];
    REWRITE_TAC[MAP; o_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let t_unify_to_pure_add_constraints = prove
 (`!s (s':(num,infer_t)fmap) h t constraints s''.
     pure_add_constraints s (APPEND constraints [h,t]) s''
     ==> ?s'. pure_add_constraints s constraints s' /\ t_unify s' h t = SOME s''`,
  REWRITE_TAC[pure_add_constraints_append; pure_add_constraints_def] THEN MESON_TAC[]);;

let add_constraint_success2 = prove
 (`!l t1 t2 st st' x.
     add_constraint l t1 t2 st = (M_success x,st') <=>
     x = one /\
     pure_add_constraints (infer_st_subst st) [t1,t2] (infer_st_subst st') /\
     infer_st_next_uvar st' = infer_st_next_uvar st /\
     infer_st_next_id st' = infer_st_next_id st`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[add_constraint_success; pure_add_constraints_def] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[infer_st_component_equality; infer_st_rewrs; infer_st_INFO.ri_accfupds;
              K_THM] THEN
  MESON_TAC[]);;

let pure_add_constraints_combine = prove
 (`!st ls x1 x2 ls' st'' y1 y2.
     (?st'. (pure_add_constraints (infer_st_subst st) ls (infer_st_subst st') /\
             infer_st_next_uvar st' = x1 /\ infer_st_next_id st' = x2) /\
            (pure_add_constraints (infer_st_subst st') ls' (infer_st_subst st'') /\
             y1 = infer_st_next_uvar st' /\ y2 = infer_st_next_id st')) <=>
     pure_add_constraints (infer_st_subst st) (APPEND ls ls') (infer_st_subst st'') /\
     y1 = x1 /\ y2 = x2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pure_add_constraints_append] THEN EQ_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `infer_st_REC x1 s2 x2` THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accessors]);;
let t_unify_ignore = prove
 (`(!s t t'. t_wfs s ==> t_walkstar s t = t_walkstar s t' ==> t_unify s t t' = SOME s) /\
   (!s ts ts'.
      t_wfs s ==> MAP (t_walkstar s) ts = MAP (t_walkstar s) ts' ==> ts_unify s ts ts' = SOME s)`,
  MP_TAC(ISPECL
    [`\s t t'. t_walkstar s t = t_walkstar s t' ==> t_unify s t t' = SOME s`;
     `\s ts ts'. MAP (t_walkstar s) ts = MAP (t_walkstar s) ts' ==> ts_unify s ts ts' = SOME s`]
    t_unify_strongind) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_unify_eqn th]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      INFER1AUX_ec_is_app "t_walkstar" (lhs(concl th)))) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_walkstar_eqn th]) THEN
    MP_TAC(ISPEC `t_walk (s:(num,infer_t)fmap) t` (CONJUNCT1 (cases "infer_t"))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `t_walk (s:(num,infer_t)fmap) t'` (CONJUNCT1 (cases "infer_t"))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "infer_t"; distinctness "infer_t"] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `ts:infer_t list` list_CASES) THEN STRIP_TAC THEN
    MP_TAC(ISPEC `ts':infer_t list` list_CASES) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; ts_unify_def] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `t_unify s h h' = SOME (s:(num,infer_t)fmap)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let pure_add_constraints_ignore = prove
 (`!s ls.
     t_wfs s /\ ALL (\(x,y). t_walkstar s x = t_walkstar s y) ls
     ==> pure_add_constraints s ls s`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[pure_add_constraints_def; ALL] THEN
  SPEC_TAC(`h:infer_t#infer_t`,`h:infer_t#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pure_add_constraints_def] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
  ASM_SIMP_TAC[t_unify_ignore]);;

let t_compat_ground = prove
 (`!a b tvs.
     t_compat a b
     ==> !uv. uv IN FDOM a /\ check_t tvs {} (t_walkstar a (Infer_Tuvar uv))
              ==> uv IN FDOM b /\ check_t tvs {} (t_walkstar b (Infer_Tuvar uv))`,
  REWRITE_TAC[t_compat_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_walkstar b (Infer_Tuvar uv) = t_walkstar a (Infer_Tuvar uv)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `Infer_Tuvar uv`) THEN
    MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(uv:num) IN FDOM (b:(num,infer_t)fmap)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`b:(num,infer_t)fmap`; `uv:num`] t_walkstar_tuvar_props) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `check_t tvs {} (t_walkstar a (Infer_Tuvar uv))` THEN
  ASM_REWRITE_TAC[check_t_def; NOT_IN_EMPTY]);;

let t_walkstar_tuvar_props2 = prove
 (`!s x uv.
     t_wfs s /\ t_walkstar s x = Infer_Tuvar uv
     ==> ?k. x = Infer_Tuvar k /\ (k = uv ==> ~(k IN FDOM s)) /\
             (~(k = uv) ==> k IN FDOM s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:infer_t` (CONJUNCT1 (cases "infer_t"))) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP t_walkstar_eqn1
      (ASSUME `t_wfs (s:(num,infer_t)fmap)`); distinctness "infer_t"]) THEN
    FIRST_X_ASSUM CONTR_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP t_walkstar_eqn1
      (ASSUME `t_wfs (s:(num,infer_t)fmap)`); distinctness "infer_t"]) THEN
    FIRST_X_ASSUM CONTR_TAC;
    EXISTS_TAC `a:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `a:num`] t_walkstar_tuvar_props) THEN
    ASM_REWRITE_TAC[injectivity "infer_t"] THEN MESON_TAC[]]);;

let check_t_less = prove
 (`!s n uvars.
     (!t. t_wfs s /\
          (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
          check_t 0 uvars t
          ==> check_t n (uvars INTER COMPL (FDOM s)) (t_walkstar s t)) /\
     (!ts. t_wfs s /\
           (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
           ALL (check_t 0 uvars) ts
           ==> ALL (check_t n (uvars INTER COMPL (FDOM s))) (MAP (t_walkstar s) ts))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[check_t_def; LT; ALL; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; check_t_def] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_CASES_TAC `(a:num) IN FDOM (s:(num,infer_t)fmap)` THENL
   [MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] (CONJUNCT1 check_t_more)) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `a:num`] t_walkstar_tuvar_props) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[check_t_def; IN_INTER; COMPL_DEF; IN_DIFF; IN_UNIV]]);;
let t_compat_bi_ground = prove
 (`!a b n.
     (!uv. uv IN FDOM a ==> check_t n {} (t_walkstar a (Infer_Tuvar uv))) /\
     t_compat a b /\ t_compat b a
     ==> (!uv. uv IN FDOM b ==> check_t n {} (t_walkstar b (Infer_Tuvar uv))) /\
         FDOM a = FDOM b /\
         ((!t. t_walkstar a t = t_walkstar b t) /\
          (!ts. MAP (t_walkstar a) ts = MAP (t_walkstar b) ts))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `t_wfs (a:(num,infer_t)fmap) /\ t_wfs (b:(num,infer_t)fmap) /\
    (!t. t_walkstar b (t_walkstar a t) = t_walkstar b t) /\
    (!t. t_walkstar a (t_walkstar b t) = t_walkstar a t)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  ABBREV_TAC `ab = !t. t_walkstar b (t_walkstar a t) = t_walkstar (b:(num,infer_t)fmap) t` THEN
  ABBREV_TAC `ba = !t. t_walkstar a (t_walkstar b t) = t_walkstar (a:(num,infer_t)fmap) t` THEN
  SUBGOAL_THEN `!uv. uv IN FDOM a ==>
                  t_walkstar b (Infer_Tuvar uv) = t_walkstar a (Infer_Tuvar uv)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `Infer_Tuvar uv` (EQ_MP (SYM (ASSUME `(!t. t_walkstar b (t_walkstar a t) =
                                           t_walkstar (b:(num,infer_t)fmap) t) <=> ab`))
                                         (ASSUME `ab:bool`))) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC t_walkstar_no_vars THEN
    EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!uv. uv IN FDOM (b:(num,infer_t)fmap) ==> uv IN FDOM (a:(num,infer_t)fmap)`
    ASSUME_TAC THENL
   [X_GEN_TAC `uv:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(uv:num) IN FDOM (a:(num,infer_t)fmap)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:(num,infer_t)fmap`; `uv:num`] t_walkstar_tuvar_props) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `Infer_Tuvar uv` (EQ_MP (SYM (ASSUME `(!t. t_walkstar a (t_walkstar b t) =
                                           t_walkstar (a:(num,infer_t)fmap) t) <=> ba`))
                                         (ASSUME `ba:bool`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP t_walkstar_tuvar_props2 o
      CONJ (ASSUME `t_wfs (a:(num,infer_t)fmap)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `k:num = uv` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`b:(num,infer_t)fmap`; `uv:num`] t_walkstar_tuvar_props) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(k:num) IN FDOM (a:(num,infer_t)fmap)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `check_t n {} (t_walkstar a (Infer_Tuvar k))` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `t_walkstar a (Infer_Tuvar k) = Infer_Tuvar uv` SUBST1_TAC THENL
       [MP_TAC(SPEC `Infer_Tuvar uv` (EQ_MP (SYM (ASSUME `(!t. t_walkstar a (t_walkstar b t) =
                                           t_walkstar (a:(num,infer_t)fmap) t) <=> ba`))
                                         (ASSUME `ba:bool`))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[check_t_def; NOT_IN_EMPTY]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (a:(num,infer_t)fmap) = FDOM (b:(num,infer_t)fmap)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`a:(num,infer_t)fmap`; `b:(num,infer_t)fmap`; `n:num`]
             t_compat_ground) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_SIMP_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!t. t_walkstar a t = t_walkstar b t) /\
                (!ts. MAP (t_walkstar a) ts = MAP (t_walkstar (b:(num,infer_t)fmap)) ts)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC infer_t_INDUCT THEN ASM_SIMP_TAC[t_walkstar_eqn1; MAP] THEN
    X_GEN_TAC `uv:num` THEN
    ASM_CASES_TAC `(uv:num) IN FDOM (a:(num,infer_t)fmap)` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`a:(num,infer_t)fmap`; `uv:num`] t_walkstar_tuvar_props) THEN
    MP_TAC(ISPECL [`b:(num,infer_t)fmap`; `uv:num`] t_walkstar_tuvar_props) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(uv:num) IN FDOM (a:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_eq(snd(dest_forall(concl th))) &&
                            rator(lhs(snd(dest_forall(concl th)))) =
                              `t_walkstar (a:(num,infer_t)fmap)`
                         then REWRITE_TAC[GSYM th] else failwith "") THEN
  ASM_SIMP_TAC[]);;
(* a uvar bound to a ground type walks to it *)
let INFER1AUX_walkstar_flookup_ground = prove
 (`!s u X n.
     t_wfs s /\ FLOOKUP s u = SOME X /\ check_t n {} X ==> t_walkstar s (Infer_Tuvar u) = X`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATCH_MP t_walkstar_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`); t_walk_eqn] THEN
  PURE_ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`)] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `X:infer_t` (CONJUNCT1 (cases "infer_t"))) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[check_t_def; NOT_IN_EMPTY]) THEN
  TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[injectivity "infer_t"] THEN
  REWRITE_TAC[MAP_EQ_ID] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC t_walkstar_no_vars THEN
  EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[]);;

(* Free properties when extending the completed map with uvar->ground var *)
let extend_one_props = prove
 (`!st s constraints n t.
     t_wfs (infer_st_subst st) /\ t_wfs s /\
     pure_add_constraints (infer_st_subst st) constraints s /\
     (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
     check_freevars n [] t /\ FDOM s = count (infer_st_next_uvar st)
     ==> let s' = s |++ [(infer_st_next_uvar st,unconvert_t t)] in
         t_wfs s' /\
         pure_add_constraints s [Infer_Tuvar (infer_st_next_uvar st),unconvert_t t] s' /\
         s SUBMAP s' /\ infer_st_subst st SUBMAP s' /\
         pure_add_constraints (infer_st_subst st)
           (APPEND constraints [(Infer_Tuvar (infer_st_next_uvar st),unconvert_t t)]) s' /\
         FDOM s' = count (infer_st_next_uvar st + 1) /\
         t_walkstar s' (Infer_Tuvar (infer_st_next_uvar st)) = unconvert_t t /\
         !uv. uv IN FDOM s' ==> check_t n {} (t_walkstar s' (Infer_Tuvar uv))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `u = infer_st_next_uvar st` THEN
  SUBGOAL_THEN `check_t n {} (unconvert_t t)` ASSUME_TAC THENL
   [MATCH_MP_TAC check_freevars_to_check_t THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pure_add_constraints s [Infer_Tuvar u,unconvert_t t]
                  (s |++ [(u,unconvert_t t)])` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `[t:t]`; `u:num`; `n:num`]
           pure_add_constraints_exists) THEN
    ASM_REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[LENGTH; ONE; COUNT_LIST_DEF; MAP; ZIP; ADD_CLAUSES];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pure_add_constraints_success o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  MP_TAC(ISPECL [`infer_st_subst st`; `constraints:(infer_t#infer_t)list`;
                 `s:(num,infer_t)fmap`] pure_add_constraints_success) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `infer_st_subst st SUBMAP (s |++ [(u,unconvert_t t)])` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBMAP_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FDOM (s |++ [(u,unconvert_t t)]) = count (u + 1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FUPDATE_LIST; MAP; set_of_list; EXTENSION; IN_UNION; IN_COUNT;
                    IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar (s |++ [(u,unconvert_t t)]) (Infer_Tuvar u) = unconvert_t t`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walkstar_flookup_ground THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[FUPDATE_LIST_THM; FLOOKUP_UPDATE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pure_add_constraints_append] THEN ASM_MESON_TAC[];
    X_GEN_TAC `uv:num` THEN ASM_REWRITE_TAC[IN_COUNT] THEN DISCH_TAC THEN
    ASM_CASES_TAC `uv:num = u` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(uv:num) IN FDOM (s:(num,infer_t)fmap)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_COUNT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `s |++ [(u:num,unconvert_t t)]`;
                   `Infer_Tuvar uv`] t_walkstar_SUBMAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `check_t n {} (t_walkstar s (Infer_Tuvar uv))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`n:num`; `t_walkstar s (Infer_Tuvar uv)`;
                   `s |++ [(u:num,unconvert_t t)]`] t_walkstar_no_vars) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;
(* HOL4's ALOOKUP_lemma (an ML value of the script) *)
let INFER1AUX_ALOOKUP_lemma = prove
 (`!n (ls:A list) offset.
     n < LENGTH ls
     ==> ALOOKUP (REVERSE (ZIP (MAP (\n. offset + n) (COUNT_LIST (LENGTH ls))) ls))
                 (offset + n) =
         SOME (EL n ls)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (ZIP (MAP (\n. offset + n) (COUNT_LIST (LENGTH ls)))
                                          (ls:A list)))` ASSUME_TAC THENL
   [SIMP_TAC[MAP_FST_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
    MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[all_distinct_count_list] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[alookup_distinct_reverse] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MEM_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
  EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST]);;

let submap_t_walkstar_replace = prove
 (`!s s' n h.
     t_wfs s' /\ s SUBMAP s' /\ check_t n {} (t_walkstar s h)
     ==> t_walkstar s h = t_walkstar s' h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `s':(num,infer_t)fmap`; `h:infer_t`]
         t_walkstar_SUBMAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC t_walkstar_no_vars THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;
let extend_multi_props = prove
 (`!st constraints s ts n.
     t_wfs (infer_st_subst st) /\ t_wfs s /\
     pure_add_constraints (infer_st_subst st) constraints s /\
     (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
     ALL (check_freevars n []) ts /\ FDOM s = count (infer_st_next_uvar st)
     ==> let tys = MAP (\n. infer_st_next_uvar st + n) (COUNT_LIST (LENGTH ts)) in
         let targs = MAP unconvert_t ts in
         let new_constraints = ZIP (MAP Infer_Tuvar tys) targs in
         let extension = ZIP tys targs in
         let s' = s |++ extension in
         pure_add_constraints s new_constraints s' /\
         pure_add_constraints (infer_st_subst st) (APPEND constraints new_constraints) s' /\
         t_wfs s' /\ s SUBMAP s' /\ infer_st_subst st SUBMAP s' /\
         FDOM s' = count (infer_st_next_uvar st + LENGTH ts) /\
         (!n. n < LENGTH ts
              ==> t_walkstar s' (Infer_Tuvar (infer_st_next_uvar st + n)) = EL n targs) /\
         (!uv. uv IN FDOM s' ==> check_t n {} (t_walkstar s' (Infer_Tuvar uv)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `u = infer_st_next_uvar st` THEN
  ABBREV_TAC `ext = ZIP (MAP (\n. u + n) (COUNT_LIST (LENGTH (ts:t list))))
                        (MAP unconvert_t ts)` THEN
  SUBGOAL_THEN `pure_add_constraints s
     (ZIP (MAP Infer_Tuvar (MAP (\n. u + n) (COUNT_LIST (LENGTH (ts:t list)))))
          (MAP unconvert_t ts)) ((s:(num,infer_t)fmap) |++ ext)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `ts:t list`; `u:num`; `n:num`]
           pure_add_constraints_exists) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pure_add_constraints_success o
    CONJ (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
  MP_TAC(ISPECL [`infer_st_subst st`; `constraints:(infer_t#infer_t)list`;
                 `s:(num,infer_t)fmap`] pure_add_constraints_success) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k < LENGTH (ts:t list)
                    ==> t_walkstar ((s:(num,infer_t)fmap) |++ ext) (Infer_Tuvar (u + k)) =
                        EL k (MAP unconvert_t ts)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INFER1AUX_walkstar_flookup_ground THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "ext" THEN REWRITE_TAC[flookup_fupdate_list] THEN
      MP_TAC(ISPECL [`k:num`; `MAP unconvert_t ts`; `u:num`] INFER1AUX_ALOOKUP_lemma) THEN
      ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[option_CASE];
      ASM_SIMP_TAC[EL_MAP] THEN MATCH_MP_TAC check_freevars_to_check_t THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[GSYM ALL_MEM] o
        check (fun th -> INFER1AUX_ec_is_app "ALL" (concl th))) THEN
      MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FDOM ((s:(num,infer_t)fmap) |++ ext) = count (u + LENGTH (ts:t list))` ASSUME_TAC THENL
   [EXPAND_TAC "ext" THEN
    ASM_SIMP_TAC[FDOM_FUPDATE_LIST; MAP_FST_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_COUNT; IN_SET_OF_LIST; MEM_MAP; MEM_COUNT_LIST] THEN
    X_GEN_TAC `x:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN ASM_CASES_TAC `x < u` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `x - u:num` THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pure_add_constraints_append] THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `uv:num` THEN ASM_REWRITE_TAC[IN_COUNT] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(uv:num) IN FDOM (s:(num,infer_t)fmap)` THENL
     [SUBGOAL_THEN `check_t n {} (t_walkstar s (Infer_Tuvar uv))` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `(s:(num,infer_t)fmap) |++ ext`; `n:num`; `Infer_Tuvar uv`]
             submap_t_walkstar_replace) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `uv = u + (uv - u) /\ uv - u < LENGTH (ts:t list)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `~((uv:num) IN FDOM (s:(num,infer_t)fmap))` THEN
        ASM_REWRITE_TAC[IN_COUNT] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if concl th = `uv = u + (uv - u):num` then SUBST1_TAC th
                              else failwith "") THEN
      ASM_SIMP_TAC[EL_MAP] THEN MATCH_MP_TAC check_freevars_to_check_t THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[GSYM ALL_MEM] o
        check (fun th -> INFER1AUX_ec_is_app "ALL" (concl th))) THEN
      MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[]]]);;
(* ---------- constrain_op ---------- *)

(* completeness of a list of constraints that the completion satisfies *)
let INFER1AUX_cs_core = prove
 (`!n m s0 cs s CS.
     sub_completion n m s0 cs s /\ FDOM s = count m /\ t_wfs s0 /\
     ALL (\(x,y). t_walkstar s x = t_walkstar s y) CS
     ==> ?s1 si cs'.
           pure_add_constraints s0 CS s1 /\ sub_completion n m s1 cs' si /\
           t_compat s si /\ FDOM s1 SUBSET count m /\ FDOM si = count m /\
           (!x. t_walkstar si x = t_walkstar s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `pure_add_constraints s0 (APPEND cs CS) (s:(num,infer_t)fmap)` MP_TAC THENL
   [REWRITE_TAC[pure_add_constraints_append] THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_SIMP_TAC[pure_add_constraints_ignore];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP pure_add_constraints_swap o
    CONJ (ASSUME `t_wfs (s0:(num,infer_t)fmap)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `si:(num,infer_t)fmap` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `si:(num,infer_t)fmap`; `n:num`]
         t_compat_bi_ground) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pure_add_constraints_append] o
    check (fun th -> INFER1AUX_ec_is_app "pure_add_constraints" (concl th) &&
                     rand(concl th) = `si:(num,infer_t)fmap`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `si:(num,infer_t)fmap`;
                        `cs:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:(num,infer_t)fmap`; `cs:(infer_t#infer_t)list`;
                 `si:(num,infer_t)fmap`] pure_add_constraints_success) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  ASM_MESON_TAC[]);;

(* the same, after binding the next uvar m to a ground type *)
let INFER1AUX_cs_core1 = prove
 (`!n m s0 cs s CS tt.
     sub_completion n m s0 cs s /\ FDOM s = count m /\ t_wfs s0 /\
     check_freevars n [] tt /\
     ALL (\(x,y). t_walkstar (s |++ [(m,unconvert_t tt)]) x =
                  t_walkstar (s |++ [(m,unconvert_t tt)]) y) CS
     ==> ?s1 si cs'.
           pure_add_constraints s0 CS s1 /\ sub_completion n (m + 1) s1 cs' si /\
           t_compat s si /\ FDOM s1 SUBSET count (m + 1) /\ FDOM si = count (m + 1) /\
           (!x. t_walkstar si x = t_walkstar (s |++ [(m,unconvert_t tt)]) x) /\
           t_walkstar (s |++ [(m,unconvert_t tt)]) (Infer_Tuvar m) = unconvert_t tt /\
           s SUBMAP (s |++ [(m,unconvert_t tt)]) /\ t_wfs (s |++ [(m,unconvert_t tt)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MP_TAC(ISPECL [`infer_st_REC m s0 0`; `s:(num,infer_t)fmap`; `cs:(infer_t#infer_t)list`;
                 `n:num`; `tt:t`] extend_one_props) THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accessors] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `m + 1`; `s0:(num,infer_t)fmap`;
                 `APPEND cs [Infer_Tuvar m,unconvert_t tt]`;
                 `(s:(num,infer_t)fmap) |++ [(m,unconvert_t tt)]`;
                 `CS:(infer_t#infer_t)list`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `si:(num,infer_t)fmap`;
                        `cs':(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC t_compat_trans THEN
  EXISTS_TAC `(s:(num,infer_t)fmap) |++ [(m,unconvert_t tt)]` THEN
  ASM_SIMP_TAC[SUBMAP_t_compat]);;
(* convert_t of the inferencer's type of a primitive type *)
let INFER1AUX_ec_convert_t_num_of = prove
 (`!ty. convert_t (Infer_Tapp [] (t_num_of ty)) = t_of ty`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[convert_t_def; MAP; t_num_of_def; t_of_def; typeSystem_Tbool_def;
              typeSystem_Tint_def; typeSystem_Tchar_def; typeSystem_Tstring_def;
              typeSystem_Tword8_def; typeSystem_Tword64_def; typeSystem_Tdouble_def]);;

let INFER1AUX_ALL_EQ_REPLICATE = prove
 (`!(l:A list) a. ALL (\x. x = a) l ==> l = REPLICATE (LENGTH l) a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LENGTH; REPLICATE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* the simple operations: ground argument and result types, which type_op *)
(* forces                                                                 *)
let INFER1AUX_simple_ops = prove
 (`!op args ret.
     op_simple_constraints op = (T,args,ret)
     ==> ALL (check_t 0 {}) args /\ check_t 0 {} ret /\
         !ts t. type_op op ts t ==> ts = MAP convert_t args /\ t = convert_t ret`,
  GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[op_simple_constraints_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  TRY(fun (asl,w as gl) ->
        let tm = find_term (fun t -> INFER1AUX_ec_is_app "supported_arith" t) w in
        (MP_TAC (ISPEC tm (cases "option")) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]) gl) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN RVEQ_TAC THEN
  REWRITE_TAC[check_t_def; ALL; EVERY_REPLICATE] THEN
  REWRITE_TAC[type_op_cases; distinctness "op"; injectivity "op"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[MAP; convert_t_def; INFER1AUX_ec_convert_t_num_of; word_tc_def;
                  map_replicate] THEN
  FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
    if is_eq(concl th1) && is_eq(concl th2) && lhs(concl th1) = lhs(concl th2)
    then let eq = REWRITE_RULE[injectivity "option"] (TRANS (SYM th1) th2) in
         SUBST1_TAC (if INFER1AUX_ec_is_app "LENGTH" (lhs(concl eq)) then SYM eq else eq)
    else failwith "")) THEN
  MATCH_MP_TAC INFER1AUX_ALL_EQ_REPLICATE THEN ASM_REWRITE_TAC[]);;
let INFER1AUX_unconvert_convert_list = prove
 (`!n l. ALL (check_t n {}) l ==> MAP unconvert_t (MAP convert_t l) = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONS_11] THEN
  MATCH_MP_TAC check_t_empty_unconvert_convert_id THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[]);;

let INFER1AUX_ALL_ZIP_MAP_EQ = prove
 (`!(f:A->B) l1 l2.
     LENGTH l1 = LENGTH l2 /\ MAP f l1 = MAP f l2 ==> ALL (\(x,y). f x = f y) (ZIP l1 l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; ALL; MAP; CONS_11] THEN
  ASM_MESON_TAC[]);;

let constrain_op_complete_simple_helper = prove
 (`!st constraints s op ts t ts' n.
     sub_completion n (infer_st_next_uvar st) (infer_st_subst st) constraints s /\
     type_op op ts t /\
     MAP (convert_t o t_walkstar s) ts' = ts /\
     FST (op_simple_constraints op) /\
     FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
     FDOM s = count (infer_st_next_uvar st) /\
     t_wfs (infer_st_subst st) /\
     ALL (check_t n {}) (MAP (t_walkstar s) ts') /\
     check_freevars n [] t
     ==> ?(st':infer_st) xs t'.
           t = convert_t (t_walkstar s t') /\
           pure_add_constraints s xs s /\
           (!l st'.
              infer_st_next_uvar st' = infer_st_next_uvar st /\
              infer_st_next_id st' = infer_st_next_id st /\
              pure_add_constraints (infer_st_subst st) xs (infer_st_subst st')
              ==> constrain_op l op ts' st = (M_success t',st'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  MP_TAC(ISPEC `op_simple_constraints op` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `p:infer_t list#infer_t`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `p:infer_t list#infer_t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:infer_t list` (X_CHOOSE_THEN `ret:infer_t`
    SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `b = T` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FST (op_simple_constraints op)` THEN ASM_REWRITE_TAC[FST]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFER1AUX_simple_ops) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ts:t list`; `t:t`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `MAP (t_walkstar s) ts' = args` ASSUME_TAC THENL
   [SUBGOAL_THEN `MAP convert_t (MAP (t_walkstar s) ts') = MAP convert_t args` MP_TAC THENL
     [REWRITE_TAC[GSYM MAP_o] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `MAP unconvert_t`) THEN
    MP_TAC(ISPECL [`n:num`; `MAP (t_walkstar s) ts'`] INFER1AUX_unconvert_convert_list) THEN
    MP_TAC(ISPECL [`0`; `args:infer_t list`] INFER1AUX_unconvert_convert_list) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun a -> DISCH_THEN(fun b -> REWRITE_TAC[a; b]));
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar s) args = args` ASSUME_TAC THENL
   [REWRITE_TAC[MAP_EQ_ID] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[GSYM ALL_MEM] o
      check (fun th -> concl th = `ALL (check_t 0 {}) (args:infer_t list)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ts':infer_t list) = LENGTH (args:infer_t list)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `MAP (t_walkstar s) ts' = args`
                          then REWRITE_TAC[GSYM th] else failwith "") THEN
    REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ZIP (ts':infer_t list) (args:infer_t list)`; `ret:infer_t`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC t_walkstar_no_vars THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC pure_add_constraints_ignore THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INFER1AUX_ALL_ZIP_MAP_EQ THEN ASM_REWRITE_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[constrain_op_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[inferProps_st_ex_bind_success; inferProps_st_ex_return_success;
                    add_constraints_success; I_THM; MAP_I] THEN
    MAP_EVERY EXISTS_TAC [`one`; `st':infer_st`] THEN ASM_REWRITE_TAC[]]);;
(* constrain_op_complete for an operation whose run is a chain of           *)
(* constraints CS, without and with a fresh unification variable           *)
let INFER1AUX_coc0 = prove
 (`!n st constraints s CS R (run:(infer_t,locs option#mlstring)exc#infer_st) t.
     sub_completion n (infer_st_next_uvar st) (infer_st_subst st) constraints s /\
     FDOM s = count (infer_st_next_uvar st) /\ t_wfs (infer_st_subst st) /\
     ALL (\(x,y). t_walkstar s x = t_walkstar s y) CS /\
     (!s1. pure_add_constraints (infer_st_subst st) CS s1
           ==> run = (M_success R,infer_st_subst_fupd (K s1) st)) /\
     t = convert_t (t_walkstar s R)
     ==> ?t' st' s' constraints'.
           run = (M_success t',st') /\
           sub_completion n (infer_st_next_uvar st') (infer_st_subst st') constraints' s' /\
           t_compat s s' /\
           FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
           FDOM s' = count (infer_st_next_uvar st') /\
           t = convert_t (t_walkstar s' t')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `infer_st_next_uvar st`; `infer_st_subst st`;
                 `constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                 `CS:(infer_t#infer_t)list`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`R:infer_t`; `infer_st_subst_fupd (K s1) st`;
                        `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[infer_st_rewrs]);;

let INFER1AUX_coc1 = prove
 (`!n st constraints s CS R (run:(infer_t,locs option#mlstring)exc#infer_st) tt t.
     sub_completion n (infer_st_next_uvar st) (infer_st_subst st) constraints s /\
     FDOM s = count (infer_st_next_uvar st) /\ t_wfs (infer_st_subst st) /\
     check_freevars n [] tt /\
     ALL (\(x,y). t_walkstar (s |++ [(infer_st_next_uvar st,unconvert_t tt)]) x =
                  t_walkstar (s |++ [(infer_st_next_uvar st,unconvert_t tt)]) y) CS /\
     (!s1. pure_add_constraints (infer_st_subst st) CS s1
           ==> run = (M_success R,
                      infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1))
                        (infer_st_subst_fupd (K s1) st))) /\
     t = convert_t (t_walkstar (s |++ [(infer_st_next_uvar st,unconvert_t tt)]) R)
     ==> ?t' st' s' constraints'.
           run = (M_success t',st') /\
           sub_completion n (infer_st_next_uvar st') (infer_st_subst st') constraints' s' /\
           t_compat s s' /\
           FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
           FDOM s' = count (infer_st_next_uvar st') /\
           t = convert_t (t_walkstar s' t')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `infer_st_next_uvar st`; `infer_st_subst st`;
                 `constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                 `CS:(infer_t#infer_t)list`; `tt:t`] INFER1AUX_cs_core1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`R:infer_t`;
                        `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1))
                           (infer_st_subst_fupd (K s1) st)`;
                        `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[infer_st_rewrs]);;
let INFER1AUX_MAP_EQ_CONS2 = prove
 (`!(f:A->B) l h t.
     MAP f l = CONS h t <=> ?x0 t0. l = CONS x0 t0 /\ h = f x0 /\ MAP f t0 = t`,
  REWRITE_TAC[MAP_EQ_CONS] THEN MESON_TAC[]);;

(* the shape of the arguments of a typed operation *)
let INFER1AUX_COC_SHAPE_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[type_op_cases; distinctness "op"; injectivity "op"] o
    check (fun th -> INFER1AUX_ec_is_app "type_op" (concl th))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    INFER1AUX_ec_is_app "MAP" (lhs(concl th)))) THEN
  REWRITE_TAC[INFER1AUX_MAP_EQ_CONS2; MAP_EQ_NIL; o_THM] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* t_walkstar s x = unconvert_t A, for every A = convert_t (t_walkstar s x) *)
let INFER1AUX_UNCONV_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let is_walk tm = INFER1AUX_ec_is_app "t_walkstar" tm in
  let grounds = filter (fun th -> INFER1AUX_ec_is_app "check_t" (concl th) &&
                                  (try is_walk (rand(concl th)) with Failure _ -> false)) ths in
  let us = mapfilter (MATCH_MP check_t_empty_unconvert_convert_id) grounds in
  let eqs = filter (fun th -> is_eq(concl th) &&
                     (try INFER1AUX_ec_is_app "convert_t" (rhs(concl th)) &&
                          is_walk (rand(rhs(concl th))) with Failure _ -> false)) ths in
  let mk th =
    let th1 = AP_TERM `unconvert_t` (SYM th) in
    REWRITE_RULE (unconvert_t_def :: MAP :: us) th1 in
  MAP_EVERY (ASSUME_TAC o mk) eqs gl;;

(* evaluate a run of constrain_op on unifications given as assumptions *)
let INFER1AUX_COC_RUN_TAC : tactic =
  GEN_TAC THEN REWRITE_TAC[pure_add_constraints_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[constrain_op_def; op_simple_constraints_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[st_ex_bind_def; st_ex_return_def; fresh_uvar_def; add_constraint_def] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[]));;

let INFER1AUX_ext_facts = prove
 (`!n m s tt.
     t_wfs s /\ FDOM s = count m /\
     (!uv. uv IN FDOM s ==> check_t n {} (t_walkstar s (Infer_Tuvar uv))) /\
     check_freevars n [] tt
     ==> t_wfs (s |++ [(m,unconvert_t tt)]) /\ s SUBMAP (s |++ [(m,unconvert_t tt)]) /\
         t_walkstar (s |++ [(m,unconvert_t tt)]) (Infer_Tuvar m) = unconvert_t tt /\
         (!x. check_t n {} (t_walkstar s x)
              ==> t_walkstar (s |++ [(m,unconvert_t tt)]) x = t_walkstar s x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`infer_st_REC m s 0`; `s:(num,infer_t)fmap`; `[]:(infer_t#infer_t)list`;
                 `n:num`; `tt:t`] extend_one_props) THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accessors; pure_add_constraints_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC submap_t_walkstar_replace THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

(* convert_t (unconvert_t t) = t for the checked types of the assumptions *)
let INFER1AUX_CU_TAC : thm_tactic -> tactic = fun ttac (asl,w as gl) ->
  let ths = mapfilter (MATCH_MP check_freevars_empty_convert_unconvert_id) (map snd asl) in
  MAP_EVERY ttac ths gl;;

(* the closing steps of a case of constrain_op_complete *)
let INFER1AUX_COC_CLOSE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [INFER1AUX_COC_RUN_TAC THEN
         TRY(REWRITE_TAC[PAIR_EQ; injectivity "exc"; infer_st_component_equality;
                         infer_st_rewrs; infer_st_INFO.ri_accfupds; K_THM]) THEN NO_TAC;
         INFER1AUX_CU_TAC ASSUME_TAC THEN
         ASM_SIMP_TAC[t_walkstar_eqn1; MAP; convert_t_def; unconvert_t_def] THEN NO_TAC;
         ALL_TAC];;

(* check_freevars of the types A in the facts A = convert_t (t_walkstar s x) *)
let INFER1AUX_ARGCHECK_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let is_walk tm = INFER1AUX_ec_is_app "t_walkstar" tm in
  let grounds = filter (fun th -> INFER1AUX_ec_is_app "check_t" (concl th) &&
                                  (try is_walk (rand(concl th)) with Failure _ -> false)) ths in
  let cfs = mapfilter (fun g -> SPEC_ALL (MATCH_MP check_t_to_check_freevars g)) grounds in
  let eqs = filter (fun th -> is_eq(concl th) &&
                     (try INFER1AUX_ec_is_app "convert_t" (rhs(concl th)) &&
                          is_walk (rand(rhs(concl th))) with Failure _ -> false)) ths in
  let res = mapfilter (fun eq ->
      let cf = find (fun c -> rand(concl c) = rhs(concl eq)) cfs in
      REWRITE_RULE[check_freevars_def; ALL] (REWRITE_RULE[SYM eq] cf)) eqs in
  MAP_EVERY STRIP_ASSUME_TAC res gl;;

let INFER1AUX_COC_NF_TAC cs r : tactic =
  MATCH_MP_TAC INFER1AUX_coc0 THEN
  MAP_EVERY EXISTS_TAC [`st:infer_st`; `constraints:(infer_t#infer_t)list`; cs; r] THEN
  ASM_REWRITE_TAC[ALL] THEN INFER1AUX_COC_CLOSE_TAC;;

let INFER1AUX_COC_F_TAC cs r tt : tactic =
  MP_TAC(SPECL [`n:num`; `infer_st_next_uvar st`; `s:(num,infer_t)fmap`; tt]
    INFER1AUX_ext_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC INFER1AUX_coc1 THEN
  MAP_EVERY EXISTS_TAC [`st:infer_st`; `constraints:(infer_t#infer_t)list`; cs; r; tt] THEN
  ASM_REWRITE_TAC[ALL] THEN INFER1AUX_COC_CLOSE_TAC;;
let INFER1AUX_COC_PRE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  INFER1AUX_COC_SHAPE_TAC THEN INFER1AUX_UNCONV_TAC THEN INFER1AUX_ARGCHECK_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[check_freevars_def; ALL]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (try INFER1AUX_ec_is_app "convert_t" (rhs(concl th)) &&
         INFER1AUX_ec_is_app "t_walkstar" (rand(rhs(concl th))) with Failure _ -> false))));;

let INFER1AUX_COC_PRE2_TAC =
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  INFER1AUX_COC_SHAPE_TAC THEN INFER1AUX_UNCONV_TAC THEN INFER1AUX_ARGCHECK_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[check_freevars_def; ALL]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (try INFER1AUX_ec_is_app "convert_t" (rhs(concl th)) &&
         INFER1AUX_ec_is_app "t_walkstar" (rand(rhs(concl th))) with Failure _ -> false))));;
let INFER1AUX_COC_EQUALITY_TAC =
  INFER1AUX_COC_NF_TAC `[x0:infer_t, x0':infer_t]` `Infer_Tapp [] Tbool_num`;;
let INFER1AUX_COC_OPAPP_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [x0'; Infer_Tuvar (infer_st_next_uvar st)] Tfn_num]`
    `Infer_Tuvar (infer_st_next_uvar st)` `t:t`;;
let INFER1AUX_COC_OPASSIGN_TAC =
  INFER1AUX_COC_NF_TAC `[x0:infer_t, Infer_Tapp [x0'] Tref_num]` `Infer_Tapp [] Ttup_num`;;
let INFER1AUX_COC_OPREF_TAC =
  INFER1AUX_COC_NF_TAC `[]:(infer_t#infer_t)list` `Infer_Tapp [x0] Tref_num`;;
let INFER1AUX_COC_OPDEREF_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tref_num]`
    `Infer_Tuvar (infer_st_next_uvar st)` `t:t`;;
let INFER1AUX_COC_VFROMLIST_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tlist_num]`
    `Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tvector_num` `a0':t`;;
let INFER1AUX_COC_VSUB_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tvector_num;
      x0':infer_t, Infer_Tapp [] Tint_num]`
    `Infer_Tuvar (infer_st_next_uvar st)` `t:t`;;
let INFER1AUX_COC_VLENGTH_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tvector_num]`
    `Infer_Tapp [] Tint_num` `a0':t`;;
let INFER1AUX_COC_AALLOC_TAC =
  INFER1AUX_COC_NF_TAC `[x0:infer_t, Infer_Tapp [] Tint_num]` `Infer_Tapp [x0'] Tarray_num`;;
let INFER1AUX_COC_AALLOCEMPTY_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [] Ttup_num]`
    `Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tarray_num` `t2:t`;;
let INFER1AUX_COC_ASUB_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tarray_num;
      x0':infer_t, Infer_Tapp [] Tint_num]`
    `Infer_Tuvar (infer_st_next_uvar st)` `t:t`;;
let INFER1AUX_COC_ALENGTH_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tarray_num]`
    `Infer_Tapp [] Tint_num` `a0':t`;;
let INFER1AUX_COC_AUPDATE_TAC =
  INFER1AUX_COC_NF_TAC
    `[x0:infer_t, Infer_Tapp [x0''] Tarray_num; x0':infer_t, Infer_Tapp [] Tint_num]`
    `Infer_Tapp [] Ttup_num`;;
let INFER1AUX_COC_LISTAPPEND_TAC =
  INFER1AUX_COC_F_TAC
    `[x0:infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tlist_num;
      x0':infer_t, Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tlist_num]`
    `Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st)] Tlist_num` `a0':t`;;
(* the simple operations of constrain_op_complete *)
let INFER1AUX_COC_SIMPLE_TAC : tactic =
  MP_TAC(ISPECL [`st:infer_st`; `constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                 `op:op`; `ts:t list`; `t:t`; `ts':infer_t list`; `n:num`]
         constrain_op_complete_simple_helper) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(infer_t#infer_t)list`
    (X_CHOOSE_THEN `t0:infer_t` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`n:num`; `infer_st_next_uvar st`; `infer_st_subst st`;
                 `constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                 `xs:(infer_t#infer_t)list`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC t_compat_pure_add_constraints_2 THEN
    EXISTS_TAC `s:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[sub_completion_wfs];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t0:infer_t`; `infer_st_subst_fupd (K s1) st`;
                        `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[infer_st_rewrs; infer_st_INFO.ri_accfupds; K_THM];;

(* an operation that is not simple, but is one of the simple ones or does *)
(* not type                                                                *)
let INFER1AUX_COC_IMPOSSIBLE_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[type_op_cases; distinctness "op"; injectivity "op"] o
    check (fun th -> INFER1AUX_ec_is_app "type_op" (concl th))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
    (try INFER1AUX_ec_is_app "FST" (dest_neg(concl th)) with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[op_simple_constraints_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[];;

let INFER1AUX_COC_DISPATCH_TAC : tactic = fun (asl,w as gl) ->
  let tm = find_term (fun t -> INFER1AUX_ec_is_app "constrain_op" t) w in
  let op = el 1 (snd(strip_comb tm)) in
  let name = fst(dest_const(fst(strip_comb op))) in
  let tac = assoc name
    ["Equality", INFER1AUX_COC_EQUALITY_TAC; "Opapp", INFER1AUX_COC_OPAPP_TAC;
     "Opassign", INFER1AUX_COC_OPASSIGN_TAC; "Opref", INFER1AUX_COC_OPREF_TAC;
     "Opderef", INFER1AUX_COC_OPDEREF_TAC; "VfromList", INFER1AUX_COC_VFROMLIST_TAC;
     "Vsub", INFER1AUX_COC_VSUB_TAC; "Vlength", INFER1AUX_COC_VLENGTH_TAC;
     "Aalloc", INFER1AUX_COC_AALLOC_TAC; "AallocEmpty", INFER1AUX_COC_AALLOCEMPTY_TAC;
     "Asub", INFER1AUX_COC_ASUB_TAC; "Alength", INFER1AUX_COC_ALENGTH_TAC;
     "Aupdate", INFER1AUX_COC_AUPDATE_TAC; "ListAppend", INFER1AUX_COC_LISTAPPEND_TAC] in
  tac gl;;

let constrain_op_complete = prove
 (`!op ts t st constraints s ts' l n.
     type_op op ts t /\
     sub_completion n (infer_st_next_uvar st) (infer_st_subst st) constraints s /\
     FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
     FDOM s = count (infer_st_next_uvar st) /\
     t_wfs (infer_st_subst st) /\
     MAP (convert_t o t_walkstar s) ts' = ts /\
     ALL (check_t n {}) (MAP (t_walkstar s) ts') /\
     check_freevars n [] t
     ==> ?t' st' s' constraints'.
           constrain_op l op ts' st = (M_success t',st') /\
           sub_completion n (infer_st_next_uvar st') (infer_st_subst st') constraints' s' /\
           t_compat s s' /\
           FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
           FDOM s' = count (infer_st_next_uvar st') /\
           t = convert_t (t_walkstar s' t')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `FST (op_simple_constraints op)` THENL
   [INFER1AUX_COC_SIMPLE_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `op:op` (cases "op")) THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  TRY(INFER1AUX_COC_IMPOSSIBLE_TAC THEN NO_TAC) THEN
  INFER1AUX_COC_PRE2_TAC THEN INFER1AUX_COC_DISPATCH_TAC);;
(* ---------- patterns ---------- *)

let simp_tenv_invC_def = cake_def
  `simp_tenv_invC (s:(num,infer_t)fmap) (tvs:num) (tenv:(A#infer_t)list)
                  (tenvE:(A#t)list) <=>
     (!n t. ALOOKUP tenvE n = SOME t
            ==> check_freevars tvs [] t /\
                ?t'. ALOOKUP tenv n = SOME t' /\ unconvert_t t = t_walkstar s t') /\
     (!n t'. ALOOKUP tenv n = SOME t' ==> ?t. ALOOKUP tenvE n = SOME t)`;;

let simp_tenv_invC_empty = prove
 (`!s n. simp_tenv_invC s n ([]:(A#infer_t)list) ([]:(A#t)list)`,
  REWRITE_TAC[simp_tenv_invC_def; ALOOKUP_THM; option_DISTINCT]);;

let simp_tenv_invC_more = prove
 (`!s s' tvs (tenv:(A#infer_t)list) tenvE.
     simp_tenv_invC s tvs tenv tenvE /\ t_compat s s'
     ==> simp_tenv_invC s' tvs tenv tenvE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simp_tenv_invC_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[t_compat_def] o
    check (fun th -> INFER1AUX_ec_is_app "t_compat" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:A`; `t:t`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t':infer_t` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `t':infer_t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s t')` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      INFER1AUX_ec_is_app "unconvert_t" (lhs(concl th)))) THEN
    MATCH_MP_TAC check_freevars_to_check_t THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':infer_t` o check (fun th -> is_forall(concl th) &&
    (try INFER1AUX_ec_is_app "t_walkstar" (lhs(snd(dest_forall(concl th))))
     with Failure _ -> false))) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `tvs:num` THEN
  ASM_REWRITE_TAC[]);;
let simp_tenv_invC_append = prove
 (`!s'' tvs (tenv:(A#infer_t)list) tenvE tenv' tenvE'.
     simp_tenv_invC s'' tvs tenv tenvE /\ simp_tenv_invC s'' tvs tenv' tenvE'
     ==> simp_tenv_invC s'' tvs (APPEND tenv' tenv) (APPEND tenvE' tenvE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simp_tenv_invC_def; ALOOKUP_APPEND] THEN
  STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `k:A` THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SPEC `k:A` o check (fun th ->
    is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:A`))) THEN
  MAP_EVERY (fun (tm,v) ->
     DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN v SUBST_ALL_TAC)
       (ISPEC tm (cases "option")))
    [`ALOOKUP (tenvE:(A#t)list) k`, `e1:t`; `ALOOKUP (tenv:(A#infer_t)list) k`, `e2:infer_t`;
     `ALOOKUP (tenvE':(A#t)list) k`, `e3:t`; `ALOOKUP (tenv':(A#infer_t)list) k`, `e4:infer_t`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; injectivity "option"; option_DISTINCT;
                              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; UNWIND_THM1;
                              UNWIND_THM2]) THEN
  REWRITE_TAC[option_CASE; injectivity "option"; option_DISTINCT;
              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; UNWIND_THM1; UNWIND_THM2] THEN
  ASM_MESON_TAC[]);;

let convert_bi_remove = prove
 (`!A B n m.
     convert_t A = convert_t B /\ check_t n {} A /\ check_t m {} B ==> A = B`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `unconvert_t` o check (fun th -> is_eq(concl th))) THEN
  ASM_MESON_TAC[check_t_empty_unconvert_convert_id]);;

let infer_type_subst_check_t_less = prove
 (`!ls tvs n.
     LENGTH ls = LENGTH tvs /\ ALL (check_t n {}) ls
     ==> (!t. check_freevars n tvs t
              ==> check_t n {} (infer_type_subst (ZIP tvs ls) t)) /\
         (!ts. ALL (check_freevars n tvs) ts
               ==> ALL (check_t n {}) (MAP (infer_type_subst (ZIP tvs ls)) ts))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[check_freevars_def; infer_type_subst_alt; check_t_def; ALL; MAP] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:mlstring` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x. ALOOKUP (ZIP (tvs:mlstring list) (ls:infer_t list)) v = SOME x`
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[cases "option"]
        `~((o1:infer_t option) = NONE) ==> ?x. o1 = SOME x`) THEN
      REWRITE_TAC[ALOOKUP_NONE] THEN ASM_SIMP_TAC[MAP_FST_ZIP];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    ASM_SIMP_TAC[MEM_ZIP] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM ALL_EL] o check (fun th ->
      concl th = `ALL (check_t n {}) (ls:infer_t list)`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;
(* forward evaluation of a run of infer_p from runs given as assumptions *)
let INFER1AUX_P_RUN_TAC : tactic =
  REWRITE_TAC[infer_p_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[st_ex_bind_def; st_ex_return_def; fresh_uvar_def; add_constraint_def] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[])) THEN
  TRY(REWRITE_TAC[PAIR_EQ; injectivity "exc"; infer_st_component_equality;
                  infer_st_rewrs; infer_st_INFO.ri_accfupds; K_THM]);;

let INFER1AUX_IPC_CLOSE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [INFER1AUX_P_RUN_TAC THEN NO_TAC;
         MATCH_MP_TAC SUBMAP_t_compat THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[simp_tenv_invC_empty] THEN NO_TAC;
         REWRITE_TAC[simp_tenv_invC_def; ALOOKUP_THM] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
         COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
         REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
         MESON_TAC[];
         MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count (infer_st_next_uvar st)` THEN
         ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ARITH_TAC;
         INFER1AUX_CU_TAC ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         ALL_TAC];;

let INFER1AUX_ec_tydefs =
  [typeSystem_Tarray_def; typeSystem_Tbool_def; typeSystem_Tchar_def; typeSystem_Texn_def;
   typeSystem_Tfn_def; typeSystem_Tint_def; typeSystem_Tlist_def; typeSystem_Tref_def;
   typeSystem_Tstring_def; typeSystem_Ttup_def; typeSystem_Tvector_def;
   typeSystem_Tword64_def; typeSystem_Tword8_def; typeSystem_Tword8array_def;
   typeSystem_Tdouble_def];;

(* the start of a case of infer_p_complete *)
let INFER1AUX_IPC_START_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC];;

let INFER1AUX_IPC_LIT_TAC tm : tactic =
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  (fun (asl,w as gl) ->
     let sc = find (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th)) (map snd asl) in
     let s = rand(concl sc) in
     (SUBGOAL_THEN (mk_comb(`t_wfs:(num,infer_t)fmap->bool`, s)) ASSUME_TAC THENL
       [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [tm; `[]:(mlstring#infer_t)list`; `st:infer_st`; s;
                            `constraints:(infer_t#infer_t)list`]) gl) THEN
  ASM_SIMP_TAC[t_compat_refl; t_walkstar_eqn1; MAP; convert_t_def] THEN
  REWRITE_TAC INFER1AUX_ec_tydefs THEN INFER1AUX_IPC_CLOSE_TAC;;

(* HOL4 proves this after infer_p_complete; it is needed there *)
let sub_completion_completes = prove
 (`!s n t tvs.
     t_wfs s /\ check_t 0 (count n) t /\ FDOM s = count n /\
     (!uv. uv < n ==> check_t tvs {} (t_walkstar s (Infer_Tuvar uv)))
     ==> check_t tvs {} (t_walkstar s t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT1(SPECL [`s:(num,infer_t)fmap`; `tvs:num`; `count n`] check_t_less)) THEN
  DISCH_THEN(MP_TAC o SPEC `t:infer_t`) THEN ASM_REWRITE_TAC[IN_COUNT] THEN
  SUBGOAL_THEN `count n INTER COMPL (count n) = {}` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; COMPL_DEF; IN_DIFF; IN_UNIV; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;
(* apply an induction hypothesis of infer_p_complete *)
let INFER1AUX_IPC_IH_TAC ls (names:term list) : tactic =
  FIRST_X_ASSUM(MP_TAC o SPECL ls o check (fun th ->
    let c = concl th in is_forall c &&
      (try is_exists(snd(dest_imp(snd(strip_forall c)))) with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    let rec chs ns th = match ns with
        [] -> STRIP_ASSUME_TAC th
      | n::rest -> X_CHOOSE_THEN n (chs rest) th in
    chs names th);;

(* t_wfs of the completing substitution of a run *)
let INFER1AUX_IPC_WFS_TAC (st1:term) (s1:term) : tactic =
  SUBGOAL_THEN (mk_comb(`t_wfs:(num,infer_t)fmap->bool`, mk_comb(`infer_st_subst`, st1)))
    ASSUME_TAC THENL [ASM_MESON_TAC[infer_p_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(`t_wfs:(num,infer_t)fmap->bool`, s1)) ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC];;

let INFER1AUX_IPC_PREF_TAC : tactic =
  INFER1AUX_IPC_START_TAC THEN
  INFER1AUX_IPC_IH_TAC [`l:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    [`t1:infer_t`; `nb1:(mlstring#infer_t)list`; `st1:infer_st`;
     `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st1:infer_st` `s1:(num,infer_t)fmap` THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tapp [t1] Tref_num`; `nb1:(mlstring#infer_t)list`;
    `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP; convert_t_def] THEN
  REWRITE_TAC INFER1AUX_ec_tydefs THEN INFER1AUX_IPC_CLOSE_TAC;;

let INFER1AUX_IPC_PCON_NONE_TAC : tactic =
  INFER1AUX_IPC_START_TAC THEN
  INFER1AUX_IPC_IH_TAC [`l:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    [`ts1:infer_t list`; `nb1:(mlstring#infer_t)list`; `st1:infer_st`;
     `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st1:infer_st` `s1:(num,infer_t)fmap` THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tapp ts1 Ttup_num`; `nb1:(mlstring#infer_t)list`;
    `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP; convert_t_def; GSYM MAP_o] THEN
  REWRITE_TAC INFER1AUX_ec_tydefs THEN INFER1AUX_IPC_CLOSE_TAC;;

(* a type with its uvars below the next_uvar of a complete state completes *)
(* to a ground type                                                         *)
let INFER1AUX_sc_ground = prove
 (`!tvs m s1 cs s t.
     sub_completion tvs m s1 cs s /\ FDOM s = count m /\ t_wfs s /\ check_t 0 (count m) t
     ==> check_t tvs {} (t_walkstar s t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC sub_completion_completes THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_COUNT]);;

let INFER1AUX_IPC_PAS_TAC : tactic =
  INFER1AUX_IPC_START_TAC THEN
  INFER1AUX_IPC_IH_TAC [`l:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    [`t1:infer_t`; `nb1:(mlstring#infer_t)list`; `st1:infer_st`;
     `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st1:infer_st` `s1:(num,infer_t)fmap` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_p_check_t) o
    check (fun th -> try INFER1AUX_ec_is_app "infer_p" (lhs(concl th))
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s1 t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1:infer_t`; `APPEND nb1 [(v:mlstring,t1:infer_t)]`;
    `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [INFER1AUX_P_RUN_TAC; ALL_TAC] THEN
  MATCH_MP_TAC simp_tenv_invC_append THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simp_tenv_invC_def; ALOOKUP_THM] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
  TRY(MESON_TAC[] THEN NO_TAC) THEN
  FIRST
   [MATCH_MP_TAC check_t_to_check_freevars THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC check_t_empty_unconvert_convert_id THEN EXISTS_TAC `tvs:num` THEN
    ASM_REWRITE_TAC[]];;

(* the induction hypothesis about a run of fname *)
let INFER1AUX_IPC_IHF_TAC fname ls (names:term list) : tactic =
  FIRST_X_ASSUM(MP_TAC o SPECL ls o check (fun th ->
    let c = concl th in is_forall c &&
      (try let e = snd(dest_imp(snd(strip_forall c))) in
           let body = snd(strip_exists e) in
           INFER1AUX_ec_is_app fname (lhs(hd(conjuncts body)))
       with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    let rec chs ns th = match ns with
        [] -> STRIP_ASSUME_TAC th
      | n::rest -> X_CHOOSE_THEN n (chs rest) th in
    chs names th);;

let INFER1AUX_IPC_PSCONS_TAC : tactic =
  INFER1AUX_IPC_START_TAC THEN
  INFER1AUX_IPC_IHF_TAC "infer_p" [`l:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    [`t1:infer_t`; `nb1:(mlstring#infer_t)list`; `st1:infer_st`;
     `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st1:infer_st` `s1:(num,infer_t)fmap` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_p_check_t) o
    check (fun th -> try INFER1AUX_ec_is_app "infer_p" (lhs(concl th))
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s1 t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  INFER1AUX_IPC_IHF_TAC "infer_ps" [`l:loc_err_info`; `s1:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st1:infer_st`; `cs1:(infer_t#infer_t)list`]
    [`ts2:infer_t list`; `nb2:(mlstring#infer_t)list`; `st2:infer_st`;
     `s2:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st2:infer_st` `s2:(num,infer_t)fmap` THEN
  SUBGOAL_THEN `t_walkstar s2 t1 = t_walkstar s1 t1` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t1:infer_t` o CONJUNCT2 o CONJUNCT2 o
      REWRITE_RULE[t_compat_def] o check (fun th -> concl th = `t_compat s1 s2`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC t_walkstar_no_vars THEN
    EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`CONS (t1:infer_t) ts2`; `APPEND nb2 nb1:(mlstring#infer_t)list`;
    `st2:infer_st`; `s2:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[MAP; o_THM] THEN REPEAT CONJ_TAC THENL
   [INFER1AUX_P_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans];
    MATCH_MP_TAC simp_tenv_invC_append THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC simp_tenv_invC_more THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[]];;

let INFER1AUX_IPC_PTANNOT_TAC : tactic =
  INFER1AUX_IPC_START_TAC THEN
  INFER1AUX_IPC_IHF_TAC "infer_p" [`l:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    [`t1:infer_t`; `nb1:(mlstring#infer_t)list`; `st1:infer_st`;
     `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st1:infer_st` `s1:(num,infer_t)fmap` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 infer_p_check_t) o
    check (fun th -> try INFER1AUX_ec_is_app "infer_p" (lhs(concl th))
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s1 t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tn0 = type_name_subst (type_env_t tenv) t` THEN
  SUBGOAL_THEN `check_freevars 0 [] tn0` ASSUME_TAC THENL
   [EXPAND_TAC "tn0" THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s1 t1 = infer_type_subst [] tn0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t_walkstar s1 t1`; `tvs:num`] check_t_empty_unconvert_convert_id) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if concl th = `tn0 = convert_t (t_walkstar s1 t1)`
                          then REWRITE_TAC[GSYM th] else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(CONJUNCT1(SPEC `0` infer_type_subst_nil)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `tn0 = convert_t (t_walkstar s1 t1)`)) THEN
  MP_TAC(ISPECL [`tvs:num`; `infer_st_next_uvar st1`; `infer_st_subst st1`;
                 `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`;
                 `[t1:infer_t, infer_type_subst [] tn0]`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[ALL] THEN ANTS_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(CONJUNCT1 infer_type_subst_empty_check) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pure_add_constraints_def] o check (fun th ->
    INFER1AUX_ec_is_app "pure_add_constraints" (concl th) &&
    rand(concl th) = `s2:(num,infer_t)fmap`)) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:ast_t`; `l:loc_err_info`;
    `\tv. mlstring_concat [implode "Type variable "; tv;
                           implode " found in type annotation. ";
                           implode "Type variables are not supported in type annotations."]`;
    `inf_env_inf_t ienv`; `[]:mlstring list`; `st1:infer_st`; `tn0:t`]
    (CONJUNCT1 type_name_check_subst_comp_thm)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:infer_t`; `nb1:(mlstring#infer_t)list`;
    `infer_st_subst_fupd (K s2) st1`; `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN REPEAT CONJ_TAC THEN
  FIRST [INFER1AUX_P_RUN_TAC THEN NO_TAC;
         MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC simp_tenv_invC_more THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MP_TAC(SPEC `tn0:t` (CONJUNCT1 (SPEC `0` infer_type_subst_nil))) THEN
         ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
         MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN EXISTS_TAC `0` THEN
         ASM_REWRITE_TAC[]];;

let INFER1AUX_sc_ground_list = prove
 (`!tvs m s1 cs s ts.
     sub_completion tvs m s1 cs s /\ FDOM s = count m /\ t_wfs s /\
     ALL (check_t 0 (count m)) ts
     ==> ALL (check_t tvs {}) (MAP (t_walkstar s) ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> INFER1AUX_ec_is_app "ALL" (concl th))) THEN
  MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC INFER1AUX_sc_ground THEN ASM_MESON_TAC[]);;

(* walking a list of ground types with a larger substitution *)
let INFER1AUX_walk_list_submap = prove
 (`!tvs s s' ts.
     t_wfs s' /\ s SUBMAP s' /\ ALL (check_t tvs {}) (MAP (t_walkstar s) ts)
     ==> MAP (t_walkstar s') ts = MAP (t_walkstar s) ts`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL; CONS_11] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC submap_t_walkstar_replace THEN
  EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_unconvert_list_check = prove
 (`!tvs ts'. ALL (check_freevars tvs []) ts' ==> ALL (check_t tvs {}) (MAP unconvert_t ts')`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC check_freevars_to_check_t THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_convert_unconvert_list = prove
 (`!tvs ts'. ALL (check_freevars tvs []) ts' ==> MAP convert_t (MAP unconvert_t ts') = ts'`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN
  EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[]);;

(* MAP convert_t is injective on lists of ground types *)
let INFER1AUX_ground_list_eq = prove
 (`!n m l1 l2.
     ALL (check_t n {}) l1 /\ ALL (check_t m {}) l2 /\ MAP convert_t l1 = MAP convert_t l2
     ==> l1 = l2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `l1:infer_t list`] INFER1AUX_unconvert_convert_list) THEN
  MP_TAC(ISPECL [`m:num`; `l2:infer_t list`] INFER1AUX_unconvert_convert_list) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* the constraints of a constructor pattern hold in the extended completion *)
let INFER1AUX_pcon_constraints = prove
 (`!tvs s1 s'' (ts1:infer_t list) tvs' ts ts' u.
     t_wfs s'' /\ t_wfs s1 /\ s1 SUBMAP s'' /\
     ALL (check_t tvs {}) (MAP (t_walkstar s1) ts1) /\
     ALL (check_freevars tvs []) ts' /\ LENGTH ts' = LENGTH tvs' /\
     ALL (check_freevars 0 tvs') ts /\
     (!n. n < LENGTH ts'
          ==> t_walkstar s'' (Infer_Tuvar (u + n)) = EL n (MAP unconvert_t ts')) /\
     MAP (type_subst (alist_to_fmap (ZIP tvs' ts'))) ts = MAP (convert_t o t_walkstar s1) ts1
     ==> MAP (t_walkstar s'') ts1 =
         MAP (t_walkstar s'')
           (MAP (infer_type_subst
                   (ZIP tvs' (MAP (\n. Infer_Tuvar (u + n)) (COUNT_LIST (LENGTH tvs'))))) ts)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tvs:num`; `s1:(num,infer_t)fmap`; `s'':(num,infer_t)fmap`;
                 `ts1:infer_t list`] INFER1AUX_walk_list_submap) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATCH_MP (CONJUNCT2 subst_infer_subst_swap) (ASSUME `t_wfs (s'':(num,infer_t)fmap)`)] THEN
  SUBGOAL_THEN `MAP (\n. t_walkstar s'' (Infer_Tuvar (u + n)))
                    (COUNT_LIST (LENGTH (tvs':mlstring list))) = MAP unconvert_t ts'`
    SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ] THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t tvs {})
       (MAP (infer_type_subst (ZIP tvs' (MAP unconvert_t ts'))) ts)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`MAP unconvert_t ts'`; `tvs':mlstring list`; `tvs:num`]
           infer_type_subst_check_t_less) THEN
    ASM_SIMP_TAC[LENGTH_MAP; INFER1AUX_unconvert_list_check] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `ALL (check_freevars 0 tvs') ts`)) THEN
    MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`0`; `tvs':mlstring list`; `x:t`] check_freevars_add) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `tvs:num`) THEN
    REWRITE_TAC[GE; LE_0];
    ALL_TAC] THEN
  MATCH_MP_TAC INFER1AUX_ground_list_eq THEN
  MAP_EVERY EXISTS_TAC [`tvs:num`; `tvs:num`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ts:t list`; `tvs':mlstring list`; `MAP unconvert_t ts'`]
         (CONJUNCT2 convert_t_subst)) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`tvs:num`; `ts':t list`] INFER1AUX_convert_unconvert_list) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[GSYM MAP_o]);;

let INFER1AUX_n_fresh_uvar_eq = prove
 (`!n st. n_fresh_uvar n st =
          (M_success (MAP (\k. Infer_Tuvar (infer_st_next_uvar st + k)) (COUNT_LIST n))
             :(infer_t list,locs option#mlstring)exc,
           infer_st_next_uvar_fupd (K (infer_st_next_uvar st + n)) st)`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[n_fresh_uvar_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; COUNT_LIST_DEF; MAP; ADD_CLAUSES; infer_st_rewrs;
              st_ex_return_def; st_ex_bind_def; fresh_uvar_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[infer_st_rewrs; PAIR_EQ; injectivity "exc"; CONS_11; MAP_MAP_o; o_DEF] THEN
  REWRITE_TAC[infer_st_component_equality; infer_st_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `(a + 1) + n = SUC(a + n)`] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let INFER1AUX_IPC_PCON_SOME_TAC : tactic =
  INFER1AUX_IPC_START_TAC THEN
  INFER1AUX_IPC_IHF_TAC "infer_ps" [`l:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
                        `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    [`ts1:infer_t list`; `nb1:(mlstring#infer_t)list`; `st1:infer_st`;
     `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IPC_WFS_TAC `st1:infer_st` `s1:(num,infer_t)fmap` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT2 infer_p_check_t) o
    check (fun th -> try INFER1AUX_ec_is_app "infer_ps" (lhs(concl th))
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `ALL (check_t tvs {}) (MAP (t_walkstar s1) ts1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground_list THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_freevars 0 tvs') ts` ASSUME_TAC THENL
   [MATCH_MP_TAC tenv_ctor_ok_lookup THEN
    MAP_EVERY EXISTS_TAC [`type_env_c tenv`; `cn:(mlstring,mlstring)id`; `tn:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th) &&
                     rand(concl th) = `s1:(num,infer_t)fmap`)) THEN
  MP_TAC(ISPECL [`st1:infer_st`; `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`;
                 `ts':t list`; `tvs:num`] extend_multi_props) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `s2 = (s1:(num,infer_t)fmap) |++
       ZIP (MAP (\n. infer_st_next_uvar st1 + n) (COUNT_LIST (LENGTH (tvs':mlstring list))))
       (MAP unconvert_t ts')` THEN
  ABBREV_TAC `nc = ZIP (MAP Infer_Tuvar
       (MAP (\n. infer_st_next_uvar st1 + n) (COUNT_LIST (LENGTH (tvs':mlstring list)))))
      (MAP unconvert_t ts')` THEN
  MP_TAC(ISPECL [`tvs:num`; `s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`;
                 `ts1:infer_t list`; `tvs':mlstring list`; `ts:t list`; `ts':t list`;
                 `infer_st_next_uvar st1`] INFER1AUX_pcon_constraints) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (ts1:infer_t list) = LENGTH (ts:t list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:t list->num` o check (fun th ->
      concl th = `MAP (type_subst (alist_to_fmap (ZIP tvs' ts'))) ts =
                  MAP (convert_t o t_walkstar s1) ts1`)) THEN
    REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tvs:num`; `infer_st_next_uvar st1 + LENGTH (tvs':mlstring list)`;
                 `infer_st_subst st1`; `APPEND cs1 nc:(infer_t#infer_t)list`;
                 `s2:(num,infer_t)fmap`;
                 `ZIP (ts1:infer_t list)
                    (MAP (infer_type_subst (ZIP tvs'
                       (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                            (COUNT_LIST (LENGTH (tvs':mlstring list)))))) ts)`]
         INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ALL_ZIP_MAP_EQ THEN ASM_REWRITE_TAC[LENGTH_MAP; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
    [`Infer_Tapp (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                    (COUNT_LIST (LENGTH (tvs':mlstring list)))) tn`;
     `nb1:(mlstring#infer_t)list`;
     `infer_st_subst_fupd (K s3) (infer_st_next_uvar_fupd
        (K (infer_st_next_uvar st1 + LENGTH (tvs':mlstring list))) st1)`;
     `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN
  SUBGOAL_THEN `t_compat s1 (si:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s2:(num,infer_t)fmap` THEN
    ASM_SIMP_TAC[SUBMAP_t_compat];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `add_constraints l ts1
        (MAP (infer_type_subst (ZIP tvs'
           (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                (COUNT_LIST (LENGTH (tvs':mlstring list)))))) ts)
        (infer_st_next_uvar_fupd (K (infer_st_next_uvar st1 + LENGTH (tvs':mlstring list)))
           st1) =
      (M_success one,
       infer_st_subst_fupd (K s3) (infer_st_next_uvar_fupd
          (K (infer_st_next_uvar st1 + LENGTH (tvs':mlstring list))) st1))` ASSUME_TAC THENL
     [REWRITE_TAC[add_constraints_success] THEN
      ASM_REWRITE_TAC[infer_st_rewrs; LENGTH_MAP; infer_st_INFO.ri_accfupds; K_THM];
      ALL_TAC] THEN
    REWRITE_TAC[infer_p_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def; lookup_st_ex_def;
                infer_guard_def; INFER1AUX_n_fresh_uvar_eq] THEN
    REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[]));
    REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC simp_tenv_invC_more THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def; injectivity "t"] THEN
    SUBGOAL_THEN `MAP (t_walkstar s2) (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                     (COUNT_LIST (LENGTH (tvs':mlstring list)))) = MAP unconvert_t ts'`
      SUBST1_TAC THENL
     [REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_COUNT_LIST] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_convert_unconvert_list THEN
    EXISTS_TAC `tvs:num` THEN ASM_REWRITE_TAC[]];;


(* the Pany and Pvar cases: a fresh unification variable, bound to the type *)
let INFER1AUX_IPC_FRESH_TAC nb : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  MP_TAC(ISPECL [`st:infer_st`; `s:(num,infer_t)fmap`; `constraints:(infer_t#infer_t)list`;
                 `tvs:num`; `t:t`] extend_one_props) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tuvar (infer_st_next_uvar st)`; nb;
    `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st`;
    `(s:(num,infer_t)fmap) |++ [(infer_st_next_uvar st, unconvert_t t)]`;
    `APPEND constraints [(Infer_Tuvar (infer_st_next_uvar st), unconvert_t t)]`] THEN
  REWRITE_TAC[infer_st_rewrs] THEN ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN
  INFER1AUX_IPC_CLOSE_TAC;;


let infer_p_complete = prove
 (`(!tvs tenv p t tenvE.
     type_p tvs tenv p t tenvE
     ==> !l s ienv st constraints.
           tenv_ctor_ok (type_env_c tenv) /\
           inf_env_inf_c ienv = type_env_c tenv /\
           inf_env_inf_t ienv = type_env_t tenv /\
           tenv_abbrev_ok (type_env_t tenv) /\
           t_wfs (infer_st_subst st) /\
           sub_completion tvs (infer_st_next_uvar st) (infer_st_subst st) constraints s /\
           FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
           FDOM s = count (infer_st_next_uvar st)
           ==> ?t' new_bindings st' s' constraints'.
                 infer_p l ienv p st = (M_success (t',new_bindings),st') /\
                 sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
                   constraints' s' /\
                 FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
                 FDOM s' = count (infer_st_next_uvar st') /\
                 t_compat s s' /\
                 simp_tenv_invC s' tvs new_bindings tenvE /\
                 t = convert_t (t_walkstar s' t')) /\
   (!tvs tenv ps ts tenvE.
     type_ps tvs tenv ps ts tenvE
     ==> !l s ienv st constraints.
           tenv_ctor_ok (type_env_c tenv) /\
           inf_env_inf_c ienv = type_env_c tenv /\
           inf_env_inf_t ienv = type_env_t tenv /\
           tenv_abbrev_ok (type_env_t tenv) /\
           t_wfs (infer_st_subst st) /\
           sub_completion tvs (infer_st_next_uvar st) (infer_st_subst st) constraints s /\
           FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
           FDOM s = count (infer_st_next_uvar st)
           ==> ?ts' new_bindings st' s' constraints'.
                 infer_ps l ienv ps st = (M_success (ts',new_bindings),st') /\
                 sub_completion tvs (infer_st_next_uvar st') (infer_st_subst st')
                   constraints' s' /\
                 FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
                 FDOM s' = count (infer_st_next_uvar st') /\
                 t_compat s s' /\
                 simp_tenv_invC s' tvs new_bindings tenvE /\
                 ts = MAP (convert_t o t_walkstar s') ts')`,
  MATCH_MP_TAC type_p_strongind THEN REPEAT CONJ_TAC THENL
   [INFER1AUX_IPC_FRESH_TAC `[]:(mlstring#infer_t)list`;
    INFER1AUX_IPC_FRESH_TAC `[(n:mlstring,Infer_Tuvar (infer_st_next_uvar st))]`;
    INFER1AUX_IPC_LIT_TAC `Infer_Tapp [] Tint_num`;
    INFER1AUX_IPC_LIT_TAC `Infer_Tapp [] Tchar_num`;
    INFER1AUX_IPC_LIT_TAC `Infer_Tapp [] Tstring_num`;
    INFER1AUX_IPC_LIT_TAC `Infer_Tapp [] Tword8_num`;
    INFER1AUX_IPC_LIT_TAC `Infer_Tapp [] Tword64_num`;
    INFER1AUX_IPC_PCON_SOME_TAC; INFER1AUX_IPC_PCON_NONE_TAC; INFER1AUX_IPC_PREF_TAC;
    INFER1AUX_IPC_PAS_TAC; INFER1AUX_IPC_PTANNOT_TAC;
    INFER1AUX_IPC_LIT_TAC `[]:infer_t list`; INFER1AUX_IPC_PSCONS_TAC]);;

(* ---------- expressions ---------- *)

let lookup_var_bind_var_list = prove
 (CASE_TERM `!x tenvE tenv bindings.
     lookup_var x (bind_var_list 0 bindings tenvE) tenv =
     match x with
       Short id -> (match ALOOKUP bindings id with
                      SOME t -> SOME (0,t)
                    | NONE -> lookup_var x tenvE tenv)
     | _ -> lookup_var x tenvE tenv`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[tveLookup_bvl] THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (bindings:(mlstring#t)list) a` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[deBruijn_inc0]);;

let INFER1AUX_ALOOKUP_MAP_0 = prove
 (CASE_TERM `!(nb:(mlstring#infer_t)list) k.
     ALOOKUP (MAP (\nt. match nt with (n,t) -> (n,(0,t))) nb) k =
     OPTION_MAP (\t. (0,t)) (ALOOKUP nb k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:mlstring#infer_t`,`h:mlstring#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALOOKUP_THM] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

(* lookups in the environment extended with the bindings of a pattern *)
let INFER1AUX_nsLookup_pat_env = prove
 (CASE_TERM `!(nb:(mlstring#infer_t)list) (E:(mlstring,mlstring,num#infer_t)namespace) x.
     nsLookup (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) nb)) E) x =
     match x with
       Short id -> (match ALOOKUP nb id with SOME t -> SOME (0,t) | NONE -> nsLookup E x)
     | _ -> nsLookup E x`,
  GEN_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `E:(mlstring,mlstring,num#infer_t)namespace` (CONJUNCT1 (cases "namespace"))) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[alist_to_ns_def; nsAppend_def; nsLookup_def; APPEND; ALOOKUP_APPEND;
              INFER1AUX_ALOOKUP_MAP_0] THEN
  CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (nb:(mlstring#infer_t)list) a` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE] THEN CASE_REWRITE_TAC[]);;

(* the environment entry for x of an env_rel_complete, weakened *)
let INFER1AUX_ERC_OLD_TAC : tactic =
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    FIRST_ASSUM(fun ih -> MP_TAC(MATCH_MP ih th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`)
    (X_CHOOSE_THEN `tvs':num` (X_CHOOSE_THEN `t':infer_t` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`tvs':num`; `t':infer_t`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC tscheme_approx_weakening2 THEN EXISTS_TAC `s':(num,infer_t)fmap` THEN
  ASM_REWRITE_TAC[];;

(* env_rel_complete for the environment extended with a pattern's bindings *)
let INFER1AUX_env_rel_complete_pat = prove
 (CASE_TERM `!s' si s'' ienv tenv tenvE (nb:(mlstring#infer_t)list) bindings.
     env_rel_complete s' ienv tenv tenvE /\ t_compat s' si /\ FDOM s' SUBSET FDOM si /\
     t_wfs si /\ t_compat s'' si /\ simp_tenv_invC s'' (num_tvs tenvE) nb bindings
     ==> env_rel_complete si
           (inf_env_inf_v_fupd
              (K (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) nb))
                           (inf_env_inf_v ienv))) ienv)
           tenv (bind_var_list 0 bindings tenvE)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[env_rel_complete_def; inf_env_INFO.ri_accfupds; K_THM; num_tvs_bind_var_list;
              lookup_var_bind_var_list; INFER1AUX_nsLookup_pat_env] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[simp_tenv_invC_def] o
    check (fun th -> INFER1AUX_ec_is_app "simp_tenv_invC" (concl th))) THEN
  MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `tvs:num`; `t:t`] THEN
  MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC; INFER1AUX_ERC_OLD_TAC] THEN
  MP_TAC(ISPEC `ALOOKUP (bindings:(mlstring#t)list) a` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
    (X_CHOOSE_THEN `a':t` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `ALOOKUP (nb:(mlstring#infer_t)list) a = NONE` SUBST1_TAC THENL
     [MATCH_MP_TAC(MESON[cases "option"]
        `(!x. ~((o1:infer_t option) = SOME x)) ==> o1 = NONE`) THEN
      X_GEN_TAC `y:infer_t` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:mlstring`; `y:infer_t`] o check (fun th ->
        is_forall(concl th) &&
        (try free_in `nb:(mlstring#infer_t)list`
               (lhs(fst(dest_imp(snd(strip_forall(concl th)))))) with Failure _ -> false))) THEN
      ASM_REWRITE_TAC[option_DISTINCT];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN UNDISCH_TAC `lookup_var (Short a) tenvE tenv = SOME (tvs,t)` THEN
    INFER1AUX_ERC_OLD_TAC;
    REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:mlstring`; `t:t`] o check (fun th ->
      is_forall(concl th) &&
      (try free_in `bindings:(mlstring#t)list` (fst(dest_imp(snd(strip_forall(concl th)))))
       with Failure _ -> false))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t1:infer_t` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `num_tvs tenvE` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:infer_t`] THEN REWRITE_TAC[] THEN
    REWRITE_TAC[tscheme_approx_def; LENGTH_EQ_NIL] THEN
    EXISTS_TAC `[]:infer_t list` THEN REWRITE_TAC[ALL; MAP] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[infer_deBruijn_subst_id] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `t_compat s'' si`
      then REWRITE_TAC[REWRITE_RULE[t_compat_def] th] else failwith "")]);;

(* forward runs of the monadic steps of infer_pes *)
let INFER1AUX_check_dups_ok = prove
 (`!(l:loc_err_info) (f:A->B) ls (s:S).
     ALL_DISTINCT ls ==> check_dups l f ls s = (M_success one,s)`,
  REWRITE_TAC[check_dups_success]);;

let INFER1AUX_add_constraint_run = prove
 (`!l t1 t2 st s.
     pure_add_constraints (infer_st_subst st) [t1,t2] s
     ==> add_constraint l t1 t2 st = (M_success one,infer_st_subst_fupd (K s) st)`,
  REWRITE_TAC[add_constraint_success2; infer_st_INFO.ri_accfupds; K_THM]);;

let INFER1AUX_infer_pes_cons_run = prove
 (CASE_TERM `!l ienv p e pes0 t1' t2' st0 tp nb st1 s2 tt st3 s4 res.
     infer_p l ienv p st0 = (M_success (tp,nb),st1) /\ ALL_DISTINCT (MAP FST nb) /\
     pure_add_constraints (infer_st_subst st1) [t1',tp] s2 /\
     infer_e l
       (inf_env_inf_v_fupd
          (K (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) nb))
                       (inf_env_inf_v ienv))) ienv) e
       (infer_st_subst_fupd (K s2) st1) = (M_success tt,st3) /\
     pure_add_constraints (infer_st_subst st3) [t2',tt] s4 /\
     infer_pes l ienv pes0 t1' t2' (infer_st_subst_fupd (K s4) st3) = res
     ==> infer_pes l ienv (CONS (p,e) pes0) t1' t2' st0 = res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[infer_e_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INFER1AUX_check_dups_ok] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP INFER1AUX_add_constraint_run
    (ASSUME `pure_add_constraints (infer_st_subst st1) [t1',tp] s2`)] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP INFER1AUX_add_constraint_run
    (ASSUME `pure_add_constraints (infer_st_subst st3) [t2',tt] s4`)] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `res:(1,locs option#mlstring)exc#infer_st` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:(1,locs option#mlstring)exc` (cases "exc")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN MESON_TAC[one]);;

(* a ground type that both walks reach makes them agree *)
let INFER1AUX_ground_eq = prove
 (`!s0 s1 n ta tb u.
     t_compat s0 s1 /\ u = t_walkstar s0 ta /\ u = t_walkstar s1 tb /\ check_t n {} u
     ==> t_walkstar s1 ta = t_walkstar s1 tb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[t_compat_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `ta:infer_t` th)]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `u = t_walkstar s0 ta`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `u = t_walkstar s1 tb`)) THEN
  MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

(* the pattern and the first constraint of a clause of infer_pes *)
let INFER1AUX_pes_pat_step = prove
 (CASE_TERM `!l ienv tenv tenvE uvar p bindings t1 t1' st0 cs0 s0.
     ienv_ok (count uvar) ienv /\ uvar <= infer_st_next_uvar st0 /\
     t_wfs (infer_st_subst st0) /\ env_rel_complete s0 ienv tenv tenvE /\
     ALL_DISTINCT (pat_bindings p) /\ type_p (num_tvs tenvE) tenv p t1 bindings /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st0) (infer_st_subst st0) cs0 s0 /\
     FDOM (infer_st_subst st0) SUBSET count (infer_st_next_uvar st0) /\
     FDOM s0 = count (infer_st_next_uvar st0) /\
     unconvert_t t1 = t_walkstar s0 t1'
     ==> ?tp nb st1 s2 si cs'.
           infer_p l ienv p st0 = (M_success (tp,nb),st1) /\ ALL_DISTINCT (MAP FST nb) /\
           pure_add_constraints (infer_st_subst st1) [t1',tp] s2 /\
           infer_st_next_uvar st0 <= infer_st_next_uvar st1 /\
           check_t (num_tvs tenvE) {} (unconvert_t t1) /\
           t_wfs s2 /\ FDOM s2 SUBSET count (infer_st_next_uvar st1) /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st1) s2 cs' si /\
           FDOM si = count (infer_st_next_uvar st1) /\ t_compat s0 si /\
           ienv_ok (count (infer_st_next_uvar st1))
             (inf_env_inf_v_fupd
               (K (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) nb))
                            (inf_env_inf_v ienv))) ienv) /\
           env_rel_complete si
             (inf_env_inf_v_fupd
               (K (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) nb))
                            (inf_env_inf_v ienv))) ienv)
             tenv (bind_var_list 0 bindings tenvE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `unconvert_t t1 = t_walkstar s0 t1'`)) THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv /\ inf_env_inf_c ienv = type_env_c tenv`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `env_rel_complete s0 ienv tenv tenvE` THEN
    REWRITE_TAC[env_rel_complete_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tenv_ctor_ok (type_env_c tenv) /\ tenv_abbrev_ok (type_env_t tenv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok (count uvar) ienv` THEN ASM_REWRITE_TAC[ienv_ok_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `tenv:type_env`; `p:pat`; `t1:t`;
                `bindings:(mlstring#t)list`] (CONJUNCT1 infer_p_complete)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:loc_err_info`; `s0:(num,infer_t)fmap`; `ienv:inf_env`;
                             `st0:infer_st`; `cs0:(infer_t#infer_t)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:infer_t` (X_CHOOSE_THEN `nb:(mlstring#infer_t)list`
    (X_CHOOSE_THEN `st1:infer_st` (X_CHOOSE_THEN `s1:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs1:(infer_t#infer_t)list` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `infer_st_next_uvar st0 <= infer_st_next_uvar st1` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_next_uvar_mono) THEN
    MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv:inf_env`; `p:pat`; `tp:infer_t`;
                          `nb:(mlstring#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv:inf_env`; `p:pat`; `st0:infer_st`;
                          `tp:infer_t`; `nb:(mlstring#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (nb:(mlstring#infer_t)list))` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (CONJUNCT1 infer_p_bindings)
      (ASSUME `infer_p l ienv p st0 = (M_success (tp,nb),st1)`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_check_t)
    (ASSUME `infer_p l ienv p st0 = (M_success (tp,nb),st1)`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `check_t (num_tvs tenvE) {} (t_walkstar s1 tp)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `unconvert_t t1 = t_walkstar s1 tp` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `t1 = convert_t (t_walkstar s1 tp)`) THEN
    MATCH_MP_TAC check_t_empty_unconvert_convert_id THEN
    EXISTS_TAC `num_tvs tenvE` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t (num_tvs tenvE) {} (unconvert_t t1)` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `unconvert_t t1 = t_walkstar s1 tp`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s1 t1' = t_walkstar s1 tp` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_eq THEN
    MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `num_tvs tenvE`; `unconvert_t t1`] THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `t1 = convert_t (t_walkstar s1 tp)`)) THEN
  MP_TAC(ISPECL [`num_tvs tenvE`; `infer_st_next_uvar st1`; `infer_st_subst st1`;
                 `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`;
                 `[t1':infer_t, tp:infer_t]`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[ALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`tp:infer_t`; `nb:(mlstring#infer_t)list`; `st1:infer_st`;
    `s2:(num,infer_t)fmap`; `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  SUBGOAL_THEN `t_compat s0 (si:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (si:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `uvar <= infer_st_next_uvar st1` ASSUME_TAC THENL
   [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_wfs THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st1`; `[t1':infer_t, tp:infer_t]`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
    MP_TAC(SPECL [`uvar:num`; `infer_st_next_uvar st1`; `ienv:inf_env`] ienv_ok_more) THEN
    ASM_REWRITE_TAC[ienv_ok_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_pes THEN
    ASM_REWRITE_TAC[GSYM every_shim];
    MATCH_MP_TAC INFER1AUX_env_rel_complete_pat THEN
    MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;

(* a ground walk is preserved by a compatible substitution *)
let INFER1AUX_ground_transfer = prove
 (`!s0 s1 n ta u.
     t_compat s0 s1 /\ u = t_walkstar s0 ta /\ check_t n {} u ==> u = t_walkstar s1 ta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[t_compat_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `ta:infer_t` th)]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `u = t_walkstar s0 ta`)) THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

(* the second constraint of a clause of infer_pes *)
let INFER1AUX_pes_exp_step = prove
 (`!n s0 s3 st3 cs3 t2 t2' tt.
     t_compat s0 s3 /\ unconvert_t t2 = t_walkstar s0 t2' /\
     sub_completion n (infer_st_next_uvar st3) (infer_st_subst st3) cs3 s3 /\
     FDOM s3 = count (infer_st_next_uvar st3) /\ t_wfs (infer_st_subst st3) /\
     check_t 0 (count (infer_st_next_uvar st3)) tt /\
     t2 = convert_t (t_walkstar s3 tt)
     ==> ?s4 si cs4.
           pure_add_constraints (infer_st_subst st3) [t2',tt] s4 /\
           sub_completion n (infer_st_next_uvar st3) s4 cs4 si /\
           FDOM s4 SUBSET count (infer_st_next_uvar st3) /\
           FDOM si = count (infer_st_next_uvar st3) /\ t_wfs s4 /\
           t_compat s0 si /\ check_t n {} (unconvert_t t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t n {} (t_walkstar s3 tt)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st3`; `infer_st_subst st3`;
                          `cs3:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `unconvert_t t2 = t_walkstar s3 tt` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `t2 = convert_t (t_walkstar s3 tt)`) THEN
    MATCH_MP_TAC check_t_empty_unconvert_convert_id THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t n {} (unconvert_t t2)` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `unconvert_t t2 = t_walkstar s3 tt`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s3 t2' = t_walkstar s3 tt` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_eq THEN
    MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `n:num`; `unconvert_t t2`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `infer_st_next_uvar st3`; `infer_st_subst st3`;
                 `cs3:(infer_t#infer_t)list`; `s3:(num,infer_t)fmap`;
                 `[t2':infer_t, tt:infer_t]`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[ALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs4:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`s4:(num,infer_t)fmap`; `si:(num,infer_t)fmap`;
                        `cs4:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_wfs THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st3`; `[t2':infer_t, tt:infer_t]`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s3:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[]]);;

(* apply a lemma to the infer_e assumption *)
let INFER1AUX_IE_TAC (thm:thm) : tactic =
  FIRST_ASSUM(fun th ->
    if (try INFER1AUX_ec_is_app "infer_e" (lhs(concl th)) with Failure _ -> false)
    then MP_TAC(MATCH_MP thm th) else failwith "INFER1AUX_IE_TAC");;

let infer_pes_complete = prove
 (`!l ienv tenv tenvE uvar t1 t2 t1' t2' pes st' constraints' s'.
     ~(pes = []) /\
     ienv_ok (count uvar) ienv /\
     uvar <= infer_st_next_uvar st' /\
     t_wfs (infer_st_subst st') /\
     env_rel_complete s' ienv tenv tenvE /\
     (!p e. MEM (p,e) pes
            ==> ?bindings.
                  ALL_DISTINCT (pat_bindings p) /\
                  type_p (num_tvs tenvE) tenv p t1 bindings /\
                  type_e tenv (bind_var_list 0 bindings tenvE) e t2 /\
                  !l s'' ienv' st'' constraints''.
                    ienv_ok (count (infer_st_next_uvar st'')) ienv' /\
                    t_wfs (infer_st_subst st'') /\
                    FDOM (infer_st_subst st'') SUBSET count (infer_st_next_uvar st'') /\
                    sub_completion (num_tvs (bind_var_list 0 bindings tenvE))
                      (infer_st_next_uvar st'') (infer_st_subst st'') constraints'' s'' /\
                    FDOM s'' = count (infer_st_next_uvar st'') /\
                    env_rel_complete s'' ienv' tenv (bind_var_list 0 bindings tenvE)
                    ==> ?t'' st''' s''' constraints'''.
                          infer_e l ienv' e st'' = (M_success t'',st''') /\
                          sub_completion (num_tvs tenvE) (infer_st_next_uvar st''')
                            (infer_st_subst st''') constraints''' s''' /\
                          FDOM (infer_st_subst st''') SUBSET
                            count (infer_st_next_uvar st''') /\
                          FDOM s''' = count (infer_st_next_uvar st''') /\
                          t_compat s'' s''' /\
                          t2 = convert_t (t_walkstar s''' t'')) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
       constraints' s' /\
     FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
     FDOM s' = count (infer_st_next_uvar st') /\
     unconvert_t t1 = t_walkstar s' t1' /\
     unconvert_t t2 = t_walkstar s' t2'
     ==> ?st'' s'' constraints''.
           infer_pes l ienv pes t1' t2' st' = (M_success one,st'') /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st'') (infer_st_subst st'')
             constraints'' s'' /\
           FDOM (infer_st_subst st'') SUBSET count (infer_st_next_uvar st'') /\
           FDOM s'' = count (infer_st_next_uvar st'') /\
           t_compat s' s''`,
  MAP_EVERY X_GEN_TAC [`l:loc_err_info`; `ienv:inf_env`; `tenv:type_env`;
    `tenvE:tenv_val_exp`; `uvar:num`; `t1:t`; `t2:t`; `t1':infer_t`; `t2':infer_t`] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:pat#exp`,`h:pat#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pat`; `e:exp`; `st0:infer_st`; `cs0:(infer_t#infer_t)list`;
                       `s0:(num,infer_t)fmap`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p:pat`; `e:exp`] o check (fun th ->
    is_forall(concl th) &&
    (try INFER1AUX_ec_is_app "MEM" (fst(dest_imp(snd(strip_forall(concl th)))))
     with Failure _ -> false))) THEN
  REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `bindings:(mlstring#t)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`l:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
                `uvar:num`; `p:pat`; `bindings:(mlstring#t)list`; `t1:t`; `t1':infer_t`;
                `st0:infer_st`; `cs0:(infer_t#infer_t)list`; `s0:(num,infer_t)fmap`]
         INFER1AUX_pes_pat_step) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:infer_t` (X_CHOOSE_THEN `nb:(mlstring#infer_t)list`
    (X_CHOOSE_THEN `st1:infer_st` (X_CHOOSE_THEN `s2:(num,infer_t)fmap`
    (X_CHOOSE_THEN `si:(num,infer_t)fmap` (X_CHOOSE_THEN `cs':(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(fun th26 ->
    if INFER1AUX_ec_is_app "ienv_ok" (concl th26) &&
       free_in `nb:(mlstring#infer_t)list` (concl th26)
    then let ie = rand(concl th26) in
      FIRST_X_ASSUM(MP_TAC o SPECL [`l:loc_err_info`; `si:(num,infer_t)fmap`; ie;
          `infer_st_subst_fupd (K s2) st1`; `cs':(infer_t#infer_t)list`] o
        check (fun th -> is_forall(concl th) &&
          (try INFER1AUX_ec_is_app "ienv_ok"
                 (hd(conjuncts(fst(dest_imp(snd(strip_forall(concl th)))))))
           with Failure _ -> false)))
    else failwith "") THEN
  REWRITE_TAC[infer_st_rewrs; num_tvs_bind_var_list] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:infer_t` (X_CHOOSE_THEN `st3:infer_st`
    (X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `cs3:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] o
    check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th) &&
                     free_in `nb:(mlstring#infer_t)list` (concl th))) THEN
  INFER1AUX_IE_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT1 infer_e_wfs)) THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN DISCH_TAC THEN
  INFER1AUX_IE_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT1 infer_e_check_t)) THEN
  ASM_REWRITE_TAC[infer_st_rewrs; inf_env_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
  INFER1AUX_IE_TAC (CONJUNCT1 infer_e_next_uvar_mono) THEN
  REWRITE_TAC[infer_st_rewrs] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t_compat s0 (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `si:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `s0:(num,infer_t)fmap`; `s3:(num,infer_t)fmap`;
                `st3:infer_st`; `cs3:(infer_t#infer_t)list`; `t2:t`; `t2':infer_t`;
                `tt:infer_t`] INFER1AUX_pes_exp_step) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:(num,infer_t)fmap` (X_CHOOSE_THEN `si':(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs4:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `uvar <= infer_st_next_uvar st3` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s0 t1' = t_walkstar si' t1'` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `unconvert_t t2 = t_walkstar si' t2'` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `env_rel_complete si' ienv tenv tenvE` ASSUME_TAC THENL
   [MATCH_MP_TAC env_rel_complete_t_compat THEN EXISTS_TAC `s0:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[t_compat_def]];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h2:pat#exp` (X_CHOOSE_THEN `t2s:(pat#exp)list` SUBST_ALL_TAC))
    (ISPEC `t:(pat#exp)list` list_CASES) THENL
   [MAP_EVERY EXISTS_TAC [`infer_st_subst_fupd (K s4) st3`; `si':(num,infer_t)fmap`;
                          `cs4:(infer_t#infer_t)list`] THEN
    REWRITE_TAC[infer_st_rewrs] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INFER1AUX_infer_pes_cons_run THEN
    MAP_EVERY EXISTS_TAC [`tp:infer_t`; `nb:(mlstring#infer_t)list`; `st1:infer_st`;
      `s2:(num,infer_t)fmap`; `tt:infer_t`; `st3:infer_st`; `s4:(num,infer_t)fmap`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[infer_e_def; st_ex_return_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`infer_st_subst_fupd (K s4) st3`;
      `cs4:(infer_t#infer_t)list`; `si':(num,infer_t)fmap`] o
    check (fun th -> is_forall(concl th) &&
      (try is_neg(hd(conjuncts(fst(dest_imp(snd(strip_forall(concl th)))))))
       with Failure _ -> false))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[infer_st_rewrs; NOT_CONS_NIL] THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
           ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st5:infer_st` (X_CHOOSE_THEN `s5:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs5:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`st5:infer_st`; `s5:(num,infer_t)fmap`;
                        `cs5:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFER1AUX_infer_pes_cons_run THEN
    MAP_EVERY EXISTS_TAC [`tp:infer_t`; `nb:(mlstring#infer_t)list`; `st1:infer_st`;
      `s2:(num,infer_t)fmap`; `tt:infer_t`; `st3:infer_st`; `s4:(num,infer_t)fmap`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `si':(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[]]);;

(* ---------- substitutions of type schemes ---------- *)
let INFER1AUX_deBruijn_subst_append = prove
 (`!n (targs:t list) ls.
     (!t. check_freevars (LENGTH targs) [] t
          ==> deBruijn_subst n (APPEND targs ls) t = deBruijn_subst n targs t) /\
     (!ts. ALL (check_freevars (LENGTH targs) []) ts
           ==> MAP (deBruijn_subst n (APPEND targs ls)) ts = MAP (deBruijn_subst n targs) ts)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[deBruijn_subst_def; check_freevars_def; ALL; MAP; LENGTH_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `a < n` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a < (LENGTH (targs:t list) + LENGTH (ls:t list)) + n /\
                a < LENGTH targs + n /\ a - n < LENGTH targs`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[EL_APPEND]]);;

let deBrujin_subst_excess = prove
 (`!n targs t t'.
     check_freevars (LENGTH targs) [] t /\ deBruijn_subst n targs t = t'
     ==> !ls. deBruijn_subst n (APPEND targs ls) t = t'`,
  MESON_TAC[INFER1AUX_deBruijn_subst_append]);;

let convert_infer_deBruijn_subst = prove
 (`!subst t.
     check_t (LENGTH subst) {} t
     ==> convert_t (infer_deBruijn_subst subst t) =
         deBruijn_subst 0 (MAP convert_t subst) (convert_t t)`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_subst_alt; check_t_def; convert_t_def; deBruijn_subst_def;
              NOT_IN_EMPTY; LT; LENGTH_MAP; ADD_CLAUSES; SUB_0] THEN
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[EL_MAP];
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th -> is_forall(concl th) &&
      is_imp(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ASM_SIMP_TAC[]]);;

let t_walkstar_infer_db_subst = prove
 (`!s s' uvars subst tvs.
     s SUBMAP s' /\ t_wfs s' /\ FDOM s = count uvars /\
     (!n. n < uvars ==> check_t tvs {} (t_walkstar s (Infer_Tuvar n))) /\
     (!n. n < LENGTH subst
          ==> t_walkstar s' (Infer_Tuvar (n + uvars)) = t_walkstar s (EL n subst))
     ==> (!t. check_t (LENGTH subst) (count uvars) t
              ==> t_walkstar s (infer_deBruijn_subst subst t) =
                  t_walkstar s'
                    (infer_deBruijn_subst
                       (MAP (\n. Infer_Tuvar (n + uvars)) (COUNT_LIST (LENGTH subst))) t)) /\
         (!ts. ALL (check_t (LENGTH subst) (count uvars)) ts
               ==> MAP (t_walkstar s o infer_deBruijn_subst subst) ts =
                   MAP (t_walkstar s' o
                        infer_deBruijn_subst
                          (MAP (\n. Infer_Tuvar (n + uvars)) (COUNT_LIST (LENGTH subst))))
                       ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_wfs_SUBMAP]; ALL_TAC] THEN
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[infer_deBruijn_subst_alt; check_t_def; ALL; MAP; o_THM; IN_COUNT;
              LENGTH_MAP; LENGTH_COUNT_LIST] THEN
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST];
    ASM_SIMP_TAC[t_walkstar_eqn1; MAP_MAP_o];
    MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `s':(num,infer_t)fmap`; `Infer_Tuvar a`]
      t_walkstar_SUBMAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `tvs:num` THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let ienv_val_ok_more = prove
 (`(!cuvs cuvs' env. ienv_val_ok cuvs env /\ cuvs SUBSET cuvs' ==> ienv_val_ok cuvs' env) /\
   (!uvs uvs' env.
      ienv_val_ok (count uvs) env /\ uvs <= uvs' ==> ienv_val_ok (count uvs') env)`,
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[TYSYS2AUX_ienv_val_ok_mono]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ienv_val_ok_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MP_TAC th) ASSUME_TAC) THEN
  MATCH_MP_TAC nsAll_mono THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[check_t_more5]);;

(* ---------- infer_e_complete ---------- *)
(* a literal case of infer_e_complete *)
let INFER1AUX_IEC_LIT_TAC tm : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (fun (asl,w as gl) ->
     let sc = find (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th)) (map snd asl) in
     let s = rand(concl sc) in
     (SUBGOAL_THEN (mk_comb(`t_wfs:(num,infer_t)fmap->bool`, s)) ASSUME_TAC THENL
       [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [tm; `st:infer_st`; s; `constraints:(infer_t#infer_t)list`]) gl) THEN
  ASM_SIMP_TAC[t_compat_refl; t_walkstar_eqn1; MAP; convert_t_def; infer_e_def;
               st_ex_return_def] THEN
  REWRITE_TAC INFER1AUX_ec_tydefs;;

(* the invariants after a successful completed inference step *)
let INFER1AUX_iec_step = prove
 (`!loc ienv e st t1 st1 s s1 cs1 tenv tenvE.
     infer_e loc ienv e st = (M_success t1,st1) /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\ t_wfs (infer_st_subst st) /\
     FDOM s = count (infer_st_next_uvar st) /\ env_rel_complete s ienv tenv tenvE /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st1) (infer_st_subst st1) cs1 s1 /\
     FDOM s1 = count (infer_st_next_uvar st1) /\ t_compat s s1
     ==> infer_st_next_uvar st <= infer_st_next_uvar st1 /\ t_wfs (infer_st_subst st1) /\
         t_wfs s1 /\ ienv_ok (count (infer_st_next_uvar st1)) ienv /\
         env_rel_complete s1 ienv tenv tenvE /\
         check_t 0 (count (infer_st_next_uvar st1)) t1 /\
         check_t (num_tvs tenvE) {} (t_walkstar s1 t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar st <= infer_st_next_uvar st1` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_next_uvar_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (count (infer_st_next_uvar st1)) t1` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `st:infer_st`] THEN
    ASM_MESON_TAC[ienv_ok_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ienv_ok_more THEN EXISTS_TAC `infer_st_next_uvar st` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC env_rel_complete_t_compat THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[]]);;

let INFER1AUX_iec_steps = prove
 (`!loc ienv es st ts1 st1 s s1 cs1 tenv tenvE.
     infer_es loc ienv es st = (M_success ts1,st1) /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\ t_wfs (infer_st_subst st) /\
     FDOM s = count (infer_st_next_uvar st) /\ env_rel_complete s ienv tenv tenvE /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st1) (infer_st_subst st1) cs1 s1 /\
     FDOM s1 = count (infer_st_next_uvar st1) /\ t_compat s s1
     ==> infer_st_next_uvar st <= infer_st_next_uvar st1 /\ t_wfs (infer_st_subst st1) /\
         t_wfs s1 /\ ienv_ok (count (infer_st_next_uvar st1)) ienv /\
         env_rel_complete s1 ienv tenv tenvE /\
         ALL (check_t 0 (count (infer_st_next_uvar st1))) ts1 /\
         ALL (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s1) ts1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar st <= infer_st_next_uvar st1` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_next_uvar_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (count (infer_st_next_uvar st1))) ts1` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 infer_e_check_t)) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `es:exp list`; `st:infer_st`] THEN
    ASM_MESON_TAC[ienv_ok_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ienv_ok_more THEN EXISTS_TAC `infer_st_next_uvar st` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC env_rel_complete_t_compat THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC INFER1AUX_sc_ground_list THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st1`; `infer_st_subst st1`;
                          `cs1:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[]]);;

(* the invariants after an inference step, as assumptions *)
let INFER1AUX_IEC_STEP_TAC (lem:thm) (specs:term list) : tactic =
  MP_TAC(SPECL specs lem) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

let INFER1AUX_IEC_START_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC;;

let INFER1AUX_IEC_LANNOT_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN REWRITE_TAC[infer_e_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`loc_err_info_loc_fupd (K (SOME l)) loc`;
      `s:(num,infer_t)fmap`; `ienv:inf_env`; `st:infer_st`;
      `constraints:(infer_t#infer_t)list`] o check (is_forall o concl)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[]];;

let INFER1AUX_IEC_NIL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_completion_wfs]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`[]:infer_t list`; `st:infer_st`; `s:(num,infer_t)fmap`;
                        `constraints:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[t_compat_refl; MAP; infer_e_def; st_ex_return_def];;

(* env_rel_complete for the environment extended with a variable of type ty *)
let INFER1AUX_erc_bind = prove
 (`!s s' ienv tenv tenvE n t1 ty.
     env_rel_complete s ienv tenv tenvE /\ t_compat s s' /\ FDOM s SUBSET FDOM s' /\
     t_wfs s' /\ check_freevars (num_tvs tenvE) [] t1 /\ t_walkstar s' ty = unconvert_t t1
     ==> env_rel_complete s'
           (inf_env_inf_v_fupd (K (nsBind n (0,ty) (inf_env_inf_v ienv))) ienv)
           tenv (Bind_name n 0 t1 tenvE)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[env_rel_complete_def; inf_env_INFO.ri_accfupds; K_THM; num_tvs_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `tvs:num`; `t:t`] THEN
  ASM_CASES_TAC `(x:(mlstring,mlstring)id) = Short n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[tveLookup_def; deBruijn_inc0; nsLookup_nsBind] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
    CONJ_TAC THENL [EXISTS_TAC `num_tvs tenvE` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`0`; `ty:infer_t`] THEN REWRITE_TAC[] THEN
    REWRITE_TAC[tscheme_approx_def; LENGTH_EQ_NIL] THEN
    EXISTS_TAC `[]:infer_t list` THEN REWRITE_TAC[ALL; MAP] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[infer_deBruijn_subst_id] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC t_walkstar_no_vars THEN
    EXISTS_TAC `num_tvs tenvE` THEN ASM_SIMP_TAC[check_freevars_to_check_t];
    ASM_SIMP_TAC[INFER1AUX_lookup_var_Bind_name_other; nsLookup_nsBind] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih
      (ASSUME `lookup_var x tenvE tenv = SOME (tvs,t)`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`)
      (X_CHOOSE_THEN `tvs':num` (X_CHOOSE_THEN `t':infer_t` STRIP_ASSUME_TAC))) THEN
    (* since HOL Light 2828953 the ASM_SIMP_TAC above may prove the first conjunct itself *)
    TRY (CONJ_TAC THENL [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    MAP_EVERY EXISTS_TAC [`tvs':num`; `t':infer_t`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC tscheme_approx_weakening2 THEN
    EXISTS_TAC `s:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[]]);;

(* the invariants for the body of a function with a fresh argument type *)
let INFER1AUX_iec_fresh = prove
 (`!st s constraints ienv tenv tenvE n t1.
     ienv_ok (count (infer_st_next_uvar st)) ienv /\ t_wfs (infer_st_subst st) /\
     FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
       constraints s /\
     FDOM s = count (infer_st_next_uvar st) /\ env_rel_complete s ienv tenv tenvE /\
     check_freevars (num_tvs tenvE) [] t1
     ==> ienv_ok (count (infer_st_next_uvar st + 1))
           (inf_env_inf_v_fupd
              (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv)))
              ienv) /\
         FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st + 1) /\
         sub_completion (num_tvs tenvE) (infer_st_next_uvar st + 1) (infer_st_subst st)
           (APPEND constraints [(Infer_Tuvar (infer_st_next_uvar st),unconvert_t t1)])
           (s |++ [(infer_st_next_uvar st,unconvert_t t1)]) /\
         FDOM (s |++ [(infer_st_next_uvar st,unconvert_t t1)]) =
           count (infer_st_next_uvar st + 1) /\
         env_rel_complete (s |++ [(infer_st_next_uvar st,unconvert_t t1)])
           (inf_env_inf_v_fupd
              (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv)))
              ienv)
           tenv (Bind_name n 0 t1 tenvE) /\
         t_compat s (s |++ [(infer_st_next_uvar st,unconvert_t t1)]) /\
         t_walkstar (s |++ [(infer_st_next_uvar st,unconvert_t t1)])
           (Infer_Tuvar (infer_st_next_uvar st)) = unconvert_t t1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MP_TAC(SPECL [`st:infer_st`; `s:(num,infer_t)fmap`; `constraints:(infer_t#infer_t)list`;
                `num_tvs tenvE`; `t1:t`] extend_one_props) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o
      check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_nsBind THEN
    REWRITE_TAC[check_t_def; IN_COUNT] THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN
    EXISTS_TAC `infer_st_next_uvar st` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count (infer_st_next_uvar st)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ARITH_TAC;
    MATCH_MP_TAC INFER1AUX_erc_bind THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_SIMP_TAC[SUBMAP_t_compat; SUBSET; IN_COUNT] THEN ARITH_TAC;
    MATCH_MP_TAC SUBMAP_t_compat THEN ASM_REWRITE_TAC[]]);;

(* apply the induction hypothesis about the expression key *)
let INFER1AUX_IEC_IH_TAC (key:term) (specs:term list) (rws:thm list) (names:term list) : tactic =
  FIRST_X_ASSUM(MP_TAC o SPECL specs o check (fun th ->
    let c = concl th in is_forall c && free_in key c &&
      (try is_exists(snd(dest_imp(snd(strip_forall c)))) with Failure _ -> false))) THEN
  REWRITE_TAC rws THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let rec chs ns th = match ns with
        [] -> STRIP_ASSUME_TAC th
      | n::rest -> X_CHOOSE_THEN n (chs rest) th in
    chs names th);;

(* adding constraints that the completion already satisfies *)
let INFER1AUX_iec_constrain = prove
 (`!n st cs s CS ienv tenv tenvE.
     sub_completion n (infer_st_next_uvar st) (infer_st_subst st) cs s /\
     FDOM s = count (infer_st_next_uvar st) /\ t_wfs (infer_st_subst st) /\
     env_rel_complete s ienv tenv tenvE /\
     ALL (\(x,y). t_walkstar s x = t_walkstar s y) CS
     ==> ?s1 si cs'.
           pure_add_constraints (infer_st_subst st) CS s1 /\
           sub_completion n (infer_st_next_uvar st) s1 cs' si /\
           FDOM s1 SUBSET count (infer_st_next_uvar st) /\
           FDOM si = count (infer_st_next_uvar st) /\ t_compat s si /\
           (!x. t_walkstar si x = t_walkstar s x) /\ t_wfs s1 /\ t_wfs si /\
           env_rel_complete si ienv tenv tenvE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `infer_st_next_uvar st`; `infer_st_subst st`;
                `cs:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                `CS:(infer_t#infer_t)list`] INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `si:(num,infer_t)fmap`;
                        `cs':(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap) /\ t_wfs (si:(num,infer_t)fmap)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs; t_compat_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC env_rel_complete_t_compat THEN
  EXISTS_TAC `s:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

(* a type that convert_t maps to a ground type of the typing *)
let INFER1AUX_unconvert_walk = prove
 (`!n s t tt.
     tt = convert_t (t_walkstar s t) /\ check_t n {} (t_walkstar s t)
     ==> t_walkstar s t = unconvert_t tt`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC check_t_empty_unconvert_convert_id THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[]);;

let INFER1AUX_walk_unconvert = prove
 (`!s0 s1 n t tt.
     t_compat s0 s1 /\ tt = convert_t (t_walkstar s0 t) /\ check_t n {} (t_walkstar s0 t)
     ==> t_walkstar s1 t = unconvert_t tt`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `s0:(num,infer_t)fmap`; `t:infer_t`; `tt:t`]
    INFER1AUX_unconvert_walk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INFER1AUX_ground_transfer THEN
  MAP_EVERY EXISTS_TAC [`s0:(num,infer_t)fmap`; `n:num`] THEN ASM_REWRITE_TAC[]);;

(* expand the explicit constraint lists into unifications *)
let INFER1AUX_IEC_PAC_TAC : tactic =
  let is_explicit th =
    INFER1AUX_ec_is_app "pure_add_constraints" (concl th) &&
    (let l = rand(rator(concl th)) in
     try fst(dest_const(fst(strip_comb l))) = "CONS" with Failure _ -> false) in
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pure_add_constraints_def] o
                       check is_explicit));;

let INFER1AUX_IEC_RUN_TAC : tactic =
  INFER1AUX_IEC_PAC_TAC THEN
  REWRITE_TAC[infer_e_def; st_ex_bind_def; st_ex_return_def; fresh_uvar_def;
              add_constraint_def] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[])) THEN
  TRY(REWRITE_TAC[PAIR_EQ; injectivity "exc"; infer_st_component_equality;
                  infer_st_INFO.ri_accfupds; K_THM] THEN NO_TAC);;

let INFER1AUX_IEC_ACCEPT_TAC : tactic =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM(ACCEPT_TAC o SYM)];;

let INFER1AUX_IEC_APP_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `es:exp list` [`loc:loc_err_info`; `s:(num,infer_t)fmap`;
      `ienv:inf_env`; `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`ts1:infer_t list`; `st1:infer_st`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_steps
    [`loc:loc_err_info`; `ienv:inf_env`; `es:exp list`; `st:infer_st`; `ts1:infer_t list`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  MP_TAC(SPECL [`op:op`; `ts:t list`; `t:t`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`;
                `s1:(num,infer_t)fmap`; `ts1:infer_t list`; `loc:loc_err_info`;
                `num_tvs tenvE`] constrain_op_complete) THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:infer_t` (X_CHOOSE_THEN `st2:infer_st`
    (X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`t2:infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
                        `cs2:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[]];;

let INFER1AUX_IEC_ESCONS_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `e:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1:infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `st:infer_st`; `t1:infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  INFER1AUX_IEC_IH_TAC `es:exp list` [`loc:loc_err_info`; `s1:(num,infer_t)fmap`;
      `ienv:inf_env`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`] []
    [`ts2:infer_t list`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
     `cs2:(infer_t#infer_t)list`] THEN
  SUBGOAL_THEN `t_walkstar s1 t1 = t_walkstar s2 t1` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`CONS (t1:infer_t) ts2`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
                        `cs2:(infer_t#infer_t)list`] THEN
  REWRITE_TAC[MAP; o_THM] THEN INFER1AUX_IEC_RUN_TAC THEN
  MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN ASM_REWRITE_TAC[];;

(* the body of a function, inferred with a fresh argument type *)
let INFER1AUX_iec_fun_body = prove
 (`!loc ienv tenv tenvE n e t1 t2 st s constraints.
     (!loc s ienv st constraints.
        ienv_ok (count (infer_st_next_uvar st)) ienv /\
        t_wfs (infer_st_subst st) /\
        FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
        sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
          constraints s /\
        FDOM s = count (infer_st_next_uvar st) /\
        env_rel_complete s ienv tenv (Bind_name n 0 t1 tenvE)
        ==> ?t' st' s' constraints'.
              infer_e loc ienv e st = (M_success t',st') /\
              sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
                constraints' s' /\
              FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
              FDOM s' = count (infer_st_next_uvar st') /\
              t_compat s s' /\
              t2 = convert_t (t_walkstar s' t')) /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\ t_wfs (infer_st_subst st) /\
     FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
       constraints s /\
     FDOM s = count (infer_st_next_uvar st) /\ env_rel_complete s ienv tenv tenvE /\
     check_freevars (num_tvs tenvE) [] t1
     ==> ?t2' st2 s2 cs2.
           infer_e loc
             (inf_env_inf_v_fupd
                (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv)))
                ienv) e
             (infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st) =
             (M_success t2',st2) /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st2) (infer_st_subst st2)
             cs2 s2 /\
           FDOM (infer_st_subst st2) SUBSET count (infer_st_next_uvar st2) /\
           FDOM s2 = count (infer_st_next_uvar st2) /\
           t_compat s s2 /\ infer_st_next_uvar st < infer_st_next_uvar st2 /\
           t_wfs (infer_st_subst st2) /\ t_wfs s2 /\
           ienv_ok (count (infer_st_next_uvar st2)) ienv /\
           env_rel_complete s2 ienv tenv tenvE /\
           t1 = convert_t (t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st))) /\
           t2 = convert_t (t_walkstar s2 t2') /\
           check_t (num_tvs tenvE) {} (t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st))) /\
           check_t (num_tvs tenvE) {} (t_walkstar s2 t2')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_fresh
    [`st:infer_st`; `s:(num,infer_t)fmap`; `constraints:(infer_t#infer_t)list`;
     `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`; `n:mlstring`; `t1:t`] THEN
  INFER1AUX_IEC_IH_TAC `e:exp`
    [`loc:loc_err_info`; `s |++ [(infer_st_next_uvar st,unconvert_t t1)]`;
     `inf_env_inf_v_fupd
        (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv))) ienv`;
     `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st`;
     `APPEND constraints [(Infer_Tuvar (infer_st_next_uvar st),unconvert_t t1)]`]
    [infer_st_rewrs]
    [`t2':infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  MAP_EVERY EXISTS_TAC [`t2':infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
                        `cs2:(infer_t#infer_t)list`] THEN
  SUBGOAL_THEN `unconvert_t t1 = t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s |++ [(infer_st_next_uvar st,unconvert_t t1)]`; `num_tvs tenvE`] THEN
    ASM_SIMP_TAC[check_freevars_to_check_t];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `t_compat s (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_trans THEN
    EXISTS_TAC `s |++ [(infer_st_next_uvar st,unconvert_t t1)]` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`loc:loc_err_info`;
    `inf_env_inf_v_fupd
        (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv))) ienv`;
    `e:exp`; `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st`;
    `st2:infer_st`; `t2':infer_t`] (CONJUNCT1 infer_e_next_uvar_mono)) THEN
  MP_TAC(SPECL [`loc:loc_err_info`;
    `inf_env_inf_v_fupd
        (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv))) ienv`;
    `e:exp`; `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st`;
    `st2:infer_st`; `t2':infer_t`] (CONJUNCT1 infer_e_wfs)) THEN
  MP_TAC(SPECL [`loc:loc_err_info`;
    `inf_env_inf_v_fupd
        (K (nsBind n (0,Infer_Tuvar (infer_st_next_uvar st)) (inf_env_inf_v ienv))) ienv`;
    `e:exp`; `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st`;
    `st2:infer_st`; `t2':infer_t`] (CONJUNCT1 infer_e_check_t)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] o
    check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th) &&
                     free_in `nsBind:mlstring->num#infer_t->(mlstring,mlstring,num#infer_t)namespace->(mlstring,mlstring,num#infer_t)namespace` (concl th))) THEN
  ASM_REWRITE_TAC[infer_st_rewrs; inf_env_INFO.ri_accfupds; K_THM] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar st < infer_st_next_uvar st2` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `check_t (num_tvs tenvE) {} (t_walkstar s2 t2')` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_sc_ground THEN
    MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st2`; `infer_st_subst st2`;
                          `cs2:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `t1:t`] check_freevars_empty_convert_unconvert_id) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `unconvert_t t1 = t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st))`)) THEN
  ASM_SIMP_TAC[check_freevars_to_check_t] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ienv_ok_more THEN EXISTS_TAC `infer_st_next_uvar st` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC env_rel_complete_t_compat THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC]);;

let INFER1AUX_IEC_FUN_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_tvs_def]) THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
                `n:mlstring`; `e:exp`; `t1:t`; `t2:t`; `st:infer_st`; `s:(num,infer_t)fmap`;
                `constraints:(infer_t#infer_t)list`] INFER1AUX_iec_fun_body) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2':infer_t` (X_CHOOSE_THEN `st2:infer_st`
    (X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st); t2'] Tfn_num`;
                        `st2:infer_st`; `s2:(num,infer_t)fmap`;
                        `cs2:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP; convert_t_def; typeSystem_Tfn_def] THEN
  INFER1AUX_IEC_RUN_TAC;;

let INFER1AUX_IEC_FUNSCONS_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[typeSystem_Tfn_def; check_freevars_def; ALL] o
    check (fun th -> INFER1AUX_ec_is_app "check_freevars" (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_tvs_def]) THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
                `n:mlstring`; `e:exp`; `t1:t`; `t2:t`; `st:infer_st`; `s:(num,infer_t)fmap`;
                `constraints:(infer_t#infer_t)list`] INFER1AUX_iec_fun_body) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2':infer_t` (X_CHOOSE_THEN `st2:infer_st`
    (X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  INFER1AUX_IEC_IH_TAC `funs:(mlstring#mlstring#exp)list`
    [`loc:loc_err_info`; `s2:(num,infer_t)fmap`; `ienv:inf_env`; `st2:infer_st`;
     `cs2:(infer_t#infer_t)list`] []
    [`env3:infer_t list`; `st3:infer_st`; `s3:(num,infer_t)fmap`;
     `cs3:(infer_t#infer_t)list`] THEN
  SUBGOAL_THEN `t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st)) =
                t_walkstar s3 (Infer_Tuvar (infer_st_next_uvar st))` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `num_tvs tenvE`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s2 t2' = t_walkstar s3 t2'` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `num_tvs tenvE`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
    [`CONS (Infer_Tapp [Infer_Tuvar (infer_st_next_uvar st); t2'] Tfn_num) env3`;
     `st3:infer_st`; `s3:(num,infer_t)fmap`; `cs3:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; MAP; o_THM; convert_t_def; typeSystem_Tfn_def] THEN
  CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s2:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[]];;

let INFER1AUX_IEC_LOG_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `e1:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1:infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e1:exp`; `st:infer_st`; `t1:infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  INFER1AUX_IEC_IH_TAC `e2:exp` [`loc:loc_err_info`; `s1:(num,infer_t)fmap`;
      `ienv:inf_env`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`] []
    [`t2:infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e2:exp`; `st1:infer_st`; `t2:infer_t`;
     `st2:infer_st`; `s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`;
     `cs2:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `t_compat s2 (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_refl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s2 t1 = unconvert_t Tbool` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
    MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s2 t2 = unconvert_t Tbool` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
    MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `st2:infer_st`; `cs2:(infer_t#infer_t)list`;
    `s2:(num,infer_t)fmap`;
    `[t1:infer_t,Infer_Tapp [] Tbool_num; t2,Infer_Tapp [] Tbool_num]`;
    `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`] INFER1AUX_iec_constrain) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[t_walkstar_eqn1; MAP; typeSystem_Tbool_def; unconvert_t_def];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs3:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tapp [] Tbool_num`; `infer_st_subst_fupd (K s3) st2`;
                        `si:(num,infer_t)fmap`; `cs3:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[infer_st_rewrs; t_walkstar_eqn1; MAP; convert_t_def; typeSystem_Tbool_def] THEN
  CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans]];;

let INFER1AUX_convert_check = prove
 (`!n s x tt. tt = convert_t (t_walkstar s x) /\ check_t n {} (t_walkstar s x)
              ==> check_freevars n [] tt`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC check_t_to_check_freevars THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_final_type = prove
 (`!n si s x tt.
     (!y. t_walkstar si y = t_walkstar s y) /\ t_walkstar s x = unconvert_t tt /\
     check_freevars n [] tt
     ==> tt = convert_t (t_walkstar si x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_IEC_IF_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `e1:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1:infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e1:exp`; `st:infer_st`; `t1:infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `t_compat s1 (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_refl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s1 t1 = unconvert_t Tbool` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
    MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`;
    `s1:(num,infer_t)fmap`; `[t1:infer_t,Infer_Tapp [] Tbool_num]`;
    `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`] INFER1AUX_iec_constrain) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[t_walkstar_eqn1; MAP; typeSystem_Tbool_def; unconvert_t_def];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sA:(num,infer_t)fmap` (X_CHOOSE_THEN `siA:(num,infer_t)fmap`
    (X_CHOOSE_THEN `csA:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `ienv_ok (count (infer_st_next_uvar (infer_st_subst_fupd (K sA) st1))) ienv /\
                t_wfs (infer_st_subst (infer_st_subst_fupd (K sA) st1)) /\
                FDOM (infer_st_subst (infer_st_subst_fupd (K sA) st1)) SUBSET
                  count (infer_st_next_uvar (infer_st_subst_fupd (K sA) st1)) /\
                sub_completion (num_tvs tenvE)
                  (infer_st_next_uvar (infer_st_subst_fupd (K sA) st1))
                  (infer_st_subst (infer_st_subst_fupd (K sA) st1)) csA siA /\
                FDOM siA = count (infer_st_next_uvar (infer_st_subst_fupd (K sA) st1))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[infer_st_rewrs] THEN INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  INFER1AUX_IEC_IH_TAC `e2:exp` [`loc:loc_err_info`; `siA:(num,infer_t)fmap`;
      `ienv:inf_env`; `infer_st_subst_fupd (K sA) st1`; `csA:(infer_t#infer_t)list`] []
    [`t2:infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e2:exp`; `infer_st_subst_fupd (K sA) st1`;
     `t2:infer_t`; `st2:infer_st`; `siA:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`;
     `cs2:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  INFER1AUX_IEC_IH_TAC `e3:exp` [`loc:loc_err_info`; `s2:(num,infer_t)fmap`;
      `ienv:inf_env`; `st2:infer_st`; `cs2:(infer_t#infer_t)list`] []
    [`t3:infer_t`; `st3:infer_st`; `s3:(num,infer_t)fmap`; `cs3:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e3:exp`; `st2:infer_st`; `t3:infer_t`;
     `st3:infer_st`; `s2:(num,infer_t)fmap`; `s3:(num,infer_t)fmap`;
     `cs3:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `t_compat s3 (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_refl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s3 t2 = unconvert_t t` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
    MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s3 t3 = unconvert_t t` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
    MAP_EVERY EXISTS_TAC [`s3:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `st3:infer_st`; `cs3:(infer_t#infer_t)list`;
    `s3:(num,infer_t)fmap`; `[t2:infer_t,t3:infer_t]`;
    `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`] INFER1AUX_iec_constrain) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs4:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `check_freevars (num_tvs tenvE) [] t` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_convert_check THEN
    MAP_EVERY EXISTS_TAC [`s3:(num,infer_t)fmap`; `t3:infer_t`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t = convert_t (t_walkstar si t2)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_final_type THEN
    MAP_EVERY EXISTS_TAC [`num_tvs tenvE`; `s3:(num,infer_t)fmap`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t2:infer_t`; `infer_st_subst_fupd (K s4) st3`;
                        `si:(num,infer_t)fmap`; `cs4:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans]];;

let INFER1AUX_inf_env_v_id = prove
 (`!ienv. inf_env_inf_v_fupd (K (inf_env_inf_v ienv)) ienv = ienv`,
  REWRITE_TAC[inf_env_INFO.ri_component_equality; inf_env_INFO.ri_accfupds; K_THM]);;

let INFER1AUX_IEC_LET_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `e1:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1':infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e1:exp`; `st:infer_st`; `t1':infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  MP_TAC(ISPEC `n:mlstring option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x:mlstring` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[opt_bind_name_def; num_tvs_def]) THEN
  REWRITE_TAC[infer_e_def; nsOptBind_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INFER1AUX_inf_env_v_id] THENL
   [INFER1AUX_IEC_IH_TAC `e2:exp` [`loc:loc_err_info`; `s1:(num,infer_t)fmap`;
        `ienv:inf_env`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`] []
      [`t2':infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
       `cs2:(infer_t#infer_t)list`];
    SUBGOAL_THEN `check_freevars (num_tvs tenvE) [] t1` ASSUME_TAC THENL
     [MATCH_MP_TAC INFER1AUX_convert_check THEN
      MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `t1':infer_t`] THEN
      INFER1AUX_IEC_ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t_compat s1 (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
     [MATCH_MP_TAC t_compat_refl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `ienv_ok (count (infer_st_next_uvar st1))
         (inf_env_inf_v_fupd (K (nsBind x (0,t1') (inf_env_inf_v ienv))) ienv) /\
       env_rel_complete s1
         (inf_env_inf_v_fupd (K (nsBind x (0,t1') (inf_env_inf_v ienv))) ienv)
         tenv (Bind_name x 0 t1 tenvE)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o check (fun th ->
          concl th = `ienv_ok (count (infer_st_next_uvar st1)) ienv`)) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_nsBind THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC INFER1AUX_erc_bind THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
        REPEAT CONJ_TAC THEN
        FIRST [INFER1AUX_IEC_ACCEPT_TAC; REWRITE_TAC[SUBSET_REFL] THEN NO_TAC;
               MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
               MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
               INFER1AUX_IEC_ACCEPT_TAC]];
      ALL_TAC] THEN
    INFER1AUX_IEC_IH_TAC `e2:exp` [`loc:loc_err_info`; `s1:(num,infer_t)fmap`;
        `inf_env_inf_v_fupd (K (nsBind x (0,t1') (inf_env_inf_v ienv))) ienv`;
        `st1:infer_st`; `cs1:(infer_t#infer_t)list`] []
      [`t2':infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
       `cs2:(infer_t#infer_t)list`]] THEN
  (MAP_EVERY EXISTS_TAC [`t2':infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
                         `cs2:(infer_t#infer_t)list`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [INFER1AUX_IEC_RUN_TAC;
     MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
     ASM_REWRITE_TAC[]]);;

let INFER1AUX_IEC_CONNONE_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `es:exp list` [`loc:loc_err_info`; `s:(num,infer_t)fmap`;
      `ienv:inf_env`; `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`ts1:infer_t list`; `st1:infer_st`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`] THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tapp ts1 Ttup_num`; `st1:infer_st`; `s1:(num,infer_t)fmap`;
                        `cs1:(infer_t#infer_t)list`] THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def; typeSystem_Ttup_def; MAP_MAP_o] THEN
  INFER1AUX_IEC_RUN_TAC;;

let INFER1AUX_IEC_RAISE_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `e:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t2:infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `st:infer_st`; `t2:infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `t_compat s1 (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_refl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s1 t2 = unconvert_t Texn` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_unconvert THEN
    MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o check (fun th ->
    INFER1AUX_ec_is_app "sub_completion" (concl th) &&
    rand(concl th) = `s1:(num,infer_t)fmap`)) THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `infer_st_next_uvar st1`; `s1:(num,infer_t)fmap`; `t:t`]
    INFER1AUX_ext_facts) THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `infer_st_next_uvar st1`; `infer_st_subst st1`;
                `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`;
                `[t2:infer_t, Infer_Tapp [] Texn_num]`; `t:t`] INFER1AUX_cs_core1) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [INFER1AUX_IEC_ACCEPT_TAC; INFER1AUX_IEC_ACCEPT_TAC; INFER1AUX_IEC_ACCEPT_TAC;
      INFER1AUX_IEC_ACCEPT_TAC;
      REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[t_walkstar_eqn1; MAP; typeSystem_Texn_def; unconvert_t_def]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tuvar (infer_st_next_uvar st1)`;
    `infer_st_next_uvar_fupd (K (infer_st_next_uvar st1 + 1)) (infer_st_subst_fupd (K s2) st1)`;
    `si:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  REWRITE_TAC[infer_st_rewrs] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `t:t`] check_freevars_empty_convert_unconvert_id) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans]];;

let INFER1AUX_IEC_TANNOT_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  INFER1AUX_IEC_IH_TAC `e:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1:infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `st:infer_st`; `t1:infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv` ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_complete_def]; ALL_TAC] THEN
  SUBGOAL_THEN `tenv_abbrev_ok (type_env_t tenv)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ienv_ok_def]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!err. type_name_check_subst loc err (type_env_t tenv) [] (t:ast_t) (st1:infer_st) =
           (M_success (type_name_subst (type_env_t tenv) t),st1)`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(CONJUNCT1 type_name_check_subst_comp_thm) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tn0 = type_name_subst (type_env_t tenv) t` THEN
  SUBGOAL_THEN `check_freevars 0 [] tn0` ASSUME_TAC THENL
   [EXPAND_TAC "tn0" THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `infer_type_subst [] tn0 = unconvert_t tn0` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(SPEC `0` infer_type_subst_nil)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`;
    `s1:(num,infer_t)fmap`; `[t1:infer_t, infer_type_subst [] tn0]`;
    `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`] INFER1AUX_iec_constrain) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY INFER1AUX_IEC_ACCEPT_TAC THEN
    REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `infer_type_subst [] tn0 = unconvert_t tn0`] THEN
    SUBGOAL_THEN `t_walkstar s1 t1 = unconvert_t tn0` SUBST1_TAC THENL
     [MATCH_MP_TAC INFER1AUX_unconvert_walk THEN EXISTS_TAC `num_tvs tenvE` THEN
      INFER1AUX_IEC_ACCEPT_TAC;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN
    ASM_SIMP_TAC[check_freevars_to_check_t];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `tn0 = convert_t (t_walkstar s1 t1)`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `infer_type_subst [] tn0 = unconvert_t tn0`)) THEN
  MAP_EVERY EXISTS_TAC [`t1:infer_t`; `infer_st_subst_fupd (K s2) st1`;
                        `si:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans]];;

(* the type of the branches of a match is closed: infer the first branch *)
let INFER1AUX_mat_freevars = prove
 (`!ienv tenv tenvE uvar pes t1 t2 t1' st1 cs1 s1.
     ~(pes = []) /\ ienv_ok (count uvar) ienv /\ uvar <= infer_st_next_uvar st1 /\
     t_wfs (infer_st_subst st1) /\ env_rel_complete s1 ienv tenv tenvE /\
     (!p e. MEM (p,e) pes
            ==> ?bindings.
                  ALL_DISTINCT (pat_bindings p) /\
                  type_p (num_tvs tenvE) tenv p t1 bindings /\
                  type_e tenv (bind_var_list 0 bindings tenvE) e t2 /\
                  !l s'' ienv' st'' constraints''.
                    ienv_ok (count (infer_st_next_uvar st'')) ienv' /\
                    t_wfs (infer_st_subst st'') /\
                    FDOM (infer_st_subst st'') SUBSET count (infer_st_next_uvar st'') /\
                    sub_completion (num_tvs tenvE)
                      (infer_st_next_uvar st'') (infer_st_subst st'') constraints'' s'' /\
                    FDOM s'' = count (infer_st_next_uvar st'') /\
                    env_rel_complete s'' ienv' tenv (bind_var_list 0 bindings tenvE)
                    ==> ?t'' st''' s''' constraints'''.
                          infer_e l ienv' e st'' = (M_success t'',st''') /\
                          sub_completion (num_tvs tenvE) (infer_st_next_uvar st''')
                            (infer_st_subst st''') constraints''' s''' /\
                          FDOM (infer_st_subst st''') SUBSET
                            count (infer_st_next_uvar st''') /\
                          FDOM s''' = count (infer_st_next_uvar st''') /\
                          t_compat s'' s''' /\
                          t2 = convert_t (t_walkstar s''' t'')) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st1) (infer_st_subst st1) cs1 s1 /\
     FDOM (infer_st_subst st1) SUBSET count (infer_st_next_uvar st1) /\
     FDOM s1 = count (infer_st_next_uvar st1) /\
     unconvert_t t1 = t_walkstar s1 t1'
     ==> check_freevars (num_tvs tenvE) [] t2`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `h:pat#exp` (X_CHOOSE_THEN `rest:(pat#exp)list` SUBST1_TAC))
    (ISPEC `pes:(pat#exp)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  SPEC_TAC(`h:pat#exp`,`h:pat#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p0:pat`; `e0:exp`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p0:pat`; `e0:exp`] o check (fun th ->
    is_forall(concl th) &&
    (try INFER1AUX_ec_is_app "MEM" (fst(dest_imp(snd(strip_forall(concl th)))))
     with Failure _ -> false))) THEN
  REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `bindings:(mlstring#t)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
                `uvar:num`; `p0:pat`; `bindings:(mlstring#t)list`; `t1:t`; `t1':infer_t`;
                `st1:infer_st`; `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`]
         INFER1AUX_pes_pat_step) THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:infer_t` (X_CHOOSE_THEN `nb:(mlstring#infer_t)list`
    (X_CHOOSE_THEN `stP:infer_st` (X_CHOOSE_THEN `s2:(num,infer_t)fmap`
    (X_CHOOSE_THEN `si:(num,infer_t)fmap` (X_CHOOSE_THEN `cs':(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(fun th26 ->
    if INFER1AUX_ec_is_app "ienv_ok" (concl th26) &&
       free_in `nb:(mlstring#infer_t)list` (concl th26)
    then let ie = rand(concl th26) in
      FIRST_X_ASSUM(MP_TAC o SPECL [`loc:loc_err_info`; `si:(num,infer_t)fmap`; ie;
          `infer_st_subst_fupd (K s2) stP`; `cs':(infer_t#infer_t)list`] o
        check (fun th -> is_forall(concl th) &&
          (try INFER1AUX_ec_is_app "ienv_ok"
                 (hd(conjuncts(fst(dest_imp(snd(strip_forall(concl th)))))))
           with Failure _ -> false)))
    else failwith "") THEN
  REWRITE_TAC[infer_st_rewrs] THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:infer_t` (X_CHOOSE_THEN `st3:infer_st`
    (X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `cs3:(infer_t#infer_t)list`
     STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] o
    check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th) &&
                     free_in `nb:(mlstring#infer_t)list` (concl th))) THEN
  INFER1AUX_IE_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT1 infer_e_check_t)) THEN
  ASM_REWRITE_TAC[infer_st_rewrs; inf_env_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t_wfs (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  MATCH_MP_TAC INFER1AUX_convert_check THEN
  MAP_EVERY EXISTS_TAC [`s3:(num,infer_t)fmap`; `tt:infer_t`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_sc_ground THEN
  MAP_EVERY EXISTS_TAC [`infer_st_next_uvar st3`; `infer_st_subst st3`;
                        `cs3:(infer_t#infer_t)list`] THEN ASM_REWRITE_TAC[]);;

let INFER1AUX_pes_complete' = REWRITE_RULE[num_tvs_bind_var_list] infer_pes_complete;;

let INFER1AUX_IEC_HANDLE_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_tvs_bind_var_list]) THEN
  INFER1AUX_IEC_IH_TAC `e:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1:infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `st:infer_st`; `t1:infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `unconvert_t t = t_walkstar s1 t1` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_unconvert_walk THEN
    EXISTS_TAC `num_tvs tenvE` THEN INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `unconvert_t Texn = t_walkstar s1 (Infer_Tapp [] Texn_num)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[t_walkstar_eqn1; MAP; typeSystem_Texn_def; unconvert_t_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
    `infer_st_next_uvar st`; `Texn`; `t:t`; `Infer_Tapp [] Texn_num`; `t1:infer_t`;
    `pes:(pat#exp)list`; `st1:infer_st`; `cs1:(infer_t#infer_t)list`;
    `s1:(num,infer_t)fmap`] INFER1AUX_pes_complete') THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st2:infer_st` (X_CHOOSE_THEN `s2:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `t_walkstar s1 t1 = t_walkstar s2 t1` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1:infer_t`; `st2:infer_st`; `s2:(num,infer_t)fmap`;
                        `cs2:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans]];;

let INFER1AUX_IEC_MAT_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_tvs_bind_var_list]) THEN
  INFER1AUX_IEC_IH_TAC `e:exp` [`loc:loc_err_info`; `s:(num,infer_t)fmap`; `ienv:inf_env`;
      `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`t1':infer_t`; `st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_step
    [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `st:infer_st`; `t1':infer_t`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `unconvert_t t1 = t_walkstar s1 t1'` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_unconvert_walk THEN
    EXISTS_TAC `num_tvs tenvE` THEN INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t (num_tvs tenvE) {} (unconvert_t t1)` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `unconvert_t t1 = t_walkstar s1 t1'`] THEN INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
    `infer_st_next_uvar st`; `pes:(pat#exp)list`; `t1:t`; `t2:t`; `t1':infer_t`;
    `st1:infer_st`; `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`]
    INFER1AUX_mat_freevars) THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; DISCH_TAC] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_fresh
    [`st1:infer_st`; `s1:(num,infer_t)fmap`; `cs1:(infer_t#infer_t)list`;
     `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`; `x:mlstring`; `t2:t`] THEN
  SUBGOAL_THEN
    `unconvert_t t1 = t_walkstar (s1 |++ [(infer_st_next_uvar st1,unconvert_t t2)]) t1'`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    INFER1AUX_IEC_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s1 |++ [(infer_st_next_uvar st1,unconvert_t t2)])` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `env_rel_complete (s1 |++ [(infer_st_next_uvar st1,unconvert_t t2)])
                  ienv tenv tenvE` ASSUME_TAC THENL
   [MATCH_MP_TAC env_rel_complete_t_compat THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `infer_st_next_uvar st <= infer_st_next_uvar st1 + 1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tenvE:tenv_val_exp`;
    `infer_st_next_uvar st`; `t1:t`; `t2:t`; `t1':infer_t`;
    `Infer_Tuvar (infer_st_next_uvar st1)`; `pes:(pat#exp)list`;
    `infer_st_next_uvar_fupd (K (infer_st_next_uvar st1 + 1)) st1`;
    `APPEND cs1 [(Infer_Tuvar (infer_st_next_uvar st1),unconvert_t t2)]`;
    `s1 |++ [(infer_st_next_uvar st1,unconvert_t t2)]`] INFER1AUX_pes_complete') THEN
  REWRITE_TAC[infer_st_rewrs] THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st2:infer_st` (X_CHOOSE_THEN `s2:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs2:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `unconvert_t t2 = t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st1))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s1 |++ [(infer_st_next_uvar st1,unconvert_t t2)]`;
                          `num_tvs tenvE`] THEN
    ASM_SIMP_TAC[check_freevars_to_check_t];
    ALL_TAC] THEN
  MP_TAC(SPECL [`num_tvs tenvE`; `t2:t`] check_freevars_empty_convert_unconvert_id) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Infer_Tuvar (infer_st_next_uvar st1)`; `st2:infer_st`;
                        `s2:(num,infer_t)fmap`; `cs2:(infer_t#infer_t)list`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `unconvert_t t2 = t_walkstar s2 (Infer_Tuvar (infer_st_next_uvar st1))`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [INFER1AUX_IEC_RUN_TAC;
    ASM_MESON_TAC[t_compat_trans]];;

(* the Var case of infer_e_complete *)
let INFER1AUX_iec_var = prove
 (`!tenv tenvE n t targs tvs loc s ienv st constraints.
     tvs = LENGTH targs /\ ALL (check_freevars (num_tvs tenvE) []) targs /\
     lookup_var n tenvE tenv = SOME (tvs,t) /\
     ienv_ok (count (infer_st_next_uvar st)) ienv /\ t_wfs (infer_st_subst st) /\
     FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
     sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
       constraints s /\
     FDOM s = count (infer_st_next_uvar st) /\ env_rel_complete s ienv tenv tenvE
     ==> ?t' st' s' constraints'.
           infer_e loc ienv (Var n) st = (M_success t',st') /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
             constraints' s' /\
           FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
           FDOM s' = count (infer_st_next_uvar st') /\
           t_compat s s' /\
           deBruijn_subst 0 targs t = convert_t (t_walkstar s' t')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `lookup_var n tenvE tenv = SOME (tvs,t)`) o
    CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[env_rel_complete_def] o
    check (fun th -> INFER1AUX_ec_is_app "env_rel_complete" (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`)
    (X_CHOOSE_THEN `tvs':num` (X_CHOOSE_THEN `t':infer_t` STRIP_ASSUME_TAC))) THEN
  (* the inferred type scheme is closed in the current uvars *)
  SUBGOAL_THEN `check_t tvs' (count (infer_st_next_uvar st)) t'` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[ienv_ok_def; ienv_val_ok_def; nsAll_def] o
      check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:(mlstring,mlstring)id`; `(tvs',t'):num#infer_t`] o
      CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the instantiation of the typing scheme *)
  SUBGOAL_THEN `ALL (check_t (num_tvs tenvE) {}) (MAP unconvert_t targs)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (check_freevars (num_tvs tenvE) []) targs` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN MESON_TAC[check_freevars_to_check_t];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t':infer_t`; `num_tvs tenvE`; `s:(num,infer_t)fmap`; `tvs:num`; `tvs':num`;
                `unconvert_t t`] tscheme_approx_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `MAP unconvert_t targs`) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `subst':infer_t list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `deBruijn_subst 0 targs t =
                convert_t (t_walkstar s (infer_deBruijn_subst subst' t'))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && INFER1AUX_ec_is_app "t_walkstar" (lhs(concl th)))) THEN
    MP_TAC(SPECL [`t:t`; `m:num`; `s:(num,infer_t)fmap`; `MAP unconvert_t targs`]
      db_subst_infer_subst_swap3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[MAP_MAP_o; MAP_EQ_ID; o_THM] THEN
    X_GEN_TAC `x:t` THEN DISCH_TAC THEN
    SUBGOAL_THEN `check_freevars (num_tvs tenvE) [] x` ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (check_freevars (num_tvs tenvE) []) targs` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t_walkstar s (unconvert_t x) = unconvert_t x` SUBST1_TAC THENL
     [MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `num_tvs tenvE` THEN
      ASM_SIMP_TAC[check_freevars_to_check_t];
      MATCH_MP_TAC check_freevars_empty_convert_unconvert_id THEN
      EXISTS_TAC `num_tvs tenvE` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && INFER1AUX_ec_is_app "t_walkstar" (lhs(concl th)))) THEN
  SUBGOAL_THEN `ALL (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s) subst')`
    ASSUME_TAC THENL
   [REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC(CONJUNCT2 check_t_walkstar) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`st:infer_st`; `constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                `MAP (convert_t o t_walkstar s) subst'`; `num_tvs tenvE`]
    extend_multi_props) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s) subst')` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; o_THM] THEN
    MESON_TAC[check_t_to_check_freevars];
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH_MAP] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s2 = s |++ ZIP (MAP (\n. infer_st_next_uvar st + n) (COUNT_LIST tvs'))
                             (MAP unconvert_t (MAP (convert_t o t_walkstar s) subst'))` THEN
  SUBGOAL_THEN `!k. k < tvs'
                    ==> t_walkstar s2 (Infer_Tuvar (k + infer_st_next_uvar st)) =
                        t_walkstar s (EL k (subst':infer_t list))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        (try INFER1AUX_ec_is_app "EL" (rhs(snd(dest_imp(snd(dest_forall(concl th))))))
         with Failure _ -> false)
      then MP_TAC(SPEC `k:num` th) else failwith "") THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; o_THM] THEN
    MATCH_MP_TAC check_t_empty_unconvert_convert_id THEN EXISTS_TAC `num_tvs tenvE` THEN
    UNDISCH_TAC `ALL (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s) subst')` THEN
    REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[EL_MAP];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`; `infer_st_next_uvar st`;
                `subst':infer_t list`; `num_tvs tenvE`] t_walkstar_infer_db_subst) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        (try INFER1AUX_ec_is_app "IN" (fst(dest_imp(snd(dest_forall(concl th))))) &&
             not (free_in `s2:(num,infer_t)fmap` (concl th))
         with Failure _ -> false)
      then MATCH_MP_TAC th else failwith "") THEN
    ASM_REWRITE_TAC[IN_COUNT];
    DISCH_THEN(MP_TAC o SPEC `t':infer_t` o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\n. Infer_Tuvar (n + infer_st_next_uvar st)) =
                (\k. Infer_Tuvar (infer_st_next_uvar st + k))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
    [`infer_deBruijn_subst (MAP (\k. Infer_Tuvar (infer_st_next_uvar st + k))
                                 (COUNT_LIST tvs')) t'`;
     `infer_st_next_uvar_fupd (K (infer_st_next_uvar st + tvs')) st`;
     `s2:(num,infer_t)fmap`;
     `APPEND constraints
        (ZIP (MAP Infer_Tuvar (MAP (\n. infer_st_next_uvar st + n) (COUNT_LIST tvs')))
             (MAP unconvert_t (MAP (convert_t o t_walkstar s) subst')))`] THEN
  REWRITE_TAC[infer_st_rewrs] THEN ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[infer_e_def; st_ex_bind_def; st_ex_return_def; lookup_st_ex_def;
                     INFER1AUX_n_fresh_uvar_eq] THEN
         REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[])) THEN
         NO_TAC;
         MATCH_MP_TAC SUBMAP_t_compat THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count (infer_st_next_uvar st)` THEN
         ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ARITH_TAC]);;

let INFER1AUX_IEC_VAR_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  MP_TAC(SPECL [`tenv:type_env`; `tenvE:tenv_val_exp`; `n:(mlstring,mlstring)id`; `t:t`;
                `targs:t list`; `tvs:num`; `loc:loc_err_info`; `s:(num,infer_t)fmap`;
                `ienv:inf_env`; `st:infer_st`; `constraints:(infer_t#infer_t)list`]
    INFER1AUX_iec_var) THEN
  ANTS_TAC THENL [INFER1AUX_IEC_ACCEPT_TAC; REWRITE_TAC[]];;

let INFER1AUX_IEC_CONSOME_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && INFER1AUX_ec_is_app "LENGTH" (lhs(concl th)))) THEN
  INFER1AUX_IEC_IH_TAC `es:exp list` [`loc:loc_err_info`; `s:(num,infer_t)fmap`;
      `ienv:inf_env`; `st:infer_st`; `constraints:(infer_t#infer_t)list`] []
    [`ts1:infer_t list`; `st1:infer_st`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`] THEN
  INFER1AUX_IEC_STEP_TAC INFER1AUX_iec_steps
    [`loc:loc_err_info`; `ienv:inf_env`; `es:exp list`; `st:infer_st`; `ts1:infer_t list`;
     `st1:infer_st`; `s:(num,infer_t)fmap`; `s1:(num,infer_t)fmap`;
     `cs1:(infer_t#infer_t)list`; `tenv:type_env`; `tenvE:tenv_val_exp`] THEN
  SUBGOAL_THEN `inf_env_inf_c ienv = type_env_c tenv` ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_complete_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_freevars 0 tvs) ts` ASSUME_TAC THENL
   [MATCH_MP_TAC tenv_ctor_ok_lookup THEN
    MAP_EVERY EXISTS_TAC [`type_env_c tenv`; `cn:(mlstring,mlstring)id`; `tn:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ienv_ok_def];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th) &&
                     rand(concl th) = `s1:(num,infer_t)fmap`)) THEN
  MP_TAC(ISPECL [`st1:infer_st`; `cs1:(infer_t#infer_t)list`; `s1:(num,infer_t)fmap`;
                 `ts':t list`; `num_tvs tenvE`] extend_multi_props) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `s2 = (s1:(num,infer_t)fmap) |++
       ZIP (MAP (\n. infer_st_next_uvar st1 + n) (COUNT_LIST (LENGTH (tvs:mlstring list))))
       (MAP unconvert_t ts')` THEN
  ABBREV_TAC `nc = ZIP (MAP Infer_Tuvar
       (MAP (\n. infer_st_next_uvar st1 + n) (COUNT_LIST (LENGTH (tvs:mlstring list)))))
      (MAP unconvert_t ts')` THEN
  MP_TAC(ISPECL [`num_tvs tenvE`; `s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`;
                 `ts1:infer_t list`; `tvs:mlstring list`; `ts:t list`; `ts':t list`;
                 `infer_st_next_uvar st1`] INFER1AUX_pcon_constraints) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (ts1:infer_t list) = LENGTH (ts:t list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:t list->num` o check (fun th ->
      concl th = `MAP (type_subst (alist_to_fmap (ZIP tvs ts'))) ts =
                  MAP (convert_t o t_walkstar s1) ts1`)) THEN
    REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`num_tvs tenvE`; `infer_st_next_uvar st1 + LENGTH (tvs:mlstring list)`;
                 `infer_st_subst st1`; `APPEND cs1 nc:(infer_t#infer_t)list`;
                 `s2:(num,infer_t)fmap`;
                 `ZIP (ts1:infer_t list)
                    (MAP (infer_type_subst (ZIP tvs
                       (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                            (COUNT_LIST (LENGTH (tvs:mlstring list)))))) ts)`]
         INFER1AUX_cs_core) THEN
  ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INFER1AUX_ALL_ZIP_MAP_EQ THEN ASM_REWRITE_TAC[LENGTH_MAP; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs':(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
    [`Infer_Tapp (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                    (COUNT_LIST (LENGTH (tvs:mlstring list)))) tn`;
     `infer_st_subst_fupd (K s3) (infer_st_next_uvar_fupd
        (K (infer_st_next_uvar st1 + LENGTH (tvs:mlstring list))) st1)`;
     `si:(num,infer_t)fmap`; `cs':(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN
  SUBGOAL_THEN `t_compat s1 (si:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s2:(num,infer_t)fmap` THEN
    ASM_SIMP_TAC[SUBMAP_t_compat];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `add_constraints loc ts1
        (MAP (infer_type_subst (ZIP tvs
           (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                (COUNT_LIST (LENGTH (tvs:mlstring list)))))) ts)
        (infer_st_next_uvar_fupd (K (infer_st_next_uvar st1 + LENGTH (tvs:mlstring list)))
           st1) =
      (M_success one,
       infer_st_subst_fupd (K s3) (infer_st_next_uvar_fupd
          (K (infer_st_next_uvar st1 + LENGTH (tvs:mlstring list))) st1))` ASSUME_TAC THENL
     [REWRITE_TAC[add_constraints_success] THEN
      ASM_REWRITE_TAC[infer_st_rewrs; LENGTH_MAP; infer_st_INFO.ri_accfupds; K_THM];
      ALL_TAC] THEN
    REWRITE_TAC[infer_e_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def; lookup_st_ex_def;
                infer_guard_def; INFER1AUX_n_fresh_uvar_eq] THEN
    REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[]));
    REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC t_compat_trans THEN EXISTS_TAC `s1:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[t_walkstar_eqn1; convert_t_def; injectivity "t"] THEN
    SUBGOAL_THEN `MAP (t_walkstar s2) (MAP (\n. Infer_Tuvar (infer_st_next_uvar st1 + n))
                     (COUNT_LIST (LENGTH (tvs:mlstring list)))) = MAP unconvert_t ts'`
      SUBST1_TAC THENL
     [REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_COUNT_LIST] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_convert_unconvert_list THEN
    EXISTS_TAC `num_tvs tenvE` THEN ASM_REWRITE_TAC[]];;

(* the environment of a Letrec as a pattern environment *)
let INFER1AUX_MAP2_funs = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) (uvars:infer_t list).
     LENGTH funs = LENGTH uvars
     ==> MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs uvars =
         MAP (\nt. match nt with (n,t) -> (n,(0,t))) (ZIP (MAP FST funs) uvars)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MAP; ZIP] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[CONS_11] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST]);;

(* the typing facts of a type_funs judgement *)
let INFER1AUX_type_funs_facts = prove
 (`!tenv tenvE funs bindings.
     type_funs tenv tenvE funs bindings
     ==> ALL_DISTINCT (MAP FST funs) /\ MAP FST bindings = MAP FST funs /\
         ALL (check_freevars (num_tvs tenvE) []) (MAP SND bindings)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `MAP FST (bindings:(mlstring#t)list) = MAP FST (funs:(mlstring#mlstring#exp)list)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC type_funs_MAP_FST THEN
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (funs:(mlstring#mlstring#exp)list))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tenv:type_env`; `tenvE:tenv_val_exp`;
                  `funs:(mlstring#mlstring#exp)list`; `bindings:(mlstring#t)list`]
      type_funs_distinct) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`tenv:type_env`; `tenvE:tenv_val_exp`; `funs:(mlstring#mlstring#exp)list`;
                `bindings:(mlstring#t)list`; `0`; `p2:t`; `p1:mlstring`] type_funs_Tfn) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* the inferred and the typed environments of a Letrec agree *)
let INFER1AUX_simp_tenv_invC_funs = prove
 (`!s n (bindings:(mlstring#t)list) (ks:mlstring list) (us:infer_t list).
     MAP FST bindings = ks /\ ALL_DISTINCT ks /\ LENGTH us = LENGTH ks /\
     ALL (check_freevars n []) (MAP SND bindings) /\
     (!k. k < LENGTH ks ==> t_walkstar s (EL k us) = unconvert_t (SND (EL k bindings)))
     ==> simp_tenv_invC s n (ZIP ks us) bindings`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (bindings:(mlstring#t)list) = LENGTH (ks:mlstring list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `MAP FST (bindings:(mlstring#t)list) = ks`
      then REWRITE_TAC[GSYM th; LENGTH_MAP] else failwith ""); ALL_TAC] THEN
  REWRITE_TAC[simp_tenv_invC_def] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:mlstring`; `t:t`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x = EL k (ks:mlstring list) /\ t = SND (EL k (bindings:(mlstring#t)list))`
      STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `MAP FST (bindings:(mlstring#t)list) = ks`)) THEN
      ASM_SIMP_TAC[EL_MAP] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(x:mlstring,t:t) = EL k bindings`)) THEN
      REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    SUBGOAL_THEN `k < LENGTH (ks:mlstring list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ALL (check_freevars n []) (MAP SND (bindings:(mlstring#t)list))` THEN
      REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
      ASM_SIMP_TAC[EL_MAP];
      ALL_TAC] THEN
    EXISTS_TAC `EL k (us:infer_t list)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
      ASM_SIMP_TAC[MAP_FST_ZIP; MEM_EXISTS_EL; LENGTH_ZIP] THEN
      EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[EL_ZIP];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `t':infer_t`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(MESON[cases "option"]
      `~((o1:t option) = NONE) ==> ?t. o1 = SOME t`) THEN
    REWRITE_TAC[ALOOKUP_NONE] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `FST:mlstring#infer_t->mlstring` MEM_MAP_f)) THEN
    ASM_SIMP_TAC[MAP_FST_ZIP]]);;

(* apply a lemma to the infer_funs assumption *)
let INFER1AUX_IFN_TAC (thm:thm) : tactic =
  FIRST_ASSUM(fun th ->
    if (try INFER1AUX_ec_is_app "infer_funs" (lhs(concl th)) with Failure _ -> false)
    then MP_TAC(MATCH_MP thm th) else failwith "INFER1AUX_IFN_TAC");;

(* the environment term of a Letrec, taken from the ienv_ok assumption *)
let INFER1AUX_LETREC_ENV_TAC (ttac:term -> tactic) : tactic =
  FIRST_ASSUM(fun th ->
    if INFER1AUX_ec_is_app "ienv_ok" (concl th) &&
       free_in `funs:(mlstring#mlstring#exp)list` (concl th)
    then ttac (rand(concl th)) else failwith "INFER1AUX_LETREC_ENV_TAC");;

let INFER1AUX_IEC_LETREC_TAC : tactic =
  INFER1AUX_IEC_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_tvs_bind_var_list]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[num_tvs_bind_var_list] o
    MATCH_MP INFER1AUX_type_funs_facts o
    check (fun th -> INFER1AUX_ec_is_app "type_funs" (concl th))) THEN
  SUBGOAL_THEN `LENGTH (bindings:(mlstring#t)list) = LENGTH (funs:(mlstring#mlstring#exp)list)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:mlstring list->num` o check (fun th ->
      concl th = `MAP FST (bindings:(mlstring#t)list) = MAP FST (funs:(mlstring#mlstring#exp)list)`)) THEN
    REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o
    check (fun th -> INFER1AUX_ec_is_app "sub_completion" (concl th))) THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MP_TAC(ISPECL [`st:infer_st`; `constraints:(infer_t#infer_t)list`; `s:(num,infer_t)fmap`;
                 `MAP SND (bindings:(mlstring#t)list)`; `num_tvs tenvE`] extend_multi_props) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN STRIP_TAC THEN
  ABBREV_TAC `s2 = (s:(num,infer_t)fmap) |++
       ZIP (MAP (\n. infer_st_next_uvar st + n)
              (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))
       (MAP unconvert_t (MAP SND (bindings:(mlstring#t)list)))` THEN
  ABBREV_TAC `nc = ZIP (MAP Infer_Tuvar
       (MAP (\n. infer_st_next_uvar st + n)
          (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))))
      (MAP unconvert_t (MAP SND (bindings:(mlstring#t)list)))` THEN
  ABBREV_TAC `us = MAP (\k. Infer_Tuvar (infer_st_next_uvar st + k))
                     (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))` THEN
  SUBGOAL_THEN `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`
    ASSUME_TAC THENL
   [EXPAND_TAC "us" THEN REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `simp_tenv_invC s2 (num_tvs tenvE)
                  (ZIP (MAP FST (funs:(mlstring#mlstring#exp)list)) us) bindings`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_simp_tenv_invC_funs THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    EXPAND_TAC "us" THEN ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM
    `ienv_ok (count (infer_st_next_uvar st + LENGTH (funs:(mlstring#mlstring#exp)list)))
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t)))
                                  (ZIP (MAP FST funs) us)))
                (inf_env_inf_v ienv))) ienv) /\
     env_rel_complete s2
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t)))
                                  (ZIP (MAP FST funs) us)))
                (inf_env_inf_v ienv))) ienv)
       tenv (bind_var_list 0 bindings tenvE)`) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def] o check (fun th ->
        concl th = `ienv_ok (count (infer_st_next_uvar st)) ienv`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_pes THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN EXPAND_TAC "us" THEN
        REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; MEM_COUNT_LIST] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN
        EXISTS_TAC `infer_st_next_uvar st` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
      MATCH_MP_TAC INFER1AUX_env_rel_complete_pat THEN
      MAP_EVERY EXISTS_TAC [`s:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`] THEN
      ASM_SIMP_TAC[SUBMAP_t_compat; t_compat_refl; SUBSET; IN_COUNT] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (infer_st_subst st) SUBSET
                  count (infer_st_next_uvar st + LENGTH (funs:(mlstring#mlstring#exp)list)) /\
                sub_completion (num_tvs tenvE)
                  (infer_st_next_uvar st + LENGTH (funs:(mlstring#mlstring#exp)list))
                  (infer_st_subst st) (APPEND constraints nc) s2`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sub_completion_def; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count (infer_st_next_uvar st)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ARITH_TAC;
    ALL_TAC] THEN
  INFER1AUX_LETREC_ENV_TAC (fun ie ->
    INFER1AUX_IEC_IH_TAC `funs:(mlstring#mlstring#exp)list`
      [`loc:loc_err_info`; `s2:(num,infer_t)fmap`; ie;
       `infer_st_next_uvar_fupd
          (K (infer_st_next_uvar st + LENGTH (funs:(mlstring#mlstring#exp)list))) st`;
       `APPEND constraints nc:(infer_t#infer_t)list`]
      [infer_st_rewrs]
      [`env1:infer_t list`; `st2:infer_st`; `s3:(num,infer_t)fmap`;
       `cs3:(infer_t#infer_t)list`]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `MAP SND (bindings:(mlstring#t)list) = MAP (convert_t o t_walkstar s3) env1`)) THEN
  INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_wfs)))) THEN
  ASM_REWRITE_TAC[infer_st_rewrs] THEN DISCH_TAC THEN
  INFER1AUX_IFN_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_uvar_mono))) THEN
  REWRITE_TAC[infer_st_rewrs] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] o
    check (fun th -> INFER1AUX_ec_is_app "ienv_ok" (concl th) &&
                     free_in `funs:(mlstring#mlstring#exp)list` (concl th))) THEN
  INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_t)))) THEN
  ASM_REWRITE_TAC[infer_st_rewrs; inf_env_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t_wfs (s3:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s3) env1)` ASSUME_TAC THENL
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
    EXISTS_TAC `num_tvs tenvE` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar s3) us = MAP unconvert_t (MAP SND (bindings:(mlstring#t)list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k < LENGTH (bindings:(mlstring#t)list) /\ k < LENGTH (us:infer_t list)`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP] THEN
    SUBGOAL_THEN `EL k (us:infer_t list) = Infer_Tuvar (infer_st_next_uvar st + k)`
      SUBST1_TAC THENL
     [EXPAND_TAC "us" THEN ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER1AUX_ground_transfer THEN
    MAP_EVERY EXISTS_TAC [`s2:(num,infer_t)fmap`; `num_tvs tenvE`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        is_forall(concl th) &&
        (try INFER1AUX_ec_is_app "EL" (rhs(snd(dest_imp(snd(dest_forall(concl th))))))
         with Failure _ -> false))) THEN
      ASM_SIMP_TAC[EL_MAP; LENGTH_MAP];
      MATCH_MP_TAC check_freevars_to_check_t THEN
      UNDISCH_TAC `ALL (check_freevars (num_tvs tenvE) []) (MAP SND (bindings:(mlstring#t)list))` THEN
      REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
      ASM_SIMP_TAC[EL_MAP]];
    ALL_TAC] THEN
  INFER1AUX_LETREC_ENV_TAC (fun ie ->
    SUBGOAL_THEN (list_mk_comb(`env_rel_complete:(num,infer_t)fmap->inf_env->type_env->tenv_val_exp->bool`,
                  [`s3:(num,infer_t)fmap`; ie; `tenv:type_env`; `bind_var_list 0 bindings tenvE`]))
      ASSUME_TAC THENL
     [MATCH_MP_TAC env_rel_complete_t_compat THEN EXISTS_TAC `s2:(num,infer_t)fmap` THEN
      ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`num_tvs tenvE`; `st2:infer_st`; `cs3:(infer_t#infer_t)list`;
                  `s3:(num,infer_t)fmap`; `ZIP (us:infer_t list) (env1:infer_t list)`; ie; `tenv:type_env`;
                  `bind_var_list 0 bindings tenvE`] INFER1AUX_iec_constrain)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY INFER1AUX_IEC_ACCEPT_TAC THEN
    MATCH_MP_TAC INFER1AUX_ALL_ZIP_MAP_EQ THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:(num,infer_t)fmap` (X_CHOOSE_THEN `si:(num,infer_t)fmap`
    (X_CHOOSE_THEN `cs4:(infer_t#infer_t)list` STRIP_ASSUME_TAC))) THEN
  INFER1AUX_LETREC_ENV_TAC (fun ie ->
    SUBGOAL_THEN (list_mk_comb(`ienv_ok:(num->bool)->inf_env->bool`,
                               [`count (infer_st_next_uvar st2)`; ie])) ASSUME_TAC THENL
     [MATCH_MP_TAC ienv_ok_more THEN
      EXISTS_TAC `infer_st_next_uvar st + LENGTH (funs:(mlstring#mlstring#exp)list)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    INFER1AUX_IEC_IH_TAC `e:exp`
      [`loc:loc_err_info`; `si:(num,infer_t)fmap`; ie;
       `infer_st_subst_fupd (K s4) st2`; `cs4:(infer_t#infer_t)list`]
      [infer_st_rewrs]
      [`tt:infer_t`; `st4:infer_st`; `s5:(num,infer_t)fmap`;
       `cs5:(infer_t#infer_t)list`]) THEN
  SUBGOAL_THEN
    `add_constraints loc us env1 st2 = (M_success one, infer_st_subst_fupd (K s4) st2)`
    ASSUME_TAC THENL
   [REWRITE_TAC[add_constraints_success] THEN
    ASM_REWRITE_TAC[infer_st_rewrs; infer_st_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`tt:infer_t`; `st4:infer_st`; `s5:(num,infer_t)fmap`;
                        `cs5:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[infer_e_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def;
                INFER1AUX_n_fresh_uvar_eq] THEN
    ASM_SIMP_TAC[INFER1AUX_check_dups_ok] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INFER1AUX_MAP2_funs] THEN
    REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[infer_st_rewrs] THEN CASE_REWRITE_TAC[]));
    SUBGOAL_THEN `t_compat s (s2:(num,infer_t)fmap)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SUBMAP_t_compat]; ALL_TAC] THEN
    ASM_MESON_TAC[t_compat_trans]];;


let infer_e_complete = prove
 (`(!tenv tenvE e t.
     type_e tenv tenvE e t
     ==> !loc s ienv st constraints.
           ienv_ok (count (infer_st_next_uvar st)) ienv /\
           t_wfs (infer_st_subst st) /\
           FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
             constraints s /\
           FDOM s = count (infer_st_next_uvar st) /\
           env_rel_complete s ienv tenv tenvE
           ==> ?t' st' s' constraints'.
                 infer_e loc ienv e st = (M_success t',st') /\
                 sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
                   constraints' s' /\
                 FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
                 FDOM s' = count (infer_st_next_uvar st') /\
                 t_compat s s' /\
                 t = convert_t (t_walkstar s' t')) /\
   (!tenv tenvE es ts.
     type_es tenv tenvE es ts
     ==> !loc s ienv st constraints.
           ienv_ok (count (infer_st_next_uvar st)) ienv /\
           t_wfs (infer_st_subst st) /\
           FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
             constraints s /\
           FDOM s = count (infer_st_next_uvar st) /\
           env_rel_complete s ienv tenv tenvE
           ==> ?ts' st' s' constraints'.
                 infer_es loc ienv es st = (M_success ts',st') /\
                 sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
                   constraints' s' /\
                 FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
                 FDOM s' = count (infer_st_next_uvar st') /\
                 t_compat s s' /\
                 ts = MAP (convert_t o t_walkstar s') ts') /\
   (!tenv tenvE funs env.
     type_funs tenv tenvE funs env
     ==> !loc s ienv st constraints.
           ienv_ok (count (infer_st_next_uvar st)) ienv /\
           t_wfs (infer_st_subst st) /\
           FDOM (infer_st_subst st) SUBSET count (infer_st_next_uvar st) /\
           sub_completion (num_tvs tenvE) (infer_st_next_uvar st) (infer_st_subst st)
             constraints s /\
           FDOM s = count (infer_st_next_uvar st) /\
           env_rel_complete s ienv tenv tenvE
           ==> ?env' st' s' constraints'.
                 infer_funs loc ienv funs st = (M_success env',st') /\
                 sub_completion (num_tvs tenvE) (infer_st_next_uvar st') (infer_st_subst st')
                   constraints' s' /\
                 FDOM (infer_st_subst st') SUBSET count (infer_st_next_uvar st') /\
                 FDOM s' = count (infer_st_next_uvar st') /\
                 t_compat s s' /\
                 MAP SND env = MAP (convert_t o t_walkstar s') env')`,
  MATCH_MP_TAC type_e_strongind THEN REPEAT CONJ_TAC THENL
   [INFER1AUX_IEC_LIT_TAC `Infer_Tapp [] Tint_num`;
    INFER1AUX_IEC_LIT_TAC `Infer_Tapp [] Tchar_num`;
    INFER1AUX_IEC_LIT_TAC `Infer_Tapp [] Tstring_num`;
    INFER1AUX_IEC_LIT_TAC `Infer_Tapp [] Tword8_num`;
    INFER1AUX_IEC_LIT_TAC `Infer_Tapp [] Tword64_num`;
    INFER1AUX_IEC_LIT_TAC `Infer_Tapp [] Tdouble_num`;
    INFER1AUX_IEC_RAISE_TAC; INFER1AUX_IEC_HANDLE_TAC; INFER1AUX_IEC_CONSOME_TAC;
    INFER1AUX_IEC_CONNONE_TAC; INFER1AUX_IEC_VAR_TAC; INFER1AUX_IEC_FUN_TAC;
    INFER1AUX_IEC_APP_TAC; INFER1AUX_IEC_LOG_TAC; INFER1AUX_IEC_IF_TAC;
    INFER1AUX_IEC_MAT_TAC; INFER1AUX_IEC_LET_TAC; INFER1AUX_IEC_LETREC_TAC;
    INFER1AUX_IEC_TANNOT_TAC; INFER1AUX_IEC_LANNOT_TAC; INFER1AUX_IEC_NIL_TAC;
    INFER1AUX_IEC_ESCONS_TAC; INFER1AUX_IEC_NIL_TAC; INFER1AUX_IEC_FUNSCONS_TAC]);;
