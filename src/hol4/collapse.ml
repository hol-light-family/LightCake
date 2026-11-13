(* ========================================================================= *)
(* collapse: port of HOL4 examples/algorithms/unification/triangular/       *)
(* first-order/collapseScript.sml (HOL4 library used by CakeML v3479):      *)
(* collapsing a triangular substitution into an idempotent one, and its     *)
(* relation to walkstar.  (Collapsing destroys the shared tails of a        *)
(* triangular substitution; walkstar is the intended way to apply one.)     *)
(*                                                                           *)
(* Notes: HOL4 walk-star is walkstar, and HOL4 s ' v is FAPPLY s v.         *)
(* Helper lemmas are LUNIFAUX_.                                              *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/walkstar.ml";;

type_invention_error := true;;

let collapse_def = new_definition
  `collapse (s:(num,A term_term)fmap) =
     FUN_FMAP (\v. walkstar s (term_Var v)) (FDOM s)`;;

let LUNIFAUX_FLOOKUP_collapse = prove
 (`!(s:(num,A term_term)fmap) v.
     FLOOKUP (collapse s) v =
     if v IN FDOM s then SOME (walkstar s (term_Var v)) else NONE`,
  SIMP_TAC[collapse_def; FLOOKUP_FUN_FMAP; FDOM_FINITE]);;

let collapse_APPLY_eq_walkstar = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !t. subst_APPLY (collapse s) t = walkstar s t`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  ASM_SIMP_TAC[subst_APPLY_def; walkstar_thm; LUNIFAUX_FLOOKUP_collapse] THEN
  X_GEN_TAC `v:num` THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[option_CASE; walkstar_thm; NOT_FDOM_vwalk; term_term_CASE]);;

let collapse_FAPPLY_eq_walkstar = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !v. v IN FDOM s ==> FAPPLY (collapse s) v = walkstar s (term_Var v)`,
  SIMP_TAC[collapse_def; FUN_FMAP_DEF; FDOM_FINITE]);;

let walkstar_unchanged = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !t. DISJOINT (term_vars t) (FDOM s) ==> walkstar s t = t`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  ASM_SIMP_TAC[walkstar_thm; term_vars_def; DISJOINT_UNION; DISJOINT_INSERT;
               DISJOINT_EMPTY; NOT_FDOM_vwalk; term_term_CASE]);;

let collapse_idempotent = prove
 (`!s:(num,A term_term)fmap. wfs s ==> idempotent (collapse s)`,
  SIMP_TAC[idempotent_def; collapse_APPLY_eq_walkstar] THEN
  MESON_TAC[walkstar_idempotent]);;

let idempotent_collapse = prove
 (`!s:(num,A term_term)fmap. idempotent s /\ noids s ==> collapse s = s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_idempotent]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[idempotent_rangevars]
    (ASSUME `idempotent (s:(num,A term_term)fmap) /\ noids s`)) THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM fmap_EQ_THM] THEN
  SIMP_TAC[collapse_def; FUN_FMAP_DEF; FDOM_FINITE] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `x:num`; `ARB:A term_term`;
                `ARB:A term_term`; `ARB:A`] apply_ts_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `FLOOKUP (s:(num,A term_term)fmap) x = SOME (FAPPLY s x)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  REWRITE_TAC[option_CASE] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP walkstar_unchanged) THEN
  UNDISCH_TAC `DISJOINT (FDOM (s:(num,A term_term)fmap)) (rangevars s)` THEN
  REWRITE_TAC[LUNIFAUX_IN_rangevars; IN_DISJOINT] THEN ASM_MESON_TAC[]);;

let walkstar_eq_idem_APPLY = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> (idempotent s <=> walkstar s = subst_APPLY s)`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    MP_TAC(SPEC `s:(num,A term_term)fmap` idempotent_collapse) THEN
    ASM_SIMP_TAC[wfs_noids] THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THEN
    ASM_SIMP_TAC[collapse_APPLY_eq_walkstar];
    DISCH_TAC THEN REWRITE_TAC[idempotent_def] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[walkstar_idempotent]]);;

let subst_APPLY_walkstar = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !t. subst_APPLY s (walkstar s t) = walkstar s t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP apply_ts_ind) THEN
  ASM_SIMP_TAC[apply_ts_thm; subst_APPLY_def] THEN
  X_GEN_TAC `v:num` THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  ASM_REWRITE_TAC[option_CASE; subst_APPLY_def] THEN
  DISCH_THEN MATCH_MP_TAC THEN REFL_TAC);;

let collapse_noids = prove
 (`!s:(num,A term_term)fmap. wfs s ==> noids (collapse s)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[noids_def; LUNIFAUX_FLOOKUP_collapse] THEN X_GEN_TAC `v:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ASM_SIMP_TAC[walkstar_thm] THEN
  CASES_ON `vwalk (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[term_term_CASE; term_term_distinct; term_term_11] THEN
  ASM_MESON_TAC[vwalk_to_var]);;

let wfs_collapse = prove
 (`!s:(num,A term_term)fmap. wfs s ==> wfs (collapse s)`,
  MESON_TAC[collapse_idempotent; collapse_noids; wfs_idempotent]);;
