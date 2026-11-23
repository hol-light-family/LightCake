(* ========================================================================= *)
(* subst: port of HOL4 examples/algorithms/unification/triangular/          *)
(* first-order/substScript.sml (HOL4 library used by CakeML v3479):         *)
(* triangular substitutions, finite maps from variables to terms, and their *)
(* well-formedness wfs (the variable relation vR is well-founded).          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's type abbreviation subst = num |-> 'a term takes a parameter,    *)
(*   which HOL Light abbreviations cannot: the port writes                   *)
(*   (num,A term_term)fmap.                                                  *)
(* - HOL4 s ' v is FAPPLY s v, BIGUNION is UNIONS, R^+ is TC R, FUNPOW f n x *)
(*   is ITER n f x; the HOL4 infix for subst_APPLY is not used.              *)
(* - Not ported (the CakeML closure does not use them): s_o_s, selfapp, vR1  *)
(*   and the fixpoint characterisation of wfs (wfs_iff_fixpoint); of that   *)
(*   part only IN_vars_APPLY is here.  Helper lemmas are LUNIFAUX_.         *)
(* - HOL4 vR is subst_vR (a short or common word), and vR_def is             *)
(*   subst_vR_def.                                                           *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/basic.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/term.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* rangevars, substvars, the variable relation vR and wfs.                   *)
(* ------------------------------------------------------------------------- *)

let FUNPOW_extends_mono = prove
 (`!P (f:A->A) x n. (!x. P x ==> P (f x)) /\ P x ==> P (ITER n f x)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ITER]);;

let rangevars_def = new_definition
  `rangevars (s:(B,A term_term)fmap) = UNIONS (IMAGE term_vars (FRANGE s))`;;

let FINITE_rangevars = prove
 (`!s:(B,A term_term)fmap. FINITE (rangevars s)`,
  SIMP_TAC[rangevars_def; FINITE_UNIONS; FINITE_IMAGE; FINITE_FRANGE;
           FORALL_IN_IMAGE; FINITE_vars]);;

let IN_FRANGE_rangevars = prove
 (`!t (s:(B,A term_term)fmap). t IN FRANGE s ==> term_vars t SUBSET rangevars s`,
  REWRITE_TAC[rangevars_def; SUBSET; IN_UNIONS; IN_IMAGE] THEN MESON_TAC[]);;

let rangevars_FUPDATE = prove
 (`!(s:(B,A term_term)fmap) v t.
     ~(v IN FDOM s) ==> rangevars (s |+ (v,t)) = rangevars s UNION term_vars t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rangevars_def; EXTENSION; IN_UNIONS;
    IN_IMAGE; IN_UNION; IN_FRANGE; FDOM_FUPDATE; IN_INSERT;
    FAPPLY_FUPDATE_THM] THEN
  ASM_MESON_TAC[]);;

let substvars_def = new_definition
  `substvars (s:(num,A term_term)fmap) = FDOM s UNION rangevars s`;;

let FINITE_substvars = prove
 (`!s:(num,A term_term)fmap. FINITE (substvars s)`,
  SIMP_TAC[substvars_def; FINITE_UNION; FDOM_FINITE; FINITE_rangevars]);;

let subst_vR_def = cake_def
  `subst_vR (s:(B,A term_term)fmap) y x =
     match FLOOKUP s x with SOME t -> y IN term_vars t | _ -> F`;;

let LUNIFAUX_vR_FDOM = prove
 (`!(s:(B,A term_term)fmap) y x. subst_vR s y x ==> x IN FDOM s`,
  REWRITE_TAC[subst_vR_def; FLOOKUP_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

let wfs_def = new_definition
  `wfs (s:(num,A term_term)fmap) <=> WF (subst_vR s)`;;

let wfs_FEMPTY = prove
 (`wfs (FEMPTY:(num,A term_term)fmap)`,
  REWRITE_TAC[wfs_def] THEN MATCH_MP_TAC WF_SUBSET THEN
  EXISTS_TAC `\x:num y:num. F` THEN
  REWRITE_TAC[WF_FALSE; subst_vR_def; FLOOKUP_EMPTY; option_CASE]);;

let wfs_SUBMAP = prove
 (`!(s:(num,A term_term)fmap) sx. wfs sx /\ s SUBMAP sx ==> wfs s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wfs_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC WF_SUBSET THEN EXISTS_TAC `subst_vR (sx:(num,A term_term)fmap)` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN
  REWRITE_TAC[subst_vR_def] THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `FLOOKUP (sx:(num,A term_term)fmap) v = SOME a`
    (fun th -> REWRITE_TAC[th; option_CASE]) THEN
  ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let wfs_no_cycles = prove
 (`!s:(num,A term_term)fmap. wfs s <=> !v. ~TC (subst_vR s) v v`,
  GEN_TAC THEN REWRITE_TAC[wfs_def] THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC WF_REFL THEN
    REWRITE_TAC[ETA_AX; WF_TC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[WF_DCHAIN; NOT_EXISTS_THM] THEN
  X_GEN_TAC `f:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. (f:num->num) n IN FDOM (s:(num,A term_term)fmap)`
    ASSUME_TAC THENL [ASM_MESON_TAC[LUNIFAUX_vR_FDOM]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!m n. m < n ==> TC (subst_vR (s:(num,A term_term)fmap)) ((f:num->num) n) (f m)`
    ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[TC_INC]; ASM_MESON_TAC[TC_TRANS_R]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(!x y. (f:num->num) x = f y ==> x = y)` MP_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `(:num)` o MATCH_MP INFINITE_IMAGE_INJ) THEN
    REWRITE_TAC[num_INFINITE; INFINITE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `FDOM (s:(num,A term_term)fmap)` THEN
    REWRITE_TAC[FDOM_FINITE; SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
    DISJ_CASES_TAC(SPECL [`m:num`; `n:num`] LT_CASES) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    POP_ASSUM DISJ_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Applying a substitution directly.                                         *)
(* ------------------------------------------------------------------------- *)

let subst_APPLY_def = cake_def
  `(subst_APPLY (s:(num,A term_term)fmap) (term_Var v) =
      match FLOOKUP s v with NONE -> term_Var v | SOME t -> t) /\
   (subst_APPLY s (Pair t1 t2) = Pair (subst_APPLY s t1) (subst_APPLY s t2)) /\
   (subst_APPLY s (Const c) = Const c)`;;

let subst_APPLY_FAPPLY = prove
 (`!(s:(num,A term_term)fmap) v.
     v IN FDOM s ==> FAPPLY s v = subst_APPLY s (term_Var v)`,
  SIMP_TAC[subst_APPLY_def; FLOOKUP_DEF; option_CASE]);;

let noids_def = new_definition
  `noids (s:(num,A term_term)fmap) <=> !v. ~(FLOOKUP s v = SOME (term_Var v))`;;

let subst_APPLY_id = prove
 (`!(s:(num,A term_term)fmap) t.
     subst_APPLY s t = t <=>
     !v. v IN term_vars t /\ v IN FDOM s ==> FAPPLY s v = term_Var v`,
  GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[subst_APPLY_def; term_vars_def; IN_SING; NOT_IN_EMPTY;
                  IN_UNION; term_term_11] THENL
   [REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[];
    MESON_TAC[]]);;

let idempotent_def = new_definition
  `idempotent (s:(num,A term_term)fmap) <=>
     !t. subst_APPLY s (subst_APPLY s t) = subst_APPLY s t`;;

let wfs_noids = prove
 (`!s:(num,A term_term)fmap. wfs s ==> noids s`,
  REWRITE_TAC[wfs_no_cycles; noids_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:num`) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC TC_INC THEN
  ASM_REWRITE_TAC[subst_vR_def; option_CASE; term_vars_def; IN_SING]);;

let LUNIFAUX_EXISTS_EQ_R = prove
 (`!(P:B->bool) a. (?x. P x /\ x = a) <=> P a`,
  MESON_TAC[]);;

let IN_vars_APPLY = prove
 (`!(s:(num,A term_term)fmap) t v.
     v IN term_vars (subst_APPLY s t) <=>
     ~(v IN FDOM s) /\ v IN term_vars t \/ ?x. subst_vR s v x /\ x IN term_vars t`,
  GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[subst_APPLY_def; term_vars_def; IN_SING; NOT_IN_EMPTY;
                  IN_UNION; LUNIFAUX_EXISTS_EQ_R] THENL
   [REWRITE_TAC[subst_vR_def; FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_CASE; term_vars_def; IN_SING] THEN ASM_MESON_TAC[];
    MESON_TAC[]]);;

let LUNIFAUX_vR_ALT = prove
 (`!(s:(B,A term_term)fmap) y x.
     subst_vR s y x <=> x IN FDOM s /\ y IN term_vars (FAPPLY s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subst_vR_def; FLOOKUP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

let LUNIFAUX_IN_rangevars = prove
 (`!(s:(B,A term_term)fmap) v.
     v IN rangevars s <=> ?x. x IN FDOM s /\ v IN term_vars (FAPPLY s x)`,
  REWRITE_TAC[rangevars_def; IN_UNIONS; IN_IMAGE; IN_FRANGE] THEN
  MESON_TAC[]);;

let idempotent_rangevars = prove
 (`!s:(num,A term_term)fmap.
     idempotent s /\ noids s <=> DISJOINT (FDOM s) (rangevars s)`,
  GEN_TAC THEN REWRITE_TAC[IN_DISJOINT; LUNIFAUX_IN_rangevars] THEN
  EQ_TAC THENL
   [REWRITE_TAC[idempotent_def; noids_def] THEN STRIP_TAC THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `v:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `term_Var x:A term_term`) THEN
    ASM_SIMP_TAC[GSYM subst_APPLY_FAPPLY; subst_APPLY_id] THEN
    DISCH_THEN(MP_TAC o SPEC `v:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `v:num`) THEN
    ASM_REWRITE_TAC[FLOOKUP_DEF];
    DISCH_TAC THEN REWRITE_TAC[idempotent_def; noids_def] THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[subst_APPLY_id; IN_vars_APPLY;
                               LUNIFAUX_vR_ALT] THEN
      ASM_MESON_TAC[];
      GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      REWRITE_TAC[] THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[term_vars_def; IN_SING]]]);;

let wfs_FAPPLY_var = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !v. v IN FDOM s ==> ~(FAPPLY s v = term_Var v)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP wfs_noids) THEN
  REWRITE_TAC[noids_def; FLOOKUP_DEF] THEN MESON_TAC[]);;

let TC_vR_vars_FRANGE = prove
 (`!(s:(num,A term_term)fmap) u v.
     TC (subst_vR s) u v ==> v IN FDOM s ==> u IN UNIONS (IMAGE term_vars (FRANGE s))`,
  REWRITE_TAC[GSYM rangevars_def; LUNIFAUX_IN_rangevars] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TC_CASES_R] THEN
  REWRITE_TAC[LUNIFAUX_vR_ALT] THEN MESON_TAC[]);;

let wfs_idempotent = prove
 (`!s:(num,A term_term)fmap. idempotent s /\ noids s ==> wfs s`,
  GEN_TAC THEN REWRITE_TAC[idempotent_rangevars; wfs_no_cycles] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TC_vR_vars_FRANGE) THEN
  REWRITE_TAC[GSYM rangevars_def] THEN
  SUBGOAL_THEN `(v:num) IN FDOM (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[TC_CASES_L]) THEN
    MESON_TAC[LUNIFAUX_vR_FDOM];
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let _ = cake_add_simps
  [FINITE_rangevars; FINITE_substvars; wfs_FEMPTY; subst_APPLY_def];;
