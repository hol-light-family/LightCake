(* ========================================================================= *)
(* walk: port of HOL4 examples/algorithms/unification/triangular/           *)
(* first-order/walkScript.sml (HOL4 library used by CakeML v3479): walking  *)
(* a variable or a term through a triangular substitution.                  *)
(*                                                                           *)
(* How vwalk is defined: HOL4 defines vwalk with a schematic TFL definition *)
(* (xDefineSchema) whose termination relation is vR s and whose hypotheses  *)
(* are discharged by wfs s.  Here vwalk is a new_specification of a        *)
(* function proved to exist (by WF_REC on vR s for each s with wfs s), with *)
(* exactly HOL4's characterisation vwalk_def as its defining property; its  *)
(* values are unspecified when wfs s fails, as in HOL4.                      *)
(*                                                                           *)
(* Notes: HOL4 vwalk_ind has the hypothesis wfs s; here the hypothesis is   *)
(* discharged (!s. wfs s ==> !P. ...).  vwalk_al is HOL4's overload        *)
(* \al. vwalk (alist_to_fmap al), written out.  Not ported (not used by the *)
(* CakeML closure): vwalk_rhs, ELENGTH and their lemmas.  HOL4 walk_thm is *)
(* walk_walk_thm (CakeML's pattern_comp has a theorem walk_thm).  Helper    *)
(* lemmas are LUNIFAUX_.                                                     *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/alist.ml";;
needs "hol4/subst.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* vwalk.                                                                    *)
(* ------------------------------------------------------------------------- *)

let LUNIFAUX_vwalk_exists_s = prove
 (CASE_TERM `!s:(num,A term_term)fmap. wfs s ==> ?g.
     !v. g v =
     (match FLOOKUP s v with SOME (term_Var u) -> g u | SOME t -> t
                           | NONE -> term_Var v)`,
  GEN_TAC THEN REWRITE_TAC[wfs_def] THEN DISCH_TAC THEN
  MP_TAC(ISPEC (CASE_TERM
      `\(g:num->A term_term) (v:num).
         match FLOOKUP (s:(num,A term_term)fmap) v with
           SOME (term_Var u) -> g u | SOME t -> t | NONE -> term_Var v`)
    (MATCH_MP WF_REC (ASSUME `WF (vR (s:(num,A term_term)fmap))`))) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`f:num->A term_term`; `g:num->A term_term`; `x:num`] THEN
  DISCH_TAC THEN CASES_ON `FLOOKUP (s:(num,A term_term)fmap) x` THEN
  REWRITE_TAC[option_CASE] THEN CASES_ON `a:A term_term` THEN
  REWRITE_TAC[term_term_CASE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[vR_def; option_CASE; term_vars_def; IN_SING]);;

let vwalk_def = new_specification ["vwalk"]
 (prove
   (CASE_TERM `?vwalk. !(s:(num,A term_term)fmap) v. wfs s ==>
      vwalk s v =
      (match FLOOKUP s v with SOME (term_Var u) -> vwalk s u | SOME t -> t
                            | NONE -> term_Var v)`,
    MP_TAC(REWRITE_RULE[GSYM RIGHT_EXISTS_IMP_THM; SKOLEM_THM]
             LUNIFAUX_vwalk_exists_s) THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]));;

let vwalk_ind = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !P. (!v. (!u. FLOOKUP s v = SOME (term_Var u) ==> P u) ==> P v)
         ==> !v. P v`,
  GEN_TAC THEN REWRITE_TAC[wfs_def; WF_IND] THEN DISCH_TAC THEN
  X_GEN_TAC `P:num->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `P:num->bool`) THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `!u. FLOOKUP (s:(num,A term_term)fmap) x = SOME (term_Var u) ==> P u`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[vR_def; option_CASE; term_vars_def; IN_SING];
    ASM_MESON_TAC[]]);;

let NOT_FDOM_vwalk = prove
 (`!(s:(num,A term_term)fmap) v.
     wfs s /\ ~(v IN FDOM s) ==> vwalk s v = term_Var v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP vwalk_def th]) THEN
  ASM_REWRITE_TAC[FLOOKUP_DEF; option_CASE]);;

let vwalk_to_var = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !v u. vwalk s v = term_Var u ==> ~(u IN FDOM s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN X_GEN_TAC `u:num` THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP vwalk_def th]) THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_CASE] THENL
   [REWRITE_TAC[term_term_11] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[flookup_thm];
    CASES_ON `a:A term_term` THEN
    REWRITE_TAC[term_term_CASE; term_term_distinct] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* walk.                                                                     *)
(* ------------------------------------------------------------------------- *)

let walk_def = cake_def
  `walk (s:(num,A term_term)fmap) t =
     match t with term_Var v -> vwalk s v | t -> t`;;

let walk_walk_thm = prove
 (`!(s:(num,A term_term)fmap) v t1 t2 c.
     walk s (term_Var v) = vwalk s v /\
     walk s (Pair t1 t2) = Pair t1 t2 /\
     walk s (Const c) = Const c`,
  REWRITE_TAC[walk_def; term_term_CASE]);;

let walk_FEMPTY = prove
 (`!(t:A term_term) v.
     walk FEMPTY t = t /\ vwalk (FEMPTY:(num,A term_term)fmap) v = term_Var v`,
  SUBGOAL_THEN `!v. vwalk (FEMPTY:(num,A term_term)fmap) v = term_Var v`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC NOT_FDOM_vwalk THEN
    REWRITE_TAC[wfs_FEMPTY; FDOM_FEMPTY; NOT_IN_EMPTY];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_term_INDUCT THEN
    ASM_REWRITE_TAC[walk_walk_thm]]);;

let walk_var_vwalk = prove
 (`!(s:(num,A term_term)fmap) t v.
     wfs s ==> walk s t = term_Var v ==> ?u. t = term_Var u /\ vwalk s u = term_Var v`,
  GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[walk_walk_thm; term_term_distinct; term_term_11] THEN MESON_TAC[]);;

let walk_to_var = prove
 (`!(s:(num,A term_term)fmap) t v.
     wfs s /\ walk s t = term_Var v ==> ~(v IN FDOM s) /\ ?u. t = term_Var u`,
  GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[walk_walk_thm; term_term_distinct; term_term_11] THEN
  MESON_TAC[vwalk_to_var]);;

let vwalk_vR = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !v u. u IN term_vars (vwalk s v) /\ ~(vwalk s v = term_Var v)
                     ==> TC (vR s) u v`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN X_GEN_TAC `u:num` THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP vwalk_def th]) THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_CASE] THEN CASES_ON `a:A term_term` THEN
  REWRITE_TAC[term_term_CASE; term_term_distinct; term_vars_def; NOT_IN_EMPTY] THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `vR (s:(num,A term_term)fmap) a' v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[vR_def; option_CASE; term_vars_def; IN_SING]; ALL_TAC] THEN
    ASM_CASES_TAC `vwalk (s:(num,A term_term)fmap) a' = term_Var a'` THENL
     [UNDISCH_TAC `u IN term_vars (vwalk (s:(num,A term_term)fmap) a')` THEN
      ASM_REWRITE_TAC[term_vars_def; IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC `a':num` THEN
      ASM_MESON_TAC[]];
    STRIP_TAC THEN MATCH_MP_TAC TC_INC THEN
    ASM_REWRITE_TAC[vR_def; option_CASE; term_vars_def]]);;

let vwalk_IN_FRANGE = prove
 (`!(s:(num,A term_term)fmap) v.
     wfs s /\ v IN FDOM s ==> vwalk s v IN FRANGE s`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP vwalk_def th]) THEN
  SUBGOAL_THEN `FLOOKUP (s:(num,A term_term)fmap) v = SOME (FAPPLY s v)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  CASES_ON `FAPPLY (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[term_term_CASE] THENL
   [ASM_CASES_TAC `(a:num) IN FDOM (s:(num,A term_term)fmap)` THENL
     [ASM_MESON_TAC[];
      ASM_SIMP_TAC[NOT_FDOM_vwalk] THEN REWRITE_TAC[IN_FRANGE] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[IN_FRANGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_FRANGE] THEN ASM_MESON_TAC[]]);;

let walk_IN_FRANGE = prove
 (`!(s:(num,A term_term)fmap) t.
     wfs s /\ ~(walk s t = t) ==> walk s t IN FRANGE s`,
  GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN REWRITE_TAC[walk_walk_thm] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC vwalk_IN_FRANGE THEN
  ASM_MESON_TAC[NOT_FDOM_vwalk]);;

let vwalk_SUBMAP = prove
 (CASE_TERM `!sx:(num,A term_term)fmap. wfs sx ==>
     !v s. s SUBMAP sx ==>
           (match vwalk s v with term_Var u -> vwalk sx v = vwalk sx u
                               | t -> vwalk sx v = t)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN X_GEN_TAC `s:(num,A term_term)fmap` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_SUBMAP]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`] vwalk_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_CASE; term_term_CASE] THEN
  SUBGOAL_THEN `FLOOKUP (sx:(num,A term_term)fmap) v = SOME a` ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOKUP_SUBMAP]; ALL_TAC] THEN
  MP_TAC(SPECL [`sx:(num,A term_term)fmap`; `v:num`] vwalk_def) THEN
  ASM_REWRITE_TAC[option_CASE] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `a:A term_term` THEN REWRITE_TAC[term_term_CASE] THEN
  ASM_MESON_TAC[]);;

let vwalk_no_cycles = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !v u. vwalk s v = term_Var u /\ v IN FDOM s ==> ~(v = u)`,
  MESON_TAC[vwalk_to_var]);;

(* ------------------------------------------------------------------------- *)
(* vwalk with concrete alists (HOL4 vwalk_al al = vwalk (alist_to_fmap al)). *)
(* ------------------------------------------------------------------------- *)

let vwalk_al_thm = prove
 (CASE_TERM `!(al:(num#A term_term)list) v.
     wfs (alist_to_fmap al) ==>
     vwalk (alist_to_fmap al) v =
     (match ALOOKUP al v with
        NONE -> term_Var v
      | SOME (term_Var u) -> vwalk (alist_to_fmap al) u
      | SOME t -> t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP vwalk_def th]) THEN
  REWRITE_TAC[ALOOKUP_EQ_FLOOKUP]);;

let vwalk_al_eq_vwalk = prove
 (`!s:(num,A term_term)fmap. vwalk s = vwalk (alist_to_fmap (fmap_to_alist s))`,
  REWRITE_TAC[fmap_to_alist_to_fmap]);;

let _ = cake_add_simps [walk_walk_thm; walk_FEMPTY];;
