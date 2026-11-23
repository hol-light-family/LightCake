(* ========================================================================= *)
(* walkstar: port of HOL4 examples/algorithms/unification/triangular/       *)
(* first-order/walkstarScript.sml (HOL4 library used by CakeML v3479):      *)
(* applying a triangular substitution completely (HOL4 walk-star, here      *)
(* walkstar), and the occurs check walkstar_oc (HOL4 oc).                    *)
(*                                                                           *)
(* How walkstar is defined: HOL4 defines it with a schematic TFL definition *)
(* (xDefineSchema) instantiated with the relation walkstarR s, whose        *)
(* hypotheses walkstar_th1, walkstar_th2, walkstar_thWF hold under wfs s.   *)
(* Here walkstar is a new_specification of a function proved to exist (by   *)
(* WF_REC on walkstarR s for each s with wfs s), with exactly HOL4's         *)
(* characterisation walkstar_def as its defining property.                  *)
(*                                                                           *)
(* Notes: the HOL4 overload walk-star is walkstar; HOL4 mlt R is            *)
(* TC (mlt1 R), R^+ is TC R and the reflexive transitive closure is RTC R.  *)
(* HOL4 walkstar_ind and apply_ts_ind have the hypothesis wfs s; here it is *)
(* discharged (!s. wfs s ==> !P. ...).  The termination conditions          *)
(* walkstar_th1/th2 are stated !t t1 t2. walk s t = Pair t1 t2 ==>          *)
(* walkstarR s ti t.  walkstar_oc (HOL4 oc, renamed: oc is a common         *)
(* variable name) is an inductive relation as in HOL4 (s is a schematic      *)
(* variable of the rules).  Helper lemmas (HOL4 val bindings that are not    *)
(* stored theorems) are LUNIFAUX_.                                           *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/bag.ml";;
needs "hol4/walk.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The termination relation walkstarR and its properties.                    *)
(* ------------------------------------------------------------------------- *)

let walkstarR_def = new_definition
  `walkstarR (s:(num,A term_term)fmap) =
     inv_image (TC (mlt1 (TC (subst_vR s))) LEX MEASURE pair_count)
               (\t:A term_term. (varb t, t))`;;

let walkstar_thWF = prove
 (`!s:(num,A term_term)fmap. wfs s ==> WF (walkstarR s)`,
  REWRITE_TAC[wfs_def; walkstarR_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WF_inv_image THEN MATCH_MP_TAC WF_LEX_HOL4 THEN
  REWRITE_TAC[WF_MEASURE; WF_TC] THEN MATCH_MP_TAC WF_mlt1 THEN
  ASM_REWRITE_TAC[WF_TC]);;

let LUNIFAUX_walkstarR_Var = prove
 (`!(s:(num,A term_term)fmap) n t.
     wfs s /\ (!e. e IN term_vars t ==> TC (subst_vR s) e n)
     ==> walkstarR s t (term_Var n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[walkstarR_def; inv_image_THM; LEX_THM; varb_def] THEN
  DISJ1_TAC THEN MATCH_MP_TAC TC_INC THEN
  REWRITE_TAC[mlt1_def; FINITE_varb; FINITE_BAG_THM] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `varb (t:A term_term)`; `EMPTY_BAG:num->num`] THEN
  ASM_REWRITE_TAC[BAG_UNION_EMPTY; IN_varb_vars]);;

let walkstar_th1 = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !t t1 t2. walk s t = Pair t1 t2 ==> walkstarR s t1 t`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[walk_walk_thm; term_term_distinct; term_term_11] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LUNIFAUX_walkstarR_Var THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_vR) THEN
    ASM_REWRITE_TAC[term_vars_def; IN_UNION; term_term_distinct];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[walkstarR_def; inv_image_THM; LEX_THM; varb_def;
                measure_THM; pair_count_def] THEN
    ASM_CASES_TAC `varb (a1:A term_term) = EMPTY_BAG` THENL
     [ASM_REWRITE_TAC[BAG_UNION_EMPTY] THEN ARITH_TAC;
      DISJ1_TAC THEN MATCH_MP_TAC TC_mlt1_UNION2_I THEN
      ASM_REWRITE_TAC[FINITE_varb]]]);;

let walkstar_th2 = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !t t1 t2. walk s t = Pair t1 t2 ==> walkstarR s t2 t`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[walk_walk_thm; term_term_distinct; term_term_11] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LUNIFAUX_walkstarR_Var THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_vR) THEN
    ASM_REWRITE_TAC[term_vars_def; IN_UNION; term_term_distinct];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[walkstarR_def; inv_image_THM; LEX_THM; varb_def;
                measure_THM; pair_count_def] THEN
    ASM_CASES_TAC `varb (a0:A term_term) = EMPTY_BAG` THENL
     [ASM_REWRITE_TAC[BAG_UNION_EMPTY] THEN ARITH_TAC;
      DISJ1_TAC THEN MATCH_MP_TAC TC_mlt1_UNION1_I THEN
      ASM_REWRITE_TAC[FINITE_varb]]]);;

(* ------------------------------------------------------------------------- *)
(* walkstar.                                                                 *)
(* ------------------------------------------------------------------------- *)

let LUNIFAUX_walkstar_exists_s = prove
 (CASE_TERM `!s:(num,A term_term)fmap. wfs s ==> ?g.
     !t. g t =
     (match walk s t with Pair t1 t2 -> Pair (g t1) (g t2) | w -> w)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC (CASE_TERM
      `\(g:A term_term->A term_term) (t:A term_term).
         match walk (s:(num,A term_term)fmap) t with
           Pair t1 t2 -> Pair (g t1) (g t2) | w -> w`)
    (MATCH_MP WF_REC (MATCH_MP walkstar_thWF
       (ASSUME `wfs (s:(num,A term_term)fmap)`)))) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC
    [`f:A term_term->A term_term`; `g:A term_term->A term_term`;
     `x:A term_term`] THEN
  DISCH_TAC THEN CASES_ON `walk (s:(num,A term_term)fmap) x` THEN
  REWRITE_TAC[term_term_CASE; term_term_11] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[walkstar_th1; walkstar_th2]);;

let walkstar_def = new_specification ["walkstar"]
 (prove
   (CASE_TERM `?walkstar. !(s:(num,A term_term)fmap) t. wfs s ==>
      walkstar s t =
      (match walk s t with
         Pair t1 t2 -> Pair (walkstar s t1) (walkstar s t2) | w -> w)`,
    MP_TAC(REWRITE_RULE[GSYM RIGHT_EXISTS_IMP_THM; SKOLEM_THM]
             LUNIFAUX_walkstar_exists_s) THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]));;

let walkstar_ind = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !P. (!t. (!t1 t2. walk s t = Pair t1 t2 ==> P t1) /\
              (!t1 t2. walk s t = Pair t1 t2 ==> P t2) ==> P t)
         ==> !t. P t`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `P:A term_term->bool` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `P:A term_term->bool` o REWRITE_RULE[WF_IND] o
              MATCH_MP walkstar_thWF) THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `t:A term_term` THEN
  DISCH_THEN(fun ih -> FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC ih) THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[walkstar_th1; walkstar_th2]);;

let walkstar_thm = prove
 (CASE_TERM `!(s:(num,A term_term)fmap) v t1 t2 c. wfs s ==>
     walkstar s (term_Var v) =
       (match vwalk s v with
          Pair t1 t2 -> Pair (walkstar s t1) (walkstar s t2) | t' -> t') /\
     walkstar s (Pair t1 t2) = Pair (walkstar s t1) (walkstar s t2) /\
     walkstar s (Const c) = Const c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP walkstar_def th]) THEN
  REWRITE_TAC[walk_walk_thm; term_term_CASE]);;

let walkstar_FEMPTY = prove
 (`!t:A term_term. walkstar FEMPTY t = t`,
  MATCH_MP_TAC term_term_INDUCT THEN
  ASM_SIMP_TAC[walkstar_thm; wfs_FEMPTY; walk_FEMPTY; term_term_CASE]);;

let NOT_FDOM_walkstar = prove
 (`!(s:(num,A term_term)fmap) v.
     wfs s ==> !t. ~(v IN FDOM s) ==> v IN term_vars t ==> v IN term_vars (walkstar s t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN
  ASM_SIMP_TAC[walkstar_thm; term_vars_def; IN_SING; IN_UNION; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[NOT_FDOM_vwalk; term_term_CASE; term_vars_def; IN_SING]);;

let vwalk_EQ_var_vR = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !u v1 v2. vwalk s u = term_Var v1 /\ TC (subst_vR s) v2 u /\ ~(v2 IN FDOM s)
               ==> v1 = v2`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `u:num` THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`v1:num`; `v2:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?y. subst_vR (s:(num,A term_term)fmap) y u` MP_TAC THENL
   [ASM_MESON_TAC[TC_CASES_L]; ALL_TAC] THEN
  REWRITE_TAC[subst_vR_def] THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) u` THEN REWRITE_TAC[option_CASE] THEN
  UNDISCH_TAC `vwalk (s:(num,A term_term)fmap) u = term_Var v1` THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MATCH_MP vwalk_def th]) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  CASES_ON `a:A term_term` THEN
  REWRITE_TAC[term_term_CASE; term_term_distinct; term_vars_def; IN_SING;
              NOT_IN_EMPTY] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `TC (subst_vR (s:(num,A term_term)fmap)) v2 u` THEN
  ONCE_REWRITE_TAC[TC_CASES_L] THEN
  ASM_REWRITE_TAC[subst_vR_def; option_CASE; term_vars_def; IN_SING;
                  LUNIFAUX_EXISTS_EQ_R] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `vwalk (s:(num,A term_term)fmap) a' = term_Var v1` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[NOT_FDOM_vwalk; term_term_11] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `a':num`) THEN REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LUNIFAUX_vwalk_FLOOKUP = prove
 (`!(s:(num,A term_term)fmap) v. wfs s ==>
     (FLOOKUP s v = NONE ==> vwalk s v = term_Var v) /\
     (!u. FLOOKUP s v = SOME (term_Var u) ==> vwalk s v = vwalk s u) /\
     (!t1 t2. FLOOKUP s v = SOME (Pair t1 t2) ==> vwalk s v = Pair t1 t2) /\
     (!c. FLOOKUP s v = SOME (Const c) ==> vwalk s v = Const c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`] vwalk_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; term_term_CASE]);;

let LUNIFAUX_vR_CASES = prove
 (`!(s:(num,A term_term)fmap) y u.
     wfs s /\ subst_vR s y u
     ==> (FLOOKUP s u = SOME (term_Var y) /\ vwalk s u = vwalk s y) \/
         (?t1 t2. FLOOKUP s u = SOME (Pair t1 t2) /\ vwalk s u = Pair t1 t2 /\
                  (y IN term_vars t1 \/ y IN term_vars t2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subst_vR_def] THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) u` THEN
  REWRITE_TAC[option_CASE] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `u:num`] LUNIFAUX_vwalk_FLOOKUP) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASES_ON `a:A term_term` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[term_vars_def; IN_SING; NOT_IN_EMPTY; IN_UNION]) THEN
  ASM_REWRITE_TAC[term_term_distinct; term_term_11; option_INJ] THEN
  ASM_MESON_TAC[]);;

let vwalk_EQ_const_vR = prove
 (`!(s:(num,A term_term)fmap) v u.
     TC (subst_vR s) v u ==> ~(v IN FDOM s) /\ wfs s ==> !c. ~(vwalk s u = Const c)`,
  GEN_TAC THEN MATCH_MP_TAC TC_INDUCT_L THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LUNIFAUX_vR_CASES o
    CONJ (ASSUME `wfs (s:(num,A term_term)fmap)`)) THENL
   [STRIP_TAC THEN UNDISCH_TAC `vwalk (s:(num,A term_term)fmap) u = Const c` THEN
    ASM_SIMP_TAC[NOT_FDOM_vwalk; term_term_distinct];
    STRIP_TAC THEN UNDISCH_TAC `vwalk (s:(num,A term_term)fmap) z = Const c` THEN
    ASM_SIMP_TAC[term_term_distinct]]);;

let vwalk_EQ_pair_vR = prove
 (`!(s:(num,A term_term)fmap) v u.
     TC (subst_vR s) v u ==>
     !t1 t2. ~(v IN FDOM s) /\ wfs s /\ vwalk s u = Pair t1 t2
             ==> ?u. (u IN term_vars t1 \/ u IN term_vars t2) /\ RTC (subst_vR s) v u`,
  GEN_TAC THEN MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LUNIFAUX_vR_CASES o
    CONJ (ASSUME `wfs (s:(num,A term_term)fmap)`)) THEN STRIP_TAC THENL
   [UNDISCH_TAC `vwalk (s:(num,A term_term)fmap) y = Pair t1 t2` THEN
    ASM_SIMP_TAC[NOT_FDOM_vwalk; term_term_distinct];
    SUBGOAL_THEN `t1':A term_term = t1 /\ t2':A term_term = t2`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_term_11]; ALL_TAC] THEN
    ASM_MESON_TAC[RTC_REFL];
    SUBGOAL_THEN `t1':A term_term = t1 /\ t2':A term_term = t2`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_term_11]; ALL_TAC] THEN
    ASM_MESON_TAC[RTC_REFL];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `t1':A term_term = t1 /\ t2':A term_term = t2`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_term_11]; ALL_TAC] THEN
    ASM_MESON_TAC[RTC_INC_TC];
    SUBGOAL_THEN `t1':A term_term = t1 /\ t2':A term_term = t2`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_term_11]; ALL_TAC] THEN
    ASM_MESON_TAC[RTC_INC_TC]]);;

let TC_vR_vars_walkstar = prove
 (`!(s:(num,A term_term)fmap) u t v.
     wfs s /\ u IN term_vars t /\ TC (subst_vR s) v u /\ ~(v IN FDOM s)
     ==> v IN term_vars (walkstar s t)`,
  SUBGOAL_THEN
   `!s:(num,A term_term)fmap. wfs s ==>
     !t v u. TC (subst_vR s) v u /\ ~(v IN FDOM s) /\ u IN term_vars t
             ==> v IN term_vars (walkstar s t)`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP walkstar_ind) THEN
  X_GEN_TAC `t:A term_term` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`v:num`; `u:num`] THEN STRIP_TAC THEN
  UNDISCH_TAC `u IN term_vars (t:A term_term)` THEN
  CASES_ON `t:A term_term` THEN
  ASM_SIMP_TAC[walkstar_thm; term_vars_def; IN_SING; IN_UNION; NOT_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[walk_walk_thm; term_term_11]) THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    CASES_ON `vwalk (s:(num,A term_term)fmap) a` THEN
    REWRITE_TAC[term_term_CASE; term_vars_def; IN_SING; IN_UNION] THENL
     [CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_EQ_var_vR) THEN
      EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`; `a:num`]
                   vwalk_EQ_pair_vR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`]) THEN
      ASM_REWRITE_TAC[RTC; RC_EXPLICIT] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[NOT_FDOM_walkstar];
      MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`; `a:num`]
                   vwalk_EQ_const_vR) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ASM_MESON_TAC[]]);;

let walkstar_SUBMAP = prove
 (`!(s:(num,A term_term)fmap) sx t.
     s SUBMAP sx /\ wfs sx ==> walkstar sx t = walkstar sx (walkstar s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_SUBMAP]; ALL_TAC] THEN
  SPEC_TAC(`t:A term_term`,`t:A term_term`) THEN
  MATCH_MP_TAC(MATCH_MP walkstar_ind (ASSUME `wfs (s:(num,A term_term)fmap)`)) THEN
  X_GEN_TAC `t:A term_term` THEN STRIP_TAC THEN
  CASES_ON `t:A term_term` THEN ASM_SIMP_TAC[walkstar_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[walk_walk_thm; term_term_11]) THENL
   [MP_TAC(SPECL [`a:num`; `s:(num,A term_term)fmap`]
      (MATCH_MP vwalk_SUBMAP (ASSUME `wfs (sx:(num,A term_term)fmap)`))) THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `vwalk (s:(num,A term_term)fmap) a` THEN
    ASM_SIMP_TAC[term_term_CASE; walkstar_thm; term_term_11] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let walkstar_idempotent = prove
 (`!s:(num,A term_term)fmap.
     wfs s ==> !t. walkstar s t = walkstar s (walkstar s t)`,
  MESON_TAC[walkstar_SUBMAP; SUBMAP_REFL]);;

let walkstar_subterm_idem = prove
 (`!(s:(num,A term_term)fmap) t1 t1a t1d.
     walkstar s t1 = Pair t1a t1d /\ wfs s
     ==> walkstar s t1a = t1a /\ walkstar s t1d = t1d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t1:A term_term` o MATCH_MP walkstar_idempotent) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP walkstar_thm th]) THEN
  REWRITE_TAC[term_term_11] THEN MESON_TAC[]);;

let walkstar_walk = prove
 (`!(s:(num,A term_term)fmap) t.
     wfs s ==> walkstar s (walk s t) = walkstar s t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `t:A term_term` THEN ASM_SIMP_TAC[walk_walk_thm; walkstar_thm] THEN
  CASES_ON `vwalk (s:(num,A term_term)fmap) a` THEN
  ASM_SIMP_TAC[walkstar_thm; term_term_CASE] THEN
  SUBGOAL_THEN `vwalk (s:(num,A term_term)fmap) a' = term_Var a'`
    (fun th -> REWRITE_TAC[th; term_term_CASE]) THEN
  ASM_MESON_TAC[vwalk_to_var; NOT_FDOM_vwalk]);;

let walkstar_to_var = prove
 (`!(s:(num,A term_term)fmap) t v.
     walkstar s t = term_Var v /\ wfs s ==> ~(v IN FDOM s) /\ ?u. t = term_Var u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `walkstar (s:(num,A term_term)fmap) t = term_Var v` THEN
  CASES_ON `t:A term_term` THEN
  ASM_SIMP_TAC[walkstar_thm; term_term_distinct; term_term_11] THEN
  CASES_ON `vwalk (s:(num,A term_term)fmap) a` THEN
  REWRITE_TAC[term_term_CASE; term_term_distinct; term_term_11] THEN
  ASM_MESON_TAC[vwalk_to_var]);;

(* ------------------------------------------------------------------------- *)
(* The direct version of walkstar that does the walk itself.                 *)
(* ------------------------------------------------------------------------- *)

let apply_ts_thm = prove
 (CASE_TERM `!(s:(num,A term_term)fmap) v t1 t2 c. wfs s ==>
     walkstar s (term_Var v) =
       (match FLOOKUP s v with NONE -> term_Var v | SOME t -> walkstar s t) /\
     walkstar s (Pair t1 t2) = Pair (walkstar s t1) (walkstar s t2) /\
     walkstar s (Const c) = Const c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[walkstar_thm] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`] vwalk_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_CASE; term_term_CASE] THEN
  CASES_ON `a:A term_term` THEN
  ASM_SIMP_TAC[term_term_CASE; walkstar_thm]);;

let apply_ts_ind = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !P. (!v. (!t. FLOOKUP s v = SOME t ==> P t) ==> P (term_Var v)) /\
         (!t1 t2. P t1 /\ P t2 ==> P (Pair t1 t2)) /\ (!c. P (Const c))
         ==> !v. P v`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "var")
    (CONJUNCTS_THEN2 (LABEL_TAC "pair") (LABEL_TAC "const"))) THEN
  SUBGOAL_THEN
   `!n. (!t1 t2. vwalk (s:(num,A term_term)fmap) n = Pair t1 t2
                 ==> P t1 /\ P t2) ==> P (term_Var n)`
   (LABEL_TAC "vlem") THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
    DISCH_THEN(LABEL_TAC "prem") THEN
    USE_THEN "var" MATCH_MP_TAC THEN X_GEN_TAC `t:A term_term` THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`s:(num,A term_term)fmap`; `n:num`] LUNIFAUX_vwalk_FLOOKUP) THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `t:A term_term` THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; term_term_distinct; term_term_11] THENL
     [DISCH_THEN(MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "ih" (MP_TAC o SPEC `a:num`) THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME
        `FLOOKUP (s:(num,A term_term)fmap) n = SOME (term_Var a)`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "prem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`]) THEN
      REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "pair" MATCH_MP_TAC THEN
      USE_THEN "prem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN USE_THEN "const" MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP walkstar_ind) THEN
  X_GEN_TAC `t:A term_term` THEN STRIP_TAC THEN
  CASES_ON `t:A term_term` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[walk_walk_thm; term_term_11]) THENL
   [USE_THEN "vlem" MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`t1:A term_term`; `t2:A term_term`] THEN
    DISCH_TAC THEN ASM_MESON_TAC[];
    USE_THEN "pair" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    USE_THEN "const" MATCH_ACCEPT_TAC]);;

let vars_walkstar = prove
 (`!s:(num,A term_term)fmap. wfs s ==>
     !t. term_vars (walkstar s t) SUBSET term_vars t UNION UNIONS (FRANGE (term_vars o_f s))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP apply_ts_ind) THEN
  ASM_SIMP_TAC[apply_ts_thm; term_vars_def] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
    REWRITE_TAC[option_CASE; term_vars_def] THENL
     [SET_TAC[];
      SUBGOAL_THEN
        `term_vars (a:A term_term) IN FRANGE (term_vars o_f (s:(num,A term_term)fmap))`
        MP_TAC THENL
       [MATCH_MP_TAC o_f_FRANGE THEN REWRITE_TAC[FRANGE_FLOOKUP] THEN
        ASM_MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `a:A term_term`) THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[]]];
    SET_TAC[];
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The occurs check, proved equivalent to term_vars o walkstar.              *)
(* ------------------------------------------------------------------------- *)

let walkstar_oc_rules,walkstar_oc_ind,walkstar_oc_cases,walkstar_oc_strong_ind = cake_inductive
  `(!t v. v IN term_vars t /\ ~(v IN FDOM (s:(num,A term_term)fmap)) ==> walkstar_oc s t v) /\
   (!t v u t'. u IN term_vars t /\ vwalk s u = t' /\ walkstar_oc s t' v ==> walkstar_oc s t v)`;;

let LUNIFAUX_oc_pair = prove
 (`!(s:(num,A term_term)fmap) t1 t2 v.
     walkstar_oc s (Pair t1 t2) v <=> walkstar_oc s t1 v \/ walkstar_oc s t2 v`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [walkstar_oc_cases] THEN
    REWRITE_TAC[term_vars_def; IN_UNION] THEN MESON_TAC[walkstar_oc_rules];
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o ONCE_REWRITE_RULE[walkstar_oc_cases])) THEN
    MESON_TAC[walkstar_oc_rules; term_vars_def; IN_UNION]]);;

let LUNIFAUX_oc_const = prove
 (`!(s:(num,A term_term)fmap) c v. ~walkstar_oc s (Const c) v`,
  ONCE_REWRITE_TAC[walkstar_oc_cases] THEN REWRITE_TAC[term_vars_def; NOT_IN_EMPTY]);;

let LUNIFAUX_oc_var1 = prove
 (CASE_TERM `!s:(num,A term_term)fmap. wfs s ==>
     !t v. walkstar_oc s t v ==>
           !u. t = term_Var u ==>
               (match vwalk s u with
                  term_Var w -> v = w
                | Pair t1 t2 -> walkstar_oc s t1 v \/ walkstar_oc s t2 v
                | _ -> F)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC walkstar_oc_strong_ind THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[term_vars_def; IN_SING]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[NOT_FDOM_vwalk; term_term_CASE];
    MAP_EVERY X_GEN_TAC [`t:A term_term`; `v:num`; `u':num`; `t':A term_term`] THEN
    STRIP_TAC THEN X_GEN_TAC `u:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[term_vars_def; IN_SING]) THEN
    UNDISCH_TAC `u':num = u` THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `vwalk (s:(num,A term_term)fmap) u = t'` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    CASES_ON `vwalk (s:(num,A term_term)fmap) u` THEN
    ASM_REWRITE_TAC[term_term_CASE] THENL
     [SUBGOAL_THEN `vwalk (s:(num,A term_term)fmap) a = term_Var a`
        ASSUME_TAC THENL
       [ASM_MESON_TAC[vwalk_to_var; NOT_FDOM_vwalk]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN
      ASM_REWRITE_TAC[term_term_CASE];
      ASM_MESON_TAC[LUNIFAUX_oc_pair];
      ASM_MESON_TAC[LUNIFAUX_oc_const]]]);;

let LUNIFAUX_oc_var2 = prove
 (CASE_TERM `!s:(num,A term_term)fmap. wfs s ==>
     !v x. (match vwalk s v with
              term_Var u -> x = u
            | Pair t1 t2 -> walkstar_oc s t1 x \/ walkstar_oc s t2 x
            | _ -> F) ==> walkstar_oc s (term_Var v) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC `s:(num,A term_term)fmap` walkstar_oc_rules) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "r2")) THEN
  CASES_ON `vwalk (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[term_term_CASE] THEN DISCH_TAC THEN
  USE_THEN "r2" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:num`; `vwalk (s:(num,A term_term)fmap) v`] THEN
  ASM_REWRITE_TAC[term_vars_def; IN_SING; LUNIFAUX_oc_pair] THEN
  USE_THEN "r1" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[term_vars_def; IN_SING] THEN ASM_MESON_TAC[vwalk_to_var]);;

let oc_thm = prove
 (CASE_TERM `!(s:(num,A term_term)fmap) v x t1 t2 c.
     (wfs s ==>
      (walkstar_oc s (term_Var v) x <=>
       match vwalk s v with
         term_Var u -> x = u
       | Pair t1 t2 -> walkstar_oc s t1 x \/ walkstar_oc s t2 x
       | _ -> F)) /\
     (walkstar_oc s (Pair t1 t2) v <=> walkstar_oc s t1 v \/ walkstar_oc s t2 v) /\
     ~walkstar_oc s (Const c) v`,
  REWRITE_TAC[LUNIFAUX_oc_pair; LUNIFAUX_oc_const] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MP_TAC(SPEC `s:(num,A term_term)fmap` LUNIFAUX_oc_var1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`term_Var v:A term_term`; `x:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:num`) THEN
    REWRITE_TAC[];
    ASM_MESON_TAC[LUNIFAUX_oc_var2]]);;

let oc_walking = prove
 (CASE_TERM `!(s:(num,A term_term)fmap) t v. wfs s ==>
     (walkstar_oc s t v <=>
      match walk s t with
        term_Var u -> v = u
      | Pair t1 t2 -> walkstar_oc s t1 v \/ walkstar_oc s t2 v
      | _ -> F)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASES_ON `t:A term_term` THEN
  ASM_SIMP_TAC[walk_walk_thm; oc_thm; term_term_CASE]);;

let oc_NOTIN_FDOM = prove
 (`!s:(num,A term_term)fmap. wfs s ==> !t v. walkstar_oc s t v ==> ~(v IN FDOM s)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC walkstar_oc_ind THEN MESON_TAC[]);;

let oc_eq_vars_walkstar = prove
 (`!(s:(num,A term_term)fmap) t v.
     wfs s ==> (walkstar_oc s t v <=> v IN term_vars (walkstar s t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`v:num`,`v:num`) THEN
  SPEC_TAC(`t:A term_term`,`t:A term_term`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP walkstar_ind) THEN
  X_GEN_TAC `t:A term_term` THEN STRIP_TAC THEN X_GEN_TAC `v:num` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP oc_walking th]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
    [MATCH_MP walkstar_def th]) THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t` THEN
  REWRITE_TAC[term_term_CASE; term_vars_def; IN_SING; IN_UNION; NOT_IN_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`]) THEN
  REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let _ = cake_add_simps [walkstar_thm; walkstar_FEMPTY; oc_thm];;
