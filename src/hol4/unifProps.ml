(* ========================================================================= *)
(* unifProps: port of HOL4 examples/algorithms/unification/triangular/      *)
(* first-order/unifPropsScript.sml (HOL4 library used by CakeML v3479): the *)
(* properties of unify: it computes a most general unifier (unify_unifier,  *)
(* unify_mgu), and it succeeds whenever a unifier exists (eqs_unify).       *)
(*                                                                           *)
(* Notes: HOL4 walk-star is walkstar; HOL4's infix COMPAT is an infix here. *)
(* Helper lemmas (HOL4 val bindings that are not stored theorems) are      *)
(* LUNIFAUX_.                                                                *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/unifDef.ml";;

type_invention_error := true;;

let LUNIFAUX_vR_SUBMAP = prove
 (`!(s:(num,A term_term)fmap) sx u v.
     s SUBMAP sx ==> vR s u v ==> vR sx u v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[vR_def] THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `FLOOKUP (sx:(num,A term_term)fmap) v = SOME a`
    (fun th -> REWRITE_TAC[th; option_CASE]) THEN
  ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let TC_vR_SUBMAP = prove
 (`!(s:(num,A term_term)fmap) sx.
     s SUBMAP sx ==> !u v. TC (vR s) u v ==> TC (vR sx) u v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TC_MONO THEN
  ASM_MESON_TAC[LUNIFAUX_vR_SUBMAP]);;

let vwalk_irrelevant_FUPDATE = prove
 (`!(s:(num,A term_term)fmap) vx tx.
     wfs (s |+ (vx,tx)) /\ ~(vx IN FDOM s) ==>
     !v. ~RTC (vR s) vx v ==> vwalk (s |+ (vx,tx)) v = vwalk s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_SUBMAP; SUBMAP_FUPDATE_EQN]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(vx:num = v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP ((s:(num,A term_term)fmap) |+ (vx,tx)) v = FLOOKUP s v`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_UPDATE]; ALL_TAC] THEN
  MP_TAC(SPECL [`(s:(num,A term_term)fmap) |+ (vx,tx)`; `v:num`]
               LUNIFAUX_vwalk_FLOOKUP) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`] LUNIFAUX_vwalk_FLOOKUP) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:A term_term` THEN
  REWRITE_TAC[term_term_distinct; term_term_11; FORALL_UNWIND_THM1] THENL
   [ALL_TAC; MESON_TAC[]; MESON_TAC[]] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a':num`) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~RTC (vR (s:(num,A term_term)fmap)) vx v` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `a':num` THEN
  ASM_REWRITE_TAC[vR_def; option_CASE; term_vars_def; IN_SING]);;

let vwalk_FUPDATE_var = prove
 (`!(s:(num,A term_term)fmap) v1 v2.
     wfs (s |+ (v1,term_Var v2)) /\ ~(v1 IN FDOM s)
     ==> vwalk (s |+ (v1,term_Var v2)) v2 = vwalk s v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v1:num`; `term_Var v2:A term_term`]
               vwalk_irrelevant_FUPDATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `vR ((s:(num,A term_term)fmap) |+ (v1,term_Var v2)) v2 v1`
    ASSUME_TAC THENL
   [REWRITE_TAC[vR_def; FLOOKUP_UPDATE; option_CASE; term_vars_def; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:(num,A term_term)fmap) SUBMAP (s |+ (v1,term_Var v2))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN]; ALL_TAC] THEN
  REWRITE_TAC[RTC; RC_EXPLICIT; DE_MORGAN_THM] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `TC (vR ((s:(num,A term_term)fmap) |+ (v1,term_Var v2))) v1 v1`
      MP_TAC THENL
     [MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC `v2:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[TC_vR_SUBMAP];
      ASM_MESON_TAC[wfs_no_cycles]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[wfs_no_cycles; TC_INC]]);;

let walkstar_extend = prove
 (`!(s1:(num,A term_term)fmap) s vx tx.
     wfs s1 /\ wfs (s |+ (vx,tx)) /\ ~(vx IN FDOM s) /\
     walkstar s1 (term_Var vx) = walkstar s1 (walkstar s tx)
     ==> !t. walkstar s1 (walkstar (s |+ (vx,tx)) t) = walkstar s1 (walkstar s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:(num,A term_term)fmap) SUBMAP (s |+ (vx,tx))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN]; ALL_TAC] THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_SUBMAP]; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP walkstar_ind
    (ASSUME `wfs ((s:(num,A term_term)fmap) |+ (vx,tx))`)) THEN
  X_GEN_TAC `t:A term_term` THEN STRIP_TAC THEN
  CASES_ON `t:A term_term` THEN ASM_SIMP_TAC[walkstar_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[walk_walk_thm; term_term_11]) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  MP_TAC(SPECL [`a:num`; `s:(num,A term_term)fmap`] (MATCH_MP vwalk_SUBMAP
    (ASSUME `wfs ((s:(num,A term_term)fmap) |+ (vx,tx))`))) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `vwalk (s:(num,A term_term)fmap) a` THEN
  REWRITE_TAC[term_term_CASE] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[term_term_CASE] THENL
   [ALL_TAC; ASM_SIMP_TAC[walkstar_thm; term_term_11] THEN ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `a':num = vx` THENL
   [ALL_TAC;
    SUBGOAL_THEN `vwalk ((s:(num,A term_term)fmap) |+ (vx,tx)) a' = term_Var a'`
      SUBST1_TAC THENL
     [MATCH_MP_TAC NOT_FDOM_vwalk THEN ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN
      ASM_MESON_TAC[vwalk_to_var];
      REWRITE_TAC[term_term_CASE]]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`(s:(num,A term_term)fmap) |+ (vx,tx)`; `vx:num`]
               LUNIFAUX_vwalk_FLOOKUP) THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
  CASES_ON `tx:A term_term` THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; term_term_distinct; term_term_11;
              FORALL_UNWIND_THM1] THENL
   [DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
      `vwalk ((s:(num,A term_term)fmap) |+ (vx,term_Var a'')) a'' = vwalk s a''`
      ASSUME_TAC THENL
     [MATCH_MP_TAC vwalk_FUPDATE_var THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `vwalk ((s:(num,A term_term)fmap) |+ (vx,term_Var a'')) a = vwalk s a''`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`(s:(num,A term_term)fmap) |+ (vx,term_Var a'')`; `vx:num`]
                   LUNIFAUX_vwalk_FLOOKUP) THEN
      ASM_REWRITE_TAC[FLOOKUP_UPDATE; option_INJ; option_DISTINCT;
                      term_term_distinct; term_term_11; FORALL_UNWIND_THM1];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[walkstar_thm] THEN
    CASES_ON `vwalk (s:(num,A term_term)fmap) a''` THEN
    ASM_SIMP_TAC[term_term_CASE; walkstar_thm; term_term_11] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[term_term_CASE] THEN
    ASM_SIMP_TAC[walkstar_thm; term_term_11] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[term_term_CASE; walkstar_thm]]);;

let LUNIFAUX_unify_same = prove
 (`!(s:(num,A term_term)fmap) t1 t2. wfs s /\ t1 = t2 ==> unify s t1 t2 = SOME s`,
  MATCH_MP_TAC unify_ind THEN
  MAP_EVERY X_GEN_TAC [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t2:A term_term`; `t2:A term_term`]
               unify_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE] THEN
  USE_THEN "ih2" (fun th -> MP_TAC(REWRITE_RULE
    [ASSUME `wfs (s:(num,A term_term)fmap)`]
    (SPECL [`a0:A term_term`; `a1:A term_term`; `a0:A term_term`;
            `a1:A term_term`] th))) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPTION_BIND_DEF] THEN
  USE_THEN "ih1" (fun th -> MP_TAC(REWRITE_RULE
    [ASSUME `wfs (s:(num,A term_term)fmap)`]
    (SPECL [`a0:A term_term`; `a1:A term_term`; `a0:A term_term`;
            `a1:A term_term`; `s:(num,A term_term)fmap`] th))) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  USE_THEN "ih2" (fun th -> MP_TAC(REWRITE_RULE
    [ASSUME `wfs (s:(num,A term_term)fmap)`]
    (SPECL [`a0:A term_term`; `a1:A term_term`; `a0:A term_term`;
            `a1:A term_term`] th))) THEN
  REWRITE_TAC[]);;

let unify_same = prove
 (`!s:(num,A term_term)fmap. wfs s ==> !t. unify s t t = SOME s`,
  MESON_TAC[LUNIFAUX_unify_same]);;

let wex = prove
 (`!(s1:(num,A term_term)fmap) s vx tx.
     wfs s1 /\ wfs (s |+ (vx,tx)) /\
     walkstar s1 (walkstar s (term_Var vx)) = walkstar s1 (walkstar s tx) /\
     ~(vx IN FDOM s)
     ==> !t. walkstar s1 (walkstar (s |+ (vx,tx)) t) =
             walkstar s1 (walkstar s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC walkstar_extend THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_SUBMAP; SUBMAP_FUPDATE_EQN]; ALL_TAC] THEN
  UNDISCH_TAC `walkstar s1 (walkstar s (term_Var vx)) =
               walkstar (s1:(num,A term_term)fmap) (walkstar s tx)` THEN
  ASM_SIMP_TAC[walkstar_thm; NOT_FDOM_vwalk; term_term_CASE]);;

let LUNIFAUX_wex_tac =
  MATCH_MP_TAC wex THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP walk_to_var
    (CONJ (ASSUME `wfs (s:(num,A term_term)fmap)`) th)) THEN
    SIMP_TAC[] THEN NO_TAC);;

let LUNIFAUX_mgu_ext_tac =
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_TAC THEN LUNIFAUX_wex_tac;;

let unify_mgu = prove
 (`!(s:(num,A term_term)fmap) t1 t2 sx s2.
     wfs s /\ unify s t1 t2 = SOME sx /\ wfs s2 /\
     walkstar s2 (walkstar s t1) = walkstar s2 (walkstar s t2)
     ==> !t. walkstar s2 (walkstar sx t) = walkstar s2 (walkstar s t)`,
  MATCH_MP_TAC unify_ind THEN
  MAP_EVERY X_GEN_TAC [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  MAP_EVERY X_GEN_TAC [`sx:(num,A term_term)fmap`; `s2:(num,A term_term)fmap`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wfs (sx:(num,A term_term)fmap)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                  `sx:(num,A term_term)fmap`] unify_uP) THEN
    ASM_REWRITE_TAC[uP_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `walkstar s2 (walkstar s (walk s t1)) =
                walkstar (s2:(num,A term_term)fmap) (walkstar s (walk s t2))`
    MP_TAC THENL
   [REWRITE_TAC[MATCH_MP walkstar_walk (ASSUME `wfs (s:(num,A term_term)fmap)`)] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `unify (s:(num,A term_term)fmap) t1 t2 = SOME sx` THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`]
               unify_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE; ext_s_check_def; option_DISTINCT] THENL
   [REWRITE_TAC[option_INJ] THEN COND_CASES_TAC THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_TAC THENL
    [REWRITE_TAC[];
     LUNIFAUX_wex_tac];
    LUNIFAUX_mgu_ext_tac;
    LUNIFAUX_mgu_ext_tac;
    LUNIFAUX_mgu_ext_tac;
    CASES_ON `unify (s:(num,A term_term)fmap) a0 a0'` THEN
    REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT] THEN
    DISCH_TAC THEN
    REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s:(num,A term_term)fmap)`)] THEN
    REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s2:(num,A term_term)fmap)`);
                term_term_11] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `wfs (a:(num,A term_term)fmap)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`s:(num,A term_term)fmap`; `a0:A term_term`; `a0':A term_term`;
                    `a:(num,A term_term)fmap`] unify_uP) THEN
      ASM_REWRITE_TAC[uP_def] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!t. walkstar s2 (walkstar a t) =
                      walkstar (s2:(num,A term_term)fmap) (walkstar s t)`
      ASSUME_TAC THENL
     [USE_THEN "ih2" (MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`;
                                      `a0':A term_term`; `a1':A term_term`]) THEN
      REWRITE_TAC[ASSUME `wfs (s:(num,A term_term)fmap)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!t. walkstar s2 (walkstar sx t) =
                      walkstar (s2:(num,A term_term)fmap) (walkstar a t)`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`;
                                    `a0':A term_term`; `a1':A term_term`;
                                    `a:(num,A term_term)fmap`]) THEN
    REWRITE_TAC[ASSUME `wfs (s:(num,A term_term)fmap)`;
                ASSUME `unify (s:(num,A term_term)fmap) a0 a0' = SOME a`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    LUNIFAUX_mgu_ext_tac;
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[]]);;

let unify_mgu_FEMPTY = prove
 (`!(t1:A term_term) t2 sx.
     unify FEMPTY t1 t2 = SOME sx
     ==> !s. wfs s /\ walkstar s t1 = walkstar s t2
             ==> ?s'. !t. walkstar s' (walkstar sx t) = walkstar s t`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `s:(num,A term_term)fmap` THEN
  MP_TAC(SPECL [`FEMPTY:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                `sx:(num,A term_term)fmap`; `s:(num,A term_term)fmap`] unify_mgu) THEN
  ASM_REWRITE_TAC[wfs_FEMPTY; walkstar_FEMPTY]);;

let walkstar_walk_SUBMAP = prove
 (`!(s:(num,A term_term)fmap) sx t.
     s SUBMAP sx /\ wfs sx ==> walkstar sx t = walkstar sx (walk s t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wfs (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_SUBMAP]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`;
                `t:A term_term`] walkstar_SUBMAP) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`;
                `walk (s:(num,A term_term)fmap) t`] walkstar_SUBMAP) THEN
  ASM_SIMP_TAC[walkstar_walk]);;

let LUNIFAUX_walkstar_ext_var = prove
 (`!(s:(num,A term_term)fmap) v t.
     wfs (s |+ (v,t)) ==> walkstar (s |+ (v,t)) (term_Var v) = walkstar (s |+ (v,t)) t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(s:(num,A term_term)fmap) |+ (v,t)`; `v:num`; `t:A term_term`;
                `t:A term_term`; `ARB:A`] apply_ts_thm) THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; option_CASE] THEN SIMP_TAC[]);;

let LUNIFAUX_unifier_ext_tac sym =
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  (if sym then CONV_TAC SYM_CONV else ALL_TAC) THEN
  MATCH_MP_TAC LUNIFAUX_walkstar_ext_var THEN FIRST_ASSUM ACCEPT_TAC;;

let unify_unifier = prove
 (`!(s:(num,A term_term)fmap) t1 t2 sx.
     wfs s /\ unify s t1 t2 = SOME sx
     ==> wfs sx /\ s SUBMAP sx /\ walkstar sx t1 = walkstar sx t2`,
  MATCH_MP_TAC unify_ind THEN
  MAP_EVERY X_GEN_TAC [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  X_GEN_TAC `sx:(num,A term_term)fmap` THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfs (sx:(num,A term_term)fmap) /\ s SUBMAP sx` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                  `sx:(num,A term_term)fmap`] unify_uP) THEN
    ASM_REWRITE_TAC[uP_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`; `t1:A term_term`]
               walkstar_walk_SUBMAP) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`; `t2:A term_term`]
               walkstar_walk_SUBMAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `unify (s:(num,A term_term)fmap) t1 t2 = SOME sx` THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`]
               unify_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE; ext_s_check_def; option_DISTINCT] THENL
   [REWRITE_TAC[option_INJ] THEN COND_CASES_TAC THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC LUNIFAUX_walkstar_ext_var THEN FIRST_ASSUM ACCEPT_TAC;
    LUNIFAUX_unifier_ext_tac false;
    LUNIFAUX_unifier_ext_tac false;
    LUNIFAUX_unifier_ext_tac true;
    CASES_ON `unify (s:(num,A term_term)fmap) a0 a0'` THEN
   REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT] THEN DISCH_TAC THEN
   USE_THEN "ih2" (MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`;
                                   `a0':A term_term`; `a1':A term_term`]) THEN
   REWRITE_TAC[ASSUME `wfs (s:(num,A term_term)fmap)`] THEN
   DISCH_THEN(MP_TAC o SPEC `a:(num,A term_term)fmap`) THEN
   REWRITE_TAC[ASSUME `unify (s:(num,A term_term)fmap) a0 a0' = SOME a`] THEN
   STRIP_TAC THEN
   USE_THEN "ih1" (MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`;
                                   `a0':A term_term`; `a1':A term_term`;
                                   `a:(num,A term_term)fmap`]) THEN
   REWRITE_TAC[ASSUME `wfs (s:(num,A term_term)fmap)`;
               ASSUME `unify (s:(num,A term_term)fmap) a0 a0' = SOME a`;
               ASSUME `wfs (a:(num,A term_term)fmap)`] THEN
   DISCH_THEN(MP_TAC o SPEC `sx:(num,A term_term)fmap`) THEN
   REWRITE_TAC[ASSUME `unify (a:(num,A term_term)fmap) a1 a1' = SOME sx`] THEN
   STRIP_TAC THEN
   REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (sx:(num,A term_term)fmap)`);
               term_term_11] THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`a:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`;
                 `a0:A term_term`] walkstar_SUBMAP) THEN
   MP_TAC(SPECL [`a:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`;
                 `a0':A term_term`] walkstar_SUBMAP) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    LUNIFAUX_unifier_ext_tac true;
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

let LUNIFAUX_vars_pc_le = prove
 (`!(s:(num,A term_term)fmap) v t.
     wfs s /\ v IN term_vars t
     ==> pair_count (walkstar s (term_Var v)) <= pair_count (walkstar s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `(v:num) IN term_vars (t:A term_term)` THEN
  SPEC_TAC(`t:A term_term`,`t:A term_term`) THEN
  MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[term_vars_def; IN_SING; IN_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s:(num,A term_term)fmap)`);
              pair_count_def] THEN
  CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let vars_measure = prove
 (`!(s:(num,A term_term)fmap) v t.
     v IN term_vars t /\ (!w. ~(t = term_Var w)) /\ wfs s
     ==> measure (pair_count o walkstar s) (term_Var v) t`,
  REPEAT GEN_TAC THEN CASES_ON `t:A term_term` THEN
  REWRITE_TAC[term_vars_def; NOT_IN_EMPTY; term_term_distinct; term_term_11] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; measure_THM; o_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s:(num,A term_term)fmap)`);
              pair_count_def] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`; `a0:A term_term`]
               LUNIFAUX_vars_pc_le) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`; `a1:A term_term`]
               LUNIFAUX_vars_pc_le) THEN
  ASM_REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s:(num,A term_term)fmap)`)] THEN
  ARITH_TAC);;

let oc_subterm_neq = prove
 (`!(s:(num,A term_term)fmap) t v s2.
     walkstar_oc s t v /\ (!w. ~(t = term_Var w)) /\ wfs s /\ wfs s2
     ==> ~(walkstar s2 (term_Var v) = walkstar s2 (walkstar s t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:num) IN term_vars (walkstar (s:(num,A term_term)fmap) t)`
    ASSUME_TAC THENL [ASM_MESON_TAC[oc_eq_vars_walkstar]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. ~(walkstar (s:(num,A term_term)fmap) t = term_Var w)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `walkstar_oc (s:(num,A term_term)fmap) t v` THEN
    UNDISCH_TAC `!w. ~((t:A term_term) = term_Var w)` THEN
    CASES_ON `t:A term_term` THEN
    REWRITE_TAC[term_term_distinct; term_term_11; LUNIFAUX_oc_const] THEN
    REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s:(num,A term_term)fmap)`);
                term_term_distinct] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s2:(num,A term_term)fmap`; `v:num`;
                `walkstar (s:(num,A term_term)fmap) t`] vars_measure) THEN
  ASM_REWRITE_TAC[measure_THM; o_THM] THEN MESON_TAC[LT_REFL]);;

let LUNIFAUX_walkstar_NOT_FDOM_var = prove
 (`!(s:(num,A term_term)fmap) v.
     wfs s /\ ~(v IN FDOM s) ==> walkstar s (term_Var v) = term_Var v`,
  SIMP_TAC[walkstar_thm; NOT_FDOM_vwalk; term_term_CASE]);;

let LUNIFAUX_wsthm_tac =
  REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s:(num,A term_term)fmap)`)] THEN
  REWRITE_TAC[MATCH_MP walkstar_thm (ASSUME `wfs (s2:(num,A term_term)fmap)`)];;

let LUNIFAUX_eqs_var_tac =
  SUBGOAL_THEN `walkstar (s:(num,A term_term)fmap) (term_Var a) = term_Var a`
    SUBST1_TAC THENL
   [MATCH_MP_TAC LUNIFAUX_walkstar_NOT_FDOM_var THEN ASM_MESON_TAC[walk_to_var];
    ALL_TAC] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [MP_TAC(SPECL [`s:(num,A term_term)fmap`; `Pair a0 a1:A term_term`; `a:num`;
                  `s2:(num,A term_term)fmap`] oc_subterm_neq) THEN
    ASM_REWRITE_TAC[term_term_distinct];
    MESON_TAC[]];;

let eqs_unify = prove
 (`!(s:(num,A term_term)fmap) t1 t2 s2.
     wfs s /\ wfs s2 /\ walkstar s2 (walkstar s t1) = walkstar s2 (walkstar s t2)
     ==> ?sx. unify s t1 t2 = SOME sx`,
  MATCH_MP_TAC unify_ind THEN
  MAP_EVERY X_GEN_TAC [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  X_GEN_TAC `s2:(num,A term_term)fmap` THEN STRIP_TAC THEN
  SUBGOAL_THEN `walkstar s2 (walkstar s (walk s t1)) =
                walkstar (s2:(num,A term_term)fmap) (walkstar s (walk s t2))`
    MP_TAC THENL
   [REWRITE_TAC[MATCH_MP walkstar_walk (ASSUME `wfs (s:(num,A term_term)fmap)`)] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`]
               unify_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE; ext_s_check_def; option_DISTINCT;
              LUNIFAUX_oc_const] THENL
   [DISCH_TAC THEN MESON_TAC[];
    LUNIFAUX_eqs_var_tac;
    DISCH_TAC THEN MESON_TAC[];
    LUNIFAUX_eqs_var_tac;
    LUNIFAUX_wsthm_tac THEN REWRITE_TAC[term_term_11] THEN STRIP_TAC THEN
    USE_THEN "ih2" (MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`;
                                    `a0':A term_term`; `a1':A term_term`]) THEN
    REWRITE_TAC[ASSUME `wfs (s:(num,A term_term)fmap)`] THEN
    DISCH_THEN(MP_TAC o SPEC `s2:(num,A term_term)fmap`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:(num,A term_term)fmap` ASSUME_TAC) THEN
    ASM_REWRITE_TAC[OPTION_BIND_DEF] THEN
    SUBGOAL_THEN `wfs (x:(num,A term_term)fmap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[unify_unifier]; ALL_TAC] THEN
    SUBGOAL_THEN `!t. walkstar s2 (walkstar x t) =
                      walkstar (s2:(num,A term_term)fmap) (walkstar s t)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC unify_mgu THEN
      MAP_EVERY EXISTS_TAC [`a0:A term_term`; `a0':A term_term`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`a0:A term_term`; `a1:A term_term`;
                                    `a0':A term_term`; `a1':A term_term`;
                                    `x:(num,A term_term)fmap`]) THEN
    REWRITE_TAC[ASSUME `wfs (s:(num,A term_term)fmap)`;
                ASSUME `unify (s:(num,A term_term)fmap) a0 a0' = SOME x`] THEN
    DISCH_THEN(MP_TAC o SPEC `s2:(num,A term_term)fmap`) THEN
    ASM_REWRITE_TAC[];
    LUNIFAUX_wsthm_tac THEN REWRITE_TAC[term_term_distinct];
    DISCH_TAC THEN MESON_TAC[];
    LUNIFAUX_wsthm_tac THEN REWRITE_TAC[term_term_distinct];
    LUNIFAUX_wsthm_tac THEN REWRITE_TAC[term_term_11] THEN
    DISCH_THEN SUBST1_TAC THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* COMPAT: a substitution more specific than another.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("COMPAT",(12,"right"));;

let COMPAT_def = new_definition
  `(s:(num,A term_term)fmap) COMPAT s0 <=>
     wfs s /\ wfs s0 /\ (!t. walkstar s (walkstar s0 t) = walkstar s t)`;;

let SUBMAP_COMPAT = prove
 (`!(s:(num,A term_term)fmap) sx. wfs sx /\ s SUBMAP sx ==> sx COMPAT s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPAT_def] THEN
  ASM_MESON_TAC[wfs_SUBMAP; walkstar_SUBMAP]);;

let COMPAT_REFL = prove
 (`!s:(num,A term_term)fmap. wfs s ==> s COMPAT s`,
  SIMP_TAC[COMPAT_def] THEN MESON_TAC[walkstar_idempotent]);;

let COMPAT_TRANS = prove
 (`!(s2:(num,A term_term)fmap) s1 s0.
     s2 COMPAT s1 /\ s1 COMPAT s0 ==> s2 COMPAT s0`,
  REWRITE_TAC[COMPAT_def] THEN MESON_TAC[]);;

let COMPAT_extend = prove
 (`!(sx:(num,A term_term)fmap) s vx tx.
     sx COMPAT s /\ wfs (s |+ (vx,tx)) /\ ~(vx IN FDOM s) /\
     walkstar sx (term_Var vx) = walkstar sx tx
     ==> sx COMPAT (s |+ (vx,tx))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPAT_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  MP_TAC(SPECL [`sx:(num,A term_term)fmap`; `s:(num,A term_term)fmap`;
                `vx:num`; `tx:A term_term`] walkstar_extend) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

let COMPAT_eqs_unify = prove
 (`!(s:(num,A term_term)fmap) t1 t2 sx.
     sx COMPAT s /\ walkstar sx t1 = walkstar sx t2
     ==> ?si. unify s t1 t2 = SOME si /\ sx COMPAT si`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPAT_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                `sx:(num,A term_term)fmap`] eqs_unify) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `si:(num,A term_term)fmap` ASSUME_TAC) THEN
  EXISTS_TAC `si:(num,A term_term)fmap` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[unify_unifier]; ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                `si:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`] unify_mgu) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

let COMPAT_more_specific = prove
 (`!(s:(num,A term_term)fmap) s0.
     s COMPAT s0 <=>
     wfs s /\ wfs s0 /\
     (!t1 t2. walkstar s0 t1 = walkstar s0 t2 ==> walkstar s t1 = walkstar s t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPAT_def] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[walkstar_idempotent]]);;

let _ = cake_add_simps [unify_same];;
