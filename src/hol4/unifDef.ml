(* ========================================================================= *)
(* unifDef: port of HOL4 examples/algorithms/unification/triangular/        *)
(* first-order/unifDefScript.sml (HOL4 library used by CakeML v3479): the   *)
(* definition of triangular unification, unify.                             *)
(*                                                                           *)
(* How unify is defined: as in HOL4, unify is a new_specification whose     *)
(* defining property is unify_def (the recursion equations under wfs s).    *)
(* HOL4 proves the specification satisfiable with tunify, a TFL definition  *)
(* (nested recursion, relation uR) made total by Defn.tprove.  Here the     *)
(* witness is the function given by WF_REC on uR for the functional whose   *)
(* second recursive call is guarded by uR (as in HOL4's tunify_tupled_aux);  *)
(* the guard is then shown redundant (the result of a call satisfies uP).   *)
(* HOL4's internal tunify, tunify_tupled_aux and their lemmas (aux_uP,      *)
(* tcd_thm, aux_eq_tunify, unify_eq_tunify) are therefore not constants or  *)
(* theorems here.  WF_uR is proved with a simpler measure than HOL4's:      *)
(* (CARD (allvars s t1 t2) - CARD (FDOM s), pair_count (walkstar s t1))      *)
(* decreases lexicographically.                                              *)
(*                                                                           *)
(* Notes: HOL4's monad_bind is an overload of OPTION_BIND (do-notation); the *)
(* port writes OPTION_BIND.  uR_ind is stated with readable variable names.  *)
(* Helper lemmas are LUNIFAUX_.                                              *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/walkstar.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Extending a substitution keeps it well-formed.                            *)
(* ------------------------------------------------------------------------- *)

let vR_update = prove
 (`!(s:(num,A term_term)fmap) v t x y.
     ~(v IN FDOM s) /\ ~(x = v) ==> (vR (s |+ (v,t)) y x <=> vR s y x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[vR_def; FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[]);;

let TC_vR_update = prove
 (`!(s:(num,A term_term)fmap) v t y x.
     TC (vR (s |+ (v,t))) y x ==> ~(v IN FDOM s) ==>
     TC (vR s) y x \/ ?u. RTC (vR s) v x /\ u IN term_vars t /\ RTC (vR s) y u`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`x:num`,`x:num`) THEN SPEC_TAC(`y:num`,`y:num`) THEN
  MATCH_MP_TAC TC_INDUCT THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:num`; `x:num`] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `x:num = v` THENL
     [DISJ2_TAC THEN EXISTS_TAC `y:num` THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[vR_def; FLOOKUP_UPDATE; option_CASE]) THEN
      ASM_REWRITE_TAC[RTC_REFL];
      DISJ1_TAC THEN MATCH_MP_TAC TC_INC THEN ASM_MESON_TAC[vR_update]];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[TC_TRANS; RTC_TRANS; RTC_INC_TC]]);;

let wfs_extend = prove
 (`!(s:(num,A term_term)fmap) v t.
     wfs s /\ ~(v IN FDOM s) /\ ~(v IN term_vars (walkstar s t))
     ==> wfs (s |+ (v,t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u. u IN term_vars (t:A term_term) ==> ~TC (vR (s:(num,A term_term)fmap)) v u`
    ASSUME_TAC THENL [ASM_MESON_TAC[TC_vR_vars_walkstar]; ALL_TAC] THEN
  SUBGOAL_THEN `~((v:num) IN term_vars (t:A term_term))` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_FDOM_walkstar]; ALL_TAC] THEN
  REWRITE_TAC[wfs_no_cycles] THEN X_GEN_TAC `w:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`; `t:A term_term`;
                `w:num`; `w:num`] TC_vR_update) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[wfs_no_cycles];
    SUBGOAL_THEN `RTC (vR (s:(num,A term_term)fmap)) v u` MP_TAC THENL
     [ASM_MESON_TAC[RTC_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[RTC; RC_EXPLICIT] THEN ASM_MESON_TAC[]]);;

let vwalk_FDOM = prove
 (`!(s:(num,A term_term)fmap) v t.
     wfs s ==> vwalk s v = t ==>
     (~(v IN FDOM s) /\ t = term_Var v) \/
     (v IN FDOM s /\ ~(t = term_Var v) /\
      ?u. vwalk s v = vwalk s u /\ FLOOKUP s u = SOME t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `(v:num) IN FDOM (s:(num,A term_term)fmap)` THEN
  ASM_SIMP_TAC[NOT_FDOM_vwalk] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[vwalk_to_var]; ALL_TAC] THEN
  UNDISCH_TAC `(v:num) IN FDOM (s:(num,A term_term)fmap)` THEN
  SPEC_TAC(`v:num`,`v:num`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `v:num`] LUNIFAUX_vwalk_FLOOKUP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FLOOKUP (s:(num,A term_term)fmap) v = SOME (FAPPLY s v)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASES_ON `FAPPLY (s:(num,A term_term)fmap) v` THEN
  REWRITE_TAC[term_term_distinct; term_term_11] THEN STRIP_TAC THENL
   [ASM_CASES_TAC `(a:num) IN FDOM (s:(num,A term_term)fmap)` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `v:num` THEN ASM_MESON_TAC[NOT_FDOM_vwalk]];
    EXISTS_TAC `v:num` THEN ASM_MESON_TAC[];
    EXISTS_TAC `v:num` THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* allvars, the termination relation uR and its well-foundedness.            *)
(* ------------------------------------------------------------------------- *)

let allvars_def = new_definition
  `allvars (s:(num,A term_term)fmap) (t1:A term_term) (t2:A term_term) =
     (term_vars t1 UNION term_vars t2) UNION substvars s`;;

let FINITE_allvars = prove
 (`!(s:(num,A term_term)fmap) t1 t2. FINITE (allvars s t1 t2)`,
  REWRITE_TAC[allvars_def; FINITE_UNION; FINITE_vars; FINITE_substvars]);;

let allvars_sym = prove
 (`!(s:(num,A term_term)fmap) t1 t2. allvars s t1 t2 = allvars s t2 t1`,
  REWRITE_TAC[allvars_def] THEN SET_TAC[]);;

let uR_def = cake_def
  `uR (sx:(num,A term_term)fmap,c1:A term_term,c2:A term_term) (s,t1,t2) <=>
     wfs sx /\ s SUBMAP sx /\ allvars sx c1 c2 SUBSET allvars s t1 t2 /\
     measure (pair_count o walkstar sx) c1 t1`;;

let LUNIFAUX_SUBMAP_FDOM_EQ = prove
 (`!(f:(A,B)fmap) g. f SUBMAP g /\ FDOM g = FDOM f ==> g = f`,
  REWRITE_TAC[SUBMAP_DEF; GSYM fmap_EQ_THM] THEN MESON_TAC[]);;

let LUNIFAUX_FDOM_allvars = prove
 (`!(s:(num,A term_term)fmap) t1 t2. FDOM s SUBSET allvars s t1 t2`,
  REWRITE_TAC[allvars_def; substvars_def] THEN SET_TAC[]);;

let WF_uR = prove
 (`WF (uR:(num,A term_term)fmap#A term_term#A term_term->
          (num,A term_term)fmap#A term_term#A term_term->bool)`,
  MATCH_MP_TAC WF_SUBSET THEN
  EXISTS_TAC
   `inv_image ((<) LEX (<))
      (\x:(num,A term_term)fmap#A term_term#A term_term.
         (CARD (allvars (FST x) (FST(SND x)) (SND(SND x))) - CARD (FDOM (FST x)),
          pair_count (walkstar (FST x) (FST (SND x)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC WF_inv_image THEN MATCH_MP_TAC WF_LEX_HOL4 THEN
    REWRITE_TAC[WF_LT_NUM]] THEN
  REWRITE_TAC[FORALL_PAIR_THM; uR_def; inv_image_THM; LEX_THM; measure_THM;
              o_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`sx:(num,A term_term)fmap`; `c1:A term_term`; `c2:A term_term`;
    `s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`]
               SUBMAP_FDOM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`sx:(num,A term_term)fmap`; `c1:A term_term`; `c2:A term_term`]
               LUNIFAUX_FDOM_allvars) THEN
  MP_TAC(ISPECL [`allvars (sx:(num,A term_term)fmap) c1 c2`;
                `allvars (s:(num,A term_term)fmap) t1 t2`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_allvars] THEN
  ASM_CASES_TAC `FDOM (sx:(num,A term_term)fmap) = FDOM (s:(num,A term_term)fmap)` THENL
   [SUBGOAL_THEN `sx:(num,A term_term)fmap = s` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[LUNIFAUX_SUBMAP_FDOM_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`FDOM (sx:(num,A term_term)fmap)`;
                `allvars (sx:(num,A term_term)fmap) c1 c2`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_allvars] THEN
  MP_TAC(ISPECL [`FDOM (s:(num,A term_term)fmap)`;
                `FDOM (sx:(num,A term_term)fmap)`] CARD_PSUBSET) THEN
  ASM_REWRITE_TAC[FDOM_FINITE; PSUBSET] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] ORELSE ALL_TAC) THEN
  ASM_ARITH_TAC);;

let uR_lex_def = new_definition
  `uR_lex =
     inv_image ((\s1 s2. s2 SUBMAP s1 /\ ~(s2 = s1)) LEX
                (\s1 s2. s1 PSUBSET s2 /\ FINITE s2) LEX measure pair_count)
               (\(s:(num,A term_term)fmap,t1:A term_term,t2:A term_term).
                  (s,allvars s t1 t2,walkstar s t1))`;;

let uR_RSUBSET_uR_lex = prove
 (`RSUBSET (uR:(num,A term_term)fmap#A term_term#A term_term->
              (num,A term_term)fmap#A term_term#A term_term->bool) uR_lex`,
  REWRITE_TAC[RSUBSET_DEF; FORALL_PAIR_THM; uR_def; uR_lex_def; inv_image_THM;
              LEX_THM; measure_THM; o_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`sx:(num,A term_term)fmap`; `c1:A term_term`; `c2:A term_term`;
    `s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `sx:(num,A term_term)fmap = s` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[PSUBSET; FINITE_allvars] THEN ASM_MESON_TAC[]);;

let WF_FINITE_PSUBSET = prove
 (`WF (\s1 s2:A->bool. s1 PSUBSET s2 /\ FINITE s2)`,
  MATCH_MP_TAC WF_SUBSET THEN EXISTS_TAC `measure (CARD:(A->bool)->num)` THEN
  REWRITE_TAC[WF_measure; measure_THM] THEN MESON_TAC[CARD_PSUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The termination conditions of unify.                                      *)
(* ------------------------------------------------------------------------- *)

let LUNIFAUX_walk_rangevars = prove
 (`!(s:(num,A term_term)fmap) t.
     wfs s ==> term_vars (walk s t) SUBSET rangevars s UNION term_vars t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `walk (s:(num,A term_term)fmap) t = t` THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`walk (s:(num,A term_term)fmap) t`; `s:(num,A term_term)fmap`]
                 IN_FRANGE_rangevars) THEN
    ASM_SIMP_TAC[walk_IN_FRANGE] THEN SET_TAC[]]);;

let vwalk_to_Pair_SUBSET_rangevars = prove
 (`!(s:(num,A term_term)fmap) v t1 t2.
     wfs s /\ vwalk s v = Pair t1 t2
     ==> term_vars t1 SUBSET rangevars s /\ term_vars t2 SUBSET rangevars s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:num) IN FDOM (s:(num,A term_term)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_FDOM_vwalk; term_term_distinct]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Pair t1 t2:A term_term`; `s:(num,A term_term)fmap`]
               IN_FRANGE_rangevars) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[vwalk_IN_FRANGE]; ALL_TAC] THEN
  REWRITE_TAC[term_vars_def] THEN SET_TAC[]);;

let allvars_SUBSET = prove
 (`!(s:(num,A term_term)fmap) t1 t2 t1a t1d t2a t2d.
     wfs s /\ walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d
     ==> allvars s t1a t2a SUBSET allvars s t1 t2 /\
         allvars s t1d t2d SUBSET allvars s t1 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`]
               LUNIFAUX_walk_rangevars) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t2:A term_term`]
               LUNIFAUX_walk_rangevars) THEN
  ASM_REWRITE_TAC[allvars_def; substvars_def; term_vars_def] THEN SET_TAC[]);;

let walkstar_subterm_smaller = prove
 (`!(s:(num,A term_term)fmap) t1 t1a t1d.
     wfs s /\ walk s t1 = Pair t1a t1d
     ==> pair_count (walkstar s t1a) < pair_count (walkstar s t1) /\
         pair_count (walkstar s t1d) < pair_count (walkstar s t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`] walkstar_def) THEN
  ASM_REWRITE_TAC[term_term_CASE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_count_def] THEN ARITH_TAC);;

let tca_thm = prove
 (`!(s:(num,A term_term)fmap) t1 t2 t1a t1d t2a t2d.
     wfs s /\ walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d
     ==> uR (s,t1a,t2a) (s,t1,t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[uR_def; SUBMAP_REFL; measure_THM; o_THM] THEN
  ASM_MESON_TAC[allvars_SUBSET; walkstar_subterm_smaller]);;

let walk_SUBMAP = prove
 (CASE_TERM `!(s:(num,A term_term)fmap) sx t. wfs sx /\ s SUBMAP sx ==>
     (match walk s t with term_Var u -> walk sx t = walk sx (term_Var u)
                        | u -> walk sx t = u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `t:A term_term` THEN
  REWRITE_TAC[walk_walk_thm; term_term_CASE] THEN
  MP_TAC(SPECL [`a:num`; `s:(num,A term_term)fmap`]
    (MATCH_MP vwalk_SUBMAP (ASSUME `wfs (sx:(num,A term_term)fmap)`))) THEN
  ASM_REWRITE_TAC[]);;

let allvars_SUBSET_FUPDATE = prove
 (`!(s:(num,A term_term)fmap) t1 t2 t1a t1d t2a t2d v.
     walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d /\
     walk s t1a = term_Var v /\ wfs s
     ==> allvars (s |+ (v,walk s t2a)) t1d t2d SUBSET allvars s t1 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((v:num) IN FDOM (s:(num,A term_term)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[walk_to_var]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                `t1a:A term_term`; `t1d:A term_term`; `t2a:A term_term`;
                `t2d:A term_term`] allvars_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1a:A term_term`]
               LUNIFAUX_walk_rangevars) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t2a:A term_term`]
               LUNIFAUX_walk_rangevars) THEN
  ASM_SIMP_TAC[allvars_def; substvars_def; FDOM_FUPDATE; rangevars_FUPDATE;
               term_vars_def] THEN
  SET_TAC[]);;

let walkstar_subterm_FUPDATE = prove
 (`!(s:(num,A term_term)fmap) v t t1 t1a t1d.
     wfs s /\ ~(v IN FDOM s) /\ ~(v IN term_vars (walkstar s t)) /\
     walk s t1 = Pair t1a t1d
     ==> pair_count (walkstar (s |+ (v,t)) t1d) <
         pair_count (walkstar (s |+ (v,t)) t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfs ((s:(num,A term_term)fmap) |+ (v,t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[wfs_extend]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:(num,A term_term)fmap) SUBMAP (s |+ (v,t))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN]; ALL_TAC] THEN
  SUBGOAL_THEN `walk ((s:(num,A term_term)fmap) |+ (v,t)) t1 = Pair t1a t1d`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:(num,A term_term)fmap`; `(s:(num,A term_term)fmap) |+ (v,t)`;
                  `t1:A term_term`] walk_SUBMAP) THEN
    ASM_REWRITE_TAC[term_term_CASE];
    ASM_MESON_TAC[walkstar_subterm_smaller]]);;

let uR_subterm = prove
 (`!(s:(num,A term_term)fmap) t1 t2 t1a t1d t2a t2d.
     wfs s /\ walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d
     ==> uR (s,t1a,t2a) (s,t1,t2) /\ uR (s,t1d,t2d) (s,t1,t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[uR_def; SUBMAP_REFL; measure_THM; o_THM] THEN
  ASM_MESON_TAC[allvars_SUBSET; walkstar_subterm_smaller]);;

let uR_subterm_FUPDATE = prove
 (`!(s:(num,A term_term)fmap) t1 t2 t1a t1d t2a t2d v t.
     walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d /\
     (walk s t1a = term_Var v /\ walk s t2a = t \/
      walk s t2a = term_Var v /\ walk s t1a = t) /\
     wfs s /\ ~(v IN FDOM s) /\ ~(v IN term_vars (walkstar s t))
     ==> uR (s |+ (v,t),t1d,t2d) (s,t1,t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `wfs ((s:(num,A term_term)fmap) |+ (v,t))` ASSUME_TAC THENL
    [ASM_MESON_TAC[wfs_extend]; ALL_TAC] THEN
   ASM_REWRITE_TAC[uR_def; SUBMAP_FUPDATE_EQN; measure_THM; o_THM] THEN
   CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[walkstar_subterm_FUPDATE]]) THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC allvars_SUBSET_FUPDATE THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ONCE_REWRITE_TAC[allvars_sym] THEN
    MATCH_MP_TAC allvars_SUBSET_FUPDATE THEN ASM_MESON_TAC[]]);;

let uR_ind = prove
 (`!P. (!(s:(num,A term_term)fmap) t1 t2.
          (!sx c1 c2. uR (sx,c1,c2) (s,t1,t2) ==> P sx c1 c2) ==> P s t1 t2)
       ==> !s t1 t2. P s t1 t2`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[WF_IND] WF_uR) THEN
  DISCH_THEN(MP_TAC o SPEC
    `\x:(num,A term_term)fmap#A term_term#A term_term.
        P (FST x) (FST(SND x)) (SND(SND x)):bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]);;

let uP_def = new_definition
  `uP (sx:(num,A term_term)fmap) s t1 t2 <=>
     wfs sx /\ s SUBMAP sx /\ substvars sx SUBSET allvars s t1 t2`;;

let uP_sym = prove
 (`!(sx:(num,A term_term)fmap) s t1 t2. uP sx s t1 t2 <=> uP sx s t2 t1`,
  REWRITE_TAC[uP_def] THEN MESON_TAC[allvars_sym]);;

let uP_FUPDATE = prove
 (`!(s:(num,A term_term)fmap) v t1 t2.
     wfs s /\ ~(v IN FDOM s) /\ ~(v IN term_vars (walkstar s t2)) /\
     walk s t1 = term_Var v
     ==> uP (s |+ (v,walk s t2)) s t1 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfs ((s:(num,A term_term)fmap) |+ (v,walk s t2))` ASSUME_TAC THENL
   [MATCH_MP_TAC wfs_extend THEN ASM_SIMP_TAC[walkstar_walk]; ALL_TAC] THEN
  ASM_REWRITE_TAC[uP_def; SUBMAP_FUPDATE_EQN] THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`]
               LUNIFAUX_walk_rangevars) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t2:A term_term`]
               LUNIFAUX_walk_rangevars) THEN
  ASM_SIMP_TAC[allvars_def; substvars_def; FDOM_FUPDATE; rangevars_FUPDATE;
               term_vars_def] THEN
  SET_TAC[]);;

let uR_IMP_uP = prove
 (`!(sx:(num,A term_term)fmap) c1 c2 s t1 t2.
     uR (sx,c1,c2) (s,t1,t2) ==> uP sx s t1 t2`,
  REWRITE_TAC[uR_def; uP_def; allvars_def] THEN SET_TAC[]);;

let uP_IMP_subterm_uR = prove
 (`!(s:(num,A term_term)fmap) t1 t2 t1a t1d t2a t2d sx.
     wfs s /\ walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d /\
     (uP sx s t1a t2a \/ uP sx s t1d t2d)
     ==> uR (sx,t1d,t2d) (s,t1,t2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ (d \/ e) ==> f <=>
                    (a /\ b /\ c /\ d ==> f) /\ (a /\ b /\ c /\ e ==> f)`] THEN
  CONJ_TAC THEN REWRITE_TAC[uP_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                `t1a:A term_term`; `t1d:A term_term`; `t2a:A term_term`;
                `t2d:A term_term`] allvars_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `walk (sx:(num,A term_term)fmap) t1 = Pair t1a t1d` ASSUME_TAC THEN
  TRY(MP_TAC(SPECL [`s:(num,A term_term)fmap`; `sx:(num,A term_term)fmap`;
                    `t1:A term_term`] walk_SUBMAP) THEN
      ASM_REWRITE_TAC[term_term_CASE] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[uR_def; measure_THM; o_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[allvars_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[allvars_def]) THEN
    ASM SET_TAC[];
    MP_TAC(SPECL [`sx:(num,A term_term)fmap`; `t1:A term_term`; `t1a:A term_term`;
                  `t1d:A term_term`] walkstar_subterm_smaller) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[allvars_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[allvars_def]) THEN
    ASM SET_TAC[];
    MP_TAC(SPECL [`sx:(num,A term_term)fmap`; `t1:A term_term`; `t1a:A term_term`;
                  `t1d:A term_term`] walkstar_subterm_smaller) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The definition of unify.                                                  *)
(* ------------------------------------------------------------------------- *)

let ext_s_check_def = new_definition
  `ext_s_check (s:(num,A term_term)fmap) v t =
     if walkstar_oc s t v then NONE else SOME (s |+ (v,t))`;;

(* the functional of WF_REC: HOL4's tunify with the second recursive call   *)
(* guarded by uR (tunify_tupled_aux)                                        *)

let LUNIFAUX_unify_H = CASE_TERM
 `\(f:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option)
   (x:(num,A term_term)fmap#A term_term#A term_term).
   match x with (s,t1,t2) ->
     if wfs s then
       (match (walk s t1, walk s t2) with
          (term_Var v1, term_Var v2) ->
            SOME (if v1 = v2 then s else s |+ (v1,term_Var v2))
        | (term_Var v1, t2) -> ext_s_check s v1 t2
        | (t1, term_Var v2) -> ext_s_check s v2 t1
        | (Pair t1a t1d, Pair t2a t2d) ->
            OPTION_BIND (f (s,t1a,t2a))
              (\sx. if uR (sx,t1d,t2d) (s,t1,t2) then f (sx,t1d,t2d) else ARB)
        | (Const c1, Const c2) -> if c1 = c2 then SOME s else NONE
        | _ -> NONE)
     else ARB`;;

let LUNIFAUX_unify_H_adm_tm =
  let hv = mk_var("HH", type_of LUNIFAUX_unify_H) in
  vsubst [LUNIFAUX_unify_H, hv]
   `!(f:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option) g x.
       (!z. uR z x ==> f z = g z) ==>
       (HH:((num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option)->
           (num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option)
         f x = HH g x`;;

let LUNIFAUX_unify_H_adm = prove
 (LUNIFAUX_unify_H_adm_tm,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option`;
    `g:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option`;
    `s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE] THEN
  SUBGOAL_THEN
    `(f:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option)
     (s,a0,a0') = g (s,a0,a0')` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[uR_subterm]; ALL_TAC] THEN
  AP_TERM_TAC THEN ABS_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let LUNIFAUX_uP_refl = prove
 (`!(s:(num,A term_term)fmap) t1 t2. wfs s ==> uP s s t1 t2`,
  SIMP_TAC[uP_def; SUBMAP_REFL; allvars_def] THEN SET_TAC[]);;

let LUNIFAUX_uP_ext = prove
 (`!(s:(num,A term_term)fmap) t1 t2 v.
     wfs s /\ walk s t1 = term_Var v /\ ~walkstar_oc s (walk s t2) v
     ==> uP (s |+ (v,walk s t2)) s t1 t2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC uP_FUPDATE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[walk_to_var]; ALL_TAC] THEN
  ASM_MESON_TAC[oc_eq_vars_walkstar; walkstar_walk]);;

let LUNIFAUX_unify_guP_tm =
  let hv = mk_var("HH", type_of LUNIFAUX_unify_H) in
  vsubst [LUNIFAUX_unify_H, hv]
   `!(f:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option).
       (!x. f x =
            (HH:((num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option)->
                (num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option)
              f x)
       ==> !s t1 t2 sx. wfs s /\ f (s,t1,t2) = SOME sx ==> uP sx s t1 t2`;;

let LUNIFAUX_ext_case_tac v ta tb sym =
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  (if sym then ONCE_REWRITE_TAC[uP_sym] else ALL_TAC) THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; ta; tb; v] LUNIFAUX_uP_ext) THEN
  ASM_REWRITE_TAC[];;

let LUNIFAUX_unify_guP = prove
 (LUNIFAUX_unify_guP_tm,
  GEN_TAC THEN
  DISCH_THEN(fun th ->
    let fe = REWRITE_RULE[FORALL_PAIR_THM; pair_CASE] th in
    MATCH_MP_TAC uR_ind THEN
    MAP_EVERY X_GEN_TAC
      [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
    DISCH_TAC THEN X_GEN_TAC `sx:(num,A term_term)fmap` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [fe]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE; option_DISTINCT; ext_s_check_def] THENL
   [REWRITE_TAC[option_INJ] THEN COND_CASES_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THENL
     [ASM_SIMP_TAC[LUNIFAUX_uP_refl];
      MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                    `a:num`] LUNIFAUX_uP_ext) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `vwalk (s:(num,A term_term)fmap) a' = term_Var a'`
        ASSUME_TAC THENL
       [ASM_MESON_TAC[NOT_FDOM_vwalk; walk_to_var]; ALL_TAC] THEN
      ASM_SIMP_TAC[oc_thm; term_term_CASE]];
    LUNIFAUX_ext_case_tac `a:num` `t1:A term_term` `t2:A term_term` false;
    LUNIFAUX_ext_case_tac `a:num` `t1:A term_term` `t2:A term_term` false;
    LUNIFAUX_ext_case_tac `a:num` `t2:A term_term` `t1:A term_term` true;
    CASES_ON `(f:(num,A term_term)fmap#A term_term#A term_term->
                 ((num,A term_term)fmap)option) (s,a0,a0')` THEN
    REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT] THEN
    SUBGOAL_THEN `uP (a:(num,A term_term)fmap) s a0 a0'` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`s:(num,A term_term)fmap`; `a0:A term_term`;
                                    `a0':A term_term`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[uR_subterm]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `uR (a:(num,A term_term)fmap,a1,a1') (s,t1,t2)` ASSUME_TAC THENL
     [MATCH_MP_TAC uP_IMP_subterm_uR THEN
      MAP_EVERY EXISTS_TAC [`a0:A term_term`; `a0':A term_term`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:(num,A term_term)fmap`; `a1:A term_term`;
                                  `a1':A term_term`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sx:(num,A term_term)fmap`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[uP_def; uR_def]) THEN ASM_REWRITE_TAC[uP_def] THEN
    ASM_MESON_TAC[SUBMAP_TRANS; SUBSET_TRANS];
    LUNIFAUX_ext_case_tac `a':num` `t2:A term_term` `t1:A term_term` true;
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LUNIFAUX_uP_refl]]);;

let unify_def = new_specification ["unify"]
 (prove
   (CASE_TERM `?unify. !(s:(num,A term_term)fmap) t1 t2. wfs s ==>
      unify s t1 t2 =
      (match (walk s t1, walk s t2) with
         (term_Var v1, term_Var v2) ->
           SOME (if v1 = v2 then s else s |+ (v1,term_Var v2))
       | (term_Var v1, t2) -> ext_s_check s v1 t2
       | (t1, term_Var v2) -> ext_s_check s v2 t1
       | (Pair t1a t1d, Pair t2a t2d) ->
           OPTION_BIND (unify s t1a t2a) (\sx. unify sx t1d t2d)
       | (Const c1, Const c2) -> if c1 = c2 then SOME s else NONE
       | _ -> NONE)`,
    MP_TAC(MATCH_MP (MATCH_MP WF_REC WF_uR) LUNIFAUX_unify_H_adm) THEN
    DISCH_THEN(X_CHOOSE_THEN
      `f:(num,A term_term)fmap#A term_term#A term_term->((num,A term_term)fmap)option`
      (fun th ->
         let fe = REWRITE_RULE[FORALL_PAIR_THM; pair_CASE] th in
         EXISTS_TAC `\s t1 t2.
           (f:(num,A term_term)fmap#A term_term#A term_term->
              ((num,A term_term)fmap)option) (s,t1,t2)` THEN
         REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
         GEN_REWRITE_TAC LAND_CONV [fe] THEN
         ASSUME_TAC(MATCH_MP LUNIFAUX_unify_guP th))) THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
    CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
    REWRITE_TAC[term_term_CASE] THEN
    CASES_ON `(f:(num,A term_term)fmap#A term_term#A term_term->
                 ((num,A term_term)fmap)option) (s,a0,a0')` THEN
    REWRITE_TAC[OPTION_BIND_DEF] THEN
    SUBGOAL_THEN `uR (a:(num,A term_term)fmap,a1,a1') (s,t1,t2)`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC uP_IMP_subterm_uR THEN
    MAP_EVERY EXISTS_TAC [`a0:A term_term`; `a0':A term_term`] THEN
    ASM_MESON_TAC[]));;

let unify_uP = prove
 (`!(s:(num,A term_term)fmap) t1 t2 sx.
     wfs s /\ unify s t1 t2 = SOME sx ==> uP sx s t1 t2`,
  MATCH_MP_TAC uR_ind THEN
  MAP_EVERY X_GEN_TAC
    [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_TAC THEN X_GEN_TAC `sx:(num,A term_term)fmap` THEN STRIP_TAC THEN
  UNDISCH_TAC `unify (s:(num,A term_term)fmap) t1 t2 = SOME sx` THEN
  MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`]
               unify_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t1` THEN
  CASES_ON `walk (s:(num,A term_term)fmap) t2` THEN
  REWRITE_TAC[term_term_CASE; option_DISTINCT; ext_s_check_def] THENL
   [REWRITE_TAC[option_INJ] THEN COND_CASES_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THENL
     [ASM_SIMP_TAC[LUNIFAUX_uP_refl];
      MP_TAC(SPECL [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`;
                    `a:num`] LUNIFAUX_uP_ext) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `vwalk (s:(num,A term_term)fmap) a' = term_Var a'`
        ASSUME_TAC THENL
       [ASM_MESON_TAC[NOT_FDOM_vwalk; walk_to_var]; ALL_TAC] THEN
      ASM_SIMP_TAC[oc_thm; term_term_CASE]];
    LUNIFAUX_ext_case_tac `a:num` `t1:A term_term` `t2:A term_term` false;
    LUNIFAUX_ext_case_tac `a:num` `t1:A term_term` `t2:A term_term` false;
    LUNIFAUX_ext_case_tac `a:num` `t2:A term_term` `t1:A term_term` true;
    CASES_ON `unify (s:(num,A term_term)fmap) a0 a0'` THEN
    REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT] THEN
    SUBGOAL_THEN `uP (a:(num,A term_term)fmap) s a0 a0'` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`s:(num,A term_term)fmap`; `a0:A term_term`;
                                    `a0':A term_term`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[uR_subterm]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `uR (a:(num,A term_term)fmap,a1,a1') (s,t1,t2)` ASSUME_TAC THENL
     [MATCH_MP_TAC uP_IMP_subterm_uR THEN
      MAP_EVERY EXISTS_TAC [`a0:A term_term`; `a0':A term_term`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:(num,A term_term)fmap`; `a1:A term_term`;
                                  `a1':A term_term`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sx:(num,A term_term)fmap`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[uP_def; uR_def]) THEN ASM_REWRITE_TAC[uP_def] THEN
    ASM_MESON_TAC[SUBMAP_TRANS; SUBSET_TRANS];
    LUNIFAUX_ext_case_tac `a':num` `t2:A term_term` `t1:A term_term` true;
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LUNIFAUX_uP_refl]]);;

let unify_ind = prove
 (`!P. (!(s:(num,A term_term)fmap) t1 t2.
          (!t1a t1d t2a t2d sx.
             wfs s /\ walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d /\
             unify s t1a t2a = SOME sx ==> P sx t1d t2d) /\
          (!t1a t1d t2a t2d.
             wfs s /\ walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d
             ==> P s t1a t2a)
          ==> P s t1 t2)
       ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "hyp") THEN MATCH_MP_TAC uR_ind THEN
  MAP_EVERY X_GEN_TAC
    [`s:(num,A term_term)fmap`; `t1:A term_term`; `t2:A term_term`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN USE_THEN "hyp" MATCH_MP_TAC THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THENL
   [MATCH_MP_TAC uP_IMP_subterm_uR THEN
    MAP_EVERY EXISTS_TAC [`t1a:A term_term`; `t2a:A term_term`] THEN
    ASM_MESON_TAC[unify_uP];
    ASM_MESON_TAC[uR_subterm]]);;

let _ = cake_add_simps [FINITE_allvars; ext_s_check_def];;
