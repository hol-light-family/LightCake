(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 7 (HOL4 lines      *)
(* 5196-5713): typing of the steps, hypotheses under the steps,              *)
(* proves_substitutable.                                                     *)
(* ========================================================================= *)

needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem_p6.ml";;

prioritize_num();;
type_invention_error := true;;

let term_image_cong = prove
 (`!ls f g. (!t. MEM t ls ==> f t = g t) ==> term_image f ls = term_image g ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[term_image_nil; CSYNAUX_P3_term_image_cons; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:hol_term->hol_term) h = g h /\ term_image f t = term_image g t`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let apply_steps_typeof_eq = prove
 (`!sig stps t1 t2.
     steps_ok sig stps /\ hol_term_ok sig t1 /\ hol_term_ok sig t2 /\
     typeof t1 = typeof t2
     ==> typeof (apply_steps stps t1) = typeof (apply_steps stps t2)`,
  let pre_tac =
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `typeof (apply_steps t (t1:hol_term)) = typeof (apply_steps t t2)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `hol_term_ok sig (apply_steps t (t1:hol_term)) /\
                  hol_term_ok sig (apply_steps t (t2:hol_term))` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] in
  GEN_TAC THEN LIST_INDUCT_TAC THENL [SIMP[apply_steps_def]; ALL_TAC] THEN
  NAMED_CASES_ON "h" ["ilist"; "tyin"] THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THENL
   [pre_tac THEN
    SUBGOAL_THEN `!tm. hol_term_ok sig tm ==> typeof (VSUBST ilist tm) = typeof tm`
    (fun th -> ASM_SIMP_TAC[th]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC typeof_vsubst1 THEN EXISTS_TAC `sig:sig` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    pre_tac THEN
    SUBGOAL_THEN `!tm. welltyped tm ==> typeof (INST tyin tm) = TYPE_SUBST tyin (typeof tm)`
    (fun th -> ASM_MESON_TAC[th; term_ok_welltyped]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WELLTYPED_LEMMA THEN MATCH_MP_TAC INST_HAS_TYPE THEN
    EXISTS_TAC `typeof (tm:hol_term)` THEN ASM_REWRITE_TAC[GSYM WELLTYPED]]);;

(* HOL4 proves the theorem proves_substitutable_aux by rule induction on   *)
(* |- and suspends the ten cases, which it resumes in this part (Resume)     *)
(* and closes at Finalise.  Here each case is a lemma at the place of its    *)
(* Resume block, about the induction predicate CLITAUX_psa below, and        *)
(* proves_substitutable_aux follows at the place of Finalise.               *)
let CLITAUX_psa_def = new_definition
 `CLITAUX_psa sig axs h c <=>
    theory_ok (sig,axs)
    ==> !sigma stps.
          (!ax. ax IN axs ==> no_var_collapse sigma ax) /\
          esubsts_ok sig sigma /\
          steps_ok sig stps
          ==> ((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),
               term_image (esubst sigma []) (term_image (apply_steps stps) h)) |-
              esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps c)`;;

(* The start of a case: the facts of proves_term_ok for its sequent
   hypotheses, the definition unfolded, the induction hypotheses with their
   theory_ok antecedent discharged, and sigma, stps and their conditions as
   assumptions. *)
let CLITAUX_PSA_IH_TAC =
  FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_imp t && (try fst(dest_const(rator(fst(dest_imp t)))) = "theory_ok"
                    with Failure _ -> false)
    then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let CLITAUX_PSA_INTRO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUM_LIST(fun ths -> EVERY (mapfilter (fun th -> MP_TAC(MATCH_MP proves_term_ok th)) ths)) THEN
  REWRITE_TAC[FST; SND; ALL; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLITAUX_psa_def; PAIR]) THEN
  REWRITE_TAC[CLITAUX_psa_def; PAIR] THEN DISCH_TAC THEN
  REPEAT CLITAUX_PSA_IH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC;;

(* the induction hypotheses at the case's sigma and stps *)
let CLITAUX_PSA_SPEC_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL
    [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `stps:subst_step list`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC);;

(* The hypotheses of the substituted sequents (helpers for the cases). *)
let CLITAUX_psa_hyp_ok = prove
 (`!sig axs sigma stps l x.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\ steps_ok sig stps /\
     (!t. MEM t l ==> hol_term_ok sig t /\ t has_type Tyapp (implode "bool") []) /\
     MEM x (term_image (esubst sigma []) (term_image (apply_steps stps) l))
     ==> hol_term_ok (esubst_sig sigma sig) x /\ x has_type Tyapp (implode "bool") []`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hol_term_ok sig (apply_steps stps x'') /\
                apply_steps stps x'' has_type Tyapp (implode "bool") []`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[apply_steps_term_ok; apply_steps_has_type_Bool]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `axs:hol_term->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC esubst_has_type_bool THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 rev_drule_then drule_all esubst_apply_steps_Abs_alpha gives an Abs  *)
(* with esubst sigma [] inside; the case needs the avds of the hypotheses.  *)
let CLITAUX_ABS_ACONV_TAC side =
  MATCH_MP_TAC ACONV_TRANS THEN
  QEXISTS_TAC ("hol_Abs (hol_Var z ty') (esubst sigma [] (apply_steps stps " ^
               "(VSUBST [hol_Var z ty,hol_Var x ty] " ^ side ^ ")))") THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_ABS THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN ASM_MESON_TAC[];
    MATCH_MP_TAC ACONV_SYM THEN ASM_REWRITE_TAC[]];;

let CLITAUX_psa_Abs = prove
 (`!h l r thy ty x.
     ~EX (VFREE_IN (hol_Var x ty)) h /\ type_ok (FST (FST thy)) ty /\
     (thy,h) |- (l === r) /\ CLITAUX_psa (FST thy) (SND thy) h (l === r)
     ==> CLITAUX_psa (FST thy) (SND thy) h
           (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)`,
  CLITAUX_PSA_INTRO_TAC THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy) /\ is_std_sig (FST thy)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIR; theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) l /\ hol_term_ok (FST thy) r /\ typeof r = typeof l`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `SND (thy:thy)`;
    `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
    `FLAT (MAP tm_names (h:hol_term list))`; `x:mlstring`; `ty:hol_type`;
    `l:hol_term`; `r:hol_term`; `stps:subst_step list`;
    `FLAT (MAP tm_names (term_image (esubst sigma []) (term_image (apply_steps stps) h)))`]
    esubst_apply_steps_Abs_alpha) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:mlstring` (X_CHOOSE_THEN `ty':hol_type` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) [hol_Var z ty,hol_Var x ty]
                       ==> ?x' ty''. s = hol_Var x' ty'' /\ s' has_type ty'' /\
                                     hol_term_ok (FST (thy:thy)) s'`
  ASSUME_TAC THENL
   [REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN
    ASM_REWRITE_TAC[hol_term_ok_def; has_type_rules];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `APPEND stps [VStep [hol_Var z ty,hol_Var x ty]]`]) THEN
  ASM_REWRITE_TAC[steps_ok_append; steps_ok_def] THEN
  REWRITE_TAC[apply_steps_append; apply_steps_def] THEN
  SUBGOAL_THEN `term_image (apply_steps (APPEND stps [VStep [hol_Var z ty,hol_Var x ty]])) h =
                term_image (apply_steps stps) h` SUBST1_TAC THENL
   [MATCH_MP_TAC term_image_cong THEN REWRITE_TAC[apply_steps_append; apply_steps_def] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUBST_NOT_FREE_VAR THEN
    EXISTS_TAC `FST (thy:thy)` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[EX_MEM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (VSUBST [hol_Var z ty,hol_Var x ty] l) /\
                hol_term_ok (FST thy) (VSUBST [hol_Var z ty,hol_Var x ty] r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] l)) /\
                hol_term_ok (FST thy) (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] r))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `esubst sigma (FLAT (MAP tm_names h))
      (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] (l === r))) =
    esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] l)) ===
    esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] r))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SUBGOAL_THEN `VSUBST [hol_Var z ty,hol_Var x ty] (l === r) =
                  VSUBST [hol_Var z ty,hol_Var x ty] l === VSUBST [hol_Var z ty,hol_Var x ty] r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUBST_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] l ===
                                    VSUBST [hol_Var z ty,hol_Var x ty] r) =
                  apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] l) ===
                  apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] r)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC apply_steps_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`term_image (esubst sigma []) (term_image (apply_steps stps) h)`;
    `esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] l))`;
    `esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] r))`;
    `(esubst_sig sigma (FST (thy:thy)),IMAGE (esubst sigma []) (SND thy))`;
    `ty':hol_type`; `z:mlstring`] proves_ABS) THEN
  ASM_REWRITE_TAC[FST] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM EX_MEM] THEN DISCH_THEN(X_CHOOSE_THEN `p:hol_term` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN
    EXISTS_TAC `tm_names p` THEN CONJ_TAC THENL
     [EXISTS_TAC `p:hol_term` THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[VFREE_IN_tm_names]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (hol_Abs (hol_Var x ty) l) /\
                hol_term_ok (FST thy) (hol_Abs (hol_Var x ty) r)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[hol_term_ok_def] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!avds t. hol_term_ok (FST (thy:thy)) t
                    ==> welltyped (esubst sigma avds t) /\
                        typeof (esubst sigma avds t) = ty_esubst sigma (typeof t)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC esubst_welltyped THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC typeof_esubst THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t ==> hol_term_ok (FST thy) (apply_steps stps t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  SUBGOAL_THEN
   `esubst sigma (FLAT (MAP tm_names h))
      (apply_steps stps (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)) =
    esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (hol_Abs (hol_Var x ty) l)) ===
    esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (hol_Abs (hol_Var x ty) r))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `apply_steps stps (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r) =
                  apply_steps stps (hol_Abs (hol_Var x ty) l) ===
                  apply_steps stps (hol_Abs (hol_Var x ty) r)` SUBST1_TAC THENL
     [MATCH_MP_TAC apply_steps_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `typeof (apply_steps stps (hol_Abs (hol_Var x ty) r)) =
                typeof (apply_steps stps (hol_Abs (hol_Var x ty) l))` ASSUME_TAC THENL
   [MATCH_MP_TAC apply_steps_typeof_eq THEN EXISTS_TAC `FST (thy:thy)` THEN
    ASM_REWRITE_TAC[typeof_def];
    ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC `term_image (esubst sigma []) (term_image (apply_steps stps) h)` THEN
  QEXISTS_TAC "hol_Abs (hol_Var z ty')
                 (esubst sigma (FLAT (MAP tm_names h))
                    (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] l))) ===
               hol_Abs (hol_Var z ty')
                 (esubst sigma (FLAT (MAP tm_names h))
                    (apply_steps stps (VSUBST [hol_Var z ty,hol_Var x ty] r)))" THEN
  ASM_REWRITE_TAC[FST; GSYM ALL_MEM; GSYM EX_MEM] THEN
  ASM_SIMP_TAC[hypset_ok_term_image] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[welltyped_equation; EQUATION_HAS_TYPE_BOOL];
    MATCH_MP_TAC ACONV_equation THEN ASM_SIMP_TAC[WELLTYPED_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC[]; MESON_TAC[]; CLITAUX_ABS_ACONV_TAC "l"; CLITAUX_ABS_ACONV_TAC "r"];
    REPEAT STRIP_TAC THEN EXISTS_TAC `x':hol_term` THEN ASM_REWRITE_TAC[ACONV_REFL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_ok THEN
    MAP_EVERY EXISTS_TAC [`SND (thy:thy)`; `stps:subst_step list`; `h:hol_term list`] THEN
    ASM_SIMP_TAC[]]);;

let CLITAUX_psa_Assume = prove
 (`!p thy.
     theory_ok thy /\ p has_type Tyapp (implode "bool") [] /\ hol_term_ok (FST thy) p
     ==> CLITAUX_psa (FST thy) (SND thy) [p] p`,
  REWRITE_TAC[CLITAUX_psa_def; PAIR] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[term_image_sing; MAP; FLAT; APPEND_NIL] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps p) /\
                apply_steps stps p has_type Tyapp (implode "bool") []` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[apply_steps_term_ok; apply_steps_has_type_Bool]; ALL_TAC] THEN
  ABBREV_TAC `q = esubst sigma [] (apply_steps stps (p:hol_term))` THEN
  SUBGOAL_THEN `hol_term_ok (esubst_sig (sigma:(mlstring,mlstring list#hol_type)fmap#
                                       (mlstring,hol_term#hol_type)fmap) (FST (thy:thy))) q /\
                q has_type Tyapp (implode "bool") []` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_MESON_TAC[esubst_term_ok; esubst_has_type_bool; PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `theory_ok (esubst_sig sigma (FST (thy:thy)),IMAGE (esubst sigma []) (SND thy))`
  ASSUME_TAC THENL [ASM_MESON_TAC[theory_ok_esubst_axs; PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (esubst sigma (tm_names p) (apply_steps stps p)) /\
                ACONV q (esubst sigma (tm_names p) (apply_steps stps p))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_MESON_TAC[esubst_welltyped; ACONV_esubst_avds; term_ok_welltyped;
                                     PAIR];
    ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  MAP_EVERY EXISTS_TAC [`[q:hol_term]`; `q:hol_term`] THEN
  ASM_REWRITE_TAC[FST; ALL; EX; ACONV_REFL; hypset_ok_sing] THEN
  MATCH_MP_TAC proves_ASSUME THEN ASM_REWRITE_TAC[FST]);;

let CLITAUX_psa_Beta = prove
 (`!t thy ty x.
     theory_ok thy /\ type_ok (FST (FST thy)) ty /\ hol_term_ok (FST thy) t
     ==> CLITAUX_psa (FST thy) (SND thy) []
           (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)`,
  CLITAUX_PSA_INTRO_TAC THEN REWRITE_TAC[term_image_nil; MAP; FLAT] THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy) /\ is_std_sig (FST thy)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIR; theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (hol_Var x ty) /\
                hol_term_ok (FST thy) (hol_Abs (hol_Var x ty) t) /\
                hol_term_ok (FST thy) (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[hol_term_ok_def; WELLTYPED_CLAUSES; typeof_def] THEN
    ASM_MESON_TAC[term_ok_welltyped];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `esubst sigma [] (apply_steps stps
      (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)) =
    hol_Comb (esubst sigma [] (apply_steps stps (hol_Abs (hol_Var x ty) t)))
             (esubst sigma [] (apply_steps stps (hol_Var x ty))) ===
    esubst sigma [] (apply_steps stps t)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!a. hol_term_ok (FST (thy:thy)) a ==> hol_term_ok (FST thy) (apply_steps stps a)`
    ASSUME_TAC THENL [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
    SUBGOAL_THEN `apply_steps stps (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t) =
                  apply_steps stps (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty)) ===
                  apply_steps stps t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC apply_steps_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`FST (thy:thy)`;
      `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
      `[]:mlstring list`;
      `apply_steps stps (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty))`;
      `apply_steps stps t`] esubst_equation) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `apply_steps stps (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty)) =
                  hol_Comb (apply_steps stps (hol_Abs (hol_Var x ty) t))
                           (apply_steps stps (hol_Var x ty))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC apply_steps_comb THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC esubst_comb THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FST (thy:thy)`; `SND (thy:thy)`;
    `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
    `[]:mlstring list`; `x:mlstring`; `ty:hol_type`; `t:hol_term`; `stps:subst_step list`]
    esubst_apply_steps_Abs) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:mlstring` (X_CHOOSE_THEN `ty':hol_type`
    (X_CHOOSE_THEN `body:hol_term` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = esubst sigma [] (apply_steps stps (hol_Var x ty))` THEN
  SUBGOAL_THEN `theory_ok (esubst_sig sigma (FST (thy:thy)),IMAGE (esubst sigma []) (SND thy))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC theory_ok_esubst_axs THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (esubst_sig (sigma:(mlstring,mlstring list#hol_type)fmap#
                (mlstring,hol_term#hol_type)fmap) (FST (thy:thy))) a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `SND (thy:thy)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`body:hol_term`;
    `(esubst_sig sigma (FST (thy:thy)),IMAGE (esubst sigma []) (SND thy))`;
    `ty':hol_type`; `z:mlstring`] proves_BETA) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] proves_INST)) THEN
  DISCH_THEN(MP_TAC o SPEC `[(a:hol_term,hol_Var z ty')]`) THEN
  REWRITE_TAC[MEM; PAIR_EQ; FST] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
    MAP_EVERY EXISTS_TAC [`z:mlstring`; `ty':hol_type`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[term_image_nil] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) [a,hol_Var z ty']
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty`
  ASSUME_TAC THENL
   [REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`z:mlstring`; `ty':hol_type`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped body /\ typeof (VSUBST [a,hol_Var z ty'] body) = typeof body`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `welltyped body` ASSUME_TAC THENL
     [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WELLTYPED_LEMMA THEN
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[GSYM WELLTYPED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `VSUBST [a,hol_Var z ty'] (hol_Comb (hol_Abs (hol_Var z ty') body) (hol_Var z ty') === body) =
    hol_Comb (hol_Abs (hol_Var z ty') body) a === VSUBST [a,hol_Var z ty'] body`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `VSUBST [a,hol_Var z ty'] (hol_Comb (hol_Abs (hol_Var z ty') body) (hol_Var z ty'))
                === VSUBST [a,hol_Var z ty'] body` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_equation THEN
      QEXISTS_TAC "esubst_sig sigma (FST thy)" THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[hol_term_ok_def; WELLTYPED_CLAUSES; typeof_def] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN MESON_TAC[];
      REWRITE_TAC[VSUBST_def; REV_ASSOCD_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[FILTER; EX; VSUBST_nil] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[FILTER; EX; VSUBST_nil]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC `[]:hol_term list` THEN
  QEXISTS_TAC "hol_Comb (hol_Abs (hol_Var z ty') body) a === VSUBST [a,hol_Var z ty'] body" THEN
  ASM_REWRITE_TAC[ALL; hypset_ok_nil] THEN
  SUBGOAL_THEN `welltyped (esubst sigma [] (apply_steps stps (t:hol_term)))` ASSUME_TAC THENL
   [MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (hol_Comb (hol_Abs (hol_Var z ty') body) a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def] THEN
    REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    ASM_MESON_TAC[welltyped_def];
    EXISTS_TAC `typeof (body:hol_term)` THEN REWRITE_TAC[CONS_11; injectivity "hol_type"] THEN
    ASM_MESON_TAC[WELLTYPED_LEMMA]];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST [a,hol_Var z ty'] body)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[welltyped_equation; EQUATION_HAS_TYPE_BOOL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[typeof_def; codomain_def] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ACONV_TYPE o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "ACONV" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC ACONV_equation THEN ASM_REWRITE_TAC[ACONV_REFL]]);;

let apply_steps_ACONV = prove
 (`!sig stps x y.
     steps_ok sig stps /\
     welltyped x /\
     welltyped y /\
     ACONV x y
     ==> ACONV (apply_steps stps x) (apply_steps stps y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [SIMP[apply_steps_def]; ALL_TAC] THEN
  NAMED_CASES_ON "h" ["ilist"; "tyin"] THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC ACONV_VSUBST THEN ASM_MESON_TAC[apply_steps_welltyped];
    MATCH_MP_TAC ACONV_INST THEN ASM_MESON_TAC[apply_steps_welltyped]]);;

let term_ok_MEM_term_image_apply_steps = prove
 (`!sig l stps y.
     MEM y (term_image (apply_steps stps) l) /\
     steps_ok sig stps /\
     (!t. MEM t l ==> hol_term_ok sig t)
     ==> hol_term_ok sig y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_image_imp) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC apply_steps_term_ok THEN
  ASM_MESON_TAC[]);;

let MEM_term_image_compose_ACONV = prove
 (`!sig sigma axs l stps x y.
     MEM y l /\ ACONV x y /\ hypset_ok l /\
     (!t. MEM t l ==> hol_term_ok sig t) /\
     hol_term_ok sig x /\
     steps_ok sig stps /\ esubsts_ok sig sigma /\ theory_ok (sig,axs)
     ==> ?e. MEM e (term_image (esubst sigma []) (term_image (apply_steps stps) l)) /\
             ACONV (esubst sigma [] (apply_steps stps x)) e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:hol_term list`; `apply_steps stps`; `y:hol_term`] MEM_term_image) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y':hol_term` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`term_image (apply_steps stps) l`; `esubst sigma []`; `y':hol_term`]
    MEM_term_image) THEN
  ASM_SIMP_TAC[hypset_ok_term_image] THEN
  DISCH_THEN(X_CHOOSE_THEN `y'':hol_term` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y'':hol_term` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `esubst sigma [] y'` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC esubst_ACONV THEN MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC term_ok_MEM_term_image_apply_steps THEN
    MAP_EVERY EXISTS_TAC [`l:hol_term list`; `stps:subst_step list`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `apply_steps stps y` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC apply_steps_ACONV THEN ASM_MESON_TAC[term_ok_welltyped]]);;

let CLITAUX_psa_hyp_union = prove
 (`!sig axs sigma stps h1 h2 x.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\ steps_ok sig stps /\
     hypset_ok h1 /\ hypset_ok h2 /\
     (!t. MEM t h1 ==> hol_term_ok sig t) /\ (!t. MEM t h2 ==> hol_term_ok sig t) /\
     MEM x (term_union (term_image (esubst sigma []) (term_image (apply_steps stps) h1))
                       (term_image (esubst sigma []) (term_image (apply_steps stps) h2)))
     ==> ?e. ACONV x e /\
             MEM e (term_image (esubst sigma [])
                      (term_image (apply_steps stps) (term_union h1 h2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MP_TAC(ISPECL [`h1:hol_term list`; `h2:hol_term list`; `x'':hol_term`] MEM_term_union) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:hol_term` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEM_term_image_compose_ACONV THEN
  MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`; `y1:hol_term`] THEN
  ASM_SIMP_TAC[hypset_ok_term_union] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THEN
  ASM_SIMP_TAC[]);;

let CLITAUX_psa_hyp_remove = prove
 (`!sig axs sigma stps h1 h2 c1 c2 avds1 avds2 x.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\ steps_ok sig stps /\
     hypset_ok h1 /\ hypset_ok h2 /\
     (!t. MEM t h1 ==> hol_term_ok sig t) /\ (!t. MEM t h2 ==> hol_term_ok sig t) /\
     hol_term_ok sig c1 /\ hol_term_ok sig c2 /\
     MEM x (term_union
              (term_remove (esubst sigma avds2 (apply_steps stps c2))
                 (term_image (esubst sigma []) (term_image (apply_steps stps) h1)))
              (term_remove (esubst sigma avds1 (apply_steps stps c1))
                 (term_image (esubst sigma []) (term_image (apply_steps stps) h2))))
     ==> ?e. ACONV x e /\
             MEM e (term_image (esubst sigma [])
                      (term_image (apply_steps stps)
                         (term_union (term_remove c2 h1) (term_remove c1 h2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c y. hol_term_ok sig c /\ hol_term_ok sig y /\ ACONV c y
                      ==> !avds. ACONV (esubst sigma avds (apply_steps stps c))
                                       (esubst sigma [] (apply_steps stps y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_ACONV THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN
    ASM_SIMP_TAC[apply_steps_term_ok] THEN MATCH_MP_TAC apply_steps_ACONV THEN
    EXISTS_TAC `sig:sig` THEN ASM_MESON_TAC[term_ok_welltyped];
    ALL_TAC] THEN
  SUBGOAL_THEN `hypset_ok (term_union (term_remove c2 h1) (term_remove c1 h2)) /\
                (!t. MEM t (term_union (term_remove c2 h1) (term_remove c1 h2))
                     ==> hol_term_ok sig t)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[hypset_ok_term_union; hypset_ok_term_remove] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MEM_term_remove_imp) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_remove_imp) THEN
    ASM_SIMP_TAC[hypset_ok_term_image] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `MEM (x'':hol_term) (term_remove c2 h1)` ASSUME_TAC THENL
     [MATCH_MP_TAC MEM_term_remove THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM] o
        check (is_forall o concl)) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`term_remove c2 h1`; `term_remove c1 h2`; `x'':hol_term`]
      MEM_term_union) THEN
    ASM_SIMP_TAC[hypset_ok_term_remove] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:hol_term` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN MATCH_MP_TAC MEM_term_image_compose_ACONV THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`; `y1:hol_term`] THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_remove_imp) THEN
    ASM_SIMP_TAC[hypset_ok_term_image] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `MEM (x'':hol_term) (term_remove c1 h2)` ASSUME_TAC THENL
     [MATCH_MP_TAC MEM_term_remove THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM] o
        check (is_forall o concl)) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`term_remove c2 h1`; `term_remove c1 h2`; `x'':hol_term`]
      MEM_term_union) THEN
    ASM_SIMP_TAC[hypset_ok_term_remove] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:hol_term` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN MATCH_MP_TAC MEM_term_image_compose_ACONV THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`; `y1:hol_term`] THEN
    ASM_SIMP_TAC[]]);;

let CLITAUX_psa_DeductAntisym = prove
 (`!c1 c2 h1 h2 thy.
     ((thy,h1) |- c1 /\ CLITAUX_psa (FST thy) (SND thy) h1 c1) /\
     ((thy,h2) |- c2 /\ CLITAUX_psa (FST thy) (SND thy) h2 c2)
     ==> CLITAUX_psa (FST thy) (SND thy)
           (term_union (term_remove c2 h1) (term_remove c1 h2)) (c1 === c2)`,
  CLITAUX_PSA_INTRO_TAC THEN CLITAUX_PSA_SPEC_TAC THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy) /\ is_std_sig (FST thy)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIR; theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t ==> hol_term_ok (FST thy) (apply_steps stps t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `!avds t. hol_term_ok (FST (thy:thy)) t
                    ==> welltyped (esubst sigma avds t) /\
                        typeof (esubst sigma avds t) = ty_esubst sigma (typeof t)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC esubst_welltyped THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC typeof_esubst THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `typeof (apply_steps stps c1) = typeof (apply_steps stps (c2:hol_term))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC apply_steps_typeof_eq THEN EXISTS_TAC `FST (thy:thy)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[WELLTYPED_LEMMA];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps c1)`;
    `esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps c2)`;
    `term_image (esubst sigma []) (term_image (apply_steps stps) h1)`;
    `term_image (esubst sigma []) (term_image (apply_steps stps) h2)`;
    `(esubst_sig sigma (FST (thy:thy)),IMAGE (esubst sigma []) (SND thy))`]
   proves_DEDUCT_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `esubst sigma (FLAT (MAP tm_names (term_union (term_remove c2 h1) (term_remove c1 h2))))
      (apply_steps stps (c1 === c2)) =
    esubst sigma (FLAT (MAP tm_names (term_union (term_remove c2 h1) (term_remove c1 h2))))
      (apply_steps stps c1) ===
    esubst sigma (FLAT (MAP tm_names (term_union (term_remove c2 h1) (term_remove c1 h2))))
      (apply_steps stps c2)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `apply_steps stps (c1 === c2) = apply_steps stps c1 === apply_steps stps c2`
    SUBST1_TAC THENL
     [MATCH_MP_TAC apply_steps_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC
   `term_union
      (term_remove (esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps c2))
         (term_image (esubst sigma []) (term_image (apply_steps stps) h1)))
      (term_remove (esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps c1))
         (term_image (esubst sigma []) (term_image (apply_steps stps) h2)))` THEN
  EXISTS_TAC `esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps c1) ===
              esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps c2)` THEN
  ASM_REWRITE_TAC[FST; GSYM ALL_MEM; GSYM EX_MEM] THEN
  ASM_SIMP_TAC[hypset_ok_term_image; hypset_ok_term_union; hypset_ok_term_remove] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[welltyped_equation; EQUATION_HAS_TYPE_BOOL];
    MATCH_MP_TAC ACONV_equation THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN ASM_MESON_TAC[];
    REPEAT(MATCH_MP_TAC hypset_ok_term_image) THEN MATCH_MP_TAC hypset_ok_term_union THEN
    ASM_MESON_TAC[hypset_ok_term_remove];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_remove THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`;
      `FLAT (MAP tm_names (h1:hol_term list))`; `FLAT (MAP tm_names (h2:hol_term list))`] THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_ok THEN
    MAP_EVERY EXISTS_TAC [`SND (thy:thy)`; `stps:subst_step list`;
      `term_union (term_remove c2 h1) (term_remove c1 h2):hol_term list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MEM_term_remove_imp) THEN ASM_SIMP_TAC[]]);;

let CLITAUX_psa_EQ_MP = prove
 (`!h1 h2 p p' q thy.
     ((thy,h1) |- (p === q) /\ CLITAUX_psa (FST thy) (SND thy) h1 (p === q)) /\
     ((thy,h2) |- p' /\ CLITAUX_psa (FST thy) (SND thy) h2 p') /\ ACONV p p'
     ==> CLITAUX_psa (FST thy) (SND thy) (term_union h1 h2) q`,
  CLITAUX_PSA_INTRO_TAC THEN
  CLITAUX_PSA_SPEC_TAC THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy) /\ is_std_sig (FST thy)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIR; theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) p /\ hol_term_ok (FST thy) q /\ typeof q = typeof p`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps p) /\
                hol_term_ok (FST thy) (apply_steps stps q) /\
                hol_term_ok (FST thy) (apply_steps stps p')` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `apply_steps stps (p === q) = apply_steps stps p === apply_steps stps q`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC apply_steps_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps p === apply_steps stps q) =
                esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps p) ===
                esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps q)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC esubst_equation THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(esubst_sig sigma (FST thy),IMAGE (esubst sigma []) (SND thy)),
    term_union (term_image (esubst sigma []) (term_image (apply_steps stps) h1))
               (term_image (esubst sigma []) (term_image (apply_steps stps) h2)) |-
    esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC proves_EQ_MP THEN
    EXISTS_TAC `esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps p)` THEN
    EXISTS_TAC `esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps p')` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC esubst_ACONV THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC apply_steps_ACONV THEN EXISTS_TAC `FST (thy:thy)` THEN
    ASM_MESON_TAC[term_ok_welltyped];
    ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC `term_union (term_image (esubst sigma []) (term_image (apply_steps stps) h1))
                         (term_image (esubst sigma []) (term_image (apply_steps stps) h2))` THEN
  EXISTS_TAC `esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps q)` THEN
  ASM_REWRITE_TAC[FST; GSYM ALL_MEM; GSYM EX_MEM] THEN
  ASM_SIMP_TAC[hypset_ok_term_image; hypset_ok_term_union] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_union THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_ok THEN
    MAP_EVERY EXISTS_TAC [`SND (thy:thy)`; `stps:subst_step list`;
                          `term_union h1 h2:hol_term list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THEN ASM_SIMP_TAC[]]);;

let CLITAUX_psa_INST = prove
 (`!c h ilist thy.
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok (FST thy) s') /\
     (thy,h) |- c /\ CLITAUX_psa (FST thy) (SND thy) h c
     ==> CLITAUX_psa (FST thy) (SND thy) (term_image (VSUBST ilist) h) (VSUBST ilist c)`,
  CLITAUX_PSA_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `APPEND stps [VStep ilist]`]) THEN
  ASM_REWRITE_TAC[steps_ok_append; steps_ok_def] THEN
  REWRITE_TAC[apply_steps_append; apply_steps_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t ==> hol_term_ok (FST thy) (VSUBST ilist t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t has_type Tyapp (implode "bool") []
                    ==> VSUBST ilist t has_type Tyapp (implode "bool") []`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t
                    ==> hol_term_ok (FST thy) (apply_steps stps t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC
   `term_image (esubst sigma []) (term_image (apply_steps (APPEND stps [VStep ilist])) h)` THEN
  EXISTS_TAC `esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (VSUBST ilist c))` THEN
  ASM_REWRITE_TAC[FST; GSYM ALL_MEM; GSYM EX_MEM] THEN
  ASM_SIMP_TAC[hypset_ok_term_image] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps (VSUBST ilist c))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
    ASM_REWRITE_TAC[apply_steps_append; apply_steps_def] THEN
    MP_TAC(ISPECL [`h:hol_term list`; `VSUBST ilist`; `x'':hol_term`] MEM_term_image) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:hol_term` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN MATCH_MP_TAC MEM_term_image_compose_ACONV THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`; `y1:hol_term`] THEN
    ASM_SIMP_TAC[hypset_ok_term_image] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp) THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps (VSUBST ilist x''')) /\
                  apply_steps stps (VSUBST ilist x''') has_type Tyapp (implode "bool") []`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC apply_steps_has_type_Bool THEN
      EXISTS_TAC `FST (thy:thy)` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `SND (thy:thy)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_has_type_bool THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[]]]);;

let proves_concl_welltyped = prove
 (`!(thy:thy#(hol_term)list) c. thy |- c ==> welltyped c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[ALL] THEN MESON_TAC[term_ok_welltyped]);;

let CLITAUX_psa_INST_TYPE = prove
 (`!c h thy tyin.
     ALL (type_ok (FST (FST thy))) (MAP FST tyin) /\
     (thy,h) |- c /\ CLITAUX_psa (FST thy) (SND thy) h c
     ==> CLITAUX_psa (FST thy) (SND thy) (term_image (INST tyin) h) (INST tyin c)`,
  CLITAUX_PSA_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `APPEND stps [TStep tyin]`]) THEN
  ASM_REWRITE_TAC[steps_ok_append; steps_ok_def] THEN
  REWRITE_TAC[apply_steps_append; apply_steps_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t ==> hol_term_ok (FST thy) (INST tyin t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t has_type Tyapp (implode "bool") []
                    ==> INST tyin t has_type Tyapp (implode "bool") []`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INST_HAS_TYPE THEN
    EXISTS_TAC `Tyapp (implode "bool") []` THEN ASM_REWRITE_TAC[TYPE_SUBST_Bool]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t
                    ==> hol_term_ok (FST thy) (apply_steps stps t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC
   `term_image (esubst sigma []) (term_image (apply_steps (APPEND stps [TStep tyin])) h)` THEN
  EXISTS_TAC `esubst sigma (FLAT (MAP tm_names h)) (apply_steps stps (INST tyin c))` THEN
  ASM_REWRITE_TAC[FST; GSYM ALL_MEM; GSYM EX_MEM] THEN
  ASM_SIMP_TAC[hypset_ok_term_image] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps (INST tyin c))` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
    ASM_REWRITE_TAC[apply_steps_append; apply_steps_def] THEN
    MP_TAC(ISPECL [`h:hol_term list`; `INST tyin`; `x'':hol_term`] MEM_term_image) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:hol_term` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN MATCH_MP_TAC MEM_term_image_compose_ACONV THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`; `y1:hol_term`] THEN
    ASM_SIMP_TAC[hypset_ok_term_image] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp) THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MEM_term_image_imp)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps (INST tyin x''')) /\
                  apply_steps stps (INST tyin x''') has_type Tyapp (implode "bool") []`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC apply_steps_has_type_Bool THEN
      EXISTS_TAC `FST (thy:thy)` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `SND (thy:thy)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_has_type_bool THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[]]]);;

let ty_esubst_Fun_ex = prove
 (`!sig sigma a b.
     esubsts_ok sig sigma /\ (?rty. a = Tyapp (implode "fun") [b; rty])
     ==> ?rty. ty_esubst sigma a = Tyapp (implode "fun") [ty_esubst sigma b; rty]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QEXISTS_TAC "ty_esubst sigma rty" THEN ASM_MESON_TAC[ty_esubst_fun]);;

let apply_steps_welltyped_Comb = prove
 (`!sig t1 t2 stps.
     steps_ok sig stps /\ hol_term_ok sig t1 /\ hol_term_ok sig t2 /\
     welltyped (hol_Comb t1 t2)
     ==> welltyped (hol_Comb (apply_steps stps t1) (apply_steps stps t2))`,
  let pre_tac =
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `welltyped (hol_Comb (apply_steps t t1) (apply_steps t t2))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `hol_term_ok sig (apply_steps t (t1:hol_term)) /\
                  hol_term_ok sig (apply_steps t (t2:hol_term))` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC in
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [SIMP[apply_steps_def]; ALL_TAC] THEN
  NAMED_CASES_ON "h" ["ilist"; "tyin"] THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THENL
   [pre_tac THEN
    SUBGOAL_THEN `!tm. hol_term_ok sig tm ==> typeof (VSUBST ilist tm) = typeof tm`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC typeof_vsubst1 THEN EXISTS_TAC `sig:sig` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC VSUBST_WELLTYPED) THEN ASM_MESON_TAC[];
    pre_tac THEN ASM_SIMP_TAC[INST_WELLTYPED] THEN
    EXISTS_TAC `TYPE_SUBST tyin rty` THEN
    SUBGOAL_THEN `!tm. welltyped tm ==> typeof (INST tyin tm) = TYPE_SUBST tyin (typeof tm)`
    (fun th -> ASM_SIMP_TAC[th]) THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WELLTYPED_LEMMA THEN MATCH_MP_TAC INST_HAS_TYPE THEN
      EXISTS_TAC `typeof (tm:hol_term)` THEN ASM_REWRITE_TAC[GSYM WELLTYPED];
      REWRITE_TAC[TYPE_SUBST_def; MAP]]]);;

let CLITAUX_psa_MK_COMB = prove
 (`!h1 h2 l1 l2 r1 r2 thy.
     ((thy,h1) |- (l1 === r1) /\ CLITAUX_psa (FST thy) (SND thy) h1 (l1 === r1)) /\
     ((thy,h2) |- (l2 === r2) /\ CLITAUX_psa (FST thy) (SND thy) h2 (l2 === r2)) /\
     welltyped (hol_Comb l1 l2)
     ==> CLITAUX_psa (FST thy) (SND thy) (term_union h1 h2)
           (hol_Comb l1 l2 === hol_Comb r1 r2)`,
  CLITAUX_PSA_INTRO_TAC THEN CLITAUX_PSA_SPEC_TAC THEN
  SUBGOAL_THEN `theory_ok (FST (thy:thy),SND thy) /\ is_std_sig (FST thy)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIR; theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) l1 /\ hol_term_ok (FST thy) r1 /\
                typeof r1 = typeof l1 /\
                hol_term_ok (FST thy) l2 /\ hol_term_ok (FST thy) r2 /\
                typeof r2 = typeof l2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (hol_Comb r1 r2)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ASM_MESON_TAC[term_ok_welltyped];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. hol_term_ok (FST (thy:thy)) t ==> hol_term_ok (FST thy) (apply_steps stps t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `!avds t. hol_term_ok (FST (thy:thy)) t
                    ==> hol_term_ok (esubst_sig sigma (FST thy)) (esubst sigma avds t) /\
                        welltyped (esubst sigma avds t)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `SND (thy:thy)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_welltyped THEN
      MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. hol_term_ok (FST (thy:thy)) a /\ hol_term_ok (FST thy) b
                      ==> apply_steps stps (a === b) = apply_steps stps a === apply_steps stps b`
  (fun th -> RULE_ASSUM_TAC(SIMP_RULE[th]) THEN ASSUME_TAC th) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC apply_steps_equation THEN
    EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!avds a b. hol_term_ok (FST (thy:thy)) a /\ hol_term_ok (FST thy) b
                    ==> esubst sigma avds (a === b) = esubst sigma avds a === esubst sigma avds b`
  (fun th -> RULE_ASSUM_TAC(SIMP_RULE[th]) THEN ASSUME_TAC th) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_equation THEN
    EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apply_steps stps (l1 === r1) = apply_steps stps l1 === apply_steps stps r1 /\
    apply_steps stps (l2 === r2) = apply_steps stps l2 === apply_steps stps r2 /\
    esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps l1 === apply_steps stps r1) =
    esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps l1) ===
    esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps r1) /\
    esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps l2 === apply_steps stps r2) =
    esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps l2) ===
    esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps r2)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!avds t. hol_term_ok (FST (thy:thy)) t
                    ==> typeof (esubst sigma avds t) = ty_esubst sigma (typeof t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC typeof_esubst THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (hol_Comb (apply_steps stps l1) (apply_steps stps l2)) /\
                welltyped (hol_Comb (apply_steps stps r1) (apply_steps stps r2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC apply_steps_welltyped_Comb THEN
    EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!avds1 avds2.
      welltyped (hol_Comb (esubst sigma avds1 (apply_steps stps l1))
                          (esubst sigma avds2 (apply_steps stps l2)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ASSUME `welltyped (hol_Comb (apply_steps stps l1) (apply_steps stps (l2:hol_term)))`) THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC ty_esubst_Fun_ex THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(esubst_sig sigma (FST thy),IMAGE (esubst sigma []) (SND thy)),
    term_union (term_image (esubst sigma []) (term_image (apply_steps stps) h1))
               (term_image (esubst sigma []) (term_image (apply_steps stps) h2)) |-
    hol_Comb (esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps l1))
             (esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps l2)) ===
    hol_Comb (esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps r1))
             (esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps r2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC proves_MK_COMB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `esubst sigma (FLAT (MAP tm_names (term_union h1 h2)))
      (apply_steps stps (hol_Comb l1 l2 === hol_Comb r1 r2)) =
    hol_Comb (esubst sigma (FLAT (MAP tm_names (term_union h1 h2))) (apply_steps stps l1))
             (esubst sigma (FLAT (MAP tm_names (term_union h1 h2))) (apply_steps stps l2)) ===
    hol_Comb (esubst sigma (FLAT (MAP tm_names (term_union h1 h2))) (apply_steps stps r1))
             (esubst sigma (FLAT (MAP tm_names (term_union h1 h2))) (apply_steps stps r2))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!a b. hol_term_ok (FST (thy:thy)) a /\ hol_term_ok (FST thy) b
                        ==> apply_steps stps (hol_Comb a b) =
                            hol_Comb (apply_steps stps a) (apply_steps stps b)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC apply_steps_comb THEN
      EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!avds a b. hol_term_ok (FST (thy:thy)) a /\ hol_term_ok (FST thy) b
                        ==> esubst sigma avds (hol_Comb a b) =
                            hol_Comb (esubst sigma avds a) (esubst sigma avds b)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_comb THEN
      EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[hol_term_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!avds1 avds2.
      welltyped (hol_Comb (esubst sigma avds1 (apply_steps stps r1))
                          (esubst sigma avds2 (apply_steps stps r2)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ASSUME `welltyped (hol_Comb (apply_steps stps r1) (apply_steps stps (r2:hol_term)))`) THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC ty_esubst_Fun_ex THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `typeof (apply_steps stps r1) = typeof (apply_steps stps (l1:hol_term))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC apply_steps_typeof_eq THEN EXISTS_TAC `FST (thy:thy)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV THEN
  EXISTS_TAC `term_union (term_image (esubst sigma []) (term_image (apply_steps stps) h1))
                         (term_image (esubst sigma []) (term_image (apply_steps stps) h2))` THEN
  EXISTS_TAC
   `hol_Comb (esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps l1))
             (esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps l2)) ===
    hol_Comb (esubst sigma (FLAT (MAP tm_names h1)) (apply_steps stps r1))
             (esubst sigma (FLAT (MAP tm_names h2)) (apply_steps stps r2))` THEN
  ASM_REWRITE_TAC[FST; GSYM ALL_MEM; GSYM EX_MEM] THEN
  ASM_SIMP_TAC[hypset_ok_term_image; hypset_ok_term_union] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[welltyped_equation; EQUATION_HAS_TYPE_BOOL; typeof_def] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC ACONV_equation THEN ASM_REWRITE_TAC[ACONV_COMB] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_union THEN
    MAP_EVERY EXISTS_TAC [`FST (thy:thy)`; `SND (thy:thy)`] THEN ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CLITAUX_psa_hyp_ok THEN
    MAP_EVERY EXISTS_TAC [`SND (thy:thy)`; `stps:subst_step list`;
                          `term_union h1 h2:hol_term list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_term_union_imp) THEN ASM_SIMP_TAC[]]);;

let CLITAUX_psa_Refl = prove
 (`!t thy.
     theory_ok thy /\ hol_term_ok (FST thy) t
     ==> CLITAUX_psa (FST thy) (SND thy) [] (t === t)`,
  REWRITE_TAC[CLITAUX_psa_def; PAIR] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[term_image_nil; MAP; FLAT] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (apply_steps stps t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[apply_steps_term_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `apply_steps stps ((t:hol_term) === t) =
                apply_steps stps t === apply_steps stps t` SUBST1_TAC THENL
   [ASM_MESON_TAC[apply_steps_equation]; ALL_TAC] THEN
  SUBGOAL_THEN `esubst sigma [] (apply_steps stps t === apply_steps stps (t:hol_term)) =
                esubst sigma [] (apply_steps stps t) === esubst sigma [] (apply_steps stps t)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[esubst_equation; theory_ok_sig]; ALL_TAC] THEN
  MATCH_MP_TAC proves_REFL THEN REWRITE_TAC[FST] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[theory_ok_esubst_axs; PAIR]; ASM_MESON_TAC[esubst_term_ok; PAIR]]);;

let CLITAUX_psa_Axioms = prove
 (`!c thy.
     theory_ok thy /\ c IN SND thy
     ==> CLITAUX_psa (FST thy) (SND thy) [] c`,
  REWRITE_TAC[CLITAUX_psa_def; PAIR] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[term_image_nil; MAP; FLAT] THEN
  MATCH_MP_TAC axiom_steps_derivable THEN ASM_MESON_TAC[PAIR]);;

(* HOL4: Finalise proves_substitutable_aux *)
let proves_substitutable_aux = prove
 (`!sig axs h c.
     theory_ok (sig,axs) /\
     ((sig,axs),h) |- c
     ==> !sigma steps.
           (!ax. ax IN axs ==> no_var_collapse sigma ax) /\
           esubsts_ok sig sigma /\
           steps_ok sig steps
           ==> ((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),
                term_image (esubst sigma []) (term_image (apply_steps steps) h)) |-
               esubst sigma (FLAT (MAP tm_names h)) (apply_steps steps c)`,
  SUBGOAL_THEN
   `!a (c:hol_term). a |- c ==> CLITAUX_psa (FST (FST a)) (SND (FST a)) (SND a) c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC proves_strongind THEN REWRITE_TAC[FST; SND] THEN
    REWRITE_TAC[CLITAUX_psa_Abs; CLITAUX_psa_Assume; CLITAUX_psa_Beta;
                CLITAUX_psa_DeductAntisym; CLITAUX_psa_EQ_MP; CLITAUX_psa_INST;
                CLITAUX_psa_INST_TYPE; CLITAUX_psa_MK_COMB; CLITAUX_psa_Refl;
                CLITAUX_psa_Axioms];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`((sig,axs),h):thy#(hol_term)list`; `c:hol_term`]) THEN
    ASM_REWRITE_TAC[CLITAUX_psa_def; FST; SND] THEN ASM_MESON_TAC[]]);;

let apply_steps_id = prove
 (`apply_steps [] = (\p. p)`,
  REWRITE_TAC[FUN_EQ_THM; apply_steps_def]);;

let proves_substitutable = prove
 (`!sigma sig axs h c.
     theory_ok (sig,axs) /\ ((sig,axs),h) |- c /\
     esubsts_ok sig sigma /\
     (!ax. ax IN axs ==> no_var_collapse sigma ax)
     ==> ((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),
          term_image (esubst sigma []) h) |-
         esubst sigma (FLAT (MAP tm_names h)) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sig:sig`; `axs:hol_term->bool`; `h:(hol_term)list`; `c:hol_term`]
    proves_substitutable_aux) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `[]:(subst_step)list`]) THEN
  ASM_REWRITE_TAC[steps_ok_def; apply_steps_id; term_image_id]);;
