(* ========================================================================= *)
(* holExtension: port of HOL4 candle/standard/semantics/holExtensionScript   *)
(* .sml (CakeML v3479).  Soundness of the context extension rules: any model *)
(* of a context can be extended to a model of the context obtained by        *)
(* applying one of the non-axiomatic context updates.  Headline:             *)
(* extends_consistent (statement: candle_logic_statement.ml).                *)
(*                                                                           *)
(* Notes on the rendering: the header of holSemantics.ml; besides:           *)
(* - HOL4's Overload sound_update is sound_update0 mem; the context          *)
(*   Overloads (thyof, sigof, tysof, tmsof, axsof) are written out as in     *)
(*   holSyntax.ml, and HOL4's ConstDef x t as hol_ConstSpec [(x,t)]           *)
(*   (hol_Var x (typeof t) === t).                                           *)
(* - HOL4's variables abs and rep (abs is a HOL Light interface name) are    *)
(*   abs_name and rep_name, as in holSyntax.ml.                              *)
(* - HOL4's eqsh (a definition eqsh = $= that shields two equations from     *)
(*   simp inside new_type_definition_correct, deleted at the end of the      *)
(*   theory) is not needed by these proofs and not defined.                  *)
(* - HOL4 writes the type valuation of a constant's type arguments l as      *)
(*   K boolset =++ REVERSE (ZIP (vars,l)); here ZIP vars l (HOL Light's ZIP, *)
(*   curried); every use has LENGTH l = LENGTH vars.                         *)
(* - Local helpers that are not HOL4 theorems are CSEMAUX_.                  *)
(* ========================================================================= *)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holSoundness.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: Definition sound_update_def *)
let sound_update0_def = cake_def
  `sound_update0 (mem:U->U->bool) ctxt upd <=>
     !i. models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   ctxt)))
         ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                            alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                  models0 mem i'
                    ((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd))
                                            (CONS upd ctxt))))`;;

(* The type valuation built from a list of values for the sorted type      *)
(* variables (HOL4 writes K boolset =++ REVERSE (ZIP (vars,l))): on the     *)
(* variables it gives the values.                                           *)
let CSEMAUX_UPDATE_LIST_ZIP_MAP = prove
 (`!(f:A->B) g vars x.
     (g =++ REVERSE (ZIP vars (MAP f vars))) x = if MEM x vars then f x else g x`,
  REWRITE_TAC[APPLY_UPDATE_LIST_ALOOKUP; REVERSE_REVERSE] THEN
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ZIP; ALOOKUP_def; MEM; option_CASE] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN MESON_TAC[]);;
let new_constant_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt name ty.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                       ctxt))) /\
     ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) ty
     ==> sound_update0 mem ctxt (hol_NewConst name ty)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[sound_update0_def; MAP; FLAT; types_of_upd_def; consts_of_upd_def;
               axexts_of_upd_def; conexts_of_upd_def; APPEND; alist_to_fmap_thm] THEN
   ABBREV_TAC `tys = alist_to_fmap (FLAT (MAP types_of_upd ctxt))` THEN
   ABBREV_TAC `tms = alist_to_fmap (FLAT (MAP consts_of_upd ctxt))` THEN
   ABBREV_TAC `axs = set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))` THEN
   STRIP_TAC THEN X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  ABBREV_TAC `vars = MAP implode (STRING_SORT (MAP explode (hol_tyvars ty)))` THEN
   SUBGOAL_THEN `!x. MEM x vars <=> MEM x (hol_tyvars ty)` ASSUME_TAC THENL
    [EXPAND_TAC "vars" THEN
     REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode];
     ALL_TAC] THEN
   EXISTS_TAC
    `(FST (i:(mlstring->U list->U)#(mlstring->U list->U)),
      (name =+ (\l. @v. (mem:U->U->bool) v
                  (typesem (FST i) (K (setSpec_two mem) =++ REVERSE (ZIP vars l)) ty)))
      (SND i))` THEN
   SUBGOAL_THEN `is_std_sig (tys:tysig,tms:tmsig)` ASSUME_TAC THENL
    [ASM_MESON_TAC[theory_ok_sig; FST]; ALL_TAC] THEN
   SUBGOAL_THEN `~(name = implode "=")` ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[is_std_sig_def]) THEN ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT];
     ALL_TAC] THEN
   SUBGOAL_THEN `equal_on (tys:tysig,tms:tmsig) i
      (FST (i:(mlstring->U list->U)#(mlstring->U list->U)),
       (name =+ (\l. @v. (mem:U->U->bool) v
                  (typesem (FST i) (K (setSpec_two mem) =++ REVERSE (ZIP vars l)) ty)))
       (SND i))` ASSUME_TAC THENL
    [REWRITE_TAC[equal_on_def; APPLY_UPDATE_THM] THEN ASM_MESON_TAC[];
     ASM_REWRITE_TAC[]] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "is_interpretation0" with _ -> false))
         (concl th))) THEN
   REWRITE_TAC[models0_def] THEN REPEAT CONJ_TAC THENL
   [(* is_interpretation *)
    UNDISCH_TAC `is_interpretation0 (mem:U->U->bool) (tys,tms) i` THEN
   REWRITE_TAC[is_interpretation0_def; is_term_assignment0_def; FEVERY_ALL_FLOOKUP;
               FLOOKUP_UPDATE] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY X_GEN_TAC [`k:mlstring`; `tk:hol_type`] THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[] THEN
     X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                     (K (setSpec_two (mem:U->U->bool)) =++ REVERSE (ZIP vars (MAP tau vars))) ty =
                   typesem (FST i) tau ty` SUBST1_TAC THENL
      [MATCH_MP_TAC typesem_tyvars THEN ASM_SIMP_TAC[CSEMAUX_UPDATE_LIST_ZIP_MAP];
       ALL_TAC] THEN
     CONV_TAC SELECT_CONV THEN MATCH_MP_TAC(UNDISCH typesem_inhabited) THEN
     EXISTS_TAC `tys:tysig` THEN ASM_REWRITE_TAC[];
     DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `tk:hol_type`]) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]];
    (* is_std_interpretation *)
    UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
   REWRITE_TAC[is_std_interpretation0_def; interprets0_def; APPLY_UPDATE_THM] THEN
   ASM_REWRITE_TAC[];
    (* the axioms *)
    X_GEN_TAC `p:hol_term` THEN DISCH_TAC THEN
   MATCH_MP_TAC satisfies_extend THEN
   MAP_EVERY EXISTS_TAC [`tys:tysig`; `tms:tmsig`] THEN
   ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL; ALL] THEN
   SUBGOAL_THEN `hol_term_ok (tys:tysig,tms:tmsig) p` ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def]) THEN ASM_MESON_TAC[FST; SND]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC satisfies_sig THEN
   EXISTS_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN
   ASM_SIMP_TAC[ALL]]);;
(* The constant interpretation updated along a specification (HOL4 writes  *)
(* tmaof i =++ MAP (\(s,t). (s, ..)) (REVERSE eqs)): looked up in eqs.     *)
let CSEMAUX_UPDATE_LIST_MAP_REVERSE = prove
 (CASE_TERM
  `!(f:A->C) (g:B->C) (eqs:(A#B)list) k.
     (f =++ MAP (\(s,t). (s, g t)) (REVERSE eqs)) k =
     match ALOOKUP eqs k with NONE -> f k | SOME t -> g t`,
  REWRITE_TAC[APPLY_UPDATE_LIST_ALOOKUP; MAP_REVERSE; REVERSE_REVERSE; ALOOKUP_MAP; o_THM] THEN
  REPEAT GEN_TAC THEN CASES_ON `ALOOKUP (eqs:(A#B)list) k` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE]);;

(* The value of a closed term with tvars t SUBSET hol_tyvars (typeof t) under   *)
(* the type valuation of HOL4's new_specification_correct.                  *)
let CSEMAUX_termsem_closed_tyvars = prove
 (`!G (i:(mlstring->U list->U)#(mlstring->U list->U)) t tau sigma.
     hol_term_ok G t /\ CLOSED t /\
     (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t)))
     ==> termsem0 (mem:U->U->bool) (SND G) i
           (K (setSpec_two mem) =++
            REVERSE (ZIP (MAP implode (STRING_SORT (MAP explode (hol_tyvars (typeof t)))))
                         (MAP tau (MAP implode (STRING_SORT (MAP explode (hol_tyvars (typeof t))))))),
            ARB) t =
         termsem0 mem (SND G) i (tau,sigma) t`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) (SND (G:sig)) i (tau,ARB) t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC termsem_tyfrees THEN EXISTS_TAC `G:sig` THEN
    ASM_REWRITE_TAC[CSEMAUX_UPDATE_LIST_ZIP_MAP] THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode] THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC termsem_frees THEN RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[term_ok_welltyped]]);;

(* Lookup of a variable in the inverted substitution of a specification. *)
let CSEMAUX_ALOOKUP_ilist = prove
 (CASE_TERM
  `!eqs x ty.
     ALL_DISTINCT (MAP FST eqs)
     ==> ALOOKUP (MAP (\(s',s). (s,s'))
                   (MAP (\(s,t). (hol_Const s (typeof t), hol_Var s (typeof t))) eqs))
                 (hol_Var x ty) =
         match ALOOKUP eqs x with
           NONE -> NONE
         | SOME t -> if typeof t = ty then SOME (hol_Const x ty) else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_def; option_CASE] THEN
  PAIR_CASES_ON `h:mlstring#hol_term` THEN
  REWRITE_TAC[MAP; ALOOKUP_def; ALL_DISTINCT; injectivity "hol_term"] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ALOOKUP_def; injectivity "hol_term"] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `ALL_DISTINCT (MAP FST (t:(mlstring#hol_term)list))`)] ORELSE ALL_TAC) THEN
  ASM_CASES_TAC `h0:mlstring = x` THEN ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `ALOOKUP (t:(mlstring#hol_term)list) x = NONE` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[ALOOKUP_NONE]; ALL_TAC] THEN
  REWRITE_TAC[option_CASE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let new_specification_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt eqs prop.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                       ctxt))) /\
     ((((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                               ctxt))),
       MAP (\(s,t). hol_Var s (typeof t) === t) eqs) |- prop) /\
     ALL (\t. CLOSED t /\ (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))))
         (MAP SND eqs) /\
     (!x ty. VFREE_IN (hol_Var x ty) prop ==> MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
     (!s. MEM s (MAP FST eqs)
          ==> ~(s IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))) /\
     ALL_DISTINCT (MAP FST eqs)
     ==> sound_update0 mem ctxt (hol_ConstSpec eqs prop)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[sound_update0_def; MAP; FLAT; types_of_upd_def; consts_of_upd_def;
               axexts_of_upd_def; conexts_of_upd_def; APPEND; LET_DEF; LET_END_DEF;
               alist_to_fmap_APPEND; set_of_list] THEN
   ABBREV_TAC `tys = alist_to_fmap (FLAT (MAP types_of_upd ctxt))` THEN
   ABBREV_TAC `tms = alist_to_fmap (FLAT (MAP consts_of_upd ctxt))` THEN
   ABBREV_TAC `axs = set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))` THEN
   STRIP_TAC THEN X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
   SUBGOAL_THEN `is_std_sig (tys:tysig,tms:tmsig)` ASSUME_TAC THENL
    [ASM_MESON_TAC[theory_ok_sig; FST]; ALL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP (UNDISCH proves_sound)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
   REWRITE_TAC[FST; SND; ALL] THEN STRIP_TAC THEN
   SUBGOAL_THEN
    `!s t. MEM (s,t) eqs
           ==> hol_term_ok (tys,tms) t /\ CLOSED t /\
               (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))) /\
               hol_term_ok (tys,tms) (hol_Var s (typeof t) === t)`
    ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN DISCH_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM]) THEN
     SUBGOAL_THEN `hol_term_ok (tys,tms) (hol_Var s (typeof t) === t)` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `hol_Var s (typeof t) === t` o
                     check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> try fst(dest_const t) = "hol_term_ok"
                                                with _ -> false)) (concl th) &&
                       can (find_term (fun t -> try fst(dest_const t) = "equation"
                                                with _ -> false)) (concl th))) THEN
       ANTS_TAC THENL [EXISTS_TAC `s:mlstring` THEN EXISTS_TAC `t:hol_term` THEN
                       ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC;
                       SIMP_TAC[]];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[term_ok_equation]; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `t:hol_term` o
                   check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "CLOSED"
                                                     with _ -> false)) (concl th))) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[SND]; SIMP_TAC[]];
     ALL_TAC] THEN
  ABBREV_TAC `gm = SND (i:(mlstring->U list->U)#(mlstring->U list->U)) =++
     MAP (\(s,t). (s, \l. termsem0 (mem:U->U->bool) tms i
                            (K (setSpec_two mem) =++
                             REVERSE (ZIP (MAP implode (STRING_SORT (MAP explode
                                                          (hol_tyvars (typeof t))))) l),
                             ARB) t))
         (REVERSE eqs)` THEN
   SUBGOAL_THEN
    `(!k. ALOOKUP eqs k = NONE ==> gm k = SND (i:(mlstring->U list->U)#(mlstring->U list->U)) k) /\
     (!k t. ALOOKUP eqs k = SOME t
            ==> gm k = \l. termsem0 (mem:U->U->bool) tms i
                             (K (setSpec_two mem) =++
                              REVERSE (ZIP (MAP implode (STRING_SORT (MAP explode
                                                           (hol_tyvars (typeof t))))) l),
                              ARB) t)`
    STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "gm" THEN REWRITE_TAC[CSEMAUX_UPDATE_LIST_MAP_REVERSE] THEN
     SIMP_TAC[option_CASE];
     ALL_TAC] THEN
  EXISTS_TAC `(FST (i:(mlstring->U list->U)#(mlstring->U list->U)), gm:mlstring->U list->U)` THEN
   SUBGOAL_THEN `!k. k IN FDOM (tms:tmsig) ==> ALOOKUP (eqs:(mlstring#hol_term)list) k = NONE`
     ASSUME_TAC THENL [REWRITE_TAC[ALOOKUP_NONE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `ALOOKUP (eqs:(mlstring#hol_term)list) (implode "=") = NONE` ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[is_std_sig_def]) THEN
     ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT; FST; SND];
     ALL_TAC] THEN
   SUBGOAL_THEN `equal_on (tys:tysig,tms:tmsig) i
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U)), gm:mlstring->U list->U)`
     ASSUME_TAC THENL
    [REWRITE_TAC[equal_on_def] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "is_interpretation0" with _ -> false))
         (concl th))) THEN
   REWRITE_TAC[models0_def] THEN REPEAT CONJ_TAC THENL
   [(* is_interpretation *)
    MP_TAC(ASSUME `is_interpretation0 (mem:U->U->bool) (tys,tms) i`) THEN
   REWRITE_TAC[is_interpretation0_def; is_term_assignment0_def; FEVERY_ALL_FLOOKUP;
               FLOOKUP_FUNION; ALOOKUP_EQ_FLOOKUP; ALOOKUP_MAP; o_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY X_GEN_TAC [`k:mlstring`; `tk:hol_type`] THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   CASES_ON `ALOOKUP (eqs:(mlstring#hol_term)list) k` THEN
   REWRITE_TAC[OPTION_MAP_DEF; option_CASE] THENL
     [(* a constant of ctxt *)
      DISCH_TAC THEN
   SUBGOAL_THEN `gm (k:mlstring) = SND (i:(mlstring->U list->U)#(mlstring->U list->U)) k`
     SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `tk:hol_type`]) THEN ASM_REWRITE_TAC[];
      (* a new constant *)
      REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
   SUBGOAL_THEN `MEM (k:mlstring, a:hol_term) eqs` ASSUME_TAC THENL
    [ASM_MESON_TAC[ALOOKUP_MEM]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
     (ASSUME `ALOOKUP (eqs:(mlstring#hol_term)list) k = SOME a`)]) THEN
   BETA_TAC THEN
   MP_TAC(ISPECL [`tys:tysig`; `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                  `tau:mlstring->U`] (UNDISCH term_valuation_exists)) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[is_interpretation0_def; FST]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `sigma:mlstring#hol_type->U`) THEN
   MP_TAC(ISPECL [`(tys:tysig,tms:tmsig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                  `a:hol_term`; `tau:mlstring->U`; `sigma:mlstring#hol_type->U`]
            CSEMAUX_termsem_closed_tyvars) THEN
   REWRITE_TAC[SND] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
   MATCH_MP_TAC(UNDISCH termsem_typesem_matchable) THEN
   MAP_EVERY EXISTS_TAC [`(tys:tysig,tms:tmsig)`;
                         `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                         `tau:mlstring->U`] THEN
   ASM_REWRITE_TAC[FST; SND] THEN
   ASM_MESON_TAC[is_std_interpretation_is_type]];
    (* is_std_interpretation *)
    UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
   REWRITE_TAC[is_std_interpretation0_def; interprets0_def] THEN
   SUBGOAL_THEN `gm (implode "=") =
                 SND (i:(mlstring->U list->U)#(mlstring->U list->U)) (implode "=")`
     SUBST1_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    (* the axioms *)
    SUBGOAL_THEN
    `!k. k IN FDOM (alist_to_fmap (MAP (\(s,t). (s,typeof t)) (eqs:(mlstring#hol_term)list))) <=>
         MEM k (MAP FST eqs)` ASSUME_TAC THENL
    [REWRITE_TAC[FDOM_alist_to_fmap; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM] THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ; FST] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `(tms:tmsig) SUBMAP FUNION (alist_to_fmap (MAP (\(s,t). (s,typeof t)) eqs)) tms`
     ASSUME_TAC THENL
    [MATCH_MP_TAC SUBMAP_FUNION THEN DISJ2_TAC THEN REWRITE_TAC[SUBMAP_REFL; IN_DISJOINT] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `p:hol_term` THEN STRIP_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC satisfies_extend THEN
     MAP_EVERY EXISTS_TAC [`tys:tysig`; `tms:tmsig`] THEN
     ASM_REWRITE_TAC[SUBMAP_REFL; ALL] THEN
     SUBGOAL_THEN `hol_term_ok (tys:tysig,tms:tmsig) p` ASSUME_TAC THENL
      [RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def]) THEN ASM_MESON_TAC[FST; SND]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC satisfies_sig THEN
     EXISTS_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN
     ASM_SIMP_TAC[ALL]] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
   ABBREV_TAC `tms' = FUNION (alist_to_fmap (MAP (\(s,t). (s,typeof t))
                                 (eqs:(mlstring#hol_term)list))) tms` THEN
   ABBREV_TAC `ilist = MAP (\(s,t). (hol_Const s (typeof t), hol_Var s (typeof t)))
                           (eqs:(mlstring#hol_term)list)` THEN
   REWRITE_TAC[satisfies0_def; ALL] THEN
   X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN STRIP_TAC THEN
   SUBGOAL_THEN
    `!x t. ALOOKUP (eqs:(mlstring#hol_term)list) x = SOME t
           ==> termsem0 (mem:U->U->bool) tms'
                 (FST (i:(mlstring->U list->U)#(mlstring->U list->U)),gm) v
                 (hol_Const x (typeof t)) =
               termsem0 mem tms i v t`
    ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `MEM (x:mlstring, t:hol_term) eqs` ASSUME_TAC THENL
      [ASM_MESON_TAC[ALOOKUP_MEM]; ALL_TAC] THEN
     SUBGOAL_THEN `FLOOKUP (tms':tmsig) x = SOME (typeof t)` ASSUME_TAC THENL
      [EXPAND_TAC "tms'" THEN
       ASM_REWRITE_TAC[FLOOKUP_FUNION; ALOOKUP_EQ_FLOOKUP; ALOOKUP_MAP; o_THM;
                       OPTION_MAP_DEF; option_CASE];
       ALL_TAC] THEN
     REWRITE_TAC[termsem0_def] THEN
     MP_TAC(ISPECL [`tms':tmsig`;
                    `(FST (i:(mlstring->U list->U)#(mlstring->U list->U)),gm:mlstring->U list->U)`;
                    `x:mlstring`; `typeof t`; `typeof t`; `[]:(hol_type#hol_type)list`]
              instance_def) THEN
     ASM_REWRITE_TAC[TYPE_SUBST_NIL] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
     SUBGOAL_THEN `(typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                      (FST (v:(mlstring->U)#(mlstring#hol_type->U))) o
                    TYPE_SUBST [] o Tyvar) = FST v`
       SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM; o_THM; TYPE_SUBST_NIL; typesem_def]; ALL_TAC] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
       (ASSUME `ALOOKUP (eqs:(mlstring#hol_term)list) x = SOME t`)]) THEN
     BETA_TAC THEN
     MP_TAC(ISPECL [`(tys:tysig,tms:tmsig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                    `t:hol_term`; `FST (v:(mlstring->U)#(mlstring#hol_type->U))`;
                    `SND (v:(mlstring->U)#(mlstring#hol_type->U))`]
              CSEMAUX_termsem_closed_tyvars) THEN
     REWRITE_TAC[SND; PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty`
     ASSUME_TAC THENL
    [EXPAND_TAC "ilist" THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
     MESON_TAC[has_type_rules];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`prop:hol_term`; `ilist:(hol_term#hol_term)list`] termsem_VSUBST) THEN
   ANTS_TAC THENL
    [ASM_MESON_TAC[term_ok_welltyped]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
   ABBREV_TAC `vv = (FST (v:(mlstring->U)#(mlstring#hol_type->U)),
                     SND v =++ MAP ((dest_var ## termsem0 (mem:U->U->bool) tms'
                                       (FST (i:(mlstring->U list->U)#(mlstring->U list->U)),
                                        gm:mlstring->U list->U) v) o
                                    (\(s',s). (s,s'))) (REVERSE ilist))` THEN
   SUBGOAL_THEN (CASE_TERM
    `!x ty. SND (vv:(mlstring->U)#(mlstring#hol_type->U)) (x,ty) =
            match ALOOKUP (eqs:(mlstring#hol_term)list) x with
              NONE -> SND (v:(mlstring->U)#(mlstring#hol_type->U)) (x,ty)
            | SOME t -> if typeof t = ty
                        then termsem0 (mem:U->U->bool) tms'
                               (FST (i:(mlstring->U list->U)#(mlstring->U list->U)),
                                gm:mlstring->U list->U) v (hol_Const x ty)
                        else SND v (x,ty)`)
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "vv" THEN REWRITE_TAC[SND] THEN
   QSPECL_THEN ["ilist"; "SND v"; "termsem0 mem tms' (FST i,gm) v"; "x"; "ty"] MP_TAC
     CSEMAUX_UPDATE_LIST_dest_var THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
   EXPAND_TAC "ilist" THEN ASM_SIMP_TAC[CSEMAUX_ALOOKUP_ilist] THEN
   CASES_ON `ALOOKUP (eqs:(mlstring#hol_term)list) x` THEN REWRITE_TAC[option_CASE] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_CASE];
      SUBGOAL_THEN `FST (vv:(mlstring->U)#(mlstring#hol_type->U)) =
                 FST (v:(mlstring->U)#(mlstring#hol_type->U))` ASSUME_TAC THENL
    [EXPAND_TAC "vv" THEN REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool)
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))` ASSUME_TAC THENL
    [ASM_MESON_TAC[is_std_interpretation_is_type]; ALL_TAC] THEN
   SUBGOAL_THEN `is_valuation0 (mem:U->U->bool) tys
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) vv` ASSUME_TAC THENL
    [UNDISCH_TAC `is_valuation0 (mem:U->U->bool) tys
                    (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) v` THEN
     REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN DISCH_TAC THEN
     CASES_ON `ALOOKUP (eqs:(mlstring#hol_term)list) x` THEN ASM_SIMP_TAC[option_CASE] THEN
     COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
       (ASSUME `ALOOKUP (eqs:(mlstring#hol_term)list) x = SOME a`)]) THEN
     MATCH_MP_TAC(UNDISCH termsem_typesem_matchable) THEN
     MAP_EVERY EXISTS_TAC [`(tys:tysig,tms:tmsig)`;
                           `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                           `FST (v:(mlstring->U)#(mlstring#hol_type->U))`] THEN
     ASM_REWRITE_TAC[FST; SND; is_valuation0_def; is_term_valuation0_def] THEN
     ASM_MESON_TAC[ALOOKUP_MEM];
     ALL_TAC] THEN
      SUBGOAL_THEN
    `ALL (\t. termsem0 (mem:U->U->bool) tms i vv t = setSpec_true mem)
         (MAP (\(s,t). hol_Var s (typeof t) === t) (eqs:(mlstring#hol_term)list))`
    ASSUME_TAC THENL
    [REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
     X_GEN_TAC `e:hol_term` THEN
     DISCH_THEN(X_CHOOSE_THEN `s:mlstring` (X_CHOOSE_THEN `t:hol_term` STRIP_ASSUME_TAC)) THEN
     FIRST_X_ASSUM SUBST1_TAC THEN
     SUBGOAL_THEN `ALOOKUP (eqs:(mlstring#hol_term)list) s = SOME t` ASSUME_TAC THENL
      [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MP_TAC(ISPECL [`(tys:tysig,tms:tmsig)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                    `vv:(mlstring->U)#(mlstring#hol_type->U)`;
                    `hol_Var s (typeof t)`; `t:hol_term`; `tms:tmsig`]
              (UNDISCH termsem_equation)) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[is_structure0_def; SND; FST] THEN ASM_MESON_TAC[];
       DISCH_THEN SUBST1_TAC] THEN
     REWRITE_TAC[UNDISCH boolean_eq_true; CONJUNCT1 termsem0_def] THEN
     ASM_REWRITE_TAC[option_CASE] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
       (ASSUME `ALOOKUP (eqs:(mlstring#hol_term)list) s = SOME t`)]) THEN
     MATCH_MP_TAC termsem_frees THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `CLOSED t /\ welltyped t` MP_TAC THENL
      [ASM_MESON_TAC[term_ok_welltyped]; SIMP_TAC[CLOSED_def]];
     ALL_TAC] THEN
   SUBGOAL_THEN `termsem0 (mem:U->U->bool) tms'
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U)),gm:mlstring->U list->U)
                   vv prop = termsem0 mem tms i vv prop`
     SUBST1_TAC THENL
    [TRANS_TAC EQ_TRANS `termsem0 (mem:U->U->bool) tms
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U)),gm:mlstring->U list->U)
                   vv prop` THEN CONJ_TAC THENL
      [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] termsem_extend) THEN
       EXISTS_TAC `tys:tysig` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "tms'" THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC termsem_sig THEN EXISTS_TAC `(tys:tysig,tms:tmsig)` THEN
       ASM_REWRITE_TAC[SND]];
     ALL_TAC] THEN
   UNDISCH_TAC `entails0 (mem:U->U->bool)
      (((tys,tms),axs),MAP (\(s,t). hol_Var s (typeof t) === t) (eqs:(mlstring#hol_term)list))
      prop` THEN
   REWRITE_TAC[entails0_def] THEN
   DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
              last o CONJUNCTS) THEN
   ANTS_TAC THENL [REWRITE_TAC[models0_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[satisfies0_def; FST; SND] THEN
   DISCH_THEN(MP_TAC o SPEC `vv:(mlstring->U)#(mlstring#hol_type->U)`) THEN
   ASM_REWRITE_TAC[]]]);;
(* HOL4 ConstDef x t is ConstSpec [(x,t)] (Var x (typeof t) === t)          *)
(* (holSyntaxExtra_p1.ml header).                                           *)
let new_definition_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt name tm.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                       ctxt))) /\
     hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) tm /\
     ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     CLOSED tm /\
     set_of_list (tvars tm) SUBSET set_of_list (hol_tyvars (typeof tm))
     ==> sound_update0 mem ctxt
           (hol_ConstSpec [(name,tm)] (hol_Var name (typeof tm) === tm))`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(UNDISCH new_specification_correct) THEN
  ASM_REWRITE_TAC[MAP; ALL; MEM; ALL_DISTINCT] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST; CLOSED_def]) THEN
  ASM_REWRITE_TAC[CLOSED_def; vfree_in_equation; VFREE_IN_def; distinctness "hol_term";
                  injectivity "hol_term"; PAIR_EQ] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ABBREV_TAC `thy = ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                  (conexts_of_upd upd)) ctxt)))` THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) tm` ASSUME_TAC THENL
   [EXPAND_TAC "thy" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC proves_ASSUME THEN
  ASM_SIMP_TAC[EQUATION_HAS_TYPE_BOOL; term_ok_equation; hol_term_ok_def; WELLTYPED_CLAUSES;
               typeof_def] THEN
  ASM_MESON_TAC[term_ok_welltyped; term_ok_type_ok]);;
let new_type_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt name arity.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                       ctxt))) /\
     ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt))))
     ==> sound_update0 mem ctxt (hol_NewType name arity)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[sound_update0_def; MAP; FLAT; types_of_upd_def; consts_of_upd_def;
              axexts_of_upd_def; conexts_of_upd_def; APPEND; alist_to_fmap_thm] THEN
  ABBREV_TAC `tys = alist_to_fmap (FLAT (MAP types_of_upd ctxt))` THEN
  ABBREV_TAC `tms = alist_to_fmap (FLAT (MAP consts_of_upd ctxt))` THEN
  ABBREV_TAC `axs = set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                   (conexts_of_upd upd)) ctxt))` THEN
  STRIP_TAC THEN X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
  EXISTS_TAC `((name =+ K (setSpec_two (mem:U->U->bool)))
                 (FST (i:(mlstring->U list->U)#(mlstring->U list->U))), SND i)` THEN
  SUBGOAL_THEN `is_std_sig (tys:tysig,tms:tmsig)` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_sig; FST]; ALL_TAC] THEN
  SUBGOAL_THEN `~(name = implode "fun") /\ ~(name = implode "bool")` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[is_std_sig_def]) THEN ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN FDOM (tys:tysig)
                    ==> (name =+ K (setSpec_two (mem:U->U->bool)))
                          (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) k = FST i k`
    ASSUME_TAC THENL [REWRITE_TAC[APPLY_UPDATE_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `equal_on (tys:tysig,tms:tmsig) i
      ((name =+ K (setSpec_two (mem:U->U->bool)))
         (FST (i:(mlstring->U list->U)#(mlstring->U list->U))), SND i)`
    ASSUME_TAC THENL
   [REWRITE_TAC[equal_on_def] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[models0_def]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "is_interpretation0" with _ -> false))
        (concl th))) THEN
  REWRITE_TAC[models0_def] THEN REPEAT CONJ_TAC THENL
   [(* is_interpretation *)
    MP_TAC(ASSUME `is_interpretation0 (mem:U->U->bool) (tys,tms) i`) THEN
    REWRITE_TAC[is_interpretation0_def; is_type_assignment0_def; is_term_assignment0_def;
                FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[K_THM] THEN ASM_MESON_TAC[boolean_in_boolset];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:mlstring`; `tk:hol_type`] THEN DISCH_TAC THEN
    X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
    SUBGOAL_THEN `type_ok (tys:tysig) tk` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def; FST; SND]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT1 o check (is_conj o concl)) THEN
      REWRITE_TAC[IN_FRANGE] THEN ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT; injectivity "option"];
      ALL_TAC] THEN
    SUBGOAL_THEN `typesem ((name =+ K (setSpec_two (mem:U->U->bool)))
                    (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))) tau tk =
                  typesem (FST i) tau tk` SUBST1_TAC THENL
     [MATCH_MP_TAC typesem_sig THEN EXISTS_TAC `tys:tysig` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    (* is_std_interpretation *)
    UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
    REWRITE_TAC[is_std_interpretation0_def; is_std_type_assignment0_def; APPLY_UPDATE_THM] THEN
    ASM_REWRITE_TAC[];
    (* the axioms *)
    X_GEN_TAC `p:hol_term` THEN DISCH_TAC THEN
    MATCH_MP_TAC satisfies_extend THEN
    MAP_EVERY EXISTS_TAC [`tys:tysig`; `tms:tmsig`] THEN
    ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL; ALL] THEN
    SUBGOAL_THEN `hol_term_ok (tys:tysig,tms:tmsig) p` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def]) THEN ASM_MESON_TAC[FST; SND]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC satisfies_sig THEN
    EXISTS_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN
    ASM_SIMP_TAC[ALL]]);;
(* Sorted lists of type variables with the same members are equal (used    *)
(* for HOL4's eqsh facts in new_type_definition_correct).                   *)
let CSEMAUX_STRING_SORT_MAP_explode_EQ = prove
 (`!l1 l2. ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ (!x. MEM x l1 <=> MEM x l2)
           ==> STRING_SORT (MAP explode l1) = STRING_SORT (MAP explode l2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`MAP explode (l1:mlstring list)`; `MAP explode (l2:mlstring list)`]
    STRING_SORT_EQ) THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_MAP_explode] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PERM_ALL_DISTINCT THEN REWRITE_TAC[ALL_DISTINCT_MAP_explode] THEN
  ASM_REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]);;

let CSEMAUX_MEM_tyvars_Tyapp_MAP_Tyvar = prove
 (`!name l x. MEM x (hol_tyvars (Tyapp name (MAP Tyvar l))) <=> MEM x l`,
  REWRITE_TAC[hol_tyvars_def; MEM_FOLDR_LIST_UNION; MEM; MEM_MAP] THEN
  MESON_TAC[CONJUNCT1 hol_tyvars_def; MEM]);;

let CSEMAUX_MEM_tyvars_Fun = prove
 (`!a b x. MEM x (hol_tyvars (Tyapp (implode "fun") [a; b])) <=>
           MEM x (hol_tyvars a) \/ MEM x (hol_tyvars b)`,
  REWRITE_TAC[hol_tyvars_def; ITLIST; CSEMAUX_MEM_LIST_UNION; MEM]);;

let CSEMAUX_sorted_tyvars_typedef = prove
 (`!pred rty name.
     (!x. MEM x (hol_tyvars rty) ==> MEM x (tvars pred))
     ==> MAP implode (STRING_SORT (MAP explode (hol_tyvars
           (Tyapp (implode "fun")
              [rty; Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode
                                                     (tvars pred)))))])))) =
         MAP implode (STRING_SORT (MAP explode (tvars pred))) /\
         MAP implode (STRING_SORT (MAP explode (hol_tyvars
           (Tyapp (implode "fun")
              [Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode
                                                     (tvars pred))))); rty])))) =
         MAP implode (STRING_SORT (MAP explode (tvars pred)))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CSEMAUX_STRING_SORT_MAP_explode_EQ THEN
  REWRITE_TAC[tyvars_ALL_DISTINCT; tvars_ALL_DISTINCT] THEN
  REWRITE_TAC[CSEMAUX_MEM_tyvars_Fun; CSEMAUX_MEM_tyvars_Tyapp_MAP_Tyvar] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN ASM_MESON_TAC[]);;
let CSEMAUX_typesem_o_Tyvar = prove
 (`!(dl:mlstring->U list->U) tau. typesem dl tau o TYPE_SUBST [] o Tyvar = tau`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; TYPE_SUBST_NIL; typesem_def]);;
let CSEMAUX_termsem_equation_true = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !sig i v s t tmenv.
     is_structure0 mem sig i v /\ hol_term_ok sig (s === t) /\ tmenv = SND sig /\
     termsem0 mem tmenv i v s = termsem0 mem tmenv i v t
     ==> termsem0 mem tmenv i v (s === t) = setSpec_true mem`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sig:sig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `v:(mlstring->U)#(mlstring#hol_type->U)`; `s:hol_term`; `t:hol_term`;
                 `tmenv:tmsig`] (UNDISCH termsem_equation)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[boolean_def]);;
let new_type_definition_correct = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt name pred abs_name rep_name witness.
     ((((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                               ctxt))),
       []) |- hol_Comb pred witness) /\
     CLOSED pred /\
     ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
     ~(abs_name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     ~(rep_name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     ~(abs_name = rep_name)
     ==> sound_update0 mem ctxt (hol_TypeDefn name pred abs_name rep_name)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[sound_update0_def; MAP; FLAT; types_of_upd_def; consts_of_upd_def;
               axexts_of_upd_def; conexts_of_upd_def; APPEND; LET_DEF; LET_END_DEF;
               alist_to_fmap_thm; set_of_list] THEN
   ABBREV_TAC `tys = alist_to_fmap (FLAT (MAP types_of_upd ctxt))` THEN
   ABBREV_TAC `tms = alist_to_fmap (FLAT (MAP consts_of_upd ctxt))` THEN
   ABBREV_TAC `axs = set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))` THEN
   STRIP_TAC THEN X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN DISCH_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP (UNDISCH proves_sound)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP hol_proves_theory_ok) THEN
   REWRITE_TAC[FST; SND; ALL] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
   SUBGOAL_THEN `is_std_sig (tys:tysig,tms:tmsig)` ASSUME_TAC THENL
    [ASM_MESON_TAC[theory_ok_sig; FST]; ALL_TAC] THEN
   ALL_TAC THEN
  SUBGOAL_THEN `hol_term_ok (tys:tysig,tms:tmsig) pred /\ hol_term_ok (tys,tms) witness /\
                 pred has_type Tyapp (implode "fun") [typeof witness; Tyapp (implode "bool") []]`
     STRIP_ASSUME_TAC THENL
  [ CONJ_TAC THENL
    [UNDISCH_TAC `hol_term_ok (tys:tysig,tms:tmsig) (hol_Comb pred witness)` THEN
     SIMP_TAC[hol_term_ok_def];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [UNDISCH_TAC `hol_term_ok (tys:tysig,tms:tmsig) (hol_Comb pred witness)` THEN
     SIMP_TAC[hol_term_ok_def];
     ALL_TAC] THEN
   MP_TAC(ONCE_REWRITE_RULE[has_type_cases]
     (ASSUME `hol_Comb pred witness has_type Tyapp (implode "bool") []`)) THEN
   REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `typeof t = dty` SUBST1_TAC THENL
    [ASM_MESON_TAC[WELLTYPED_LEMMA]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `typeof pred = Tyapp (implode "fun") [typeof witness; Tyapp (implode "bool") []]`
     ASSUME_TAC THENL [ASM_MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
   ASM_REWRITE_TAC[hol_domain_def] THEN
   SUBGOAL_THEN `type_ok (tys:tysig) (typeof witness)` ASSUME_TAC THENL
    [ASM_MESON_TAC[term_ok_type_ok; FST]; ALL_TAC] THEN
   SUBGOAL_THEN `!x. MEM x (hol_tyvars (typeof witness)) ==> MEM x (tvars pred)` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP tyvars_typeof_subset_tvars o
       check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "has_type"
                                                  with _ -> false)) (concl th) &&
                        can (find_term (fun t -> t = `pred:hol_term`)) (concl th))) THEN
     REWRITE_TAC[hol_tyvars_def; ITLIST; SUBSET; IN_SET_OF_LIST; CSEMAUX_MEM_LIST_UNION; MEM] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   ABBREV_TAC `rty = typeof witness` THEN
   ABBREV_TAC `argv = MAP implode (STRING_SORT (MAP explode (tvars pred)))` THEN
   ABBREV_TAC `aty = Tyapp name (MAP Tyvar argv)` THEN
  SUBGOAL_THEN `!x. MEM x argv <=> MEM x (tvars pred)` ASSUME_TAC THENL
    [EXPAND_TAC "argv" THEN
     REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode];
     ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (argv:mlstring list) = LENGTH (tvars pred)` ASSUME_TAC THENL
    [EXPAND_TAC "argv" THEN
     SIMP_TAC[LENGTH_MAP; LENGTH_STRING_SORT; ALL_DISTINCT_MAP_explode; tvars_ALL_DISTINCT];
     ALL_TAC] THEN
   MP_TAC(SPECL [`pred:hol_term`; `rty:hol_type`; `name:mlstring`]
                CSEMAUX_sorted_tyvars_typedef) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ABBREV_TAC `tv = \args:U list. K (setSpec_two (mem:U->U->bool)) =++
                      REVERSE (ZIP (argv:mlstring list) args)` THEN
   ABBREV_TAC `sv = \tau:mlstring->U. \(x:mlstring,ty:hol_type).
                      @v. (mem:U->U->bool) v
                      (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                         tau ty)` THEN
   ABBREV_TAC `mpred = \tau:mlstring->U. termsem0 (mem:U->U->bool) tms i (tau, sv tau) pred` THEN
   ABBREV_TAC `mty = \args:U list. setSpec_sub (mem:U->U->bool)
                       (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (tv args) rty)
                       (setSpec_holds mem (mpred (tv args)))` THEN
   ABBREV_TAC `mrep = \args:U list. abstract (mem:U->U->bool) (mty args)
                       (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (tv args) rty)
                       I` THEN
   ABBREV_TAC `mabs = \args:U list. abstract (mem:U->U->bool)
                       (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (tv args) rty)
                       (mty args)
                       (\v. if setSpec_holds mem (mpred (tv args)) v then v else @v. mem v (mty args))` THEN
  SUBGOAL_THEN `!tau:mlstring->U. tv (MAP tau argv) =
                   (\x. if MEM x (tvars pred) then tau x else setSpec_two (mem:U->U->bool))`
     ASSUME_TAC THENL
    [GEN_TAC THEN EXPAND_TAC "tv" THEN REWRITE_TAC[FUN_EQ_THM] THEN
     ASM_REWRITE_TAC[CSEMAUX_UPDATE_LIST_ZIP_MAP; K_THM];
     ALL_TAC] THEN
  SUBGOAL_THEN `!ls. LENGTH ls = LENGTH (argv:mlstring list) /\ ALL (\s. ?x. mem x s) ls
                      ==> is_type_valuation0 (mem:U->U->bool) (tv ls)`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN EXPAND_TAC "tv" THEN
     REWRITE_TAC[is_type_valuation0_def; APPLY_UPDATE_LIST_ALOOKUP; REVERSE_REVERSE] THEN
     X_GEN_TAC `x:mlstring` THEN
     CASES_ON `ALOOKUP (ZIP (argv:mlstring list) (ls:U list)) x` THEN
     REWRITE_TAC[option_CASE; K_THM] THENL
     [MESON_TAC[UNDISCH boolean_in_boolset];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
   MP_TAC(ISPECL [`argv:mlstring list`; `ls:U list`] MEM_ZIP) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   STRIP_TAC THEN
   UNDISCH_TAC `ALL (\s. ?x. (mem:U->U->bool) x s) ls` THEN
   REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEM_EL THEN ASM_MESON_TAC[]];
     ALL_TAC] THEN
  MP_TAC(ASSUME `models0 (mem:U->U->bool) i ((tys,tms),axs)`) THEN
   REWRITE_TAC[models0_def; is_interpretation0_def; FST; SND] THEN STRIP_TAC THEN
   SUBGOAL_THEN `!tau. is_type_valuation0 (mem:U->U->bool) tau
                       ==> is_term_valuation0 mem tys
                             (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) tau (sv tau)`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN EXPAND_TAC "sv" THEN
     REWRITE_TAC[is_term_valuation0_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
     REPEAT STRIP_TAC THEN CONV_TAC SELECT_CONV THEN
     MATCH_MP_TAC(UNDISCH typesem_inhabited) THEN EXISTS_TAC `tys:tysig` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN `!ls. LENGTH ls = LENGTH (argv:mlstring list) /\ ALL (\s. ?x. mem x s) ls
                      ==> ?v. (mem:U->U->bool) v (mty ls)`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN EXPAND_TAC "mty" THEN BETA_TAC THEN
     REWRITE_TAC[UNDISCH mem_sub] THEN
     SUBGOAL_THEN `is_valuation0 (mem:U->U->bool) tys
                     (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                     (tv (ls:U list), sv (tv ls))` ASSUME_TAC THENL
      [REWRITE_TAC[is_valuation0_def] THEN
       SUBGOAL_THEN `is_type_valuation0 (mem:U->U->bool) (tv (ls:U list))` ASSUME_TAC THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
       ASM_SIMP_TAC[];
       ALL_TAC] THEN
     UNDISCH_TAC `entails0 (mem:U->U->bool) (((tys,tms),axs),[]) (hol_Comb pred witness)` THEN
     REWRITE_TAC[entails0_def] THEN
     DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                last o CONJUNCTS) THEN
     ANTS_TAC THENL
      [UNDISCH_TAC `models0 (mem:U->U->bool) i ((tys,tms),axs)` THEN SIMP_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[satisfies0_def; ALL; FST; SND] THEN
     DISCH_THEN(MP_TAC o SPEC
       `(tv (ls:U list), sv (tv ls)):(mlstring->U)#(mlstring#hol_type->U)`) THEN
     ASM_REWRITE_TAC[termsem0_def] THEN DISCH_TAC THEN
     EXISTS_TAC `termsem0 (mem:U->U->bool) tms i (tv (ls:U list), sv (tv ls)) witness` THEN
     CONJ_TAC THENL
      [EXPAND_TAC "rty" THEN MATCH_MP_TAC(UNDISCH termsem_typesem_matchable) THEN
       MAP_EVERY EXISTS_TAC [`(tys:tysig,tms:tmsig)`;
                             `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                             `(tv:U list->mlstring->U) ls`] THEN
       ASM_REWRITE_TAC[FST; SND; is_interpretation0_def] THEN
       ASM_MESON_TAC[is_std_interpretation_is_type];
       EXPAND_TAC "mpred" THEN ASM_REWRITE_TAC[setSpec_holds_def]];
     ALL_TAC] THEN
  SUBGOAL_THEN `!tau ty. type_ok tys ty
                    ==> typesem ((name =+ (mty:U list->U))
                                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))) tau ty =
                        typesem (FST i) tau ty`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC typesem_sig THEN EXISTS_TAC `tys:tysig` THEN
     ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN X_GEN_TAC `n:mlstring` THEN DISCH_TAC THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     UNDISCH_TAC `~(name IN FDOM (tys:tysig))` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!tau y. typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                           (\x. if MEM x (tvars pred) then tau x else y) rty =
                         typesem (FST i) tau rty`
     ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN MATCH_MP_TAC typesem_tyvars THEN REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `MEM (x:mlstring) (tvars pred)` (fun th -> REWRITE_TAC[th]) THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t -> t = `rty:hol_type`))
                                                   (concl th) && is_forall (concl th))) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!tau y. (mpred:(mlstring->U)->U) (\x. if MEM x (tvars pred) then tau x else y) =
                         mpred tau`
     ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN EXPAND_TAC "mpred" THEN
     TRANS_TAC EQ_TRANS
       `termsem0 (mem:U->U->bool) tms i
          (tau, sv (\x. if MEM x (tvars pred) then tau x else y:U)) pred` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC termsem_tyfrees THEN EXISTS_TAC `(tys:tysig,tms:tmsig)` THEN
       ASM_REWRITE_TAC[SND; FST] THEN SIMP_TAC[];
       MATCH_MP_TAC termsem_frees THEN RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_ok_welltyped THEN
       EXISTS_TAC `(tys:tysig,tms:tmsig)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
  SUBGOAL_THEN `implode "fun" IN FDOM (tys:tysig) /\ implode "bool" IN FDOM tys /\
                 implode "=" IN FDOM (tms:tmsig)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `is_std_sig (tys:tysig,tms:tmsig)` THEN
     REWRITE_TAC[is_std_sig_def; FST; SND; FLOOKUP_DEF] THEN
     REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(name = implode "fun") /\ ~(name = implode "bool") /\
                 ~(abs_name = implode "=") /\ ~(rep_name = implode "=")` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN DISCH_TAC THEN
     UNDISCH_TAC `~(name IN FDOM (tys:tysig))` THEN
     UNDISCH_TAC `~(abs_name IN FDOM (tms:tmsig))` THEN
     UNDISCH_TAC `~(rep_name IN FDOM (tms:tmsig))` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   EXISTS_TAC `((name =+ (mty:U list->U))
                  (FST (i:(mlstring->U list->U)#(mlstring->U list->U))),
                (abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))` THEN
   REWRITE_TAC[FST; SND] THEN
   SUBGOAL_THEN `equal_on (tys:tysig,tms:tmsig) (i:(mlstring->U list->U)#(mlstring->U list->U))
                   (((name =+ (mty:U list->U)) (FST i)),
                    ((abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i))))`
                ASSUME_TAC THENL
    [REWRITE_TAC[equal_on_def; FST; SND; APPLY_UPDATE_THM] THEN CONJ_TAC THEN
     X_GEN_TAC `n:mlstring` THEN DISCH_TAC THEN
     REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     UNDISCH_TAC `~(name IN FDOM (tys:tysig))` THEN
     UNDISCH_TAC `~(abs_name IN FDOM (tms:tmsig))` THEN
     UNDISCH_TAC `~(rep_name IN FDOM (tms:tmsig))` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool)
                   ((name =+ (mty:U list->U))
                      (FST (i:(mlstring->U list->U)#(mlstring->U list->U))))`
     ASSUME_TAC THENL
    [UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
     REWRITE_TAC[is_std_interpretation0_def; is_std_type_assignment0_def; APPLY_UPDATE_THM] THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `is_type_assignment0 (mem:U->U->bool)
                   (tys |+ (name,LENGTH (tvars pred)))
                   ((name =+ (mty:U list->U))
                      (FST (i:(mlstring->U list->U)#(mlstring->U list->U))))`
     ASSUME_TAC THENL
    [REWRITE_TAC[is_type_assignment0_def; FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE] THEN
       CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
       MAP_EVERY X_GEN_TAC [`k:mlstring`; `n:num`] THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
       COND_CASES_TAC THENL
        [REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
         ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
         ASM_REWRITE_TAC[];
         DISCH_TAC THEN
         UNDISCH_TAC `is_type_assignment0 (mem:U->U->bool) tys
                        (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))` THEN
         REWRITE_TAC[is_type_assignment0_def; FEVERY_ALL_FLOOKUP] THEN
         DISCH_THEN(MP_TAC o SPECL [`k:mlstring`; `n:num`]) THEN
         ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]];
     ALL_TAC] THEN
  SUBGOAL_THEN `!tau:mlstring->U. typesem ((name =+ (mty:U list->U))
                    (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))) tau aty =
                  mty (MAP tau argv)` ASSUME_TAC THENL
    [GEN_TAC THEN EXPAND_TAC "aty" THEN
     REWRITE_TAC[typesem_def; APPLY_UPDATE_THM; MAP_MAP_o; o_DEF; ETA_AX];
     ALL_TAC] THEN
   SUBGOAL_THEN `!tau:mlstring->U. mabs (MAP tau argv) =
       abstract (mem:U->U->bool)
         (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) tau rty)
         ((mty:U list->U) (MAP tau argv))
         (\v. if setSpec_holds mem ((mpred:(mlstring->U)->U) tau) v then v
              else @v. mem v (mty (MAP tau argv)))` ASSUME_TAC THENL
    [GEN_TAC THEN EXPAND_TAC "mabs" THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!tau:mlstring->U. mrep (MAP tau argv) =
       abstract (mem:U->U->bool) ((mty:U list->U) (MAP tau argv))
         (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) tau rty) I`
     ASSUME_TAC THENL
    [GEN_TAC THEN EXPAND_TAC "mrep" THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!tau:mlstring->U x.
       (mem:U->U->bool) x ((mty:U list->U) (MAP tau argv)) <=>
       mem x (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) tau rty) /\
       setSpec_holds mem ((mpred:(mlstring->U)->U) tau) x` ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN EXPAND_TAC "mty" THEN ASM_REWRITE_TAC[UNDISCH mem_sub];
     ALL_TAC] THEN
   SUBGOAL_THEN `!tau:mlstring->U. is_type_valuation0 (mem:U->U->bool) tau
                   ==> ?v. mem v ((mty:U list->U) (MAP tau argv))` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[LENGTH_MAP; ALL_MAP; o_DEF] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[is_type_valuation0_def]) THEN ASM_REWRITE_TAC[ALL_T];
     ALL_TAC] THEN
  SUBGOAL_THEN `is_term_assignment0 (mem:U->U->bool)
                  (tms |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                          (abs_name,Tyapp (implode "fun") [rty; aty]))
                  ((name =+ (mty:U list->U)) (FST (i:(mlstring->U list->U)#(mlstring->U list->U))))
                  ((abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))`
              ASSUME_TAC THENL
    [REWRITE_TAC[is_term_assignment0_def; FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE] THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   MAP_EVERY X_GEN_TAC [`k:mlstring`; `tk:hol_type`] THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
   COND_CASES_TAC THENL
    [(* the abstraction *)
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
     ASM_SIMP_TAC[typesem_Fun] THEN
     MATCH_MP_TAC(UNDISCH abstract_in_funspace) THEN
     X_GEN_TAC `x:U` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THENL
      [ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
       UNDISCH_TAC `!tau:mlstring->U. is_type_valuation0 (mem:U->U->bool) tau
                       ==> ?v. mem v ((mty:U list->U) (MAP tau argv))` THEN
       DISCH_THEN(MP_TAC o SPEC `tau:mlstring->U`) THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   COND_CASES_TAC THENL
    [(* the representation *)
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
     ASM_SIMP_TAC[typesem_Fun] THEN
     MATCH_MP_TAC(UNDISCH abstract_in_funspace) THEN
     X_GEN_TAC `x:U` THEN ASM_SIMP_TAC[I_THM];
     ALL_TAC] THEN
   (* the old constants *)
   DISCH_TAC THEN X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
   SUBGOAL_THEN `type_ok (tys:tysig) tk` ASSUME_TAC THENL
    [UNDISCH_TAC `theory_ok ((tys:tysig,tms:tmsig),axs)` THEN
     REWRITE_TAC[theory_ok_def; FST; SND; IN_FRANGE] THEN
     DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN EXISTS_TAC `k:mlstring` THEN
     UNDISCH_TAC `FLOOKUP (tms:tmsig) k = SOME tk` THEN
     REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
     REWRITE_TAC[option_DISTINCT; injectivity "option"];
     ALL_TAC] THEN
   ASM_SIMP_TAC[] THEN
   UNDISCH_TAC `is_term_assignment0 (mem:U->U->bool) tms
                  (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (SND i)` THEN
   REWRITE_TAC[is_term_assignment0_def; FEVERY_ALL_FLOOKUP] THEN
   DISCH_THEN(MP_TAC o SPECL [`k:mlstring`; `tk:hol_type`]) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN `is_std_interpretation0 (mem:U->U->bool)
                  (((name =+ (mty:U list->U)) (FST i)),
                   ((abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i))))`
               ASSUME_TAC THENL
    [ASM_REWRITE_TAC[is_std_interpretation0_def] THEN
     UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
     REWRITE_TAC[is_std_interpretation0_def; interprets0_def; APPLY_UPDATE_THM] THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `is_std_sig (tys |+ (name,LENGTH (tvars pred)),
                   tms |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                          (abs_name,Tyapp (implode "fun") [rty; aty]))` ASSUME_TAC THENL
    [UNDISCH_TAC `is_std_sig (tys:tysig,tms:tmsig)` THEN
     REWRITE_TAC[is_std_sig_def; FST; SND; FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `(tys:tysig) SUBMAP tys |+ (name,LENGTH (tvars pred)) /\
                 (tms:tmsig) SUBMAP tms |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                         (abs_name,Tyapp (implode "fun") [rty; aty])`
     STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
     CONJ_TAC THEN X_GEN_TAC `n:mlstring` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
      [SUBGOAL_THEN `~(n:mlstring = name)` (fun th -> REWRITE_TAC[th]) THEN
       DISCH_TAC THEN UNDISCH_TAC `(n:mlstring) IN FDOM (tys:tysig)` THEN ASM_REWRITE_TAC[];
       SUBGOAL_THEN `~(n:mlstring = abs_name) /\ ~(n = rep_name)` (fun th -> REWRITE_TAC[th]) THEN
       CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `(n:mlstring) IN FDOM (tms:tmsig)` THEN
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
SUBGOAL_THEN `type_ok (tys |+ (name,LENGTH (tvars pred))) rty /\
                 type_ok (tys |+ (name,LENGTH (tvars pred))) aty` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC type_ok_extend THEN EXISTS_TAC `tys:tysig` THEN ASM_REWRITE_TAC[];
       EXPAND_TAC "aty" THEN
       ASM_REWRITE_TAC[type_ok_def; FLOOKUP_UPDATE; LENGTH_MAP; ALL_MAP; o_DEF; ALL_T]];
     ALL_TAC] THEN
   SUBGOAL_THEN `type_ok (tys |+ (name,LENGTH (tvars pred))) (Tyapp (implode "fun") [rty; aty]) /\
                 type_ok (tys |+ (name,LENGTH (tvars pred))) (Tyapp (implode "fun") [aty; rty])`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `is_std_sig (tys |+ (name,LENGTH (tvars pred)),
                   tms |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                          (abs_name,Tyapp (implode "fun") [rty; aty]))` THEN
     REWRITE_TAC[is_std_sig_def; FST; SND] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[type_ok_def; LENGTH; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   SUBGOAL_THEN
    `FLOOKUP ((tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                     (abs_name,Tyapp (implode "fun") [rty; aty])) abs_name =
       SOME (Tyapp (implode "fun") [rty; aty]) /\
     FLOOKUP (tms |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                     (abs_name,Tyapp (implode "fun") [rty; aty])) rep_name =
       SOME (Tyapp (implode "fun") [aty; rty])`
     STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC[FLOOKUP_UPDATE]; ALL_TAC] THEN
   SUBGOAL_THEN
    `!tau. instance ((tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                    (abs_name,Tyapp (implode "fun") [rty; aty]))
             ((name =+ (mty:U list->U)) (FST (i:(mlstring->U list->U)#(mlstring->U list->U))),
              (abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))
             abs_name (Tyapp (implode "fun") [rty; aty]) tau = mabs (MAP tau argv) /\
           instance ((tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                    (abs_name,Tyapp (implode "fun") [rty; aty]))
             ((name =+ (mty:U list->U)) (FST (i:(mlstring->U list->U)#(mlstring->U list->U))),
              (abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))
             rep_name (Tyapp (implode "fun") [aty; rty]) tau = mrep (MAP tau argv)`
     ASSUME_TAC THENL
    [GEN_TAC THEN CONJ_TAC THEN
     W(fun (asl,w) ->
         let args = snd(strip_comb(lhs w)) in
         MP_TAC(ISPECL [el 0 args; el 1 args; el 2 args; el 3 args; el 3 args;
                        `[]:(hol_type#hol_type)list`] instance_def)) THEN
     ASM_REWRITE_TAC[TYPE_SUBST_NIL] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
     REWRITE_TAC[CSEMAUX_typesem_o_Tyvar] THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM];
     ALL_TAC] THEN
   REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `p:hol_term` THEN STRIP_TAC THENL
    [ALL_TAC;
     ALL_TAC;
     MATCH_MP_TAC satisfies_extend THEN
     MAP_EVERY EXISTS_TAC [`tys:tysig`; `tms:tmsig`] THEN
     ASM_REWRITE_TAC[ALL] THEN
     SUBGOAL_THEN `hol_term_ok (tys:tysig,tms:tmsig) p` ASSUME_TAC THENL
      [UNDISCH_TAC `theory_ok ((tys:tysig,tms:tmsig),axs)` THEN
       REWRITE_TAC[theory_ok_def; FST; SND] THEN
       DISCH_THEN(MP_TAC o SPEC `p:hol_term` o CONJUNCT1 o CONJUNCT2) THEN
       ASM_SIMP_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC satisfies_sig THEN
     EXISTS_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN
     ASM_SIMP_TAC[ALL]] THENL
  [(* abs (rep a) = a *)
   FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
   REWRITE_TAC[satisfies0_def; ALL; FST; SND] THEN
   X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
   SUBGOAL_THEN
    `hol_term_ok (tys |+ (name,LENGTH (tvars pred)),
                  (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                 (abs_name,Tyapp (implode "fun") [rty; aty]))
       (hol_Comb (hol_Const abs_name (Tyapp (implode "fun") [rty; aty]))
          (hol_Comb (hol_Const rep_name (Tyapp (implode "fun") [aty; rty]))
             (hol_Var (implode "a") aty)) ===
        hol_Var (implode "a") aty)`
     ASSUME_TAC THENL
    [ASM_SIMP_TAC[term_ok_equation; hol_term_ok_def; WELLTYPED_CLAUSES; typeof_def; codomain_def;
                  FST; SND; injectivity "option"] THEN
     REPEAT CONJ_TAC THEN MESON_TAC[TYPE_SUBST_NIL];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `(mem:U->U->bool) (SND (v:(mlstring->U)#(mlstring#hol_type->U)) (implode "a",aty))
                      ((mty:U list->U) (MAP (FST v) argv))` MP_TAC THENL
    [UNDISCH_TAC `is_valuation0 (mem:U->U->bool) (tys |+ (name,LENGTH (tvars pred)))
                    ((name =+ (mty:U list->U))
                       (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))) v` THEN
     REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
     DISCH_THEN(MP_TAC o SPECL [`implode "a"`; `aty:hol_type`] o CONJUNCT2) THEN
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
   MATCH_MP_TAC(UNDISCH CSEMAUX_termsem_equation_true) THEN
   EXISTS_TAC `((tys:tysig) |+ (name,LENGTH (tvars pred)),
                (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                               (abs_name,Tyapp (implode "fun") [rty; aty]))` THEN
   ASM_REWRITE_TAC[is_structure0_def; is_interpretation0_def; FST; SND] THEN
   REWRITE_TAC[termsem0_def] THEN ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[UNDISCH apply_abstract; I_THM];
   (* pred r = (rep (abs r) = r) *)
   FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
   REWRITE_TAC[satisfies0_def; ALL; FST; SND] THEN
   X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(mem:U->U->bool) (SND (v:(mlstring->U)#(mlstring#hol_type->U)) (implode "r",rty))
                   (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (FST v) rty)`
     ASSUME_TAC THENL
    [UNDISCH_TAC `is_valuation0 (mem:U->U->bool) (tys |+ (name,LENGTH (tvars pred)))
                    ((name =+ (mty:U list->U))
                       (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))) v` THEN
     REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
     DISCH_THEN(MP_TAC o SPECL [`implode "r"`; `rty:hol_type`] o CONJUNCT2) THEN
     ASM_SIMP_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `is_type_valuation0 (mem:U->U->bool)
                   (FST (v:(mlstring->U)#(mlstring#hol_type->U)))` ASSUME_TAC THENL
    [ASM_MESON_TAC[is_valuation0_def]; ALL_TAC] THEN
   SUBGOAL_THEN
    `termsem0 (mem:U->U->bool)
       ((tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                       (abs_name,Tyapp (implode "fun") [rty; aty]))
       ((name =+ (mty:U list->U)) (FST (i:(mlstring->U list->U)#(mlstring->U list->U))),
        (abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))
       v pred =
     mpred (FST (v:(mlstring->U)#(mlstring#hol_type->U)))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `termsem0 (mem:U->U->bool) tms
       ((name =+ (mty:U list->U)) (FST (i:(mlstring->U list->U)#(mlstring->U list->U))),
        (abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))
       v pred` THEN CONJ_TAC THENL
      [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] termsem_extend) THEN
       EXISTS_TAC `tys:tysig` THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `termsem0 (mem:U->U->bool) tms i v pred` THEN CONJ_TAC THENL
      [MATCH_MP_TAC termsem_sig THEN EXISTS_TAC `(tys:tysig,tms:tmsig)` THEN
       ASM_REWRITE_TAC[SND];
       ALL_TAC] THEN
     EXPAND_TAC "mpred" THEN BETA_TAC THEN MATCH_MP_TAC termsem_frees THEN
     RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC term_ok_welltyped THEN EXISTS_TAC `(tys:tysig,tms:tmsig)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `hol_term_ok (tys |+ (name,LENGTH (tvars pred)),
                  (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                 (abs_name,Tyapp (implode "fun") [rty; aty]))
       (hol_Comb (hol_Const rep_name (Tyapp (implode "fun") [aty; rty]))
          (hol_Comb (hol_Const abs_name (Tyapp (implode "fun") [rty; aty]))
             (hol_Var (implode "r") rty)) ===
        hol_Var (implode "r") rty) /\
     hol_term_ok (tys |+ (name,LENGTH (tvars pred)),
                  (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                 (abs_name,Tyapp (implode "fun") [rty; aty]))
       (hol_Comb pred (hol_Var (implode "r") rty) ===
        (hol_Comb (hol_Const rep_name (Tyapp (implode "fun") [aty; rty]))
          (hol_Comb (hol_Const abs_name (Tyapp (implode "fun") [rty; aty]))
             (hol_Var (implode "r") rty)) ===
         hol_Var (implode "r") rty))`
     STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN
      `hol_term_ok (tys |+ (name,LENGTH (tvars pred)),
                    (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                   (abs_name,Tyapp (implode "fun") [rty; aty])) pred`
       ASSUME_TAC THENL
      [MATCH_MP_TAC hol_term_ok_extend THEN
       MAP_EVERY EXISTS_TAC [`tys:tysig`; `tms:tmsig`] THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_SIMP_TAC[term_ok_equation; hol_term_ok_def; WELLTYPED_CLAUSES; typeof_def; codomain_def;
                  FST; SND; injectivity "option"; EQUATION_HAS_TYPE_BOOL;
                  CSYNAUX_typeof_equation] THEN
     SUBGOAL_THEN `welltyped pred` ASSUME_TAC THENL
      [MATCH_MP_TAC term_ok_welltyped THEN EXISTS_TAC `(tys:tysig,tms:tmsig)` THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MESON_TAC[TYPE_SUBST_NIL];
     ALL_TAC] THEN
   ABBREV_TAC `x = SND (v:(mlstring->U)#(mlstring#hol_type->U)) (implode "r",rty)` THEN
   ABBREV_TAC `f = (mpred:(mlstring->U)->U) (FST (v:(mlstring->U)#(mlstring#hol_type->U)))` THEN
   SUBGOAL_THEN `(mem:U->U->bool) f
                   (setSpec_funspace mem (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                                    (FST (v:(mlstring->U)#(mlstring#hol_type->U))) rty) (setSpec_two mem))`
     ASSUME_TAC THENL
    [EXPAND_TAC "f" THEN EXPAND_TAC "mpred" THEN BETA_TAC THEN
     MATCH_MP_TAC(UNDISCH termsem_typesem_matchable) THEN
     MAP_EVERY EXISTS_TAC [`(tys:tysig,tms:tmsig)`;
                           `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                           `FST (v:(mlstring->U)#(mlstring#hol_type->U))`] THEN
     SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool)
                     (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))` ASSUME_TAC THENL
      [UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
       SIMP_TAC[is_std_interpretation0_def];
       ALL_TAC] THEN
     ASM_SIMP_TAC[FST; SND; is_valuation0_def; is_interpretation0_def; typesem_Fun;
                  typesem_Bool];
     ALL_TAC] THEN
   SUBGOAL_THEN `(mem:U->U->bool) (setSpec_apply mem f x) (setSpec_two mem)` ASSUME_TAC THENL
    [MATCH_MP_TAC(UNDISCH apply_in_rng) THEN
     EXISTS_TAC `typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                   (FST (v:(mlstring->U)#(mlstring#hol_type->U))) rty` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MATCH_MP_TAC(UNDISCH CSEMAUX_termsem_equation_true) THEN
   EXISTS_TAC `((tys:tysig) |+ (name,LENGTH (tvars pred)),
                (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                               (abs_name,Tyapp (implode "fun") [rty; aty]))` THEN
   ASM_REWRITE_TAC[is_structure0_def; is_interpretation0_def; FST; SND] THEN
   REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 termsem0_def)); CONJUNCT1 termsem0_def] THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`((tys:tysig) |+ (name,LENGTH (tvars pred)),
                    (tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                   (abs_name,Tyapp (implode "fun") [rty; aty]))`;
                  `((name =+ (mty:U list->U))
                      (FST (i:(mlstring->U list->U)#(mlstring->U list->U))),
                    (abs_name =+ (mabs:U list->U)) ((rep_name =+ (mrep:U list->U)) (SND i)))`;
                  `v:(mlstring->U)#(mlstring#hol_type->U)`;
                  `hol_Comb (hol_Const rep_name (Tyapp (implode "fun") [aty; rty]))
                     (hol_Comb (hol_Const abs_name (Tyapp (implode "fun") [rty; aty]))
                        (hol_Var (implode "r") rty))`;
                  `hol_Var (implode "r") rty`;
                  `(tms:tmsig) |+ (rep_name,Tyapp (implode "fun") [aty; rty]) |+
                                  (abs_name,Tyapp (implode "fun") [rty; aty])`]
            (UNDISCH termsem_equation)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[is_structure0_def; is_interpretation0_def; FST; SND]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[termsem0_def] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(mem:U->U->bool) x (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                    (FST (v:(mlstring->U)#(mlstring#hol_type->U))) rty)` ASSUME_TAC THENL
    [EXPAND_TAC "x" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `setSpec_holds (mem:U->U->bool) f x` THENL
    [ASM_SIMP_TAC[UNDISCH apply_abstract; I_THM] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[setSpec_holds_def]) THEN ASM_REWRITE_TAC[boolean_def];
     ALL_TAC] THEN
   ABBREV_TAC `c0 = @w. (mem:U->U->bool) w
                      (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                         (FST (v:(mlstring->U)#(mlstring#hol_type->U))) rty) /\
                      setSpec_holds mem f w` THEN
   SUBGOAL_THEN `(mem:U->U->bool) c0
                   (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                      (FST (v:(mlstring->U)#(mlstring#hol_type->U))) rty) /\
                 setSpec_holds mem f c0` STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "c0" THEN CONV_TAC SELECT_CONV THEN
     UNDISCH_TAC `!tau:mlstring->U. is_type_valuation0 (mem:U->U->bool) tau
                    ==> ?v. mem v ((mty:U list->U) (MAP tau argv))` THEN
     DISCH_THEN(MP_TAC o SPEC `FST (v:(mlstring->U)#(mlstring#hol_type->U))`) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_SIMP_TAC[UNDISCH apply_abstract; I_THM] THEN
   SUBGOAL_THEN `~(c0:U = x)` (fun th -> REWRITE_TAC[th; boolean_def]) THENL
    [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~setSpec_holds (mem:U->U->bool) f x` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   UNDISCH_TAC `(mem:U->U->bool) (setSpec_apply mem f x) (setSpec_two mem)` THEN
   ASM_SIMP_TAC[UNDISCH mem_boolset] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[setSpec_holds_def]) THEN ASM_REWRITE_TAC[]]);;
let updates_consistent = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !upd ctxt.
     upd updates ctxt
     ==> theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                     alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                    set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                         (conexts_of_upd upd)) ctxt))) /\
         (!p. ~(upd = hol_NewAxiom p))
         ==> sound_update0 mem ctxt upd`,
  STRIP_TAC THEN MATCH_MP_TAC updates_ind THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH new_constant_correct) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH new_specification_correct) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH new_type_correct) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH new_type_definition_correct) THEN
    EXISTS_TAC `witness:hol_term` THEN ASM_REWRITE_TAC[]]);;
(* The headline: context extensions without new axioms preserve models. *)
let extends_consistent = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt1 ctxt2.
     ctxt2 extends ctxt1
     ==> !i. theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                         alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
                        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd)) ctxt1))) /\
             models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt1))) /\
             (!p. MEM (hol_NewAxiom p) ctxt2 ==> MEM (hol_NewAxiom p) ctxt1)
             ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                                alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))) i i' /\
                      models0 mem i'
                        ((alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                          alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                              (conexts_of_upd upd)) ctxt2)))`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN STRIP_TAC THEN
   MP_TAC(ISPEC
    `\ctxt. theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                        alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                       set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                            (conexts_of_upd upd)) ctxt))) /\
            ?ls. ctxt = APPEND ls ctxt1 /\
                 DISJOINT (FDOM (alist_to_fmap (FLAT (MAP types_of_upd ls))))
                          (FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)))) /\
                 DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ls))))
                          (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt1)))) /\
                 ((!p. MEM (hol_NewAxiom p) ls ==> MEM (hol_NewAxiom p) ctxt1)
                  ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                                     alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))) i i' /\
                           models0 (mem:U->U->bool) i'
                             ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                               alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                                   (conexts_of_upd upd))
                                                     ctxt))))`
    extends_ind) THEN
   BETA_TAC THEN
  ANTS_TAC THENL
   [(* the induction step *)
    MAP_EVERY X_GEN_TAC [`upd:update`; `ctxt:update list`] THEN STRIP_TAC THEN
     FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates_theory_ok) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     EXISTS_TAC `CONS (upd:update) ls` THEN REWRITE_TAC[APPEND] THEN
     SUBGOAL_THEN
      `DISJOINT (FDOM (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ls)))))
                (FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)))) /\
       DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ls)))))
                (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))))`
      (fun th -> REWRITE_TAC[th]) THENL
      [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP updates_DISJOINT) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[FDOM_alist_to_fmap; MAP_APPEND; FLAT_APPEND; MAP;
                                   FLAT; SET_OF_LIST_APPEND; DISJOINT_UNION]) THEN
       REWRITE_TAC[FDOM_alist_to_fmap; MAP_APPEND; FLAT_APPEND; MAP; FLAT; SET_OF_LIST_APPEND;
                   DISJOINT_UNION] THEN
       ASM_REWRITE_TAC[] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_DISJOINT; IN_UNION]) THEN
       REWRITE_TAC[IN_DISJOINT] THEN ASM_MESON_TAC[];
       ALL_TAC] THEN
     DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
       can (find_term (fun t -> t = `ls:update list`)) (concl th))) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `j:(mlstring->U list->U)#(mlstring->U list->U)`
                  STRIP_ASSUME_TAC) THEN
     ASM_CASES_TAC `?p. upd = hol_NewAxiom p` THENL
      [(* an axiom *)
       FIRST_X_ASSUM(X_CHOOSE_THEN `p0:hol_term` SUBST_ALL_TAC) THEN
       EXISTS_TAC `j:(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `models0 (mem:U->U->bool) j
         ((alist_to_fmap (FLAT (MAP types_of_upd (APPEND ls ctxt1))),
           alist_to_fmap (FLAT (MAP consts_of_upd (APPEND ls ctxt1)))),
          set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                 (APPEND ls (ctxt1:update list)))))` THEN
       REWRITE_TAC[models0_def; MAP; FLAT; types_of_upd_def; consts_of_upd_def;
                   axexts_of_upd_def; conexts_of_upd_def; APPEND; set_of_list; IN_INSERT] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:hol_term` THEN STRIP_TAC THEN
       ASM_REWRITE_TAC[] THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC[IN_SET_OF_LIST; MEM_FLAT; MEM_MAP; MEM_APPEND] THEN
         EXISTS_TAC `[p0:hol_term]` THEN REWRITE_TAC[MEM] THEN
   EXISTS_TAC `hol_NewAxiom p0` THEN
   REWRITE_TAC[axexts_of_upd_def; conexts_of_upd_def; APPEND] THEN
   DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM];
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
       (* a conservative extension *)
       MP_TAC(ISPECL [`upd:update`; `APPEND ls (ctxt1:update list)`]
         (UNDISCH updates_consistent)) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[sound_update0_def] THEN
   DISCH_THEN(MP_TAC o SPEC `j:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `z:(mlstring->U list->U)#(mlstring->U list->U)`
                STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `z:(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC equal_on_trans THEN
   EXISTS_TAC `j:(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC equal_on_reduce THEN EXISTS_TAC `ls:update list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`ctxt1:update list`; `ctxt2:update list`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [EXISTS_TAC `[]:update list` THEN
     REWRITE_TAC[APPEND; MAP; FLAT; alist_to_fmap_thm; FDOM_FEMPTY; DISJOINT_EMPTY; MEM] THEN
     EXISTS_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN
     ASM_REWRITE_TAC[equal_on_refl];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ls:update list` STRIP_ASSUME_TAC o CONJUNCT2) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `p:hol_term` THEN DISCH_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND]);;
