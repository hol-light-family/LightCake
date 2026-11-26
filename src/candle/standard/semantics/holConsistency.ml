(* ========================================================================= *)
(* holConsistency: port of HOL4 candle/standard/semantics/                   *)
(* holConsistencyScript.sml (CakeML v3479).  Consistency of the inference    *)
(* system: starting from any context with a model, any context reached by   *)
(* non-axiomatic extensions has both provable and unprovable sequents.  And  *)
(* the base case: the HOL contexts (the initial context with no axioms,     *)
(* with all but the infinity axiom, with all three axioms) have models       *)
(* (under suitable assumptions).                                             *)
(* ========================================================================= *)

needs "candle/set-theory/setSpec.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holSoundness.ml";;
needs "candle/standard/semantics/holExtension.ml";;
needs "candle/standard/semantics/holBool.ml";;
needs "candle/standard/semantics/holAxioms.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering: as in holBool.ml and holAxioms.ml (see their      *)
(* headers and those of holSemantics.ml and holSyntax.ml).  HOL4's variable  *)
(* inf (a HOL Light constant) is inf'.  Local helpers that are not HOL4      *)
(* theorems are CBOOLAUX_.                                                   *)

let consistent_theory_def = cake_def
  `consistent_theory (thy:thy) <=>
     (thy,[]) |- (hol_Var (implode "x") (Tyapp (implode "bool") []) ===
                  hol_Var (implode "x") (Tyapp (implode "bool") [])) /\
     ~((thy,[]) |- (hol_Var (implode "x") (Tyapp (implode "bool") []) ===
                    hol_Var (implode "y") (Tyapp (implode "bool") [])))`;;

let proves_consistent = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !thy. theory_ok thy /\ (?i. models0 mem i thy) ==> consistent_theory thy`,
  DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def] o MATCH_MP theory_ok_sig) THEN
  REWRITE_TAC[consistent_theory_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC proves_REFL THEN
    ASM_REWRITE_TAC[hol_term_ok_def; type_ok_def; ALL; LENGTH];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    (MATCH_MP proves_sound (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
  REWRITE_TAC[entails0_def] THEN
  DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[satisfies0_def; ALL] THEN
  QPAT_ASSUM "models0 _ _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[models0_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_std_type_facts) THEN
  ABBREV_TAC
   `sigma = \(x:mlstring,ty:hol_type).
      if (x,ty) = (implode "x",Tyapp (implode "bool") []) then setSpec_true (mem:U->U->bool)
      else if (x,ty) = (implode "y",Tyapp (implode "bool") []) then setSpec_false mem
      else @v. mem v (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                             (combin_K (setSpec_two mem)) ty)` THEN
  DISCH_THEN(MP_TAC o SPEC
    `(combin_K (setSpec_two (mem:U->U->bool)):mlstring->U, sigma:mlstring#hol_type->U)`) THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> F) ==> (a ==> b) ==> F`) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[is_valuation0_def; is_type_valuation0_def; is_term_valuation0_def;
                FST; SND; K_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[boolean_in_boolset]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN DISCH_TAC THEN
    EXPAND_TAC "sigma" THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[typesem_def; MAP] THENL
     [ASM_SIMP_TAC[CBOOLAUX_true_in_boolset];
      ASM_SIMP_TAC[CBOOLAUX_false_in_boolset];
      CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP typesem_inhabited) THEN
      EXISTS_TAC `FST (FST (thy:thy))` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[is_type_valuation0_def; K_THM] THEN ASM_MESON_TAC[boolean_in_boolset];
        QPAT_ASSUM "is_interpretation0 _ _ _" (MP_TAC o REWRITE_RULE[is_interpretation0_def]) THEN
        SIMP_TAC[]]];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o ISPECL
     [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
      `(combin_K (setSpec_two (mem:U->U->bool)):mlstring->U, sigma:mlstring#hol_type->U)`;
      `hol_Var (implode "x") (Tyapp (implode "bool") [])`;
      `hol_Var (implode "y") (Tyapp (implode "bool") [])`; `SND (FST (thy:thy))`] o
     MATCH_MP termsem_equation) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[is_structure0_def] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP term_ok_clauses (MATCH_MP theory_ok_sig th);
                                      typeof_def]) THEN
    ASM_REWRITE_TAC[type_ok_def; ALL; LENGTH];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[boolean_eq_true; termsem0_def; SND] THEN
  EXPAND_TAC "sigma" THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC([PAIR_EQ] @ CBOOLAUX_STRING_THMS) THEN
  ASM_SIMP_TAC[true_neq_false]);;

(* finite maps with one or two keys *)
let CBOOLAUX_FEVERY_1 = prove
 (`!(P:A#B->bool) k v. FEVERY P (FEMPTY |+ (k,v)) <=> P (k,v)`,
  REWRITE_TAC[FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`k:A`; `v:B`]) THEN REWRITE_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]]);;

let CBOOLAUX_FEVERY_2 = prove
 (`!(P:A#B->bool) k1 v1 k2 v2.
     FEVERY P (FEMPTY |+ (k1,v1) |+ (k2,v2)) <=> P (k2,v2) /\ (~(k2 = k1) ==> P (k1,v1))`,
  REWRITE_TAC[FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`k2:A`; `v2:B`]) THEN REWRITE_TAC[];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`k1:A`; `v1:B`]) THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]]);;

let init_ctxt_has_model = prove
 (`is_set_theory (mem:U->U->bool) ==>
   ?i. models0 mem i
         ((alist_to_fmap (FLAT (MAP types_of_upd init_ctxt)),
           alist_to_fmap (FLAT (MAP consts_of_upd init_ctxt))),
          set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                 init_ctxt)))`,
  DISCH_TAC THEN
  EXISTS_TAC
   `(\x. if x = implode "fun" then (\ls. setSpec_funspace (mem:U->U->bool) (HD ls) (HD (TL ls)))
         else if x = implode "bool" then combin_K (setSpec_two mem) else ARB),
    (combin_K (\l. abstract (mem:U->U->bool) (HD l) (setSpec_funspace mem (HD l) (setSpec_two mem))
              (\x. abstract mem (HD l) (setSpec_two mem) (\y. boolean mem (x = y))))
       :mlstring->U list->U)` THEN
  REWRITE_TAC[models0_def; init_ctxt_def; MAP; FLAT; APPEND; types_of_upd_def;
              consts_of_upd_def; axexts_of_upd_def; conexts_of_upd_def; alist_to_fmap_thm;
              set_of_list; NOT_IN_EMPTY; FST; SND] THEN
  REWRITE_TAC[is_interpretation0_def; is_std_interpretation0_def; is_std_type_assignment0_def;
              is_type_assignment0_def; is_term_assignment0_def; interprets0_def;
              CBOOLAUX_FEVERY_1; CBOOLAUX_FEVERY_2; FST; SND; K_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC([HD; TL; LENGTH_EQ_NIL; ALL] @ CBOOLAUX_STRING_THMS) THEN
  REWRITE_TAC[K_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[K_THM] THEN MESON_TAC[boolean_in_boolset; ASSUME `is_set_theory (mem:U->U->bool)`];
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 = SUC (SUC 0)`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
    REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN REWRITE_TAC[HD; TL] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP funspace_inhabited) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC CBOOLAUX_TYVARS_THMS THEN
    REWRITE_TAC([typesem_def; MAP; HD; TL; K_THM] @ CBOOLAUX_STRING_THMS) THEN
    X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
    ASM_SIMP_TAC[boolean_in_boolset]]);;

let min_hol_consistent = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt. ctxt extends init_ctxt /\
          (!p. MEM (hol_NewAxiom p) ctxt ==> MEM (hol_NewAxiom p) init_ctxt)
          ==> consistent_theory
                ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd)) ctxt)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP proves_consistent) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[extends_theory_ok; init_theory_ok];
    FIRST_ASSUM(X_CHOOSE_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
                MATCH_MP init_ctxt_has_model) THEN
    MP_TAC(SPECL [`init_ctxt`; `ctxt:update list`]
             (MATCH_MP extends_consistent (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
    ASM_REWRITE_TAC[init_theory_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* computations in the HOL contexts built from init_ctxt *)
let CBOOLAUX_EVAL_CTXT_TAC : tactic =
  CBOOLAUX_EVAL CBOOLAUX_AX_THMS THEN
  REWRITE_TAC[MAP; FLAT; APPEND; consts_of_upd_def; types_of_upd_def; alist_to_fmap_thm;
              FLOOKUP_UPDATE; FDOM_FUPDATE; FDOM_FEMPTY; IN_INSERT; NOT_IN_EMPTY;
              FLOOKUP_EMPTY] THEN
  CBOOLAUX_EVAL CBOOLAUX_AX_THMS;;

let fhol_ctxt_def = cake_def
  `fhol_ctxt = mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`;;

let CBOOLAUX_bool_init_std_sig = prove
 (`is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt init_ctxt))),
               alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt init_ctxt))))`,
  MATCH_MP_TAC is_bool_sig_std THEN MATCH_MP_TAC bool_has_bool_sig THEN
  MP_TAC(MATCH_MP theory_ok_sig init_theory_ok) THEN REWRITE_TAC[FST]);;

let fhol_extends_bool = prove
 (`fhol_ctxt extends (mk_bool_ctxt init_ctxt)`,
  REWRITE_TAC[fhol_ctxt_def] THEN MATCH_MP_TAC extends_trans THEN
  EXISTS_TAC `mk_eta_ctxt (mk_bool_ctxt init_ctxt)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC select_extends THEN
    REWRITE_TAC[is_std_sig_def; mk_eta_ctxt_def; mk_bool_ctxt_def; init_ctxt_def; FST; SND] THEN
    CBOOLAUX_EVAL CBOOLAUX_AX_THMS THEN
    REWRITE_TAC[MAP; FLAT; APPEND; consts_of_upd_def; types_of_upd_def; alist_to_fmap_thm;
                FLOOKUP_UPDATE; FDOM_FUPDATE; FDOM_FEMPTY; IN_INSERT; NOT_IN_EMPTY;
                FLOOKUP_EMPTY] THEN
    CBOOLAUX_EVAL CBOOLAUX_AX_THMS;
    MATCH_MP_TAC eta_extends THEN ACCEPT_TAC CBOOLAUX_bool_init_std_sig]);;

(* the model of fhol_ctxt, with the interpretations of the connectives      *)
let CBOOLAUX_theory_ok_bool_init = prove
 (`theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt init_ctxt))),
               alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt init_ctxt)))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                     (mk_bool_ctxt init_ctxt))))`,
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
  EXISTS_TAC `init_ctxt` THEN REWRITE_TAC[bool_extends_init; init_theory_ok]);;

let CBOOLAUX_theory_ok_eta_bool_init = prove
 (`theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))),
               alist_to_fmap (FLAT (MAP consts_of_upd (mk_eta_ctxt (mk_bool_ctxt init_ctxt))))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                     (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))))`,
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
  EXISTS_TAC `mk_bool_ctxt init_ctxt` THEN REWRITE_TAC[CBOOLAUX_theory_ok_bool_init] THEN
  MATCH_MP_TAC eta_extends THEN ACCEPT_TAC CBOOLAUX_bool_init_std_sig);;

let CBOOLAUX_theory_ok_fhol = prove
 (`theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd fhol_ctxt)),
               alist_to_fmap (FLAT (MAP consts_of_upd fhol_ctxt))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                     fhol_ctxt)))`,
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
  EXISTS_TAC `mk_bool_ctxt init_ctxt` THEN
  REWRITE_TAC[CBOOLAUX_theory_ok_bool_init; fhol_extends_bool]);;

(* the interpretation of a constant of mk_eta_ctxt (mk_bool_ctxt init_ctxt) *)
(* carries over to an interpretation equal on its signature               *)
let CBOOLAUX_EQUAL_ON_INTERP_TAC ty : tactic =
  REWRITE_TAC CBOOLAUX_ints THEN MATCH_MP_TAC equal_on_interprets THEN
  MAP_EVERY EXISTS_TAC
   [`(alist_to_fmap (FLAT (MAP types_of_upd (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))),
      alist_to_fmap (FLAT (MAP consts_of_upd (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))))`;
    `i2:(mlstring->U list->U)#(mlstring->U list->U)`; ty] THEN
  RULE_ASSUM_TAC(REWRITE_RULE CBOOLAUX_ints) THEN ASM_REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[mk_eta_ctxt_def; mk_bool_ctxt_def; init_ctxt_def] THEN
  CBOOLAUX_EVAL_CTXT_TAC THEN REWRITE_TAC CBOOLAUX_TYVARS_THMS THEN
  CBOOLAUX_EVAL CBOOLAUX_AX_THMS;;

let CBOOLAUX_fhol_model = prove
 (`is_set_theory (mem:U->U->bool) ==>
   ?i. models0 mem i
         ((alist_to_fmap (FLAT (MAP types_of_upd fhol_ctxt)),
           alist_to_fmap (FLAT (MAP consts_of_upd fhol_ctxt))),
          set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                 fhol_ctxt))) /\
       is_implies_interpretation0 mem (SND i) /\ is_and_interpretation0 mem (SND i) /\
       is_forall_interpretation0 mem (SND i) /\ is_exists_interpretation0 mem (SND i) /\
       is_not_interpretation0 mem (SND i)`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `i0:(mlstring->U list->U)#(mlstring->U list->U)` o
              MATCH_MP init_ctxt_has_model) THEN
  MP_TAC(SPECL [`init_ctxt`; `mk_bool_ctxt init_ctxt`]
           (MATCH_MP extends_consistent (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
  REWRITE_TAC[bool_extends_init] THEN
  DISCH_THEN(MP_TAC o SPEC `i0:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[init_theory_ok] THEN ANTS_TAC THENL
   [REWRITE_TAC[mk_bool_ctxt_def; init_ctxt_def; MEM; distinctness "update"]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i2:(mlstring->U list->U)#(mlstring->U list->U)`
               STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `is_bool_interpretation0 (mem:U->U->bool)
                  (i2:(mlstring->U list->U)#(mlstring->U list->U))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP bool_has_bool_interpretation) THEN
    EXISTS_TAC `init_ctxt` THEN ASM_REWRITE_TAC[CBOOLAUX_theory_ok_bool_init];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `models0 (mem:U->U->bool) (i2:(mlstring->U list->U)#(mlstring->U list->U))
      ((alist_to_fmap (FLAT (MAP types_of_upd (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))),
        alist_to_fmap (FLAT (MAP consts_of_upd (mk_eta_ctxt (mk_bool_ctxt init_ctxt))))),
       set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                              (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))))`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `mk_bool_ctxt init_ctxt` (MATCH_MP eta_has_model
      (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
    REWRITE_TAC[CBOOLAUX_bool_init_std_sig] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `mk_eta_ctxt (mk_bool_ctxt init_ctxt)` (MATCH_MP select_has_model
    (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CBOOLAUX_theory_ok_eta_bool_init; is_implies_sig_def] THEN
    REWRITE_TAC[mk_eta_ctxt_def; mk_bool_ctxt_def; init_ctxt_def] THEN
    CBOOLAUX_EVAL_CTXT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i2:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[is_bool_interpretation0_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i3:(mlstring->U list->U)#(mlstring->U list->U)`
               STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i3:(mlstring->U list->U)#(mlstring->U list->U)` THEN
  ASM_REWRITE_TAC[fhol_ctxt_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_bool_interpretation0_def] o
    check (fun th -> can (term_match [] `is_bool_interpretation0 (mem:U->U->bool) i`)
                         (concl th))) THEN
  REPEAT CONJ_TAC THENL
   [CBOOLAUX_EQUAL_ON_INTERP_TAC CBOOLAUX_ty_bbb;
    CBOOLAUX_EQUAL_ON_INTERP_TAC CBOOLAUX_ty_bbb;
    CBOOLAUX_EQUAL_ON_INTERP_TAC CBOOLAUX_ty_qbb;
    CBOOLAUX_EQUAL_ON_INTERP_TAC CBOOLAUX_ty_qbb;
    CBOOLAUX_EQUAL_ON_INTERP_TAC CBOOLAUX_ty_bb]);;

let fhol_has_model = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt. ctxt extends fhol_ctxt /\
          (!p. MEM (hol_NewAxiom p) ctxt ==> MEM (hol_NewAxiom p) fhol_ctxt)
          ==> theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                              (conexts_of_upd upd)) ctxt))) /\
              ?i. models0 mem i
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd)) ctxt)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[extends_theory_ok; CBOOLAUX_theory_ok_fhol]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `i3:(mlstring->U list->U)#(mlstring->U list->U)`
    STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_fhol_model) THEN
  MP_TAC(SPECL [`fhol_ctxt`; `ctxt:update list`]
           (MATCH_MP extends_consistent (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
  ASM_REWRITE_TAC[CBOOLAUX_theory_ok_fhol] THEN
  DISCH_THEN(MP_TAC o SPEC `i3:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let fhol_consistent = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt. ctxt extends fhol_ctxt /\
          (!p. MEM (hol_NewAxiom p) ctxt ==> MEM (hol_NewAxiom p) fhol_ctxt)
          ==> consistent_theory
                ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd)) ctxt)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP proves_consistent) THEN
  FIRST_ASSUM(MP_TAC o SPEC `ctxt:update list` o MATCH_MP fhol_has_model) THEN
  ASM_REWRITE_TAC[]);;

let hol_ctxt_def = cake_def
  `hol_ctxt = mk_infinity_ctxt fhol_ctxt`;;

let hol_extends_fhol = prove
 (`hol_ctxt extends fhol_ctxt`,
  REWRITE_TAC[hol_ctxt_def] THEN MATCH_MP_TAC infinity_extends THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
    EXISTS_TAC `mk_bool_ctxt init_ctxt` THEN REWRITE_TAC[fhol_extends_bool] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
    EXISTS_TAC `init_ctxt` THEN REWRITE_TAC[bool_extends_init; init_theory_ok];
    ALL_TAC] THEN
  REWRITE_TAC[fhol_ctxt_def; mk_select_ctxt_def; mk_eta_ctxt_def; mk_bool_ctxt_def;
              init_ctxt_def] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN CBOOLAUX_EVAL_CTXT_TAC THEN
  REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  CBOOLAUX_EVAL CBOOLAUX_AX_THMS);;

let hol_extends_bool = prove
 (`hol_ctxt extends (mk_bool_ctxt init_ctxt)`,
  MATCH_MP_TAC extends_trans THEN
  ASM_MESON_TAC[hol_extends_fhol; fhol_extends_bool]);;

let CBOOLAUX_theory_ok_hol = prove
 (`theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd hol_ctxt)),
               alist_to_fmap (FLAT (MAP consts_of_upd hol_ctxt))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                     hol_ctxt)))`,
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
  EXISTS_TAC `fhol_ctxt` THEN REWRITE_TAC[CBOOLAUX_theory_ok_fhol; hol_extends_fhol]);;

let CBOOLAUX_hol_model = prove
 (`is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf') ==>
   ?i. models0 mem i
         ((alist_to_fmap (FLAT (MAP types_of_upd hol_ctxt)),
           alist_to_fmap (FLAT (MAP consts_of_upd hol_ctxt))),
          set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                 hol_ctxt)))`,
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `i3:(mlstring->U list->U)#(mlstring->U list->U)`
    STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_fhol_model) THEN
  MP_TAC(SPEC `fhol_ctxt` (MATCH_MP infinity_has_model
    (CONJ (ASSUME `is_set_theory (mem:U->U->bool)`)
          (ASSUME `?inf'. is_infinite (mem:U->U->bool) inf'`)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC(CBOOLAUX_theory_ok_fhol :: CBOOLAUX_sigs) THEN
    REWRITE_TAC[fhol_ctxt_def; mk_select_ctxt_def; mk_eta_ctxt_def; mk_bool_ctxt_def;
                init_ctxt_def] THEN
    CBOOLAUX_EVAL_CTXT_TAC THEN
    REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    CBOOLAUX_EVAL CBOOLAUX_AX_THMS;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i3:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[hol_ctxt_def] THEN MESON_TAC[]);;

let hol_has_model = prove
 (`is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf') ==>
   !ctxt. ctxt extends hol_ctxt /\
          (!p. MEM (hol_NewAxiom p) ctxt ==> MEM (hol_NewAxiom p) hol_ctxt)
          ==> theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                              (conexts_of_upd upd)) ctxt))) /\
              ?i. models0 mem i
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd)) ctxt)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[extends_theory_ok; CBOOLAUX_theory_ok_hol]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `i4:(mlstring->U list->U)#(mlstring->U list->U)` o
              MATCH_MP CBOOLAUX_hol_model) THEN
  MP_TAC(SPECL [`hol_ctxt`; `ctxt:update list`]
           (MATCH_MP extends_consistent (CONJUNCT1 (ASSUME
             `is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf')`)))) THEN
  ASM_REWRITE_TAC[CBOOLAUX_theory_ok_hol] THEN
  DISCH_THEN(MP_TAC o SPEC `i4:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let hol_consistent = prove
 (`is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf')
   ==> !ctxt. ctxt extends hol_ctxt /\
              (!p. MEM (hol_NewAxiom p) ctxt ==> MEM (hol_NewAxiom p) hol_ctxt)
              ==> consistent_theory
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd)) ctxt)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(MATCH_MP proves_consistent (CONJUNCT1 (ASSUME
    `is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf')`))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `ctxt:update list` o MATCH_MP hol_has_model) THEN
  ASM_REWRITE_TAC[]);;
