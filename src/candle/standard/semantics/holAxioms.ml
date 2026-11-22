(* ========================================================================= *)
(* holAxioms: port of HOL4 candle/standard/semantics/holAxiomsScript.sml     *)
(* (CakeML v3479).  Consistency of each of the axioms (for the axiom of      *)
(* infinity, under an additional assumption on the set theory).              *)
(* ========================================================================= *)

needs "candle/standard/semantics/holBool.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holExtension.ml";;
needs "hol4/libext.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - As in holBool.ml (see its header and those of holSemantics.ml and       *)
(*   holAxiomsSyntax.ml): the constants with a mem argument are written with *)
(*   it (good_select is good_select0 mem, base_select is base_select0 mem,   *)
(*   models is models0 mem, ...), the set-theory and syntax overloads are    *)
(*   written out.  HOL4's variable inf (a HOL Light constant) is inf'.       *)
(* - Local helpers that are not HOL4 theorems are CBOOLAUX_.                 *)

(* is_std_sig sig: hol_term_ok sig of terms built with the equality *)
let CBOOLAUX_STD_TERM_OK_TAC : tactic =
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP term_ok_clauses th]) THEN
  REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def; codomain_def; injectivity "hol_type"; CONS_11;
              CBOOLAUX_EXISTS_REFL; RIGHT_EXISTS_AND_THM; CBOOLAUX_typeof_equation];;

let eta_has_model = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt. is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
     ==> !i. models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt)))
             ==> models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd (mk_eta_ctxt ctxt))),
                 alist_to_fmap (FLAT (MAP consts_of_upd (mk_eta_ctxt ctxt)))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd))
                                       (mk_eta_ctxt ctxt))))`,
  DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[mk_eta_ctxt_def; CBOOLAUX_tysof_NewAxiom; CBOOLAUX_tmsof_NewAxiom] THEN
  REWRITE_TAC[MAP; FLAT; axexts_of_upd_def; conexts_of_upd_def; APPEND; set_of_list] THEN
  REWRITE_TAC[models0_def; FST; SND; IN_INSERT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:hol_term` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[satisfies0_def; ALL; FST; SND] THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL
     [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
        alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`;
      `i:(mlstring->U list->U)#(mlstring->U list->U)`;
      `v:(mlstring->U)#(mlstring#hol_type->U)`] o
     MATCH_MP termsem_equation) THEN
  REWRITE_TAC[SND] THEN
  DISCH_THEN(fun th -> W(fun (_,w) -> MP_TAC (PART_MATCH (lhs o rand) th (lhs w)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[is_structure0_def] THEN CBOOLAUX_STD_TERM_OK_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  CBOOLAUX_BOOLEAN_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_std_type_facts) THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  SUBGOAL_THEN
   `mem (SND (v:(mlstring->U)#(mlstring#hol_type->U))
          (implode "f",Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
        (funspace mem (FST v (implode "A")) (FST v (implode "B")))`
  MP_TAC THENL
   [UNDISCH_TAC `is_valuation0 (mem:U->U->bool)
                   (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) v` THEN
    REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`implode "f"`;
      `Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[typesem_def; MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[is_std_sig_def; FST]) THEN
    ASM_REWRITE_TAC[type_ok_def; ALL; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (MATCH_MP in_funspace_abstract th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN
  ASM_SIMP_TAC[apply_abstract]);;

(* HOL4: Definition good_select_def (Overload good_select = good_select0 ^mem) *)
let good_select0_def = cake_def
  `good_select0 (mem:U->U->bool) (select:U->(U->bool)->U) <=>
     (!ty p x. mem x ty ==> mem (select ty p) ty /\ (p x ==> p (select ty p)))`;;

let select_has_model_gen = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt.
     ~(implode "@" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     is_implies_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt)))
     ==> !i select.
           models0 mem i
             ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
               alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                   (conexts_of_upd upd)) ctxt))) /\
           is_implies_interpretation0 mem (SND i) /\
           good_select0 mem select
           ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                              alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                    models0 mem i'
                      ((alist_to_fmap (FLAT (MAP types_of_upd (mk_select_ctxt ctxt))),
                        alist_to_fmap (FLAT (MAP consts_of_upd (mk_select_ctxt ctxt)))),
                       set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                            (conexts_of_upd upd))
                                              (mk_select_ctxt ctxt)))) /\
                    SND i' (implode "@") =
                    (\ls. abstract mem (funspace mem (HD ls) (two mem)) (HD ls)
                            (\p. select (HD ls) (holds mem p)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def; FST; SND] o
              MATCH_MP theory_ok_sig) THEN
  ABBREV_TAC `sel = \l. abstract (mem:U->U->bool) (funspace mem (HD l) (two mem)) (HD l)
                           (\p. select (HD l) (holds mem p))` THEN
  EXISTS_TAC `(FST (i:(mlstring->U list->U)#(mlstring->U list->U)),
               (implode "@" =+ (sel:U list->U)) (SND i))` THEN
  REWRITE_TAC[FST; SND; APPLY_UPDATE_THM] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[equal_on_def; FST; SND; APPLY_UPDATE_THM] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[mk_select_ctxt_def; CBOOLAUX_tysof_NewAxiom; CBOOLAUX_tmsof_NewAxiom;
              CBOOLAUX_tysof_NewConst; CBOOLAUX_tmsof_NewConst] THEN
  REWRITE_TAC[MAP; FLAT; axexts_of_upd_def; conexts_of_upd_def; APPEND; set_of_list] THEN
  REWRITE_TAC[models0_def; FST; SND; IN_INSERT] THEN
  QPAT_ASSUM "models0 _ _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[models0_def; FST; SND]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_std_type_facts) THEN
  REPEAT CONJ_TAC THENL
   [(* the interpretation *)
    UNDISCH_TAC `is_interpretation0 (mem:U->U->bool)
                   (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                    alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i` THEN
    REWRITE_TAC[is_interpretation0_def; FST; SND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `is_term_assignment0 (mem:U->U->bool)
                   (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (SND i)` THEN
    REWRITE_TAC[is_term_assignment0_def; FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:mlstring`; `ty:hol_type`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
      REWRITE_TAC CBOOLAUX_TYVARS_THMS THEN EXPAND_TAC "sel" THEN
      REWRITE_TAC[HD; typesem_def; MAP] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `tau:mlstring->U` THEN REWRITE_TAC[is_type_valuation0_def] THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[good_select0_def]) THEN ASM_MESON_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `ty:hol_type`]) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]];
    (* standard *)
    UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool) i` THEN
    REWRITE_TAC([is_std_interpretation0_def; FST; SND; interprets0_def; APPLY_UPDATE_THM] @
                CBOOLAUX_STRING_THMS);
    ALL_TAC] THEN
  (* the axioms *)
  GEN_TAC THEN STRIP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC satisfies_extend THEN
    MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd ctxt))`;
                          `alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`] THEN
    ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL] THEN
    SUBGOAL_THEN `ALL (hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                                     alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) [p]`
      ASSUME_TAC THENL
     [REWRITE_TAC[ALL] THEN ASM_MESON_TAC[theory_ok_def; FST; SND]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC satisfies_sig THEN
    EXISTS_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig)] THEN
  (* the select axiom *)
  ASM_REWRITE_TAC[satisfies0_def; ALL; FST; SND] THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_implies_sig_def]) THEN
  SUBGOAL_THEN `SND (i:(mlstring->U list->U)#(mlstring->U list->U)) (implode "==>") [] =
                Boolrel0 (mem:U->U->bool) (==>)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`mem:U->U->bool`; `SND (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                   `implode "==>"`; `K (Boolrel0 (mem:U->U->bool) (==>)):U list->U`]
      CBOOLAUX_interp_nil_value) THEN
    ASM_REWRITE_TAC[GSYM is_implies_interpretation0_def; K_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC([termsem0_def; identity_instance; FLOOKUP_UPDATE] @ CBOOLAUX_STRING_THMS) THEN
  REWRITE_TAC CBOOLAUX_TYVARS_THMS THEN
  ASM_REWRITE_TAC([APPLY_UPDATE_THM; HD; MAP] @ CBOOLAUX_STRING_THMS) THEN
  EXPAND_TAC "sel" THEN REWRITE_TAC[HD] THEN
  SUBGOAL_THEN
   `mem (SND (v:(mlstring->U)#(mlstring#hol_type->U))
          (implode "P", Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]))
        (funspace mem (FST v (implode "A")) (two mem)) /\
    mem (SND v (implode "x", Tyvar (implode "A"))) (FST v (implode "A"))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `is_valuation0 (mem:U->U->bool) (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))
                   (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) v` THEN
    REWRITE_TAC[is_valuation0_def; is_term_valuation0_def] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_THEN(fun th ->
      MP_TAC(SPECL [`implode "P"`; `Tyapp (implode "fun") [Tyvar (implode "A");
                                     Tyapp (implode "bool") []]`] th) THEN
      MP_TAC(SPECL [`implode "x"`; `Tyvar (implode "A")`] th)) THEN
    ASM_REWRITE_TAC[type_ok_def; ALL; LENGTH; typesem_def; MAP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `pp = SND (v:(mlstring->U)#(mlstring#hol_type->U))
                    (implode "P", Tyapp (implode "fun") [Tyvar (implode "A");
                                                          Tyapp (implode "bool") []])` THEN
  ABBREV_TAC `xx = SND (v:(mlstring->U)#(mlstring#hol_type->U))
                      (implode "x", Tyvar (implode "A"))` THEN
  ABBREV_TAC `ta = FST (v:(mlstring->U)#(mlstring#hol_type->U)) (implode "A")` THEN
  SUBGOAL_THEN `mem ((select:U->(U->bool)->U) ta (holds mem pp)) ta` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[good_select0_def]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[apply_abstract] THEN
  SUBGOAL_THEN `mem (apply mem pp xx) (two (mem:U->U->bool)) /\
                mem (apply mem pp ((select:U->(U->bool)->U) ta (holds mem pp))) (two mem)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP apply_in_rng) THEN
    EXISTS_TAC `ta:U` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CBOOLAUX_apply_boolrel] THEN CBOOLAUX_BOOLEAN_TAC THEN
  REWRITE_TAC[GSYM holds_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_select0_def]) THEN ASM_MESON_TAC[]);;

(* HOL4: Definition base_select_def (Overload base_select = base_select0 ^mem) *)
let base_select0_def = cake_def
  `base_select0 (mem:U->U->bool) ty (p:U->bool) =
     if ?x. mem x ty then
       (match some x. mem x ty /\ p x with NONE -> (@x. mem x ty) | SOME v -> v)
     else ARB`;;

let good_select_base_select = prove
 (`is_set_theory (mem:U->U->bool) ==> good_select0 mem (base_select0 mem)`,
  DISCH_TAC THEN REWRITE_TAC[good_select0_def; base_select0_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:U. (mem:U->U->bool) x ty` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[SELECT_AX] `(?x:U. P x) ==> P (@x. P x)`)) THEN
    MESON_TAC[];
    CONJ_TAC THENL [ASM_MESON_TAC[SELECT_AX]; ASM_MESON_TAC[]]]);;

let select_has_model = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt.
     ~(implode "@" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     is_implies_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt)))
     ==> !i. models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
             is_implies_interpretation0 mem (SND i)
             ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                                alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                      models0 mem i'
                        ((alist_to_fmap (FLAT (MAP types_of_upd (mk_select_ctxt ctxt))),
                          alist_to_fmap (FLAT (MAP consts_of_upd (mk_select_ctxt ctxt)))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                              (conexts_of_upd upd))
                                                (mk_select_ctxt ctxt))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ctxt:update list` o MATCH_MP select_has_model_gen) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:(mlstring->U list->U)#(mlstring->U list->U)`;
                             `base_select0 (mem:U->U->bool)`]) THEN
  ASM_SIMP_TAC[good_select_base_select] THEN MESON_TAC[]);;

(* The axiom of infinity.  HOL4 proves infinity_has_model_gen in one proof; *)
(* here the model of the extended context is built from a model of the     *)
(* context with the definitions of ONE_ONE and ONTO (CBOOLAUX_infinity_core), *)
(* with the meanings of ONE_ONE and ONTO computed as in holBool.ml.          *)

(* the instance of a constant of type (A -> B) -> bool *)
let CBOOLAUX_instance_AB = prove
 (`!tmsig (i:(mlstring->U list->U)#(mlstring->U list->U)) c ty1 ty2 tau.
     FLOOKUP tmsig c =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []])
     ==> instance tmsig i c
           (Tyapp (implode "fun") [Tyapp (implode "fun") [ty1; ty2];
                                   Tyapp (implode "bool") []]) tau =
         SND i c [typesem (FST i) tau ty1; typesem (FST i) tau ty2]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmsig:tmsig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `c:mlstring`;
                 `Tyapp (implode "fun") [Tyapp (implode "fun") [ty1; ty2];
                                         Tyapp (implode "bool") []]`;
                 `Tyapp (implode "fun")
                    [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                     Tyapp (implode "bool") []]`;
                 `[(ty1:hol_type,Tyvar (implode "A")); (ty2,Tyvar (implode "B"))]`]
                instance_def) THEN
  ASM_REWRITE_TAC([TYPE_SUBST_def; MAP; REV_ASSOCD] @ CBOOLAUX_STRING_THMS) THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(REWRITE_CONV (CBOOLAUX_TYVARS_THMS @ CBOOLAUX_STRING_THMS @
             [string_lt_def; char_lt_def; ORD_DEF; BITVAL_CLAUSES]) THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC(o_THM :: TYPE_SUBST_def :: REV_ASSOCD :: typesem_def :: MAP :: APPEND ::
              CBOOLAUX_STRING_THMS));;

let CBOOLAUX_TYVARS_STR_CONV =
  REPEATC (CHANGED_CONV
   (REWRITE_CONV (CBOOLAUX_TYVARS_THMS @ CBOOLAUX_STRING_THMS @
                  [string_lt_def; char_lt_def; ORD_DEF; BITVAL_CLAUSES]) THENC
    NUM_REDUCE_CONV));;

(* hol_term_ok in a standard signature whose lookups are assumptions *)
let CBOOLAUX_TERM_OK_STD_THMS =
  [welltyped_equation; EQUATION_HAS_TYPE_BOOL; CONJUNCT1 hol_term_ok_def;
   CONJUNCT1 (CONJUNCT2 hol_term_ok_def);
   CONJUNCT1 (CONJUNCT2 (CONJUNCT2 hol_term_ok_def)); CBOOLAUX_term_ok_Abs_Var;
   term_ok_equation; type_ok_def; ALL; LENGTH; ARITH_RULE `SUC (SUC 0) = 2`;
   CONJUNCT1 WELLTYPED_CLAUSES; CONJUNCT1 (CONJUNCT2 WELLTYPED_CLAUSES);
   CONJUNCT1 (CONJUNCT2 (CONJUNCT2 WELLTYPED_CLAUSES)); CBOOLAUX_welltyped_Abs_Var;
   typeof_def; codomain_def; CBOOLAUX_typeof_equation;
   TYPE_SUBST_def; MAP; REV_ASSOCD; option_INJ; UNWIND_THM1; hol_tyvar_inst_exists;
   CBOOLAUX_EXISTS_REFL; RIGHT_EXISTS_AND_THM; FST; SND] @ CBOOLAUX_STRING_THMS;;

(* termsem of an equation at a valuation of a model *)
let CBOOLAUX_termsem_equation_val = prove
 (`!(mem:U->U->bool) thy i v s t.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\
     is_valuation0 mem (FST (FST thy)) (FST i) v /\ hol_term_ok (FST thy) (s === t)
     ==> termsem0 mem (SND (FST thy)) i v (s === t) =
         boolean mem (termsem0 mem (SND (FST thy)) i v s = termsem0 mem (SND (FST thy)) i v t)`,
  MESON_TAC[CBOOLAUX_termsem_equation; CBOOLAUX_structure]);;

(* the termsem lemmas of the connectives, with their side conditions, in a  *)
(* standard signature whose lookups are assumptions                          *)
let CBOOLAUX_SEM_SIMP_STD_TAC thl : tactic =
  W(fun (asl,w) ->
    let st = find (fun th -> can (term_match [] `is_set_theory (mem:U->U->bool)`) (concl th))
                  (map snd asl) in
    let sems = map (fun th -> MATCH_MP th st)
                 [termsem_and; termsem_implies; termsem_forall; termsem_exists; termsem_not] in
    ASM_SIMP_TAC(sems @ CBOOLAUX_TERM_OK_STD_THMS @
                 [CBOOLAUX_termsem_equation_val; CBOOLAUX_is_valuation_update2;
                  typesem_def] @ thl));;

(* the same, for a signature given as a pair term sg (FST, SND reduced) *)
let CBOOLAUX_SEM_SIMP_SIG_TAC sg thl : tactic =
  W(fun (asl,w) ->
    let st = find (fun th -> can (term_match [] `is_set_theory (mem:U->U->bool)`) (concl th))
                  (map snd asl) in
    let sems = map (fun th -> REWRITE_RULE[FST; SND] (ISPEC sg (MATCH_MP th st)))
                 [termsem_and; termsem_implies; termsem_forall; termsem_exists; termsem_not] in
    ASM_SIMP_TAC(sems @ CBOOLAUX_TERM_OK_STD_THMS @
                 [CBOOLAUX_is_valuation_update2; typesem_def; FLOOKUP_UPDATE] @ thl));;

(* interprets0 mem (SND i) n vs f from the axiom hol_Const n ty === D of the  *)
(* theory (an assumption): the goal becomes the termsem of D at a valuation v *)
let CBOOLAUX_FROM_AXIOM_TAC f : tactic =
  W(fun (asl,w) ->
    let isax t = try let l,r = dest_binop `(IN):hol_term->(hol_term->bool)->bool` t in
                     r = `SND (thy:thy)` with Failure _ -> false in
    let ax = find isax (map (concl o snd) asl) in
    let eq = lhand ax in
    let c = lhand eq and d = rand eq in
    let n, ty = rand(rator c), rand c in
    MP_TAC(ISPECL [`mem:U->U->bool`; `thy:thy`;
                   `i:(mlstring->U list->U)#(mlstring->U list->U)`; n; ty; d; f]
             CBOOLAUX_interp_from_def)) THEN
  CONV_TAC(LAND_CONV CBOOLAUX_TYVARS_STR_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC;;

(* the facts of a model of a theory with a standard signature, as assumptions *)
let CBOOLAUX_STD_SETUP_TAC : tactic =
  QPAT_ASSUM "models0 _ _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[models0_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_std_type_facts o
              check (fun th -> can (term_match [] `is_std_interpretation0 (mem:U->U->bool) i`)
                                   (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_std_interpretation_is_type o
              check (fun th -> can (term_match [] `is_std_interpretation0 (mem:U->U->bool) i`)
                                   (concl th))) THEN
  QPAT_ASSUM "theory_ok _" (fun th ->
    let ss = MATCH_MP theory_ok_sig th in
    ASSUME_TAC ss THEN STRIP_ASSUME_TAC (REWRITE_RULE[is_std_sig_def] ss)) THEN
  W(fun (asl,w) ->
    MAP_EVERY (fun th -> ASSUME_TAC(REWRITE_RULE CBOOLAUX_sigs th))
      (filter (fun th -> exists (fun d -> can (PART_MATCH lhs d) (concl th))
                           (map SPEC_ALL CBOOLAUX_sigs)) (map snd asl)));;

(* for a goal termsem0 mem tmenv i vv tm = _ : vv is a valuation and tm is ok *)
let CBOOLAUX_VAL_OK_STD_TAC : tactic =
  W(fun (asl,w) ->
     let tm = rand(lhs w) in
     let vv = rand(rator(lhs w)) in
     SUBGOAL_THEN (list_mk_comb(`is_valuation0 (mem:U->U->bool)`,
                    [`FST (FST (thy:thy))`;
                     `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`; vv]))
       ASSUME_TAC THENL
      [ASM_SIMP_TAC[CBOOLAUX_is_valuation_update2; PAIR; typesem_def; MAP];
       SUBGOAL_THEN (mk_comb(`hol_term_ok (FST (thy:thy))`, tm)) ASSUME_TAC THENL
        [ASM_SIMP_TAC CBOOLAUX_TERM_OK_STD_THMS; ALL_TAC]]);;

(* the meaning of ONE_ONE in a model of a theory with its definition *)
let CBOOLAUX_one_one_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\
     is_forall_sig (SND (FST thy)) /\ is_implies_sig (SND (FST thy)) /\
     is_forall_interpretation0 mem (SND i) /\ is_implies_interpretation0 mem (SND i) /\
     FLOOKUP (SND (FST thy)) (implode "ONE_ONE") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []]) /\
     (hol_Const (implode "ONE_ONE")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
            Tyapp (implode "bool") []]) ===
         hol_Abs
           (hol_Var (implode "f")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var (implode "x1") (Tyvar (implode "A")))
                 (hol_Comb
                    (hol_Const (implode "!")
                       (Tyapp (implode "fun")
                          [Tyapp (implode "fun")
                             [Tyvar (implode "A"); Tyapp (implode "bool") []];
                           Tyapp (implode "bool") []]))
                    (hol_Abs (hol_Var (implode "x2") (Tyvar (implode "A")))
                       (hol_Comb
                          (hol_Comb
                             (hol_Const (implode "==>")
                                (Tyapp (implode "fun")
                                   [Tyapp (implode "bool") [];
                                    Tyapp (implode "fun")
                                      [Tyapp (implode "bool") [];
                                       Tyapp (implode "bool") []]]))
                             ((hol_Comb
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x1") (Tyvar (implode "A")))) ===
                              (hol_Comb
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x2") (Tyvar (implode "A"))))))
                          ((hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                           (hol_Var (implode "x2") (Tyvar (implode "A")))))))))) IN SND thy
     ==> interprets0 mem (SND i) (implode "ONE_ONE") [implode "A"; implode "B"]
           (\l. abstract mem (funspace mem (HD l) (HD (TL l))) (two mem)
                  (\g. boolean mem
                         (!a1. mem a1 (HD l)
                               ==> !a2. mem a2 (HD l)
                                        ==> apply mem g a1 = apply mem g a2 ==> a1 = a2)))`,
  REPEAT STRIP_TAC THEN CBOOLAUX_FROM_AXIOM_TAC
    `\l. abstract (mem:U->U->bool) (funspace mem (HD l) (HD (TL l))) (two mem)
           (\g. boolean mem
                  (!a1. mem a1 (HD l)
                        ==> !a2. mem a2 (HD l)
                                 ==> apply mem g a1 = apply mem g a2 ==> a1 = a2))` THEN
  CBOOLAUX_STD_SETUP_TAC THEN
  ONCE_REWRITE_TAC[termsem0_def] THEN
  ASM_REWRITE_TAC [typesem_def; MAP; typeof_def; codomain_def; HD; TL] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `g:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_STD_TAC THEN
  CBOOLAUX_SEM_SIMP_STD_TAC [MAP] THEN
  CBOOLAUX_BOOLEAN_TAC THEN ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS);;

(* p /\ q with p as the context of q, for the simplifier *)
let CBOOLAUX_AND_CONTEXT = TAUT `(p /\ q <=> p /\ (p ==> q))`;;

(* the meaning of ONTO in a model of a theory with its definition *)
let CBOOLAUX_onto_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\
     is_forall_sig (SND (FST thy)) /\ is_exists_sig (SND (FST thy)) /\
     is_forall_interpretation0 mem (SND i) /\ is_exists_interpretation0 mem (SND i) /\
     FLOOKUP (SND (FST thy)) (implode "ONTO") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []]) /\
     (hol_Const (implode "ONTO")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
            Tyapp (implode "bool") []]) ===
         hol_Abs
           (hol_Var (implode "f")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
                 (hol_Comb
                    (hol_Const (implode "?")
                       (Tyapp (implode "fun")
                          [Tyapp (implode "fun")
                             [Tyvar (implode "A"); Tyapp (implode "bool") []];
                           Tyapp (implode "bool") []]))
                    (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                       ((hol_Var (implode "y") (Tyvar (implode "B"))) ===
                        (hol_Comb
                           (hol_Var (implode "f")
                              (Tyapp (implode "fun")
                                 [Tyvar (implode "A"); Tyvar (implode "B")]))
                           (hol_Var (implode "x") (Tyvar (implode "A")))))))))) IN SND thy
     ==> interprets0 mem (SND i) (implode "ONTO") [implode "A"; implode "B"]
           (\l. abstract mem (funspace mem (HD l) (HD (TL l))) (two mem)
                  (\g. boolean mem
                         (!b. mem b (HD (TL l)) ==> ?a. mem a (HD l) /\ b = apply mem g a)))`,
  REPEAT STRIP_TAC THEN CBOOLAUX_FROM_AXIOM_TAC
    `\l. abstract (mem:U->U->bool) (funspace mem (HD l) (HD (TL l))) (two mem)
           (\g. boolean mem
                  (!b. mem b (HD (TL l)) ==> ?a. mem a (HD l) /\ b = apply mem g a))` THEN
  CBOOLAUX_STD_SETUP_TAC THEN
  ONCE_REWRITE_TAC[termsem0_def] THEN
  ASM_REWRITE_TAC [typesem_def; MAP; typeof_def; codomain_def; HD; TL] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `g:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_STD_TAC THEN
  CBOOLAUX_SEM_SIMP_STD_TAC [MAP] THEN
  ONCE_REWRITE_TAC[CBOOLAUX_AND_CONTEXT] THEN CBOOLAUX_SEM_SIMP_STD_TAC [MAP] THEN
  REWRITE_TAC[TAUT `p /\ (p ==> q) <=> p /\ q`] THEN
  CBOOLAUX_BOOLEAN_TAC THEN ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS);;

(* a model of the context with ONE_ONE and ONTO gives one of the axiom of  *)
(* infinity, with the type ind interpreted as the infinite set inf'           *)
let CBOOLAUX_infinity_core = prove
 (`!(mem:U->U->bool) tys1 tms1 axs1 i1 inf'.
     is_set_theory mem /\ theory_ok ((tys1,tms1),axs1) /\
     models0 mem i1 ((tys1,tms1),axs1) /\
     ~(implode "ind" IN FDOM tys1) /\
     is_implies_sig tms1 /\ is_and_sig tms1 /\ is_forall_sig tms1 /\
     is_exists_sig tms1 /\ is_not_sig tms1 /\
     is_implies_interpretation0 mem (SND i1) /\ is_and_interpretation0 mem (SND i1) /\
     is_forall_interpretation0 mem (SND i1) /\ is_exists_interpretation0 mem (SND i1) /\
     is_not_interpretation0 mem (SND i1) /\
     FLOOKUP tms1 (implode "ONE_ONE") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []]) /\
     (hol_Const (implode "ONE_ONE")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
            Tyapp (implode "bool") []]) ===
         hol_Abs
           (hol_Var (implode "f")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var (implode "x1") (Tyvar (implode "A")))
                 (hol_Comb
                    (hol_Const (implode "!")
                       (Tyapp (implode "fun")
                          [Tyapp (implode "fun")
                             [Tyvar (implode "A"); Tyapp (implode "bool") []];
                           Tyapp (implode "bool") []]))
                    (hol_Abs (hol_Var (implode "x2") (Tyvar (implode "A")))
                       (hol_Comb
                          (hol_Comb
                             (hol_Const (implode "==>")
                                (Tyapp (implode "fun")
                                   [Tyapp (implode "bool") [];
                                    Tyapp (implode "fun")
                                      [Tyapp (implode "bool") [];
                                       Tyapp (implode "bool") []]]))
                             ((hol_Comb
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x1") (Tyvar (implode "A")))) ===
                              (hol_Comb
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x2") (Tyvar (implode "A"))))))
                          ((hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                           (hol_Var (implode "x2") (Tyvar (implode "A")))))))))) IN axs1 /\
     FLOOKUP tms1 (implode "ONTO") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []]) /\
     (hol_Const (implode "ONTO")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
            Tyapp (implode "bool") []]) ===
         hol_Abs
           (hol_Var (implode "f")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
                 (hol_Comb
                    (hol_Const (implode "?")
                       (Tyapp (implode "fun")
                          [Tyapp (implode "fun")
                             [Tyvar (implode "A"); Tyapp (implode "bool") []];
                           Tyapp (implode "bool") []]))
                    (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                       ((hol_Var (implode "y") (Tyvar (implode "B"))) ===
                        (hol_Comb
                           (hol_Var (implode "f")
                              (Tyapp (implode "fun")
                                 [Tyvar (implode "A"); Tyvar (implode "B")]))
                           (hol_Var (implode "x") (Tyvar (implode "A")))))))))) IN axs1 /\
     is_infinite mem inf'
     ==> equal_on (tys1,tms1) i1 ((implode "ind" =+ K inf') (FST i1), SND i1) /\
         models0 mem ((implode "ind" =+ K inf') (FST i1), SND i1)
           ((tys1 |+ (implode "ind",0), tms1),
            (
          hol_Comb
            (hol_Const (implode "?")
               (Tyapp (implode "fun")
                  [Tyapp (implode "fun")
                     [Tyapp (implode "fun")
                        [Tyapp (implode "ind") []; Tyapp (implode "ind") []];
                      Tyapp (implode "bool") []];
                   Tyapp (implode "bool") []]))
            (hol_Abs
               (hol_Var (implode "f")
                  (Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind") []]))
               (hol_Comb
                  (hol_Comb
                     (hol_Const (implode "/\\")
                        (Tyapp (implode "fun")
                           [Tyapp (implode "bool") [];
                            Tyapp (implode "fun")
                              [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))
                     (hol_Comb
                        (hol_Const (implode "ONE_ONE")
                           (Tyapp (implode "fun")
                              [typeof
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyapp (implode "ind") [];
                                        Tyapp (implode "ind") []]));
                               Tyapp (implode "bool") []]))
                        (hol_Var (implode "f")
                           (Tyapp (implode "fun")
                              [Tyapp (implode "ind") []; Tyapp (implode "ind") []]))))
                  (hol_Comb
                     (hol_Const (implode "~")
                        (Tyapp (implode "fun")
                           [Tyapp (implode "bool") []; Tyapp (implode "bool") []]))
                     (hol_Comb
                        (hol_Const (implode "ONTO")
                           (Tyapp (implode "fun")
                              [typeof
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyapp (implode "ind") [];
                                        Tyapp (implode "ind") []]));
                               Tyapp (implode "bool") []]))
                        (hol_Var (implode "f")
                           (Tyapp (implode "fun")
                              [Tyapp (implode "ind") []; Tyapp (implode "ind") []])))))))
            INSERT axs1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_ASSUM "models0 _ _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[models0_def; FST; SND]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_std_type_facts) THEN
  QPAT_ASSUM "theory_ok _" (STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def; FST; SND] o
                            MATCH_MP theory_ok_sig) THEN
  SUBGOAL_THEN `?x:U. (mem:U->U->bool) x inf'` ASSUME_TAC THENL
   [QPAT_ASSUM "is_infinite _ _" (MP_TAC o REWRITE_RULE[is_infinite_def]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[equal_on_def; FST; SND; APPLY_UPDATE_THM] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[models0_def; FST; SND; IN_INSERT] THEN
  W(fun (asl,w) ->
    MAP_EVERY (fun th -> ASSUME_TAC(REWRITE_RULE CBOOLAUX_sigs th))
      (filter (fun th -> exists (fun d -> can (PART_MATCH lhs d) (concl th))
                           (map SPEC_ALL CBOOLAUX_sigs)) (map snd asl))) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [UNDISCH_TAC `is_interpretation0 (mem:U->U->bool) (tys1,tms1)
                   (i1:(mlstring->U list->U)#(mlstring->U list->U))` THEN
    REWRITE_TAC[is_interpretation0_def; FST; SND] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `is_type_assignment0 (mem:U->U->bool) tys1
                     (FST (i1:(mlstring->U list->U)#(mlstring->U list->U)))` THEN
      REWRITE_TAC[is_type_assignment0_def; FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:mlstring`; `n:num`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THENL
       [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[APPLY_UPDATE_THM; K_THM] THEN
        CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `n:num`]) THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `is_term_assignment0 (mem:U->U->bool) tms1
                     (FST (i1:(mlstring->U list->U)#(mlstring->U list->U))) (SND i1)` THEN
      REWRITE_TAC[is_term_assignment0_def; FEVERY_ALL_FLOOKUP] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:mlstring`; `ty:hol_type`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `ty:hol_type`]) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      SUBGOAL_THEN `!tau. typesem ((implode "ind" =+ K inf')
                                    (FST (i1:(mlstring->U list->U)#(mlstring->U list->U))))
                                  tau ty = typesem (FST i1) tau ty`
        (fun th -> REWRITE_TAC[th]) THEN
      GEN_TAC THEN MATCH_MP_TAC typesem_sig THEN EXISTS_TAC `tys1:tysig` THEN
      REWRITE_TAC[APPLY_UPDATE_THM] THEN CONJ_TAC THENL
       [UNDISCH_TAC `theory_ok ((tys1,tms1),axs1)` THEN
        REWRITE_TAC[theory_ok_def; FST; SND] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN REWRITE_TAC[FRANGE_FLOOKUP] THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]]];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [UNDISCH_TAC `is_std_interpretation0 (mem:U->U->bool)
                   (i1:(mlstring->U list->U)#(mlstring->U list->U))` THEN
    REWRITE_TAC([is_std_interpretation0_def; is_std_type_assignment0_def; FST; SND;
                 APPLY_UPDATE_THM] @ CBOOLAUX_STRING_THMS);
    DISCH_TAC] THEN
   GEN_TAC THEN STRIP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC satisfies_extend THEN
    MAP_EVERY EXISTS_TAC [`tys1:tysig`; `tms1:tmsig`] THEN
    ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL] THEN
    SUBGOAL_THEN `ALL (hol_term_ok (tys1,tms1)) [p]` ASSUME_TAC THENL
     [REWRITE_TAC[ALL] THEN ASM_MESON_TAC[theory_ok_def; FST; SND]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC satisfies_sig THEN
    EXISTS_TAC `i1:(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig)] THEN
  (* the axiom of infinity *)
  ASM_REWRITE_TAC[satisfies0_def; ALL; FST; SND] THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mem:U->U->bool`; `((tys1:tysig,tms1:tmsig),axs1:hol_term->bool)`;
                 `i1:(mlstring->U list->U)#(mlstring->U list->U)`] CBOOLAUX_one_one_interp) THEN
  MP_TAC(ISPECL [`mem:U->U->bool`; `((tys1:tysig,tms1:tmsig),axs1:hol_term->bool)`;
                 `i1:(mlstring->U list->U)#(mlstring->U list->U)`] CBOOLAUX_onto_interp) THEN
  ASM_REWRITE_TAC[FST; SND; interprets0_def] THEN
  DISCH_THEN(MP_TAC o SPEC `K (inf':U):mlstring->U`) THEN
  REWRITE_TAC[is_type_valuation0_def; K_THM; MAP; HD; TL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `K (inf':U):mlstring->U`) THEN
  REWRITE_TAC[is_type_valuation0_def; K_THM; MAP; HD; TL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  CBOOLAUX_SEM_SIMP_SIG_TAC `(tys1:tysig) |+ (implode "ind",0),(tms1:tmsig)`
    [CBOOLAUX_tyvar_inst_exists2; APPLY_UPDATE_THM; K_THM; MAP] THEN
  CBOOLAUX_BOOLEAN_TAC THEN
   QPAT_ASSUM "is_infinite _ _" (MP_TAC o REWRITE_RULE[is_infinite_def; INFINITE_INJ_NOT_SURJ]) THEN
   DISCH_THEN(X_CHOOSE_THEN `fi:U->U` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `!x:U. mem x inf' ==> (mem:U->U->bool) (fi x) inf'` ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_ELIM_THM]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `abstract (mem:U->U->bool) inf' inf' fi` THEN
   MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
    [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN ASM_REWRITE_TAC[];
     DISCH_TAC] THEN
  SUBGOAL_THEN `is_valuation0 (mem:U->U->bool) ((tys1:tysig) |+ (implode "ind",0))
                   ((implode "ind" =+ K (inf':U))
                      (FST (i1:(mlstring->U list->U)#(mlstring->U list->U))))
                   (FST (v:(mlstring->U)#(mlstring#hol_type->U)),
                    ((implode "f",
                      Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind") []]) =+
                     abstract mem inf' inf' fi) (SND v))` ASSUME_TAC THENL
   [MATCH_MP_TAC CBOOLAUX_is_valuation_update2 THEN
    ASM_REWRITE_TAC([PAIR; typesem_def; MAP; APPLY_UPDATE_THM; K_THM] @ CBOOLAUX_STRING_THMS);
    ALL_TAC] THEN
   SUBGOAL_THEN `is_std_type_assignment0 (mem:U->U->bool)
                   ((implode "ind" =+ K (inf':U))
                      (FST (i1:(mlstring->U list->U)#(mlstring->U list->U))))`
   ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[FST] o MATCH_MP is_std_interpretation_is_type o
                check (fun th -> can (term_match []
                  `is_std_interpretation0 (mem:U->U->bool)
                     ((implode "ind" =+ K (inf':U))
                        (FST (i1:(mlstring->U list->U)#(mlstring->U list->U))),SND i1)`)
                  (concl th)));
    ALL_TAC] THEN
   CBOOLAUX_SEM_SIMP_SIG_TAC `(tys1:tysig) |+ (implode "ind",0),(tms1:tmsig)`
     [CBOOLAUX_tyvar_inst_exists2; APPLY_UPDATE_THM; K_THM; MAP; PAIR] THEN
  CBOOLAUX_BOOLEAN_TAC THEN
   ASM_SIMP_TAC([termsem0_def; CBOOLAUX_instance_AB; typesem_def; MAP; FST; SND;
                 APPLY_UPDATE_THM; K_THM] @ CBOOLAUX_STRING_THMS) THEN
  ASM_SIMP_TAC[apply_abstract; boolean_in_boolset] THEN CBOOLAUX_BOOLEAN_TAC THEN
   ASM_SIMP_TAC[apply_abstract] THEN
  SUBGOAL_THEN `!a. (mem:U->U->bool) a inf' ==> apply mem (abstract mem inf' inf' fi) a = fi a`
     ASSUME_TAC THENL [ASM_SIMP_TAC[apply_abstract]; ALL_TAC] THEN
   QPAT_X_ASSUM "INJ _ _ _" (MP_TAC o REWRITE_RULE[INJ; IN_ELIM_THM]) THEN
   QPAT_X_ASSUM "~SURJ _ _ _" (MP_TAC o REWRITE_RULE[SURJ; IN_ELIM_THM]) THEN
   QPAT_X_ASSUM "!a. mem a inf' ==> apply mem (abstract mem inf' inf' fi) a = fi a" MP_TAC THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[]);;

(* the axiom of infinity has a model (HOL4 proves it with extends_consistent *)
(* and the model construction inline)                                         *)

(* a context that has an extension as its tail extends what the tail extends *)
let CBOOLAUX_extends_tl = prove
 (`!a l c. CONS a l extends c /\ ~(CONS a l = c) ==> l extends c`,
  REWRITE_TAC[extends_def] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [RTC_CASES_R] THEN
  REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

(* the context ctxt1 (an abbreviation) is not equal to a shorter one *)
let CBOOLAUX_LENGTH_NEQ_TAC : tactic =
  EXPAND_TAC "ctxt1" THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:update list->num`) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC;;

(* lookups in ctxt1, the definitions of ONTO and ONE_ONE over ctxt *)
let CBOOLAUX_CTXT1_TAC : tactic =
  EXPAND_TAC "ctxt1" THEN
  REWRITE_TAC([CBOOLAUX_tysof_ConstSpec; CBOOLAUX_tmsof_ConstDef; FLOOKUP_UPDATE; FDOM_FUPDATE;
               IN_INSERT; typeof_def; codomain_def; CBOOLAUX_typeof_equation] @
              CBOOLAUX_STRING_THMS) THEN
  ASM_REWRITE_TAC[];;

(* the definitions of ONTO and ONE_ONE are axioms of ctxt1 *)
let CBOOLAUX_AXIOM_IN_CTXT1_TAC : tactic =
  W(fun (asl,w) ->
    let body = rand(lhand w) in
    SUBGOAL_THEN (mk_comb(`CLOSED`, body)) ASSUME_TAC THENL
     [REWRITE_TAC[CLOSED_def; VFREE_IN_def; equation_def; distinctness "hol_term"] THEN
      REPEAT GEN_TAC THEN CONV_TAC TAUT;
      ALL_TAC]) THEN
  EXPAND_TAC "ctxt1" THEN
  ASM_SIMP_TAC[MAP; FLAT; APPEND; axexts_of_upd_def; CBOOLAUX_conexts_ConstDef;
               IN_SET_OF_LIST; MEM_APPEND; MEM] THEN
  REWRITE_TAC[typeof_def; codomain_def; CBOOLAUX_typeof_equation];;
(* an interpretation of a constant of type ty of ctxt carries over to an     *)
(* interpretation equal on the signature of ctxt                             *)
let CBOOLAUX_INTERP_TAC ty : tactic =
  REWRITE_TAC CBOOLAUX_ints THEN MATCH_MP_TAC equal_on_interprets THEN
  MAP_EVERY EXISTS_TAC
    [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
       alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`;
     `i:(mlstring->U list->U)#(mlstring->U list->U)`; ty] THEN
  RULE_ASSUM_TAC(REWRITE_RULE CBOOLAUX_ints) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def; FST; SND] o
              MATCH_MP theory_ok_sig) THEN
  ASM_REWRITE_TAC([type_ok_def; ALL; LENGTH; ARITH_RULE `SUC (SUC 0) = 2`] @
                  CBOOLAUX_TYVARS_THMS @ CBOOLAUX_STRING_THMS) THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[set_of_list];;
(* the types of the connectives ==>, /\ (bbb), !, ? (qbb) and ~ (bb) *)
let CBOOLAUX_ty_bbb = `Tyapp (implode "fun") [Tyapp (implode "bool") [];
            Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]`
and CBOOLAUX_ty_qbb = `Tyapp (implode "fun")
            [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
             Tyapp (implode "bool") []]`
and CBOOLAUX_ty_bb =
  `Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]`;;

let infinity_has_model_gen = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
              {implode "ONE_ONE", implode "ONTO"} /\
     ~(implode "ind" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
     is_implies_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_and_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_forall_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_exists_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_not_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
     ==> !i inf'.
           models0 mem i
             ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
               alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                   (conexts_of_upd upd)) ctxt))) /\
           is_implies_interpretation0 mem (SND i) /\
           is_and_interpretation0 mem (SND i) /\
           is_forall_interpretation0 mem (SND i) /\
           is_exists_interpretation0 mem (SND i) /\
           is_not_interpretation0 mem (SND i) /\
           is_infinite mem inf'
           ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                              alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                    models0 mem i'
                      ((alist_to_fmap (FLAT (MAP types_of_upd (mk_infinity_ctxt ctxt))),
                        alist_to_fmap (FLAT (MAP consts_of_upd (mk_infinity_ctxt ctxt)))),
                       set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                            (conexts_of_upd upd))
                                              (mk_infinity_ctxt ctxt)))) /\
                    FST i' (implode "ind") [] = inf'`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mk_infinity_ctxt ctxt extends ctxt` MP_TAC THENL
   [MATCH_MP_TAC infinity_extends THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE CBOOLAUX_sigs) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let th = SPEC `ctxt:update list` mk_infinity_ctxt_def in
    let c1 = rand(rand(rand(concl th))) in
    REWRITE_TAC[th] THEN ABBREV_TAC (mk_eq(`ctxt1:update list`, c1))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(ctxt1:update list) extends ctxt` ASSUME_TAC THENL
   [MATCH_MP_TAC CBOOLAUX_extends_tl THEN
    EXISTS_TAC `hol_NewType (implode "ind") 0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CBOOLAUX_extends_tl THEN
      W(fun (asl,w) ->
        let isext t = try fst(dest_const(fst(strip_comb t))) = "extends"
                      with Failure _ -> false in
        let ex = find isext
                      (map (concl o snd) asl) in
        EXISTS_TAC (rand(rator(lhand ex)))) THEN
      ASM_REWRITE_TAC[] THEN CBOOLAUX_LENGTH_NEQ_TAC;
      CBOOLAUX_LENGTH_NEQ_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ctxt:update list`; `ctxt1:update list`]
     (MATCH_MP extends_consistent (ASSUME `is_set_theory (mem:U->U->bool)`))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [EXPAND_TAC "ctxt1" THEN REWRITE_TAC[MEM; distinctness "update"];
     DISCH_THEN(X_CHOOSE_THEN `i1:(mlstring->U list->U)#(mlstring->U list->U)`
                  STRIP_ASSUME_TAC)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE CBOOLAUX_sigs) THEN
   MP_TAC(ISPECL [`mem:U->U->bool`; `alist_to_fmap (FLAT (MAP types_of_upd ctxt1))`;
                  `alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))`;
                  `set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                          ctxt1))`;
                  `i1:(mlstring->U list->U)#(mlstring->U list->U)`; `inf':U`]
                 CBOOLAUX_infinity_core) THEN
   ANTS_TAC THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
   EXISTS_TAC `ctxt:update list` THEN ASM_REWRITE_TAC[];
    CBOOLAUX_CTXT1_TAC;
    REWRITE_TAC CBOOLAUX_sigs THEN CBOOLAUX_CTXT1_TAC;
    REWRITE_TAC CBOOLAUX_sigs THEN CBOOLAUX_CTXT1_TAC;
    REWRITE_TAC CBOOLAUX_sigs THEN CBOOLAUX_CTXT1_TAC;
    REWRITE_TAC CBOOLAUX_sigs THEN CBOOLAUX_CTXT1_TAC;
    REWRITE_TAC CBOOLAUX_sigs THEN CBOOLAUX_CTXT1_TAC;
    CBOOLAUX_INTERP_TAC CBOOLAUX_ty_bbb;
    CBOOLAUX_INTERP_TAC CBOOLAUX_ty_bbb;
    CBOOLAUX_INTERP_TAC CBOOLAUX_ty_qbb;
    CBOOLAUX_INTERP_TAC CBOOLAUX_ty_qbb;
    CBOOLAUX_INTERP_TAC CBOOLAUX_ty_bb;
    CBOOLAUX_CTXT1_TAC;
    CBOOLAUX_AXIOM_IN_CTXT1_TAC;
    CBOOLAUX_CTXT1_TAC;
    CBOOLAUX_AXIOM_IN_CTXT1_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
   EXISTS_TAC `((implode "ind" =+ K (inf':U))
                  (FST (i1:(mlstring->U list->U)#(mlstring->U list->U))), SND i1)` THEN
   REWRITE_TAC[FST; SND; APPLY_UPDATE_THM; K_THM] THEN CONJ_TAC THENL
    [MATCH_MP_TAC equal_on_trans THEN
     EXISTS_TAC `i1:(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[equal_on_def; FST; SND; APPLY_UPDATE_THM] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[CBOOLAUX_tysof_NewAxiom; CBOOLAUX_tmsof_NewAxiom; CBOOLAUX_tysof_NewType;
               CBOOLAUX_tmsof_NewType; MAP; FLAT; APPEND; axexts_of_upd_def;
               conexts_of_upd_def; set_of_list] THEN
   ASM_REWRITE_TAC[]);;

let infinity_has_model = prove
 (`is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf') ==>
   !ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
              {implode "ONE_ONE", implode "ONTO"} /\
     ~(implode "ind" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
     is_implies_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_and_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_forall_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_exists_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_not_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
     ==> !i. models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
             models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
             is_implies_interpretation0 mem (SND i) /\
             is_and_interpretation0 mem (SND i) /\
             is_forall_interpretation0 mem (SND i) /\
             is_exists_interpretation0 mem (SND i) /\
             is_not_interpretation0 mem (SND i)
             ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                                alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                      models0 mem i'
                        ((alist_to_fmap (FLAT (MAP types_of_upd (mk_infinity_ctxt ctxt))),
                          alist_to_fmap (FLAT (MAP consts_of_upd (mk_infinity_ctxt ctxt)))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                              (conexts_of_upd upd))
                                                (mk_infinity_ctxt ctxt))))`,
  STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ctxt:update list` o MATCH_MP infinity_has_model_gen) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:(mlstring->U list->U)#(mlstring->U list->U)`; `inf':U`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
