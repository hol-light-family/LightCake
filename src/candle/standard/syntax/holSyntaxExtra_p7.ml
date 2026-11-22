(* ========================================================================= *)
(* holSyntaxExtra, part 7 (HOL4 holSyntaxExtraScript.sml lines 3401-3907):   *)
(* extensions of contexts: distinct names, signature extensions preserve ok, *)
(* updates and extensions preserve theory_ok, the initial context, constant  *)
(* definitions as specifications, lookups in extended contexts, proofs in    *)
(* extended contexts.  Notes on the rendering: holSyntaxExtra_p1.ml.         *)
(* - The context Overloads are written out as in holSyntax.ml (its header):  *)
(*   type_list ctxt is FLAT (MAP types_of_upd ctxt), const_list ctxt         *)
(*   FLAT (MAP consts_of_upd ctxt), tysof ctxt alist_to_fmap (type_list      *)
(*   ctxt), tmsof ctxt alist_to_fmap (const_list ctxt), sigof ctxt the pair  *)
(*   of these, axsof ctxt set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd *)
(*   upd) (conexts_of_upd upd)) ctxt)), thyof ctxt the pair (sigof ctxt,     *)
(*   axsof ctxt); on a theory or signature, tysof, tmsof and sigof are FST   *)
(*   and SND of the pair, as there (tysof (thyof ctxt) is FST (FST (thyof    *)
(*   ctxt)) with thyof ctxt written out).                                    *)
(* - HOL4's Overload ConstDef x t is hol_ConstSpec [(x,t)] (hol_Var x        *)
(*   (typeof t) === t); HOL4's infix SUBMAP is the infix SUBMAP of           *)
(*   finite_map.ml; FUNION is FUNION.                                        *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_P7_.               *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p6.ml";;
needs "hol4/libext.ml";;

prioritize_num();;
type_invention_error := true;;

(* extensions have all distinct names *)

(* the names of the constants of a ConstSpec *)
let CSYNAUX_P7_MAP_FST_consts = prove
 (`!eqs. MAP FST (MAP (\(s:mlstring,t). s,typeof t) eqs) = MAP FST eqs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  PAIR_CASES_ON `h:mlstring#hol_term` THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let updates_ALL_DISTINCT = prove
 (`!upd ctxt. upd updates ctxt
     ==> (ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd ctxt)))
          ==> ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd (CONS upd ctxt))))) /\
         (ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd ctxt)))
          ==> ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd (CONS upd ctxt)))))`,
  MATCH_MP_TAC updates_ind THEN
  REWRITE_TAC[MAP; FLAT; types_of_upd_def; consts_of_upd_def; APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP_APPEND; ALL_DISTINCT_APPEND; MAP; ALL_DISTINCT; MEM; APPEND;
              FDOM_alist_to_fmap; IN_SET_OF_LIST; CSYNAUX_P7_MAP_FST_consts] THEN
  MESON_TAC[]);;

let extends_ALL_DISTINCT = prove
 (`!ctxt1 ctxt2. ctxt2 extends ctxt1
     ==> (ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd ctxt1)))
          ==> ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd ctxt2)))) /\
         (ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd ctxt1)))
          ==> ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd ctxt2))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `\ctxt. ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd ctxt)))`
      extends_ind);
    MP_TAC(ISPEC `\ctxt. ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd ctxt)))`
      extends_ind)] THEN
  REWRITE_TAC[] THEN ANTS_TAC THEN ASM_MESON_TAC[updates_ALL_DISTINCT]);;

let init_ALL_DISTINCT = prove
 (`ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd init_ctxt))) /\
   ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd init_ctxt)))`,
  REWRITE_TAC[init_ctxt_def; MAP; FLAT; consts_of_upd_def; types_of_upd_def;
              APPEND; ALL_DISTINCT; MEM] THEN
  SIMP[injectivity "mlstring"]);;

let updates_DISJOINT = prove
 (`!upd ctxt.
     upd updates ctxt
     ==> DISJOINT (FDOM (alist_to_fmap (consts_of_upd upd)))
                  (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
         DISJOINT (FDOM (alist_to_fmap (types_of_upd upd)))
                  (FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt))))`,
  MATCH_MP_TAC updates_ind THEN
  REWRITE_TAC[types_of_upd_def; consts_of_upd_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FDOM_alist_to_fmap; MAP; CSYNAUX_P7_MAP_FST_consts; set_of_list;
              IN_DISJOINT; IN_INSERT; NOT_IN_EMPTY; IN_SET_OF_LIST] THEN
  MESON_TAC[IN_SET_OF_LIST]);;

let updates_upd_ALL_DISTINCT = prove
 (`!upd ctxt. upd updates ctxt
              ==> ALL_DISTINCT (MAP FST (consts_of_upd upd)) /\
                  ALL_DISTINCT (MAP FST (types_of_upd upd))`,
  MATCH_MP_TAC updates_ind THEN
  REWRITE_TAC[types_of_upd_def; consts_of_upd_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; MEM; CSYNAUX_P7_MAP_FST_consts] THEN
  MESON_TAC[]);;

let updates_upd_DISJOINT = prove
 (`!upd ctxt. upd updates ctxt
     ==> DISJOINT (set_of_list (MAP FST (types_of_upd upd)))
                  (set_of_list (MAP FST (FLAT (MAP types_of_upd ctxt)))) /\
         DISJOINT (set_of_list (MAP FST (consts_of_upd upd)))
                  (set_of_list (MAP FST (FLAT (MAP consts_of_upd ctxt))))`,
  REWRITE_TAC[GSYM FDOM_alist_to_fmap] THEN MESON_TAC[updates_DISJOINT]);;

(* signature extensions preserve ok *)

let type_ok_extend = prove
 (`!t tyenv tyenv'.
     tyenv SUBMAP tyenv' /\
     type_ok tyenv t
     ==> type_ok tyenv' t`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[type_ok_def; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[FLOOKUP_SUBMAP]; ASM_MESON_TAC[]]);;

(* HOL4: term_ok_extend *)
let hol_term_ok_extend = prove
 (`!t tyenv tmenv tyenv' tmenv'.
     tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv' /\
     hol_term_ok (tyenv,tmenv) t
     ==> hol_term_ok (tyenv',tmenv') t`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[hol_term_ok_def] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[type_ok_extend; FLOOKUP_SUBMAP]);;

(* an update extends both maps of the signature *)
let CSYNAUX_P7_SUBMAP_updates = prove
 (`!upd ctxt. upd updates ctxt
     ==> alist_to_fmap (FLAT (MAP types_of_upd ctxt)) SUBMAP
         alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))) /\
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt)) SUBMAP
         alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP updates_DISJOINT) THEN
  REWRITE_TAC[MAP; FLAT; alist_to_fmap_APPEND] THEN
  MESON_TAC[SUBMAP_FUNION_ID]);;

let term_ok_updates = prove
 (`!upd ctxt. upd updates ctxt
     ==> hol_term_ok
           (FST (((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                   alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                  set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                       (conexts_of_upd upd)) ctxt)))))
           tm
         ==> hol_term_ok
               (FST (((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                       alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                      set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                           (conexts_of_upd upd))
                                             (CONS upd ctxt))))))
               tm`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CSYNAUX_P7_SUBMAP_updates) THEN
  REWRITE_TAC[FST] THEN MESON_TAC[hol_term_ok_extend]);;

let is_std_sig_extend = prove
 (`!tyenv tmenv tyenv' tmenv'.
     is_std_sig (tyenv,tmenv) /\ tyenv SUBMAP tyenv' /\ tmenv SUBMAP tmenv'
     ==> is_std_sig (tyenv',tmenv')`,
  REWRITE_TAC[is_std_sig_def] THEN MESON_TAC[FLOOKUP_SUBMAP]);;

(* updates preserve ok *)

(* an update keeps theory_ok if the types of its new constants and its new *)
(* axioms are ok (the old ones carry over by the SUBMAP facts)             *)
let CSYNAUX_P7_theory_ok_updates = prove
 (`!upd ctxt.
     upd updates ctxt /\
     theory_ok
       ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                             (conexts_of_upd upd)) ctxt))) /\
     (!ty. MEM ty (MAP SND (consts_of_upd upd))
           ==> type_ok (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt)))) ty) /\
     (!p. MEM p (APPEND (axexts_of_upd upd) (conexts_of_upd upd))
          ==> hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                           alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))) p /\
              p has_type Tyapp (implode "bool") [])
     ==> theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
             alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                 (conexts_of_upd upd))
                                   (CONS upd ctxt))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CSYNAUX_P7_SUBMAP_updates) THEN
  UNDISCH_TAC
   `theory_ok
      ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
        alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
       set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                            (conexts_of_upd upd)) ctxt)))` THEN
  REWRITE_TAC[theory_ok_def; FST; SND] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAP; FLAT; alist_to_fmap_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FLAT; alist_to_fmap_APPEND]) THEN
    MATCH_MP_TAC IN_FRANGE_FUNION_suff THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_FRANGE_alist_to_fmap_suff THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC type_ok_extend THEN
      EXISTS_TAC `alist_to_fmap (FLAT (MAP types_of_upd ctxt))` THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND]) THEN
    GEN_TAC THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC hol_term_ok_extend THEN
      MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd ctxt))`;
                            `alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`] THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC is_std_sig_extend THEN
    MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd ctxt))`;
                          `alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`] THEN
    ASM_REWRITE_TAC[]]);;

(* the new constants of a ConstSpec, looked up in the extended signature *)
let CSYNAUX_P7_FLOOKUP_ConstSpec = prove
 (`!eqs tm n t.
     ALL_DISTINCT (MAP FST eqs) /\ MEM (n,t) eqs
     ==> FLOOKUP (FUNION (alist_to_fmap (MAP (\(s:mlstring,t). s,typeof t) eqs)) tm) n =
         SOME (typeof t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FLOOKUP_FUNION; ALOOKUP_EQ_FLOOKUP] THEN
  SUBGOAL_THEN `ALOOKUP (MAP (\(s:mlstring,t). s,typeof t) eqs) n = SOME (typeof t)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_REWRITE_TAC[CSYNAUX_P7_MAP_FST_consts; MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    MAP_EVERY EXISTS_TAC [`n:mlstring`; `t:hol_term`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[option_CASE]]);;

(* the new constants and axioms of an update are ok in the extended theory *)
let CSYNAUX_P7_updates_new_ok = prove
 (`!upd ctxt.
     upd updates ctxt
     ==> theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                 (conexts_of_upd upd)) ctxt)))
         ==> (!ty. MEM ty (MAP SND (consts_of_upd upd))
                   ==> type_ok (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt)))) ty) /\
             (!p. MEM p (APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                  ==> hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                                   alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))) p /\
                      p has_type Tyapp (implode "bool") [])`,
  MATCH_MP_TAC updates_ind THEN
  REWRITE_TAC[MAP; FLAT; APPEND; MEM; alist_to_fmap_APPEND; types_of_upd_def;
              consts_of_upd_def; axexts_of_upd_def; conexts_of_upd_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP; FLAT; APPEND; MEM; alist_to_fmap_thm; FUNION_FEMPTY_1] THEN
  REPEAT CONJ_TAC THENL
   [(* NewAxiom *)
    SIMP_TAC[];
    (* NewConst *)
    SIMP_TAC[];
    (* ConstSpec *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
    REWRITE_TAC[FST; SND; ALL; GSYM ALL_MEM] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig) THEN
    SUBGOAL_THEN `!n t. MEM (n,t) (eqs:(mlstring#hol_term)list)
                        ==> type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) (typeof t)`
      ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      QPAT_X_ASSUM "!x. MEM x (MAP _ eqs) ==> _" (MP_TAC o SPEC `hol_Var n (typeof t) === t`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
        CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
        MAP_EVERY EXISTS_TAC [`n:mlstring`; `t:hol_term`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[term_ok_equation] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`; `t:hol_term`]
             term_ok_type_ok) THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `!s s'. MEM (s',s) (MAP (\(s,t). hol_Const s (typeof t),hol_Var s (typeof t))
                             (eqs:(mlstring#hol_term)list))
             ==> ?n t. MEM (n,t) eqs /\ s' = hol_Const n (typeof t) /\
                       s = hol_Var n (typeof t)`
      (LABEL_TAC "IL") THENL
     [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC term_ok_VSUBST THEN CONJ_TAC THENL
       [MATCH_MP_TAC hol_term_ok_extend THEN
        MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd ctxt))`;
                              `alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`] THEN
        ASM_REWRITE_TAC[SUBMAP_REFL] THEN
        MATCH_MP_TAC(CONJUNCT2 SUBMAP_FUNION_ID) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[FDOM_alist_to_fmap; IN_SET_OF_LIST]) THEN
        ASM_REWRITE_TAC[FDOM_alist_to_fmap; CSYNAUX_P7_MAP_FST_consts; IN_DISJOINT;
                        IN_SET_OF_LIST] THEN
        ASM_MESON_TAC[];
        REPEAT GEN_TAC THEN DISCH_THEN(fun th -> USE_THEN "IL" (MP_TAC o C MATCH_MP th)) THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`n:mlstring`; `t:hol_term`] THEN
        STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`n:mlstring`; `typeof t`] THEN
        ASM_REWRITE_TAC[CSYNAUX_P3_has_type_Const; hol_term_ok_def] THEN
        EXISTS_TAC `typeof t` THEN
        ASM_SIMP_TAC[CSYNAUX_P7_FLOOKUP_ConstSpec] THEN
        EXISTS_TAC `[]:(hol_type#hol_type)list` THEN REWRITE_TAC[TYPE_SUBST_NIL]];
      MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[] THEN
      REPEAT GEN_TAC THEN DISCH_THEN(fun th -> USE_THEN "IL" (MP_TAC o C MATCH_MP th)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"; CSYNAUX_P3_has_type_Const] THEN
      MESON_TAC[]];
    (* TypeDefn *)
    MAP_EVERY X_GEN_TAC [`abs_name:mlstring`; `ctxt:update list`; `name:mlstring`;
                         `pred:hol_term`; `rep_name:mlstring`; `witness:hol_term`] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
    REWRITE_TAC[FST; SND; ALL; hol_term_ok_def; CSYNAUX_P3_has_type_Comb] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `typeof pred = Tyapp (implode "fun") [dty; Tyapp (implode "bool") []] /\
                  type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) dty`
      STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `typeof pred = Tyapp (implode "fun") [dty; Tyapp (implode "bool") []]`
        ASSUME_TAC THENL [ASM_MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`; `pred:hol_term`]
             term_ok_type_ok) THEN
      ASM_REWRITE_TAC[FST; type_ok_def; ALL] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[hol_domain_def] THEN
    ABBREV_TAC `at = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode
                                                                       (tvars pred)))))` THEN
    SUBGOAL_THEN `~(name = implode "fun") /\ ~(name = implode "bool")` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                               alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))` THEN
      REWRITE_TAC[is_std_sig_def; FST; SND; flookup_thm] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `alist_to_fmap (FLAT (MAP types_of_upd ctxt)) SUBMAP
      alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+ (name,LENGTH (tvars pred)) /\
      alist_to_fmap (FLAT (MAP consts_of_upd ctxt)) SUBMAP
      FUNION (FEMPTY |+ (rep_name,Tyapp (implode "fun") [at; dty]) |+
                        (abs_name,Tyapp (implode "fun") [dty; at]))
             (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(CONJUNCT2 SUBMAP_FUNION_ID) THEN
        REWRITE_TAC[FDOM_FUPDATE; FDOM_FEMPTY; IN_DISJOINT; IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+ (name,LENGTH (tvars pred)),
                  FUNION (FEMPTY |+ (rep_name,Tyapp (implode "fun") [at; dty]) |+
                                    (abs_name,Tyapp (implode "fun") [dty; at]))
                         (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC is_std_sig_extend THEN
      MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd ctxt))`;
                            `alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!a b. type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+
                     (name,LENGTH (tvars pred)))
                    (Tyapp (implode "fun") [a; b]) <=>
            type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+
                     (name,LENGTH (tvars pred))) a /\
            type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+
                     (name,LENGTH (tvars pred))) b`
      ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[is_std_sig_def; FST; SND]) THEN
      REWRITE_TAC[type_ok_def; ALL; LENGTH; ARITH_RULE `SUC(SUC 0) = 2`] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+
               (name,LENGTH (tvars pred))) dty /\
      type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+
               (name,LENGTH (tvars pred))) at`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC type_ok_extend THEN
        EXISTS_TAC `alist_to_fmap (FLAT (MAP types_of_upd ctxt))` THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "at" THEN
        ASM_SIMP_TAC[type_ok_def; FLOOKUP_UPDATE; LENGTH_MAP; LENGTH_STRING_SORT;
                     ALL_DISTINCT_MAP_explode; tvars_ALL_DISTINCT] THEN
        REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[type_ok_def]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `FLOOKUP (FUNION (FEMPTY |+ (rep_name,Tyapp (implode "fun") [at; dty]) |+
                                  (abs_name,Tyapp (implode "fun") [dty; at]))
                       (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) abs_name =
      SOME (Tyapp (implode "fun") [dty; at]) /\
      FLOOKUP (FUNION (FEMPTY |+ (rep_name,Tyapp (implode "fun") [at; dty]) |+
                                  (abs_name,Tyapp (implode "fun") [dty; at]))
                       (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) rep_name =
      SOME (Tyapp (implode "fun") [at; dty])`
      STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FLOOKUP_FUNION; FLOOKUP_UPDATE] THEN REWRITE_TAC[option_CASE];
      ALL_TAC] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+ (name,LENGTH (tvars pred)),
                   FUNION (FEMPTY |+ (rep_name,Tyapp (implode "fun") [at; dty]) |+
                                     (abs_name,Tyapp (implode "fun") [dty; at]))
                          (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) pred /\
      welltyped pred`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC hol_term_ok_extend THEN
        MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd ctxt))`;
                              `alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`] THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[term_ok_welltyped]];
      ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[term_ok_equation; EQUATION_HAS_TYPE_BOOL; hol_term_ok_def;
                 WELLTYPED_CLAUSES; typeof_def; codomain_def; injectivity "hol_type";
                 CONS_11; is_instance_refl; FST; SND; injectivity "option"] THEN
    REWRITE_TAC[equation_def; typeof_def; codomain_def; WELLTYPED_CLAUSES;
                injectivity "hol_type"; CONS_11; UNWIND_THM1; is_instance_refl] THEN
    MESON_TAC[]]);;

let updates_theory_ok = prove
 (`!upd ctxt. upd updates ctxt
     ==> theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                 (conexts_of_upd upd)) ctxt)))
         ==> theory_ok
               ((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                 alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd))
                                       (CONS upd ctxt))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CSYNAUX_P7_theory_ok_updates THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`upd:update`; `ctxt:update list`] CSYNAUX_P7_updates_new_ok) THEN
  ASM_REWRITE_TAC[]);;

let extends_theory_ok = prove
 (`!ctxt1 ctxt2. ctxt2 extends ctxt1
     ==> theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                 (conexts_of_upd upd)) ctxt1)))
         ==> theory_ok
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt2)))`,
  MATCH_MP_TAC extends_ind THEN MESON_TAC[updates_theory_ok]);;

(* init_ctxt ok *)

let init_theory_ok = prove
 (`theory_ok
     ((alist_to_fmap (FLAT (MAP types_of_upd init_ctxt)),
       alist_to_fmap (FLAT (MAP consts_of_upd init_ctxt))),
      set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                           (conexts_of_upd upd)) init_ctxt)))`,
  REWRITE_TAC[theory_ok_def; init_ctxt_def; MAP; FLAT; APPEND; types_of_upd_def;
              consts_of_upd_def; axexts_of_upd_def; conexts_of_upd_def;
              alist_to_fmap_thm; FST; SND; set_of_list; NOT_IN_EMPTY;
              is_std_sig_def; FLOOKUP_UPDATE; FRANGE_FUPDATE; FRANGE_FEMPTY;
              DOMSUB_FEMPTY; IN_INSERT] THEN
  SIMP[injectivity "mlstring"; type_ok_def; FLOOKUP_UPDATE; ALL; LENGTH;
       ARITH_RULE `SUC(SUC 0) = 2`]);;

(* is_std_sig is preserved *)

let is_std_sig_extends = prove
 (`!ctxt1 ctxt2. ctxt2 extends ctxt1
     ==> is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                     alist_to_fmap (FLAT (MAP consts_of_upd ctxt1)))
         ==> is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                         alist_to_fmap (FLAT (MAP consts_of_upd ctxt2)))`,
  MATCH_MP_TAC extends_ind THEN
  MESON_TAC[is_std_sig_extend; CSYNAUX_P7_SUBMAP_updates]);;

(* recover constant definition as a special case of specification *)

(* HOL4: Overload ConstDef x t = ConstSpec [(x,t)] (Var x (typeof t) === t) *)
let ConstDef_updates = prove
 (`!name tm ctxt.
     theory_ok
       ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                             (conexts_of_upd upd)) ctxt))) /\
     hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) tm /\
     ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
     CLOSED tm /\
     set_of_list (tvars tm) SUBSET set_of_list (tyvars (typeof tm))
     ==> (hol_ConstSpec [(name,tm)] (hol_Var name (typeof tm) === tm)) updates ctxt`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(el 2 (CONJUNCTS updates_rules)) THEN
  REWRITE_TAC[MAP; ALL; MEM; ALL_DISTINCT] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig) THEN
  SUBGOAL_THEN `welltyped tm /\
                type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) (typeof tm)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[term_ok_welltyped];
      MP_TAC(ISPECL [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`; `tm:hol_term`]
             term_ok_type_ok) THEN
      ASM_REWRITE_TAC[FST]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC proves_ASSUME THEN
    ASM_SIMP_TAC[EQUATION_HAS_TYPE_BOOL; term_ok_equation; FST; hol_term_ok_def;
                 WELLTYPED_CLAUSES; typeof_def];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM SET_TAC[];
    UNDISCH_TAC `CLOSED tm` THEN
    REWRITE_TAC[CLOSED_def; vfree_in_equation; VFREE_IN_def; distinctness "hol_term";
                injectivity "hol_term"; PAIR_EQ] THEN
    MESON_TAC[];
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* lookups in extended contexts *)

let FLOOKUP_tmsof_updates = prove
 (`!upd ctxt. upd updates ctxt
     ==> FLOOKUP (SND (FST (((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                              alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                             set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))))))
                 name = SOME ty
         ==> FLOOKUP (SND (FST (((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                                  alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                        (conexts_of_upd upd))
                                                   (CONS upd ctxt)))))))
                     name = SOME ty`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP updates_DISJOINT) THEN
  REWRITE_TAC[FST; SND; MAP; FLAT; alist_to_fmap_APPEND; FLOOKUP_FUNION] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (alist_to_fmap (consts_of_upd upd)) name = NONE`
    (fun th -> ASM_REWRITE_TAC[th; option_CASE]) THEN
  REWRITE_TAC[flookup_thm] THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_DISJOINT; flookup_thm]) THEN
  ASM_MESON_TAC[]);;

let FLOOKUP_tysof_updates = prove
 (`!upd ctxt. upd updates ctxt
     ==> FLOOKUP (FST (FST (((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                              alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                             set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))))))
                 name = SOME a
         ==> FLOOKUP (FST (FST (((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                                  alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                        (conexts_of_upd upd))
                                                   (CONS upd ctxt)))))))
                     name = SOME a`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP updates_DISJOINT) THEN
  REWRITE_TAC[FST; SND; MAP; FLAT; alist_to_fmap_APPEND; FLOOKUP_FUNION] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (alist_to_fmap (types_of_upd upd)) name = NONE`
    (fun th -> ASM_REWRITE_TAC[th; option_CASE]) THEN
  REWRITE_TAC[flookup_thm] THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_DISJOINT; flookup_thm]) THEN
  ASM_MESON_TAC[]);;

let FLOOKUP_tysof_extends = prove
 (`!ctxt2 ctxt1. ctxt1 extends ctxt2
     ==> FLOOKUP (FST (alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt2)))) k = SOME v
         ==> FLOOKUP (FST (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                           alist_to_fmap (FLAT (MAP consts_of_upd ctxt1)))) k = SOME v`,
  MATCH_MP_TAC extends_ind THEN REWRITE_TAC[FST] THEN
  MESON_TAC[REWRITE_RULE[FST] FLOOKUP_tysof_updates]);;

let FLOOKUP_tmsof_extends = prove
 (`!ctxt2 ctxt1. ctxt1 extends ctxt2
     ==> FLOOKUP (SND (alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt2)))) k = SOME v
         ==> FLOOKUP (SND (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                           alist_to_fmap (FLAT (MAP consts_of_upd ctxt1)))) k = SOME v`,
  MATCH_MP_TAC extends_ind THEN REWRITE_TAC[SND] THEN
  MESON_TAC[REWRITE_RULE[FST; SND] FLOOKUP_tmsof_updates]);;

let extends_sub = prove
 (`!ctxt2 ctxt1. ctxt2 extends ctxt1
     ==> alist_to_fmap (FLAT (MAP consts_of_upd ctxt1)) SUBMAP
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt2)) /\
         alist_to_fmap (FLAT (MAP types_of_upd ctxt1)) SUBMAP
         alist_to_fmap (FLAT (MAP types_of_upd ctxt2)) /\
         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                              (conexts_of_upd upd)) ctxt1)) SUBSET
         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                              (conexts_of_upd upd)) ctxt2))`,
  REWRITE_TAC[extends_def] THEN MATCH_MP_TAC RTC_INDUCT THEN
  REWRITE_TAC[SUBMAP_REFL; SUBSET_REFL] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `upd:update` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CSYNAUX_P7_SUBMAP_updates) THEN
    ASM_REWRITE_TAC[MAP; FLAT; SET_OF_LIST_APPEND] THEN SET_TAC[];
    MESON_TAC[SUBMAP_TRANS; SUBSET_TRANS]]);;

(* proofs still work in extended contexts *)

(* well-formedness carries over one update *)
let CSYNAUX_P7_type_ok_upd = prove
 (`!upd ctxt ty. upd updates ctxt /\
                 type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) ty
                 ==> type_ok (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt)))) ty`,
  MESON_TAC[type_ok_extend; CSYNAUX_P7_SUBMAP_updates]);;

let CSYNAUX_P7_term_ok_upd = prove
 (`!upd ctxt tm. upd updates ctxt /\
                 hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                              alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) tm
                 ==> hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                                  alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))) tm`,
  MESON_TAC[hol_term_ok_extend; CSYNAUX_P7_SUBMAP_updates]);;

let update_extension = prove
 (`!lhs tm.
     lhs |- tm
     ==> !ctxt tms upd.
           lhs = (((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                    alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                   set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                        (conexts_of_upd upd)) ctxt))),
                  tms) /\
           upd updates ctxt
           ==> (((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                  alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd))
                                        (CONS upd ctxt)))),
                tms) |- tm`,
  MATCH_MP_TAC proves_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`ctxt0:update list`; `tms:(hol_term)list`; `upd0:update`] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
                                       fst(dest_var(lhs(concl th))) = "thy")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
                                       fst(dest_var(rhs(concl th))) = "tms")) THENL
   [(* ABS *)
    MATCH_MP_TAC proves_ABS THEN ASM_REWRITE_TAC[FST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CSYNAUX_P7_type_ok_upd THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* ASSUME *)
    MATCH_MP_TAC proves_ASSUME THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    ASM_REWRITE_TAC[FST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates_theory_ok) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSYNAUX_P7_term_ok_upd THEN ASM_REWRITE_TAC[]];
    (* BETA *)
    MATCH_MP_TAC proves_BETA THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    ASM_REWRITE_TAC[FST] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates_theory_ok) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSYNAUX_P7_type_ok_upd THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSYNAUX_P7_term_ok_upd THEN ASM_REWRITE_TAC[]];
    (* DEDUCT_ANTISYM *)
    MATCH_MP_TAC proves_DEDUCT_ANTISYM THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* EQ_MP *)
    MATCH_MP_TAC proves_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`p:hol_term`; `p':hol_term`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* INST *)
    MATCH_MP_TAC proves_INST THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN REWRITE_TAC[FST] THEN
      ASM_MESON_TAC[CSYNAUX_P7_term_ok_upd];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* INST_TYPE *)
    MATCH_MP_TAC proves_INST_TYPE THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[FST; GSYM ALL_MEM]) THEN REWRITE_TAC[FST; GSYM ALL_MEM] THEN
      ASM_MESON_TAC[CSYNAUX_P7_type_ok_upd];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* MK_COMB *)
    MATCH_MP_TAC proves_MK_COMB THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* REFL *)
    MATCH_MP_TAC proves_REFL THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    ASM_REWRITE_TAC[FST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates_theory_ok) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSYNAUX_P7_term_ok_upd THEN ASM_REWRITE_TAC[]];
    (* axioms *)
    MATCH_MP_TAC proves_axioms THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates_theory_ok) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(c:hol_term) IN
         SND ((alist_to_fmap (FLAT (MAP types_of_upd ctxt0)),
               alist_to_fmap (FLAT (MAP consts_of_upd ctxt0))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                   (conexts_of_upd upd)) ctxt0)))` THEN
      REWRITE_TAC[SND; MAP; FLAT; SET_OF_LIST_APPEND; IN_UNION] THEN MESON_TAC[]]]);;

let updates_proves = prove
 (`!upd ctxt. upd updates ctxt
     ==> !h c. (((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd)) ctxt))),
                h) |- c
               ==> (((alist_to_fmap (FLAT (MAP types_of_upd (CONS upd ctxt))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (CONS upd ctxt)))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd))
                                            (CONS upd ctxt)))),
                    h) |- c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP update_extension) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let extends_proves = prove
 (`!c2 c1.
     c2 extends c1
     ==> !h c.
           (((alist_to_fmap (FLAT (MAP types_of_upd c1)),
              alist_to_fmap (FLAT (MAP consts_of_upd c1))),
             set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                  (conexts_of_upd upd)) c1))),
            h) |- c
           ==> (((alist_to_fmap (FLAT (MAP types_of_upd c2)),
                  alist_to_fmap (FLAT (MAP consts_of_upd c2))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd)) c2))),
                h) |- c`,
  REWRITE_TAC[extends_def] THEN MATCH_MP_TAC RTC_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `upd:update` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[updates_proves];
    MESON_TAC[];
    MESON_TAC[]]);;
