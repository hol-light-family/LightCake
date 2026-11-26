(* ========================================================================= *)
(* holKernelProof: port of HOL4 candle/standard/monadic/                     *)
(* holKernelProofScript.sml (CakeML v3479).  Correctness of the monadic      *)
(* functions: they are faithful to the inference rules of the Candle logic. *)
(*                                                                           *)
(* Notes on the rendering (see also holKernel.ml):                           *)
(* - HOL4's overloads tysof, tmsof, axsof, sigof and thyof of a context are  *)
(*   written out (FLAT (MAP types_of_upd ctxt) and so on).                   *)
(* - Variables that are free in a HOL4 statement are universally            *)
(*   quantified, after the variables HOL4 quantifies itself.                 *)
(* - HOL4's case expressions in statements (new_specification_thm and the   *)
(*   other context functions) are kit matches; the pattern M_success () is  *)
(*   M_success u with u of type 1.                                           *)
(* - HOL4's helper vals (type_IND, INST_CORE_EMPTY, ...) are named below;   *)
(*   local helpers of this port have the prefix HOLKPAUX_.                   *)
(* - HOL4's [simp] theorems are added to the kit simp set.                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mllist.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: temp_delsimps ["lift_disj_eq", "lift_imp_disj"] and                *)
(* augment_srw_ss [rewrites [aty_def, bool_ty_def]] have no counterpart; the *)
(* proofs give holKernel_aty_def and holKernel_bool_ty_def where HOL4's      *)
(* srw_ss used them.                                                         *)

(* HOL4: Type M = ``: hol_refs -> ('a, hol_exn) exc # hol_refs``, written out *)

let rev_assocd_thm = prove
 (`(holKernel_rev_assocd:A->(B#A)list->B->B) = REV_ASSOCD`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ONCE_REWRITE_TAC[holKernel_rev_assocd_def] THEN CAKE_REWRITE_TAC[REV_ASSOCD] THEN
  PAIR_CASES_ON `h:B#A` THEN ASM_SIMP_TAC[REV_ASSOCD] THEN CAKE_REWRITE_TAC[]);;

(* HOL4: val REPLICATE_GENLIST = rich_listTheory.REPLICATE_GENLIST (an      *)
(* unused alias)                                                             *)

let REPLICATE_11 = prove
 (`!m n (x:A). REPLICATE n x = REPLICATE m x <=> m = n`,
  INDUCT_TAC THEN INDUCT_TAC THEN
  SIMP[REPLICATE; NOT_SUC; SUC_INJ; GSYM NOT_SUC]);;

(* HOL4: Overload impossible_term = Comb (Var <<x>> Bool) (Var <<x>> Bool),  *)
(* written out                                                               *)

(* ------------------------------------------------------------------------- *)
(* case_eq theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4: val case_eq_thms = CaseEqs ["prod", "list", "option", "type",      *)
(* "term", "thm", "update", "hol_exn", "exc"]                               *)
let HOLKPAUX_case_eq_thms =
  end_itlist CONJ (map case_eq ["prod"; "list"; "option"; "hol_type"; "hol_term";
                                "thm"; "update"; "hol_exn"; "exc"]);;

(* ------------------------------------------------------------------------- *)
(* Refinement invariants                                                     *)
(* ------------------------------------------------------------------------- *)

let holKernelProof_TYPE_def = cake_def
  `holKernelProof_TYPE ctxt ty =
     type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) ty`;;

let holKernelProof_TERM_def = cake_def
  `holKernelProof_TERM ctxt tm =
     hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) tm`;;

let holKernelProof_CONTEXT_def = cake_def
  `holKernelProof_CONTEXT ctxt <=> ctxt extends init_ctxt`;;

let holKernelProof_THM_def = cake_def
  `holKernelProof_THM ctxt (Sequent asl c) <=>
     (((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
        alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
       set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                            (conexts_of_upd upd)) ctxt))),
      asl) |- c`;;

(* the invariants unapplied (HOL4's EVERY (TYPE defs) l unfolds them) *)
let HOLKPAUX_TYPE_ETA = prove
 (`!defs. holKernelProof_TYPE defs =
          type_ok (alist_to_fmap (FLAT (MAP types_of_upd defs)))`,
  REWRITE_TAC[FUN_EQ_THM; holKernelProof_TYPE_def]);;

let HOLKPAUX_TERM_ETA = prove
 (`!defs. holKernelProof_TERM defs =
          hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd defs)),
                       alist_to_fmap (FLAT (MAP consts_of_upd defs)))`,
  REWRITE_TAC[FUN_EQ_THM; holKernelProof_TERM_def]);;

let lift_tm_def = cake_def
  `lift_tm c = Sequent [] c`;;

let holKernelProof_STATE_def = cake_def
  `holKernelProof_STATE ctxt state <=>
     ctxt = hol_refs_the_context state /\ holKernelProof_CONTEXT ctxt /\
     hol_refs_the_type_constants state = FLAT (MAP types_of_upd ctxt) /\
     hol_refs_the_term_constants state = FLAT (MAP consts_of_upd ctxt) /\
     hol_refs_the_axioms state = MAP lift_tm (FLAT (MAP axexts_of_upd ctxt))`;;

(* ------------------------------------------------------------------------- *)
(* impossible term lemmas                                                    *)
(* ------------------------------------------------------------------------- *)

let term_ok_impossible_term = prove
 (`!defs. ~hol_term_ok defs
             (hol_Comb (hol_Var (implode "x") (Tyapp (implode "bool") []))
                       (hol_Var (implode "x") (Tyapp (implode "bool") [])))`,
  SIMP[hol_term_ok_def; WELLTYPED_CLAUSES; typeof_def; injectivity "hol_type"]);;

let impossible_term_thm = prove
 (`!defs tm.
     holKernelProof_TERM defs tm
     ==> ~(tm = hol_Comb (hol_Var (implode "x") (Tyapp (implode "bool") []))
                         (hol_Var (implode "x") (Tyapp (implode "bool") [])))`,
  REWRITE_TAC[holKernelProof_TERM_def] THEN REPEAT STRIP_TAC THEN
  RFS[term_ok_impossible_term]);;

let Abs_Var = prove
 (`!defs v tm. holKernelProof_TERM defs (hol_Abs v tm) ==> ?s ty. v = hol_Var s ty`,
  SIMP[holKernelProof_TERM_def; hol_term_ok_def] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* invariant lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

let CONTEXT_ALL_DISTINCT = prove
 (`!defs. holKernelProof_CONTEXT defs
          ==> ALL_DISTINCT (MAP FST (FLAT (MAP types_of_upd defs))) /\
              ALL_DISTINCT (MAP FST (FLAT (MAP consts_of_upd defs)))`,
  RW[holKernelProof_CONTEXT_def] THEN
  ASM_MESON_TAC[extends_ALL_DISTINCT; init_ALL_DISTINCT]);;

let STATE_ALL_DISTINCT = prove
 (`!defs s. holKernelProof_STATE defs s
            ==> ALL_DISTINCT (MAP FST (hol_refs_the_type_constants s)) /\
                ALL_DISTINCT (MAP FST (hol_refs_the_term_constants s))`,
  RW[holKernelProof_STATE_def] THEN ASM_MESON_TAC[CONTEXT_ALL_DISTINCT]);;

let TYPE_Tyapp = prove
 (`!tyop args r defs.
     MEM (tyop,LENGTH args) (hol_refs_the_type_constants r) /\
     holKernelProof_STATE defs r /\ ALL (holKernelProof_TYPE defs) args
     ==> holKernelProof_TYPE defs (Tyapp tyop args)`,
  RW[GSYM ALL_MEM; holKernelProof_TYPE_def] THEN
  IMP_RES_TAC STATE_ALL_DISTINCT THEN
  RW[type_ok_def; GSYM ALL_MEM] THEN
  FS[holKernelProof_STATE_def; ALOOKUP_EQ_FLOOKUP] THEN
  ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]);;

let CONTEXT_std_sig = prove
 (`!defs. holKernelProof_CONTEXT defs
          ==> is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd defs)),
                          alist_to_fmap (FLAT (MAP consts_of_upd defs)))`,
  RW[holKernelProof_CONTEXT_def] THEN
  IMP_RES_TAC extends_theory_ok THEN RFS[init_theory_ok] THEN
  IMP_RES_TAC theory_ok_sig THEN RFS[]);;

let CONTEXT_fun = prove
 (`!defs. holKernelProof_CONTEXT defs
          ==> !a. MEM (implode "fun",a) (FLAT (MAP types_of_upd defs)) <=> a = 2`,
  RW[] THEN IMP_RES_TAC CONTEXT_ALL_DISTINCT THEN
  IMP_RES_TAC CONTEXT_std_sig THEN
  RFS[is_std_sig_def; ALOOKUP_EQ_FLOOKUP] THEN
  ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM; ALOOKUP_MEM; injectivity "option"]);;

let TYPE = prove
 (`(!defs state v. holKernelProof_STATE defs state
                   ==> holKernelProof_TYPE defs (Tyvar v)) /\
   (!defs op tys. holKernelProof_TYPE defs (Tyapp op tys)
                  ==> ALL (holKernelProof_TYPE defs) tys)`,
  CONJ_TAC THENL
   [SIMP[holKernelProof_STATE_def; holKernelProof_TYPE_def; type_ok_def];
    RW[HOLKPAUX_TYPE_ETA; type_ok_def]]);;

let TERM = prove
 (`(!defs n ty. holKernelProof_TERM defs (hol_Var n ty)
                ==> holKernelProof_TYPE defs ty) /\
   (!defs n ty. holKernelProof_TERM defs (hol_Const n ty)
                ==> holKernelProof_TYPE defs ty) /\
   (!defs v ty x. holKernelProof_TERM defs (hol_Abs (hol_Var v ty) x)
                  ==> holKernelProof_TERM defs x /\ holKernelProof_TYPE defs ty) /\
   (!defs x y. holKernelProof_TERM defs (hol_Comb x y)
               ==> holKernelProof_TERM defs x /\ holKernelProof_TERM defs y)`,
  RW[holKernelProof_TERM_def; holKernelProof_TYPE_def] THEN
  RFS[hol_term_ok_def; injectivity "hol_term"]);;

let TYPE_Fun = prove
 (`!defs ty1 ty2.
     holKernelProof_CONTEXT defs /\ holKernelProof_TYPE defs ty1 /\
     holKernelProof_TYPE defs ty2
     ==> holKernelProof_TYPE defs (Tyapp (implode "fun") [ty1; ty2])`,
  RW[holKernelProof_TYPE_def; type_ok_def; ALL; LENGTH; ALOOKUP_EQ_FLOOKUP] THEN
  IMP_RES_TAC CONTEXT_fun THEN IMP_RES_TAC CONTEXT_ALL_DISTINCT THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
  ASM_REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`]);;

let TERM_Var_SIMP = prove
 (`!defs n ty. holKernelProof_TERM defs (hol_Var n ty) <=> holKernelProof_TYPE defs ty`,
  RW[holKernelProof_TERM_def; holKernelProof_TYPE_def; hol_term_ok_def]);;

let TERM_Var = prove
 (`!defs ty n. holKernelProof_TYPE defs ty ==> holKernelProof_TERM defs (hol_Var n ty)`,
  MESON_TAC[TERM_Var_SIMP]);;

let IMP_TERM_Abs = prove
 (`!defs str ty bod.
     holKernelProof_TERM defs (hol_Var str ty) /\ holKernelProof_TERM defs bod
     ==> holKernelProof_TERM defs (hol_Abs (hol_Var str ty) bod)`,
  RW[holKernelProof_TERM_def; hol_term_ok_def] THEN ASM_MESON_TAC[]);;

let IMP_TERM_Comb = prove
 (`!defs f a ty1 ty2.
     holKernelProof_TERM defs f /\ holKernelProof_TERM defs a /\
     typeof a = ty1 /\ typeof f = Tyapp (implode "fun") [ty1; ty2]
     ==> holKernelProof_TERM defs (hol_Comb f a)`,
  RW[holKernelProof_TERM_def; hol_term_ok_def; WELLTYPED_CLAUSES] THEN
  ASM_MESON_TAC[term_ok_welltyped]);;

let TERM_Abs = prove
 (`!defs v ty tm.
     holKernelProof_TERM defs (hol_Abs (hol_Var v ty) tm) <=>
     holKernelProof_TYPE defs ty /\ holKernelProof_TERM defs tm`,
  RW[holKernelProof_TERM_def; hol_term_ok_def; holKernelProof_TYPE_def;
     injectivity "hol_term"] THEN MESON_TAC[]);;

(* HOL4: val INST_CORE_LEMMA, INST_CORE_HAS_TYPE with n = sizeof tm and the *)
(* empty environment (the Clash case is impossible then)                    *)
let HOLKPAUX_INST_CORE_LEMMA = prove
 (`!tyin tm.
     welltyped tm
     ==> ?tm'. INST_CORE [] tyin tm = hol_Result tm' /\
               tm' has_type TYPE_SUBST tyin (typeof tm) /\
               (!u uty. VFREE_IN (hol_Var u uty) tm' <=>
                        ?oty. VFREE_IN (hol_Var u oty) tm /\
                              uty = TYPE_SUBST tyin oty)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN MESON_TAC[]);;

(* HOL4: val INST_CORE_EMPTY, before and after its specialisation to the   *)
(* empty environment                                                        *)
let HOLKPAUX_REV_ASSOCD_ID = prove
 (`!env (a:hol_term). ALL (\(x,y). x = y) env ==> REV_ASSOCD a env a = a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD; ALL] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN
  ASM_SIMP_TAC[REV_ASSOCD] THEN MESON_TAC[]);;

let HOLKPAUX_INST_CORE_EMPTY_gen = prove
 (`!tm env. welltyped tm /\ ALL (\(x,y). x = y) env
            ==> INST_CORE env [] tm = hol_Result tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [SIMP[INST_CORE_def; TYPE_SUBST_NIL; HOLKPAUX_REV_ASSOCD_ID];
    SIMP[INST_CORE_def; TYPE_SUBST_NIL];
    STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    RW[INST_CORE_def; IS_CLASH_def; RESULT_def];
    STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (a0,a0) env:(hol_term#hol_term)list`) THEN
    SIMP[INST_CORE_def; TYPE_SUBST_NIL; dest_var_def; ALL; IS_RESULT_def;
          RESULT_def]]);;

let HOLKPAUX_INST_CORE_EMPTY = prove
 (`!tm. welltyped tm ==> INST_CORE [] [] tm = hol_Result tm`,
  SIMP_TAC[HOLKPAUX_INST_CORE_EMPTY_gen; ALL]);;

let THM = prove
 (`!defs asl c. holKernelProof_THM defs (Sequent asl c)
                ==> ALL (holKernelProof_TERM defs) asl /\ holKernelProof_TERM defs c`,
  REWRITE_TAC[holKernelProof_THM_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[ALL; holKernelProof_TERM_def; GSYM ALL_MEM; FST; SND] THEN
  MESON_TAC[]);;

(* HOL4: val type_IND, holSyntaxExtra's type_ind *)

let type_subst_EMPTY = prove
 (`!ty. holKernel_type_subst [] ty = ty`,
  MATCH_MP_TAC type_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_type_subst_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[rev_assocd_thm; REV_ASSOCD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `MAP (holKernel_type_subst []) l = l` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MAP_EQ_ID] THEN ASM_MESON_TAC[ALL_MEM]);;

let MAP_EQ_2 = prove
 (`!(f:A->B) l x y. MAP f l = [x; y] <=> ?x0 y0. l = [x0; y0] /\ x = f x0 /\ y = f y0`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; distinctness "list"; CONS_11] THEN
  SPEC_TAC(`t:A list`,`t:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; distinctness "list"; CONS_11; MAP_EQ_NIL] THEN
  MESON_TAC[]);;

let sequent_has_type_bool = prove
 (`!d h c. (d,h) |- c
           ==> ALL (\t. t has_type Tyapp (implode "bool") []) (CONS c h)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[ALL; GSYM ALL_MEM; SND] THEN MESON_TAC[]);;

let THM_term_ok_bool = prove
 (`!defs asl p.
     holKernelProof_THM defs (Sequent asl p)
     ==> ALL (\t. hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd defs)),
                               alist_to_fmap (FLAT (MAP consts_of_upd defs))) t /\
                  typeof t = Tyapp (implode "bool") [])
             (CONS p asl)`,
  REWRITE_TAC[holKernelProof_THM_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[ALL; GSYM ALL_MEM; FST; SND] THEN MESON_TAC[WELLTYPED_LEMMA]);;

(* TODO move *)
let ALOOKUP_ALL_DISTINCT_MEM_EXISTS = prove
 (`!alist (v:B). (?k:A. MEM (k,v) alist) /\ ALL_DISTINCT (MAP FST alist)
                 ==> ?k. ALOOKUP alist k = SOME v`,
  MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]);;

let the_term_constants_TYPE = prove
 (`!defs refs.
     holKernelProof_STATE defs refs
     ==> ALL (\(nm,ty). holKernelProof_TYPE defs ty)
             (hol_refs_the_term_constants refs)`,
  REWRITE_TAC[holKernelProof_STATE_def; holKernelProof_TYPE_def; GSYM ALL_MEM;
              FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC CONTEXT_ALL_DISTINCT THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_CONTEXT_def]) THEN
  MP_TAC(SPECL [`init_ctxt`; `defs:update list`] extends_theory_ok) THEN
  ASM_REWRITE_TAC[init_theory_ok; theory_ok_def; FST; SND] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[IN_FRANGE_FLOOKUP; ALOOKUP_EQ_FLOOKUP] THEN
  ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]);;

let HOLKPAUX_MEM_axexts = prove
 (`!defs x. MEM x (FLAT (MAP axexts_of_upd defs))
            ==> MEM x (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                               (conexts_of_upd upd)) defs))`,
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN MESON_TAC[MEM_APPEND]);;

let the_axioms_THM = prove
 (`!defs refs.
     holKernelProof_STATE defs refs
     ==> ALL (holKernelProof_THM defs) (hol_refs_the_axioms refs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernelProof_STATE_def] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[lift_tm_def; holKernelProof_THM_def] THEN
  MATCH_MP_TAC proves_axioms THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
    EXISTS_TAC `init_ctxt` THEN
    ASM_REWRITE_TAC[init_theory_ok; GSYM holKernelProof_CONTEXT_def];
    REWRITE_TAC[SND; IN_SET_OF_LIST] THEN
    MATCH_MP_TAC HOLKPAUX_MEM_axexts THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Verification of type functions                                            *)
(* ------------------------------------------------------------------------- *)

let can_thm = prove
 (CASE_TERM
  `!(f:X->A->(B,C)exc#A) x s.
     ml_monadBase_can f x s =
     match f x s with
       (M_success _,s) -> (M_success T,s)
     | (_,s) -> (M_success F,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ml_monadBase_can_def; st_ex_ignore_bind_def; otherwise_def] THEN
  MP_TAC(ISPEC `(f:X->A->(B,C)exc#A) x s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(B,C)exc` (X_CHOOSE_THEN `s1:A` SUBST1_TAC)) THEN
  STRUCT_CASES_TAC(ISPEC `r:(B,C)exc` (cases "exc")) THEN
  CAKE_REWRITE_TAC[st_ex_return_def]);;

let assoc_thm = prove
 (`!xs (y:A) (z:(B,hol_exn)exc) s s'.
     holKernel_assoc y xs s = (z,s')
     ==> s' = s /\ (!i. z = M_success i ==> MEM (y,i) xs) /\
         (!e. z = M_failure e ==> !i. ~MEM (y,i) xs)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_assoc_def] THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; MEM] THENL
   [MESON_TAC[distinctness "exc"];
    PAIR_CASES_ON `h:A#B` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
    ASM_MESON_TAC[injectivity "exc"; distinctness "exc"]]);;

let get_type_arity_thm = prove
 (`!name s z s'.
     holKernel_get_type_arity name s = (z,s')
     ==> s' = s /\
         (!i. z = M_success i ==> MEM (name,i) (hol_refs_the_type_constants s)) /\
         (!e. z = M_failure e ==> !i. ~MEM (name,i) (hol_refs_the_type_constants s))`,
  REWRITE_TAC[holKernel_get_type_arity_def; st_ex_bind_def;
              holKernel_get_the_type_constants_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP assoc_thm) THEN REWRITE_TAC[]);;

let mk_vartype_thm = prove
 (`!name s ctxt. holKernelProof_STATE ctxt s
            ==> holKernelProof_TYPE ctxt (holKernel_mk_vartype name)`,
  SIMP[holKernel_mk_vartype_def; holKernelProof_TYPE_def; type_ok_def]);;

let mk_type_thm = prove
 (`!tyop args s z s' defs.
     holKernel_mk_type (tyop,args) s = (z,s') /\
     holKernelProof_STATE defs s /\
     ALL (holKernelProof_TYPE defs) args
     ==> s' = s /\
         (tyop = implode "fun" /\ LENGTH args = 2 ==> ?i. z = M_success i) /\
         !i. z = M_success i ==> holKernelProof_TYPE defs i /\ i = Tyapp tyop args`,
  REWRITE_TAC[holKernel_mk_type_def; holKernel_try_def; st_ex_bind_def;
              otherwise_def] THEN
  REPEAT GEN_TAC THEN QCASES_ON "holKernel_get_type_arity tyop s" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_type_arity_thm) THEN
  QCASES_ON "x" THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def] THEN
  RW[] THEN RFS[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  TRY(MATCH_MP_TAC TYPE_Tyapp THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_STATE_def]) THEN
  ASM_MESON_TAC[CONTEXT_fun]);;

let mk_type_bool = prove
 (`!defs s. holKernelProof_STATE defs s
   ==> holKernel_mk_type (implode "bool",[]) s =
       (M_success (Tyapp (implode "bool") []),s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. MEM (implode "bool",a) (hol_refs_the_type_constants s) <=> a = 0`
    ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[holKernelProof_STATE_def]) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTEXT_ALL_DISTINCT) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTEXT_std_sig) THEN
    REWRITE_TAC[is_std_sig_def; ALOOKUP_EQ_FLOOKUP; FST] THEN
    ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM; ALOOKUP_MEM; injectivity "option"];
    ALL_TAC] THEN
  REWRITE_TAC[holKernel_mk_type_def; st_ex_bind_def; holKernel_try_def;
              otherwise_def] THEN
  QCASES_ON "holKernel_get_type_arity (implode \"bool\") s" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_type_arity_thm) THEN
  QCASES_ON "x" THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; LENGTH] THEN
  ASM_MESON_TAC[]);;

let dest_type_thm = prove
 (`!ty s z s' defs.
     holKernelProof_STATE defs s /\
     holKernel_dest_type ty s = (z,s') /\ holKernelProof_TYPE defs ty
     ==> s' = s /\
         !i. z = M_success i
             ==> ?n tys. ty = Tyapp n tys /\ i = (n,tys) /\
                         ALL (holKernelProof_TYPE defs) tys`,
  GEN_TAC THEN QCASES_ON "ty" THEN
  REWRITE_TAC[holKernel_dest_type_def] THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"; injectivity "hol_type"] THEN
  ASM_MESON_TAC[TYPE]);;

let dest_vartype_thm = prove
 (`!ty s z s'.
     holKernel_dest_vartype ty s = (z,s')
     ==> s' = s /\ !i. z = M_success i ==> ty = Tyvar i`,
  GEN_TAC THEN QCASES_ON "ty" THEN
  REWRITE_TAC[holKernel_dest_vartype_def] THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"]);;

let is_type_thm = prove
 (`!ty. holKernel_is_type ty <=> ?s tys. ty = Tyapp s tys`,
  GEN_TAC THEN QCASES_ON "ty" THEN
  REWRITE_TAC[holKernel_is_type_def] THEN
  CAKE_REWRITE_TAC[injectivity "hol_type"; distinctness "hol_type"] THEN
  MESON_TAC[]);;

let is_vartype_thm = prove
 (`!ty. holKernel_is_vartype ty <=> ?s. ty = Tyvar s`,
  GEN_TAC THEN QCASES_ON "ty" THEN
  REWRITE_TAC[holKernel_is_vartype_def] THEN
  CAKE_REWRITE_TAC[injectivity "hol_type"; distinctness "hol_type"] THEN
  MESON_TAC[]);;

(* the members of a union of lists, for both kinds of tyvars *)
let HOLKPAUX_MEM_itlist_union = prove
 (`!l (f:A->B list) s.
     MEM s (itlist hol_union (MAP f l) []) <=> ?a. MEM a l /\ MEM s (f a)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[itlist_def] THEN
  ASM_REWRITE_TAC[MAP; MEM; MEM_union] THEN CAKE_REWRITE_TAC[MEM] THEN
  ASM_REWRITE_TAC[MEM_union] THEN MESON_TAC[]);;

let tyvars_thm = prove
 (`!ty s. MEM s (holKernel_tyvars ty) <=> MEM s (hol_tyvars ty)`,
  MATCH_MP_TAC holKernel_tyvars_ind THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  QCASES_ON "x" THEN ONCE_REWRITE_TAC[holKernel_tyvars_def] THEN
  CAKE_REWRITE_TAC[hol_tyvars_def; HOLKPAUX_MEM_itlist_union;
                   MEM_FOLDR_LIST_UNION; MEM] THEN
  ASM_MESON_TAC[]);;

(* the first conjunct of type_subst *)
let HOLKPAUX_type_subst_TYPE_SUBST = prove
 (`!i ty. holKernel_type_subst i ty = TYPE_SUBST i ty`,
  MATCH_MP_TAC holKernel_type_subst_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  QCASES_ON "ty" THEN ONCE_REWRITE_TAC[holKernel_type_subst_def] THEN
  CAKE_REWRITE_TAC[TYPE_SUBST_def; rev_assocd_thm] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `MAP (holKernel_type_subst i) a1 = MAP (TYPE_SUBST i) a1` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4: type_subst *)
let holKernelProof_type_subst = prove
 (`!i ty s.
     holKernel_type_subst i ty = TYPE_SUBST i ty /\
     (ALL (\(x,y). holKernelProof_TYPE s x /\ holKernelProof_TYPE s y) i /\
      holKernelProof_TYPE s ty
      ==> holKernelProof_TYPE s (holKernel_type_subst i ty))`,
  REWRITE_TAC[HOLKPAUX_type_subst_TYPE_SUBST; holKernelProof_TYPE_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC type_ok_TYPE_SUBST THEN
  ASM_REWRITE_TAC[ALL_MAP] THEN
  UNDISCH_TAC `ALL (\(x,y). type_ok (alist_to_fmap (FLAT (MAP types_of_upd s))) x /\
                            type_ok (alist_to_fmap (FLAT (MAP types_of_upd s))) y)
                   (i:(hol_type#hol_type)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN MESON_TAC[]);;

let mk_fun_ty_thm = prove
 (`!ty1 ty2 defs i.
     holKernelProof_CONTEXT defs /\ ALL (holKernelProof_TYPE defs) [ty1; ty2] /\
     holKernel_mk_fun_ty ty1 ty2 = i
     ==> i = Tyapp (implode "fun") [ty1; ty2] /\ holKernelProof_TYPE defs i`,
  RW[holKernel_mk_fun_ty_def; ALL] THEN MATCH_MP_TAC TYPE_Fun THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Verification of term functions                                            *)
(* ------------------------------------------------------------------------- *)

(* HOL4: Overload aty[local] = ``(Tyvar <<A>>):type``, written out *)

let get_const_type_thm = prove
 (`!name s z s'.
     holKernel_get_const_type name s = (z,s')
     ==> s' = s /\
         (!i. z = M_success i ==> MEM (name,i) (hol_refs_the_term_constants s)) /\
         (!e. z = M_failure e ==> !i. ~MEM (name,i) (hol_refs_the_term_constants s))`,
  REWRITE_TAC[holKernel_get_const_type_def; st_ex_bind_def;
              holKernel_get_the_term_constants_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP assoc_thm) THEN REWRITE_TAC[]);;

let term_type_def = cake_def
  `term_type tm =
     match tm with
       hol_Var _ ty -> ty
     | hol_Const _ ty -> ty
     | hol_Comb s _ ->
         (match term_type s with
            Tyapp nm (CONS _ (CONS ty1 _)) ->
              if nm = implode "fun" then ty1 else Tyvar (implode "")
          | _ -> Tyvar (implode ""))
     | hol_Abs (hol_Var _ ty) t -> Tyapp (implode "fun") [ty; term_type t]
     | _ -> Tyvar (implode "")`;;

let term_type = prove
 (`!defs tm. holKernelProof_CONTEXT defs /\ holKernelProof_TERM defs tm
             ==> term_type tm = typeof tm /\ holKernelProof_TYPE defs (term_type tm)`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[typeof_def] THEN
    MESON_TAC[TERM];
    ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[typeof_def] THEN
    MESON_TAC[TERM];
    STRIP_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (el 3 (CONJUNCTS TERM))) THEN
    UNDISCH_TAC `holKernelProof_TERM defs (hol_Comb a0 a1)` THEN
    REWRITE_TAC[holKernelProof_TERM_def; hol_term_ok_def; WELLTYPED_CLAUSES] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `term_type a0 = typeof a0 /\ holKernelProof_TYPE defs (term_type a0)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[typeof_def] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[codomain_def] THEN
    UNDISCH_TAC `holKernelProof_TYPE defs (term_type a0)` THEN
    ASM_REWRITE_TAC[holKernelProof_TYPE_def; type_ok_def; ALL] THEN
    SIMP_TAC[];
    STRIP_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Abs_Var) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (el 2 (CONJUNCTS TERM))) THEN
    SUBGOAL_THEN `term_type a1 = typeof a1 /\ holKernelProof_TYPE defs (term_type a1)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[typeof_def] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYPE_Fun THEN ASM_MESON_TAC[]]);;

(* HOL4 proves type_of_has_type before type_of_thm, from type_of_def; here *)
(* type_of_thm comes first and type_of_has_type follows from it            *)
let type_of_thm = prove
 (`!tm defs s. holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s
        ==> holKernel_type_of tm s = (M_success (term_type tm),s)`,
  MATCH_MP_TAC holKernel_type_of_ind THEN GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  QCASES_ON "tm" THEN ONCE_REWRITE_TAC[holKernel_type_of_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def] THEN
  RFS[injectivity "hol_term"; distinctness "hol_term"] THENL
   [ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[];
    ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (el 3 (CONJUNCTS TERM))) THEN
    SUBGOAL_THEN `holKernel_type_of a0 s = M_success (term_type a0),s` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?rty. term_type a0 = Tyapp (implode "fun") [typeof a1; rty]`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `holKernelProof_TERM defs (hol_Comb a0 a1)` THEN
      REWRITE_TAC[holKernelProof_TERM_def; hol_term_ok_def; WELLTYPED_CLAUSES] THEN
      ASM_MESON_TAC[term_type];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[st_ex_bind_def] THEN
    CAKE_REWRITE_TAC[holKernel_dest_type_def; st_ex_return_def] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
    ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    FIRST_ASSUM(X_CHOOSE_THEN `nm:mlstring` (X_CHOOSE_THEN `ty:hol_type`
      SUBST_ALL_TAC) o MATCH_MP Abs_Var) THEN
    CAKE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `holKernel_type_of a1 s = M_success (term_type a1),s` ASSUME_TAC THENL
     [ASM_MESON_TAC[TERM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[st_ex_bind_def] THEN
    CAKE_REWRITE_TAC[holKernel_mk_fun_ty_def] THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
    GEN_REWRITE_TAC RAND_CONV [term_type_def] THEN CAKE_REWRITE_TAC[]]);;

let type_of_has_type = prove
 (`!tm refs ty refs' defs.
     holKernelProof_STATE defs refs /\
     holKernelProof_TERM defs tm /\
     holKernel_type_of tm refs = (M_success ty,refs')
     ==> tm has_type ty /\ typeof tm = ty`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ty = term_type tm` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[type_of_thm; PAIR_EQ; injectivity "exc"]; ALL_TAC] THEN
  SUBGOAL_THEN `term_type tm = typeof tm` SUBST1_TAC THENL
   [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  REWRITE_TAC[GSYM WELLTYPED] THEN
  ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped]);;

let alphavars_thm = prove
 (`!env s defs tm1 tm2. holKernelProof_STATE defs s /\ holKernelProof_TERM defs tm1 /\
         holKernelProof_TERM defs tm2 /\
         ALL (\(v1,v2). holKernelProof_TERM defs v1 /\ holKernelProof_TERM defs v2) env
         ==> (holKernel_alphavars env tm1 tm2 <=> ALPHAVARS env (tm1,tm2))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[holKernel_alphavars_def] THEN
  CAKE_REWRITE_TAC[ALPHAVARS_def] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN
  CAKE_REWRITE_TAC[ALL; ALPHAVARS_def; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_refs`; `defs:update list`; `tm1:hol_term`;
                                `tm2:hol_term`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[]);;

let raconv_thm = prove
 (`!tm1 tm2 env s defs.
     holKernelProof_STATE defs s /\ holKernelProof_TERM defs tm1 /\
     holKernelProof_TERM defs tm2 /\
     ALL (\(v1,v2). holKernelProof_TERM defs v1 /\ holKernelProof_TERM defs v2) env
     ==> (holKernel_raconv env tm1 tm2 <=> RACONV env (tm1,tm2))`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN QCASES_ON "tm2" THEN
  ONCE_REWRITE_TAC[holKernel_raconv_def] THEN
  CAKE_REWRITE_TAC[RACONV; injectivity "hol_term"; distinctness "hol_term"] THENL
   [MATCH_MP_TAC alphavars_thm THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[TERM];
    QPAT_ASSUM "holKernelProof_TERM defs (hol_Abs a0 a1)"
      (MP_TAC o MATCH_MP Abs_Var) THEN
    QPAT_ASSUM "holKernelProof_TERM defs (hol_Abs a0' a1')"
      (MP_TAC o MATCH_MP Abs_Var) THEN
    REPEAT STRIP_TAC THEN GVS[] THEN CAKE_REWRITE_TAC[typeof_def] THEN
    ASM_CASES_TAC `ty = ty':hol_type` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[TERM; TERM_Var]]);;

let aconv_thm = prove
 (`!tm1 tm2 (env:(hol_term#hol_term)list) s defs.
     holKernelProof_STATE defs s /\ holKernelProof_TERM defs tm1 /\
     holKernelProof_TERM defs tm2
     ==> (holKernel_aconv tm1 tm2 <=> ACONV tm1 tm2)`,
  REWRITE_TAC[holKernel_aconv_def; ACONV_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC raconv_thm THEN
  MAP_EVERY EXISTS_TAC [`s:hol_refs`; `defs:update list`] THEN
  ASM_REWRITE_TAC[ALL]);;

let is_term_thm = prove
 (`!tm. (holKernel_is_var tm <=> ?n ty. tm = hol_Var n ty) /\
   (holKernel_is_const tm <=> ?n ty. tm = hol_Const n ty) /\
   (holKernel_is_abs tm <=> ?v x. tm = hol_Abs v x) /\
   (holKernel_is_comb tm <=> ?x y. tm = hol_Comb x y)`,
  GEN_TAC THEN QCASES_ON "tm" THEN
  REWRITE_TAC[holKernel_is_var_def; holKernel_is_const_def; holKernel_is_abs_def;
              holKernel_is_comb_def] THEN
  CAKE_REWRITE_TAC[injectivity "hol_term"; distinctness "hol_term"] THEN
  MESON_TAC[]);;

let mk_var_thm = prove
 (`!s defs v ty. holKernelProof_STATE defs s /\ holKernelProof_TYPE defs ty
   ==> holKernelProof_TERM defs (holKernel_mk_var (v,ty))`,
  SIMP_TAC[holKernel_mk_var_def] THEN MESON_TAC[TERM_Var]);;

let mk_abs_thm = prove
 (`!res s1 s defs bvar bod. holKernel_mk_abs (bvar,bod) s = (res,s1) /\
         holKernelProof_TERM defs bvar /\ holKernelProof_TERM defs bod
         ==> s1 = s /\
             !t. res = M_success t ==> holKernelProof_TERM defs t /\
                                       t = hol_Abs bvar bod`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernel_mk_abs_def] THEN QCASES_ON "bvar" THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN
  ASM_MESON_TAC[IMP_TERM_Abs]);;

let mk_comb_thm = prove
 (`!s1 s res defs f a. holKernel_mk_comb (f,a) s = (res,s1) /\ holKernelProof_TERM defs f /\
   holKernelProof_TERM defs a /\ holKernelProof_STATE defs s
   ==> s1 = s /\
       (!t. res = M_failure t
            ==> !ty. ~(term_type f = Tyapp (implode "fun") [term_type a; ty])) /\
       !t. res = M_success t ==> holKernelProof_TERM defs t /\ t = hol_Comb f a`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  SUBGOAL_THEN `holKernel_type_of f s = (M_success (term_type f),s) /\
                holKernel_type_of a s = (M_success (term_type a),s)`
    (fun th -> SIMP[holKernel_mk_comb_def; st_ex_bind_def; th]) THENL
   [ASM_MESON_TAC[type_of_thm]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"; injectivity "hol_type"] THEN
  MATCH_MP_TAC IMP_TERM_Comb THEN ASM_MESON_TAC[term_type]);;

let dest_var_thm = prove
 (`!v s s' res defs. holKernelProof_TERM defs v /\ holKernelProof_STATE defs s
   ==> holKernel_dest_var v s = (res,s')
   ==> s' = s /\ !n ty. res = M_success (n,ty) ==> holKernelProof_TYPE defs ty`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN REWRITE_TAC[holKernel_dest_var_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN ASM_MESON_TAC[TERM]);;

(* HOL4: dest_const_thm *)
let holKernelProof_dest_const_thm = prove
 (`!v s s' res defs. holKernelProof_TERM defs v /\ holKernelProof_STATE defs s
   ==> holKernel_dest_const v s = (res,s')
   ==> s' = s /\ !n ty. res = M_success (n,ty) ==> holKernelProof_TYPE defs ty`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN REWRITE_TAC[holKernel_dest_const_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN ASM_MESON_TAC[TERM]);;

let dest_comb_thm = prove
 (`!v s s' res defs. holKernel_dest_comb v s = (res,s')
   ==> holKernelProof_TERM defs v /\ holKernelProof_STATE defs s
   ==> s' = s /\
       !x y. res = M_success (x,y) ==> holKernelProof_TERM defs x /\
                                       holKernelProof_TERM defs y`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN REWRITE_TAC[holKernel_dest_comb_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN ASM_MESON_TAC[TERM]);;

let dest_abs_thm = prove
 (`!v s s' res defs. holKernelProof_TERM defs v /\ holKernelProof_STATE defs s
   ==> holKernel_dest_abs v s = (res,s')
   ==> s' = s /\
       !x y. res = M_success (x,y) ==> holKernelProof_TERM defs x /\
                                       holKernelProof_TERM defs y`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN REWRITE_TAC[holKernel_dest_abs_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Abs_Var) THEN
  GVS[] THEN ASM_MESON_TAC[TERM; TERM_Var]);;

let rator_thm = prove
 (`!v s s' res defs. holKernelProof_TERM defs v /\ holKernelProof_STATE defs s
   ==> holKernel_rator v s = (res,s')
   ==> s' = s /\ !x. res = M_success x ==> holKernelProof_TERM defs x`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN REWRITE_TAC[holKernel_rator_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN ASM_MESON_TAC[TERM]);;

let rand_thm = prove
 (`!v s s' res defs. holKernelProof_TERM defs v /\ holKernelProof_STATE defs s
   ==> holKernel_rand v s = (res,s')
   ==> s' = s /\ !x. res = M_success x ==> holKernelProof_TERM defs x`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN REWRITE_TAC[holKernel_rand_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN ASM_MESON_TAC[TERM]);;
let type_subst_bool = prove
 (`!i. holKernel_type_subst i (Tyapp (implode "bool") []) = Tyapp (implode "bool") []`,
  REWRITE_TAC[HOLKPAUX_type_subst_TYPE_SUBST; TYPE_SUBST_def; MAP]);;

let type_subst_fun = prove
 (`!i ty1 ty2.
     holKernel_type_subst i (Tyapp (implode "fun") [ty1; ty2]) =
   Tyapp (implode "fun") [holKernel_type_subst i ty1; holKernel_type_subst i ty2]`,
  REWRITE_TAC[HOLKPAUX_type_subst_TYPE_SUBST; TYPE_SUBST_def; MAP]);;

let TERM_Const = prove
 (`!defs r name a.
     holKernelProof_STATE defs r /\ MEM (name,a) (hol_refs_the_term_constants r)
     ==> holKernelProof_TERM defs (hol_Const name a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP the_term_constants_TYPE) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`name:mlstring`; `a:hol_type`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STATE_ALL_DISTINCT) THEN
  UNDISCH_TAC `holKernelProof_STATE defs r` THEN
  REWRITE_TAC[holKernelProof_STATE_def] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && can (find_term ((=) `r:hol_refs`)) (lhs (concl th))))) THEN
  REWRITE_TAC[holKernelProof_TERM_def; holKernelProof_TYPE_def; hol_term_ok_def;
              ALOOKUP_EQ_FLOOKUP; FST; SND] THEN
  DISCH_TAC THEN EXISTS_TAC `a:hol_type` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]; ALL_TAC] THEN
  EXISTS_TAC `[]:(hol_type#hol_type)list` THEN REWRITE_TAC[TYPE_SUBST_NIL]);;
let TERM_Const_type_subst = prove
 (`!defs theta name a.
     ALL (\(x,y). holKernelProof_TYPE defs x /\ holKernelProof_TYPE defs y) theta /\
     holKernelProof_TERM defs (hol_Const name a)
     ==> holKernelProof_TERM defs (hol_Const name (holKernel_type_subst theta a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernelProof_TERM_def; holKernelProof_TYPE_def; hol_term_ok_def;
              HOLKPAUX_type_subst_TYPE_SUBST; FST; SND] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC `ty0:hol_type` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_REWRITE_TAC[ALL_MAP] THEN
    UNDISCH_TAC `ALL (\(x,y). type_ok (alist_to_fmap (FLAT (MAP types_of_upd defs))) x /\
                              type_ok (alist_to_fmap (FLAT (MAP types_of_upd defs))) y)
                     (theta:(hol_type#hol_type)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN MESON_TAC[];
    REWRITE_TAC[TYPE_SUBST_compose] THEN MESON_TAC[]]);;
(* the parts of STATE without the equation of the context, which would     *)
(* rewrite defs everywhere                                                  *)
let HOLKPAUX_STATE_CONJ = prove
 (`!defs s. holKernelProof_STATE defs s
            ==> holKernelProof_CONTEXT defs /\
                hol_refs_the_type_constants s = FLAT (MAP types_of_upd defs) /\
                hol_refs_the_term_constants s = FLAT (MAP consts_of_upd defs) /\
                hol_refs_the_axioms s = MAP lift_tm (FLAT (MAP axexts_of_upd defs))`,
  SIMP_TAC[holKernelProof_STATE_def]);;

let get_const_type_Equal = prove
 (`!defs s.
     holKernelProof_STATE defs s
     ==> holKernel_get_const_type (implode "=") s =
       (M_success (Tyapp (implode "fun")
          [Tyvar (implode "A");
           Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]]),s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTEXT_ALL_DISTINCT) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTEXT_std_sig) THEN
  REWRITE_TAC[is_std_sig_def; ALOOKUP_EQ_FLOOKUP; FST; SND] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`implode "="`; `s:hol_refs`] get_const_type_thm) THEN
  ASM_REWRITE_TAC[] THEN
  QCASES_ON "holKernel_get_const_type (implode \"=\") s" THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN QCASES_ON "x" THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM; ALOOKUP_MEM; injectivity "option"]);;
let mk_const_thm = prove
 (`!name theta s z s' defs.
     holKernel_mk_const (name,theta) s = (z,s') /\
     holKernelProof_STATE defs s /\
     ALL (\(x,y). holKernelProof_TYPE defs x /\ holKernelProof_TYPE defs y) theta
     ==> s' = s /\ !i. z = M_success i ==> holKernelProof_TERM defs i`,
  REWRITE_TAC[holKernel_mk_const_def; holKernel_try_def; st_ex_bind_def;
              otherwise_def] THEN
  REPEAT GEN_TAC THEN QCASES_ON "holKernel_get_const_type name s" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_const_type_thm) THEN
  QCASES_ON "x" THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN
  MATCH_MP_TAC TERM_Const_type_subst THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TERM_Const THEN ASM_MESON_TAC[]);;

let mk_const_eq = prove
 (`!defs s.
     holKernelProof_STATE defs s
     ==> holKernel_mk_const (implode "=",[]) s =
       (M_success (hol_Const (implode "=")
          (Tyapp (implode "fun")
            [Tyvar (implode "A");
             Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])),s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_const_type_Equal) THEN
  ASM_REWRITE_TAC[holKernel_mk_const_def; st_ex_bind_def; holKernel_try_def;
                  otherwise_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; type_subst_EMPTY]);;

let mk_eq_lemma = prove
 (`!x s.
   holKernel_inst [(term_type x,Tyvar (implode "A"))]
     (hol_Const (implode "=")
        (Tyapp (implode "fun")
          [Tyvar (implode "A");
           Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])) s =
   st_ex_return
     (hol_Const (implode "=")
        (Tyapp (implode "fun")
          [term_type x;
           Tyapp (implode "fun") [term_type x; Tyapp (implode "bool") []]])) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernel_inst_def; NOT_CONS_NIL] THEN
  ONCE_REWRITE_TAC[holKernel_inst_aux_def] THEN CAKE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[HOLKPAUX_type_subst_TYPE_SUBST; TYPE_SUBST_def; MAP; REV_ASSOCD] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_type"; CONS_11]) THEN
  ASM_REWRITE_TAC[]);;

let safe_mk_eq_thm = prove
 (`!x y s res s' defs.
     holKernel_safe_mk_eq x y s = (res,s')
     ==> holKernelProof_TERM defs x /\ holKernelProof_TERM defs y /\
         holKernelProof_STATE defs s
     ==> typeof x = typeof y
     ==> s' = s /\ (!t. ~(res = M_failure t)) /\
         (!t. res = M_success t
              ==> t = hol_Comb (hol_Comb (hol_Const (implode "=")
                         (Tyapp (implode "fun")
                           [term_type x;
                            Tyapp (implode "fun")
                              [term_type x; Tyapp (implode "bool") []]])) x) y /\
                  holKernelProof_TERM defs t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  SUBGOAL_THEN `holKernel_type_of x s = (M_success (term_type x),s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[type_of_thm]; ALL_TAC] THEN
  UNDISCH_TAC `holKernel_safe_mk_eq x y s = (res,s')` THEN
  ASM_REWRITE_TAC[holKernel_safe_mk_eq_def; st_ex_bind_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"; holKernel_bool_ty_def] THEN
  SUBGOAL_THEN `term_type x = typeof x` SUBST1_TAC THENL
   [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  REWRITE_TAC[GSYM equation_def] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[holKernelProof_TERM_def] THEN
  ASM_SIMP_TAC[term_ok_clauses; CONTEXT_std_sig] THEN
  ASM_MESON_TAC[holKernelProof_TERM_def]);;

(* type_of on constants and combinations (HOL4: SIMP_CONV with Once type_of_def) *)
let HOLKPAUX_type_of_Const = prove
 (`!n ty. holKernel_type_of (hol_Const n ty) = st_ex_return ty`,
  ONCE_REWRITE_TAC[holKernel_type_of_def] THEN CAKE_REWRITE_TAC[]);;

let HOLKPAUX_type_of_Comb = prove
 (CASE_TERM
  `!s t. holKernel_type_of (hol_Comb s t) =
         st_ex_bind (holKernel_type_of s) (\ty.
         st_ex_bind (holKernel_dest_type ty) (\x.
         match x with
           (_,CONS _ (CONS ty1 _)) -> st_ex_return ty1
         | _ -> holKernel_raise_Failure (implode "match")))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [holKernel_type_of_def] THEN
  CAKE_REWRITE_TAC[]);;

let mk_eq_thm = prove
 (`!x y s res s' defs.
     holKernel_mk_eq (x,y) s = (res,s')
     ==> holKernelProof_TERM defs x /\ holKernelProof_TERM defs y /\
         holKernelProof_STATE defs s
     ==> s' = s /\
         (!t. res = M_failure t ==> ~(term_type x = term_type y)) /\
         !t. res = M_success t
             ==> t = hol_Comb (hol_Comb (hol_Const (implode "=")
                        (Tyapp (implode "fun")
                          [term_type x;
                           Tyapp (implode "fun")
                             [term_type x; Tyapp (implode "bool") []]])) x) y /\
                 holKernelProof_TERM defs t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP mk_const_eq) THEN
  SUBGOAL_THEN `holKernel_type_of x s = (M_success (term_type x),s) /\
                holKernel_type_of y s = (M_success (term_type y),s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[type_of_thm]; ALL_TAC] THEN
  UNDISCH_TAC `holKernel_mk_eq (x,y) s = (res,s')` THEN
  SIMP[holKernel_mk_eq_def; holKernel_try_def; otherwise_def; st_ex_bind_def;
       holKernel_aty_def; mk_eq_lemma; st_ex_return_def; holKernel_mk_comb_def;
       HOLKPAUX_type_of_Const; HOLKPAUX_type_of_Comb; holKernel_dest_type_def;
       holKernel_raise_Failure_def] THEN
  COND_CASES_TAC THEN SIMP[PAIR_EQ] THEN RW[] THEN
  GVS[distinctness "exc"; injectivity "exc"] THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN `term_type x = typeof x /\ term_type y = typeof y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  UNDISCH_TAC `term_type y = term_type x` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM equation_def; holKernelProof_TERM_def] THEN
  ASM_SIMP_TAC[term_ok_clauses; CONTEXT_std_sig] THEN
  ASM_MESON_TAC[holKernelProof_TERM_def]);;

let TERM_Eq_x = prove
 (`!defs s ty x.
     holKernelProof_STATE defs s /\
     holKernelProof_TERM defs (hol_Comb (hol_Const (implode "=") ty) x)
     ==> Tyapp (implode "fun")
           [typeof x; Tyapp (implode "fun") [typeof x; Tyapp (implode "bool") []]] = ty`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTEXT_std_sig) THEN
  UNDISCH_TAC `holKernelProof_TERM defs (hol_Comb (hol_Const (implode "=") ty) x)` THEN
  REWRITE_TAC[holKernelProof_TERM_def; hol_term_ok_def; is_std_sig_def;
              WELLTYPED_CLAUSES; typeof_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  GVS[injectivity "option"; TYPE_SUBST_def; MAP; injectivity "hol_type"; CONS_11]);;

let TERM_Comb = prove
 (`!defs f a.
     holKernelProof_CONTEXT defs
     ==> (holKernelProof_TERM defs (hol_Comb f a) <=>
          holKernelProof_TERM defs f /\ holKernelProof_TERM defs a /\
          ?ty. term_type f = Tyapp (implode "fun") [term_type a; ty])`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (el 3 (CONJUNCTS TERM))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `holKernelProof_TERM defs (hol_Comb f a)` THEN
    REWRITE_TAC[holKernelProof_TERM_def; hol_term_ok_def; WELLTYPED_CLAUSES] THEN
    ASM_MESON_TAC[term_type];
    MATCH_MP_TAC IMP_TERM_Comb THEN ASM_MESON_TAC[term_type]]);;

let MAP_EQ_2_SYM = prove
 (`!(f:A->B) l x y. [x; y] = MAP f l <=> MAP f l = [x; y]`,
  MESON_TAC[]);;

(* HOL4: Equal_type *)
let holKernelProof_Equal_type = prove
 (`!defs s ty.
     holKernelProof_STATE defs s /\ holKernelProof_TERM defs (hol_Const (implode "=") ty)
     ==> ?a. ty = Tyapp (implode "fun")
                    [a; Tyapp (implode "fun") [a; Tyapp (implode "bool") []]]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTEXT_std_sig) THEN
  UNDISCH_TAC `holKernelProof_TERM defs (hol_Const (implode "=") ty)` THEN
  REWRITE_TAC[holKernelProof_TERM_def; hol_term_ok_def; is_std_sig_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  GVS[injectivity "option"; TYPE_SUBST_def; MAP; injectivity "hol_type"; CONS_11] THEN
  MESON_TAC[]);;

let Equal_type_IMP = prove
 (`!defs s a' ll.
     holKernelProof_STATE defs s /\
     holKernelProof_TERM defs
       (hol_Comb (hol_Const (implode "=")
          (Tyapp (implode "fun") [a'; Tyapp (implode "fun") [a'; Tyapp (implode "bool") []]]))
          ll)
     ==> typeof ll = a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TERM_Eq_x o CONJ (ASSUME `holKernelProof_STATE defs s`)) THEN
  REWRITE_TAC[injectivity "hol_type"; CONS_11] THEN MESON_TAC[]);;

let dest_eq_thm = prove
 (`!tm s res s' defs.
     holKernel_dest_eq tm s = (res,s') /\
     holKernelProof_TERM defs tm /\
     holKernelProof_STATE defs s
     ==> s' = s /\
         !t1 t2. res = M_success (t1,t2)
                 ==> holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2 /\
                     tm = hol_Comb (hol_Comb (hol_Const (implode "=")
                            (Tyapp (implode "fun")
                              [typeof t1;
                               Tyapp (implode "fun")
                                 [typeof t1; Tyapp (implode "bool") []]])) t1) t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernel_dest_eq_def] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  RW[] THEN GVS[distinctness "exc"; injectivity "exc"] THEN
  ASM_MESON_TAC[TERM; TERM_Eq_x]);;

let VFREE_IN_IMP = prove
 (`!y defs ty s name.
     holKernelProof_TERM defs y /\ holKernelProof_TYPE defs ty /\
     holKernelProof_STATE defs s /\ VFREE_IN (hol_Var name ty) y
     ==> vfree_in (hol_Var name ty) y`,
  MESON_TAC[vfree_in_thm]);;

let SELECT_LEMMA = prove
 (`!t:hol_term. (@f. !s (s':hol_term). f (s',s) <=> ~(s = t)) =
                (\(z:hol_term,y). ~(y = t))`,
  GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN MESON_TAC[]);;

let SELECT_LEMMA2 = prove
 (`!s' ty tm'.
     (@f. !s s''. f (s'',s) <=>
                  VFREE_IN (hol_Var s' ty) s'' /\ VFREE_IN s tm') =
     (\(x,y). VFREE_IN (hol_Var s' ty) x /\ VFREE_IN y tm')`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN MESON_TAC[]);;

let is_var_thm = prove
 (`!x. holKernel_is_var x <=> ?v ty. x = hol_Var v ty`,
  GEN_TAC THEN QCASES_ON "x" THEN REWRITE_TAC[holKernel_is_var_def] THEN
  CAKE_REWRITE_TAC[injectivity "hol_term"; distinctness "hol_term"] THEN
  MESON_TAC[]);;

let VSUBST_EMPTY = prove
 (`!tm. VSUBST [] tm = tm`,
  REWRITE_TAC[VSUBST_NIL]);;

let VFREE_IN_TYPE = prove
 (`!x name oty defs.
     VFREE_IN (hol_Var name oty) x /\ holKernelProof_TERM defs x
     ==> ?ty. oty = ty /\ holKernelProof_TYPE defs ty`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VFREE_IN_def; injectivity "hol_term"; distinctness "hol_term"] THEN
  REPEAT STRIP_TAC THEN GVS[] THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Abs_Var) THEN GVS[]) THEN
  ASM_MESON_TAC[TERM]);;

let VFREE_IN_IMP_MEM = prove
 (`!name oty h0 defs s.
     VFREE_IN (hol_Var name oty) h0 /\ holKernelProof_TERM defs h0 /\
     holKernelProof_STATE defs s
     ==> ?ty1. MEM (hol_Var name ty1) (hol_frees h0) /\ oty = ty1 /\
               holKernelProof_TYPE defs ty1`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `oty:hol_type` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[vfree_in_IMP; vfree_in_thm]; ASM_MESON_TAC[VFREE_IN_TYPE]]);;

let term_type_Var = prove
 (`!v ty. term_type (hol_Var v ty) = ty`,
  ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[]);;

(* vsubst_aux is VSUBST on welltyped terms, for substitutions of variables *)
let HOLKPAUX_EX_vfree_in = prove
 (`!l n ty tm.
     ALL (\(t1,t2). holKernel_is_var t2) l
     ==> (EX (\(t,x). vfree_in (hol_Var n ty) t /\ vfree_in x tm) l <=>
          EX (\(t,x). VFREE_IN (hol_Var n ty) t /\ VFREE_IN x tm) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; EX] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN CAKE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `holKernel_is_var h1` THEN REWRITE_TAC[is_var_thm] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM vfree_in_thm]);;

let HOLKPAUX_vsubst_aux_VSUBST = prove
 (`!tm theta. welltyped tm /\ ALL (\(t1,t2). holKernel_is_var t2) theta
              ==> holKernel_vsubst_aux theta tm = VSUBST theta tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_vsubst_aux_def] THEN
  CAKE_REWRITE_TAC[VSUBST_def; rev_assocd_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:mlstring` (X_CHOOSE_THEN `ty:hol_type`
    STRIP_ASSUME_TAC)) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[holKernel_is_var_def; dest_var_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL (\(t1,t2). holKernel_is_var t2)
                  (FILTER (\(t,x). ~(x = hol_Var n ty)) (theta:(hol_term#hol_term)list))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\(t1,t2). holKernel_is_var t2) (theta:(hol_term#hol_term)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER; FORALL_PAIR_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `FILTER (\(t:hol_term,x). ~(x = hol_Var n ty))
                   (theta:(hol_term#hol_term)list) = []` THEN
  ASM_REWRITE_TAC[VSUBST_NIL; EX] THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[HOLKPAUX_EX_vfree_in; variant_vsubst_thm] THEN
  SUBGOAL_THEN `!v. holKernel_is_var (hol_Var v ty)` ASSUME_TAC THENL
   [REWRITE_TAC[is_var_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ALL]);;

(* a term with the invariant has its term_type *)
let HOLKPAUX_TERM_has_type = prove
 (`!defs tm. holKernelProof_CONTEXT defs /\ holKernelProof_TERM defs tm
             ==> tm has_type term_type tm`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `term_type tm = typeof tm` SUBST1_TAC THENL
   [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  REWRITE_TAC[GSYM WELLTYPED] THEN
  ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped]);;

let vsubst_aux_thm = prove
 (`!t tm theta defs s.
     ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2 /\
                    term_type t1 = term_type t2 /\ holKernel_is_var t2) theta /\
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s /\
     holKernel_vsubst_aux theta tm = t
     ==> holKernelProof_TERM defs t /\ t = VSUBST theta tm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  SUBGOAL_THEN `t = VSUBST theta tm` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `holKernel_vsubst_aux theta tm = t` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOLKPAUX_vsubst_aux_VSUBST THEN CONJ_TAC THENL
     [ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped];
      UNDISCH_TAC `ALL (\(t1,t2). holKernelProof_TERM defs t1 /\
                                  holKernelProof_TERM defs t2 /\
                                  term_type t1 = term_type t2 /\
                                  holKernel_is_var t2) theta` THEN
      REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN REWRITE_TAC[holKernelProof_TERM_def] THEN
  MATCH_MP_TAC term_ok_VSUBST THEN
  CONJ_TAC THENL [ASM_MESON_TAC[holKernelProof_TERM_def]; ALL_TAC] THEN
  UNDISCH_TAC `ALL (\(t1,t2). holKernelProof_TERM defs t1 /\
                              holKernelProof_TERM defs t2 /\
                              term_type t1 = term_type t2 /\
                              holKernel_is_var t2) theta` THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; is_var_thm] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`p2:hol_term`; `p1:hol_term`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`p1:hol_term`; `p2:hol_term`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[holKernelProof_TERM_def]] THEN
  UNDISCH_TAC `term_type p1 = term_type p2` THEN
  ASM_REWRITE_TAC[term_type_Var] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[HOLKPAUX_TERM_has_type]);;

let forall_thm = prove
 (`!(f:hol_term#hol_term->S->(bool,E)exc#S) s (xs:(hol_term#hol_term)list) res s'.
     holKernel_forall f xs s = (res,s')
     ==> (!x. ?r. f x s = (r,s))
     ==> s' = s /\ (res = M_success T ==> ALL (\x. FST (f x s) = M_success T) xs)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ONCE_REWRITE_TAC[holKernel_forall_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; st_ex_bind_def; PAIR_EQ; ALL] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:(bool,E)exc` o SPEC `h:hol_term#hol_term`) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[PAIR_EQ; FST] THENL
   [COND_CASES_TAC THEN CAKE_REWRITE_TAC[PAIR_EQ] THENL
     [ASM_MESON_TAC[];
      RW[] THEN GVS[injectivity "exc"]];
    RW[] THEN GVS[distinctness "exc"]]);;

let assoc_state = prove
 (`!xs (x:A) s. ?r. holKernel_assoc x xs s = (r:(B,hol_exn)exc,s)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_assoc_def] THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  PAIR_CASES_ON `h:A#B` THEN CAKE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  MESON_TAC[]);;

(* state preservation (HOL4's proofs case-split the monadic code) *)
let HOLKPAUX_st_ex_bind_state = prove
 (`!(m:S->(A,E)exc#S) (f:A->S->(B,E)exc#S) s.
     (!s. ?r. m s = (r,s)) /\ (!x s. ?r. f x s = (r,s))
     ==> ?r. st_ex_bind m f s = (r,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `r:(A,E)exc` o SPEC `s:S`) THEN
  ASM_REWRITE_TAC[st_ex_bind_def] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXISTS_REFL] THEN MESON_TAC[]);;

let HOLKPAUX_dest_type_state = prove
 (`!x s. ?r. holKernel_dest_type x s = (r,s)`,
  GEN_TAC THEN QCASES_ON "x" THEN REWRITE_TAC[holKernel_dest_type_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  MESON_TAC[]);;

let type_of_state = prove
 (`!tm s. ?r. holKernel_type_of tm s = (r,s)`,
  MATCH_MP_TAC holKernel_type_of_ind THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  QCASES_ON "tm" THEN ONCE_REWRITE_TAC[holKernel_type_of_def] THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[st_ex_return_def] THEN MESON_TAC[];
    REWRITE_TAC[st_ex_return_def] THEN MESON_TAC[];
    MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a1:hol_term`; `a0:hol_term`] o CONJUNCT1) THEN
      REWRITE_TAC[];
      REPEAT GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN
      REWRITE_TAC[HOLKPAUX_dest_type_state] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CAKE_REWRITE_TAC[] THEN
      STRUCT_CASES_TAC(ISPEC `p2:hol_type list` list_CASES) THEN
      CAKE_REWRITE_TAC[holKernel_raise_Failure_def] THEN
      REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
      STRUCT_CASES_TAC(ISPEC `t:hol_type list` list_CASES) THEN
      CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def] THEN
      REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]];
    QCASES_ON "a0" THEN CAKE_REWRITE_TAC[holKernel_raise_Failure_def] THEN
    REWRITE_TAC[PAIR_EQ] THENL
     [MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`a0':mlstring`; `a1':hol_type`; `a1:hol_term`] o
                      CONJUNCT2) THEN REWRITE_TAC[];
        REWRITE_TAC[st_ex_return_def] THEN MESON_TAC[]];
      MESON_TAC[]; MESON_TAC[]; MESON_TAC[]]]);;

let variant_thm = prove
 (`!tms tm defs s.
     ALL (holKernelProof_TERM defs) tms /\ holKernelProof_TERM defs tm /\
     holKernelProof_STATE defs s
     ==> holKernelProof_TERM defs (variant tms tm)`,
  MATCH_MP_TAC variant_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [variant_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(SPEC `v:hol_term` (cases "hol_term")) THEN
  CAKE_REWRITE_TAC[injectivity "hol_term"] THEN REPEAT STRIP_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:mlstring`; `a1:hol_type`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`defs:update list`; `s:hol_refs`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[TERM_Var_SIMP]);;

(* the test of vsubst: state, and when it succeeds *)
let HOLKPAUX_vsubst_test_state = prove
 (`!s p. ?r. (\(t,x). st_ex_bind (holKernel_type_of t) (\ty.
                      st_ex_bind (holKernel_dest_var x) (\vty.
                      st_ex_return (ty = SND vty)))) p s = (r,s)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN REWRITE_TAC[type_of_state] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN CONJ_TAC THENL
   [GEN_TAC THEN QCASES_ON "p2" THEN REWRITE_TAC[holKernel_dest_var_def] THEN
    CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
    MESON_TAC[];
    REWRITE_TAC[st_ex_return_def] THEN MESON_TAC[]]);;

let HOLKPAUX_vsubst_test = prove
 (`!defs s t1 t2.
     holKernelProof_TERM defs t1 /\ holKernelProof_STATE defs s
     ==> (FST ((\(t,x). st_ex_bind (holKernel_type_of t) (\ty.
                        st_ex_bind (holKernel_dest_var x) (\vty.
                        st_ex_return (ty = SND vty)))) (t1,t2) s) = M_success T <=>
          ?n. t2 = hol_Var n (term_type t1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `holKernel_type_of t1 s = (M_success (term_type t1),s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[type_of_thm]; ALL_TAC] THEN
  ASM_REWRITE_TAC[st_ex_bind_def] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "t2" THEN REWRITE_TAC[holKernel_dest_var_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; FST;
                   injectivity "exc"; distinctness "exc"; injectivity "hol_term";
                   distinctness "hol_term"] THEN
  MESON_TAC[]);;

let vsubst_thm = prove
 (`!theta tm s res s' defs.
     ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2) theta /\
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s /\
     holKernel_vsubst theta tm s = (res,s')
     ==> s' = s /\
         !t. res = M_success t
             ==> holKernelProof_TERM defs t /\ t = VSUBST theta tm /\
                 ALL (\(p_1,p_2). ?x ty. p_2 = hol_Var x ty /\ p_1 has_type ty) theta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernel_vsubst_def] THEN
  ASM_CASES_TAC `theta:(hol_term#hol_term)list = []` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; ALL; VSUBST_NIL] THEN
    RW[] THEN GVS[injectivity "exc"];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN BETA_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:hol_refs` HOLKPAUX_vsubst_test_state) THEN
  MP_TAC(SPECL [`defs:update list`; `s:hol_refs`] HOLKPAUX_vsubst_test) THEN
  ABBREV_TAC `f0 = \(t,x). st_ex_bind (holKernel_type_of t) (\ty.
                           st_ex_bind (holKernel_dest_var x) (\vty.
                           st_ex_return (ty = SND vty)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`f0:hol_term#hol_term->hol_refs->(bool,hol_exn)exc#hol_refs`;
                 `s:hol_refs`; `theta:(hol_term#hol_term)list`] forall_thm) THEN
  MP_TAC(ISPEC `holKernel_forall (f0:hol_term#hol_term->hol_refs->(bool,hol_exn)exc#hol_refs)
                  theta s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bool,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs`
    ASSUME_TAC)) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:(bool,hol_exn)exc`; `s1:hol_refs`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "_ = (res,s')" MP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[distinctness "exc"]] THEN
  COND_CASES_TAC THENL [ALL_TAC;
    REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[distinctness "exc"]] THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2 /\
                               term_type t1 = term_type t2 /\ holKernel_is_var t2)
                    (theta:(hol_term#hol_term)list)` ASSUME_TAC THENL
   [QPAT_X_ASSUM "M_success a = M_success T ==> _" MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2)
                     (theta:(hol_term#hol_term)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[term_type_Var; is_var_thm];
    ALL_TAC] THEN
  MP_TAC(SPECL [`holKernel_vsubst_aux theta tm`; `tm:hol_term`;
                `theta:(hol_term#hol_term)list`; `defs:update list`; `s:hol_refs`]
               vsubst_aux_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2 /\
                              term_type t1 = term_type t2 /\ holKernel_is_var t2)
                   (theta:(hol_term#hol_term)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; is_var_thm] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`p1:hol_term`; `p2:hol_term`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `term_type p1 = term_type p2` THEN ASM_REWRITE_TAC[term_type_Var] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[HOLKPAUX_TERM_has_type]);;

let inst_aux_Var = prove
 (`!theta v ty state.
     holKernel_inst_aux [] theta (hol_Var v ty) state =
     (M_success (hol_Var v (holKernel_type_subst theta ty)),state)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [holKernel_inst_aux_def] THEN
  CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[rev_assocd_thm; REV_ASSOCD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[st_ex_return_def]);;

(* HOL4: MEM_subtract (a second copy of holKernel's local lemma) *)
let holKernelProof_MEM_subtract = prove
 (`!xs ys (x:A). MEM x (subtract xs ys) <=> MEM x xs /\ ~MEM x ys`,
  REWRITE_TAC[holKernel_MEM_subtract]);;

let MEM_frees = prove
 (`!tm y defs. holKernelProof_TERM defs tm /\ MEM y (hol_frees tm)
               ==> ?v ty. y = hol_Var v ty /\ holKernelProof_TYPE defs ty`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[hol_frees_def] THEN
  CAKE_REWRITE_TAC[MEM; MEM_union; holKernelProof_MEM_subtract] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[TERM]; ASM_MESON_TAC[TERM]; ASM_MESON_TAC[TERM];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Abs_Var) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[TERM]]);;

let MEM_freesl = prove
 (`!tms y defs. ALL (holKernelProof_TERM defs) tms /\ MEM y (holKernel_freesl tms)
                ==> ?v ty. y = hol_Var v ty /\ holKernelProof_TYPE defs ty`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[holKernel_freesl_def] THEN
  ONCE_REWRITE_TAC[itlist_def] THEN CAKE_REWRITE_TAC[MEM; ALL] THEN
  REWRITE_TAC[o_THM; MEM_union; GSYM holKernel_freesl_def] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[MEM_frees]; ASM_MESON_TAC[]]);;

(* inst_aux on variables and constants, with any environment *)
let HOLKPAUX_inst_aux_Var_gen = prove
 (`!env theta n ty s.
     holKernel_inst_aux env theta (hol_Var n ty) s =
     ((if REV_ASSOCD (hol_Var n (TYPE_SUBST theta ty)) env (hol_Var n ty) = hol_Var n ty
       then M_success (hol_Var n (TYPE_SUBST theta ty))
       else M_failure (holKernel_Clash (hol_Var n (TYPE_SUBST theta ty)))),s)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [holKernel_inst_aux_def] THEN
  CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[rev_assocd_thm; HOLKPAUX_type_subst_TYPE_SUBST] THEN
  SUBGOAL_THEN `(if TYPE_SUBST theta ty = ty then hol_Var n ty
                 else hol_Var n (TYPE_SUBST theta ty)) = hol_Var n (TYPE_SUBST theta ty)`
    SUBST1_TAC THENL [COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[st_ex_return_def; holKernel_raise_Clash_def]);;

let HOLKPAUX_inst_aux_Const = prove
 (`!env theta c ty s.
     holKernel_inst_aux env theta (hol_Const c ty) s =
     (M_success (hol_Const c (TYPE_SUBST theta ty)),s)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [holKernel_inst_aux_def] THEN
  CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[HOLKPAUX_type_subst_TYPE_SUBST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[st_ex_return_def]);;

let inst_aux_thm = prove
 (CASE_TERM
  `!env theta tm s s' res defs.
     ALL (\(t1,t2). holKernelProof_TYPE defs t1 /\ holKernelProof_TYPE defs t2) theta /\
     ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2) env /\
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s /\
     holKernel_inst_aux env theta tm s = (res,s')
     ==> s' = s /\
         (match res with
            M_success t -> INST_CORE env theta tm = hol_Result t
          | M_failure (holKernel_Clash v) -> INST_CORE env theta tm = Clash v
          | _ -> F)`,
  MATCH_MP_TAC holKernel_inst_aux_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
    [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
   QCASES_ON "tm" THENL
    [QPAT_X_ASSUM "holKernel_inst_aux _ _ _ _ = _" MP_TAC THEN
     REWRITE_TAC[HOLKPAUX_inst_aux_Var_gen; PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     COND_CASES_TAC THEN CAKE_REWRITE_TAC[];
     QPAT_X_ASSUM "holKernel_inst_aux _ _ _ _ = _" MP_TAC THEN
     REWRITE_TAC[HOLKPAUX_inst_aux_Const; PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     REWRITE_TAC[INST_CORE_def] THEN CAKE_REWRITE_TAC[];
     SUBGOAL_THEN `holKernelProof_TERM defs a0 /\ holKernelProof_TERM defs a1`
       STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[TERM]; ALL_TAC] THEN
     MP_TAC(ISPEC `holKernel_inst_aux env tyin a0 s` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `r1:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs`
       ASSUME_TAC)) THEN
     MP_TAC(ISPEC `holKernel_inst_aux env tyin a1 s` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `r2:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s2:hol_refs`
       ASSUME_TAC)) THEN
     FIRST_ASSUM(MP_TAC o SPECL [`a1:hol_term`; `a0:hol_term`] o el 3 o CONJUNCTS) THEN
     FIRST_ASSUM(MP_TAC o SPECL [`a0:hol_term`; `a1:hol_term`] o el 2 o CONJUNCTS) THEN
     REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`s:hol_refs`; `s2:hol_refs`; `r2:(hol_term,hol_exn)exc`;
                                `defs:update list`]) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
     DISCH_THEN(MP_TAC o SPECL [`s:hol_refs`; `s1:hol_refs`; `r1:(hol_term,hol_exn)exc`;
                                `defs:update list`]) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
     QPAT_X_ASSUM "holKernel_inst_aux _ _ (hol_Comb _ _) _ = _" MP_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RATOR_CONV) [holKernel_inst_aux_def] THEN
     CAKE_REWRITE_TAC[] THEN REWRITE_TAC[st_ex_bind_def] THEN ASM_REWRITE_TAC[] THEN
     CAKE_REWRITE_TAC[] THEN REWRITE_TAC[INST_CORE_def] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
     QCASES_ON "r1" THEN QCASES_ON "r2" THEN CAKE_REWRITE_TAC[] THENL
      [REPEAT DISCH_TAC THEN FIRST_X_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
       CAKE_REWRITE_TAC[IS_CLASH_def; RESULT_def] THEN
       COND_CASES_TAC THEN REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
       DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CAKE_REWRITE_TAC[] THEN
       ASM_REWRITE_TAC[];
       REPEAT DISCH_TAC THEN FIRST_X_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
       CAKE_REWRITE_TAC[IS_CLASH_def; RESULT_def; PAIR_EQ] THEN
       DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CAKE_REWRITE_TAC[] THEN
       QPAT_X_ASSUM "match a' with holKernel_Failure _ -> F | holKernel_Clash v -> _"
         MP_TAC THEN
       QCASES_ON "a'" THEN CAKE_REWRITE_TAC[IS_CLASH_def] THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IS_CLASH_def];
       DISCH_TAC THEN QCASES_ON "a" THEN CAKE_REWRITE_TAC[] THEN
       DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
       CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IS_CLASH_def];
       DISCH_THEN(K ALL_TAC) THEN QCASES_ON "a" THEN CAKE_REWRITE_TAC[] THEN
       DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
       CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IS_CLASH_def]];
     ((FIRST_ASSUM(X_CHOOSE_THEN `vn:mlstring` (X_CHOOSE_THEN `vty:hol_type` SUBST_ALL_TAC) o
     MATCH_MP Abs_Var) THEN
   SUBGOAL_THEN `holKernelProof_TYPE defs vty /\ holKernelProof_TERM defs a1` STRIP_ASSUME_TAC
     THENL [ASM_MESON_TAC[TERM]; ALL_TAC] THEN
   SUBGOAL_THEN `welltyped a1` ASSUME_TAC THENL
    [ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped]; ALL_TAC] THEN
   ABBREV_TAC `ty1 = TYPE_SUBST tyin vty` THEN
   SUBGOAL_THEN `holKernelProof_TYPE defs ty1` ASSUME_TAC THENL
    [EXPAND_TAC "ty1" THEN REWRITE_TAC[GSYM HOLKPAUX_type_subst_TYPE_SUBST] THEN
     MATCH_MP_TAC(CONJUNCT2(SPEC_ALL holKernelProof_type_subst)) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   QPAT_X_ASSUM "holKernel_inst_aux _ _ (hol_Abs _ _) _ = _" MP_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RATOR_CONV) [holKernel_inst_aux_def] THEN
   CAKE_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[st_ex_bind_def] THEN BETA_TAC THEN
   REWRITE_TAC[inst_aux_Var; HOLKPAUX_type_subst_TYPE_SUBST] THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[st_ex_bind_def] THEN BETA_TAC THEN
   REWRITE_TAC[st_ex_return_def] THEN CAKE_REWRITE_TAC[] THEN
   MP_TAC(ISPEC `holKernel_inst_aux (CONS (hol_Var vn vty,hol_Var vn ty1) env) tyin a1 s`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r2:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s2:hol_refs`
     ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o SPECL [`hol_Var vn vty`;
                               `CONS (hol_Var vn vty,hol_Var vn ty1) env`;
                               `a1:hol_term`] o el 4 o CONJUNCTS) THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`s:hol_refs`; `s2:hol_refs`; `r2:(hol_term,hol_exn)exc`;
                              `defs:update list`]) THEN
   ASM_REWRITE_TAC[ALL] THEN
   ANTS_TAC THENL [ASM_MESON_TAC[TERM_Var]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
   REWRITE_TAC[holKernel_handle_Clash_def; st_ex_bind_def] THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[] THEN REWRITE_TAC[INST_CORE_def; dest_var_def] THEN
   CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
   POP_ASSUM MP_TAC THEN QCASES_ON "r2" THEN CAKE_REWRITE_TAC[] THENL
    [DISCH_TAC THEN COND_CASES_TAC THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def] THEN
     FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[];
     ALL_TAC] THEN
   QCASES_ON "a" THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[holKernel_raise_Clash_def; PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[IS_RESULT_def; CLASH_def];
     ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC) THEN
   (MP_TAC(ISPEC `holKernel_inst_aux [] tyin a1 s` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r3:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s3:hol_refs`
     ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o SPECL [`hol_Var vn vty`; `hol_Var vn ty1`; `hol_Var vn ty1`;
                               `a1:hol_term`] o el 0 o CONJUNCTS) THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`s:hol_refs`; `s3:hol_refs`; `r3:(hol_term,hol_exn)exc`;
                              `defs:update list`]) THEN
   ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
   MP_TAC(SPECL [`tyin:(hol_type#hol_type)list`; `a1:hol_term`] HOLKPAUX_INST_CORE_LEMMA) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `tm1:hol_term` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
   QCASES_ON "r3" THEN CAKE_REWRITE_TAC[] THENL
    [ALL_TAC;
     ASM_REWRITE_TAC[distinctness "hol_result"] THEN TOP_CASE_TAC THEN
     CAKE_REWRITE_TAC[]] THEN
   REWRITE_TAC[injectivity "hol_result"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
   (SUBGOAL_THEN `welltyped tm1` ASSUME_TAC THENL
    [ASM_MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]; ALL_TAC] THEN
   CAKE_ASM_SIMP_TAC[variant_inst_thm] THEN
   ABBREV_TAC `x1 = VARIANT tm1 (explode vn) ty1` THEN
   REWRITE_TAC[holKernel_dest_var_def] THEN CAKE_REWRITE_TAC[st_ex_return_def] THEN
   REWRITE_TAC[RESULT_def; IS_RESULT_def; CLASH_def] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `holKernel_vsubst_aux [hol_Var x1 vty,hol_Var vn vty] a1 =
                 VSUBST [hol_Var x1 vty,hol_Var vn vty] a1 /\
                 holKernelProof_TERM defs (holKernel_vsubst_aux [hol_Var x1 vty,hol_Var vn vty] a1)`
     STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(a /\ b) ==> (b /\ a)`) THEN MATCH_MP_TAC vsubst_aux_thm THEN
     EXISTS_TAC `s:hol_refs` THEN
     ASM_REWRITE_TAC[ALL; term_type_Var; is_var_thm] THEN
     ASM_MESON_TAC[TERM_Var];
     ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM(SUBST_ALL_TAC o SYM) THEN DISCH_TAC) THEN
   (MP_TAC(ISPEC `holKernel_inst_aux (CONS (hol_Var x1 vty,hol_Var x1 ty1) env) tyin
                   (holKernel_vsubst_aux [hol_Var x1 vty,hol_Var vn vty] a1) s`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r4:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s4:hol_refs`
     ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o SPECL [`hol_Var vn ty1`; `hol_Var vn ty1`; `ty1:hol_type`;
                               `x1:mlstring`; `vty:hol_type`; `hol_Var vn vty`;
                               `a1:hol_term`] o el 5 o CONJUNCTS) THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`s:hol_refs`; `s4:hol_refs`; `r4:(hol_term,hol_exn)exc`;
                              `defs:update list`]) THEN
   ASM_REWRITE_TAC[ALL] THEN
   ANTS_TAC THENL [ASM_MESON_TAC[TERM_Var]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
   STRUCT_CASES_TAC(ISPEC `r4:(hol_term,hol_exn)exc` (cases "exc")) THEN
   CAKE_REWRITE_TAC[PAIR_EQ] THENL
    [DISCH_TAC THEN ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CAKE_REWRITE_TAC[];
     TOP_CASE_TAC THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[IS_RESULT_def] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CAKE_REWRITE_TAC[]]))]);;

let inst_lemma = prove
 (`!theta tm s res s' defs.
     ALL (\(t1,t2). holKernelProof_TYPE defs t1 /\ holKernelProof_TYPE defs t2) theta /\
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s /\
     holKernel_inst theta tm s = (res,s')
     ==> s' = s /\ !t. res = M_success t ==> t = INST theta tm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holKernel_inst_def; INST_def] THEN
  ASM_CASES_TAC `theta:(hol_type#hol_type)list = []` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `M_success tm:(hol_term,hol_exn)exc = res` THEN
    UNDISCH_TAC `s:hol_refs = s'` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[injectivity "exc"] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL
     [ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped]; ALL_TAC] THEN
    ASM_SIMP_TAC[HOLKPAUX_INST_CORE_EMPTY; RESULT_def];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `theta:(hol_type#hol_type)list`;
                `tm:hol_term`; `s:hol_refs`; `s':hol_refs`;
                `res:(hol_term,hol_exn)exc`; `defs:update list`] inst_aux_thm) THEN
  ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `res:(hol_term,hol_exn)exc` (cases "exc")) THEN
  CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  SIMP_TAC[RESULT_def]);;

let inst_thm = prove
 (`!theta tm s res s' defs.
     ALL (\(t1,t2). holKernelProof_TYPE defs t1 /\ holKernelProof_TYPE defs t2) theta /\
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s /\
     holKernel_inst theta tm s = (res,s')
     ==> s' = s /\ res = M_success (INST theta tm) /\
         holKernelProof_TERM defs (INST theta tm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`theta:(hol_type#hol_type)list`; `tm:hol_term`; `s:hol_refs`;
                `res:(hol_term,hol_exn)exc`; `s':hol_refs`; `defs:update list`]
               inst_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped]; ALL_TAC] THEN
  MP_TAC(SPECL [`theta:(hol_type#hol_type)list`; `tm:hol_term`] HOLKPAUX_INST_CORE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tm1:hol_term` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `holKernel_inst theta tm s = res,s'` THEN
    REWRITE_TAC[holKernel_inst_def] THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[st_ex_return_def; PAIR_EQ; INST_def; HOLKPAUX_INST_CORE_EMPTY;
                   RESULT_def] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        concl th = `theta:(hol_type#hol_type)list = []`)) THEN
      MP_TAC(SPEC `tm:hol_term` HOLKPAUX_INST_CORE_EMPTY) THEN
      ASM_REWRITE_TAC[injectivity "hol_result"] THEN MESON_TAC[];
      DISCH_TAC THEN
      MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `theta:(hol_type#hol_type)list`;
                    `tm:hol_term`; `s:hol_refs`; `s':hol_refs`;
                    `res:(hol_term,hol_exn)exc`; `defs:update list`] inst_aux_thm) THEN
      ASM_REWRITE_TAC[ALL] THEN
      STRUCT_CASES_TAC(ISPEC `res:(hol_term,hol_exn)exc` (cases "exc")) THEN
      REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[INST_def; RESULT_def; injectivity "hol_result"] THENL
       [MESON_TAC[]; TOP_CASE_TAC THEN CAKE_REWRITE_TAC[distinctness "hol_result"]]];
    REWRITE_TAC[INST_def; holKernelProof_TERM_def] THEN
    MATCH_MP_TAC term_ok_INST_CORE THEN
    ASM_REWRITE_TAC[MEM; IS_RESULT_def] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[holKernelProof_TERM_def]; ALL_TAC] THEN
    UNDISCH_TAC `ALL (\(t1,t2). holKernelProof_TYPE defs t1 /\ holKernelProof_TYPE defs t2)
                     (theta:(hol_type#hol_type)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; holKernelProof_TYPE_def; FST] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; FST] THEN MESON_TAC[]]);;

let freesin_IMP = prove
 (`!rhs vars defs x ty.
     holKernel_freesin vars rhs /\ holKernelProof_TERM defs rhs /\
     VFREE_IN (hol_Var x ty) rhs
     ==> MEM (hol_Var x ty) vars`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_freesin_def] THEN
  CAKE_REWRITE_TAC[VFREE_IN_def; injectivity "hol_term"] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[TERM];
    ASM_MESON_TAC[TERM];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Abs_Var) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (hol_Var s ty') vars`; `defs:update list`;
                                  `x:mlstring`; `ty:hol_type`]) THEN
    ASM_REWRITE_TAC[MEM] THEN ANTS_TAC THENL [ASM_MESON_TAC[TERM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let ALL_DISTINCT_union = prove
 (`!xs (ys:A list). ALL_DISTINCT (hol_union xs ys) <=> ALL_DISTINCT ys`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[hol_union_def] THEN
  ONCE_REWRITE_TAC[itlist_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM hol_union_def; hol_insert_def] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT] THEN
  ASM_MESON_TAC[]);;

let ALL_DISTINCT_tyvars_ALT = prove
 (`!h. ALL_DISTINCT (holKernel_tyvars h)`,
  MATCH_MP_TAC type_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_tyvars_def] THEN CAKE_REWRITE_TAC[ALL_DISTINCT; MEM] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:hol_type list`,`l:hol_type list`) THEN
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[itlist_def] THEN
  CAKE_REWRITE_TAC[MAP; ALL; ALL_DISTINCT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT_union]);;

let ALL_DISTINCT_type_vars_in_term = prove
 (`!P. ALL_DISTINCT (holKernel_type_vars_in_term P)`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_type_vars_in_term_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_union; ALL_DISTINCT_tyvars_ALT]);;

let MEM_type_vars_in_term = prove
 (`!rhs v defs.
     holKernelProof_TERM defs rhs
     ==> (MEM v (holKernel_type_vars_in_term rhs) <=> MEM v (tvars rhs))`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_type_vars_in_term_def] THEN
  CAKE_REWRITE_TAC[tvars_def; tyvars_thm; MEM_union] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; MEM_LIST_UNION; IN_UNION] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THENL
   [SUBGOAL_THEN `holKernelProof_TERM defs a0 /\ holKernelProof_TERM defs a1`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[TERM]; ALL_TAC] THEN ASM_SIMP_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP Abs_Var) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `holKernelProof_TERM defs a1` ASSUME_TAC THENL
      [ASM_MESON_TAC[TERM]; ALL_TAC] THEN ASM_SIMP_TAC[] THEN
    ONCE_REWRITE_TAC[holKernel_type_vars_in_term_def] THEN
    CAKE_REWRITE_TAC[tvars_def; tyvars_thm]]);;

let sort_type_vars_in_term = prove
 (`!P defs.
     holKernelProof_TERM defs P
     ==> sort string_le (MAP explode (holKernel_type_vars_in_term P)) =
         STRING_SORT (MAP explode (tvars P))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transitive string_le /\ antisymmetric string_le /\ total string_le`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[transitive_def; antisymmetric_def; total_def; string_le_def] THEN
    MESON_TAC[string_lt_antisym; string_lt_trans; string_lt_cases];
    ALL_TAC] THEN
  MP_TAC(ISPEC `string_le` SORTED_PERM_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[sort_SORTED];
    MATCH_MP_TAC SORTED_weaken THEN EXISTS_TAC `string_lt` THEN
    REWRITE_TAC[STRING_SORT_SORTED; string_le_def] THEN MESON_TAC[];
    MATCH_MP_TAC PERM_ALL_DISTINCT THEN REWRITE_TAC[ALL_DISTINCT_STRING_SORT] THEN
    CONJ_TAC THENL
     [MESON_TAC[ALL_DISTINCT_PERM; sort_PERM; ALL_DISTINCT_type_vars_in_term;
                ALL_DISTINCT_MAP_explode];
      GEN_TAC THEN
      SUBGOAL_THEN `!x (l:string list). MEM x (STRING_SORT l) <=> MEM x l` (fun th ->
        REWRITE_TAC[th]) THENL
       [REWRITE_TAC[GSYM IN_SET_OF_LIST; MEM_STRING_SORT]; ALL_TAC] THEN
      MP_TAC(ISPECL [`string_le`; `MAP explode (holKernel_type_vars_in_term P)`]
                    sort_PERM) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MEM_PERM th)]) THEN
      REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[MEM_type_vars_in_term]]]);;

(* ------------------------------------------------------------------------- *)
(* Verification of thm functions                                             *)
(* ------------------------------------------------------------------------- *)

(* the theory of a context is ok, and an equation in a context is === *)
let HOLKPAUX_CONTEXT_theory_ok = prove
 (`!defs. holKernelProof_CONTEXT defs
          ==> theory_ok
                ((alist_to_fmap (FLAT (MAP types_of_upd defs)),
                  alist_to_fmap (FLAT (MAP consts_of_upd defs))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd)) defs)))`,
  REWRITE_TAC[holKernelProof_CONTEXT_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
  EXISTS_TAC `init_ctxt` THEN ASM_REWRITE_TAC[init_theory_ok]);;

let HOLKPAUX_EQ_FORM = prove
 (`!defs s ty l r.
     holKernelProof_STATE defs s /\
     holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r)
     ==> hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r = l === r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equation_def; injectivity "hol_term"] THEN
  MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC TERM_Eq_x THEN
  MAP_EVERY EXISTS_TAC [`defs:update list`; `s:hol_refs`] THEN ASM_MESON_TAC[TERM]);;

let dest_thm_thm = prove
 (`!defs th s asl c.
     holKernelProof_THM defs th /\ holKernelProof_STATE defs s /\
     holKernel_dest_thm th = (asl,c)
     ==> ALL (holKernelProof_TERM defs) asl /\ holKernelProof_TERM defs c`,
  GEN_TAC THEN MATCH_MP_TAC thm_INDUCT THEN
  REWRITE_TAC[holKernel_dest_thm_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th))))) THEN
  ASM_MESON_TAC[THM]);;

let hyp_thm = prove
 (`!defs th s asl.
     holKernelProof_THM defs th /\ holKernelProof_STATE defs s /\ holKernel_hyp th = asl
     ==> ALL (holKernelProof_TERM defs) asl`,
  GEN_TAC THEN MATCH_MP_TAC thm_INDUCT THEN
  REWRITE_TAC[holKernel_hyp_def] THEN MESON_TAC[THM]);;

let concl_thm = prove
 (`!defs th s c.
     holKernelProof_THM defs th /\ holKernelProof_STATE defs s /\ holKernel_concl th = c
     ==> holKernelProof_TERM defs c`,
  GEN_TAC THEN MATCH_MP_TAC thm_INDUCT THEN
  REWRITE_TAC[holKernel_concl_def] THEN MESON_TAC[THM]);;

let REFL_thm = prove
 (`!defs tm s res s'.
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s /\
     holKernel_REFL tm s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  UNDISCH_TAC `holKernel_REFL tm s = res,s'` THEN
  REWRITE_TAC[holKernel_REFL_def; st_ex_bind_def] THEN
  MP_TAC(ISPEC `holKernel_safe_mk_eq tm tm s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs`
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`tm:hol_term`; `tm:hol_term`; `s:hol_refs`; `r:(hol_term,hol_exn)exc`;
                `s1:hol_refs`; `defs:update list`] safe_mk_eq_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "exc"; injectivity "exc"]) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:hol_term`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `term_type tm = typeof tm` SUBST1_TAC THENL
   [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  REWRITE_TAC[GSYM equation_def; holKernelProof_THM_def] THEN
  MATCH_MP_TAC proves_REFL THEN
  ASM_SIMP_TAC[HOLKPAUX_CONTEXT_theory_ok; FST] THEN
  ASM_MESON_TAC[holKernelProof_TERM_def]);;

(* the result of safe_mk_eq on terms of the same type *)
let HOLKPAUX_safe_mk_eq_ok = prove
 (`!defs s x y.
     holKernelProof_TERM defs x /\ holKernelProof_TERM defs y /\
     holKernelProof_STATE defs s /\ typeof x = typeof y
     ==> holKernel_safe_mk_eq x y s = (M_success (x === y),s) /\
         holKernelProof_TERM defs (x === y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  MP_TAC(ISPEC `holKernel_safe_mk_eq x y s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_term,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs`
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`x:hol_term`; `y:hol_term`; `s:hol_refs`; `r:(hol_term,hol_exn)exc`;
                `s1:hol_refs`; `defs:update list`] safe_mk_eq_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QCASES_ON "r" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "exc"; injectivity "exc"]) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:hol_term`) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `term_type x = typeof x` SUBST1_TAC THENL
   [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  REWRITE_TAC[GSYM equation_def] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

(* TRANS on two equations *)
let HOLKPAUX_TRANS_ok = prove
 (`!defs s asl1 asl2 ty1 ty2 l m1 m2 r.
     holKernelProof_STATE defs s /\
     holKernelProof_THM defs
       (Sequent asl1 (hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l) m1)) /\
     holKernelProof_THM defs
       (Sequent asl2 (hol_Comb (hol_Comb (hol_Const (implode "=") ty2) m2) r)) /\
     holKernel_aconv m1 m2
     ==> holKernelProof_THM defs
           (Sequent (term_union asl1 asl2)
              (hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l) r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l) m1) /\
    holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty2) m2) r)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holKernelProof_TERM defs (hol_Comb (hol_Const (implode "=") ty1) l) /\
    holKernelProof_TERM defs l /\ holKernelProof_TERM defs m1 /\
    holKernelProof_TERM defs m2 /\ holKernelProof_TERM defs r`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[TERM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l) m1 = l === m1 /\
    hol_Comb (hol_Comb (hol_Const (implode "=") ty2) m2) r = m2 === r /\
    hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l) r = l === r`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC HOLKPAUX_EQ_FORM THEN ASM_MESON_TAC[]) THEN
    REWRITE_TAC[equation_def; injectivity "hol_term"] THEN
    MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC TERM_Eq_x THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l) m1 = l === m1`;
   ASSUME `hol_Comb (hol_Comb (hol_Const (implode "=") ty2) m2) r = m2 === r`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `holKernelProof_THM defs (Sequent asl1 (l === m1))` THEN
  UNDISCH_TAC `holKernelProof_THM defs (Sequent asl2 (m2 === r))` THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] trans_equation) THEN
  MAP_EVERY EXISTS_TAC [`m1:hol_term`; `m2:hol_term`] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[aconv_thm]);;

let TRANS_thm = prove
 (`!defs th1 th2 s res s'.
     holKernelProof_THM defs th1 /\ holKernelProof_THM defs th2 /\
     holKernelProof_STATE defs s /\ holKernel_TRANS th1 th2 s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRUCT_CASES_TAC(SPEC `th2:thm` (cases "thm")) THEN
  REWRITE_TAC[holKernel_TRANS_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN GVS[] THEN
  MATCH_MP_TAC HOLKPAUX_TRANS_ok THEN ASM_MESON_TAC[]);;

(* SYM on an equation *)
let HOLKPAUX_SYM_ok = prove
 (`!defs s asl ty l r.
     holKernelProof_STATE defs s /\
     holKernelProof_THM defs
       (Sequent asl (hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r))
     ==> holKernelProof_THM defs
           (Sequent asl (hol_Comb (hol_Comb (hol_Const (implode "=") ty) r) l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `Tyapp (implode "fun") [typeof l; Tyapp (implode "fun") [typeof l; Tyapp (implode "bool") []]]
    = ty` (SUBST_ALL_TAC o SYM) THENL
   [MATCH_MP_TAC TERM_Eq_x THEN MAP_EVERY EXISTS_TAC [`defs:update list`; `s:hol_refs`] THEN
    ASM_MESON_TAC[THM; TERM];
    ALL_TAC] THEN
  UNDISCH_TAC `holKernelProof_THM defs (Sequent asl
     (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [typeof l; Tyapp (implode "fun") [typeof l;
           Tyapp (implode "bool") []]])) l) r))` THEN
  REWRITE_TAC[holKernelProof_THM_def; hol_sym]);;

let SYM_thm = prove
 (`!th s res s' defs.
     holKernel_SYM th s = (res,s') /\ holKernelProof_THM defs th /\
     holKernelProof_STATE defs s
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
  REWRITE_TAC[holKernel_SYM_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o
         check (fun th -> is_conj (concl th) && is_eq (lhand (concl th))))) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN GVS[] THEN
  MATCH_MP_TAC HOLKPAUX_SYM_ok THEN ASM_MESON_TAC[]);;

let PROVE_HYP_thm = prove
 (`!defs th1 th2 s res s'.
     holKernelProof_THM defs th1 /\ holKernelProof_THM defs th2 /\
     holKernelProof_STATE defs s /\
     holKernel_PROVE_HYP th1 th2 s = (res:(thm,B)exc,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRUCT_CASES_TAC(SPEC `th2:thm` (cases "thm")) THEN
  REWRITE_TAC[holKernel_PROVE_HYP_def; st_ex_return_def; PAIR_EQ;
              holKernelProof_THM_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_comb (lhs (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[holKernelProof_THM_def] THEN
  MATCH_MP_TAC proveHyp THEN ASM_REWRITE_TAC[]);;

let map_type_of = prove
 (`!ls s r s' defs.
     ALL (holKernelProof_TERM defs) ls /\ holKernelProof_STATE defs s /\
     holKernel_map holKernel_type_of ls s = (M_success r,s')
     ==> s' = s /\ r = MAP term_type ls`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_map_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"; MAP; ALL] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernel_type_of h s = (M_success (term_type h),s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[type_of_thm]; ALL_TAC] THEN
  QPAT_X_ASSUM "st_ex_bind _ _ _ = _" MP_TAC THEN
  ASM_REWRITE_TAC[st_ex_bind_def] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `holKernel_map holKernel_type_of t s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(hol_type list,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "r1" THEN CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc";
                                       distinctness "exc"] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_refs`; `a:hol_type list`; `s1:hol_refs`;
                                `defs:update list`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let map_type_of_state = prove
 (`!ls s r s'. holKernel_map holKernel_type_of ls s = (r,s') ==> s' = s`,
  SUBGOAL_THEN `!ls s. ?r. holKernel_map holKernel_type_of ls s = (r,s)` MP_TAC THENL
   [LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_map_def] THEN
    CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN
    REWRITE_TAC[type_of_state] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HOLKPAUX_st_ex_bind_state THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[st_ex_return_def] THEN MESON_TAC[];
    MESON_TAC[PAIR_EQ]]);;

let hypset_ok_list_to_hypset = prove
 (`!ls a. hypset_ok a ==> hypset_ok (holKernel_list_to_hypset ls a)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[holKernel_list_to_hypset_def;
                                    hypset_ok_term_union; hypset_ok_sing]);;
let _ = cake_add_simps [hypset_ok_list_to_hypset];;

let MEM_list_to_hypset_imp = prove
 (`!ls a x. MEM x (holKernel_list_to_hypset ls a) ==> MEM x ls \/ MEM x a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[holKernel_list_to_hypset_def; MEM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_term_union_imp) THEN REWRITE_TAC[MEM] THEN
  MESON_TAC[]);;

let ALPHA_THM_thm = prove
 (`!th h c s res s' defs.
     holKernelProof_THM defs th /\ ALL (holKernelProof_TERM defs) h /\
     holKernelProof_TERM defs c /\ holKernelProof_STATE defs s /\
     holKernel_ALPHA_THM th (h,c) s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
   REWRITE_TAC[holKernel_ALPHA_THM_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THENL [ALL_TAC;
     REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[distinctness "exc"]] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   COND_CASES_TAC THENL [ALL_TAC;
     REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[distinctness "exc"]] THEN
   REWRITE_TAC[st_ex_bind_def] THEN
   MP_TAC(ISPEC `holKernel_map holKernel_type_of (holKernel_list_to_hypset h []) s`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `r1:(hol_type list,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs`
     ASSUME_TAC)) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP map_type_of_state) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   QCASES_ON "r1" THEN CAKE_REWRITE_TAC[PAIR_EQ] THENL [ALL_TAC;
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[distinctness "exc"]] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN
   GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `h' = holKernel_list_to_hypset h []` THEN
   SUBGOAL_THEN `ALL (holKernelProof_TERM defs) h'` ASSUME_TAC THENL
    [EXPAND_TAC "h'" THEN
     UNDISCH_TAC `ALL (holKernelProof_TERM defs) h` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
     MESON_TAC[MEM_list_to_hypset_imp; MEM];
     ALL_TAC] THEN
   SUBGOAL_THEN `a = MAP term_type (h':hol_term list)` SUBST_ALL_TAC THENL
    [ASM_MESON_TAC[map_type_of]; ALL_TAC] THEN
   SUBGOAL_THEN `ALL (holKernelProof_TERM defs) a0 /\ holKernelProof_TERM defs a1`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[THM]; ALL_TAC] THEN
   SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
    [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
   UNDISCH_TAC `holKernelProof_THM defs (Sequent a0 a1)` THEN
   REWRITE_TAC[holKernelProof_THM_def] THEN DISCH_TAC THEN
   MATCH_MP_TAC proves_ACONV THEN
   MAP_EVERY EXISTS_TAC [`a0:hol_term list`; `a1:hol_term`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped];
     ASM_MESON_TAC[aconv_thm];
     EXPAND_TAC "h'" THEN SIMP_TAC[hypset_ok_list_to_hypset; hypset_ok_nil];
     UNDISCH_TAC `ALL (\x. EX (holKernel_aconv x) h') (a0:hol_term list)` THEN
     UNDISCH_TAC `ALL (holKernelProof_TERM defs) a0` THEN
     UNDISCH_TAC `ALL (holKernelProof_TERM defs) h'` THEN
     REWRITE_TAC[GSYM ALL_MEM; EXISTS_MEM] THEN ASM_MESON_TAC[aconv_thm];
     UNDISCH_TAC `ALL (\ty. ty = holKernel_bool_ty) (MAP term_type (h':hol_term list))` THEN
     UNDISCH_TAC `ALL (holKernelProof_TERM defs) h'` THEN
     REWRITE_TAC[GSYM ALL_MEM; ALL_MAP; o_THM; holKernel_bool_ty_def; FST] THEN
     REPEAT STRIP_TAC THENL
      [ASM_MESON_TAC[holKernelProof_TERM_def];
       SUBGOAL_THEN `term_type x = Tyapp (implode "bool") []` (SUBST1_TAC o SYM) THENL
        [ASM_MESON_TAC[]; ASM_MESON_TAC[HOLKPAUX_TERM_has_type]]]]);;

let HOLKPAUX_TERM_EQ = prove
 (`!defs l r. holKernelProof_CONTEXT defs /\ holKernelProof_TERM defs (l === r)
              ==> holKernelProof_TERM defs l /\ holKernelProof_TERM defs r /\
                  typeof l = typeof r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `holKernelProof_TERM defs (l === r)` THEN
  REWRITE_TAC[holKernelProof_TERM_def] THEN
  ASM_SIMP_TAC[MATCH_MP term_ok_clauses
    (MATCH_MP CONTEXT_std_sig (ASSUME `holKernelProof_CONTEXT defs`))]);;

let HOLKPAUX_MK_COMB_ok = prove
 (`!defs s asl1 asl2 ty1 ty2 l1 r1 l2 r2 res s'.
     holKernelProof_STATE defs s /\
     holKernelProof_THM defs
       (Sequent asl1 (hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l1) r1)) /\
     holKernelProof_THM defs
       (Sequent asl2 (hol_Comb (hol_Comb (hol_Const (implode "=") ty2) l2) r2)) /\
     holKernel_MK_COMB
       (Sequent asl1 (hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l1) r1),
        Sequent asl2 (hol_Comb (hol_Comb (hol_Const (implode "=") ty2) l2) r2)) s =
     (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
    [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
   SUBGOAL_THEN
    `holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l1) r1) /\
     holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty2) l2) r2)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[THM]; ALL_TAC] THEN
   SUBGOAL_THEN
    `hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l1) r1 = l1 === r1 /\
     hol_Comb (hol_Comb (hol_Const (implode "=") ty2) l2) r2 = l2 === r2`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC HOLKPAUX_EQ_FORM THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   QPAT_X_ASSUM "holKernel_MK_COMB _ _ = _" MP_TAC THEN
   REWRITE_TAC[holKernel_MK_COMB_def] THEN CAKE_REWRITE_TAC[] THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
     `hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l1) r1 = l1 === r1`;
     ASSUME `hol_Comb (hol_Comb (hol_Const (implode "=") ty2) l2) r2 = l2 === r2`]) THEN
   SUBGOAL_THEN
    `holKernelProof_TERM defs l1 /\ holKernelProof_TERM defs r1 /\ typeof l1 = typeof r1 /\
     holKernelProof_TERM defs l2 /\ holKernelProof_TERM defs r2 /\ typeof l2 = typeof r2`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[HOLKPAUX_TERM_EQ]; ALL_TAC] THEN
   SUBGOAL_THEN `holKernel_type_of r1 s = (M_success (term_type r1),s) /\
                 holKernel_type_of r2 s = (M_success (term_type r2),s)`
     (fun th -> REWRITE_TAC[st_ex_bind_def; th]) THENL
    [CONJ_TAC THEN MATCH_MP_TAC type_of_thm THEN EXISTS_TAC `defs:update list` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `term_type r1 = typeof r1 /\ term_type r2 = typeof r2 /\
                 term_type l1 = typeof l1 /\ term_type l2 = typeof l2` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
  (EVERY_CASE_TAC THEN
   REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
   TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
       REWRITE_TAC[distinctness "exc"] THEN NO_TAC)) THEN
  FIRST [(SUBGOAL_THEN `a0' = typeof r2 /\ y = (s:hol_refs)` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [MP_TAC(SPECL [`r2:hol_term`; `defs:update list`; `s:hol_refs`] type_of_thm) THEN
     ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `holKernelProof_TERM defs (hol_Comb l1 l2) /\
                 holKernelProof_TERM defs (hol_Comb r1 r2) /\
                 typeof (hol_Comb l1 l2) = typeof (hol_Comb r1 r2)` STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[TERM_Comb; typeof_def; codomain_def] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(SPECL [`defs:update list`; `s:hol_refs`; `hol_Comb l1 l2`; `hol_Comb r1 r2`]
                HOLKPAUX_safe_mk_eq_ok) THEN
   ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"] THEN
   STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   ASM_REWRITE_TAC[injectivity "exc"] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC[holKernelProof_THM_def] THEN
   MATCH_MP_TAC proves_MK_COMB THEN
   UNDISCH_TAC `holKernelProof_THM defs (Sequent asl1 (l1 === r1))` THEN
   UNDISCH_TAC `holKernelProof_THM defs (Sequent asl2 (l2 === r2))` THEN
   REWRITE_TAC[holKernelProof_THM_def] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[holKernelProof_TERM_def; term_ok_welltyped]); (DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[distinctness "exc"] THEN
   MP_TAC(SPECL [`r2:hol_term`; `s:hol_refs`] type_of_state) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[])]);;

let MK_COMB_thm = prove
 (`!th1 th2 s res s' defs.
     holKernelProof_THM defs th1 /\ holKernelProof_THM defs th2 /\
     holKernelProof_STATE defs s /\ holKernel_MK_COMB (th1,th2) s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRUCT_CASES_TAC(SPEC `th2:thm` (cases "thm")) THEN
  ASM_CASES_TAC
   `?ty1 l1 r1 ty2 l2 r2.
      a1 = hol_Comb (hol_Comb (hol_Const (implode "=") ty1) l1) r1 /\
      a1' = hol_Comb (hol_Comb (hol_Const (implode "=") ty2) l2) r2` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    MESON_TAC[HOLKPAUX_MK_COMB_ok];
    ALL_TAC] THEN
  REWRITE_TAC[holKernel_MK_COMB_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "exc"] THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let term_type_Const = prove
 (`!n ty. term_type (hol_Const n ty) = ty`,
  ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[]);;

let term_type_Comb_Equal = prove
 (`!ty ty'.
     term_type (hol_Comb (hol_Const (implode "=")
       (Tyapp (implode "fun") [ty; Tyapp (implode "fun") [ty; Tyapp (implode "bool") []]]))
       ty') =
     Tyapp (implode "fun") [ty; Tyapp (implode "bool") []]`,
  ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[term_type_Const]);;

(* ABS on a variable and an equation *)
let HOLKPAUX_ABS_ok = prove
 (`!defs s x ty asl ty0 l r res s'.
     holKernelProof_STATE defs s /\ holKernelProof_TERM defs (hol_Var x ty) /\
     holKernelProof_THM defs
       (Sequent asl (hol_Comb (hol_Comb (hol_Const (implode "=") ty0) l) r)) /\
     holKernel_ABS (hol_Var x ty)
       (Sequent asl (hol_Comb (hol_Comb (hol_Const (implode "=") ty0) l) r)) s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty0) l) r)`
    ASSUME_TAC THENL [ASM_MESON_TAC[THM]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_Comb (hol_Comb (hol_Const (implode "=") ty0) l) r = l === r`
    ASSUME_TAC THENL [MATCH_MP_TAC HOLKPAUX_EQ_FORM THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  QPAT_X_ASSUM "holKernel_ABS _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[holKernel_ABS_def] THEN CAKE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `hol_Comb (hol_Comb (hol_Const (implode "=") ty0) l) r = l === r`]) THEN
  SUBGOAL_THEN `holKernelProof_TERM defs l /\ holKernelProof_TERM defs r /\
                typeof l = typeof r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_TERM_EQ]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[distinctness "exc"];
    ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_TERM defs (hol_Abs (hol_Var x ty) l) /\
                holKernelProof_TERM defs (hol_Abs (hol_Var x ty) r) /\
                typeof (hol_Abs (hol_Var x ty) l) = typeof (hol_Abs (hol_Var x ty) r)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TERM_Abs; typeof_def] THEN ASM_MESON_TAC[TERM]; ALL_TAC] THEN
  MP_TAC(SPECL [`defs:update list`; `s:hol_refs`; `hol_Abs (hol_Var x ty) l`;
                `hol_Abs (hol_Var x ty) r`] HOLKPAUX_safe_mk_eq_ok) THEN
  ASM_REWRITE_TAC[st_ex_bind_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `holKernelProof_THM defs (Sequent asl (l === r))` THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC proves_ABS THEN ASM_REWRITE_TAC[FST] THEN CONJ_TAC THENL
   [UNDISCH_TAC `~EX (vfree_in (hol_Var x ty)) asl` THEN
    REWRITE_TAC[EXISTS_MEM; vfree_in_thm];
    ASM_MESON_TAC[TERM; holKernelProof_TYPE_def]]);;

let ABS_thm = prove
 (`!tm th1 s res s' defs.
     holKernel_ABS tm th1 s = (res,s') /\ holKernelProof_TERM defs tm /\
     holKernelProof_THM defs th1 /\ holKernelProof_STATE defs s
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  ASM_CASES_TAC
   `?x ty ty0 l r. tm = hol_Var x ty /\
                   a1 = hol_Comb (hol_Comb (hol_Const (implode "=") ty0) l) r` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    MESON_TAC[HOLKPAUX_ABS_ok];
    ALL_TAC] THEN
  REWRITE_TAC[holKernel_ABS_def] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "exc"] THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
                                          is_exists (rand (concl th)))) THEN
  ASM_REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[]);;


(* BETA on a beta-redex whose bound variable is a variable *)
let HOLKPAUX_BETA_ok = prove
 (`!defs s x ty bod res s'.
     holKernelProof_STATE defs s /\
     holKernelProof_TERM defs (hol_Comb (hol_Abs (hol_Var x ty) bod) (hol_Var x ty)) /\
     holKernel_BETA (hol_Comb (hol_Abs (hol_Var x ty) bod) (hol_Var x ty)) s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_TERM defs bod /\ holKernelProof_TYPE defs ty`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[TERM; TERM_Abs]; ALL_TAC] THEN
  MP_TAC(SPECL [`defs:update list`; `s:hol_refs`;
                `hol_Comb (hol_Abs (hol_Var x ty) bod) (hol_Var x ty)`; `bod:hol_term`]
         HOLKPAUX_safe_mk_eq_ok) THEN
  ASM_REWRITE_TAC[typeof_def; codomain_def] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "holKernel_BETA _ _ = _" MP_TAC THEN
  REWRITE_TAC[holKernel_BETA_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[st_ex_bind_def] THEN CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_BETA THEN
  ASM_SIMP_TAC[HOLKPAUX_CONTEXT_theory_ok; FST] THEN
  ASM_MESON_TAC[holKernelProof_TERM_def; holKernelProof_TYPE_def]);;

let BETA_thm = prove
 (`!tm s res s' defs.
     holKernel_BETA tm s = (res,s') /\ holKernelProof_TERM defs tm /\
     holKernelProof_STATE defs s
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `?x ty bod. tm = hol_Comb (hol_Abs (hol_Var x ty) bod) (hol_Var x ty)` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    MESON_TAC[HOLKPAUX_BETA_ok];
    ALL_TAC] THEN
  ASM_CASES_TAC `?v bod. tm = hol_Comb (hol_Abs v bod) v` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x ty. v = hol_Var x ty` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[TERM; Abs_Var]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[holKernel_BETA_def] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "exc"] THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
                                          is_exists (rand (concl th)))) THEN
  ASM_REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[]);;


let ASSUME_thm = prove
 (`!tm s res s' defs.
     holKernel_ASSUME tm s = (res,s') /\ holKernelProof_TERM defs tm /\
     holKernelProof_STATE defs s
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  MP_TAC(SPECL [`tm:hol_term`; `defs:update list`; `s:hol_refs`] type_of_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  QPAT_X_ASSUM "holKernel_ASSUME _ _ = _" MP_TAC THEN
  ASM_REWRITE_TAC[holKernel_ASSUME_def; st_ex_bind_def] THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_ASSUME THEN
  ASM_SIMP_TAC[HOLKPAUX_CONTEXT_theory_ok; FST] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_TERM_has_type; holKernel_bool_ty_def];
    ASM_MESON_TAC[holKernelProof_TERM_def]]);;


(* EQ_MP with an explicit equation sequent *)
let HOLKPAUX_EQ_MP_ok = prove
 (`!defs s asl1 asl2 ty l r c res s'.
     holKernelProof_THM defs
       (Sequent asl1 (hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r)) /\
     holKernelProof_THM defs (Sequent asl2 c) /\ holKernelProof_STATE defs s /\
     holKernel_EQ_MP
       (Sequent asl1 (hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r))
       (Sequent asl2 c) s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holKernelProof_TERM defs (hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r) /\
    holKernelProof_TERM defs c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[THM]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r = l === r`
    ASSUME_TAC THENL [MATCH_MP_TAC HOLKPAUX_EQ_FORM THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_TERM defs l /\ holKernelProof_TERM defs r`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[HOLKPAUX_TERM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `holKernel_aconv l c <=> ACONV l c` ASSUME_TAC THENL
   [MATCH_MP_TAC aconv_thm THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  QPAT_X_ASSUM "holKernel_EQ_MP _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[holKernel_EQ_MP_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `holKernelProof_THM defs
       (Sequent asl1 (hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r))` THEN
  UNDISCH_TAC `holKernelProof_THM defs (Sequent asl2 c)` THEN
  ASM_REWRITE_TAC[holKernelProof_THM_def] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC proves_EQ_MP THEN
  MAP_EVERY EXISTS_TAC [`l:hol_term`; `c:hol_term`] THEN ASM_REWRITE_TAC[]);;

let EQ_MP_thm = prove
 (`!th1 th2 s res s' defs.
     holKernelProof_THM defs th1 /\ holKernelProof_THM defs th2 /\
     holKernelProof_STATE defs s /\ holKernel_EQ_MP th1 th2 s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRUCT_CASES_TAC(SPEC `th2:thm` (cases "thm")) THEN
  ASM_CASES_TAC
   `?ty l r. a1 = hol_Comb (hol_Comb (hol_Const (implode "=") ty) l) r` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    MESON_TAC[HOLKPAUX_EQ_MP_ok];
    ALL_TAC] THEN
  REWRITE_TAC[holKernel_EQ_MP_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "exc"] THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
                                          is_exists (rand (concl th)))) THEN
  ASM_REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[]);;

let DEDUCT_ANTISYM_RULE_thm = prove
 (`!th1 th2 s res s' defs.
     holKernelProof_THM defs th1 /\ holKernelProof_THM defs th2 /\
     holKernelProof_STATE defs s /\
     holKernel_DEDUCT_ANTISYM_RULE th1 th2 s = (res,s')
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRUCT_CASES_TAC(SPEC `th2:thm` (cases "thm")) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `holKernelProof_TERM defs a1 /\ holKernelProof_TERM defs a1' /\
                typeof a1 = typeof a1'` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`defs:update list`; `a0:hol_term list`; `a1:hol_term`]
                 THM_term_ok_bool) THEN
    MP_TAC(SPECL [`defs:update list`; `a0':hol_term list`; `a1':hol_term`]
                 THM_term_ok_bool) THEN
    ASM_REWRITE_TAC[ALL; holKernelProof_TERM_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`defs:update list`; `s:hol_refs`; `a1:hol_term`; `a1':hol_term`]
         HOLKPAUX_safe_mk_eq_ok) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "holKernel_DEDUCT_ANTISYM_RULE _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[holKernel_DEDUCT_ANTISYM_RULE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[st_ex_bind_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_THM_def]) THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_DEDUCT_ANTISYM THEN
  ASM_REWRITE_TAC[]);;


let image_lemma = prove
 (`!(f:hol_term->hol_refs->(hol_term,B)exc#hol_refs) l s g defs res s'.
     holKernel_image f l s = (res,s') /\ holKernelProof_STATE defs s
     ==> ALL (\x. !s. holKernelProof_STATE defs s ==> f x s = (M_success (g x),s)) l
     ==> s' = s /\ res = M_success (term_image g l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_image_def] THEN
  CAKE_REWRITE_TAC[ALL] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; term_image_nil] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(f:hol_term->hol_refs->(hol_term,B)exc#hol_refs) h s = (M_success (g h),s)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `holKernel_image (f:hol_term->hol_refs->(hol_term,B)exc#hol_refs) t s`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_term list,B)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_refs`; `g:hol_term->hol_term`; `defs:update list`;
                                `r:(hol_term list,B)exc`; `s1:hol_refs`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  QPAT_X_ASSUM "st_ex_bind _ _ _ = _" MP_TAC THEN
  ASM CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_return_def; PAIR_EQ] THEN
  REWRITE_TAC[CSYNAUX_P3_term_image_cons] THEN MESON_TAC[]);;

let INST_TYPE_thm = prove
 (`!theta th1 s res s' defs.
     ALL (\(t1,t2). holKernelProof_TYPE defs t1 /\ holKernelProof_TYPE defs t2) theta /\
     holKernelProof_THM defs th1 /\ holKernelProof_STATE defs s /\
     holKernel_INST_TYPE theta th1 s = (res,s')
     ==> s' = s /\ ?th. res = M_success th /\ holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL (holKernelProof_TERM defs) a0 /\ holKernelProof_TERM defs a1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x s9. holKernelProof_TERM defs x /\ holKernelProof_STATE defs s9
           ==> holKernel_inst theta x s9 = (M_success (INST theta x),s9)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `holKernel_inst theta x s9` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(hol_term,hol_exn)exc`
      (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
    MP_TAC(SPECL [`theta:(hol_type#hol_type)list`; `x:hol_term`; `s9:hol_refs`;
                  `r:(hol_term,hol_exn)exc`; `s1:hol_refs`; `defs:update list`]
                 inst_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `holKernel_image (holKernel_inst theta) a0 s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_term list,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`holKernel_inst theta`; `a0:hol_term list`; `s:hol_refs`;
                 `INST theta`; `defs:update list`; `r:(hol_term list,hol_exn)exc`;
                 `s1:hol_refs`] image_lemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `ALL (holKernelProof_TERM defs) a0` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `holKernel_inst theta a1 s = (M_success (INST theta a1),s)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  QPAT_X_ASSUM "holKernel_INST_TYPE _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[holKernel_INST_TYPE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_INST_TYPE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_THM_def]) THEN ASM_REWRITE_TAC[FST] THEN
  UNDISCH_TAC
   `ALL (\(t1,t2). holKernelProof_TYPE defs t1 /\ holKernelProof_TYPE defs t2) theta` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; EXISTS_PAIR_THM;
              holKernelProof_TYPE_def] THEN
  MESON_TAC[]);;


let image_lemma = prove
 (`!(f:hol_term->hol_refs->(hol_term,B)exc#hol_refs) l s g defs res s'.
     holKernel_image f l s = (res,s') /\ holKernelProof_STATE defs s
     ==> ALL (\x. !s. holKernelProof_STATE defs s
                      ==> ?r (s':hol_refs). f x s = (r,s) /\
                                            (!t. r = M_success t ==> t = g x)) l
     ==> s' = s /\ !ts. res = M_success ts ==> ts = term_image g l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_image_def] THEN
  CAKE_REWRITE_TAC[ALL] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; term_image_nil] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o CONJUNCT1) THEN
    REWRITE_TAC[injectivity "exc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?r. (f:hol_term->hol_refs->(hol_term,B)exc#hol_refs) h s = (r,s) /\
        (!t. r = M_success t ==> t = g h)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `holKernel_image (f:hol_term->hol_refs->(hol_term,B)exc#hol_refs) t s`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(hol_term list,B)exc`
    (X_CHOOSE_THEN `s2:hol_refs` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_refs`; `g:hol_term->hol_term`; `defs:update list`;
                                `r2:(hol_term list,B)exc`; `s2:hol_refs`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "st_ex_bind _ _ _ = _" MP_TAC THEN
  QCASES_ON "r" THEN QCASES_ON "r2" THEN
  ASM CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_return_def; PAIR_EQ; injectivity "exc";
                       distinctness "exc"] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; distinctness "exc"; FORALL_UNWIND_THM1]) THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"; CSYNAUX_P3_term_image_cons;
                  FORALL_UNWIND_THM1]);;

let INST_thm = prove
 (`!theta th1 s res s' defs.
     holKernel_INST theta th1 s = (res,s') /\
     ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2) theta /\
     holKernelProof_THM defs th1 /\ holKernelProof_STATE defs s
     ==> s' = s /\ !th. res = M_success th ==> holKernelProof_THM defs th`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th1:thm` (cases "thm")) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL (holKernelProof_TERM defs) a0 /\ holKernelProof_TERM defs a1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `holKernel_image (holKernel_vsubst theta) a0 s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_term list,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`holKernel_vsubst theta`; `a0:hol_term list`; `s:hol_refs`;
                 `VSUBST theta`; `defs:update list`; `r:(hol_term list,hol_exn)exc`;
                 `s1:hol_refs`] image_lemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `ALL (holKernelProof_TERM defs) a0` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `holKernel_vsubst theta x s'' ` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r9:(hol_term,hol_exn)exc`
      (X_CHOOSE_THEN `s9:hol_refs` ASSUME_TAC)) THEN
    MP_TAC(SPECL [`theta:(hol_term#hol_term)list`; `x:hol_term`; `s'':hol_refs`;
                  `r9:(hol_term,hol_exn)exc`; `s9:hol_refs`; `defs:update list`]
                 vsubst_thm) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `r9:(hol_term,hol_exn)exc` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC(ISPEC `holKernel_vsubst theta a1 s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(hol_term,hol_exn)exc`
    (X_CHOOSE_THEN `s2:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`theta:(hol_term#hol_term)list`; `a1:hol_term`; `s:hol_refs`;
                `r2:(hol_term,hol_exn)exc`; `s2:hol_refs`; `defs:update list`]
               vsubst_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  QPAT_X_ASSUM "holKernel_INST _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[holKernel_INST_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  QCASES_ON "r" THEN QCASES_ON "r2" THEN
  ASM CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; FORALL_UNWIND_THM1]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_INST THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_THM_def]) THEN ASM_REWRITE_TAC[FST] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MAP_EVERY UNDISCH_TAC
   [`ALL (\(p_1,p_2). ?x ty. p_2 = hol_Var x ty /\ p_1 has_type ty) theta`;
    `ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2) theta`] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; holKernelProof_TERM_def] THEN MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Verification of definition functions                                      *)
(* ------------------------------------------------------------------------- *)

(* TODO move *)
let ALL_DISTINCT_DISJOINT = prove
 (`!(xs:A list) ys.
     ALL_DISTINCT (APPEND xs ys) ==> DISJOINT (set_of_list xs) (set_of_list ys)`,
  SIMP_TAC[ALL_DISTINCT_APPEND']);;

(* the tail of a distinct association list is a submap of the whole list *)
let HOLKPAUX_SUBMAP_APPEND = prove
 (`!(l1:(A#B)list) l2.
     ALL_DISTINCT (MAP FST (APPEND l1 l2))
     ==> alist_to_fmap l2 SUBMAP alist_to_fmap (APPEND l1 l2)`,
  REWRITE_TAC[alist_to_fmap_APPEND; MAP_APPEND] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBMAP_FUNION THEN DISJ2_TAC THEN
  REWRITE_TAC[SUBMAP_REFL; FDOM_alist_to_fmap] THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN MATCH_MP_TAC ALL_DISTINCT_DISJOINT THEN
  ASM_REWRITE_TAC[]);;

let TYPE_CONS_EXTEND = prove
 (`!d defs s ty.
     holKernelProof_STATE (CONS d defs) s /\ holKernelProof_TYPE defs ty
     ==> holKernelProof_TYPE (CONS d defs) ty`,
  REWRITE_TAC[holKernelProof_TYPE_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC type_ok_extend THEN
  EXISTS_TAC `alist_to_fmap (FLAT (MAP types_of_upd defs))` THEN
  ASM_REWRITE_TAC[MAP; FLAT] THEN MATCH_MP_TAC HOLKPAUX_SUBMAP_APPEND THEN
  MP_TAC(SPEC `CONS d defs:update list` CONTEXT_ALL_DISTINCT) THEN
  ASM_MESON_TAC[HOLKPAUX_STATE_CONJ; MAP; FLAT]);;

let TYPE_APPEND_EXTEND = prove
 (`!ds defs s ty.
     holKernelProof_STATE (APPEND ds defs) s /\ holKernelProof_TYPE defs ty
     ==> holKernelProof_TYPE (APPEND ds defs) ty`,
  REWRITE_TAC[holKernelProof_TYPE_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC type_ok_extend THEN
  EXISTS_TAC `alist_to_fmap (FLAT (MAP types_of_upd defs))` THEN
  ASM_REWRITE_TAC[MAP_APPEND; FLAT_APPEND] THEN MATCH_MP_TAC HOLKPAUX_SUBMAP_APPEND THEN
  MP_TAC(SPEC `APPEND ds defs:update list` CONTEXT_ALL_DISTINCT) THEN
  ASM_MESON_TAC[HOLKPAUX_STATE_CONJ; MAP_APPEND; FLAT_APPEND]);;

let TERM_CONS_EXTEND = prove
 (`!d defs s tm.
     holKernelProof_STATE (CONS d defs) s /\ holKernelProof_TERM defs tm
     ==> holKernelProof_TERM (CONS d defs) tm`,
  REWRITE_TAC[holKernelProof_TERM_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC hol_term_ok_extend THEN
  MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd defs))`;
                        `alist_to_fmap (FLAT (MAP consts_of_upd defs))`] THEN
  ASM_REWRITE_TAC[MAP; FLAT] THEN CONJ_TAC THEN
  MATCH_MP_TAC HOLKPAUX_SUBMAP_APPEND THEN
  MP_TAC(SPEC `CONS d defs:update list` CONTEXT_ALL_DISTINCT) THEN
  ASM_MESON_TAC[HOLKPAUX_STATE_CONJ; MAP; FLAT]);;

let TERM_APPEND_EXTEND = prove
 (`!ds defs s tm.
     holKernelProof_STATE (APPEND ds defs) s /\ holKernelProof_TERM defs tm
     ==> holKernelProof_TERM (APPEND ds defs) tm`,
  REWRITE_TAC[holKernelProof_TERM_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC hol_term_ok_extend THEN
  MAP_EVERY EXISTS_TAC [`alist_to_fmap (FLAT (MAP types_of_upd defs))`;
                        `alist_to_fmap (FLAT (MAP consts_of_upd defs))`] THEN
  ASM_REWRITE_TAC[MAP_APPEND; FLAT_APPEND] THEN CONJ_TAC THEN
  MATCH_MP_TAC HOLKPAUX_SUBMAP_APPEND THEN
  MP_TAC(SPEC `APPEND ds defs:update list` CONTEXT_ALL_DISTINCT) THEN
  ASM_MESON_TAC[HOLKPAUX_STATE_CONJ; MAP_APPEND; FLAT_APPEND]);;

(* HOL4 defines STRCAT_SHADOW (nocompute) to keep its simplifier from      *)
(* evaluating string concatenations, and deletes the constant after        *)
(* new_specification_thm; HOL Light needs neither, the definition is kept  *)
(* (STRCAT is APPEND on strings)                                           *)
let STRCAT_SHADOW_def = cake_def
  `STRCAT_SHADOW = (APPEND:string->string->string)`;;

let first_dup_thm = prove
 (`!(ls:A list) acc.
     holKernel_first_dup ls acc = NONE
     ==> ALL_DISTINCT ls /\ (!x. MEM x ls ==> ~MEM x acc)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_first_dup_def] THEN
  CAKE_REWRITE_TAC[ALL_DISTINCT; MEM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let first_dup_SOME = prove
 (`!(ls:A list) acc x.
     holKernel_first_dup ls acc = SOME x ==> ~ALL_DISTINCT (APPEND ls acc)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_first_dup_def] THEN
  CAKE_REWRITE_TAC[distinctness "option"] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[APPEND; ALL_DISTINCT; MEM_APPEND] THEN ASM_MESON_TAC[];
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[APPEND; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM; MEM_APPEND] THEN
    MESON_TAC[]]);;

let add_constants_thm = prove
 (`!ls s (res:(1,hol_exn)exc) s'.
     holKernel_add_constants ls s = (res,s')
     ==> (!u. res = M_success u /\
              ALL_DISTINCT (MAP FST (hol_refs_the_term_constants s))
              ==> ALL_DISTINCT (APPEND (MAP FST ls)
                                       (MAP FST (hol_refs_the_term_constants s))) /\
                  s' = hol_refs_the_term_constants_fupd
                         (combin_K (APPEND ls (hol_refs_the_term_constants s))) s) /\
         (!msg. res = M_failure msg
                ==> s' = s /\
                    ~ALL_DISTINCT (APPEND (MAP FST ls)
                                          (MAP FST (hol_refs_the_term_constants s))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[holKernel_add_constants_def; st_ex_bind_def;
              holKernel_get_the_term_constants_def] THEN
  CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `holKernel_first_dup (MAP FST (ls:(mlstring#hol_type)list))
                  (MAP FST (hol_refs_the_term_constants s))` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; holKernel_set_the_term_constants_def;
                   PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP first_dup_thm) THEN
    REWRITE_TAC[ALL_DISTINCT_APPEND] THEN MESON_TAC[];
    ASM_MESON_TAC[first_dup_SOME]]);;

(* HOL Light's itlist and union of holSyntaxExtra are ITLIST and LIST_UNION *)
let HOLKPAUX_itlist_ITLIST = prove
 (`!(f:A->B->B) l b. itlist f l b = ITLIST f l b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[itlist_def] THEN
  CAKE_REWRITE_TAC[ITLIST] THEN ASM_REWRITE_TAC[]);;

let HOLKPAUX_union_LIST_UNION = prove
 (`!(l1:A list) l2. hol_union l1 l2 = LIST_UNION l1 l2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[hol_union_def; LIST_UNION_def; HOLKPAUX_itlist_ITLIST] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; hol_insert_def; LIST_INSERT_def]);;

(* TODO move *)
let tyvars_EQ_thm = prove
 (`holKernel_tyvars = hol_tyvars`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC holKernel_tyvars_ind THEN
  GEN_TAC THEN DISCH_TAC THEN QCASES_ON "x" THEN
  ONCE_REWRITE_TAC[holKernel_tyvars_def] THEN CAKE_REWRITE_TAC[hol_tyvars_def] THEN
  SUBGOAL_THEN `!a. MEM a a1 ==> holKernel_tyvars a = hol_tyvars a` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`a1:hol_type list`,`l:hol_type list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ITLIST; MEM; HOLKPAUX_itlist_ITLIST; HOLKPAUX_union_LIST_UNION] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[HOLKPAUX_itlist_ITLIST; HOLKPAUX_union_LIST_UNION] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]);;

(* TODO move, unless it already exists elsewhere *)
let LIST_REL_MAP_EQ = prove
 (`!r l (f:A->B). ALL2 (\x y. x = f y) l r ==> MAP f r = l`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL2; MAP; CONS_11] THEN ASM_MESON_TAC[]);;


(* new_specification: the function mapped over the equations (an OCaml     *)
(* term taken from the definition, HOL4's Q.PAT_ABBREV_TAC f)               *)
let HOLKPAUX_new_spec_lambda =
  rand(rator(rand(rator(rhs(concl(SPEC_ALL holKernel_new_specification_def))))));;

(* what it computes for one equation (HOL4: the first part of the map       *)
(* lemma proved inside new_specification_thm)                               *)
let HOLKPAUX_new_spec_f = prove
 (subst
  [HOLKPAUX_new_spec_lambda,
   `f:hol_term->hol_refs->((mlstring#hol_type)#hol_term,hol_exn)exc#hol_refs`]
  `!defs e st res st1.
     (f:hol_term->hol_refs->((mlstring#hol_type)#hol_term,hol_exn)exc#hol_refs) e st =
       (res,st1) /\ holKernelProof_STATE defs st /\
     (\t. holKernelProof_TERM defs t /\ typeof t = Tyapp (implode "bool") []) e
     ==> st1 = st /\
         !x. res = M_success x
             ==> (\e x. ?n ty t. x = ((n,ty),t) /\ e = hol_Var n ty === t /\
                               t has_type ty /\ CLOSED t /\
                               (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))) /\
                               holKernelProof_TERM defs t /\ holKernelProof_TYPE defs ty)
                 e x`,
  REPEAT GEN_TAC THEN BETA_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  REWRITE_TAC[st_ex_bind_def] THEN
  MP_TAC(ISPEC `holKernel_dest_eq e st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(hol_term#hol_term,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`e:hol_term`; `st:hol_refs`; `r1:(hol_term#hol_term,hol_exn)exc`;
                `s1:hol_refs`; `defs:update list`] dest_eq_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "r1" THEN CAKE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[distinctness "exc"]] THEN
  MP_TAC(ISPEC `a:hol_term#hol_term` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:hol_term` (X_CHOOSE_THEN `r:hol_term` SUBST_ALL_TAC)) THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:hol_term`; `r:hol_term`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `e = l === r` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[equation_def]; ALL_TAC] THEN
  QCASES_ON "l" THEN
  REWRITE_TAC[holKernel_dest_var_def] THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "exc"] THEN NO_TAC) THEN
  CAKE_REWRITE_TAC[st_ex_return_def] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`a0:mlstring`; `a1:hol_type`; `r:hol_term`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `typeof r = a1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`defs:update list`; `hol_Var a0 a1`; `r:hol_term`] HOLKPAUX_TERM_EQ) THEN
    ASM_REWRITE_TAC[typeof_def] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_TERM_has_type; term_type];
    REWRITE_TAC[CLOSED_def] THEN ASM_MESON_TAC[freesin_IMP; MEM];
    UNDISCH_TAC `holKernel_subset (holKernel_type_vars_in_term r) (holKernel_tyvars a1)` THEN
    REWRITE_TAC[holKernel_subset_def; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM_type_vars_in_term; tyvars_thm];
    ASM_MESON_TAC[TERM_Var_SIMP]]);;

(* holKernel_map with a function that keeps the state and whose results     *)
(* are related to its arguments                                             *)
let HOLKPAUX_map_REL = prove
 (`!(f:A->hol_refs->(B,C)exc#hol_refs) (P:A->bool) (R:A->B->bool) defs.
     (!e st r st1. f e st = (r,st1) /\ holKernelProof_STATE defs st /\ P e
                   ==> st1 = st /\ !x. r = M_success x ==> R e x)
     ==> !l st res st1.
           holKernel_map f l st = (res,st1) /\ holKernelProof_STATE defs st /\ ALL P l
           ==> st1 = st /\ !xs. res = M_success xs ==> ALL2 R l xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ONCE_REWRITE_TAC[holKernel_map_def] THEN CAKE_REWRITE_TAC[ALL; ALL2] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o CONJUNCT1) THEN
    REWRITE_TAC[injectivity "exc"] THEN MESON_TAC[ALL2];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(f:A->hol_refs->(B,C)exc#hol_refs) h st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(B,C)exc` (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`h:A`; `st:hol_refs`; `r1:(B,C)exc`; `s1:hol_refs`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC(ISPEC `holKernel_map (f:A->hol_refs->(B,C)exc#hol_refs) t st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(B list,C)exc` (X_CHOOSE_THEN `s2:hol_refs` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`st:hol_refs`; `r2:(B list,C)exc`; `s2:hol_refs`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  QPAT_X_ASSUM "st_ex_bind _ _ _ = _" MP_TAC THEN
  QCASES_ON "r1" THEN QCASES_ON "r2" THEN
  ASM CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_return_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"; ALL2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; distinctness "exc"; FORALL_UNWIND_THM1]) THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[ALL2]);;


(* consequences of the relation between the equations and the results of   *)
(* the map (HOL4: the EVERY2 reasoning inside new_specification_thm)        *)
let HOLKPAUX_new_spec_REL = prove
 (`!xs eqs defs.
     ALL2 (\e x. ?n ty t. x = ((n,ty),t) /\ e = hol_Var n ty === t /\
                          t has_type ty /\ CLOSED t /\
                          (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))) /\
                          holKernelProof_TERM defs t /\ holKernelProof_TYPE defs ty)
          eqs xs
     ==> MAP (\(s,t). hol_Var s (typeof t) === t)
             (MAP (\((s,ty),r). (s,r)) xs) = eqs /\
         MAP (\(s,t). (s,typeof t)) (MAP (\((s,ty),r). (s,r)) xs) = MAP FST xs /\
         ALL (\t. CLOSED t /\ (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))))
             (MAP SND (MAP (\((s,ty),r). (s,r)) xs)) /\
         MAP FST (MAP (\((s,ty),r). (s,r)) xs) = MAP FST (MAP FST xs) /\
         MAP (\(s,t). (hol_Const s (typeof t),hol_Var s (typeof t)))
             (MAP (\((s,ty),r). (s,r)) xs) =
         MAP (\(s,ty). (hol_Const s ty,hol_Var s ty)) (MAP FST xs) /\
         ALL (\(s,ty). holKernelProof_TYPE defs ty) (MAP FST xs) /\
         ALL (\((s,ty),r). holKernelProof_TERM defs r /\ r has_type ty) xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MAP; ALL] THEN
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':hol_term list`; `defs:update list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `typeof t'' = ty` ASSUME_TAC THENL
   [ASM_MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;


let HOLKPAUX_new_spec_updates = prove
 (`!defs s eqs p xs.
     holKernelProof_STATE defs s /\ holKernelProof_THM defs (Sequent eqs p) /\
     ALL2 (\e x. ?n ty t. x = ((n,ty),t) /\ e = hol_Var n ty === t /\
                          t has_type ty /\ CLOSED t /\
                          (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))) /\
                          holKernelProof_TERM defs t /\ holKernelProof_TYPE defs ty)
          eqs xs /\
     holKernel_freesin (MAP (UNCURRY hol_Var) (MAP FST xs)) p /\
     ALL_DISTINCT (APPEND (MAP FST (MAP FST xs)) (MAP FST (hol_refs_the_term_constants s)))
     ==> hol_ConstSpec (MAP (\((s,ty),r). (s,r)) xs) p updates defs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_new_spec_REL) THEN
  SUBGOAL_THEN `holKernelProof_TERM defs p` ASSUME_TAC THENL
   [ASM_MESON_TAC[THM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  MATCH_MP_TAC(el 2 (CONJUNCTS updates_rules)) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_THM_def]) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`p:hol_term`;
                  `MAP (UNCURRY hol_Var) (MAP FST (xs:((mlstring#hol_type)#hol_term)list))`;
                  `defs:update list`; `x:mlstring`; `ty:hol_type`] freesin_IMP) THEN
    ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; UNCURRY_DEF; injectivity "hol_term"] THEN
    MESON_TAC[];
    UNDISCH_TAC
     `ALL_DISTINCT (APPEND (MAP FST (MAP FST (xs:((mlstring#hol_type)#hol_term)list)))
                   (MAP FST (hol_refs_the_term_constants s)))` THEN
    ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; FDOM_alist_to_fmap; IN_SET_OF_LIST] THEN
    MESON_TAC[];
    UNDISCH_TAC
     `ALL_DISTINCT (APPEND (MAP FST (MAP FST (xs:((mlstring#hol_type)#hol_term)list)))
                   (MAP FST (hol_refs_the_term_constants s)))` THEN
    REWRITE_TAC[ALL_DISTINCT_APPEND] THEN MESON_TAC[]]);;

let HOLKPAUX_CONTEXT_CONS = prove
 (`!d defs. holKernelProof_CONTEXT defs /\ d updates defs
            ==> holKernelProof_CONTEXT (CONS d defs)`,
  REWRITE_TAC[holKernelProof_CONTEXT_def; extends_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `defs:update list` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `d:update` THEN ASM_REWRITE_TAC[]);;

(* the state after an update that only adds constants *)
let HOLKPAUX_STATE_add_consts = prove
 (`!defs s d.
     holKernelProof_STATE defs s /\ d updates defs /\
     types_of_upd d = [] /\ axexts_of_upd d = []
     ==> holKernelProof_STATE (CONS d defs)
           (hol_refs_the_context_fupd (combin_K (CONS d (hol_refs_the_context s)))
              (hol_refs_the_term_constants_fupd
                 (combin_K (APPEND (consts_of_upd d) (hol_refs_the_term_constants s))) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  SUBGOAL_THEN `hol_refs_the_context s = defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[holKernelProof_STATE_def; hol_refs_INFO.ri_accfupds; K_THM; MAP;
                  FLAT; APPEND] THEN
  MATCH_MP_TAC HOLKPAUX_CONTEXT_CONS THEN ASM_REWRITE_TAC[]);;


(* the substitution built by new_specification *)
let HOLKPAUX_ilist_ok = prove
 (`!defs s (vars:(mlstring#hol_type)list).
     holKernelProof_STATE defs s /\
     ALL (\(n,ty). holKernelProof_TYPE defs ty /\
                   MEM (n,ty) (hol_refs_the_term_constants s)) vars
     ==> ALL (\(t1,t2). holKernelProof_TERM defs t1 /\ holKernelProof_TERM defs t2 /\
                        term_type t1 = term_type t2 /\ holKernel_is_var t2)
             (MAP (\(s,ty). (hol_Const s ty,hol_Var s ty)) vars)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  PAIR_CASES_ON `h:mlstring#hol_type` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[term_type_Const] THEN
  ONCE_REWRITE_TAC[term_type_def] THEN CAKE_REWRITE_TAC[holKernel_is_var_def] THEN
  ASM_MESON_TAC[TERM_Const; TERM_Var]);;

(* the theorem returned by new_specification *)
let HOLKPAUX_new_spec_thm_ok = prove
 (`!defs s4 eqs p xs.
     holKernelProof_STATE (CONS (hol_ConstSpec (MAP (\((s,ty),r). (s,r)) xs) p) defs) s4 /\
     holKernelProof_TERM defs p /\
     ALL2 (\e x. ?n ty t. x = ((n,ty),t) /\ e = hol_Var n ty === t /\
                          t has_type ty /\ CLOSED t /\
                          (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))) /\
                          holKernelProof_TERM defs t /\ holKernelProof_TYPE defs ty)
          eqs xs /\
     (!n ty. MEM (n,ty) (MAP FST xs) ==> MEM (n,ty) (hol_refs_the_term_constants s4))
     ==> holKernelProof_THM (CONS (hol_ConstSpec (MAP (\((s,ty),r). (s,r)) xs) p) defs)
           (Sequent []
              (holKernel_vsubst_aux
                 (MAP (\(s,ty). (hol_Const s ty,hol_Var s ty)) (MAP FST xs)) p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_new_spec_REL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  ABBREV_TAC `d = hol_ConstSpec (MAP (\((s,ty),r). (s,r))
                     (xs:((mlstring#hol_type)#hol_term)list)) p` THEN
  SUBGOAL_THEN
   `ALL (\(t1,t2). holKernelProof_TERM (CONS d defs) t1 /\
                   holKernelProof_TERM (CONS d defs) t2 /\
                   term_type t1 = term_type t2 /\ holKernel_is_var t2)
        (MAP (\(s,ty). (hol_Const s ty,hol_Var s ty))
             (MAP FST (xs:((mlstring#hol_type)#hol_term)list)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_ilist_ok THEN EXISTS_TAC `s4:hol_refs` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\(s,ty). holKernelProof_TYPE defs ty)
                     (MAP FST (xs:((mlstring#hol_type)#hol_term)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[TYPE_CONS_EXTEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_TERM (CONS d defs) p` ASSUME_TAC THENL
   [MATCH_MP_TAC TERM_CONS_EXTEND THEN EXISTS_TAC `s4:hol_refs` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`holKernel_vsubst_aux (MAP (\(s,ty). (hol_Const s ty,hol_Var s ty))
                              (MAP FST (xs:((mlstring#hol_type)#hol_term)list))) p`;
    `p:hol_term`;
    `MAP (\(s,ty). (hol_Const s ty,hol_Var s ty))
         (MAP FST (xs:((mlstring#hol_type)#hol_term)list))`;
    `CONS d defs:update list`; `s4:hol_refs`] vsubst_aux_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_axioms THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOLKPAUX_CONTEXT_theory_ok]; ALL_TAC] THEN
  EXPAND_TAC "d" THEN
  REWRITE_TAC[SND; MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND; axexts_of_upd_def;
              conexts_of_upd_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[MEM]);;


(* new_specification on a theorem, with its result and state (the body of  *)
(* HOL4's new_specification_thm)                                            *)
let HOLKPAUX_new_spec_map_tm =
  rand(rator(rhs(concl(SPEC_ALL holKernel_new_specification_def))));;

let HOLKPAUX_new_spec_ok = prove
 (`!eqs p s (res:(thm,hol_exn)exc) s' defs.
     holKernelProof_THM defs (Sequent eqs p) /\ holKernelProof_STATE defs s /\
     holKernel_new_specification (Sequent eqs p) s = (res,s')
     ==> (!e. res = M_failure e ==> s' = s) /\
         (!th. res = M_success th
               ==> ?d. holKernelProof_THM (CONS d defs) th /\
                       holKernelProof_STATE (CONS d defs) s' /\
                       !th. holKernelProof_THM defs th
                            ==> holKernelProof_THM (CONS d defs) th)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\t. holKernelProof_TERM defs t /\
                         typeof t = Tyapp (implode "bool") []) eqs /\
                holKernelProof_TERM defs p` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`defs:update list`; `eqs:hol_term list`; `p:hol_term`]
                 THM_term_ok_bool) THEN
    ASM_REWRITE_TAC[ALL; holKernelProof_TERM_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC (mk_comb(HOLKPAUX_new_spec_map_tm,`s:hol_refs`)) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(((mlstring#hol_type)#hol_term)list,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`eqs:hol_term list`; `s:hol_refs`;
                `r1:(((mlstring#hol_type)#hol_term)list,hol_exn)exc`; `s1:hol_refs`]
         (MATCH_MP HOLKPAUX_map_REL (SPEC `defs:update list` HOLKPAUX_new_spec_f))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  REWRITE_TAC[holKernel_new_specification_def] THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "r1" THEN CAKE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[distinctness "exc"]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:((mlstring#hol_type)#hol_term)list`) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THENL
   [REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[distinctness "exc"];
    ALL_TAC] THEN
  MP_TAC(ISPEC `holKernel_add_constants
                  (MAP FST (a:((mlstring#hol_type)#hol_term)list)) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:(1,hol_exn)exc` (X_CHOOSE_THEN `s3:hol_refs` ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP add_constants_thm) THEN
  ONCE_REWRITE_TAC[st_ex_ignore_bind_def] THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "r3" THEN CAKE_REWRITE_TAC[] THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[distinctness "exc"] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (hol_refs_the_term_constants s))` ASSUME_TAC THENL
   [ASM_MESON_TAC[STATE_ALL_DISTINCT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a':1`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[st_ex_ignore_bind_def; holKernel_add_def_def; st_ex_bind_def;
              holKernel_get_the_context_def; holKernel_set_the_context_def;
              st_ex_return_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; hol_refs_INFO.ri_accfupds] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (ASSUME_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `hol_ConstSpec (MAP (\((s,ty),r). (s,r))
                (a:((mlstring#hol_type)#hol_term)list)) p` THEN
  SUBGOAL_THEN `hol_ConstSpec (MAP (\((s,ty),r). (s,r))
                  (a:((mlstring#hol_type)#hol_term)list)) p updates defs`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_new_spec_updates THEN
    MAP_EVERY EXISTS_TAC [`s:hol_refs`; `eqs:hol_term list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_new_spec_REL) THEN
  SUBGOAL_THEN `holKernelProof_STATE
                  (CONS (hol_ConstSpec (MAP (\((s,ty),r). (s,r))
                     (a:((mlstring#hol_type)#hol_term)list)) p) defs) s'`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`defs:update list`; `s:hol_refs`;
                  `hol_ConstSpec (MAP (\((s,ty),r). (s,r))
                     (a:((mlstring#hol_type)#hol_term)list)) p`]
                 HOLKPAUX_STATE_add_consts) THEN
    ASM_REWRITE_TAC[types_of_upd_def; axexts_of_upd_def; consts_of_upd_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_new_spec_thm_ok THEN
    MAP_EVERY EXISTS_TAC [`s':hol_refs`; `eqs:hol_term list`] THEN
    ASM_REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM; MEM_APPEND] THEN
    MESON_TAC[];
    GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
    REWRITE_TAC[holKernelProof_THM_def] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP updates_proves)]);;

let new_specification_thm = prove
 (CASE_TERM
  `!th s defs.
     holKernelProof_THM defs th /\ holKernelProof_STATE defs s
     ==> match holKernel_new_specification th s with
           (M_failure exn,s') -> s' = s
         | (M_success th,s') ->
             ?d. holKernelProof_THM (CONS d defs) th /\
                 holKernelProof_STATE (CONS d defs) s' /\
                 !th. holKernelProof_THM defs th
                      ==> holKernelProof_THM (CONS d defs) th`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `holKernel_new_specification (Sequent a0 a1) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:(thm,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`a0:hol_term list`; `a1:hol_term`; `s:hol_refs`;
                `res:(thm,hol_exn)exc`; `s1:hol_refs`; `defs:update list`]
               HOLKPAUX_new_spec_ok) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "res" THEN
  CAKE_REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN MESON_TAC[]);;

(* HOL4: val _ = delete_const "STRCAT_SHADOW" (no counterpart) *)


let new_basic_definition_thm = prove
 (CASE_TERM
  `!tm s defs.
     holKernelProof_TERM defs tm /\ holKernelProof_STATE defs s
     ==> match holKernel_new_basic_definition tm s with
           (M_failure exn,s') -> s' = s
         | (M_success th,s') ->
             ?d. holKernelProof_THM (CONS d defs) th /\
                 holKernelProof_STATE (CONS d defs) s' /\
                 !th. holKernelProof_THM defs th
                      ==> holKernelProof_THM (CONS d defs) th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[holKernel_new_basic_definition_def; st_ex_bind_def] THEN
  MP_TAC(ISPEC `holKernel_ASSUME tm s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(thm,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`tm:hol_term`; `s:hol_refs`; `r:(thm,hol_exn)exc`; `s1:hol_refs`;
                `defs:update list`] ASSUME_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:thm`) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC new_specification_thm THEN ASM_REWRITE_TAC[]);;


(* the existence tests of new_basic_type_definition *)
let HOLKPAUX_can_get_type_arity = prove
 (`!name s.
     ml_monadBase_can holKernel_get_type_arity name s =
     (M_success (?i. MEM (name,i) (hol_refs_the_type_constants s)),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[can_thm] THEN
  MP_TAC(ISPEC `holKernel_get_type_arity name s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(num,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP get_type_arity_thm) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"; PAIR_EQ] THEN
  MESON_TAC[]);;

let HOLKPAUX_can_get_const_type = prove
 (`!name s.
     ml_monadBase_can holKernel_get_const_type name s =
     (M_success (?ty. MEM (name,ty) (hol_refs_the_term_constants s)),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[can_thm] THEN
  MP_TAC(ISPEC `holKernel_get_const_type name s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_type,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP get_const_type_thm) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* the state after an update without axioms, field by field *)
let HOLKPAUX_STATE_upd = prove
 (`!defs s d s'.
     holKernelProof_STATE defs s /\ d updates defs /\ axexts_of_upd d = [] /\
     hol_refs_the_context s' = CONS d defs /\
     hol_refs_the_type_constants s' =
       APPEND (types_of_upd d) (hol_refs_the_type_constants s) /\
     hol_refs_the_term_constants s' =
       APPEND (consts_of_upd d) (hol_refs_the_term_constants s) /\
     hol_refs_the_axioms s' = hol_refs_the_axioms s
     ==> holKernelProof_STATE (CONS d defs) s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  ASM_REWRITE_TAC[holKernelProof_STATE_def; MAP; FLAT; APPEND] THEN
  MATCH_MP_TAC HOLKPAUX_CONTEXT_CONS THEN ASM_REWRITE_TAC[]);;


(* the steps of new_basic_type_definition after its tests *)
let HOLKPAUX_add_type_ok = prove
 (`!name arity s.
     ~(?i. MEM (name,i) (hol_refs_the_type_constants s))
     ==> holKernel_add_type (name,arity) s =
         (M_success one,
          hol_refs_the_type_constants_fupd
            (combin_K (CONS (name,arity) (hol_refs_the_type_constants s))) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[holKernel_add_type_def; st_ex_bind_def; HOLKPAUX_can_get_type_arity] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[st_ex_bind_def; holKernel_get_the_type_constants_def;
              holKernel_set_the_type_constants_def] THEN
  CAKE_REWRITE_TAC[]);;

let HOLKPAUX_mk_type_new = prove
 (`!name args s l.
     hol_refs_the_type_constants s = CONS (name,LENGTH args) l
     ==> holKernel_mk_type (name,args) s = (M_success (Tyapp name args),s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[holKernel_mk_type_def; holKernel_try_def; otherwise_def; st_ex_bind_def;
              holKernel_get_type_arity_def; holKernel_get_the_type_constants_def] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[holKernel_assoc_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def]);;

let HOLKPAUX_add_constants_ok = prove
 (`!ls s.
     ALL_DISTINCT (APPEND (MAP FST ls) (MAP FST (hol_refs_the_term_constants s)))
     ==> holKernel_add_constants ls s =
         (M_success one,
          hol_refs_the_term_constants_fupd
            (combin_K (APPEND ls (hol_refs_the_term_constants s))) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (hol_refs_the_term_constants s))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL_DISTINCT (APPEND (MAP FST (ls:(mlstring#hol_type)list))
                   (MAP FST (hol_refs_the_term_constants s)))` THEN
    SIMP_TAC[ALL_DISTINCT_APPEND];
    ALL_TAC] THEN
  MP_TAC(ISPEC `holKernel_add_constants ls s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(1,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP add_constants_thm) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "r" THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"; PAIR_EQ] THEN
  ASM_MESON_TAC[one]);;

let HOLKPAUX_add_def_ok = prove
 (`!d s. (holKernel_add_def d s:(1,C)exc#hol_refs) =
         (M_success one,
          hol_refs_the_context_fupd (combin_K (CONS d (hol_refs_the_context s))) s)`,
  REWRITE_TAC[holKernel_add_def_def; st_ex_bind_def; holKernel_get_the_context_def;
              holKernel_set_the_context_def] THEN
  CAKE_REWRITE_TAC[]);;

let HOLKPAUX_mk_const_ok = prove
 (`!name ty s.
     holKernel_get_const_type name s = (M_success ty,s)
     ==> holKernel_mk_const (name,[]) s = (M_success (hol_Const name ty),s)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[holKernel_mk_const_def; holKernel_try_def; otherwise_def;
                  st_ex_bind_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def; type_subst_EMPTY]);;

let HOLKPAUX_get_const_type_CONS = prove
 (`!name s n ty l.
     hol_refs_the_term_constants s = CONS (n,ty) l
     ==> holKernel_get_const_type name s =
         if name = n then (M_success ty,s)
         else holKernel_assoc name l s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[holKernel_get_const_type_def; st_ex_bind_def;
              holKernel_get_the_term_constants_def] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [holKernel_assoc_def] THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[st_ex_return_def]);;

let HOLKPAUX_mk_comb_ok = prove
 (`!defs s f a ty.
     holKernelProof_TERM defs f /\ holKernelProof_TERM defs a /\
     holKernelProof_STATE defs s /\
     term_type f = Tyapp (implode "fun") [term_type a; ty]
     ==> holKernel_mk_comb (f,a) s = (M_success (hol_Comb f a),s) /\
         holKernelProof_TERM defs (hol_Comb f a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `holKernel_mk_comb (f,a) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(hol_term,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`s1:hol_refs`; `s:hol_refs`; `r:(hol_term,hol_exn)exc`; `defs:update list`;
                `f:hol_term`; `a:hol_term`] mk_comb_thm) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "r" THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"; FORALL_UNWIND_THM1] THEN
  ASM_MESON_TAC[]);;


let HOLKPAUX_try_dest_comb = prove
 (`!f x msg s.
     holKernel_try holKernel_dest_comb (hol_Comb f x) msg s = (M_success (f,x),s)`,
  REWRITE_TAC[holKernel_try_def; otherwise_def; holKernel_dest_comb_def] THEN
  CAKE_REWRITE_TAC[st_ex_return_def]);;

(* closes a goal  raise_Failure msg s = (res,s') ==> P  where P holds for *)
(* failures that keep the state                                           *)
let HOLKPAUX_FAIL_CLOSER =
  REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"];;


let HOLKPAUX_term_type_Comb = prove
 (`!f a x y. term_type f = Tyapp (implode "fun") [x; y] ==> term_type (hol_Comb f a) = y`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [term_type_def] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;


(* new_basic_type_definition on a theorem, with its result and state (the  *)
(* body of HOL4's new_basic_type_definition_thm)                            *)
let HOLKPAUX_nbtd_ok = prove
 (`!tyname absname repname asl c s (res:(thm#thm,hol_exn)exc) s' defs.
     holKernelProof_THM defs (Sequent asl c) /\ holKernelProof_STATE defs s /\
     holKernel_new_basic_type_definition (tyname,absname,repname,Sequent asl c) s = (res,s')
     ==> (!e. res = M_failure e ==> s' = s) /\
         (!th1 th2. res = M_success (th1,th2)
            ==> ?ds. holKernelProof_THM (APPEND ds defs) th1 /\
                     holKernelProof_THM (APPEND ds defs) th2 /\
                     holKernelProof_STATE (APPEND ds defs) s' /\
                     !th. holKernelProof_THM defs th
                          ==> holKernelProof_THM (APPEND ds defs) th)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[holKernel_new_basic_type_definition_def] THEN CAKE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN
  REWRITE_TAC[HOLKPAUX_can_get_type_arity] THEN CAKE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN
  REWRITE_TAC[HOLKPAUX_can_get_const_type] THEN CAKE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN
  REWRITE_TAC[HOLKPAUX_can_get_const_type] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [HOLKPAUX_FAIL_CLOSER; ALL_TAC] THEN
  COND_CASES_TAC THENL [HOLKPAUX_FAIL_CLOSER; ALL_TAC] THEN
  COND_CASES_TAC THENL [HOLKPAUX_FAIL_CLOSER; ALL_TAC] THEN
  COND_CASES_TAC THENL [HOLKPAUX_FAIL_CLOSER; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN
  QCASES_ON "c" THEN REWRITE_TAC[HOLKPAUX_try_dest_comb] THEN
  TRY(REWRITE_TAC[holKernel_try_def; otherwise_def; holKernel_dest_comb_def] THEN
      CAKE_REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "exc"] THEN NO_TAC) THEN
  CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [HOLKPAUX_FAIL_CLOSER; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; holKernel_mk_fun_ty_def; holKernel_mk_var_def] THEN
  BETA_TAC THEN
  ABBREV_TAC `tyvars = MAP Tyvar (MAP implode (sort string_le
                 (MAP explode (holKernel_type_vars_in_term a0))))` THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holKernelProof_TERM defs a0 /\ holKernelProof_TERM defs a1 /\
    term_type a0 = Tyapp (implode "fun") [term_type a1; Tyapp (implode "bool") []]`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`defs:update list`; `[]:hol_term list`; `hol_Comb a0 a1`]
                 THM_term_ok_bool) THEN
    ASM_REWRITE_TAC[ALL; GSYM holKernelProof_TERM_def] THEN
    ASM_SIMP_TAC[TERM_Comb] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `typeof a0 = term_type a0` ASSUME_TAC THENL
     [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
    UNDISCH_TAC `typeof (hol_Comb a0 a1) = Tyapp (implode "bool") []` THEN
    ASM_REWRITE_TAC[typeof_def; codomain_def] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars a0)))) = tyvars`
    ASSUME_TAC THENL
   [EXPAND_TAC "tyvars" THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC sort_type_vars_in_term THEN EXISTS_TAC `defs:update list` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holKernel_type_of a1 s = (M_success (term_type a1),s)` ASSUME_TAC THENL
   [MATCH_MP_TAC type_of_thm THEN EXISTS_TAC `defs:update list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tyname:mlstring`; `LENGTH (tyvars:hol_type list)`; `s:hol_refs`]
               HOLKPAUX_add_type_ok) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `s1 = hol_refs_the_type_constants_fupd
                     (combin_K (CONS (tyname,LENGTH (tyvars:hol_type list))
                              (hol_refs_the_type_constants s))) s` THEN
  SUBGOAL_THEN `holKernel_mk_type (tyname,tyvars) s1 = (M_success (Tyapp tyname tyvars),s1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_mk_type_new THEN
    EXISTS_TAC `hol_refs_the_type_constants s` THEN EXPAND_TAC "s1" THEN
    REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hol_refs_the_term_constants s1 = hol_refs_the_term_constants s /\
    hol_refs_the_context s1 = hol_refs_the_context s /\
    hol_refs_the_axioms s1 = hol_refs_the_axioms s /\
    hol_refs_the_type_constants s1 =
      CONS (tyname,LENGTH (tyvars:hol_type list)) (hol_refs_the_type_constants s)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`[(absname:mlstring,Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars]);
      (repname:mlstring,Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])]`;
    `s1:hol_refs`] HOLKPAUX_add_constants_ok) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MAP; APPEND; ALL_DISTINCT; MEM] THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    ASM_MESON_TAC[STATE_ALL_DISTINCT];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `s3 = hol_refs_the_term_constants_fupd
           (combin_K (APPEND [(absname:mlstring,
                        Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars]);
                       (repname:mlstring,
                        Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])]
                      (hol_refs_the_term_constants s1))) s1` THEN
  MP_TAC(ISPECL [`hol_TypeDefn tyname a0 absname repname`; `s3:hol_refs`]
                (INST_TYPE [`:hol_exn`,`:C`] HOLKPAUX_add_def_ok)) THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `s2 = hol_refs_the_context_fupd
           (combin_K (CONS (hol_TypeDefn tyname a0 absname repname) (hol_refs_the_context s3))) s3` THEN
  SUBGOAL_THEN `hol_refs_the_context s = defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GSYM o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  SUBGOAL_THEN `hol_TypeDefn tyname a0 absname repname updates defs` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 4 (CONJUNCTS updates_rules)) THEN EXISTS_TAC `a1:hol_term` THEN
    UNDISCH_TAC `holKernelProof_THM defs (Sequent [] (hol_Comb a0 a1))` THEN
    REWRITE_TAC[holKernelProof_THM_def] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[FDOM_alist_to_fmap; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    REWRITE_TAC[CLOSED_def] THEN ASM_MESON_TAC[freesin_IMP; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `typeof a0 = Tyapp (implode "fun") [term_type a1; Tyapp (implode "bool") []]`
    ASSUME_TAC THENL [ASM_MESON_TAC[term_type]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (tvars a0) = LENGTH (tyvars:hol_type list)` ASSUME_TAC THENL
   [UNDISCH_TAC `MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars a0)))) = tyvars` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `ALL_DISTINCT (MAP explode (tvars a0))` ASSUME_TAC THENL
     [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN SIMP_TAC[explode_11; tvars_ALL_DISTINCT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_MAP; LENGTH_STRING_SORT];
    ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_STATE (CONS (hol_TypeDefn tyname a0 absname repname) defs) s2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_STATE_upd THEN EXISTS_TAC `s:hol_refs` THEN
    ASM_REWRITE_TAC[axexts_of_upd_def; types_of_upd_def; consts_of_upd_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[hol_domain_def] THEN
    MAP_EVERY EXPAND_TAC ["s2"; "s3"] THEN
    ASM_REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM; APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hol_refs_the_term_constants s2 =
      CONS (absname,Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars])
     (CONS (repname,Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])
           (hol_refs_the_term_constants s)) /\
    hol_refs_the_type_constants s2 =
      CONS (tyname,LENGTH (tyvars:hol_type list)) (hol_refs_the_type_constants s)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s2"; "s3"] THEN
    ASM_REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM; APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(repname:mlstring = absname)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holKernel_mk_const (repname,[]) s2 =
      (M_success (hol_Const repname
                    (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])),s2) /\
    holKernel_mk_const (absname,[]) s2 =
      (M_success (hol_Const absname
                    (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars])),s2)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HOLKPAUX_mk_const_ok THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HOLKPAUX_get_const_type_CONS th]) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[holKernel_assoc_def] THEN
    CAKE_REWRITE_TAC[st_ex_return_def];
    ALL_TAC] THEN
  ABBREV_TAC `ctx = CONS (hol_TypeDefn tyname a0 absname repname) defs` THEN
  SUBGOAL_THEN `holKernelProof_TYPE ctx (Tyapp tyname tyvars) /\
                holKernelProof_TYPE ctx (term_type a1) /\
                holKernelProof_TERM ctx a0`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TYPE_Tyapp THEN EXISTS_TAC `s2:hol_refs` THEN
      ASM_REWRITE_TAC[MEM] THEN
      UNDISCH_TAC `MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars a0)))) = tyvars` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
      ASM_MESON_TAC[TYPE];
      EXPAND_TAC "ctx" THEN MATCH_MP_TAC TYPE_CONS_EXTEND THEN
      EXISTS_TAC `s2:hol_refs` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[term_type];
      EXPAND_TAC "ctx" THEN MATCH_MP_TAC TERM_CONS_EXTEND THEN
      EXISTS_TAC `s2:hol_refs` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `holKernelProof_TERM ctx
      (hol_Const repname (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])) /\
    holKernelProof_TERM ctx
      (hol_Const absname (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars])) /\
    holKernelProof_TERM ctx (hol_Var (implode "a") (Tyapp tyname tyvars)) /\
    holKernelProof_TERM ctx (hol_Var (implode "r") (term_type a1))`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TERM_Const THEN EXISTS_TAC `s2:hol_refs` THEN ASM_REWRITE_TAC[MEM];
      MATCH_MP_TAC TERM_Const THEN EXISTS_TAC `s2:hol_refs` THEN ASM_REWRITE_TAC[MEM];
      MATCH_MP_TAC TERM_Var THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TERM_Var THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
                `hol_Const repname
                   (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])`;
                `hol_Var (implode "a") (Tyapp tyname tyvars)`; `term_type a1`]
               HOLKPAUX_mk_comb_ok) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[term_type_Const; term_type_Var]; STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
                `hol_Const absname
                   (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars])`;
                `hol_Var (implode "r") (term_type a1)`; `Tyapp tyname tyvars`]
               HOLKPAUX_mk_comb_ok) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[term_type_Const; term_type_Var]; STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
                `hol_Const absname
                   (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars])`;
                `hol_Comb (hol_Const repname
                   (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1]))
                   (hol_Var (implode "a") (Tyapp tyname tyvars))`; `Tyapp tyname tyvars`]
               HOLKPAUX_mk_comb_ok) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[term_type_Const] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HOLKPAUX_term_type_Comb THEN
    EXISTS_TAC `Tyapp tyname tyvars` THEN REWRITE_TAC[term_type_Const];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
                `hol_Const repname
                   (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1])`;
                `hol_Comb (hol_Const absname
                   (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars]))
                   (hol_Var (implode "r") (term_type a1))`; `term_type a1`]
               HOLKPAUX_mk_comb_ok) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[term_type_Const] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HOLKPAUX_term_type_Comb THEN
    EXISTS_TAC `term_type a1` THEN REWRITE_TAC[term_type_Const];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`; `a0:hol_term`;
                `hol_Var (implode "r") (term_type a1)`; `Tyapp (implode "bool") []`]
               HOLKPAUX_mk_comb_ok) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[term_type_Var]; STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
     `hol_Comb (hol_Const absname (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars]))
        (hol_Comb (hol_Const repname
                     (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1]))
           (hol_Var (implode "a") (Tyapp tyname tyvars)))`;
     `hol_Var (implode "a") (Tyapp tyname tyvars)`] HOLKPAUX_safe_mk_eq_ok) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[typeof_def; codomain_def]; STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
     `hol_Comb (hol_Const repname (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1]))
        (hol_Comb (hol_Const absname
                     (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars]))
           (hol_Var (implode "r") (term_type a1)))`;
     `hol_Var (implode "r") (term_type a1)`] HOLKPAUX_safe_mk_eq_ok) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[typeof_def; codomain_def]; STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx:update list`; `s2:hol_refs`;
     `hol_Comb a0 (hol_Var (implode "r") (term_type a1))`;
     `hol_Comb (hol_Const repname (Tyapp (implode "fun") [Tyapp tyname tyvars; term_type a1]))
        (hol_Comb (hol_Const absname
                     (Tyapp (implode "fun") [term_type a1; Tyapp tyname tyvars]))
           (hol_Var (implode "r") (term_type a1))) ===
      hol_Var (implode "r") (term_type a1)`] HOLKPAUX_safe_mk_eq_ok) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[typeof_def; codomain_def; CSYNAUX_typeof_equation];
                  STRIP_TAC] THEN
  ASM CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  EXISTS_TAC `[hol_TypeDefn tyname a0 absname repname]` THEN
  ASM_REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT ctx` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOLKPAUX_STATE_CONJ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_axioms THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOLKPAUX_CONTEXT_theory_ok]; ALL_TAC] THEN
    EXPAND_TAC "ctx" THEN
    REWRITE_TAC[SND; MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND; axexts_of_upd_def;
                conexts_of_upd_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[hol_domain_def; MEM];
    REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_axioms THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOLKPAUX_CONTEXT_theory_ok]; ALL_TAC] THEN
    EXPAND_TAC "ctx" THEN
    REWRITE_TAC[SND; MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND; axexts_of_upd_def;
                conexts_of_upd_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[hol_domain_def; MEM];
    GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
    REWRITE_TAC[holKernelProof_THM_def] THEN EXPAND_TAC "ctx" THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP updates_proves)]);;

let new_basic_type_definition_thm = prove
 (CASE_TERM
  `!tyname absname repname th s defs.
     holKernelProof_THM defs th /\ holKernelProof_STATE defs s
     ==> match holKernel_new_basic_type_definition (tyname,absname,repname,th) s with
           (M_failure exn,s') -> s' = s
         | (M_success (th1,th2),s') ->
             ?ds. holKernelProof_THM (APPEND ds defs) th1 /\
                  holKernelProof_THM (APPEND ds defs) th2 /\
                  holKernelProof_STATE (APPEND ds defs) s' /\
                  !th. holKernelProof_THM defs th
                       ==> holKernelProof_THM (APPEND ds defs) th`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `holKernel_new_basic_type_definition (tyname,absname,repname,Sequent a0 a1) s`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:(thm#thm,hol_exn)exc`
    (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`tyname:mlstring`; `absname:mlstring`; `repname:mlstring`;
                `a0:hol_term list`; `a1:hol_term`; `s:hol_refs`;
                `res:(thm#thm,hol_exn)exc`; `s1:hol_refs`; `defs:update list`]
               HOLKPAUX_nbtd_ok) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "res" THEN
  CAKE_REWRITE_TAC[distinctness "exc"; injectivity "exc"] THENL
   [MP_TAC(ISPEC `a:thm#thm` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:thm` (X_CHOOSE_THEN `t2:thm` SUBST_ALL_TAC)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Verification of context extension functions                               *)
(* ------------------------------------------------------------------------- *)

let new_type_thm = prove
 (CASE_TERM
  `!name arity s defs.
     holKernelProof_STATE defs s
     ==> match holKernel_new_type (name,arity) s with
           (M_failure exn,s') -> s' = s
         | (M_success u,s') ->
             ?d. holKernelProof_STATE (CONS d defs) s' /\
                 !th. holKernelProof_THM defs th ==> holKernelProof_THM (CONS d defs) th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hol_refs_the_context s = defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  REWRITE_TAC[holKernel_new_type_def; st_ex_ignore_bind_def] THEN
  ASM_CASES_TAC `?i. MEM (name,i) (hol_refs_the_type_constants s)` THENL
   [REWRITE_TAC[holKernel_add_type_def; st_ex_bind_def; HOLKPAUX_can_get_type_arity] THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[holKernel_raise_Failure_def] THEN
    CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HOLKPAUX_add_type_ok] THEN CAKE_REWRITE_TAC[HOLKPAUX_add_def_ok] THEN
  EXISTS_TAC `hol_NewType name arity` THEN
  SUBGOAL_THEN `hol_NewType name arity updates defs` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 3 (CONJUNCTS updates_rules)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GSYM o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
    ASM_REWRITE_TAC[FDOM_alist_to_fmap; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_STATE_upd THEN EXISTS_TAC `s:hol_refs` THEN
    ASM_REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM; axexts_of_upd_def;
                    types_of_upd_def; consts_of_upd_def; APPEND];
    GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
    REWRITE_TAC[holKernelProof_THM_def] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP updates_proves)]);;

let new_constant_thm = prove
 (CASE_TERM
  `!name ty s defs.
     holKernelProof_STATE defs s /\ holKernelProof_TYPE defs ty
     ==> match holKernel_new_constant (name,ty) s with
           (M_failure exn,s') -> s' = s
         | (M_success u,s') ->
             ?d. holKernelProof_STATE (CONS d defs) s' /\
                 !th. holKernelProof_THM defs th ==> holKernelProof_THM (CONS d defs) th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hol_refs_the_context s = defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STATE_ALL_DISTINCT) THEN
  REWRITE_TAC[holKernel_new_constant_def; st_ex_ignore_bind_def] THEN
  MP_TAC(ISPEC `holKernel_add_constants [(name,ty)] s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(1,hol_exn)exc` (X_CHOOSE_THEN `s1:hol_refs` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP add_constants_thm) THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN
  REWRITE_TAC[injectivity "exc"; distinctness "exc"; FORALL_UNWIND_THM1] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[HOLKPAUX_add_def_ok] THEN
  EXISTS_TAC `hol_NewConst name ty` THEN
  SUBGOAL_THEN `hol_NewConst name ty updates defs` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 1 (CONJUNCTS updates_rules)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GSYM o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_TYPE_def]) THEN
    ASM_REWRITE_TAC[FDOM_alist_to_fmap; IN_SET_OF_LIST] THEN
    UNDISCH_TAC `ALL_DISTINCT (APPEND (MAP FST [name:mlstring,ty:hol_type])
                   (MAP FST (hol_refs_the_term_constants s)))` THEN
    REWRITE_TAC[MAP; APPEND; ALL_DISTINCT; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_STATE_upd THEN EXISTS_TAC `s:hol_refs` THEN
    ASM_REWRITE_TAC[hol_refs_INFO.ri_accfupds; K_THM; axexts_of_upd_def;
                    types_of_upd_def; consts_of_upd_def; APPEND];
    GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
    REWRITE_TAC[holKernelProof_THM_def] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP updates_proves)]);;


let new_axiom_thm = prove
 (CASE_TERM
  `!p s defs.
     holKernelProof_STATE defs s /\ holKernelProof_TERM defs p
     ==> match holKernel_new_axiom p s with
           (M_failure exn,s') -> s' = s
         | (M_success th,s') ->
             ?d. holKernelProof_THM (CONS d defs) th /\
                 holKernelProof_STATE (CONS d defs) s' /\
                 !th. holKernelProof_THM defs th ==> holKernelProof_THM (CONS d defs) th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hol_refs_the_context s = defs` ASSUME_TAC THENL
   [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOLKPAUX_STATE_CONJ) THEN
  MP_TAC(SPECL [`p:hol_term`; `defs:update list`; `s:hol_refs`] type_of_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[holKernel_new_axiom_def] THEN
  ONCE_REWRITE_TAC[st_ex_bind_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[holKernel_raise_Failure_def] THEN CAKE_REWRITE_TAC[]] THEN
  CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def;
                   holKernel_get_the_axioms_def; holKernel_set_the_axioms_def;
                   HOLKPAUX_add_def_ok] THEN
  EXISTS_TAC `hol_NewAxiom p` THEN
  SUBGOAL_THEN `hol_NewAxiom p updates defs` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 0 (CONJUNCTS updates_rules)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[holKernel_bool_ty_def]) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[HOLKPAUX_TERM_has_type];
      ASM_MESON_TAC[holKernelProof_TERM_def]];
    ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_CONTEXT (CONS (hol_NewAxiom p) defs)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLKPAUX_CONTEXT_CONS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[holKernelProof_THM_def] THEN MATCH_MP_TAC proves_axioms THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOLKPAUX_CONTEXT_theory_ok]; ALL_TAC] THEN
    REWRITE_TAC[SND; MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND; axexts_of_upd_def;
                conexts_of_upd_def; MEM];
    ASM_REWRITE_TAC[holKernelProof_STATE_def; hol_refs_INFO.ri_accfupds; K_THM; MAP;
                    FLAT; APPEND; axexts_of_upd_def; types_of_upd_def; consts_of_upd_def;
                    lift_tm_def];
    GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
    REWRITE_TAC[holKernelProof_THM_def] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP updates_proves)]);;


(* ------------------------------------------------------------------------- *)
(* Removing clash exceptions                                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 marks the function specific theorems [simp]; they are added to the  *)
(* kit simp set below                                                       *)

(* combinators of the state-exception monad that never raise Clash          *)
let HOLKPAUX_NC_bind = prove
 (`!(m:S->(A,hol_exn)exc#S) (f:A->S->(B,hol_exn)exc#S) s tm refs.
     (!s. ~(m s = (M_failure (holKernel_Clash tm),refs))) /\
     (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs)))
     ==> ~(st_ex_bind m f s = (M_failure (holKernel_Clash tm),refs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[st_ex_bind_def] THEN
  MP_TAC(ISPEC `(m:S->(A,hol_exn)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,hol_exn)exc` (X_CHOOSE_THEN `s1:S` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HOLKPAUX_NC_ignore_bind = prove
 (`!(m:S->(A,hol_exn)exc#S) (f:S->(B,hol_exn)exc#S) s tm refs.
     (!s. ~(m s = (M_failure (holKernel_Clash tm),refs))) /\
     (!s. ~(f s = (M_failure (holKernel_Clash tm),refs)))
     ==> ~(st_ex_ignore_bind m f s = (M_failure (holKernel_Clash tm),refs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[st_ex_ignore_bind_def] THEN
  MP_TAC(ISPEC `(m:S->(A,hol_exn)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,hol_exn)exc` (X_CHOOSE_THEN `s1:S` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HOLKPAUX_NC_otherwise = prove
 (`!(x:S->(A,hol_exn)exc#S) y s tm refs.
     (!s. ~(y s = (M_failure (holKernel_Clash tm),refs)))
     ==> ~((x otherwise y) s = (M_failure (holKernel_Clash tm),refs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[otherwise_def] THEN
  MP_TAC(ISPEC `(x:S->(A,hol_exn)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,hol_exn)exc` (X_CHOOSE_THEN `s1:S` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN QCASES_ON "r" THEN
  CAKE_REWRITE_TAC[PAIR_EQ; distinctness "exc"] THEN ASM_MESON_TAC[]);;

let HOLKPAUX_NC_return = prove
 (`!(x:A) (s:S) tm refs.
     ~(st_ex_return x s = (M_failure (holKernel_Clash tm):(A,hol_exn)exc,refs))`,
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; distinctness "exc"]);;

let HOLKPAUX_NC_raise = prove
 (`!msg s tm refs.
     ~(holKernel_raise_Failure msg s =
       (M_failure (holKernel_Clash tm):(A,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ; injectivity "exc";
              distinctness "hol_exn"]);;

let HOLKPAUX_NC_try = prove
 (`!(f:B->hol_refs->(A,hol_exn)exc#hol_refs) x msg s tm refs.
     ~(holKernel_try f x msg s = (M_failure (holKernel_Clash tm),refs))`,
  REWRITE_TAC[holKernel_try_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC HOLKPAUX_NC_otherwise THEN REWRITE_TAC[HOLKPAUX_NC_raise]);;

(* Support theorems *)

let map_not_clash_thm = prove
 (`!(f:A->B->(C,hol_exn)exc#B) xs s tm refs.
     (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs)))
     ==> ~(holKernel_map f xs s = (M_failure (holKernel_Clash tm),refs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_map_def] THEN
  CAKE_REWRITE_TAC[HOLKPAUX_NC_return] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HOLKPAUX_NC_bind THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC HOLKPAUX_NC_bind THEN ASM_SIMP_TAC[HOLKPAUX_NC_return]);;

let forall_clash_thm = prove
 (`!(f:A->B->(bool,hol_exn)exc#B) l s tm refs.
     (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs)))
     ==> ~(holKernel_forall f l s = (M_failure (holKernel_Clash tm),refs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_forall_def] THEN
  CAKE_REWRITE_TAC[HOLKPAUX_NC_return] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HOLKPAUX_NC_bind THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[HOLKPAUX_NC_return]);;

let image_clash_thm = prove
 (`!(f:hol_term->B->(hol_term,hol_exn)exc#B) l s tm refs.
     (!x s. ~(f x s = (M_failure (holKernel_Clash tm),refs)))
     ==> ~(holKernel_image f l s = (M_failure (holKernel_Clash tm),refs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_image_def] THEN
  CAKE_REWRITE_TAC[HOLKPAUX_NC_return] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HOLKPAUX_NC_bind THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC HOLKPAUX_NC_bind THEN ASM_SIMP_TAC[HOLKPAUX_NC_return]);;


(* proves  ~(m s = (M_failure (holKernel_Clash tm),refs))  for m built from *)
(* the monad combinators and functions known not to raise Clash (ths)      *)
let HOLKPAUX_NC_TAC ths =
  let simps = [HOLKPAUX_NC_return; HOLKPAUX_NC_raise; HOLKPAUX_NC_try; FORALL_PAIR_THM;
               PAIR_EQ; distinctness "exc"; injectivity "exc"; distinctness "hol_exn"] @
              ths in
  REPEAT(FIRST
   [CONJ_TAC;
    CHANGED_TAC(CAKE_REWRITE_TAC simps);
    GEN_TAC;
    MATCH_MP_TAC HOLKPAUX_NC_bind;
    MATCH_MP_TAC HOLKPAUX_NC_ignore_bind;
    MATCH_MP_TAC HOLKPAUX_NC_otherwise;
    MATCH_MP_TAC map_not_clash_thm;
    MATCH_MP_TAC forall_clash_thm;
    MATCH_MP_TAC image_clash_thm;
    COND_CASES_TAC;
    CHANGED_TAC EVERY_CASE_TAC]);;

(* Function specific theorems *)

let dest_type_not_clash = prove
 (`!x y tm refs.
     ~(holKernel_dest_type x y =
       (M_failure (holKernel_Clash tm):(mlstring#hol_type list,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_dest_type_def] THEN HOLKPAUX_NC_TAC[]);;

let type_of_not_clash = prove
 (`!x y tm refs.
     ~(holKernel_type_of x y =
       (M_failure (holKernel_Clash tm):(hol_type,hol_exn)exc,refs))`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; ALL_TAC; DISCH_TAC; DISCH_TAC] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[holKernel_type_of_def] THEN
  ASM HOLKPAUX_NC_TAC[dest_type_not_clash]);;

let mk_abs_not_clash = prove
 (`!x y tm refs.
     ~(holKernel_mk_abs x y = (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[FORALL_PAIR_THM; holKernel_mk_abs_def] THEN HOLKPAUX_NC_TAC[]);;

let mk_comb_not_clash = prove
 (`!x y tm refs.
     ~(holKernel_mk_comb x y = (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[FORALL_PAIR_THM; holKernel_mk_comb_def] THEN
  HOLKPAUX_NC_TAC[type_of_not_clash]);;


let HOLKPAUX_FORALL_thm = prove
 (`!P. (!th. P th) <=> (!asl c. P (Sequent asl c))`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN ASM_REWRITE_TAC[]);;

let mk_eq_not_clash = prove
 (`!x y tm refs.
     ~(holKernel_mk_eq x y = (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[FORALL_PAIR_THM; holKernel_mk_eq_def; HOLKPAUX_NC_try]);;

let mk_type_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_mk_type a b = (M_failure (holKernel_Clash tm):(hol_type,hol_exn)exc,refs))`,
  REWRITE_TAC[FORALL_PAIR_THM; holKernel_mk_type_def] THEN HOLKPAUX_NC_TAC[]);;

let safe_mk_eq_not_clash = prove
 (`!x y s tm refs.
     ~(holKernel_safe_mk_eq x y s =
       (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_safe_mk_eq_def] THEN HOLKPAUX_NC_TAC[type_of_not_clash]);;

let ABS_not_clash = prove
 (`!x y z tm refs.
     ~(holKernel_ABS x y z = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_ABS_def] THEN
  HOLKPAUX_NC_TAC[safe_mk_eq_not_clash]);;

let MK_COMB_not_clash = prove
 (`!a b c tm refs.
     ~(holKernel_MK_COMB (a,b) c = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_MK_COMB_def] THEN
  HOLKPAUX_NC_TAC[safe_mk_eq_not_clash; type_of_not_clash]);;

let ASSUME_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_ASSUME a b = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_ASSUME_def] THEN HOLKPAUX_NC_TAC[type_of_not_clash]);;

let BETA_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_BETA a b = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_BETA_def] THEN HOLKPAUX_NC_TAC[safe_mk_eq_not_clash]);;

let mk_const_not_clash = prove
 (`!a b c tm refs.
     ~(holKernel_mk_const (a,b) c =
       (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_mk_const_def] THEN HOLKPAUX_NC_TAC[]);;

let assoc_not_clash = prove
 (`!(a:A) (b:(A#B)list) c tm refs.
     ~(holKernel_assoc a b c = (M_failure (holKernel_Clash tm),refs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_assoc_def] THEN
  ASM HOLKPAUX_NC_TAC[]);;

let get_const_type_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_get_const_type a b =
       (M_failure (holKernel_Clash tm):(hol_type,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_get_const_type_def; holKernel_get_the_term_constants_def] THEN
  HOLKPAUX_NC_TAC[assoc_not_clash]);;

let DEDUCT_ANTISYM_RULE_not_clash = prove
 (`!a b c tm refs.
     ~(holKernel_DEDUCT_ANTISYM_RULE a b c =
       (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_DEDUCT_ANTISYM_RULE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN HOLKPAUX_NC_TAC[safe_mk_eq_not_clash]);;

let SYM_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_SYM a b = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_SYM_def] THEN HOLKPAUX_NC_TAC[]);;

let dest_comb_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_dest_comb a b =
       (M_failure (holKernel_Clash tm):(hol_term#hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_dest_comb_def] THEN HOLKPAUX_NC_TAC[]);;

let dest_eq_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_dest_eq a b =
       (M_failure (holKernel_Clash tm):(hol_term#hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_dest_eq_def] THEN HOLKPAUX_NC_TAC[]);;

let EQ_MP_not_clash = prove
 (`!a b c tm refs.
     ~(holKernel_EQ_MP a b c = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_EQ_MP_def] THEN HOLKPAUX_NC_TAC[]);;

let PROVE_HYP_not_clash = prove
 (`!a b (c:A) tm (refs:A).
     ~(holKernel_PROVE_HYP a b c = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_PROVE_HYP_def] THEN HOLKPAUX_NC_TAC[]);;

let REFL_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_REFL a b = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_REFL_def] THEN HOLKPAUX_NC_TAC[safe_mk_eq_not_clash]);;

let TRANS_not_clash = prove
 (`!a b c tm refs.
     ~(holKernel_TRANS a b c = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_TRANS_def] THEN HOLKPAUX_NC_TAC[]);;


let ALPHA_THM_not_clash = prove
 (`!a b c d tm refs.
     ~(holKernel_ALPHA_THM a (b,c) d =
       (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_ALPHA_THM_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN HOLKPAUX_NC_TAC[type_of_not_clash]);;

let add_constants_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_add_constants a b = (M_failure (holKernel_Clash tm):(1,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_add_constants_def; holKernel_get_the_term_constants_def;
              holKernel_set_the_term_constants_def] THEN
  HOLKPAUX_NC_TAC[]);;

let add_def_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_add_def a b = (M_failure (holKernel_Clash tm):(1,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_add_def_ok; PAIR_EQ; distinctness "exc"]);;

let dest_var_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_dest_var a b =
       (M_failure (holKernel_Clash tm):(mlstring#hol_type,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_dest_var_def] THEN HOLKPAUX_NC_TAC[]);;

let new_specification_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_new_specification a b =
       (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_new_specification_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  HOLKPAUX_NC_TAC[dest_eq_not_clash; dest_var_not_clash; add_constants_not_clash;
                  add_def_not_clash]);;

let new_basic_definition_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_new_basic_definition a b =
       (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_new_basic_definition_def] THEN
  HOLKPAUX_NC_TAC[ASSUME_not_clash; new_specification_not_clash]);;

let add_type_not_clash = prove
 (`!a b c tm refs.
     ~(holKernel_add_type (a,b) c = (M_failure (holKernel_Clash tm):(1,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_add_type_def; ml_monadBase_can_def;
              holKernel_get_the_type_constants_def;
              holKernel_set_the_type_constants_def] THEN
  HOLKPAUX_NC_TAC[]);;

let new_basic_type_definition_not_clash = prove
 (`!a b c d e tm refs.
     ~(holKernel_new_basic_type_definition (a,b,c,d) e =
       (M_failure (holKernel_Clash tm):(thm#thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_new_basic_type_definition_def;
              ml_monadBase_can_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  HOLKPAUX_NC_TAC[type_of_not_clash; add_type_not_clash; mk_type_not_clash;
                  add_constants_not_clash; add_def_not_clash; mk_const_not_clash;
                  mk_comb_not_clash; safe_mk_eq_not_clash]);;

let vsubst_not_clash = prove
 (`!x y s tm refs.
     ~(holKernel_vsubst x y s = (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_vsubst_def] THEN
  HOLKPAUX_NC_TAC[type_of_not_clash; dest_var_not_clash]);;

let INST_not_clash = prove
 (`!theta x s tm refs.
     ~(holKernel_INST theta x s = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,refs))`,
  REWRITE_TAC[HOLKPAUX_FORALL_thm; holKernel_INST_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN HOLKPAUX_NC_TAC[vsubst_not_clash]);;

let new_axiom_not_clash = prove
 (`!ax s tm t.
     ~(holKernel_new_axiom ax s = (M_failure (holKernel_Clash tm):(thm,hol_exn)exc,t))`,
  REWRITE_TAC[holKernel_new_axiom_def; holKernel_get_the_axioms_def;
              holKernel_set_the_axioms_def] THEN
  HOLKPAUX_NC_TAC[type_of_not_clash; add_def_not_clash]);;

let new_constant_not_clash = prove
 (`!a b s tm t.
     ~(holKernel_new_constant (a,b) s = (M_failure (holKernel_Clash tm):(1,hol_exn)exc,t))`,
  REWRITE_TAC[holKernel_new_constant_def] THEN
  HOLKPAUX_NC_TAC[add_constants_not_clash; add_def_not_clash]);;

let new_type_not_clash = prove
 (`!a b s tm t.
     ~(holKernel_new_type (a,b) s = (M_failure (holKernel_Clash tm):(1,hol_exn)exc,t))`,
  REWRITE_TAC[holKernel_new_type_def] THEN
  HOLKPAUX_NC_TAC[add_type_not_clash; add_def_not_clash]);;

let dest_abs_not_clash = prove
 (`!x s tm t.
     ~(holKernel_dest_abs x s =
       (M_failure (holKernel_Clash tm):(hol_term#hol_term,hol_exn)exc,t))`,
  REWRITE_TAC[holKernel_dest_abs_def] THEN HOLKPAUX_NC_TAC[]);;


let _ = cake_add_simps
  [dest_type_not_clash; type_of_not_clash; mk_abs_not_clash; mk_comb_not_clash;
   mk_eq_not_clash; mk_type_not_clash; safe_mk_eq_not_clash; ABS_not_clash;
   MK_COMB_not_clash; ASSUME_not_clash; BETA_not_clash; mk_const_not_clash;
   assoc_not_clash; get_const_type_not_clash; DEDUCT_ANTISYM_RULE_not_clash;
   SYM_not_clash; dest_comb_not_clash; dest_eq_not_clash; EQ_MP_not_clash;
   PROVE_HYP_not_clash; REFL_not_clash; TRANS_not_clash; ALPHA_THM_not_clash;
   add_constants_not_clash; add_def_not_clash; dest_var_not_clash;
   new_specification_not_clash; new_basic_definition_not_clash; add_type_not_clash;
   new_basic_type_definition_not_clash; vsubst_not_clash; INST_not_clash;
   new_axiom_not_clash; new_constant_not_clash; new_type_not_clash;
   dest_abs_not_clash];;

(* HOL4 ends with a commented-out block (variant_same_ty, vsubst_same_Var,  *)
(* inst_aux_clash_is_var, sizeof', inst_aux_clash_is_var_in_env,             *)
(* inst_aux_not_clash, inst_not_clash, INST_TYPE_not_clash: "TODO Prove for *)
(* inst_aux"); it is not part of the theory and is not ported.               *)
