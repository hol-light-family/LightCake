(* ========================================================================= *)
(* holBoolSyntax: port of HOL4 candle/standard/syntax/holBoolSyntaxScript    *)
(* .sml (CakeML v3479).  Definitions to extend a theory context to include  *)
(* the theory of Booleans, and some basic syntactic properties of these     *)
(* extensions.                                                               *)
(* ========================================================================= *)

needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 Overloads are written out, as in holSyntax.ml (see its header):    *)
(*   Bool is Tyapp (implode "bool") [], Fun s t is Tyapp (implode "fun")     *)
(*   [s; t], and the global overloads of this theory are                    *)
(*     True        hol_Const (implode "T") Bool                              *)
(*     And p1 p2   hol_Comb (hol_Comb (hol_Const (implode "/\\")             *)
(*                   (Fun Bool (Fun Bool Bool))) p1) p2                      *)
(*     Implies p1 p2   the same with implode "==>"                           *)
(*     Or p1 p2        the same with implode "\\/"                           *)
(*     Forall x ty p   hol_Comb (hol_Const (implode "!")                     *)
(*                       (Fun (Fun ty Bool) Bool)) (hol_Abs (hol_Var x ty) p)*)
(*     Exists x ty p   the same with implode "?"                             *)
(*     False       hol_Const (implode "F") Bool                              *)
(*     Not p       hol_Comb (hol_Const (implode "~") (Fun Bool Bool)) p      *)
(*   The local overloads p, q, r, f, A, P, x, FAp, FAq, FAr, FAx are the     *)
(*   variables hol_Var (implode "p") Bool, ..., Tyvar (implode "A") and the *)
(*   quantifications Forall (implode "p") Bool, ....  ConstDef x t is        *)
(*   hol_ConstSpec [(x,t)] (hol_Var x (typeof t) === t); thyof, tmsof,       *)
(*   tysof, sigof of a context are written out as in holSyntax.ml.           *)
(* - HOL4 strlit is implode; a set enumeration {"T";"F"} is {"T", "F"}.      *)
(* - Local helpers that are not HOL4 theorems are CBOOLAUX_.                 *)

let TrueDef_def = cake_def
  `TrueDef =
     hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
             (hol_Var (implode "p") (Tyapp (implode "bool") [])) ===
     hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
             (hol_Var (implode "p") (Tyapp (implode "bool") []))`;;

let AndDef_def = cake_def
  `AndDef =
     hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
      (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") []))
        (hol_Abs (hol_Var (implode "f")
                   (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                      Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                             Tyapp (implode "bool") []]]))
           (hol_Comb
              (hol_Comb
                 (hol_Var (implode "f")
                    (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                       Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                              Tyapp (implode "bool") []]]))
                 (hol_Var (implode "p") (Tyapp (implode "bool") [])))
              (hol_Var (implode "q") (Tyapp (implode "bool") []))) ===
         hol_Abs (hol_Var (implode "f")
                   (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                      Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                             Tyapp (implode "bool") []]]))
           (hol_Comb
              (hol_Comb
                 (hol_Var (implode "f")
                    (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                       Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                              Tyapp (implode "bool") []]]))
                 (hol_Const (implode "T") (Tyapp (implode "bool") [])))
              (hol_Const (implode "T") (Tyapp (implode "bool") [])))))`;;

let ImpliesDef_def = cake_def
  `ImpliesDef =
     hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
      (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") []))
        (hol_Comb
           (hol_Comb
              (hol_Const (implode "/\\")
                 (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                    Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                           Tyapp (implode "bool") []]]))
              (hol_Var (implode "p") (Tyapp (implode "bool") [])))
           (hol_Var (implode "q") (Tyapp (implode "bool") [])) ===
         hol_Var (implode "p") (Tyapp (implode "bool") [])))`;;

let ForallDef_def = cake_def
  `ForallDef =
     hol_Abs (hol_Var (implode "P")
                (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]))
       (hol_Var (implode "P")
          (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]) ===
        hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
          (hol_Const (implode "T") (Tyapp (implode "bool") [])))`;;

let ExistsDef_def = cake_def
  `ExistsDef =
     hol_Abs (hol_Var (implode "P")
                (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]))
       (hol_Comb
          (hol_Const (implode "!")
             (Tyapp (implode "fun")
                [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []];
                 Tyapp (implode "bool") []]))
          (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") []))
             (hol_Comb
                (hol_Comb
                   (hol_Const (implode "==>")
                      (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                         Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                                Tyapp (implode "bool") []]]))
                   (hol_Comb
                      (hol_Const (implode "!")
                         (Tyapp (implode "fun")
                            [Tyapp (implode "fun") [Tyvar (implode "A");
                                                    Tyapp (implode "bool") []];
                             Tyapp (implode "bool") []]))
                      (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                         (hol_Comb
                            (hol_Comb
                               (hol_Const (implode "==>")
                                  (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                     Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                                            Tyapp (implode "bool") []]]))
                               (hol_Comb
                                  (hol_Var (implode "P")
                                     (Tyapp (implode "fun") [Tyvar (implode "A");
                                                             Tyapp (implode "bool") []]))
                                  (hol_Var (implode "x") (Tyvar (implode "A")))))
                            (hol_Var (implode "q") (Tyapp (implode "bool") []))))))
                (hol_Var (implode "q") (Tyapp (implode "bool") [])))))`;;

let OrDef_def = cake_def
  `OrDef =
     hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
      (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") []))
        (hol_Comb
           (hol_Const (implode "!")
              (Tyapp (implode "fun")
                 [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []];
                  Tyapp (implode "bool") []]))
           (hol_Abs (hol_Var (implode "r") (Tyapp (implode "bool") []))
              (hol_Comb
                 (hol_Comb
                    (hol_Const (implode "==>")
                       (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                          Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                                 Tyapp (implode "bool") []]]))
                    (hol_Comb
                       (hol_Comb
                          (hol_Const (implode "==>")
                             (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                                       Tyapp (implode "bool") []]]))
                          (hol_Var (implode "p") (Tyapp (implode "bool") [])))
                       (hol_Var (implode "r") (Tyapp (implode "bool") []))))
                 (hol_Comb
                    (hol_Comb
                       (hol_Const (implode "==>")
                          (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                             Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                                    Tyapp (implode "bool") []]]))
                       (hol_Comb
                          (hol_Comb
                             (hol_Const (implode "==>")
                                (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                   Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                                          Tyapp (implode "bool") []]]))
                             (hol_Var (implode "q") (Tyapp (implode "bool") [])))
                          (hol_Var (implode "r") (Tyapp (implode "bool") []))))
                    (hol_Var (implode "r") (Tyapp (implode "bool") [])))))))`;;

let FalseDef_def = cake_def
  `FalseDef =
     hol_Comb
       (hol_Const (implode "!")
          (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []];
              Tyapp (implode "bool") []]))
       (hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
          (hol_Var (implode "p") (Tyapp (implode "bool") [])))`;;

let NotDef_def = cake_def
  `NotDef =
     hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
       (hol_Comb
          (hol_Comb
             (hol_Const (implode "==>")
                (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                   Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                          Tyapp (implode "bool") []]]))
             (hol_Var (implode "p") (Tyapp (implode "bool") [])))
          (hol_Const (implode "F") (Tyapp (implode "bool") [])))`;;

let mk_bool_ctxt_def = cake_def
  `mk_bool_ctxt ctxt =
     CONS (hol_ConstSpec [(implode "~",NotDef)]
             (hol_Var (implode "~") (typeof NotDef) === NotDef))
     (CONS (hol_ConstSpec [(implode "F",FalseDef)]
              (hol_Var (implode "F") (typeof FalseDef) === FalseDef))
     (CONS (hol_ConstSpec [(implode "\\/",OrDef)]
              (hol_Var (implode "\\/") (typeof OrDef) === OrDef))
     (CONS (hol_ConstSpec [(implode "?",ExistsDef)]
              (hol_Var (implode "?") (typeof ExistsDef) === ExistsDef))
     (CONS (hol_ConstSpec [(implode "!",ForallDef)]
              (hol_Var (implode "!") (typeof ForallDef) === ForallDef))
     (CONS (hol_ConstSpec [(implode "==>",ImpliesDef)]
              (hol_Var (implode "==>") (typeof ImpliesDef) === ImpliesDef))
     (CONS (hol_ConstSpec [(implode "/\\",AndDef)]
              (hol_Var (implode "/\\") (typeof AndDef) === AndDef))
     (CONS (hol_ConstSpec [(implode "T",TrueDef)]
              (hol_Var (implode "T") (typeof TrueDef) === TrueDef))
     ctxt)))))))`;;

(* HOL4: val Defs (an ML list) *)
let CBOOLAUX_defs = [TrueDef_def; AndDef_def; ImpliesDef_def; ForallDef_def;
                     ExistsDef_def; OrDef_def; FalseDef_def; NotDef_def];;

(* bool is a good extension *)

(* HOL4's ConstDef_tac and pull_tac: each ConstDef of mk_bool_ctxt is an   *)
(* update of the context below it (ConstDef_updates); the side conditions  *)
(* are decided by rewriting down to the signature of ctxt.                 *)

let CBOOLAUX_extends_CONS = prove
 (`!upd ctxt ctxt0. upd updates ctxt /\ ctxt extends ctxt0
                    ==> CONS upd ctxt extends ctxt0`,
  REWRITE_TAC[extends_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `ctxt:update list` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `upd:update` THEN ASM_REWRITE_TAC[]);;

let CBOOLAUX_ConstDef_extends = prove
 (`!name tm rest ctxt.
     theory_ok
       ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                             (conexts_of_upd upd)) ctxt))) /\
     (hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd rest)),
                   alist_to_fmap (FLAT (MAP consts_of_upd rest))) tm /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd rest)))) /\
      CLOSED tm /\
      set_of_list (tvars tm) SUBSET set_of_list (hol_tyvars (typeof tm))) /\
     rest extends ctxt
     ==> CONS (hol_ConstSpec [(name,tm)] (hol_Var name (typeof tm) === tm)) rest
           extends ctxt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CBOOLAUX_extends_CONS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ConstDef_updates THEN
  ASM_MESON_TAC[extends_theory_ok]);;

let CBOOLAUX_tysof_ConstSpec = prove
 (`!eqs prop ctxt.
     alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_ConstSpec eqs prop) ctxt))) =
     alist_to_fmap (FLAT (MAP types_of_upd ctxt))`,
  REWRITE_TAC[MAP; FLAT; types_of_upd_def; APPEND]);;

let CBOOLAUX_tmsof_ConstDef = prove
 (`!n t prop ctxt.
     alist_to_fmap (FLAT (MAP consts_of_upd
                            (CONS (hol_ConstSpec [(n,t)] prop) ctxt))) =
     alist_to_fmap (FLAT (MAP consts_of_upd ctxt)) |+ (n,typeof t)`,
  SIMP[MAP; FLAT; consts_of_upd_def; APPEND; alist_to_fmap_thm]);;

let CBOOLAUX_term_ok_Abs_Var = prove
 (`!sig s ty t. hol_term_ok (sig:sig) (hol_Abs (hol_Var s ty) t) <=>
                type_ok (FST sig) ty /\ hol_term_ok sig t`,
  REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN MESON_TAC[]);;

let CBOOLAUX_welltyped_Abs_Var = prove
 (`!n ty t. welltyped (hol_Abs (hol_Var n ty) t) <=> welltyped t`,
  REWRITE_TAC[WELLTYPED_CLAUSES; injectivity "hol_term"] THEN MESON_TAC[]);;

let CBOOLAUX_EXISTS_REFL = prove
 (`!a:hol_type. ?x. a = x`,
  MESON_TAC[]);;

(* Rewriting to a fixpoint, with string literal equations decided.  The    *)
(* list decides hol_term_ok, type_ok and welltyped of the closed terms of  *)
(* this theory and the lookups in a context made of ConstDefs over ctxt.   *)

let CBOOLAUX_EVAL thl =
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC thl THEN CONV_TAC (DEPTH_CONV STRING_EQ_CONV)));;

let CBOOLAUX_TERM_THMS =
  [CONJUNCT1 hol_term_ok_def; CONJUNCT1 (CONJUNCT2 hol_term_ok_def);
   CONJUNCT1 (CONJUNCT2 (CONJUNCT2 hol_term_ok_def)); CBOOLAUX_term_ok_Abs_Var;
   type_ok_def; ALL; LENGTH; ARITH_RULE `SUC (SUC 0) = 2`;
   CONJUNCT1 WELLTYPED_CLAUSES; CONJUNCT1 (CONJUNCT2 WELLTYPED_CLAUSES);
   CONJUNCT1 (CONJUNCT2 (CONJUNCT2 WELLTYPED_CLAUSES)); CBOOLAUX_welltyped_Abs_Var;
   typeof_def; codomain_def; equation_def;
   TYPE_SUBST_def; MAP; REV_ASSOCD; injectivity "hol_type"; injectivity "mlstring";
   injectivity "char"; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL; option_INJ;
   UNWIND_THM1; hol_tyvar_inst_exists; CBOOLAUX_EXISTS_REFL;
   CBOOLAUX_tysof_ConstSpec; CBOOLAUX_tmsof_ConstDef; FLOOKUP_UPDATE; FDOM_FUPDATE;
   IN_INSERT; FST; SND] @ CBOOLAUX_defs;;

let CBOOLAUX_CLOSED_TAC =
  REWRITE_TAC(CLOSED_def :: VFREE_IN_def :: equation_def :: distinctness "hol_term" ::
              CBOOLAUX_defs) THEN
  REPEAT GEN_TAC THEN CONV_TAC TAUT;;

let CBOOLAUX_TVARS_TAC =
  REWRITE_TAC([tvars_def; hol_tyvars_def; equation_def; typeof_def; codomain_def; ITLIST;
               MEM_LIST_UNION; set_of_list; UNION_EMPTY] @ CBOOLAUX_defs) THEN
  SET_TAC[];;

(* HOL4: pull_tac() >- ConstDef_tac *)
let CBOOLAUX_STEP_TAC =
  MATCH_MP_TAC CBOOLAUX_ConstDef_extends THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THENL
     [CBOOLAUX_EVAL CBOOLAUX_TERM_THMS; CBOOLAUX_EVAL CBOOLAUX_TERM_THMS;
      CBOOLAUX_CLOSED_TAC; CBOOLAUX_TVARS_TAC];
    ALL_TAC];;

let bool_extends = prove
 (`!ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
              (IMAGE implode {"T", "F", "==>", "/\\", "\\/", "~", "!", "?"})
     ==> mk_bool_ctxt ctxt extends ctxt`,
  GEN_TAC THEN REWRITE_TAC[mk_bool_ctxt_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def; FST; SND] o
              MATCH_MP theory_ok_sig) THEN
  QPAT_X_ASSUM "DISJOINT _ _" (STRIP_ASSUME_TAC o
    REWRITE_RULE[IMAGE_CLAUSES; DISJOINT_INSERT; DISJOINT_EMPTY] o
    ONCE_REWRITE_RULE[DISJOINT_SYM]) THEN
  REPEAT CBOOLAUX_STEP_TAC THEN REWRITE_TAC[extends_def; RTC_REFL]);;

let bool_extends_init = prove
 (`mk_bool_ctxt init_ctxt extends init_ctxt`,
  MATCH_MP_TAC bool_extends THEN REWRITE_TAC[init_theory_ok] THEN
  REWRITE_TAC[init_ctxt_def; MAP; FLAT; APPEND; consts_of_upd_def; FDOM_alist_to_fmap;
              set_of_list; IMAGE_CLAUSES; DISJOINT_INSERT; DISJOINT_EMPTY; IN_INSERT;
              NOT_IN_EMPTY; injectivity "mlstring"; injectivity "char"; CONS_11;
              NOT_CONS_NIL; GSYM NOT_CONS_NIL]);;

(* signatures of Boolean constants *)
let is_true_sig_def = cake_def
  `is_true_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "T") = SOME (Tyapp (implode "bool") [])`;;

let is_false_sig_def = cake_def
  `is_false_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "F") = SOME (Tyapp (implode "bool") [])`;;

let is_implies_sig_def = cake_def
  `is_implies_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "==>") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") [];
             Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])`;;

let is_and_sig_def = cake_def
  `is_and_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "/\\") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") [];
             Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])`;;

let is_or_sig_def = cake_def
  `is_or_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "\\/") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") [];
             Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])`;;

let is_not_sig_def = cake_def
  `is_not_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "~") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []])`;;

let is_forall_sig_def = cake_def
  `is_forall_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "!") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
              Tyapp (implode "bool") []])`;;

let is_exists_sig_def = cake_def
  `is_exists_sig (tmsig:tmsig) <=>
     FLOOKUP tmsig (implode "?") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
              Tyapp (implode "bool") []])`;;

(* HOL4: val sigs (an ML list) *)
let CBOOLAUX_sigs = [is_true_sig_def; is_false_sig_def; is_implies_sig_def; is_and_sig_def;
                     is_or_sig_def; is_not_sig_def; is_forall_sig_def; is_exists_sig_def];;

let is_bool_sig_def = cake_def
  `is_bool_sig (sig:sig) <=>
     is_std_sig sig /\
     is_true_sig (SND sig) /\
     is_false_sig (SND sig) /\
     is_implies_sig (SND sig) /\
     is_and_sig (SND sig) /\
     is_or_sig (SND sig) /\
     is_not_sig (SND sig) /\
     is_forall_sig (SND sig) /\
     is_exists_sig (SND sig)`;;

let bool_has_bool_sig = prove
 (`!ctxt. is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
          ==> is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt ctxt))),
                           alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt ctxt))))`,
  GEN_TAC THEN REWRITE_TAC[is_std_sig_def; FST; SND] THEN STRIP_TAC THEN
  REWRITE_TAC(is_bool_sig_def :: is_std_sig_def :: mk_bool_ctxt_def :: CBOOLAUX_sigs) THEN
  CBOOLAUX_EVAL CBOOLAUX_TERM_THMS);;

let is_bool_sig_std = prove
 (`is_bool_sig sig ==> is_std_sig sig`,
  SIMP_TAC[is_bool_sig_def]);;

(* HOL4 proves it by induction on updates; the lookups that the signature  *)
(* predicates make are kept by any extension (FLOOKUP_tmsof_extends).      *)
let is_bool_sig_extends = prove
 (`!ctxt1 ctxt2. ctxt2 extends ctxt1
     ==> is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt1)))
     ==> is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_std_sig_extends) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_ALL o REWRITE_RULE[SND] o
              MATCH_MP FLOOKUP_tmsof_extends) THEN
  REWRITE_TAC(is_bool_sig_def :: SND :: CBOOLAUX_sigs) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

(* Boolean terms are ok *)

let bool_term_ok = prove
 (`!sig. is_bool_sig sig ==>
    hol_term_ok sig (hol_Const (implode "T") (Tyapp (implode "bool") [])) /\
    (!p1 p2.
       hol_term_ok sig
         (hol_Comb (hol_Comb (hol_Const (implode "/\\")
            (Tyapp (implode "fun") [Tyapp (implode "bool") [];
               Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                      Tyapp (implode "bool") []]])) p1) p2) <=>
       hol_term_ok sig p1 /\ hol_term_ok sig p2 /\
       typeof p1 = Tyapp (implode "bool") [] /\ typeof p2 = Tyapp (implode "bool") []) /\
    (!p1 p2.
       hol_term_ok sig
         (hol_Comb (hol_Comb (hol_Const (implode "==>")
            (Tyapp (implode "fun") [Tyapp (implode "bool") [];
               Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                      Tyapp (implode "bool") []]])) p1) p2) <=>
       hol_term_ok sig p1 /\ hol_term_ok sig p2 /\
       typeof p1 = Tyapp (implode "bool") [] /\ typeof p2 = Tyapp (implode "bool") []) /\
    (!z ty p.
       hol_term_ok sig
         (hol_Comb (hol_Const (implode "!")
            (Tyapp (implode "fun") [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                                    Tyapp (implode "bool") []]))
            (hol_Abs (hol_Var z ty) p)) <=>
       type_ok (FST sig) ty /\ hol_term_ok sig p /\ typeof p = Tyapp (implode "bool") []) /\
    (!z ty p.
       hol_term_ok sig
         (hol_Comb (hol_Const (implode "?")
            (Tyapp (implode "fun") [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                                    Tyapp (implode "bool") []]))
            (hol_Abs (hol_Var z ty) p)) <=>
       type_ok (FST sig) ty /\ hol_term_ok sig p /\ typeof p = Tyapp (implode "bool") []) /\
    (!p1 p2.
       hol_term_ok sig
         (hol_Comb (hol_Comb (hol_Const (implode "\\/")
            (Tyapp (implode "fun") [Tyapp (implode "bool") [];
               Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                      Tyapp (implode "bool") []]])) p1) p2) <=>
       hol_term_ok sig p1 /\ hol_term_ok sig p2 /\
       typeof p1 = Tyapp (implode "bool") [] /\ typeof p2 = Tyapp (implode "bool") []) /\
    hol_term_ok sig (hol_Const (implode "F") (Tyapp (implode "bool") [])) /\
    (!p.
       hol_term_ok sig
         (hol_Comb (hol_Const (implode "~")
            (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]))
            p) <=>
       hol_term_ok sig p /\ typeof p = Tyapp (implode "bool") [])`,
  GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE(is_bool_sig_def :: CBOOLAUX_sigs)) THEN
  FIRST_ASSUM(fun th -> let cl = MATCH_MP term_ok_clauses th in
    REWRITE_TAC[cl] THEN
    ASM_REWRITE_TAC[cl; CONJUNCT1 (CONJUNCT2 hol_term_ok_def);
     CONJUNCT1 WELLTYPED_CLAUSES; CONJUNCT1 (CONJUNCT2 WELLTYPED_CLAUSES);
     CONJUNCT1 (CONJUNCT2 (CONJUNCT2 WELLTYPED_CLAUSES)); CBOOLAUX_welltyped_Abs_Var;
     typeof_def; codomain_def; TYPE_SUBST_def; MAP; REV_ASSOCD;
     injectivity "hol_type"; CONS_11; option_INJ; UNWIND_THM1; hol_tyvar_inst_exists;
     RIGHT_EXISTS_AND_THM; CBOOLAUX_EXISTS_REFL]) THEN
  MESON_TAC[term_ok_welltyped]);;
