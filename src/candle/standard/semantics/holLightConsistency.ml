(* ========================================================================= *)
(* holLightConsistency: port of HOL4 candle/standard/semantics/              *)
(* holLightConsistencyScript.sml (CakeML v3479).  Consistency of the         *)
(* contexts that HOL Light actually builds: holConsistency's results need   *)
(* an extension of init_ctxt without axioms, or of fhol_ctxt or hol_ctxt,   *)
(* but a real HOL Light session interleaves definitions between the three   *)
(* axioms, states ETA_AX and SELECT_AX universally closed, declares ind     *)
(* below ONE_ONE and ONTO, and binds those two definitions with generated   *)
(* variables.  This theory states consistency for that shape (hol_light_ctxt *)
(* and fhol_light_ctxt), shows each shape realisable, and checks it against *)
(* the context a Candle session prints after loading core HOL Light.        *)
(*                                                                           *)
(* Notes on the rendering (see also the headers of holSyntax.ml,            *)
(* holBoolSyntax.ml and holSemantics.ml):                                    *)
(* - HOL4's overloads are written out: the local ones A, B (Tyvar           *)
(*   (implode "A"), Tyvar (implode "B")), x, P, tf, gf, x1, x2, y, h (the     *)
(*   variables hol_Var (implode "x") A, ...; tf is hol_Var (implode "t")     *)
(*   (Fun A B), gf and h are hol_Var (implode "f") of types Fun A B and      *)
(*   Fun Ind Ind), holAxiomsSyntax's Select ty, One_One f, Onto f            *)
(*   (hol_Comb (hol_Const (implode "ONE_ONE") (Fun (typeof f) Bool)) f, with *)
(*   typeof unevaluated, as HOL4 stores it) and Ind (Tyapp (implode "ind")   *)
(*   []), holBoolSyntax's Forall, Exists, And, Not, Implies, holSyntax's      *)
(*   ConstDef x t (hol_ConstSpec [(x,t)] (hol_Var x (typeof t) === t)), and *)
(*   this theory's axiom_free l, which is ALL (\u. !p. ~(u = hol_NewAxiom    *)
(*   p)) l.                                                                  *)
(* - HOL4's ^mem is the variable mem:U->U->bool and the constants with a mem *)
(*   argument are written as in holSemantics.ml: i models thy is models0 mem *)
(*   i thy, i satisfies (sig,h,c) is satisfies0 mem i (sig,h,c), and so on.  *)
(* - HOL4's variable inf (a HOL Light constant) is inf'.                     *)
(* - HOL4's l0 ++ l1 ++ l2 is left-associative: APPEND (APPEND l0 l1) l2.    *)
(* - HOL4's EVAL_TAC proofs (the measured context, the lookups in the       *)
(*   contexts of the nonempty theorems) rewrite with the definitions; the   *)
(*   HOL4 comments that number the updates of measured_prefix are in the    *)
(*   comment before it (a comment cannot be inside a term).                 *)
(* - Local helpers that are not HOL4 theorems are CHLAUX_.                   *)
(* ========================================================================= *)

needs "candle/set-theory/setSpec.ml";;
needs "candle/set-theory/setModel.ml";;
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
needs "candle/standard/semantics/holConsistency.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The three axiom-carrying blocks, in the form HOL Light states them.       *)
(* ETA_AX and SELECT_AX are the universal closures of the terms modelled in  *)
(* holAxiomsSyntax, with the closure binders pinned to the names HOL Light   *)
(* uses (class.ml): the predicates below fix these updates by equality of    *)
(* contexts, not up to alpha, so a different binder is a different context.  *)
(* The two constants of the infinity block are bound by generated variables, *)
(* so those two names alone are parameters.                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4: NewAxiom (Forall <<t>> (Fun A B) (Abs x (Comb tf x) === tf)) :: ctxt *)
let mk_eta_ctxt_cl_def = cake_def
  `mk_eta_ctxt_cl ctxt =
     CONS (hol_NewAxiom
             (hol_Comb
                (hol_Const (implode "!")
                   (Tyapp (implode "fun")
                      [Tyapp (implode "fun")
                         [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                          Tyapp (implode "bool") []];
                       Tyapp (implode "bool") []]))
                (hol_Abs
                   (hol_Var (implode "t")
                      (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                   (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                      (hol_Comb
                         (hol_Var (implode "t")
                            (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                         (hol_Var (implode "x") (Tyvar (implode "A")))) ===
                    hol_Var (implode "t")
                      (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])))))
          ctxt`;;

(* HOL4: NewAxiom (Forall <<P>> (Fun A Bool) (Forall <<x>> A
           (Implies (Comb P x) (Comb P (Comb (Select A) P))))) ::
         NewConst <<@>> (Fun (Fun A Bool) A) :: ctxt *)
let mk_select_ctxt_cl_def = cake_def
  `mk_select_ctxt_cl ctxt =
     CONS (hol_NewAxiom
             (hol_Comb
                (hol_Const (implode "!")
                   (Tyapp (implode "fun")
                      [Tyapp (implode "fun")
                         [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                          Tyapp (implode "bool") []];
                       Tyapp (implode "bool") []]))
                (hol_Abs
                   (hol_Var (implode "P")
                      (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]))
                   (hol_Comb
                      (hol_Const (implode "!")
                         (Tyapp (implode "fun")
                            [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                             Tyapp (implode "bool") []]))
                      (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                         (hol_Comb
                            (hol_Comb
                               (hol_Const (implode "==>")
                                  (Tyapp (implode "fun")
                                     [Tyapp (implode "bool") [];
                                      Tyapp (implode "fun")
                                        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))
                               (hol_Comb
                                  (hol_Var (implode "P")
                                     (Tyapp (implode "fun")
                                        [Tyvar (implode "A"); Tyapp (implode "bool") []]))
                                  (hol_Var (implode "x") (Tyvar (implode "A")))))
                            (hol_Comb
                               (hol_Var (implode "P")
                                  (Tyapp (implode "fun")
                                     [Tyvar (implode "A"); Tyapp (implode "bool") []]))
                               (hol_Comb
                                  (hol_Const (implode "@")
                                     (Tyapp (implode "fun")
                                        [Tyapp (implode "fun")
                                           [Tyvar (implode "A"); Tyapp (implode "bool") []];
                                         Tyvar (implode "A")]))
                                  (hol_Var (implode "P")
                                     (Tyapp (implode "fun")
                                        [Tyvar (implode "A"); Tyapp (implode "bool") []]))))))))))
     (CONS (hol_NewConst (implode "@")
              (Tyapp (implode "fun")
                 [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                  Tyvar (implode "A")]))
           ctxt)`;;

(* HOL4: NewAxiom (Exists <<f>> (Fun Ind Ind) (And (One_One h) (Not (Onto h)))) ::
         ConstDef <<ONTO>> (Abs (Var b2 (Fun A B))
           (Forall <<y>> B (Exists <<x>> A (y === Comb (Var b2 (Fun A B)) x)))) ::
         ConstDef <<ONE_ONE>> (Abs (Var b1 (Fun A B)) (Forall <<x1>> A (Forall <<x2>> A
           (Implies (Comb (Var b1 (Fun A B)) x1 === Comb (Var b1 (Fun A B)) x2)
                    (x1 === x2))))) ::
         NewType <<ind>> 0 :: ctxt *)
let mk_infinity_ctxt_hl_def = cake_def
  `mk_infinity_ctxt_hl b1 b2 ctxt =
     CONS
       (hol_NewAxiom
          (hol_Comb
             (hol_Const (implode "?")
                (Tyapp (implode "fun")
                   [Tyapp (implode "fun")
                      [Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind") []];
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
                                        [Tyapp (implode "ind") []; Tyapp (implode "ind") []]));
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
                                        [Tyapp (implode "ind") []; Tyapp (implode "ind") []]));
                                Tyapp (implode "bool") []]))
                         (hol_Var (implode "f")
                            (Tyapp (implode "fun")
                               [Tyapp (implode "ind") []; Tyapp (implode "ind") []]))))))))
       (CONS
          (hol_ConstSpec
             [(implode "ONTO",
               hol_Abs
                 (hol_Var b2 (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                             (hol_Var (implode "y") (Tyvar (implode "B")) ===
                              hol_Comb
                                (hol_Var b2
                                   (Tyapp (implode "fun")
                                      [Tyvar (implode "A"); Tyvar (implode "B")]))
                                (hol_Var (implode "x") (Tyvar (implode "A")))))))))]
             (hol_Var (implode "ONTO")
                (typeof
                   (hol_Abs
                      (hol_Var b2
                         (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                      (hol_Comb
                         (hol_Const (implode "!")
                            (Tyapp (implode "fun")
                               [Tyapp (implode "fun")
                                  [Tyvar (implode "B"); Tyapp (implode "bool") []];
                                Tyapp (implode "bool") []]))
                         (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
                            (hol_Comb
                               (hol_Const (implode "?")
                                  (Tyapp (implode "fun")
                                     [Tyapp (implode "fun")
                                        [Tyvar (implode "A"); Tyapp (implode "bool") []];
                                      Tyapp (implode "bool") []]))
                               (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                                  (hol_Var (implode "y") (Tyvar (implode "B")) ===
                                   hol_Comb
                                     (hol_Var b2
                                        (Tyapp (implode "fun")
                                           [Tyvar (implode "A"); Tyvar (implode "B")]))
                                     (hol_Var (implode "x") (Tyvar (implode "A")))))))))) ===
              hol_Abs
                (hol_Var b2 (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                            (hol_Var (implode "y") (Tyvar (implode "B")) ===
                             hol_Comb
                               (hol_Var b2
                                  (Tyapp (implode "fun")
                                     [Tyvar (implode "A"); Tyvar (implode "B")]))
                               (hol_Var (implode "x") (Tyvar (implode "A"))))))))))
          (CONS
             (hol_ConstSpec
                [(implode "ONE_ONE",
                  hol_Abs
                    (hol_Var b1
                       (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                    (hol_Comb
                       (hol_Const (implode "!")
                          (Tyapp (implode "fun")
                             [Tyapp (implode "fun")
                                [Tyvar (implode "A"); Tyapp (implode "bool") []];
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
                                      (hol_Comb
                                         (hol_Var b1
                                            (Tyapp (implode "fun")
                                               [Tyvar (implode "A"); Tyvar (implode "B")]))
                                         (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                       hol_Comb
                                         (hol_Var b1
                                            (Tyapp (implode "fun")
                                               [Tyvar (implode "A"); Tyvar (implode "B")]))
                                         (hol_Var (implode "x2") (Tyvar (implode "A")))))
                                   (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                                    hol_Var (implode "x2") (Tyvar (implode "A")))))))))]
                (hol_Var (implode "ONE_ONE")
                   (typeof
                      (hol_Abs
                         (hol_Var b1
                            (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                         (hol_Comb
                            (hol_Const (implode "!")
                               (Tyapp (implode "fun")
                                  [Tyapp (implode "fun")
                                     [Tyvar (implode "A"); Tyapp (implode "bool") []];
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
                                           (hol_Comb
                                              (hol_Var b1
                                                 (Tyapp (implode "fun")
                                                    [Tyvar (implode "A"); Tyvar (implode "B")]))
                                              (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                            hol_Comb
                                              (hol_Var b1
                                                 (Tyapp (implode "fun")
                                                    [Tyvar (implode "A"); Tyvar (implode "B")]))
                                              (hol_Var (implode "x2") (Tyvar (implode "A")))))
                                        (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                                         hol_Var (implode "x2") (Tyvar (implode "A")))))))))) ===
                 hol_Abs
                   (hol_Var b1 (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                   (hol_Comb
                      (hol_Const (implode "!")
                         (Tyapp (implode "fun")
                            [Tyapp (implode "fun")
                               [Tyvar (implode "A"); Tyapp (implode "bool") []];
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
                                     (hol_Comb
                                        (hol_Var b1
                                           (Tyapp (implode "fun")
                                              [Tyvar (implode "A"); Tyvar (implode "B")]))
                                        (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                      hol_Comb
                                        (hol_Var b1
                                           (Tyapp (implode "fun")
                                              [Tyvar (implode "A"); Tyvar (implode "B")]))
                                        (hol_Var (implode "x2") (Tyvar (implode "A")))))
                                  (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                                   hol_Var (implode "x2") (Tyvar (implode "A"))))))))))
             (CONS (hol_NewType (implode "ind") 0) ctxt)))`;;

(* ------------------------------------------------------------------------- *)
(* Extension chains and their suffixes.  Each step of an extension conses a  *)
(* single update, so the chain from c0 up to ctxt visits precisely the       *)
(* suffixes of ctxt.  Any suffix that still has c0 below it is therefore one *)
(* of them, and the update sitting directly on top of such a suffix is one   *)
(* the chain performed: that is where every freshness side condition below   *)
(* comes from.                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4's simp uses APPEND_EQ_SELF here *)
let CHLAUX_CONS_APPEND_NEQ = prove
 (`!(u:A) m c0. ~(CONS u (APPEND m c0) = c0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

(* the chain cannot already have arrived at c0, since c0 sits strictly below
   the update on top; so its last step is that update *)

let extends_CONS = prove
 (`!u ctxt c0 m.
     CONS u ctxt extends c0 /\ ctxt = APPEND m c0 ==> u updates ctxt /\ ctxt extends c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS[] THEN
  QPAT_X_ASSUM "_ extends _" (MP_TAC o REWRITE_RULE[extends_def]) THEN
  SIMP[ONCE RTC_CASES1] THEN STRIP_TAC THEN GVS[GSYM extends_def; CHLAUX_CONS_APPEND_NEQ]);;

let extends_CONS_I = prove
 (`!u ctxt base. ctxt extends base /\ u updates ctxt ==> CONS u ctxt extends base`,
  RW[extends_def] THEN SIMP[ONCE RTC_CASES1] THEN ASM_MESON_TAC[]);;

let extends_suffix = prove
 (`!l base c0.
     APPEND l base extends c0 /\ (?m. base = APPEND m c0) ==> APPEND l base extends base`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
  [REWRITE_TAC[extends_def; RTC_REFL];
   REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m:update list` SUBST_ALL_TAC)) THEN
   MP_TAC(ISPECL [`h:update`; `APPEND t (APPEND m c0):update list`; `c0:update list`;
                  `APPEND t m:update list`] extends_CONS) THEN
   ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN STRIP_TAC THEN
   MATCH_MP_TAC extends_CONS_I THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let extends_suffix_below = prove
 (`!l base c0. APPEND l base extends c0 /\ (?m. base = APPEND m c0) ==> base extends c0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
  [MESON_TAC[];
   REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m:update list` SUBST_ALL_TAC)) THEN
   MP_TAC(ISPECL [`h:update`; `APPEND t (APPEND m c0):update list`; `c0:update list`;
                  `APPEND t m:update list`] extends_CONS) THEN
   ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let extends_updates_at = prove
 (`!l u rest c0.
     APPEND l (CONS u rest) extends c0 /\ (?m. rest = APPEND m c0)
     ==> u updates rest /\ rest extends c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC extends_CONS THEN
  EXISTS_TAC `m:update list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC extends_suffix_below THEN EXISTS_TAC `l:update list` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; EXISTS_TAC `CONS (u:update) m` THEN
                  ASM_REWRITE_TAC[APPEND]]);;

(* ------------------------------------------------------------------------- *)
(* Models along a chain                                                      *)
(* ------------------------------------------------------------------------- *)

(* an axiom-free segment carries a model along with it *)

let models_axiom_free_segment = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !l base i.
         APPEND l base extends base /\
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd base)),
             alist_to_fmap (FLAT (MAP consts_of_upd base))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) base))) /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd base)),
             alist_to_fmap (FLAT (MAP consts_of_upd base))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) base))) /\
         ALL (\u. !p. ~(u = hol_NewAxiom p)) l
         ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd base)),
                            alist_to_fmap (FLAT (MAP consts_of_upd base))) i i' /\
                  models0 mem i'
                    ((alist_to_fmap (FLAT (MAP types_of_upd (APPEND l base))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (APPEND l base)))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd))
                                            (APPEND l base))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base:update list`; `APPEND l base:update list`]
           (UNDISCH extends_consistent)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FS[GSYM ALL_MEM; MEM_APPEND] THEN ASM_MESON_TAC[]);;
(* asserting an axiom leaves the signature alone *)

let models_NewAxiom = prove
 (`!i p ctxt.
     models0 (mem:U->U->bool) i
       ((alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewAxiom p) ctxt))),
         alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewAxiom p) ctxt)))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                               (CONS (hol_NewAxiom p) ctxt)))) <=>
     models0 mem i
       ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                               ctxt))) /\
     satisfies0 mem i
       ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),[],p)`,
  RW[models0_def; conexts_of_upd_def] THEN MESON_TAC[]);;

(* and a model does not see the names of bound variables *)

let satisfies_ACONV = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !i sig p q.
         ACONV p q /\ welltyped p /\ welltyped q /\ satisfies0 mem i (sig,[],p)
         ==> satisfies0 mem i (sig,[],q)`,
  RW[satisfies0_def] THEN ASM_MESON_TAC[termsem_aconv]);;

let models_ACONV = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !i ctxt1 ctxt2.
         (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
          alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))) =
         (alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
          alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))) /\
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   ctxt1))) /\
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   ctxt2))) /\
         (!p. p IN set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                        (conexts_of_upd upd)) ctxt2))
              ==> ?q. q IN set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                                (conexts_of_upd upd))
                                                  ctxt1)) /\
                      ACONV q p) /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   ctxt1)))
         ==> models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt2)))`,
  REPEAT STRIP_TAC THEN FS[models0_def] THEN REPEAT STRIP_TAC THEN
  QBY "?q. MEM q (FLAT (MAP (\\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt1)) /\\
           ACONV q p" (ASM_MESON_TAC[IN_SET_OF_LIST]) THEN
  QBY "welltyped p /\\ welltyped q"
    (FS[theory_ok_def] THEN ASM_MESON_TAC[welltyped_def; IN_SET_OF_LIST]) THEN
  IRULE (UNDISCH satisfies_ACONV) THEN ASM_MESON_TAC[IN_SET_OF_LIST]);;

(* closing an axiom over a variable keeps it satisfied *)

let satisfies_Forall = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !i sig nm ty b.
         is_interpretation0 mem sig i /\ is_std_interpretation0 mem i /\
         type_ok (FST sig) ty /\ hol_term_ok sig b /\ typeof b = Tyapp (implode "bool") [] /\
         is_forall_sig (SND sig) /\ is_forall_interpretation0 mem (SND i) /\
         satisfies0 mem i (sig,[],b)
         ==> satisfies0 mem i
               (sig,[],
                hol_Comb
                  (hol_Const (implode "!")
                     (Tyapp (implode "fun")
                        [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                         Tyapp (implode "bool") []]))
                  (hol_Abs (hol_Var nm ty) b))`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[satisfies0_def; ALL] THEN STRIP_TAC THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`sig:sig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                `v:(mlstring->U)#(mlstring#hol_type->U)`; `nm:mlstring`; `ty:hol_type`;
                `b:hol_term`] (UNDISCH termsem_forall)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[UNDISCH boolean_eq_true] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FS[is_valuation0_def; is_term_valuation0_def; APPLY_UPDATE_THM] THEN
  RW[] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The blocks have models                                                    *)
(* ------------------------------------------------------------------------- *)

let welltyped_eta_ax = prove
 (`!nm. welltyped
          (hol_Comb
             (hol_Const (implode "!")
                (Tyapp (implode "fun")
                   [Tyapp (implode "fun")
                      [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                       Tyapp (implode "bool") []];
                    Tyapp (implode "bool") []]))
             (hol_Abs
                (hol_Var nm (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                   (hol_Comb
                      (hol_Var nm
                         (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                      (hol_Var (implode "x") (Tyvar (implode "A")))) ===
                 hol_Var nm (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))))`,
  SIMP[equation_def; typeof_def; codomain_def]);;

let ACONV_eta_ax = prove
 (`ACONV
     (hol_Comb
        (hol_Const (implode "!")
           (Tyapp (implode "fun")
              [Tyapp (implode "fun")
                 [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                  Tyapp (implode "bool") []];
               Tyapp (implode "bool") []]))
        (hol_Abs
           (hol_Var (implode "f")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
           (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
              (hol_Comb
                 (hol_Var (implode "f")
                    (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                 (hol_Var (implode "x") (Tyvar (implode "A")))) ===
            hol_Var (implode "f")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))))
     (hol_Comb
        (hol_Const (implode "!")
           (Tyapp (implode "fun")
              [Tyapp (implode "fun")
                 [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                  Tyapp (implode "bool") []];
               Tyapp (implode "bool") []]))
        (hol_Abs
           (hol_Var (implode "t")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
           (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
              (hol_Comb
                 (hol_Var (implode "t")
                    (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                 (hol_Var (implode "x") (Tyvar (implode "A")))) ===
            hol_Var (implode "t")
              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))))`,
  SIMP[ACONV_def; RACONV; ALPHAVARS_def; equation_def; typeof_def; codomain_def;
       injectivity "char"]);;

let eta_cl_has_model = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !ctxt i.
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))) /\
         is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))) /\
         is_bool_interpretation0 mem i
         ==> models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd (mk_eta_ctxt_cl ctxt))),
                 alist_to_fmap (FLAT (MAP consts_of_upd (mk_eta_ctxt_cl ctxt)))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                        (conexts_of_upd upd))
                                       (mk_eta_ctxt_cl ctxt))))`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  MP_TAC(SPEC `ctxt:update list` (UNDISCH eta_has_model)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[] THEN
  PURE_REWRITE_TAC[mk_eta_ctxt_def; mk_eta_ctxt_cl_def; models_NewAxiom] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] (UNDISCH satisfies_ACONV)) ACONV_eta_ax) THEN
  REWRITE_TAC[welltyped_eta_ax] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC(UNDISCH satisfies_Forall) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FS[is_bool_sig_def; is_bool_interpretation0_def; models0_def; is_std_sig_def; type_ok_def;
     term_ok_equation; hol_term_ok_def; equation_def; typeof_def; codomain_def]);;
let equal_on_bool_interpretation = prove
 (`!s j1 j2.
     equal_on s j1 j2 /\ is_bool_interpretation0 (mem:U->U->bool) j1 /\ is_bool_sig s /\
     is_std_interpretation0 mem j2
     ==> is_bool_interpretation0 mem j2`,
  RW[is_bool_interpretation0_def; is_true_interpretation0_def; is_and_interpretation0_def;
     is_implies_interpretation0_def; is_forall_interpretation0_def;
     is_exists_interpretation0_def; is_or_interpretation0_def;
     is_false_interpretation0_def; is_not_interpretation0_def] THEN
  MATCH_MP_TAC equal_on_interprets THEN
  MAP_EVERY EXISTS_TAC [`s:sig`; `j1:(mlstring->U list->U)#(mlstring->U list->U)`] THEN
  FS[is_bool_sig_def; is_true_sig_def; is_and_sig_def; is_implies_sig_def;
     is_forall_sig_def; is_exists_sig_def; is_or_sig_def; is_false_sig_def;
     is_not_sig_def] THEN
  SIMP[type_ok_def; tyvars_def] THEN FS[is_std_sig_def]);;
let term_ok_Forall = prove
 (`!sig nm ty p.
     is_std_sig sig /\ is_forall_sig (SND sig) /\ type_ok (FST sig) ty /\
     hol_term_ok sig p /\ typeof p = Tyapp (implode "bool") []
     ==> hol_term_ok sig
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var nm ty) p)) /\
         typeof
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var nm ty) p)) =
         Tyapp (implode "bool") []`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC term_ok_welltyped THEN
  SIMP[hol_term_ok_def; type_ok_def; typeof_def; codomain_def] THEN
  FS[is_std_sig_def; is_forall_sig_def] THEN
  EXISTS_TAC `[(ty:hol_type,Tyvar (implode "A"))]` THEN REWRITE_TAC[REV_ASSOCD]);;
let models_close_axiom = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !i ctxt nm ty p.
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewAxiom p) ctxt))),
             alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewAxiom p) ctxt)))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   (CONS (hol_NewAxiom p) ctxt)))) /\
         is_forall_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
         is_forall_interpretation0 mem (SND i) /\
         type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) ty /\
         hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) p /\
         typeof p = Tyapp (implode "bool") []
         ==> models0 mem i
               ((alist_to_fmap (FLAT (MAP types_of_upd
                   (CONS (hol_NewAxiom
                            (hol_Comb
                               (hol_Const (implode "!")
                                  (Tyapp (implode "fun")
                                     [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                                      Tyapp (implode "bool") []]))
                               (hol_Abs (hol_Var nm ty) p)))
                         ctxt))),
                 alist_to_fmap (FLAT (MAP consts_of_upd
                   (CONS (hol_NewAxiom
                            (hol_Comb
                               (hol_Const (implode "!")
                                  (Tyapp (implode "fun")
                                     [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                                      Tyapp (implode "bool") []]))
                               (hol_Abs (hol_Var nm ty) p)))
                         ctxt)))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd))
                  (CONS (hol_NewAxiom
                           (hol_Comb
                              (hol_Const (implode "!")
                                 (Tyapp (implode "fun")
                                    [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                                     Tyapp (implode "bool") []]))
                              (hol_Abs (hol_Var nm ty) p)))
                        ctxt))))`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[models_NewAxiom] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(UNDISCH satisfies_Forall) THEN
  FS[models0_def; FST; SND]);;
(* the axiom of a good theory is a term of type bool (HOL4 extracts it inline
   from theory_ok_def) *)
let CHLAUX_theory_ok_NewAxiom = prove
 (`!p c. theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewAxiom p) c))),
             alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewAxiom p) c)))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   (CONS (hol_NewAxiom p) c))))
         ==> hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd c)),
                          alist_to_fmap (FLAT (MAP consts_of_upd c))) p /\
             typeof p = Tyapp (implode "bool") []`,
  SIMP[theory_ok_def; IN_SET_OF_LIST] THEN MESON_TAC[WELLTYPED_LEMMA]);;

let select_cl_has_model = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !ctxt i.
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))) /\
         is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
         ~(implode "@" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))) /\
         is_bool_interpretation0 mem i
         ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                            alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                  models0 mem i'
                    ((alist_to_fmap (FLAT (MAP types_of_upd (mk_select_ctxt_cl ctxt))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (mk_select_ctxt_cl ctxt)))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd))
                                            (mk_select_ctxt_cl ctxt))))`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  QBY "is_implies_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))" (FS[is_bool_sig_def]) THEN
  QBY "is_implies_interpretation0 mem (SND (i:(mlstring->U list->U)#(mlstring->U list->U)))"
    (FS[is_bool_interpretation0_def]) THEN
  MP_TAC(SPEC `ctxt:update list` (UNDISCH select_has_model)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':(mlstring->U list->U)#(mlstring->U list->U)`
               STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i':(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_REWRITE_TAC[] THEN
  QBY "CONS (hol_NewConst (implode \"@\")
               (Tyapp (implode \"fun\")
                  [Tyapp (implode \"fun\") [Tyvar (implode \"A\"); Tyapp (implode \"bool\") []];
                   Tyvar (implode \"A\")])) ctxt extends ctxt"
    (MATCH_MP_TAC extends_CONS_I THEN REWRITE_TAC[extends_def; RTC_REFL] THEN
     MATCH_MP_TAC (el 1 (CONJUNCTS updates_rules)) THEN ASM_REWRITE_TAC[] THEN
     FS[type_ok_def; is_std_sig_def]) THEN
  QBY "mk_select_ctxt ctxt extends ctxt"
    (MATCH_MP_TAC select_extends THEN FS[is_std_sig_def; is_implies_sig_def]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP extends_theory_ok) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  QBY "is_bool_sig
         (alist_to_fmap (FLAT (MAP types_of_upd
            (CONS (hol_NewConst (implode \"@\")
                     (Tyapp (implode \"fun\")
                        [Tyapp (implode \"fun\")
                           [Tyvar (implode \"A\"); Tyapp (implode \"bool\") []];
                         Tyvar (implode \"A\")])) ctxt))),
          alist_to_fmap (FLAT (MAP consts_of_upd
            (CONS (hol_NewConst (implode \"@\")
                     (Tyapp (implode \"fun\")
                        [Tyapp (implode \"fun\")
                           [Tyvar (implode \"A\"); Tyapp (implode \"bool\") []];
                         Tyvar (implode \"A\")])) ctxt))))"
    (ASM_MESON_TAC[is_bool_sig_extends]) THEN
  QBY "is_std_interpretation0 mem (i':(mlstring->U list->U)#(mlstring->U list->U))"
    (FS[models0_def]) THEN
  QBY "is_bool_interpretation0 mem (i':(mlstring->U list->U)#(mlstring->U list->U))"
    (ASM_MESON_TAC[equal_on_bool_interpretation]) THEN
  QBY "is_forall_interpretation0 mem (SND (i':(mlstring->U list->U)#(mlstring->U list->U)))"
    (FS[is_bool_interpretation0_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_select_ctxt_def]) THEN
  REWRITE_TAC[mk_select_ctxt_cl_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CHLAUX_theory_ok_NewAxiom) THEN
  MATCH_MP_TAC(UNDISCH models_close_axiom) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC(UNDISCH models_close_axiom) THEN ASM_REWRITE_TAC[type_ok_def] THEN
   FS[is_bool_sig_def];
   ALL_TAC] THEN
  CONJ_TAC THENL [FS[is_bool_sig_def]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FS[is_bool_sig_def; is_std_sig_def; type_ok_def]; ALL_TAC] THEN
  MATCH_MP_TAC term_ok_Forall THEN ASM_REWRITE_TAC[type_ok_def] THEN
  FS[is_bool_sig_def]);;

(* HOL Light declares ind at the bottom of the infinity block rather than
   above the two definitions, and binds the two definitions with generated
   variables. A NewType update contributes no constants and no axioms and a
   ConstSpec update contributes no types, so moving ind past them leaves the
   type and constant lists as the very same lists; and a bound variable name
   is invisible to the signature. *)

let sigof_mk_infinity_ctxt_hl = prove
 (`!b1 b2 ctxt.
     alist_to_fmap (FLAT (MAP types_of_upd (mk_infinity_ctxt_hl b1 b2 ctxt))) =
     alist_to_fmap (FLAT (MAP types_of_upd (mk_infinity_ctxt ctxt))) /\
     alist_to_fmap (FLAT (MAP consts_of_upd (mk_infinity_ctxt_hl b1 b2 ctxt))) =
     alist_to_fmap (FLAT (MAP consts_of_upd (mk_infinity_ctxt ctxt)))`,
  SIMP[mk_infinity_ctxt_hl_def; mk_infinity_ctxt_def; typeof_def; codomain_def]);;

let ACONV_ONE_ONE_conext = prove
 (`!b. ACONV
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
                           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                            Tyapp (implode "bool") []]))
                     (hol_Abs (hol_Var (implode "x2") (Tyvar (implode "A")))
                        (hol_Comb
                           (hol_Comb
                              (hol_Const (implode "==>")
                                 (Tyapp (implode "fun")
                                    [Tyapp (implode "bool") [];
                                     Tyapp (implode "fun")
                                       [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))
                              (hol_Comb
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                               hol_Comb
                                 (hol_Var (implode "f")
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x2") (Tyvar (implode "A")))))
                           (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                            hol_Var (implode "x2") (Tyvar (implode "A")))))))))
         (hol_Const (implode "ONE_ONE")
            (Tyapp (implode "fun")
               [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                Tyapp (implode "bool") []]) ===
          hol_Abs (hol_Var b (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
            (hol_Comb
               (hol_Const (implode "!")
                  (Tyapp (implode "fun")
                     [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                      Tyapp (implode "bool") []]))
               (hol_Abs (hol_Var (implode "x1") (Tyvar (implode "A")))
                  (hol_Comb
                     (hol_Const (implode "!")
                        (Tyapp (implode "fun")
                           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                            Tyapp (implode "bool") []]))
                     (hol_Abs (hol_Var (implode "x2") (Tyvar (implode "A")))
                        (hol_Comb
                           (hol_Comb
                              (hol_Const (implode "==>")
                                 (Tyapp (implode "fun")
                                    [Tyapp (implode "bool") [];
                                     Tyapp (implode "fun")
                                       [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))
                              (hol_Comb
                                 (hol_Var b
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                               hol_Comb
                                 (hol_Var b
                                    (Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyvar (implode "B")]))
                                 (hol_Var (implode "x2") (Tyvar (implode "A")))))
                           (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                            hol_Var (implode "x2") (Tyvar (implode "A")))))))))`,
  SIMP[ACONV_def; RACONV; ALPHAVARS_def; equation_def; typeof_def; codomain_def;
       injectivity "char"]);;

let ACONV_ONTO_conext = prove
 (`!b. ACONV
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
                           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                            Tyapp (implode "bool") []]))
                     (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                        (hol_Var (implode "y") (Tyvar (implode "B")) ===
                         hol_Comb
                           (hol_Var (implode "f")
                              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                           (hol_Var (implode "x") (Tyvar (implode "A")))))))))
         (hol_Const (implode "ONTO")
            (Tyapp (implode "fun")
               [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
                Tyapp (implode "bool") []]) ===
          hol_Abs (hol_Var b (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
            (hol_Comb
               (hol_Const (implode "!")
                  (Tyapp (implode "fun")
                     [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
                      Tyapp (implode "bool") []]))
               (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
                  (hol_Comb
                     (hol_Const (implode "?")
                        (Tyapp (implode "fun")
                           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                            Tyapp (implode "bool") []]))
                     (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                        (hol_Var (implode "y") (Tyvar (implode "B")) ===
                         hol_Comb
                           (hol_Var b
                              (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                           (hol_Var (implode "x") (Tyvar (implode "A")))))))))`,
  SIMP[ACONV_def; RACONV; ALPHAVARS_def; equation_def; typeof_def; codomain_def;
       injectivity "char"]);;

(* HOL4 simplifies with VSUBST_def, deciding each guard of its conditional
   first; HOL Light's simplifier would also unfold the branches and loop, so
   VSUBST is unfolded one level at a time *)
let axioms_mk_infinity_ctxt_hl = prove
 (`!b1 b2 ctxt p.
     p IN set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                 (mk_infinity_ctxt_hl b1 b2 ctxt)))
     ==> ?q. q IN set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                       (conexts_of_upd upd))
                                         (mk_infinity_ctxt ctxt))) /\
             ACONV q p`,
  REWRITE_TAC[mk_infinity_ctxt_hl_def; mk_infinity_ctxt_def; conexts_of_upd_def; MAP; FLAT;
              APPEND; axexts_of_upd_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[MAP; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[VSUBST_def] THEN
                     SIMP[equation_def; REV_ASSOCD; typeof_def; codomain_def; FILTER; EX;
                          VFREE_IN_def])) THEN
  RW[] THENL
  [MESON_TAC[ACONV_REFL];
   IRULE_AT Any (SIMP_RULE[equation_def; typeof_def; codomain_def] ACONV_ONTO_conext) THEN
   SIMP[];
   IRULE_AT Any (SIMP_RULE[equation_def; typeof_def; codomain_def] ACONV_ONE_ONE_conext) THEN
   SIMP[];
   ASM_MESON_TAC[ACONV_REFL]]);;
let infinity_hl_has_model = prove
 (`is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf')
   ==> !ctxt i b1 b2.
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))) /\
         theory_ok
           ((alist_to_fmap (FLAT (MAP types_of_upd (mk_infinity_ctxt_hl b1 b2 ctxt))),
             alist_to_fmap (FLAT (MAP consts_of_upd (mk_infinity_ctxt_hl b1 b2 ctxt)))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd))
                                   (mk_infinity_ctxt_hl b1 b2 ctxt)))) /\
         is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
         DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
                  {implode "ONE_ONE", implode "ONTO"} /\
         ~(implode "ind" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
             alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) ctxt))) /\
         is_bool_interpretation0 mem i
         ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                            alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) i i' /\
                  models0 mem i'
                    ((alist_to_fmap (FLAT (MAP types_of_upd (mk_infinity_ctxt_hl b1 b2 ctxt))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (mk_infinity_ctxt_hl b1 b2 ctxt)))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd))
                                            (mk_infinity_ctxt_hl b1 b2 ctxt))))`,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  MP_TAC(SPEC `ctxt:update list`
           (UNDISCH(UNDISCH(ONCE_REWRITE_RULE[GSYM IMP_IMP] infinity_has_model)))) THEN
  ANTS_TAC THENL [FS[is_bool_sig_def]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ANTS_TAC THENL [FS[is_bool_interpretation0_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':(mlstring->U list->U)#(mlstring->U list->U)`
               STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i':(mlstring->U list->U)#(mlstring->U list->U)` THEN ASM_REWRITE_TAC[] THEN
  QBY "mk_infinity_ctxt ctxt extends ctxt"
    (MATCH_MP_TAC infinity_extends THEN
     FS[is_bool_sig_def; is_true_sig_def; is_and_sig_def; is_implies_sig_def;
        is_forall_sig_def; is_exists_sig_def; is_or_sig_def; is_false_sig_def;
        is_not_sig_def; IMAGE_CLAUSES]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP extends_theory_ok) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`i':(mlstring->U list->U)#(mlstring->U list->U)`; `mk_infinity_ctxt ctxt`;
                `mk_infinity_ctxt_hl b1 b2 ctxt`] (UNDISCH models_ACONV)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[sigof_mk_infinity_ctxt_hl] THEN ASM_MESON_TAC[axioms_mk_infinity_ctxt_hl];
   SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The context shapes a HOL Light session builds.  Everything the predicates *)
(* pin down is decidable on a printed context: the eight boolean definitions *)
(* on top of the initial context, the three axiom terms, the declaration of  *)
(* @ immediately below SELECT_AX, and the four updates of the infinity       *)
(* block.  Everything else is quantified over, and asked only not to assert *)
(* an axiom.                                                                 *)
(* ------------------------------------------------------------------------- *)

let fhol_light_ctxt_def = cake_def
  `fhol_light_ctxt ctxt <=>
     ?l2 l1 l0.
       ctxt = APPEND l2 (mk_select_ctxt_cl
                           (APPEND l1 (mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt))))) /\
       ALL (\u. !p. ~(u = hol_NewAxiom p)) (APPEND (APPEND l0 l1) l2)`;;

let hol_light_ctxt_def = cake_def
  `hol_light_ctxt ctxt <=>
     ?l3 l2 l1 l0 b1 b2.
       ctxt = APPEND l3 (mk_infinity_ctxt_hl b1 b2
                (APPEND l2 (mk_select_ctxt_cl
                   (APPEND l1 (mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt))))))) /\
       ALL (\u. !p. ~(u = hol_NewAxiom p)) (APPEND (APPEND (APPEND l0 l1) l2) l3)`;;

(* ------------------------------------------------------------------------- *)
(* Consistency                                                               *)
(* ------------------------------------------------------------------------- *)

(* the facts every cut point of the chain needs: it lies above the boolean
   definitions, so it is a good theory with a boolean signature, and any
   model of it interprets the boolean constants as intended *)

(* HOL4 gives the eight updates of mk_bool_ctxt as the witness *)
let CHLAUX_CONS_SUFFIX = prove
 (`!(x:A) l c. (?m. l = APPEND m c) ==> ?m. CONS x l = APPEND m c`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `CONS (x:A) m` THEN ASM_REWRITE_TAC[APPEND]);;

let mk_bool_ctxt_APPEND = prove
 (`!ctxt. ?m. mk_bool_ctxt ctxt = APPEND m ctxt`,
  GEN_TAC THEN REWRITE_TAC[mk_bool_ctxt_def] THEN
  REPEAT(MATCH_MP_TAC CHLAUX_CONS_SUFFIX) THEN
  EXISTS_TAC `[]:update list` THEN REWRITE_TAC[APPEND]);;

let extends_bool_suffix = prove
 (`!l. APPEND l (mk_bool_ctxt init_ctxt) extends init_ctxt
       ==> APPEND l (mk_bool_ctxt init_ctxt) extends mk_bool_ctxt init_ctxt`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC extends_suffix THEN
  EXISTS_TAC `init_ctxt` THEN ASM_REWRITE_TAC[mk_bool_ctxt_APPEND]);;

let suffix_facts_m = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !m i.
         APPEND m (mk_bool_ctxt init_ctxt) extends init_ctxt /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd (APPEND m (mk_bool_ctxt init_ctxt)))),
             alist_to_fmap (FLAT (MAP consts_of_upd (APPEND m (mk_bool_ctxt init_ctxt))))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                   (APPEND m (mk_bool_ctxt init_ctxt)))))
         ==> theory_ok
               ((alist_to_fmap (FLAT (MAP types_of_upd (APPEND m (mk_bool_ctxt init_ctxt)))),
                 alist_to_fmap (FLAT (MAP consts_of_upd (APPEND m (mk_bool_ctxt init_ctxt))))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd))
                                       (APPEND m (mk_bool_ctxt init_ctxt))))) /\
             is_bool_sig
               (alist_to_fmap (FLAT (MAP types_of_upd (APPEND m (mk_bool_ctxt init_ctxt)))),
                alist_to_fmap (FLAT (MAP consts_of_upd (APPEND m (mk_bool_ctxt init_ctxt))))) /\
             is_bool_interpretation0 mem i`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP extends_bool_suffix) THEN
  QBY "is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd init_ctxt)),
                    alist_to_fmap (FLAT (MAP consts_of_upd init_ctxt)))"
    (MP_TAC init_theory_ok THEN SIMP[theory_ok_def]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bool_has_bool_sig) THEN
  MP_TAC(MATCH_MP extends_theory_ok bool_extends_init) THEN
  REWRITE_TAC[init_theory_ok] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP extends_theory_ok o
    check (fun th -> rand(concl th) = `mk_bool_ctxt init_ctxt`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP is_bool_sig_extends o
    check (fun th -> rand(concl th) = `mk_bool_ctxt init_ctxt`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(GEN_ALL extends_is_bool_interpretation) THEN
  MAP_EVERY EXISTS_TAC [`init_ctxt`; `APPEND m (mk_bool_ctxt init_ctxt)`] THEN
  ASM_REWRITE_TAC[]);;

let suffix_facts = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !sfx i.
         sfx extends init_ctxt /\ (?m. sfx = APPEND m (mk_bool_ctxt init_ctxt)) /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd sfx)),
             alist_to_fmap (FLAT (MAP consts_of_upd sfx))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                 (conexts_of_upd upd)) sfx)))
         ==> theory_ok
               ((alist_to_fmap (FLAT (MAP types_of_upd sfx)),
                 alist_to_fmap (FLAT (MAP consts_of_upd sfx))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) sfx))) /\
             is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd sfx)),
                          alist_to_fmap (FLAT (MAP consts_of_upd sfx))) /\
             is_bool_interpretation0 mem i`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`m:update list`; `i:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH suffix_facts_m)) THEN
  ASM_REWRITE_TAC[]);;

let bool_ctxt_has_model = prove
 (`is_set_theory (mem:U->U->bool)
   ==> ?i. models0 mem i
             ((alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt init_ctxt))),
               alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt init_ctxt)))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                      (conexts_of_upd upd))
                                     (mk_bool_ctxt init_ctxt))))`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `i:(mlstring->U list->U)#(mlstring->U list->U)` o
              MATCH_MP init_ctxt_has_model) THEN
  MP_TAC(SPECL [`init_ctxt`; `mk_bool_ctxt init_ctxt`] (UNDISCH extends_consistent)) THEN
  REWRITE_TAC[bool_extends_init] THEN
  DISCH_THEN(MP_TAC o SPEC `i:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  ASM_REWRITE_TAC[init_theory_ok] THEN ANTS_TAC THENL
  [REWRITE_TAC[mk_bool_ctxt_def; init_ctxt_def; MEM; distinctness "update"];
   MESON_TAC[]]);;

let climb_axiom_free = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !l sfx i.
         APPEND l sfx extends sfx /\ sfx extends init_ctxt /\
         ALL (\u. !p. ~(u = hol_NewAxiom p)) l /\
         models0 mem i
           ((alist_to_fmap (FLAT (MAP types_of_upd sfx)),
             alist_to_fmap (FLAT (MAP consts_of_upd sfx))),
            set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                    (conexts_of_upd upd)) sfx)))
         ==> ?i'. models0 mem i'
                    ((alist_to_fmap (FLAT (MAP types_of_upd (APPEND l sfx))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (APPEND l sfx)))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd))
                                            (APPEND l sfx))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP extends_theory_ok (ASSUME `sfx extends init_ctxt`)) THEN
  REWRITE_TAC[init_theory_ok] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`l:update list`; `sfx:update list`;
                `i:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH models_axiom_free_segment)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let bool_ctxt_suffix_init = prove
 (`!mk. ?m. APPEND mk (mk_bool_ctxt init_ctxt) = APPEND m init_ctxt`,
  GEN_TAC THEN STRIP_ASSUME_TAC(SPEC `init_ctxt` mk_bool_ctxt_APPEND) THEN
  EXISTS_TAC `APPEND mk m:update list` THEN ASM_REWRITE_TAC[APPEND_ASSOC]);;

let chain_cut = prove
 (`!l mk.
     APPEND l (APPEND mk (mk_bool_ctxt init_ctxt)) extends init_ctxt
     ==> APPEND l (APPEND mk (mk_bool_ctxt init_ctxt)) extends
           APPEND mk (mk_bool_ctxt init_ctxt) /\
         APPEND mk (mk_bool_ctxt init_ctxt) extends init_ctxt`,
  REPEAT STRIP_TAC THENL
  [MP_TAC(SPECL [`l:update list`; `APPEND mk (mk_bool_ctxt init_ctxt)`; `init_ctxt`]
            extends_suffix);
   MP_TAC(SPECL [`l:update list`; `APPEND mk (mk_bool_ctxt init_ctxt)`; `init_ctxt`]
            extends_suffix_below)] THEN
  ASM_REWRITE_TAC[bool_ctxt_suffix_init]);;

(* every cut point of the chain is again of the form "something on top of the
   boolean definitions", so one lemma recognises them all *)

let above_bool = prove
 (`(?m. mk_bool_ctxt init_ctxt = APPEND m (mk_bool_ctxt init_ctxt)) /\
   (!X l. (?m. X = APPEND m (mk_bool_ctxt init_ctxt))
          ==> ?m. APPEND l X = APPEND m (mk_bool_ctxt init_ctxt)) /\
   (!X u. (?m. X = APPEND m (mk_bool_ctxt init_ctxt))
          ==> ?m. CONS u X = APPEND m (mk_bool_ctxt init_ctxt))`,
  REPEAT STRIP_TAC THENL
  [EXISTS_TAC `[]:update list` THEN REWRITE_TAC[APPEND];
   EXISTS_TAC `APPEND l m:update list` THEN ASM_REWRITE_TAC[APPEND_ASSOC];
   EXISTS_TAC `CONS u m:update list` THEN ASM_REWRITE_TAC[APPEND]]);;

let chain_cut2 = prove
 (`!l base.
     APPEND l base extends init_ctxt /\ (?m. base = APPEND m (mk_bool_ctxt init_ctxt))
     ==> APPEND l base extends base /\ base extends init_ctxt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`l:update list`; `m:update list`] chain_cut) THEN ASM_REWRITE_TAC[]);;

let chain_cut_CONS = prove
 (`!u base m.
     CONS u base extends init_ctxt /\ base = APPEND m (mk_bool_ctxt init_ctxt)
     ==> CONS u base extends base /\ base extends init_ctxt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`[u:update]`; `base:update list`] chain_cut2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND] THEN ASM_MESON_TAC[]; REWRITE_TAC[APPEND]]);;

let cut_eta = prove
 (`!X. mk_eta_ctxt_cl X extends init_ctxt /\ (?m. X = APPEND m (mk_bool_ctxt init_ctxt))
       ==> mk_eta_ctxt_cl X extends X /\ X extends init_ctxt`,
  GEN_TAC THEN REWRITE_TAC[mk_eta_ctxt_cl_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC chain_cut_CONS THEN ASM_MESON_TAC[]);;

let cut_select = prove
 (`!X. mk_select_ctxt_cl X extends init_ctxt /\ (?m. X = APPEND m (mk_bool_ctxt init_ctxt))
       ==> mk_select_ctxt_cl X extends X /\ X extends init_ctxt /\
           ~(implode "@" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd X))))`,
  GEN_TAC THEN STRIP_TAC THEN
  QBY "?m. CONS (hol_NewConst (implode \"@\")
                   (Tyapp (implode \"fun\")
                      [Tyapp (implode \"fun\") [Tyvar (implode \"A\"); Tyapp (implode \"bool\") []];
                       Tyvar (implode \"A\")])) X = APPEND m (mk_bool_ctxt init_ctxt)"
    (ASM_MESON_TAC[above_bool]) THEN
  QPAT_X_ASSUM "_ extends init_ctxt" (MP_TAC o REWRITE_RULE[mk_select_ctxt_cl_def]) THEN
  STRIP_TAC THEN
  DRULE_ALL chain_cut_CONS THEN STRIP_TAC THEN
  DRULE_ALL chain_cut_CONS THEN STRIP_TAC THEN
  QBY "?m. X = APPEND m init_ctxt" (ASM_MESON_TAC[bool_ctxt_suffix_init]) THEN
  DRULE_ALL extends_CONS THEN STRIP_TAC THEN
  REWRITE_TAC[mk_select_ctxt_cl_def] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[extends_trans]; ALL_TAC] THEN
  QPAT_X_ASSUM "hol_NewConst _ _ updates _" MP_TAC THEN SIMP[ONCE updates_cases]);;

let chain_cut_CONS4 = prove
 (`!u1 u2 u3 u4 base m.
     CONS u1 (CONS u2 (CONS u3 (CONS u4 base))) extends init_ctxt /\
     base = APPEND m (mk_bool_ctxt init_ctxt)
     ==> CONS u1 (CONS u2 (CONS u3 (CONS u4 base))) extends base /\
         base extends init_ctxt /\
         u4 updates base /\ u3 updates CONS u4 base /\ u2 updates CONS u3 (CONS u4 base)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u1:update`; `CONS u2 (CONS u3 (CONS u4 base)):update list`;
                `CONS u2 (CONS u3 (CONS u4 m)):update list`] chain_cut_CONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND]; STRIP_TAC] THEN
  MP_TAC(SPECL [`u2:update`; `CONS u3 (CONS u4 base):update list`;
                `CONS u3 (CONS u4 m):update list`] chain_cut_CONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND]; STRIP_TAC] THEN
  MP_TAC(SPECL [`u3:update`; `CONS u4 base:update list`; `CONS u4 m:update list`]
           chain_cut_CONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND]; STRIP_TAC] THEN
  MP_TAC(SPECL [`u4:update`; `base:update list`; `m:update list`] chain_cut_CONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND]; STRIP_TAC] THEN
  SUBGOAL_THEN `?k1. base = APPEND k1 init_ctxt` STRIP_ASSUME_TAC THENL
  [MP_TAC(SPEC `m:update list` bool_ctxt_suffix_init) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`u4:update`; `base:update list`; `init_ctxt`; `k1:update list`]
           extends_CONS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`u3:update`; `CONS u4 base:update list`; `init_ctxt`;
                `CONS u4 k1:update list`] extends_CONS) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                   REWRITE_TAC[APPEND; CONS_11] THEN FIRST_ASSUM ACCEPT_TAC];
   STRIP_TAC] THEN
  MP_TAC(SPECL [`u2:update`; `CONS u3 (CONS u4 base):update list`; `init_ctxt`;
                `CONS u3 (CONS u4 k1):update list`] extends_CONS) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                   REWRITE_TAC[APPEND; CONS_11] THEN FIRST_ASSUM ACCEPT_TAC];
   STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC extends_trans THEN
  EXISTS_TAC `CONS u2 (CONS u3 (CONS u4 base)):update list` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC extends_trans THEN EXISTS_TAC `CONS u3 (CONS u4 base):update list` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC extends_trans THEN EXISTS_TAC `CONS u4 base:update list` THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let cut_infinity = prove
 (`!X b1 b2.
     mk_infinity_ctxt_hl b1 b2 X extends init_ctxt /\
     (?m. X = APPEND m (mk_bool_ctxt init_ctxt))
     ==> mk_infinity_ctxt_hl b1 b2 X extends X /\ X extends init_ctxt /\
         ~(implode "ind" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd X)))) /\
         DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd X))))
                  {implode "ONE_ONE", implode "ONTO"}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "_ extends init_ctxt" (MP_TAC o REWRITE_RULE[mk_infinity_ctxt_hl_def]) THEN
  STRIP_TAC THEN DRULE_ALL chain_cut_CONS4 THEN STRIP_TAC THEN
  QPAT_X_ASSUM "X = _" (K ALL_TAC) THEN
  REWRITE_TAC[mk_infinity_ctxt_hl_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP updates_DISJOINT)) THEN
  REWRITE_TAC[MAP; FLAT; types_of_upd_def; consts_of_upd_def; APPEND; FDOM_alist_to_fmap;
              MAP_APPEND; SET_OF_LIST_APPEND; FST; set_of_list] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[MAP; FST; set_of_list] THEN
  SET_TAC[]);;

let fhol_light_has_model = prove
 (`is_set_theory (mem:U->U->bool)
   ==> !ctxt. ctxt extends init_ctxt /\ fhol_light_ctxt ctxt
              ==> theory_ok
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd)) ctxt))) /\
                  ?i. models0 mem i
                        ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                                 (conexts_of_upd upd)) ctxt)))`,
  DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP extends_theory_ok) THEN REWRITE_TAC[init_theory_ok] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "fhol_light_ctxt _" (STRIP_ASSUME_TAC o REWRITE_RULE[fhol_light_ctxt_def]) THEN
  QPAT_X_ASSUM "ctxt = _" SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "ALL _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[ALL_APPEND]) THEN
  (* peel the chain apart from the top *)
  MP_TAC(SPECL [`l2:update list`;
                `mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                   (APPEND l0 (mk_bool_ctxt init_ctxt))))`] chain_cut2) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[mk_select_ctxt_cl_def; mk_eta_ctxt_cl_def] THEN MESON_TAC[above_bool]];
   STRIP_TAC] THEN
  MP_TAC(SPEC `APPEND l1 (mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt)))`
           cut_select) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[mk_eta_ctxt_cl_def] THEN MESON_TAC[above_bool]];
   STRIP_TAC] THEN
  MP_TAC(SPECL [`l1:update list`;
                `mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt))`] chain_cut2) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[mk_eta_ctxt_cl_def] THEN MESON_TAC[above_bool]];
   STRIP_TAC] THEN
  MP_TAC(SPEC `APPEND l0 (mk_bool_ctxt init_ctxt)` cut_eta) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[above_bool]]; STRIP_TAC] THEN
  MP_TAC(SPECL [`l0:update list`; `mk_bool_ctxt init_ctxt`] chain_cut2) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[above_bool]]; STRIP_TAC] THEN
  (* climb, building the model *)
  MP_TAC(UNDISCH bool_ctxt_has_model) THEN
  DISCH_THEN(X_CHOOSE_TAC `j0:(mlstring->U list->U)#(mlstring->U list->U)`) THEN
  MP_TAC(SPECL [`l0:update list`; `mk_bool_ctxt init_ctxt`;
                `j0:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH climb_axiom_free)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[];
   DISCH_THEN(X_CHOOSE_TAC `j1:(mlstring->U list->U)#(mlstring->U list->U)`)] THEN
  MP_TAC(SPECL [`APPEND l0 (mk_bool_ctxt init_ctxt)`;
                `j1:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH suffix_facts)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MESON_TAC[above_bool]; STRIP_TAC] THEN
  MP_TAC(SPECL [`APPEND l0 (mk_bool_ctxt init_ctxt)`;
                `j1:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH eta_cl_has_model)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`l1:update list`; `mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt))`;
                `j1:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH climb_axiom_free)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[];
   DISCH_THEN(X_CHOOSE_TAC `j2:(mlstring->U list->U)#(mlstring->U list->U)`)] THEN
  MP_TAC(SPECL [`APPEND l1 (mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt)))`;
                `j2:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH suffix_facts)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_eta_ctxt_cl_def] THEN MESON_TAC[above_bool];
   STRIP_TAC] THEN
  MP_TAC(SPECL [`APPEND l1 (mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt init_ctxt)))`;
                `j2:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH select_cl_has_model)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[];
   DISCH_THEN(X_CHOOSE_THEN `j3:(mlstring->U list->U)#(mlstring->U list->U)`
                STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`l2:update list`;
                `mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                   (APPEND l0 (mk_bool_ctxt init_ctxt))))`;
                `j3:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH climb_axiom_free)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]
);;

let hol_light_has_model = prove
 (`is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf')
   ==> !ctxt. ctxt extends init_ctxt /\ hol_light_ctxt ctxt
              ==> theory_ok
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd)) ctxt))) /\
                  ?i. models0 mem i
                        ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                                 (conexts_of_upd upd)) ctxt)))`,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP extends_theory_ok) THEN REWRITE_TAC[init_theory_ok] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "hol_light_ctxt _" (STRIP_ASSUME_TAC o REWRITE_RULE[hol_light_ctxt_def]) THEN
  QPAT_X_ASSUM "ctxt = _" SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "ALL _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[ALL_APPEND]) THEN
  MP_TAC(SPECL [`l3:update list`;
                `mk_infinity_ctxt_hl b1 b2
                   (APPEND l2 (mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                      (APPEND l0 (mk_bool_ctxt init_ctxt))))))`] chain_cut2) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[mk_infinity_ctxt_hl_def; mk_select_ctxt_cl_def; mk_eta_ctxt_cl_def] THEN
    MESON_TAC[above_bool]];
   STRIP_TAC] THEN
  MP_TAC(SPECL [`APPEND l2 (mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                   (APPEND l0 (mk_bool_ctxt init_ctxt)))))`;
                `b1:mlstring`; `b2:mlstring`] cut_infinity) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[mk_select_ctxt_cl_def; mk_eta_ctxt_cl_def] THEN MESON_TAC[above_bool]];
   STRIP_TAC] THEN
  QPAT_ASSUM "mk_infinity_ctxt_hl _ _ _ extends init_ctxt"
    (MP_TAC o MATCH_MP extends_theory_ok) THEN
  REWRITE_TAC[init_theory_ok] THEN DISCH_TAC THEN
  MP_TAC(SPEC `APPEND l2 (mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                 (APPEND l0 (mk_bool_ctxt init_ctxt)))))`
           (UNDISCH fhol_light_has_model)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[fhol_light_ctxt_def] THEN
   MAP_EVERY EXISTS_TAC [`l2:update list`; `l1:update list`; `l0:update list`] THEN
   ASM_REWRITE_TAC[ALL_APPEND];
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_TAC `k0:(mlstring->U list->U)#(mlstring->U list->U)`))] THEN
  MP_TAC(SPECL [`APPEND l2 (mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                   (APPEND l0 (mk_bool_ctxt init_ctxt)))))`;
                `k0:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH suffix_facts)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[mk_select_ctxt_cl_def; mk_eta_ctxt_cl_def] THEN
   MESON_TAC[above_bool];
   STRIP_TAC] THEN
  MP_TAC(SPECL [`APPEND l2 (mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                   (APPEND l0 (mk_bool_ctxt init_ctxt)))))`;
                `k0:(mlstring->U list->U)#(mlstring->U list->U)`;
                `b1:mlstring`; `b2:mlstring`]
           (UNDISCH(UNDISCH(ONCE_REWRITE_RULE[GSYM IMP_IMP] infinity_hl_has_model)))) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[];
   DISCH_THEN(X_CHOOSE_THEN `k1:(mlstring->U list->U)#(mlstring->U list->U)`
                STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`l3:update list`;
                `mk_infinity_ctxt_hl b1 b2
                   (APPEND l2 (mk_select_ctxt_cl (APPEND l1 (mk_eta_ctxt_cl
                      (APPEND l0 (mk_bool_ctxt init_ctxt))))))`;
                `k1:(mlstring->U list->U)#(mlstring->U list->U)`]
           (UNDISCH climb_axiom_free)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]
);;

let init_light_consistent = prove
 (`!ctxt. ctxt extends init_ctxt /\ ALL (\u. !p. ~(u = hol_NewAxiom p)) ctxt
          ==> consistent_theory
                ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                         (conexts_of_upd upd)) ctxt)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `V_mem:A V->A V->bool` (GEN `mem:U->U->bool` min_hol_consistent)) THEN
  REWRITE_TAC[is_set_theory_V] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FS[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let fhol_light_consistent = prove
 (`!ctxt. ctxt extends init_ctxt /\ fhol_light_ctxt ctxt
          ==> consistent_theory
                ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                 set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                         (conexts_of_upd upd)) ctxt)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `V_mem:A V->A V->bool` (GEN `mem:U->U->bool` proves_consistent)) THEN
  REWRITE_TAC[is_set_theory_V] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `V_mem:A V->A V->bool` (GEN `mem:U->U->bool` fhol_light_has_model)) THEN
  REWRITE_TAC[is_set_theory_V] THEN
  DISCH_THEN(MP_TAC o SPEC `ctxt:update list`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let hol_light_consistent = prove
 (`(?inf'. is_infinite (V_mem:A V->A V->bool) inf')
   ==> !ctxt. ctxt extends init_ctxt /\ hol_light_ctxt ctxt
              ==> consistent_theory
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                             (conexts_of_upd upd)) ctxt)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `V_mem:A V->A V->bool` (GEN `mem:U->U->bool` proves_consistent)) THEN
  REWRITE_TAC[is_set_theory_V] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `V_mem:A V->A V->bool` (GEN `mem:U->U->bool` hol_light_has_model)) THEN
  REWRITE_TAC[is_set_theory_V] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ctxt:update list`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The shapes are realisable.  The results above are conditional on a        *)
(* context both extending init_ctxt and having one of the shapes, and        *)
(* nothing so far rules out those two conditions being jointly              *)
(* unsatisfiable, which would leave the results true but empty.  So exhibit  *)
(* a context of each shape that really is a definitional extension of the    *)
(* initial context.  The measured context below says more, since it is a     *)
(* context a session actually reached, but it is compared against a          *)
(* translation of the kernel printout prepared outside the logic; these      *)
(* three owe nothing to anything outside it.                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 proves the axiom updates of the next two theorems inline with
   term_ok_Forall and metis; here once for all *)
let CHLAUX_NewAxiom_Forall_updates = prove
 (`!ctxt nm ty p.
     is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     is_forall_sig (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) ty /\
     hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) p /\
     typeof p = Tyapp (implode "bool") []
     ==> hol_NewAxiom
           (hol_Comb
              (hol_Const (implode "!")
                 (Tyapp (implode "fun")
                    [Tyapp (implode "fun") [ty; Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var nm ty) p))
         updates ctxt`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (el 0 (CONJUNCTS updates_rules)) THEN
  MP_TAC(ISPECL [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                   alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`;
                 `nm:mlstring`; `ty:hol_type`; `p:hol_term`] term_ok_Forall) THEN
  ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[term_ok_welltyped; WELLTYPED]);;

let eta_cl_extends = prove
 (`!ctxt. is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
          ==> mk_eta_ctxt_cl ctxt extends ctxt`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  REWRITE_TAC[mk_eta_ctxt_cl_def] THEN MATCH_MP_TAC extends_CONS_I THEN
  REWRITE_TAC[extends_def; RTC_REFL] THEN
  MATCH_MP_TAC CHLAUX_NewAxiom_Forall_updates THEN
  FS[is_bool_sig_def; is_std_sig_def; type_ok_def; term_ok_equation; hol_term_ok_def;
     equation_def; typeof_def; codomain_def]);;

let select_cl_extends = prove
 (`!ctxt. is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
          ~(implode "@" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
          ==> mk_select_ctxt_cl ctxt extends ctxt`,
  GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  SUBGOAL_THEN
    `CONS (hol_NewConst (implode "@")
             (Tyapp (implode "fun")
                [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                 Tyvar (implode "A")])) ctxt extends ctxt` ASSUME_TAC THENL
  [MATCH_MP_TAC extends_CONS_I THEN REWRITE_TAC[extends_def; RTC_REFL] THEN
   MATCH_MP_TAC (el 1 (CONJUNCTS updates_rules)) THEN ASM_REWRITE_TAC[] THEN
   FS[type_ok_def; is_std_sig_def];
   ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MATCH_MP is_bool_sig_extends th))) THEN
  REWRITE_TAC[mk_select_ctxt_cl_def] THEN MATCH_MP_TAC extends_CONS_I THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CHLAUX_NewAxiom_Forall_updates THEN
  CONJ_TAC THENL [FS[is_bool_sig_def]; ALL_TAC] THEN
  CONJ_TAC THENL [FS[is_bool_sig_def]; ALL_TAC] THEN
  CONJ_TAC THENL [FS[is_bool_sig_def; is_std_sig_def; type_ok_def]; ALL_TAC] THEN
  MATCH_MP_TAC term_ok_Forall THEN
  FS[is_bool_sig_def; is_std_sig_def; is_forall_sig_def; is_implies_sig_def; type_ok_def;
     hol_term_ok_def; typeof_def; codomain_def;
     WELLTYPED_CLAUSES; FLOOKUP_UPDATE; alist_to_fmap_thm; MAP; FLAT; APPEND]);;

(* the two definitions of the infinity block, over any bool signature that
   has not used their names, in particular over one that has already
   declared ind, which is where HOL Light puts them *)

let ONE_ONE_def_updates = prove
 (`!b ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     ~(implode "ONE_ONE" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
     ==> (hol_ConstSpec
            [(implode "ONE_ONE",
              hol_Abs
                (hol_Var b (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                                           [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))
                                  (hol_Comb
                                     (hol_Var b
                                        (Tyapp (implode "fun")
                                           [Tyvar (implode "A"); Tyvar (implode "B")]))
                                     (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                   hol_Comb
                                     (hol_Var b
                                        (Tyapp (implode "fun")
                                           [Tyvar (implode "A"); Tyvar (implode "B")]))
                                     (hol_Var (implode "x2") (Tyvar (implode "A")))))
                               (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                                hol_Var (implode "x2") (Tyvar (implode "A")))))))))]
            (hol_Var (implode "ONE_ONE")
               (typeof
                  (hol_Abs
                     (hol_Var b
                        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                     (hol_Comb
                        (hol_Const (implode "!")
                           (Tyapp (implode "fun")
                              [Tyapp (implode "fun")
                                 [Tyvar (implode "A"); Tyapp (implode "bool") []];
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
                                       (hol_Comb
                                          (hol_Var b
                                             (Tyapp (implode "fun")
                                                [Tyvar (implode "A"); Tyvar (implode "B")]))
                                          (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                        hol_Comb
                                          (hol_Var b
                                             (Tyapp (implode "fun")
                                                [Tyvar (implode "A"); Tyvar (implode "B")]))
                                          (hol_Var (implode "x2") (Tyvar (implode "A")))))
                                    (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                                     hol_Var (implode "x2") (Tyvar (implode "A")))))))))) ===
             hol_Abs
               (hol_Var b (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                                          [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))
                                 (hol_Comb
                                    (hol_Var b
                                       (Tyapp (implode "fun")
                                          [Tyvar (implode "A"); Tyvar (implode "B")]))
                                    (hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                  hol_Comb
                                    (hol_Var b
                                       (Tyapp (implode "fun")
                                          [Tyvar (implode "A"); Tyvar (implode "B")]))
                                    (hol_Var (implode "x2") (Tyvar (implode "A")))))
                              (hol_Var (implode "x1") (Tyvar (implode "A")) ===
                               hol_Var (implode "x2") (Tyvar (implode "A"))))))))))
         updates ctxt`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  MATCH_MP_TAC ConstDef_updates THEN
  SIMP[CLOSED_def; tvars_def; tyvars_def; equation_def; hol_term_ok_def; type_ok_def;
       typeof_def; codomain_def] THEN
  FS[is_bool_sig_def; is_std_sig_def; is_forall_sig_def; is_implies_sig_def] THEN
  CONJ_TAC THENL
  [EXISTS_TAC `[(Tyvar (implode "B"),Tyvar (implode "A"))]` THEN REWRITE_TAC[REV_ASSOCD];
   MESON_TAC[]]);;

let ONTO_def_updates = prove
 (`!b ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     ~(implode "ONTO" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
     ==> (hol_ConstSpec
            [(implode "ONTO",
              hol_Abs
                (hol_Var b (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                            (hol_Var (implode "y") (Tyvar (implode "B")) ===
                             hol_Comb
                               (hol_Var b
                                  (Tyapp (implode "fun")
                                     [Tyvar (implode "A"); Tyvar (implode "B")]))
                               (hol_Var (implode "x") (Tyvar (implode "A")))))))))]
            (hol_Var (implode "ONTO")
               (typeof
                  (hol_Abs
                     (hol_Var b
                        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                     (hol_Comb
                        (hol_Const (implode "!")
                           (Tyapp (implode "fun")
                              [Tyapp (implode "fun")
                                 [Tyvar (implode "B"); Tyapp (implode "bool") []];
                               Tyapp (implode "bool") []]))
                        (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
                           (hol_Comb
                              (hol_Const (implode "?")
                                 (Tyapp (implode "fun")
                                    [Tyapp (implode "fun")
                                       [Tyvar (implode "A"); Tyapp (implode "bool") []];
                                     Tyapp (implode "bool") []]))
                              (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                                 (hol_Var (implode "y") (Tyvar (implode "B")) ===
                                  hol_Comb
                                    (hol_Var b
                                       (Tyapp (implode "fun")
                                          [Tyvar (implode "A"); Tyvar (implode "B")]))
                                    (hol_Var (implode "x") (Tyvar (implode "A")))))))))) ===
             hol_Abs
               (hol_Var b (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                           (hol_Var (implode "y") (Tyvar (implode "B")) ===
                            hol_Comb
                              (hol_Var b
                                 (Tyapp (implode "fun")
                                    [Tyvar (implode "A"); Tyvar (implode "B")]))
                              (hol_Var (implode "x") (Tyvar (implode "A"))))))))))
         updates ctxt`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  MATCH_MP_TAC ConstDef_updates THEN
  SIMP[CLOSED_def; tvars_def; tyvars_def; equation_def; hol_term_ok_def; type_ok_def;
       typeof_def; codomain_def] THEN
  FS[is_bool_sig_def; is_std_sig_def; is_forall_sig_def; is_exists_sig_def] THEN
  CONJ_TAC THENL
  [EXISTS_TAC `[(Tyvar (implode "B"),Tyvar (implode "A"))]` THEN REWRITE_TAC[REV_ASSOCD];
   MESON_TAC[]]);;

(* INFINITY_AX is well formed as soon as ind and the two constants are
   there, whatever the definitions bound them with *)

let infinity_ax_updates = prove
 (`!ctxt.
     is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "ONE_ONE") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []]) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "ONTO") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
              Tyapp (implode "bool") []]) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) (implode "ind") = SOME 0
     ==> (hol_NewAxiom
            (hol_Comb
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
                                          [Tyapp (implode "ind") []; Tyapp (implode "ind") []]));
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
                                          [Tyapp (implode "ind") []; Tyapp (implode "ind") []]));
                                  Tyapp (implode "bool") []]))
                           (hol_Var (implode "f")
                              (Tyapp (implode "fun")
                                 [Tyapp (implode "ind") []; Tyapp (implode "ind") []]))))))))
         updates ctxt`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  MATCH_MP_TAC (el 0 (CONJUNCTS updates_rules)) THEN
  CONJ_TAC THENL [REPEAT(SIMP[ONCE has_type_cases]); ALL_TAC] THEN
  SIMP[hol_term_ok_def; type_ok_def; typeof_def; codomain_def] THEN
  FS[is_bool_sig_def; is_std_sig_def; is_and_sig_def; is_not_sig_def; is_exists_sig_def] THEN
  CONJ_TAC THENL
  [EXISTS_TAC `[(Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind") []],
                 Tyvar (implode "A"))]` THEN REWRITE_TAC[REV_ASSOCD];
   EXISTS_TAC `[(Tyapp (implode "ind") [],Tyvar (implode "A"));
                (Tyapp (implode "ind") [],Tyvar (implode "B"))]` THEN
   SIMP[REV_ASSOCD; injectivity "char"]]);;

(* one more update over a bool signature: the three facts HOL4 derives after
   each update of infinity_hl_extends *)
let CHLAUX_bool_updates_step = prove
 (`!u c ctxt.
     c extends ctxt /\
     is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd c)),
                 alist_to_fmap (FLAT (MAP consts_of_upd c))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) c))) /\
     u updates c
     ==> CONS u c extends ctxt /\
         theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd (CONS u c))),
                     alist_to_fmap (FLAT (MAP consts_of_upd (CONS u c)))),
                    set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                         (conexts_of_upd upd))
                                           (CONS u c)))) /\
         is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd (CONS u c))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (CONS u c))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CONS (u:update) c extends ctxt` ASSUME_TAC THENL
  [MATCH_MP_TAC extends_CONS_I THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[updates_theory_ok]; ASM_MESON_TAC[is_bool_sig_extends]]);;

let infinity_hl_extends = prove
 (`!b1 b2 ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
              {implode "ONE_ONE", implode "ONTO"} /\
     ~(implode "ind" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt))))
     ==> mk_infinity_ctxt_hl b1 b2 ctxt extends ctxt`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_bool_sig_std) THEN
  (* the type of individuals, declared first *)
  QBY "hol_NewType (implode \"ind\") 0 updates ctxt" (FS[ONCE updates_cases]) THEN
  QBY "CONS (hol_NewType (implode \"ind\") 0) ctxt extends ctxt"
    (IRULE extends_CONS_I THEN ASM_REWRITE_TAC[extends_def; RTC_REFL]) THEN
  QBY "theory_ok
         ((alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewType (implode \"ind\") 0) ctxt))),
           alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewType (implode \"ind\") 0) ctxt)))),
          set_of_list (FLAT (MAP (\\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                                 (CONS (hol_NewType (implode \"ind\") 0) ctxt))))"
    (ASM_MESON_TAC[updates_theory_ok]) THEN
  QBY "is_bool_sig
         (alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewType (implode \"ind\") 0) ctxt))),
          alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewType (implode \"ind\") 0) ctxt))))"
    (ASM_MESON_TAC[is_bool_sig_extends]) THEN
  (* then the two definitions, over a signature that already has ind *)
  MP_TAC(SPECL [`b1:mlstring`; `CONS (hol_NewType (implode "ind") 0) ctxt`]
           ONE_ONE_def_updates) THEN
  ANTS_TAC THENL [FS[IN_DISJOINT] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  MATCH_ASMSUB_ABBREV_TAC "u1 updates CONS (hol_NewType (implode \"ind\") 0) ctxt" THEN
  MP_TAC(SPECL [`u1:update`; `CONS (hol_NewType (implode "ind") 0) ctxt`;
                `ctxt:update list`] CHLAUX_bool_updates_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b2:mlstring`; `CONS u1 (CONS (hol_NewType (implode "ind") 0) ctxt)`]
           ONTO_def_updates) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "u1" THEN FS[IN_DISJOINT] THEN ASM_MESON_TAC[];
   DISCH_TAC] THEN
  MATCH_ASMSUB_ABBREV_TAC "u2 updates CONS u1 (CONS (hol_NewType (implode \"ind\") 0) ctxt)" THEN
  MP_TAC(SPECL [`u2:update`; `CONS u1 (CONS (hol_NewType (implode "ind") 0) ctxt)`;
                `ctxt:update list`] CHLAUX_bool_updates_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* and finally the axiom *)
  MP_TAC(SPEC `CONS u2 (CONS u1 (CONS (hol_NewType (implode "ind") 0) ctxt))`
           infinity_ax_updates) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "u1" THEN EXPAND_TAC "u2" THEN
   SIMP[FLOOKUP_UPDATE; alist_to_fmap_thm; typeof_def; codomain_def];
   DISCH_TAC] THEN
  REWRITE_TAC[mk_infinity_ctxt_hl_def] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC extends_CONS_I THEN ASM_REWRITE_TAC[]);;

let init_light_nonempty = prove
 (`?ctxt. ctxt extends init_ctxt /\ ALL (\u. !p. ~(u = hol_NewAxiom p)) ctxt`,
  EXISTS_TAC `init_ctxt` THEN REWRITE_TAC[extends_def; RTC_REFL] THEN
  REWRITE_TAC[init_ctxt_def] THEN SIMP[]);;

(* the shapes with nothing interleaved anywhere *)

(* HOL4 decides these lookups with EVAL_TAC *)
let CHLAUX_STR_TAC =
  REWRITE_TAC[mk_select_ctxt_cl_def; mk_eta_ctxt_cl_def; mk_bool_ctxt_def; init_ctxt_def;
              MAP; FLAT; APPEND; consts_of_upd_def; types_of_upd_def; FDOM_alist_to_fmap;
              set_of_list; IN_INSERT; NOT_IN_EMPTY; DISJOINT_INSERT; DISJOINT_EMPTY;
              IN_DISJOINT] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[MAP; FST; set_of_list; IN_INSERT; NOT_IN_EMPTY; injectivity "mlstring"] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];;

let fhol_light_base_extends = prove
 (`mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)) extends init_ctxt /\
   is_bool_sig
     (alist_to_fmap (FLAT (MAP types_of_upd
        (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))))),
      alist_to_fmap (FLAT (MAP consts_of_upd
        (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))))))`,
  QBY "is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd init_ctxt)),
                    alist_to_fmap (FLAT (MAP consts_of_upd init_ctxt)))"
    (MP_TAC init_theory_ok THEN SIMP[theory_ok_def]) THEN
  QBY "is_bool_sig (alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt init_ctxt))),
                     alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt init_ctxt))))"
    (ASM_MESON_TAC[bool_has_bool_sig]) THEN
  QBY "mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt) extends mk_bool_ctxt init_ctxt"
    (ASM_MESON_TAC[eta_cl_extends]) THEN
  QBY "is_bool_sig
         (alist_to_fmap (FLAT (MAP types_of_upd (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))),
          alist_to_fmap (FLAT (MAP consts_of_upd (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))))"
    (ASM_MESON_TAC[is_bool_sig_extends]) THEN
  QBY "~(implode \"@\" IN
         FDOM (alist_to_fmap (FLAT (MAP consts_of_upd
                 (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))))))"
    CHLAUX_STR_TAC THEN
  QBY "mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)) extends
       mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)" (ASM_MESON_TAC[select_cl_extends]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[extends_trans; bool_extends_init]; ALL_TAC] THEN
  ASM_MESON_TAC[is_bool_sig_extends; bool_extends_init; extends_trans]);;

let fhol_light_nonempty = prove
 (`?ctxt. ctxt extends init_ctxt /\ fhol_light_ctxt ctxt`,
  EXISTS_TAC `mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))` THEN
  REWRITE_TAC[fhol_light_base_extends; fhol_light_ctxt_def] THEN
  MAP_EVERY EXISTS_TAC [`[]:update list`; `[]:update list`; `[]:update list`] THEN
  REWRITE_TAC[APPEND; ALL]);;

let hol_light_nonempty = prove
 (`?ctxt. ctxt extends init_ctxt /\ hol_light_ctxt ctxt`,
  EXISTS_TAC `mk_infinity_ctxt_hl (implode "b1") (implode "b2")
                (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))` THEN
  ASSUME_TAC fhol_light_base_extends THEN
  QBY "theory_ok
         ((alist_to_fmap (FLAT (MAP types_of_upd
             (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))))),
           alist_to_fmap (FLAT (MAP consts_of_upd
             (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))))),
          set_of_list (FLAT (MAP (\\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
            (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))))))"
    (ASM_MESON_TAC[extends_theory_ok; init_theory_ok]) THEN
  QBY "DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd
                  (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))))))
                {implode \"ONE_ONE\", implode \"ONTO\"}"
    (ONCE_REWRITE_TAC[DISJOINT_SYM] THEN CHLAUX_STR_TAC) THEN
  QBY "~(implode \"ind\" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd
                  (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))))))"
    CHLAUX_STR_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[extends_trans; infinity_hl_extends]; ALL_TAC] THEN
  REWRITE_TAC[hol_light_ctxt_def] THEN
  MAP_EVERY EXISTS_TAC [`[]:update list`; `[]:update list`; `[]:update list`;
                        `[]:update list`; `implode "b1"`; `implode "b2"`] THEN
  REWRITE_TAC[APPEND; ALL]);;

(* ------------------------------------------------------------------------- *)
(* The measured context.  What follows is the first 42 updates (newest       *)
(* first, so the oldest position 1 is last) of the record the Candle kernel  *)
(* printed for a session that loaded core HOL Light.  It is a mechanical     *)
(* retranslation of that record's s-expressions through the grammar of       *)
(* print_thm, so the theorems below compare the definitions above against    *)
(* the kernel's own output rather than against a hand-written guess.  Beyond *)
(* position 42 the session declares no further axiom.  The two generated     *)
(* binder names are the only session-dependent part.                         *)
(*                                                                           *)
(* HOL4 marks each position with a comment; the positions, newest first     *)
(* (ConstSpec unless said otherwise):                                        *)
(*   42 NewAxiom INFINITY_AX, 41 ONTO, 40 ONE_ONE, 39 NewType ind,           *)
(*   38 PASSOC, 37 UNCURRY, 36 CURRY, 35 SND, 34 FST, 33 the pairing comma,  *)
(*   32 TypeDefn prod, 31 mk_pair, 30 _FUNCTION, 29 _MATCH,                  *)
(*   28 _GUARDED_PATTERN, 27 _UNGUARDED_PATTERN, 26 _SEQPATTERN, 25 GEQ,     *)
(*   24 GABS, 23 LET_END, 22 LET, 21 one, 20 TypeDefn 1, 19 I, 18 o,         *)
(*   17 COND, 16 NewAxiom SELECT_AX, 15 NewConst @, 14 NewAxiom ETA_AX,      *)
(*   13 _FALSITY_, 12 the unique existence quantifier, 11 negation, 10 F,    *)
(*   9 disjunction, 8 ?, 7 !, 6 implication, 5 conjunction, 4 T,             *)
(*   3 NewConst equality, 2 NewType bool, 1 NewType fun.                     *)
(* ------------------------------------------------------------------------- *)

let measured_prefix_def = cake_def
  `measured_prefix =
     [hol_NewAxiom (hol_Comb (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind")
        []]; Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "f") (Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind")
        []])) (hol_Comb (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Comb (hol_Const (implode "ONE_ONE") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind") []]; Tyapp
        (implode "bool") []])) (hol_Var (implode "f") (Tyapp (implode "fun") [Tyapp
        (implode "ind") []; Tyapp (implode "ind") []])))) (hol_Comb (hol_Const (implode "~")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []])) (hol_Comb
        (hol_Const (implode "ONTO") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "ind") []; Tyapp (implode "ind") []]; Tyapp (implode "bool") []])) (hol_Var
        (implode "f") (Tyapp (implode "fun") [Tyapp (implode "ind") []; Tyapp (implode "ind")
        []])))))));
      hol_ConstSpec [((implode "ONTO"), hol_Abs (hol_Var (implode "_2045") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "!") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
        (hol_Comb (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "y") (Tyvar (implode "B")))) (hol_Comb (hol_Var
        (implode "_2045") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
        (hol_Var (implode "x") (Tyvar (implode "A"))))))))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyapp (implode "bool") []]; Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")];
        Tyapp (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Var (implode "ONTO") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "bool") []]))) (hol_Abs (hol_Var (implode "_2045") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "!") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
        (hol_Comb (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "y") (Tyvar (implode "B")))) (hol_Comb (hol_Var
        (implode "_2045") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
        (hol_Var (implode "x") (Tyvar (implode "A")))))))))));
      hol_ConstSpec [((implode "ONE_ONE"), hol_Abs (hol_Var (implode "_2040") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Const
        (implode "!") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "x1") (Tyvar
        (implode "A"))) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Abs (hol_Var (implode "x2") (Tyvar (implode "A"))) (hol_Comb (hol_Comb
        (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Comb (hol_Var
        (implode "_2040") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
        (hol_Var (implode "x1") (Tyvar (implode "A"))))) (hol_Comb (hol_Var (implode "_2040")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var
        (implode "x2") (Tyvar (implode "A")))))) (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "bool") []]])) (hol_Var (implode "x1") (Tyvar (implode "A")))) (hol_Var
        (implode "x2") (Tyvar (implode "A"))))))))))] (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyapp (implode "bool") []]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Var (implode "ONE_ONE") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "bool") []]))) (hol_Abs (hol_Var (implode "_2040") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "!") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "x1") (Tyvar (implode "A")))
        (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "x2") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const (implode "==>")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]])) (hol_Comb (hol_Var (implode "_2040") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var (implode "x1")
        (Tyvar (implode "A"))))) (hol_Comb (hol_Var (implode "_2040") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var (implode "x2") (Tyvar
        (implode "A")))))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]])) (hol_Var (implode "x1") (Tyvar (implode "A")))) (hol_Var (implode "x2") (Tyvar
        (implode "A")))))))))));
      hol_NewType (implode "ind") 0;
      hol_ConstSpec [((implode "PASSOC"), hol_Abs (hol_Var (implode "_1297") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar (implode "D")])) (hol_Abs (hol_Var
        (implode "_1298") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]])) (hol_Comb (hol_Var (implode "_1297") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar (implode "D")])) (hol_Comb (hol_Comb
        (hol_Const (implode ", ") (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun") [Tyvar (implode "C"); Tyapp
        (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")]]])) (hol_Comb (hol_Comb (hol_Const (implode ", ") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Comb (hol_Const (implode "FST") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyvar (implode "A")])) (hol_Var
        (implode "_1298") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]])))) (hol_Comb (hol_Const (implode "FST")
        (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")];
        Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "SND") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar
        (implode "C")]]; Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]]))
        (hol_Var (implode "_1298") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp
        (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]])))))) (hol_Comb (hol_Const
        (implode "SND") (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar
        (implode "C")]; Tyvar (implode "C")])) (hol_Comb (hol_Const (implode "SND") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyapp (implode "prod") [Tyvar (implode "B");
        Tyvar (implode "C")]])) (hol_Var (implode "_1298") (Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]]))))))))]
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "prod") [Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar (implode "D")]; Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyvar (implode "D")]]; Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "prod") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar
        (implode "D")]; Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp
        (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyvar (implode "D")]]; Tyapp
        (implode "bool") []]])) (hol_Var (implode "PASSOC") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar (implode "D")]; Tyapp (implode "fun")
        [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod") [Tyvar (implode "B");
        Tyvar (implode "C")]]; Tyvar (implode "D")]]))) (hol_Abs (hol_Var (implode "_1297") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar (implode "D")])) (hol_Abs (hol_Var
        (implode "_1298") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]])) (hol_Comb (hol_Var (implode "_1297") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyvar (implode "C")]; Tyvar (implode "D")])) (hol_Comb (hol_Comb
        (hol_Const (implode ", ") (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun") [Tyvar (implode "C"); Tyapp
        (implode "prod") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")]]])) (hol_Comb (hol_Comb (hol_Const (implode ", ") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Comb (hol_Const (implode "FST") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyvar (implode "A")])) (hol_Var
        (implode "_1298") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]])))) (hol_Comb (hol_Const (implode "FST")
        (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")];
        Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "SND") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar
        (implode "C")]]; Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]]))
        (hol_Var (implode "_1298") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp
        (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]])))))) (hol_Comb (hol_Const
        (implode "SND") (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar
        (implode "C")]; Tyvar (implode "C")])) (hol_Comb (hol_Const (implode "SND") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyapp (implode "prod")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyapp (implode "prod") [Tyvar (implode "B");
        Tyvar (implode "C")]])) (hol_Var (implode "_1298") (Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyapp (implode "prod") [Tyvar (implode "B"); Tyvar (implode "C")]])))))))));
      hol_ConstSpec [((implode "UNCURRY"), hol_Abs (hol_Var (implode "_1280") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar
        (implode "C")]])) (hol_Abs (hol_Var (implode "_1281") (Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Comb (hol_Var (implode "_1280")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyvar (implode "C")]])) (hol_Comb (hol_Const (implode "FST") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "A")]))
        (hol_Var (implode "_1281") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")])))) (hol_Comb (hol_Const (implode "SND") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "B")]))
        (hol_Var (implode "_1281") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")]))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyapp (implode "fun") [Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]]; Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyapp (implode "fun") [Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]]; Tyapp (implode "bool")
        []]])) (hol_Var (implode "UNCURRY") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")]]; Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")]]))) (hol_Abs (hol_Var (implode "_1280") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")]]))
        (hol_Abs (hol_Var (implode "_1281") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")])) (hol_Comb (hol_Comb (hol_Var (implode "_1280") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")]]))
        (hol_Comb (hol_Const (implode "FST") (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyvar (implode "A")])) (hol_Var (implode "_1281")
        (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")])))) (hol_Comb
        (hol_Const (implode "SND") (Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyvar (implode "B")])) (hol_Var (implode "_1281")
        (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")])))))));
      hol_ConstSpec [((implode "CURRY"), hol_Abs (hol_Var (implode "_1259") (Tyapp (implode "fun")
        [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]))
        (hol_Abs (hol_Var (implode "_1260") (Tyvar (implode "A"))) (hol_Abs (hol_Var
        (implode "_1261") (Tyvar (implode "B"))) (hol_Comb (hol_Var (implode "_1259") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")])) (hol_Comb (hol_Comb (hol_Const (implode ", ") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Var (implode "_1260") (Tyvar
        (implode "A")))) (hol_Var (implode "_1261") (Tyvar (implode "B"))))))))] (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyvar (implode "C")]]]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyvar (implode "C")]]]; Tyapp (implode "bool") []]])) (hol_Var
        (implode "CURRY") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]; Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar
        (implode "C")]]]))) (hol_Abs (hol_Var (implode "_1259") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "C")]))
        (hol_Abs (hol_Var (implode "_1260") (Tyvar (implode "A"))) (hol_Abs (hol_Var
        (implode "_1261") (Tyvar (implode "B"))) (hol_Comb (hol_Var (implode "_1259") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar
        (implode "C")])) (hol_Comb (hol_Comb (hol_Const (implode ", ") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Var (implode "_1260") (Tyvar
        (implode "A")))) (hol_Var (implode "_1261") (Tyvar (implode "B")))))))));
      hol_ConstSpec [((implode "SND"), hol_Abs (hol_Var (implode "p") (Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "@") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
        Tyvar (implode "B")])) (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B"))) (hol_Comb
        (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]))) (hol_Comb (hol_Comb (hol_Const (implode ", ")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Var
        (implode "x") (Tyvar (implode "A")))) (hol_Var (implode "y") (Tyvar
        (implode "B"))))))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")]; Tyvar (implode "B")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "B")]; Tyapp
        (implode "bool") []]])) (hol_Var (implode "SND") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "B")])))
        (hol_Abs (hol_Var (implode "p") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")])) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B"))) (hol_Comb (hol_Const (implode "?")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "bool") []]]))
        (hol_Var (implode "p") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")]))) (hol_Comb (hol_Comb (hol_Const (implode ", ") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Var (implode "x") (Tyvar
        (implode "A")))) (hol_Var (implode "y") (Tyvar (implode "B")))))))))));
      hol_ConstSpec [((implode "FST"), hol_Abs (hol_Var (implode "p") (Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Const (implode "@") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyvar (implode "A")])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb
        (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "y") (Tyvar (implode "B"))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "prod") [Tyvar
        (implode "A"); Tyvar (implode "B")]))) (hol_Comb (hol_Comb (hol_Const (implode ", ")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Var
        (implode "x") (Tyvar (implode "A")))) (hol_Var (implode "y") (Tyvar
        (implode "B"))))))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")]; Tyvar (implode "A")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "A")]; Tyapp
        (implode "bool") []]])) (hol_Var (implode "FST") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyvar (implode "A")])))
        (hol_Abs (hol_Var (implode "p") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")])) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyvar (implode "A")]))
        (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Const (implode "?")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun") [Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "bool") []]]))
        (hol_Var (implode "p") (Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")]))) (hol_Comb (hol_Comb (hol_Const (implode ", ") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]])) (hol_Var (implode "x") (Tyvar
        (implode "A")))) (hol_Var (implode "y") (Tyvar (implode "B")))))))))));
      hol_ConstSpec [((implode ", "), hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
        (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B"))) (hol_Comb (hol_Const
        (implode "ABS_prod") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]; Tyapp
        (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]])) (hol_Comb (hol_Comb
        (hol_Const (implode "mk_pair") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]]])) (hol_Var
        (implode "x") (Tyvar (implode "A")))) (hol_Var (implode "y") (Tyvar (implode "B")))))))]
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]]; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "prod")
        [Tyvar (implode "A"); Tyvar (implode "B")]]]; Tyapp (implode "bool") []]])) (hol_Var
        (implode ", ") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar (implode "B")]]])))
        (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Abs (hol_Var (implode "y")
        (Tyvar (implode "B"))) (hol_Comb (hol_Const (implode "ABS_prod") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyapp (implode "bool") []]]; Tyapp (implode "prod") [Tyvar (implode "A"); Tyvar
        (implode "B")]])) (hol_Comb (hol_Comb (hol_Const (implode "mk_pair") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]]]])) (hol_Var (implode "x") (Tyvar (implode "A")))) (hol_Var
        (implode "y") (Tyvar (implode "B"))))))));
      hol_TypeDefn (implode "prod") (hol_Abs (hol_Var (implode "x") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]))
        (hol_Comb (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "a") (Tyvar (implode "A"))) (hol_Comb (hol_Const (implode "?") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "b") (Tyvar (implode "B")))
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]; Tyapp (implode "bool")
        []]])) (hol_Var (implode "x") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]))) (hol_Comb (hol_Comb
        (hol_Const (implode "mk_pair") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]]])) (hol_Var
        (implode "a") (Tyvar (implode "A")))) (hol_Var (implode "b") (Tyvar (implode "B"))))))))))
        (implode "ABS_prod") (implode "REP_prod");
      hol_ConstSpec [((implode "mk_pair"), hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
        (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B"))) (hol_Abs (hol_Var (implode "a")
        (Tyvar (implode "A"))) (hol_Abs (hol_Var (implode "b") (Tyvar (implode "B"))) (hol_Comb
        (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])) (hol_Var (implode "a")
        (Tyvar (implode "A")))) (hol_Var (implode "x") (Tyvar (implode "A"))))) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "b")
        (Tyvar (implode "B")))) (hol_Var (implode "y") (Tyvar (implode "B")))))))))] (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]]];
        Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]]]]; Tyapp (implode "bool") []]]))
        (hol_Var (implode "mk_pair") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]]]))) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Abs (hol_Var (implode "y") (Tyvar
        (implode "B"))) (hol_Abs (hol_Var (implode "a") (Tyvar (implode "A"))) (hol_Abs (hol_Var
        (implode "b") (Tyvar (implode "B"))) (hol_Comb (hol_Comb (hol_Const (implode "/\\") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "a") (Tyvar (implode "A")))) (hol_Var
        (implode "x") (Tyvar (implode "A"))))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "b") (Tyvar (implode "B")))) (hol_Var
        (implode "y") (Tyvar (implode "B"))))))))));
      hol_ConstSpec [((implode "_FUNCTION"), hol_Abs (hol_Var (implode "r") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb
        (hol_Comb (hol_Const (implode "COND") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyvar (implode "B")]]])) (hol_Comb (hol_Const (implode "?!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Abs (hol_Var (implode "z") (Tyvar (implode "B"))) (hol_Const (implode "F") (Tyapp
        (implode "bool") [])))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]; Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "B")]]; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyapp (implode "bool") []]]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "B")]]; Tyapp (implode "bool") []]])) (hol_Var (implode "_FUNCTION") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]]; Tyapp (implode "fun") [Tyvar (implode "A");
        Tyvar (implode "B")]]))) (hol_Abs (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]))
        (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Comb
        (hol_Const (implode "COND") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar
        (implode "B")]]])) (hol_Comb (hol_Const (implode "?!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Abs (hol_Var (implode "z") (Tyvar (implode "B"))) (hol_Const (implode "F") (Tyapp
        (implode "bool") []))))))));
      hol_ConstSpec [((implode "_MATCH"), hol_Abs (hol_Var (implode "e") (Tyvar (implode "A")))
        (hol_Abs (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb
        (hol_Comb (hol_Const (implode "COND") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B");
        Tyvar (implode "B")]]])) (hol_Comb (hol_Const (implode "?!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "e")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "e")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Abs (hol_Var (implode "z") (Tyvar (implode "B"))) (hol_Const (implode "F") (Tyapp
        (implode "bool") [])))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]]; Tyvar (implode "B")]]; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]; Tyvar
        (implode "B")]]; Tyapp (implode "bool") []]])) (hol_Var (implode "_MATCH") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]];
        Tyvar (implode "B")]]))) (hol_Abs (hol_Var (implode "e") (Tyvar (implode "A"))) (hol_Abs
        (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Comb
        (hol_Const (implode "COND") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyvar
        (implode "B")]]])) (hol_Comb (hol_Const (implode "?!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "e")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "e")
        (Tyvar (implode "A")))))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyvar (implode "B")]))
        (hol_Abs (hol_Var (implode "z") (Tyvar (implode "B"))) (hol_Const (implode "F") (Tyapp
        (implode "bool") []))))))));
      hol_ConstSpec [((implode "_GUARDED_PATTERN"), hol_Abs (hol_Var (implode "p") (Tyapp
        (implode "bool") [])) (hol_Abs (hol_Var (implode "g") (Tyapp (implode "bool") []))
        (hol_Abs (hol_Var (implode "r") (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb
        (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "p") (Tyapp (implode "bool") []))) (hol_Comb (hol_Comb (hol_Const (implode "/\\")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "g") (Tyapp
        (implode "bool") []))) (hol_Var (implode "r") (Tyapp (implode "bool") [])))))))] (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]]; Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]]]; Tyapp (implode "bool") []]])) (hol_Var
        (implode "_GUARDED_PATTERN") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]]]))) (hol_Abs (hol_Var (implode "p") (Tyapp
        (implode "bool") [])) (hol_Abs (hol_Var (implode "g") (Tyapp (implode "bool") []))
        (hol_Abs (hol_Var (implode "r") (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb
        (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "p") (Tyapp (implode "bool") []))) (hol_Comb (hol_Comb (hol_Const (implode "/\\")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "g") (Tyapp
        (implode "bool") []))) (hol_Var (implode "r") (Tyapp (implode "bool") []))))))));
      hol_ConstSpec [((implode "_UNGUARDED_PATTERN"), hol_Abs (hol_Var (implode "p") (Tyapp
        (implode "bool") [])) (hol_Abs (hol_Var (implode "r") (Tyapp (implode "bool") []))
        (hol_Comb (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "bool") []))) (hol_Var
        (implode "r") (Tyapp (implode "bool") [])))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp (implode "bool") []]]))
        (hol_Var (implode "_UNGUARDED_PATTERN") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))) (hol_Abs
        (hol_Var (implode "p") (Tyapp (implode "bool") [])) (hol_Abs (hol_Var (implode "r") (Tyapp
        (implode "bool") [])) (hol_Comb (hol_Comb (hol_Const (implode "/\\") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "bool") [])))
        (hol_Var (implode "r") (Tyapp (implode "bool") []))))));
      hol_ConstSpec [((implode "_SEQPATTERN"), hol_Abs (hol_Var (implode "r") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]])) (hol_Abs (hol_Var (implode "s") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]))
        (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Comb
        (hol_Const (implode "COND") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []];
        Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]; Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]]])) (hol_Comb
        (hol_Const (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "y") (Tyvar (implode "B"))) (hol_Comb (hol_Comb (hol_Var (implode "r") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "x") (Tyvar (implode "A")))) (hol_Var
        (implode "y") (Tyvar (implode "B"))))))) (hol_Comb (hol_Var (implode "r") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "x") (Tyvar (implode "A"))))) (hol_Comb (hol_Var
        (implode "s") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "x") (Tyvar
        (implode "A"))))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp
        (implode "bool") []]]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]]]]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]]; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyapp (implode "bool") []]]]]; Tyapp (implode "bool") []]])) (hol_Var
        (implode "_SEQPATTERN") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]];
        Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]]; Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]]]]))) (hol_Abs (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Abs
        (hol_Var (implode "s") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Abs (hol_Var (implode "x") (Tyvar
        (implode "A"))) (hol_Comb (hol_Comb (hol_Comb (hol_Const (implode "COND") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]; Tyapp (implode "fun")
        [Tyvar (implode "B"); Tyapp (implode "bool") []]]]])) (hol_Comb (hol_Const (implode "?")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool")
        []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
        (hol_Comb (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var
        (implode "x") (Tyvar (implode "A")))) (hol_Var (implode "y") (Tyvar (implode "B")))))))
        (hol_Comb (hol_Var (implode "r") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A"))))) (hol_Comb (hol_Var (implode "s") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "B"); Tyapp (implode "bool") []]]))
        (hol_Var (implode "x") (Tyvar (implode "A")))))))));
      hol_ConstSpec [((implode "GEQ"), hol_Abs (hol_Var (implode "a") (Tyvar (implode "A")))
        (hol_Abs (hol_Var (implode "b") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]])) (hol_Var (implode "a") (Tyvar
        (implode "A")))) (hol_Var (implode "b") (Tyvar (implode "A"))))))] (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]];
        Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "bool") []]]; Tyapp (implode "bool") []]])) (hol_Var
        (implode "GEQ") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]]))) (hol_Abs (hol_Var (implode "a") (Tyvar
        (implode "A"))) (hol_Abs (hol_Var (implode "b") (Tyvar (implode "A"))) (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])) (hol_Var (implode "a")
        (Tyvar (implode "A")))) (hol_Var (implode "b") (Tyvar (implode "A")))))));
      hol_ConstSpec [((implode "GABS"), hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Const (implode "@")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]; Tyvar (implode "A")])) (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyvar (implode "A")]; Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]; Tyvar (implode "A")]; Tyapp (implode "bool") []]])) (hol_Var (implode "GABS") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyvar (implode "A")]))) (hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Const (implode "@") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyvar (implode "A")])) (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "bool") []])))));
      hol_ConstSpec [((implode "LET_END"), hol_Abs (hol_Var (implode "t") (Tyvar (implode "A")))
        (hol_Var (implode "t") (Tyvar (implode "A"))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "A")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "A")]; Tyapp (implode "bool") []]])) (hol_Var (implode "LET_END") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "A")]))) (hol_Abs (hol_Var
        (implode "t") (Tyvar (implode "A"))) (hol_Var (implode "t") (Tyvar (implode "A")))));
      hol_ConstSpec [((implode "LET"), hol_Abs (hol_Var (implode "f") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Abs (hol_Var (implode "x") (Tyvar
        (implode "A"))) (hol_Comb (hol_Var (implode "f") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "B")])) (hol_Var (implode "x") (Tyvar (implode "A"))))))]
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "B")]]; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "B")]]; Tyapp (implode "bool") []]])) (hol_Var
        (implode "LET") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "B")]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]])))
        (hol_Abs (hol_Var (implode "f") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "B")])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Var
        (implode "f") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var
        (implode "x") (Tyvar (implode "A")))))));
      hol_ConstSpec [((implode "one"), hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "1") []; Tyapp (implode "bool") []]; Tyapp
        (implode "1") []])) (hol_Abs (hol_Var (implode "x") (Tyapp (implode "1") [])) (hol_Const
        (implode "T") (Tyapp (implode "bool") []))))] (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyapp (implode "1") []; Tyapp (implode "fun") [Tyapp (implode "1")
        []; Tyapp (implode "bool") []]])) (hol_Var (implode "one") (Tyapp (implode "1") [])))
        (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "1") []; Tyapp (implode "bool") []]; Tyapp (implode "1") []])) (hol_Abs (hol_Var
        (implode "x") (Tyapp (implode "1") [])) (hol_Const (implode "T") (Tyapp (implode "bool")
        [])))));
      hol_TypeDefn (implode "1") (hol_Abs (hol_Var (implode "b") (Tyapp (implode "bool") []))
        (hol_Var (implode "b") (Tyapp (implode "bool") []))) (implode "one_ABS")
        (implode "one_REP");
      hol_ConstSpec [((implode "I"), hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
        (hol_Var (implode "x") (Tyvar (implode "A"))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "A")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "A")]; Tyapp (implode "bool") []]])) (hol_Var (implode "I") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "A")]))) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Var (implode "x") (Tyvar (implode "A")))));
      hol_ConstSpec [((implode "o"), hol_Abs (hol_Var (implode "f") (Tyapp (implode "fun") [Tyvar
        (implode "B"); Tyvar (implode "C")])) (hol_Abs (hol_Var (implode "g") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Var (implode "f") (Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")])) (hol_Comb (hol_Var
        (implode "g") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var
        (implode "x") (Tyvar (implode "A"))))))))] (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B");
        Tyvar (implode "C")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "C")]]];
        Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "B");
        Tyvar (implode "C")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A");
        Tyvar (implode "B")]; Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "C")]]];
        Tyapp (implode "bool") []]])) (hol_Var (implode "o") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "C")]]]))) (hol_Abs (hol_Var (implode "f") (Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")])) (hol_Abs (hol_Var
        (implode "g") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Abs
        (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Var (implode "f") (Tyapp
        (implode "fun") [Tyvar (implode "B"); Tyvar (implode "C")])) (hol_Comb (hol_Var
        (implode "g") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var
        (implode "x") (Tyvar (implode "A")))))))));
      hol_ConstSpec [((implode "COND"), hol_Abs (hol_Var (implode "t") (Tyapp (implode "bool")
        [])) (hol_Abs (hol_Var (implode "t1") (Tyvar (implode "A"))) (hol_Abs (hol_Var
        (implode "t2") (Tyvar (implode "A"))) (hol_Comb (hol_Const (implode "@") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyvar (implode "A")])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb
        (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "t") (Tyapp (implode "bool") []))) (hol_Const (implode "T") (Tyapp
        (implode "bool") [])))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "x") (Tyvar (implode "A")))) (hol_Var
        (implode "t1") (Tyvar (implode "A")))))) (hol_Comb (hol_Comb (hol_Const (implode "==>")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "t") (Tyapp
        (implode "bool") []))) (hol_Const (implode "F") (Tyapp (implode "bool") [])))) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A")))) (hol_Var (implode "t2") (Tyvar (implode "A")))))))))))] (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyvar (implode "A")]]]; Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "A")]]]; Tyapp (implode "bool")
        []]])) (hol_Var (implode "COND") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar
        (implode "A")]]]))) (hol_Abs (hol_Var (implode "t") (Tyapp (implode "bool") [])) (hol_Abs
        (hol_Var (implode "t1") (Tyvar (implode "A"))) (hol_Abs (hol_Var (implode "t2") (Tyvar
        (implode "A"))) (hol_Comb (hol_Const (implode "@") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyvar (implode "A")]))
        (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const
        (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const
        (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "t") (Tyapp
        (implode "bool") []))) (hol_Const (implode "T") (Tyapp (implode "bool") [])))) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]])) (hol_Var (implode "x")
        (Tyvar (implode "A")))) (hol_Var (implode "t1") (Tyvar (implode "A")))))) (hol_Comb
        (hol_Comb (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "t") (Tyapp (implode "bool") []))) (hol_Const (implode "F") (Tyapp
        (implode "bool") [])))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]])) (hol_Var (implode "x") (Tyvar (implode "A")))) (hol_Var
        (implode "t2") (Tyvar (implode "A"))))))))))));
      hol_NewAxiom (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "P")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []])) (hol_Comb
        (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Var (implode "P") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "bool") []])) (hol_Var (implode "x") (Tyvar
        (implode "A"))))) (hol_Comb (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Const (implode "@") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyvar (implode "A")])) (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "bool") []])))))))));
      hol_NewConst (implode "@") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyvar (implode "A")]);
      hol_NewAxiom (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]; Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "t") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyvar (implode "B")]; Tyapp (implode "bool") []]])) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Var (implode "t") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])) (hol_Var (implode "x") (Tyvar
        (implode "A")))))) (hol_Var (implode "t") (Tyapp (implode "fun") [Tyvar (implode "A");
        Tyvar (implode "B")])))));
      hol_ConstSpec [((implode "_FALSITY_"), hol_Const (implode "F") (Tyapp (implode "bool") []))]
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Var (implode "_FALSITY_") (Tyapp (implode "bool") [])))
        (hol_Const (implode "F") (Tyapp (implode "bool") [])));
      hol_ConstSpec [((implode "?!"), hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Comb (hol_Const (implode "/\\")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Const (implode "?")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]; Tyapp (implode "bool") []])) (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])))) (hol_Comb (hol_Const (implode "!") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
        (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var
        (implode "y") (Tyvar (implode "A"))) (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const (implode "/\\") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Var (implode "P") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "bool") []])) (hol_Var (implode "x") (Tyvar
        (implode "A"))))) (hol_Comb (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])) (hol_Var (implode "y") (Tyvar
        (implode "A")))))) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]])) (hol_Var (implode "x") (Tyvar (implode "A")))) (hol_Var (implode "y") (Tyvar
        (implode "A")))))))))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Var (implode "?!") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]))) (hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Comb (hol_Const
        (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Const
        (implode "?") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Var (implode "P") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []])))) (hol_Comb (hol_Const
        (implode "!") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "x") (Tyvar
        (implode "A"))) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Abs (hol_Var (implode "y") (Tyvar (implode "A"))) (hol_Comb (hol_Comb
        (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []])) (hol_Var (implode "x") (Tyvar (implode "A"))))) (hol_Comb (hol_Var (implode "P")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []])) (hol_Var
        (implode "y") (Tyvar (implode "A")))))) (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar (implode "A");
        Tyapp (implode "bool") []]])) (hol_Var (implode "x") (Tyvar (implode "A")))) (hol_Var
        (implode "y") (Tyvar (implode "A"))))))))))));
      hol_ConstSpec [((implode "~"), hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "bool") []))) (hol_Const
        (implode "F") (Tyapp (implode "bool") []))))] (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Var (implode "~")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]))) (hol_Abs
        (hol_Var (implode "p") (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb (hol_Const
        (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "p") (Tyapp
        (implode "bool") []))) (hol_Const (implode "F") (Tyapp (implode "bool") [])))));
      hol_ConstSpec [((implode "F"), hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []])) (hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Var (implode "p") (Tyapp (implode "bool") []))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "F") (Tyapp
        (implode "bool") []))) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []])) (hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Var (implode "p") (Tyapp (implode "bool") [])))));
      hol_ConstSpec [((implode "\\/"), hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") [])) (hol_Comb (hol_Const
        (implode "!") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "bool") []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "r")
        (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "bool") [])))
        (hol_Var (implode "r") (Tyapp (implode "bool") [])))) (hol_Comb (hol_Comb (hol_Const
        (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const
        (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "q") (Tyapp
        (implode "bool") []))) (hol_Var (implode "r") (Tyapp (implode "bool") [])))) (hol_Var
        (implode "r") (Tyapp (implode "bool") []))))))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp (implode "bool") []]]))
        (hol_Var (implode "\\/") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))) (hol_Abs
        (hol_Var (implode "p") (Tyapp (implode "bool") [])) (hol_Abs (hol_Var (implode "q") (Tyapp
        (implode "bool") [])) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []])) (hol_Abs (hol_Var (implode "r") (Tyapp (implode "bool") []))
        (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "bool") [])))
        (hol_Var (implode "r") (Tyapp (implode "bool") [])))) (hol_Comb (hol_Comb (hol_Const
        (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Const
        (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var (implode "q") (Tyapp
        (implode "bool") []))) (hol_Var (implode "r") (Tyapp (implode "bool") [])))) (hol_Var
        (implode "r") (Tyapp (implode "bool") [])))))))));
      hol_ConstSpec [((implode "?"), hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Const (implode "!") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool")
        []]; Tyapp (implode "bool") []])) (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool")
        [])) (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb
        (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []])) (hol_Var (implode "x") (Tyvar (implode "A"))))) (hol_Var (implode "q") (Tyapp
        (implode "bool") [])))))) (hol_Var (implode "q") (Tyapp (implode "bool") []))))))]
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []]])) (hol_Var (implode "?") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []]))) (hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []])) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []])) (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") []))
        (hol_Comb (hol_Comb (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Comb (hol_Const (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []])) (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A"))) (hol_Comb (hol_Comb
        (hol_Const (implode "==>") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []])) (hol_Var (implode "x") (Tyvar (implode "A"))))) (hol_Var (implode "q") (Tyapp
        (implode "bool") [])))))) (hol_Var (implode "q") (Tyapp (implode "bool") [])))))));
      hol_ConstSpec [((implode "!"), hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []])) (hol_Comb (hol_Comb (hol_Const (implode "=")
        (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool")
        []]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Var (implode "P") (Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]))) (hol_Abs (hol_Var
        (implode "x") (Tyvar (implode "A"))) (hol_Const (implode "T") (Tyapp (implode "bool")
        [])))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []]; Tyapp (implode "bool") []]])) (hol_Var (implode "!") (Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp (implode "bool")
        []]))) (hol_Abs (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "bool") []])) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]; Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]])) (hol_Var (implode "P") (Tyapp (implode "fun") [Tyvar
        (implode "A"); Tyapp (implode "bool") []]))) (hol_Abs (hol_Var (implode "x") (Tyvar
        (implode "A"))) (hol_Const (implode "T") (Tyapp (implode "bool") []))))));
      hol_ConstSpec [((implode "==>"), hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "p") (Tyapp (implode "bool") []))) (hol_Var (implode "q") (Tyapp (implode "bool")
        [])))) (hol_Var (implode "p") (Tyapp (implode "bool") [])))))] (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]]; Tyapp (implode "bool") []]])) (hol_Var (implode "==>") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]]))) (hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool")
        [])) (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Const (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "p") (Tyapp (implode "bool") []))) (hol_Var (implode "q") (Tyapp (implode "bool")
        [])))) (hol_Var (implode "p") (Tyapp (implode "bool") []))))));
      hol_ConstSpec [((implode "/\\"), hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Abs (hol_Var (implode "q") (Tyapp (implode "bool") [])) (hol_Comb (hol_Comb
        (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]]; Tyapp (implode "bool") []]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []]])) (hol_Abs (hol_Var (implode "f") (Tyapp (implode "fun") [Tyapp
        (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Var (implode "f") (Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]])) (hol_Var (implode "p") (Tyapp (implode "bool") []))) (hol_Var
        (implode "q") (Tyapp (implode "bool") []))))) (hol_Abs (hol_Var (implode "f") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Comb (hol_Comb (hol_Var (implode "f") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Const (implode "T") (Tyapp (implode "bool") [])))
        (hol_Const (implode "T") (Tyapp (implode "bool") [])))))))] (hol_Comb (hol_Comb (hol_Const
        (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp (implode "bool") []]]))
        (hol_Var (implode "/\\") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]))) (hol_Abs
        (hol_Var (implode "p") (Tyapp (implode "bool") [])) (hol_Abs (hol_Var (implode "q") (Tyapp
        (implode "bool") [])) (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]; Tyapp
        (implode "bool") []]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]]; Tyapp (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Abs
        (hol_Var (implode "f") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Var (implode "f") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Var
        (implode "p") (Tyapp (implode "bool") []))) (hol_Var (implode "q") (Tyapp (implode "bool")
        []))))) (hol_Abs (hol_Var (implode "f") (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Comb
        (hol_Comb (hol_Var (implode "f") (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])) (hol_Const
        (implode "T") (Tyapp (implode "bool") []))) (hol_Const (implode "T") (Tyapp
        (implode "bool") []))))))));
      hol_ConstSpec [((implode "T"), hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool")
        []]; Tyapp (implode "fun") [Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp
        (implode "bool") []]; Tyapp (implode "bool") []]])) (hol_Abs (hol_Var (implode "p") (Tyapp
        (implode "bool") [])) (hol_Var (implode "p") (Tyapp (implode "bool") [])))) (hol_Abs
        (hol_Var (implode "p") (Tyapp (implode "bool") [])) (hol_Var (implode "p") (Tyapp
        (implode "bool") []))))] (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "fun") [Tyapp (implode "bool")
        []; Tyapp (implode "bool") []]])) (hol_Var (implode "T") (Tyapp (implode "bool") [])))
        (hol_Comb (hol_Comb (hol_Const (implode "=") (Tyapp (implode "fun") [Tyapp (implode "fun")
        [Tyapp (implode "bool") []; Tyapp (implode "bool") []]; Tyapp (implode "fun") [Tyapp
        (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]; Tyapp
        (implode "bool") []]])) (hol_Abs (hol_Var (implode "p") (Tyapp (implode "bool") []))
        (hol_Var (implode "p") (Tyapp (implode "bool") [])))) (hol_Abs (hol_Var (implode "p")
        (Tyapp (implode "bool") [])) (hol_Var (implode "p") (Tyapp (implode "bool") [])))));
      hol_NewConst (implode "=") (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp
        (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]]);
      hol_NewType (implode "bool") 0;
      hol_NewType (implode "fun") 2]`;;

(* Each block agrees with the kernel printout update for update.  The index
   arithmetic reads the list newest first: positions 42-39 are the infinity
   block, 16-15 the select block, 14 the eta axiom, and 11-1 the booleans on
   top of the initial context. *)

let measured_infinity_block = prove
 (`TAKE 4 measured_prefix = mk_infinity_ctxt_hl (implode "_2040") (implode "_2045") []`,
  REWRITE_TAC[measured_prefix_def; mk_infinity_ctxt_hl_def] THEN
  SIMP[equation_def; typeof_def; codomain_def]);;

let measured_select_block = prove
 (`TAKE 2 (DROP 26 measured_prefix) = mk_select_ctxt_cl []`,
  REWRITE_TAC[measured_prefix_def; mk_select_ctxt_cl_def] THEN SIMP[]);;

let measured_eta_block = prove
 (`TAKE 1 (DROP 28 measured_prefix) = mk_eta_ctxt_cl []`,
  REWRITE_TAC[measured_prefix_def; mk_eta_ctxt_cl_def] THEN
  SIMP[equation_def; typeof_def; codomain_def]);;

let measured_bool_block = prove
 (`DROP 31 measured_prefix = mk_bool_ctxt init_ctxt`,
  REWRITE_TAC[measured_prefix_def; mk_bool_ctxt_def; init_ctxt_def; TrueDef_def; AndDef_def;
              ImpliesDef_def; ForallDef_def; ExistsDef_def; OrDef_def; FalseDef_def;
              NotDef_def] THEN
  SIMP[equation_def; typeof_def; codomain_def]);;

(* the four blocks compose, with positions 38-17 and 13-12 in between and
   nothing at all between the eta and select blocks *)

let measured_prefix_decomposition = prove
 (`measured_prefix =
   mk_infinity_ctxt_hl (implode "_2040") (implode "_2045")
     (APPEND (TAKE 22 (DROP 4 measured_prefix))
        (mk_select_ctxt_cl
           (mk_eta_ctxt_cl
              (APPEND (TAKE 2 (DROP 29 measured_prefix)) (mk_bool_ctxt init_ctxt)))))`,
  REWRITE_TAC[measured_prefix_def; mk_infinity_ctxt_hl_def; mk_select_ctxt_cl_def;
              mk_eta_ctxt_cl_def; mk_bool_ctxt_def; init_ctxt_def; TrueDef_def; AndDef_def;
              ImpliesDef_def; ForallDef_def; ExistsDef_def; OrDef_def; FalseDef_def;
              NotDef_def] THEN
  SIMP[equation_def; typeof_def; codomain_def]);;

(* so the guarantee fires on the measured session: whatever the session goes
   on to define after position 42, as long as it declares no further axiom
   (and the record shows it does not), the context it reaches is one of the
   shapes above *)

let measured_prefix_hol_light_ctxt = prove
 (`!l. ALL (\u. !p. ~(u = hol_NewAxiom p)) l ==> hol_light_ctxt (APPEND l measured_prefix)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hol_light_ctxt_def] THEN
  MAP_EVERY EXISTS_TAC
    [`l:update list`; `TAKE 22 (DROP 4 measured_prefix)`; `[]:update list`;
     `TAKE 2 (DROP 29 measured_prefix)`; `implode "_2040"`; `implode "_2045"`] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[APPEND] THEN AP_TERM_TAC THEN ACCEPT_TAC measured_prefix_decomposition;
   ASM_REWRITE_TAC[ALL_APPEND; APPEND_NIL; ALL] THEN
   REWRITE_TAC[measured_prefix_def] THEN SIMP[]]);;
