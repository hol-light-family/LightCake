(* ========================================================================= *)
(* holAxiomsSyntax: port of HOL4 candle/standard/syntax/                     *)
(* holAxiomsSyntaxScript.sml (CakeML v3479).  Context extensions for         *)
(* asserting the mathematical axioms.                                        *)
(* ========================================================================= *)

needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 Overloads are written out, as in holSyntax.ml and holBoolSyntax.ml *)
(*   (see their headers).  The local ones of this theory: A and B are        *)
(*   Tyvar (implode "A") and Tyvar (implode "B"), x is hol_Var (implode "x") *)
(*   A, g is hol_Var (implode "f") (Fun A B), P is hol_Var (implode "P")     *)
(*   (Fun A Bool), x1, x2, y are hol_Var (implode "x1") A, ..., hol_Var      *)
(*   (implode "y") B, h is hol_Var (implode "f") (Fun Ind Ind); FAx1, FAx2,  *)
(*   FAy, EXx, Exh are Forall (implode "x1") A, ..., Exists (implode "f")   *)
(*   (Fun Ind Ind).  The global ones:                                        *)
(*     Select ty   hol_Const (implode "@") (Fun (Fun ty Bool) ty)            *)
(*     One_One f   hol_Comb (hol_Const (implode "ONE_ONE")                   *)
(*                   (Fun (typeof f) Bool)) f                                *)
(*     Onto f      the same with implode "ONTO"                              *)
(*     Ind         Tyapp (implode "ind") []                                  *)
(*   One_One h and Onto h keep the subterm typeof h, as HOL4 stores them.    *)
(* - Local helpers that are not HOL4 theorems are CBOOLAUX_; the context    *)
(*   tactics of holBoolSyntax.ml (CBOOLAUX_EVAL, CBOOLAUX_TERM_THMS, ...)    *)
(*   are used here too.                                                      *)

(* Lookups in contexts that start with a new axiom, constant or type. *)

let CBOOLAUX_tysof_NewAxiom = prove
 (`!p ctxt.
     alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewAxiom p) ctxt))) =
     alist_to_fmap (FLAT (MAP types_of_upd ctxt))`,
  REWRITE_TAC[MAP; FLAT; types_of_upd_def; APPEND]);;

let CBOOLAUX_tmsof_NewAxiom = prove
 (`!p ctxt.
     alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewAxiom p) ctxt))) =
     alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`,
  REWRITE_TAC[MAP; FLAT; consts_of_upd_def; APPEND]);;

let CBOOLAUX_tysof_NewConst = prove
 (`!n ty ctxt.
     alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewConst n ty) ctxt))) =
     alist_to_fmap (FLAT (MAP types_of_upd ctxt))`,
  REWRITE_TAC[MAP; FLAT; types_of_upd_def; APPEND]);;

let CBOOLAUX_tmsof_NewConst = prove
 (`!n ty ctxt.
     alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewConst n ty) ctxt))) =
     alist_to_fmap (FLAT (MAP consts_of_upd ctxt)) |+ (n,ty)`,
  REWRITE_TAC[MAP; FLAT; consts_of_upd_def; APPEND; alist_to_fmap_thm]);;

let CBOOLAUX_tysof_NewType = prove
 (`!n k ctxt.
     alist_to_fmap (FLAT (MAP types_of_upd (CONS (hol_NewType n k) ctxt))) =
     alist_to_fmap (FLAT (MAP types_of_upd ctxt)) |+ (n,k)`,
  REWRITE_TAC[MAP; FLAT; types_of_upd_def; APPEND; alist_to_fmap_thm]);;

let CBOOLAUX_tmsof_NewType = prove
 (`!n k ctxt.
     alist_to_fmap (FLAT (MAP consts_of_upd (CONS (hol_NewType n k) ctxt))) =
     alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`,
  REWRITE_TAC[MAP; FLAT; consts_of_upd_def; APPEND]);;

let CBOOLAUX_has_type_welltyped = prove
 (`!tm ty. tm has_type ty <=> welltyped tm /\ typeof tm = ty`,
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

let CBOOLAUX_tyvar_inst_exists2 = prove
 (`!ty1 ty2.
     ?i. ty1 = REV_ASSOCD (Tyvar (implode "A")) i (Tyvar (implode "A")) /\
         ty2 = REV_ASSOCD (Tyvar (implode "B")) i (Tyvar (implode "B"))`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `[(ty1:hol_type,Tyvar (implode "A")); (ty2,Tyvar (implode "B"))]` THEN
  REWRITE_TAC[REV_ASSOCD; injectivity "hol_type"; injectivity "mlstring";
              injectivity "char"; CONS_11]);;

let CBOOLAUX_AX_THMS =
  [CBOOLAUX_tysof_NewAxiom; CBOOLAUX_tmsof_NewAxiom; CBOOLAUX_tysof_NewConst;
   CBOOLAUX_tmsof_NewConst; CBOOLAUX_tysof_NewType; CBOOLAUX_tmsof_NewType;
   CBOOLAUX_tyvar_inst_exists2] @ CBOOLAUX_TERM_THMS;;

(* ETA_AX *)

let mk_eta_ctxt_def = cake_def
  `mk_eta_ctxt ctxt =
     CONS (hol_NewAxiom
             (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                (hol_Comb
                   (hol_Var (implode "f")
                      (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")]))
                   (hol_Var (implode "x") (Tyvar (implode "A")))) ===
              hol_Var (implode "f")
                (Tyapp (implode "fun") [Tyvar (implode "A"); Tyvar (implode "B")])))
          ctxt`;;

let eta_extends = prove
 (`!ctxt. is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))
          ==> mk_eta_ctxt ctxt extends ctxt`,
  GEN_TAC THEN REWRITE_TAC[is_std_sig_def; FST; SND] THEN STRIP_TAC THEN
  REWRITE_TAC[mk_eta_ctxt_def] THEN MATCH_MP_TAC CBOOLAUX_extends_CONS THEN
  REWRITE_TAC[extends_def; RTC_REFL] THEN
  MATCH_MP_TAC (el 0 (CONJUNCTS updates_rules)) THEN
  REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN CBOOLAUX_EVAL CBOOLAUX_AX_THMS);;

(* SELECT_AX *)

let mk_select_ctxt_def = cake_def
  `mk_select_ctxt ctxt =
     CONS (hol_NewAxiom
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
                (hol_Comb
                   (hol_Var (implode "P")
                      (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]))
                   (hol_Comb
                      (hol_Const (implode "@")
                         (Tyapp (implode "fun")
                            [Tyapp (implode "fun") [Tyvar (implode "A");
                                                    Tyapp (implode "bool") []];
                             Tyvar (implode "A")]))
                      (hol_Var (implode "P")
                         (Tyapp (implode "fun") [Tyvar (implode "A");
                                                 Tyapp (implode "bool") []]))))))
     (CONS (hol_NewConst (implode "@")
              (Tyapp (implode "fun")
                 [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                  Tyvar (implode "A")]))
     ctxt)`;;

let select_extends = prove
 (`!ctxt. is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) /\
          ~(implode "@" IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
          FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "==>") =
          SOME (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                  Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                         Tyapp (implode "bool") []]])
          ==> mk_select_ctxt ctxt extends ctxt`,
  GEN_TAC THEN REWRITE_TAC[is_std_sig_def; FST; SND] THEN STRIP_TAC THEN
  REWRITE_TAC[mk_select_ctxt_def] THEN MATCH_MP_TAC CBOOLAUX_extends_CONS THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS updates_rules)) THEN
    REWRITE_TAC[CBOOLAUX_has_type_welltyped] THEN CBOOLAUX_EVAL CBOOLAUX_AX_THMS;
    MATCH_MP_TAC CBOOLAUX_extends_CONS THEN REWRITE_TAC[extends_def; RTC_REFL] THEN
    MATCH_MP_TAC (el 1 (CONJUNCTS updates_rules)) THEN
    CBOOLAUX_EVAL CBOOLAUX_AX_THMS]);;

(* INFINITY_AX *)

let mk_infinity_ctxt_def = cake_def
  `mk_infinity_ctxt ctxt =
     CONS
       (hol_NewAxiom
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
                   (Tyapp (implode "fun")
                      [Tyapp (implode "ind") []; Tyapp (implode "ind") []]))
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
                               [Tyapp (implode "ind") []; Tyapp (implode "ind") []]))))))))
       (CONS (hol_NewType (implode "ind") 0)
          (CONS
             (hol_ConstSpec
                [(implode "ONTO",
                  hol_Abs
                    (hol_Var (implode "f")
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
                                ((hol_Var (implode "y") (Tyvar (implode "B"))) ===
                                 (hol_Comb
                                    (hol_Var (implode "f")
                                       (Tyapp (implode "fun")
                                          [Tyvar (implode "A"); Tyvar (implode "B")]))
                                    (hol_Var (implode "x") (Tyvar (implode "A"))))))))))]
                ((hol_Var (implode "ONTO")
                    (typeof
                       (hol_Abs
                          (hol_Var (implode "f")
                             (Tyapp (implode "fun")
                                [Tyvar (implode "A"); Tyvar (implode "B")]))
                          (hol_Comb
                             (hol_Const (implode "!")
                                (Tyapp (implode "fun")
                                   [Tyapp (implode "fun")
                                      [Tyvar (implode "B");
                                       Tyapp (implode "bool") []];
                                    Tyapp (implode "bool") []]))
                             (hol_Abs (hol_Var (implode "y") (Tyvar (implode "B")))
                                (hol_Comb
                                   (hol_Const (implode "?")
                                      (Tyapp (implode "fun")
                                         [Tyapp (implode "fun")
                                            [Tyvar (implode "A");
                                             Tyapp (implode "bool") []];
                                          Tyapp (implode "bool") []]))
                                   (hol_Abs
                                      (hol_Var (implode "x") (Tyvar (implode "A")))
                                      ((hol_Var (implode "y") (Tyvar (implode "B"))) ===
                                       (hol_Comb
                                          (hol_Var (implode "f")
                                             (Tyapp (implode "fun")
                                                [Tyvar (implode "A");
                                                 Tyvar (implode "B")]))
                                          (hol_Var (implode "x")
                                             (Tyvar (implode "A")))))))))))) ===
                 (hol_Abs
                    (hol_Var (implode "f")
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
                                      [Tyvar (implode "A");
                                       Tyapp (implode "bool") []];
                                    Tyapp (implode "bool") []]))
                             (hol_Abs (hol_Var (implode "x") (Tyvar (implode "A")))
                                ((hol_Var (implode "y") (Tyvar (implode "B"))) ===
                                 (hol_Comb
                                    (hol_Var (implode "f")
                                       (Tyapp (implode "fun")
                                          [Tyvar (implode "A");
                                           Tyvar (implode "B")]))
                                    (hol_Var (implode "x") (Tyvar (implode "A"))))))))))))
             (CONS
                (hol_ConstSpec
                   [(implode "ONE_ONE",
                     hol_Abs
                       (hol_Var (implode "f")
                          (Tyapp (implode "fun")
                             [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                                         [Tyvar (implode "A");
                                          Tyapp (implode "bool") []];
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
                                                   [Tyvar (implode "A");
                                                    Tyvar (implode "B")]))
                                             (hol_Var (implode "x1")
                                                (Tyvar (implode "A")))) ===
                                          (hol_Comb
                                             (hol_Var (implode "f")
                                                (Tyapp (implode "fun")
                                                   [Tyvar (implode "A");
                                                    Tyvar (implode "B")]))
                                             (hol_Var (implode "x2")
                                                (Tyvar (implode "A"))))))
                                      ((hol_Var (implode "x1") (Tyvar (implode "A"))) ===
                                       (hol_Var (implode "x2") (Tyvar (implode "A"))))))))))]
                   ((hol_Var (implode "ONE_ONE")
                       (typeof
                          (hol_Abs
                             (hol_Var (implode "f")
                                (Tyapp (implode "fun")
                                   [Tyvar (implode "A"); Tyvar (implode "B")]))
                             (hol_Comb
                                (hol_Const (implode "!")
                                   (Tyapp (implode "fun")
                                      [Tyapp (implode "fun")
                                         [Tyvar (implode "A");
                                          Tyapp (implode "bool") []];
                                       Tyapp (implode "bool") []]))
                                (hol_Abs
                                   (hol_Var (implode "x1") (Tyvar (implode "A")))
                                   (hol_Comb
                                      (hol_Const (implode "!")
                                         (Tyapp (implode "fun")
                                            [Tyapp (implode "fun")
                                               [Tyvar (implode "A");
                                                Tyapp (implode "bool") []];
                                             Tyapp (implode "bool") []]))
                                      (hol_Abs
                                         (hol_Var (implode "x2")
                                            (Tyvar (implode "A")))
                                         (hol_Comb
                                            (hol_Comb
                                               (hol_Const (implode "==>")
                                                  (Tyapp (implode "fun")
                                                     [Tyapp (implode "bool") [];
                                                      Tyapp (implode "fun")
                                                        [Tyapp
                                                           (implode "bool")
                                                           [];
                                                         Tyapp
                                                           (implode "bool")
                                                           []]]))
                                               ((hol_Comb
                                                   (hol_Var (implode "f")
                                                      (Tyapp (implode "fun")
                                                         [Tyvar (implode "A");
                                                          Tyvar (implode "B")]))
                                                   (hol_Var (implode "x1")
                                                      (Tyvar (implode "A")))) ===
                                                (hol_Comb
                                                   (hol_Var (implode "f")
                                                      (Tyapp (implode "fun")
                                                         [Tyvar (implode "A");
                                                          Tyvar (implode "B")]))
                                                   (hol_Var (implode "x2")
                                                      (Tyvar (implode "A"))))))
                                            ((hol_Var (implode "x1")
                                                (Tyvar (implode "A"))) ===
                                             (hol_Var (implode "x2")
                                                (Tyvar (implode "A")))))))))))) ===
                    (hol_Abs
                       (hol_Var (implode "f")
                          (Tyapp (implode "fun")
                             [Tyvar (implode "A"); Tyvar (implode "B")]))
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
                                         [Tyvar (implode "A");
                                          Tyapp (implode "bool") []];
                                       Tyapp (implode "bool") []]))
                                (hol_Abs
                                   (hol_Var (implode "x2") (Tyvar (implode "A")))
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
                                                   [Tyvar (implode "A");
                                                    Tyvar (implode "B")]))
                                             (hol_Var (implode "x1")
                                                (Tyvar (implode "A")))) ===
                                          (hol_Comb
                                             (hol_Var (implode "f")
                                                (Tyapp (implode "fun")
                                                   [Tyvar (implode "A");
                                                    Tyvar (implode "B")]))
                                             (hol_Var (implode "x2")
                                                (Tyvar (implode "A"))))))
                                      ((hol_Var (implode "x1")
                                          (Tyvar (implode "A"))) ===
                                       (hol_Var (implode "x2")
                                          (Tyvar (implode "A"))))))))))))
                ctxt)))`;;

(* HOL4: Theorem tyvar_inst_exists[local] *)
let holAxiomsSyntax_tyvar_inst_exists = prove
 (`?i. (ty:A) = REV_ASSOCD (Tyvar a) i b`,
  EXISTS_TAC `[(ty:A,Tyvar a)]` THEN REWRITE_TAC[REV_ASSOCD]);;

let infinity_extends = prove
 (`!ctxt.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                 alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd)) ctxt))) /\
     DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))
              (IMAGE implode {"ONE_ONE", "ONTO"}) /\
     ~(implode "ind" IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "==>") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") [];
             Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "/\\") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") [];
             Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "!") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
              Tyapp (implode "bool") []]) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "?") =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
              Tyapp (implode "bool") []]) /\
     FLOOKUP (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) (implode "~") =
     SOME (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []])
     ==> mk_infinity_ctxt ctxt extends ctxt`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def; FST; SND] o
              MATCH_MP theory_ok_sig) THEN
  QPAT_X_ASSUM "DISJOINT _ _" (STRIP_ASSUME_TAC o
    REWRITE_RULE[IMAGE_CLAUSES; DISJOINT_INSERT; DISJOINT_EMPTY] o
    ONCE_REWRITE_RULE[DISJOINT_SYM]) THEN
  REWRITE_TAC[mk_infinity_ctxt_def] THEN
  MATCH_MP_TAC CBOOLAUX_extends_CONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS updates_rules)) THEN
    REWRITE_TAC[CBOOLAUX_has_type_welltyped] THEN CBOOLAUX_EVAL CBOOLAUX_AX_THMS;
    MATCH_MP_TAC CBOOLAUX_extends_CONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC (el 3 (CONJUNCTS updates_rules)) THEN CBOOLAUX_EVAL CBOOLAUX_AX_THMS;
      REPEAT CBOOLAUX_STEP_TAC THEN REWRITE_TAC[extends_def; RTC_REFL]]]);;
