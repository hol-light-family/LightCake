(* ========================================================================= *)
(* term: port of HOL4 examples/algorithms/unification/triangular/           *)
(* first-order/termScript.sml (HOL4 library used by CakeML v3479):          *)
(* the first-order terms of triangular unification.                         *)
(*                                                                           *)
(* Names: the HOL4 type term is term_term here and its constructor Var is   *)
(* term_Var (CakeML has a type term and a constructor Var of its own); the  *)
(* constructors Pair and Const keep their names.  The HOL4 datatype         *)
(* theorems term_11, term_distinct, term_induction, term_nchotomy and the   *)
(* case constant term_CASE are term_term_11, term_term_distinct,             *)
(* term_term_INDUCT, term_term_nchotomy and term_term_CASE.  HOL4 vars is   *)
(* term_vars (vars is a common variable name) with term_vars_def; the other *)
(* theorem names are HOL4's.  HOL4 bag literals: the bag of x is            *)
(* BAG_INSERT x EMPTY_BAG (bag.ml).                                          *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/bag.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The datatype.                                                             *)
(* ------------------------------------------------------------------------- *)

let term_term_INDUCT,term_term_RECURSION = cake_type
  "term_term = term_Var num | Pair term_term term_term | Const A";;

let term_term_distinct = distinctness "term_term";;
let term_term_11 = injectivity "term_term";;
let term_term_CASE = case_def "term_term";;
let term_term_case_eq = case_eq "term_term";;
let term_term_nchotomy = cases "term_term";;
let term_term_size_def = type_size_def "term_term";;

(* ------------------------------------------------------------------------- *)
(* pair_count, term_vars (HOL4 vars), varb.                                  *)
(* ------------------------------------------------------------------------- *)

let pair_count_def = cake_def
  `(pair_count (term_Var v) = 0) /\
   (pair_count (Const (c:A)) = 0) /\
   (pair_count (Pair t1 t2) = 1 + pair_count t1 + pair_count t2)`;;

let term_vars_def = cake_def
  `(term_vars (term_Var x) = {x}) /\
   (term_vars (Pair t1 t2) = term_vars t1 UNION term_vars t2) /\
   (term_vars (Const (c:A)) = {})`;;

let FINITE_vars = prove
 (`!t:A term_term. FINITE (term_vars t)`,
  MATCH_MP_TAC term_term_INDUCT THEN
  REWRITE_TAC[term_vars_def; FINITE_INSERT; FINITE_EMPTY; FINITE_UNION] THEN
  MESON_TAC[]);;

let varb_def = cake_def
  `(varb (term_Var s) = BAG_INSERT s EMPTY_BAG) /\
   (varb (Pair t1 t2) = BAG_UNION (varb t1) (varb t2)) /\
   (varb (Const (c:A)) = EMPTY_BAG)`;;

let FINITE_varb = prove
 (`!t:A term_term. FINITE_BAG (varb t)`,
  MATCH_MP_TAC term_term_INDUCT THEN
  ASM_SIMP_TAC[varb_def; FINITE_BAG_THM; FINITE_BAG_UNION]);;

let IN_varb_vars = prove
 (`!e (t:A term_term). BAG_IN e (varb t) <=> e IN term_vars t`,
  GEN_TAC THEN MATCH_MP_TAC term_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[varb_def; term_vars_def; BAG_IN_BAG_INSERT; BAG_IN_BAG_UNION;
                  NOT_IN_EMPTY_BAG; IN_INSERT; IN_UNION; NOT_IN_EMPTY]);;

let _ = cake_add_simps
  [pair_count_def; term_vars_def; FINITE_vars; varb_def; FINITE_varb; IN_varb_vars];;
