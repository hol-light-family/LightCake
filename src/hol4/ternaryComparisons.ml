(* ========================================================================= *)
(* ternaryComparisons: port of HOL4 src/sort/ternaryComparisonsScript.sml    *)
(* (HOL4 library).  The three-valued type ordering = LESS | EQUAL | GREATER  *)
(* (HOL4 toto calls it cpn, comparison writes Less, Equal, Greater) and the *)
(* comparison functions for bool, pairs, options, num and lists.            *)
(*                                                                           *)
(* The constants have HOL4's most general types: list_compare, for          *)
(* example, takes a comparison of type A->B->ordering.                       *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The datatype and its HOL4 theorems.                                       *)
(* ------------------------------------------------------------------------- *)

let ordering_INDUCT,ordering_RECURSION =
  cake_type "ordering = LESS | EQUAL | GREATER";;

(* HOL4: ordering_induction, ordering_Axiom *)

let ordering_induction = ordering_INDUCT;;

let ordering_Axiom = ordering_RECURSION;;

let ordering_case_def = case_def "ordering";;

let ordering_case_eq = case_eq "ordering";;

let ordering_nchotomy = prove
 (`!a. a = LESS \/ a = EQUAL \/ a = GREATER`,
  MATCH_MP_TAC ordering_INDUCT THEN REWRITE_TAC[]);;

let ordering_distinct = prove
 (`~(LESS = EQUAL) /\ ~(LESS = GREATER) /\ ~(EQUAL = GREATER)`,
  REWRITE_TAC[distinctness "ordering"]);;

(* HOL4 ordering_eq_dec: the equality decision of the type, as rewrites *)

let ordering_eq_dec = prove
 (`(!x:ordering. x = x <=> T) /\
   (LESS = EQUAL <=> F) /\ (LESS = GREATER <=> F) /\
   (EQUAL = LESS <=> F) /\ (EQUAL = GREATER <=> F) /\
   (GREATER = LESS <=> F) /\ (GREATER = EQUAL <=> F)`,
  REWRITE_TAC[distinctness "ordering"]);;

(* ------------------------------------------------------------------------- *)
(* Comparison functions.                                                     *)
(* ------------------------------------------------------------------------- *)

let bool_compare_def = cake_def
  `(bool_compare T T = EQUAL) /\
   (bool_compare F F = EQUAL) /\
   (bool_compare T F = GREATER) /\
   (bool_compare F T = LESS)`;;

(* Lifting comparison functions through various type operators *)

let pair_compare_def = cake_def
  `pair_compare (c1:A->B->ordering) (c2:C->D->ordering) (a,b) (x,y) =
     match c1 a x with
       EQUAL -> c2 b y
     | res -> res`;;

let option_compare_def = cake_def
  `(option_compare (c:A->B->ordering) NONE NONE = EQUAL) /\
   (option_compare c NONE (SOME v0) = LESS) /\
   (option_compare c (SOME v3) NONE = GREATER) /\
   (option_compare c (SOME v1) (SOME v2) = c v1 v2)`;;

let option_compare_ind = prove
 (`!P. (!c:A->B->ordering. P c (NONE:A option) (NONE:B option)) /\
       (!c v0. P c NONE (SOME v0)) /\
       (!c v3. P c (SOME v3) NONE) /\
       (!c v1 v2. P c (SOME v1) (SOME v2))
       ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:A->B->ordering` THEN
  MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
  MATCH_MP_TAC option_INDUCT THEN ASM_REWRITE_TAC[]);;

let num_compare_def = cake_def
  `num_compare n1 n2 =
     if n1 = n2 then EQUAL else if n1 < n2 then LESS else GREATER`;;

(* General results on lists *)

let list_compare_def = cake_def_wf
  `measure (\p:(A->B->ordering)#(A list)#(B list). LENGTH (FST (SND p)))`
  (REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN ARITH_TAC)
  `(list_compare (cmp:A->B->ordering) [] [] = EQUAL) /\
   (list_compare cmp [] (CONS v4 v5) = LESS) /\
   (list_compare cmp (CONS v8 v9) [] = GREATER) /\
   (list_compare cmp (CONS x l1) (CONS y l2) =
      match cmp x y with
        LESS -> LESS
      | EQUAL -> list_compare cmp l1 l2
      | GREATER -> GREATER)`;;

let list_compare_ind = cake_ind "list_compare";;

let compare_equal = prove
 (`!cmp:A->A->ordering.
     (!x y. cmp x y = EQUAL <=> x = y)
     ==> !l1 l2. list_compare cmp l1 l2 = EQUAL <=> l1 = l2`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_compare_def; NOT_CONS_NIL; CONS_11;
                  distinctness "ordering"] THEN
  MP_TAC(ISPEC `(cmp:A->A->ordering) h h'` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def; distinctness "ordering"] THEN
  ASM_MESON_TAC[distinctness "ordering"]);;

(* looks out of place *)

let list_merge_def = cake_def_wf
  `measure (\p:(A->A->bool)#(A list)#(A list).
              LENGTH (FST (SND p)) + LENGTH (SND (SND p)))`
  (REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN ARITH_TAC)
  `(list_merge (a_lt:A->A->bool) l1 [] = l1) /\
   (list_merge a_lt [] (CONS v4 v5) = CONS v4 v5) /\
   (list_merge a_lt (CONS x l1) (CONS y l2) =
      if a_lt x y then CONS x (list_merge a_lt l1 (CONS y l2))
      else CONS y (list_merge a_lt (CONS x l1) l2))`;;

let list_merge_ind = cake_ind "list_merge";;

let invert_comparison_def = cake_def
  `(invert_comparison GREATER = LESS) /\
   (invert_comparison LESS = GREATER) /\
   (invert_comparison EQUAL = EQUAL)`;;

let invert_eq_EQUAL = prove
 (`!x. invert_comparison x = EQUAL <=> x = EQUAL`,
  MATCH_MP_TAC ordering_INDUCT THEN
  REWRITE_TAC[invert_comparison_def; distinctness "ordering"]);;

(* below are 2 leaking assumptions when installing hol-ring *)

let ordering_distinct1 = prove
 (`~(EQUAL = LESS)`,
  REWRITE_TAC[distinctness "ordering"]);;

let ordering_distinct2 = prove
 (`~(GREATER = EQUAL)`,
  REWRITE_TAC[distinctness "ordering"]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [bool_compare_def; option_compare_def; invert_comparison_def;
   invert_eq_EQUAL];;
