(* ========================================================================= *)
(* transfer: port of HOL4 src/transfer/transferScript.sml (HOL4 library     *)
(* used by CakeML v3479), the part that rmfmap and CakeML's unify use: the  *)
(* relation combinator FUN_REL (infix |==>, HOL4 quotient$===>) and the     *)
(* uniqueness and totality properties of relations.                         *)
(*                                                                           *)
(* Notes: HOL4's transfer automation (transferLib) is not ported, nor the  *)
(* rule theorems that only feed it (ALL_IFF, ALL_surj_RDOM, ..., the       *)
(* PAIR/OPTREL/LIST_REL rules).  HOL4 transfer$total is transfer_total here *)
(* (vocab.ml's total is relation$total), with transfer_total_def; HOL4      *)
(* combin$C (written flip in transferScript) is vocab.ml's flip.            *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/basic.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Uniqueness, totality, surjectivity.                                       *)
(* ------------------------------------------------------------------------- *)

let right_unique_def = new_definition
  `right_unique (R:A->B->bool) <=> !a b1 b2. R a b1 /\ R a b2 ==> b1 = b2`;;

let right_unique_EQ = prove
 (`right_unique ((=):A->A->bool)`,
  REWRITE_TAC[right_unique_def] THEN MESON_TAC[]);;

let left_unique_def = new_definition
  `left_unique (R:A->B->bool) <=> !a1 a2 b. R a1 b /\ R a2 b ==> a1 = a2`;;

let left_unique_EQ = prove
 (`left_unique ((=):A->A->bool)`,
  REWRITE_TAC[left_unique_def] THEN MESON_TAC[]);;

let bi_unique_def = new_definition
  `bi_unique (R:A->B->bool) <=> left_unique R /\ right_unique R`;;

let bi_unique_implied = prove
 (`!r:A->B->bool. left_unique r /\ right_unique r ==> bi_unique r`,
  REWRITE_TAC[bi_unique_def]);;

let bi_unique_EQ = prove
 (`bi_unique ((=):A->A->bool)`,
  REWRITE_TAC[bi_unique_def; left_unique_EQ; right_unique_EQ]);;

let transfer_total_def = new_definition
  `transfer_total (R:A->B->bool) <=> !x. ?y. R x y`;;

let surj_def = new_definition
  `surj (R:A->B->bool) <=> !y. ?x. R x y`;;

let bitotal_def = new_definition
  `bitotal (R:A->B->bool) <=> transfer_total R /\ surj R`;;

let bitotal_implied = prove
 (`!r:A->B->bool. transfer_total r /\ surj r ==> bitotal r`,
  REWRITE_TAC[bitotal_def]);;

let total_EQ = prove
 (`transfer_total ((=):A->A->bool)`,
  REWRITE_TAC[transfer_total_def] THEN MESON_TAC[]);;

let surj_EQ = prove
 (`surj ((=):A->A->bool)`,
  REWRITE_TAC[surj_def] THEN MESON_TAC[]);;

let bitotal_EQ = prove
 (`bitotal ((=):A->A->bool)`,
  REWRITE_TAC[bitotal_def; total_EQ; surj_EQ]);;

let equalityp_def = new_definition
  `equalityp (A:A->A->bool) <=> A = (=)`;;

let eq_equalityp = prove
 (`equalityp ((=):A->A->bool)`,
  REWRITE_TAC[equalityp_def]);;

let equalityp_applied = prove
 (`!A (x:A). equalityp A ==> A x x`,
  SIMP_TAC[equalityp_def]);;

(* ------------------------------------------------------------------------- *)
(* FUN_REL.                                                                  *)
(* ------------------------------------------------------------------------- *)

let FUN_REL_def = new_definition
  `FUN_REL (R1:A->B->bool) (R2:C->D->bool) f g <=>
     !a b. R1 a b ==> R2 (f a) (g b)`;;

parse_as_infix("|==>",(13,"right"));;
override_interface("|==>",`FUN_REL:(A->B->bool)->(C->D->bool)->(A->C)->(B->D)->bool`);;

let FUN_REL_COMB = prove
 (`!(AB:A->B->bool) (CD:C->D->bool) f g a b.
     (AB |==> CD) f g /\ AB a b ==> CD (f a) (g b)`,
  REWRITE_TAC[FUN_REL_def] THEN MESON_TAC[]);;

let FUN_REL_COMB_EQ = prove
 (`!(AB1:A->B->bool) AB2 (CD:C->D->bool) f g a b.
     (AB1 |==> CD) f g /\ AB2 a b ==> AB1 = AB2 ==> CD (f a) (g b)`,
  REWRITE_TAC[FUN_REL_def] THEN MESON_TAC[]);;

let FUN_REL_IFF_IMP = prove
 (`!(AB:A->B->bool) P Q.
     (AB |==> (=)) P Q ==> (AB |==> (==>)) P Q /\ (AB |==> flip (==>)) P Q`,
  REWRITE_TAC[FUN_REL_def; flip_DEF] THEN MESON_TAC[]);;

let equalityp_FUN_REL = prove
 (`!(AB:A->A->bool) (CD:B->B->bool).
     equalityp AB /\ equalityp CD ==> equalityp (AB |==> CD)`,
  SIMP_TAC[equalityp_def; FUN_REL_def; FUN_EQ_THM] THEN MESON_TAC[]);;

let EQ_bi_unique = prove
 (`!AB:A->B->bool. bi_unique AB ==> (AB |==> AB |==> (=)) (=) (=)`,
  REWRITE_TAC[FUN_REL_def; bi_unique_def; left_unique_def; right_unique_def] THEN
  MESON_TAC[]);;

let surj_eqeq = prove
 (`surj (((=):A->A->bool) |==> ((=):B->B->bool))`,
  REWRITE_TAC[surj_def; FUN_REL_def] THEN GEN_TAC THEN
  EXISTS_TAC `y:A->B` THEN MESON_TAC[]);;

let FUN_REL_iff_imp_strengthen = prove
 (`!(AB:A->B->bool) P Q. (AB |==> (=)) P Q ==> (AB |==> (==>)) P Q`,
  REWRITE_TAC[FUN_REL_def] THEN MESON_TAC[]);;

let FUN_REL_iff_cimp_strengthen = prove
 (`!(AB:A->B->bool) P Q. (AB |==> (=)) P Q ==> (AB |==> flip (==>)) P Q`,
  REWRITE_TAC[FUN_REL_def; flip_DEF] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* OPTREL (option relation lifting, vocab.ml).                               *)
(* ------------------------------------------------------------------------- *)

let OPTREL_left_unique = prove
 (`!AB:A->B->bool. left_unique AB ==> left_unique (OPTREL AB)`,
  REWRITE_TAC[left_unique_def; FORALL_OPTION; OPTREL_THM; option_DISTINCT;
              option_INJ] THEN MESON_TAC[]);;

let OPTREL_right_unique = prove
 (`!AB:A->B->bool. right_unique AB ==> right_unique (OPTREL AB)`,
  REWRITE_TAC[right_unique_def; FORALL_OPTION; OPTREL_THM; option_DISTINCT;
              option_INJ] THEN MESON_TAC[]);;

let equalityp_OPTREL = prove
 (`!AB:A->A->bool. equalityp AB ==> equalityp (OPTREL AB)`,
  SIMP_TAC[equalityp_def; OPTREL_eq]);;
