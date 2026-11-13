(* ========================================================================= *)
(* toto: port of HOL4 src/finite_maps/totoScript.sml (HOL4 library).         *)
(* Basic theory of total orders modeled not as in relation theory, but      *)
(* rather in imitation of ML's facilities stemming from the 3-element       *)
(* "order" type - here called "cpn" for "comparison".                       *)
(*                                                                           *)
(* HOL4 cpn is the type ordering of ternaryComparisons.ml and HOL4 'a comp  *)
(* is A->A->ordering; StrongOrder and StrongLinearOrder are basic.ml's.     *)
(* Not ported: the type 'a toto with apto and TO and the theorems about it  *)
(* (its type definition needs a total order on every type, i.e. the         *)
(* well-ordering theorem), the theorems about HOL4 relation notions that    *)
(* the port does not have (LinearOrder, WeakLinearOrder, inv, STRORD), the  *)
(* numeral and qk_numOrd machinery, and charOrd (needs ORD of string4.ml).  *)
(* In TotOrd_TO_of_LO, HOL4 LinearOrder r is written out as                 *)
(* (antisymmetric r /\ transitive r) /\ trichotomous r.                     *)
(* ========================================================================= *)

needs "hol4/basic.ml";;
needs "hol4/ternaryComparisons.ml";;

type_invention_error := true;;

(* HOL4 cpn_distinct, cpn_case_def, cpn_nchotomy (vals of the script) *)

let cpn_distinct = ordering_distinct;;

let cpn_case_def = ordering_case_def;;

let cpn_nchotomy = ordering_nchotomy;;

(* ------------------------------------------------------------------------- *)
(* Being a (cpn-valued) total order.                                         *)
(* ------------------------------------------------------------------------- *)

let TotOrd = new_definition
  `TotOrd (c:A->A->ordering) <=>
     (!x y. c x y = EQUAL <=> x = y) /\
     (!x y. c x y = GREATER <=> c y x = LESS) /\
     (!x y z. c x y = LESS /\ c y z = LESS ==> c x z = LESS)`;;

let TO_of_LinearOrder = new_definition
  `TO_of_LinearOrder (r:A->A->bool) x y =
     if x = y then EQUAL else if r x y then LESS else GREATER`;;

(* lemma to ease use of "trichotomous" and work with disjunctions *)

let trichotomous_ALT = prove
 (`!R:A->A->bool. trichotomous R <=> !x y. ~R x y /\ ~R y x ==> x = y`,
  REWRITE_TAC[trichotomous_DEF] THEN MESON_TAC[]);;

(* HOL4 LinearOrder r, i.e. Order r /\ trichotomous r, written out *)

let TotOrd_TO_of_LO = prove
 (`!r:A->A->bool.
     (antisymmetric r /\ transitive r) /\ trichotomous r
     ==> TotOrd (TO_of_LinearOrder r)`,
  REWRITE_TAC[antisymmetric_DEF; transitive_DEF; trichotomous_DEF;
              TotOrd; TO_of_LinearOrder] THEN
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"] THEN
  ASM_MESON_TAC[]);;

(* Utility theorem for equality of pairs: *)

let SPLIT_PAIRS = prove
 (`!x y:A#B. x = y <=> FST x = FST y /\ SND x = SND y`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let all_cpn_distinct = prove
 (`(~(LESS = EQUAL) /\ ~(LESS = GREATER) /\ ~(EQUAL = GREATER)) /\
   (~(EQUAL = LESS) /\ ~(GREATER = LESS) /\ ~(GREATER = EQUAL))`,
  REWRITE_TAC[distinctness "ordering"]);;

let TO_equal_eq = prove
 (`!c:A->A->ordering. TotOrd c ==> (!x y. c x y = EQUAL <=> x = y)`,
  SIMP_TAC[TotOrd]);;

let TO_refl = prove
 (`!c:A->A->ordering. TotOrd c ==> (!x. c x x = EQUAL)`,
  SIMP_TAC[TotOrd]);;

let TO_antisym = prove
 (`!c:A->A->ordering. TotOrd c ==> (!x y. c x y = GREATER <=> c y x = LESS)`,
  SIMP_TAC[TotOrd]);;

let TO_cpn_eqn = prove
 (`!c. TotOrd (c:A->A->ordering)
       ==> (!x y. c x y = LESS ==> ~(x = y)) /\
           (!x y. c x y = GREATER ==> ~(x = y)) /\
           (!x y. c x y = EQUAL ==> x = y)`,
  REWRITE_TAC[TotOrd] THEN MESON_TAC[distinctness "ordering"]);;

(* ------------------------------------------------------------------------- *)
(* Relations from total orders.                                              *)
(* ------------------------------------------------------------------------- *)

let WeakLinearOrder_of_TO = cake_def
  `WeakLinearOrder_of_TO (c:A->A->ordering) x y =
     match c x y with LESS -> T | EQUAL -> T | GREATER -> F`;;

let StrongLinearOrder_of_TO = cake_def
  `StrongLinearOrder_of_TO (c:A->A->ordering) x y =
     match c x y with LESS -> T | EQUAL -> F | GREATER -> F`;;

(* Converse of a total order *)

let TO_inv = new_definition
  `TO_inv (c:A->A->ordering) x y = c y x`;;

let TotOrd_inv = prove
 (`!c:A->A->ordering. TotOrd c ==> TotOrd (TO_inv c)`,
  REWRITE_TAC[TotOrd; TO_inv] THEN MESON_TAC[]);;

let TO_inv_TO_inv = prove
 (`!c:A->A->ordering. TO_inv (TO_inv c) = c`,
  REWRITE_TAC[FUN_EQ_THM; TO_inv]);;

(* ------------------------------------------------------------------------- *)
(* Lexicographic order.                                                      *)
(* ------------------------------------------------------------------------- *)

let LEX_ALT = prove
 (`!R:A->A->bool U:B->B->bool c d.
     (R LEX U) c d <=> R (FST c) (FST d) \/ FST c = FST d /\ U (SND c) (SND d)`,
  REWRITE_TAC[LEX_DEF]);;

parse_as_infix("lexTO",(14,"right"));;

let lexTO = new_definition
  `(R:A->A->ordering) lexTO (V:B->B->ordering) =
     TO_of_LinearOrder (StrongLinearOrder_of_TO R LEX StrongLinearOrder_of_TO V)`;;

let lexTO_thm = prove
 (CASE_TERM
  `!R:A->A->ordering V:B->B->ordering.
     TotOrd R /\ TotOrd V
     ==> !x y. (R lexTO V) x y =
               match R (FST x) (FST y) with
                 LESS -> LESS
               | EQUAL -> V (SND x) (SND y)
               | GREATER -> GREATER`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lexTO; TO_of_LinearOrder; StrongLinearOrder_of_TO; LEX_DEF;
              SPLIT_PAIRS] THEN
  SUBGOAL_THEN `FST (x:A#B) = FST (y:A#B) <=>
                (R:A->A->ordering) (FST x) (FST y) = EQUAL` SUBST1_TAC THENL
   [ASM_MESON_TAC[TO_equal_eq]; ALL_TAC] THEN
  SUBGOAL_THEN `SND (x:A#B) = SND (y:A#B) <=>
                (V:B->B->ordering) (SND x) (SND y) = EQUAL` SUBST1_TAC THENL
   [ASM_MESON_TAC[TO_equal_eq]; ALL_TAC] THEN
  MP_TAC(ISPEC `(R:A->A->ordering) (FST (x:A#B)) (FST (y:A#B))`
               ordering_nchotomy) THEN
  MP_TAC(ISPEC `(V:B->B->ordering) (SND (x:A#B)) (SND (y:A#B))`
               ordering_nchotomy) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ordering_case_def; distinctness "ordering"]);;

let lexTO_ALT = prove
 (CASE_TERM
  `!R:A->A->ordering V:B->B->ordering.
     TotOrd R /\ TotOrd V
     ==> !r u r' u'. (R lexTO V) (r,u) (r',u') =
                     match R r r' with
                       LESS -> LESS
                     | EQUAL -> V u u'
                     | GREATER -> GREATER`,
  SIMP_TAC[lexTO_thm; FST; SND]);;

let TO_lexTO = prove
 (`!R:A->A->ordering V:B->B->ordering.
     TotOrd R /\ TotOrd V ==> TotOrd (R lexTO V)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[TotOrd; MATCH_MP lexTO_thm th]) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TotOrd; FORALL_PAIR_THM; PAIR_EQ; FST; SND; ordering_case_eq;
              distinctness "ordering"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* num, lists, images.                                                       *)
(* ------------------------------------------------------------------------- *)

let numOrd = new_definition
  `numOrd = TO_of_LinearOrder ((<):num->num->bool)`;;

let TO_numOrd = prove
 (`TotOrd numOrd`,
  REWRITE_TAC[numOrd] THEN MATCH_MP_TAC TotOrd_TO_of_LO THEN
  REWRITE_TAC[antisymmetric_DEF; transitive_DEF; trichotomous_DEF] THEN
  ARITH_TAC);;

let listorder = cake_def
  `(listorder (V:A->A->bool) l [] <=> F) /\
   (listorder V [] (CONS s m) <=> T) /\
   (listorder V (CONS r l) (CONS s m) <=> V r s \/ r = s /\ listorder V l m)`;;

let imageOrd = new_definition
  `imageOrd (f:A->C) (cp:C->C->ordering) a b = cp (f a) (f b)`;;

let TO_injection = prove
 (`!cp:C->C->ordering. TotOrd cp ==> !f:D->C. ONE_ONE f ==> TotOrd (imageOrd f cp)`,
  REWRITE_TAC[TotOrd; imageOrd; ONE_ONE] THEN MESON_TAC[]);;

let StrongLinearOrder_of_TO_TO_of_LinearOrder = prove
 (`!R:A->A->bool.
     irreflexive R ==> StrongLinearOrder_of_TO (TO_of_LinearOrder R) = R`,
  REWRITE_TAC[irreflexive_DEF; FUN_EQ_THM; StrongLinearOrder_of_TO;
              TO_of_LinearOrder] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ordering_case_def]);;

let TO_of_LinearOrder_LEX = prove
 (`!R:A->A->bool V:B->B->bool.
     irreflexive R /\ irreflexive V
     ==> TO_of_LinearOrder (R LEX V) =
         (TO_of_LinearOrder R) lexTO (TO_of_LinearOrder V)`,
  SIMP_TAC[lexTO; StrongLinearOrder_of_TO_TO_of_LinearOrder]);;

(* ------------------------------------------------------------------------- *)
(* Strong linear orders (HOL4 relation StrongLinearOrder, from basic.ml).   *)
(* ------------------------------------------------------------------------- *)

let LCMPAUX_StrongLinearOrder_of_TO_LESS = prove
 (`!c:A->A->ordering x y. StrongLinearOrder_of_TO c x y <=> c x y = LESS`,
  REPEAT GEN_TAC THEN REWRITE_TAC[StrongLinearOrder_of_TO] THEN
  MP_TAC(ISPEC `(c:A->A->ordering) x y` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ordering_case_def; distinctness "ordering"]);;

let Strong_Strong_of_TO = prove
 (`!c:A->A->ordering.
     TotOrd c ==> StrongLinearOrder (StrongLinearOrder_of_TO c)`,
  GEN_TAC THEN REWRITE_TAC[TotOrd] THEN STRIP_TAC THEN
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_DEF; transitive_DEF;
              trichotomous_DEF; LCMPAUX_StrongLinearOrder_of_TO_LESS] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ASM_MESON_TAC[distinctness "ordering"];
    ASM_MESON_TAC[];
    MP_TAC(ISPEC `(c:A->A->ordering) a b` ordering_nchotomy) THEN
    ASM_MESON_TAC[]]);;

let TotOrd_TO_of_Strong = prove
 (`!r:A->A->bool. StrongLinearOrder r ==> TotOrd (TO_of_LinearOrder r)`,
  GEN_TAC THEN REWRITE_TAC[StrongLinearOrder; StrongOrder] THEN STRIP_TAC THEN
  MATCH_MP_TAC TotOrd_TO_of_LO THEN ASM_REWRITE_TAC[antisymmetric_DEF] THEN
  ASM_MESON_TAC[irreflexive_DEF; transitive_DEF]);;

let TO_of_less_rel = prove
 (`!r:A->A->bool.
     StrongLinearOrder r ==> !x y. TO_of_LinearOrder r x y = LESS <=> r x y`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_DEF;
              TO_of_LinearOrder] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "ordering"]);;

let TO_of_greater_ler = prove
 (`!r:A->A->bool.
     StrongLinearOrder r ==> !x y. TO_of_LinearOrder r x y = GREATER <=> r y x`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_DEF; transitive_DEF;
              trichotomous_DEF; TO_of_LinearOrder] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "ordering"] THEN ASM_MESON_TAC[]);;

let StrongOrder_ALT = prove
 (`!Z:A->A->bool. StrongOrder Z <=> irreflexive Z /\ transitive Z`,
  REWRITE_TAC[StrongOrder]);;

let SLO_LEX = prove
 (`!R:A->A->bool V:B->B->bool.
     StrongLinearOrder R /\ StrongLinearOrder V
     ==> StrongLinearOrder (R LEX V)`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_DEF; transitive_DEF;
              trichotomous_DEF; FORALL_PAIR_THM; LEX_THM; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  ASM_MESON_TAC[]);;

let StrongLinearOrder_LESS = prove
 (`StrongLinearOrder ((<):num->num->bool)`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_DEF; transitive_DEF;
              trichotomous_DEF] THEN
  ARITH_TAC);;

let SLO_listorder = prove
 (`!V:A->A->bool. StrongLinearOrder V ==> StrongLinearOrder (listorder V)`,
  GEN_TAC THEN
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_DEF; transitive_DEF;
              trichotomous_DEF] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[listorder];
    LIST_INDUCT_TAC THEN MAP_EVERY X_GEN_TAC [`y:A list`; `z:A list`] THEN
    STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
    STRUCT_CASES_TAC(ISPEC `z:A list` list_CASES) THEN
    ASM_REWRITE_TAC[listorder] THEN ASM_MESON_TAC[];
    LIST_INDUCT_TAC THEN X_GEN_TAC `y:A list` THEN
    STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
    ASM_REWRITE_TAC[listorder; NOT_CONS_NIL; CONS_11] THEN ASM_MESON_TAC[]]);;
