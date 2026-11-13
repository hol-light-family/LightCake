(* ========================================================================= *)
(* comparison: port of HOL4 src/finite_maps/comparisonScript.sml (HOL4      *)
(* library).  Good comparison functions (good_cmp) and the comparison        *)
(* functions of ternaryComparisons.ml.                                       *)
(*                                                                           *)
(* HOL4 overloads, expanded at their uses: Less, Equal, Greater are LESS,   *)
(* EQUAL, GREATER; option_cmp, list_cmp, pair_cmp, bool_cmp, num_cmp are    *)
(* option_compare, list_compare, pair_compare, bool_compare, num_compare.   *)
(* HOL4 comparison num_cmp_def is comparison_num_cmp_def here (num_cmp_def  *)
(* is the name of semanticPrimitives' own num_cmp).  Not ported: char_cmp   *)
(* and string_cmp (stringTheory char_compare and string_compare are not in  *)
(* the port), list_cmp_ListOrd and string_cmp_stringto (the type 'a toto).  *)
(* ========================================================================= *)

needs "hol4/list.ml";;
needs "hol4/toto.ml";;

type_invention_error := true;;

let good_cmp_def = new_definition
  `good_cmp (cmp:A->A->ordering) <=>
     (!x. cmp x x = EQUAL) /\
     (!x y. cmp x y = EQUAL ==> cmp y x = EQUAL) /\
     (!x y. cmp x y = GREATER <=> cmp y x = LESS) /\
     (!x y z. cmp x y = EQUAL /\ cmp y z = LESS ==> cmp x z = LESS) /\
     (!x y z. cmp x y = LESS /\ cmp y z = EQUAL ==> cmp x z = LESS) /\
     (!x y z. cmp x y = EQUAL /\ cmp y z = EQUAL ==> cmp x z = EQUAL) /\
     (!x y z. cmp x y = LESS /\ cmp y z = LESS ==> cmp x z = LESS)`;;

let good_cmp_thm = prove
 (`!cmp:A->A->ordering.
     good_cmp cmp <=>
     (!x. cmp x x = EQUAL) /\
     (!x y z.
        (cmp x y = GREATER <=> cmp y x = LESS) /\
        (cmp x y = LESS /\ cmp y z = EQUAL ==> cmp x z = LESS) /\
        (cmp x y = LESS /\ cmp y z = LESS ==> cmp x z = LESS))`,
  GEN_TAC THEN REWRITE_TAC[good_cmp_def; FORALL_AND_THM] THEN EQ_TAC THENL
   [MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!x y. (cmp:A->A->ordering) x y = EQUAL ==> cmp y x = EQUAL`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `(cmp:A->A->ordering) y x` ordering_nchotomy) THEN
    ASM_MESON_TAC[distinctness "ordering"];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(cmp:A->A->ordering) x z` ordering_nchotomy) THEN
  ASM_MESON_TAC[distinctness "ordering"]);;

let cmp_thms = end_itlist CONJ
  [ordering_distinct; ordering_case_def; ordering_nchotomy; good_cmp_def];;

(* HOL4 option_cmp_def: option_compare_def *)

let option_cmp_def = option_compare_def;;

let option_cmp2_def = cake_def
  `(option_cmp2 (cmp:A->B->ordering) NONE NONE = EQUAL) /\
   (option_cmp2 cmp NONE (SOME y0) = GREATER) /\
   (option_cmp2 cmp (SOME x0) NONE = LESS) /\
   (option_cmp2 cmp (SOME x) (SOME y) = cmp x y)`;;

let option_cmp2_ind = prove
 (`!P. (!cmp:A->B->ordering. P cmp (NONE:A option) (NONE:B option)) /\
       (!cmp x. P cmp NONE (SOME x)) /\
       (!cmp x. P cmp (SOME x) NONE) /\
       (!cmp x y. P cmp (SOME x) (SOME y))
       ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `cmp:A->B->ordering` THEN
  MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
  MATCH_MP_TAC option_INDUCT THEN ASM_REWRITE_TAC[]);;

(* HOL4 pair_cmp_def: pair_compare_def on arbitrary pairs *)

let pair_cmp_def = prove
 (CASE_TERM
  `!c1:A->B->ordering c2:C->D->ordering x y.
     pair_compare c1 c2 x y =
     match c1 (FST x) (FST y) with
       LESS -> LESS
     | EQUAL -> c2 (SND x) (SND y)
     | GREATER -> GREATER`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_compare_def; FST; SND]);;

(* HOL4 bool_cmp_def, num_cmp_def: bool_compare_def, num_compare_def *)

let bool_cmp_def = bool_compare_def;;

let comparison_num_cmp_def = num_compare_def;;

(* ------------------------------------------------------------------------- *)
(* Relationship to toto.                                                     *)
(* ------------------------------------------------------------------------- *)

let TotOrder_imp_good_cmp = prove
 (`!cmp:A->A->ordering. TotOrd cmp ==> good_cmp cmp`,
  REWRITE_TAC[TotOrd; good_cmp_thm] THEN MESON_TAC[]);;

let TO_inv_invert = prove
 (`!c:A->A->ordering.
     TotOrd c ==> TO_inv c = CURRY (invert_comparison o UNCURRY c)`,
  GEN_TAC THEN REWRITE_TAC[TotOrd] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  REWRITE_TAC[TO_inv; CURRY_DEF; o_THM; UNCURRY_DEF] THEN
  MP_TAC(ISPEC `(c:A->A->ordering) x y` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[invert_comparison_def] THEN
  ASM_MESON_TAC[]);;

let option_cmp2_TO_inv = prove
 (`!c:A->A->ordering. option_cmp2 c = TO_inv (option_compare (TO_inv c))`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; TO_inv] THEN
  REWRITE_TAC[FORALL_OPTION_THM; option_cmp2_def; option_compare_def; TO_inv]);;

let pair_cmp_lexTO = prove
 (`!R:A->A->ordering V:B->B->ordering.
     TotOrd R /\ TotOrd V ==> pair_compare R V = R lexTO V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; pair_cmp_def] THEN
  ASM_SIMP_TAC[lexTO_thm]);;

let num_cmp_numOrd = prove
 (`num_compare = numOrd`,
  REWRITE_TAC[FUN_EQ_THM; num_compare_def; numOrd; TO_of_LinearOrder]);;

(* ------------------------------------------------------------------------- *)
(* cmps are good                                                             *)
(* ------------------------------------------------------------------------- *)

let option_cmp_good = prove
 (`!cmp:A->A->ordering. good_cmp cmp ==> good_cmp (option_compare cmp)`,
  GEN_TAC THEN REWRITE_TAC[good_cmp_def] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; option_compare_def; distinctness "ordering"] THEN
  ASM_MESON_TAC[]);;

let option_cmp2_good = prove
 (`!cmp:A->A->ordering. good_cmp cmp ==> good_cmp (option_cmp2 cmp)`,
  GEN_TAC THEN REWRITE_TAC[good_cmp_def] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; option_cmp2_def; distinctness "ordering"] THEN
  ASM_MESON_TAC[]);;

let list_cmp_good = prove
 (`!cmp:A->A->ordering. good_cmp cmp ==> good_cmp (list_compare cmp)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[good_cmp_thm; FORALL_AND_THM] THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[good_cmp_def]) THEN
  REPEAT CONJ_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_compare_def; ordering_case_def];
    LIST_INDUCT_TAC THEN X_GEN_TAC `y:A list` THEN
    STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
    ASM_REWRITE_TAC[list_compare_def; ordering_case_eq;
                    distinctness "ordering"] THEN
    ASM_MESON_TAC[];
    LIST_INDUCT_TAC THEN MAP_EVERY X_GEN_TAC [`y:A list`; `z:A list`] THEN
    STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
    STRUCT_CASES_TAC(ISPEC `z:A list` list_CASES) THEN
    ASM_REWRITE_TAC[list_compare_def; ordering_case_eq;
                    distinctness "ordering"] THEN
    ASM_MESON_TAC[];
    LIST_INDUCT_TAC THEN MAP_EVERY X_GEN_TAC [`y:A list`; `z:A list`] THEN
    STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
    STRUCT_CASES_TAC(ISPEC `z:A list` list_CASES) THEN
    ASM_REWRITE_TAC[list_compare_def; ordering_case_eq;
                    distinctness "ordering"] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 proves TotOrd_list_cmp through ListOrd (the type 'a toto); here it
   follows from list_cmp_good and compare_equal *)

let TotOrd_list_cmp = prove
 (`!c:A->A->ordering. TotOrd c ==> TotOrd (list_compare c)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_cmp_good o
              MATCH_MP TotOrder_imp_good_cmp) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP compare_equal o MATCH_MP TO_equal_eq) THEN
  REWRITE_TAC[TotOrd; good_cmp_def] THEN MESON_TAC[]);;

let pair_cmp_good = prove
 (`!cmp1:A->A->ordering cmp2:B->B->ordering.
     good_cmp cmp1 /\ good_cmp cmp2 ==> good_cmp (pair_compare cmp1 cmp2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_cmp_def] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_compare_def; ordering_case_eq;
              distinctness "ordering"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ASM_MESON_TAC[]);;

let bool_cmp_good = prove
 (`good_cmp bool_compare`,
  REWRITE_TAC[good_cmp_def; FORALL_BOOL_THM; bool_compare_def;
              distinctness "ordering"]);;

let num_cmp_good = prove
 (`good_cmp num_compare`,
  REWRITE_TAC[num_cmp_numOrd] THEN MATCH_MP_TAC TotOrder_imp_good_cmp THEN
  REWRITE_TAC[TO_numOrd]);;

(* ------------------------------------------------------------------------- *)
(* Congruence rules (HOL4 defncong).                                        *)
(* ------------------------------------------------------------------------- *)

let list_cmp_cong = prove
 (`!cmp l1 l2 cmp' l1' l2'.
     l1 = l1' /\ l2 = l2' /\
     (!x x'. MEM x l1' /\ MEM x' l2' ==> cmp x x' = cmp' x x')
     ==> list_compare (cmp:A->B->ordering) l1 l2 = list_compare cmp' l1' l2'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  SPEC_TAC(`l2':B list`,`l2:B list`) THEN SPEC_TAC(`l1':A list`,`l1:A list`) THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [ALL_TAC; MAP_EVERY X_GEN_TAC [`a:A`; `t1:A list`] THEN DISCH_TAC] THEN
  X_GEN_TAC `l2:B list` THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `t2:B list`
    SUBST1_TAC)) (ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[list_compare_def; MEM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(cmp:A->B->ordering) a b = cmp' a b` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `list_compare (cmp:A->B->ordering) t1 t2 = list_compare cmp' t1 t2`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; REFL_TAC]);;

let option_cmp_cong = prove
 (`!cmp v1 v2 cmp' v1' v2'.
     v1 = v1' /\ v2 = v2' /\
     (!x x'. v1' = SOME x /\ v2' = SOME x' ==> cmp x x' = cmp' x x')
     ==> option_compare (cmp:A->B->ordering) v1 v2 =
         option_compare cmp' v1' v2'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  SPEC_TAC(`v2':B option`,`v2:B option`) THEN
  SPEC_TAC(`v1':A option`,`v1:A option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; option_compare_def; option_DISTINCT;
              option_INJ] THEN
  MESON_TAC[]);;

let option_cmp2_cong = prove
 (`!cmp v1 v2 cmp' v1' v2'.
     v1 = v1' /\ v2 = v2' /\
     (!x x'. v1' = SOME x /\ v2' = SOME x' ==> cmp x x' = cmp' x x')
     ==> option_cmp2 (cmp:A->B->ordering) v1 v2 = option_cmp2 cmp' v1' v2'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  SPEC_TAC(`v2':B option`,`v2:B option`) THEN
  SPEC_TAC(`v1':A option`,`v1:A option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; option_cmp2_def; option_DISTINCT;
              option_INJ] THEN
  MESON_TAC[]);;

let pair_cmp_cong = prove
 (`!cmp1 cmp2 v1 v2 cmp1' cmp2' v1' v2'.
     v1 = v1' /\ v2 = v2' /\
     (!a b c d. v1' = (a,b) /\ v2' = (c,d) ==> cmp1 a c = cmp1' a c) /\
     (!a b c d. v1' = (a,b) /\ v2' = (c,d) ==> cmp2 b d = cmp2' b d)
     ==> pair_compare (cmp1:A->C->ordering) (cmp2:B->D->ordering) v1 v2 =
         pair_compare cmp1' cmp2' v1' v2'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  SPEC_TAC(`v2':C#D`,`v2:C#D`) THEN SPEC_TAC(`v1':A#B`,`v1:A#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; pair_compare_def] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `c:C`; `d:D`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cmp1:A->C->ordering) a c = cmp1' a c` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(cmp2:B->D->ordering) b d = cmp2' b d` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Transitivity, antisymmetry.                                               *)
(* ------------------------------------------------------------------------- *)

let good_cmp_trans = prove
 (`!cmp:A->A->ordering.
     good_cmp cmp ==> transitive (\(k:A,v:B) (k',v'). cmp k k' = LESS)`,
  REWRITE_TAC[good_cmp_def; transitive_DEF; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

let good_cmp_Less_trans = prove
 (`!cmp:A->A->ordering. good_cmp cmp ==> transitive (\k k'. cmp k k' = LESS)`,
  REWRITE_TAC[good_cmp_def; transitive_DEF] THEN MESON_TAC[]);;

let good_cmp_Less_irrefl_trans = prove
 (`!cmp:A->A->ordering.
     good_cmp cmp
     ==> irreflexive (\k k'. cmp k k' = LESS) /\
         transitive (\k k'. cmp k k' = LESS)`,
  SIMP_TAC[good_cmp_Less_trans] THEN
  SIMP_TAC[good_cmp_def; irreflexive_DEF; distinctness "ordering"]);;

let bool_cmp_antisym = prove
 (`!x y. bool_compare x y = EQUAL <=> x = y`,
  REWRITE_TAC[FORALL_BOOL_THM; bool_compare_def; distinctness "ordering"]);;

let num_cmp_antisym = prove
 (`!x y. num_compare x y = EQUAL <=> x = y`,
  REWRITE_TAC[num_compare_def] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"]);;

let list_cmp_antisym = prove
 (`!cmp:A->A->ordering x y.
     (!x y. cmp x y = EQUAL <=> x = y)
     ==> (list_compare cmp x y = EQUAL <=> x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP compare_equal th]));;

let pair_cmp_antisym = prove
 (`!cmp1:A->A->ordering cmp2:B->B->ordering x y.
     (!x y. cmp1 x y = EQUAL <=> x = y) /\
     (!x y. cmp2 x y = EQUAL <=> x = y)
     ==> (pair_compare cmp1 cmp2 x y = EQUAL <=> x = y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; pair_compare_def; ordering_case_eq;
              distinctness "ordering"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let option_cmp_antisym = prove
 (`!cmp:A->A->ordering x y.
     (!x y. cmp x y = EQUAL <=> x = y)
     ==> (option_compare cmp x y = EQUAL <=> x = y)`,
  REWRITE_TAC[FORALL_OPTION_THM; option_compare_def; option_DISTINCT;
              option_INJ; distinctness "ordering"] THEN
  SIMP_TAC[]);;

let option_cmp2_antisym = prove
 (`!cmp:A->A->ordering x y.
     (!x y. cmp x y = EQUAL <=> x = y)
     ==> (option_cmp2 cmp x y = EQUAL <=> x = y)`,
  REWRITE_TAC[FORALL_OPTION_THM; option_cmp2_def; option_DISTINCT;
              option_INJ; distinctness "ordering"] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Respecting the equivalence of a comparison.                               *)
(* ------------------------------------------------------------------------- *)

let resp_equiv_def = new_definition
  `resp_equiv (cmp:A->A->ordering) (f:A->B->C) <=>
     !k1 k2 v. cmp k1 k2 = EQUAL ==> f k1 v = f k2 v`;;

let resp_equiv2_def = new_definition
  `resp_equiv2 (cmp:A->A->ordering) (cmp2:B->B->ordering) (f:A->B) <=>
     (!k1 k2. cmp k1 k2 = EQUAL ==> cmp2 (f k1) (f k2) = EQUAL)`;;

let equiv_inj_def = new_definition
  `equiv_inj (cmp:A->A->ordering) (cmp2:B->B->ordering) (f:A->B) <=>
     (!k1 k2. cmp2 (f k1) (f k2) = EQUAL ==> cmp k1 k2 = EQUAL)`;;

let antisym_resp_equiv = prove
 (`!cmp:A->A->ordering f:A->B->C.
     (!x y. cmp x y = EQUAL ==> x = y)
     ==> resp_equiv cmp f /\
         !cmp2. good_cmp cmp2 ==> resp_equiv2 cmp cmp2 f`,
  REWRITE_TAC[resp_equiv_def; resp_equiv2_def; good_cmp_def] THEN
  MESON_TAC[]);;

let list_cmp_equal_list_rel = prove
 (`!cmp:A->B->ordering l1 l2.
     list_compare cmp l1 l2 = EQUAL <=> ALL2 (\x y. cmp x y = EQUAL) l1 l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_REWRITE_TAC[list_compare_def; ALL2; ordering_case_eq;
                  distinctness "ordering"]);;

let TO_of_LinearOrder_LLEX = prove
 (`!R:A->A->bool.
     irreflexive R
     ==> TO_of_LinearOrder (LLEX R) = list_compare (TO_of_LinearOrder R)`,
  GEN_TAC THEN REWRITE_TAC[irreflexive_DEF] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[FUN_EQ_THM] THEN
  LIST_INDUCT_TAC THEN X_GEN_TAC `l2:A list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:A list` list_CASES) THEN
  ASM_REWRITE_TAC[list_compare_def] THEN
  REWRITE_TAC[TO_of_LinearOrder; LLEX_def; list_CASE; NOT_CONS_NIL; CONS_11] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ordering_case_def; distinctness "ordering"] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [bool_cmp_good; num_cmp_good; bool_cmp_antisym; num_cmp_antisym];;
