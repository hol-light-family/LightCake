(* ========================================================================= *)
(* holSyntaxExtra, part 3 (HOL4 holSyntaxExtraScript.sml lines 966-1640):    *)
(* VFREE_IN lemmas, hypset_ok, term_union, term_remove and term_image        *)
(* lemmas, VSUBST lemmas, INST_CORE_HAS_TYPE and the INST lemmas, tyvars     *)
(* and tvars.  Notes on the rendering: holSyntaxExtra_p1.ml.                 *)
(* - HOL4's SET_TO_LIST is list_of_set (src/hol4/list.ml).                   *)
(* - The vacuous bound variable ty of VSUBST_WELLTYPED (a type variable in   *)
(*   HOL4) has the type hol_type.                                            *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_P3_.               *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* VFREE_IN lemmas *)

let VFREE_IN_RACONV = prove
 (`!env p. RACONV env p
           ==> !x ty. VFREE_IN (hol_Var x ty) (FST p) /\
                      ~(?y. MEM (hol_Var x ty,y) env) <=>
                      VFREE_IN (hol_Var x ty) (SND p) /\
                      ~(?y. MEM (y,hol_Var x ty) env)`,
  MATCH_MP_TAC RACONV_ind THEN REWRITE_TAC[VFREE_IN_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[ALPHAVARS_def; MEM; PAIR_EQ] THENL
     [SIMP_TAC[injectivity "hol_term"]; ALL_TAC] THEN
    PAIR_CASES_ON `h:hol_term#hol_term` THEN
    REWRITE_TAC[PAIR_EQ; FST; SND; MEM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
      MESON_TAC[];
      FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[distinctness "hol_term"];
    MESON_TAC[];
    REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[]]);;

let VFREE_IN_ACONV = prove
 (`!s t x ty. ACONV s t
              ==> (VFREE_IN (hol_Var x ty) s <=> VFREE_IN (hol_Var x ty) t)`,
  REWRITE_TAC[ACONV_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP VFREE_IN_RACONV) THEN
  REWRITE_TAC[FST; SND; MEM] THEN SIMP_TAC[]);;

let VFREE_IN_subterm = prove
 (`!t1 t2. VFREE_IN t1 t2 ==> RTC subterm1 t1 t2`,
  QINDUCT_ON "t2" THEN
  SIMP[VFREE_IN_def; subterm_Comb; subterm_Abs; subterm_Var; subterm_Const] THEN
  MESON_TAC[]);;

(* hypset_ok *)

let hypset_ok_nil = prove
 (`hypset_ok []`,
  REWRITE_TAC[hypset_ok_def; SORTED_DEF]);;
let _ = cake_add_simps [hypset_ok_nil];;

let hypset_ok_sing = prove
 (`!p. hypset_ok [p]`,
  REWRITE_TAC[hypset_ok_def; SORTED_DEF]);;
let _ = cake_add_simps [hypset_ok_sing];;

let hypset_ok_cons = prove
 (`hypset_ok (CONS h hs) <=> ALL (alpha_lt h) hs /\ hypset_ok hs`,
  REWRITE_TAC[hypset_ok_def; MATCH_MP SORTED_EQ transitive_alpha_lt;
              GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let hypset_ok_ALL_DISTINCT = prove
 (`!h. hypset_ok h ==> ALL_DISTINCT h`,
  REWRITE_TAC[hypset_ok_def] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[MATCH_MP SORTED_EQ transitive_alpha_lt; ALL_DISTINCT] THEN
  ASM_MESON_TAC[alpha_lt_not_refl]);;

let hypset_ok_eq = prove
 (`!h1 h2. hypset_ok h1 /\ hypset_ok h2
           ==> (h1 = h2 <=> set_of_list h1 = set_of_list h2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MATCH_MP SORTED_PERM_EQ
    (CONJ transitive_alpha_lt antisymmetric_alpha_lt)) THEN
  ASM_REWRITE_TAC[GSYM hypset_ok_def] THEN MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  ASM_SIMP_TAC[hypset_ok_ALL_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_SET_OF_LIST]) THEN
  SIMP_TAC[]);;

(* HOL4: Q.ISPEC alpha_lt SORTED_APPEND_GEN with hypset_ok folded *)
let hypset_ok_append = prove
 (`!L1 L2. hypset_ok (APPEND L1 L2) <=>
           hypset_ok L1 /\ hypset_ok L2 /\
           (L1 = [] \/ L2 = [] \/ alpha_lt (LAST L1) (HD L2))`,
  REWRITE_TAC[hypset_ok_def; SORTED_APPEND_GEN]);;

(* HOL4: MATCH_MP SORTED_EL_LESS transitive_alpha_lt with hypset_ok folded *)
let hypset_ok_el_less = prove
 (`!ls. hypset_ok ls <=>
        !m n. m < n /\ n < LENGTH ls ==> alpha_lt (EL m ls) (EL n ls)`,
  REWRITE_TAC[hypset_ok_def; MATCH_MP SORTED_EL_LESS transitive_alpha_lt]);;

(* term_union lemmas *)

let term_union_idem = prove
 (`!ls. term_union ls ls = ls`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[term_union_def] THEN
  REWRITE_TAC[list_CASE] THEN ONCE_REWRITE_TAC[orda_def] THEN
  ASM_SIMP_TAC[LET_DEF; LET_END_DEF]);;
let _ = cake_add_simps [term_union_idem];;

let term_union_thm = prove
 (CASE_TERM
  `(!l2. term_union [] l2 = l2) /\
   (!l1. term_union l1 [] = l1) /\
   (!h1 t1 h2 t2.
      term_union (CONS h1 t1) (CONS h2 t2) =
      match orda [] h1 h2 with
        EQUAL -> CONS h1 (term_union t1 t2)
      | LESS -> CONS h1 (term_union t1 (CONS h2 t2))
      | GREATER -> CONS h2 (term_union (CONS h1 t1) t2))`,
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[term_union_def] THEN REWRITE_TAC[list_CASE];
    LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[term_union_def] THEN REWRITE_TAC[list_CASE];
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [term_union_def] THEN
    REWRITE_TAC[list_CASE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    STRUCT_CASES_TAC(ISPEC `orda [] h1 h2` (cases "ordering")) THEN
    REWRITE_TAC[distinctness "ordering"] THEN CAKE_REWRITE_TAC[]]);;

let MEM_term_union_imp = prove
 (`!l1 l2 x. MEM x (term_union l1 l2) ==> MEM x l1 \/ MEM x l2`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[term_union_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[term_union_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:hol_term` THEN REWRITE_TAC[term_union_thm] THEN
  STRUCT_CASES_TAC(ISPEC `orda [] h h'` (cases "ordering")) THEN
  CAKE_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[MEM]);;

(* orda [] in the GREATER case, through orda_sym *)
let CSYNAUX_P3_orda_GREATER = prove
 (`!t1 t2. orda [] t1 t2 = GREATER <=> alpha_lt t2 t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[alpha_lt_def] THEN
  MP_TAC(ISPECL [`[]:(hol_term#hol_term)list`; `t1:hol_term`; `t2:hol_term`]
    orda_sym) THEN
  REWRITE_TAC[MAP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  STRUCT_CASES_TAC(ISPEC `orda [] t1 t2` (cases "ordering")) THEN
  REWRITE_TAC[invert_comparison_def; distinctness "ordering"]);;

let hypset_ok_term_union = prove
 (`!l1 l2. hypset_ok l1 /\ hypset_ok l2 ==> hypset_ok (term_union l1 l2)`,
  REWRITE_TAC[hypset_ok_def] THEN
  LIST_INDUCT_TAC THENL [SIMP_TAC[term_union_thm]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL [SIMP_TAC[term_union_thm]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP SORTED_EQ transitive_alpha_lt] THEN STRIP_TAC THEN
  REWRITE_TAC[term_union_thm] THEN
  MP_TAC transitive_alpha_lt THEN REWRITE_TAC[transitive_def] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `orda [] h h'` (cases "ordering")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP SORTED_EQ transitive_alpha_lt] THENL
   [(* LESS *)
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th ORELSE NO_TAC) THEN
      ASM_REWRITE_TAC[MATCH_MP SORTED_EQ transitive_alpha_lt];
      X_GEN_TAC `y:hol_term` THEN DISCH_THEN(MP_TAC o MATCH_MP MEM_term_union_imp) THEN
      REWRITE_TAC[MEM] THEN ASM_MESON_TAC[alpha_lt_def]];
    (* EQUAL *)
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th ORELSE NO_TAC) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:hol_term` THEN DISCH_THEN(MP_TAC o MATCH_MP MEM_term_union_imp) THEN
      ASM_MESON_TAC[ACONV_eq_orda; alpha_lt_trans_ACONV]];
    (* GREATER *)
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th ORELSE NO_TAC) THEN
      ASM_REWRITE_TAC[MATCH_MP SORTED_EQ transitive_alpha_lt];
      X_GEN_TAC `y:hol_term` THEN DISCH_THEN(MP_TAC o MATCH_MP MEM_term_union_imp) THEN
      REWRITE_TAC[MEM] THEN ASM_MESON_TAC[CSYNAUX_P3_orda_GREATER]]]);;
let _ = cake_add_simps [hypset_ok_term_union];;

let EVERY_term_union = prove
 (`ALL P l1 /\ ALL P l2 ==> ALL P (term_union l1 l2)`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MEM_term_union_imp]);;

let MEM_term_union = prove
 (`!h1 h2 t. hypset_ok h1 /\ hypset_ok h2 /\ (MEM t h1 \/ MEM t h2)
             ==> ?y. MEM y (term_union h1 h2) /\ ACONV t y`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[term_union_thm; MEM] THEN MESON_TAC[ACONV_REFL]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[term_union_thm; MEM] THEN MESON_TAC[ACONV_REFL; MEM]; ALL_TAC] THEN
  X_GEN_TAC `tm:hol_term` THEN REWRITE_TAC[hypset_ok_cons] THEN STRIP_TAC THEN
  REWRITE_TAC[term_union_thm] THEN
  MP_TAC(ISPEC `orda [] h h'` (cases "ordering")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ACONV_eq_orda]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[ACONV_REFL; ACONV_SYM; hypset_ok_cons; MEM]);;

let term_union_sing_lt = prove
 (`!ys x. ALL (\y. alpha_lt x y) ys ==> term_union [x] ys = CONS x ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[term_union_thm; ALL; alpha_lt_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[term_union_thm]);;

let term_union_insert = prove
 (`!ys x zs.
     ALL (\y. alpha_lt y x) ys /\
     ALL (\z. alpha_lt x z) zs
     ==> term_union [x] (APPEND ys zs) = APPEND ys (CONS x zs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ALL] THENL
   [MESON_TAC[term_union_sing_lt]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[term_union_thm] THEN
  SUBGOAL_THEN `orda [] x h = GREATER` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[CSYNAUX_P3_orda_GREATER]; ALL_TAC] THEN
  CAKE_REWRITE_TAC[] THEN ASM_SIMP_TAC[term_union_thm]);;

let term_union_replace = prove
 (`!ys x x' zs.
     ALL (\y. alpha_lt y x) ys /\ ACONV x x' /\
     ALL (\z. alpha_lt x z) zs
     ==> term_union [x] (APPEND ys (CONS x' zs)) = APPEND ys (CONS x zs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ALL; term_union_thm] THENL
   [REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ACONV_eq_orda]) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[term_union_thm];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `orda [] x h = GREATER` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[CSYNAUX_P3_orda_GREATER]; ALL_TAC] THEN
  CAKE_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let MEM_term_union_first = prove
 (`!h1 h2 t. hypset_ok h1 /\ hypset_ok h2 /\ MEM t h1
             ==> MEM t (term_union h1 h2)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[MEM]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[term_union_thm]; ALL_TAC] THEN
  X_GEN_TAC `tm:hol_term` THEN REWRITE_TAC[hypset_ok_cons] THEN STRIP_TAC THEN
  REWRITE_TAC[term_union_thm] THEN
  MP_TAC(ISPEC `orda [] h h'` (cases "ordering")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[hypset_ok_cons; MEM]);;

let term_union_insert_mem = prove
 (`!c h. hypset_ok h /\ MEM c h ==> term_union [c] h = h`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; hypset_ok_cons] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[term_union_thm] THEN
    SUBGOAL_THEN `orda [] h h = EQUAL` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM ACONV_eq_orda; ACONV_REFL]; ALL_TAC] THEN
    CAKE_REWRITE_TAC[term_union_thm];
    REWRITE_TAC[term_union_thm] THEN
    SUBGOAL_THEN `orda [] c h = GREATER` SUBST1_TAC THENL
     [REWRITE_TAC[CSYNAUX_P3_orda_GREATER] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

(* one step of term_remove (HOL4: simp[Once term_remove_def]) *)
let CSYNAUX_P3_term_remove_cons = prove
 (`!x h t. term_remove x (CONS h t) =
           if orda [] x h = GREATER then
             (if term_remove x t = t then CONS h t else CONS h (term_remove x t))
           else if orda [] x h = EQUAL then t else CONS h t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [term_remove_def] THEN
  REWRITE_TAC[list_CASE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let term_union_insert_remove = prove
 (`!c h. hypset_ok h /\ MEM c h /\ ACONV c' c
         ==> term_union [c] (term_remove c' h) = h`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; hypset_ok_cons] THEN
  STRIP_TAC THENL
   [(* c = h *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[CSYNAUX_P3_term_remove_cons] THEN
    SUBGOAL_THEN `orda [] c' h = EQUAL` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM ACONV_eq_orda]; ALL_TAC] THEN
    REWRITE_TAC[distinctness "ordering"] THEN
    MATCH_MP_TAC term_union_sing_lt THEN ASM_REWRITE_TAC[ETA_AX];
    (* MEM c t *)
    SUBGOAL_THEN `alpha_lt h c` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `orda [] c' h = GREATER` ASSUME_TAC THENL
     [REWRITE_TAC[CSYNAUX_P3_orda_GREATER] THEN
      ASM_MESON_TAC[alpha_lt_trans_ACONV; ACONV_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `orda [] c h = GREATER` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CSYNAUX_P3_orda_GREATER]; ALL_TAC] THEN
    REWRITE_TAC[CSYNAUX_P3_term_remove_cons] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[term_union_thm] THEN ASM_REWRITE_TAC[] THEN
    CAKE_REWRITE_TAC[injectivity "list"] THEN
    ASM_MESON_TAC[term_union_insert_mem; term_union_thm]]);;

(* term_remove *)

let term_remove_nil = prove
 (`!a. term_remove a [] = []`,
  ONCE_REWRITE_TAC[term_remove_def] THEN REWRITE_TAC[list_CASE]);;
let _ = cake_add_simps [term_remove_nil];;

let MEM_term_remove_imp = prove
 (`!ls x t. MEM t (term_remove x ls)
            ==> MEM t ls /\ (hypset_ok ls ==> ~ACONV x t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[term_remove_nil; MEM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CSYNAUX_P3_term_remove_cons; hypset_ok_cons] THEN
  MP_TAC transitive_alpha_lt THEN REWRITE_TAC[transitive_def] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `orda [] x h` (cases "ordering")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "ordering"] THENL
   [(* LESS *)
    REWRITE_TAC[MEM; GSYM ALL_MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM alpha_lt_def]) THEN
    ASM_MESON_TAC[alpha_lt_not_refl; ACONV_eq_orda; alpha_lt_def;
                  distinctness "ordering"];
    (* EQUAL *)
    REWRITE_TAC[GSYM ALL_MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ACONV_eq_orda]) THEN
    ASM_MESON_TAC[alpha_lt_trans_ACONV; ACONV_eq_orda; alpha_lt_def;
                  distinctness "ordering"];
    (* GREATER *)
    COND_CASES_TAC THEN REWRITE_TAC[MEM] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:hol_term`; `t':hol_term`]) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[ACONV_eq_orda; distinctness "ordering"];
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:hol_term`; `t':hol_term`]) THEN
      ASM_MESON_TAC[ACONV_eq_orda; distinctness "ordering"]]]);;

let hypset_ok_term_remove = prove
 (`!ls. hypset_ok ls ==> !t. hypset_ok (term_remove t ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[term_remove_nil; hypset_ok_nil] THEN
  REWRITE_TAC[hypset_ok_cons] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CSYNAUX_P3_term_remove_cons] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[hypset_ok_cons] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[MEM_term_remove_imp]);;
let _ = cake_add_simps [hypset_ok_term_remove];;

let EVERY_term_remove = prove
 (`ALL P ls ==> ALL P (term_remove t ls)`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MEM_term_remove_imp]);;

let MEM_term_remove = prove
 (`!h x t. MEM t h /\ ~ACONV x t /\ hypset_ok h ==> MEM t (term_remove x h)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; hypset_ok_cons] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CSYNAUX_P3_term_remove_cons] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[MEM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ACONV_eq_orda]) THEN
  ASM_MESON_TAC[]);;

let term_remove_exists = prove
 (`!c h. ~(term_remove c h = h) ==> ?c'. MEM c' h /\ ACONV c c'`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[term_remove_nil; MEM] THEN
  REWRITE_TAC[CSYNAUX_P3_term_remove_cons] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[injectivity "list"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ACONV_eq_orda]) THEN
  ASM_MESON_TAC[]);;

(* term_image *)

let term_image_nil = prove
 (`term_image f [] = []`,
  ONCE_REWRITE_TAC[term_image_def] THEN REWRITE_TAC[list_CASE]);;
let _ = cake_add_simps [term_image_nil];;

(* one step of term_image (HOL4: simp[Once term_image_def]) *)
let CSYNAUX_P3_term_image_cons = prove
 (`!f h t. term_image f (CONS h t) =
           if f h = h /\ term_image f t = t then CONS h t
           else term_union [f h] (term_image f t)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [term_image_def] THEN
  REWRITE_TAC[list_CASE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MEM_term_image_imp = prove
 (`!ls f t. MEM t (term_image f ls) ==> ?x. MEM x ls /\ t = f x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[term_image_nil; MEM] THEN
  REWRITE_TAC[CSYNAUX_P3_term_image_cons] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[MEM] THENL
   [ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP MEM_term_union_imp) THEN REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[]]);;

let hypset_ok_term_image = prove
 (`!ls f. hypset_ok ls ==> hypset_ok (term_image f ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[term_image_nil; hypset_ok_nil] THEN
  REWRITE_TAC[CSYNAUX_P3_term_image_cons] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC hypset_ok_term_union THEN REWRITE_TAC[hypset_ok_sing] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[hypset_ok_cons]);;

let MEM_term_image = prove
 (`!ls f t. MEM t ls /\ hypset_ok ls
            ==> ?y. MEM y (term_image f ls) /\ ACONV (f t) y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  REWRITE_TAC[CSYNAUX_P3_term_image_cons; hypset_ok_cons] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MEM] THENL
   [ASM_MESON_TAC[ACONV_REFL];
    ASM_MESON_TAC[MEM_term_union; hypset_ok_sing; MEM; hypset_ok_term_image];
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:hol_term->hol_term`; `t':hol_term`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:hol_term->hol_term`; `t':hol_term`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEM_term_union; hypset_ok_sing; hypset_ok_term_image; ACONV_TRANS]]);;

(* VSUBST lemmas *)

(* inversions of has_type (HOL4: simp[Once has_type_cases]) *)
let CSYNAUX_P3_has_type_Var = prove
 (`!n ty ty'. hol_Var n ty has_type ty' <=> ty' = ty`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[]);;

let CSYNAUX_P3_has_type_Const = prove
 (`!n ty ty'. hol_Const n ty has_type ty' <=> ty' = ty`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[]);;

let CSYNAUX_P3_has_type_Comb = prove
 (`!s t ty. hol_Comb s t has_type ty <=>
            ?dty. s has_type Tyapp (implode "fun") [dty; ty] /\ t has_type dty`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[]);;

let CSYNAUX_P3_has_type_Abs = prove
 (`!v t ty. hol_Abs v t has_type ty <=>
            ?n dty rty. v = hol_Var n dty /\
                        ty = Tyapp (implode "fun") [dty; rty] /\ t has_type rty`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[]);;

let VSUBST_HAS_TYPE = prove
 (`!tm ty ilist.
     tm has_type ty /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)
     ==> VSUBST ilist tm has_type ty`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`;
                   `hol_Var a0 a1`] REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`hol_Var a0 a1`; `REV_ASSOCD (hol_Var a0 a1) ilist (hol_Var a0 a1)`]) THEN
    ASM_REWRITE_TAC[injectivity "hol_term"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CSYNAUX_P3_has_type_Var]) THEN
    ASM_MESON_TAC[];
    SIMP_TAC[VSUBST_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[VSUBST_def; CSYNAUX_P3_has_type_Comb] THEN ASM_MESON_TAC[];
    X_GEN_TAC `v:hol_term` THEN X_GEN_TAC `t:hol_term` THEN STRIP_TAC THEN
    X_GEN_TAC `ty:hol_type` THEN X_GEN_TAC `ilist:(hol_term#hol_term)list` THEN
    REWRITE_TAC[CSYNAUX_P3_has_type_Abs] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VSUBST_def; dest_var_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[CSYNAUX_P3_has_type_Abs; injectivity "hol_term"] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; EXISTS_REFL;
                GSYM CONJ_ASSOC; UNWIND_THM1; UNWIND_THM2;
                injectivity "hol_type"; CONS_11] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_MESON_TAC[CSYNAUX_P3_has_type_Var]]);;

let VSUBST_WELLTYPED = prove
 (`!tm (ty:hol_type) ilist.
     welltyped tm /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)
     ==> welltyped (VSUBST ilist tm)`,
  MESON_TAC[VSUBST_HAS_TYPE; welltyped_def]);;

let VFREE_IN_VSUBST = prove
 (`!tm u uty ilist.
     welltyped tm
     ==> (VFREE_IN (hol_Var u uty) (VSUBST ilist tm) <=>
          ?y ty. VFREE_IN (hol_Var y ty) tm /\
                 VFREE_IN (hol_Var u uty) (REV_ASSOCD (hol_Var y ty) ilist (hol_Var y ty)))`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VSUBST_def; VFREE_IN_def; injectivity "hol_term"] THEN MESON_TAC[];
    REWRITE_TAC[VSUBST_def; VFREE_IN_def; distinctness "hol_term"];
    REWRITE_TAC[VSUBST_def; VFREE_IN_def; WELLTYPED_CLAUSES] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:hol_term` THEN X_GEN_TAC `t:hol_term` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "IH")) THEN
  MAP_EVERY X_GEN_TAC [`u:mlstring`; `uty:hol_type`; `ilist:(hol_term#hol_term)list`] THEN
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:mlstring` (X_CHOOSE_THEN `bty:hol_type` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[VSUBST_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE] THEN
  ABBREV_TAC `ilist' = FILTER (\(s':hol_term,s:hol_term). ~(s = hol_Var b bty))
                              (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!y ty. REV_ASSOCD (hol_Var y ty) ilist' (hol_Var y ty) =
                       if hol_Var y ty = hol_Var b bty then hol_Var y ty
                       else REV_ASSOCD (hol_Var y ty) ilist (hol_Var y ty)`
    (LABEL_TAC "REV'") THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[REV_ASSOCD_FILTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VFREE_IN_def] THEN ASM_SIMP_TAC[REV_ASSOCD] THENL
   [(* a bound variable is renamed *)
    USE_THEN "IH" (MP_TAC o SPECL [`VARIANT (VSUBST ilist' t) (explode b) bty`;
                                   `bty:hol_type`; `ilist':(hol_term#hol_term)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "REV'" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`VSUBST ilist' t`; `explode b`; `bty:hol_type`] VARIANT_THM) THEN
    REWRITE_TAC[COND_RAND; COND_EXPAND; VFREE_IN_def] THEN MESON_TAC[];
    (* no renaming *)
    SUBGOAL_THEN
      `!y ty. ~(hol_Var y ty = hol_Var b bty) /\ VFREE_IN (hol_Var y ty) t
              ==> ~VFREE_IN (hol_Var b bty)
                            (REV_ASSOCD (hol_Var y ty) ilist (hol_Var y ty))`
      ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var y ty`; `hol_Var y ty`]
        REV_ASSOCD_MEM) THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `~EX (\(s':hol_term,s:hol_term).
                            VFREE_IN (hol_Var b bty) s' /\ VFREE_IN s t) ilist'` THEN
        EXPAND_TAC "ilist'" THEN REWRITE_TAC[GSYM EX_MEM; MEM_FILTER] THEN
        EXISTS_TAC `(REV_ASSOCD (hol_Var y ty) ilist (hol_Var y ty), hol_Var y ty)` THEN
        CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `VFREE_IN (hol_Var b bty)
                       (REV_ASSOCD (hol_Var y ty) ilist (hol_Var y ty))` THEN
        ASM_REWRITE_TAC[VFREE_IN_def]];
      ALL_TAC] THEN
    REWRITE_TAC[COND_RAND; COND_EXPAND; VFREE_IN_def] THEN ASM_MESON_TAC[]]);;

let VSUBST_NIL = prove
 (`!tm. VSUBST [] tm = tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  SIMP[VSUBST_def; REV_ASSOCD; FILTER; EX; LET_DEF; LET_END_DEF]);;
let _ = cake_add_simps [VSUBST_NIL];;

(* INST lemmas *)

let INST_CORE_HAS_TYPE = prove
 (`!n tm env tyin.
     welltyped tm /\ sizeof tm = n /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty))
     ==> (?x ty. INST_CORE env tyin tm = Clash (hol_Var x (TYPE_SUBST tyin ty)) /\
                 VFREE_IN (hol_Var x ty) tm /\
                 ~(REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty)) env (hol_Var x ty) =
                   hol_Var x ty)) \/
         (!x ty. VFREE_IN (hol_Var x ty) tm
                 ==> REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty)) env (hol_Var x ty) =
                     hol_Var x ty) /\
         (?tm'. INST_CORE env tyin tm = hol_Result tm' /\
                tm' has_type (TYPE_SUBST tyin (typeof tm)) /\
                (!u uty. VFREE_IN (hol_Var u uty) tm' <=>
                         ?oty. VFREE_IN (hol_Var u oty) tm /\
                               uty = TYPE_SUBST tyin oty))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "WF") THEN
  SUBGOAL_THEN
   `!tm env tyin.
      sizeof tm < n /\ welltyped tm /\
      (!s s'. MEM (s,s') env
              ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty))
      ==> (?x ty. INST_CORE env tyin tm = Clash (hol_Var x (TYPE_SUBST tyin ty)) /\
                  VFREE_IN (hol_Var x ty) tm /\
                  ~(REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty)) env (hol_Var x ty) =
                    hol_Var x ty)) \/
          (!x ty. VFREE_IN (hol_Var x ty) tm
                  ==> REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty)) env (hol_Var x ty) =
                      hol_Var x ty) /\
          (?tm'. INST_CORE env tyin tm = hol_Result tm' /\
                 tm' has_type (TYPE_SUBST tyin (typeof tm)) /\
                 (!u uty. VFREE_IN (hol_Var u uty) tm' <=>
                          ?oty. VFREE_IN (hol_Var u oty) tm /\
                                uty = TYPE_SUBST tyin oty))`
    (LABEL_TAC "IH") THENL
   [REPEAT STRIP_TAC THEN
    REMOVE_THEN "WF" (MP_TAC o SPEC `sizeof (tm:hol_term)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "WF" (K ALL_TAC)] THEN
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Var *)
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `xty:hol_type`; `env:(hol_term#hol_term)list`;
                         `tyin:(hol_type#hol_type)list`] THEN STRIP_TAC THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "hol_result"; injectivity "hol_result"; VFREE_IN_def;
                injectivity "hol_term"; typeof_def] THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `hol_Var x (TYPE_SUBST tyin xty)` THEN
      REWRITE_TAC[CSYNAUX_P3_has_type_Var; VFREE_IN_def; injectivity "hol_term"] THEN
      MESON_TAC[];
      ASM_MESON_TAC[]];
    (* Const *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INST_CORE_def] THEN
    REWRITE_TAC[distinctness "hol_result"; injectivity "hol_result"; VFREE_IN_def;
                distinctness "hol_term"; typeof_def; UNWIND_THM1;
                CSYNAUX_P3_has_type_Const];
    (* Comb *)
    MAP_EVERY X_GEN_TAC [`s:hol_term`; `t:hol_term`] THEN DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`; `tyin:(hol_type#hol_type)list`] THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; sizeof_def] THEN STRIP_TAC THEN
    USE_THEN "IH" (MP_TAC o SPECL [`s:hol_term`; `env:(hol_term#hol_term)list`;
                                   `tyin:(hol_type#hol_type)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "IH" (MP_TAC o SPECL [`t:hol_term`; `env:(hol_term#hol_term)list`;
                                   `tyin:(hol_type#hol_type)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[IS_CLASH_def; RESULT_def; distinctness "hol_result";
                    injectivity "hol_result"; VFREE_IN_def; typeof_def; codomain_def;
                    UNWIND_THM1; UNWIND_THM2] THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        REWRITE_TAC[CSYNAUX_P3_has_type_Comb] THEN
        EXISTS_TAC `TYPE_SUBST tyin (typeof t)` THEN
        QPAT_X_ASSUM "_ has_type TYPE_SUBST tyin (typeof s)" MP_TAC THEN
        ASM_REWRITE_TAC[TYPE_SUBST_def; MAP] THEN SIMP_TAC[];
        MESON_TAC[]]];
    (* Abs *)
    X_GEN_TAC `v:hol_term` THEN X_GEN_TAC `t:hol_term` THEN DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`; `tyin:(hol_type#hol_type)list`] THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:mlstring`; `bty:hol_type`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v:hol_term`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[sizeof_def]) THEN
    USE_THEN "IH" (MP_TAC o SPECL
      [`t:hol_term`; `CONS (hol_Var b bty,hol_Var b (TYPE_SUBST tyin bty)) env`;
       `tyin:(hol_type#hol_type)list`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[INST_CORE_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[pair_CASE] THEN
    ABBREV_TAC `x' = VARIANT (RESULT (INST_CORE [] tyin t)) (explode b)
                             (TYPE_SUBST tyin bty)` THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def; CLASH_def; distinctness "hol_result";
                    injectivity "hol_result"; UNWIND_THM1; UNWIND_THM2] THENL
     [(* the body clashes *)
      ASM_CASES_TAC `hol_Var x (TYPE_SUBST tyin ty) = hol_Var b (TYPE_SUBST tyin bty)` THEN
      ASM_REWRITE_TAC[] THENL
       [(* the clash is the bound variable: rename it *)
        USE_THEN "IH" (MP_TAC o SPECL [`t:hol_term`; `[]:(hol_term#hol_term)list`;
                                       `tyin:(hol_type#hol_type)list`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[MEM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REV_ASSOCD] THEN
        DISCH_THEN(X_CHOOSE_THEN `tt0:hol_term` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `!oty. VFREE_IN (hol_Var x' oty) t
                            ==> ~(TYPE_SUBST tyin oty = TYPE_SUBST tyin bty)`
          (LABEL_TAC "F3") THENL
         [MP_TAC(ISPECL [`RESULT (INST_CORE [] tyin t)`; `explode b`;
                         `TYPE_SUBST tyin bty`] VARIANT_THM) THEN
          ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[RESULT_def] THEN MESON_TAC[];
          ALL_TAC] THEN
        ABBREV_TAC `t' = VSUBST [hol_Var x' bty,hol_Var b bty] t` THEN
        SUBGOAL_THEN `t' has_type typeof t` ASSUME_TAC THENL
         [EXPAND_TAC "t'" THEN MATCH_MP_TAC VSUBST_HAS_TYPE THEN
          ASM_REWRITE_TAC[GSYM WELLTYPED; MEM; PAIR_EQ] THEN
          MESON_TAC[CSYNAUX_P3_has_type_Var];
          ALL_TAC] THEN
        SUBGOAL_THEN `welltyped t' /\ typeof t' = typeof t` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[welltyped_def; WELLTYPED_LEMMA]; ALL_TAC] THEN
        SUBGOAL_THEN `sizeof t' = sizeof t` ASSUME_TAC THENL
         [EXPAND_TAC "t'" THEN REWRITE_TAC[CSYNAUX_SIZEOF_VSUBST_VAR]; ALL_TAC] THEN
        SUBGOAL_THEN
         `!u uty. VFREE_IN (hol_Var u uty) t' <=>
                  (VFREE_IN (hol_Var b bty) t /\ hol_Var u uty = hol_Var x' bty) \/
                  (VFREE_IN (hol_Var u uty) t /\ ~(hol_Var u uty = hol_Var b bty))`
          (LABEL_TAC "F6") THENL
         [EXPAND_TAC "t'" THEN ASM_SIMP_TAC[VFREE_IN_VSUBST; REV_ASSOCD] THEN
          REWRITE_TAC[COND_RAND; COND_EXPAND; VFREE_IN_def] THEN MESON_TAC[];
          ALL_TAC] THEN
        USE_THEN "IH" (MP_TAC o SPECL
          [`t':hol_term`; `CONS (hol_Var x' bty,hol_Var x' (TYPE_SUBST tyin bty)) env`;
           `tyin:(hol_type#hol_type)list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def; distinctness "hol_result";
                        injectivity "hol_result"; UNWIND_THM1; UNWIND_THM2] THENL
         [(* the renamed body clashes *)
          SUBGOAL_THEN `~(hol_Var x'' ty' = hol_Var x' bty)` ASSUME_TAC THENL
           [REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
            UNDISCH_TAC `~(REV_ASSOCD (hol_Var x'' (TYPE_SUBST tyin ty'))
                            (CONS (hol_Var x' bty,hol_Var x' (TYPE_SUBST tyin bty)) env)
                            (hol_Var x'' ty') = hol_Var x'' ty')` THEN
            ASM_REWRITE_TAC[REV_ASSOCD];
            ALL_TAC] THEN
          SUBGOAL_THEN `VFREE_IN (hol_Var x'' ty') t /\ ~(hol_Var x'' ty' = hol_Var b bty)`
            STRIP_ASSUME_TAC THENL
           [USE_THEN "F6" (fun th -> MP_TAC(EQ_MP (SPECL [`x'':mlstring`; `ty':hol_type`] th)
                                                 (ASSUME `VFREE_IN (hol_Var x'' ty') t'`))) THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          SUBGOAL_THEN
            `~(hol_Var x' (TYPE_SUBST tyin bty) = hol_Var x'' (TYPE_SUBST tyin ty'))`
            ASSUME_TAC THENL
           [REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
            REMOVE_THEN "F3" (MP_TAC o SPEC `ty':hol_type`) THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          MAP_EVERY EXISTS_TAC [`x'':mlstring`; `ty':hol_type`] THEN
          UNDISCH_TAC `~(REV_ASSOCD (hol_Var x'' (TYPE_SUBST tyin ty'))
                          (CONS (hol_Var x' bty,hol_Var x' (TYPE_SUBST tyin bty)) env)
                          (hol_Var x'' ty') = hol_Var x'' ty')` THEN
          ASM_REWRITE_TAC[REV_ASSOCD; VFREE_IN_def] THEN ASM_MESON_TAC[];
          (* the renamed body is a result *)
          REPEAT CONJ_TAC THENL
           [MAP_EVERY X_GEN_TAC [`y:mlstring`; `yty:hol_type`] THEN
            REWRITE_TAC[VFREE_IN_def] THEN STRIP_TAC THEN
            SUBGOAL_THEN `VFREE_IN (hol_Var y yty) t'` ASSUME_TAC THENL
             [USE_THEN "F6" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
            SUBGOAL_THEN
              `~(hol_Var x' (TYPE_SUBST tyin bty) = hol_Var y (TYPE_SUBST tyin yty))`
              ASSUME_TAC THENL
             [REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
              REMOVE_THEN "F3" (MP_TAC o SPEC `yty:hol_type`) THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            QPAT_X_ASSUM "!x ty. VFREE_IN (hol_Var x ty) t' ==> _"
              (MP_TAC o SPECL [`y:mlstring`; `yty:hol_type`]) THEN
            ASM_REWRITE_TAC[REV_ASSOCD];
            REWRITE_TAC[typeof_def; TYPE_SUBST_def; MAP; CSYNAUX_P3_has_type_Abs;
                        injectivity "hol_term"] THEN
            MAP_EVERY EXISTS_TAC [`x':mlstring`; `TYPE_SUBST tyin bty`;
                                  `TYPE_SUBST tyin (typeof t)`] THEN
            ASM_MESON_TAC[];
            REWRITE_TAC[VFREE_IN_def] THEN
            QPAT_X_ASSUM "!u uty. VFREE_IN (hol_Var u uty) tm' <=> _"
              (fun th -> REWRITE_TAC[th]) THEN
            USE_THEN "F6" (fun th -> REWRITE_TAC[th]) THEN
            USE_THEN "F3" MP_TAC THEN
            REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[]]];
        (* the clash is another variable *)
        DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN
        REWRITE_TAC[VFREE_IN_def] THEN
        SUBGOAL_THEN `~(hol_Var b (TYPE_SUBST tyin bty) = hol_Var x (TYPE_SUBST tyin ty)) /\
                      ~(hol_Var b bty = hol_Var x ty)` STRIP_ASSUME_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
          REWRITE_TAC[injectivity "hol_term"] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `~(REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty))
                        (CONS (hol_Var b bty,hol_Var b (TYPE_SUBST tyin bty)) env)
                        (hol_Var x ty) = hol_Var x ty)` THEN
        ASM_REWRITE_TAC[REV_ASSOCD]];
      (* the body is a result *)
      REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`y:mlstring`; `yty:hol_type`] THEN
        REWRITE_TAC[VFREE_IN_def] THEN STRIP_TAC THEN
        QPAT_X_ASSUM "!x ty. VFREE_IN (hol_Var x ty) t ==> _"
          (MP_TAC o SPECL [`y:mlstring`; `yty:hol_type`]) THEN
        ASM_REWRITE_TAC[REV_ASSOCD] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[typeof_def; TYPE_SUBST_def; MAP; CSYNAUX_P3_has_type_Abs;
                    injectivity "hol_term"] THEN
        MAP_EVERY EXISTS_TAC [`b:mlstring`; `TYPE_SUBST tyin bty`;
                              `TYPE_SUBST tyin (typeof t)`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[VFREE_IN_def] THEN
        QPAT_X_ASSUM "!u uty. VFREE_IN (hol_Var u uty) tm' <=> _"
          (fun th -> REWRITE_TAC[th]) THEN
        QPAT_X_ASSUM "!x ty. VFREE_IN (hol_Var x ty) t ==> _" MP_TAC THEN
        REWRITE_TAC[REV_ASSOCD; injectivity "hol_term"; COND_RAND; COND_RATOR;
                    COND_EXPAND] THEN
        MESON_TAC[]]]]);;

let INST_CORE_NIL_IS_RESULT = prove
 (`!tyin tm. welltyped tm ==> IS_RESULT (INST_CORE [] tyin tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IS_RESULT_def]);;

let INST_HAS_TYPE = prove
 (`!tm ty tyin ty'. tm has_type ty /\ ty' = TYPE_SUBST tyin ty
                    ==> INST tyin tm has_type ty'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL
   [ASM_MESON_TAC[welltyped_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RESULT_def] THEN ASM_MESON_TAC[WELLTYPED_LEMMA]);;

let INST_WELLTYPED = prove
 (`!tm tyin. welltyped tm ==> welltyped (INST tyin tm)`,
  MESON_TAC[INST_HAS_TYPE; WELLTYPED; welltyped_def]);;

let INST_CORE_NIL = prove
 (`!env tyin tm.
     welltyped tm /\ tyin = [] /\
     (!x ty. VFREE_IN (hol_Var x ty) tm
             ==> REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty)) env (hol_Var x ty) =
                 hol_Var x ty)
     ==> INST_CORE env tyin tm = hol_Result tm`,
  SUBGOAL_THEN
   `!tm env. welltyped tm /\
             (!x ty. VFREE_IN (hol_Var x ty) tm
                     ==> REV_ASSOCD (hol_Var x ty) env (hol_Var x ty) = hol_Var x ty)
             ==> INST_CORE env [] tm = hol_Result tm`
    (fun th -> REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
               MATCH_MP_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[TYPE_SUBST_NIL]) THEN
               ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INST_CORE_def; TYPE_SUBST_NIL] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[VFREE_IN_def];
    REWRITE_TAC[INST_CORE_def; TYPE_SUBST_NIL];
    MAP_EVERY X_GEN_TAC [`s:hol_term`; `t:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHs") (LABEL_TAC "IHt")) THEN
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; VFREE_IN_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `INST_CORE env [] s = hol_Result s /\ INST_CORE env [] t = hol_Result t`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [REMOVE_THEN "IHs" MATCH_MP_TAC; REMOVE_THEN "IHt" MATCH_MP_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[IS_CLASH_def; RESULT_def];
    MAP_EVERY X_GEN_TAC [`v:hol_term`; `t:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "IHt")) THEN
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:mlstring`; `bty:hol_type`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v:hol_term`)) THEN
    SUBGOAL_THEN `INST_CORE (CONS (hol_Var b bty,hol_Var b bty) env) [] t = hol_Result t`
      ASSUME_TAC THENL
     [REMOVE_THEN "IHt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VFREE_IN_def]) THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[INST_CORE_def; dest_var_def; TYPE_SUBST_NIL] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[pair_CASE] THEN ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def]]);;

let INST_nil = prove
 (`welltyped tm ==> INST [] tm = tm`,
  DISCH_TAC THEN REWRITE_TAC[INST_def] THEN
  MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `[]:(hol_type#hol_type)list`;
                `tm:hol_term`] INST_CORE_NIL) THEN
  ASM_REWRITE_TAC[REV_ASSOCD] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RESULT_def]);;

(* tyvars and tvars *)

let tyvars_ALL_DISTINCT = prove
 (`!ty. ALL_DISTINCT (hol_tyvars ty)`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[hol_tyvars_def; ALL_DISTINCT; MEM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`l:hol_type list`,`l:hol_type list`) THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ITLIST; ALL_DISTINCT; ALL_DISTINCT_LIST_UNION]);;
let _ = cake_add_simps [tyvars_ALL_DISTINCT];;

let tvars_ALL_DISTINCT = prove
 (`!tm. ALL_DISTINCT (tvars tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  ASM_SIMP_TAC[tvars_def; tyvars_ALL_DISTINCT; ALL_DISTINCT_LIST_UNION]);;
let _ = cake_add_simps [tvars_ALL_DISTINCT];;

let tyvars_TYPE_SUBST = prove
 (`!ty tyin.
     set_of_list (hol_tyvars (TYPE_SUBST tyin ty)) =
     {v | ?x. MEM x (hol_tyvars ty) /\
              MEM v (hol_tyvars (REV_ASSOCD (Tyvar x) tyin (Tyvar x)))}`,
  MATCH_MP_TAC type_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[TYPE_SUBST_def; hol_tyvars_def; MEM; EXTENSION; IN_ELIM_THM;
                IN_SET_OF_LIST] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[TYPE_SUBST_def; hol_tyvars_def; EXTENSION; IN_ELIM_THM;
                IN_SET_OF_LIST; MEM_FOLDR_LIST_UNION; MEM; MEM_MAP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST]) THEN
    ASM_MESON_TAC[]]);;

let tyvars_typeof_subset_tvars = prove
 (`!tm ty. tm has_type ty
           ==> set_of_list (hol_tyvars ty) SUBSET set_of_list (tvars tm)`,
  MATCH_MP_TAC has_type_ind THEN
  REWRITE_TAC[tvars_def; hol_tyvars_def; ITLIST; MEM_LIST_UNION; set_of_list] THEN
  SET_TAC[]);;

let tyvars_Tyapp_MAP_Tyvar = prove
 (`!x ls. ALL_DISTINCT ls ==> hol_tyvars (Tyapp x (MAP Tyvar ls)) = LIST_UNION [] ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; LIST_UNION_NIL] THEN
  REWRITE_TAC[hol_tyvars_def; MAP; ITLIST] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[hol_tyvars_def; LIST_UNION_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[LIST_UNION_def; ITLIST; LIST_INSERT_def]);;

let STRING_SORT_SET_TO_LIST_set_tvars = prove
 (`!tm. STRING_SORT (MAP explode (list_of_set (set_of_list (tvars tm)))) =
        STRING_SORT (MAP explode (tvars tm))`,
  GEN_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (list_of_set (set_of_list (tvars tm)))` ASSUME_TAC THENL
   [SIMP_TAC[ALL_DISTINCT_SET_TO_LIST; FINITE_SET_OF_LIST]; ALL_TAC] THEN
  ASM_SIMP_TAC[STRING_SORT_EQ; ALL_DISTINCT_MAP_explode; tvars_ALL_DISTINCT] THEN
  MATCH_MP_TAC PERM_MAP THEN MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  ASM_SIMP_TAC[tvars_ALL_DISTINCT; MEM_LIST_OF_SET; FINITE_SET_OF_LIST;
               IN_SET_OF_LIST]);;

let mlstring_sort_SET_TO_LIST_set_tvars = prove
 (`mlstring_sort (list_of_set (set_of_list (tvars tm))) = mlstring_sort (tvars tm)`,
  REWRITE_TAC[mlstring_sort_def; STRING_SORT_SET_TO_LIST_set_tvars]);;
