(* ========================================================================= *)
(* holSyntaxExtra, part 2 (HOL4 holSyntaxExtraScript.sml lines 336-965):     *)
(* the term ordering (type_lt, term_lt, type_cmp, term_cmp are total         *)
(* orders) and the alpha ordering orda (agrees with RACONV, symmetric,       *)
(* transitive).  Notes on the rendering: holSyntaxExtra_p1.ml.               *)
(* - HOL4 mlstring$compare is mlstring_compare, pair_cmp is pair_compare,    *)
(*   list_cmp is list_compare, flip_ord is invert_comparison.                *)
(* - HOL4's irreflexive_mlstring_lt (local) is hol_irreflexive_mlstring_lt   *)
(*   (names.tsv: mlstring.ml has its own irreflexive_mlstring_lt).           *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_P2_.               *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* term ordering *)

let type_lt_thm = prove
 (`(!x1 x2. type_lt (Tyvar x1) (Tyvar x2) <=> mlstring_lt x1 x2) /\
   (!x1 x2 args2. type_lt (Tyvar x1) (Tyapp x2 args2) <=> T) /\
   (!x1 args1 x2. type_lt (Tyapp x1 args1) (Tyvar x2) <=> F) /\
   (!x1 args1 x2 args2.
      type_lt (Tyapp x1 args1) (Tyapp x2 args2) <=>
      (mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN SIMP[ONCE type_lt_cases]);;

let term_lt_thm = prove
 (`(!x1 ty1 x2 ty2.
      term_lt (hol_Var x1 ty1) (hol_Var x2 ty2) <=>
      (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) /\
   (!x1 ty1 x2 ty2. term_lt (hol_Var x1 ty1) (hol_Const x2 ty2) <=> T) /\
   (!x1 ty1 t1 t2. term_lt (hol_Var x1 ty1) (hol_Comb t1 t2) <=> T) /\
   (!x1 ty1 t1 t2. term_lt (hol_Var x1 ty1) (hol_Abs t1 t2) <=> T) /\
   (!x1 ty1 x2 ty2. term_lt (hol_Const x1 ty1) (hol_Var x2 ty2) <=> F) /\
   (!x1 ty1 x2 ty2.
      term_lt (hol_Const x1 ty1) (hol_Const x2 ty2) <=>
      (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) /\
   (!x1 ty1 t1 t2. term_lt (hol_Const x1 ty1) (hol_Comb t1 t2) <=> T) /\
   (!x1 ty1 t1 t2. term_lt (hol_Const x1 ty1) (hol_Abs t1 t2) <=> T) /\
   (!s1 s2 x2 ty2. term_lt (hol_Comb s1 s2) (hol_Var x2 ty2) <=> F) /\
   (!s1 s2 x2 ty2. term_lt (hol_Comb s1 s2) (hol_Const x2 ty2) <=> F) /\
   (!s1 s2 t1 t2.
      term_lt (hol_Comb s1 s2) (hol_Comb t1 t2) <=>
      (term_lt LEX term_lt) (s1,s2) (t1,t2)) /\
   (!s1 s2 t1 t2. term_lt (hol_Comb s1 s2) (hol_Abs t1 t2) <=> T) /\
   (!s1 s2 x2 ty2. term_lt (hol_Abs s1 s2) (hol_Var x2 ty2) <=> F) /\
   (!s1 s2 x2 ty2. term_lt (hol_Abs s1 s2) (hol_Const x2 ty2) <=> F) /\
   (!s1 s2 t1 t2. term_lt (hol_Abs s1 s2) (hol_Comb t1 t2) <=> F) /\
   (!s1 s2 t1 t2.
      term_lt (hol_Abs s1 s2) (hol_Abs t1 t2) <=>
      (term_lt LEX term_lt) (s1,s2) (t1,t2))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN SIMP[ONCE term_lt_cases]);;

let type_cmp_refl = prove
 (`type_cmp t t = EQUAL`,
  REWRITE_TAC[type_cmp_def; TO_of_LinearOrder]);;
let _ = cake_add_simps [type_cmp_refl];;

let term_cmp_refl = prove
 (`term_cmp t t = EQUAL`,
  REWRITE_TAC[term_cmp_def; TO_of_LinearOrder]);;
let _ = cake_add_simps [term_cmp_refl];;

let CSYNAUX_P2_LLEX_CONS = prove
 (`!(R:A->A->bool) h1 t1 h2 t2.
     LLEX R (CONS h1 t1) (CONS h2 t2) <=> R h1 h2 \/ h1 = h2 /\ LLEX R t1 t2`,
  REWRITE_TAC[LLEX_def; list_CASE] THEN MESON_TAC[]);;

let CSYNAUX_P2_LLEX_trichotomous = prove
 (`!(R:A->A->bool) l1 l2.
     ALL (\a. !b. R a b \/ R b a \/ a = b) l1
     ==> LLEX R l1 l2 \/ LLEX R l2 l1 \/ l1 = l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:A list` list_CASES) THEN
  REWRITE_TAC[LLEX_def; LLEX_NIL2; CSYNAUX_P2_LLEX_CONS; ALL; NOT_CONS_NIL;
              CONS_11] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':A list`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CSYNAUX_P2_LLEX_trans = prove
 (`!(Q:A->A->bool) R l1 l2 l3.
     (!a b. Q a b ==> R a b) /\ (!a b c. Q a b /\ R b c ==> R a c) /\
     LLEX Q l1 l2 /\ LLEX R l2 l3 ==> LLEX R l1 l3`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `l3:A list` list_CASES) THEN
  REWRITE_TAC[LLEX_def; LLEX_NIL2; CSYNAUX_P2_LLEX_CONS; NOT_CONS_NIL;
              list_CASE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let irreflexive_type_lt = prove
 (`irreflexive type_lt`,
  MP_TAC StrongLinearOrder_mlstring_lt THEN
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC type_ind THEN
  ASM_REWRITE_TAC[type_lt_thm; LEX_DEF_THM] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL; LLEX_def; CSYNAUX_P2_LLEX_CONS]);;

let trichotomous_type_lt = prove
 (`trichotomous type_lt`,
  MP_TAC StrongLinearOrder_mlstring_lt THEN
  REWRITE_TAC[StrongLinearOrder; trichotomous] THEN STRIP_TAC THEN
  MATCH_MP_TAC type_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; DISCH_TAC THEN GEN_TAC] THEN
  STRUCT_CASES_TAC(SPEC `b:hol_type` (CONJUNCT1 (cases "hol_type"))) THEN
  REWRITE_TAC[type_lt_thm; LEX_DEF_THM; injectivity "hol_type";
              distinctness "hol_type"] THENL
   [ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `a1:hol_type list` o
      MATCH_MP CSYNAUX_P2_LLEX_trichotomous) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:mlstring`; `a0:mlstring`]) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let transitive_type_lt = prove
 (`!x y. type_lt x y ==> !z. type_lt y z ==> type_lt x z`,
  MATCH_MP_TAC type_lt_strongind THEN
  MP_TAC StrongLinearOrder_mlstring_lt THEN
  REWRITE_TAC[StrongLinearOrder; StrongOrder; transitive_def] THEN
  STRIP_TAC THEN REPEAT STRIP_TAC THEN CASES_ON `z:hol_type` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[type_lt_thm; LEX_DEF_THM]) THEN
  ASM_REWRITE_TAC[type_lt_thm; LEX_DEF_THM] THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST
     [DISJ2_TAC THEN MATCH_MP_TAC CSYNAUX_P2_LLEX_trans THEN
      EXISTS_TAC `\a b. type_lt a b /\ !z. type_lt b z ==> type_lt a z` THEN
      EXISTS_TAC `args2:hol_type list` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let StrongLinearOrder_type_lt = prove
 (`StrongLinearOrder type_lt`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_type_lt;
              trichotomous_type_lt; transitive_def] THEN
  MESON_TAC[transitive_type_lt]);;

let TotOrd_type_cmp = prove
 (`TotOrd type_cmp`,
  REWRITE_TAC[type_cmp_def] THEN MATCH_MP_TAC TotOrd_TO_of_Strong THEN
  ACCEPT_TAC StrongLinearOrder_type_lt);;

let irreflexive_term_lt = prove
 (`irreflexive term_lt`,
  MP_TAC StrongLinearOrder_mlstring_lt THEN
  MP_TAC StrongLinearOrder_type_lt THEN
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_def] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  ASM_SIMP_TAC[term_lt_thm; LEX_DEF_THM]);;

let trichotomous_term_lt = prove
 (`trichotomous term_lt`,
  MP_TAC StrongLinearOrder_mlstring_lt THEN
  MP_TAC StrongLinearOrder_type_lt THEN
  REWRITE_TAC[StrongLinearOrder; trichotomous] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(SPEC `b:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[term_lt_thm; LEX_DEF_THM; injectivity "hol_term";
              distinctness "hol_term"] THEN
  ASM_MESON_TAC[]);;

let transitive_term_lt = prove
 (`!x y. term_lt x y ==> !z. term_lt y z ==> term_lt x z`,
  MATCH_MP_TAC term_lt_strongind THEN
  MP_TAC StrongLinearOrder_mlstring_lt THEN
  MP_TAC StrongLinearOrder_type_lt THEN
  REWRITE_TAC[StrongLinearOrder; StrongOrder; transitive_def] THEN
  REPEAT STRIP_TAC THEN CASES_ON `z:hol_term` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[term_lt_thm; LEX_DEF_THM]) THEN
  ASM_REWRITE_TAC[term_lt_thm; LEX_DEF_THM] THEN ASM_MESON_TAC[]);;

let StrongLinearOrder_term_lt = prove
 (`StrongLinearOrder term_lt`,
  REWRITE_TAC[StrongLinearOrder; StrongOrder; irreflexive_term_lt;
              trichotomous_term_lt; transitive_def] THEN
  MESON_TAC[transitive_term_lt]);;

let TotOrd_term_cmp = prove
 (`TotOrd term_cmp`,
  REWRITE_TAC[term_cmp_def] THEN MATCH_MP_TAC TotOrd_TO_of_Strong THEN
  ACCEPT_TAC StrongLinearOrder_term_lt);;

let StrongLinearOrder_irreflexive = prove
 (`StrongLinearOrder (R:A->A->bool) ==> irreflexive R`,
  SIMP_TAC[StrongLinearOrder; StrongOrder]);;

(* HOL4: irreflexive_mlstring_lt [local] *)
let hol_irreflexive_mlstring_lt =
  MATCH_MP StrongLinearOrder_irreflexive StrongLinearOrder_mlstring_lt;;

let LLEX_irreflexive = prove
 (`!R:A->A->bool. irreflexive R ==> irreflexive (LLEX R)`,
  GEN_TAC THEN REWRITE_TAC[irreflexive_def] THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LLEX_def; CSYNAUX_P2_LLEX_CONS]);;

let irreflexive_LLEX_type_lt =
  MATCH_MP LLEX_irreflexive irreflexive_type_lt;;

let CSYNAUX_P2_compare_TO = prove
 (`mlstring_compare = TO_of_LinearOrder mlstring_lt`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`s1:mlstring`; `s2:mlstring`] THEN
  REWRITE_TAC[TO_of_LinearOrder; mlstring_lt_def] THEN
  MP_TAC TotOrd_compare THEN REWRITE_TAC[TotOrd] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mlstring_compare s1 s2` ordering_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"] THEN
  ASM_MESON_TAC[distinctness "ordering"]);;

let type_cmp_thm = prove
 (CASE_TERM
  `!t1 t2. type_cmp t1 t2 =
     match (t1,t2) with
       (Tyvar x1, Tyvar x2) -> mlstring_compare x1 x2
     | (Tyvar _, _) -> LESS
     | (_, Tyvar _) -> GREATER
     | (Tyapp x1 a1, Tyapp x2 a2) ->
         pair_compare mlstring_compare (list_compare type_cmp) (x1,a1) (x2,a2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `t1:hol_type` (CONJUNCT1 (cases "hol_type"))) THEN
  STRUCT_CASES_TAC(SPEC `t2:hol_type` (CONJUNCT1 (cases "hol_type"))) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP pair_cmp_lexTO
    (CONJ TotOrd_compare (MATCH_MP TotOrd_list_cmp TotOrd_type_cmp))] THEN
  REWRITE_TAC[type_cmp_def; CSYNAUX_P2_compare_TO;
    SYM(MATCH_MP TO_of_LinearOrder_LLEX irreflexive_type_lt)] THEN
  REWRITE_TAC[SYM(MATCH_MP TO_of_LinearOrder_LEX
    (CONJ hol_irreflexive_mlstring_lt irreflexive_LLEX_type_lt))] THEN
  REWRITE_TAC[TO_of_LinearOrder; type_lt_thm; injectivity "hol_type";
              distinctness "hol_type"; PAIR_EQ]);;

let type_cmp_ind = prove
 (`!P. (!t1 t2.
          (!x1 a1 x2 a2 x y.
             t1 = Tyapp x1 a1 /\ t2 = Tyapp x2 a2 /\ MEM x a1 /\ MEM y a2
             ==> P x y)
          ==> P t1 t2)
       ==> !t1 t2. P t1 t2`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN MATCH_MP_TAC type_ind THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  USE_THEN "H" MATCH_MP_TAC THEN
  REWRITE_TAC[distinctness "hol_type"; injectivity "hol_type"] THEN
  ASM_MESON_TAC[]);;

let term_cmp_thm = prove
 (CASE_TERM
  `!t1 t2. term_cmp t1 t2 =
     match (t1,t2) with
       (hol_Var x1 ty1, hol_Var x2 ty2) ->
         pair_compare mlstring_compare type_cmp (x1,ty1) (x2,ty2)
     | (hol_Var _ _, _) -> LESS
     | (_, hol_Var _ _) -> GREATER
     | (hol_Const x1 ty1, hol_Const x2 ty2) ->
         pair_compare mlstring_compare type_cmp (x1,ty1) (x2,ty2)
     | (hol_Const _ _, _) -> LESS
     | (_, hol_Const _ _) -> GREATER
     | (hol_Comb s1 t1, hol_Comb s2 t2) ->
         pair_compare term_cmp term_cmp (s1,t1) (s2,t2)
     | (hol_Comb _ _, _) -> LESS
     | (_, hol_Comb _ _) -> GREATER
     | (hol_Abs s1 t1, hol_Abs s2 t2) ->
         pair_compare term_cmp term_cmp (s1,t1) (s2,t2)
     | (hol_Abs _ _, _) -> LESS
     | (_, hol_Abs _ _) -> GREATER`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `t1:hol_term` (cases "hol_term")) THEN
  STRUCT_CASES_TAC(SPEC `t2:hol_term` (cases "hol_term")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP pair_cmp_lexTO (CONJ TotOrd_compare TotOrd_type_cmp);
              MATCH_MP pair_cmp_lexTO (CONJ TotOrd_term_cmp TotOrd_term_cmp)] THEN
  REWRITE_TAC[term_cmp_def; type_cmp_def; CSYNAUX_P2_compare_TO] THEN
  REWRITE_TAC[SYM(MATCH_MP TO_of_LinearOrder_LEX
                (CONJ hol_irreflexive_mlstring_lt irreflexive_type_lt));
              SYM(MATCH_MP TO_of_LinearOrder_LEX
                (CONJ irreflexive_term_lt irreflexive_term_lt))] THEN
  REWRITE_TAC[TO_of_LinearOrder; term_lt_thm; injectivity "hol_term";
              distinctness "hol_term"; PAIR_EQ]);;

let term_cmp_ind = prove
 (`!P. (!t1 t2.
          (!x1 y1 x2 y2. t1 = hol_Comb x1 y1 /\ t2 = hol_Comb x2 y2 ==> P x1 x2) /\
          (!x1 y1 x2 y2. t1 = hol_Comb x1 y1 /\ t2 = hol_Comb x2 y2 ==> P y1 y2) /\
          (!x1 y1 x2 y2. t1 = hol_Abs x1 y1 /\ t2 = hol_Abs x2 y2 ==> P x1 x2) /\
          (!x1 y1 x2 y2. t1 = hol_Abs x1 y1 /\ t2 = hol_Abs x2 y2 ==> P y1 y2)
          ==> P t1 t2)
       ==> !t1 t2. P t1 t2`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REPEAT STRIP_TAC THEN USE_THEN "H" MATCH_MP_TAC THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN
  ASM_MESON_TAC[]);;

(* alpha ordering *)

let ALPHAVARS_ordav = prove
 (`!env tp. ALPHAVARS env tp ==> ordav env (FST tp) (SND tp) = EQUAL`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALPHAVARS_def; ordav_def; FST; SND] THENL
   [SIMP_TAC[term_cmp_refl];
    PAIR_CASES_ON `h:hol_term#hol_term` THEN
    REWRITE_TAC[ALPHAVARS_def; ordav_def; FST; SND; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p1,p2):hol_term#hol_term`) THEN
    ASM_REWRITE_TAC[FST; SND]]);;

let ordav_ALPHAVARS = prove
 (`!env t1 t2. ordav env t1 t2 = EQUAL ==> ALPHAVARS env (t1,t2)`,
  MATCH_MP_TAC ordav_ind THEN
  REWRITE_TAC[ALPHAVARS_def; ordav_def; FST; SND; PAIR_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[term_cmp_def; TO_of_LinearOrder] THEN REPEAT GEN_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[distinctness "ordering"];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "ordering"] THEN ASM_MESON_TAC[]]);;

let ALPHAVARS_eq_ordav = prove
 (`!env t1 t2. ALPHAVARS env (t1,t2) <=> ordav env t1 t2 = EQUAL`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[ordav_ALPHAVARS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ALPHAVARS_ordav) THEN REWRITE_TAC[FST; SND]);;

let RACONV_orda = prove
 (`!env tp. RACONV env tp ==> orda env (FST tp) (SND tp) = EQUAL`,
  MATCH_MP_TAC RACONV_ind THEN REWRITE_TAC[FST; SND; ALPHAVARS_eq_ordav] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[orda_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; term_cmp_refl; type_cmp_refl; COND_ID]);;

let orda_RACONV = prove
 (`!env t1 t2. orda env t1 t2 = EQUAL ==> RACONV env (t1,t2)`,
  MATCH_MP_TAC orda_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[orda_def] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN DISCH_TAC THEN
    MATCH_MP_TAC RACONV_REFL THEN REWRITE_TAC[ALL];
    ALL_TAC] THEN
  CASES_ON `t1:hol_term` THEN CASES_ON `t2:hol_term` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[RACONV; distinctness "ordering"] THEN
  TRY(REWRITE_TAC[ALPHAVARS_eq_ordav] THEN NO_TAC) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; CONJUNCT1(REWRITE_RULE[TotOrd] TotOrd_term_cmp);
              CONJUNCT1(REWRITE_RULE[TotOrd] TotOrd_type_cmp); injectivity "hol_term"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"; distinctness "hol_term"]) THEN
  TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "ordering";
                  CONJUNCT1(REWRITE_RULE[TotOrd] TotOrd_type_cmp)] THEN
  ASM_MESON_TAC[type_cmp_refl]);;

let RACONV_eq_orda = prove
 (`!env t1 t2. RACONV env (t1,t2) <=> orda env t1 t2 = EQUAL`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[orda_RACONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RACONV_orda) THEN REWRITE_TAC[FST; SND]);;

let ACONV_eq_orda = prove
 (`!t1 t2. ACONV t1 t2 <=> orda [] t1 t2 = EQUAL`,
  REWRITE_TAC[ACONV_def; RACONV_eq_orda]);;

let ordav_FILTER = prove
 (CASE_TERM
  `!env x y. ordav env x y =
     match FILTER (\(x',y'). x' = x \/ y' = y) env with
       [] -> term_cmp x y
     | CONS (x',y') _ ->
         if x' = x then if y' = y then EQUAL else LESS else GREATER`,
  MATCH_MP_TAC ordav_ind THEN SIMP[ordav_def; FILTER] THEN REPEAT STRIP_TAC THEN
  RW[] THEN FS[]);;

let CSYNAUX_P2_invert_TotOrd = prove
 (`!c:A->A->ordering. TotOrd c ==> !x y. invert_comparison (c x y) = c y x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C AP_THM `y:A` o C AP_THM `x:A` o MATCH_MP TO_inv_invert) THEN
  REWRITE_TAC[TO_inv; CURRY_DEF; o_THM; UNCURRY_DEF] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let ordav_sym = prove
 (`!env v1 v2. invert_comparison (ordav env v1 v2) =
               ordav (MAP (\(x,y). (y,x)) env) v2 v1`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ordav_def; MAP; MATCH_MP CSYNAUX_P2_invert_TotOrd TotOrd_term_cmp];
    PAIR_CASES_ON `h:hol_term#hol_term` THEN
    SIMP[ordav_def; MAP] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `v1:hol_term = h0` THEN ASM_CASES_TAC `v2:hol_term = h1` THEN
    ASM_REWRITE_TAC[invert_comparison_def]]);;

let orda_sym = prove
 (`!env t1 t2. invert_comparison (orda env t1 t2) =
               orda (MAP (\(x,y). (y,x)) env) t2 t1`,
  MATCH_MP_TAC orda_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[orda_def] THEN REWRITE_TAC[MAP_EQ_NIL] THEN
  ASM_CASES_TAC `t1:hol_term = t2 /\ env:(hol_term#hol_term)list = []` THENL
   [ASM_REWRITE_TAC[invert_comparison_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t2:hol_term = t1 /\ env:(hol_term#hol_term)list = [])`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `t1:hol_term` THEN CASES_ON `t2:hol_term` THEN
  RFS[injectivity "hol_term"; invert_comparison_def; ordav_sym; MAP;
      MATCH_MP CSYNAUX_P2_invert_TotOrd TotOrd_term_cmp] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_CASES_TAC `orda env a0 a0' = EQUAL` THEN
    ASM_REWRITE_TAC[invert_comparison_def; invert_eq_EQUAL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBST1_TAC(SYM(SPECL [`typeof a0`; `typeof a0'`]
      (MATCH_MP CSYNAUX_P2_invert_TotOrd TotOrd_type_cmp))) THEN
    ASM_CASES_TAC `type_cmp (typeof a0) (typeof a0') = EQUAL` THEN
    ASM_REWRITE_TAC[invert_comparison_def; invert_eq_EQUAL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let antisymmetric_alpha_lt = prove
 (`antisymmetric alpha_lt`,
  REWRITE_TAC[antisymmetric_def; alpha_lt_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `x:hol_term`; `y:hol_term`]
    orda_sym) THEN
  ASM_REWRITE_TAC[MAP; invert_comparison_def; distinctness "ordering"]);;

(* HOL4: orda env t1 t2 = the else branch of orda_def *)
let orda_thm =
  let env = `env:(hol_term#hol_term)list`
  and t1 = `t1:hol_term` and t2 = `t2:hol_term` in
  let _,(_,b) = dest_cond(rhs(concl(SPECL [env; t1; t2] orda_def))) in
  prove
   (list_mk_forall([env; t1; t2], mk_eq(list_mk_comb(`orda`,[env; t1; t2]), b)),
    SUBGOAL_THEN `!env t. ALL (UNCURRY (=)) env ==> orda env t t = EQUAL`
      ASSUME_TAC THENL [MESON_TAC[RACONV_REFL; RACONV_eq_orda]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [orda_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    CASES_ON `t2:hol_term` THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ordav_def; term_cmp_refl; type_cmp_refl; LET_DEF; LET_END_DEF;
                 ALL; UNCURRY_DEF]);;

let ordav_lx_trans = prove
 (`!t1 t2 t3 env1 env2.
     ~(ordav env1 t1 t2 = GREATER) /\
     ~(ordav env2 t2 t3 = GREATER) /\
     MAP SND env1 = MAP FST env2
     ==> ~(ordav (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = GREATER) /\
         (ordav env1 t1 t2 = LESS \/ ordav env2 t2 t3 = LESS
          ==> ordav (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = LESS)`,
  MP_TAC TotOrd_term_cmp THEN REWRITE_TAC[TotOrd] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`env2:(hol_term#hol_term)list`,`env2:(hol_term#hol_term)list`) THEN
  SPEC_TAC(`env1:(hol_term#hol_term)list`,`env1:(hol_term#hol_term)list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `env2:(hol_term#hol_term)list` list_CASES) THEN
  REWRITE_TAC[MAP; ZIP; ordav_def; NOT_CONS_NIL] THENL
   [MP_TAC(ISPEC `term_cmp t1 t2` ordering_nchotomy) THEN
    MP_TAC(ISPEC `term_cmp t2 t3` ordering_nchotomy) THEN
    MP_TAC(ISPEC `term_cmp t1 t3` ordering_nchotomy) THEN
    ASM_MESON_TAC[distinctness "ordering"];
    PAIR_CASES_ON `h:hol_term#hol_term` THEN
    PAIR_CASES_ON `h':hol_term#hol_term` THEN
    REWRITE_TAC[MAP; ZIP; ordav_def; CONS_11] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t':(hol_term#hol_term)list`) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t1:hol_term = h0` THEN ASM_CASES_TAC `t2:hol_term = h'0` THEN
    ASM_CASES_TAC `t3:hol_term = h'1` THEN
    ASM_REWRITE_TAC[distinctness "ordering"] THEN CONV_TAC TAUT]);;

let undo_zip_map_fst = prove
 (`CONS (p:A#B) (ZIP (MAP FST (l1:(A#C)list)) (MAP SND (l2:(C#B)list))) =
   ZIP (MAP FST (CONS (FST p,v2) l1)) (MAP SND (CONS (v2,SND p) l2))`,
  REWRITE_TAC[MAP; ZIP; FST; SND; PAIR]);;

let CSYNAUX_P2_orda_EQUAL_trans = prove
 (`!env1 t1 t2 env2 t3.
     orda env1 t1 t2 = EQUAL /\ orda env2 t2 t3 = EQUAL /\
     MAP SND env1 = MAP FST env2
     ==> orda (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = EQUAL`,
  REWRITE_TAC[GSYM RACONV_eq_orda] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`env1:(hol_term#hol_term)list`; `(t1,t2):hol_term#hol_term`]
    RACONV_TRANS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(MP_TAC o SPECL [`MAP SND (env2:(hol_term#hol_term)list)`; `t3:hol_term`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(hol_term)list->num`) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; ZIP_MAP_FST_SND_EQ] THEN SIMP_TAC[]);;

let CSYNAUX_P2_TotOrd_lx_trans = prove
 (`!c:A->A->ordering. TotOrd c ==>
     !x y z. (c x y = LESS /\ ~(c y z = GREATER) \/
              ~(c x y = GREATER) /\ c y z = LESS ==> c x z = LESS) /\
             (c x y = EQUAL /\ c y z = EQUAL ==> c x z = EQUAL)`,
  GEN_TAC THEN REWRITE_TAC[TotOrd] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(c:A->A->ordering) x y` ordering_nchotomy) THEN
  MP_TAC(ISPEC `(c:A->A->ordering) y z` ordering_nchotomy) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"] THEN
  ASM_MESON_TAC[distinctness "ordering"]);;

let CSYNAUX_P2_lex_step = prove
 (`!c1 c2 c3 d1 d2 d3:ordering.
     (c1 = LESS /\ ~(c2 = GREATER) \/ ~(c1 = GREATER) /\ c2 = LESS
      ==> c3 = LESS) /\
     (c1 = EQUAL /\ c2 = EQUAL ==> c3 = EQUAL) /\
     (d1 = LESS /\ ~(d2 = GREATER) \/ ~(d1 = GREATER) /\ d2 = LESS
      ==> d3 = LESS) /\
     ((if ~(c1 = EQUAL) then c1 else d1) = LESS /\
      ~((if ~(c2 = EQUAL) then c2 else d2) = GREATER) \/
      ~((if ~(c1 = EQUAL) then c1 else d1) = GREATER) /\
      (if ~(c2 = EQUAL) then c2 else d2) = LESS)
     ==> (if ~(c3 = EQUAL) then c3 else d3) = LESS`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(SPEC t ordering_nchotomy))
    [`c1:ordering`; `c2:ordering`; `c3:ordering`] THEN
  REWRITE_TAC[distinctness "ordering"] THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(SPEC t ordering_nchotomy))
    [`d1:ordering`; `d2:ordering`; `d3:ordering`] THEN
  REWRITE_TAC[distinctness "ordering"]);;

let CSYNAUX_P2_orda_LESS_trans = prove
 (`!t1 env1 t2 env2 t3.
     MAP SND env1 = MAP FST env2 /\
     (orda env1 t1 t2 = LESS /\ ~(orda env2 t2 t3 = GREATER) \/
      ~(orda env1 t1 t2 = GREATER) /\ orda env2 t2 t3 = LESS)
     ==> orda (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = LESS`,
  let split_tac =
    NAMED_CASES_ON "t2" ["x2 ty2"; "x2 ty2"; "s2 u2"; "s2 u2"] THEN
    NAMED_CASES_ON "t3" ["x3 ty3"; "x3 ty3"; "s3 u3"; "s3 u3"] THEN
    ONCE_REWRITE_TAC[orda_thm] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "ordering"; LET_DEF; LET_END_DEF] in
  let gens = MAP_EVERY X_GEN_TAC
    [`env1:(hol_term#hol_term)list`; `t2:hol_term`;
     `env2:(hol_term#hol_term)list`; `t3:hol_term`] in
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x1:mlstring`; `ty1:hol_type`] THEN gens THEN
    split_tac THEN MESON_TAC[ordav_lx_trans; distinctness "ordering"];
    MAP_EVERY X_GEN_TAC [`x1:mlstring`; `ty1:hol_type`] THEN gens THEN
    split_tac THEN
    MESON_TAC[MATCH_MP CSYNAUX_P2_TotOrd_lx_trans TotOrd_term_cmp];
    MAP_EVERY X_GEN_TAC [`s1:hol_term`; `u1:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    gens THEN split_tac THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC CSYNAUX_P2_lex_step THEN
    MAP_EVERY EXISTS_TAC
     [`orda env1 s1 s2`; `orda env2 s2 s3`; `orda env1 u1 u2`;
      `orda env2 u2 u3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN USE_THEN "IH1" MATCH_MP_TAC THEN
      EXISTS_TAC `s2:hol_term` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN MATCH_MP_TAC CSYNAUX_P2_orda_EQUAL_trans THEN
      EXISTS_TAC `s2:hol_term` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN USE_THEN "IH2" MATCH_MP_TAC THEN
      EXISTS_TAC `u2:hol_term` THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`s1:hol_term`; `u1:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    gens THEN split_tac THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBST1_TAC(REWRITE_RULE[FST; SND]
      (ISPECL [`(s1,s3):hol_term#hol_term`; `env1:(hol_term#hol_term)list`;
               `env2:(hol_term#hol_term)list`; `s2:hol_term`]
         (GENL [`p:A#B`; `l1:(A#C)list`; `l2:(C#B)list`; `v2:C`]
            undo_zip_map_fst))) THEN
    MATCH_MP_TAC CSYNAUX_P2_lex_step THEN
    MAP_EVERY EXISTS_TAC
     [`type_cmp (typeof s1) (typeof s2)`; `type_cmp (typeof s2) (typeof s3)`;
      `orda (CONS (s1,s2) env1) u1 u2`; `orda (CONS (s2,s3) env2) u2 u3`] THEN
    ASM_REWRITE_TAC[MATCH_MP CSYNAUX_P2_TotOrd_lx_trans TotOrd_type_cmp] THEN
    DISCH_TAC THEN USE_THEN "IH2" MATCH_MP_TAC THEN
    EXISTS_TAC `u2:hol_term` THEN ASM_REWRITE_TAC[MAP]]);;

let orda_lx_trans = prove
 (`!env1 t1 t2 env2 t3.
     ~(orda env1 t1 t2 = GREATER) /\
     ~(orda env2 t2 t3 = GREATER) /\
     MAP SND env1 = MAP FST env2
     ==> ~(orda (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = GREATER) /\
         (orda env1 t1 t2 = LESS \/ orda env2 t2 t3 = LESS
          ==> orda (ZIP (MAP FST env1) (MAP SND env2)) t1 t3 = LESS)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `orda env1 t1 t2 = LESS \/ orda env2 t2 t3 = LESS` THENL
   [SUBGOAL_THEN `orda (ZIP (MAP FST (env1:(hol_term#hol_term)list))
                           (MAP SND (env2:(hol_term#hol_term)list))) t1 t3 = LESS`
      (fun th -> REWRITE_TAC[th; distinctness "ordering"]) THEN
    MATCH_MP_TAC CSYNAUX_P2_orda_LESS_trans THEN
    EXISTS_TAC `t2:hol_term` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "ordering"];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `orda (ZIP (MAP FST (env1:(hol_term#hol_term)list))
                          (MAP SND (env2:(hol_term#hol_term)list))) t1 t3 = EQUAL`
      (fun th -> REWRITE_TAC[th; distinctness "ordering"]) THEN
    MATCH_MP_TAC CSYNAUX_P2_orda_EQUAL_trans THEN EXISTS_TAC `t2:hol_term` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ordering_nchotomy]]);;

let transitive_alpha_lt = prove
 (`transitive alpha_lt`,
  REWRITE_TAC[transitive_def; alpha_lt_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `x:hol_term`; `y:hol_term`;
                `[]:(hol_term#hol_term)list`; `z:hol_term`] orda_lx_trans) THEN
  ASM_REWRITE_TAC[MAP; ZIP; distinctness "ordering"] THEN SIMP_TAC[]);;

let alpha_lt_trans_ACONV = prove
 (`!x y z.
     (ACONV x y /\ alpha_lt y z ==> alpha_lt x z) /\
     (alpha_lt x y /\ ACONV y z ==> alpha_lt x z)`,
  REWRITE_TAC[alpha_lt_def; ACONV_eq_orda] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `x:hol_term`; `y:hol_term`;
                `[]:(hol_term#hol_term)list`; `z:hol_term`] orda_lx_trans) THEN
  ASM_REWRITE_TAC[MAP; ZIP; distinctness "ordering"] THEN SIMP_TAC[]);;

let alpha_lt_not_refl = prove
 (`!x. ~alpha_lt x x`,
  REWRITE_TAC[alpha_lt_def; REWRITE_RULE[ACONV_eq_orda] (SPEC_ALL ACONV_REFL);
              distinctness "ordering"]);;
let _ = cake_add_simps [alpha_lt_not_refl];;
