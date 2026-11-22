(* ========================================================================= *)
(* holSyntaxExtra: port of HOL4 candle/standard/syntax/holSyntaxExtraScript  *)
(* .sml (CakeML v3479).  Some lemmas about the syntactic functions.          *)
(* The theory is in eight consecutive parts, each loading the one before;    *)
(* holSyntaxExtra.ml loads them all.  Part 1 (HOL4 lines 1-335): type        *)
(* substitution, welltyped terms, alpha-equivalence, subtypes, subterms.     *)
(*                                                                           *)
(* Notes on the rendering (all parts):                                       *)
(* - HOL4 Overloads are written out, as in holSyntax.ml (see its header):    *)
(*   Fun s t is Tyapp (implode "fun") [s; t], Bool is Tyapp (implode "bool") *)
(*   [], Equal ty is hol_Const (implode "=") (Fun ty (Fun ty Bool)),         *)
(*   is_instance ty0 ty is ?i. ty = TYPE_SUBST i ty0, tysof, tmsof, sigof,   *)
(*   axsof, thyof on signatures, theories and contexts as there; the infix   *)
(*   subtype is RTC subtype1 and subterm is RTC subterm1; ConstDef x t is    *)
(*   hol_ConstSpec [(x,t)] (hol_Var x (typeof t) === t).                     *)
(* - HOL4's type1_size (the size of a hol_type list) is list_size            *)
(*   hol_type_size; term_size is hol_term_size; the datatype induction       *)
(*   theorem term_induction is hol_term_INDUCT; HOL4 RTC_CASES2 is HOL       *)
(*   Light's RTC_CASES_L and HOL4 RTC_INDUCT is RTC_INDUCT_R.                *)
(* - HOL4's val cpn_distinct and cpn_nchotomy are toto.ml's.                 *)
(* - The rules of subtype1 and subterm1 quantify their variables in HOL4's   *)
(*   order (by name), as those of holSyntax.ml do.                           *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/toto.ml";;
needs "hol4/comparison.ml";;
needs "hol4/ternaryComparisons.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;

prioritize_num();;
type_invention_error := true;;

let type_ind = prove
 (`!P. (!m. P (Tyvar m)) /\ (!m l. ALL P l ==> P (Tyapp m l)) ==> !t. P t`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:hol_type->bool`; `ALL (P:hol_type->bool)`]
    hol_type_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

let type1_size_append = prove
 (`!l1 l2. list_size hol_type_size (APPEND l1 l2) =
           list_size hol_type_size l1 + list_size hol_type_size l2`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; list_size_def] THEN ARITH_TAC);;

let extends_ind = prove
 (`!P. (!upd ctxt. upd updates ctxt /\ P ctxt ==> P (CONS upd ctxt))
       ==> !ctxt1 ctxt2. ctxt2 extends ctxt1 ==> P ctxt1 ==> P ctxt2`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[extends_def] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  ASM_MESON_TAC[]);;

(* deconstructing variables *)

let ALOOKUP_MAP_dest_var = prove
 (`!ls (f:A->B) x ty.
     ALL (\s. ?x ty. s = hol_Var x ty) (MAP FST ls)
     ==> ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
         OPTION_MAP f (ALOOKUP ls (hol_Var x ty))`,
  LIST_INDUCT_TAC THEN SIMP[MAP; ALOOKUP_def; OPTION_MAP_DEF] THEN
  PAIR_CASES_ON `h:hol_term#A` THEN
  RW[MAP; ALL; PAIR_MAP_THM; ALOOKUP_def; dest_var_def; OPTION_MAP_DEF] THEN
  FS[dest_var_def]);;

(* type substitution *)

let TYPE_SUBST_NIL = prove
 (`!ty. TYPE_SUBST [] ty = ty`,
  MATCH_MP_TAC type_ind THEN
  REWRITE_TAC[TYPE_SUBST_def; REV_ASSOCD; injectivity "hol_type"; MAP_EQ_ID;
              GSYM ALL_MEM] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [TYPE_SUBST_NIL];;

let TYPE_SUBST_Bool = prove
 (`!tyin. TYPE_SUBST tyin (Tyapp (implode "bool") []) = Tyapp (implode "bool") []`,
  REWRITE_TAC[TYPE_SUBST_def; MAP]);;

let is_instance_refl = prove
 (`!ty. ?i. ty = TYPE_SUBST i ty`,
  GEN_TAC THEN EXISTS_TAC `[]:(hol_type#hol_type)list` THEN
  REWRITE_TAC[TYPE_SUBST_NIL]);;
let _ = cake_add_simps [is_instance_refl];;

let swap_ff = prove
 (`!(f:A->B) (g:C->D). (\(x,y). (y,x)) o (f ## g) = (g ## f) o (\(x,y). (y,x))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM]);;

let ff_def = prove
 (`!(f:A->B) (g:C->D). (f ## g) = \(x,y). (f x,g y)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM]);;

let TYPE_SUBST_compose = prove
 (`!tyin1 ty tyin2.
     TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
     TYPE_SUBST (APPEND (MAP (TYPE_SUBST tyin2 ## I) tyin1) tyin2) ty`,
  MATCH_MP_TAC TYPE_SUBST_ind THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[TYPE_SUBST_def] THEN
    SPEC_TAC(`i:(hol_type#hol_type)list`,`i:(hol_type#hol_type)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[TYPE_SUBST_def; REV_ASSOCD; APPEND; MAP] THEN
    PAIR_CASES_ON `h:hol_type#hol_type` THEN
    REWRITE_TAC[MAP; PAIR_MAP_THM; I_THM; APPEND; REV_ASSOCD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[TYPE_SUBST_def; MAP_MAP_o; o_DEF; MAP_EQ_f; injectivity "hol_type"] THEN
    SIMP_TAC[]]);;

let TYPE_SUBST_tyvars = prove
 (`!ty tyin tyin'.
     TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty <=>
     !x. MEM x (tyvars ty)
         ==> REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
             REV_ASSOCD (Tyvar x) tyin (Tyvar x)`,
  MATCH_MP_TAC type_ind THEN
  REWRITE_TAC[tyvars_def; TYPE_SUBST_def; injectivity "hol_type"; MEM; MAP_EQ_f;
              MEM_FOLDR_LIST_UNION; GSYM ALL_MEM] THEN
  CONJ_TAC THENL [MESON_TAC[]; REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MESON_TAC[]]);;

(* Welltyped terms *)

let WELLTYPED_LEMMA = prove
 (`!tm ty. tm has_type ty ==> typeof tm = ty`,
  MATCH_MP_TAC has_type_ind THEN SIMP[typeof_def; codomain_def]);;

let WELLTYPED = prove
 (`!tm. welltyped tm <=> tm has_type (typeof tm)`,
  SIMP[welltyped_def] THEN MESON_TAC[WELLTYPED_LEMMA]);;

let WELLTYPED_CLAUSES = prove
 (`(!n ty. welltyped (hol_Var n ty)) /\
   (!n ty. welltyped (hol_Const n ty)) /\
   (!s t. welltyped (hol_Comb s t) <=>
          welltyped s /\ welltyped t /\
          ?rty. typeof s = Tyapp (implode "fun") [typeof t; rty]) /\
   (!v t. welltyped (hol_Abs v t) <=> ?n ty. v = hol_Var n ty /\ welltyped t)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[welltyped_def] THEN
  SIMP[ONCE has_type_cases] THEN MESON_TAC[WELLTYPED; WELLTYPED_LEMMA; welltyped_def]);;
let _ = cake_add_simps [WELLTYPED_CLAUSES];;

(* Alpha-equivalence *)

let RACONV = prove
 (`(RACONV env (hol_Var x1 ty1,hol_Var x2 ty2) <=>
      ALPHAVARS env (hol_Var x1 ty1,hol_Var x2 ty2)) /\
   (RACONV env (hol_Var x1 ty1,hol_Const x2 ty2) <=> F) /\
   (RACONV env (hol_Var x1 ty1,hol_Comb l2 r2) <=> F) /\
   (RACONV env (hol_Var x1 ty1,hol_Abs v2 t2) <=> F) /\
   (RACONV env (hol_Const x1 ty1,hol_Var x2 ty2) <=> F) /\
   (RACONV env (hol_Const x1 ty1,hol_Const x2 ty2) <=> x1 = x2 /\ ty1 = ty2) /\
   (RACONV env (hol_Const x1 ty1,hol_Comb l2 r2) <=> F) /\
   (RACONV env (hol_Const x1 ty1,hol_Abs v2 t2) <=> F) /\
   (RACONV env (hol_Comb l1 r1,hol_Var x2 ty2) <=> F) /\
   (RACONV env (hol_Comb l1 r1,hol_Const x2 ty2) <=> F) /\
   (RACONV env (hol_Comb l1 r1,hol_Comb l2 r2) <=>
      RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (hol_Comb l1 r1,hol_Abs v2 t2) <=> F) /\
   (RACONV env (hol_Abs v1 t1,hol_Var x2 ty2) <=> F) /\
   (RACONV env (hol_Abs v1 t1,hol_Const x2 ty2) <=> F) /\
   (RACONV env (hol_Abs v1 t1,hol_Comb l2 r2) <=> F) /\
   (RACONV env (hol_Abs v1 t1,hol_Abs v2 t2) <=>
      typeof v1 = typeof v2 /\ RACONV (CONS (v1,v2) env) (t1,t2))`,
  REPEAT CONJ_TAC THEN SIMP[ONCE RACONV_cases] THEN MESON_TAC[]);;

let RACONV_REFL = prove
 (`!t env. ALL (UNCURRY (=)) env ==> RACONV env (t,t)`,
  MATCH_MP_TAC hol_term_INDUCT THEN SIMP[RACONV; ALPHAVARS_REFL; ALL; UNCURRY_DEF]);;

let ACONV_REFL = prove
 (`!t. ACONV t t`,
  SIMP[ACONV_def; RACONV_REFL; ALL]);;
let _ = cake_add_simps [ACONV_REFL];;

(* the Var case of RACONV_TRANS (HOL4: an induction inside its proof) *)
let CSYNAUX_P1_RACONV_TRANS_VAR = prove
 (`!env vs x1 ty1 x2 ty2 u.
     ALPHAVARS env (hol_Var x1 ty1,hol_Var x2 ty2) /\ LENGTH vs = LENGTH env /\
     RACONV (ZIP (MAP SND env) vs) (hol_Var x2 ty2,u)
     ==> RACONV (ZIP (MAP FST env) vs) (hol_Var x1 ty1,u)`,
  LIST_INDUCT_TAC THENL
   [SIMP[ALPHAVARS_def; LENGTH; LENGTH_EQ_NIL; MAP; ZIP] THEN MESON_TAC[]; ALL_TAC] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:hol_term list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP; HD; TL; NOT_CONS_NIL;
              ARITH_RULE `~(0 = SUC n)`] THEN
  REPEAT GEN_TAC THEN CASES_ON `u:hol_term` THEN
  REWRITE_TAC[RACONV; ALPHAVARS_def; PAIR_EQ; FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':hol_term list`; `x1:mlstring`; `ty1:hol_type`;
     `x2:mlstring`; `ty2:hol_type`; `hol_Var a0 a1`]) THEN
  REWRITE_TAC[RACONV] THEN MESON_TAC[]);;

let RACONV_TRANS = prove
 (`!env tp. RACONV env tp
            ==> !vs t. LENGTH vs = LENGTH env /\
                       RACONV (ZIP (MAP SND env) vs) (SND tp,t)
                       ==> RACONV (ZIP (MAP FST env) vs) (FST tp,t)`,
  MATCH_MP_TAC RACONV_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[CSYNAUX_P1_RACONV_TRANS_VAR];
    REPEAT GEN_TAC THEN CASES_ON `t:hol_term` THEN REWRITE_TAC[RACONV] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN CASES_ON `t:hol_term` THEN
    REWRITE_TAC[RACONV] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN CASES_ON `t:hol_term` THEN
    REWRITE_TAC[RACONV] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (a0:hol_term) vs`; `a1:hol_term`]) THEN
    ASM_REWRITE_TAC[LENGTH; MAP; ZIP; HD; TL] THEN ASM_MESON_TAC[]]);;

let ACONV_TRANS = prove
 (`!t1 t2 t3. ACONV t1 t2 /\ ACONV t2 t3 ==> ACONV t1 t3`,
  REWRITE_TAC[ACONV_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[]:(hol_term#hol_term)list`; `(t1:hol_term,t2:hol_term)`]
    RACONV_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`[]:hol_term list`; `t3:hol_term`]) THEN
  ASM_REWRITE_TAC[LENGTH; MAP; ZIP; FST; SND]);;

(* the Var case of RACONV_SYM *)
let CSYNAUX_P1_ALPHAVARS_SYM = prove
 (`!env (s:A) t. ALPHAVARS env (s,t) ==> ALPHAVARS (MAP (\(x,y). (y,x)) env) (t,s)`,
  MATCH_MP_TAC list_INDUCT THEN
  SIMP[FORALL_PAIR_THM; ALPHAVARS_def; MAP; PAIR_EQ] THEN MESON_TAC[]);;

let RACONV_SYM = prove
 (`!env tp. RACONV env tp
            ==> RACONV (MAP (\(x,y). (y,x)) env) (SND tp,FST tp)`,
  MATCH_MP_TAC RACONV_ind THEN SIMP[RACONV; MAP; CSYNAUX_P1_ALPHAVARS_SYM]);;

let ACONV_SYM = prove
 (`!t1 t2. ACONV t1 t2 ==> ACONV t2 t1`,
  REWRITE_TAC[ACONV_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RACONV_SYM) THEN REWRITE_TAC[MAP; FST; SND]);;

let ALPHAVARS_TYPE = prove
 (`!env s t.
     ALPHAVARS env (s,t) /\
     ALL (\(x,y). welltyped x /\ welltyped y /\ typeof x = typeof y) env /\
     welltyped s /\ welltyped t
     ==> typeof s = typeof t`,
  MATCH_MP_TAC list_INDUCT THEN
  SIMP[FORALL_PAIR_THM; ALPHAVARS_def; ALL; PAIR_EQ] THEN MESON_TAC[]);;

let RACONV_TYPE = prove
 (`!env p. RACONV env p
           ==> ALL (\(x,y). welltyped x /\ welltyped y /\ typeof x = typeof y) env /\
               welltyped (FST p) /\ welltyped (SND p)
               ==> typeof (FST p) = typeof (SND p)`,
  MATCH_MP_TAC RACONV_ind THEN SIMP[typeof_def; WELLTYPED_CLAUSES; ALL] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`env:(hol_term#hol_term)list`; `hol_Var x1 ty1`; `hol_Var x2 ty2`]
      ALPHAVARS_TYPE) THEN SIMP[WELLTYPED_CLAUSES; typeof_def];
    FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP[WELLTYPED_CLAUSES]]);;

let ACONV_TYPE = prove
 (`!s t. ACONV s t ==> welltyped s /\ welltyped t ==> typeof s = typeof t`,
  REWRITE_TAC[ACONV_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RACONV_TYPE) THEN ASM_REWRITE_TAC[ALL; FST; SND]);;

(* subtypes *)

let subtype1_rules,subtype1_ind,subtype1_cases,subtype1_strongind = cake_inductive
  `!a args name. MEM a args ==> subtype1 a (Tyapp name args)`;;

(* HOL4: Overload subtype = RTC subtype1 (infix) *)

let subtype_Tyvar = prove
 (`RTC subtype1 ty (Tyvar x) <=> ty = Tyvar x`,
  SIMP[ONCE RTC_CASES_L; subtype1_cases]);;
let _ = cake_add_simps [subtype_Tyvar];;

let subtype_Tyapp = prove
 (`RTC subtype1 ty (Tyapp name args) <=>
   ty = Tyapp name args \/ ?a. RTC subtype1 ty a /\ MEM a args`,
  SIMP[ONCE RTC_CASES_L; subtype1_cases] THEN MESON_TAC[]);;

let subtype_type_ok = prove
 (`!tysig ty1 ty2. type_ok tysig ty2 /\ RTC subtype1 ty1 ty2 ==> type_ok tysig ty1`,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[subtype1_cases] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[type_ok_def; GSYM ALL_MEM]);;

(* subterms *)

let subterm1_rules,subterm1_ind,subterm1_cases,subterm1_strongind = cake_inductive
  `(!t1 t2. subterm1 t1 (hol_Comb t1 t2)) /\
   (!t1 t2. subterm1 t2 (hol_Comb t1 t2)) /\
   (!tm v. subterm1 tm (hol_Abs v tm)) /\
   (!tm v. subterm1 v (hol_Abs v tm))`;;

(* HOL4: Overload subterm = RTC subterm1 (infix) *)

let subterm_Var = prove
 (`RTC subterm1 tm (hol_Var x ty) <=> tm = hol_Var x ty`,
  SIMP[ONCE RTC_CASES_L; subterm1_cases]);;
let _ = cake_add_simps [subterm_Var];;

let subterm_Const = prove
 (`RTC subterm1 tm (hol_Const x ty) <=> tm = hol_Const x ty`,
  SIMP[ONCE RTC_CASES_L; subterm1_cases]);;
let _ = cake_add_simps [subterm_Const];;

let subterm_Comb = prove
 (`RTC subterm1 tm (hol_Comb t1 t2) <=>
   tm = hol_Comb t1 t2 \/ RTC subterm1 tm t1 \/ RTC subterm1 tm t2`,
  SIMP[ONCE RTC_CASES_L; subterm1_cases] THEN MESON_TAC[]);;

let subterm_Abs = prove
 (`RTC subterm1 tm (hol_Abs v t) <=>
   tm = hol_Abs v t \/ RTC subterm1 tm t \/ RTC subterm1 tm v`,
  SIMP[ONCE RTC_CASES_L; subterm1_cases] THEN MESON_TAC[]);;

let subterm_welltyped_helper = prove
 (`!tm ty. tm has_type ty ==> !t. RTC subterm1 t tm ==> welltyped t`,
  MATCH_MP_TAC has_type_strongind THEN
  SIMP[subterm_Comb; subterm_Abs; subterm_Var; subterm_Const; WELLTYPED_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WELLTYPED_CLAUSES] THEN
  ASM_MESON_TAC[RTC_REFL; WELLTYPED_LEMMA]);;

let subterm_welltyped = prove
 (`!t tm. welltyped tm /\ RTC subterm1 t tm ==> welltyped t`,
  MESON_TAC[subterm_welltyped_helper; welltyped_def]);;
