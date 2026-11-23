(* ========================================================================= *)
(* holSyntaxExtra, part 4 of 8: HOL4 candle/standard/syntax/                 *)
(* holSyntaxExtraScript.sml lines 1641-2402 (CakeML v3479): equations,       *)
(* type_ok and term_ok, de Bruijn terms, and the respect of alpha-           *)
(* equivalence by VSUBST and INST.  Notes on the rendering: the header of    *)
(* holSyntaxExtra_p1.ml.  HOL4 bind and db are hol_bind and hol_db           *)
(* (names.tsv).  Local helpers that are not HOL4 theorems are CSYNAUX_P4_.   *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p3.ml";;

prioritize_num();;
type_invention_error := true;;

(* Equations *)

let EQUATION_HAS_TYPE_BOOL = prove
 (`!s t. (s === t) has_type (Tyapp (implode "bool") []) <=>
         welltyped s /\ welltyped t /\ typeof s = typeof t`,
  REWRITE_TAC[equation_def; CSYNAUX_P3_has_type_Comb; CSYNAUX_P3_has_type_Const;
              injectivity "hol_type"; CONS_11] THEN
  MESON_TAC[WELLTYPED_LEMMA; WELLTYPED]);;

let welltyped_equation = prove
 (`!s t. welltyped (s === t) <=> (s === t) has_type (Tyapp (implode "bool") [])`,
  REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN
  REWRITE_TAC[equation_def; WELLTYPED_CLAUSES; typeof_def; codomain_def;
              injectivity "hol_type"; CONS_11] THEN
  MESON_TAC[]);;

let typeof_equation = prove
 (`welltyped (l === r) ==> typeof (l === r) = Tyapp (implode "bool") []`,
  REWRITE_TAC[welltyped_equation] THEN MESON_TAC[WELLTYPED_LEMMA]);;

let vfree_in_equation = prove
 (`VFREE_IN v (s === t) <=>
   v = hol_Const (implode "=")
         (Tyapp (implode "fun") [typeof s;
            Tyapp (implode "fun") [typeof s; Tyapp (implode "bool") []]]) \/
   VFREE_IN v s \/ VFREE_IN v t`,
  REWRITE_TAC[equation_def; VFREE_IN_def] THEN MESON_TAC[]);;

let equation_intro = prove
 (`ty = typeof p
   ==> hol_Comb (hol_Comb (hol_Const (implode "=")
          (Tyapp (implode "fun") [ty;
             Tyapp (implode "fun") [ty; Tyapp (implode "bool") []]])) p) q =
       p === q`,
  SIMP_TAC[equation_def]);;

(* type_ok *)

let type_ok_TYPE_SUBST = prove
 (`!s tyin ty.
     type_ok s ty /\
     ALL (type_ok s) (MAP FST tyin)
     ==> type_ok s (TYPE_SUBST tyin ty)`,
  GEN_TAC THEN MATCH_MP_TAC TYPE_SUBST_ind THEN
  REWRITE_TAC[TYPE_SUBST_def; type_ok_def] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`i:(hol_type#hol_type)list`; `Tyvar v`; `Tyvar v`]
      REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[type_ok_def] THEN ASM_MESON_TAC[FST];
    REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_MAP; ALL_MAP] THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]]);;

let type_ok_TYPE_SUBST_imp = prove
 (`!s tyin ty. type_ok s (TYPE_SUBST tyin ty)
               ==> !x. MEM x (hol_tyvars ty) ==> type_ok s (TYPE_SUBST tyin (Tyvar x))`,
  GEN_TAC THEN MATCH_MP_TAC TYPE_SUBST_ind THEN
  REWRITE_TAC[hol_tyvars_def; MEM_FOLDR_LIST_UNION; MEM; type_ok_def;
              TYPE_SUBST_def] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[]);;

(* term_ok *)

let term_ok_welltyped = prove
 (`!sig t. hol_term_ok sig t ==> welltyped t`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[hol_term_ok_def; WELLTYPED_CLAUSES] THEN MESON_TAC[]);;

let term_ok_type_ok = prove
 (`!sig t. is_std_sig sig /\ hol_term_ok sig t
           ==> type_ok (FST sig) (typeof t)`,
  REWRITE_TAC[FORALL_PAIR_THM; is_std_sig_def] THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[hol_term_ok_def; typeof_def; WELLTYPED_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[codomain_def; typeof_def] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) then MP_TAC th else failwith "")) THEN
  ASM_REWRITE_TAC[type_ok_def; ALL; LENGTH; ARITH_RULE `SUC(SUC 0) = 2`;
                  typeof_def] THEN
  MESON_TAC[]);;

let term_ok_equation = prove
 (`is_std_sig sig
   ==> (hol_term_ok sig (s === t) <=>
        hol_term_ok sig s /\ hol_term_ok sig t /\
        typeof t = typeof s)`,
  STRIP_TAC THEN
  REWRITE_TAC[equation_def; hol_term_ok_def; WELLTYPED_CLAUSES; typeof_def;
              codomain_def; injectivity "hol_type"; CONS_11] THEN
  SIMP[] THEN EQ_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `type_ok (FST (sig:sig)) (typeof s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_type_ok]; ALL_TAC] THEN
  ASM_SIMP_TAC[term_ok_welltyped] THEN
  UNDISCH_TAC `is_std_sig (sig:sig)` THEN REWRITE_TAC[is_std_sig_def] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1; type_ok_def;
                  ALL; LENGTH] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `[(typeof s,Tyvar (implode "A"))]` THEN
  REWRITE_TAC[TYPE_SUBST_def; MAP; REV_ASSOCD]);;

let term_ok_clauses = prove
 (`is_std_sig sig
   ==> (hol_term_ok sig (hol_Var s ty) <=> type_ok (FST sig) ty) /\
       (type_ok (FST sig) (Tyvar a) <=> T) /\
       (type_ok (FST sig) (Tyapp (implode "bool") []) <=> T) /\
       (type_ok (FST sig) (Tyapp (implode "fun") [ty1; ty2]) <=>
          type_ok (FST sig) ty1 /\ type_ok (FST sig) ty2) /\
       (hol_term_ok sig (hol_Comb t1 t2) <=>
          hol_term_ok sig t1 /\ hol_term_ok sig t2 /\ welltyped (hol_Comb t1 t2)) /\
       (hol_term_ok sig (hol_Const (implode "=")
          (Tyapp (implode "fun") [ty;
             Tyapp (implode "fun") [ty; Tyapp (implode "bool") []]])) <=>
          type_ok (FST sig) ty) /\
       (hol_term_ok sig (t1 === t2) <=>
          hol_term_ok sig t1 /\ hol_term_ok sig t2 /\ typeof t1 = typeof t2) /\
       (hol_term_ok sig (hol_Abs (hol_Var s ty) t) <=>
          type_ok (FST sig) ty /\ hol_term_ok sig t)`,
  DISCH_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP term_ok_equation th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_std_sig_def]) THEN
  ASM_REWRITE_TAC[hol_term_ok_def; type_ok_def; ALL; LENGTH; option_INJ;
                  injectivity "hol_term"; UNWIND_THM1; RIGHT_EXISTS_AND_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `b ==> (a /\ b <=> a)`) THEN
    EXISTS_TAC `[(ty:hol_type,Tyvar (implode "A"))]` THEN
    REWRITE_TAC[TYPE_SUBST_def; MAP; REV_ASSOCD];
    MESON_TAC[];
    MESON_TAC[]]);;

let term_ok_VSUBST = prove
 (`!sig tm ilist.
     hol_term_ok sig tm /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s')
     ==> hol_term_ok sig (VSUBST ilist tm)`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[VSUBST_def] THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`;
                   `hol_Var a0 a1`] REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[VSUBST_def];
    REWRITE_TAC[VSUBST_def] THEN
    SUBGOAL_THEN `welltyped (VSUBST ilist (hol_Comb a0 a1))` MP_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN
      CONJ_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[VSUBST_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
    ASM_SIMP_TAC[hol_term_ok_def] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `hol_term_ok sig (hol_Abs a0 a1)` THEN
    REWRITE_TAC[hol_term_ok_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[VSUBST_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP[dest_var_def] THEN COND_CASES_TAC THEN
    SIMP[hol_term_ok_def; injectivity "hol_term"] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CSYNAUX_P3_has_type_Var; hol_term_ok_def; injectivity "hol_term"] THEN
    ASM_MESON_TAC[]]);;

let CSYNAUX_P4_INST_CORE_Abs_Var = prove
 (`!env tyin x ty t.
     INST_CORE env tyin (hol_Abs (hol_Var x ty) t) =
     let tres = INST_CORE (CONS (hol_Var x ty,hol_Var x (TYPE_SUBST tyin ty)) env)
                  tyin t in
     if IS_RESULT tres
     then hol_Result (hol_Abs (hol_Var x (TYPE_SUBST tyin ty)) (RESULT tres))
     else if ~(CLASH tres = hol_Var x (TYPE_SUBST tyin ty)) then tres
     else let x' = VARIANT (RESULT (INST_CORE [] tyin t)) (explode x)
                     (TYPE_SUBST tyin ty) in
          let tres' = INST_CORE (CONS (hol_Var x' ty,hol_Var x' (TYPE_SUBST tyin ty)) env)
                        tyin (VSUBST [hol_Var x' ty,hol_Var x ty] t) in
          if IS_RESULT tres'
          then hol_Result (hol_Abs (hol_Var x' (TYPE_SUBST tyin ty)) (RESULT tres'))
          else tres'`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [INST_CORE_def] THEN
  REWRITE_TAC[dest_var_def] THEN SIMP[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* the induction hypothesis of a proof by complete induction on n = sizeof tm,  *)
(* for the term tm and the environment env                                     *)
let CSYNAUX_P4_IH_TAC tm env =
  FIRST_ASSUM(fun ih -> MP_TAC(SPECL [tm; env]
    (MP (SPEC (mk_comb(`sizeof`,tm)) ih)
        (ASSUME (mk_binary "<" (mk_comb(`sizeof`,tm),`n:num`))))));;

let CSYNAUX_P4_term_ok_INST_CORE = prove
 (`!sig tyin n tm env.
     sizeof tm = n /\
     hol_term_ok sig tm /\
     ALL (type_ok (FST sig)) (MAP FST tyin) /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
     IS_RESULT (INST_CORE env tyin tm)
     ==> hol_term_ok sig (RESULT (INST_CORE env tyin tm))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `tm:hol_term` THEN
  STRUCT_CASES_TAC(ISPEC `tm:hol_term` (cases "hol_term")) THEN
  X_GEN_TAC `env:(hol_term#hol_term)list` THEN STRIP_TAC THENL
   [UNDISCH_TAC `IS_RESULT (INST_CORE env tyin (hol_Var a0 a1))` THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_RESULT_def; RESULT_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
    REWRITE_TAC[hol_term_ok_def] THEN ASM_MESON_TAC[type_ok_TYPE_SUBST];
    REWRITE_TAC[INST_CORE_def; RESULT_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
    REWRITE_TAC[hol_term_ok_def] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
    EXISTS_TAC `ty0:hol_type` THEN ASM_SIMP_TAC[type_ok_TYPE_SUBST] THEN
    ASM_REWRITE_TAC[TYPE_SUBST_compose] THEN MESON_TAC[];
    UNDISCH_TAC `IS_RESULT (INST_CORE env tyin (hol_Comb a0 a1))` THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `sizeof a0 < n /\ sizeof a1 < n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `sizeof (hol_Comb a0 a1) = n` THEN
      REWRITE_TAC[sizeof_def] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `hol_term_ok sig (hol_Comb a0 a1)` THEN
    REWRITE_TAC[hol_term_ok_def] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`sizeof a0`; `a0:hol_term`; `env:(hol_term#hol_term)list`;
                  `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
    MP_TAC(SPECL [`sizeof a1`; `a1:hol_term`; `env:(hol_term#hol_term)list`;
                  `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
    ASM_SIMP_TAC[term_ok_welltyped] THEN
    ABBREV_TAC `r0 = INST_CORE env tyin a0` THEN
    ABBREV_TAC `r1 = INST_CORE env tyin a1` THEN
    REPEAT STRIP_TAC THEN FS[IS_CLASH_def; IS_RESULT_def; RESULT_def; hol_term_ok_def] THEN
    SUBGOAL_THEN `typeof tm'' = TYPE_SUBST tyin (typeof a0) /\
                  typeof tm' = TYPE_SUBST tyin (typeof a1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WELLTYPED_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CSYNAUX_P4_IH_TAC `a0:hol_term` `env:(hol_term#hol_term)list` THEN
    CSYNAUX_P4_IH_TAC `a1:hol_term` `env:(hol_term#hol_term)list` THEN
    ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[TYPE_SUBST_def; MAP; injectivity "hol_type"; CONS_11] THEN
    REWRITE_TAC[welltyped_def] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `hol_term_ok sig (hol_Abs a0 a1)` THEN REWRITE_TAC[hol_term_ok_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `IS_RESULT (INST_CORE env tyin (hol_Abs (hol_Var x ty) a1))` THEN
    REWRITE_TAC[CSYNAUX_P4_INST_CORE_Abs_Var] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN
     `sizeof a1 < n /\
      sizeof (VSUBST [hol_Var (VARIANT (RESULT (INST_CORE [] tyin a1)) (explode x)
                       (TYPE_SUBST tyin ty)) ty,hol_Var x ty] a1) < n`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `sizeof (hol_Abs (hol_Var x ty) a1) = n` THEN
      REWRITE_TAC[sizeof_def; CSYNAUX_SIZEOF_VSUBST_VAR] THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `x' = VARIANT (RESULT (INST_CORE [] tyin a1)) (explode x)
                       (TYPE_SUBST tyin ty)` THEN
    ABBREV_TAC `tres = INST_CORE (CONS (hol_Var x ty,hol_Var x (TYPE_SUBST tyin ty)) env)
                         tyin a1` THEN
    ABBREV_TAC `tres' = INST_CORE (CONS (hol_Var x' ty,hol_Var x' (TYPE_SUBST tyin ty)) env)
                          tyin (VSUBST [hol_Var x' ty,hol_Var x ty] a1)` THEN
    SUBGOAL_THEN `type_ok (FST (sig:sig)) (TYPE_SUBST tyin ty)` ASSUME_TAC THENL
     [MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_RESULT_def; RESULT_def] THENL
     [ASM_REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN
      MAP_EVERY EXISTS_TAC [`x:mlstring`; `TYPE_SUBST tyin ty`] THEN
      ASM_REWRITE_TAC[] THEN
      CSYNAUX_P4_IH_TAC `a1:hol_term`
        `CONS (hol_Var x ty,hol_Var x (TYPE_SUBST tyin ty)) env` THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def] THEN
    ASM_REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN
    MAP_EVERY EXISTS_TAC [`x':mlstring`; `TYPE_SUBST tyin ty`] THEN
    ASM_REWRITE_TAC[] THEN
    CSYNAUX_P4_IH_TAC `VSUBST [hol_Var x' ty,hol_Var x ty] a1`
      `CONS (hol_Var x' ty,hol_Var x' (TYPE_SUBST tyin ty)) env` THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[injectivity "hol_term"; hol_term_ok_def;
                      CSYNAUX_P3_has_type_Var] THEN
      MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let term_ok_INST_CORE = prove
 (`!sig env tyin tm.
     hol_term_ok sig tm /\
     ALL (type_ok (FST sig)) (MAP FST tyin) /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
     IS_RESULT (INST_CORE env tyin tm)
     ==> hol_term_ok sig (RESULT (INST_CORE env tyin tm))`,
  MESON_TAC[CSYNAUX_P4_term_ok_INST_CORE]);;

let term_ok_INST = prove
 (`!sig tyin tm.
     hol_term_ok sig tm /\
     ALL (type_ok (FST sig)) (MAP FST tyin)
     ==> hol_term_ok sig (INST tyin tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  MATCH_MP_TAC term_ok_INST_CORE THEN
  ASM_SIMP_TAC[MEM; INST_CORE_NIL_IS_RESULT; term_ok_welltyped] THEN
  ASM_MESON_TAC[INST_CORE_NIL_IS_RESULT; term_ok_welltyped]);;

let term_ok_raconv = prove
 (`!env tp. RACONV env tp
            ==> !sig. ALL (\(s,s'). welltyped s /\ welltyped s' /\
                                    typeof s = typeof s' /\
                                    type_ok (FST sig) (typeof s)) env
                      ==> hol_term_ok sig (FST tp) /\ welltyped (SND tp)
                          ==> hol_term_ok sig (SND tp)`,
  MATCH_MP_TAC RACONV_strongind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP ALPHAVARS_MEM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(hol_Var x1 ty1,hol_Var x2 ty2)` o
                    REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
      ASM_REWRITE_TAC[hol_term_ok_def; typeof_def] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def; WELLTYPED_CLAUSES]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `sig:sig` o check (is_forall o concl))) THEN
    ASM_REWRITE_TAC[hol_term_ok_def; WELLTYPED_CLAUSES] THEN MESON_TAC[];
    UNDISCH_TAC `hol_term_ok sig (hol_Abs v1 t1)` THEN
    UNDISCH_TAC `welltyped (hol_Abs v2 t2)` THEN
    REWRITE_TAC[hol_term_ok_def; WELLTYPED_CLAUSES] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sig:sig` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[typeof_def]) THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def; injectivity "hol_term"] THEN
    SUBGOAL_THEN `ty':hol_type = ty` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `typeof v1 = typeof v2` THEN ASM_REWRITE_TAC[typeof_def];
      ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let term_ok_aconv = prove
 (`!sig t1 t2. ACONV t1 t2 /\ hol_term_ok sig t1 /\ welltyped t2
               ==> hol_term_ok sig t2`,
  REWRITE_TAC[ACONV_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[]:(hol_term#hol_term)list`; `(t1:hol_term,t2:hol_term)`]
    term_ok_raconv) THEN
  ASM_REWRITE_TAC[ALL; FST; SND] THEN ASM_MESON_TAC[]);;

let term_ok_VFREE_IN = prove
 (`!sig t x. VFREE_IN x t /\ hol_term_ok sig t ==> hol_term_ok sig x`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[VFREE_IN_def] THEN
  REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN
  ASM_REWRITE_TAC[hol_term_ok_def] THEN ASM_MESON_TAC[]);;

(* de Bruijn terms, for showing alpha-equivalence respect
   by substitution and instantiation *)

let dbterm_INDUCT,dbterm_RECURSION = cake_type
  "dbterm = dbVar mlstring hol_type
          | dbBound num
          | dbConst mlstring hol_type
          | dbComb dbterm dbterm
          | dbAbs hol_type dbterm";;

(* bind a variable above a de Bruijn term *)

(* HOL4: bind_def *)
let hol_bind_def = cake_def
  `(hol_bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) /\
   (hol_bind v n (dbBound m) = dbBound m) /\
   (hol_bind v n (dbConst x ty) = dbConst x ty) /\
   (hol_bind v n (dbComb t1 t2) = dbComb (hol_bind v n t1) (hol_bind v n t2)) /\
   (hol_bind v n (dbAbs ty tm) = dbAbs ty (hol_bind v (n + 1) tm))`;;
let _ = cake_add_simps [hol_bind_def];;

(* conversion into de Bruijn *)

(* HOL4: db_def *)
let hol_db_def = cake_def
  `(hol_db (hol_Var x ty) = dbVar x ty) /\
   (hol_db (hol_Const x ty) = dbConst x ty) /\
   (hol_db (hol_Comb t1 t2) = dbComb (hol_db t1) (hol_db t2)) /\
   (hol_db (hol_Abs v tm) = dbAbs (typeof v) (hol_bind (dest_var v) 0 (hol_db tm)))`;;
let _ = cake_add_simps [hol_db_def];;

(* de Bruijn versions of VSUBST and VFREE_IN *)

let dbVSUBST_def = cake_def
  `(dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty)) /\
   (dbVSUBST ilist (dbBound m) = dbBound m) /\
   (dbVSUBST ilist (dbConst x ty) = dbConst x ty) /\
   (dbVSUBST ilist (dbComb t1 t2) =
      dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2)) /\
   (dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t))`;;
let _ = cake_add_simps [dbVSUBST_def];;

let dbVFREE_IN_def = cake_def
  `(dbVFREE_IN v (dbVar x ty) <=> dbVar x ty = v) /\
   (dbVFREE_IN v (dbBound n) <=> F) /\
   (dbVFREE_IN v (dbConst x ty) <=> dbConst x ty = v) /\
   (dbVFREE_IN v (dbComb t1 t2) <=> dbVFREE_IN v t1 \/ dbVFREE_IN v t2) /\
   (dbVFREE_IN v (dbAbs ty t) <=> dbVFREE_IN v t)`;;
let _ = cake_add_simps [dbVFREE_IN_def];;

let bind_not_free = prove
 (`!t n v. ~dbVFREE_IN (UNCURRY dbVar v) t ==> hol_bind v n t = t`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; hol_bind_def; dbVFREE_IN_def; DE_MORGAN_THM;
              injectivity "dbterm"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* REV_ASSOCD returns the default when the key is not a second component *)
let CSYNAUX_P4_REV_ASSOCD_NOT_MEM = prove
 (`!(ls:(A#B)list) k d. ~MEM k (MAP SND ls) ==> REV_ASSOCD k ls d = d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ls:(A#B)list`; `k:B`; `d:A`] REV_ASSOCD_MEM) THEN
  UNDISCH_TAC `~MEM (k:B) (MAP SND (ls:(A#B)list))` THEN
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[SND]);;

let bind_dbVSUBST = prove
 (`!tm v n ls.
     ~(UNCURRY dbVar v IN set_of_list (MAP SND ls)) /\
     (!k. dbVFREE_IN k tm /\ MEM k (MAP SND ls)
          ==> ~dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
     ==> hol_bind v n (dbVSUBST ls tm) = dbVSUBST ls (hol_bind v n tm)`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbVSUBST_def; hol_bind_def; dbVFREE_IN_def; IN_SET_OF_LIST] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[UNCURRY_DEF]) THEN
      ASM_SIMP_TAC[CSYNAUX_P4_REV_ASSOCD_NOT_MEM; hol_bind_def; dbVSUBST_def];
      REWRITE_TAC[dbVSUBST_def] THEN
      ASM_CASES_TAC `MEM (dbVar a0 a1) (MAP SND (ls:(dbterm#dbterm)list))` THENL
       [MATCH_MP_TAC bind_not_free THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[CSYNAUX_P4_REV_ASSOCD_NOT_MEM; hol_bind_def]]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[injectivity "dbterm"] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[injectivity "dbterm"] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let bind_dbVSUBST_cons = prove
 (`!tm z x n ls.
     ~dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (hol_bind x n tm))
     ==> hol_bind z n (dbVSUBST (CONS (UNCURRY dbVar z,UNCURRY dbVar x) ls) tm) =
         dbVSUBST ls (hol_bind x n tm)`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbVSUBST_def; hol_bind_def; dbVFREE_IN_def; REV_ASSOCD] THEN
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; PAIR_EQ; injectivity "dbterm"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[dbVSUBST_def; hol_bind_def; PAIR_EQ] THEN
    REWRITE_TAC[dbVFREE_IN_def] THEN DISCH_TAC THEN MATCH_MP_TAC bind_not_free THEN
    ASM_REWRITE_TAC[UNCURRY_DEF];
    DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let dbVSUBST_frees = prove
 (`!tm ls ls'.
     (!k. dbVFREE_IN k tm ==> REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ==> dbVSUBST ls tm = dbVSUBST ls' tm`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbVSUBST_def; dbVFREE_IN_def; injectivity "dbterm"] THEN
  MESON_TAC[]);;

let dbVFREE_IN_bind = prove
 (`!tm x v n (b:A).
     dbVFREE_IN x (hol_bind v n tm) <=> ~(x = UNCURRY dbVar v) /\ dbVFREE_IN x tm`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; hol_bind_def; dbVFREE_IN_def] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[dbVFREE_IN_def; PAIR_EQ] THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o REWRITE_RULE[PAIR_EQ]) THEN
      MESON_TAC[];
      EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[injectivity "dbterm"] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[distinctness "dbterm"];
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

let CSYNAUX_P4_db_eq_dbVar = prove
 (`!x m t. hol_db x = dbVar m t <=> x = hol_Var m t`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[hol_db_def; distinctness "dbterm"; injectivity "dbterm";
              distinctness "hol_term"; injectivity "hol_term"]);;

let CSYNAUX_P4_db_eq_dbConst = prove
 (`!x m t. hol_db x = dbConst m t <=> x = hol_Const m t`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[hol_db_def; distinctness "dbterm"; injectivity "dbterm";
              distinctness "hol_term"; injectivity "hol_term"]);;

let dbVFREE_IN_VFREE_IN = prove
 (`!tm x. welltyped tm ==> (dbVFREE_IN (hol_db x) (hol_db tm) <=> VFREE_IN x tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[hol_db_def; dbVFREE_IN_def; VFREE_IN_def; WELLTYPED_CLAUSES] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MESON_TAC[CSYNAUX_P4_db_eq_dbVar];
    MESON_TAC[CSYNAUX_P4_db_eq_dbConst];
    STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[hol_db_def; dbVFREE_IN_def; dbVFREE_IN_bind; dest_var_def;
                 typeof_def; UNCURRY_DEF; CSYNAUX_P4_db_eq_dbVar] THEN
    MESON_TAC[]]);;

let MAP_db_FILTER_neq = prove
 (`!ls z ty.
     MAP (\(x,y). (hol_db x,hol_db y)) (FILTER (\(x,y). ~(y = hol_Var z ty)) ls) =
     FILTER (\(x,y). ~(y = dbVar z ty)) (MAP (\(x,y). (hol_db x,hol_db y)) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; FILTER] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[CSYNAUX_P4_db_eq_dbVar] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[]);;

let REV_ASSOCD_MAP_db = prove
 (`!ls k ky.
     (!k v. MEM (v,k) ls ==> ?x ty. k = hol_Var x ty)
     ==> REV_ASSOCD (dbVar k ky) (MAP (\(x,y). (hol_db x,hol_db y)) ls) (dbVar k ky) =
         hol_db (REV_ASSOCD (hol_Var k ky) ls (hol_Var k ky))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; REV_ASSOCD; hol_db_def] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; REV_ASSOCD; MEM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[REV_ASSOCD; CSYNAUX_P4_db_eq_dbVar] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let dbVFREE_IN_dbVSUBST = prove
 (`!tm u uty ilist.
     dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) <=>
     ?y ty. dbVFREE_IN (dbVar y ty) tm /\
            dbVFREE_IN (dbVar u uty) (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty))`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbVSUBST_def; dbVFREE_IN_def; distinctness "dbterm";
              injectivity "dbterm"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let CSYNAUX_P4_REV_ASSOCD_welltyped = prove
 (`!ilist y ty.
     (!k v. MEM (v,k) ilist ==> welltyped v)
     ==> welltyped (REV_ASSOCD (hol_Var y ty) ilist (hol_Var y ty))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var y ty`; `hol_Var y ty`]
    REV_ASSOCD_MEM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ASM_MESON_TAC[]);;

(* the substitution under a binder does not see the bound variable's pair *)
let CSYNAUX_P4_dbVSUBST_FILTER_bind = prove
 (`!ilist b bty n x.
     dbVSUBST (MAP (\(x,y). (hol_db x,hol_db y))
                 (FILTER (\(s',s). ~(s = hol_Var b bty)) ilist))
              (hol_bind (b,bty) n x) =
     dbVSUBST (MAP (\(x,y). (hol_db x,hol_db y)) ilist) (hol_bind (b,bty) n x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC dbVSUBST_frees THEN
  REWRITE_TAC[MAP_db_FILTER_neq; dbVFREE_IN_bind; UNCURRY_DEF] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`MAP (\(x,y). (hol_db x,hol_db y)) (ilist:(hol_term#hol_term)list)`;
     `k:dbterm`; `k:dbterm`; `T`]
    (INST [`\y:dbterm. ~(y = dbVar b bty)`,`P:dbterm->bool`]
       (INST_TYPE [`:dbterm`,`:A`; `:dbterm`,`:B`] REV_ASSOCD_FILTER)))) THEN
  ASM_REWRITE_TAC[]);;

let CSYNAUX_P4_MEM_SND_MAP_db = prove
 (`!il k. MEM k (MAP SND (MAP (\(x,y). (hol_db x,hol_db y)) il)) <=>
          ?s' s. MEM (s',s) il /\ k = hol_db s`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let VSUBST_dbVSUBST = prove
 (`!tm ilist.
     welltyped tm /\
     (!k v. MEM (v,k) ilist ==> welltyped v /\ ?x ty. k = hol_Var x ty)
     ==> hol_db (VSUBST ilist tm) =
         dbVSUBST (MAP (\(x,y). (hol_db x,hol_db y)) ilist) (hol_db tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[VSUBST_def; hol_db_def; dbVSUBST_def] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REV_ASSOCD_MAP_db THEN ASM_MESON_TAC[];
    REWRITE_TAC[VSUBST_def; hol_db_def; dbVSUBST_def];
    RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
    ASM_SIMP_TAC[VSUBST_def; hol_db_def; dbVSUBST_def];
    ALL_TAC] THEN
  UNDISCH_TAC `welltyped (hol_Abs a0 a1)` THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:mlstring` (X_CHOOSE_THEN `bty:hol_type`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[VSUBST_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[dest_var_def] THEN SIMP[] THEN
  REWRITE_TAC[hol_db_def; dbVSUBST_def; typeof_def; dest_var_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CSYNAUX_P4_dbVSUBST_FILTER_bind] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) (FILTER (\(s',s). ~(s = hol_Var b bty)) ilist)
                      ==> welltyped v /\ ?x ty. k = hol_Var x ty` ASSUME_TAC THENL
   [REWRITE_TAC[MEM_FILTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `il' = FILTER (\(s',s). ~(s = hol_Var b bty))
                      (ilist:(hol_term#hol_term)list)` THEN
  COND_CASES_TAC THENL
   [(* a variable of the substituted terms is captured: rename *)
    ABBREV_TAC `V = VARIANT (VSUBST (il':(hol_term#hol_term)list) a1) (explode b) bty` THEN
    REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; injectivity "dbterm"] THEN
    SUBGOAL_THEN `hol_db (VSUBST (CONS (hol_Var V bty,hol_Var b bty) il') a1) =
                  dbVSUBST (MAP (\(x,y). hol_db x,hol_db y)
                    (CONS (hol_Var V bty,hol_Var b bty) il')) (hol_db a1)`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[hol_db_def] THEN
    MATCH_MP_TAC(REWRITE_RULE[UNCURRY_DEF] (ISPECL
      [`hol_db a1`; `(V:mlstring,bty:hol_type)`; `(b:mlstring,bty:hol_type)`; `0`;
       `MAP (\(x,y). hol_db x,hol_db y) (il':(hol_term#hol_term)list)`]
      bind_dbVSUBST_cons)) THEN
    REWRITE_TAC[dbVFREE_IN_dbVSUBST; dbVFREE_IN_bind; UNCURRY_DEF; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:mlstring`; `ty:hol_type`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var y ty) a1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`a1:hol_term`; `hol_Var y ty`] dbVFREE_IN_VFREE_IN) THEN
      ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
    SUBGOAL_THEN `REV_ASSOCD (dbVar y ty) (MAP (\(x,y). hol_db x,hol_db y) il')
                    (dbVar y ty) =
                  hol_db (REV_ASSOCD (hol_Var y ty) il' (hol_Var y ty))`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC REV_ASSOCD_MAP_db THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `welltyped (REV_ASSOCD (hol_Var y ty) il' (hol_Var y ty))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC CSYNAUX_P4_REV_ASSOCD_welltyped THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var V bty) (REV_ASSOCD (hol_Var y ty) il' (hol_Var y ty))`
      ASSUME_TAC THENL
     [MP_TAC(SPECL [`REV_ASSOCD (hol_Var y ty) il' (hol_Var y ty)`; `hol_Var V bty`]
        dbVFREE_IN_VFREE_IN) THEN ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
    MP_TAC(SPECL [`VSUBST il' a1`; `explode b`; `bty:hol_type`] VARIANT_THM) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[VFREE_IN_VSUBST] THEN ASM_MESON_TAC[];
    (* no capture *)
    REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; injectivity "dbterm"] THEN
    SUBGOAL_THEN `hol_db (VSUBST il' a1) =
                  dbVSUBST (MAP (\(x,y). hol_db x,hol_db y) il') (hol_db a1)`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC bind_dbVSUBST THEN REWRITE_TAC[UNCURRY_DEF; IN_SET_OF_LIST] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "il'" THEN
      REWRITE_TAC[CSYNAUX_P4_MEM_SND_MAP_db; MEM_FILTER] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[CSYNAUX_P4_db_eq_dbVar];
      ALL_TAC] THEN
    REWRITE_TAC[CSYNAUX_P4_MEM_SND_MAP_db] THEN X_GEN_TAC `k:dbterm` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP (ASSUME
      `!k v. MEM (v,k) il' ==> welltyped v /\ (?x ty. k = hol_Var x ty)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `ty:hol_type` SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[hol_db_def]) THEN
    REWRITE_TAC[hol_db_def] THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var x ty) a1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`a1:hol_term`; `hol_Var x ty`] dbVFREE_IN_VFREE_IN) THEN
      ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
    SUBGOAL_THEN `REV_ASSOCD (dbVar x ty)
                    (MAP (\(x,y). hol_db x,hol_db y) (il':(hol_term#hol_term)list))
                    (dbVar x ty) =
                  hol_db (REV_ASSOCD (hol_Var x ty) il' (hol_Var x ty))` SUBST1_TAC THENL
     [MATCH_MP_TAC REV_ASSOCD_MAP_db THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `welltyped (REV_ASSOCD (hol_Var x ty) (il':(hol_term#hol_term)list)
                    (hol_Var x ty))` ASSUME_TAC THENL
     [MATCH_MP_TAC CSYNAUX_P4_REV_ASSOCD_welltyped THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(CONJUNCT1 hol_db_def)] THEN ASM_SIMP_TAC[dbVFREE_IN_VFREE_IN] THEN
    MP_TAC(ISPECL [`il':(hol_term#hol_term)list`; `hol_Var x ty`; `hol_Var x ty`]
      REV_ASSOCD_MEM) THEN STRIP_TAC THENL
     [UNDISCH_TAC `~EX (\(s',s). VFREE_IN (hol_Var b bty) s' /\ VFREE_IN s a1)
                       (il':(hol_term#hol_term)list)` THEN
      REWRITE_TAC[NOT_EX; GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `(REV_ASSOCD (hol_Var x ty) (il':(hol_term#hol_term)list)
                                   (hol_Var x ty),hol_Var x ty)`) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[VFREE_IN_def] THEN
      UNDISCH_TAC `MEM (s':hol_term,hol_Var x ty) (il':(hol_term#hol_term)list)` THEN
      EXPAND_TAC "il'" THEN
      REWRITE_TAC[MEM_FILTER] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      MESON_TAC[]]]);;

(* de Bruijn version of INST *)

let dbINST_def = cake_def
  `(dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty)) /\
   (dbINST tyin (dbBound n) = dbBound n) /\
   (dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty)) /\
   (dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2)) /\
   (dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t))`;;
let _ = cake_add_simps [dbINST_def];;

let dbINST_bind = prove
 (`!tm v n ls.
     (!ty. dbVFREE_IN (dbVar (FST v) ty) tm /\
           TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)
           ==> ty = SND v)
     ==> dbINST ls (hol_bind v n tm) =
         hol_bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm)`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; hol_bind_def; dbINST_def; dbVFREE_IN_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[injectivity "dbterm"; PAIR_EQ] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[dbINST_def; hol_bind_def; PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[dbINST_def; hol_bind_def; injectivity "dbterm"] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[dbINST_def; hol_bind_def; injectivity "dbterm"] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let dbVSUBST_nil = prove
 (`!tm. dbVSUBST [] tm = tm`,
  MATCH_MP_TAC dbterm_INDUCT THEN ASM_SIMP_TAC[dbVSUBST_def; REV_ASSOCD]);;
let _ = cake_add_simps [dbVSUBST_nil];;

let CSYNAUX_P4_INST_CORE_dbINST = prove
 (`!tyin n tm env tmi.
     sizeof tm = n /\
     welltyped tm /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
     INST_CORE env tyin tm = hol_Result tmi
     ==> hol_db tmi = dbINST tyin (hol_db tm)`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `tm:hol_term` THEN
  STRUCT_CASES_TAC(ISPEC `tm:hol_term` (cases "hol_term")) THEN
  MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`; `tmi:hol_term`] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `INST_CORE env tyin (hol_Var a0 a1) = hol_Result tmi` THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "hol_result"; injectivity "hol_result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[hol_db_def; dbINST_def];
    UNDISCH_TAC `INST_CORE env tyin (hol_Const a0 a1) = hol_Result tmi` THEN
    REWRITE_TAC[INST_CORE_def; injectivity "hol_result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[hol_db_def; dbINST_def];
    UNDISCH_TAC `INST_CORE env tyin (hol_Comb a0 a1) = hol_Result tmi` THEN
    REWRITE_TAC[INST_CORE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `sizeof a0 < n /\ sizeof a1 < n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `sizeof (hol_Comb a0 a1) = n` THEN
      REWRITE_TAC[sizeof_def] THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
    DISJ_CASES_THEN2 (X_CHOOSE_TAC `c0:hol_term`) (X_CHOOSE_TAC `r0:hol_term`)
      (ISPEC `INST_CORE env tyin a0` (cases "hol_result")) THEN
    ASM_REWRITE_TAC[IS_CLASH_def; distinctness "hol_result"] THEN
    DISJ_CASES_THEN2 (X_CHOOSE_TAC `c1:hol_term`) (X_CHOOSE_TAC `r1:hol_term`)
      (ISPEC `INST_CORE env tyin a1` (cases "hol_result")) THEN
    ASM_REWRITE_TAC[IS_CLASH_def; distinctness "hol_result"; RESULT_def;
                    injectivity "hol_result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[hol_db_def; dbINST_def; injectivity "dbterm"] THEN CONJ_TAC THENL
     [CSYNAUX_P4_IH_TAC `a0:hol_term` `env:(hol_term#hol_term)list` THEN
      DISCH_THEN(MP_TAC o SPEC `r0:hol_term`) THEN ASM_REWRITE_TAC[];
      CSYNAUX_P4_IH_TAC `a1:hol_term` `env:(hol_term#hol_term)list` THEN
      DISCH_THEN(MP_TAC o SPEC `r1:hol_term`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `welltyped (hol_Abs a0 a1)` THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:mlstring` (X_CHOOSE_THEN `bty:hol_type`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `sizeof a1 < n /\
    sizeof (VSUBST [hol_Var (VARIANT (RESULT (INST_CORE [] tyin a1)) (explode b)
                     (TYPE_SUBST tyin bty)) bty,hol_Var b bty] a1) < n`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sizeof (hol_Abs (hol_Var b bty) a1) = n` THEN
    REWRITE_TAC[sizeof_def; CSYNAUX_SIZEOF_VSUBST_VAR] THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `INST_CORE env tyin (hol_Abs (hol_Var b bty) a1) = hol_Result tmi` THEN
  REWRITE_TAC[CSYNAUX_P4_INST_CORE_Abs_Var] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[hol_db_def; dest_var_def; typeof_def; dbINST_def] THEN
  ABBREV_TAC `x' = VARIANT (RESULT (INST_CORE [] tyin a1)) (explode b)
                     (TYPE_SUBST tyin bty)` THEN
  ABBREV_TAC `tres = INST_CORE (CONS (hol_Var b bty,hol_Var b (TYPE_SUBST tyin bty)) env)
                       tyin a1` THEN
  ABBREV_TAC `tres' = INST_CORE (CONS (hol_Var x' bty,hol_Var x' (TYPE_SUBST tyin bty)) env)
                        tyin (VSUBST [hol_Var x' bty,hol_Var b bty] a1)` THEN
  COND_CASES_TAC THENL
   [(* the body instantiates without a clash *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `tt:hol_term` SUBST_ALL_TAC o
                  MATCH_MP IS_RESULT_IMP_Result) THEN
    REWRITE_TAC[RESULT_def; injectivity "hol_result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[hol_db_def; dest_var_def; typeof_def; injectivity "dbterm"] THEN
    SUBGOAL_THEN `hol_db tt = dbINST tyin (hol_db a1)` SUBST1_TAC THENL
     [CSYNAUX_P4_IH_TAC `a1:hol_term`
        `CONS (hol_Var b bty,hol_Var b (TYPE_SUBST tyin bty)) env` THEN
      DISCH_THEN(MP_TAC o SPEC `tt:hol_term`) THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hol_db a1`; `(b:mlstring,bty:hol_type)`; `0`;
                   `tyin:(hol_type#hol_type)list`] dbINST_bind) THEN
    REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
     [X_GEN_TAC `ty2:hol_type` THEN STRIP_TAC THEN
      SUBGOAL_THEN `VFREE_IN (hol_Var b ty2) a1` ASSUME_TAC THENL
       [MP_TAC(SPECL [`a1:hol_term`; `hol_Var b ty2`] dbVFREE_IN_VFREE_IN) THEN
        ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
      MP_TAC(SPECL [`sizeof a1`; `a1:hol_term`;
                    `CONS (hol_Var b bty,hol_Var b (TYPE_SUBST tyin bty)) env`;
                    `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ; distinctness "hol_result"] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`b:mlstring`; `ty2:hol_type`] o CONJUNCT1) THEN
      ASM_REWRITE_TAC[REV_ASSOCD; injectivity "hol_term"] THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~IS_RESULT (tres:(hol_term)hol_result)` THEN
    ASM_REWRITE_TAC[IS_RESULT_def];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN UNDISCH_TAC `~IS_RESULT (tres':(hol_term)hol_result)` THEN
    ASM_REWRITE_TAC[IS_RESULT_def]] THEN
  (* the bound variable is renamed to x' *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `tt:hol_term` SUBST_ALL_TAC o
                MATCH_MP IS_RESULT_IMP_Result) THEN
  REWRITE_TAC[RESULT_def; injectivity "hol_result"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[hol_db_def; dest_var_def; typeof_def; injectivity "dbterm"] THEN
  SUBGOAL_THEN `hol_bind (b,bty) 0 (hol_db a1) =
                hol_bind (x',bty) 0 (dbVSUBST [(dbVar x' bty,dbVar b bty)] (hol_db a1))`
    SUBST1_TAC THENL
   [MP_TAC(REWRITE_RULE[UNCURRY_DEF; dbVSUBST_nil] (ISPECL
      [`hol_db a1`; `(x':mlstring,bty:hol_type)`; `(b:mlstring,bty:hol_type)`; `0`;
       `[]:(dbterm#dbterm)list`] bind_dbVSUBST_cons)) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC] THEN
    REWRITE_TAC[dbVFREE_IN_bind; UNCURRY_DEF; DE_MORGAN_THM] THEN DISJ2_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var x' bty) a1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`a1:hol_term`; `hol_Var x' bty`] dbVFREE_IN_VFREE_IN) THEN
      ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
    MP_TAC(SPECL [`tyin:(hol_type#hol_type)list`; `a1:hol_term`]
      INST_CORE_NIL_IS_RESULT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `tm0:hol_term` o MATCH_MP IS_RESULT_IMP_Result) THEN
    MP_TAC(SPECL [`sizeof a1`; `a1:hol_term`; `[]:(hol_term#hol_term)list`;
                  `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
    ASM_REWRITE_TAC[MEM; distinctness "hol_result"; injectivity "hol_result";
                    UNWIND_THM1] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var x' (TYPE_SUBST tyin bty)) tm0` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `VARIANT (RESULT (INST_CORE [] tyin a1)) (explode b)
                   (TYPE_SUBST tyin bty) = x'` THEN
    REWRITE_TAC[ASSUME `INST_CORE [] tyin a1 = hol_Result tm0`; RESULT_def] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VARIANT_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:hol_term`; `[hol_Var x' bty,hol_Var b bty]`] VSUBST_dbVSUBST) THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ; MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[hol_db_def] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ABBREV_TAC `tv = VSUBST [hol_Var x' bty,hol_Var b bty] a1` THEN
  SUBGOAL_THEN `welltyped tv` ASSUME_TAC THENL
   [EXPAND_TAC "tv" THEN MATCH_MP_TAC VSUBST_WELLTYPED THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[CSYNAUX_P3_has_type_Var] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hol_db tv`; `(x':mlstring,bty:hol_type)`; `0`;
                 `tyin:(hol_type#hol_type)list`] dbINST_bind) THEN
  REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [X_GEN_TAC `ty2:hol_type` THEN STRIP_TAC THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var x' ty2) tv` ASSUME_TAC THENL
     [MP_TAC(SPECL [`tv:hol_term`; `hol_Var x' ty2`] dbVFREE_IN_VFREE_IN) THEN
      ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
    MP_TAC(SPECL [`sizeof tv`; `tv:hol_term`;
                  `CONS (hol_Var x' bty,hol_Var x' (TYPE_SUBST tyin bty)) env`;
                  `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ; distinctness "hol_result"] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x':mlstring`; `ty2:hol_type`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[REV_ASSOCD; injectivity "hol_term"] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  CSYNAUX_P4_IH_TAC `tv:hol_term`
    `CONS (hol_Var x' bty,hol_Var x' (TYPE_SUBST tyin bty)) env` THEN
  DISCH_THEN(MP_TAC o SPEC `tt:hol_term`) THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let INST_CORE_dbINST = prove
 (`!tm tyin env tmi.
     welltyped tm /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
     INST_CORE env tyin tm = hol_Result tmi
     ==> hol_db tmi = dbINST tyin (hol_db tm)`,
  MESON_TAC[CSYNAUX_P4_INST_CORE_dbINST]);;

let INST_dbINST = prove
 (`!tm tyin. welltyped tm ==> hol_db (INST tyin tm) = dbINST tyin (hol_db tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  MP_TAC(SPECL [`tyin:(hol_type#hol_type)list`; `tm:hol_term`]
    INST_CORE_NIL_IS_RESULT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r:hol_term` o MATCH_MP IS_RESULT_IMP_Result) THEN
  ASM_REWRITE_TAC[RESULT_def] THEN MATCH_MP_TAC INST_CORE_dbINST THEN
  EXISTS_TAC `[]:(hol_term#hol_term)list` THEN ASM_REWRITE_TAC[MEM]);;

(* conversion into de Bruijn given an environment of already bound variables *)

let dbterm_def = cake_def
  `(dbterm env (hol_Var s ty) =
      match find_index (s,ty) env 0 with SOME n -> dbBound n | NONE -> dbVar s ty) /\
   (dbterm env (hol_Const s ty) = dbConst s ty) /\
   (dbterm env (hol_Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) /\
   (dbterm env (hol_Abs v t) = dbAbs (typeof v) (dbterm (CONS (dest_var v) env) t))`;;
let _ = cake_add_simps [dbterm_def];;

let bind_list_aux_def = cake_def
  `(bind_list_aux n [] tm = tm) /\
   (bind_list_aux n (CONS v vs) tm = bind_list_aux (n + 1) vs (hol_bind v n tm))`;;
let _ = cake_add_simps [bind_list_aux_def];;

let bind_list_aux_clauses = prove
 (`(!env m. bind_list_aux m env (dbBound n) = dbBound n) /\
   (!env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) /\
   (!env m t1 t2.
      bind_list_aux m env (dbComb t1 t2) =
      dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) /\
   (!env m ty tm.
      bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m + 1) env tm))`,
  REPEAT CONJ_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[bind_list_aux_def; hol_bind_def]);;

let CSYNAUX_P4_dbterm_Var = prove
 (CASE_TERM
  `!env s ty n.
     (match find_index (s,ty) env n with SOME k -> dbBound k | NONE -> dbVar s ty) =
     bind_list_aux n env (dbVar s ty)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; bind_list_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN REWRITE_TAC[hol_bind_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bind_list_aux_clauses] THEN
  CASE_REWRITE_TAC[]);;

let dbterm_bind = prove
 (`!tm env. dbterm env tm = bind_list_aux 0 env (hol_db tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  ASM_REWRITE_TAC[dbterm_def; hol_db_def; bind_list_aux_clauses; bind_list_aux_def;
                  CSYNAUX_P4_dbterm_Var] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bind_list_aux_def; ADD_CLAUSES]);;

let dbterm_db = prove
 (`!tm. dbterm [] tm = hol_db tm`,
  REWRITE_TAC[dbterm_bind; bind_list_aux_def]);;

(* alpha-equivalence on de Bruijn terms *)

let CSYNAUX_P4_find_index_SUC_ne = prove
 (`!l (x:A) n k. find_index x l (n + 1) = SOME k ==> ~(k = n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP find_index_shift) THEN
  ARITH_TAC);;

let CSYNAUX_P4_dbterm_RACONV_Var = prove
 (CASE_TERM
  `!env1 env2 n x1 ty1 x2 ty2.
     LENGTH env1 = LENGTH env2 /\
     (match find_index (x1,ty1) env1 n with SOME k -> dbBound k | NONE -> dbVar x1 ty1) =
     (match find_index (x2,ty2) env2 n with SOME k -> dbBound k | NONE -> dbVar x2 ty2)
     ==> ALPHAVARS (ZIP (MAP (UNCURRY hol_Var) env1) (MAP (UNCURRY hol_Var) env2))
                   (hol_Var x1 ty1,hol_Var x2 ty2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; find_index_def; MAP; ZIP;
              ALPHAVARS_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "dbterm"; injectivity "hol_term"; PAIR_EQ] THEN
  PAIR_CASES_ON `h:mlstring#hol_type` THEN PAIR_CASES_ON `h':mlstring#hol_type` THEN
  REWRITE_TAC[UNCURRY_DEF; PAIR_EQ; injectivity "hol_term"] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `h0:mlstring = x1 /\ h1:hol_type = ty1` THEN
  ASM_CASES_TAC `h'0:mlstring = x2 /\ h'1:hol_type = ty2` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `k:num` (fun th ->
      ASSUME_TAC th THEN SUBST1_TAC th))
      (ISPEC `find_index (x2:mlstring,ty2:hol_type) t' (n + 1)` (cases "option")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "dbterm"; injectivity "dbterm"] THEN
    ASM_MESON_TAC[CSYNAUX_P4_find_index_SUC_ne];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `k:num` (fun th ->
      ASSUME_TAC th THEN SUBST1_TAC th))
      (ISPEC `find_index (x1:mlstring,ty1:hol_type) t (n + 1)` (cases "option")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "dbterm"; injectivity "dbterm"] THEN
    ASM_MESON_TAC[CSYNAUX_P4_find_index_SUC_ne];
    STRIP_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `n + 1` THEN ASM_REWRITE_TAC[]]);;

(* the de Bruijn translation of a variable is a bound index or the variable *)
let CSYNAUX_P4_dbterm_Var_cases = prove
 (`!env s ty. (?k. dbterm env (hol_Var s ty) = dbBound k) \/
              dbterm env (hol_Var s ty) = dbVar s ty`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dbterm_def] THEN
  STRUCT_CASES_TAC(ISPEC `find_index (s:mlstring,ty:hol_type) env 0` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let dbterm_RACONV = prove
 (`!t1 env1 t2 env2.
     welltyped t1 /\ welltyped t2 /\ dbterm env1 t1 = dbterm env2 t2 /\
     LENGTH env1 = LENGTH env2
     ==> RACONV (ZIP (MAP (UNCURRY hol_Var) env1) (MAP (UNCURRY hol_Var) env2))
                (t1,t2)`,
  let VL_TAC = MP_TAC(SPECL [`env1:(mlstring#hol_type)list`; `a0:mlstring`;
                             `a1:hol_type`] CSYNAUX_P4_dbterm_Var_cases) THEN
               STRIP_TAC THEN ASM_REWRITE_TAC[dbterm_def; distinctness "dbterm"]
  and VR_TAC = MP_TAC(SPECL [`env2:(mlstring#hol_type)list`; `a0':mlstring`;
                             `a1':hol_type`] CSYNAUX_P4_dbterm_Var_cases) THEN
               STRIP_TAC THEN ASM_REWRITE_TAC[dbterm_def; distinctness "dbterm"]
  and D_TAC = REWRITE_TAC[dbterm_def; distinctness "dbterm"] in
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t2:hol_term` (cases "hol_term")) THENL
     [REWRITE_TAC[dbterm_def; RACONV] THEN STRIP_TAC THEN
      MATCH_MP_TAC CSYNAUX_P4_dbterm_RACONV_Var THEN EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC[];
      VL_TAC; VL_TAC; VL_TAC];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t2:hol_term` (cases "hol_term")) THENL
     [VR_TAC;
      REWRITE_TAC[dbterm_def; RACONV; injectivity "dbterm"] THEN MESON_TAC[];
      D_TAC; D_TAC];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `t2:hol_term` (cases "hol_term")) THENL
     [VR_TAC; D_TAC;
      REWRITE_TAC[dbterm_def; RACONV; injectivity "dbterm"; WELLTYPED_CLAUSES] THEN
      STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      D_TAC];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `t2:hol_term` (cases "hol_term")) THENL
     [VR_TAC; D_TAC; D_TAC;
      REWRITE_TAC[dbterm_def; RACONV; injectivity "dbterm"; WELLTYPED_CLAUSES] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`CONS (dest_var a0) env1:(mlstring#hol_type)list`; `a1':hol_term`;
         `CONS (dest_var a0') env2:(mlstring#hol_type)list`]) THEN
      ASM_REWRITE_TAC[LENGTH; MAP; ZIP; dest_var_def; UNCURRY_DEF]]]);;

let CSYNAUX_P4_RACONV_dbterm_Var = prove
 (CASE_TERM
  `!env n x1 ty1 x2 ty2.
     ALPHAVARS env (hol_Var x1 ty1,hol_Var x2 ty2) /\
     (!vp. MEM vp env ==> (?x ty. FST vp = hol_Var x ty) /\ (?x ty. SND vp = hol_Var x ty))
     ==> (match find_index (x1,ty1) (MAP (dest_var o FST) env) n with
            SOME k -> dbBound k | NONE -> dbVar x1 ty1) =
         (match find_index (x2,ty2) (MAP (dest_var o SND) env) n with
            SOME k -> dbBound k | NONE -> dbVar x2 ty2)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALPHAVARS_def; MAP; find_index_def; MEM; o_THM] THEN
  CASE_REWRITE_TAC[] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(h0:hol_term,h1:hol_term)`) THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:mlstring` (X_CHOOSE_TAC `b:hol_type`))
                             (X_CHOOSE_THEN `c:mlstring` (X_CHOOSE_TAC `d:hol_type`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; FST; SND]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let l,r = dest_eq(concl th) in is_var l && mem (fst(dest_var l)) ["h0";"h1"]))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
  ASM_REWRITE_TAC[dest_var_def; PAIR_EQ] THENL
   [CASE_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `vp:hol_term#hol_term` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vp:hol_term#hol_term`) THEN ASM_REWRITE_TAC[]]);;

let RACONV_dbterm = prove
 (`!env tp. RACONV env tp
            ==> welltyped (FST tp) /\ welltyped (SND tp) /\
                (!vp. MEM vp env
                      ==> (?x ty. FST vp = hol_Var x ty) /\
                          (?x ty. SND vp = hol_Var x ty))
                ==> dbterm (MAP (dest_var o FST) env) (FST tp) =
                    dbterm (MAP (dest_var o SND) env) (SND tp)`,
  MATCH_MP_TAC RACONV_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[dbterm_def] THEN
    MATCH_MP_TAC CSYNAUX_P4_RACONV_dbterm_Var THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[dbterm_def];
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
    REWRITE_TAC[dbterm_def; injectivity "dbterm"] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN DISCH_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[typeof_def]) THEN
    REWRITE_TAC[dbterm_def; injectivity "dbterm"; typeof_def] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[MAP; o_THM; FST; SND; MEM; dest_var_def] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `vp:hol_term#hol_term` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[]; ASM_MESON_TAC[]]]);;

let dbterm_ACONV = prove
 (`!t1 t2. welltyped t1 /\ welltyped t2
           ==> (ACONV t1 t2 <=> dbterm [] t1 = dbterm [] t2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ACONV_def] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`[]:(hol_term#hol_term)list`; `(t1:hol_term,t2:hol_term)`]
      RACONV_dbterm) THEN
    ASM_REWRITE_TAC[MEM; MAP; FST; SND];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t1:hol_term`; `[]:(mlstring#hol_type)list`; `t2:hol_term`;
                   `[]:(mlstring#hol_type)list`] dbterm_RACONV) THEN
    ASM_REWRITE_TAC[MAP; ZIP]]);;

let ACONV_db = prove
 (`!t1 t2. welltyped t1 /\ welltyped t2 ==> (ACONV t1 t2 <=> hol_db t1 = hol_db t2)`,
  SIMP_TAC[dbterm_ACONV; dbterm_db]);;

(* respect of alpha-equivalence by VSUBST and INST follows *)

let ACONV_VSUBST = prove
 (`!t1 t2 ilist.
     welltyped t1 /\ welltyped t2 /\
     (!k v. MEM (v,k) ilist ==> ?x ty. k = hol_Var x ty /\ v has_type ty) /\
     ACONV t1 t2
     ==> ACONV (VSUBST ilist t1) (VSUBST ilist t2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k v. MEM (v,k) ilist ==> welltyped v /\ ?x ty. k = hol_Var x ty`
    ASSUME_TAC THENL [ASM_MESON_TAC[welltyped_def]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST ilist t1) /\ welltyped (VSUBST ilist t2)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ACONV_db; VSUBST_dbVSUBST] THEN ASM_MESON_TAC[ACONV_db]);;

let ACONV_INST = prove
 (`!t1 t2 tyin. welltyped t1 /\ welltyped t2 /\ ACONV t1 t2
                ==> ACONV (INST tyin t1) (INST tyin t2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ACONV_db; INST_WELLTYPED; INST_dbINST] THEN ASM_MESON_TAC[ACONV_db]);;
