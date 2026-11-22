(* ========================================================================= *)
(* holSyntaxExtra, part 5 of 8: HOL4 candle/standard/syntax/                 *)
(* holSyntaxExtraScript.sml lines 2403-3035 (CakeML v3479): bound variable   *)
(* names, simpler (non-capture-avoiding) substitution and instantiation,     *)
(* renaming of bound variables, fresh names and terms, the alternative       *)
(* characterisation of VARIANT by variant, frees, INST_CORE_Abs_thm.         *)
(* Notes on the rendering: the header of holSyntaxExtra_p1.ml.  HOL4 insert  *)
(* and union are hol_insert and hol_union (names.tsv); HOL4 s ^ t is         *)
(* strcat s t; SUM_SET and BIGUNION (UNIONS) as in hol4/basic.ml.  Local     *)
(* helpers that are not HOL4 theorems are CSYNAUX_P5_.                       *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p4.ml";;
needs "hol4/libext.ml";;

prioritize_num();;
type_invention_error := true;;

(* list of bound variable names in a term *)

let bv_names_def = cake_def
  `(bv_names (hol_Var _ _) = []) /\
   (bv_names (hol_Const _ _) = []) /\
   (bv_names (hol_Comb s t) = APPEND (bv_names s) (bv_names t)) /\
   (bv_names (hol_Abs v t) = CONS (FST (dest_var v)) (bv_names t))`;;
let _ = cake_add_simps [bv_names_def];;

(* Simpler versions (non-capture-avoiding) of substitution and instantiation.
   We do the semantics proofs on these and then use the fact that it is
   alpha-equivalence respecting, and suitable equivalent term always exists
   (see below). *)

let simple_subst_def = cake_def
  `(simple_subst ilist (hol_Var x ty) = REV_ASSOCD (hol_Var x ty) ilist (hol_Var x ty)) /\
   (simple_subst ilist (hol_Const x ty) = hol_Const x ty) /\
   (simple_subst ilist (hol_Comb t1 t2) =
      hol_Comb (simple_subst ilist t1) (simple_subst ilist t2)) /\
   (simple_subst ilist (hol_Abs v tm) =
      hol_Abs v (simple_subst (FILTER (\(s',s). ~(s = v)) ilist) tm))`;;
let _ = cake_add_simps [simple_subst_def];;

let simple_inst_def = cake_def
  `(simple_inst tyin (hol_Var x ty) = hol_Var x (TYPE_SUBST tyin ty)) /\
   (simple_inst tyin (hol_Const x ty) = hol_Const x (TYPE_SUBST tyin ty)) /\
   (simple_inst tyin (hol_Comb s t) =
      hol_Comb (simple_inst tyin s) (simple_inst tyin t)) /\
   (simple_inst tyin (hol_Abs v t) = hol_Abs (simple_inst tyin v) (simple_inst tyin t))`;;
let _ = cake_add_simps [simple_inst_def];;

let VSUBST_simple_subst = prove
 (`!tm ilist.
     DISJOINT (set_of_list (bv_names tm))
              {y | ?ty u. VFREE_IN (hol_Var y ty) u /\ MEM u (MAP FST ilist)} /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty) /\
     welltyped tm
     ==> VSUBST ilist tm = simple_subst ilist tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VSUBST_def; simple_subst_def; bv_names_def; WELLTYPED_CLAUSES;
              SET_OF_LIST_APPEND; DISJOINT_UNION; set_of_list] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[DISJOINT_INSERT; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[dest_var_def; FST]) THEN
    SUBGOAL_THEN `~EX (\(s',s). VFREE_IN (hol_Var n ty) s' /\ VFREE_IN s a1)
                      (FILTER (\(s',s). ~(s = hol_Var n ty)) ilist)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXISTS_MEM; MEM_FILTER; EXISTS_PAIR_THM] THEN
      QPAT_X_ASSUM "~(?ty u. _)" MP_TAC THEN
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN SIMP[] THEN MESON_TAC[];
      ALL_TAC] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_FILTER] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] DISJOINT_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; MEM_MAP; MEM_FILTER] THEN MESON_TAC[]]);;

(* the side conditions of the Abs case of INST_CORE_simple_inst *)
let CSYNAUX_P5_MEM_FST_ENV = prove
 (`!env x ty tyin.
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
     MEM (hol_Var x ty) (MAP FST env)
     ==> MEM x (MAP (FST o dest_var o SND) env)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; o_THM; FST; SND] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  MAP_EVERY EXISTS_TAC [`p1:hol_term`; `p2:hol_term`] THEN ASM_REWRITE_TAC[dest_var_def] THEN
  ASM_MESON_TAC[injectivity "hol_term"]);;

let CSYNAUX_P5_INST_ABS_COND = prove
 (`!n ty t env tyin.
  ALL_DISTINCT (APPEND (bv_names (hol_Abs (hol_Var n ty) t)) (MAP (FST o dest_var o SND) env)) /\
  DISJOINT (set_of_list (bv_names (hol_Abs (hol_Var n ty) t)))
           {x | ?ty'. VFREE_IN (hol_Var x ty') (hol_Abs (hol_Var n ty) t)} /\
  (!s s'. MEM (s,s') env ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
  (!x ty' ty''. VFREE_IN (hol_Var x ty') (hol_Abs (hol_Var n ty) t) /\
                MEM (hol_Var x ty'') (MAP FST env) ==> ty'' = ty')
  ==>
  ALL_DISTINCT (APPEND (bv_names t) (MAP (FST o dest_var o SND)
                  (CONS (hol_Var n ty,hol_Var n (TYPE_SUBST tyin ty)) env))) /\
  DISJOINT (set_of_list (bv_names t)) {x | ?ty. VFREE_IN (hol_Var x ty) t} /\
  (!s s'. MEM (s,s') (CONS (hol_Var n ty,hol_Var n (TYPE_SUBST tyin ty)) env)
          ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
  (!x ty' ty''. VFREE_IN (hol_Var x ty') t /\
                MEM (hol_Var x ty'')
                    (MAP FST (CONS (hol_Var n ty,hol_Var n (TYPE_SUBST tyin ty)) env))
                ==> ty'' = ty')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bv_names_def; dest_var_def; FST; SND; MAP; o_THM; APPEND; set_of_list;
              ALL_DISTINCT; ALL_DISTINCT_APPEND; MEM_APPEND; MEM; VFREE_IN_def;
              DISJOINT; EXTENSION; IN_INTER; IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY;
              IN_SET_OF_LIST; injectivity "hol_term"; PAIR_EQ] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:mlstring`) THEN ASM_MESON_TAC[];
    ASM_CASES_TAC `x:mlstring = n` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`env:(hol_term#hol_term)list`; `n:mlstring`; `ty'':hol_type`;
                     `tyin:(hol_type#hol_type)list`] CSYNAUX_P5_MEM_FST_ENV) THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let INST_CORE_simple_inst = prove
 (`!env tyin tm.
     ALL_DISTINCT (APPEND (bv_names tm) (MAP (FST o dest_var o SND) env)) /\
     DISJOINT (set_of_list (bv_names tm)) {x | ?ty. VFREE_IN (hol_Var x ty) tm} /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (TYPE_SUBST tyin ty)) /\
     (!x ty ty'. VFREE_IN (hol_Var x ty) tm /\ MEM (hol_Var x ty') (MAP FST env)
                 ==> ty' = ty) /\
     welltyped tm
     ==> INST_CORE env tyin tm = hol_Result (simple_inst tyin tm)`,
  MATCH_MP_TAC INST_CORE_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INST_CORE_def; simple_inst_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MP_TAC(ISPECL [`env:(hol_term#hol_term)list`; `hol_Var x (TYPE_SUBST tyin ty)`;
                   `hol_Var x ty`] REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th o
      check (fun th -> is_comb(concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "MEM"))) THEN
    SUBGOAL_THEN `REV_ASSOCD (hol_Var x (TYPE_SUBST tyin ty)) env (hol_Var x ty) =
                  hol_Var x ty` (fun th -> REWRITE_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `MEM (hol_Var x' ty') (MAP FST (env:(hol_term#hol_term)list))`
      ASSUME_TAC THENL
     [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[VFREE_IN_def];
    REWRITE_TAC[INST_CORE_def; simple_inst_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[bv_names_def; SET_OF_LIST_APPEND; DISJOINT_UNION; VFREE_IN_def;
                WELLTYPED_CLAUSES; ALL_DISTINCT_APPEND; MEM_APPEND] THEN
    STRIP_TAC THEN REWRITE_TAC[INST_CORE_def; simple_inst_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `INST_CORE env tyin s = hol_Result (simple_inst tyin s)` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT_APPEND] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN
      QPAT_X_ASSUM "DISJOINT (set_of_list (bv_names s)) _" MP_TAC THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `INST_CORE env tyin t = hol_Result (simple_inst tyin t)` ASSUME_TAC THENL
     [QPAT_X_ASSUM "~IS_CLASH (INST_CORE env tyin s) ==> _" MP_TAC THEN
      ASM_REWRITE_TAC[IS_CLASH_def] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ALL_DISTINCT_APPEND] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN
      QPAT_X_ASSUM "DISJOINT (set_of_list (bv_names t)) _" MP_TAC THEN SET_TAC[];
      ASM_REWRITE_TAC[IS_CLASH_def; RESULT_def]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[dest_var_def; PAIR_EQ]) THEN
    SUBGOAL_THEN `INST_CORE (CONS (hol_Var n ty,hol_Var n (TYPE_SUBST tyin ty)) env) tyin t =
                  hol_Result (simple_inst tyin t)` ASSUME_TAC THENL
     [QPAT_X_ASSUM "!x ty'. n = x /\\ ty = ty' ==> _"
        (MP_TAC o SPECL [`n:mlstring`; `ty:hol_type`]) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC(TAUT `(a /\ b /\ c /\ d) /\ w ==> a /\ b /\ c /\ d /\ w`) THEN
      CONJ_TAC THENL [MATCH_MP_TAC CSYNAUX_P5_INST_ABS_COND THEN ASM_REWRITE_TAC[];
                      ASM_REWRITE_TAC[]];
      REWRITE_TAC[INST_CORE_def; dest_var_def; simple_inst_def] THEN CASE_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[IS_RESULT_def; RESULT_def]]]);;

let INST_simple_inst = prove
 (`!tyin tm.
     ALL_DISTINCT (bv_names tm) /\
     DISJOINT (set_of_list (bv_names tm)) {x | ?ty. VFREE_IN (hol_Var x ty) tm} /\
     welltyped tm
     ==> INST tyin tm = simple_inst tyin tm`,
  REWRITE_TAC[INST_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[]:(hol_term#hol_term)list`; `tyin:(hol_type#hol_type)list`; `tm:hol_term`]
    INST_CORE_simple_inst) THEN
  ASM_REWRITE_TAC[MAP; APPEND_NIL; MEM] THEN SIMP_TAC[RESULT_def]);;

let simple_subst_has_type = prove
 (`!tm ty.
     tm has_type ty
     ==> !subst.
           ALL (\(s',s). s' has_type typeof s) subst
           ==> simple_subst subst tm has_type ty`,
  MATCH_MP_TAC has_type_ind THEN REWRITE_TAC[simple_subst_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subst:(hol_term#hol_term)list`; `hol_Var n ty`; `hol_Var n ty`]
      REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[has_type_rules] THEN
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    SIMP[typeof_def];
    REWRITE_TAC[has_type_rules];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(el 2 (CONJUNCTS has_type_rules)) THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(el 3 (CONJUNCTS has_type_rules)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ALL (\(s',s). s' has_type typeof s) subst` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN SIMP[]]);;

let simple_inst_has_type = prove
 (`!tm tyin. welltyped tm ==> simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm))`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  SIMP[simple_inst_def; typeof_def; WELLTYPED_CLAUSES; has_type_rules] THEN
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[codomain_def] THEN MATCH_MP_TAC(el 2 (CONJUNCTS has_type_rules)) THEN
    EXISTS_TAC `TYPE_SUBST tyin (typeof a1)` THEN ASM_MESON_TAC[TYPE_SUBST_def];
    ASM_REWRITE_TAC[simple_inst_def; typeof_def] THEN
    MATCH_MP_TAC(el 3 (CONJUNCTS has_type_rules)) THEN ASM_SIMP_TAC[]]);;

(* rename bound variables from a source of names *)

let rename_bvars_def = cake_def_wf
  `measure (\(names:mlstring list,env:(mlstring#mlstring#hol_type)list,tm).
              hol_term_size tm)`
  TERM_TAC
  `(rename_bvars names env (hol_Var s ty) =
      (names, hol_Var (REV_ASSOCD (s,ty) env s) ty)) /\
   (rename_bvars names env (hol_Const s ty) = (names, hol_Const s ty)) /\
   (rename_bvars names env (hol_Comb t1 t2) =
      let (names,t1) = rename_bvars names env t1 in
      let (names,t2) = rename_bvars names env t2 in
      (names, hol_Comb t1 t2)) /\
   (rename_bvars [] env (hol_Abs v tm) =
      let (names,tm) = rename_bvars [] env tm in
      (names, hol_Abs v tm)) /\
   (rename_bvars (CONS s' names) env (hol_Abs v tm) =
      let (names,tm) = rename_bvars names (CONS (s',dest_var v) env) tm in
      (names, hol_Abs (hol_Var s' (typeof v)) tm))`;;

let rename_bvars_ind = cake_ind "rename_bvars";;

let FST_rename_bvars = prove
 (`!names env tm.
     LENGTH (bv_names tm) <= LENGTH names
     ==> FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names`,
  MATCH_MP_TAC rename_bvars_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[rename_bvars_def; bv_names_def] THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN
  FS[LENGTH; LENGTH_APPEND; DROP_0; DROP_DEF; NOT_SUC; ARITH_RULE `~(SUC n <= 0)`] THENL
   [SUBGOAL_THEN `names' = DROP (LENGTH (bv_names t1)) (names:mlstring list)`
      SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    QPAT_X_ASSUM "_ ==> FST _ = _" MP_TAC THEN REWRITE_TAC[LENGTH_DROP] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    MATCH_MP_TAC DROP_DROP THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUC_SUB1]]);;

(* the Var case of rename_bvars_RACONV (HOL4: an induction inside the proof) *)
let CSYNAUX_P5_RENAME_VAR = prove
 (`!env s ty.
     ~MEM s (MAP FST env) /\ ALL_DISTINCT (MAP FST env)
     ==> ALPHAVARS (MAP (\(s',(s,ty)). (hol_Var s ty, hol_Var s' ty)) env)
                   (hol_Var s ty, hol_Var (REV_ASSOCD (s,ty) env s) ty)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[MAP; ALPHAVARS_def; REV_ASSOCD]; ALL_TAC] THEN
  PAIR_CASES_ON `h:mlstring#mlstring#hol_type` THEN
  REWRITE_TAC[MAP; ALPHAVARS_def; REV_ASSOCD; MEM; ALL_DISTINCT; PAIR_EQ;
              injectivity "hol_term"; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; SND; PAIR_EQ; injectivity "hol_term"] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `h1:mlstring = s /\ h2:hol_type = ty` THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(mlstring#mlstring#hol_type)list`; `(s:mlstring,ty:hol_type)`;
                   `s:mlstring`] REV_ASSOCD_MEM) THEN
    SUBGOAL_THEN `!y:mlstring. MEM (y,(s:mlstring,ty:hol_type)) t
                               ==> MEM y (MAP FST (t:(mlstring#mlstring#hol_type)list))`
      MP_TAC THENL
     [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~MEM (h0:mlstring) (MAP FST (t:(mlstring#mlstring#hol_type)list))` THEN
    UNDISCH_TAC `~(s = h0 \/ MEM s (MAP FST (t:(mlstring#mlstring#hol_type)list)))` THEN
    MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let rename_bvars_RACONV = prove
 (`!names env tm.
     LENGTH (bv_names tm) <= LENGTH names /\
     DISJOINT (set_of_list (APPEND (MAP FST env) names))
              (set_of_list (APPEND (MAP (FST o SND) env) (bv_names tm))) /\
     DISJOINT (set_of_list (APPEND (MAP FST env) names))
              {x | ?ty. VFREE_IN (hol_Var x ty) tm} /\
     ALL_DISTINCT (APPEND (MAP FST env) names) /\
     welltyped tm
     ==> RACONV (MAP (\(s',(s,ty)). (hol_Var s ty, hol_Var s' ty)) env)
                (tm, SND (rename_bvars names env tm))`,
  MATCH_MP_TAC rename_bvars_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[rename_bvars_def; RACONV; SND] THEN STRIP_TAC THEN
    MATCH_MP_TAC CSYNAUX_P5_RENAME_VAR THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND; DISJOINT; EXTENSION; IN_INTER;
      IN_ELIM_THM; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM_APPEND; VFREE_IN_def]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[rename_bvars_def; RACONV; SND];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHA") (LABEL_TAC "IHB")) THEN
    REWRITE_TAC[bv_names_def; LENGTH_APPEND; WELLTYPED_CLAUSES; VFREE_IN_def] THEN
    STRIP_TAC THEN REWRITE_TAC[rename_bvars_def] THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[SND; RACONV] THEN
    SUBGOAL_THEN `names' = DROP (LENGTH (bv_names t1)) (names:mlstring list)`
      SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`names:mlstring list`; `env:(mlstring#mlstring#hol_type)list`;
                     `t1:hol_term`] FST_rename_bvars) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "IHB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [QPAT_X_ASSUM "DISJOINT _ (set_of_list (APPEND (MAP (FST o SND) env) _))" MP_TAC THEN
        REWRITE_TAC[SET_OF_LIST_APPEND] THEN SET_TAC[];
        QPAT_X_ASSUM "DISJOINT _ {x | _}" MP_TAC THEN SET_TAC[]];
      SUBGOAL_THEN `set_of_list (DROP (LENGTH (bv_names t1)) names) SUBSET
                    set_of_list (names:mlstring list)` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN MESON_TAC[MEM_DROP_IMP]; ALL_TAC] THEN
      REMOVE_THEN "IHA" (MP_TAC o SPECL [`t1':hol_term`;
        `DROP (LENGTH (bv_names t1)) (names:mlstring list)`]) THEN
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[SND] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[LENGTH_DROP] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [QPAT_X_ASSUM "DISJOINT _ (set_of_list (APPEND (MAP (FST o SND) env) _))" MP_TAC THEN
        QPAT_X_ASSUM "_ SUBSET _" MP_TAC THEN REWRITE_TAC[SET_OF_LIST_APPEND] THEN SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [QPAT_X_ASSUM "DISJOINT _ {x | _}" MP_TAC THEN
        QPAT_X_ASSUM "_ SUBSET _" MP_TAC THEN REWRITE_TAC[SET_OF_LIST_APPEND] THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ALL_DISTINCT (APPEND (MAP FST (env:(mlstring#mlstring#hol_type)list))
                                        (names:mlstring list))` THEN
      REWRITE_TAC[ALL_DISTINCT_APPEND] THEN MESON_TAC[ALL_DISTINCT_DROP; MEM_DROP_IMP]];
    DISCH_TAC THEN REWRITE_TAC[bv_names_def; LENGTH; ARITH_RULE `~(SUC n <= 0)`];
    DISCH_THEN(LABEL_TAC "IH") THEN
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[rename_bvars_def] THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[SND; RACONV; typeof_def; dest_var_def] THEN
    REMOVE_THEN "IH" MP_TAC THEN REWRITE_TAC[dest_var_def; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bv_names_def; dest_var_def; FST; LENGTH; LE_SUC;
      VFREE_IN_def; injectivity "hol_term"]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM; FST; SND] THEN
    CONJ_TAC THENL
     [QPAT_X_ASSUM "DISJOINT _ (set_of_list _)" MP_TAC THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `!x ty'. VFREE_IN (hol_Var x ty') tm
                    ==> x = n \/
                        x IN {x | ?ty'. ~(n = x /\ ty = ty') /\ VFREE_IN (hol_Var x ty') tm}`
        MP_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
      QPAT_X_ASSUM "DISJOINT _ (set_of_list _)" MP_TAC THEN
      QPAT_X_ASSUM "DISJOINT _ {x | _}" MP_TAC THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      SPEC_TAC(`{x | ?ty'. ~(n = x /\ ty = ty') /\ VFREE_IN (hol_Var x ty') tm}`,
               `S:mlstring->bool`) THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ALL_DISTINCT (APPEND (MAP FST (env:(mlstring#mlstring#hol_type)list))
                                      (CONS s' names))` THEN
    REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM] THEN MESON_TAC[]]);;

let rename_bvars_ACONV = prove
 (`!names tm.
     LENGTH (bv_names tm) <= LENGTH names /\ ALL_DISTINCT names /\
     DISJOINT (set_of_list names)
              {x | MEM x (bv_names tm) \/ ?ty. VFREE_IN (hol_Var x ty) tm} /\
     welltyped tm
     ==> ACONV tm (SND (rename_bvars names [] tm))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ACONV_def] THEN
  MP_TAC(ISPECL [`names:mlstring list`; `[]:(mlstring#mlstring#hol_type)list`;
                 `tm:hol_term`] rename_bvars_RACONV) THEN
  REWRITE_TAC[MAP; APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (set_of_list names)
              {x | MEM x (bv_names tm) \/ ?ty. VFREE_IN (hol_Var x ty) tm}` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_SET_OF_LIST] THEN
  MESON_TAC[]);;

(* the assumption that is a has_type fact (not an induction hypothesis) *)
let CSYNAUX_P5_IS_HAS_TYPE th =
  try fst(dest_const(fst(strip_comb(concl th)))) = "has_type"
  with Failure _ -> false;;

let rename_bvars_has_type = prove
 (`!names env tm ty. tm has_type ty ==> SND (rename_bvars names env tm) has_type ty`,
  MATCH_MP_TAC rename_bvars_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[rename_bvars_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check CSYNAUX_P5_IS_HAS_TYPE) THEN
  GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[injectivity "hol_term"; distinctness "hol_term"] THEN
  REPEAT STRIP_TAC THEN REPEAT PAIRARG_TAC THEN FS[] THEN RFS[] THEN
  ASM_MESON_TAC[has_type_rules]);;

let rename_bvars_welltyped = prove
 (`!names env tm. welltyped tm ==> welltyped (SND (rename_bvars names env tm))`,
  MESON_TAC[rename_bvars_has_type; welltyped_def]);;

(* appropriate fresh term for using the simple functions above *)

(* HOL4 derives the existence from IN_INFINITE_NOT_FINITE and              *)
(* INFINITE_LIST_UNIV; here PRIMED_INFINITE gives an infinite set of        *)
(* strings.                                                                  *)
let fresh_def = new_specification ["fresh"]
 (prove
   (`?f. !s:string->bool. FINITE s ==> ~(f s IN s)`,
    REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (\n. APPEND [] (list_of_seq (K (CHR 39)) n)) (:num)`;
                   `s:string->bool`] IN_INFINITE_NOT_FINITE) THEN
    ASM_REWRITE_TAC[REWRITE_RULE[] (INST [`[]:string`,`x:string`] PRIMED_INFINITE)] THEN
    MESON_TAC[]));;

let fresh_union = prove
 (`FINITE s /\ FINITE t ==> ~(fresh (s UNION t) IN s) /\ ~(fresh (s UNION t) IN t)`,
  MESON_TAC[fresh_def; FINITE_UNION; IN_UNION]);;

let fresh_names_exist = prove
 (`!s n. FINITE (s:string->bool)
         ==> ?names. LENGTH names = n /\ ALL_DISTINCT names /\
                     DISJOINT (set_of_list names) s`,
  GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `[]:string list` THEN
    REWRITE_TAC[LENGTH; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY];
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
    EXISTS_TAC `CONS (fresh (s UNION set_of_list names)) names` THEN
    ASM_SIMP_TAC[LENGTH; ALL_DISTINCT; set_of_list; DISJOINT_INSERT;
                 GSYM IN_SET_OF_LIST; fresh_union; FINITE_SET_OF_LIST]]);;

let bv_names_rename_bvars = prove
 (`!names env tm.
     LENGTH (bv_names tm) <= LENGTH names
     ==> bv_names (SND (rename_bvars names env tm)) =
         TAKE (LENGTH (bv_names tm)) names`,
  MATCH_MP_TAC rename_bvars_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[rename_bvars_def; bv_names_def] THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN
  FS[LENGTH; LENGTH_APPEND; TAKE_0; TAKE_DEF; NOT_SUC; ARITH_RULE `~(SUC n <= 0)`;
     bv_names_def; dest_var_def; FST; SUC_SUB1] THEN
  SUBGOAL_THEN `names' = DROP (LENGTH (bv_names t1)) (names:mlstring list)` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`names:mlstring list`; `env:(mlstring#mlstring#hol_type)list`;
                   `t1:hol_term`] FST_rename_bvars) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]; ALL_TAC] THEN
  QPAT_X_ASSUM "_ ==> bv_names (SND _) = _" MP_TAC THEN REWRITE_TAC[LENGTH_DROP] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `bv_names t1' = TAKE (LENGTH (bv_names t1)) (names:mlstring list)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAKE_SUM]);;

(* various rewrites for FINITE sets to make this go through *)

let FINITE_VFREE_IN = prove
 (`!tm. FINITE {x | ?ty. VFREE_IN (hol_Var x ty) tm}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\v. FST (dest_var v)) {v | VFREE_IN v tm}` THEN
  SIMP_TAC[FINITE_IMAGE; VFREE_IN_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[dest_var_def; FST]);;
let _ = cake_add_simps [FINITE_VFREE_IN];;

let FINITE_VFREE_IN_2 = prove
 (`!tm. FINITE {(x,ty) | VFREE_IN (hol_Var x ty) tm}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE dest_var {v | VFREE_IN v tm}` THEN
  SIMP_TAC[FINITE_IMAGE; VFREE_IN_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; FORALL_PAIR_THM] THEN
  MESON_TAC[dest_var_def]);;
let _ = cake_add_simps [FINITE_VFREE_IN_2];;

let FINITE_VFREE_IN_list = prove
 (`!ls. FINITE {x | ?ty u. VFREE_IN (hol_Var x ty) u /\ MEM u ls}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\u. {x | ?ty. VFREE_IN (hol_Var x ty) u}) (set_of_list ls))` THEN
  SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FINITE_SET_OF_LIST; FORALL_IN_IMAGE;
           FINITE_VFREE_IN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_SET_OF_LIST] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [FINITE_VFREE_IN_list];;

let FINITE_MEM_Var = prove
 (`!ls. FINITE {(x,ty) | MEM (hol_Var x ty) ls}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE dest_var (set_of_list ls)` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_SET_OF_LIST] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_SET_OF_LIST; FORALL_PAIR_THM] THEN
  MESON_TAC[dest_var_def]);;
let _ = cake_add_simps [FINITE_MEM_Var];;

let CSYNAUX_P5_MAP_explode_implode = prove
 (`!l. MAP explode (MAP implode l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; explode_implode]);;

let fresh_term_def = new_specification ["fresh_term"]
 (prove
   (`?f. !s tm. FINITE s
                ==> welltyped tm
                ==> welltyped (f s tm) /\
                    ACONV tm (f s tm) /\
                    ALL_DISTINCT (bv_names (f s tm)) /\
                    DISJOINT (set_of_list (bv_names (f s tm))) s`,
    REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE explode (s UNION set_of_list (bv_names tm) UNION
                                   {x | ?ty. VFREE_IN (hol_Var x ty) tm})`;
                   `LENGTH (bv_names tm)`] fresh_names_exist) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_UNION; FINITE_SET_OF_LIST; FINITE_VFREE_IN];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `names:string list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SND (rename_bvars (MAP implode names) [] tm)` THEN
    SUBGOAL_THEN `bv_names (SND (rename_bvars (MAP implode names) [] tm)) =
                  MAP implode names` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`MAP implode names`; `[]:(mlstring#mlstring#hol_type)list`;
                     `tm:hol_term`] bv_names_rename_bvars) THEN
      ASM_REWRITE_TAC[LENGTH_MAP; LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC TAKE_LENGTH_ID_rwt THEN ASM_REWRITE_TAC[LENGTH_MAP];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL_DISTINCT (MAP implode names)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM ALL_DISTINCT_MAP_explode] THEN
      ASM_REWRITE_TAC[CSYNAUX_P5_MAP_explode_implode];
      ALL_TAC] THEN
    ASM_SIMP_TAC[rename_bvars_welltyped] THEN CONJ_TAC THENL
     [MATCH_MP_TAC rename_bvars_ACONV THEN ASM_REWRITE_TAC[LENGTH_MAP; LE_REFL];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (set_of_list names)
       (IMAGE explode (s UNION set_of_list (bv_names tm) UNION
                       {x | ?ty. VFREE_IN (hol_Var x ty) tm}))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_SET_OF_LIST;
                IN_IMAGE; IN_UNION; MEM_MAP] THEN
    MESON_TAC[explode_implode; implode_explode]));;

(* Alternative characterisation of VARIANT, and thereby of VSUBST and INST_CORE.
   Better for evaluation. *)

let vfree_in_def = cake_def
  `vfree_in v tm =
     match tm with
       hol_Abs bv bod -> ~(v = bv) /\ vfree_in v bod
     | hol_Comb s t -> vfree_in v s \/ vfree_in v t
     | _ -> tm = v`;;

let vfree_in_thm = prove
 (`!name ty y. VFREE_IN (hol_Var name ty) y <=> vfree_in (hol_Var name ty) y`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[vfree_in_def] THEN SIMP[VFREE_IN_def] THEN MESON_TAC[]);;

(* the sets of the termination measure of variant are finite *)
let CSYNAUX_P5_FINITE_STRLEN = prove
 (`!a. FINITE {strlen x + 1 | x | ?ty. VFREE_IN (hol_Var x ty) a}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\x. strlen x + 1) {x | ?ty. VFREE_IN (hol_Var x ty) a}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_VFREE_IN] THEN SET_TAC[]);;

(* HOL4's measure, with its let n = .. in written out *)
let variant_def = cake_def_wf
  (CASE_TERM `measure (\(avoid:hol_term list,v:hol_term).
     SUM_SET (UNIONS (set_of_list
       (MAP (\a. {strlen x + 1 | x | ?ty. VFREE_IN (hol_Var x ty) a}) avoid))) -
     (match v with hol_Var x ty -> strlen x | _ -> 0))`)
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[strlen_strcat; strlen_def; LENGTH] THEN
   MATCH_MP_TAC(ARITH_RULE `a < n ==> n - (a + SUC 0) < n - a`) THEN
   MATCH_MP_TAC SUM_SET_IN_LT THEN EXISTS_TAC `strlen s' + 1` THEN
   REWRITE_TAC[ARITH_RULE `a < a + 1`] THEN CONJ_TAC THENL
    [REWRITE_TAC[FINITE_UNIONS; FINITE_SET_OF_LIST; IN_SET_OF_LIST; MEM_MAP] THEN
     MESON_TAC[CSYNAUX_P5_FINITE_STRLEN];
     UNDISCH_TAC `EX (vfree_in v) avoid` THEN ASM_REWRITE_TAC[EXISTS_MEM] THEN
     REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; GSYM vfree_in_thm] THEN
     DISCH_THEN(X_CHOOSE_THEN `a:hol_term` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `{strlen x + 1 | x | ?ty. VFREE_IN (hol_Var x ty) a}` THEN
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]])
  `variant avoid v =
     if EX (vfree_in v) avoid then
       match v with
         hol_Var s ty -> variant avoid (hol_Var (strcat s (implode "'")) ty)
       | _ -> v
     else v`;;

let variant_ind = cake_ind "variant";;

(* VARIANT by variant: HOL4 proves both corollaries with variant_ind and    *)
(* REPLICATE; here one lemma for any list of terms whose free variables are *)
(* those of x, from the uniqueness of the least number of primes.           *)
let CSYNAUX_P5_PRIMES_SUC = prove
 (`!m. list_of_seq (K (CHR 39)) (SUC m) = CONS (CHR 39) (list_of_seq (K (CHR 39)) m)`,
  SUBGOAL_THEN `!m. APPEND (list_of_seq (K (CHR 39)) m) [CHR 39] =
                    CONS (CHR 39) (list_of_seq (K (CHR 39)) m)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[list_of_seq; K_THM; APPEND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[list_of_seq; K_THM]);;

let CSYNAUX_P5_VARIANT_PRIMES_UNIQUE = prove
 (`!t s ty n.
     ~VFREE_IN (hol_Var (implode (APPEND s (list_of_seq (K (CHR 39)) n))) ty) t /\
     (!m. m < n
          ==> VFREE_IN (hol_Var (implode (APPEND s (list_of_seq (K (CHR 39)) m))) ty) t)
     ==> VARIANT_PRIMES t s ty = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:hol_term`; `s:string`; `ty:hol_type`] VARIANT_PRIMES_def) THEN
  STRIP_TAC THEN MATCH_MP_TAC(ARITH_RULE `~(a < b) /\ ~(b < a) ==> a = b`) THEN
  ASM_MESON_TAC[]);;

let CSYNAUX_P5_APPEND_PRIME = prove
 (`!s m. APPEND (APPEND s "'") (list_of_seq (K (CHR 39)) m) =
         APPEND s (list_of_seq (K (CHR 39)) (SUC m))`,
  REWRITE_TAC[CSYNAUX_P5_PRIMES_SUC; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[CHR_DEF] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let CSYNAUX_P5_VARIANT_NOT_FREE = prove
 (`!x name ty. ~VFREE_IN (hol_Var name ty) x ==> VARIANT x (explode name) ty = name`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VARIANT_def] THEN
  SUBGOAL_THEN `VARIANT_PRIMES x (explode name) ty = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC CSYNAUX_P5_VARIANT_PRIMES_UNIQUE THEN
    ASM_REWRITE_TAC[list_of_seq; APPEND_NIL; implode_explode; LT];
    REWRITE_TAC[list_of_seq; APPEND_NIL; implode_explode]]);;

let CSYNAUX_P5_VARIANT_FREE = prove
 (`!x name ty.
     VFREE_IN (hol_Var name ty) x
     ==> VARIANT x (explode (strcat name (implode "'"))) ty = VARIANT x (explode name) ty`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[strcat_thm; explode_implode] THEN
  MP_TAC(SPECL [`x:hol_term`; `explode name`; `ty:hol_type`] VARIANT_PRIMES_def) THEN
  ABBREV_TAC `k = VARIANT_PRIMES x (explode name) ty` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?j. k = SUC j` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `k = 0` THENL
     [UNDISCH_TAC `~VFREE_IN (hol_Var (implode (APPEND (explode name)
                      (list_of_seq (K (CHR 39)) k))) ty) x` THEN
      ASM_REWRITE_TAC[list_of_seq; APPEND_NIL; implode_explode];
      ASM_MESON_TAC[num_CASES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `VARIANT_PRIMES x (APPEND (explode name) "'") ty = j` ASSUME_TAC THENL
   [MATCH_MP_TAC CSYNAUX_P5_VARIANT_PRIMES_UNIQUE THEN
    REWRITE_TAC[CSYNAUX_P5_APPEND_PRIME] THEN ASM_MESON_TAC[LT_SUC];
    ASM_REWRITE_TAC[VARIANT_def; CSYNAUX_P5_APPEND_PRIME]]);;

let CSYNAUX_P5_variant_VARIANT = prove
 (`!avoid v x name ty.
     v = hol_Var name ty /\
     (!n. EX (vfree_in (hol_Var n ty)) avoid <=> VFREE_IN (hol_Var n ty) x)
     ==> variant avoid v = hol_Var (VARIANT x (explode name) ty) ty`,
  MATCH_MP_TAC variant_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[variant_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`name:mlstring`; `ty:hol_type`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:hol_term`; `strcat name (implode "'")`; `ty:hol_type`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[CSYNAUX_P5_VARIANT_FREE];
    ASM_SIMP_TAC[CSYNAUX_P5_VARIANT_NOT_FREE]]);;

let variant_vsubst_thm = prove
 (`variant [x] (hol_Var name ty) = hol_Var (VARIANT x (explode name) ty) ty`,
  MATCH_MP_TAC CSYNAUX_P5_variant_VARIANT THEN
  REWRITE_TAC[EX; GSYM vfree_in_thm]);;

(* HOL4: REWRITE_RULE[SYM variant_vsubst_thm] VSUBST_def *)
let VSUBST_thm = prove
 (CASE_TERM
  `(!ilist x ty.
      VSUBST ilist (hol_Var x ty) = REV_ASSOCD (hol_Var x ty) ilist (hol_Var x ty)) /\
   (!ilist x ty. VSUBST ilist (hol_Const x ty) = hol_Const x ty) /\
   (!ilist s t.
      VSUBST ilist (hol_Comb s t) = hol_Comb (VSUBST ilist s) (VSUBST ilist t)) /\
   (!ilist v t.
      VSUBST ilist (hol_Abs v t) =
      let ilist' = FILTER (\(s',s). ~(s = v)) ilist in
      let t' = VSUBST ilist' t in
      if EX (\(s',s). VFREE_IN v s' /\ VFREE_IN s t) ilist'
      then let (x,ty) = dest_var v in
           let z = variant [t'] (hol_Var x ty) in
           let ilist'' = CONS (z,v) ilist' in
           hol_Abs z (VSUBST ilist'' t)
      else hol_Abs v t')`,
  REWRITE_TAC[variant_vsubst_thm] THEN MATCH_ACCEPT_TAC VSUBST_def);;

let subtract_def = cake_def
  `subtract (l1:A list) l2 = FILTER (\t. ~(MEM t l2)) l1`;;

(* HOL4: insert *)
let hol_insert_def = cake_def
  `hol_insert (x:A) l = if MEM x l then l else CONS x l`;;

let itlist_def = cake_def
  `itlist (f:A->B->B) l b =
     match l with
       [] -> b
     | CONS h t -> f h (itlist f t b)`;;

(* HOL4: union *)
let hol_union_def = cake_def
  `hol_union (l1:A list) l2 = itlist hol_insert l1 l2`;;

let MEM_union = prove
 (`!xs ys (x:A). MEM x (hol_union xs ys) <=> MEM x xs \/ MEM x ys`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[hol_union_def] THEN ONCE_REWRITE_TAC[itlist_def] THEN
  SIMP[MEM] THEN REWRITE_TAC[GSYM hol_union_def; hol_insert_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let EXISTS_union = prove
 (`!xs ys. EX (P:A->bool) (hol_union xs ys) <=> EX P xs \/ EX P ys`,
  REWRITE_TAC[EXISTS_MEM; MEM_union] THEN MESON_TAC[]);;

let frees_def = cake_def
  `frees tm =
     match tm with
       hol_Var _ _ -> [tm]
     | hol_Const _ _ -> []
     | hol_Abs bv bod -> subtract (frees bod) [bv]
     | hol_Comb s t -> hol_union (frees s) (frees t)`;;

let MEM_frees_EQ = prove
 (`!a x. MEM x (frees a) <=> ?n ty. x = hol_Var n ty /\ MEM (hol_Var n ty) (frees a)`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[frees_def] THEN
  CASE_REWRITE_TAC[MEM; MEM_union; subtract_def; MEM_FILTER] THEN ASM_MESON_TAC[]);;

(* the elements of frees a are the free variables of a *)
let CSYNAUX_P5_MEM_frees = prove
 (`!a n ty. MEM (hol_Var n ty) (frees a) <=> VFREE_IN (hol_Var n ty) a`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[frees_def] THEN
  CASE_REWRITE_TAC[MEM; MEM_union; subtract_def; MEM_FILTER; VFREE_IN_def] THEN
  ASM_MESON_TAC[]);;

let CSYNAUX_P5_EX_frees = prove
 (`!a n ty. EX (vfree_in (hol_Var n ty)) (frees a) <=> MEM (hol_Var n ty) (frees a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXISTS_MEM] THEN
  ONCE_REWRITE_TAC[MEM_frees_EQ] THEN REWRITE_TAC[GSYM vfree_in_thm; VFREE_IN_def] THEN
  SIMP[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC; VFREE_IN_def] THEN MESON_TAC[]);;

let variant_inst_thm = prove
 (`welltyped a
   ==> variant (frees a) (hol_Var name ty1) =
       hol_Var (VARIANT a (explode name) ty1) ty1`,
  DISCH_TAC THEN MATCH_MP_TAC CSYNAUX_P5_variant_VARIANT THEN
  REWRITE_TAC[CSYNAUX_P5_EX_frees; CSYNAUX_P5_MEM_frees]);;

let INST_CORE_Abs_thm = prove
 (CASE_TERM
  `!v t env tyin.
     welltyped (hol_Abs v t)
     ==> INST_CORE env tyin (hol_Abs v t) =
         (let (x,ty) = dest_var v in
          let ty' = TYPE_SUBST tyin ty in
          let v' = hol_Var x ty' in
          let env' = CONS (v,v') env in
          let tres = INST_CORE env' tyin t in
          if IS_RESULT tres then hol_Result (hol_Abs v' (RESULT tres))
          else
            (let w = CLASH tres in
             if ~(w = v') then tres
             else
               (let (x',_) =
                  dest_var (variant (frees (RESULT (INST_CORE [] tyin t)))
                                    (hol_Var x ty')) in
                let t' = VSUBST [(hol_Var x' ty,hol_Var x ty)] t in
                let env'' = CONS (hol_Var x' ty,hol_Var x' ty') env in
                let tres' = INST_CORE env'' tyin t' in
                if IS_RESULT tres' then
                  hol_Result (hol_Abs (hol_Var x' ty') (RESULT tres'))
                else tres')))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [INST_CORE_def] THEN
  REWRITE_TAC[dest_var_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped (RESULT (INST_CORE [] tyin t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[INST_WELLTYPED; INST_def]; ALL_TAC] THEN
  ASM_SIMP_TAC[variant_inst_thm; dest_var_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;
