(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 5 (HOL4 lines      *)
(* 3595-4408): substitution steps (apply_steps), unique                      *)
(* variable names, pick_names, derivable axiom steps.                        *)
(* ========================================================================= *)

needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem_p4.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 pair SWAP (not in the port's library): defined here *)
let CLITAUX_SWAP_def = new_definition
  `CLITAUX_SWAP (a:A#B) = (SND a,FST a)`;;

(* Substitution steps: a list of VSUBST and INST_TYPE operations to apply *)
let subst_step_INDUCT,subst_step_RECURSION = cake_type
  "subst_step = VStep ((hol_term#hol_term) list) | TStep ((hol_type#hol_type) list)";;

let apply_steps_def = cake_def
  `(apply_steps [] c = c) /\
   (apply_steps (CONS (VStep ilist) rest) c = VSUBST ilist (apply_steps rest c)) /\
   (apply_steps (CONS (TStep tyin) rest) c = INST tyin (apply_steps rest c))`;;

let apply_steps_ind = cake_ind "apply_steps";;

let steps_ok_def = cake_def
  `(steps_ok sig [] <=> T) /\
   (steps_ok sig (CONS (VStep ilist) rest) <=>
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s') /\
      steps_ok sig rest) /\
   (steps_ok sig (CONS (TStep tyin) rest) <=>
      ALL (type_ok (FST sig)) (MAP FST tyin) /\ steps_ok sig rest)`;;

(* the ilist condition of VSUBST_WELLTYPED and VSUBST_HAS_TYPE from a
   stronger one *)
let CLITAUX_ilist_wk = prove
 (`!(P:hol_term->bool) ilist.
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ P s')
     ==> (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)`,
  MESON_TAC[]);;

let apply_steps_append = prove
 (`!s1 s2 c. apply_steps (APPEND s1 s2) c = apply_steps s1 (apply_steps s2 c)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; apply_steps_def] THEN
  QCASES_ON "h" THEN ASM_REWRITE_TAC[APPEND; apply_steps_def]);;

let steps_ok_append = prove
 (`!s1 s2 sig. steps_ok sig (APPEND s1 s2) <=> steps_ok sig s1 /\ steps_ok sig s2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; steps_ok_def] THEN
  QCASES_ON "h" THEN ASM_REWRITE_TAC[APPEND; steps_ok_def; CONJ_ASSOC]);;

let apply_steps_welltyped = prove
 (`!steps c sig.
     welltyped c /\ steps_ok sig steps ==> welltyped (apply_steps steps c)`,
  REC_IND_TAC apply_steps_ind THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST [MATCH_MP_TAC VSUBST_WELLTYPED; MATCH_MP_TAC INST_WELLTYPED] THEN
  TRY CONJ_TAC THEN
  FIRST [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLITAUX_ilist_wk);
         FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `sig:sig`) THEN ASM_REWRITE_TAC[]]);;

let apply_steps_term_ok = prove
 (`!steps c sig.
     hol_term_ok sig c /\ steps_ok sig steps ==> hol_term_ok sig (apply_steps steps c)`,
  REC_IND_TAC apply_steps_ind THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST [MATCH_MP_TAC term_ok_VSUBST; MATCH_MP_TAC term_ok_INST] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `sig:sig`) THEN ASM_REWRITE_TAC[]);;

let apply_steps_has_type_Bool = prove
 (`!steps c sig.
     c has_type Tyapp (implode "bool") [] /\ steps_ok sig steps
     ==> apply_steps steps c has_type Tyapp (implode "bool") []`,
  REC_IND_TAC apply_steps_ind THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC VSUBST_HAS_TYPE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `sig:sig`) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLITAUX_ilist_wk)];
    MATCH_MP_TAC INST_HAS_TYPE THEN EXISTS_TAC `Tyapp (implode "bool") []` THEN
    REWRITE_TAC[TYPE_SUBST_Bool] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `sig:sig`) THEN ASM_REWRITE_TAC[]]);;

let unique_varnames_def = cake_def
  `unique_varnames tm <=>
     !x ty1 ty2. VFREE_IN (hol_Var x ty1) tm /\ VFREE_IN (hol_Var x ty2) tm ==> ty1 = ty2`;;

let unique_varnames_no_var_collapse = prove
 (`!tm sigma. unique_varnames tm ==> no_var_collapse sigma tm`,
  REWRITE_TAC[unique_varnames_def; no_var_collapse] THEN MESON_TAC[]);;

let unique_varnames_INST = prove
 (`!tm tyin. welltyped tm /\ unique_varnames tm ==> unique_varnames (INST tyin tm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  MP_TAC(ISPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                 `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RESULT_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[unique_varnames_def]) THEN
  REWRITE_TAC[unique_varnames_def] THEN ASM_MESON_TAC[]);;

let unique_varnames_abs = prove
 (`!x ty z body.
     welltyped body /\
     unique_varnames (hol_Abs (hol_Var x ty) body) /\ ~MEM z (tm_names body)
     ==> unique_varnames (VSUBST [(hol_Var z ty,hol_Var x ty)] body)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[unique_varnames_def] THEN
  MAP_EVERY X_GEN_TAC [`y:mlstring`; `t1:hol_type`; `t2:hol_type`] THEN
  ASM_SIMP_TAC[VFREE_IN_VSUBST; REV_ASSOCD] THEN
  REWRITE_TAC[COND_RAND; VFREE_IN_def; injectivity "hol_term"] THEN
  QPAT_X_ASSUM "unique_varnames _"
    (MP_TAC o REWRITE_RULE[unique_varnames_def; VFREE_IN_def; injectivity "hol_term"]) THEN
  QPAT_X_ASSUM "~MEM _ _" (MP_TAC o MATCH_MP (MESON[VFREE_IN_tm_names]
    `~MEM z (tm_names body) ==> !ty. ~VFREE_IN (hol_Var z ty) body`)) THEN
  MESON_TAC[]);;

let pick_names_def = cake_def
  `(pick_names c avds [] = []) /\
   (pick_names c avds (CONS (x,ty) rest) =
      let n = NVARIANT x avds c in
      CONS (hol_Var n ty,hol_Var x ty) (pick_names c (CONS n avds) rest))`;;

(* induction on the variable list of pick_names, one step unfolded *)
let CLITAUX_PICK_PREP =
  LIST_INDUCT_TAC THEN REWRITE_TAC[pick_names_def; MEM] THEN
  PAIR_CASES_ON `h:mlstring#hol_type` THEN
  REWRITE_TAC[pick_names_def; LET_DEF; LET_END_DEF; MEM; PAIR_EQ;
              injectivity "hol_term"; ALL_DISTINCT; REV_ASSOCD];;

let CLITAUX_PICK_TAC thl = CLITAUX_PICK_PREP THEN ASM_MESON_TAC thl;;

let pick_names_form = prove
 (`!vars c avds s' s.
     MEM (s',s) (pick_names c avds vars)
     ==> ?x ty n. s = hol_Var x ty /\ s' = hol_Var n ty /\ MEM (x,ty) vars`,
  CLITAUX_PICK_TAC[]);;

let pick_names_fresh = prove
 (`!vars c avds n ty x ty'.
     MEM (hol_Var n ty,hol_Var x ty') (pick_names c avds vars)
     ==> ~MEM n (tm_names c) /\ ty = ty'`,
  CLITAUX_PICK_TAC[NVARIANT_NAMES_THM]);;

let pick_names_targets_not_in_avds = prove
 (`!vars c avds n ty s.
     MEM (hol_Var n ty,s) (pick_names c avds vars) ==> ~MEM n avds`,
  CLITAUX_PICK_PREP THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[NVARIANT_AVDS_THM];
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:hol_term`; `CONS (NVARIANT h0 avds c) avds`;
                                  `n:mlstring`; `ty:hol_type`; `s:hol_term`]) THEN
    ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN SIMP_TAC[]]);;

let pick_names_targets_inj = prove
 (`!vars c avds n ty1 s1 ty2 s2.
     MEM (hol_Var n ty1,s1) (pick_names c avds vars) /\
     MEM (hol_Var n ty2,s2) (pick_names c avds vars)
     ==> ty1 = ty2 /\ s1 = s2`,
  CLITAUX_PICK_PREP THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GVS[] THEN
  TRY(IMP_RES_TAC pick_names_targets_not_in_avds THEN FS[MEM] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`c:hol_term`; `CONS (NVARIANT h0 avds c) avds`;
                                       `n:mlstring`]) THEN ASM_REWRITE_TAC[]);;

let pick_names_sources_inj = prove
 (`!vars c avds.
     ALL_DISTINCT vars
     ==> !t1 t2 x ty.
           MEM (t1,hol_Var x ty) (pick_names c avds vars) /\
           MEM (t2,hol_Var x ty) (pick_names c avds vars)
           ==> t1 = t2`,
  CLITAUX_PICK_PREP THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS[] THEN
  TRY(IMP_RES_TAC pick_names_form THEN GVS[] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`c:hol_term`; `CONS (NVARIANT h0 avds c) avds`]) THEN
  MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[]);;

let pick_names_sources = prove
 (`!vars c avds x ty.
     MEM (x,ty) vars ==> ?n. MEM (hol_Var n ty,hol_Var x ty) (pick_names c avds vars)`,
  CLITAUX_PICK_PREP THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `NVARIANT h0 avds c` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:hol_term`; `CONS (NVARIANT h0 avds c) avds`;
                                  `x:mlstring`; `ty:hol_type`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let pick_names_REV_ASSOCD = prove
 (`!vars c avds y ty d.
     MEM (y,ty) vars
     ==> ?n. REV_ASSOCD (hol_Var y ty) (pick_names c avds vars) d = hol_Var n ty /\
             MEM (hol_Var n ty,hol_Var y ty) (pick_names c avds vars)`,
  CLITAUX_PICK_PREP THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `h0:mlstring = y /\ h1:hol_type = ty` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `NVARIANT y avds c` THEN REWRITE_TAC[];
    STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:hol_term`; `CONS (NVARIANT h0 avds c) avds`;
                                  `y:mlstring`; `ty:hol_type`; `d:hol_term`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let rename_to_unique_varnames = prove
 (`!sig c.
     hol_term_ok sig c
     ==> ?ilist_r.
           unique_varnames (VSUBST ilist_r c) /\
           (!t s. MEM (t,s) ilist_r
                  ==> ?x ty y. s = hol_Var x ty /\ t = hol_Var y ty /\
                               hol_term_ok sig t /\ VFREE_IN s c) /\
           (!nm ty1 v1 ty2 v2.
              MEM (hol_Var nm ty1,v1) ilist_r /\ MEM (hol_Var nm ty2,v2) ilist_r
              ==> ty1 = ty2 /\ v1 = v2) /\
           (!nm ty0 v. MEM (hol_Var nm ty0,v) ilist_r ==> ~VFREE_IN (hol_Var nm ty0) c) /\
           (!t1 t2 s. MEM (t1,s) ilist_r /\ MEM (t2,s) ilist_r ==> t1 = t2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped c` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  ABBREV_TAC `vars = list_of_set {(x,ty) | VFREE_IN (hol_Var x ty) c}` THEN
  SUBGOAL_THEN `ALL_DISTINCT vars /\ (!y t. MEM (y,t) vars <=> VFREE_IN (hol_Var y t) c)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "vars" THEN
    SIMP_TAC[ALL_DISTINCT_SET_TO_LIST; MEM_LIST_OF_SET; FINITE_VFREE_IN_2] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM]; ALL_TAC] THEN
  EXISTS_TAC `pick_names c [] vars` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[unique_varnames_def] THEN
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty1:hol_type`; `ty2:hol_type`] THEN
    MP_TAC(ISPECL [`c:hol_term`; `x:mlstring`; `ty1:hol_type`; `pick_names c [] vars`]
                  VFREE_IN_VSUBST) THEN
    MP_TAC(ISPECL [`c:hol_term`; `x:mlstring`; `ty2:hol_type`; `pick_names c [] vars`]
                  VFREE_IN_VSUBST) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y1:mlstring`; `t1:hol_type`] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`y2:mlstring`; `t2:hol_type`] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`vars:(mlstring#hol_type)list`; `c:hol_term`; `[]:mlstring list`;
                   `y1:mlstring`; `t1:hol_type`; `hol_Var y1 t1`] pick_names_REV_ASSOCD) THEN
    MP_TAC(ISPECL [`vars:(mlstring#hol_type)list`; `c:hol_term`; `[]:mlstring list`;
                   `y2:mlstring`; `t2:hol_type`; `hol_Var y2 t2`] pick_names_REV_ASSOCD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:mlstring` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:mlstring` STRIP_ASSUME_TAC) THEN
    GVS[VFREE_IN_def; injectivity "hol_term"] THEN
    ASM_MESON_TAC[pick_names_targets_inj];
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP pick_names_form) THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`; `n:mlstring`] THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var x ty) c` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[hol_term_ok_def] THEN
    MP_TAC(ISPECL [`sig:sig`; `c:hol_term`; `hol_Var x ty`] term_ok_VFREE_IN) THEN
    ASM_REWRITE_TAC[hol_term_ok_def];
    MATCH_ACCEPT_TAC(SPECL [`vars:(mlstring#hol_type)list`; `c:hol_term`; `[]:mlstring list`]
                           pick_names_targets_inj);
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP pick_names_form) THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (hol_Var nm ty0,v) (pick_names c [] vars)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP pick_names_fresh) THEN MESON_TAC[VFREE_IN_tm_names];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP pick_names_form) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`vars:(mlstring#hol_type)list`; `c:hol_term`; `[]:mlstring list`]
                  pick_names_sources_inj) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_MESON_TAC[]]);;

(* HOL4 val ilist_r_thms *)
let CLITAUX_ilist_r_thms =
  [MEM_MAP; LAMBDA_PROD; EXISTS_PROD; FORALL_PROD; CLITAUX_SWAP_def; MEM_FILTER];;

let INST_equation = prove
 (`!sig a b tyin.
     hol_term_ok sig a /\ hol_term_ok sig b /\
     ALL (type_ok (FST sig)) (MAP FST tyin)
     ==> INST tyin (a === b) = INST tyin a === INST tyin b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped a /\ welltyped b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `typeof (INST tyin a) = TYPE_SUBST tyin (typeof a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INST_HAS_TYPE; WELLTYPED; has_type_typeof]; ALL_TAC] THEN
  SUBGOAL_THEN
   `welltyped (hol_Comb (hol_Const (implode "=")
      (Tyapp (implode "fun") [typeof a; Tyapp (implode "fun") [typeof a;
         Tyapp (implode "bool") []]])) a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[equation_def] THEN ASM_SIMP_TAC[INST_COMB; WELLTYPED_CLAUSES] THEN
  REWRITE_TAC[INST_def; INST_CORE_def; RESULT_def; TYPE_SUBST_def; MAP; TYPE_SUBST_Bool] THEN
  ASM_REWRITE_TAC[GSYM INST_def]);;

let apply_steps_equation = prove
 (`!sig x y stps.
     hol_term_ok sig x /\ hol_term_ok sig y /\ steps_ok sig stps
     ==> apply_steps stps (x === y) = apply_steps stps x === apply_steps stps y`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[apply_steps_def] THEN
  QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `apply_steps t (x === y) = apply_steps t x === apply_steps t y`
     SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  FIRST [MATCH_MP_TAC VSUBST_equation; MATCH_MP_TAC INST_equation] THEN
  EXISTS_TAC `sig:sig` THEN ASM_SIMP_TAC[apply_steps_term_ok] THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLITAUX_ilist_wk));;

(* HOL4 val eqn_dist_tac *)
let CLITAUX_eqn_dist_tac =
  DEP_REWRITE_TAC[apply_steps_equation; esubst_equation; VSUBST_equation; INST_equation] THEN
  SIMP[apply_steps_term_ok];;

let REV_ASSOCD_UNIQUE_MEM = prove
 (`!(a:A) (k:B) d l.
     MEM (a,k) l /\ (!v. MEM (v,k) l ==> v = a) ==> REV_ASSOCD k l d = a`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[REV_ASSOCD; MEM; PAIR_EQ] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* REV_ASSOCD through a MAP that changes the values only *)
let CLITAUX_REV_ASSOCD_MAP_VAL = prove
 (`!(l:(A#B)list) k (g:A->A) d.
     (?v0. MEM (v0,k) l)
     ==> ?v. MEM (v,k) l /\ REV_ASSOCD k (MAP (\(s',s). (g s',s)) l) d = g v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN PAIR_CASES_ON `h:A#B` THEN
  REWRITE_TAC[MAP; MEM; PAIR_EQ] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[REV_ASSOCD] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let CLITAUX_REV_ASSOCD_MAP_NONE = prove
 (`!(l:(A#B)list) k (g:A->A) d.
     ~(?v0. MEM (v0,k) l) ==> REV_ASSOCD k (MAP (\(s',s). (g s',s)) l) d = d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; REV_ASSOCD] THEN PAIR_CASES_ON `h:A#B` THEN
  REWRITE_TAC[MAP; MEM; PAIR_EQ] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[REV_ASSOCD] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let CLITAUX_MEM_MAP_SWAP = prove
 (`!(l:(A#B)list) x y. MEM (x,y) (MAP CLITAUX_SWAP l) <=> MEM (y,x) l`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; CLITAUX_SWAP_def; PAIR_EQ] THEN MESON_TAC[]);;

let VSUBST_inverse_ACONV = prove
 (`!sig c ilist_r.
     hol_term_ok sig c /\
     (!t s. MEM (t,s) ilist_r
            ==> ?x ty y. s = hol_Var x ty /\ t = hol_Var y ty /\
                         hol_term_ok sig t /\ VFREE_IN s c) /\
     (!n ty1 s1 ty2 s2.
        MEM (hol_Var n ty1,s1) ilist_r /\ MEM (hol_Var n ty2,s2) ilist_r
        ==> ty1 = ty2 /\ s1 = s2) /\
     (!n ty s. MEM (hol_Var n ty,s) ilist_r ==> ~VFREE_IN (hol_Var n ty) c)
     ==> ACONV c (VSUBST (MAP CLITAUX_SWAP ilist_r) (VSUBST ilist_r c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H2")
             (CONJUNCTS_THEN2 (LABEL_TAC "H3") (LABEL_TAC "H4")))) THEN
  ABBREV_TAC `w = MAP CLITAUX_SWAP (ilist_r:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!s' s. MEM (s',s) w <=> MEM (s,s') (ilist_r:(hol_term#hol_term)list)`
    ASSUME_TAC THENL [EXPAND_TAC "w" THEN REWRITE_TAC[CLITAUX_MEM_MAP_SWAP]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped c` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `!t s. MEM (t,s) ilist_r
                      ==> ?x ty y. s = hol_Var x ty /\ t = hol_Var y ty /\
                                   type_ok (FST (sig:sig)) ty /\ VFREE_IN s c`
    (LABEL_TAC "H2'") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> REMOVE_THEN "H2" (MP_TAC o C MATCH_MP th)) THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`; `y:mlstring`] THEN
    UNDISCH_TAC `hol_term_ok (sig:sig) t` THEN ASM_REWRITE_TAC[hol_term_ok_def]; ALL_TAC] THEN
  ABBREV_TAC `ilist1 = APPEND (MAP (\(s',s). (VSUBST w s',s)) ilist_r)
                              (FILTER (\(s',s). ~MEM s (MAP SND ilist_r)) w)` THEN
  MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `VSUBST ilist1 c` THEN CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "ilist1" THEN MATCH_MP_TAC VSUBST_VSUBST_ACONV THEN EXISTS_TAC `sig:sig` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "H2'" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[has_type_rules]] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (w:(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty` (LABEL_TAC "W") THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun m -> USE_THEN "H2'" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[has_type_rules]; ALL_TAC] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) ilist1 ==> ?x ty. k = hol_Var x ty /\ v has_type ty`
    (LABEL_TAC "I1") THENL
   [EXPAND_TAC "ilist1" THEN REWRITE_TAC[MEM_APPEND; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM;
                                         PAIR_EQ] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(fun m -> USE_THEN "H2'" (fun h -> MP_TAC(MATCH_MP h m))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"] THEN
      MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[has_type_rules];
      USE_THEN "W" (fun h -> FIRST_ASSUM(MP_TAC o MATCH_MP h)) THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x ty. VFREE_IN (hol_Var x ty) c
                       ==> REV_ASSOCD (hol_Var x ty) ilist1 (hol_Var x ty) = hol_Var x ty`
    (LABEL_TAC "CORE") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ilist1" THEN REWRITE_TAC[REV_ASSOCD_APPEND] THEN
    ASM_CASES_TAC `?t. MEM (t,hol_Var x ty) (ilist_r:(hol_term#hol_term)list)` THENL
     [MP_TAC(ISPECL [`ilist_r:(hol_term#hol_term)list`; `hol_Var x ty`; `VSUBST w`;
        `REV_ASSOCD (hol_Var x ty)
           (FILTER (\(s',s). ~MEM s (MAP SND (ilist_r:(hol_term#hol_term)list))) w)
           (hol_Var x ty)`] CLITAUX_REV_ASSOCD_MAP_VAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:hol_term` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun m -> USE_THEN "H2'" (fun h -> MP_TAC(MATCH_MP h m))) THEN
      REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[VSUBST_def] THEN MATCH_MP_TAC REV_ASSOCD_UNIQUE_MEM THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `MEM (v,hol_Var x ty) (ilist_r:(hol_term#hol_term)list)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "H3" MP_TAC THEN MESON_TAC[];
      MP_TAC(ISPECL [`ilist_r:(hol_term#hol_term)list`; `hol_Var x ty`; `VSUBST w`;
        `REV_ASSOCD (hol_Var x ty)
           (FILTER (\(s',s). ~MEM s (MAP SND (ilist_r:(hol_term#hol_term)list))) w)
           (hol_Var x ty)`] CLITAUX_REV_ASSOCD_MAP_NONE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REV_ASSOCD_EQ_DEFAULT_i THEN
      ASM_REWRITE_TAC[MEM_FILTER] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun m -> USE_THEN "H4" (fun h -> MP_TAC(MATCH_MP h m))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST ilist1 c)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[] THEN USE_THEN "I1" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:hol_term`; `VSUBST ilist1 c`] ACONV_db) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`c:hol_term`; `ilist1:(hol_term#hol_term)list`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun m -> USE_THEN "I1" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[welltyped_def];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM dbVSUBST_nil] THEN
  MATCH_MP_TAC dbVSUBST_frees THEN X_GEN_TAC `k:dbterm` THEN DISCH_TAC THEN
  REWRITE_TAC[REV_ASSOCD] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) (ilist1:(hol_term#hol_term)list) ==> ?x ty. k = hol_Var x ty`
    (LABEL_TAC "K") THENL
   [USE_THEN "I1" MP_TAC THEN MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `dbVFREE_IN k (hol_db c)` THEN QCASES_ON "k" THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`ilist1:(hol_term#hol_term)list`; `a0:mlstring`; `a1:hol_type`]
                  REV_ASSOCD_MAP_db) THEN
    ANTS_TAC THENL [USE_THEN "K" MATCH_ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `VFREE_IN (hol_Var a0 a1) c`
      (fun th -> USE_THEN "CORE" (fun h -> REWRITE_TAC[MATCH_MP h th; hol_db_def])) THEN
    MP_TAC(ISPECL [`c:hol_term`; `hol_Var a0 a1`] dbVFREE_IN_VFREE_IN) THEN
    ASM_REWRITE_TAC[hol_db_def];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REV_ASSOCD_EQ_DEFAULT_i THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  USE_THEN "K" (fun h -> FIRST_ASSUM(MP_TAC o MATCH_MP h)) THEN STRIP_TAC THEN
  GVS[hol_db_def]);;

let VFREE_IN_VSUBST_UNIQUE_MEM = prove
 (`!n ty sx sty tm ilist.
     welltyped tm /\
     VFREE_IN (hol_Var sx sty) tm /\
     MEM (hol_Var n ty,hol_Var sx sty) ilist /\
     (!v'. MEM (v',hol_Var sx sty) ilist ==> v' = hol_Var n ty)
     ==> VFREE_IN (hol_Var n ty) (VSUBST ilist tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tm:hol_term`; `n:mlstring`; `ty:hol_type`;
                 `ilist:(hol_term#hol_term)list`] VFREE_IN_VSUBST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`sx:mlstring`; `sty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `REV_ASSOCD (hol_Var sx sty) ilist (hol_Var sx sty) = hol_Var n ty`
    SUBST1_TAC THENL
   [MATCH_MP_TAC REV_ASSOCD_UNIQUE_MEM THEN ASM_REWRITE_TAC[]; REWRITE_TAC[VFREE_IN_def]]);;

let REV_ASSOCD_dbINST = prove
 (`!ilistdb x ty tyin.
     (!t ty'. MEM (t,dbVar x ty') ilistdb ==> ty' = ty)
     ==> dbINST tyin (REV_ASSOCD (dbVar x ty) ilistdb (dbVar x ty)) =
         REV_ASSOCD (dbVar x (TYPE_SUBST tyin ty))
                    (MAP (\(t,s). (dbINST tyin t,dbINST tyin s)) ilistdb)
                    (dbVar x (TYPE_SUBST tyin ty))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD; MAP; dbINST_def] THEN
  PAIR_CASES_ON `h:dbterm#dbterm` THEN REWRITE_TAC[MAP; REV_ASSOCD; MEM; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[REV_ASSOCD] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `h1 = dbVar x ty` THEN ASM_REWRITE_TAC[dbINST_def] THEN
  SUBGOAL_THEN `~(dbINST tyin h1 = dbVar x (TYPE_SUBST tyin ty))`
    (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_TAC THEN SUBGOAL_THEN `?ty'. h1 = dbVar x ty'` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `dbINST tyin h1 = dbVar x (TYPE_SUBST tyin ty)` THEN QCASES_ON "h1" THEN
      REWRITE_TAC[dbINST_def; injectivity "dbterm"; distinctness "dbterm"] THEN MESON_TAC[];
      ASM_MESON_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let dbINST_dbVSUBST_comm = prove
 (`!dbtm ilistdb tyin.
     (!x ty1 ty2. dbVFREE_IN (dbVar x ty1) dbtm /\
                  dbVFREE_IN (dbVar x ty2) dbtm ==> ty1 = ty2) /\
     (!t x ty. MEM (t,dbVar x ty) ilistdb ==> dbVFREE_IN (dbVar x ty) dbtm)
     ==> dbINST tyin (dbVSUBST ilistdb dbtm) =
         dbVSUBST (MAP (\(t,s). (dbINST tyin t,dbINST tyin s)) ilistdb)
                  (dbINST tyin dbtm)`,
  SUBGOAL_THEN
   `!dbtm ilistdb tyin.
      (!x ty. dbVFREE_IN (dbVar x ty) dbtm
              ==> !ty'. (?t. MEM (t,dbVar x ty') ilistdb) ==> ty' = ty)
      ==> dbINST tyin (dbVSUBST ilistdb dbtm) =
          dbVSUBST (MAP (\(t,s). (dbINST tyin t,dbINST tyin s)) ilistdb)
                   (dbINST tyin dbtm)`
   (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[dbVSUBST_def; dbINST_def; dbVFREE_IN_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[injectivity "dbterm"] THENL
   [MATCH_MP_TAC REV_ASSOCD_dbINST THEN ASM_MESON_TAC[];
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let CLITAUX_INST_Var = prove
 (`!tyin x ty. INST tyin (hol_Var x ty) = hol_Var x (TYPE_SUBST tyin ty)`,
  REWRITE_TAC[INST_def; INST_CORE_def; LET_DEF; LET_END_DEF; REV_ASSOCD; RESULT_def]);;

let INST_VSUBST_ACONV = prove
 (`!tm ilist tyin.
     welltyped tm /\ unique_varnames tm /\
     (!t s. MEM (t,s) ilist ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\ VFREE_IN s tm)
     ==> ACONV (INST tyin (VSUBST ilist tm))
               (VSUBST (MAP (\(t,s). (INST tyin t,INST tyin s)) ilist) (INST tyin tm))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IL"))) THEN
  SUBGOAL_THEN `!v k. MEM (v,k) (ilist:(hol_term#hol_term)list)
                      ==> welltyped v /\ ?x ty. k = hol_Var x ty` (LABEL_TAC "A") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun m -> USE_THEN "IL" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[welltyped_def]; ALL_TAC] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (ilist:(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty` (LABEL_TAC "B") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun m -> USE_THEN "IL" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `il = MAP (\(t,s). (INST tyin t,INST tyin s)) (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) il ==> ?x ty. s = hol_Var x ty /\ s' has_type ty`
    (LABEL_TAC "C") THENL
   [EXPAND_TAC "il" THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun m -> USE_THEN "B" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CLITAUX_INST_Var; injectivity "hol_term"] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `TYPE_SUBST tyin ty`] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INST_HAS_TYPE THEN EXISTS_TAC `ty:hol_type` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST ilist tm)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[] THEN USE_THEN "B" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST il (INST tyin tm))` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_SIMP_TAC[INST_WELLTYPED] THEN
    USE_THEN "C" MATCH_ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`INST tyin (VSUBST ilist tm)`; `VSUBST il (INST tyin tm)`] ACONV_db) THEN
  ASM_SIMP_TAC[INST_WELLTYPED] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[INST_dbINST] THEN
  MP_TAC(ISPECL [`tm:hol_term`; `ilist:(hol_term#hol_term)list`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "A" MATCH_ACCEPT_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`INST tyin tm`; `il:(hol_term#hol_term)list`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INST_WELLTYPED] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun m -> USE_THEN "C" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[welltyped_def];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[INST_dbINST] THEN
  SUBGOAL_THEN
   `MAP (\(x,y). (hol_db x,hol_db y)) il =
    MAP (\(t,s). (dbINST tyin t,dbINST tyin s))
        (MAP (\(x,y). (hol_db x,hol_db y)) (ilist:(hol_term#hol_term)list))`
    SUBST1_TAC THENL
   [EXPAND_TAC "il" THEN REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "A" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[INST_dbINST; WELLTYPED_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC dbINST_dbVSUBST_comm THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`tm:hol_term`; `hol_Var x ty1`] dbVFREE_IN_VFREE_IN) THEN
  MP_TAC(ISPECL [`tm:hol_term`; `hol_Var x ty2`] dbVFREE_IN_VFREE_IN) THEN
  ASM_REWRITE_TAC[hol_db_def] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  UNDISCH_TAC `unique_varnames tm` THEN REWRITE_TAC[unique_varnames_def] THEN MESON_TAC[];
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun m -> USE_THEN "IL" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
  UNDISCH_TAC `dbVar x ty = hol_db p2` THEN ASM_REWRITE_TAC[hol_db_def; injectivity "dbterm"] THEN
  STRIP_TAC THEN MP_TAC(ISPECL [`tm:hol_term`; `hol_Var x ty`] dbVFREE_IN_VFREE_IN) THEN
  ASM_REWRITE_TAC[hol_db_def] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]]);;

let VFREE_IN_INST_imp = prove
 (`!tm x ty tyin.
     welltyped tm /\ VFREE_IN (hol_Var x ty) tm
     ==> VFREE_IN (hol_Var x (TYPE_SUBST tyin ty)) (INST tyin tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  MP_TAC(ISPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                 `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RESULT_def] THEN ASM_MESON_TAC[]);;

let INST_compose_ACONV = prove
 (`!c tyin1 tyin2.
     welltyped c
     ==> ACONV (INST tyin1 (INST tyin2 c))
               (INST (APPEND (MAP (\(ty,a). (TYPE_SUBST tyin1 ty,a)) tyin2) tyin1) c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (INST tyin2 c)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INST_WELLTYPED]; ALL_TAC] THEN
  ASM_SIMP_TAC[ACONV_db; INST_WELLTYPED; INST_dbINST; dbINST_compose]);;

(* apply_steps_3layer, a VStep: VSUBST l of a term ACONV to VSUBST ilist_f tm *)
let CLITAUX_3layer_V = prove
 (`!sig u l tm ilist_f.
     welltyped u /\
     (!s s'. MEM (s',s) l
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s') /\
     hol_term_ok sig tm /\
     ACONV u (VSUBST ilist_f tm) /\
     (!t s. MEM (t,s) ilist_f
            ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\ hol_term_ok sig t /\
                       VFREE_IN s tm)
     ==> ?ilist_f'.
           ACONV (VSUBST l u) (VSUBST ilist_f' tm) /\
           (!t s. MEM (t,s) ilist_f'
                  ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\ hol_term_ok sig t /\
                             VFREE_IN s tm)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))))) THEN
  ABBREV_TAC `X = APPEND (MAP (\(t,s). (VSUBST l t,s)) (ilist_f:(hol_term#hol_term)list))
                         (FILTER (\(t,s). ~MEM s (MAP SND ilist_f)) l)` THEN
  EXISTS_TAC `FILTER (\(t:hol_term,s). VFREE_IN s tm) X` THEN
  SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (ilist_f:(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s'`
    (LABEL_TAC "F'") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun m -> USE_THEN "F" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `VSUBST l (VSUBST ilist_f tm)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ACONV_VSUBST THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "F'" (MATCH_ACCEPT_TAC o MATCH_MP CLITAUX_ilist_wk);
        REPEAT GEN_TAC THEN DISCH_THEN(fun m -> USE_THEN "L" (fun h -> MP_TAC(MATCH_MP h m))) THEN
        MESON_TAC[]];
      MP_TAC(ISPECL [`sig:sig`; `tm:hol_term`; `X:(hol_term#hol_term)list`]
                    VSUBST_FILTER_VFREE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "X" THEN
      MATCH_MP_TAC ACONV_SYM THEN MATCH_MP_TAC VSUBST_VSUBST_ACONV THEN
      EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[]];
    EXPAND_TAC "X" THEN REWRITE_TAC[MEM_FILTER; MEM_APPEND; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(fun m -> USE_THEN "F" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "L" (MATCH_ACCEPT_TAC o MATCH_MP CLITAUX_ilist_wk);
      MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM(fun m -> USE_THEN "L" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[]]]);;

(* apply_steps_3layer, a TStep *)
let CLITAUX_3layer_T = prove
 (`!sig u l tm0 tyin ilist_f.
     welltyped u /\
     ALL (type_ok (FST sig)) (MAP FST l) /\
     hol_term_ok sig tm0 /\ unique_varnames tm0 /\
     ALL (type_ok (FST sig)) (MAP FST tyin) /\
     ACONV u (VSUBST ilist_f (INST tyin tm0)) /\
     (!t s. MEM (t,s) ilist_f
            ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\ hol_term_ok sig t /\
                       VFREE_IN s (INST tyin tm0))
     ==> ACONV (INST l u)
               (VSUBST (MAP (\(t,s). (INST l t,INST l s)) ilist_f)
                  (INST (APPEND (MAP (\(ty,a). (TYPE_SUBST l ty,a)) tyin) l) tm0)) /\
         (!t s. MEM (t,s) (MAP (\(t,s). (INST l t,INST l s)) ilist_f)
                ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\ hol_term_ok sig t /\
                           VFREE_IN s (INST (APPEND (MAP (\(ty,a). (TYPE_SUBST l ty,a)) tyin) l)
                                            tm0)) /\
         ALL (type_ok (FST sig)) (MAP FST (APPEND (MAP (\(ty,a). (TYPE_SUBST l ty,a)) tyin) l))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))))))) THEN
  ABBREV_TAC `tm = INST tyin tm0` THEN
  ABBREV_TAC `tyin' = APPEND (MAP (\(ty,a). (TYPE_SUBST l ty,a)) tyin) l` THEN
  ABBREV_TAC `il = MAP (\(t,s). (INST l t,INST l s)) (ilist_f:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `welltyped tm0` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL
   [EXPAND_TAC "tm" THEN ASM_SIMP_TAC[INST_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `ACONV (INST l tm) (INST tyin' tm0)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tm"; "tyin'"] THEN MATCH_MP_TAC INST_compose_ACONV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t s. MEM (t,s) il
                      ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\ hol_term_ok sig t /\
                                 VFREE_IN s (INST tyin' tm0)` (LABEL_TAC "G") THENL
   [EXPAND_TAC "il" THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "F" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CLITAUX_INST_Var; injectivity "hol_term"] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `TYPE_SUBST l ty`] THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INST_HAS_TYPE THEN EXISTS_TAC `ty:hol_type` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP VFREE_IN_ACONV th)]) THEN
      MATCH_MP_TAC VFREE_IN_INST_imp THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `INST l (VSUBST ilist_f tm)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_INST THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUBST_WELLTYPED THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "F" MP_TAC THEN MESON_TAC[];
    MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `VSUBST il (INST l tm)` THEN CONJ_TAC THENL
     [EXPAND_TAC "il" THEN MATCH_MP_TAC INST_VSUBST_ACONV THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "tm" THEN MATCH_MP_TAC unique_varnames_INST THEN ASM_REWRITE_TAC[];
        USE_THEN "F" MP_TAC THEN MESON_TAC[]];
      MATCH_MP_TAC ACONV_VSUBST THEN ASM_SIMP_TAC[INST_WELLTYPED] THEN
      USE_THEN "G" MP_TAC THEN MESON_TAC[]]];
    EXPAND_TAC "tyin'" THEN ASM_REWRITE_TAC[MAP_APPEND; ALL_APPEND] THEN
  UNDISCH_TAC `ALL (type_ok (FST (sig:sig))) (MAP FST (tyin:(hol_type#hol_type)list))` THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_MESON_TAC[]]);;

let apply_steps_3layer = prove
 (`!sig steps c.
     hol_term_ok sig c /\ steps_ok sig steps
     ==> ?ilist_r tyin ilist_f.
           ACONV (apply_steps steps c) (VSUBST ilist_f (INST tyin (VSUBST ilist_r c))) /\
           unique_varnames (VSUBST ilist_r c) /\
           (!t s. MEM (t,s) ilist_r
                  ==> ?x ty y. s = hol_Var x ty /\ t = hol_Var y ty /\
                               hol_term_ok sig t /\ VFREE_IN s c) /\
           (!t s. MEM (t,s) ilist_f
                  ==> ?x ty. s = hol_Var x ty /\ t has_type ty /\
                             hol_term_ok sig t /\
                             VFREE_IN s (INST tyin (VSUBST ilist_r c))) /\
           ALL (type_ok (FST sig)) (MAP FST tyin) /\
           (!nm ty0 v. MEM (hol_Var nm ty0,v) ilist_r ==> ~VFREE_IN (hol_Var nm ty0) c)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THENL
   [X_GEN_TAC `c:hol_term` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP rename_to_unique_varnames) THEN
    DISCH_THEN(X_CHOOSE_THEN `ilist_r:(hol_term#hol_term)list`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "R")
       (CONJUNCTS_THEN2 (LABEL_TAC "TI") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SI")))))) THEN
    SUBGOAL_THEN `welltyped c` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
    SUBGOAL_THEN `welltyped (VSUBST ilist_r c)` ASSUME_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m))) THEN
      MESON_TAC[has_type_rules]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ilist_r:(hol_term#hol_term)list`; `[]:(hol_type#hol_type)list`;
                          `MAP CLITAUX_SWAP (ilist_r:(hol_term#hol_term)list)`] THEN
    SUBGOAL_THEN `INST [] (VSUBST ilist_r c) = VSUBST ilist_r c` SUBST1_TAC THENL
     [MATCH_MP_TAC(GEN_ALL INST_nil) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MAP; ALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_inverse_ACONV THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CLITAUX_MEM_MAP_SWAP] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m) THEN ASSUME_TAC m)) THEN
      STRIP_TAC THEN RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`y:mlstring`; `ty:hol_type`] THEN
      UNDISCH_TAC `hol_term_ok (sig:sig) (hol_Var y ty)` THEN
      REWRITE_TAC[hol_term_ok_def; has_type_rules] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VFREE_IN_VSUBST_UNIQUE_MEM THEN
      MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN DISCH_TAC THEN USE_THEN "SI" MATCH_MP_TAC THEN
      EXISTS_TAC `hol_Var x ty` THEN ASM_REWRITE_TAC[]];
    QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN
    X_GEN_TAC `c:hol_term` THEN STRIP_TAC THEN
    LAST_X_ASSUM(MP_TAC o SPEC `c:hol_term`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ilist_r:(hol_term#hol_term)list`
      (X_CHOOSE_THEN `tyin:(hol_type#hol_type)list`
        (X_CHOOSE_THEN `ilist_f:(hol_term#hol_term)list`
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 (LABEL_TAC "R") (CONJUNCTS_THEN2 (LABEL_TAC "F")
              (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
    (SUBGOAL_THEN `welltyped (apply_steps t c)` ASSUME_TAC THENL
      [MATCH_MP_TAC apply_steps_welltyped THEN EXISTS_TAC `sig:sig` THEN
       ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC]) THEN
    (SUBGOAL_THEN `hol_term_ok sig (VSUBST ilist_r c)` ASSUME_TAC THENL
      [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
       DISCH_THEN(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m))) THEN
       MESON_TAC[has_type_rules]; ALL_TAC]) THENL
     [MP_TAC(ISPECL [`sig:sig`; `apply_steps t c`; `a:(hol_term#hol_term)list`;
                      `INST tyin (VSUBST ilist_r c)`; `ilist_f:(hol_term#hol_term)list`]
                     CLITAUX_3layer_V) THEN
       ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `ilist_f':(hol_term#hol_term)list` STRIP_ASSUME_TAC) THEN
       MAP_EVERY EXISTS_TAC [`ilist_r:(hol_term#hol_term)list`; `tyin:(hol_type#hol_type)list`;
                             `ilist_f':(hol_term#hol_term)list`] THEN
       ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`sig:sig`; `apply_steps t c`; `a:(hol_type#hol_type)list`;
                      `VSUBST ilist_r c`; `tyin:(hol_type#hol_type)list`;
                      `ilist_f:(hol_term#hol_term)list`] CLITAUX_3layer_T) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
       MAP_EVERY EXISTS_TAC [`ilist_r:(hol_term#hol_term)list`;
                             `APPEND (MAP (\(ty,b). (TYPE_SUBST a ty,b)) tyin) a`;
                             `MAP (\(t,s). (INST a t,INST a s))
                                  (ilist_f:(hol_term#hol_term)list)`] THEN
       ASM_REWRITE_TAC[]]]);;

let CLITAUX_esubsts_ok_FLOOKUP = prove
 (`!sig sigma0 sigma1 n repl decl.
     esubsts_ok sig (sigma0,sigma1) /\ FLOOKUP sigma1 n = SOME (repl,decl)
     ==> FLOOKUP (SND sig) n = SOME decl /\ CLOSED repl /\ welltyped repl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[esubsts_ok_def; flookup_thm] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:mlstring`) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[term_ok_welltyped]);;

let VFREE_IN_esubst_ty0 = prove
 (`!sig x ty env sigma avds tm subst_tm.
     hol_term_ok sig tm /\ esubsts_ok sig sigma /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty)) /\
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
     ==> (VFREE_IN (hol_Var x ty) (esubst_tm sigma subst_tm) <=>
          VFREE_IN (hol_Var x ty) subst_tm)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REC_IND_TAC esubst_ty0_ind THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def; LET_DEF; LET_END_DEF] THEN
      COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def];
    REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def; injectivity "error"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      PAIR_CASES_ON `sigma:(mlstring,mlstring list#hol_type)fmap#
                         (mlstring,hol_term#hol_type)fmap` THEN
      REWRITE_TAC[esubst_tm_def; VFREE_IN_def; distinctness "hol_term"] THEN
      TOP_CASE_TAC THEN REWRITE_TAC[VFREE_IN_def; distinctness "hol_term"] THEN
      TOP_CASE_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[VFREE_IN_def; distinctness "hol_term"] THENL
       [FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
         MP_TAC(MATCH_MP CLITAUX_esubsts_ok_FLOOKUP (CONJ th th2)))) THEN STRIP_TAC THEN
      UNDISCH_TAC `hol_term_ok sig (hol_Const n ty')` THEN
      ASM_REWRITE_TAC[hol_term_ok_def; injectivity "option"] THEN STRIP_TAC THEN
        RVEQ_TAC THEN
      MP_TAC(ISPECL [`ty0:hol_type`; `i:(hol_type#hol_type)list`; `FST (sig:sig)`; `SND (sig:sig)`;
                     `(sigma0,sigma1):(mlstring,mlstring list#hol_type)fmap#
                                      (mlstring,hol_term#hol_type)fmap`] ty_esubst_TYPE_SUBST) THEN
      ASM_REWRITE_TAC[PAIR] THEN
      DISCH_THEN(X_CHOOSE_TAC `i':(hol_type#hol_type)list`) THEN
      MP_TAC(ISPECL [`ty_esubst ((sigma0,sigma1):(mlstring,mlstring list#hol_type)fmap#
                                                 (mlstring,hol_term#hol_type)fmap) ty0`;
                     `ty_esubst ((sigma0,sigma1):(mlstring,mlstring list#hol_type)fmap#
                                                 (mlstring,hol_term#hol_type)fmap)
                        (TYPE_SUBST i ty0)`] match_type_complete) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[distinctness "option"]];
        FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
         MP_TAC(MATCH_MP CLITAUX_esubsts_ok_FLOOKUP (CONJ th th2)))) THEN STRIP_TAC THEN
      MATCH_MP_TAC(GEN_ALL(MESON[CLOSED_def]
        `CLOSED t ==> ~VFREE_IN (hol_Var x ty) t`)) THEN
      MATCH_MP_TAC CLOSED_INST THEN ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
      GEN_TAC THEN REWRITE_TAC[esubst_ty0_def; bind_EQ_return; hol_term_ok_def;
                               injectivity "error"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def; VFREE_IN_def] THEN
      REMOVE_THEN "IH1" (MP_TAC o SPEC `u:hol_term`) THEN
      REMOVE_THEN "IH2" (MP_TAC o SPEC `u':hol_term`) THEN
      ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    REPEAT GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHR")
        (CONJUNCTS_THEN2 (LABEL_TAC "IH0") (LABEL_TAC "IHE"))) THEN
      GEN_TAC THEN REWRITE_TAC[hol_term_ok_def] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n0:mlstring` (X_CHOOSE_THEN `t0:hol_type`
        STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      UNDISCH_TAC `esubst_ty0 env sigma avds (hol_Abs (hol_Var n0 t0) body) =
                   errorMonad_return subst_tm` THEN
      ONCE_REWRITE_TAC[esubst_ty0_def] THEN
      REWRITE_TAC[dest_var_def; pair_CASE; LET_DEF; LET_END_DEF; try_eq_return] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[bind_EQ_return; COND_CASE_EQ; distinctness "error"; injectivity "error"] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def; VFREE_IN_def] THEN
      REMOVE_THEN "IHE" (MP_TAC o SPECL [`n0:mlstring`; `t0:hol_type`]) THEN
      REWRITE_TAC[dest_var_def] THEN DISCH_THEN(MP_TAC o SPEC `u:hol_term`) THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def; VFREE_IN_def] THEN
      REMOVE_THEN "IH0" (K ALL_TAC) THEN
      REMOVE_THEN "IHR"
        (MP_TAC o SPECL [`e:hol_term`; `u:hol_term`; `n0:mlstring`; `t0:hol_type`]) THEN
      ASM_REWRITE_TAC[dest_var_def] THEN DISCH_THEN(MP_TAC o SPEC `u':hol_term`) THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[hol_term_ok_def] THEN
          MESON_TAC[has_type_rules];
          REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"] THEN
          ASM_MESON_TAC[]];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]]]);;

let esubst_not_VFREE_IN = prove
 (`!sig sigma tm x ty.
     esubsts_ok sig sigma /\ hol_term_ok sig tm /\
     ~VFREE_IN (hol_Var x ty) tm /\
     (!oty. VFREE_IN (hol_Var x oty) tm /\ ty_esubst sigma oty = ty_esubst sigma ty
            ==> oty = ty)
     ==> ~VFREE_IN (hol_Var x (ty_esubst sigma ty)) (esubst sigma [] tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                 `tm:hol_term`; `sig:sig`; `[]:mlstring list`] esubst_ty0_always_returns) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `tm1:hol_term`) THEN
  UNDISCH_TAC `VFREE_IN (hol_Var x (ty_esubst sigma ty)) (esubst sigma [] tm)` THEN
  ASM_REWRITE_TAC[esubst_def; esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sig:sig`; `x:mlstring`;
                 `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap) ty`;
                 `[]:(hol_term#hol_term)list`;
                 `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                 `[]:mlstring list`; `tm:hol_term`; `tm1:hol_term`] VFREE_IN_esubst_ty0) THEN
  ASM_REWRITE_TAC[MEM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`sig:sig`; `[]:(hol_term#hol_term)list`;
                 `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                 `[]:mlstring list`; `tm:hol_term`; `tm1:hol_term`] esubst_ty0_all_free) THEN
  ASM_REWRITE_TAC[MEM] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let unique_varnames_comb = prove
 (`!x y. unique_varnames (hol_Comb x y) ==> unique_varnames x /\ unique_varnames y`,
  REWRITE_TAC[unique_varnames_def; VFREE_IN_def] THEN MESON_TAC[]);;

let unique_varnames_equation = prove
 (`!x y. unique_varnames (x === y) ==> unique_varnames x /\ unique_varnames y`,
  REWRITE_TAC[equation_def] THEN MESON_TAC[unique_varnames_comb]);;

let REV_ASSOCD_ID = prove
 (`!(x:A) ilist. (!k v. MEM (v,k) ilist ==> x = v) ==> REV_ASSOCD x ilist x = x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD; MEM] THEN
  PAIR_CASES_ON `h:A#A` THEN REWRITE_TAC[REV_ASSOCD; MEM; PAIR_EQ] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* esubst commutes past VSUBST o INST up to ACONV, combining
   esubst_INST_comm and esubst_VSUBST_comm into one result. *)
let esubst_INST_VSUBST_ACONV = prove
 (`!sig axs sigma t tyin ilist.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     hol_term_ok sig t /\ unique_varnames t /\
     ALL (type_ok (FST sig)) (MAP FST tyin) /\
     (!s' s. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\
                        hol_term_ok sig s' /\
                        VFREE_IN s (INST tyin t))
     ==> ACONV (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist)
                       (INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin)
                             (esubst sigma [] t)))
               (esubst sigma [] (VSUBST ilist (INST tyin t)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IL")))))) THEN
  SUBGOAL_THEN `welltyped t` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (INST tyin t)` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ACONV_TRANS THEN
  EXISTS_TAC `VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist)
                     (esubst sigma [] (INST tyin t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_VSUBST THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INST_WELLTYPED THEN MATCH_MP_TAC esubst_welltyped THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_welltyped THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun m -> USE_THEN "IL" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[esubst_ty_var; injectivity "hol_term"] THEN
      MAP_EVERY EXISTS_TAC [`x:mlstring`;
        `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                          (mlstring,hol_term#hol_type)fmap) ty`] THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC esubst_has_type1 THEN EXISTS_TAC `sig:sig` THEN
      EXISTS_TAC `axs:hol_term->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ACONV_SYM THEN MATCH_MP_TAC esubst_INST_comm THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC esubst_VSUBST_comm THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC unique_varnames_no_var_collapse THEN
    MATCH_MP_TAC unique_varnames_INST THEN ASM_REWRITE_TAC[]]);;

let axiom_steps_derivable = prove
 (`!sig axs sigma stps c.
     theory_ok (sig,axs) /\
     c IN axs /\
     no_var_collapse sigma c /\
     esubsts_ok sig sigma /\
     steps_ok sig stps
     ==> ((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),[]) |-
         esubst sigma [] (apply_steps stps c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok sig c` ASSUME_TAC THENL
   [UNDISCH_TAC `theory_ok (sig,axs)` THEN REWRITE_TAC[theory_ok_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `stps:subst_step list`; `c:hol_term`] apply_steps_3layer) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ilist_r:(hol_term#hol_term)list`
    (X_CHOOSE_THEN `tyin:(hol_type#hol_type)list`
      (X_CHOOSE_THEN `ilist_f:(hol_term#hol_term)list`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (LABEL_TAC "R") (CONJUNCTS_THEN2 (LABEL_TAC "F")
            (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `theory_ok (esubst_sig sigma sig,IMAGE (esubst sigma []) axs)` ASSUME_TAC THENL
   [MATCH_MP_TAC theory_ok_esubst_axs THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (VSUBST ilist_r c)` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[has_type_rules]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (INST tyin (VSUBST ilist_r c))` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (VSUBST ilist_f (INST tyin (VSUBST ilist_r c)))` ASSUME_TAC
  THENL
   [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun m -> USE_THEN "F" (fun h -> MP_TAC(MATCH_MP h m))) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (apply_steps stps c)` ASSUME_TAC THENL
   [MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),[]) |- esubst sigma [] c`
    ASSUME_TAC THENL
   [MATCH_MP_TAC proves_axioms THEN ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),[]) |-
    VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_r)
           (esubst sigma [] c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`esubst sigma [] c`; `[]:hol_term list`;
      `MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
           (ilist_r:(hol_term#hol_term)list)`;
      `(esubst_sig sigma sig,IMAGE (esubst sigma []) axs):thy`] proves_INST) THEN
    ASM_REWRITE_TAC[term_image_thm] THEN ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[esubst_var; esubst_ty_var; injectivity "hol_term"; hol_term_ok_def;
                    tysof_esubst_sig] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`;
      `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
                 ty`] THEN
    REWRITE_TAC[has_type_rules] THEN MATCH_MP_TAC esubsts_ok_type_ok THEN
    UNDISCH_TAC `hol_term_ok (sig:sig) p1` THEN ASM_REWRITE_TAC[hol_term_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),[]) |-
    INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin)
      (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_r)
              (esubst sigma [] c))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
                                (ilist_r:(hol_term#hol_term)list))
                           (esubst sigma [] c)`; `[]:hol_term list`;
      `(esubst_sig sigma sig,IMAGE (esubst sigma []) axs):thy`;
      `MAP (\(ty,a). (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                       (mlstring,hol_term#hol_type)fmap) ty,a))
           (tyin:(hol_type#hol_type)list)`] proves_INST_TYPE) THEN
    ASM_REWRITE_TAC[term_image_thm] THEN ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
    REWRITE_TAC[tysof_esubst_sig; MAP_MAP_o] THEN
    UNDISCH_TAC `ALL (type_ok (FST (sig:sig))) (MAP FST (tyin:(hol_type#hol_type)list))` THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC esubsts_ok_type_ok THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((esubst_sig sigma sig,IMAGE (esubst sigma []) axs),[]) |-
    VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_f)
      (INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin)
        (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_r)
                (esubst sigma [] c)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin)
        (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
                     (ilist_r:(hol_term#hol_term)list))
                (esubst sigma [] c))`; `[]:hol_term list`;
      `MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
           (ilist_f:(hol_term#hol_term)list)`;
      `(esubst_sig sigma sig,IMAGE (esubst sigma []) axs):thy`] proves_INST) THEN
    ASM_REWRITE_TAC[term_image_thm] THEN ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "F" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[esubst_ty_var; injectivity "hol_term"] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`;
      `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
                 ty`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC esubst_has_type1 THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `axs:hol_term->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC proves_ACONV_concl THEN
  EXISTS_TAC
   `VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_f)
      (INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin)
        (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_r)
                (esubst sigma [] c)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!tm. hol_term_ok sig tm ==> welltyped (esubst sigma [] tm)` (LABEL_TAC "W") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "W" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k v. MEM (v,k) (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
                         (ilist_r:(hol_term#hol_term)list))
          ==> ?x ty. k = hol_Var x ty /\ v has_type ty` (LABEL_TAC "ILR") THENL
   [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[esubst_var; esubst_ty_var; injectivity "hol_term"] THEN
    MESON_TAC[has_type_rules]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k v. MEM (v,k) (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
                         (ilist_f:(hol_term#hol_term)list))
          ==> ?x ty. k = hol_Var x ty /\ v has_type ty` (LABEL_TAC "ILF") THENL
   [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun m -> USE_THEN "F" (fun h -> MP_TAC(MATCH_MP h m))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[esubst_ty_var; injectivity "hol_term"] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`;
      `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap)
                 ty`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC esubst_has_type1 THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
                                     ilist_r) (esubst sigma [] c))` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN CONJ_TAC THENL
     [USE_THEN "W" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ILR" MP_TAC THEN MESON_TAC[]]; ALL_TAC] THEN
  MATCH_MP_TAC ACONV_TRANS THEN
  EXISTS_TAC `VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist_f)
                     (esubst sigma [] (INST tyin (VSUBST ilist_r c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_VSUBST THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INST_WELLTYPED THEN ASM_REWRITE_TAC[];
      USE_THEN "W" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ILF" MATCH_ACCEPT_TAC;
      MATCH_MP_TAC ACONV_TRANS THEN
      EXISTS_TAC `INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin)
                       (esubst sigma [] (VSUBST ilist_r c))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ACONV_INST THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [USE_THEN "W" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC esubst_VSUBST_comm THEN
          MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[] THEN
          REPEAT GEN_TAC THEN
          DISCH_THEN(fun m -> USE_THEN "R" (fun h -> MP_TAC(MATCH_MP h m))) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"] THEN
          MESON_TAC[has_type_rules]];
        MATCH_MP_TAC ACONV_SYM THEN MATCH_MP_TAC esubst_INST_comm THEN
        MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC ACONV_TRANS THEN
    EXISTS_TAC `esubst sigma [] (VSUBST ilist_f (INST tyin (VSUBST ilist_r c)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_VSUBST_comm THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC unique_varnames_no_var_collapse THEN
      MATCH_MP_TAC unique_varnames_INST THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[term_ok_welltyped];
      MATCH_MP_TAC esubst_ACONV THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ACONV_SYM THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 val blast_term_validation *)
let CLITAUX_blast_term_validation =
  DEP_REWRITE_TAC[esubst_welltyped; VSUBST_WELLTYPED; INST_WELLTYPED; esubst_term_ok;
                  apply_steps_welltyped; apply_steps_term_ok; term_ok_VSUBST] THEN
  SIMP[hol_term_ok_def; apply_steps_term_ok; term_ok_welltyped;
       welltyped_comb; welltyped_equation; EQUATION_HAS_TYPE_BOOL];;

let apply_steps_comb = prove
 (`!sig x y stps.
     hol_term_ok sig x /\ hol_term_ok sig y /\ steps_ok sig stps
     ==> apply_steps stps (hol_Comb x y) =
         hol_Comb (apply_steps stps x) (apply_steps stps y)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[apply_steps_def] THEN
  QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `apply_steps t (hol_Comb x y) = hol_Comb (apply_steps t x) (apply_steps t y)`
     SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[VSUBST_def] THEN
  MATCH_MP_TAC INST_COMB THEN ASM_MESON_TAC[apply_steps_welltyped; term_ok_welltyped]);;

let CLITAUX_Abs_ex = prove
 (`!n ty b. welltyped b
            ==> ?n2 ty2 bd2. hol_Abs (hol_Var n ty) b = hol_Abs (hol_Var n2 ty2) bd2 /\
                             welltyped bd2`,
  MESON_TAC[]);;

let apply_steps_Abs = prove
 (`!sig stps n0 ty0 abs_bd.
     steps_ok sig stps ==> welltyped abs_bd
     ==> ?n2 ty2 bd2. apply_steps stps (hol_Abs (hol_Var n0 ty0) abs_bd) =
                      hol_Abs (hol_Var n2 ty2) bd2 /\
                      welltyped bd2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[apply_steps_def] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n0:mlstring`; `ty0:hol_type`; `abs_bd:hol_term`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[VSUBST_def; dest_var_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
    COND_CASES_TAC THEN MATCH_MP_TAC CLITAUX_Abs_ex THEN
    MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[has_type_rules];
    SUBGOAL_THEN `welltyped (hol_Abs (hol_Var n2 ty2) bd2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`hol_Abs (hol_Var n2 ty2) bd2`; `a:(hol_type#hol_type)list`]
                  INST_dbINST) THEN
    MP_TAC(ISPECL [`hol_Abs (hol_Var n2 ty2) bd2`; `a:(hol_type#hol_type)list`]
                  INST_WELLTYPED) THEN
    ASM_REWRITE_TAC[hol_db_def; dbINST_def] THEN
    SPEC_TAC(`INST a (hol_Abs (hol_Var n2 ty2) bd2)`,`u:hol_term`) THEN
    GEN_TAC THEN QCASES_ON "u" THEN
    REWRITE_TAC[hol_db_def; distinctness "dbterm"; WELLTYPED_CLAUSES] THEN MESON_TAC[]]);;

let REV_ASSOCD_default_eq = prove
 (`!(l:(A#B)list) (x:B) d1 d2. (?v. MEM (v,x) l) ==> REV_ASSOCD x l d1 = REV_ASSOCD x l d2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN PAIR_CASES_ON `h:A#B` THEN
  REWRITE_TAC[REV_ASSOCD; MEM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;
