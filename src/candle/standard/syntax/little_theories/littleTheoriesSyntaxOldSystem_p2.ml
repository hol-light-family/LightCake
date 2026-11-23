(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 2 (HOL4 lines      *)
(* 1001-1879): ty_esubst and TYPE_SUBST, term_ok of the                      *)
(* substitutions, typing, de Bruijn esubst (db_esubst).                      *)
(* ========================================================================= *)

needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem_p1.ml";;

prioritize_num();;
type_invention_error := true;;

let LIST_INSERT_EQ_NIL = prove
 (`!(h:A) xs. ~(LIST_INSERT h xs = [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_INSERT_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN ASM_MESON_TAC[MEM]);;
let _ = cake_add_simps [LIST_INSERT_EQ_NIL];;

let LIST_UNION_EQ_NIL = prove
 (`!(xs:A list) ys. LIST_UNION xs ys = [] <=> xs = [] /\ ys = []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LIST_UNION_def; ITLIST; LIST_INSERT_EQ_NIL; NOT_CONS_NIL]);;
let _ = cake_add_simps [LIST_UNION_EQ_NIL];;

let monomorphic_type_subst = prove
 (`!ty i. hol_tyvars ty = [] ==> TYPE_SUBST i ty = ty`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[hol_tyvars_def; TYPE_SUBST_def; NOT_CONS_NIL] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; ITLIST; MAP; LIST_UNION_EQ_NIL; injectivity "hol_type"; CONS_11] THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_type"]) THEN
  ASM_MESON_TAC[]);;

let typeof_has_type = prove
 (`!tm typ. welltyped tm ==> (tm has_type typ <=> typeof tm = typ)`,
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

let FLOOKUP_COMP = prove
 (`!(f1:(A,B)fmap) (f2:(B,C)fmap) k v.
     FLOOKUP f1 k = SOME v ==> FLOOKUP f2 v = FLOOKUP f2 (FAPPLY f1 k)`,
  SIMP_TAC[FAPPLY_FLOOKUP; THE_DEF]);;

let FLOOKUP_FAPPLY = prove
 (`!(fm:(A,B)fmap) k v. FLOOKUP fm k = SOME v <=> k IN FDOM fm /\ FAPPLY fm k = v`,
  REWRITE_TAC[flookup_thm]);;

let esubsts_ok_type_ok = prove
 (`!ty sig sigma.
     esubsts_ok sig sigma /\ type_ok (FST sig) ty
     ==> type_ok (FST sig) (ty_esubst sigma ty)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
                       `s2:(mlstring,hol_term#hol_type)fmap`] THEN
  STRIP_TAC THEN UNDISCH_TAC `type_ok (FST (sig:sig)) ty` THEN
  SPEC_TAC(`ty:hol_type`,`ty:hol_type`) THEN
  MATCH_MP_TAC type_ind THEN CONJ_TAC THENL [REWRITE_TAC[ty_esubst_def]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:mlstring`; `l:hol_type list`] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[type_ok_def; GSYM ALL_MEM]) THEN
  REWRITE_TAC[ty_esubst_def; FST] THEN TOP_CASE_TAC THEN REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[type_ok_def; LENGTH_MAP; GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  PAIR_CASES_ON `a:mlstring list#hol_type` THEN REWRITE_TAC[pair_CASE] THEN
  QPAT_X_ASSUM "esubsts_ok _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
  SUBGOAL_THEN `(m:mlstring) IN FDOM (s1:(mlstring,mlstring list#hol_type)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; distinctness "option"]; ALL_TAC] THEN
  RES_TAC THEN
  CLITAUX_QUNDISCH_TAC "FLOOKUP s1 m = SOME (a0,a1)" THEN
  ASM_REWRITE_TAC[flookup_thm; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CLITAUX_QUNDISCH_TAC
    "FLOOKUP (FST sig) m = SOME (LENGTH l) /\\ (!x. MEM x l ==> type_ok (FST sig) x)" THEN
  ASM_REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[TAKE_LENGTH_TOO_LONG; LENGTH_MAP; LE_REFL] THEN
  MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_SIMP_TAC[MAP_FST_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[]);;

let REV_ASSOCD_MAP = prove
 (`!(l:(A#B)list) x (f:A->A) d.
     REV_ASSOCD x (MAP (\(v,k). (f v,k)) l) d =
     if ?v0. MEM (v0,x) l then f (REV_ASSOCD x l d) else d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; REV_ASSOCD_def] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[REV_ASSOCD; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let TYPE_SUBST_eta = prove
 (`TYPE_SUBST [] = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; TYPE_SUBST_NIL]);;

let CLITAUX_REV_ASSOCD_ZIP_TYPE_SUBST = prove
 (`!s m params vals.
     MEM m params /\ LENGTH (vals:hol_type list) = LENGTH params
     ==> TYPE_SUBST s (REV_ASSOCD (Tyvar m) (ZIP vals (MAP Tyvar params)) (Tyvar m)) =
         REV_ASSOCD (Tyvar m) (ZIP (MAP (TYPE_SUBST s) vals) (MAP Tyvar params)) (Tyvar m)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vals:hol_type list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP_def; REV_ASSOCD; injectivity "hol_type"] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYPE_SUBST_ZIP_compose = prove
 (`!body params vals s.
     set_of_list (hol_tyvars body) SUBSET set_of_list params /\
     LENGTH vals = LENGTH params
     ==> TYPE_SUBST s (TYPE_SUBST (ZIP vals (MAP Tyvar params)) body) =
         TYPE_SUBST (ZIP (MAP (TYPE_SUBST s) vals) (MAP Tyvar params)) body`,
  MATCH_MP_TAC type_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[hol_tyvars_def; TYPE_SUBST_def; set_of_list; INSERT_SUBSET; EMPTY_SUBSET;
                IN_SET_OF_LIST] THEN
    MESON_TAC[CLITAUX_REV_ASSOCD_ZIP_TYPE_SUBST];
    MAP_EVERY X_GEN_TAC [`m:mlstring`; `l:hol_type list`] THEN
    REWRITE_TAC[GSYM ALL_MEM; hol_tyvars_def; TYPE_SUBST_def; injectivity "hol_type"] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN X_GEN_TAC `y:hol_type` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:hol_type`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `set_of_list (ITLIST (\x y. LIST_UNION (hol_tyvars x) y) l [])` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_FOLDR_LIST_UNION] THEN ASM_MESON_TAC[]]);;

let ty_esubst_TYPE_SUBST_comm = prove
 (`!ty i tys tms sigma.
     esubsts_ok (tys,tms) sigma /\ type_ok tys (TYPE_SUBST i ty)
     ==> ty_esubst sigma (TYPE_SUBST i ty) =
         TYPE_SUBST (MAP (\(v,k). (ty_esubst sigma v,k)) i) (ty_esubst sigma ty)`,
  MATCH_MP_TAC type_ind THEN CONJ_TAC THENL
   [X_GEN_TAC `m:mlstring` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[TYPE_SUBST_def; ty_esubst_def; REV_ASSOCD_MAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`i:(hol_type#hol_type)list`; `Tyvar m`; `Tyvar m`] REV_ASSOCD_MEM) THEN
    ASM_MESON_TAC[ty_esubst_def];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:mlstring`; `l:hol_type list`] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:(hol_type#hol_type)list`; `tys:(mlstring,num)fmap`;
                       `tms:(mlstring,hol_type)fmap`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
                       `s2:(mlstring,hol_term#hol_type)fmap`] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TYPE_SUBST_def; type_ok_def; LENGTH_MAP; GSYM ALL_MEM; MEM_MAP]) THEN
  REWRITE_TAC[TYPE_SUBST_def; ty_esubst_def; FST] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[TYPE_SUBST_def] THENL
   [REWRITE_TAC[injectivity "hol_type"; MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN X_GEN_TAC `y:hol_type` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:hol_type` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:(hol_type#hol_type)list`; `tys:(mlstring,num)fmap`;
      `tms:(mlstring,hol_type)fmap`;
      `(s1,s2):(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  PAIR_CASES_ON `a:mlstring list#hol_type` THEN REWRITE_TAC[pair_CASE] THEN
  QPAT_ASSUM "esubsts_ok _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
  SUBGOAL_THEN `(m:mlstring) IN FDOM (s1:(mlstring,mlstring list#hol_type)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; distinctness "option"]; ALL_TAC] THEN
  RES_TAC THEN
  CLITAUX_QUNDISCH_TAC "FLOOKUP s1 m = SOME (a0,a1)" THEN
  ASM_REWRITE_TAC[flookup_thm; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `FLOOKUP (tys:(mlstring,num)fmap) m = SOME a`;
                              injectivity "option"]) THEN
  SUBGOAL_THEN `LENGTH (params:mlstring list) = LENGTH (l:hol_type list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[TAKE_LENGTH_TOO_LONG; LENGTH_MAP; LE_REFL] THEN
  ASM_SIMP_TAC[TYPE_SUBST_ZIP_compose; LENGTH_MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN X_GEN_TAC `y:hol_type` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:hol_type` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:(hol_type#hol_type)list`; `tys:(mlstring,num)fmap`;
    `tms:(mlstring,hol_type)fmap`;
    `(s1,s2):(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4: is_instance (ty_esubst sigma ty) (ty_esubst sigma (TYPE_SUBST i ty)) *)
let ty_esubst_TYPE_SUBST = prove
 (`!ty i tys tms sigma.
     esubsts_ok (tys,tms) sigma /\ type_ok tys (TYPE_SUBST i ty)
     ==> ?i'. ty_esubst sigma (TYPE_SUBST i ty) = TYPE_SUBST i' (ty_esubst sigma ty)`,
  MESON_TAC[ty_esubst_TYPE_SUBST_comm]);;

let term_ok_var = prove
 (`!sig x ty. hol_term_ok sig (hol_Var x ty) <=> type_ok (FST sig) ty`,
  REWRITE_TAC[hol_term_ok_def]);;
let _ = cake_add_simps [term_ok_var];;

let term_ok_comb = prove
 (`!sig tm1 tm2.
     hol_term_ok sig (hol_Comb tm1 tm2) <=>
     hol_term_ok sig tm1 /\ hol_term_ok sig tm2 /\ welltyped (hol_Comb tm1 tm2)`,
  REWRITE_TAC[hol_term_ok_def]);;
let _ = cake_add_simps [term_ok_comb];;

let term_ok_abs = prove
 (`!sig v tm.
     hol_term_ok sig (hol_Abs v tm) <=>
     ?x ty. v = hol_Var x ty /\ type_ok (FST sig) ty /\ hol_term_ok sig tm`,
  REWRITE_TAC[hol_term_ok_def]);;
let _ = cake_add_simps [term_ok_abs];;

let ty_esubst_bool = prove
 (`!sigma:(mlstring,mlstring list#hol_type)fmap#A.
     ~(implode "bool" IN FDOM (FST sigma)) ==> ty_esubst sigma (Tyapp (implode "bool") []) = Tyapp
       (implode "bool") []`,
  GEN_TAC THEN REWRITE_TAC[ty_esubst_def; FLOOKUP_DEF] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[option_CASE; MAP]);;
let _ = cake_add_simps [ty_esubst_bool];;

(* the parts of esubst_sig (the theorems tysof_esubst_sig and tmsof_esubst_sig
   come later in HOL4's order) *)
let CLITAUX_esubst_sig_FST_SND = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) sig.
     FST (esubst_sig sigma sig) = FST sig /\
     SND (esubst_sig sigma sig) = ty_esubst sigma o_f SND sig`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; esubst_sig_def]);;

let esubst_ty0_term_ok = prove
 (`!env sigma avds tm subst_tm sig.
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm /\
     hol_term_ok sig tm /\
     esubsts_ok sig sigma /\
     (!v1 v2. MEM (v1,v2) env
              ==> ?n ty. v1 = hol_Var n ty /\ v2 = hol_Var n (ty_esubst sigma ty))
     ==> hol_term_ok (esubst_sig sigma sig) subst_tm`,
  MATCH_MP_TAC esubst_ty0_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[hol_term_ok_def; CLITAUX_esubst_sig_FST_SND] THEN
    MATCH_MP_TAC esubsts_ok_type_ok THEN ASM_MESON_TAC[hol_term_ok_def];
    REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def; injectivity "error"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
    REWRITE_TAC[hol_term_ok_def; CLITAUX_esubst_sig_FST_SND; FLOOKUP_o_f] THEN
    ASM_REWRITE_TAC[option_CASE; injectivity "option"] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC esubsts_ok_type_ok THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`ty0:hol_type`; `i:(hol_type#hol_type)list`; `FST (sig:sig)`; `SND (sig:sig)`;
                     `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`]
                    ty_esubst_TYPE_SUBST) THEN
      ASM_REWRITE_TAC[PAIR] THEN ASM_MESON_TAC[]];
    ALL_TAC; ALL_TAC] THENL
   [    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
    MAP_EVERY X_GEN_TAC [`subst_tm:hol_term`; `sig:sig`] THEN
    REWRITE_TAC[esubst_ty0_def; bind_EQ_return; injectivity "error"; hol_term_ok_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[hol_term_ok_def] THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`u:hol_term`; `sig:sig`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`u':hol_term`; `sig:sig`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CLITAUX_QSUBGOAL_THEN "!k v. MEM (v,k) env ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\\
                                                        v = hol_Var n ty" ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CLITAUX_QSUBGOAL_THEN
      "typeof u = ty_esubst sigma (typeof t1) /\\ typeof u' = ty_esubst sigma (typeof t2)"
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
      [MP_TAC(SPECL [`env:(hol_term#hol_term)list`;
        `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
        `avds:mlstring list`; `t1:hol_term`; `sig:sig`] esubst_ty0_impossible1) THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:hol_term` o CONJUNCT2 o CONJUNCT2);
       MP_TAC(SPECL [`env:(hol_term#hol_term)list`;
        `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
        `avds:mlstring list`; `t2:hol_term`; `sig:sig`] esubst_ty0_impossible1) THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u':hol_term` o CONJUNCT2 o CONJUNCT2)] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    QPAT_X_ASSUM "welltyped (hol_Comb t1 t2)"
      (STRIP_ASSUME_TAC o REWRITE_RULE[welltyped_def; has_type_comb]) THEN
    IMP_RES_TAC has_type_typeof THEN
    REWRITE_TAC[welltyped_def] THEN QEXISTS_TAC "ty_esubst sigma ty" THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 has_type_rules))) THEN
    QEXISTS_TAC "typeof u'" THEN
    ASM_SIMP_TAC[MATCH_MP ty_esubst_fun (ASSUME `esubsts_ok sig sigma`)] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(MESON[WELLTYPED] `welltyped (x:hol_term) /\ typeof x = ty ==> x has_type ty`) THEN
    ASM_SIMP_TAC[MATCH_MP ty_esubst_fun (ASSUME `esubsts_ok sig sigma`)] THEN
    ASM_MESON_TAC[term_ok_welltyped];
        MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`;
       `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
       `avds:mlstring list`; `v:hol_term`; `body:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (CONJUNCTS_THEN2 (LABEL_TAC "ihb")
      (LABEL_TAC "iha"))) THEN
    MAP_EVERY X_GEN_TAC [`subst_tm:hol_term`; `sig:sig`] THEN
    REWRITE_TAC[hol_term_ok_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    REMOVE_THEN "iha" (MP_TAC o SPECL [`x:mlstring`; `ty:hol_type`]) THEN
    REWRITE_TAC[dest_var_def] THEN DISCH_THEN(LABEL_TAC "iha") THEN
    REMOVE_THEN "ihc" (MP_TAC o SPECL
      [`hol_Var x (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                    (mlstring,hol_term#hol_type)fmap) ty)`]) THEN
    REWRITE_TAC[dest_var_def; PAIR_EQ] THEN
    DISCH_THEN(MP_TAC o GEN `body1:hol_term` o SPECL [`body1:hol_term`; `x:mlstring`; `ty:hol_type`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihc") THEN
    CLITAUX_QUNDISCH_TAC "esubst_ty0 env sigma avds (hol_Abs (hol_Var x ty) body) =
                          errorMonad_return subst_tm" THEN
    REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
                distinctness "error"; COND_CASE_EQ] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"; CLITAUX_esubst_sig_FST_SND] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    (CONJ_TAC THENL [MATCH_MP_TAC esubsts_ok_type_ok THEN ASM_REWRITE_TAC[]; ALL_TAC]) THENL
     [REMOVE_THEN "iha" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
      REMOVE_THEN "ihc" (MP_TAC o SPECL [`u:hol_term`; `u':hol_term`; `sig:sig`]) THEN
      ASM_SIMP_TAC[term_ok_vsubst_variant] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]]]);;

(* HOL4's unused subst_tm has a type variable as its type; here hol_term *)
let esubst_ty_term_ok = prove
 (`!sigma avds tm (subst_tm:hol_term) sig.
     hol_term_ok sig tm /\ esubsts_ok sig sigma
     ==> hol_term_ok (esubst_sig sigma sig) (esubst_ty sigma avds tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                `tm:hol_term`; `sig:sig`; `avds:mlstring list`] esubst_ty0_always_returns) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `tm1:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def; case_def "error"] THEN
  MATCH_MP_TAC esubst_ty0_term_ok THEN
  MAP_EVERY EXISTS_TAC [`[]:(hol_term#hol_term)list`; `avds:mlstring list`; `tm:hol_term`] THEN
  ASM_REWRITE_TAC[MEM]);;

let esubst_ty_bool = prove
 (`!tm sig sigma avds.
     hol_term_ok sig tm /\ esubsts_ok sig sigma /\ tm has_type Tyapp (implode "bool") []
     ==> esubst_ty sigma avds tm has_type Tyapp (implode "bool") []`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                `tm:hol_term`; `sig:sig`; `avds:mlstring list`] esubst_ty0_always_returns) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `tm1:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def; case_def "error"] THEN
  CLITAUX_QSUBGOAL_THEN "hol_term_ok (esubst_sig sigma sig) tm1" ASSUME_TAC THENL
   [MATCH_MP_TAC esubst_ty0_term_ok THEN
    MAP_EVERY EXISTS_TAC [`[]:(hol_term#hol_term)list`; `avds:mlstring list`; `tm:hol_term`] THEN
    ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  CLITAUX_QSUBGOAL_THEN "typeof tm1 = ty_esubst sigma (typeof tm)" ASSUME_TAC THENL
   [MP_TAC(SPECL [`[]:(hol_term#hol_term)list`;
                   `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                   `avds:mlstring list`; `tm:hol_term`; `sig:sig`] esubst_ty0_impossible1) THEN
    ASM_REWRITE_TAC[MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `tm1:hol_term` o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  IMP_RES_TAC has_type_typeof THEN
  CLITAUX_QSUBGOAL_THEN
    "ty_esubst sigma (Tyapp (implode \"bool\") []) = Tyapp (implode \"bool\") []"
    ASSUME_TAC THENL
   [MATCH_MP_TAC ty_esubst_bool THEN
    UNDISCH_TAC `esubsts_ok sig sigma` THEN
    SPEC_TAC(`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`,
             `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; esubsts_ok_def; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[typeof_has_type; term_ok_welltyped]);;

let const_has_type_eq = prove
 (`!n ty typ. hol_Const n ty has_type typ ==> ty = typ`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_type_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[]);;

let esubst_ty0_ty_esubst = prove
 (`!tm env sigma avds subst_tm sig.
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm /\
     esubsts_ok sig sigma /\
     (!k v. MEM (v,k) env ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     hol_term_ok sig tm
     ==> typeof subst_tm = ty_esubst sigma (typeof tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`env:(hol_term#hol_term)list`;
                `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                `avds:mlstring list`; `tm:hol_term`; `sig:sig`] esubst_ty0_impossible1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `subst_tm:hol_term` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

(* HOL4's unused ty has a type variable as its type; here hol_type *)
let esubst_ty0_env_type_invariant = prove
 (`!tm (ty:hol_type) tm1 tm2 env1 env2 sig sigma avds.
     hol_term_ok sig tm /\
     esubsts_ok sig sigma /\
     (!k v. MEM (v,k) env1 ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     (!k v. MEM (v,k) env2 ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     esubst_ty0 env1 sigma avds tm = errorMonad_return tm1 /\
     esubst_ty0 env2 sigma avds tm = errorMonad_return tm2
     ==> typeof tm1 = typeof tm2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tm:hol_term`; `env1:(hol_term#hol_term)list`;
                `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                `avds:mlstring list`; `tm1:hol_term`; `sig:sig`] esubst_ty0_ty_esubst) THEN
  MP_TAC(SPECL [`tm:hol_term`; `env2:(hol_term#hol_term)list`;
                `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                `avds:mlstring list`; `tm2:hol_term`; `sig:sig`] esubst_ty0_ty_esubst) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CLITAUX_SIZEOF_VSUBST1 = prove
 (`!x y ty t. sizeof (VSUBST [(hol_Var x ty,hol_Var y ty)] t) = sizeof t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SIZEOF_VSUBST THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
  MESON_TAC[]);;

let sizeof_esubst_ty0 = prove
 (`!env sigma avds tm subst_tm sig.
     hol_term_ok sig tm /\
     (!k v. MEM (v,k) env ==> ?n1 ty1 n2 ty2. k = hol_Var n1 ty1 /\ v = hol_Var n2 ty2) /\
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
     ==> sizeof tm = sizeof subst_tm`,
  MATCH_MP_TAC esubst_ty0_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[sizeof_def];
    REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def; injectivity "error"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[sizeof_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`subst_tm:hol_term`; `sig:sig`] THEN
    REWRITE_TAC[esubst_ty0_def; bind_EQ_return; injectivity "error"; hol_term_ok_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[sizeof_def] THEN
    BINOP_TAC THEN TRY BINOP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`env:(hol_term#hol_term)list`;
     `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
     `avds:mlstring list`; `v:hol_term`; `body:hol_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (CONJUNCTS_THEN2 (LABEL_TAC "ihb")
    (LABEL_TAC "iha"))) THEN
  MAP_EVERY X_GEN_TAC [`subst_tm:hol_term`; `sig:sig`] THEN
  REWRITE_TAC[hol_term_ok_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  REMOVE_THEN "iha" (MP_TAC o SPECL [`x:mlstring`; `ty:hol_type`]) THEN
  REWRITE_TAC[dest_var_def] THEN DISCH_THEN(LABEL_TAC "iha") THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL
    [`hol_Var x (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                  (mlstring,hol_term#hol_type)fmap) ty)`]) THEN
  REWRITE_TAC[dest_var_def; PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o GEN `body1:hol_term` o SPECL [`body1:hol_term`; `x:mlstring`; `ty:hol_type`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihc") THEN
  CLITAUX_QUNDISCH_TAC "esubst_ty0 env sigma avds (hol_Abs (hol_Var x ty) body) =
                        errorMonad_return subst_tm" THEN
  REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
              distinctness "error"; COND_CASE_EQ] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[sizeof_def; EQ_ADD_LCANCEL] THEN
    REMOVE_THEN "iha" MATCH_MP_TAC THEN EXISTS_TAC `sig:sig` THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[sizeof_def; EQ_ADD_LCANCEL] THEN
    REMOVE_THEN "ihc" (MP_TAC o SPECL [`u:hol_term`; `u':hol_term`; `sig:sig`]) THEN
    ASM_SIMP_TAC[term_ok_vsubst_variant; CLITAUX_SIZEOF_VSUBST1] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]]);;

let tysof_esubst_sig = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) sig.
     FST (esubst_sig sigma sig) = FST sig`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; esubst_sig_def]);;
let _ = cake_add_simps [tysof_esubst_sig];;

let tmsof_esubst_sig = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) sig.
     SND (esubst_sig sigma sig) = ty_esubst sigma o_f SND sig`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; esubst_sig_def]);;
let _ = cake_add_simps [tmsof_esubst_sig];;

(* closes the goals of tymatch_complete after the induction hypothesis *)
let CLITAUX_tymatch_close =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(EXISTS_TAC `i:(hol_type#hol_type)list`) THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN
  TRY(GEN_TAC THEN COND_CASES_TAC) THEN
  ASM_MESON_TAC[injectivity "hol_type"; injectivity "option"];;

let tymatch_complete = prove
 (`!ps obs sids.
     (?i. obs = MAP (TYPE_SUBST i) ps /\
          (!name. ~(REV_ASSOCD (Tyvar name) (FST sids) (Tyvar name) = Tyvar name)
                  ==> REV_ASSOCD (Tyvar name) (FST sids) (Tyvar name) =
                      TYPE_SUBST i (Tyvar name)) /\
          (!name. MEM name (SND sids) ==> TYPE_SUBST i (Tyvar name) = Tyvar name))
     ==> ?z. tymatch ps obs sids = SOME z`,
  MATCH_MP_TAC tymatch_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tymatch_def] THEN MESON_TAC[];
    REWRITE_TAC[MAP; NOT_CONS_NIL];
    REWRITE_TAC[MAP; NOT_CONS_NIL];
    ALL_TAC;
    ALL_TAC;
    REWRITE_TAC[MAP; CONS_11; TYPE_SUBST_def; distinctness "hol_type"]] THENL
   [MAP_EVERY X_GEN_TAC [`name:mlstring`; `ps:hol_type list`; `ty:hol_type`; `obs:hol_type list`;
                         `sids:(hol_type#hol_type)list#mlstring list`] THEN
    PAIR_CASES_ON `sids:(hol_type#hol_type)list#mlstring list` THEN
    SIMP[PAIR_EQ; FST; SND] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (CONJUNCTS_THEN2 (LABEL_TAC "ih2")
      (LABEL_TAC "ih3"))) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:(hol_type#hol_type)list` STRIP_ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    REWRITE_TAC[tymatch_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE] THEN
    CLITAUX_QASM_CASES_TAC "REV_ASSOCD (Tyvar name) sids0 (Tyvar name) = Tyvar name" THEN
    ASM_REWRITE_TAC[] THENL
     [CLITAUX_QASM_CASES_TAC "MEM (name:mlstring) sids1" THEN ASM_REWRITE_TAC[option_CASE] THENL
       [SUBGOAL_THEN `REV_ASSOCD (Tyvar name) i (Tyvar name) = Tyvar name`
          (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REMOVE_THEN "ih1" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN CLITAUX_tymatch_close;
        COND_CASES_TAC THENL
         [REMOVE_THEN "ih3" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN CLITAUX_tymatch_close;
          REMOVE_THEN "ih2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN CLITAUX_tymatch_close]];
      REWRITE_TAC[option_CASE] THEN
      SUBGOAL_THEN `REV_ASSOCD (Tyvar name) sids0 (Tyvar name) =
                    REV_ASSOCD (Tyvar name) i (Tyvar name)`
        (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "ih1" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN CLITAUX_tymatch_close];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[MAP; CONS_11; TYPE_SUBST_def; injectivity "hol_type"] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:(hol_type#hol_type)list` STRIP_ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    REWRITE_TAC[tymatch_def] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[]) THEN
    EXISTS_TAC `i:(hol_type#hol_type)list` THEN ASM_REWRITE_TAC[MAP_APPEND] THEN
    ASM_REWRITE_TAC[TYPE_SUBST_def]]);;

let match_type_complete = prove
 (`!ty1 ty2. (?i. TYPE_SUBST i ty1 = ty2) ==> ?s. match_type ty1 ty2 = SOME s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[match_type_def] THEN
  MP_TAC(ISPECL [`[ty1:hol_type]`; `[ty2:hol_type]`;
                 `([],[]):(hol_type#hol_type)list#mlstring list`] tymatch_complete) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `i:(hol_type#hol_type)list` THEN
    ASM_REWRITE_TAC[MAP; FST; SND; REV_ASSOCD_def; MEM];
    STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN MESON_TAC[]]);;

(* HOL4's unused ty has a type variable as its type; here hol_type *)
(* the size induction hypothesis among the assumptions *)
let CLITAUX_mentions_sizeof th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = "sizeof")) (concl th);;

let typeof_esubst_tm_esubst_ty0 = prove
 (`!tm (ty:hol_type) subst_tm env sig sigma avds.
     hol_term_ok sig tm /\
     esubsts_ok sig sigma /\
     is_std_sig sig /\
     (!k v. MEM (v,k) env ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
     ==> typeof (esubst_tm sigma subst_tm) = typeof subst_tm`,
  GEN_TAC THEN WF_INDUCT_TAC `sizeof tm` THEN
  NAMED_CASES_ON "tm" ["x xty"; "c cty"; "t1 t2"; "v body"] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [QPAT_X_ASSUM "esubst_ty0 _ _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[esubst_ty0_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def];
    QPAT_X_ASSUM "esubst_ty0 _ _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[esubst_ty0_def; injectivity "error"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  PAIR_CASES_ON `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap` THEN
  REWRITE_TAC[esubst_tm_def; SND] THEN TOP_CASE_TAC THEN REWRITE_TAC[typeof_def] THEN
PAIR_CASES_ON `a:hol_term#hol_type` THEN REWRITE_TAC[pair_CASE] THEN
  QPAT_ASSUM "esubsts_ok _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
  SUBGOAL_THEN `(c:mlstring) IN FDOM (sigma1:(mlstring,hol_term#hol_type)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FDOM_FLOOKUP; distinctness "option"]; ALL_TAC] THEN
  RES_TAC THEN
  CLITAUX_QUNDISCH_TAC "FLOOKUP sigma1 c = SOME (a0,a1)" THEN
  ASM_REWRITE_TAC[flookup_thm; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  QPAT_X_ASSUM "hol_term_ok sig (hol_Const c cty)" (STRIP_ASSUME_TAC o REWRITE_RULE[hol_term_ok_def]) THEN
CLITAUX_QUNDISCH_TAC "FLOOKUP (SND sig) c = SOME ty0" THEN ASM_REWRITE_TAC[injectivity "option"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
                                                 fst(dest_var(lhs(concl th))) = "cty")) THEN
  CLITAUX_QSUBGOAL_THEN
    "?s. match_type (ty_esubst (sigma0,sigma1) ty)
                    (ty_esubst (sigma0,sigma1) (TYPE_SUBST i ty)) = SOME s"
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC match_type_complete THEN
    MP_TAC(ISPECL [`ty:hol_type`; `i:(hol_type#hol_type)list`; `FST (sig:sig)`; `SND (sig:sig)`;
                   `(sigma0,sigma1):(mlstring,mlstring list#hol_type)fmap#
                                    (mlstring,hol_term#hol_type)fmap`] ty_esubst_TYPE_SUBST) THEN
    ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  MATCH_MP_TAC WELLTYPED_LEMMA THEN MATCH_MP_TAC INST_HAS_TYPE THEN
  EXISTS_TAC `typeof repl` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WELLTYPED; term_ok_welltyped]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] match_type_SOME) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC type_ok_arities_match THEN
  EXISTS_TAC `FST (sig:sig)` THEN CONJ_TAC THENL
   [CLITAUX_QSUBGOAL_THEN "type_ok (FST (esubst_sig (sigma0,sigma1) sig)) (typeof repl)" MP_TAC THENL
     [MATCH_MP_TAC term_ok_type_ok THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC esubst_sig_is_std_sig THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[tysof_esubst_sig]];
    MATCH_MP_TAC esubsts_ok_type_ok THEN ASM_REWRITE_TAC[]];
    QPAT_X_ASSUM "esubst_ty0 _ _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[esubst_ty0_def; bind_EQ_return; injectivity "error"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def; typeof_def] THEN
AP_TERM_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t1:hol_term` o check CLITAUX_mentions_sizeof) THEN
  REWRITE_TAC[sizeof_def; ARITH_RULE `a < 1 + a + b`] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN ASM_MESON_TAC[];
    QPAT_X_ASSUM "hol_term_ok sig (hol_Abs v body)" (MP_TAC o REWRITE_RULE[hol_term_ok_def]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `xty:hol_type` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  QPAT_X_ASSUM "esubst_ty0 _ _ _ _ = _" MP_TAC THEN
  REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
              distinctness "error"; COND_CASE_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[esubst_tm_def; typeof_def; injectivity "hol_type"; CONS_11] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `body:hol_term` o check CLITAUX_mentions_sizeof) THEN
  REWRITE_TAC[sizeof_def; ARITH_RULE `a < 2 + a`] THEN DISCH_THEN MATCH_MP_TAC THEN
  QEXISTS_TAC "CONS (hol_Var x xty,hol_Var x (ty_esubst sigma xty)) env" THEN
  QEXISTS_TAC "sig" THEN QEXISTS_TAC "avds" THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `VSUBST [hol_Var (NVARIANT x avds u) xty,hol_Var x xty] body` o
                check CLITAUX_mentions_sizeof) THEN
  REWRITE_TAC[sizeof_def; CLITAUX_SIZEOF_VSUBST1; ARITH_RULE `a < 2 + a`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  QEXISTS_TAC "CONS (hol_Var (NVARIANT x avds u) xty,
                     hol_Var (NVARIANT x avds u) (ty_esubst sigma xty)) env" THEN
  QEXISTS_TAC "sig" THEN QEXISTS_TAC "avds" THEN
  ASM_SIMP_TAC[term_ok_vsubst_variant] THEN REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]]]);;

(* HOL4: FOLDR f b l is ITLIST f l b *)
let FOLDR_LIST_UNION_CONG = prove
 (`!(l:A list) (f:A->B list) g b.
     (!x. MEM x l ==> f x = g x)
     ==> ITLIST (\x acc. LIST_UNION (f x) acc) l b =
         ITLIST (\x acc. LIST_UNION (g x) acc) l b`,
  REPEAT GEN_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM] THEN DISCH_TAC THEN
  BINOP_TAC THENL [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let REV_ASSOCD_MEM_IMP = prove
 (`!(l:(A#B)list) k d. MEM k (MAP SND l) ==> MEM (REV_ASSOCD k l d,k) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN PAIR_CASES_ON `h:A#B` THEN
  REWRITE_TAC[REV_ASSOCD; MAP; MEM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let typeof_esubst_tm = prove
 (`!tm sig sigma theta axs.
     esubsts_ok sig (sigma,theta) /\
     theory_ok (sig,axs) /\
     hol_term_ok (esubst_sig (sigma,theta) sig) tm
     ==> typeof (esubst_tm (sigma,theta) tm) = typeof tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[esubst_tm_def; typeof_def] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:mlstring`; `ty:hol_type`] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`tys:(mlstring,num)fmap`; `tms:(mlstring,hol_type)fmap`;
                         `sigma:(mlstring,mlstring list#hol_type)fmap`;
                         `theta:(mlstring,hol_term#hol_type)fmap`; `axs:hol_term->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `FLOOKUP (theta:(mlstring,hol_term#hol_type)fmap) m` (cases "option")) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE; typeof_def] THEN
    FIRST_ASSUM(MP_TAC o SPEC `m:mlstring` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                REWRITE_RULE[esubsts_ok_def]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `ty0:hol_type` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (can (find_term ((=) `hol_Const`)) o concl)) THEN
    ASM_REWRITE_TAC[hol_term_ok_def; esubst_sig_def; FLOOKUP_o_f; FST; SND] THEN
    ASM_REWRITE_TAC[option_CASE; injectivity "option"] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?s. match_type (ty_esubst (sigma,theta:(mlstring,hol_term#hol_type)fmap) ty0) ty =
          SOME s` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC match_type_complete THEN EXISTS_TAC `i:(hol_type#hol_type)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `ty0':hol_type` o concl))) THEN
    ASM_REWRITE_TAC[option_CASE] THEN
    SUBGOAL_THEN
     `is_std_sig (esubst_sig (sigma,theta:(mlstring,hol_term#hol_type)fmap) (tys,tms))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC esubst_sig_is_std_sig THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def; FST]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `type_ok tys (typeof repl)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`esubst_sig (sigma,theta:(mlstring,hol_term#hol_type)fmap) (tys,tms)`;
                     `repl:hol_term`] term_ok_type_ok) THEN
      ASM_REWRITE_TAC[esubst_sig_def; FST];
      ALL_TAC] THEN
    MATCH_MP_TAC has_type_typeof THEN MATCH_MP_TAC INST_HAS_TYPE THEN
    EXISTS_TAC `typeof repl` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[term_ok_welltyped; WELLTYPED];
      CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ty_esubst (sigma,theta:(mlstring,hol_term#hol_type)fmap) ty0`;
                     `ty:hol_type`; `s:(hol_type#hol_type)list`] match_type_SOME) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC type_ok_arities_match THEN EXISTS_TAC `tys:(mlstring,num)fmap` THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[];
    REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[]]);;

let tymatch_type_ok = prove
 (`!ps obs sids z tys.
     tymatch ps obs sids = SOME z /\
     ALL (type_ok tys) obs /\
     ALL (type_ok tys) (MAP FST (FST sids))
     ==> ALL (type_ok tys) (MAP FST (FST z))`,
  MATCH_MP_TAC tymatch_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[tymatch_def; distinctness "option"; injectivity "option"] THENL
  [MESON_TAC[];
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1")
     (CONJUNCTS_THEN2 (LABEL_TAC "I2") (LABEL_TAC "I3"))) THEN
   PAIR_CASES_ON `sids:(hol_type#hol_type)list#mlstring list` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                               FORALL_UNWIND_THM1]) THEN
   REWRITE_TAC[pair_CASE; FST] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN
   ABBREV_TAC `r = REV_ASSOCD (Tyvar name) sids0 (Tyvar name)` THEN
   ASM_CASES_TAC `r:hol_type = Tyvar name` THEN
   POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   ASM_REWRITE_TAC[] THEN
   TRY(ASM_CASES_TAC `MEM (name:mlstring) sids1` THEN
       POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
       ASM_REWRITE_TAC[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"; injectivity "option"; MAP; ALL]) THEN
   CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN ASM_MESON_TAC[];
   DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[distinctness "option"; ALL; ALL_APPEND; type_ok_def] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
   ASM_REWRITE_TAC[ALL_APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let match_type_type_ok = prove
 (`!ty1 ty2 s tys.
     match_type ty1 ty2 = SOME s /\ type_ok tys ty2 ==> ALL (type_ok tys) (MAP FST s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[match_type_def; OPTION_MAP_EQ_SOME] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC tymatch_type_ok THEN
  MAP_EVERY EXISTS_TAC [`[ty1:hol_type]`; `[ty2:hol_type]`;
                        `([],[]):(hol_type#hol_type)list#mlstring list`] THEN
  ASM_REWRITE_TAC[ALL; MAP; FST]);;

let esubst_tm_preserves_term_ok = prove
 (`!tm sig axs sigma.
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma /\
     hol_term_ok (esubst_sig sigma sig) tm
     ==> hol_term_ok (esubst_sig sigma sig) (esubst_tm sigma tm)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[esubst_tm_def] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`m:mlstring`; `ty:hol_type`; `tys:(mlstring,num)fmap`;
                         `tms:(mlstring,hol_type)fmap`; `axs:hol_term->bool`;
                         `sigma:(mlstring,mlstring list#hol_type)fmap`;
                         `theta:(mlstring,hol_term#hol_type)fmap`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `FLOOKUP (theta:(mlstring,hol_term#hol_type)fmap) m` (cases "option")) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
    FIRST_ASSUM(MP_TAC o SPEC `m:mlstring` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                REWRITE_RULE[esubsts_ok_def]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `ty0:hol_type` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (can (find_term ((=) `hol_Const`)) o concl)) THEN
    ASM_REWRITE_TAC[hol_term_ok_def; esubst_sig_def; FLOOKUP_o_f; FST; SND] THEN
    ASM_REWRITE_TAC[option_CASE; injectivity "option"] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?s. match_type (ty_esubst (sigma,theta:(mlstring,hol_term#hol_type)fmap) ty0) ty =
          SOME s` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC match_type_complete THEN EXISTS_TAC `i:(hol_type#hol_type)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `ty0':hol_type` o concl))) THEN
    ASM_REWRITE_TAC[option_CASE] THEN RULE_ASSUM_TAC(REWRITE_RULE[esubst_sig_def]) THEN
    MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC match_type_type_ok THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t1:hol_term`; `t2:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "I2")) THEN
    MAP_EVERY X_GEN_TAC [`tys:(mlstring,num)fmap`; `tms:(mlstring,hol_type)fmap`;
                         `axs:hol_term->bool`; `sigma:(mlstring,mlstring list#hol_type)fmap`;
                         `theta:(mlstring,hol_term#hol_type)fmap`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_term_ok_def] o
                  check (can (find_term ((=) `hol_Comb`)) o concl)) THEN
    SUBGOAL_THEN
     `hol_term_ok (esubst_sig (sigma,theta) (tys,tms)) (esubst_tm (sigma,theta) t1) /\
      hol_term_ok (esubst_sig (sigma,theta) (tys,tms)) (esubst_tm (sigma,theta) t2)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [REMOVE_THEN "I1" MATCH_MP_TAC; REMOVE_THEN "I2" MATCH_MP_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `typeof (esubst_tm (sigma,theta) t1) = typeof t1 /\
      typeof (esubst_tm (sigma,theta) t2) = typeof t2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC typeof_esubst_tm THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[hol_term_ok_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[term_ok_welltyped];
    REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[]]);;

let esubst_term_ok = prove
 (`!sig axs tm sigma avds.
     theory_ok (sig,axs) /\ hol_term_ok sig tm /\ esubsts_ok sig sigma
     ==> hol_term_ok (esubst_sig sigma sig) (esubst sigma avds tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[esubst_def] THEN
  MATCH_MP_TAC esubst_tm_preserves_term_ok THEN EXISTS_TAC `axs:hol_term->bool` THEN
  ASM_SIMP_TAC[esubst_ty_term_ok]);;

let esubst_has_type = prove
 (`!tm sig axs sigma avds ty.
     theory_ok (sig,axs) /\
     esubst_ty sigma avds tm has_type ty /\
     hol_term_ok sig tm /\
     esubsts_ok sig sigma
     ==> esubst sigma avds tm has_type ty`,
  REPEAT GEN_TAC THEN
  PAIR_CASES_ON
   `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap` THEN
  STRIP_TAC THEN REWRITE_TAC[esubst_def] THEN
  ABBREV_TAC `t' = esubst_ty (sigma0,sigma1) avds tm` THEN
  SUBGOAL_THEN `hol_term_ok (esubst_sig (sigma0,sigma1:(mlstring,hol_term#hol_type)fmap) sig) t'`
    ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN ASM_SIMP_TAC[esubst_ty_term_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (esubst_tm (sigma0,sigma1) t')` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_welltyped THEN
    EXISTS_TAC `esubst_sig (sigma0,sigma1:(mlstring,hol_term#hol_type)fmap) sig` THEN
    MATCH_MP_TAC esubst_tm_preserves_term_ok THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[typeof_has_type] THEN
  SUBGOAL_THEN `typeof (esubst_tm (sigma0,sigma1) t') = typeof t'` SUBST1_TAC THENL
   [MATCH_MP_TAC typeof_esubst_tm THEN ASM_MESON_TAC[]; ASM_MESON_TAC[has_type_typeof]]);;

let esubst_has_type_bool = prove
 (`!tm sig sigma axs avds.
     tm has_type Tyapp (implode "bool") [] /\
     esubsts_ok sig sigma /\
     theory_ok (sig,axs) /\
     hol_term_ok sig tm
     ==> esubst sigma avds tm has_type Tyapp (implode "bool") []`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_has_type THEN ASM_MESON_TAC[esubst_ty_bool]);;

let is_std_sig_funion = prove
 (`!tys tms tys1 tms1.
     is_std_sig (tys,tms) ==> is_std_sig (FUNION tys tys1,FUNION tms tms1)`,
  REWRITE_TAC[is_std_sig_def; FLOOKUP_FUNION] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE]);;

let type_ok_weakening = prove
 (`!ty ts1 ts2. type_ok ts1 ty ==> type_ok (FUNION ts1 ts2) ty`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[type_ok_def; FLOOKUP_FUNION] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let term_ok_weakening = prove
 (`!tm tys tms tys1 tms1.
     hol_term_ok (tys,tms) tm ==> hol_term_ok (FUNION tys tys1,FUNION tms tms1) tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[hol_term_ok_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[type_ok_weakening; FLOOKUP_FUNION; option_CASE] THEN
  ASM_MESON_TAC[type_ok_weakening]);;

let welltyped_comb = prove
 (`!l1 l2 rty.
     welltyped l1 /\ welltyped l2 /\ typeof l1 = Tyapp (implode "fun") [typeof l2; rty]
     ==> welltyped (hol_Comb l1 l2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped_def] THEN EXISTS_TAC `rty:hol_type` THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 has_type_rules))) THEN
  EXISTS_TAC `typeof l2` THEN RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED]) THEN
  ASM_MESON_TAC[]);;

(* HOL4: proves_theory_ok *)
let little_proves_theory_ok = prove
 (`!thy h c. (thy,h) |- c ==> theory_ok thy`,
  SUBGOAL_THEN `!p c. p |- c ==> theory_ok (FST p)` (fun th -> MESON_TAC[th; FST]) THEN
  MATCH_MP_TAC proves_ind THEN SIMP[]);;

let proves_theory_ok_ext = prove
 (`!thy1 thy2 h c c1.
     theory_ok thy1 /\ (thy2,h) |- c /\ FST thy1 = FST thy2
     ==> theory_ok (FST thy1,(SND thy1 DIFF {c1}) UNION SND thy2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `theory_ok thy2` MP_TAC THENL
   [ASM_MESON_TAC[little_proves_theory_ok]; ALL_TAC] THEN
  UNDISCH_TAC `theory_ok thy1` THEN
  ASM_REWRITE_TAC[theory_ok_def; FST; SND; IN_UNION; IN_DIFF; IN_SING] THEN
  MESON_TAC[]);;

let proves_imp_theory_ok = prove
 (`!thy h c. (thy,h) |- c ==> theory_ok thy`,
  SUBGOAL_THEN `!p c. p |- c ==> theory_ok (FST p)` (fun th -> MESON_TAC[th; FST]) THEN
  MATCH_MP_TAC proves_ind THEN SIMP[]);;

let CLITAUX_B_theory_ok_axs = prove
 (`!thy B. theory_ok thy /\
           (!p. p IN B ==> hol_term_ok (FST thy) p /\ p has_type Tyapp (implode "bool") [])
           ==> theory_ok (FST thy,B)`,
  REWRITE_TAC[theory_ok_def; FST; SND] THEN MESON_TAC[]);;

let axiom_weakening = prove
 (`!A B h sig c.
     ((sig,A),h) |- c /\
     (!p. p IN B ==> hol_term_ok sig p /\ p has_type Tyapp (implode "bool") []) /\
     A SUBSET B
     ==> ((sig,B),h) |- c`,
  SUBGOAL_THEN
   `!a (c:hol_term). a |- c
      ==> !B. (!p. p IN B ==> hol_term_ok (FST (FST a)) p /\
                              p has_type Tyapp (implode "bool") []) /\
              SND (FST a) SUBSET B
              ==> ((FST (FST a),B),SND a) |- c`
   (fun th -> REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP th) THEN
              REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC proves_ind THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `B:hol_term->bool` THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC proves_ABS THEN ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_ASSUME THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC CLITAUX_B_theory_ok_axs THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_BETA THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC CLITAUX_B_theory_ok_axs THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_DEDUCT_ANTISYM THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`p:hol_term`; `p':hol_term`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_INST THEN ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_INST_TYPE THEN ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_MK_COMB THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_REFL THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC CLITAUX_B_theory_ok_axs THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_axioms THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLITAUX_B_theory_ok_axs THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SND] THEN ASM SET_TAC[]]]);;

let CLITAUX_B_theory_ok_ext = prove
 (`!thy axs1 d. theory_ok thy /\ ((FST thy,axs1),[]) |- d
                ==> theory_ok (FST thy,(SND thy DIFF {d}) UNION axs1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`thy:thy`; `(FST(thy:thy),axs1):thy`; `[]:hol_term list`; `d:hol_term`;
                 `d:hol_term`] proves_theory_ok_ext) THEN
  ASM_REWRITE_TAC[FST; SND]);;

let axioms_eliminable = prove
 (`!thy1 thy2 h2 c1 c2.
     (thy2,h2) |- c2 /\ (thy1,[]) |- c1 /\ FST thy1 = FST thy2
     ==> ((FST thy1,(SND thy2 DIFF {c1}) UNION SND thy1),h2) |- c2`,
  SUBGOAL_THEN
   `!a (c2:hol_term). a |- c2
      ==> !axs1 d. ((FST (FST a),axs1),[]) |- d
                   ==> ((FST (FST a),(SND (FST a) DIFF {d}) UNION axs1),SND a) |- c2`
   (fun th -> REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
              MP_TAC(MATCH_MP th (ASSUME `(thy2,h2) |- c2`)) THEN
              REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
              REWRITE_TAC[GSYM(ASSUME `FST(thy1:thy) = FST(thy2:thy)`); PAIR] THEN
              ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC proves_ind THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`axs1:hol_term->bool`; `d:hol_term`] THEN DISCH_TAC THENL
   [MATCH_MP_TAC proves_ABS THEN ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_ASSUME THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC CLITAUX_B_theory_ok_ext THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_BETA THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC CLITAUX_B_theory_ok_ext THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_DEDUCT_ANTISYM THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`p:hol_term`; `p':hol_term`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_INST THEN ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_INST_TYPE THEN ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_MK_COMB THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_REFL THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC CLITAUX_B_theory_ok_ext THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `c:hol_term = d` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC axiom_weakening THEN
      EXISTS_TAC `axs1:hol_term->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `theory_ok (FST thy,(SND thy DIFF {d}) UNION axs1)` MP_TAC THENL
       [MATCH_MP_TAC CLITAUX_B_theory_ok_ext THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[theory_ok_def; FST; SND] THEN STRIP_TAC THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]]];
      MATCH_MP_TAC proves_axioms THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLITAUX_B_theory_ok_ext THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SND; IN_UNION; IN_DIFF; IN_SING]]]]);;

let FAPPLY_IN_FRANGE = prove
 (`!(m:(A,B)fmap) x. x IN FDOM m ==> FAPPLY m x IN FRANGE m`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FDOM_FLOOKUP] THEN MESON_TAC[flookup_thm; FDOM_FLOOKUP]);;

let ty_esubst_type_ok_alt = prove
 (`!ty sig sigma.
     type_ok (FST sig) ty /\ esubsts_ok sig sigma
     ==> type_ok (FST sig) (ty_esubst sigma ty)`,
  MESON_TAC[esubsts_ok_type_ok]);;

let thy_axs_diff = prove
 (`!(a:A->bool) b c d.
     ~(c IN a)
     ==> a UNION ((b DIFF {c}) UNION d) = ((a UNION b) DIFF {c}) UNION (a UNION d)`,
  SET_TAC[]);;

let thy_axs_diff_alt = prove
 (`!(a:A->bool) b c d.
     c IN a ==> a UNION ((b DIFF {c}) UNION d) = (a UNION b) UNION d`,
  SET_TAC[]);;

(* HOL4: FAPPLY_FLOOKUP *)
let little_FAPPLY_FLOOKUP = prove
 (`!(f:(A,B)fmap) k v. FLOOKUP f k = SOME v ==> FAPPLY f k = v`,
  REWRITE_TAC[flookup_thm] THEN MESON_TAC[]);;

let term_image_id = prove
 (`!lst. term_image (\p. p) lst = lst`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[term_image_def] THEN FS[]);;

let esubst_equation_has_type = prove
 (`!l r sig axs sigma avds.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\ hol_term_ok sig (l === r)
     ==> esubst sigma avds (l === r) has_type Tyapp (implode "bool") []`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_has_type_bool THEN
  MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `is_std_sig sig` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(sig,axs):thy` theory_ok_sig) THEN ASM_REWRITE_TAC[FST]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (find_term ((=) `equation`)) o concl)) THEN
  ASM_SIMP_TAC[term_ok_equation; EQUATION_HAS_TYPE_BOOL] THEN
  MESON_TAC[term_ok_welltyped]);;

let term_union_left_nil = prove
 (`!h. term_union [] h = h`,
  GEN_TAC THEN ONCE_REWRITE_TAC[term_union_def] THEN SIMP[]);;
let _ = cake_add_simps [term_union_left_nil];;

let CLITAUX_B_RACONV_INV_TAC =
  (* inverts an RACONV assumption that mentions a constant, then substitutes the new variables *)
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[RACONV_cases] o
                check (fun th -> fst(strip_comb(concl th)) = `RACONV` &&
                                 can (find_term ((=) `hol_Const`)) (concl th))) THEN
  REWRITE_TAC[PAIR_EQ; distinctness "hol_term"; injectivity "hol_term"] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl)));;

let ACONV_equation_r = prove
 (`!a c.
     welltyped a /\ welltyped c
     ==> (ACONV a (c === c) <=>
          ?b d. a = b === d /\ ACONV c b /\ ACONV c d /\ welltyped b /\ welltyped d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[ACONV_def; equation_def] THEN DISCH_TAC THEN
    CLITAUX_B_RACONV_INV_TAC THEN CLITAUX_B_RACONV_INV_TAC THEN CLITAUX_B_RACONV_INV_TAC THEN
    SUBGOAL_THEN `welltyped t1 /\ welltyped t1'` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `welltyped a` THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `typeof t1' = typeof c` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ACONV_TYPE) THEN ASM_REWRITE_TAC[ACONV_def];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`t1':hol_term`; `t1:hol_term`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ACONV_def] THEN CONJ_TAC THEN MATCH_MP_TAC ACONV_SYM THEN
    ASM_REWRITE_TAC[ACONV_def];
    STRIP_TAC THEN ASM_REWRITE_TAC[equation_def; ACONV_def] THEN
    SUBGOAL_THEN `typeof b = typeof c` SUBST1_TAC THENL [ASM_MESON_TAC[ACONV_TYPE]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 RACONV_rules))) THEN CONJ_TAC) THEN
    REWRITE_TAC[GSYM ACONV_def; ACONV_REFL] THEN ASM_MESON_TAC[ACONV_SYM]]);;

let EL_APPEND_LE = prove
 (`!n (pfx:A list) lst. n < LENGTH pfx ==> EL n (APPEND pfx lst) = EL n pfx`,
  SIMP_TAC[EL_APPEND]);;

let PRE_plus_one = prove
 (`!k. PRE (k + 1) = k`,
  ARITH_TAC);;
let _ = cake_add_simps [PRE_plus_one];;

let esubst_ty_abs_avoids = prove
 (`!x ty body avds sig sigma.
     esubsts_ok sig sigma /\ hol_term_ok sig (hol_Abs (hol_Var x ty) body)
     ==> ?x1 body1.
           esubst_ty sigma avds (hol_Abs (hol_Var x ty) body) =
             hol_Abs (hol_Var x1 (ty_esubst sigma ty)) body1 /\
           (x1 = x \/ ~MEM x1 avds) /\
           hol_term_ok (esubst_sig sigma sig) (hol_Abs (hol_Var x1 (ty_esubst sigma ty)) body1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                 `hol_Abs (hol_Var x ty) body`; `sig:sig`; `avds:mlstring list`]
                esubst_ty0_always_returns) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def; case_def "error"] THEN
  QPAT_X_ASSUM "hol_term_ok _ _"
   (STRIP_ASSUME_TAC o REWRITE_RULE[hol_term_ok_def; injectivity "hol_term"]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  UNDISCH_TAC `esubst_ty0 [] sigma avds (hol_Abs (hol_Var x ty) body) = errorMonad_return v` THEN
  REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
              distinctness "error"; COND_CASE_EQ] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `v:hol_term`)) THENL
   [MAP_EVERY EXISTS_TAC [`x:mlstring`; `u:hol_term`] THEN REWRITE_TAC[] THEN
    REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"; CLITAUX_esubst_sig_FST_SND] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ty_esubst_type_ok_alt THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_ty0_term_ok THEN
      MAP_EVERY EXISTS_TAC
       [`[hol_Var x ty,hol_Var x (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                                                   (mlstring,hol_term#hol_type)fmap) ty)]`;
        `avds:mlstring list`; `body:hol_term`] THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[]];
    MAP_EVERY EXISTS_TAC [`NVARIANT x avds u`; `u':hol_term`] THEN
    REWRITE_TAC[NVARIANT_AVDS_THM] THEN
    REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"; CLITAUX_esubst_sig_FST_SND] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ty_esubst_type_ok_alt THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_ty0_term_ok THEN
      MAP_EVERY EXISTS_TAC
       [`[hol_Var (NVARIANT x avds u) ty,
          hol_Var (NVARIANT x avds u)
           (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                             (mlstring,hol_term#hol_type)fmap) ty)]`;
        `avds:mlstring list`; `VSUBST [hol_Var (NVARIANT x avds u) ty,hol_Var x ty] body`] THEN
      ASM_SIMP_TAC[term_ok_vsubst_variant; MEM; PAIR_EQ] THEN MESON_TAC[]]]);;

let esubst_ty0_abs_nvariant = prove
 (`!x ty body subst_body body1 sigma avds x1.
     esubst_ty0 [] sigma avds (hol_Abs (hol_Var x ty) body) =
       errorMonad_return (hol_Abs (hol_Var x1 (ty_esubst sigma ty)) body1) /\
     esubst_ty0 [] sigma avds body = errorMonad_return subst_body
     ==> (x1 = x \/ ~MEM x1 (tm_names subst_body))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
              distinctness "error"; COND_CASE_EQ; injectivity "hol_term"] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[];
    SUBGOAL_THEN `u:hol_term = subst_body` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[injectivity "error"]; ASM_MESON_TAC[NVARIANT_NAMES_THM]]]);;

let esubst_ty_abs_nvariant = prove
 (`!x ty body subst_body body1 sig sigma avds x1.
     esubsts_ok sig sigma /\
     hol_term_ok sig (hol_Abs (hol_Var x ty) body) /\
     esubst_ty sigma avds (hol_Abs (hol_Var x ty) body) =
       hol_Abs (hol_Var x1 (ty_esubst sigma ty)) body1 /\
     esubst_ty0 [] sigma avds body = errorMonad_return subst_body
     ==> (x1 = x \/ ~MEM x1 (tm_names subst_body))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                 `hol_Abs (hol_Var x ty) body`; `sig:sig`; `avds:mlstring list`]
                esubst_ty0_always_returns) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  MATCH_MP_TAC esubst_ty0_abs_nvariant THEN
  MAP_EVERY EXISTS_TAC
   [`ty:hol_type`; `body:hol_term`; `body1:hol_term`;
    `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
    `avds:mlstring list`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `esubst_ty sigma avds (hol_Abs (hol_Var x ty) body) =
               hol_Abs (hol_Var x1 (ty_esubst sigma ty)) body1` THEN
  ASM_REWRITE_TAC[esubst_ty_def; case_def "error"] THEN SIMP_TAC[]);;

let equation_equality = prove
 (`!l1 r1 l2 r2. l1 === r1 = l2 === r2 ==> l1 = l2 /\ r1 = r2`,
  REWRITE_TAC[equation_def; injectivity "hol_term"] THEN MESON_TAC[]);;

let ACONV_equation = prove
 (`!l l1 r r1.
     welltyped l /\ welltyped l1 /\ welltyped r /\ welltyped r1 /\
     ACONV l l1 /\ ACONV r r1
     ==> ACONV (l === r) (l1 === r1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equation_def; ACONV_def] THEN
  SUBGOAL_THEN `typeof l = typeof l1` SUBST1_TAC THENL [ASM_MESON_TAC[ACONV_TYPE]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 RACONV_rules))) THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[GSYM ACONV_def; ACONV_REFL]);;

let db_esubst_ty_def = cake_def
  `(db_esubst_ty (sigma:(mlstring,mlstring list#hol_type)fmap#A) (dbVar x ty) =
      dbVar x (ty_esubst sigma ty)) /\
   (db_esubst_ty sigma (dbBound n) = dbBound n) /\
   (db_esubst_ty sigma (dbConst x ty) = dbConst x (ty_esubst sigma ty)) /\
   (db_esubst_ty sigma (dbComb t1 t2) =
      dbComb (db_esubst_ty sigma t1) (db_esubst_ty sigma t2)) /\
   (db_esubst_ty sigma (dbAbs ty t) = dbAbs (ty_esubst sigma ty) (db_esubst_ty sigma t))`;;

let db_esubst_tm_def = cake_def
  `(db_esubst_tm (sigma:(mlstring,mlstring list#hol_type)fmap#
                        (mlstring,hol_term#hol_type)fmap) (dbVar x ty) = dbVar x ty) /\
   (db_esubst_tm sigma (dbBound n) = dbBound n) /\
   (db_esubst_tm sigma (dbConst x ty) =
      match FLOOKUP (SND sigma) x with
        NONE -> dbConst x ty
      | SOME (repl,decl_ty) ->
          match match_type (ty_esubst sigma decl_ty) ty with
            NONE -> dbConst x ty
          | SOME tyin -> dbINST tyin (hol_db repl)) /\
   (db_esubst_tm sigma (dbComb t1 t2) =
      dbComb (db_esubst_tm sigma t1) (db_esubst_tm sigma t2)) /\
   (db_esubst_tm sigma (dbAbs ty t) = dbAbs ty (db_esubst_tm sigma t))`;;

let db_esubst_def = cake_def
  `db_esubst sigma tm = db_esubst_tm sigma (db_esubst_ty sigma tm)`;;

let db_esubst_ty_bind = prove
 (`!tm v n (sigma:(mlstring,mlstring list#hol_type)fmap#A).
     (!ty. dbVFREE_IN (dbVar (FST v) ty) tm /\ ty_esubst sigma ty = ty_esubst sigma (SND v)
           ==> ty = SND v)
     ==> db_esubst_ty sigma (hol_bind v n tm) =
         hol_bind (FST v,ty_esubst sigma (SND v)) n (db_esubst_ty sigma tm)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[hol_bind_def; db_esubst_ty_def; dbVFREE_IN_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "dbterm"] THEN DISCH_TAC THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[db_esubst_ty_def; distinctness "dbterm"; injectivity "dbterm"] THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "I2")) THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[injectivity "dbterm"] THEN CONJ_TAC THENL
     [REMOVE_THEN "I1" MATCH_MP_TAC; REMOVE_THEN "I2" MATCH_MP_TAC] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[injectivity "dbterm"] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
