(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 3 (HOL4 lines      *)
(* 1880-2597): typing of esubst_ty0, de Bruijn translation of                *)
(* the substitutions, alpha-equivalence and esubst.                          *)
(* ========================================================================= *)

needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem_p2.ml";;

prioritize_num();;
type_invention_error := true;;


(* HOL4 val contrapos_tac (before esubst_ty0_var_type_thm) is p1's
   CLITAUX_contrapos_tac. *)

(* dbVFREE_IN_VFREE_IN for a variable *)
let CLITAUX_dbVFREE_IN_dbVar = prove
 (`!tm x ty. welltyped tm
             ==> (dbVFREE_IN (dbVar x ty) (hol_db tm) <=> VFREE_IN (hol_Var x ty) tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tm:hol_term`; `hol_Var x ty`] dbVFREE_IN_VFREE_IN) THEN
  ASM_REWRITE_TAC[hol_db_def]);;

let esubst_ty0_var_type_thm = prove
 (`!sig sigma avds n tm env.
     welltyped tm /\ sizeof tm = n /\ hol_term_ok sig tm /\
     esubsts_ok sig sigma /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty))
     ==> (?x ty. esubst_ty0 env sigma avds tm =
                   errorMonad_error (hol_Var x (ty_esubst sigma ty)) /\
                 VFREE_IN (hol_Var x ty) tm /\
                 ~(REV_ASSOCD (hol_Var x (ty_esubst sigma ty)) env (hol_Var x ty) =
                   hol_Var x ty)) \/
         (!x ty. VFREE_IN (hol_Var x ty) tm
                 ==> REV_ASSOCD (hol_Var x (ty_esubst sigma ty)) env (hol_Var x ty) =
                     hol_Var x ty) /\
         (?tm'. esubst_ty0 env sigma avds tm = errorMonad_return tm' /\
                tm' has_type (ty_esubst sigma (typeof tm)) /\
                (!u uty. VFREE_IN (hol_Var u uty) tm' <=>
                         ?oty. VFREE_IN (hol_Var u oty) tm /\ uty = ty_esubst sigma oty))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "WF") THEN
  SUBGOAL_THEN
   `!tm env.
      sizeof tm < n /\ welltyped tm /\ hol_term_ok sig tm /\ esubsts_ok sig sigma /\
      (!s s'. MEM (s,s') env
              ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty))
      ==> (?x ty. esubst_ty0 env sigma avds tm =
                    errorMonad_error (hol_Var x (ty_esubst sigma ty)) /\
                  VFREE_IN (hol_Var x ty) tm /\
                  ~(REV_ASSOCD (hol_Var x (ty_esubst sigma ty)) env (hol_Var x ty) =
                    hol_Var x ty)) \/
          (!x ty. VFREE_IN (hol_Var x ty) tm
                  ==> REV_ASSOCD (hol_Var x (ty_esubst sigma ty)) env (hol_Var x ty) =
                      hol_Var x ty) /\
          (?tm'. esubst_ty0 env sigma avds tm = errorMonad_return tm' /\
                 tm' has_type (ty_esubst sigma (typeof tm)) /\
                 (!u uty. VFREE_IN (hol_Var u uty) tm' <=>
                          ?oty. VFREE_IN (hol_Var u oty) tm /\ uty = ty_esubst sigma oty))`
    (LABEL_TAC "IH") THENL
   [REPEAT STRIP_TAC THEN
    REMOVE_THEN "WF" (MP_TAC o SPEC `sizeof (tm:hol_term)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "WF" (K ALL_TAC)] THEN
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:mlstring`; `xty:hol_type`; `env:(hol_term#hol_term)list`] THEN
    STRIP_TAC THEN
    REWRITE_TAC[esubst_ty0_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "error"; injectivity "error"; VFREE_IN_def;
                injectivity "hol_term"; typeof_def] THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      QEXISTS_TAC "hol_Var x (ty_esubst sigma xty)" THEN
      REWRITE_TAC[CSYNAUX_P3_has_type_Var; VFREE_IN_def; injectivity "hol_term"] THEN
      MESON_TAC[];
      ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[esubst_ty0_def] THEN
    REWRITE_TAC[distinctness "error"; injectivity "error"; VFREE_IN_def;
                distinctness "hol_term"; typeof_def; UNWIND_THM1; CSYNAUX_P3_has_type_Const];
    MAP_EVERY X_GEN_TAC [`s:hol_term`; `t:hol_term`] THEN DISCH_THEN(K ALL_TAC) THEN
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; sizeof_def; hol_term_ok_def] THEN STRIP_TAC THEN
    USE_THEN "IH" (MP_TAC o SPECL [`s:hol_term`; `env:(hol_term#hol_term)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "IH" (MP_TAC o SPECL [`t:hol_term`; `env:(hol_term#hol_term)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[esubst_ty0_def] THEN
    REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[errorMonad_bind_def; distinctness "error"; injectivity "error";
                    VFREE_IN_def; typeof_def; codomain_def; UNWIND_THM1; UNWIND_THM2] THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        REWRITE_TAC[CSYNAUX_P3_has_type_Comb] THEN QEXISTS_TAC "ty_esubst sigma (typeof t)" THEN
        ASM_REWRITE_TAC[] THEN
        QSPECL_THEN ["sig"; "sigma"; "typeof t"; "rty"] MP_TAC ty_esubst_fun THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        QPAT_X_ASSUM "_ has_type ty_esubst sigma (typeof s)" MP_TAC THEN ASM_REWRITE_TAC[];
        MESON_TAC[]]];
    X_GEN_TAC `v:hol_term` THEN X_GEN_TAC `t:hol_term` THEN DISCH_THEN(K ALL_TAC) THEN
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:mlstring`; `bty:hol_type`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v:hol_term`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[sizeof_def]) THEN
    SUBGOAL_THEN `type_ok (FST (sig:sig)) bty /\ hol_term_ok sig t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[hol_term_ok_def; injectivity "hol_term"]; ALL_TAC] THEN
    USE_THEN "IH" (QSPECL_THEN ["t"; "CONS (hol_Var b bty,hol_Var b (ty_esubst sigma bty)) env"]
                     MP_TAC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[pair_CASE] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[errorMonad_bind_def; little_try_def; distinctness "error";
                    injectivity "error"; UNWIND_THM1; UNWIND_THM2] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [DISJ1_TAC THEN QEXISTS_TAC "x" THEN QEXISTS_TAC "ty" THEN
        REWRITE_TAC[VFREE_IN_def] THEN ASM_REWRITE_TAC[] THEN
        QBY "~(hol_Var b (ty_esubst sigma bty) = hol_Var x (ty_esubst sigma ty))"
          (ASM_MESON_TAC[]) THEN
        QPAT_X_ASSUM "~(REV_ASSOCD _ _ _ = _)" MP_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD_def] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
        REWRITE_TAC[injectivity "hol_term"] THEN ASM_MESON_TAC[];
        USE_THEN "IH" (QSPECL_THEN ["t"; "[]:(hol_term#hol_term)list"] MP_TAC) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[MEM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REV_ASSOCD_def] THEN
        DISCH_THEN(X_CHOOSE_THEN `tt0:hol_term` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[errorMonad_bind_def] THEN
        ABBREV_TAC `x' = NVARIANT b avds tt0` THEN
        SUBGOAL_THEN `!oty. ~VFREE_IN (hol_Var x' oty) t` (LABEL_TAC "F3") THENL
         [GEN_TAC THEN DISCH_TAC THEN
          QSPECL_THEN ["ty_esubst sigma oty"; "tt0"; "b"; "avds"] MP_TAC NVARIANT_THM THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        ABBREV_TAC `t' = VSUBST [hol_Var x' bty,hol_Var b bty] t` THEN
        SUBGOAL_THEN `t' has_type typeof t` ASSUME_TAC THENL
         [EXPAND_TAC "t'" THEN MATCH_MP_TAC VSUBST_HAS_TYPE THEN
          ASM_REWRITE_TAC[GSYM WELLTYPED; MEM; PAIR_EQ] THEN MESON_TAC[CSYNAUX_P3_has_type_Var];
          ALL_TAC] THEN
        SUBGOAL_THEN `welltyped t' /\ typeof t' = typeof t` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[welltyped_def; WELLTYPED_LEMMA]; ALL_TAC] THEN
        SUBGOAL_THEN `sizeof t' = sizeof t` ASSUME_TAC THENL
         [EXPAND_TAC "t'" THEN REWRITE_TAC[CSYNAUX_SIZEOF_VSUBST_VAR]; ALL_TAC] THEN
        SUBGOAL_THEN `hol_term_ok sig t'` ASSUME_TAC THENL
         [EXPAND_TAC "t'" THEN MATCH_MP_TAC term_ok_vsubst_variant THEN ASM_REWRITE_TAC[];
           ALL_TAC] THEN
        SUBGOAL_THEN
         `!u uty. VFREE_IN (hol_Var u uty) t' <=>
                  (VFREE_IN (hol_Var b bty) t /\ hol_Var u uty = hol_Var x' bty) \/
                  (VFREE_IN (hol_Var u uty) t /\ ~(hol_Var u uty = hol_Var b bty))`
          (LABEL_TAC "F6") THENL
         [EXPAND_TAC "t'" THEN ASM_SIMP_TAC[VFREE_IN_VSUBST; REV_ASSOCD_def] THEN
          REWRITE_TAC[COND_RAND; COND_EXPAND; VFREE_IN_def] THEN MESON_TAC[];
          ALL_TAC] THEN
        USE_THEN "IH" (QSPECL_THEN ["t'"; "CONS (hol_Var x' bty,hol_Var x' (ty_esubst sigma
          bty)) env"]
                         MP_TAC) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[errorMonad_bind_def; distinctness "error"; injectivity "error";
                        UNWIND_THM1; UNWIND_THM2] THENL
         [SUBGOAL_THEN `~(hol_Var x'' ty' = hol_Var x' bty)` ASSUME_TAC THENL
           [REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
            QPAT_X_ASSUM "~(REV_ASSOCD _ _ _ = _)" MP_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD_def];
            ALL_TAC] THEN
          SUBGOAL_THEN `VFREE_IN (hol_Var x'' ty') t /\ ~(hol_Var x'' ty' = hol_Var b bty)`
            STRIP_ASSUME_TAC THENL
           [USE_THEN "F6" (fun th -> MP_TAC(EQ_MP (SPECL [`x'':mlstring`; `ty':hol_type`] th)
                                                 (ASSUME `VFREE_IN (hol_Var x'' ty') t'`))) THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          QBY "~(hol_Var x' (ty_esubst sigma bty) = hol_Var x'' (ty_esubst sigma ty'))"
            (REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
             REMOVE_THEN "F3" (MP_TAC o SPEC `ty':hol_type`) THEN ASM_REWRITE_TAC[]) THEN
          QEXISTS_TAC "x''" THEN QEXISTS_TAC "ty'" THEN
          QPAT_X_ASSUM "~(REV_ASSOCD _ _ _ = _)" MP_TAC THEN
          ASM_REWRITE_TAC[REV_ASSOCD_def; VFREE_IN_def] THEN ASM_MESON_TAC[];
          REPEAT CONJ_TAC THENL
           [MAP_EVERY X_GEN_TAC [`y:mlstring`; `yty:hol_type`] THEN
            REWRITE_TAC[VFREE_IN_def] THEN STRIP_TAC THEN
            SUBGOAL_THEN `VFREE_IN (hol_Var y yty) t'` ASSUME_TAC THENL
             [USE_THEN "F6" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
            QBY "~(hol_Var x' (ty_esubst sigma bty) = hol_Var y (ty_esubst sigma yty))"
              (REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THEN
               REMOVE_THEN "F3" (MP_TAC o SPEC `yty:hol_type`) THEN ASM_REWRITE_TAC[]) THEN
            QPAT_X_ASSUM "!x ty. VFREE_IN (hol_Var x ty) t' ==> _"
              (MP_TAC o SPECL [`y:mlstring`; `yty:hol_type`]) THEN
            ASM_REWRITE_TAC[REV_ASSOCD_def];
            REWRITE_TAC[typeof_def; CSYNAUX_P3_has_type_Abs; injectivity "hol_term"] THEN
            QSPECL_THEN ["sig"; "sigma"; "bty"; "typeof t"] MP_TAC ty_esubst_fun THEN
            ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
            QEXISTS_TAC "x'" THEN QEXISTS_TAC "ty_esubst sigma bty" THEN
            QEXISTS_TAC "ty_esubst sigma (typeof t)" THEN REWRITE_TAC[] THEN
            QPAT_X_ASSUM "_ has_type ty_esubst sigma (typeof t')" MP_TAC THEN ASM_REWRITE_TAC[];
            REWRITE_TAC[VFREE_IN_def] THEN
            QPAT_X_ASSUM "!u uty. VFREE_IN (hol_Var u uty) tm' <=> _"
              (fun th -> REWRITE_TAC[th]) THEN
            USE_THEN "F6" (fun th -> REWRITE_TAC[th]) THEN
            USE_THEN "F3" MP_TAC THEN
            REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[]]]];
      REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`y:mlstring`; `yty:hol_type`] THEN
        REWRITE_TAC[VFREE_IN_def] THEN STRIP_TAC THEN
        QPAT_X_ASSUM "!x ty. VFREE_IN (hol_Var x ty) t ==> _"
          (MP_TAC o SPECL [`y:mlstring`; `yty:hol_type`]) THEN
        ASM_REWRITE_TAC[REV_ASSOCD_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[typeof_def; CSYNAUX_P3_has_type_Abs; injectivity "hol_term"] THEN
        QSPECL_THEN ["sig"; "sigma"; "bty"; "typeof t"] MP_TAC ty_esubst_fun THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        QEXISTS_TAC "b" THEN QEXISTS_TAC "ty_esubst sigma bty" THEN
        QEXISTS_TAC "ty_esubst sigma (typeof t)" THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[VFREE_IN_def] THEN
        QPAT_X_ASSUM "!u uty. VFREE_IN (hol_Var u uty) tm' <=> _"
          (fun th -> REWRITE_TAC[th]) THEN
        QPAT_X_ASSUM "!x ty. VFREE_IN (hol_Var x ty) t ==> _" MP_TAC THEN
        REWRITE_TAC[REV_ASSOCD_def; injectivity "hol_term"; COND_RAND; COND_RATOR;
                    COND_EXPAND] THEN
        MESON_TAC[]]]]);;

let esubst_ty0_has_type_thm = prove
 (`!sig env sigma avds tm subst_tm.
     hol_term_ok sig tm /\ esubsts_ok sig sigma /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty)) /\
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
     ==> (!x ty. VFREE_IN (hol_Var x ty) tm
                 ==> REV_ASSOCD (hol_Var x (ty_esubst sigma ty)) env (hol_Var x ty) =
                     hol_Var x ty)`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["sig"; "sigma"; "avds"; "sizeof tm"; "tm"; "env"] MP_TAC
    esubst_ty0_var_type_thm THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  ASM_REWRITE_TAC[distinctness "error"] THEN ASM_MESON_TAC[]);;

let esubst_ty0_all_free = prove
 (`!sig env sigma avds tm subst_tm.
     hol_term_ok sig tm /\ esubsts_ok sig sigma /\
     (!s s'. MEM (s,s') env
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty)) /\
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
     ==> (!u uty. VFREE_IN (hol_Var u uty) subst_tm <=>
                  ?oty. VFREE_IN (hol_Var u oty) tm /\ uty = ty_esubst sigma oty)`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["sig"; "sigma"; "avds"; "sizeof tm"; "tm"; "env"] MP_TAC
    esubst_ty0_var_type_thm THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  ASM_REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let db_esubst_ty_thm = prove
 (`!sig sigma tm env subst_tm avds.
     esubsts_ok sig sigma /\
     hol_term_ok sig tm /\
     welltyped tm /\
     (!k v. MEM (v,k) env
            ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
     ==> hol_db subst_tm = db_esubst_ty sigma (hol_db tm)`,
  SUBGOAL_THEN
   `!env sigma avds tm sig subst_tm.
      esubsts_ok sig sigma /\
      hol_term_ok sig tm /\
      welltyped tm /\
      (!k v. MEM (v,k) env
             ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
      esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
      ==> hol_db subst_tm = db_esubst_ty sigma (hol_db tm)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC esubst_ty0_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; injectivity "error"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[hol_db_def; db_esubst_ty_def];
    REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def; injectivity "error"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[hol_db_def; db_esubst_ty_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[esubst_ty0_def; bind_EQ_return; hol_term_ok_def; WELLTYPED_CLAUSES;
                injectivity "error"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[hol_db_def; db_esubst_ty_def; injectivity "dbterm"] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH3") (CONJUNCTS_THEN2 (LABEL_TAC "IH2")
                                                                  (LABEL_TAC "IH1"))) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    QPAT_ASSUM "welltyped (hol_Abs _ _)" (MP_TAC o REWRITE_RULE[WELLTYPED_CLAUSES]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[dest_var_def; PAIR_EQ]) THEN
    QPAT_X_ASSUM "esubst_ty0 _ _ _ _ = _"
      (MP_TAC o CONV_RULE(TOP_DEPTH_CONV let_CONV) o REWRITE_RULE[esubst_ty0_def;
        dest_var_def]) THEN
    REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
                distinctness "error"] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; db_esubst_ty_def; injectivity "dbterm"] THEN
      QBY "hol_db u = db_esubst_ty sigma (hol_db body)"
       (USE_THEN "IH1" (MP_TAC o SPECL [`n:mlstring`; `ty:hol_type`]) THEN REWRITE_TAC[] THEN
        DISCH_THEN MATCH_MP_TAC THEN QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
        ASM_MESON_TAC[hol_term_ok_def]) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      QSPECL_THEN ["hol_db body"; "(n,ty)"; "0"; "sigma"] MP_TAC db_esubst_ty_bind THEN
      REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
       [X_GEN_TAC `ty2:hol_type` THEN STRIP_TAC THEN
        SUBGOAL_THEN `VFREE_IN (hol_Var n ty2) body` ASSUME_TAC THENL
         [ASM_MESON_TAC[CLITAUX_dbVFREE_IN_dbVar]; ALL_TAC] THEN
        QSPECL_THEN ["sig"; "CONS (hol_Var n ty,hol_Var n (ty_esubst sigma ty)) env"; "sigma";
                     "avds"; "body"; "u"] MP_TAC esubst_ty0_has_type_thm THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[hol_term_ok_def];
                        ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`n:mlstring`; `ty2:hol_type`]) THEN
        ASM_REWRITE_TAC[REV_ASSOCD_def; injectivity "hol_term"] THEN MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN REFL_TAC];
      QPAT_X_ASSUM "(if _ then _ else _) = _" MP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "error"; bind_EQ_return; injectivity "error"] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:hol_term` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `u':hol_term` STRIP_ASSUME_TAC))) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      ABBREV_TAC `nv = NVARIANT n avds u` THEN
      ABBREV_TAC `tv = VSUBST [hol_Var nv ty,hol_Var n ty] body` THEN
      SUBGOAL_THEN `hol_term_ok sig (body:hol_term) /\ type_ok (FST (sig:sig)) ty`
        STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[hol_term_ok_def; injectivity "hol_term"]; ALL_TAC] THEN
      SUBGOAL_THEN `!oty. ~VFREE_IN (hol_Var nv oty) body` (LABEL_TAC "F3") THENL
       [GEN_TAC THEN DISCH_TAC THEN
        QSPECL_THEN ["ty_esubst sigma oty"; "u"; "n"; "avds"] MP_TAC NVARIANT_THM THEN
        ASM_REWRITE_TAC[] THEN
        QSPECL_THEN ["sig"; "[]:(hol_term#hol_term)list"; "sigma"; "avds"; "body"; "u"] MP_TAC
          esubst_ty0_all_free THEN
        ASM_REWRITE_TAC[MEM] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `hol_term_ok sig (tv:hol_term) /\ welltyped tv` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "tv" THEN CONJ_TAC THENL
         [MATCH_MP_TAC term_ok_vsubst_variant THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
          MESON_TAC[has_type_rules]];
        ALL_TAC] THEN
      QBY "hol_db u' = db_esubst_ty sigma (hol_db tv)"
       (REMOVE_THEN "IH3" (MP_TAC o SPECL [`e:hol_term`; `u:hol_term`; `n:mlstring`;
         `ty:hol_type`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN QEXISTS_TAC "sig" THEN
        ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]) THEN
      ASM_REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; db_esubst_ty_def; injectivity
        "dbterm"] THEN
      QBY "hol_db tv = dbVSUBST [(dbVar nv ty,dbVar n ty)] (hol_db body)"
       (EXPAND_TAC "tv" THEN
        QSPECL_THEN ["body"; "[(hol_Var nv ty,hol_Var n ty)]"] MP_TAC VSUBST_dbVSUBST THEN
        ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
         [MESON_TAC[WELLTYPED_CLAUSES]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MAP; hol_db_def] THEN
        CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[hol_db_def]) THEN
      QBY "hol_bind (nv,ty) 0 (hol_db tv) = hol_bind (n,ty) 0 (hol_db body)"
       (ASM_REWRITE_TAC[] THEN
        QSPECL_THEN ["hol_db body"; "(nv,ty)"; "(n,ty)"; "0"; "[]:(dbterm#dbterm)list"] MP_TAC
          bind_dbVSUBST_cons THEN
        REWRITE_TAC[UNCURRY_DEF; dbVSUBST_nil] THEN ANTS_TAC THENL
         [REWRITE_TAC[dbVFREE_IN_bind; UNCURRY_DEF] THEN ASM_SIMP_TAC[CLITAUX_dbVFREE_IN_dbVar];
          SIMP_TAC[]]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      QSPECL_THEN ["hol_db tv"; "(nv,ty)"; "0"; "sigma"] MP_TAC db_esubst_ty_bind THEN
      REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
       [X_GEN_TAC `ty2:hol_type` THEN STRIP_TAC THEN
        SUBGOAL_THEN `VFREE_IN (hol_Var nv ty2) tv` ASSUME_TAC THENL
         [ASM_MESON_TAC[CLITAUX_dbVFREE_IN_dbVar]; ALL_TAC] THEN
        QSPECL_THEN ["sig"; "CONS (hol_Var nv ty,hol_Var nv (ty_esubst sigma ty)) env"; "sigma";
                     "avds"; "tv"; "u'"] MP_TAC esubst_ty0_has_type_thm THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`nv:mlstring`; `ty2:hol_type`]) THEN
        ASM_REWRITE_TAC[REV_ASSOCD_def; injectivity "hol_term"] THEN MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]]);;

let esubst_ty_welltyped = prove
 (`!sig sigma tm avds.
     hol_term_ok sig tm /\ esubsts_ok sig sigma ==> welltyped (esubst_ty sigma avds tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_welltyped THEN
  QEXISTS_TAC "esubst_sig sigma sig" THEN MATCH_MP_TAC esubst_ty_term_ok THEN
  ASM_REWRITE_TAC[]);;

let esubst_ty_avds_aconv = prove
 (`!sig sigma avds1 avds2 tm.
     hol_term_ok sig tm /\
     welltyped tm /\
     esubsts_ok sig sigma
     ==> ACONV (esubst_ty sigma avds1 tm) (esubst_ty sigma avds2 tm)`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "avds1"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v1:hol_term`) THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "avds2"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v2:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped (v1:hol_term) /\ welltyped (v2:hol_term)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC term_ok_welltyped THEN QEXISTS_TAC "esubst_sig sigma sig" THEN
    MATCH_MP_TAC esubst_ty0_term_ok THEN ASM_MESON_TAC[MEM];
    ASM_SIMP_TAC[ACONV_db] THEN
    QSPECL_THEN ["sig"; "sigma"; "tm"; "[]:(hol_term#hol_term)list"; "v1"; "avds1"] MP_TAC
      db_esubst_ty_thm THEN
    QSPECL_THEN ["sig"; "sigma"; "tm"; "[]:(hol_term#hol_term)list"; "v2"; "avds2"] MP_TAC
      db_esubst_ty_thm THEN
    ASM_REWRITE_TAC[MEM] THEN MESON_TAC[]]);;

let RACONV_REFL_simple = prove
 (`!x. RACONV [] (x,x)`,
  GEN_TAC THEN MATCH_MP_TAC RACONV_REFL THEN REWRITE_TAC[ALL]);;
let _ = cake_add_simps [RACONV_REFL_simple];;

let bind_dbINST_no_dbVar = prove
 (`!dbtm tyin v n.
     (!x ty. ~dbVFREE_IN (dbVar x ty) dbtm)
     ==> hol_bind v n (dbINST tyin dbtm) = dbINST tyin dbtm`,
  MATCH_MP_TAC dbterm_INDUCT THEN SIMP[dbINST_def; hol_bind_def; dbVFREE_IN_def] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let db_esubst_tm_bind = prove
 (`!tm v n sigma.
     (!m repl decl_ty. FLOOKUP (SND sigma) m = SOME (repl,decl_ty)
                       ==> CLOSED repl /\ welltyped repl)
     ==> hol_bind v n (db_esubst_tm sigma tm) = db_esubst_tm sigma (hol_bind v n tm)`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[hol_bind_def; db_esubst_tm_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[db_esubst_tm_def];
    REPEAT TOP_CASE_TAC THEN REWRITE_TAC[hol_bind_def] THEN
    MATCH_MP_TAC bind_dbINST_no_dbVar THEN
    ASM_MESON_TAC[CLOSED_def; CLITAUX_dbVFREE_IN_dbVar];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let db_esubst_tm_thm = prove
 (`!sig sigma tm.
     esubsts_ok sig sigma /\ hol_term_ok (esubst_sig sigma sig) tm
     ==> hol_db (esubst_tm sigma tm) = db_esubst_tm sigma (hol_db tm)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:(mlstring,mlstring list#hol_type)fmap`;
                       `th:(mlstring,hol_term#hol_type)fmap`] THEN
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[esubst_tm_def; hol_db_def; db_esubst_tm_def; hol_term_ok_def] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[hol_db_def] THEN
    TOP_CASE_TAC THEN TOP_CASE_TAC THENL
     [SUBGOAL_THEN `FLOOKUP (SND (sig:sig)) a0 = SOME (y:hol_type)` ASSUME_TAC THENL
       [QPAT_X_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
        STRIP_TAC THEN
        QPAT_X_ASSUM "!tmnm. tmnm IN FDOM th ==> _" (MP_TAC o SPEC `a0:mlstring`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_FAPPLY]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      QPAT_X_ASSUM "FLOOKUP (SND (esubst_sig _ _)) _ = _"
        (MP_TAC o REWRITE_RULE[tmsof_esubst_sig; FLOOKUP_o_f]) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      QSPECL_THEN ["ty_esubst (s,th) y"; "TYPE_SUBST i (ty_esubst (s,th) y)"]
        MP_TAC match_type_complete THEN
      ASM_REWRITE_TAC[distinctness "option"] THEN MESON_TAC[];
      MATCH_MP_TAC INST_dbINST THEN
      QPAT_X_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
      STRIP_TAC THEN
      QPAT_X_ASSUM "!tmnm. tmnm IN FDOM th ==> _" (MP_TAC o SPEC `a0:mlstring`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_FAPPLY]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      MESON_TAC[term_ok_welltyped]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC db_esubst_tm_bind THEN
    QPAT_X_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def]) THEN STRIP_TAC THEN
    REWRITE_TAC[SND] THEN REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_FAPPLY] THEN STRIP_TAC THEN
    QPAT_X_ASSUM "!tmnm. tmnm IN FDOM th ==> _" (MP_TAC o SPEC `m:mlstring`) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[term_ok_welltyped]]);;

let db_esubst_thm = prove
 (`!sig sigma tm avds.
     esubsts_ok sig sigma /\ hol_term_ok sig tm
     ==> hol_db (esubst sigma avds tm) = db_esubst sigma (hol_db tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[db_esubst_def; esubst_def; esubst_ty_def] THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  QSPECL_THEN ["sig"; "sigma"; "tm"; "[]:(hol_term#hol_term)list"; "v"; "avds"] MP_TAC
    db_esubst_ty_thm THEN
  ASM_REWRITE_TAC[MEM] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC db_esubst_tm_thm THEN QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC esubst_ty0_term_ok THEN ASM_MESON_TAC[MEM]);;

(* HOL4: copied from holConservativeScript (whose body is one comment) *)
let CLOSED_INST = prove
 (`!tm tysubst. CLOSED tm /\ welltyped tm ==> CLOSED (INST tysubst tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  MP_TAC(ISPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                 `tysubst:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[RESULT_def; CLOSED_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN ASM_MESON_TAC[]);;

let RACONV_REFL2 = prove
 (`!tm env.
     (!x ty. VFREE_IN (hol_Var x ty) tm ==> ALPHAVARS env (hol_Var x ty,hol_Var x ty))
     ==> RACONV env (tm,tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[VFREE_IN_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC (CONJUNCT1 RACONV_rules) THEN ASM_MESON_TAC[];
    REWRITE_TAC[RACONV_rules];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 (CONJUNCTS RACONV_rules)) THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 3 (CONJUNCTS RACONV_rules)) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ALPHAVARS_def; PAIR_EQ] THEN
    ASM_MESON_TAC[]]);;

let CLOSED_RACONV_REFL = prove
 (`!tm env. CLOSED tm ==> RACONV env (tm,tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RACONV_REFL2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN ASM_MESON_TAC[]);;

(* esubst_tm on a constant: unchanged, or an instance of a closed welltyped
   replacement (match_type cannot fail on a term_ok constant) *)
let CLITAUX_esubst_tm_Const = prove
 (`!sig sigma n ty.
     esubsts_ok sig sigma /\ hol_term_ok (esubst_sig sigma sig) (hol_Const n ty)
     ==> esubst_tm sigma (hol_Const n ty) = hol_Const n ty \/
         (?tyin repl. esubst_tm sigma (hol_Const n ty) = INST tyin repl /\
                      CLOSED repl /\ welltyped repl)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:(mlstring,mlstring list#hol_type)fmap`;
                       `th:(mlstring,hol_term#hol_type)fmap`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[esubst_tm_def; hol_term_ok_def] THEN STRIP_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[] THEN TOP_CASE_TAC THEN TOP_CASE_TAC THENL
   [SUBGOAL_THEN `FLOOKUP (SND (sig:sig)) n = SOME (y:hol_type)` ASSUME_TAC THENL
     [QPAT_X_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
      STRIP_TAC THEN
      QPAT_X_ASSUM "!tmnm. tmnm IN FDOM th ==> _" (MP_TAC o SPEC `n:mlstring`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_FAPPLY]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    QPAT_X_ASSUM "FLOOKUP (SND (esubst_sig _ _)) _ = _"
      (MP_TAC o REWRITE_RULE[tmsof_esubst_sig; FLOOKUP_o_f]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    QSPECL_THEN ["ty_esubst (s,th) y"; "TYPE_SUBST i (ty_esubst (s,th) y)"]
      MP_TAC match_type_complete THEN
    ASM_REWRITE_TAC[distinctness "option"] THEN MESON_TAC[];
    DISJ2_TAC THEN QEXISTS_TAC "a'" THEN QEXISTS_TAC "x" THEN REWRITE_TAC[] THEN
    QPAT_X_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
    STRIP_TAC THEN
    QPAT_X_ASSUM "!tmnm. tmnm IN FDOM th ==> _" (MP_TAC o SPEC `n:mlstring`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_FAPPLY]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    MESON_TAC[term_ok_welltyped]]);;

let esubst_tm_RACONV = prove
 (`!sig sigma tm1 tm2 env.
     esubsts_ok sig sigma /\
     hol_term_ok (esubst_sig sigma sig) tm1 /\
     hol_term_ok (esubst_sig sigma sig) tm2 /\
     RACONV env (tm1,tm2)
     ==> RACONV env (esubst_tm sigma tm1,esubst_tm sigma tm2)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "RACONV _ _" (MP_TAC o ONCE_REWRITE_RULE[RACONV_cases]) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "hol_term"; distinctness "hol_term"] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THENL
   [ASM_REWRITE_TAC[esubst_tm_def] THEN MATCH_MP_TAC(CONJUNCT1 RACONV_rules) THEN
    ASM_REWRITE_TAC[];
    QSPECL_THEN ["sig"; "sigma"; "x"; "ty"] MP_TAC CLITAUX_esubst_tm_Const THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[RACONV_rules] THEN
    MATCH_MP_TAC CLOSED_RACONV_REFL THEN MATCH_MP_TAC CLOSED_INST THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[hol_term_ok_def]) THEN ASM_REWRITE_TAC[esubst_tm_def] THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS RACONV_rules)) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    QPAT_X_ASSUM "hol_term_ok _ (hol_Abs v1 t1)"
      (STRIP_ASSUME_TAC o REWRITE_RULE[hol_term_ok_def]) THEN
    QPAT_X_ASSUM "hol_term_ok _ (hol_Abs v2 t2)"
      (STRIP_ASSUME_TAC o REWRITE_RULE[hol_term_ok_def]) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    REWRITE_TAC[esubst_tm_def] THEN
    MATCH_MP_TAC(el 3 (CONJUNCTS RACONV_rules)) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 quantifies an unused env here (of a type variable) *)
let esubst_tm_ACONV = prove
 (`!sig sigma tm1 tm2 (env:A).
     esubsts_ok sig sigma /\
     hol_term_ok (esubst_sig sigma sig) tm1 /\
     hol_term_ok (esubst_sig sigma sig) tm2 /\
     ACONV tm1 tm2
     ==> ACONV (esubst_tm sigma tm1) (esubst_tm sigma tm2)`,
  REWRITE_TAC[ACONV_def] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_tm_RACONV THEN
  QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[]);;

(* HOL4: Theorem esubst_ty0_type = cj 1 $ cj 3 esubst_ty0_impossible1 *)
let esubst_ty0_type = prove
 (`!sig env sigma avds tm.
     esubsts_ok sig sigma /\
     (!k v. MEM (v,k) env
            ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     hol_term_ok sig tm
     ==> !subst_tm. esubst_ty0 env sigma avds tm = errorMonad_return subst_tm
                    ==> typeof subst_tm = ty_esubst sigma (typeof tm)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP esubst_ty0_impossible1) THEN
  SIMP_TAC[]);;

let esubst_equation = prove
 (`!sig sigma avds tm1 tm2.
     esubsts_ok sig sigma /\ hol_term_ok sig tm1 /\ hol_term_ok sig tm2 /\ is_std_sig sig
     ==> esubst sigma avds (tm1 === tm2) = esubst sigma avds tm1 === esubst sigma avds tm2`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:(mlstring,mlstring list#hol_type)fmap`;
                       `th:(mlstring,hol_term#hol_type)fmap`] THEN REPEAT STRIP_TAC THEN
  QSPECL_THEN ["(s,th)"; "tm1"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v1:hol_term`) THEN
  QSPECL_THEN ["(s,th)"; "tm2"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v2:hol_term`) THEN
  REWRITE_TAC[esubst_def; esubst_ty_def; equation_def] THEN
  ASM_REWRITE_TAC[esubst_ty0_def; errorMonad_bind_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[esubst_tm_def] THEN
  SUBGOAL_THEN `FLOOKUP (th:(mlstring,hol_term#hol_type)fmap) (implode "=") = NONE`
    SUBST1_TAC THENL
   [QPAT_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def; FDOM_FLOOKUP]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `typeof (esubst_tm (s,th) v1) = ty_esubst (s,th) (typeof tm1)` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `typeof (v1:hol_term)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC typeof_esubst_tm_esubst_ty0 THEN ASM_MESON_TAC[MEM];
      MATCH_MP_TAC typeof_esubst_ty THEN ASM_MESON_TAC[MEM]];
    ALL_TAC] THEN
  QSPECL_THEN ["sig"; "(s,th)"] MP_TAC ty_esubst_fun THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  QSPECL_THEN ["(s,th)"] MP_TAC ty_esubst_bool THEN
  QPAT_ASSUM "esubsts_ok _ _" (MP_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
  SIMP_TAC[FST]);;

let esubst_tm_abs = prove
 (`!sigma v body. esubst_tm sigma (hol_Abs v body) = hol_Abs v (esubst_tm sigma body)`,
  REWRITE_TAC[esubst_tm_def]);;
let _ = cake_add_simps [esubst_tm_abs];;

let in_frange_o_f = prove
 (`!x (f:B->C) (fm:(A,B)fmap).
     x IN FRANGE (f o_f fm) ==> ?y. y IN FRANGE fm /\ x = f y`,
  REWRITE_TAC[GSYM IMAGE_FRANGE; IN_IMAGE] THEN MESON_TAC[]);;

let theory_ok_esubst_axs = prove
 (`!sig axs sigma avds.
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma
     ==> theory_ok (esubst_sig sigma sig,IMAGE (esubst sigma avds) axs)`,
  REPEAT STRIP_TAC THEN
  QPAT_ASSUM "theory_ok _" (MP_TAC o REWRITE_RULE[theory_ok_def; FST; SND]) THEN STRIP_TAC THEN
  REWRITE_TAC[theory_ok_def; FST; SND; tysof_esubst_sig; tmsof_esubst_sig] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP in_frange_o_f) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC esubsts_ok_type_ok THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_term_ok THEN QEXISTS_TAC "axs" THEN ASM_MESON_TAC[];
      MATCH_MP_TAC esubst_has_type_bool THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
      ASM_MESON_TAC[]];
    MATCH_MP_TAC esubst_sig_is_std_sig THEN ASM_REWRITE_TAC[]]);;

let esubst_ty0_env_aconv_alt = prove
 (`!sig sigma tm1 tm2 thy axs avds subst_tm1 subst_tm2 env1 env2.
     esubsts_ok sig sigma /\
     hol_term_ok sig tm1 /\
     hol_term_ok sig tm2 /\
     theory_ok (thy,axs) /\
     (!s s'. MEM (s,s') env1
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty)) /\
     (!s s'. MEM (s,s') env2
             ==> ?x ty. s = hol_Var x ty /\ s' = hol_Var x (ty_esubst sigma ty)) /\
     welltyped subst_tm1 /\ welltyped subst_tm2 /\
     ACONV tm1 tm2 /\
     esubst_ty0 env1 sigma avds tm1 = errorMonad_return subst_tm1 /\
     esubst_ty0 env2 sigma avds tm2 = errorMonad_return subst_tm2
     ==> ACONV subst_tm1 subst_tm2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (tm1:hol_term) /\ welltyped (tm2:hol_term)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  ASM_SIMP_TAC[ACONV_db] THEN
  QSPECL_THEN ["sig"; "sigma"; "tm1"; "env1"; "subst_tm1"; "avds"] MP_TAC db_esubst_ty_thm THEN
  QSPECL_THEN ["sig"; "sigma"; "tm2"; "env2"; "subst_tm2"; "avds"] MP_TAC db_esubst_ty_thm THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ASM_MESON_TAC[ACONV_db]);;

let ACONV_EQ = prove
 (`!x y. x = y ==> ACONV x y`,
  SIMP[ACONV_REFL]);;

let esubst_ty0_env_aconv = prove
 (`!sig sigma thy axs avds tm subst_tm1 subst_tm2 env1 env2.
     esubsts_ok sig sigma /\
     hol_term_ok sig tm /\
     theory_ok (thy,axs) /\
     (!k v. MEM (v,k) env1
            ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     (!k v. MEM (v,k) env2
            ==> ?n ty. k = hol_Var n (ty_esubst sigma ty) /\ v = hol_Var n ty) /\
     welltyped subst_tm1 /\ welltyped subst_tm2 /\
     esubst_ty0 env1 sigma avds tm = errorMonad_return subst_tm1 /\
     esubst_ty0 env2 sigma avds tm = errorMonad_return subst_tm2
     ==> ACONV subst_tm1 subst_tm2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (tm:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  ASM_SIMP_TAC[ACONV_db] THEN
  QSPECL_THEN ["sig"; "sigma"; "tm"; "env1"; "subst_tm1"; "avds"] MP_TAC db_esubst_ty_thm THEN
  QSPECL_THEN ["sig"; "sigma"; "tm"; "env2"; "subst_tm2"; "avds"] MP_TAC db_esubst_ty_thm THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let ACONV_ABS = prove
 (`!x ty t1 t2.
     welltyped t1 /\ welltyped t2 /\ ACONV t1 t2
     ==> ACONV (hol_Abs (hol_Var x ty) t1) (hol_Abs (hol_Var x ty) t2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (hol_Abs (hol_Var x ty) t1) /\ welltyped (hol_Abs (hol_Var x ty) t2)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ACONV_db] THEN REWRITE_TAC[hol_db_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[ACONV_db]);;

let esubst_welltyped = prove
 (`!sig axs sigma tm avds.
     theory_ok (sig,axs) /\
     hol_term_ok sig tm /\
     esubsts_ok sig sigma
     ==> welltyped (esubst sigma avds tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_welltyped THEN QEXISTS_TAC "esubst_sig sigma sig" THEN
  MATCH_MP_TAC esubst_term_ok THEN QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[]);;

let replace_binder_ACONV = prove
 (`!sig x y ty body.
     hol_term_ok sig (hol_Abs (hol_Var x ty) body) /\
     ~VFREE_IN (hol_Var y ty) body
     ==> ACONV (hol_Abs (hol_Var x ty) body)
               (hol_Abs (hol_Var y ty) (VSUBST [(hol_Var y ty,hol_Var x ty)] body))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok sig (body:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[hol_term_ok_def]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (body:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST [(hol_Var y ty,hol_Var x ty)] body)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
    MESON_TAC[has_type_rules];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hol_Abs (hol_Var x ty) body`;
                 `hol_Abs (hol_Var y ty) (VSUBST [(hol_Var y ty,hol_Var x ty)] body)`]
                   ACONV_db) THEN
  ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ANTS_TAC THENL [MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; injectivity "dbterm"] THEN
  MP_TAC(ISPECL [`body:hol_term`; `[(hol_Var y ty,hol_Var x ty)]`] VSUBST_dbVSUBST) THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
   [MESON_TAC[WELLTYPED_CLAUSES]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MAP; hol_db_def] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[hol_db_def] THEN
  MP_TAC(ISPECL [`hol_db body`; `(y:mlstring,ty:hol_type)`; `(x:mlstring,ty:hol_type)`; `0`;
                 `[]:(dbterm#dbterm)list`] bind_dbVSUBST_cons) THEN
  REWRITE_TAC[UNCURRY_DEF; dbVSUBST_nil] THEN ANTS_TAC THENL
   [REWRITE_TAC[dbVFREE_IN_bind; UNCURRY_DEF] THEN ASM_SIMP_TAC[CLITAUX_dbVFREE_IN_dbVar];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let ty_esubst_no_tycons = prove
 (`!ty (sigma:(mlstring,mlstring list#hol_type)fmap#A).
     DISJOINT (tycons ty) (FDOM (FST sigma)) ==> ty_esubst sigma ty = ty`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[ty_esubst_def; tycons_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (FST (sigma:(mlstring,mlstring list#hol_type)fmap#A)) m = NONE`
    SUBST1_TAC THENL
   [REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SIMP[injectivity "hol_type"; MAP_EQ_ID; GSYM ALL_MEM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:hol_type`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_UNIONS; IN_IMAGE;
              IN_SET_OF_LIST; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let tycons_TYPE_SUBST = prove
 (`!ty i.
     tycons (TYPE_SUBST i ty) SUBSET
     tycons ty UNION UNIONS (IMAGE (tycons o FST) (set_of_list i))`,
  MATCH_MP_TAC type_ind THEN REWRITE_TAC[tycons_def; TYPE_SUBST_def] THEN CONJ_TAC THENL
   [GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD_def; tycons_def; EMPTY_SUBSET] THEN
    PAIR_CASES_ON `h:hol_type#hol_type` THEN REWRITE_TAC[REV_ASSOCD_def] THEN
    REWRITE_TAC[set_of_list; IMAGE_CLAUSES; UNIONS_INSERT; o_THM] THEN
    COND_CASES_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNION; UNIONS_IMAGE; IN_ELIM_THM; IN_SET_OF_LIST; MEM_MAP;
              IN_SING; o_THM] THEN
  X_GEN_TAC `c:mlstring` THEN STRIP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN RENAME1 "MEM xx l" THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xx:hol_type`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `i:(hol_type#hol_type)list`) THEN
  REWRITE_TAC[SUBSET; IN_UNION; UNIONS_IMAGE; IN_ELIM_THM; IN_SET_OF_LIST; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `c:mlstring`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ty_esubst_idempotent = prove
 (`!sig sigma ty.
     esubsts_ok sig sigma ==> ty_esubst sigma (ty_esubst sigma ty) = ty_esubst sigma ty`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:(mlstring,mlstring list#hol_type)fmap`;
                       `th:(mlstring,hol_term#hol_type)fmap`] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ty_esubst_no_tycons THEN REWRITE_TAC[FST] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[esubsts_ok_def]) THEN
  SPEC_TAC(`ty:hol_type`,`ty:hol_type`) THEN MATCH_MP_TAC type_ind THEN
  REWRITE_TAC[ty_esubst_def; tycons_def; DISJOINT_EMPTY; FST] THEN
  REPEAT STRIP_TAC THEN TOP_CASE_TAC THENL
   [SUBGOAL_THEN `~((m:mlstring) IN FDOM (s:(mlstring,mlstring list#hol_type)fmap))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FDOM_FLOOKUP]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    REWRITE_TAC[tycons_def; DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_SING; UNIONS_IMAGE;
                IN_ELIM_THM; IN_SET_OF_LIST; MEM_MAP; NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
    ASM_MESON_TAC[];
    TOP_CASE_TAC THEN
    W(MP_TAC o PART_MATCH lhand tycons_TYPE_SUBST o lhand o snd) THEN
    MATCH_MP_TAC(SET_RULE `DISJOINT (t:mlstring->bool) u ==> s SUBSET t ==> DISJOINT s u`) THEN
    SUBGOAL_THEN `DISJOINT (tycons y) (FDOM (s:(mlstring,mlstring list#hol_type)fmap))`
      ASSUME_TAC THENL
     [QPAT_X_ASSUM "!tynm. tynm IN FDOM s ==> _" (MP_TAC o SPEC `m:mlstring`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_FAPPLY]) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; UNIONS_IMAGE; IN_ELIM_THM;
                IN_SET_OF_LIST; NOT_IN_EMPTY; o_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `c:mlstring` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `~((a \/ b) /\ c) <=> (a ==> ~c) /\ (b ==> ~c)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:hol_type#hol_type` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_ZIP_FST) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEM_TAKE) THEN REWRITE_TAC[MEM_MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:hol_type` STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:hol_type`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]]);;

let esubst_ACONV = prove
 (`!sig axs sigma avds1 avds2 tm1 tm2.
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma /\
     hol_term_ok sig tm1 /\
     hol_term_ok sig tm2 /\
     ACONV tm1 tm2
     ==> ACONV (esubst sigma avds1 tm1) (esubst sigma avds2 tm2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[esubst_def] THEN MATCH_MP_TAC esubst_tm_ACONV THEN
  QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[esubst_ty_term_ok];
    ASM_MESON_TAC[esubst_ty_term_ok];
    QSPECL_THEN ["sigma"; "tm1"; "sig"; "avds1"] MP_TAC esubst_ty0_always_returns THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v1:hol_term`) THEN
    QSPECL_THEN ["sigma"; "tm2"; "sig"; "avds2"] MP_TAC esubst_ty0_always_returns THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v2:hol_term`) THEN
    ASM_REWRITE_TAC[esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `welltyped (v1:hol_term) /\ welltyped (v2:hol_term) /\
                  welltyped (tm1:hol_term) /\ welltyped (tm2:hol_term)`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC term_ok_welltyped THENL
       [QEXISTS_TAC "esubst_sig sigma sig" THEN MATCH_MP_TAC esubst_ty0_term_ok THEN
        ASM_MESON_TAC[MEM];
        QEXISTS_TAC "esubst_sig sigma sig" THEN MATCH_MP_TAC esubst_ty0_term_ok THEN
        ASM_MESON_TAC[MEM];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ACONV_db] THEN
    QSPECL_THEN ["sig"; "sigma"; "tm1"; "[]:(hol_term#hol_term)list"; "v1"; "avds1"] MP_TAC
      db_esubst_ty_thm THEN
    QSPECL_THEN ["sig"; "sigma"; "tm2"; "[]:(hol_term#hol_term)list"; "v2"; "avds2"] MP_TAC
      db_esubst_ty_thm THEN
    ASM_REWRITE_TAC[MEM] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    AP_TERM_TAC THEN ASM_MESON_TAC[ACONV_db]]);;

let esubst_binder_fresh_on_hyps = prove
 (`!ty h1 y hyps.
     MEM h1 hyps /\
     ~MEM y (FLAT (MAP tm_names hyps))
     ==> ~VFREE_IN (hol_Var y ty) h1`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP VFREE_IN_tm_names) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[]);;

let esubst_ty0_abs_avds_binder = prove
 (`!sigma avds sig x y ty l.
     hol_term_ok sig l /\
     type_ok (FST sig) ty /\
     esubsts_ok sig sigma /\
     ~MEM y (tm_names l)
     ==> ?body1. esubst_ty0 [(hol_Var y ty,hol_Var y (ty_esubst sigma ty))] sigma avds
                            (VSUBST [(hol_Var y ty,hol_Var x ty)] l) =
                 errorMonad_return body1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM neq_error] THEN X_GEN_TAC `e:hol_term` THEN
  DISCH_TAC THEN
  QSPECL_THEN ["[(hol_Var y ty,hol_Var y (ty_esubst sigma ty))]"; "sigma"; "avds";
               "VSUBST [(hol_Var y ty,hol_Var x ty)] l"; "sig"] MP_TAC esubst_ty0_impossible1 THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN CONJ_TAC THENL
     [MESON_TAC[]; MATCH_MP_TAC term_ok_vsubst_variant THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:hol_term` o CONJUNCT1) THEN ASM_REWRITE_TAC[REV_ASSOCD_def] THEN
  STRIP_TAC THEN
  QPAT_X_ASSUM "(if _ then _ else _) = _" MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "hol_term"] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN STRIP_TAC THEN
    QSPECL_THEN ["l"; "n"; "typ1"; "y"; "x"; "ty"; "sig"] MP_TAC FVs_VSUBST_CASES THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FVs_in_tm_names];
    ASM_MESON_TAC[]]);;

let esubst_has_type1 = prove
 (`!sig axs sigma avds tm ty.
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma /\
     hol_term_ok sig tm /\
     tm has_type ty
     ==> esubst sigma avds tm has_type ty_esubst sigma ty`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_has_type THEN QEXISTS_TAC "sig" THEN
  QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[] THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped (v:hol_term)` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_welltyped THEN QEXISTS_TAC "esubst_sig sigma sig" THEN
    MATCH_MP_TAC esubst_ty0_term_ok THEN ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  ASM_SIMP_TAC[typeof_has_type] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP WELLTYPED_LEMMA) THEN
  MATCH_MP_TAC esubst_ty0_ty_esubst THEN ASM_MESON_TAC[MEM]);;

let FILTER_empty = prove
 (`!lst:A list. FILTER (\p. ~MEM p lst) lst = []`,
  GEN_TAC THEN REWRITE_TAC[FILTER_EQ_NIL; GSYM ALL_MEM] THEN SIMP_TAC[]);;
let _ = cake_add_simps [FILTER_empty];;

let VSUBST_equation = prove
 (`!sig a b ilist.
     hol_term_ok sig a /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)
     ==> VSUBST ilist (a === b) = VSUBST ilist a === VSUBST ilist b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equation_def; VSUBST_def] THEN
  SUBGOAL_THEN `typeof (VSUBST ilist a) = typeof a` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC WELLTYPED_LEMMA THEN MATCH_MP_TAC VSUBST_HAS_TYPE THEN
  ASM_REWRITE_TAC[GSYM WELLTYPED] THEN ASM_MESON_TAC[term_ok_welltyped]);;

let VSUBST_sing_var = prove
 (`!z y x ty.
     VSUBST [(z,y)] (hol_Var x ty) = if hol_Var x ty = y then z else hol_Var x ty`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VSUBST_def; REV_ASSOCD_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let _ = cake_add_simps [VSUBST_sing_var];;

let INST_COMB = prove
 (`!tyin e1 e2.
     welltyped e1 /\ welltyped e2
     ==> INST tyin (hol_Comb e1 e2) = hol_Comb (INST tyin e1) (INST tyin e2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def; INST_CORE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[NOT_IS_CLASH_IS_RESULT; INST_CORE_NIL_IS_RESULT; RESULT_def]);;

let ACONV_COMB = prove
 (`!a b x y. ACONV (hol_Comb a b) (hol_Comb x y) <=> ACONV a x /\ ACONV b y`,
  REWRITE_TAC[ACONV_def] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RACONV_cases] THEN
  REWRITE_TAC[injectivity "hol_term"; distinctness "hol_term"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* HOL4 refl_aconv_tac: an ACONV goal from an equation *)
let CLITAUX_refl_aconv_tac = MATCH_MP_TAC ACONV_EQ;;
