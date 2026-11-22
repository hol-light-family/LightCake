(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 6 (HOL4 lines      *)
(* 4409-5195): beta-redexes and binders under the steps, db_ok,              *)
(* unbind, alpha-renaming of binders.                                        *)
(* ========================================================================= *)

needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem_p5.ml";;

prioritize_num();;
type_invention_error := true;;

(* two double de Bruijn substitutions agree if they agree on the free variables *)
let CLITAUX_dbVSUBST2_frees = prove
 (`!t l1 l2 m1 m2.
     (!x ty. dbVFREE_IN (dbVar x ty) t
             ==> dbVSUBST l2 (REV_ASSOCD (dbVar x ty) l1 (dbVar x ty)) =
                 dbVSUBST m2 (REV_ASSOCD (dbVar x ty) m1 (dbVar x ty)))
     ==> dbVSUBST l2 (dbVSUBST l1 t) = dbVSUBST m2 (dbVSUBST m1 t)`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbVSUBST_def; dbVFREE_IN_def; injectivity "dbterm"] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let CLITAUX_dbVSUBST_single_notfree = prove
 (`!t u k. ~dbVFREE_IN k t ==> dbVSUBST [(u,k)] t = t`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM dbVSUBST_nil] THEN
  MATCH_MP_TAC dbVSUBST_frees THEN REWRITE_TAC[REV_ASSOCD] THEN ASM_MESON_TAC[]);;

let CLITAUX_REV_ASSOCD_FILTER_neq = prove
 (`!(l:(hol_term#hol_term)list) k x d.
     REV_ASSOCD x (FILTER (\(s',s). ~(s = k)) l) d =
     if x = k then d else REV_ASSOCD x l d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; REV_ASSOCD] THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN REWRITE_TAC[FILTER] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN ASM_MESON_TAC[]);;

let CLITAUX_VSUBST_Abs_ty = prove
 (`!l n ty b z ty' b'.
     VSUBST l (hol_Abs (hol_Var n ty) b) = hol_Abs (hol_Var z ty') b' ==> ty' = ty`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VSUBST_def; dest_var_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[]);;

let VSUBST_Abs_beta_ACONV = prove
 (`!bd v ty l n n' ty' bd'.
     welltyped bd /\ welltyped v /\ v has_type ty /\
     (!s s'. MEM (s',s) l ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ welltyped s') /\
     VSUBST l (hol_Abs (hol_Var n ty) bd) = hol_Abs (hol_Var n' ty') bd'
     ==> ACONV (VSUBST [(VSUBST l v,hol_Var n' ty')] bd')
               (VSUBST l (VSUBST [(v,hol_Var n ty)] bd))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "EQ"))))) THEN
  SUBGOAL_THEN `!k v'. MEM (v',k) (l:(hol_term#hol_term)list)
                       ==> welltyped v' /\ ?a b. k = hol_Var a b` (LABEL_TAC "LK") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun m -> USE_THEN "L" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (l:(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty` (LABEL_TAC "LT") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun m -> USE_THEN "L" (fun h -> MP_TAC(MATCH_MP h m))) THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ty':hol_type = ty` SUBST_ALL_TAC THENL
   [USE_THEN "EQ" (MP_TAC o MATCH_MP CLITAUX_VSUBST_Abs_ty) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped bd'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hol_Abs (hol_Var n ty) bd`; `ty:hol_type`;
                   `l:(hol_term#hol_term)list`] VSUBST_WELLTYPED) THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?L. bd' = VSUBST L bd /\
        (!k v'. MEM (v',k) L ==> welltyped v' /\ ?a b. k = hol_Var a b) /\
        REV_ASSOCD (hol_Var n ty) L (hol_Var n ty) = hol_Var n' ty /\
        (!a b. VFREE_IN (hol_Var a b) bd /\ ~(hol_Var a b = hol_Var n ty)
               ==> REV_ASSOCD (hol_Var a b) L (hol_Var a b) =
                   REV_ASSOCD (hol_Var a b) l (hol_Var a b) /\
                   ~VFREE_IN (hol_Var n' ty) (REV_ASSOCD (hol_Var a b) l (hol_Var a b)))`
    (X_CHOOSE_THEN `L:(hol_term#hol_term)list` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "LL") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LF")))))
    THENL
   [USE_THEN "EQ" MP_TAC THEN
    REWRITE_TAC[VSUBST_def; dest_var_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
    ABBREV_TAC `l' = FILTER (\(s',s). ~(s = hol_Var n ty)) (l:(hol_term#hol_term)list)` THEN
    SUBGOAL_THEN `!x d. REV_ASSOCD x (l':(hol_term#hol_term)list) d =
                        if x = hol_Var n ty then d else REV_ASSOCD x l d` (LABEL_TAC "RF") THENL
     [EXPAND_TAC "l'" THEN REWRITE_TAC[CLITAUX_REV_ASSOCD_FILTER_neq]; ALL_TAC] THEN
    SUBGOAL_THEN `!k v'. MEM (v',k) (l':(hol_term#hol_term)list)
                         ==> ~(k = hol_Var n ty) /\ MEM (v',k) l` (LABEL_TAC "MF") THENL
     [EXPAND_TAC "l'" THEN REWRITE_TAC[MEM_FILTER] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[injectivity "hol_term"] THEN STRIP_TAC THENL
     [QPAT_X_ASSUM "VARIANT _ _ _ = _"
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
        SUBGOAL_THEN `~VFREE_IN (hol_Var n' ty) (VSUBST l' bd)` ASSUME_TAC THENL
         [QPAT_X_ASSUM "VARIANT _ _ _ = _" (SUBST1_TAC o SYM) THEN REWRITE_TAC[VARIANT_THM];
          ALL_TAC] THEN
        EXISTS_TAC `CONS (hol_Var n' ty,hol_Var n ty) (l':(hol_term#hol_term)list)` THEN
        ASM_REWRITE_TAC[REV_ASSOCD; MEM; PAIR_EQ] THEN REPEAT CONJ_TAC THENL
         [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THENL
           [MESON_TAC[]; ASM_MESON_TAC[]];
          MAP_EVERY X_GEN_TAC [`a:mlstring`; `b:hol_type`] THEN STRIP_TAC THEN
          SUBGOAL_THEN `~(hol_Var a b = hol_Var n ty) /\ ~(hol_Var n ty = hol_Var a b)`
            STRIP_ASSUME_TAC THENL
           [REWRITE_TAC[injectivity "hol_term"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~VFREE_IN (hol_Var n' ty) (VSUBST l' bd)` THEN
          MP_TAC(ISPECL [`bd:hol_term`; `n':mlstring`; `ty:hol_type`; `l':(hol_term#hol_term)list`]
                        VFREE_IN_VSUBST) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[NOT_EXISTS_THM] THEN
          DISCH_THEN(MP_TAC o SPECL [`a:mlstring`; `b:hol_type`]) THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `n:mlstring = n'` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        EXISTS_TAC `l':(hol_term#hol_term)list` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [REPEAT GEN_TAC THEN
          DISCH_THEN(fun m -> USE_THEN "MF" (fun h -> MP_TAC(MATCH_MP h m))) THEN ASM_MESON_TAC[];
          MAP_EVERY X_GEN_TAC [`a:mlstring`; `b:hol_type`] THEN STRIP_TAC THEN
          SUBGOAL_THEN `~(hol_Var a b = hol_Var n ty)` ASSUME_TAC THENL
           [REWRITE_TAC[injectivity "hol_term"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~EX (\(s',s). VFREE_IN (hol_Var n ty) s' /\ VFREE_IN s bd)
                           (l':(hol_term#hol_term)list)` THEN
          EXPAND_TAC "l'" THEN
          REWRITE_TAC[GSYM EX_MEM; MEM_FILTER; EXISTS_PAIR_THM] THEN
          CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
          MP_TAC(ISPECL [`l:(hol_term#hol_term)list`; `hol_Var a b`; `hol_Var a b`]
                        REV_ASSOCD_MEM) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[VFREE_IN_def] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `VSUBST l v has_type ty` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[] THEN USE_THEN "LT" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST l v)` ASSUME_TAC THENL
   [REWRITE_TAC[welltyped_def] THEN EXISTS_TAC `ty:hol_type` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST [(v,hol_Var n ty)] bd)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`VSUBST [(VSUBST l v,hol_Var n' ty)] bd'`;
                 `VSUBST l (VSUBST [(v,hol_Var n ty)] bd)`] ACONV_db) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`bd':hol_term`; `[(VSUBST l v,hol_Var n' ty)]`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`VSUBST [(v:hol_term,hol_Var n ty)] bd`; `l:(hol_term#hol_term)list`]
                VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "LK" MATCH_ACCEPT_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`bd:hol_term`; `[(v:hol_term,hol_Var n ty)]`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`bd:hol_term`; `L:(hol_term#hol_term)list`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[hol_db_def] THEN
  MATCH_MP_TAC CLITAUX_dbVSUBST2_frees THEN
  MAP_EVERY X_GEN_TAC [`a:mlstring`; `b:hol_type`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `VFREE_IN (hol_Var a b) bd` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`bd:hol_term`; `hol_Var a b`] dbVFREE_IN_VFREE_IN) THEN
    ASM_REWRITE_TAC[hol_db_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(hol_term#hol_term)list`; `a:mlstring`; `b:hol_type`] REV_ASSOCD_MAP_db) THEN
  ANTS_TAC THENL [USE_THEN "LL" MP_TAC THEN MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REV_ASSOCD; injectivity "dbterm"] THEN
  ASM_CASES_TAC `n:mlstring = a /\ ty:hol_type = b` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[hol_db_def; dbVSUBST_def; REV_ASSOCD] THEN
    MATCH_MP_TAC VSUBST_dbVSUBST THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "LK" MATCH_ACCEPT_TAC;
    SUBGOAL_THEN `~(hol_Var a b = hol_Var n ty)` ASSUME_TAC THENL
     [REWRITE_TAC[injectivity "hol_term"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "LF" (fun h -> MP_TAC(MATCH_MP h (CONJ (ASSUME `VFREE_IN (hol_Var a b) bd`)
                                   (ASSUME `~(hol_Var a b = hol_Var n ty)`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[dbVSUBST_def] THEN
    SUBGOAL_THEN `welltyped (REV_ASSOCD (hol_Var a b) l (hol_Var a b))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`l:(hol_term#hol_term)list`; `hol_Var a b`; `hol_Var a b`]
                    REV_ASSOCD_MEM) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:(hol_term#hol_term)list`; `a:mlstring`; `b:hol_type`] REV_ASSOCD_MAP_db) THEN
    ANTS_TAC THENL [USE_THEN "LK" MP_TAC THEN MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC CLITAUX_dbVSUBST_single_notfree THEN
    MP_TAC(ISPECL [`REV_ASSOCD (hol_Var a b) l (hol_Var a b)`; `hol_Var n' ty`]
                  dbVFREE_IN_VFREE_IN) THEN
    ASM_REWRITE_TAC[hol_db_def]]);;

let db_ok_def = cake_def
  `(db_ok k (dbVar x ty) <=> T) /\
   (db_ok k (dbBound m) <=> m < k) /\
   (db_ok k (dbConst x ty) <=> T) /\
   (db_ok k (dbComb t1 t2) <=> db_ok k t1 /\ db_ok k t2) /\
   (db_ok k (dbAbs ty t) <=> db_ok (k + 1) t)`;;
let _ = cake_add_simps [db_ok_def];;

let unbind_def = cake_def
  `(unbind u k (dbVar x ty) = dbVar x ty) /\
   (unbind u k (dbBound m) = if m = k then u else dbBound m) /\
   (unbind u k (dbConst x ty) = dbConst x ty) /\
   (unbind u k (dbComb t1 t2) = dbComb (unbind u k t1) (unbind u k t2)) /\
   (unbind u k (dbAbs ty t) = dbAbs ty (unbind u (k + 1) t))`;;
let _ = cake_add_simps [unbind_def];;

let db_ok_bind = prove
 (`!dbt v k. db_ok k dbt ==> db_ok (k + 1) (hol_bind v k dbt)`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[db_ok_def; hol_bind_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[db_ok_def] THEN
  TRY ASM_ARITH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let db_ok_db = prove
 (`!tm. db_ok 0 (hol_db tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[hol_db_def; db_ok_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC db_ok_bind THEN ASM_REWRITE_TAC[]);;

let unbind_bind = prove
 (`!dbt u x ty k.
     db_ok k dbt ==> unbind u k (hol_bind (x,ty) k dbt) = dbVSUBST [(u,dbVar x ty)] dbt`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[db_ok_def; hol_bind_def; unbind_def; dbVSUBST_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REV_ASSOCD; PAIR_EQ; injectivity "dbterm"] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[unbind_def; injectivity "dbterm"] THEN
  ASM_ARITH_TAC);;

let unbind_dbINST = prove
 (`!dbt u k tyin.
     unbind (dbINST tyin u) k (dbINST tyin dbt) = dbINST tyin (unbind u k dbt)`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[dbINST_def; unbind_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[dbINST_def]);;

let unbind_bind_0 = prove
 (`!dbt u x ty.
     db_ok 0 dbt ==> dbVSUBST [(u,dbVar x ty)] dbt = unbind u 0 (hol_bind (x,ty) 0 dbt)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC unbind_bind THEN
  ASM_REWRITE_TAC[]);;

let INST_Abs_beta_ACONV = prove
 (`!bd v ty tyin n n' ty' bd'.
     welltyped bd /\ welltyped v /\ v has_type ty /\
     INST tyin (hol_Abs (hol_Var n ty) bd) = hol_Abs (hol_Var n' ty') bd'
     ==> ACONV (VSUBST [(INST tyin v,hol_Var n' ty')] bd')
               (INST tyin (VSUBST [(v,hol_Var n ty)] bd))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (hol_Abs (hol_Var n ty) bd)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped bd'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hol_Abs (hol_Var n ty) bd`; `tyin:(hol_type#hol_type)list`]
                  INST_WELLTYPED) THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hol_Abs (hol_Var n ty) bd`; `tyin:(hol_type#hol_type)list`] INST_dbINST) THEN
  ASM_REWRITE_TAC[hol_db_def; dbINST_def; typeof_def; dest_var_def; injectivity "dbterm"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  SUBGOAL_THEN `INST tyin v has_type ty'` ASSUME_TAC THENL
   [MATCH_MP_TAC INST_HAS_TYPE THEN EXISTS_TAC `ty:hol_type` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST [(v,hol_Var n ty)] bd)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST [(INST tyin v,hol_Var n' ty')] bd')` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`VSUBST [(INST tyin v,hol_Var n' ty')] bd'`;
                 `INST tyin (VSUBST [(v,hol_Var n ty)] bd)`] ACONV_db) THEN
  ASM_SIMP_TAC[INST_WELLTYPED] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`bd':hol_term`; `[(INST tyin v,hol_Var n' ty')]`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[INST_WELLTYPED]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[INST_dbINST] THEN
  MP_TAC(ISPECL [`bd:hol_term`; `[(v:hol_term,hol_Var n ty)]`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[hol_db_def] THEN
  ASM_SIMP_TAC[INST_dbINST; unbind_bind_0; db_ok_db] THEN
  REWRITE_TAC[GSYM unbind_dbINST]);;

let CLITAUX_INST_Abs_ty = prove
 (`!tyin n ty b z ty' b'.
     welltyped b /\ INST tyin (hol_Abs (hol_Var n ty) b) = hol_Abs (hol_Var z ty') b'
     ==> ty' = TYPE_SUBST tyin ty`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hol_Abs (hol_Var n ty) b`; `tyin:(hol_type#hol_type)list`] INST_dbINST) THEN
  ASM_REWRITE_TAC[WELLTYPED_CLAUSES; hol_db_def; dbINST_def; typeof_def; injectivity "dbterm"] THEN
  ANTS_TAC THENL [MESON_TAC[]; MESON_TAC[]]);;

let apply_steps_Abs_has_type = prove
 (`!sig stps x x1 ty ty1 t t1.
     steps_ok sig stps /\ hol_term_ok sig (hol_Abs (hol_Var x ty) t) /\
     apply_steps stps (hol_Abs (hol_Var x ty) t) = hol_Abs (hol_Var x1 ty1) t1
     ==> apply_steps stps (hol_Var x ty) has_type ty1`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THENL
   [REWRITE_TAC[injectivity "hol_term"] THEN MESON_TAC[has_type_rules]; ALL_TAC] THEN
  QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `welltyped t'` ASSUME_TAC THENL
    [ASM_MESON_TAC[term_ok_welltyped; WELLTYPED_CLAUSES]; ALL_TAC]) THEN
  MP_TAC(ISPECL [`sig:sig`; `t:subst_step list`; `x:mlstring`; `ty:hol_type`; `t':hol_term`]
                apply_steps_Abs) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:mlstring` (X_CHOOSE_THEN `ty2:hol_type`
    (X_CHOOSE_THEN `bd2:hol_term` STRIP_ASSUME_TAC))) THEN
  LAST_X_ASSUM(MP_TAC o SPECL [`x:mlstring`; `n2:mlstring`; `ty:hol_type`; `ty2:hol_type`;
                               `t':hol_term`; `bd2:hol_term`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  QPAT_X_ASSUM "_ (apply_steps t _) = hol_Abs _ _" MP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(ASSUME_TAC o MATCH_MP CLITAUX_VSUBST_Abs_ty) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLITAUX_ilist_wk);
    DISCH_TAC THEN
    MP_TAC(ISPECL [`a:(hol_type#hol_type)list`; `n2:mlstring`; `ty2:hol_type`; `bd2:hol_term`;
                   `x1:mlstring`; `ty1:hol_type`; `t1:hol_term`] CLITAUX_INST_Abs_ty) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC INST_HAS_TYPE THEN EXISTS_TAC `ty2:hol_type` THEN ASM_REWRITE_TAC[]]);;

let apply_steps_Abs_beta = prove
 (`!sig stps x ty t n2 ty2 bd2.
     hol_term_ok sig (hol_Abs (hol_Var x ty) t) /\ steps_ok sig stps /\
     apply_steps stps (hol_Abs (hol_Var x ty) t) = hol_Abs (hol_Var n2 ty2) bd2
     ==> ACONV (VSUBST [(apply_steps stps (hol_Var x ty),hol_Var n2 ty2)] bd2)
               (apply_steps stps t)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THENL
   [REWRITE_TAC[injectivity "hol_term"] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    SUBGOAL_THEN `VSUBST [(hol_Var x ty,hol_Var x ty)] t = t` SUBST1_TAC THENL
     [MATCH_MP_TAC VSUBST_ID THEN EXISTS_TAC `sig:sig` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var x ty) t)` THEN
        REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[];
        REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[]];
      REWRITE_TAC[ACONV_REFL]];
    ALL_TAC] THEN
  QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def] THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `welltyped t'` ASSUME_TAC THENL
    [UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var x ty) t')` THEN
     REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
   MP_TAC(ISPECL [`sig:sig`; `t:subst_step list`; `x:mlstring`; `ty:hol_type`; `t':hol_term`]
                 apply_steps_Abs) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `n1:mlstring` (X_CHOOSE_THEN `ty1:hol_type`
     (X_CHOOSE_THEN `bd1:hol_term` STRIP_ASSUME_TAC))) THEN
   LAST_X_ASSUM(MP_TAC o SPECL [`x:mlstring`; `ty:hol_type`; `t':hol_term`; `n1:mlstring`;
                                `ty1:hol_type`; `bd1:hol_term`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`sig:sig`; `t:subst_step list`; `x:mlstring`; `n1:mlstring`; `ty:hol_type`;
                  `ty1:hol_type`; `t':hol_term`; `bd1:hol_term`] apply_steps_Abs_has_type) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `welltyped (apply_steps t (hol_Var x ty)) /\ welltyped (apply_steps t t')`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC apply_steps_welltyped THEN EXISTS_TAC `sig:sig` THEN
     ASM_REWRITE_TAC[WELLTYPED_CLAUSES]; ALL_TAC] THEN
   SUBGOAL_THEN `welltyped (VSUBST [(apply_steps t (hol_Var x ty),hol_Var n1 ty1)] bd1)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   QPAT_X_ASSUM "_ (apply_steps t _) = hol_Abs _ _" MP_TAC THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC) THENL
  [MATCH_MP_TAC ACONV_TRANS THEN
     EXISTS_TAC `VSUBST a (VSUBST [(apply_steps t (hol_Var x ty),hol_Var n1 ty1)] bd1)` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC VSUBST_Abs_beta_ACONV THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
       DISCH_THEN(fun m -> QPAT_ASSUM "!s s'. MEM (s',s) a ==> _"
      (fun h -> MP_TAC(MATCH_MP h m))) THEN
       MESON_TAC[term_ok_welltyped];
       MATCH_MP_TAC ACONV_VSUBST THEN ASM_REWRITE_TAC[] THEN
       REPEAT GEN_TAC THEN
       DISCH_THEN(fun m -> QPAT_ASSUM "!s s'. MEM (s',s) a ==> _"
      (fun h -> MP_TAC(MATCH_MP h m))) THEN
       MESON_TAC[]];
   MATCH_MP_TAC ACONV_TRANS THEN
     EXISTS_TAC `INST a (VSUBST [(apply_steps t (hol_Var x ty),hol_Var n1 ty1)] bd1)` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC INST_Abs_beta_ACONV THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC ACONV_INST THEN ASM_REWRITE_TAC[]]]);;

let db_esubst_dbAbs = prove
 (`!sigma ty body.
     db_esubst sigma (dbAbs ty body) = dbAbs (ty_esubst sigma ty) (db_esubst sigma body)`,
  REWRITE_TAC[db_esubst_def; db_esubst_ty_def; db_esubst_tm_def]);;

let unbind_db_esubst_ty = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) dbt u k.
     unbind (db_esubst_ty sigma u) k (db_esubst_ty sigma dbt) =
     db_esubst_ty sigma (unbind u k dbt)`,
  GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[db_esubst_ty_def; unbind_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[db_esubst_ty_def]);;

let unbind_db_ok = prove
 (`!dbt n u k. db_ok n dbt /\ k >= n ==> unbind u k dbt = dbt`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[db_ok_def; unbind_def; injectivity "dbterm"] THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
                            ASM_ARITH_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n + 1` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let db_ok_dbINST = prove
 (`!dbt n tyin. db_ok n dbt ==> db_ok n (dbINST tyin dbt)`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[db_ok_def; dbINST_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let unbind_dbtm = prove
 (`!tm u k. unbind u k (hol_db tm) = hol_db tm`,
  MESON_TAC[unbind_db_ok; db_ok_db; ARITH_RULE `k >= 0`]);;

let unbind_dbINST_dbtm = prove
 (`!tm u k tyin. unbind u k (dbINST tyin (hol_db tm)) = dbINST tyin (hol_db tm)`,
  MESON_TAC[unbind_db_ok; db_ok_dbINST; db_ok_db; ARITH_RULE `k >= 0`]);;

let unbind_db_esubst_tm = prove
 (`!sigma dbt u k.
     unbind (db_esubst_tm sigma u) k (db_esubst_tm sigma dbt) =
     db_esubst_tm sigma (unbind u k dbt)`,
  GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[db_esubst_tm_def; unbind_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[db_esubst_tm_def];
    REPEAT TOP_CASE_TAC THEN REWRITE_TAC[unbind_def; unbind_dbINST_dbtm]]);;

let unbind_db_esubst = prove
 (`!sigma dbt u k.
     unbind (db_esubst sigma u) k (db_esubst sigma dbt) =
     db_esubst sigma (unbind u k dbt)`,
  REWRITE_TAC[db_esubst_def; unbind_db_esubst_tm; unbind_db_esubst_ty]);;

let esubst_Abs_beta_ACONV = prove
 (`!sig axs sigma avds n ty bd v n' bd'.
     hol_term_ok sig (hol_Abs (hol_Var n ty) bd) /\
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     hol_term_ok sig v /\ v has_type ty /\
     esubst sigma avds (hol_Abs (hol_Var n ty) bd) =
     hol_Abs (hol_Var n' (ty_esubst sigma ty)) bd'
     ==> ACONV (VSUBST [(esubst sigma [] v,hol_Var n' (ty_esubst sigma ty))] bd')
               (esubst sigma [] (VSUBST [(v,hol_Var n ty)] bd))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!tm avds. hol_term_ok sig tm ==> welltyped (esubst sigma avds tm)`
    (LABEL_TAC "W") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig bd /\ type_ok (FST sig) ty` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var n ty) bd)` THEN
    REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped bd /\ welltyped v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped bd'` ASSUME_TAC THENL
   [USE_THEN "W" (fun h -> MP_TAC(SPEC `avds:mlstring list`
      (MATCH_MP h (ASSUME `hol_term_ok sig (hol_Abs (hol_Var n ty) bd)`)))) THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `esubst sigma [] v has_type ty_esubst sigma ty` ASSUME_TAC THENL
   [MATCH_MP_TAC esubst_has_type1 THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (VSUBST [(v,hol_Var n ty)] bd)` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `hol_Abs (hol_Var n ty) bd`; `avds:mlstring list`] db_esubst_thm) THEN
  ASM_REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; db_esubst_dbAbs;
                  injectivity "dbterm"] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `welltyped (VSUBST [(esubst sigma [] v,hol_Var n' (ty_esubst sigma ty))] bd')`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`VSUBST [(esubst sigma [] v,hol_Var n' (ty_esubst sigma ty))] bd'`;
                 `esubst sigma [] (VSUBST [(v,hol_Var n ty)] bd)`] ACONV_db) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "W" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`bd':hol_term`; `[(esubst sigma [] v,hol_Var n' (ty_esubst sigma ty))]`]
                VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[welltyped_def];
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `VSUBST [(v,hol_Var n ty)] bd`; `[]:mlstring list`] db_esubst_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`bd:hol_term`; `[(v:hol_term,hol_Var n ty)]`] VSUBST_dbVSUBST) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `v:hol_term`; `[]:mlstring list`] db_esubst_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[hol_db_def] THEN
  SIMP_TAC[unbind_bind_0; db_ok_db] THEN ASM_REWRITE_TAC[GSYM unbind_db_esubst] THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `v:hol_term`; `[]:mlstring list`] db_esubst_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let esubst_apply_steps_Abs = prove
 (`!sig axs sigma avds x ty t stps.
     hol_term_ok sig t /\
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     type_ok (FST sig) ty /\ steps_ok sig stps
     ==> ?z ty' body.
           esubst sigma avds (apply_steps stps (hol_Abs (hol_Var x ty) t)) =
           hol_Abs (hol_Var z ty') body /\
           hol_term_ok (esubst_sig sigma sig) body /\
           type_ok (FST (esubst_sig sigma sig)) ty' /\
           esubst sigma [] (apply_steps stps (hol_Var x ty)) has_type ty' /\
           ACONV (VSUBST [(esubst sigma [] (apply_steps stps (hol_Var x ty)),
                           hol_Var z ty')] body)
                 (esubst sigma [] (apply_steps stps t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped t` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (hol_Abs (hol_Var x ty) t)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[hol_term_ok_def] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `ty:hol_type`; `t:hol_term`]
                apply_steps_Abs) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:mlstring` (X_CHOOSE_THEN `ty2:hol_type`
    (X_CHOOSE_THEN `bd2:hol_term` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `hol_term_ok sig (hol_Abs (hol_Var n2 ty2) bd2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_comb o lhs o concl)) THEN
    MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok sig (apply_steps stps (hol_Var x ty))` ASSUME_TAC THENL
   [MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[hol_term_ok_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `n2:mlstring`; `ty:hol_type`;
                 `ty2:hol_type`; `t:hol_term`; `bd2:hol_term`] apply_steps_Abs_has_type) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sig:sig`; `axs:hol_term->bool`;
                 `sigma:(mlstring,mlstring list#hol_type)fmap#
                        (mlstring,hol_term#hol_type)fmap`;
                 `avds:mlstring list`; `n2:mlstring`; `ty2:hol_type`; `bd2:hol_term`]
                simple_esubst_Abs) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:mlstring` (X_CHOOSE_THEN `body:hol_term` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`y:mlstring`;
    `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                      (mlstring,hol_term#hol_type)fmap) ty2`;
    `body:hol_term`] THEN
  ASM_REWRITE_TAC[tysof_esubst_sig] THEN
  (SUBGOAL_THEN `hol_term_ok sig bd2 /\ type_ok (FST sig) ty2` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var n2 ty2) bd2)` THEN
     REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN MESON_TAC[]; ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC ty_esubst_type_ok_alt THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC esubst_has_type1 THEN
     MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC ACONV_TRANS THEN
     EXISTS_TAC `esubst sigma []
                   (VSUBST [(apply_steps stps (hol_Var x ty),hol_Var n2 ty2)] bd2)` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC esubst_Abs_beta_ACONV THEN
       MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`; `avds:mlstring list`] THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC esubst_ACONV THEN
       MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[] THEN
       REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
         MATCH_MP_TAC apply_steps_term_ok THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC apply_steps_Abs_beta THEN EXISTS_TAC `sig:sig` THEN
         ASM_REWRITE_TAC[]]]]));;

(* HOL4 proves_substitutable_aux (HOL4 line 4854) is proved with suspend and
   Resume blocks and stored by its Finalise (HOL4 line 5692): it is in part 7,
   after the cases. *)

(* HOL4: the vacuous quantifier !thy is kept (typed A) *)
let proves_esubst_avds = prove
 (`!sig axs (thy:A) h sigma avds1 avds2 c.
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma /\
     hol_term_ok sig c /\
     ((sig,axs),h) |- esubst sigma avds1 c
     ==> ((sig,axs),h) |- esubst sigma avds2 c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC proves_ACONV_concl THEN
  EXISTS_TAC `esubst sigma avds1 c` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ACONV_esubst_avds THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN
    ASM_MESON_TAC[term_ok_welltyped]]);;

(* Helper: bind/unbind round-trip for fresh variables *)
let bind_unbind_fresh = prove
 (`!dbt z ty k.
     ~dbVFREE_IN (dbVar z ty) dbt
     ==> hol_bind (z,ty) k (unbind (dbVar z ty) k dbt) = dbt`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[hol_bind_def; unbind_def; dbVFREE_IN_def; injectivity "dbterm"; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  ASM_REWRITE_TAC[hol_bind_def; PAIR_EQ; injectivity "dbterm"] THEN ASM_MESON_TAC[]);;

(* Helper: dbINST commutes with bind when z has unique type *)
let dbINST_bind_commute = prove
 (`!dbt z ty k tyin.
     (!ty'. dbVFREE_IN (dbVar z ty') dbt ==> ty' = ty)
     ==> dbINST tyin (hol_bind (z,ty) k dbt) =
         hol_bind (z,TYPE_SUBST tyin ty) k (dbINST tyin dbt)`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[hol_bind_def; dbINST_def; dbVFREE_IN_def; injectivity "dbterm"] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  ASM_REWRITE_TAC[dbINST_def; PAIR_EQ; injectivity "dbterm"] THEN ASM_MESON_TAC[]);;

let CLITAUX_VFREE_IN_INST = prove
 (`!tm tyin u uty.
     welltyped tm
     ==> (VFREE_IN (hol_Var u uty) (INST tyin tm) <=>
          ?oty. VFREE_IN (hol_Var u oty) tm /\ uty = TYPE_SUBST tyin oty)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INST_def] THEN
  MP_TAC(ISPECL [`sizeof tm`; `tm:hol_term`; `[]:(hol_term#hol_term)list`;
                 `tyin:(hol_type#hol_type)list`] INST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RESULT_def]);;

let CLITAUX_VSUBST_Abs_fresh = prove
 (`!l z ty b.
     (!s' s. MEM (s',s) l ==> ~MEM z (tm_names s') /\ ~MEM z (tm_names s))
     ==> VSUBST l (hol_Abs (hol_Var z ty) b) = hol_Abs (hol_Var z ty) (VSUBST l b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FILTER (\(s',s). ~(s = hol_Var z ty)) (l:(hol_term#hol_term)list) = l`
    ASSUME_TAC THENL
   [REWRITE_TAC[FILTER_EQ_ID; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(MP_TAC o SPECL [`p1:hol_term`; `p2:hol_term`]) THEN
    ASM_REWRITE_TAC[tm_names_def; MEM]; ALL_TAC] THEN
  REWRITE_TAC[VSUBST_def; dest_var_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `~EX (\(s',s). VFREE_IN (hol_Var z ty) s' /\ VFREE_IN s b) l`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_MESON_TAC[VFREE_IN_tm_names]);;

(* Alpha-equivalence for apply_steps on Abs: apply_steps stps (Abs (Var x ty)
   t) is ACONV to Abs (Var z ty2) (apply_steps stps (t[z/x])) for fresh z.
   Proof by induction on stps: base: ACONV_db + bind_unbind_fresh; VStep:
   ACONV_VSUBST + z not captured (z fresh for ilist names); TStep: ACONV_INST
   + dbINST_bind_commute. *)
let apply_steps_Abs_alpha = prove
 (CASE_TERM
  `!sig stps x ty t z.
     hol_term_ok sig t /\ steps_ok sig stps /\
     ~MEM z (tm_names (hol_Abs (hol_Var x ty) t)) /\
     type_ok (FST sig) ty /\
     ALL (\step. match step with
                   VStep ilist ->
                     ALL (\(s',s). ~MEM z (APPEND (tm_names s') (tm_names s))) ilist
                 | TStep _ -> T) stps
     ==> ?ty2.
           ACONV (apply_steps stps (hol_Abs (hol_Var x ty) t))
                 (hol_Abs (hol_Var z ty2)
                    (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] t))) /\
           welltyped (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] t)) /\
           (!ty'. VFREE_IN (hol_Var z ty')
                    (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] t))
                  ==> ty' = ty2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[apply_steps_def; steps_ok_def; ALL; tm_names_def; MEM_APPEND; MEM;
              DE_MORGAN_THM] THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `ty:hol_type` THEN
    SUBGOAL_THEN `welltyped t` ASSUME_TAC THENL
     [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
    SUBGOAL_THEN `!ty'. ~VFREE_IN (hol_Var z ty') t` ASSUME_TAC THENL
     [ASM_MESON_TAC[VFREE_IN_tm_names]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC replace_binder_ACONV THEN EXISTS_TAC `sig:sig` THEN
      ASM_REWRITE_TAC[hol_term_ok_def] THEN
      MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[has_type_rules];
      X_GEN_TAC `ty':hol_type` THEN
      MP_TAC(ISPECL [`t:hol_term`; `z:mlstring`; `ty':hol_type`;
                     `[(hol_Var z ty,hol_Var x ty)]`] VFREE_IN_VSUBST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REV_ASSOCD] THEN STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[VFREE_IN_def; injectivity "hol_term"] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  QCASES_ON "h" THEN REWRITE_TAC[apply_steps_def; steps_ok_def; ALL; case_def "subst_step"] THEN
  REPEAT STRIP_TAC THEN
  LAST_X_ASSUM(MP_TAC o SPECL [`x:mlstring`; `ty:hol_type`; `t':hol_term`; `z:mlstring`]) THEN
  ASM_REWRITE_TAC[tm_names_def; MEM_APPEND; MEM; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ty2:hol_type` STRIP_ASSUME_TAC) THENL
  [EXISTS_TAC `ty2:hol_type` THEN
     SUBGOAL_THEN `!s' s. MEM (s',s) (a:(hol_term#hol_term)list)
                          ==> ~MEM z (tm_names s') /\ ~MEM z (tm_names s)` (LABEL_TAC "FR") THENL
      [UNDISCH_TAC `ALL (\(s',s). ~MEM z (tm_names s') /\ ~MEM z (tm_names s))
                        (a:(hol_term#hol_term)list)` THEN
       REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
       MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `!k v. MEM (v,k) (a:(hol_term#hol_term)list)
                         ==> ?x ty. k = hol_Var x ty /\ v has_type ty` (LABEL_TAC "AT") THENL
      [REPEAT GEN_TAC THEN
       DISCH_THEN(fun m -> QPAT_ASSUM "!s s'. MEM (s',s) a ==> _"
         (fun h -> MP_TAC(MATCH_MP h m))) THEN
       MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `welltyped (apply_steps t (hol_Abs (hol_Var x ty) t'))` ASSUME_TAC THENL
      [MATCH_MP_TAC apply_steps_welltyped THEN EXISTS_TAC `sig:sig` THEN
       ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC ACONV_TRANS THEN
       EXISTS_TAC `VSUBST a (hol_Abs (hol_Var z ty2)
                     (apply_steps t (VSUBST [(hol_Var z ty,hol_Var x ty)] t')))` THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC ACONV_VSUBST THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN
         REPEAT CONJ_TAC THEN FIRST [USE_THEN "AT" MATCH_ACCEPT_TAC; MESON_TAC[]];
         USE_THEN "FR" (fun th -> REWRITE_TAC[MATCH_MP CLITAUX_VSUBST_Abs_fresh th; ACONV_REFL])];
       MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[] THEN
       USE_THEN "AT" MP_TAC THEN MESON_TAC[];
       X_GEN_TAC `ty':hol_type` THEN
       MP_TAC(ISPECL [`apply_steps t (VSUBST [(hol_Var z ty,hol_Var x ty)] t')`; `z:mlstring`;
                      `ty':hol_type`; `a:(hol_term#hol_term)list`] VFREE_IN_VSUBST) THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
       DISCH_THEN(X_CHOOSE_THEN `y:mlstring` (X_CHOOSE_THEN `ty0:hol_type` STRIP_ASSUME_TAC)) THEN
       MP_TAC(ISPECL [`a:(hol_term#hol_term)list`; `hol_Var y ty0`; `hol_Var y ty0`]
                     REV_ASSOCD_MEM) THEN
       STRIP_TAC THENL
        [USE_THEN "FR" (fun h -> FIRST_ASSUM(MP_TAC o MATCH_MP h)) THEN
         ASM_MESON_TAC[VFREE_IN_tm_names];
         UNDISCH_TAC `VFREE_IN (hol_Var z ty')
                        (REV_ASSOCD (hol_Var y ty0) a (hol_Var y ty0))` THEN
         ASM_REWRITE_TAC[VFREE_IN_def; injectivity "hol_term"] THEN STRIP_TAC THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
   EXISTS_TAC `TYPE_SUBST a ty2` THEN
     SUBGOAL_THEN `welltyped (apply_steps t (hol_Abs (hol_Var x ty) t'))` ASSUME_TAC THENL
      [MATCH_MP_TAC apply_steps_welltyped THEN EXISTS_TAC `sig:sig` THEN
       ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
     ABBREV_TAC `B = apply_steps t (VSUBST [(hol_Var z ty,hol_Var x ty)] t')` THEN
     SUBGOAL_THEN `welltyped (hol_Abs (hol_Var z ty2) B)` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC ACONV_TRANS THEN EXISTS_TAC `INST a (hol_Abs (hol_Var z ty2) B)` THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC ACONV_INST THEN ASM_REWRITE_TAC[];
         MP_TAC(ISPECL [`INST a (hol_Abs (hol_Var z ty2) B)`;
                        `hol_Abs (hol_Var z (TYPE_SUBST a ty2)) (INST a B)`] ACONV_db) THEN
         ASM_SIMP_TAC[INST_WELLTYPED; WELLTYPED_CLAUSES] THEN
         ANTS_TAC THENL [MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
         ASM_SIMP_TAC[INST_dbINST] THEN
         REWRITE_TAC[hol_db_def; dbINST_def; typeof_def; dest_var_def; injectivity "dbterm"] THEN
         ASM_SIMP_TAC[INST_dbINST] THEN MATCH_MP_TAC dbINST_bind_commute THEN
         X_GEN_TAC `ty':hol_type` THEN
         MP_TAC(ISPECL [`B:hol_term`; `hol_Var z ty'`] dbVFREE_IN_VFREE_IN) THEN
         ASM_REWRITE_TAC[hol_db_def] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]];
       MATCH_MP_TAC INST_WELLTYPED THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `ty':hol_type` THEN ASM_SIMP_TAC[CLITAUX_VFREE_IN_INST] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_MESON_TAC[]]]);;

let esubst_Abs_alpha = prove
 (`!sig axs sigma avds z ty body.
     hol_term_ok sig (hol_Abs (hol_Var z ty) body) /\
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     (!ty2. VFREE_IN (hol_Var z ty2) body ==> ty2 = ty)
     ==> ACONV (esubst sigma avds (hol_Abs (hol_Var z ty) body))
               (hol_Abs (hol_Var z (ty_esubst sigma ty)) (esubst sigma [] body))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok sig body` ASSUME_TAC THENL
   [UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var z ty) body)` THEN
    REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped body` ASSUME_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `!tm avds. hol_term_ok sig tm ==> welltyped (esubst sigma avds tm)`
    (LABEL_TAC "W") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_welltyped THEN
    MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`esubst sigma avds (hol_Abs (hol_Var z ty) body)`;
                 `hol_Abs (hol_Var z (ty_esubst sigma ty)) (esubst sigma [] body)`] ACONV_db) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WELLTYPED_CLAUSES] THEN CONJ_TAC THENL
     [USE_THEN "W" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `hol_Abs (hol_Var z ty) body`; `avds:mlstring list`] db_esubst_thm) THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `body:hol_term`; `[]:mlstring list`] db_esubst_thm) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[hol_db_def; typeof_def; dest_var_def; db_esubst_def; db_esubst_ty_def;
              db_esubst_tm_def; injectivity "dbterm"] THEN
  MP_TAC(ISPECL [`sig:sig`; `sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap`;
                 `body:hol_term`; `[]:mlstring list`] db_esubst_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[db_esubst_def] THEN
  MP_TAC(ISPECL [`hol_db body`; `(z,ty):mlstring#hol_type`; `0`;
                 `sigma:(mlstring,mlstring list#hol_type)fmap#
                        (mlstring,hol_term#hol_type)fmap`] db_esubst_ty_bind) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `ty':hol_type` THEN
    MP_TAC(ISPECL [`body:hol_term`; `hol_Var z ty'`] dbVFREE_IN_VFREE_IN) THEN
    ASM_REWRITE_TAC[hol_db_def] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC db_esubst_tm_bind THEN
  UNDISCH_TAC `esubsts_ok sig (sigma:(mlstring,mlstring list#hol_type)fmap#
                                   (mlstring,hol_term#hol_type)fmap)` THEN
  PAIR_CASES_ON `sigma:(mlstring,mlstring list#hol_type)fmap#
                        (mlstring,hol_term#hol_type)fmap` THEN
  REWRITE_TAC[SND] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP CLITAUX_esubsts_ok_FLOOKUP (CONJ th th2)))) THEN SIMP_TAC[]);;

(* Combined: esubst/apply_steps on Abs equation is ACONV to Abs equation with
   fresh binder z and esubst/apply_steps of the bodies.  Follows from
   apply_steps_Abs_alpha + esubst_ACONV + esubst_Abs_alpha.  The quantified
   nms allows the caller to require z avoids additional names (e.g.
   hypothesis names for the proves_ABS application).  Uses a single z for
   BOTH l and r (needed because proves_ABS requires the same binder variable
   on both sides). *)
(* every step list avoids all names outside some finite list *)
let CLITAUX_steps_fresh = prove
 (CASE_TERM
  `!stps. ?ns. !z. ~MEM z ns
     ==> ALL (\step. match step with
                       VStep ilist ->
                         ALL (\(s',s). ~MEM z (APPEND (tm_names s') (tm_names s))) ilist
                     | TStep _ -> T) stps`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ns:mlstring list`) THEN QCASES_ON "h" THEN
  REWRITE_TAC[case_def "subst_step"] THENL
   [EXISTS_TAC `APPEND (FLAT (MAP (\(s',s). APPEND (tm_names s') (tm_names s))
                                  (a:(hol_term#hol_term)list))) ns` THEN
    X_GEN_TAC `z:mlstring` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[MEM_APPEND; DE_MORGAN_THM]) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `~MEM z (FLAT (MAP (\(s',s). APPEND (tm_names s') (tm_names s))
                                  (a:(hol_term#hol_term)list)))` THEN
    REWRITE_TAC[MEM_FLAT; MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
    EXISTS_TAC `ns:mlstring list` THEN ASM_REWRITE_TAC[]]);;

let CLITAUX_ACONV_Abs_ty = prove
 (`!x1 ty1 t1 x2 ty2 t2.
     ACONV (hol_Abs (hol_Var x1 ty1) t1) (hol_Abs (hol_Var x2 ty2) t2) ==> ty1 = ty2`,
  REWRITE_TAC[ACONV_def] THEN ONCE_REWRITE_TAC[RACONV_cases] THEN
  REWRITE_TAC[distinctness "hol_term"; injectivity "hol_term"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[typeof_def]) THEN
  ASM_REWRITE_TAC[]);;

let esubst_apply_steps_Abs_alpha = prove
 (`!sig axs sigma avds x ty l r stps nms.
     hol_term_ok sig l /\ hol_term_ok sig r /\
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     type_ok (FST sig) ty /\ steps_ok sig stps
     ==> ?z ty'.
           ACONV (esubst sigma avds (apply_steps stps (hol_Abs (hol_Var x ty) l)))
                 (hol_Abs (hol_Var z ty')
                    (esubst sigma []
                       (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] l)))) /\
           ACONV (esubst sigma avds (apply_steps stps (hol_Abs (hol_Var x ty) r)))
                 (hol_Abs (hol_Var z ty')
                    (esubst sigma []
                       (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] r)))) /\
           ~MEM z nms /\
           type_ok (FST (esubst_sig sigma sig)) ty' /\
           hol_term_ok (esubst_sig sigma sig)
             (esubst sigma [] (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] l))) /\
           hol_term_ok (esubst_sig sigma sig)
             (esubst sigma [] (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] r)))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `ns:mlstring list` (SPEC `stps:subst_step list` CLITAUX_steps_fresh) THEN
  ABBREV_TAC `z = NVARIANT x (APPEND nms ns)
                    (hol_Comb (hol_Abs (hol_Var x ty) l) (hol_Abs (hol_Var x ty) r))` THEN
  SUBGOAL_THEN `~MEM z (tm_names (hol_Abs (hol_Var x ty) l)) /\
                ~MEM z (tm_names (hol_Abs (hol_Var x ty) r)) /\
                ~MEM z nms /\ ~MEM z ns` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`hol_Comb (hol_Abs (hol_Var x ty) l) (hol_Abs (hol_Var x ty) r)`;
                  `x:mlstring`; `APPEND (nms:mlstring list) ns`] NVARIANT_MEM) THEN
    ASM_REWRITE_TAC[tm_names_def; MEM_APPEND; DE_MORGAN_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:mlstring` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `ty:hol_type`;
                `l:hol_term`; `z:mlstring`] apply_steps_Abs_alpha) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ty2:hol_type` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `ty:hol_type`;
                `r:hol_term`; `z:mlstring`] apply_steps_Abs_alpha) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ty3:hol_type` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `hol_term_ok sig (hol_Abs (hol_Var x ty) l) /\
                hol_term_ok sig (hol_Abs (hol_Var x ty) r)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[hol_term_ok_def] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped l /\ welltyped r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  (* both bound variables get the type of apply_steps stps (hol_Var x ty) *)
  SUBGOAL_THEN `ty3:hol_type = ty2` SUBST_ALL_TAC THENL
   [MP_TAC(SPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `ty:hol_type`;
                  `l:hol_term`] apply_steps_Abs) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `xl:mlstring` (X_CHOOSE_THEN `tyl:hol_type`
      (X_CHOOSE_THEN `bdl:hol_term` STRIP_ASSUME_TAC))) THEN
    MP_TAC(SPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `ty:hol_type`;
                  `r:hol_term`] apply_steps_Abs) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `xr:mlstring` (X_CHOOSE_THEN `tyr:hol_type`
      (X_CHOOSE_THEN `bdr:hol_term` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `tyl:hol_type = tyr` ASSUME_TAC THENL
     [MP_TAC(SPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `xl:mlstring`;
                    `ty:hol_type`; `tyl:hol_type`; `l:hol_term`; `bdl:hol_term`]
        apply_steps_Abs_has_type) THEN
      MP_TAC(SPECL [`sig:sig`; `stps:subst_step list`; `x:mlstring`; `xr:mlstring`;
                    `ty:hol_type`; `tyr:hol_type`; `r:hol_term`; `bdr:hol_term`]
        apply_steps_Abs_has_type) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
    SUBGOAL_THEN `tyl:hol_type = ty2 /\ tyr:hol_type = ty3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CLITAUX_ACONV_Abs_ty THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `hol_term_ok sig (hol_Abs (hol_Var z ty2)
                        (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] l))) /\
     hol_term_ok sig (hol_Abs (hol_Var z ty2)
                        (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] r)))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC term_ok_aconv THENL
     [EXISTS_TAC `apply_steps stps (hol_Abs (hol_Var x ty) l)`;
      EXISTS_TAC `apply_steps stps (hol_Abs (hol_Var x ty) r)`] THEN
    ASM_SIMP_TAC[apply_steps_term_ok; WELLTYPED_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
    [`z:mlstring`;
     `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                       (mlstring,hol_term#hol_type)fmap) ty2`] THEN
  ASM_REWRITE_TAC[tysof_esubst_sig] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_TRANS THEN
    EXISTS_TAC `esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                              (mlstring,hol_term#hol_type)fmap) avds
                  (hol_Abs (hol_Var z ty2)
                     (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] l)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_ACONV THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN
      ASM_SIMP_TAC[apply_steps_term_ok];
      MATCH_MP_TAC esubst_Abs_alpha THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ACONV_TRANS THEN
    EXISTS_TAC `esubst (sigma:(mlstring,mlstring list#hol_type)fmap#
                              (mlstring,hol_term#hol_type)fmap) avds
                  (hol_Abs (hol_Var z ty2)
                     (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] r)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_ACONV THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN
      ASM_SIMP_TAC[apply_steps_term_ok];
      MATCH_MP_TAC esubst_Abs_alpha THEN
      MAP_EVERY EXISTS_TAC [`sig:sig`; `axs:hol_term->bool`] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ty_esubst_type_ok_alt THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var z ty2)
                   (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] l)))` THEN
    REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN MESON_TAC[];
    MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `axs:hol_term->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var z ty2)
                   (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] l)))` THEN
    REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[];
    MATCH_MP_TAC esubst_term_ok THEN EXISTS_TAC `axs:hol_term->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hol_term_ok sig (hol_Abs (hol_Var z ty2)
                   (apply_steps stps (VSUBST [(hol_Var z ty,hol_Var x ty)] r)))` THEN
    REWRITE_TAC[hol_term_ok_def] THEN MESON_TAC[]]);;
