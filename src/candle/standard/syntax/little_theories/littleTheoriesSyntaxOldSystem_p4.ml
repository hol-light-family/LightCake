(* ========================================================================= *)
(* littleTheoriesSyntaxOldSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxOldSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(* The theory is in seven consecutive parts, each loading the one before;    *)
(* littleTheoriesSyntaxOldSystem.ml loads them all.  Part 4 (HOL4 lines      *)
(* 2598-3594): vtys_ok, dbconsts_ok, esubst and INST, esubst                 *)
(* and VSUBST, compositions of VSUBST.                                       *)
(* ========================================================================= *)

needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem_p3.ml";;

prioritize_num();;
type_invention_error := true;;

let vtys_ok_def = cake_def
  `(vtys_ok (sig:SIG) (dbVar n ty) <=> type_ok (FST sig) ty) /\
   (vtys_ok sig (dbConst n ty) <=> type_ok (FST sig) ty) /\
   (vtys_ok sig (dbBound m) <=> T) /\
   (vtys_ok sig (dbAbs v body) <=> type_ok (FST sig) v /\ vtys_ok sig body) /\
   (vtys_ok sig (dbComb e1 e2) <=> vtys_ok sig e1 /\ vtys_ok sig e2)`;;

let dbconsts_ok_def = cake_def
  `(dbconsts_ok (sig:SIG) (dbVar n ty) <=> T) /\
   (dbconsts_ok sig (dbConst n ty) <=>
      !d. FLOOKUP (SND sig) n = SOME d ==> ?i. ty = TYPE_SUBST i d) /\
   (dbconsts_ok sig (dbBound m) <=> T) /\
   (dbconsts_ok sig (dbAbs v body) <=> dbconsts_ok sig body) /\
   (dbconsts_ok sig (dbComb e1 e2) <=> dbconsts_ok sig e1 /\ dbconsts_ok sig e2)`;;

(* HOL4 val dbrws *)
let CLITAUX_dbrws = [dbINST_def; db_esubst_def; db_esubst_tm_def; db_esubst_ty_def;
                     hol_term_ok_def; hol_db_def; vtys_ok_def; dbconsts_ok_def; dbVSUBST_def];;

let type_ok_TYPE_SUBST_inv = prove
 (`!ty tys i. type_ok tys (TYPE_SUBST i ty) ==> type_ok tys ty`,
  MATCH_MP_TAC type_ind THEN
  REWRITE_TAC[type_ok_def; TYPE_SUBST_def; LENGTH_MAP; ALL_MAP] THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN MESON_TAC[]);;

let esubsts_ok_FLOOKUP_tmsof = prove
 (`!sig sigma m repl decl_ty.
     esubsts_ok sig sigma /\ FLOOKUP (SND sigma) m = SOME (repl,decl_ty)
     ==> CLOSED repl /\
         welltyped repl /\
         typeof repl = ty_esubst sigma decl_ty /\
         set_of_list (tvars repl) SUBSET set_of_list (hol_tyvars (typeof repl)) /\
         FLOOKUP (SND sig) m = SOME decl_ty`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; esubsts_ok_def] THEN
  MAP_EVERY X_GEN_TAC [`s:(mlstring,mlstring list#hol_type)fmap`;
                       `th:(mlstring,hol_term#hol_type)fmap`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_FAPPLY] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "!tmnm. tmnm IN FDOM th ==> _" (MP_TAC o SPEC `m:mlstring`) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[term_ok_welltyped]);;

let ty_esubst_match_type = prove
 (`!sig sigma ty ty0.
     esubsts_ok sig sigma /\ type_ok (FST sig) ty /\ (?i. ty = TYPE_SUBST i ty0)
     ==> ?s. match_type (ty_esubst sigma ty0) (ty_esubst sigma ty) = SOME s /\
             TYPE_SUBST s (ty_esubst sigma ty0) = ty_esubst sigma ty`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QBY "?s. match_type (ty_esubst sigma ty0) (ty_esubst sigma (TYPE_SUBST i ty0)) = SOME s"
    (MATCH_MP_TAC match_type_complete THEN
     QSPECL_THEN ["ty0"; "i"; "FST sig"; "SND sig"; "sigma"] MP_TAC ty_esubst_TYPE_SUBST THEN
     ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[]) THEN
  QEXISTS_TAC "s" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] match_type_SOME) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC type_ok_arities_match THEN QEXISTS_TAC "FST sig" THEN
  CONJ_TAC THEN MATCH_MP_TAC ty_esubst_type_ok_alt THEN ASM_MESON_TAC[type_ok_TYPE_SUBST_inv]);;

let dbtyvars_def = cake_def
  `(dbtyvars (dbVar n ty) = hol_tyvars ty) /\
   (dbtyvars (dbConst n ty) = hol_tyvars ty) /\
   (dbtyvars (dbBound k) = []) /\
   (dbtyvars (dbComb t1 t2) = APPEND (dbtyvars t1) (dbtyvars t2)) /\
   (dbtyvars (dbAbs ty t) = APPEND (hol_tyvars ty) (dbtyvars t))`;;

let dbINST_cong = prove
 (`!dbtm s1 s2.
     (!v. MEM v (dbtyvars dbtm)
          ==> REV_ASSOCD (Tyvar v) s1 (Tyvar v) = REV_ASSOCD (Tyvar v) s2 (Tyvar v))
     ==> dbINST s1 dbtm = dbINST s2 dbtm`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbINST_def; dbtyvars_def; MEM_APPEND; injectivity "dbterm"; MEM] THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_SIMP_TAC[TYPE_SUBST_tyvars] THEN ASM_MESON_TAC[]);;

let dbtyvars_bind = prove
 (`!dbtm v k.
     set_of_list (dbtyvars (hol_bind v k dbtm)) SUBSET set_of_list (dbtyvars dbtm)`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[hol_bind_def; dbtyvars_def] THEN REPEAT STRIP_TAC THEN
  TRY COND_CASES_TAC THEN
  REWRITE_TAC[dbtyvars_def; SET_OF_LIST_APPEND; set_of_list; EMPTY_SUBSET; SUBSET_REFL] THEN
  ASM SET_TAC[]);;

let dbtyvars_db = prove
 (`!tm. welltyped tm
          ==> set_of_list (dbtyvars (hol_db tm)) SUBSET set_of_list (tvars tm)`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[hol_db_def; dbtyvars_def; tvars_def; WELLTYPED_CLAUSES; SUBSET_REFL;
              MEM_LIST_UNION; SET_OF_LIST_APPEND] THEN
  REPEAT STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN ASM SET_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[typeof_def; dest_var_def; tvars_def] THEN
    MP_TAC(ISPECL [`hol_db a1`; `(n:mlstring,ty:hol_type)`; `0`] dbtyvars_bind) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN ASM SET_TAC[]]);;

let dbINST_compose = prove
 (`!dbtm tyin1 tyin2.
     dbINST tyin1 (dbINST tyin2 dbtm) =
     dbINST (APPEND (MAP (\(ty,a). (TYPE_SUBST tyin1 ty,a)) tyin2) tyin1) dbtm`,
  SUBGOAL_THEN `!tyin1:(hol_type#hol_type)list.
                  (TYPE_SUBST tyin1 ## I) = (\(ty:hol_type,a:hol_type). TYPE_SUBST tyin1 ty,a)`
    ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]; ALL_TAC] THEN
  MATCH_MP_TAC dbterm_INDUCT THEN
  ASM_REWRITE_TAC[dbINST_def; injectivity "dbterm"; TYPE_SUBST_compose] THEN MESON_TAC[]);;

let db_esubst_dbINST_comm = prove
 (`!sig sigma dbtm tyin.
     ALL (type_ok (FST sig)) (MAP FST tyin) /\
     esubsts_ok sig sigma /\ vtys_ok sig dbtm /\ dbconsts_ok sig dbtm
     ==> db_esubst sigma (dbINST tyin dbtm) =
         dbINST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin) (db_esubst sigma dbtm)`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!ty tyin. ALL (type_ok (FST sig)) (MAP FST tyin) /\ esubsts_ok sig sigma /\
              type_ok (FST sig) ty
              ==> ty_esubst sigma (TYPE_SUBST tyin ty) =
                  TYPE_SUBST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin) (ty_esubst sigma ty)`
    (LABEL_TAC "TYC") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ty:hol_type`; `tyin:(hol_type#hol_type)list`; `FST (sig:sig)`;
                   `SND (sig:sig)`] ty_esubst_TYPE_SUBST_comm) THEN
    DISCH_THEN(MP_TAC o ISPEC `sigma:(mlstring,mlstring list#hol_type)fmap#
                                    (mlstring,hol_term#hol_type)fmap`) THEN
    ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
     [MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbINST_def; db_esubst_def; db_esubst_ty_def; db_esubst_tm_def;
              vtys_ok_def; dbconsts_ok_def] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[injectivity "dbterm"] THEN
    USE_THEN "TYC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[dbINST_def; injectivity "dbterm"] THENL
     [USE_THEN "TYC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TOP_CASE_TAC THEN
    QSPECL_THEN ["sig"; "sigma"; "a0"; "x"; "y"] MP_TAC esubsts_ok_FLOOKUP_tmsof THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:hol_type`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:(hol_type#hol_type)list` SUBST_ALL_TAC) THEN
    QSPECL_THEN ["sig"; "sigma"; "TYPE_SUBST i y"; "y"] MP_TAC ty_esubst_match_type THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:(hol_type#hol_type)list` STRIP_ASSUME_TAC) THEN
    QSPECL_THEN ["sig"; "sigma"; "TYPE_SUBST tyin (TYPE_SUBST i y)"; "y"] MP_TAC
      ty_esubst_match_type THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC type_ok_TYPE_SUBST THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[TYPE_SUBST_compose] THEN MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(hol_type#hol_type)list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    QBY "TYPE_SUBST s1 (ty_esubst sigma y) =
         TYPE_SUBST (MAP (\\(ty,a). (ty_esubst sigma ty,a)) tyin)
                    (TYPE_SUBST s2 (ty_esubst sigma y))"
     (ASM_REWRITE_TAC[] THEN USE_THEN "TYC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[dbINST_compose] THEN MATCH_MP_TAC dbINST_cong THEN
    X_GEN_TAC `v:mlstring` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `x:hol_term` dbtyvars_db) THEN ASM_REWRITE_TAC[] THEN
    QPAT_X_ASSUM "set_of_list (tvars x) SUBSET _" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN DISCH_TAC THEN DISCH_TAC THEN
    QBY "MEM v (hol_tyvars (ty_esubst sigma y))" (ASM_MESON_TAC[]) THEN
    SUBGOAL_THEN `!f:hol_type->hol_type. (\(ty:hol_type,a:hol_type). f ty,a) = (f ## I)`
      (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]; ALL_TAC] THEN
    QPAT_X_ASSUM "TYPE_SUBST s1 _ = TYPE_SUBST _ (TYPE_SUBST s2 _)"
      (MP_TAC o REWRITE_RULE[TYPE_SUBST_compose; TYPE_SUBST_tyvars]) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN(MP_TAC o SPEC `v:mlstring`) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[injectivity "dbterm"] THEN
    USE_THEN "TYC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let FVL_def = cake_def
  `(FVL (hol_Var n ty) = [(n,ty)]) /\
   (FVL (hol_Const n ty) = []) /\
   (FVL (hol_Comb e1 e2) = APPEND (FVL e1) (FVL e2)) /\
   (FVL (hol_Abs v body) = FILTER (\tm. ~MEM tm (FVL v)) (FVL body))`;;

let alist_dedup_keys_def = cake_def
  `(alist_dedup_keys ([]:(A#B)list) = []) /\
   (alist_dedup_keys (CONS (v,k) t) =
      CONS (v,k) (FILTER (\(v1,k1). ~(k1 = k)) (alist_dedup_keys t)))`;;

let esubst_ilist_def = cake_def
  `esubst_ilist ilist sigma avds tm =
     alist_dedup_keys
       (MAP (\(n,ty).
               (esubst sigma avds (REV_ASSOCD (hol_Var n ty) ilist (hol_Var n ty)),
                esubst sigma avds (hol_Var n ty)))
            (FVL tm))`;;

let dbFVL_def = cake_def
  `(dbFVL (dbVar n ty) = [(n,ty)]) /\
   (dbFVL (dbConst n ty) = []) /\
   (dbFVL (dbBound m) = []) /\
   (dbFVL (dbComb e1 e2) = APPEND (dbFVL e1) (dbFVL e2)) /\
   (dbFVL (dbAbs v body) = dbFVL body)`;;

let dbFVs_def = cake_def
  `(dbFVs (dbVar n ty) = {(n,ty)}) /\
   (dbFVs (dbConst n ty) = {}) /\
   (dbFVs (dbBound m) = {}) /\
   (dbFVs (dbComb e1 e2) = dbFVs e1 UNION dbFVs e2) /\
   (dbFVs (dbAbs v body) = dbFVs body)`;;

let db_esubst_ilist_def = cake_def
  `db_esubst_ilist ilist sigma dbtm =
     alist_dedup_keys
       (MAP (\(n,ty).
               (db_esubst sigma (REV_ASSOCD (dbVar n ty) ilist (dbVar n ty)),
                db_esubst sigma (dbVar n ty)))
            (dbFVL dbtm))`;;

let db_esubst_ilist_const = prove
 (`!ilist sigma m t. db_esubst_ilist ilist sigma (dbConst m t) = []`,
  REWRITE_TAC[db_esubst_ilist_def; dbFVL_def; MAP; alist_dedup_keys_def]);;
let _ = cake_add_simps [db_esubst_ilist_const];;

let db_esubst_ty_VFREE_IN = prove
 (`!sig sigma tm.
     esubsts_ok sig sigma
     ==> !u uty. dbVFREE_IN (dbVar u uty) (db_esubst_ty sigma tm) <=>
                 ?oty. dbVFREE_IN (dbVar u oty) tm /\ uty = ty_esubst sigma oty`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`tm:dbterm`,`tm:dbterm`) THEN
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[db_esubst_ty_def; dbVFREE_IN_def; injectivity "dbterm"; distinctness "dbterm"] THEN
  MESON_TAC[]);;

let no_dbvar_collapse = cake_def
  `no_dbvar_collapse (sigma:(mlstring,mlstring list#hol_type)fmap#A) tm <=>
     !x ty1 ty2.
       dbVFREE_IN (dbVar x ty1) tm /\ dbVFREE_IN (dbVar x ty2) tm /\ ~(ty1 = ty2)
       ==> ~(ty_esubst sigma ty1 = ty_esubst sigma ty2)`;;

let no_dbvar_collapse_comb = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) dbtm1 dbtm2.
     no_dbvar_collapse sigma (dbComb dbtm1 dbtm2)
     ==> no_dbvar_collapse sigma dbtm1 /\ no_dbvar_collapse sigma dbtm2`,
  REWRITE_TAC[no_dbvar_collapse; dbVFREE_IN_def] THEN MESON_TAC[]);;

let no_dbvar_collapse_abs = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) ty t.
     no_dbvar_collapse sigma (dbAbs ty t) ==> no_dbvar_collapse sigma t`,
  REWRITE_TAC[no_dbvar_collapse; dbVFREE_IN_def] THEN MESON_TAC[]);;

let no_var_collapse_no_dbvar_collapse = prove
 (`!sigma tm.
     welltyped tm /\ no_var_collapse sigma tm ==> no_dbvar_collapse sigma (hol_db tm)`,
  REWRITE_TAC[no_var_collapse; no_dbvar_collapse] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:mlstring`; `ty1:hol_type`; `ty2:hol_type`]) THEN
  ASM_MESON_TAC[CLITAUX_dbVFREE_IN_dbVar]);;

let no_combined_collapse = cake_def
  `no_combined_collapse (sigma:(mlstring,mlstring list#hol_type)fmap#A)
                        (ilist:(B#dbterm)list) dbtm <=>
     !x ty1 ty2.
       (dbVFREE_IN (dbVar x ty1) dbtm \/ (?v1. MEM (v1,dbVar x ty1) ilist)) /\
       (?v2. MEM (v2,dbVar x ty2) ilist) /\
       ~(ty1 = ty2)
       ==> ~(ty_esubst sigma ty1 = ty_esubst sigma ty2)`;;

let no_combined_collapse_comb = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) (ilist:(B#dbterm)list) dbtm1 dbtm2.
     no_combined_collapse sigma ilist (dbComb dbtm1 dbtm2)
     ==> no_combined_collapse sigma ilist dbtm1 /\ no_combined_collapse sigma ilist dbtm2`,
  REWRITE_TAC[no_combined_collapse; dbVFREE_IN_def] THEN MESON_TAC[]);;

let no_combined_collapse_abs = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) (ilist:(B#dbterm)list) ty t.
     no_combined_collapse sigma ilist (dbAbs ty t) ==> no_combined_collapse sigma ilist t`,
  REWRITE_TAC[no_combined_collapse; dbVFREE_IN_def] THEN MESON_TAC[]);;

let no_dbvar_collapse_no_combined_collapse = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) dbtm (ilist:(B#dbterm)list).
     no_dbvar_collapse sigma dbtm /\
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty /\ dbVFREE_IN s dbtm)
     ==> no_combined_collapse sigma ilist dbtm`,
  REWRITE_TAC[no_dbvar_collapse; no_combined_collapse] THEN MESON_TAC[]);;

let db_esubst_ty_REV_ASSOCD_comm_gen = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) ilist x ty d.
     (!ty'. (?v'. MEM (v',dbVar x ty') ilist) /\ ~(ty' = ty)
            ==> ~(ty_esubst sigma ty' = ty_esubst sigma ty)) /\
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty)
     ==> db_esubst_ty sigma (REV_ASSOCD (dbVar x ty) ilist d) =
         REV_ASSOCD (dbVar x (ty_esubst sigma ty))
                    (MAP (\(v,k). (db_esubst_ty sigma v,db_esubst_ty sigma k)) ilist)
                    (db_esubst_ty sigma d)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD_def; MAP] THEN
  PAIR_CASES_ON `h:dbterm#dbterm` THEN REWRITE_TAC[REV_ASSOCD_def; MEM; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[REV_ASSOCD_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`h0:dbterm`; `h1:dbterm`]) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[db_esubst_ty_def; injectivity "dbterm"] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_MESON_TAC[]);;

let db_esubst_ty_REV_ASSOCD_comm = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) ilist x ty.
     (!ty'. (?v'. MEM (v',dbVar x ty') ilist) /\ ~(ty' = ty)
            ==> ~(ty_esubst sigma ty' = ty_esubst sigma ty)) /\
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty)
     ==> db_esubst_ty sigma (REV_ASSOCD (dbVar x ty) ilist (dbVar x ty)) =
         REV_ASSOCD (dbVar x (ty_esubst sigma ty))
                    (MAP (\(v,k). (db_esubst_ty sigma v,db_esubst_ty sigma k)) ilist)
                    (dbVar x (ty_esubst sigma ty))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#A`; `ilist:(dbterm#dbterm)list`;
                 `x:mlstring`; `ty:hol_type`; `dbVar x ty`]
                db_esubst_ty_REV_ASSOCD_comm_gen) THEN
  ASM_REWRITE_TAC[db_esubst_ty_def]);;

let db_esubst_ty_dbVSUBST_comm = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) dbtm ilist.
     no_combined_collapse sigma ilist dbtm /\
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty)
     ==> db_esubst_ty sigma (dbVSUBST ilist dbtm) =
         dbVSUBST (MAP (\(v,k). (db_esubst_ty sigma v,db_esubst_ty sigma k)) ilist)
                  (db_esubst_ty sigma dbtm)`,
  GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[db_esubst_ty_def; dbVSUBST_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC db_esubst_ty_REV_ASSOCD_comm THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[no_combined_collapse; dbVFREE_IN_def]) THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP no_combined_collapse_comb th)) THEN STRIP_TAC THEN
    REWRITE_TAC[injectivity "dbterm"] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP no_combined_collapse_abs th)) THEN DISCH_TAC THEN
    REWRITE_TAC[injectivity "dbterm"] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let dbVFREE_IN_dbINST = prove
 (`!dbt z ty' tyin.
     dbVFREE_IN (dbVar z ty') (dbINST tyin dbt) <=>
     ?oty. dbVFREE_IN (dbVar z oty) dbt /\ ty' = TYPE_SUBST tyin oty`,
  MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbINST_def; dbVFREE_IN_def; injectivity "dbterm"; distinctness "dbterm"] THEN
  MESON_TAC[]);;

let dbINST_CLOSED = prove
 (`!tyin dbt.
     ~(?n ty. dbVFREE_IN (dbVar n ty) dbt)
     ==> ~(?n ty. dbVFREE_IN (dbVar n ty) (dbINST tyin dbt))`,
  MESON_TAC[dbVFREE_IN_dbINST]);;

let dbVSUBST_CLOSED = prove
 (`!ilist dbt.
     ~(?n ty. dbVFREE_IN (dbVar n ty) dbt) ==> dbVSUBST ilist dbt = dbt`,
  GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbVSUBST_def; dbVFREE_IN_def; injectivity "dbterm"] THEN MESON_TAC[]);;

let CLOSED_dbCLOSED = prove
 (`!tm. CLOSED tm /\ welltyped tm ==> ~(?n ty. dbVFREE_IN (dbVar n ty) (hol_db tm))`,
  REWRITE_TAC[CLOSED_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:mlstring`; `ty:hol_type`]) THEN
  MP_TAC(ISPECL [`tm:hol_term`; `hol_Var n ty`] dbVFREE_IN_VFREE_IN) THEN
  ASM_REWRITE_TAC[hol_db_def]);;

let db_esubst_tm_dbVSUBST_comm_aux = prove
 (`!sig sigma m t ilist.
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty /\ vtys_ok sig s2) /\
     esubsts_ok sig sigma
     ==> db_esubst_tm sigma (REV_ASSOCD (dbVar m t) ilist (dbVar m t)) =
         REV_ASSOCD (dbVar m t) (MAP (\(v,k). (db_esubst_tm sigma v,k)) ilist) (dbVar m t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REV_ASSOCD_MAP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ilist:(dbterm#dbterm)list`; `dbVar m t`; `dbVar m t`] REV_ASSOCD_MEM) THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[db_esubst_tm_def]]);;

let db_esubst_tm_dbVSUBST_comm = prove
 (`!sig sigma dbtm ilist.
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty /\ vtys_ok sig s2) /\
     esubsts_ok sig sigma
     ==> db_esubst_tm sigma (dbVSUBST ilist dbtm) =
         dbVSUBST (MAP (\(v,k). (db_esubst_tm sigma v,k)) ilist) (db_esubst_tm sigma dbtm)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[db_esubst_tm_def; dbVSUBST_def] THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC db_esubst_tm_dbVSUBST_comm_aux THEN ASM_MESON_TAC[];
    REPEAT TOP_CASE_TAC THEN REWRITE_TAC[dbVSUBST_def] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC dbVSUBST_CLOSED THEN
    MATCH_MP_TAC dbINST_CLOSED THEN MATCH_MP_TAC CLOSED_dbCLOSED THEN
    ASM_MESON_TAC[esubsts_ok_FLOOKUP_tmsof];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let vtys_ok_esubst_ty = prove
 (`!sig sigma dbtm.
     esubsts_ok sig sigma /\ vtys_ok sig dbtm ==> vtys_ok sig (db_esubst_ty sigma dbtm)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`dbtm:dbterm`,`dbtm:dbterm`) THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[db_esubst_ty_def; vtys_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[esubsts_ok_type_ok]);;

let db_esubst_dbVSUBST_comm = prove
 (`!sig sigma dbtm ilist.
     esubsts_ok sig sigma /\
     no_combined_collapse sigma ilist dbtm /\
     (!s2 s. MEM (s2,s) ilist ==> ?x ty. s = dbVar x ty /\ vtys_ok sig s2)
     ==> db_esubst sigma (dbVSUBST ilist dbtm) =
         dbVSUBST (MAP (\(v,k). (db_esubst sigma v,db_esubst_ty sigma k)) ilist)
                  (db_esubst sigma dbtm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[db_esubst_def] THEN
  MP_TAC(ISPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#
                        (mlstring,hol_term#hol_type)fmap`;
                 `dbtm:dbterm`; `ilist:(dbterm#dbterm)list`] db_esubst_ty_dbVSUBST_comm) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`sig:sig`;
                 `sigma:(mlstring,mlstring list#hol_type)fmap#
                        (mlstring,hol_term#hol_type)fmap`;
                 `db_esubst_ty (sigma:(mlstring,mlstring list#hol_type)fmap#
                                      (mlstring,hol_term#hol_type)fmap) dbtm`;
                 `MAP (\(v,k). (db_esubst_ty (sigma:(mlstring,mlstring list#hol_type)fmap#
                                                    (mlstring,hol_term#hol_type)fmap) v,
                                db_esubst_ty sigma k)) (ilist:(dbterm#dbterm)list)`]
                db_esubst_tm_dbVSUBST_comm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (p1:dbterm,p2:dbterm) ilist`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[db_esubst_ty_def; injectivity "dbterm"] THEN
    ASM_MESON_TAC[vtys_ok_esubst_ty];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let vtys_ok_bind = prove
 (`!sig dbtm x ty n.
     vtys_ok sig dbtm /\ type_ok (FST sig) ty ==> vtys_ok sig (hol_bind (x,ty) n dbtm)`,
  GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[vtys_ok_def; hol_bind_def] THEN REPEAT STRIP_TAC THEN
  TRY COND_CASES_TAC THEN ASM_SIMP_TAC[vtys_ok_def]);;

let dbconsts_ok_bind = prove
 (`!sig dbtm x ty n.
     dbconsts_ok sig dbtm ==> dbconsts_ok sig (hol_bind (x,ty) n dbtm)`,
  GEN_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN
  REWRITE_TAC[dbconsts_ok_def; hol_bind_def] THEN REPEAT STRIP_TAC THEN
  TRY COND_CASES_TAC THEN ASM_SIMP_TAC[dbconsts_ok_def]);;

let term_ok_db_vtys_ok = prove
 (`!sig tm. hol_term_ok sig tm ==> vtys_ok sig (hol_db tm)`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[hol_db_def; vtys_ok_def; hol_term_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[typeof_def; dest_var_def] THEN ASM_SIMP_TAC[vtys_ok_bind]);;

let term_ok_db_dbconsts_ok = prove
 (`!sig tm. hol_term_ok sig tm ==> dbconsts_ok sig (hol_db tm)`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[hol_db_def; dbconsts_ok_def; hol_term_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o REWRITE_RULE[]) THEN
    ASM_MESON_TAC[option_INJ];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[dest_var_def] THEN ASM_SIMP_TAC[dbconsts_ok_bind]]);;

let esubst_INST_comm = prove
 (`!sig axs tyin sigma avds1 avds2 tm.
     theory_ok (sig,axs) /\
     ALL (type_ok (FST sig)) (MAP FST tyin) /\
     esubsts_ok sig sigma /\ hol_term_ok sig tm
     ==> ACONV (esubst sigma avds1 (INST tyin tm))
               (INST (MAP (\(ty,a). (ty_esubst sigma ty,a)) tyin) (esubst sigma avds2 tm))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok sig (INST tyin tm)` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_INST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (tm:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  QBY "welltyped (esubst sigma avds2 tm)"
   (MATCH_MP_TAC esubst_welltyped THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
    ASM_REWRITE_TAC[]) THEN
  QSPECL_THEN ["esubst sigma avds1 (INST tyin tm)";
               "INST (MAP (\\(ty,a). (ty_esubst sigma ty,a)) tyin) (esubst sigma avds2 tm)"]
    MP_TAC ACONV_db THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC esubst_welltyped THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC INST_WELLTYPED THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  QSPECL_THEN ["sig"; "sigma"; "INST tyin tm"; "avds1"] MP_TAC db_esubst_thm THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[INST_dbINST] THEN
  QSPECL_THEN ["sig"; "sigma"; "tm"; "avds2"] MP_TAC db_esubst_thm THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC db_esubst_dbINST_comm THEN QEXISTS_TAC "sig" THEN
  ASM_SIMP_TAC[term_ok_db_vtys_ok; term_ok_db_dbconsts_ok]);;

let esubst_ty_has_type = prove
 (`!sig sigma tm avds.
     hol_term_ok sig tm /\ esubsts_ok sig sigma
     ==> esubst_ty sigma avds tm has_type ty_esubst sigma (typeof tm)`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped (v:hol_term)` ASSUME_TAC THENL
   [MATCH_MP_TAC term_ok_welltyped THEN QEXISTS_TAC "esubst_sig sigma sig" THEN
    MATCH_MP_TAC esubst_ty0_term_ok THEN
    QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN QEXISTS_TAC "avds" THEN QEXISTS_TAC "tm" THEN
    ASM_REWRITE_TAC[MEM];
    ASM_SIMP_TAC[typeof_has_type] THEN MATCH_MP_TAC esubst_ty0_ty_esubst THEN
    QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN QEXISTS_TAC "avds" THEN QEXISTS_TAC "sig" THEN
    ASM_REWRITE_TAC[MEM]]);;

let NVARIANT_SUBLIST_AVDS = prove
 (`!y n avds tm tgt.
     Abbrev (y = NVARIANT n avds tm) /\
     (!n. MEM n tgt ==> MEM n avds)
     ==> ~MEM y tgt`,
  REWRITE_TAC[marker_Abbrev_def] THEN MESON_TAC[NVARIANT_AVDS_THM]);;

let term_image_sing = prove
 (`!f x. term_image f [x] = [f x]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[term_image_def] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[term_image_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[term_union_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [term_image_sing];;

let esubst_var = prove
 (`!sigma avds x ty.
     esubst sigma avds (hol_Var x ty) = hol_Var x (ty_esubst sigma ty)`,
  REWRITE_TAC[esubst_def; esubst_ty_var; esubst_tm_def]);;
let _ = cake_add_simps [esubst_var];;

let VFREE_IN_esubst_tm = prove
 (`!sigma x ty tm.
     VFREE_IN (hol_Var x ty) tm ==> VFREE_IN (hol_Var x ty) (esubst_tm sigma tm)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`tm:hol_term`,`tm:hol_term`) THEN
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[esubst_tm_def; VFREE_IN_def; distinctness "hol_term"] THEN MESON_TAC[]);;

let VFREE_IN_esubst = prove
 (`!sig axs sigma tm x ty.
     esubsts_ok sig sigma /\
     theory_ok (sig,axs) /\
     hol_term_ok sig tm /\
     VFREE_IN (hol_Var x ty) tm
     ==> VFREE_IN (hol_Var x (ty_esubst sigma ty)) (esubst sigma [] tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[esubst_def; esubst_ty_def] THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "[]:mlstring list"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN MATCH_MP_TAC VFREE_IN_esubst_tm THEN
  QSPECL_THEN ["sig"; "[]:(hol_term#hol_term)list"; "sigma"; "[]:mlstring list"; "tm"; "v"]
    MP_TAC esubst_ty0_all_free THEN
  ASM_REWRITE_TAC[MEM] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]);;

let VSUBST_NOT_FREE_VAR = prove
 (`!sig tm x ty y.
     hol_term_ok sig tm /\
     ~VFREE_IN (hol_Var x ty) tm
     ==> VSUBST [(y,hol_Var x ty)] tm = tm`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VSUBST_def; VFREE_IN_def; hol_term_ok_def; REV_ASSOCD_def] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FILTER] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_CASES_TAC `hol_Var x ty = a0` THEN ASM_REWRITE_TAC[EX; VSUBST_NIL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    SUBGOAL_THEN `~VFREE_IN (hol_Var x ty) a1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[]]]);;

let term_image_VSUBST_VFREE = prove
 (`!sig (sigma:(mlstring,mlstring list#hol_type)fmap#A) x y ty hsigma.
     ALL ((~) o VFREE_IN (hol_Var x (ty_esubst sigma ty))) hsigma /\
     ALL (hol_term_ok sig) hsigma
     ==> term_image
           (VSUBST [(hol_Var y (ty_esubst sigma ty),hol_Var x (ty_esubst sigma ty))]) hsigma =
         hsigma`,
  REPEAT GEN_TAC THEN SPEC_TAC(`hsigma:hol_term list`,`hsigma:hol_term list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; o_THM] THEN ONCE_REWRITE_TAC[term_image_def] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sig:sig`; `h:hol_term`; `x:mlstring`;
                 `ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#A) ty`;
                 `hol_Var y (ty_esubst (sigma:(mlstring,mlstring list#hol_type)fmap#A) ty)`]
                VSUBST_NOT_FREE_VAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let LENGTH_term_union_sing_aux = prove
 (`!(f:A->hol_term) h t.
     LENGTH (term_union [f h] t) = LENGTH t \/
     LENGTH (term_union [f h] t) = LENGTH t + 1`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[term_union_thm; LENGTH] THENL
   [ARITH_TAC;
    TOP_CASE_TAC THEN REWRITE_TAC[LENGTH; term_union_thm] THEN ASM_ARITH_TAC]);;
let _ = cake_add_simps [LENGTH_term_union_sing_aux];;

let term_image_LENGTH = prove
 (`!f ts. LENGTH (term_image f ts) <= LENGTH ts`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[term_image_def] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH; LE_REFL] THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LE_REFL] THEN
  MP_TAC(ISPECL [`f:hol_term->hol_term`; `h:hol_term`; `term_image f t`]
                LENGTH_term_union_sing_aux) THEN
  ASM_ARITH_TAC);;

let VARIANT_EQ_aux = prove
 (`!tm1 tm2 typ xs v n.
     xs = [tm1] /\ v = hol_Var n typ /\
     (!x ty. VFREE_IN (hol_Var x ty) tm1 <=> VFREE_IN (hol_Var x ty) tm2)
     ==> variant xs v = variant [tm2] (hol_Var n typ)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC variant_ind THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ONCE_REWRITE_TAC[variant_def] THEN
  REWRITE_TAC[EX; GSYM vfree_in_thm] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:mlstring`; `typ:hol_type`] o
                check (is_imp o snd o strip_forall o concl)) THEN
  ASM_REWRITE_TAC[EX; GSYM vfree_in_thm] THEN
  DISCH_THEN(MP_TAC o SPEC `strcat n (implode "'")`) THEN ASM_REWRITE_TAC[]);;

let VARIANT_EQ = prove
 (`!n typ tm1 tm2.
     (!x ty. VFREE_IN (hol_Var x ty) tm1 <=> VFREE_IN (hol_Var x ty) tm2)
     ==> VARIANT tm1 n typ = VARIANT tm2 n typ`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tm1:hol_term`; `tm2:hol_term`; `typ:hol_type`; `[tm1:hol_term]`;
                 `hol_Var (implode n) typ`; `implode n`] VARIANT_EQ_aux) THEN
  ASM_REWRITE_TAC[variant_vsubst_thm; explode_implode; injectivity "hol_term"]);;

let ilist_ok_REV_ASSOCD_var = prove
 (`!ilist x ty.
     (!v k. MEM (v,k) ilist ==> ?n m ty. v = hol_Var n ty /\ k = hol_Var m ty)
     ==> ?m typ. REV_ASSOCD (hol_Var x ty) ilist (hol_Var x ty) = hol_Var m typ`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var x ty`; `hol_Var x ty`]
                REV_ASSOCD_MEM) THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let simple_esubst_Abs = prove
 (`!sig axs sigma avds x ty t.
     hol_term_ok sig (hol_Abs (hol_Var x ty) t) /\
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma
     ==> ?y body.
           esubst sigma avds (hol_Abs (hol_Var x ty) t) =
           hol_Abs (hol_Var y (ty_esubst sigma ty)) body /\
           ACONV body (esubst sigma avds (VSUBST [(hol_Var y ty,hol_Var x ty)] t)) /\
           (x = y \/ ~MEM y avds) /\
           hol_term_ok (esubst_sig sigma sig) body`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `type_ok (FST (sig:sig)) ty /\ hol_term_ok sig t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[hol_term_ok_def; injectivity "hol_term"]; ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (t:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  QSPECL_THEN ["sigma"; "t"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  QSPECL_THEN ["sigma"; "hol_Abs (hol_Var x ty) t"; "sig"; "avds"] MP_TAC
    esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:hol_term`) THEN
  REWRITE_TAC[esubst_def; esubst_ty_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "esubst_ty0 [] _ _ (hol_Abs _ _) = _"
    (MP_TAC o CONV_RULE(TOP_DEPTH_CONV let_CONV) o REWRITE_RULE[esubst_ty0_def; dest_var_def]) THEN
  REWRITE_TAC[pair_CASE; try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
              distinctness "error"] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def] THEN
    QEXISTS_TAC "x" THEN QEXISTS_TAC "esubst_tm sigma u" THEN REWRITE_TAC[] THEN
    QBY "hol_term_ok (esubst_sig sigma sig) u"
     (MATCH_MP_TAC esubst_ty0_term_ok THEN
      QEXISTS_TAC "[hol_Var x ty,hol_Var x (ty_esubst sigma ty)]" THEN
      QEXISTS_TAC "avds" THEN QEXISTS_TAC "t" THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[]) THEN
    QBY "hol_term_ok (esubst_sig sigma sig) v"
     (MATCH_MP_TAC esubst_ty0_term_ok THEN QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN
      QEXISTS_TAC "avds" THEN QEXISTS_TAC "t" THEN ASM_REWRITE_TAC[MEM]) THEN
    SUBGOAL_THEN `VSUBST [(hol_Var x ty,hol_Var x ty)] t = t` SUBST1_TAC THENL
     [MATCH_MP_TAC VSUBST_ID THEN QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_tm_ACONV THEN QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[] THEN
      QSPECL_THEN ["sig"; "sigma"; "sig"; "axs"; "avds"; "t"; "u"; "v";
                   "[hol_Var x ty,hol_Var x (ty_esubst sigma ty)]"; "[]:(hol_term#hol_term)list"]
        MP_TAC esubst_ty0_env_aconv THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[term_ok_welltyped]; SIMP_TAC[]];
      MATCH_MP_TAC esubst_tm_preserves_term_ok THEN QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[]];
    QPAT_X_ASSUM "(if _ then _ else _) = _" MP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "error"; bind_EQ_return; injectivity "error"] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:hol_term` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u':hol_term` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `u:hol_term = v` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[injectivity "error"]; ALL_TAC] THEN
    ABBREV_TAC `nv = NVARIANT x avds v` THEN
    ABBREV_TAC `tv = VSUBST [hol_Var nv ty,hol_Var x ty] t` THEN
    QPAT_X_ASSUM "hol_Abs _ _ = w" (SUBST1_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def] THEN
    QEXISTS_TAC "nv" THEN QEXISTS_TAC "esubst_tm sigma u'" THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hol_term_ok sig (tv:hol_term)` ASSUME_TAC THENL
     [EXPAND_TAC "tv" THEN MATCH_MP_TAC term_ok_vsubst_variant THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    QSPECL_THEN ["sigma"; "tv"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w2:hol_term`) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    QBY "hol_term_ok (esubst_sig sigma sig) u'"
     (MATCH_MP_TAC esubst_ty0_term_ok THEN
      QEXISTS_TAC "[hol_Var nv ty,hol_Var nv (ty_esubst sigma ty)]" THEN
      QEXISTS_TAC "avds" THEN QEXISTS_TAC "tv" THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[]) THEN
    QBY "hol_term_ok (esubst_sig sigma sig) w2"
     (MATCH_MP_TAC esubst_ty0_term_ok THEN QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN
      QEXISTS_TAC "avds" THEN QEXISTS_TAC "tv" THEN ASM_REWRITE_TAC[MEM]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC esubst_tm_ACONV THEN QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[] THEN
      QSPECL_THEN ["sig"; "sigma"; "sig"; "axs"; "avds"; "tv"; "u'"; "w2";
                   "[hol_Var nv ty,hol_Var nv (ty_esubst sigma ty)]";
                   "[]:(hol_term#hol_term)list"]
        MP_TAC esubst_ty0_env_aconv THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[term_ok_welltyped]; SIMP_TAC[]];
      EXPAND_TAC "nv" THEN REWRITE_TAC[NVARIANT_AVDS_THM];
      MATCH_MP_TAC esubst_tm_preserves_term_ok THEN QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[]]]);;

let ACONV_esubst_env = prove
 (`!sig axs sigma avds1 avds2 tm.
     esubsts_ok sig sigma /\ hol_term_ok sig tm /\ theory_ok (sig,axs)
     ==> ACONV (esubst sigma avds1 tm) (esubst sigma avds2 tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[esubst_def] THEN MATCH_MP_TAC esubst_tm_ACONV THEN
  QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[esubst_ty_term_ok];
    ASM_MESON_TAC[esubst_ty_term_ok];
    MATCH_MP_TAC esubst_ty_avds_aconv THEN ASM_MESON_TAC[term_ok_welltyped]]);;

let proves_ACONV_concl = prove
 (`!thy h (n:A) c c'.
     (thy,h) |- c /\ welltyped c' /\ ACONV c c' ==> (thy,h) |- c'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC proves_ACONV THEN
  MAP_EVERY EXISTS_TAC [`h:hol_term list`; `c:hol_term`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[ALL; GSYM ALL_MEM; EXISTS_MEM] THEN MESON_TAC[ACONV_REFL]);;

let ACONV_esubst_avds = prove
 (`!sig axs sigma avds1 avds2 tm.
     hol_term_ok sig tm /\ welltyped tm /\ esubsts_ok sig sigma /\ theory_ok (sig,axs)
     ==> ACONV (esubst sigma avds1 tm) (esubst sigma avds2 tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[esubst_def] THEN MATCH_MP_TAC esubst_tm_ACONV THEN
  QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[esubst_ty_term_ok];
    ASM_MESON_TAC[esubst_ty_term_ok];
    MATCH_MP_TAC esubst_ty_avds_aconv THEN ASM_MESON_TAC[term_ok_welltyped]]);;

let esubst_avds_type = prove
 (`!sig axs sigma avds1 avds2 tm.
     theory_ok (sig,axs) /\ hol_term_ok sig tm /\ esubsts_ok sig sigma
     ==> typeof (esubst sigma avds1 tm) = typeof (esubst sigma avds2 tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ACONV_TYPE) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ACONV_esubst_avds THEN ASM_MESON_TAC[term_ok_welltyped];
    ASM_MESON_TAC[esubst_welltyped];
    ASM_MESON_TAC[esubst_welltyped]]);;

let esubst_VSUBST_has_type = prove
 (`!sig axs sigma avds c ilist.
     hol_term_ok sig c /\
     c has_type Tyapp (implode "bool") [] /\
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s')
     ==> esubst sigma avds (VSUBST ilist c) has_type Tyapp (implode "bool") []`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_has_type_bool THEN
  QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_MESON_TAC[];
    MATCH_MP_TAC term_ok_VSUBST THEN ASM_MESON_TAC[]]);;

let esubst_VSUBST_term_ok = prove
 (`!sig axs sigma avds c ilist.
     hol_term_ok sig c /\
     theory_ok (sig,axs) /\
     esubsts_ok sig sigma /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s')
     ==> hol_term_ok (esubst_sig sigma sig) (esubst sigma avds (VSUBST ilist c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_term_ok THEN QEXISTS_TAC "axs" THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_ok_VSUBST THEN ASM_MESON_TAC[]);;

let esubst_VSUBST_welltyped = prove
 (`!sig axs sigma avds c ilist.
     hol_term_ok sig c /\ theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s')
     ==> welltyped (esubst sigma avds (VSUBST ilist c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_welltyped THEN
  QEXISTS_TAC "esubst_sig sigma sig" THEN MATCH_MP_TAC esubst_VSUBST_term_ok THEN
  QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[]);;

let typeof_esubst = prove
 (`!sig axs sigma avds tm.
     hol_term_ok sig tm /\ esubsts_ok sig sigma /\ theory_ok (sig,axs)
     ==> typeof (esubst sigma avds tm) = ty_esubst sigma (typeof tm)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:(mlstring,mlstring list#hol_type)fmap`;
                       `th:(mlstring,hol_term#hol_type)fmap`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[esubst_def; esubst_ty_def] THEN
  QSPECL_THEN ["(s,th)"; "tm"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `typeof v` THEN CONJ_TAC THENL
   [MATCH_MP_TAC typeof_esubst_tm THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC esubst_ty0_term_ok THEN
    QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN QEXISTS_TAC "avds" THEN QEXISTS_TAC "tm" THEN
    ASM_REWRITE_TAC[MEM];
    MATCH_MP_TAC typeof_esubst_ty THEN QEXISTS_TAC "sig" THEN
    QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN QEXISTS_TAC "avds" THEN
    ASM_REWRITE_TAC[MEM]]);;

let theory_ok_esubst_VSUBST = prove
 (`!sig axs sigma ilist.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s')
     ==> theory_ok (esubst_sig sigma sig,IMAGE (esubst sigma [] o VSUBST ilist) axs)`,
  REPEAT STRIP_TAC THEN
  QPAT_ASSUM "theory_ok _" (MP_TAC o REWRITE_RULE[theory_ok_def; FST; SND]) THEN STRIP_TAC THEN
  REWRITE_TAC[theory_ok_def; FST; SND; tysof_esubst_sig; tmsof_esubst_sig] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP in_frange_o_f) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ty_esubst_type_ok_alt THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_IMAGE; o_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_VSUBST_term_ok THEN QEXISTS_TAC "axs" THEN ASM_MESON_TAC[];
      MATCH_MP_TAC esubst_VSUBST_has_type THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
      ASM_MESON_TAC[]];
    MATCH_MP_TAC esubst_sig_is_std_sig THEN ASM_REWRITE_TAC[]]);;
let _ = cake_add_simps [theory_ok_esubst_VSUBST];;

let esubst_VSUBST_ACONV = prove
 (`!sig axs sigma avds1 avds2 ilist tm1 tm2.
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s') /\
     ACONV tm1 tm2 /\ hol_term_ok sig tm1 /\ hol_term_ok sig tm2 /\
     theory_ok (sig,axs) /\ esubsts_ok sig sigma
     ==> ACONV (esubst sigma avds1 (VSUBST ilist tm1))
               (esubst sigma avds2 (VSUBST ilist tm2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_ACONV THEN QEXISTS_TAC "sig" THEN
  QEXISTS_TAC "axs" THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ACONV_VSUBST THEN ASM_MESON_TAC[term_ok_welltyped]]);;

let term_image_thm = prove
 (`(!f. term_image f [] = []) /\
   (!f h t. term_image f (CONS h t) =
            if f h = h /\ term_image f t = t then CONS h t
            else term_union [f h] (term_image f t))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [term_image_def] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let db_esubst_ty_thm1 = prove
 (`!sig sigma tm avds.
     esubsts_ok sig sigma /\ hol_term_ok sig tm
     ==> hol_db (esubst_ty sigma avds tm) = db_esubst_ty sigma (hol_db tm)`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["sigma"; "tm"; "sig"; "avds"] MP_TAC esubst_ty0_always_returns THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC db_esubst_ty_thm THEN QEXISTS_TAC "sig" THEN
  QEXISTS_TAC "[]:(hol_term#hol_term)list" THEN QEXISTS_TAC "avds" THEN
  ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[term_ok_welltyped]);;

let term_ok_has_type_type_ok = prove
 (`!sig axs ty tm.
     theory_ok (sig,axs) /\ hol_term_ok sig tm /\ tm has_type ty ==> type_ok (FST sig) ty`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
  SPEC_TAC(`ty:hol_type`,`ty:hol_type`) THEN SPEC_TAC(`tm:hol_term`,`tm:hol_term`) THEN
  MATCH_MP_TAC has_type_ind THEN REWRITE_TAC[hol_term_ok_def; type_ok_def; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_ASSUM(MP_TAC o MATCH_MP theory_ok_sig) THEN
      SIMP_TAC[is_std_sig_def; FST; LENGTH; ARITH_RULE `SUC (SUC 0) = 2`] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN ASM_MESON_TAC[]);;

let esubst_VSUBST_comm = prove
 (`!sig axs sigma avds avds' ilist tm.
     theory_ok (sig,axs) /\ esubsts_ok sig sigma /\ hol_term_ok sig tm /\
     no_var_collapse sigma tm /\
     (!s' s. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\
                        hol_term_ok sig s' /\ VFREE_IN s tm)
     ==> ACONV (VSUBST (MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s)) ilist)
                       (esubst sigma avds tm))
               (esubst sigma avds' (VSUBST ilist tm))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (tm:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  QBY "!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\\ s' has_type ty /\\ hol_term_ok
    sig s'"
    (ASM_MESON_TAC[]) THEN
  QBY "!k v. MEM (v,k) ilist ==> welltyped v /\\ ?x ty. k = hol_Var x ty"
    (ASM_MESON_TAC[welltyped_def]) THEN
  ABBREV_TAC `ilist1 = MAP (\(s',s). (esubst sigma [] s',esubst_ty sigma [] s))
                           (ilist:(hol_term#hol_term)list)` THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (ilist1:(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty` (LABEL_TAC "L1") THENL
   [EXPAND_TAC "ilist1" THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    QPAT_ASSUM "!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\\ s' has_type ty /\\
      hol_term_ok sig s'"
      (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (p1:hol_term,p2:hol_term) ilist`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[esubst_ty_var; injectivity "hol_term"] THEN
    QEXISTS_TAC "x" THEN QEXISTS_TAC "ty_esubst sigma ty" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC esubst_has_type1 THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) (ilist1:(hol_term#hol_term)list)
                      ==> welltyped v /\ ?x ty. k = hol_Var x ty` (LABEL_TAC "W1") THENL
   [USE_THEN "L1" MP_TAC THEN MESON_TAC[welltyped_def]; ALL_TAC] THEN
  QBY "welltyped (esubst sigma avds tm)"
   (MATCH_MP_TAC esubst_welltyped THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
    ASM_REWRITE_TAC[]) THEN
  QSPECL_THEN ["VSUBST ilist1 (esubst sigma avds tm)"; "esubst sigma avds' (VSUBST ilist tm)"]
    MP_TAC ACONV_db THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_VSUBST_welltyped THEN QEXISTS_TAC "sig" THEN QEXISTS_TAC "axs" THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[VSUBST_dbVSUBST] THEN
  QSPECL_THEN ["sig"; "sigma"; "tm"; "avds"] MP_TAC db_esubst_thm THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  QSPECL_THEN ["sig"; "sigma"; "VSUBST ilist tm"; "avds'"] MP_TAC db_esubst_thm THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC term_ok_VSUBST THEN ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[VSUBST_dbVSUBST] THEN
  QSPECL_THEN ["sig"; "sigma"; "hol_db tm"; "MAP (\\(x,y). (hol_db x,hol_db y)) ilist"] MP_TAC
    db_esubst_dbVSUBST_comm THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC no_dbvar_collapse_no_combined_collapse THEN CONJ_TAC THENL
       [MATCH_MP_TAC no_var_collapse_no_dbvar_collapse THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
        QPAT_ASSUM "!s' s. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\\ s' has_type ty /\\
          hol_term_ok sig s' /\\ VFREE_IN s tm"
          (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (p1:hol_term,p2:hol_term) ilist`))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[hol_db_def; injectivity "dbterm"] THEN
        ASM_MESON_TAC[CLITAUX_dbVFREE_IN_dbVar]];
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
      QPAT_ASSUM "!s' s. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\\ s' has_type ty /\\
        hol_term_ok sig s' /\\ VFREE_IN s tm"
        (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (p1:hol_term,p2:hol_term) ilist`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[hol_db_def; injectivity "dbterm"] THEN
      ASM_MESON_TAC[term_ok_db_vtys_ok]];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "ilist1" THEN REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  QPAT_ASSUM "!s' s. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\\ s' has_type ty /\\
    hol_term_ok sig s' /\\ VFREE_IN s tm"
    (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (p1:hol_term,p2:hol_term) ilist`))) THEN
  STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC db_esubst_thm THEN QEXISTS_TAC "sig" THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC db_esubst_ty_thm1 THEN QEXISTS_TAC "sig" THEN
    ASM_REWRITE_TAC[hol_term_ok_def] THEN ASM_MESON_TAC[term_ok_has_type_type_ok]]);;

(* VSUBST ilist tm depends only on the entries of ilist whose key is free in tm *)
let CLITAUX_REV_ASSOCD_FILTER = prove
 (`!(P:hol_term->bool) l a (b:hol_term).
     REV_ASSOCD a (FILTER (\(y,x). P x) l) b = if P a then REV_ASSOCD a l b else b`,
  REWRITE_TAC[REV_ASSOCD_FILTER]);;

let CLITAUX_FILTER_SUB = prove
 (`!(P:A->bool) Q l1 l2.
     (!x. P x ==> Q x) /\ FILTER Q l1 = FILTER Q l2 ==> FILTER P l1 = FILTER P l2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!l. FILTER P l = FILTER (P:A->bool) (FILTER Q l)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FILTER_FILTER] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

let CLITAUX_VSUBST_FILTER_EQ = prove
 (`!tm il1 il2.
     FILTER (\(s':hol_term,s:hol_term). VFREE_IN s tm) il1 =
     FILTER (\(s',s). VFREE_IN s tm) il2
     ==> VSUBST il1 tm = VSUBST il2 tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:mlstring`; `ty:hol_type`] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[VSUBST_def; VFREE_IN_def] THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\s:hol_term. hol_Var x ty = s`; `il1:(hol_term#hol_term)list`;
                             `hol_Var x ty`; `hol_Var x ty`] CLITAUX_REV_ASSOCD_FILTER)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\s:hol_term. hol_Var x ty = s`; `il2:(hol_term#hol_term)list`;
                             `hol_Var x ty`; `hol_Var x ty`] CLITAUX_REV_ASSOCD_FILTER)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[VSUBST_def];
    MAP_EVERY X_GEN_TAC [`s:hol_term`; `t:hol_term`] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[VSUBST_def; VFREE_IN_def; injectivity "hol_term"] THEN DISCH_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC CLITAUX_FILTER_SUB THEN
    EXISTS_TAC `\(s':hol_term,x:hol_term). VFREE_IN x s \/ VFREE_IN x t` THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`v:hol_term`; `t:hol_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "IH")) THEN
    MAP_EVERY X_GEN_TAC [`il1:(hol_term#hol_term)list`; `il2:(hol_term#hol_term)list`] THEN
    REWRITE_TAC[VFREE_IN_def] THEN DISCH_TAC THEN
    REWRITE_TAC[VSUBST_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `l1 = FILTER (\(s':hol_term,s:hol_term). ~(s = v))
      (il1:(hol_term#hol_term)list)` THEN
    ABBREV_TAC `l2 = FILTER (\(s':hol_term,s:hol_term). ~(s = v))
      (il2:(hol_term#hol_term)list)` THEN
    SUBGOAL_THEN `FILTER (\(s':hol_term,s). VFREE_IN s t) l1 = FILTER (\(s',s). VFREE_IN s t) l2`
      (LABEL_TAC "EQ") THENL
     [EXPAND_TAC "l1" THEN EXPAND_TAC "l2" THEN REWRITE_TAC[FILTER_FILTER] THEN
      SUBGOAL_THEN `(\x:hol_term#hol_term. (\(s',s). VFREE_IN s t) x /\ (\(s',s). ~(s = v)) x) =
                    (\(s',s). ~(v = s) /\ VFREE_IN s t)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN MESON_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `VSUBST l1 t = VSUBST l2 t` SUBST1_TAC THENL
     [USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `EX (\(s',s). VFREE_IN v s' /\ VFREE_IN s t) l1 <=>
                  EX (\(s',s). VFREE_IN v s' /\ VFREE_IN s t) l2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM] THEN
      USE_THEN "EQ" (fun th -> MP_TAC(GEN_ALL(AP_TERM `MEM (x:hol_term#hol_term)` th))) THEN
      REWRITE_TAC[MEM_FILTER; FORALL_PAIR_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN AP_TERM_TAC THEN USE_THEN "IH" MATCH_MP_TAC THEN
    REWRITE_TAC[FILTER] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let VSUBST_FILTER_VFREE = prove
 (`!sig tm ilist.
     hol_term_ok sig tm
     ==> VSUBST ilist tm = VSUBST (FILTER (\(s',s). VFREE_IN s tm) ilist) tm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLITAUX_VSUBST_FILTER_EQ THEN
  REWRITE_TAC[FILTER_FILTER] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let REV_ASSOCD_APPEND = prove
 (`!(l1:(A#B)list) l2 k d.
     REV_ASSOCD k (APPEND l1 l2) d = REV_ASSOCD k l1 (REV_ASSOCD k l2 d)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; REV_ASSOCD_def] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN PAIR_CASES_ON `h:A#B` THEN
  ASM_REWRITE_TAC[APPEND; REV_ASSOCD_def] THEN MESON_TAC[]);;

let dbVSUBST_comp = prove
 (`!t l1 l2.
     dbVSUBST l2 (dbVSUBST l1 t) =
     dbVSUBST (APPEND (MAP (\(v,k). (dbVSUBST l2 v,k)) l1)
                      (FILTER (\(v,k). ~MEM k (MAP SND l1)) l2)) t`,
  MATCH_MP_TAC dbterm_INDUCT THEN REWRITE_TAC[dbVSUBST_def] THEN
  REWRITE_TAC[REV_ASSOCD_APPEND; REV_ASSOCD_MAP; REV_ASSOCD_FILTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MEM (dbVar a0 a1) (MAP SND (l1:(dbterm#dbterm)list)) <=>
                ?v0. MEM (v0,dbVar a0 a1) l1` SUBST1_TAC THENL
   [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l1:(dbterm#dbterm)list`; `dbVar a0 a1`; `dbVar a0 a1`] REV_ASSOCD_MEM) THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[dbVSUBST_def]]);;

let CLITAUX_FILTER_CONG = prove
 (`!(P:A->bool) Q l. (!x. MEM x l ==> (P x <=> Q x)) ==> FILTER P l = FILTER Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let VSUBST_VSUBST_ACONV = prove
 (`!sig ilist ilist' tm.
     hol_term_ok sig tm /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s') /\
     (!s s'. MEM (s',s) ilist'
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok sig s')
     ==> ACONV (VSUBST (APPEND (MAP (\(s',s). (VSUBST ilist' s',s)) ilist)
                               (FILTER (\(s',s). ~MEM s (MAP SND ilist)) ilist')) tm)
               (VSUBST ilist' (VSUBST ilist tm))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (tm:hol_term)` ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  ABBREV_TAC `L = APPEND (MAP (\(s',s). (VSUBST ilist' s',s)) ilist)
                         (FILTER (\(s',s). ~MEM s (MAP SND ilist))
                                 (ilist':(hol_term#hol_term)list))` THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) L ==> ?x ty. s = hol_Var x ty /\ s' has_type ty`
    (LABEL_TAC "LOK") THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[MEM_APPEND; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[VSUBST_HAS_TYPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) (ilist:(hol_term#hol_term)list)
                      ==> welltyped v /\ ?x ty. k = hol_Var x ty` (LABEL_TAC "W1") THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) (ilist':(hol_term#hol_term)list)
                      ==> welltyped v /\ ?x ty. k = hol_Var x ty` (LABEL_TAC "W2") THENL
   [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `!k v. MEM (v,k) (L:(hol_term#hol_term)list)
                      ==> welltyped v /\ ?x ty. k = hol_Var x ty` (LABEL_TAC "W3") THENL
   [ASM_MESON_TAC[welltyped_def]; ALL_TAC] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (ilist:(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty` (LABEL_TAC "H1") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) (ilist':(hol_term#hol_term)list)
                       ==> ?x ty. s = hol_Var x ty /\ s' has_type ty` (LABEL_TAC "H2") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`VSUBST L tm`; `VSUBST ilist' (VSUBST ilist tm)`] ACONV_db) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `welltyped (VSUBST ilist tm)` ASSUME_TAC THENL
   [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[VSUBST_dbVSUBST] THEN
  GEN_REWRITE_TAC RAND_CONV [dbVSUBST_comp] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "L" THEN REWRITE_TAC[MAP_APPEND] THEN BINOP_TAC THENL
   [REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MATCH_MP_TAC VSUBST_dbVSUBST THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FILTER_MAP] THEN AP_TERM_TAC THEN MATCH_MP_TAC CLITAUX_FILTER_CONG THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    MAP_EVERY X_GEN_TAC [`a:hol_term`; `b:hol_term`] THEN DISCH_TAC THEN
    USE_THEN "W2" (fun th -> MP_TAC(MATCH_MP (SPECL [`b:hol_term`; `a:hol_term`] th)
                                      (ASSUME `MEM (a:hol_term,b:hol_term) ilist'`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[hol_db_def; MAP_MAP_o; MEM_MAP; EXISTS_PAIR_THM; o_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `q1:hol_term` (X_CHOOSE_THEN `q2:hol_term` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`hol_db q1`; `hol_db q2`] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`q1:hol_term`; `q2:hol_term`] THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[hol_db_def]];
      REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(X_CHOOSE_THEN `r1:dbterm` (X_CHOOSE_THEN `r2:dbterm` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `q1:hol_term` (X_CHOOSE_THEN `q2:hol_term` STRIP_ASSUME_TAC))
        ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`q1:hol_term`; `q2:hol_term`] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "W1" (fun th -> MP_TAC(MATCH_MP (SPECL [`q2:hol_term`; `q1:hol_term`] th)
                                        (ASSUME `MEM (q1:hol_term,q2:hol_term) ilist`))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[hol_db_def]) THEN
      ASM_MESON_TAC[injectivity "dbterm"; injectivity "hol_term"]]]);;
