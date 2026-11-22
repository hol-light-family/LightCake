(* ========================================================================= *)
(* littleTheoriesSyntaxNewSystem: port of HOL4 candle/standard/syntax/       *)
(* little_theories/littleTheoriesSyntaxNewSystemScript.sml (CakeML v3479).   *)
(* Some lemmas about the extended Little Theories syntactic functions.       *)
(*                                                                           *)
(* Notes on the rendering: as in littleTheoriesSyntax.ml and                 *)
(* littleTheoriesSyntaxOldSystem_p1.ml (see their headers); HOL4's           *)
(* Overloads lift_ctxt and drop_ctxt are MAP lift_upd and mapPartial         *)
(* drop_upd, written out.  A HOL4 statement binding an unused variable sig   *)
(* (term_ok'_type_ok, term_ok'_VSUBST) keeps the vacuous binder, with a      *)
(* type variable for its type as in HOL4.  HOL4's ML tactics rC, strip_d1,   *)
(* strip_d2, pat_conj and contrapos_tac are CLITAUX_rC, ... (pat_conj and    *)
(* the others where they are used).  Local helpers are CLITAUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/toto.ml";;
needs "hol4/comparison.ml";;
needs "hol4/ternaryComparisons.ml";;
needs "hol4/errorMonad.ml";;
needs "hol4/libext.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/syntax/little_theories/littleTheoriesSyntax.ml";;
needs "candle/standard/syntax/little_theories/littleTheoriesSyntaxOldSystem.ml";;

prioritize_num();;
type_invention_error := true;;

let term_ok'_imp_term_ok = prove
 (`!thy tm. term_ok' thy tm ==> hol_term_ok (ctys thy,ctms thy) tm`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  RW[term_ok'_def; hol_term_ok_def] THEN ASM_MESON_TAC[]);;

let theory_ok'_is_std_sig_ext = prove
 (`!thy. theory_ok' thy ==> is_std_sig (ctys thy,ctms thy)`,
  RW[theory_ok'_def; ctys_def; ctms_def; is_std_sig_def; sigof'_def] THEN
  ASM_REWRITE_TAC[FLOOKUP_FUNION; option_CASE]);;

let theory_ok_drop_thy = prove
 (`!thy es.
     theory_ok' thy /\
     (!a. a IN es ==> hol_term_ok (sigof' thy) a /\ a has_type Tyapp (implode "bool") [])
     ==> theory_ok (drop_thy es thy)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP theory_ok'_is_std_sig_ext) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[theory_ok'_def; sigof'_def]) THEN
  ASM_REWRITE_TAC[theory_ok_def; drop_thy; FST; SND; IN_UNION] THEN CONJ_TAC THENL
   [REWRITE_TAC[ctms_def] THEN ASM_SIMP_TAC[FRANGE_FUNION; IN_UNION] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[ctys_def] THEN
    MATCH_MP_TAC type_ok_weakening THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[term_ok'_imp_term_ok] THEN
    REWRITE_TAC[ctys_def; ctms_def] THEN MATCH_MP_TAC term_ok_weakening THEN
    ASM_SIMP_TAC[]]);;

let term_ok_imp_term_ok' = prove
 (`!thy c. hol_term_ok (ctys thy,ctms thy) c ==> term_ok' thy c`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  RW[term_ok'_def; hol_term_ok_def] THEN ASM_MESON_TAC[]);;

let theory_ok_drop_thy_alt = prove
 (`!thy es.
     theory_ok' thy /\
     (!a. a IN es ==> term_ok' thy a /\ a has_type Tyapp (implode "bool") [])
     ==> theory_ok (drop_thy es thy)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP theory_ok'_is_std_sig_ext) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[theory_ok'_def; sigof'_def]) THEN
  ASM_REWRITE_TAC[theory_ok_def; drop_thy; FST; SND; IN_UNION] THEN CONJ_TAC THENL
   [REWRITE_TAC[ctms_def] THEN ASM_SIMP_TAC[FRANGE_FUNION; IN_UNION] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[ctys_def] THEN
    MATCH_MP_TAC type_ok_weakening THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[term_ok'_imp_term_ok]]);;

let esubst_has_type_bool_alt = prove
 (`!thy sigma avds tm.
     esubsts_ok (ctys thy,ctms thy) sigma /\
     term_ok' thy tm /\
     theory_ok' thy /\
     tm has_type Tyapp (implode "bool") []
     ==> esubst sigma avds tm has_type Tyapp (implode "bool") []`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC esubst_has_type_bool THEN
  MAP_EVERY EXISTS_TAC [`(ctys thy,ctms thy):sig`; `ethy_axs thy`] THEN
  ASM_SIMP_TAC[term_ok'_imp_term_ok] THEN
  MP_TAC(SPECL [`thy:ethy`; `{}:hol_term->bool`] theory_ok_drop_thy_alt) THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; drop_thy; UNION_EMPTY]);;

let ty_esubst_type_ok_id = prove
 (`!tys ty (sigma:(mlstring,mlstring list#hol_type)fmap#A).
     type_ok tys ty /\ DISJOINT (FDOM (FST sigma)) (FDOM tys) ==> ty_esubst sigma ty = ty`,
  GEN_TAC THEN MATCH_MP_TAC type_ind THEN CONJ_TAC THENL
   [SIMP[ty_esubst_def]; REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (FST (sigma:(mlstring,mlstring list#hol_type)fmap#A)) m = NONE`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[type_ok_def; IN_DISJOINT]) THEN
    REWRITE_TAC[flookup_thm] THEN ASM_MESON_TAC[FDOM_FLOOKUP; option_DISTINCT];
    ASM_REWRITE_TAC[ty_esubst_def; option_CASE; injectivity "hol_type"] THEN
    REWRITE_TAC[MAP_EQ_ID] THEN RULE_ASSUM_TAC(REWRITE_RULE[type_ok_def; GSYM ALL_MEM]) THEN
    ASM_MESON_TAC[]]);;

let ty_esubst_o_f_thy_tms = prove
 (`!sigma thy.
     theory_ok' thy /\ esubsts_ok' thy sigma ==> ty_esubst sigma o_f ethy_tms thy = ethy_tms thy`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`sig1:(mlstring,mlstring list#hol_type)fmap`;
                       `sig2:(mlstring,hol_term#hol_type)fmap`; `thy:ethy`] THEN
  REWRITE_TAC[theory_ok'_def; esubsts_ok'_def] THEN STRIP_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f] THEN X_GEN_TAC `k:mlstring` THEN
  QCASES_ON "FLOOKUP (ethy_tms thy) k" THEN REWRITE_TAC[option_CASE; option_INJ] THEN
  MATCH_MP_TAC ty_esubst_type_ok_id THEN EXISTS_TAC `ethy_tys thy` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_FRANGE_FLOOKUP] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FST] THEN ASM SET_TAC[]]);;

let DISJOINT_FLOOKUP = prove
 (`!(f1:(A,B)fmap) (f2:(A,C)fmap) k v.
     DISJOINT (FDOM f1) (FDOM f2) /\ FLOOKUP f1 k = SOME v ==> FLOOKUP f2 k = NONE`,
  REWRITE_TAC[flookup_thm; IN_DISJOINT] THEN MESON_TAC[]);;

let esubsts_ok'_esubsts_ok = prove
 (`!thy sigma.
     esubsts_ok' thy sigma /\ theory_ok' thy ==> esubsts_ok (ctys thy,ctms thy) sigma`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
                       `s2:(mlstring,hol_term#hol_type)fmap`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ty_esubst (s1,s2:(mlstring,hol_term#hol_type)fmap) o_f ethy_tms thy =
                ethy_tms thy` MP_TAC THENL
   [MATCH_MP_TAC ty_esubst_o_f_thy_tms THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[esubsts_ok'_def; theory_ok'_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[esubsts_ok_def; FST; SND] THEN CONJ_TAC THENL
   [X_GEN_TAC `tynm:mlstring` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tynm:mlstring` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "tynm" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`FAPPLY (ethy_etys thy) tynm`; `params:mlstring list`;
                          `body:hol_type`] THEN
    ASM_REWRITE_TAC[ctys_def; FLOOKUP_FUNION] THEN
    SUBGOAL_THEN `~((tynm:mlstring) IN FDOM (ethy_tys thy)) /\ tynm IN FDOM (ethy_etys thy)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FLOOKUP]) THEN ASM_REWRITE_TAC[option_CASE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM FDOM_FLOOKUP]) THEN ASM_MESON_TAC[FLOOKUP_FAPPLY];
    X_GEN_TAC `tmnm:mlstring` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tmnm:mlstring` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "tmnm" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`FAPPLY (ethy_etms thy) tmnm`; `repl:hol_term`;
                          `decl_ty:hol_type`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ctms_def; FLOOKUP_FUNION] THEN
      SUBGOAL_THEN `~((tmnm:mlstring) IN FDOM (ethy_tms thy)) /\ tmnm IN FDOM (ethy_etms thy)`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FLOOKUP]) THEN ASM_REWRITE_TAC[option_CASE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM FDOM_FLOOKUP]) THEN ASM_MESON_TAC[FLOOKUP_FAPPLY];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP term_ok'_imp_term_ok o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "term_ok'" with Failure _ -> false)) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[esubst_sig_def; PAIR_EQ] THEN
      REWRITE_TAC[esubst_thy_def; ctys_def; ctms_def; ethy_INFO.ri_accfupds] THEN
      SIMP[o_f_FUNION]]]);;

let esubst_thy_ctys = prove
 (`!sigma thy. ctys (esubst_thy sigma thy) = ctys thy`,
  RW[esubst_thy_def; ctys_def]);;
let _ = cake_add_simps [esubst_thy_ctys];;

let type_ok_ctys_ty_esubst = prove
 (`!thy sigma ty.
     type_ok (ctys thy) ty /\
     esubsts_ok' thy sigma
     ==> type_ok (ctys thy) (ty_esubst sigma ty)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
                       `s2:(mlstring,hol_term#hol_type)fmap`] THEN
  MATCH_MP_TAC type_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[ty_esubst_def; type_ok_def]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:mlstring`; `l:hol_type list`] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  QBY "!t. MEM t l ==> type_ok (ctys thy) (ty_esubst (s1,s2) t)"
    (RULE_ASSUM_TAC(REWRITE_RULE[type_ok_def; GSYM ALL_MEM]) THEN ASM_MESON_TAC[]) THEN
  REWRITE_TAC[ty_esubst_def; FST] THEN
  NAMED_CASES_ON "FLOOKUP s1 m" [""; "pb"] THEN REWRITE_TAC[option_CASE] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[type_ok_def]) THEN
  ASM_REWRITE_TAC[type_ok_def; LENGTH_MAP; GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[];
    PAIR_CASES_ON `pb:mlstring list#hol_type` THEN REWRITE_TAC[pair_CASE] THEN
    MATCH_MP_TAC type_ok_TYPE_SUBST THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[esubsts_ok'_def; FLOOKUP_FAPPLY]) THEN
      ASM_MESON_TAC[PAIR_EQ];
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_ZIP_FST) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MEM_TAKE) THEN REWRITE_TAC[MEM_MAP] THEN
      ASM_MESON_TAC[]]]);;

let ty_esubst_type_ok' = prove
 (`!thy sigma ty.
     theory_ok' thy /\ esubsts_ok' thy sigma /\ type_ok (ctys thy) ty
     ==> type_ok (ctys thy) (ty_esubst sigma ty)`,
  MESON_TAC[type_ok_ctys_ty_esubst]);;

(* HOL4 variables sigma_ty, sigma_tm are sigty, sigtm *)
let esubst_thy_ctms_preserved = prove
 (`!thy sigty sigtm n ty0.
     theory_ok' thy /\ esubsts_ok' thy (sigty,sigtm) /\
     FLOOKUP (ctms thy) n = SOME ty0 /\ ~(n IN FDOM sigtm)
     ==> FLOOKUP (ctms (esubst_thy (sigty,sigtm) thy)) n =
         SOME (ty_esubst (sigty,sigtm) ty0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[esubst_thy_def; ctms_def; FLOOKUP_FUNION; FLOOKUP_o_f] THEN
  SIMP[] THEN
  QCASES_ON "FLOOKUP (ethy_tms thy) n" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ctms_def; FLOOKUP_FUNION]) THEN
  GVS[option_CASE; FLOOKUP_o_f] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ty_esubst_type_ok_id THEN
  EXISTS_TAC `ethy_tys thy` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[theory_ok'_def; esubsts_ok'_def]) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o el 0 o CONJUNCTS) THEN
    REWRITE_TAC[IN_FRANGE_FLOOKUP] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FST] THEN ASM SET_TAC[]]);;

let term_ok'_vsubst_variant = prove
 (`!thy tm ty x1 x2.
     term_ok' thy tm /\ type_ok (ctys thy) ty
     ==> term_ok' thy (VSUBST [(hol_Var x1 ty,hol_Var x2 ty)] tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_imp_term_ok' THEN
  MATCH_MP_TAC term_ok_VSUBST THEN
  ASM_SIMP_TAC[term_ok'_imp_term_ok; hol_term_ok_def; MEM; PAIR_EQ] THEN
  MESON_TAC[has_type_rules]);;

let esubst_ty0_tm_ok' = prove
 (`!thy env sigma avds tm subst_tm.
     esubst_ty0 env sigma avds tm = errorMonad_return subst_tm /\
     term_ok' thy tm /\ theory_ok' thy /\ esubsts_ok' thy sigma /\
     esubsts_ok (ctys thy,ctms thy) sigma /\
     (!v1 v2. MEM (v1,v2) env
              ==> ?n ty. v1 = hol_Var n ty /\ v2 = hol_Var n (ty_esubst sigma ty))
     ==> term_ok' (esubst_thy sigma thy) (esubst_tm sigma subst_tm)`,
  GEN_TAC THEN REC_IND_TAC esubst_ty0_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[esubst_ty0_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      COND_CASES_TAC THEN GVS[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[esubst_tm_def; term_ok'_def; esubst_thy_ctys] THEN
      MATCH_MP_TAC type_ok_ctys_ty_esubst THEN RULE_ASSUM_TAC(REWRITE_RULE[term_ok'_def]) THEN
      ASM_REWRITE_TAC[];
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
        `s2:(mlstring,hol_term#hol_type)fmap`; `avds:mlstring list`; `n:mlstring`;
        `ty:hol_type`; `subst_tm:hol_term`] THEN
      REWRITE_TAC[esubst_ty0_def; injectivity "error"] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[esubst_tm_def; SND] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[term_ok'_def] o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "term_ok'" with Failure _ -> false)) THEN
      DISCH_THEN(X_CHOOSE_THEN `ty0:hol_type` STRIP_ASSUME_TAC) THEN
      NAMED_CASES_ON "FLOOKUP s2 n" [""; "rd"] THEN REWRITE_TAC[option_CASE] THENL
     [REWRITE_TAC[term_ok'_def; esubst_thy_ctys] THEN
        QEXISTS_TAC "ty_esubst (s1,s2) ty0" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC esubst_thy_ctms_preserved THEN ASM_REWRITE_TAC[] THEN
         ASM_MESON_TAC[flookup_thm];
        MATCH_MP_TAC type_ok_ctys_ty_esubst THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th))))
          THEN
          MATCH_MP_TAC ty_esubst_TYPE_SUBST THEN
          MAP_EVERY EXISTS_TAC [`ctys thy`; `ctms thy`] THEN ASM_REWRITE_TAC[]];
      PAIR_CASES_ON `rd:hol_term#hol_type` THEN REWRITE_TAC[pair_CASE] THEN
        MP_TAC(REWRITE_RULE[esubsts_ok'_def] (ASSUME `esubsts_ok' thy (s1,s2)`)) THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:mlstring` o check (fun th ->
            try fst(dest_var(fst(dest_forall(concl th)))) = "tmnm" with Failure _ -> false)) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[flookup_thm]; ALL_TAC] THEN STRIP_TAC THEN
        SUBGOAL_THEN `repl:hol_term = rd0 /\ decl_ty:hol_type = rd1`
          (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm]) THEN ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
      MP_TAC(REWRITE_RULE[theory_ok'_def] (ASSUME `theory_ok' thy`)) THEN STRIP_TAC THEN
        QBY "n IN FDOM s2" (ASM_MESON_TAC[flookup_thm]) THEN
        SUBGOAL_THEN `ty0:hol_type = rd1` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `FLOOKUP (ctms thy) n = SOME (ty0:hol_type)` THEN
          REWRITE_TAC[ctms_def; FLOOKUP_FUNION] THEN
          SUBGOAL_THEN `FLOOKUP (ethy_tms thy) n = NONE` SUBST1_TAC THENL
           [REWRITE_TAC[flookup_thm] THEN ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[option_CASE; flookup_thm] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`(ctys thy,ctms thy):sig`;
          `(s1,s2):(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
          `ty:hol_type`; `rd1:hol_type`] ty_esubst_match_type) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[FST] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
        MATCH_MP_TAC term_ok_imp_term_ok' THEN MATCH_MP_TAC term_ok_INST THEN CONJ_TAC THENL
         [MATCH_MP_TAC term_ok'_imp_term_ok THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[esubst_thy_ctys; FST] THEN MATCH_MP_TAC match_type_type_ok THEN
          QEXISTS_TAC "ty_esubst (s1,s2) rd1" THEN QEXISTS_TAC "ty_esubst (s1,s2) ty" THEN
          CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC type_ok_ctys_ty_esubst THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]];
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
        `s2:(mlstring,hol_term#hol_type)fmap`; `avds:mlstring list`; `t1:hol_term`;
        `t2:hol_term`] THEN
      STRIP_TAC THEN X_GEN_TAC `subst_tm:hol_term` THEN
      REWRITE_TAC[esubst_ty0_def; bind_EQ_return] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "error"]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))
      THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[term_ok'_def] o check (fun th ->
        concl th = `term_ok' thy (hol_Comb t1 t2)`)) THEN
      REWRITE_TAC[esubst_tm_def; term_ok'_def] THEN
    (SUBGOAL_THEN `term_ok' (esubst_thy (s1,s2) thy) (esubst_tm (s1,s2) u) /\
                    term_ok' (esubst_thy (s1,s2) thy) (esubst_tm (s1,s2) u')` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC);
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[term_ok'_imp_term_ok; term_ok_welltyped]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[term_ok'_imp_term_ok; term_ok_welltyped]; ALL_TAC] THEN
      SUBGOAL_THEN `is_std_sig (ctys thy,ctms thy)` ASSUME_TAC THENL
       [ASM_MESON_TAC[theory_ok'_is_std_sig_ext]; ALL_TAC] THEN
      SUBGOAL_THEN `!t v. hol_term_ok (ctys thy,ctms thy) t /\
                          esubst_ty0 env (s1,s2) avds t = errorMonad_return v
                          ==> typeof (esubst_tm (s1,s2) v) = ty_esubst (s1,s2) (typeof t)`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `typeof (v:hol_term)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC typeof_esubst_tm_esubst_ty0 THEN
          MAP_EVERY EXISTS_TAC [`t:hol_term`; `env:(hol_term#hol_term)list`;
                                `(ctys thy,ctms thy):sig`; `avds:mlstring list`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MATCH_MP_TAC typeof_esubst_ty THEN
          MAP_EVERY EXISTS_TAC [`(ctys thy,ctms thy):sig`; `env:(hol_term#hol_term)list`;
                                `avds:mlstring list`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `hol_term_ok (ctys thy,ctms thy) t1 /\ hol_term_ok (ctys thy,ctms thy) t2`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok'_imp_term_ok]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[WELLTYPED_CLAUSES] o check (fun th ->
        concl th = `welltyped (hol_Comb t1 t2)`)) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      QEXISTS_TAC "ty_esubst (s1,s2) rty" THEN MATCH_MP_TAC ty_esubst_fun THEN
      EXISTS_TAC `(ctys thy,ctms thy):sig` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `env:(hol_term#hol_term)list` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:(mlstring,mlstring list#hol_type)fmap`;
        `s2:(mlstring,hol_term#hol_type)fmap`; `avds:mlstring list`; `v:hol_term`;
        `body:hol_term`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      X_GEN_TAC `subst_tm:hol_term` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[term_ok'_def] o check (fun th ->
        concl th = `term_ok' thy (hol_Abs v body)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `ty:hol_type` STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `v:hol_term = hol_Var x ty` THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[dest_var_def; PAIR_EQ]) THEN
    UNDISCH_TAC `esubst_ty0 env (s1,s2) avds (hol_Abs (hol_Var x ty) body) =
                   errorMonad_return subst_tm` THEN
      REWRITE_TAC[esubst_ty0_def; dest_var_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[try_eq_return; bind_EQ_return; bind_EQ_error; injectivity "error";
                  distinctness "error"] THEN
    SUBGOAL_THEN `type_ok (ctys (esubst_thy (s1,s2) thy)) (ty_esubst (s1,s2) ty)` ASSUME_TAC THENL
       [REWRITE_TAC[esubst_thy_ctys] THEN MATCH_MP_TAC ty_esubst_type_ok' THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def; term_ok'_def] THEN
        QEXISTS_TAC "x" THEN QEXISTS_TAC "ty_esubst (s1,s2) ty" THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:mlstring`; `ty:hol_type`] o check (fun th ->
          try length(fst(strip_forall(concl th))) = 2 with Failure _ -> false)) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
        ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
        COND_CASES_TAC THEN REWRITE_TAC[distinctness "error"; bind_EQ_return; injectivity "error"]
          THEN
        STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[esubst_tm_def; term_ok'_def] THEN
        QEXISTS_TAC "NVARIANT x avds u" THEN QEXISTS_TAC "ty_esubst (s1,s2) ty" THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`e:hol_term`; `u:hol_term`; `x:mlstring`; `ty:hol_type`] o
          check (fun th -> try length(fst(strip_forall(concl th))) = 4 with Failure _ -> false))
            THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC term_ok'_vsubst_variant THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[]]]]);;

let esubst_term_ok' = prove
 (`!thy sigma tm avds.
     theory_ok' thy /\ esubsts_ok' thy sigma /\ term_ok' thy tm
     ==> term_ok' (esubst_thy sigma thy) (esubst sigma avds tm)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `esubsts_ok (ctys thy,ctms thy) sigma` ASSUME_TAC THENL
   [ASM_MESON_TAC[esubsts_ok'_esubsts_ok]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
                 `tm:hol_term`; `(ctys thy,ctms thy):sig`; `avds:mlstring list`]
    esubst_ty0_always_returns) THEN
  ASM_SIMP_TAC[term_ok'_imp_term_ok] THEN DISCH_THEN(X_CHOOSE_TAC `v:hol_term`) THEN
  ASM_REWRITE_TAC[esubst_def; esubst_ty_def] THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC esubst_ty0_tm_ok' THEN
  MAP_EVERY EXISTS_TAC [`[]:(hol_term#hol_term)list`; `avds:mlstring list`; `tm:hol_term`] THEN
  ASM_REWRITE_TAC[MEM]);;

let theory_ok'_esubst = prove
 (`!thy sigma.
     theory_ok' thy /\ esubsts_ok' thy sigma ==> theory_ok' (esubst_thy sigma thy)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `esubsts_ok (ctys thy,ctms thy) sigma` ASSUME_TAC THENL
   [ASM_MESON_TAC[esubsts_ok'_esubsts_ok]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[theory_ok'_def; sigof'_def] (ASSUME `theory_ok' thy`)) THEN
  STRIP_TAC THEN
  REWRITE_TAC[theory_ok'_def; esubst_thy_ctys; sigof'_def] THEN
  REWRITE_TAC[esubst_thy_def; ethy_INFO.ri_accfupds; K_THM; FDOM_o_f] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM esubst_thy_def; FORALL_IN_IMAGE] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP in_frange_o_f) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC type_ok_ctys_ty_esubst THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC esubst_term_ok' THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC esubst_has_type_bool_alt THEN EXISTS_TAC `thy:ethy` THEN ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC esubst_term_ok' THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC esubst_has_type_bool_alt THEN EXISTS_TAC `thy:ethy` THEN ASM_SIMP_TAC[]]]);;

let proves'_imp_theory_ok' = prove
 (`!thy h es c. proves' (thy,es,h) c ==> theory_ok' thy`,
  SUBGOAL_THEN `!a (c:hol_term). proves' a c ==> theory_ok' (FST a)`
    (fun th -> MESON_TAC[th; FST]) THEN
  MATCH_MP_TAC proves'_ind THEN REWRITE_TAC[FST] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(MATCH_MP_TAC theory_ok'_esubst) THEN ASM_REWRITE_TAC[]);;

let term_ok_term_ok'_weakening = prove
 (`!thy p. hol_term_ok (sigof' thy) p ==> term_ok' thy p`,
  REWRITE_TAC[sigof'_def] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_imp_term_ok' THEN
  REWRITE_TAC[ctys_def; ctms_def] THEN MATCH_MP_TAC term_ok_weakening THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 contrapos_tac: CLITAUX_contrapos_tac (littleTheoriesSyntaxOldSystem_p1.ml) *)

let drop_thy_weakening = prove
 (`!B A thy' h c.
     (drop_thy B thy',h) |- c /\ B SUBSET A /\
     (!ax. ax IN A ==> hol_term_ok (ctys thy',ctms thy') ax /\
                       ax has_type Tyapp (implode "bool") [])
     ==> (drop_thy A thy',h) |- c`,
  REWRITE_TAC[drop_thy] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC axiom_weakening THEN
  EXISTS_TAC `ethy_axs thy' UNION B` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP proves_imp_theory_ok) THEN
    REWRITE_TAC[theory_ok_def; FST; SND; IN_UNION] THEN ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

let axioms_ok_no_var_collapse = prove
 (`!thy axs sigma.
     axioms_ok thy axs /\ esubsts_ok' thy sigma
     ==> !ax. ax IN axs ==> no_var_collapse sigma ax`,
  REWRITE_TAC[axioms_ok_def] THEN MESON_TAC[]);;

let proves_esubst_drop_thy = prove
 (`!es thy h c sigma.
     (drop_thy es thy,h) |- c /\
     theory_ok' thy /\
     esubsts_ok' thy sigma /\
     axioms_ok thy (ethy_axs thy) /\
     (!ax. ax IN es ==> no_var_collapse sigma ax)
     ==> (drop_thy (IMAGE (esubst sigma []) es) (esubst_thy sigma thy),
          term_image (esubst sigma []) h) |- esubst sigma (FLAT (MAP tm_names h)) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap`;
    `(ctys thy,ctms thy):sig`; `ethy_axs thy UNION es`; `h:hol_term list`; `c:hol_term`]
   proves_substitutable) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[drop_thy]) THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[little_proves_theory_ok];
      ASM_MESON_TAC[esubsts_ok'_esubsts_ok];
      REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[axioms_ok_no_var_collapse]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ; drop_thy; esubst_sig_def; IMAGE_UNION; esubst_thy_ctys] THEN
  REWRITE_TAC[esubst_thy_def; ctms_def; ethy_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[o_f_FUNION] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ty_esubst_o_f_thy_tms THEN ASM_REWRITE_TAC[]);;

let theory_ok'_lift_thy = prove
 (`!thy. theory_ok thy ==> theory_ok' (lift_thy thy)`,
  RW[theory_ok_def; theory_ok'_def; ctys_lift_thy; FRANGE_FEMPTY; FDOM_FEMPTY;
     DISJOINT_EMPTY; NOT_IN_EMPTY; term_ok'_lift_thy]);;
let _ = cake_add_simps [theory_ok'_lift_thy];;

let CLITAUX_EMPTY_ES th =
  REWRITE_RULE[UNION_EMPTY]
   (GEN_ALL (INST [`{}:hol_term->bool`,`es1:hol_term->bool`;
                   `{}:hol_term->bool`,`es2:hol_term->bool`] (SPEC_ALL th)));;

let CLITAUX_IH_TAC = FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let CLITAUX_TOK_TAC = MATCH_MP_TAC term_ok_imp_term_ok' THEN ASM_REWRITE_TAC[PAIR];;

let proves_imp_proves'_subset_axs = prove
 (`!thy h c.
     (thy,h) |- c
     ==> !thy'. FST (FST thy) = ctys thy' /\
                SND (FST thy) = ctms thy' /\
                SND thy SUBSET ethy_axs thy' /\
                theory_ok' thy'
                ==> proves' (thy',{},h) c`,
  SUBGOAL_THEN
   `!a (c:hol_term). a |- c
      ==> !thy'. theory_ok' thy' /\ ctys thy' = FST (FST (FST a)) /\
                 ctms thy' = SND (FST (FST a)) /\ SND (FST a) SUBSET ethy_axs thy'
                 ==> proves' (thy',{},SND a) c`
   (fun th -> REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP th) THEN
              REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC proves_ind THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `thy':ethy` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC proves'_ABS THEN ASM_REWRITE_TAC[] THEN CLITAUX_IH_TAC;
    MATCH_MP_TAC proves'_ASSUME THEN ASM_REWRITE_TAC[] THEN CLITAUX_TOK_TAC;
    MATCH_MP_TAC proves'_BETA THEN ASM_REWRITE_TAC[] THEN CLITAUX_TOK_TAC;
    MATCH_MP_TAC (CLITAUX_EMPTY_ES proves'_DEDUCT_ANTISYM) THEN CONJ_TAC THEN CLITAUX_IH_TAC;
    MATCH_MP_TAC (CLITAUX_EMPTY_ES proves'_EQ_MP) THEN
    MAP_EVERY EXISTS_TAC [`p:hol_term`; `p':hol_term`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN CLITAUX_IH_TAC;
    MATCH_MP_TAC proves'_INST THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_term`; `s':hol_term`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"] THEN
      MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
      CLITAUX_TOK_TAC;
      CLITAUX_IH_TAC];
    MATCH_MP_TAC proves'_INST_TYPE THEN ASM_REWRITE_TAC[] THEN CLITAUX_IH_TAC;
    MATCH_MP_TAC (CLITAUX_EMPTY_ES proves'_MK_COMB) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN CLITAUX_IH_TAC;
    MATCH_MP_TAC proves'_REFL THEN ASM_REWRITE_TAC[] THEN CLITAUX_TOK_TAC;
    MATCH_MP_TAC proves'_axioms THEN ASM SET_TAC[]]);;

let proves_imp_proves' = prove
 (`!thy' h c. (thy',h) |- c ==> proves' (lift_thy thy',{},h) c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP proves_imp_proves'_subset_axs) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ctys_lift_thy; ctms_lift_thy; axsof_lift_thy; SUBSET_REFL] THEN
  MATCH_MP_TAC theory_ok'_lift_thy THEN ASM_MESON_TAC[little_proves_theory_ok]);;

let CLITAUX_DROP_OK_TAC =
  IMP_RES_TAC little_proves_theory_ok THEN
  RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def; drop_thy; FST; SND; IN_UNION]) THEN
  REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];;

let CLITAUX_DROP_WEAK_TAC es =
  MATCH_MP_TAC drop_thy_weakening THEN EXISTS_TAC es THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; CLITAUX_DROP_OK_TAC];;

let proves'_imp_proves = prove
 (`!thy' c h used_eaxs.
     proves' (thy',used_eaxs,h) c ==> (drop_thy used_eaxs thy',h) |- c`,
  SUBGOAL_THEN `!a (c:hol_term). proves' a c ==> (drop_thy (FST (SND a)) (FST a),SND (SND a)) |- c`
   (fun th -> MESON_TAC[th; FST; SND]) THEN
  MATCH_MP_TAC proves'_ind THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC proves_ABS THEN ASM_REWRITE_TAC[sigof_drop_thy; FST];
    MATCH_MP_TAC proves_ASSUME THEN ASM_REWRITE_TAC[sigof_drop_thy] THEN CONJ_TAC THENL
     [MATCH_MP_TAC theory_ok_drop_thy THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      MATCH_MP_TAC term_ok'_imp_term_ok THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC proves_BETA THEN ASM_REWRITE_TAC[sigof_drop_thy; FST] THEN
      CONJ_TAC THENL
     [MATCH_MP_TAC theory_ok_drop_thy THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      MATCH_MP_TAC term_ok'_imp_term_ok THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC proves_DEDUCT_ANTISYM THEN CONJ_TAC THENL
     [CLITAUX_DROP_WEAK_TAC `es1:hol_term->bool`; CLITAUX_DROP_WEAK_TAC `es2:hol_term->bool`];
    MATCH_MP_TAC proves_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`p:hol_term`; `p':hol_term`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CLITAUX_DROP_WEAK_TAC `es1:hol_term->bool`; CLITAUX_DROP_WEAK_TAC `es2:hol_term->bool`];
    MATCH_MP_TAC proves_INST THEN ASM_REWRITE_TAC[sigof_drop_thy] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_term`; `s':hol_term`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"] THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC term_ok'_imp_term_ok THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_INST_TYPE THEN ASM_REWRITE_TAC[sigof_drop_thy; FST];
    MATCH_MP_TAC proves_MK_COMB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CLITAUX_DROP_WEAK_TAC `es1:hol_term->bool`; CLITAUX_DROP_WEAK_TAC `es2:hol_term->bool`];
    MATCH_MP_TAC proves_REFL THEN ASM_REWRITE_TAC[sigof_drop_thy] THEN CONJ_TAC THENL
     [MATCH_MP_TAC theory_ok_drop_thy THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      MATCH_MP_TAC term_ok'_imp_term_ok THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC proves_axioms THEN REWRITE_TAC[drop_thy; SND; IN_UNION] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM drop_thy] THEN
    MATCH_MP_TAC theory_ok_drop_thy THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
    RULE_ASSUM_TAC(REWRITE_RULE[drop_thy]) THEN REWRITE_TAC[drop_thy] THEN
    ASM_CASES_TAC `(c1:hol_term) IN ethy_axs thy` THENL
     [ASM_SIMP_TAC[thy_axs_diff_alt] THEN MATCH_MP_TAC axiom_weakening THEN
      EXISTS_TAC `ethy_axs thy UNION es2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [IMP_RES_TAC little_proves_theory_ok THEN
        RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def; FST; SND; IN_UNION]) THEN
        REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
        SET_TAC[]];
      ASM_SIMP_TAC[thy_axs_diff] THEN
      MP_TAC(ISPECL [`((ctys thy,ctms thy),ethy_axs thy UNION es1):thy`;
                     `((ctys thy,ctms thy),ethy_axs thy UNION es2):thy`;
                     `h2:hol_term list`; `c1:hol_term`; `c2:hol_term`] axioms_eliminable) THEN
      ASM_REWRITE_TAC[FST; SND]];
    MATCH_MP_TAC proves_esubst_drop_thy THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC proves_axioms THEN CONJ_TAC THENL
     [MATCH_MP_TAC theory_ok_drop_thy_alt THEN ASM_REWRITE_TAC[IN_SING] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[theory_ok'_def]) THEN ASM_MESON_TAC[];
      REWRITE_TAC[drop_thy; SND; IN_UNION; IN_SING]]]);;

let extends'_ind = prove
 (`!P. (!upd ctxt. upd updates' ctxt /\ P ctxt ==> P (CONS upd ctxt))
       ==> !ctxt1 ctxt2. ctxt2 extends' ctxt1 ==> P ctxt1 ==> P ctxt2`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[extends'_def] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  ASM_MESON_TAC[]);;

let SUBMAP_FUNION_mono = prove
 (`!(f1:(A,B)fmap) f2 g.
     f1 SUBMAP f2 /\ DISJOINT (FDOM f2) (FDOM g) ==> FUNION f1 g SUBMAP FUNION f2 g`,
  RW[SUBMAP_DEF; FUNION_DEF; FDOM_FUNION; IN_UNION] THEN ASM_MESON_TAC[IN_DISJOINT]);;

let SUBMAP_FUNION_mono_r = prove
 (`!(f:(A,B)fmap) g1 g2. g1 SUBMAP g2 ==> FUNION f g1 SUBMAP FUNION f g2`,
  RW[SUBMAP_DEF; FUNION_DEF; FDOM_FUNION; IN_UNION] THEN ASM_MESON_TAC[]);;

let term_ok'_eq = prove
 (`!thy1 thy2 tm.
     ctys thy1 = ctys thy2 /\ ctms thy1 = ctms thy2
     ==> (term_ok' thy1 tm <=> term_ok' thy2 tm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`tm:hol_term`,`tm:hol_term`) THEN
  MATCH_MP_TAC hol_term_INDUCT THEN ASM_SIMP_TAC[term_ok'_def]);;

let type_ok_ctys_subset = prove
 (`!thy1 thy2 ty.
     ctys thy1 SUBMAP ctys thy2 /\
     type_ok (ctys thy1) ty
     ==> type_ok (ctys thy2) ty`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC type_ind THEN
  RW[type_ok_def; GSYM ALL_MEM] THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let term_ok'_ctms_ctys_subset = prove
 (`!thy1 thy2 tm.
     ctys thy1 SUBMAP ctys thy2 /\
     ctms thy1 SUBMAP ctms thy2
     ==> term_ok' thy1 tm
     ==> term_ok' thy2 tm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`tm:hol_term`,`tm:hol_term`) THEN
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[term_ok'_def] THEN
  ASM_MESON_TAC[type_ok_ctys_subset; FLOOKUP_SUBMAP]);;

let type_ok_FUPDATE_fresh = prove
 (`!tys name a ty.
     type_ok tys ty /\ ~(name IN FDOM tys) ==> type_ok (tys |+ (name,a)) ty`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ty:hol_type`,`ty:hol_type`) THEN
  MATCH_MP_TAC type_ind THEN RW[type_ok_def; FLOOKUP_UPDATE; GSYM ALL_MEM] THEN
  ASM_MESON_TAC[FDOM_FLOOKUP; option_DISTINCT]);;

let term_ok'_tms_FUNION_fresh = prove
 (`!thy alist p.
     term_ok' thy p /\
     (!s. MEM s (MAP FST alist) ==> ~(s IN FDOM (ethy_tms thy))) /\
     (!s. MEM s (MAP FST alist) ==> ~(s IN FDOM (ethy_etms thy)))
     ==> term_ok' (ethy_tms_fupd (K (FUNION (alist_to_fmap alist) (ethy_tms thy))) thy) p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] term_ok'_ctms_ctys_subset) THEN
  EXISTS_TAC `thy:ethy` THEN
  ASM_REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accfupds; K_THM; SUBMAP_REFL] THEN
  REWRITE_TAC[SUBMAP_DEF; FUNION_DEF; FDOM_FUNION; IN_UNION; FDOM_alist_to_fmap;
              IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[]);;

let proves'_theory_ok' = prove
 (`!thy es h c. proves' (thy,es,h) c ==> theory_ok' thy`,
  MESON_TAC[proves'_imp_theory_ok']);;

let term_ok'_welltyped = prove
 (`!thy t. term_ok' thy t ==> welltyped t`,
  MESON_TAC[term_ok'_imp_term_ok; term_ok_welltyped]);;

let term_ok'_type_ok = prove
 (`!thy (sig:A) t. theory_ok' thy /\ term_ok' thy t ==> type_ok (ctys thy) (typeof t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(ctys thy,ctms thy)`; `t:hol_term`] term_ok_type_ok) THEN
  ASM_SIMP_TAC[theory_ok'_is_std_sig_ext; term_ok'_imp_term_ok]);;

let term_ok'_equation = prove
 (`!thy s t.
     theory_ok' thy
     ==> (term_ok' thy (s === t) <=>
          term_ok' thy s /\ term_ok' thy t /\ typeof t = typeof s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!X. term_ok' thy X <=> hol_term_ok (ctys thy,ctms thy) X`
    (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[term_ok'_imp_term_ok; term_ok_imp_term_ok'];
    MATCH_MP_TAC(GEN_ALL term_ok_equation) THEN ASM_SIMP_TAC[theory_ok'_is_std_sig_ext]]);;

let term_ok'_VSUBST = prove
 (`!thy (sig:A) tm ilist.
     term_ok' thy tm /\
     (!s s'. MEM (s',s) ilist
             ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ term_ok' thy s')
     ==> term_ok' thy (VSUBST ilist tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_imp_term_ok' THEN
  MATCH_MP_TAC term_ok_VSUBST THEN ASM_SIMP_TAC[term_ok'_imp_term_ok] THEN
  ASM_MESON_TAC[term_ok'_imp_term_ok]);;

let term_ok'_INST = prove
 (`!thy tyin tm.
     term_ok' thy tm /\ ALL (type_ok (ctys thy)) (MAP FST tyin)
     ==> term_ok' thy (INST tyin tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC term_ok_imp_term_ok' THEN
  MATCH_MP_TAC term_ok_INST THEN ASM_SIMP_TAC[term_ok'_imp_term_ok]);;

let CLITAUX_EQN_TAC l r =
  SUBGOAL_THEN (mk_conj(mk_comb(`term_ok' thy`,l),
                mk_conj(mk_comb(`term_ok' thy`,r),
                        mk_eq(mk_comb(`typeof`,r),mk_comb(`typeof`,l)))))
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[term_ok'_equation]; ALL_TAC];;

let proves'_term_ok' = prove
 (`!thy h tm. proves' (thy,h) tm ==> term_ok' thy tm /\ tm has_type Tyapp (implode "bool") []`,
  SUBGOAL_THEN `!a (c:hol_term). proves' a c
                  ==> term_ok' (FST a) c /\ c has_type Tyapp (implode "bool") []`
   (fun th -> MESON_TAC[th; FST]) THEN
  MATCH_MP_TAC proves'_strongind THEN REWRITE_TAC[FST] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(FIRST_ASSUM(ASSUME_TAC o MATCH_MP proves'_theory_ok')) THENL
   [CLITAUX_EQN_TAC `l:hol_term` `r:hol_term` THEN
    ASM_SIMP_TAC[term_ok'_equation; EQUATION_HAS_TYPE_BOOL] THEN
    REWRITE_TAC[term_ok'_def; WELLTYPED_CLAUSES; typeof_def] THEN
    ASM_MESON_TAC[term_ok'_welltyped];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[term_ok'_equation; EQUATION_HAS_TYPE_BOOL] THEN
    REWRITE_TAC[term_ok'_def; WELLTYPED_CLAUSES; typeof_def; codomain_def] THEN
    ASM_MESON_TAC[term_ok'_welltyped];
    ASM_SIMP_TAC[term_ok'_equation; EQUATION_HAS_TYPE_BOOL] THEN
    ASM_MESON_TAC[WELLTYPED_LEMMA; term_ok'_welltyped];
    CLITAUX_EQN_TAC `p:hol_term` `q:hol_term` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `typeof p = typeof (p':hol_term)` ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[ACONV_TYPE] `ACONV s t /\ welltyped s /\ welltyped t ==> typeof s = typeof
       t`) THEN
      ASM_MESON_TAC[term_ok'_welltyped];
      ALL_TAC] THEN
    ASM_MESON_TAC[WELLTYPED_LEMMA; WELLTYPED; term_ok'_welltyped];
    CONJ_TAC THENL
     [MATCH_MP_TAC term_ok'_VSUBST THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_MESON_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC term_ok'_INST THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INST_HAS_TYPE THEN EXISTS_TAC `Tyapp (implode "bool") []` THEN
      ASM_REWRITE_TAC[TYPE_SUBST_Bool]];
    CLITAUX_EQN_TAC `l1:hol_term` `r1:hol_term` THEN CLITAUX_EQN_TAC `l2:hol_term` `r2:hol_term`
      THEN
    SUBGOAL_THEN `welltyped (hol_Comb r1 r2)` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[WELLTYPED_CLAUSES]) THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN
      ASM_MESON_TAC[term_ok'_welltyped];
      ALL_TAC] THEN
    ASM_SIMP_TAC[term_ok'_equation; EQUATION_HAS_TYPE_BOOL] THEN
    ASM_REWRITE_TAC[term_ok'_def; typeof_def];
    ASM_SIMP_TAC[term_ok'_equation; EQUATION_HAS_TYPE_BOOL] THEN ASM_MESON_TAC[term_ok'_welltyped];
    RULE_ASSUM_TAC(REWRITE_RULE[theory_ok'_def]) THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [MATCH_MP_TAC esubst_term_ok' THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC esubst_has_type_bool_alt THEN EXISTS_TAC `thy:ethy` THEN
      ASM_SIMP_TAC[esubsts_ok'_esubsts_ok]];
    RULE_ASSUM_TAC(REWRITE_RULE[theory_ok'_def]) THEN ASM_MESON_TAC[]]);;

let MAP_FST_MAP = prove
 (`!(l:(A#B)list) (P:B->C). MAP FST (MAP (\(s,t). (s,P t)) l) = MAP FST l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]);;
let _ = cake_add_simps [MAP_FST_MAP];;

(* MEM in the constant-for-variable substitution of a ConstSpec *)
let CLITAUX_C_MEM_ConstVar = prove
 (`!(eqs:(mlstring#hol_term)list) s s'.
     MEM (s',s) (MAP (\(s,t). (hol_Const s (typeof t),hol_Var s (typeof t))) eqs) <=>
     ?n t. MEM (n,t) eqs /\ s' = hol_Const n (typeof t) /\ s = hol_Var n (typeof t)`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let constspec_conext_well_formed = prove
 (`!thy eqs prop.
     theory_ok' thy /\
     proves' (thy,{},MAP (\(s,t). hol_Var s (typeof t) === t) eqs) prop /\
     ALL (\t. CLOSED t /\ (!v. MEM v (tvars t) ==> MEM v (tyvars (typeof t))))
         (MAP SND eqs) /\
     ALL_DISTINCT (MAP FST eqs) /\
     (!x ty. VFREE_IN (hol_Var x ty) prop
             ==> MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
     (!s. MEM s (MAP FST eqs) ==> ~(s IN FDOM (ethy_tms thy))) /\
     (!s. MEM s (MAP FST eqs) ==> ~(s IN FDOM (ethy_etms thy))) /\
     (!s t. MEM (s,t) eqs ==> type_ok (ethy_tys thy) (typeof t))
     ==> let cprop =
           VSUBST (MAP (\(s,t). (hol_Const s (typeof t),hol_Var s (typeof t))) eqs) prop in
         let thy' =
           ethy_tms_fupd
             (K (FUNION (alist_to_fmap (MAP (\(s,t). (s,typeof t)) eqs)) (ethy_tms thy)))
             thy in
         term_ok' thy' cprop /\ cprop has_type Tyapp (implode "bool") []`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP proves'_term_ok') THEN CONJ_TAC THENL
   [MATCH_MP_TAC term_ok'_VSUBST THEN CONJ_TAC THENL
     [MATCH_MP_TAC term_ok'_tms_FUNION_fresh THEN ASM_REWRITE_TAC[MAP_FST_MAP];
      REWRITE_TAC[CLITAUX_C_MEM_ConstVar] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[injectivity "hol_term"; CSYNAUX_P4_has_type_Const] THEN
      MAP_EVERY EXISTS_TAC [`n:mlstring`; `typeof t`] THEN REWRITE_TAC[term_ok'_def] THEN
      EXISTS_TAC `typeof t` THEN
      REWRITE_TAC[ctms_def; ctys_def; ethy_INFO.ri_accfupds; K_THM; FLOOKUP_FUNION;
                  ALOOKUP_EQ_FLOOKUP] THEN
      SUBGOAL_THEN `ALOOKUP (MAP (\(s,t). (s,typeof t)) (eqs:(mlstring#hol_term)list)) n =
                    SOME (typeof t)` SUBST1_TAC THENL
       [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[MAP_FST_MAP] THEN
        REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[option_CASE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC type_ok_weakening THEN ASM_MESON_TAC[];
        EXISTS_TAC `[]:(hol_type#hol_type)list` THEN REWRITE_TAC[TYPE_SUBST_NIL]]];
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[CLITAUX_C_MEM_ConstVar] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "hol_term"; CSYNAUX_P4_has_type_Const] THEN
    MESON_TAC[]]);;

(* HOL4 variables abs, rep are abs_name, rep_name *)
let CLITAUX_C_FUNION_FUPDATE_SUBMAP = prove
 (`!(f:(A,B)fmap) g k v.
     ~(k IN FDOM f) /\ ~(k IN FDOM g) ==> FUNION f g SUBMAP FUNION (f |+ (k,v)) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUNION_FUPDATE_1] THEN
  MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN ASM_REWRITE_TAC[FDOM_FUNION; IN_UNION]);;

(* the signature after a type definition: what typedefn_eq1/eq2_well_formed need *)
let CLITAUX_C_typedefn_facts = prove
 (`!thy name pred abs_name rep_name witness.
     theory_ok' thy /\
     proves' (thy,{},[]) (hol_Comb pred witness) /\
     ~(name IN FDOM (ethy_tys thy)) /\ ~(name IN FDOM (ethy_etys thy)) /\
     ~(abs_name IN FDOM (ethy_tms thy)) /\ ~(abs_name IN FDOM (ethy_etms thy)) /\
     ~(rep_name IN FDOM (ethy_tms thy)) /\ ~(rep_name IN FDOM (ethy_etms thy)) /\
     ~(abs_name = rep_name) /\
     type_ok (ethy_tys thy) (typeof witness)
     ==> typeof pred = Tyapp (implode "fun") [typeof witness; Tyapp (implode "bool") []] /\
         welltyped pred /\
         !aty tys' tms'.
           Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) =
             aty /\
           FUNION (ethy_tys thy |+ (name,LENGTH (tvars pred))) (ethy_etys thy) = tys' /\
           FUNION (ethy_tms thy
                     |+ (abs_name,Tyapp (implode "fun") [typeof witness; aty])
                     |+ (rep_name,Tyapp (implode "fun") [aty; typeof witness]))
                  (ethy_etms thy) = tms'
           ==> is_std_sig (tys',tms') /\ type_ok tys' aty /\ type_ok tys' (typeof witness) /\
               FLOOKUP tms' abs_name = SOME (Tyapp (implode "fun") [typeof witness; aty]) /\
               FLOOKUP tms' rep_name = SOME (Tyapp (implode "fun") [aty; typeof witness]) /\
               hol_term_ok (tys',tms') pred`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `term_ok' thy pred /\ welltyped (hol_Comb pred witness) /\
                typeof (hol_Comb pred witness) = Tyapp (implode "bool") []` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP proves'_term_ok') THEN REWRITE_TAC[term_ok'_def] THEN
    MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
  SUBGOAL_THEN `typeof pred = Tyapp (implode "fun") [typeof witness; Tyapp (implode "bool") []]`
    ASSUME_TAC THENL
   [UNDISCH_TAC `welltyped (hol_Comb pred witness)` THEN REWRITE_TAC[WELLTYPED_CLAUSES] THEN
    STRIP_TAC THEN UNDISCH_TAC `typeof (hol_Comb pred witness) = Tyapp (implode "bool") []` THEN
    ASM_REWRITE_TAC[typeof_def; codomain_def] THEN SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[term_ok'_welltyped]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ctys thy SUBMAP tys' /\ ctms thy SUBMAP tms'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tys'" THEN EXPAND_TAC "tms'" THEN REWRITE_TAC[ctys_def; ctms_def] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLITAUX_C_FUNION_FUPDATE_SUBMAP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBMAP_TRANS THEN
      EXISTS_TAC `FUNION (ethy_tms thy |+
                    (abs_name,Tyapp (implode "fun") [typeof witness; aty:hol_type]))
                    (ethy_etms thy)` THEN
      CONJ_TAC THEN MATCH_MP_TAC CLITAUX_C_FUNION_FUPDATE_SUBMAP THEN
      ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_std_sig (tys',tms')` ASSUME_TAC THENL
   [MATCH_MP_TAC is_std_sig_extend THEN
    MAP_EVERY EXISTS_TAC [`ctys thy`; `ctms thy`] THEN
    ASM_SIMP_TAC[theory_ok'_is_std_sig_ext]; ALL_TAC] THEN
  SUBGOAL_THEN `type_ok tys' (typeof witness)` ASSUME_TAC THENL
   [EXPAND_TAC "tys'" THEN MATCH_MP_TAC type_ok_weakening THEN
    MATCH_MP_TAC type_ok_FUPDATE_fresh THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `type_ok tys' aty` ASSUME_TAC THENL
   [EXPAND_TAC "tys'" THEN EXPAND_TAC "aty" THEN
    REWRITE_TAC[type_ok_def; FLOOKUP_FUNION; FLOOKUP_UPDATE; option_CASE] THEN
    SIMP_TAC[LENGTH_MAP; LENGTH_STRING_SORT; ALL_DISTINCT_MAP_explode; tvars_ALL_DISTINCT;
             ALL_MAP; o_DEF; type_ok_def; ALL_T]; ALL_TAC] THEN
  SUBGOAL_THEN `~(rep_name:mlstring = abs_name)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `FLOOKUP (tms':(mlstring,hol_type)fmap) abs_name =
       SOME (Tyapp (implode "fun") [typeof witness; aty]) /\
     FLOOKUP tms' rep_name = SOME (Tyapp (implode "fun") [aty; typeof witness])`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tms'" THEN REWRITE_TAC[FLOOKUP_FUNION; FLOOKUP_UPDATE] THEN
    ASM_REWRITE_TAC[option_CASE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC hol_term_ok_extend THEN
  MAP_EVERY EXISTS_TAC [`ctys thy`; `ctms thy`] THEN ASM_SIMP_TAC[term_ok'_imp_term_ok]);;

let CLITAUX_C_typeof_eq = prove
 (`!s t. typeof (s === t) = Tyapp (implode "bool") []`,
  REWRITE_TAC[equation_def; typeof_def; codomain_def]);;

(* the common start of typedefn_eq1_well_formed and typedefn_eq2_well_formed *)
let CLITAUX_C_TYPEDEFN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`thy:ethy`; `name:mlstring`; `pred:hol_term`; `abs_name:mlstring`;
                `rep_name:mlstring`; `witness:hol_term`] CLITAUX_C_typedefn_facts) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[hol_domain_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC term_ok_imp_term_ok' THEN
    REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accfupds; K_THM] THEN
    ABBREV_TAC `aty = Tyapp name (MAP Tyvar (MAP implode
                        (STRING_SORT (MAP explode (tvars pred)))))` THEN
    ABBREV_TAC `tys' = FUNION (ethy_tys thy |+ (name,LENGTH (tvars pred))) (ethy_etys thy)` THEN
    ABBREV_TAC `tms' = FUNION (ethy_tms thy
                         |+ (abs_name,Tyapp (implode "fun") [typeof witness; aty])
                         |+ (rep_name,Tyapp (implode "fun") [aty; typeof witness]))
                         (ethy_etms thy)` THEN
    REMOVE_THEN "F" (MP_TAC o SPECL [`aty:hol_type`; `tys':(mlstring,num)fmap`;
                                     `tms':(mlstring,hol_type)fmap`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP term_ok_clauses th]) THEN
    ASM_REWRITE_TAC[hol_term_ok_def; FST; SND; WELLTYPED_CLAUSES; typeof_def;
                    codomain_def; CLITAUX_C_typeof_eq] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[FST; SND] (MATCH_MP term_ok_clauses th)]) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL; welltyped_equation; CLITAUX_C_typeof_eq;
                    WELLTYPED_CLAUSES; typeof_def; codomain_def]];;

let typedefn_eq1_well_formed = prove
 (`!thy name pred abs_name rep_name witness.
     theory_ok' thy /\
     proves' (thy,{},[]) (hol_Comb pred witness) /\
     CLOSED pred /\
     ~(name IN FDOM (ethy_tys thy)) /\ ~(name IN FDOM (ethy_etys thy)) /\
     ~(abs_name IN FDOM (ethy_tms thy)) /\ ~(abs_name IN FDOM (ethy_etms thy)) /\
     ~(rep_name IN FDOM (ethy_tms thy)) /\ ~(rep_name IN FDOM (ethy_etms thy)) /\
     ~(abs_name = rep_name) /\
     type_ok (ethy_tys thy) (typeof witness)
     ==> let abs_type =
           Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
         let rep_type = hol_domain (typeof pred) in
         let thy' =
           ethy_tys_fupd (K (ethy_tys thy |+ (name,LENGTH (tvars pred))))
             (ethy_tms_fupd
                (K (ethy_tms thy |+ (abs_name,Tyapp (implode "fun") [rep_type; abs_type])
                                 |+ (rep_name,Tyapp (implode "fun") [abs_type; rep_type])))
                thy) in
         let eq1 =
           hol_Comb (hol_Const abs_name (Tyapp (implode "fun") [rep_type; abs_type]))
                    (hol_Comb (hol_Const rep_name (Tyapp (implode "fun") [abs_type; rep_type]))
                              (hol_Var (implode "a") abs_type))
           === hol_Var (implode "a") abs_type in
         term_ok' thy' eq1 /\ eq1 has_type Tyapp (implode "bool") []`,
  CLITAUX_C_TYPEDEFN_TAC THEN MESON_TAC[TYPE_SUBST_NIL]);;

let typedefn_eq2_well_formed = prove
 (`!thy name pred abs_name rep_name witness.
     theory_ok' thy /\
     proves' (thy,{},[]) (hol_Comb pred witness) /\
     CLOSED pred /\
     ~(name IN FDOM (ethy_tys thy)) /\ ~(name IN FDOM (ethy_etys thy)) /\
     ~(abs_name IN FDOM (ethy_tms thy)) /\ ~(abs_name IN FDOM (ethy_etms thy)) /\
     ~(rep_name IN FDOM (ethy_tms thy)) /\ ~(rep_name IN FDOM (ethy_etms thy)) /\
     ~(abs_name = rep_name) /\
     type_ok (ethy_tys thy) (typeof witness)
     ==> let abs_type =
           Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
         let rep_type = hol_domain (typeof pred) in
         let thy' =
           ethy_tys_fupd (K (ethy_tys thy |+ (name,LENGTH (tvars pred))))
             (ethy_tms_fupd
                (K (ethy_tms thy |+ (abs_name,Tyapp (implode "fun") [rep_type; abs_type])
                                 |+ (rep_name,Tyapp (implode "fun") [abs_type; rep_type])))
                thy) in
         let eq2 =
           hol_Comb pred (hol_Var (implode "r") rep_type)
           === (hol_Comb (hol_Const rep_name (Tyapp (implode "fun") [abs_type; rep_type]))
                         (hol_Comb (hol_Const abs_name (Tyapp (implode "fun") [rep_type; abs_type]))
                                   (hol_Var (implode "r") rep_type))
                === hol_Var (implode "r") rep_type) in
         term_ok' thy' eq2 /\ eq2 has_type Tyapp (implode "bool") []`,
  CLITAUX_C_TYPEDEFN_TAC THEN MESON_TAC[TYPE_SUBST_NIL]);;

(* theory_ok' is kept by an extension of the six components: the new range types and axioms
   are ok, the type and constant maps only grow, and the domains stay disjoint *)
let CLITAUX_C_theory_ok'_ext = prove
 (`!tms tys axs etms etys eaxs tms' tys' axs' etms' etys' eaxs'.
     theory_ok' (ethy_REC tms tys axs etms etys eaxs) /\
     tys SUBMAP tys' /\ tms SUBMAP tms' /\
     FUNION tys etys SUBMAP FUNION tys' etys' /\
     FUNION tms etms SUBMAP FUNION tms' etms' /\
     DISJOINT (FDOM tys') (FDOM etys') /\ DISJOINT (FDOM tms') (FDOM etms') /\
     (!ty. ty IN FRANGE tms' ==> ty IN FRANGE tms \/ type_ok tys' ty) /\
     (!ty. ty IN FRANGE etms' ==> ty IN FRANGE etms \/ type_ok (FUNION tys' etys') ty) /\
     (!p. p IN axs' ==> p IN axs \/
          hol_term_ok (FUNION tys' etys',FUNION tms' etms') p /\
          p has_type Tyapp (implode "bool") []) /\
     (!p. p IN eaxs' ==> p IN eaxs \/
          hol_term_ok (FUNION tys' etys',FUNION tms' etms') p /\
          p has_type Tyapp (implode "bool") [])
     ==> theory_ok' (ethy_REC tms' tys' axs' etms' etys' eaxs')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[theory_ok'_def; ctys_def; ctms_def; sigof'_def; ethy_INFO.ri_accessors] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!p. term_ok' (ethy_REC tms tys axs etms etys eaxs) p
                    ==> term_ok' (ethy_REC tms' tys' axs' etms' etys' eaxs') p`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC term_ok'_ctms_ctys_subset THEN
    ASM_REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accessors]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. hol_term_ok (FUNION tys' etys',FUNION tms' etms') p
                    ==> term_ok' (ethy_REC tms' tys' axs' etms' etys' eaxs') p`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_ok_imp_term_ok' THEN
    ASM_REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accessors]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[type_ok_extend];
    ASM_MESON_TAC[type_ok_extend];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[is_std_sig_extend]]);;

let CLITAUX_C_IN_FRANGE_FUPDATE = prove
 (`!(f:(A,B)fmap) k v y. y IN FRANGE (f |+ (k,v)) ==> y = v \/ y IN FRANGE f`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k':A` MP_TAC) THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

let CLITAUX_C_IN_FRANGE_FUNION = prove
 (`!(f:(A,B)fmap) g y. y IN FRANGE (FUNION f g) ==> y IN FRANGE f \/ y IN FRANGE g`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_FUNION] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A` MP_TAC) THEN
  MP_TAC(ISPEC `FLOOKUP (f:(A,B)fmap) k` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[option_INJ]);;

let CLITAUX_C_IN_FRANGE_eqs = prove
 (`!(eqs:(mlstring#hol_term)list) ty.
     ty IN FRANGE (alist_to_fmap (MAP (\(s,t). (s,typeof t)) eqs))
     ==> ?s t. MEM (s,t) eqs /\ ty = typeof t`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; ALOOKUP_EQ_FLOOKUP] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* one updates' case: unfold theory_ok' of the old theory (abbreviated tms0 ... eaxs0) and
   reduce theory_ok' of the new one to CLITAUX_C_theory_ok'_ext's conditions *)
let CLITAUX_C_UPD_TAC =
  REWRITE_TAC[FUNION_FEMPTY_1; FUNION_FUPDATE_1; UNION_EMPTY] THEN
  DISCH_THEN(LABEL_TAC "prem") THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[theory_ok'_def; ctys_def; ctms_def; sigof'_def;
                                  ethy_INFO.ri_accessors] th)) THEN
  REMOVE_THEN "prem" STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC CLITAUX_C_theory_ok'_ext THEN
  MAP_EVERY EXISTS_TAC [`tms0:(mlstring,hol_type)fmap`; `tys0:(mlstring,num)fmap`;
                        `axs0:hol_term->bool`; `etms0:(mlstring,hol_type)fmap`;
                        `etys0:(mlstring,num)fmap`; `eaxs0:hol_term->bool`] THEN
  ASM_REWRITE_TAC[SUBMAP_REFL; IN_UNION; IN_SING];;

(* DISJOINT s (FDOM (f |+ (x,y))) from DISJOINT s (FDOM f) and ~(x IN s) *)
let CLITAUX_C_DISJ_R_TAC =
  REWRITE_TAC[FDOM_FUPDATE] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
  REWRITE_TAC[DISJOINT_INSERT] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];;

(* the two TypeDefn axioms, from typedefn_eq1_well_formed and typedefn_eq2_well_formed *)
let CLITAUX_C_TDEQ_TAC th =
  MP_TAC(BETA_RULE(REWRITE_RULE[LET_DEF; LET_END_DEF]
    (SPECL [`ethy_REC tms0 tys0 axs0 etms0 etys0 eaxs0`; `name:mlstring`; `pred:hol_term`;
            `abs_name:mlstring`; `rep_name:mlstring`; `witness:hol_term`] th))) THEN
  ASM_REWRITE_TAC[ethy_INFO.ri_accessors; hol_domain_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP term_ok'_imp_term_ok) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accfupds; ethy_INFO.ri_accessors; K_THM];;

let updates'_theory_ok' = prove
 (`!upd ctxt.
     upd updates' ctxt
     ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
       (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt))))
     ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' (CONS upd ctxt))))
       (alist_to_fmap (FLAT (MAP types_of_upd' (CONS upd ctxt)))) (set_of_list (FLAT (MAP
       (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) (CONS upd ctxt)))) (alist_to_fmap
       (FLAT (MAP econsts_of_upd' (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP etypes_of_upd'
       (CONS upd ctxt)))) (set_of_list (FLAT (MAP eaxexts_of_upd' (CONS upd ctxt)))))`,
  MATCH_MP_TAC updates'_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; FLAT; alist_to_fmap_APPEND; SET_OF_LIST_APPEND] THEN
  REWRITE_TAC[consts_of_upd'_def; types_of_upd'_def; econsts_of_upd'_def; etypes_of_upd'_def;
              axexts_of_upd'_def; conexts_of_upd'_def; eaxexts_of_upd'_def;
              LET_DEF; LET_END_DEF; alist_to_fmap_thm; APPEND; set_of_list] THEN
  ABBREV_TAC `tms0 = alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))` THEN
  ABBREV_TAC `tys0 = alist_to_fmap (FLAT (MAP types_of_upd' ctxt))` THEN
  ABBREV_TAC `axs0 = set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
                                            (conexts_of_upd' upd)) ctxt))` THEN
  ABBREV_TAC `etms0 = alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))` THEN
  ABBREV_TAC `etys0 = alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))` THEN
  ABBREV_TAC `eaxs0 = set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))` THEN
  CLITAUX_C_UPD_TAC THENL
   [(* NewAxiom *)
    REPEAT CONJ_TAC THEN ASM_MESON_TAC[term_ok_weakening];
    (* NewConst *)
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLITAUX_C_FUNION_FUPDATE_SUBMAP THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[FDOM_FUPDATE; DISJOINT_INSERT];
      ASM_MESON_TAC[CLITAUX_C_IN_FRANGE_FUPDATE];
      SIMP_TAC[]; SIMP_TAC[]; SIMP_TAC[]];
    (* ConstSpec *)
    SUBGOAL_THEN
      `DISJOINT (FDOM (alist_to_fmap (MAP (\(s,t). (s,typeof t))
                                         (eqs:(mlstring#hol_term)list))))
                (FDOM (tms0:(mlstring,hol_type)fmap)) /\
       DISJOINT (FDOM (alist_to_fmap (MAP (\(s,t). (s,typeof t)) eqs)))
                (FDOM (etms0:(mlstring,hol_type)fmap)) /\
       DISJOINT (FDOM (alist_to_fmap (MAP (\(s,t). (s,typeof t)) eqs)))
                (FDOM tms0 UNION FDOM etms0)`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[FDOM_alist_to_fmap; MAP_FST_MAP; IN_DISJOINT; IN_SET_OF_LIST; IN_UNION] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 SUBMAP_FUNION_ID) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM FUNION_ASSOC] THEN MATCH_MP_TAC(CONJUNCT2 SUBMAP_FUNION_ID) THEN
      ASM_REWRITE_TAC[FDOM_FUNION];
      ASM_REWRITE_TAC[FDOM_FUNION; DISJOINT_UNION];
      GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o MATCH_MP CLITAUX_C_IN_FRANGE_FUNION) THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLITAUX_C_IN_FRANGE_eqs) THEN ASM_MESON_TAC[];
      SIMP_TAC[];
      GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      MP_TAC(BETA_RULE(REWRITE_RULE[LET_DEF; LET_END_DEF]
        (SPECL [`ethy_REC tms0 tys0 axs0 etms0 etys0 eaxs0`; `eqs:(mlstring#hol_term)list`;
                `prop:hol_term`] constspec_conext_well_formed))) THEN
      ASM_REWRITE_TAC[ethy_INFO.ri_accessors] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP term_ok'_imp_term_ok) ASSUME_TAC) THEN
      ASM_REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accfupds; ethy_INFO.ri_accessors;
                      K_THM];
      SIMP_TAC[]];
    (* NewType *)
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLITAUX_C_FUNION_FUPDATE_SUBMAP THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[FDOM_FUPDATE; DISJOINT_INSERT];
      SIMP_TAC[]; SIMP_TAC[]; SIMP_TAC[]; SIMP_TAC[]];
    (* TypeDefn *)
    MP_TAC(SPECL [`ethy_REC tms0 tys0 axs0 etms0 etys0 eaxs0`; `name:mlstring`; `pred:hol_term`;
                  `abs_name:mlstring`; `rep_name:mlstring`; `witness:hol_term`]
            CLITAUX_C_typedefn_facts) THEN
    ASM_REWRITE_TAC[ethy_INFO.ri_accessors] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[hol_domain_def] THEN
    ABBREV_TAC `aty = Tyapp name (MAP Tyvar (MAP implode
                        (STRING_SORT (MAP explode (tvars pred)))))` THEN
    SUBGOAL_THEN
      `(tms0:(mlstring,hol_type)fmap) |+
         (rep_name,Tyapp (implode "fun") [aty; typeof witness]) |+
         (abs_name,Tyapp (implode "fun") [typeof witness; aty]) =
       tms0 |+ (abs_name,Tyapp (implode "fun") [typeof witness; aty]) |+
         (rep_name,Tyapp (implode "fun") [aty; typeof witness])`
      SUBST1_TAC THENL
     [MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `tys1 = (tys0:(mlstring,num)fmap) |+ (name,LENGTH (tvars pred))` THEN
    ABBREV_TAC `tms1 = (tms0:(mlstring,hol_type)fmap) |+
                         (abs_name,Tyapp (implode "fun") [typeof witness; aty]) |+
                         (rep_name,Tyapp (implode "fun") [aty; typeof witness])` THEN
    SUBGOAL_THEN `~(rep_name:mlstring = abs_name)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(tys0:(mlstring,num)fmap) SUBMAP tys1 /\ (tms0:(mlstring,hol_type)fmap) SUBMAP tms1 /\
       FUNION tys0 etys0 SUBMAP FUNION tys1 etys0 /\
       FUNION tms0 etms0 SUBMAP FUNION tms1 etms0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "tys1" THEN EXPAND_TAC "tms1" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBMAP_TRANS THEN
        EXISTS_TAC `(tms0:(mlstring,hol_type)fmap) |+
                      (abs_name,Tyapp (implode "fun") [typeof witness; aty])` THEN
        CONJ_TAC THEN MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN
        ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT];
        MATCH_MP_TAC CLITAUX_C_FUNION_FUPDATE_SUBMAP THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBMAP_TRANS THEN
        EXISTS_TAC `FUNION ((tms0:(mlstring,hol_type)fmap) |+
                      (abs_name,Tyapp (implode "fun") [typeof witness; aty])) etms0` THEN
        CONJ_TAC THEN MATCH_MP_TAC CLITAUX_C_FUNION_FUPDATE_SUBMAP THEN
        ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT]];
      ALL_TAC] THEN
    SUBGOAL_THEN `is_std_sig (tys1,tms1)` ASSUME_TAC THENL
     [MATCH_MP_TAC is_std_sig_extend THEN
      MAP_EVERY EXISTS_TAC [`tys0:(mlstring,num)fmap`; `tms0:(mlstring,hol_type)fmap`] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `type_ok tys1 aty /\ type_ok tys1 (typeof witness)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "tys1" THEN CONJ_TAC THENL
       [EXPAND_TAC "aty" THEN REWRITE_TAC[type_ok_def; FLOOKUP_UPDATE] THEN
        SIMP_TAC[LENGTH_MAP; LENGTH_STRING_SORT; ALL_DISTINCT_MAP_explode; tvars_ALL_DISTINCT;
                 ALL_MAP; o_DEF; type_ok_def; ALL_T];
        MATCH_MP_TAC type_ok_FUPDATE_fresh THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `type_ok tys1 (Tyapp (implode "fun") [typeof witness; aty]) /\
                  type_ok tys1 (Tyapp (implode "fun") [aty; typeof witness])`
      STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        REWRITE_TAC[REWRITE_RULE[FST; SND] (MATCH_MP term_ok_clauses th)]) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "tys1" THEN ASM_REWRITE_TAC[FDOM_FUPDATE; DISJOINT_INSERT];
      EXPAND_TAC "tms1" THEN ASM_REWRITE_TAC[FDOM_FUPDATE; DISJOINT_INSERT];
      EXPAND_TAC "tms1" THEN ASM_MESON_TAC[CLITAUX_C_IN_FRANGE_FUPDATE];
      SIMP_TAC[];
      GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THENL
       [CLITAUX_C_TDEQ_TAC typedefn_eq1_well_formed;
        CLITAUX_C_TDEQ_TAC typedefn_eq2_well_formed];
      SIMP_TAC[]];
    (* NewEliminableType *)
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_FUNION_mono_r THEN MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN
      ASM_REWRITE_TAC[];
      CLITAUX_C_DISJ_R_TAC;
      SIMP_TAC[]; SIMP_TAC[]; SIMP_TAC[]; SIMP_TAC[]];
    (* NewEliminableConst *)
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBMAP_FUNION_mono_r THEN MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN
      ASM_REWRITE_TAC[];
      CLITAUX_C_DISJ_R_TAC;
      SIMP_TAC[];
      ASM_MESON_TAC[CLITAUX_C_IN_FRANGE_FUPDATE];
      SIMP_TAC[]; SIMP_TAC[]];
    (* NewEliminableAxiom *)
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[]; SIMP_TAC[]; SIMP_TAC[];
      GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `term_ok' (ethy_REC tms0 tys0 axs0 etms0 etys0 eaxs0) prop` THEN
      DISCH_THEN(MP_TAC o MATCH_MP term_ok'_imp_term_ok) THEN
      REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accessors] THEN SIMP_TAC[]]]);;

let extends'_theory_ok' = prove
 (`!ctxt1 ctxt2.
     ctxt2 extends' ctxt1
     ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt1))) (alist_to_fmap
       (FLAT (MAP types_of_upd' ctxt1))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt1))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt1)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt1))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt1))))
     ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt2))) (alist_to_fmap
       (FLAT (MAP types_of_upd' ctxt2))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt2))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt2)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt2))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt2))))`,
  MATCH_MP_TAC extends'_ind THEN REWRITE_TAC[] THEN MESON_TAC[updates'_theory_ok']);;

let init_theory_ok' = prove
 (`theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' init_ectxt))) (alist_to_fmap (FLAT
   (MAP types_of_upd' init_ectxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) init_ectxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' init_ectxt)))
   (alist_to_fmap (FLAT (MAP etypes_of_upd' init_ectxt))) (set_of_list (FLAT
   (MAP eaxexts_of_upd' init_ectxt))))`,
  REWRITE_TAC[theory_ok'_def; ctys_def; ctms_def; sigof'_def; ethy_INFO.ri_accessors;
              init_ectxt_def; MAP; FLAT; APPEND; types_of_upd'_def; consts_of_upd'_def;
              etypes_of_upd'_def; econsts_of_upd'_def; axexts_of_upd'_def; conexts_of_upd'_def;
              eaxexts_of_upd'_def; alist_to_fmap_thm; set_of_list; NOT_IN_EMPTY;
              FRANGE_FUPDATE; FRANGE_FEMPTY; DRESTRICT_FEMPTY; IN_INSERT; FUNION_FEMPTY_2;
              FDOM_FEMPTY; DISJOINT_EMPTY; is_std_sig_def; FLOOKUP_UPDATE] THEN
  SIMP[injectivity "mlstring"; type_ok_def; FLOOKUP_UPDATE; ALL; LENGTH;
       ARITH_RULE `SUC(SUC 0) = 2`]);;

(* HOL4 clauses are typed one by one (a is a num and a name; n a name and a
   term): the clauses are parsed apart. *)
let lift_upd_def = cake_def_clauses
  [`lift_upd (hol_NewAxiom p) = little_NewAxiom p`;
   `lift_upd (hol_NewConst n ty) = little_NewConst n ty`;
   `lift_upd (hol_ConstSpec eqs p) = little_ConstSpec eqs p`;
   `lift_upd (hol_NewType n a) = little_NewType n a`;
   `lift_upd (hol_TypeDefn n p a r) = little_TypeDefn n p a r`];;

(* HOL4 Overload lift_ctxt = MAP lift_upd: written out *)

let drop_upd_def = cake_def_clauses
  [`drop_upd (little_NewAxiom p) = SOME (hol_NewAxiom p)`;
   `drop_upd (little_NewConst n ty) = SOME (hol_NewConst n ty)`;
   `drop_upd (little_ConstSpec eqs p) = SOME (hol_ConstSpec eqs p)`;
   `drop_upd (little_NewType n a) = SOME (hol_NewType n a)`;
   `drop_upd (little_TypeDefn n p a r) = SOME (hol_TypeDefn n p a r)`;
   `drop_upd (NewEliminableType n a) = SOME (hol_NewType n a)`;
   `drop_upd (NewEliminableConst n ty) = SOME (hol_NewConst n ty)`;
   `drop_upd (NewEliminableAxiom n) = (NONE:update option)`];;

(* HOL4 Overload drop_ctxt = mapPartial drop_upd: written out *)

let CLITAUX_FLAT_MAP_lift = prove
 (`!(f':update'->A list) (f:update->A list) ctxt.
     (!u. f' (lift_upd u) = f u) ==> FLAT (MAP f' (MAP lift_upd ctxt)) = FLAT (MAP f ctxt)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_MAP_o; o_DEF] THEN ASM_REWRITE_TAC[ETA_AX]);;

let CLITAUX_lift_upd_TAC =
  MATCH_MP_TAC CLITAUX_FLAT_MAP_lift THEN MATCH_MP_TAC update_INDUCT THEN
  REWRITE_TAC[lift_upd_def; types_of_upd'_def; types_of_upd_def; consts_of_upd'_def;
              consts_of_upd_def; etypes_of_upd'_def; econsts_of_upd'_def; eaxexts_of_upd'_def;
              axexts_of_upd'_def; axexts_of_upd_def; conexts_of_upd'_def; conexts_of_upd_def];;

let tysof'_lift_ctxt = prove
 (`!ctxt. alist_to_fmap (FLAT (MAP types_of_upd' (MAP lift_upd ctxt))) =
          alist_to_fmap (FLAT (MAP types_of_upd ctxt))`,
  GEN_TAC THEN AP_TERM_TAC THEN CLITAUX_lift_upd_TAC);;
let _ = cake_add_simps [tysof'_lift_ctxt];;

let tmsof'_lift_ctxt = prove
 (`!ctxt. alist_to_fmap (FLAT (MAP consts_of_upd' (MAP lift_upd ctxt))) =
          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))`,
  GEN_TAC THEN AP_TERM_TAC THEN CLITAUX_lift_upd_TAC);;
let _ = cake_add_simps [tmsof'_lift_ctxt];;

let CLITAUX_FLAT_MAP_lift_nil = prove
 (`!(f':update'->A list) ctxt.
     (!u. f' (lift_upd u) = []) ==> FLAT (MAP f' (MAP lift_upd ctxt)) = []`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f':update'->A list`; `\u:update. []:A list`; `ctxt:update list`]
    CLITAUX_FLAT_MAP_lift) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SPEC_TAC(`ctxt:update list`,`ctxt:update list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FLAT; APPEND]);;

let CLITAUX_lift_nil_TAC =
  MATCH_MP_TAC CLITAUX_FLAT_MAP_lift_nil THEN MATCH_MP_TAC update_INDUCT THEN
  REWRITE_TAC[lift_upd_def; etypes_of_upd'_def; econsts_of_upd'_def; eaxexts_of_upd'_def];;

let etysof_lift_ctxt = prove
 (`!ctxt. alist_to_fmap (FLAT (MAP etypes_of_upd' (MAP lift_upd ctxt))) = FEMPTY`,
  GEN_TAC THEN SUBGOAL_THEN `FLAT (MAP etypes_of_upd' (MAP lift_upd ctxt)) = []` SUBST1_TAC THENL
   [CLITAUX_lift_nil_TAC; REWRITE_TAC[alist_to_fmap_thm]]);;
let _ = cake_add_simps [etysof_lift_ctxt];;

let etmsof_lift_ctxt = prove
 (`!ctxt. alist_to_fmap (FLAT (MAP econsts_of_upd' (MAP lift_upd ctxt))) = FEMPTY`,
  GEN_TAC THEN SUBGOAL_THEN `FLAT (MAP econsts_of_upd' (MAP lift_upd ctxt)) = []` SUBST1_TAC THENL
   [CLITAUX_lift_nil_TAC; REWRITE_TAC[alist_to_fmap_thm]]);;
let _ = cake_add_simps [etmsof_lift_ctxt];;

let eaxsof_lift_ctxt = prove
 (`!ctxt. set_of_list (FLAT (MAP eaxexts_of_upd' (MAP lift_upd ctxt))) = {}`,
  GEN_TAC THEN SUBGOAL_THEN `FLAT (MAP eaxexts_of_upd' (MAP lift_upd ctxt)) = []` SUBST1_TAC THENL
   [CLITAUX_lift_nil_TAC; REWRITE_TAC[set_of_list]]);;
let _ = cake_add_simps [eaxsof_lift_ctxt];;

let axsof_lift_ctxt = prove
 (`!ctxt. set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd))
                                (MAP lift_upd ctxt))) =
          set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt))`,
  GEN_TAC THEN AP_TERM_TAC THEN CLITAUX_lift_upd_TAC);;
let _ = cake_add_simps [axsof_lift_ctxt];;

let ethyof_lift_ctxt = prove
 (`!ctxt. ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' (MAP lift_upd ctxt)))) (alist_to_fmap
   (FLAT (MAP types_of_upd' (MAP lift_upd ctxt)))) (set_of_list (FLAT (MAP (\upd. APPEND
   (axexts_of_upd' upd) (conexts_of_upd' upd)) (MAP lift_upd ctxt)))) (alist_to_fmap (FLAT
   (MAP econsts_of_upd' (MAP lift_upd ctxt)))) (alist_to_fmap (FLAT (MAP etypes_of_upd'
   (MAP lift_upd ctxt)))) (set_of_list (FLAT (MAP eaxexts_of_upd' (MAP lift_upd ctxt)))) = lift_thy
   ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),alist_to_fmap (FLAT
   (MAP consts_of_upd ctxt))),set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
   (conexts_of_upd upd)) ctxt)))`,
  REWRITE_TAC[tysof'_lift_ctxt; tmsof'_lift_ctxt; etysof_lift_ctxt; etmsof_lift_ctxt;
              eaxsof_lift_ctxt; axsof_lift_ctxt; lift_thy_def]);;
let _ = cake_add_simps [ethyof_lift_ctxt];;

let CLITAUX_tysof_drop = prove
 (`!ctxt. DISJOINT (FDOM (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))) (FDOM (alist_to_fmap
   (FLAT (MAP etypes_of_upd' ctxt))))
          ==> alist_to_fmap (FLAT (MAP types_of_upd (mapPartial drop_upd ctxt))) = FUNION
            (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (alist_to_fmap (FLAT
            (MAP etypes_of_upd' ctxt)))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[mapPartial_def; MAP; FLAT; alist_to_fmap_thm; FUNION_FEMPTY_1]; ALL_TAC] THEN
  SPEC_TAC(`h:update'`,`h:update'`) THEN MATCH_MP_TAC update'_INDUCT THEN
  REWRITE_TAC[mapPartial_def; drop_upd_def; option_CASE; MAP; FLAT; types_of_upd'_def;
              etypes_of_upd'_def; types_of_upd_def; APPEND; alist_to_fmap_thm] THEN
  REWRITE_TAC[FDOM_FUPDATE; FUNION_FUPDATE_1; FUNION_FUPDATE_2] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  ASM_REWRITE_TAC[] THEN TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]));;

let CLITAUX_tmsof_drop = prove
 (`!ctxt. DISJOINT (FDOM (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))) (FDOM (alist_to_fmap
   (FLAT (MAP econsts_of_upd' ctxt))))
          ==> alist_to_fmap (FLAT (MAP consts_of_upd (mapPartial drop_upd ctxt))) = FUNION
            (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
            (MAP econsts_of_upd' ctxt)))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[mapPartial_def; MAP; FLAT; alist_to_fmap_thm; FUNION_FEMPTY_1]; ALL_TAC] THEN
  SPEC_TAC(`h:update'`,`h:update'`) THEN MATCH_MP_TAC update'_INDUCT THEN
  REWRITE_TAC[mapPartial_def; drop_upd_def; option_CASE; MAP; FLAT; consts_of_upd'_def;
              econsts_of_upd'_def; consts_of_upd_def; APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[APPEND; alist_to_fmap_thm; alist_to_fmap_APPEND; FDOM_FUPDATE; FDOM_FUNION] THEN
  REWRITE_TAC[FUNION_FUPDATE_1; FUNION_FUPDATE_2; FUNION_ASSOC; FUNION_FEMPTY_1] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[FUNION_FUPDATE_1; FUNION_FUPDATE_2; FUNION_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]));;

let CLITAUX_axiom_list_drop = prove
 (`!ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
   (mapPartial drop_upd ctxt)) = FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) ctxt)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[mapPartial_def; MAP; FLAT]; ALL_TAC] THEN
  SPEC_TAC(`h:update'`,`h:update'`) THEN MATCH_MP_TAC update'_INDUCT THEN
  ASM_REWRITE_TAC[mapPartial_def; drop_upd_def; option_CASE; MAP; FLAT; axexts_of_upd'_def;
                  axexts_of_upd_def; conexts_of_upd'_def; conexts_of_upd_def; APPEND]);;

let tysof_drop_ctxt = prove
 (`!ctxt. theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))
          ==> alist_to_fmap (FLAT (MAP types_of_upd (mapPartial drop_upd ctxt))) = ctys (ethy_REC
            (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
            (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
            (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
            (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
            (MAP eaxexts_of_upd' ctxt))))`,
  REWRITE_TAC[theory_ok'_def; ctys_def; ethy_INFO.ri_accessors] THEN
  MESON_TAC[CLITAUX_tysof_drop]);;
let _ = cake_add_simps [tysof_drop_ctxt];;

let tmsof_drop_ctxt = prove
 (`!ctxt. theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))
          ==> alist_to_fmap (FLAT (MAP consts_of_upd (mapPartial drop_upd ctxt))) = ctms (ethy_REC
            (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
            (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
            (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
            (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
            (MAP eaxexts_of_upd' ctxt))))`,
  REWRITE_TAC[theory_ok'_def; ctms_def; ethy_INFO.ri_accessors] THEN
  MESON_TAC[CLITAUX_tmsof_drop]);;
let _ = cake_add_simps [tmsof_drop_ctxt];;

let axsof_drop_ctxt = prove
 (`!ctxt. set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
   (mapPartial drop_upd ctxt))) = set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) ctxt))`,
  REWRITE_TAC[CLITAUX_axiom_list_drop]);;
let _ = cake_add_simps [axsof_drop_ctxt];;

let thyof_drop_ctxt = prove
 (`!ctxt. theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))
          ==> ((alist_to_fmap (FLAT (MAP types_of_upd (mapPartial drop_upd ctxt))),alist_to_fmap
            (FLAT (MAP consts_of_upd (mapPartial drop_upd ctxt)))),set_of_list (FLAT (MAP
            (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
            (mapPartial drop_upd ctxt)))) = drop_thy {} (ethy_REC (alist_to_fmap (FLAT
            (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))
            (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
            (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
            (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
            (MAP eaxexts_of_upd' ctxt))))`,
  SIMP_TAC[drop_thy; tysof_drop_ctxt; tmsof_drop_ctxt; axsof_drop_ctxt;
           ethy_INFO.ri_accessors; UNION_EMPTY]);;
let _ = cake_add_simps [thyof_drop_ctxt];;

let drop_thy_lift_thy = prove
 (`!thy. drop_thy {} (lift_thy thy) = thy`,
  REWRITE_TAC[drop_thy; ctys_lift_thy; ctms_lift_thy; axsof_lift_thy; UNION_EMPTY; PAIR]);;
let _ = cake_add_simps [drop_thy_lift_thy];;

let sigof_drop_ctxt = prove
 (`!ctxt. theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap
   (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))
          ==> (alist_to_fmap (FLAT (MAP types_of_upd (mapPartial drop_upd ctxt))),alist_to_fmap
            (FLAT (MAP consts_of_upd (mapPartial drop_upd ctxt)))) =
              (ctys (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
                (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND
                (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT
                (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt)))
                (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt)))),ctms (ethy_REC (alist_to_fmap
                (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))
                (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
                (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
                (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
                (MAP eaxexts_of_upd' ctxt)))))`,
  SIMP_TAC[tysof_drop_ctxt; tmsof_drop_ctxt]);;
let _ = cake_add_simps [sigof_drop_ctxt];;

let const_list_lift_ctxt = prove
 (`!ctxt. FLAT (MAP consts_of_upd' (MAP lift_upd ctxt)) = FLAT (MAP consts_of_upd ctxt)`,
  GEN_TAC THEN CLITAUX_lift_upd_TAC);;

let econst_list_lift_ctxt = prove
 (`!ctxt. FLAT (MAP econsts_of_upd' (MAP lift_upd ctxt)) = []`,
  GEN_TAC THEN CLITAUX_lift_nil_TAC);;
let _ = cake_add_simps [econst_list_lift_ctxt];;

let type_list_lift_ctxt = prove
 (`!ctxt. FLAT (MAP types_of_upd' (MAP lift_upd ctxt)) = FLAT (MAP types_of_upd ctxt)`,
  GEN_TAC THEN CLITAUX_lift_upd_TAC);;
let _ = cake_add_simps [type_list_lift_ctxt];;

let etype_list_lift_ctxt = prove
 (`!ctxt. FLAT (MAP etypes_of_upd' (MAP lift_upd ctxt)) = []`,
  GEN_TAC THEN CLITAUX_lift_nil_TAC);;
let _ = cake_add_simps [etype_list_lift_ctxt];;

let lift_update_updates = prove
 (`!upd ctxt. upd updates ctxt <=> lift_upd upd updates' MAP lift_upd ctxt`,
  MATCH_MP_TAC update_INDUCT THEN REWRITE_TAC[lift_upd_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV) [updates_cases] THEN
  GEN_REWRITE_TAC (RAND_CONV) [updates'_cases] THEN
  REWRITE_TAC[injectivity "update"; distinctness "update"; injectivity "update'";
              distinctness "update'"; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[tysof'_lift_ctxt; tmsof'_lift_ctxt; etysof_lift_ctxt; etmsof_lift_ctxt;
              ethyof_lift_ctxt; FDOM_FEMPTY; NOT_IN_EMPTY] THENL
   [EQ_TAC THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`eqs:(mlstring#hol_term)list`;
     `prop:hol_term`] THEN
      ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL [MATCH_MP_TAC proves_imp_proves' THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP theory_ok_sig o MATCH_MP little_proves_theory_ok) THEN
        REWRITE_TAC[ALL; GSYM ALL_MEM; FST; SND] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `hol_Var s (typeof t) === t`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(s:mlstring,t:hol_term)` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN ASM_SIMP_TAC[term_ok_equation] THEN
        REWRITE_TAC[hol_term_ok_def; FST] THEN MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o MATCH_MP proves'_imp_proves) THEN
        REWRITE_TAC[drop_thy_lift_thy]];
    EQ_TAC THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`abs_name:mlstring`; `name:mlstring`; `pred:hol_term`;
                            `rep_name:mlstring`; `witness:hol_term`] THEN
      ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL [MATCH_MP_TAC proves_imp_proves' THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP theory_ok_sig o MATCH_MP little_proves_theory_ok) THEN
        REWRITE_TAC[ALL; FST; SND; hol_term_ok_def] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                         alist_to_fmap (FLAT (MAP consts_of_upd ctxt))):sig`; `witness:hol_term`]
          term_ok_type_ok) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN ASM_REWRITE_TAC[FST];
        FIRST_X_ASSUM(MP_TAC o MATCH_MP proves'_imp_proves) THEN
        REWRITE_TAC[drop_thy_lift_thy]]]);;

let lift_ctxt_extends_init_ectxt = prove
 (`!ctxt. ctxt extends init_ctxt ==> MAP lift_upd ctxt extends' init_ectxt`,
  SUBGOAL_THEN `MAP lift_upd init_ctxt = init_ectxt` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[init_ctxt_def; init_ectxt_def; MAP; lift_upd_def]; ALL_TAC] THEN
  REWRITE_TAC[extends_def; extends'_def] THEN
  SUBGOAL_THEN
   `!c2 c1. RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ upd updates ctxt1) c2 c1
            ==> RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ upd updates' ctxt1)
                    (MAP lift_upd c2) (MAP lift_upd c1)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[RTC_REFL] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[] THEN
    EXISTS_TAC `lift_upd upd` THEN ASM_REWRITE_TAC[MAP; GSYM lift_update_updates];
    MESON_TAC[RTC_TRANS]]);;

let MEM_const_list_drop_ctxt = prove
 (`!x ctxt.
     MEM x (MAP FST (FLAT (MAP consts_of_upd (mapPartial drop_upd ctxt)))) <=>
     MEM x (MAP FST (FLAT (MAP consts_of_upd' ctxt))) \/ MEM x (MAP FST (FLAT
       (MAP econsts_of_upd' ctxt)))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [REWRITE_TAC[mapPartial_def; MAP; FLAT; MEM]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:update'`,`h:update'`) THEN MATCH_MP_TAC update'_INDUCT THEN
  REWRITE_TAC[mapPartial_def; drop_upd_def; option_CASE; MAP; FLAT; consts_of_upd'_def;
              consts_of_upd_def; econsts_of_upd'_def; APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP_APPEND; MEM_APPEND; MAP; MEM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let MEM_type_list_drop_ctxt = prove
 (`!x ctxt.
     MEM x (MAP FST (FLAT (MAP types_of_upd (mapPartial drop_upd ctxt)))) <=>
     MEM x (MAP FST (FLAT (MAP types_of_upd' ctxt))) \/ MEM x (MAP FST (FLAT
       (MAP etypes_of_upd' ctxt)))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [REWRITE_TAC[mapPartial_def; MAP; FLAT; MEM]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:update'`,`h:update'`) THEN MATCH_MP_TAC update'_INDUCT THEN
  REWRITE_TAC[mapPartial_def; drop_upd_def; option_CASE; MAP; FLAT; types_of_upd'_def;
              types_of_upd_def; etypes_of_upd'_def; APPEND] THEN
  REWRITE_TAC[MAP_APPEND; MEM_APPEND; MAP; MEM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let CLITAUX_UNWIND_TAC =
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNWIND_THM2];;

let CLITAUX_DROP_PROVES_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP proves'_imp_proves o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "proves'" with Failure _ -> false)) THEN
  REWRITE_TAC[drop_thy; ctys_def; ctms_def; ethy_INFO.ri_accessors; UNION_EMPTY];;

let drop_upd_updates = prove
 (`!upd ctxt x.
     upd updates' ctxt /\
     theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
       (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt)))) /\
     drop_upd upd = SOME x
     ==> x updates (mapPartial drop_upd ctxt)`,
  MATCH_MP_TAC update'_INDUCT THEN REWRITE_TAC[drop_upd_def; option_INJ; option_DISTINCT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[updates'_cases] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "updates'" with Failure _ -> false)) THEN
  REWRITE_TAC[injectivity "update'"; distinctness "update'"] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[updates_cases] THEN
  REWRITE_TAC[injectivity "update"; distinctness "update"] THEN
  ASM_SIMP_TAC[tysof_drop_ctxt; tmsof_drop_ctxt; axsof_drop_ctxt] THEN
  REWRITE_TAC[ctys_def; ctms_def; ethy_INFO.ri_accessors; FDOM_FUNION; IN_UNION; DE_MORGAN_THM]
    THENL
   [CLITAUX_UNWIND_TAC THEN ASM_SIMP_TAC[] THEN CLITAUX_DROP_PROVES_TAC;
    MAP_EVERY EXISTS_TAC [`abs_name:mlstring`; `name:mlstring`; `pred:hol_term`;
                            `rep_name:mlstring`; `witness:hol_term`] THEN
      ASM_REWRITE_TAC[] THEN CLITAUX_DROP_PROVES_TAC;
    MAP_EVERY EXISTS_TAC [`arity:num`; `name:mlstring`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`arity:num`; `name:mlstring`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`name:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC type_ok_weakening THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`name:mlstring`; `ty:hol_type`] THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `prop:hol_term` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC term_ok_weakening THEN
      ASM_REWRITE_TAC[]]);;

let drop_thy_extends_init_ctxt = prove
 (`!ctxt'. ctxt' extends' init_ectxt ==> mapPartial drop_upd ctxt' extends init_ctxt`,
  SUBGOAL_THEN `mapPartial drop_upd init_ectxt = init_ctxt` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[init_ctxt_def; init_ectxt_def; mapPartial_def; drop_upd_def; option_CASE];
    ALL_TAC] THEN
  REWRITE_TAC[extends_def; extends'_def] THEN
  SUBGOAL_THEN
   `!c2 c1. RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ upd updates' ctxt1) c2 c1
            ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' c1))) (alist_to_fmap
              (FLAT (MAP types_of_upd' c1))) (set_of_list (FLAT (MAP (\upd. APPEND
              (axexts_of_upd' upd) (conexts_of_upd' upd)) c1))) (alist_to_fmap (FLAT
              (MAP econsts_of_upd' c1))) (alist_to_fmap (FLAT (MAP etypes_of_upd' c1)))
              (set_of_list (FLAT (MAP eaxexts_of_upd' c1))))
            ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' c2))) (alist_to_fmap
              (FLAT (MAP types_of_upd' c2))) (set_of_list (FLAT (MAP (\upd. APPEND
              (axexts_of_upd' upd) (conexts_of_upd' upd)) c2))) (alist_to_fmap (FLAT
              (MAP econsts_of_upd' c2))) (alist_to_fmap (FLAT (MAP etypes_of_upd' c2)))
              (set_of_list (FLAT (MAP eaxexts_of_upd' c2)))) /\
                RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ upd updates ctxt1)
                    (mapPartial drop_upd c2) (mapPartial drop_upd c1)`
    (fun th -> MESON_TAC[th; init_theory_ok']) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[RTC_REFL] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `upd:update'` STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates'_theory_ok') THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[mapPartial_def] THEN NAMED_CASES_ON "drop_upd upd" [""; "y"] THEN
    REWRITE_TAC[option_CASE; RTC_REFL] THEN MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[] THEN
    EXISTS_TAC `y:update` THEN REWRITE_TAC[] THEN MATCH_MP_TAC drop_upd_updates THEN
    EXISTS_TAC `upd:update'` THEN ASM_REWRITE_TAC[];
    MESON_TAC[RTC_TRANS]]);;

let lift_ctxt_extends_extends' = prove
 (`!ctxt h c.
     ctxt extends init_ctxt
     ==> ((((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),alist_to_fmap (FLAT
       (MAP consts_of_upd ctxt))),set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
       (conexts_of_upd upd)) ctxt))),h) |- c <=>
          proves' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' (MAP lift_upd ctxt))))
            (alist_to_fmap (FLAT (MAP types_of_upd' (MAP lift_upd ctxt)))) (set_of_list (FLAT (MAP
            (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) (MAP lift_upd ctxt))))
            (alist_to_fmap (FLAT (MAP econsts_of_upd' (MAP lift_upd ctxt)))) (alist_to_fmap (FLAT
            (MAP etypes_of_upd' (MAP lift_upd ctxt)))) (set_of_list (FLAT (MAP eaxexts_of_upd'
            (MAP lift_upd ctxt)))),{},h) c)`,
  REWRITE_TAC[ethyof_lift_ctxt] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC proves_imp_proves' THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP proves'_imp_proves) THEN REWRITE_TAC[drop_thy_lift_thy]]);;

let drop_ctxt_extends_extends' = prove
 (`!ctxt h c.
     ctxt extends' init_ectxt
     ==> (proves' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
       (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt))),{},h) c <=>
          (((alist_to_fmap (FLAT (MAP types_of_upd (mapPartial drop_upd ctxt))),alist_to_fmap (FLAT
            (MAP consts_of_upd (mapPartial drop_upd ctxt)))),set_of_list (FLAT (MAP (\upd. APPEND
            (axexts_of_upd upd) (conexts_of_upd upd)) (mapPartial drop_upd ctxt)))),h) |- c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))
    (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND
    (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT
    (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list
    (FLAT (MAP eaxexts_of_upd' ctxt))))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] extends'_theory_ok') THEN
    EXISTS_TAC `init_ectxt` THEN ASM_REWRITE_TAC[init_theory_ok'];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[thyof_drop_ctxt] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP proves'_imp_proves) THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP proves_imp_proves'_subset_axs) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[tysof_drop_ctxt; tmsof_drop_ctxt; FST; SND] THEN
    REWRITE_TAC[axsof_drop_ctxt; ethy_INFO.ri_accessors; SUBSET_REFL]]);;

let init_axioms_ok = prove
 (`axioms_ok (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' init_ectxt))) (alist_to_fmap (FLAT
   (MAP types_of_upd' init_ectxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) init_ectxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' init_ectxt)))
   (alist_to_fmap (FLAT (MAP etypes_of_upd' init_ectxt))) (set_of_list (FLAT
   (MAP eaxexts_of_upd' init_ectxt)))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) init_ectxt))) /\
   axioms_ok (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' init_ectxt))) (alist_to_fmap (FLAT
     (MAP types_of_upd' init_ectxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
     (conexts_of_upd' upd)) init_ectxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' init_ectxt)))
     (alist_to_fmap (FLAT (MAP etypes_of_upd' init_ectxt))) (set_of_list (FLAT
     (MAP eaxexts_of_upd' init_ectxt)))) (set_of_list (FLAT (MAP eaxexts_of_upd' init_ectxt)))`,
  REWRITE_TAC[axioms_ok_def; init_ectxt_def; MAP; FLAT; APPEND; axexts_of_upd'_def;
              conexts_of_upd'_def; eaxexts_of_upd'_def; set_of_list; NOT_IN_EMPTY]);;

let type_ok_basic_types = prove
 (`!thy sigma ty.
     type_ok (ethy_tys thy) ty /\ esubsts_ok' thy sigma /\ theory_ok' thy
     ==> ty_esubst sigma ty = ty`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ty_esubst_type_ok_id THEN
  EXISTS_TAC `ethy_tys thy` THEN ASM_REWRITE_TAC[] THEN
  PAIR_CASES_ON `sigma:(mlstring,mlstring list#hol_type)fmap#(mlstring,hol_term#hol_type)fmap` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[esubsts_ok'_def; theory_ok'_def]) THEN
  REWRITE_TAC[FST] THEN ASM SET_TAC[]);;

let term_ok_no_var_collapse = prove
 (`!thy sigma p.
     hol_term_ok (ethy_tys thy,ethy_tms thy) p /\
     theory_ok' thy /\
     esubsts_ok' thy sigma
     ==> no_var_collapse sigma p`,
  REWRITE_TAC[no_var_collapse] THEN REPEAT STRIP_TAC THEN
  QBY "!ty. VFREE_IN (hol_Var x ty) p ==> ty_esubst sigma ty = ty"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC type_ok_basic_types THEN EXISTS_TAC `thy:ethy` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(ethy_tys thy,ethy_tms thy):sig`; `p:hol_term`; `hol_Var x ty`]
      term_ok_VFREE_IN) THEN
    ASM_REWRITE_TAC[hol_term_ok_def; FST]) THEN
  ASM_MESON_TAC[]);;

let no_dup_vars_def = cake_def
  `no_dup_vars p <=>
     !x ty1 ty2. VFREE_IN (hol_Var x ty1) p /\ VFREE_IN (hol_Var x ty2) p ==> ty1 = ty2`;;

let no_dup_vars_no_var_collapse = prove
 (`!p sigma. no_dup_vars p ==> no_var_collapse sigma p`,
  REWRITE_TAC[no_dup_vars_def; no_var_collapse] THEN MESON_TAC[]);;

let REV_ASSOCD_VSUBST_const_no_free_vars = prove
 (`!l y ty u uty.
     MEM (y,ty) (MAP (\(s,t). (s,typeof t)) l)
     ==> ~VFREE_IN (hol_Var u uty)
           (REV_ASSOCD (hol_Var y ty)
              (MAP (\(s,t). (hol_Const s (typeof t),hol_Var s (typeof t))) l)
              (hol_Var y ty))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  SPEC_TAC(`h:mlstring#hol_term`,`h:mlstring#hol_term`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REV_ASSOCD_def; PAIR_EQ; injectivity "hol_term"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VFREE_IN_def; distinctness "hol_term"] THEN
  ASM_MESON_TAC[]);;

(* The signature only grows along updates' (the old maps are submaps of the new ones). *)
let CLITAUX_updates'_SUBMAP = prove
 (`!upd ctxt.
     upd updates' ctxt
     ==> alist_to_fmap (FLAT (MAP types_of_upd' ctxt)) SUBMAP
         alist_to_fmap (APPEND (types_of_upd' upd) (FLAT (MAP types_of_upd' ctxt))) /\
         alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)) SUBMAP
         alist_to_fmap (APPEND (consts_of_upd' upd) (FLAT (MAP consts_of_upd' ctxt)))`,
  REWRITE_TAC[alist_to_fmap_APPEND] THEN MATCH_MP_TAC updates'_ind THEN
  REWRITE_TAC[FDOM_alist_to_fmap; IN_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT2 SUBMAP_FUNION_ID) THEN
  REWRITE_TAC[FDOM_alist_to_fmap; IN_DISJOINT; IN_SET_OF_LIST; types_of_upd'_def;
              consts_of_upd'_def; LET_DEF; LET_END_DEF; MAP; MAP_FST_MAP; MEM; FST] THEN
  ASM_MESON_TAC[]);;

(* The axioms added by one updates' step: new axioms are well-formed in the old signature,
   conservative extensions and eliminable axioms have no clashing free variables. *)
let CLITAUX_updates'_added_axs = prove
 (`!upd ctxt.
     upd updates' ctxt
     ==> ALL (hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)),
                          alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))))
             (axexts_of_upd' upd) /\
         ALL no_dup_vars (conexts_of_upd' upd) /\
         ALL no_dup_vars (eaxexts_of_upd' upd)`,
  MATCH_MP_TAC updates'_ind THEN
  REWRITE_TAC[axexts_of_upd'_def; conexts_of_upd'_def; eaxexts_of_upd'_def; LET_DEF;
              LET_END_DEF; ALL] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `welltyped prop` ASSUME_TAC THENL
     [ASM_MESON_TAC[proves'_term_ok'; term_ok'_welltyped]; ALL_TAC] THEN
    SIMP_TAC[no_dup_vars_def; VFREE_IN_VSUBST; ASSUME `welltyped prop`] THEN
    ASM_MESON_TAC[REV_ASSOCD_VSUBST_const_no_free_vars];
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN
    REWRITE_TAC[no_dup_vars_def; equation_def; VFREE_IN_def; distinctness "hol_term";
                injectivity "hol_term"] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[no_dup_vars_def] THEN FIRST_ASSUM ACCEPT_TAC]);;

let updates'_axioms_wf = prove
 (`!upd ctxt.
     upd updates' ctxt
     ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
       (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt)))) /\
         (!p. p IN ethy_axs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))
           (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND
           (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT
           (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt)))
           (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))
              ==> no_dup_vars p \/
                  hol_term_ok (ethy_tys (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))
                    (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP
                    (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt)))
                    (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT
                    (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
                    (MAP eaxexts_of_upd' ctxt)))),ethy_tms (ethy_REC (alist_to_fmap (FLAT
                    (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))
                    (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
                    (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT
                    (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt)))
                    (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))) p) /\
         (!p. p IN ethy_eaxs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))
           (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND
           (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT
           (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt)))
           (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt)))) ==> no_dup_vars p)
         ==> (!p. p IN ethy_axs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd'
           (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP types_of_upd' (CONS upd ctxt))))
           (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd))
           (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP econsts_of_upd' (CONS upd ctxt))))
           (alist_to_fmap (FLAT (MAP etypes_of_upd' (CONS upd ctxt)))) (set_of_list (FLAT
           (MAP eaxexts_of_upd' (CONS upd ctxt)))))
                  ==> no_dup_vars p \/
                      hol_term_ok (ethy_tys (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd'
                        (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP types_of_upd'
                        (CONS upd ctxt)))) (set_of_list (FLAT (MAP (\upd. APPEND
                        (axexts_of_upd' upd) (conexts_of_upd' upd)) (CONS upd ctxt))))
                        (alist_to_fmap (FLAT (MAP econsts_of_upd' (CONS upd ctxt)))) (alist_to_fmap
                        (FLAT (MAP etypes_of_upd' (CONS upd ctxt)))) (set_of_list (FLAT
                        (MAP eaxexts_of_upd' (CONS upd ctxt))))),
                                   ethy_tms (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd'
                                     (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP types_of_upd'
                                     (CONS upd ctxt)))) (set_of_list (FLAT (MAP (\upd. APPEND
                                     (axexts_of_upd' upd) (conexts_of_upd' upd)) (CONS upd ctxt))))
                                     (alist_to_fmap (FLAT (MAP econsts_of_upd' (CONS upd ctxt))))
                                     (alist_to_fmap (FLAT (MAP etypes_of_upd' (CONS upd ctxt))))
                                     (set_of_list (FLAT (MAP eaxexts_of_upd'
                                     (CONS upd ctxt)))))) p) /\
             (!p. p IN ethy_eaxs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd'
               (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP types_of_upd' (CONS upd ctxt))))
               (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd))
               (CONS upd ctxt)))) (alist_to_fmap (FLAT (MAP econsts_of_upd' (CONS upd ctxt))))
               (alist_to_fmap (FLAT (MAP etypes_of_upd' (CONS upd ctxt)))) (set_of_list (FLAT
               (MAP eaxexts_of_upd' (CONS upd ctxt))))) ==> no_dup_vars p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLITAUX_updates'_SUBMAP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLITAUX_updates'_added_axs) THEN
  REWRITE_TAC[GSYM ALL_MEM; ethy_INFO.ri_accessors; MAP; FLAT; IN_SET_OF_LIST; MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[hol_term_ok_extend]);;

let extends'_axioms_wf = prove
 (`!ctxt1 ctxt2.
     ctxt2 extends' ctxt1
     ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt1))) (alist_to_fmap
       (FLAT (MAP types_of_upd' ctxt1))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt1))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt1)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt1))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt1)))) /\
         (!p. p IN ethy_axs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt1)))
           (alist_to_fmap (FLAT (MAP types_of_upd' ctxt1))) (set_of_list (FLAT (MAP (\upd. APPEND
           (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt1))) (alist_to_fmap (FLAT
           (MAP econsts_of_upd' ctxt1))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt1)))
           (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt1))))
              ==> no_dup_vars p \/
                  hol_term_ok (ethy_tys (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt1)))
                    (alist_to_fmap (FLAT (MAP types_of_upd' ctxt1))) (set_of_list (FLAT (MAP
                    (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt1)))
                    (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt1))) (alist_to_fmap (FLAT
                    (MAP etypes_of_upd' ctxt1))) (set_of_list (FLAT
                    (MAP eaxexts_of_upd' ctxt1)))),ethy_tms (ethy_REC (alist_to_fmap (FLAT
                    (MAP consts_of_upd' ctxt1))) (alist_to_fmap (FLAT (MAP types_of_upd' ctxt1)))
                    (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
                    (conexts_of_upd' upd)) ctxt1))) (alist_to_fmap (FLAT
                    (MAP econsts_of_upd' ctxt1))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt1)))
                    (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt1))))) p) /\
         (!p. p IN ethy_eaxs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt1)))
           (alist_to_fmap (FLAT (MAP types_of_upd' ctxt1))) (set_of_list (FLAT (MAP (\upd. APPEND
           (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt1))) (alist_to_fmap (FLAT
           (MAP econsts_of_upd' ctxt1))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt1)))
           (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt1)))) ==> no_dup_vars p)
         ==> theory_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt2))) (alist_to_fmap
           (FLAT (MAP types_of_upd' ctxt2))) (set_of_list (FLAT (MAP (\upd. APPEND
           (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt2))) (alist_to_fmap (FLAT
           (MAP econsts_of_upd' ctxt2))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt2)))
           (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt2)))) /\
             (!p. p IN ethy_axs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt2)))
               (alist_to_fmap (FLAT (MAP types_of_upd' ctxt2))) (set_of_list (FLAT (MAP
               (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt2))) (alist_to_fmap
               (FLAT (MAP econsts_of_upd' ctxt2))) (alist_to_fmap (FLAT
               (MAP etypes_of_upd' ctxt2))) (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt2))))
                  ==> no_dup_vars p \/
                      hol_term_ok (ethy_tys (ethy_REC (alist_to_fmap (FLAT
                        (MAP consts_of_upd' ctxt2))) (alist_to_fmap (FLAT
                        (MAP types_of_upd' ctxt2))) (set_of_list (FLAT (MAP (\upd. APPEND
                        (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt2))) (alist_to_fmap (FLAT
                        (MAP econsts_of_upd' ctxt2))) (alist_to_fmap (FLAT
                        (MAP etypes_of_upd' ctxt2))) (set_of_list (FLAT
                        (MAP eaxexts_of_upd' ctxt2)))),ethy_tms (ethy_REC (alist_to_fmap (FLAT
                        (MAP consts_of_upd' ctxt2))) (alist_to_fmap (FLAT
                        (MAP types_of_upd' ctxt2))) (set_of_list (FLAT (MAP (\upd. APPEND
                        (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt2))) (alist_to_fmap (FLAT
                        (MAP econsts_of_upd' ctxt2))) (alist_to_fmap (FLAT
                        (MAP etypes_of_upd' ctxt2))) (set_of_list (FLAT
                        (MAP eaxexts_of_upd' ctxt2))))) p) /\
             (!p. p IN ethy_eaxs (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt2)))
               (alist_to_fmap (FLAT (MAP types_of_upd' ctxt2))) (set_of_list (FLAT (MAP
               (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt2))) (alist_to_fmap
               (FLAT (MAP econsts_of_upd' ctxt2))) (alist_to_fmap (FLAT
               (MAP etypes_of_upd' ctxt2))) (set_of_list (FLAT
               (MAP eaxexts_of_upd' ctxt2)))) ==> no_dup_vars p)`,
  MATCH_MP_TAC extends'_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[updates'_theory_ok'];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] updates'_axioms_wf) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let eaxsof_init_ectxt = prove
 (`set_of_list (FLAT (MAP eaxexts_of_upd' init_ectxt)) = {}`,
  REWRITE_TAC[init_ectxt_def; MAP; FLAT; eaxexts_of_upd'_def; APPEND; set_of_list]);;
let _ = cake_add_simps [eaxsof_init_ectxt];;

let axsof_init_ectxt = prove
 (`set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
   (conexts_of_upd' upd)) init_ectxt)) = {}`,
  REWRITE_TAC[init_ectxt_def; MAP; FLAT; axexts_of_upd'_def; conexts_of_upd'_def; APPEND;
              set_of_list]);;
let _ = cake_add_simps [axsof_init_ectxt];;

let axioms_ok_nil = prove
 (`!thy. axioms_ok thy {}`,
  REWRITE_TAC[axioms_ok_def; NOT_IN_EMPTY]);;
let _ = cake_add_simps [axioms_ok_nil];;

let extends'_init_axioms_ok = prove
 (`!ctxt.
     ctxt extends' init_ectxt
     ==> axioms_ok (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
       (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
       (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
       (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
       (MAP eaxexts_of_upd' ctxt)))) (ethy_axs (ethy_REC (alist_to_fmap (FLAT
       (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (set_of_list
       (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt))) (alist_to_fmap
       (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt)))
       (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt))))) /\
         axioms_ok (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
           (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
           (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
           (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
           (MAP eaxexts_of_upd' ctxt)))) (ethy_eaxs (ethy_REC (alist_to_fmap (FLAT
           (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (set_of_list
           (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd) (conexts_of_upd' upd)) ctxt)))
           (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt))) (alist_to_fmap (FLAT
           (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT (MAP eaxexts_of_upd' ctxt)))))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`init_ectxt`; `ctxt:update' list`] extends'_axioms_wf) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[init_theory_ok'] THEN
    REWRITE_TAC[ethy_INFO.ri_accessors; axsof_init_ectxt; eaxsof_init_ectxt; NOT_IN_EMPTY];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[axioms_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[no_dup_vars_no_var_collapse; term_ok_no_var_collapse]);;
