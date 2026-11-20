(* ========================================================================= *)
(* inferSound: port of HOL4                                                  *)
(* compiler/inference/proofs/inferSoundScript.sml (CakeML v3479).            *)
(* Soundness of the type inferencer: any type assignment produced by the     *)
(* type inferencer is a valid type for the program.                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/typeSysProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/infer_eSound.ml";;
needs "compiler/inference/proofs/infer_eComplete.ml";;
needs "compiler/inference/proofs/type_eDeterm.ml";;

type_invention_error := true;;

let letrec_lemma2 = prove
 (CASE_TERM `!(funs_ts:infer_t list) (l:(A#B#C)list) (l':num list) s s'.
     (!t1 t2. t_walkstar s t1 = t_walkstar s t2 ==> t_walkstar s' t1 = t_walkstar s' t2) /\
     LENGTH funs_ts = LENGTH l /\ LENGTH funs_ts = LENGTH l' /\
     MAP (\n. t_walkstar s (Infer_Tuvar n)) l' = MAP (t_walkstar s) funs_ts
     ==> MAP2 (\fxe t. match fxe with (f,x,e) -> (f,t)) l
           (MAP (\n. convert_t (t_walkstar s' (Infer_Tuvar n))) l') =
         MAP2 (\xyz t. match xyz with (x,y,z) -> (x,convert_t (t_walkstar s' t))) l funs_ts`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP; MAP2; CONS_11] THEN
  REPEAT STRIP_TAC THENL
   [SPEC_TAC(`h':A#B#C`,`h':A#B#C`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      (try is_eq(snd(dest_imp(snd(strip_forall(concl th))))) with Failure _ -> false) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    INFER1AUX_IEC_ACCEPT_TAC]);;

let inferSound_sub_completion_empty = type_eDeterm_sub_completion_empty;;

let generalise_none = prove
 (`(!t s' t' x.
      check_t 0 x t /\ generalise 0 0 FEMPTY t = (0,s',t')
      ==> s' = FEMPTY /\ check_t 0 {} t) /\
   (!ts s' ts' x.
      ALL (check_t 0 x) ts /\ generalise_list 0 0 FEMPTY ts = (0,s',ts')
      ==> s' = FEMPTY /\ ALL (check_t 0 {}) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; LT; ALL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[generalise_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `generalise_list 0 0 FEMPTY a0` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `r1:(num,num)fmap#infer_t list`
      MP_TAC)) THEN
    MP_TAC(ISPEC `r1:(num,num)fmap#infer_t list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN `ts1:infer_t list`
      SUBST1_TAC)) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(num,num)fmap`; `ts1:infer_t list`; `x:num->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[generalise_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LE_0; PAIR_EQ; ARITH_EQ];
    REWRITE_TAC[generalise_def; PAIR_EQ] THEN MESON_TAC[];
    REWRITE_TAC[generalise_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `generalise 0 0 FEMPTY a0` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `r1:(num,num)fmap#infer_t`
      MP_TAC)) THEN
    MP_TAC(ISPEC `r1:(num,num)fmap#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN `t1:infer_t`
      SUBST1_TAC)) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `generalise_list 0 (n1 + 0) s1 a1` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `r2:(num,num)fmap#infer_t list`
      MP_TAC)) THEN
    MP_TAC(ISPEC `r2:(num,num)fmap#infer_t list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:(num,num)fmap` (X_CHOOSE_THEN `ts2:infer_t list`
      SUBST1_TAC)) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ; ADD_EQ_0] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(num,num)fmap`; `t1:infer_t`; `x:num->bool`] o
      check (fun th -> is_forall(concl th) &&
        (try free_in `a0:infer_t` (concl th) with Failure _ -> false))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s2:(num,num)fmap`; `ts2:infer_t list`; `x:num->bool`] o
      check (fun th -> is_forall(concl th) &&
        (try free_in `a1:infer_t list` (concl th) with Failure _ -> false))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try INFER1AUX_ec_is_app "generalise_list" (lhs(concl th)) with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

let lookup_var_empty = prove
 (`!x tvs tenv. lookup_var x (bind_tvar tvs Empty) tenv = lookup_var x Empty tenv`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN
  MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bind_tvar_rewrites; tveLookup_def]);;

let inferSound_env_rel_complete_bind = prove
 (`!ienv tenv tvs.
     env_rel_complete FEMPTY ienv tenv Empty
     ==> env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty)`,
  MESON_TAC[INFER1AUX_erc_bind_tvar; t_wfs_FEMPTY]);;

(* the set of ids n1 .... n2-1 *)
let set_ids_def = cake_def
  `set_ids n1 (n2:num) = {m | n1 <= m /\ m < n2}`;;

let set_ids_eq = prove
 (`!n1 n2. set_ids n1 n2 = set_of_list (list_of_seq (\x. x + n1) (n2 - n1))`,
  REWRITE_TAC[set_ids_def; EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST; MEM_GENLIST] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `x - n1:num` THEN ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_ARITH_TAC]);;

let set_ids_same = prove
 (`!x. set_ids x x = {}`,
  REWRITE_TAC[set_ids_def; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC);;

let _ = cake_add_simps [set_ids_same];;

let set_ids_eq_union = prove
 (`!x y z. x <= y /\ y <= z ==> set_ids x z = set_ids x y UNION set_ids y z`,
  REWRITE_TAC[set_ids_def; EXTENSION; IN_ELIM_THM; IN_UNION] THEN ARITH_TAC);;

let set_ids_eq_union_eq = prove
 (`!x y z s. x <= y /\ y <= z /\ s = set_ids y z ==> set_ids x z = set_ids x y UNION s`,
  MESON_TAC[set_ids_eq_union]);;

(* ---------- infer_d_sound ---------- *)
let INFER1AUX_set_ids_disjoint = prove
 (`!a b c. DISJOINT (set_ids a b) (set_ids b c)`,
  REWRITE_TAC[set_ids_def; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ARITH_TAC);;

let INFER1AUX_IDS_DENV_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[infer_d_def; failwith_def; PAIR_EQ; distinctness "exc"];;

let INFER1AUX_IDS_NIL_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_d_def; inferProps_st_ex_return_success] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  REWRITE_TAC[set_ids_same; ienv_to_tenv_def; inf_env_INFO.ri_accessors; nsMap_nsEmpty] THEN
  MESON_TAC[type_d_rules];;

let INFER1AUX_IDS_DMOD_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_d_def; inferProps_st_ex_bind_success; inferProps_st_ex_return_success] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ienv_to_tenv_lift] THEN
  MATCH_MP_TAC(el 6 (CONJUNCTS type_d_rules)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `ienv:inf_env` THEN ASM_REWRITE_TAC[];;

let INFER1AUX_IDS_CONS_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihd") (LABEL_TAC "ihds")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_d_def; inferProps_st_ex_bind_success; inferProps_st_ex_return_success] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ienv2:inf_env` (X_CHOOSE_THEN `sti:infer_st`
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `ienv3:inf_env` (X_CHOOSE_THEN `st3:infer_st` STRIP_ASSUME_TAC)))))
    STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN REWRITE_TAC[ienv_to_tenv_extend] THEN
  MP_TAC(SPECL [`a0:dec`; `ienv:inf_env`; `st1:infer_st`; `ienv2:inf_env`; `sti:infer_st`]
    (CONJUNCT1 infer_d_next_id_mono)) THEN
  MP_TAC(SPECL [`a1:dec list`; `extend_dec_ienv ienv2 ienv`; `sti:infer_st`; `ienv3:inf_env`;
                `st2:infer_st`] (CONJUNCT2 infer_d_next_id_mono)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `set_ids (infer_st_next_id st1) (infer_st_next_id st2) =
                set_ids (infer_st_next_id st1) (infer_st_next_id sti) UNION
                set_ids (infer_st_next_id sti) (infer_st_next_id st2)` SUBST1_TAC THENL
   [MATCH_MP_TAC set_ids_eq_union THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(el 9 (CONJUNCTS type_d_rules)) THEN
  REWRITE_TAC[INFER1AUX_set_ids_disjoint] THEN CONJ_TAC THENL
   [REMOVE_THEN "ihd" MATCH_MP_TAC THEN EXISTS_TAC `ienv:inf_env` THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "ihds" MATCH_MP_TAC THEN EXISTS_TAC `extend_dec_ienv ienv2 ienv` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC env_rel_extend THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC env_rel_ienv_to_tenv THEN
      MATCH_MP_TAC(CONJUNCT1 infer_d_check) THEN
      MAP_EVERY EXISTS_TAC [`ienv:inf_env`; `a0:dec`; `st1:infer_st`; `sti:infer_st`] THEN
      ASM_MESON_TAC[envRel_env_rel_def];
      ASM_ARITH_TAC]];;

let INFER1AUX_IDS_DLOCAL_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihds")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_d_def; inferProps_st_ex_bind_success] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ienv1:inf_env` (X_CHOOSE_THEN `sti:infer_st` STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a0:dec list`; `ienv:inf_env`; `st1:infer_st`; `ienv1:inf_env`; `sti:infer_st`]
    (CONJUNCT2 infer_d_next_id_mono)) THEN
  MP_TAC(SPECL [`a1:dec list`; `extend_dec_ienv ienv1 ienv`; `sti:infer_st`; `ienv':inf_env`;
                `st2:infer_st`] (CONJUNCT2 infer_d_next_id_mono)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `set_ids (infer_st_next_id st1) (infer_st_next_id st2) =
                set_ids (infer_st_next_id st1) (infer_st_next_id sti) UNION
                set_ids (infer_st_next_id sti) (infer_st_next_id st2)` SUBST1_TAC THENL
   [MATCH_MP_TAC set_ids_eq_union THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(el 7 (CONJUNCTS type_d_rules)) THEN
  EXISTS_TAC `ienv_to_tenv ienv1` THEN
  REWRITE_TAC[INFER1AUX_set_ids_disjoint] THEN CONJ_TAC THENL
   [REMOVE_THEN "ihl" MATCH_MP_TAC THEN EXISTS_TAC `ienv:inf_env` THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "ihds" MATCH_MP_TAC THEN EXISTS_TAC `extend_dec_ienv ienv1 ienv` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC env_rel_extend THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC env_rel_ienv_to_tenv THEN
      MATCH_MP_TAC(CONJUNCT2 infer_d_check) THEN
      MAP_EVERY EXISTS_TAC [`ienv:inf_env`; `a0:dec list`; `st1:infer_st`; `sti:infer_st`] THEN
      ASM_MESON_TAC[envRel_env_rel_def];
      ASM_ARITH_TAC]];;

let INFER1AUX_IDS_TABBREV_EXN_TAC (k:int) : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_d_def; st_ex_ignore_bind_success; inferProps_st_ex_bind_success;
              inferProps_st_ex_return_success; check_dups_success;
              type_name_check_subst_success] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv` ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def; env_rel_sound_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `inf_env_inf_t ienv = type_env_t tenv`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else failwith "") THEN
  ASM_REWRITE_TAC[set_ids_same; ienv_to_tenv_def; inf_env_INFO.ri_accessors; nsMap_nsEmpty] THEN
  MATCH_MP_TAC(el k (CONJUNCTS type_d_rules)) THEN ASM_REWRITE_TAC[];;

let INFER1AUX_fresh_ids_disjoint = prove
 (`!n m. start_type_id <= n
         ==> DISJOINT (set_of_list (list_of_seq (\x. n + x) m))
                      (set_of_list (CONS Tlist_num (CONS Tbool_num prim_type_nums)))`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM_GENLIST;
              prim_type_nums_def; MEM; start_type_id_def;
              typeSystem_Tarray_num_def; typeSystem_Tbool_num_def; typeSystem_Tchar_num_def;
              typeSystem_Texn_num_def; typeSystem_Tfn_num_def; typeSystem_Tint_num_def;
              typeSystem_Tlist_num_def; typeSystem_Tref_num_def; typeSystem_Tstring_num_def;
              typeSystem_Ttup_num_def; typeSystem_Tvector_num_def;
              typeSystem_Tword64_num_def; typeSystem_Tword8_num_def;
              typeSystem_Tword8array_num_def; typeSystem_Tdouble_num_def] THEN
  ARITH_TAC);;

let INFER1AUX_IDS_DTYPE_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_d_def; st_ex_ignore_bind_success; inferProps_st_ex_bind_success;
              inferProps_st_ex_return_success; check_type_definition_success; n_fresh_id_def;
              PAIR_EQ; injectivity "exc"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv` ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def; env_rel_sound_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `inf_env_inf_t ienv = type_env_t tenv`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else failwith "") THEN
  ASM_REWRITE_TAC[ienv_to_tenv_def; inf_env_INFO.ri_accessors; nsMap_nsEmpty;
                  infer_st_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `set_ids (infer_st_next_id st1) (infer_st_next_id st1 + LENGTH (a1:type_def)) =
                set_of_list (list_of_seq (\x. infer_st_next_id st1 + x) (LENGTH a1))`
    SUBST1_TAC THENL
   [REWRITE_TAC[set_ids_eq; ADD_SUB2] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(el 3 (CONJUNCTS type_d_rules)) THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; INFER1AUX_fresh_ids_disjoint; ALL_DISTINCT_GENLIST] THEN
  ARITH_TAC;;

(* the generalisation of the inferred types is more general than any completion *)
let INFER1AUX_gen_inst = prove
 (`!s n ls ntvs s2 last_sub ec1 tvs' constrs s''.
     t_wfs s /\ check_s 0 (count n) s /\ ALL (check_t 0 (count n)) ls /\
     generalise_list 0 0 FEMPTY (MAP (t_walkstar s) ls) =
       (ntvs,s2,MAP (t_walkstar last_sub) ls) /\
     t_wfs last_sub /\ sub_completion ntvs n s ec1 last_sub /\
     sub_completion tvs' n s constrs s''
     ==> !t. MEM t ls
             ==> tscheme_inst (tvs',convert_t (t_walkstar s'' t))
                              (ntvs,convert_t (t_walkstar last_sub t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o check (fun th ->
    INFER1AUX_ec_is_app "sub_completion" (concl th) &&
    rand(concl th) = `s'':(num,infer_t)fmap`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o check (fun th ->
    INFER1AUX_ec_is_app "sub_completion" (concl th) &&
    rand(concl th) = `last_sub:(num,infer_t)fmap`)) THEN
  SUBGOAL_THEN `t_wfs (s'':(num,infer_t)fmap) /\ t_compat s s''` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_success]; ALL_TAC] THEN
  (* the walked types are closed in the current variables *)
  SUBGOAL_THEN `!t. MEM t ls ==> check_t 0 (count n) (t_walkstar s t)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC t_walkstar_check THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `count n` THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (MP (SPEC `t:infer_t` (REWRITE_RULE[GSYM ALL_MEM]
          (ASSUME `ALL (check_t 0 (count n)) ls`))) (ASSUME `MEM (t:infer_t) ls`))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the generalisation substitution *)
  MP_TAC(SPECL [`MAP (t_walkstar s) ls`; `0`; `0`; `FEMPTY:(num,num)fmap`; `ntvs:num`;
                `s2:(num,num)fmap`; `MAP (t_walkstar last_sub) ls`]
    (CONJUNCT2 generalise_subst)) THEN
  ASM_REWRITE_TAC[infer_subst_FEMPTY; FDOM_FEMPTY; UNION_EMPTY; DIFF_EMPTY; LE_0;
                  ADD_CLAUSES; SUBMAP_FEMPTY] THEN
  STRIP_TAC THEN
  (* the instantiation of the generalised variables *)
  MP_TAC(SPECL [`s'':(num,infer_t)fmap`; `tvs':num`] generalise_subst_exist) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`MAP (t_walkstar s) ls`; `[]:infer_t list`; `0`;
    `FEMPTY:(num,num)fmap`; `ntvs:num`; `s2:(num,num)fmap`;
    `MAP (t_walkstar last_sub) ls`] o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH; FRANGE_FEMPTY; EMPTY_SUBSET; MEM; FDOM_FEMPTY; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN CONJ_TAC THEN
    X_GEN_TAC `w:infer_t` THEN DISCH_THEN(X_CHOOSE_THEN `t0:infer_t` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `count n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC check_t_t_vars THEN EXISTS_TAC `0` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (MP (SPEC `t0:infer_t` (ASSUME `!t. MEM t ls ==> check_t 0 (count n) (t_walkstar s t)`))
            (ASSUME `MEM (t0:infer_t) ls`))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subst':infer_t list` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN
  REWRITE_TAC[tscheme_inst_def] THEN EXISTS_TAC `MAP convert_t subst'` THEN
  SUBGOAL_THEN `check_t ntvs {} (t_walkstar last_sub t)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(SPECL [`last_sub:(num,infer_t)fmap`; `ntvs:num`; `count n`] check_t_less)) THEN
    DISCH_THEN(MP_TAC o SPEC `t:infer_t`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ALL (check_t 0 (count n)) ls` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `count n SUBSET FDOM (last_sub:(num,infer_t)fmap)` THEN
      REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_COMPL; NOT_IN_EMPTY] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_MAP; check_t_to_check_freevars; ALL_MAP; o_DEF] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC check_t_to_check_freevars THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `t_walkstar last_sub t`
    (CONJUNCT1(SPECL [`ntvs:num`; `subst':infer_t list`] deBruijn_subst_convert))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `t_walkstar last_sub t = infer_subst s2 (t_walkstar s t)` SUBST1_TAC THENL
   [UNDISCH_TAC `MAP (infer_subst s2) (MAP (t_walkstar s) ls) = MAP (t_walkstar last_sub) ls` THEN
    REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t:infer_t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `t_vars (t_walkstar s t) SUBSET FDOM (s2:(num,num)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `t_vars (t_walkstar s t)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t_walkstar s t` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:infer_t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s'':(num,infer_t)fmap`; `s2:(num,num)fmap`; `subst':infer_t list`; `0`;
                `count n`] infer_deBruijn_subst_infer_subst_walkstar) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_FRANGE; IN_COUNT] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t_walkstar s t` o CONJUNCT1) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET];
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[t_compat_def]]);;

let INFER1AUX_init_infer_state = prove
 (`!st. infer_st_next_uvar (init_infer_state st) = 0 /\
        infer_st_subst (init_infer_state st) = FEMPTY /\
        infer_st_next_id (init_infer_state st) = infer_st_next_id st`,
  REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM]);;

(* the witnesses of the components of a successful run, read off the assumptions:  *)
(* for each (name,shape), the assumption name ... = r gives the terms shape r     *)
let INFER1AUX_RUN_WITNESS_TAC (specs:(string * (term -> term list)) list) : tactic =
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let find name = find (fun th ->
      try INFER1AUX_ec_is_app name (lhs(concl th)) with Failure _ -> false) ths in
    let wits = itlist (fun (nm,sh) acc -> sh (rhs(concl(find nm))) @ acc) specs [] in
    MAP_EVERY EXISTS_TAC wits gl;;

let INFER1AUX_succ_shape r = let (a,b) = dest_pair r in [rand a; b];;
let INFER1AUX_succ2_shape r =
  let (a,b) = dest_pair r in let (x,y) = dest_pair (rand a) in [x; y; b];;
let INFER1AUX_some_shape r = [rand r];;
let INFER1AUX_triple_shape r =
  let (a,b) = dest_pair r in let (x,y) = dest_pair b in [a; x; y];;

let INFER1AUX_dlet_success = prove
 (`!ienv locs p e st1 ienv' st2.
     infer_d ienv (Dlet locs p e) st1 = (M_success ienv',st2)
     ==> ?t1 st' t2 env' st'' s ntvs s2 ts'.
           infer_e (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv e
             (init_infer_state st1) = (M_success t1,st') /\
           infer_p (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv p st' =
             (M_success (t2,env'),st'') /\
           ALL_DISTINCT (MAP FST env') /\
           t_unify (infer_st_subst st'') t1 t2 = SOME s /\
           generalise_list 0 0 FEMPTY (MAP (t_walkstar s) (MAP SND env')) = (ntvs,s2,ts') /\
           (ntvs = 0 \/ is_value e) /\
           ienv' = inf_env_REC (alist_to_ns (ZIP (MAP FST env') (MAP (\t. (ntvs,t)) ts')))
                     nsEmpty nsEmpty /\
           st2 = infer_st_subst_fupd (K s) st''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[infer_d_def] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[inferProps_st_ex_bind_success; st_ex_ignore_bind_success;
              inferProps_st_ex_return_success; init_state_def; get_next_uvar_success;
              check_dups_success; add_constraint_success; TYSYS2AUX_apply_subst_list_success;
              guard_success; PAIR_EQ; injectivity "exc"; EXISTS_PAIR_THM] THEN
         CASE_REWRITE_TAC[])) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INFER1AUX_init_infer_state; infer_st_rewrs]) THEN
  INFER1AUX_RUN_WITNESS_TAC
    ["infer_e",INFER1AUX_succ_shape; "infer_p",INFER1AUX_succ2_shape;
     "t_unify",INFER1AUX_some_shape; "generalise_list",INFER1AUX_triple_shape] THEN
  ASM_REWRITE_TAC[]);;

(* the type environment of a generalised let binding *)
let INFER1AUX_ienv_to_tenv_let = prove
 (`!s n (env':(mlstring#infer_t)list).
     ienv_to_tenv (inf_env_REC
       (alist_to_ns (ZIP (MAP FST env') (MAP (\t. (n,t)) (MAP (t_walkstar s) (MAP SND env')))))
       nsEmpty nsEmpty) =
     type_env_REC (alist_to_ns (tenv_add_tvs n (convert_env s env'))) nsEmpty nsEmpty`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ienv_to_tenv_def; inf_env_INFO.ri_accessors; nsMap_alist_to_ns;
              type_env_INFO.ri_component_equality; type_env_INFO.ri_accessors] THEN
  AP_TERM_TAC THEN REWRITE_TAC[tenv_add_tvs_def; convert_env_def; MAP_MAP_o] THEN
  SPEC_TAC(`env':(mlstring#infer_t)list`,`l:(mlstring#infer_t)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ZIP] THEN ASM_REWRITE_TAC[CONS_11; o_THM] THEN
  SPEC_TAC(`h:mlstring#infer_t`,`h:mlstring#infer_t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST; SND]);;

let INFER1AUX_ALL2_tenv_add_tvs = prove
 (`!tvs1 s1 tvs2 s2 (env':(mlstring#infer_t)list).
     (!t. MEM t (MAP SND env')
          ==> tscheme_inst (tvs1,convert_t (t_walkstar s1 t))
                           (tvs2,convert_t (t_walkstar s2 t)))
     ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs1 (convert_env s1 env')))
                           (MAP SND (tenv_add_tvs tvs2 (convert_env s2 env')))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tenv_add_tvs_def; convert_env_def; MAP_MAP_o] THEN
  SPEC_TAC(`env':(mlstring#infer_t)list`,`l:(mlstring#infer_t)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2; MEM] THEN
  SPEC_TAC(`h:mlstring#infer_t`,`h:mlstring#infer_t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[o_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[SND] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let INFER1AUX_ids_dlet = prove
 (`!tenv ienv locs p e st1 t1 st' t2 env' st'' s ntvs s2 ts'.
     envRel_env_rel tenv ienv /\ start_type_id <= infer_st_next_id st1 /\
     infer_e (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv e
       (init_infer_state st1) = (M_success t1,st') /\
     infer_p (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv p st' =
       (M_success (t2,env'),st'') /\
     ALL_DISTINCT (MAP FST env') /\
     t_unify (infer_st_subst st'') t1 t2 = SOME s /\
     generalise_list 0 0 FEMPTY (MAP (t_walkstar s) (MAP SND env')) = (ntvs,s2,ts') /\
     (ntvs = 0 \/ is_value e)
     ==> type_d T tenv (Dlet locs p e)
           (set_ids (infer_st_next_id st1) (infer_st_next_id (infer_st_subst_fupd (K s) st'')))
           (ienv_to_tenv (inf_env_REC (alist_to_ns (ZIP (MAP FST env') (MAP (\t. (ntvs,t)) ts')))
                            nsEmpty nsEmpty))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ABBREV_TAC `loc = loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[envRel_env_rel_def] o
    check (fun th -> INFER1AUX_ec_is_app "envRel_env_rel" (concl th))) THEN
  SUBGOAL_THEN `ienv_val_ok (count 0) (inf_env_inf_v ienv) /\
                tenv_ctor_ok (inf_env_inf_c ienv) /\ tenv_abbrev_ok (inf_env_inf_t ienv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN REWRITE_TAC[ienv_ok_def; COUNT_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv /\ inf_env_inf_c ienv = type_env_c tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_sound_def]; ALL_TAC] THEN
  (* next ids *)
  SUBGOAL_THEN `infer_st_next_id (infer_st_subst_fupd (K s) st'') = infer_st_next_id st1`
    SUBST1_TAC THENL
   [REWRITE_TAC[infer_st_INFO.ri_accfupds] THEN
    MP_TAC(MATCH_MP (CONJUNCT1 infer_e_next_id_const)
      (ASSUME `infer_e loc ienv e (init_infer_state st1) = (M_success t1,st')`)) THEN
    MP_TAC(MATCH_MP (CONJUNCT1 infer_p_next_id_const)
      (ASSUME `infer_p loc ienv p st' = (M_success (t2,env'),st'')`)) THEN
    REWRITE_TAC[INFER1AUX_init_infer_state] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[set_ids_same] THEN
  (* well-formedness and closedness *)
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state st1`; `t1:infer_t`] THEN
    ASM_REWRITE_TAC[INFER1AUX_init_infer_state; t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st'')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st':infer_st`;
                          `t2:infer_t`; `env':(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `infer_st_next_uvar st' <= infer_st_next_uvar st''` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_next_uvar_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (count (infer_st_next_uvar st')) t1` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state st1`] THEN
    ASM_REWRITE_TAC[INFER1AUX_init_infer_state];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (count (infer_st_next_uvar st')) (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state st1`; `t1:infer_t`] THEN
    ASM_REWRITE_TAC[INFER1AUX_init_infer_state; t_wfs_FEMPTY; check_s_def; FDOM_FEMPTY;
                    NOT_IN_EMPTY; COUNT_ZERO] THEN
    ASM_REWRITE_TAC[GSYM COUNT_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (count (infer_st_next_uvar st'')) (infer_st_subst st'')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st':infer_st`;
                          `t2:infer_t`; `env':(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_check_t)
    (ASSUME `infer_p loc ienv p st' = (M_success (t2,env'),st'')`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `check_s 0 (count (infer_st_next_uvar st'')) s` ASSUME_TAC THENL
   [MATCH_MP_TAC t_unify_check_s THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st''`; `t1:infer_t`; `t2:infer_t`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more4)
      (ASSUME `check_t 0 (count (infer_st_next_uvar st')) t1`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the completion of the generalisation *)
  MP_TAC(ISPECL [`0`; `s:(num,infer_t)fmap`; `MAP SND (env':(mlstring#infer_t)list)`;
                 `ntvs:num`; `s2:(num,num)fmap`; `ts':infer_t list`;
                 `infer_st_next_uvar st''`; `0`; `{}:num->bool`] generalise_complete) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX; GSYM every_shim]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec1:(infer_t#infer_t)list` (X_CHOOSE_THEN
    `last_sub:(num,infer_t)fmap` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[INFER1AUX_ienv_to_tenv_let] THEN
  (* soundness of the inferred typing under the completion *)
  SUBGOAL_THEN `sub_completion ntvs (infer_st_next_uvar st'') (infer_st_subst st'')
                  (CONS (t1,t2) ec1) last_sub` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_unify2 THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 sub_completion_infer_p)
    (CONJ (ASSUME `infer_p loc ienv p st' = (M_success (t2,env'),st'')`)
          (ASSUME `sub_completion ntvs (infer_st_next_uvar st'') (infer_st_subst st'')
                     (CONS (t1,t2) ec1) last_sub`))) THEN
  DISCH_THEN(X_CHOOSE_TAC `tsp:(infer_t#infer_t)list`) THEN
  SUBGOAL_THEN `env_rel_sound last_sub ienv tenv (bind_tvar ntvs Empty)` ASSUME_TAC THENL
   [MATCH_MP_TAC env_rel_e_sound_empty_to THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC env_rel_sound_extend_tvs THEN ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `type_e tenv (bind_tvar ntvs Empty) e (convert_t (t_walkstar last_sub t1))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_sound) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `init_infer_state st1`;
      `st':infer_st`; `APPEND tsp (CONS (t1:infer_t,t2:infer_t) ec1)`] THEN
    ASM_REWRITE_TAC[INFER1AUX_init_infer_state; COUNT_ZERO; t_wfs_FEMPTY;
                    bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `type_p ntvs tenv p (convert_t (t_walkstar last_sub t2))
                  (convert_env last_sub env')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_sound) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `st':infer_st`;
      `st'':infer_st`; `CONS (t1:infer_t,t2:infer_t) ec1`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar last_sub t1 = t_walkstar last_sub t2` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_apply THEN
    MAP_EVERY EXISTS_TAC [`ntvs:num`; `infer_st_next_uvar st''`; `s:(num,infer_t)fmap`;
                          `ec1:(infer_t#infer_t)list`] THEN
    ASM_MESON_TAC[t_unify_unifier];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (pat_bindings p)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (CONJUNCT1 infer_p_bindings)
      (ASSUME `infer_p loc ienv p st' = (M_success (t2,env'),st'')`)) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `t_walkstar last_sub t1 = t_walkstar last_sub t2`)) THEN
  ASM_CASES_TAC `is_value e` THENL
   [(* a value: the most general type scheme *)
    MATCH_MP_TAC(el 0 (CONJUNCTS type_d_rules)) THEN
    EXISTS_TAC `convert_t (t_walkstar last_sub t2)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`tvs':num`; `bindings':(mlstring#t)list`; `t':t`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tvs':num`; `p:pat`;
                  `e:exp`; `t':t`; `bindings':(mlstring#t)list`; `st1:infer_st`]
      infer_pe_complete) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[inferSound_env_rel_complete_bind]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ta:infer_t` (X_CHOOSE_THEN `tpa:infer_t`
      (X_CHOOSE_THEN `nba:(mlstring#infer_t)list` (X_CHOOSE_THEN `sta:infer_st`
      (X_CHOOSE_THEN `sta':infer_st` (X_CHOOSE_THEN `sa:(num,infer_t)fmap`
      (X_CHOOSE_THEN `csa:(infer_t#infer_t)list` (X_CHOOSE_THEN `sa':(num,infer_t)fmap`
       STRIP_ASSUME_TAC)))))))) THEN
    UNDISCH_TAC `infer_e loc ienv e (init_infer_state st1) = (M_success ta,sta)` THEN
    ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `infer_p loc ienv p st' = (M_success (tpa,nba),sta')` THEN
    ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `t_unify (infer_st_subst st'') t1 t2 = SOME sa` THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `convert_env sa' (env':(mlstring#infer_t)list) = bindings'`)) THEN
    MATCH_MP_TAC INFER1AUX_ALL2_tenv_add_tvs THEN
    MATCH_MP_TAC INFER1AUX_gen_inst THEN
    MAP_EVERY EXISTS_TAC [`s:(num,infer_t)fmap`; `infer_st_next_uvar st''`; `s2:(num,num)fmap`;
                          `ec1:(infer_t#infer_t)list`; `csa:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[GSYM every_shim];
    (* not a value: no generalisation *)
    SUBGOAL_THEN `ntvs = 0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `ntvs = 0 \/ is_value e` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(el 1 (CONJUNCTS type_d_rules)) THEN
    EXISTS_TAC `convert_t (t_walkstar last_sub t2)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bind_tvar_def]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC infer_e_type_pe_determ THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `st':infer_st`; `st'':infer_st`;
      `t1:infer_t`; `t2:infer_t`; `env':(mlstring#infer_t)list`; `s:(num,infer_t)fmap`;
      `st1:infer_st`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`MAP (t_walkstar s) (MAP SND (env':(mlstring#infer_t)list))`;
                  `s2:(num,num)fmap`; `MAP (t_walkstar last_sub) (MAP SND (env':(mlstring#infer_t)list))`;
                  `count (infer_st_next_uvar st'')`] (CONJUNCT2 generalise_none)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ALL_MAP; o_DEF] THEN
      UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (count (infer_st_next_uvar st'')) t) env'` THEN
      REWRITE_TAC[every_shim; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC t_walkstar_check THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `count (infer_st_next_uvar st'')` THEN
        ASM_REWRITE_TAC[SUBSET_UNION];
        MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] (CONJUNCT1 check_t_more5)) THEN
        EXISTS_TAC `count (infer_st_next_uvar st'')` THEN REWRITE_TAC[SUBSET_UNION] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC MEM_MAP_f THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[every_shim; ALL_MAP; o_DEF] THEN SIMP_TAC[ETA_AX]]]);;

let INFER1AUX_IDS_DLET_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INFER1AUX_dlet_success o check (fun th ->
    try INFER1AUX_ec_is_app "infer_d" (lhs(concl th)) with Failure _ -> false)) THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_ids_dlet THEN
  MAP_EVERY EXISTS_TAC [`ienv:inf_env`; `t1:infer_t`; `st':infer_st`; `t2:infer_t`;
                        `s2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[];;

let INFER1AUX_dletrec_success = prove
 (CASE_TERM `!ienv locs funs st1 ienv' st2.
     infer_d ienv (Dletrec locs funs) st1 = (M_success ienv',st2)
     ==> ?funs_ts st3 st4 num_gen s2 ts'.
           ALL_DISTINCT (MAP FST funs) /\
           infer_funs (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
             (inf_env_inf_v_fupd
                (K (nsAppend
                      (alist_to_ns
                         (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                            (MAP Infer_Tuvar (COUNT_LIST (LENGTH funs)))))
                      (inf_env_inf_v ienv))) ienv)
             funs
             (infer_st_next_uvar_fupd (K (LENGTH funs)) (init_infer_state st1)) =
             (M_success funs_ts,st3) /\
           LENGTH funs = LENGTH funs_ts /\
           infer_st_next_uvar st3 = infer_st_next_uvar st4 /\
           infer_st_next_id st3 = infer_st_next_id st4 /\
           pure_add_constraints (infer_st_subst st3)
             (ZIP (MAP Infer_Tuvar (COUNT_LIST (LENGTH funs))) funs_ts) (infer_st_subst st4) /\
           generalise_list 0 0 FEMPTY
             (MAP (t_walkstar (infer_st_subst st4)) (MAP Infer_Tuvar (COUNT_LIST (LENGTH funs)))) =
             (num_gen,s2,ts') /\
           ienv' = inf_env_REC
                     (alist_to_ns
                        (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(num_gen,t))) funs ts'))
                     nsEmpty nsEmpty /\
           st2 = st4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[infer_d_def] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[inferProps_st_ex_bind_success; st_ex_ignore_bind_success;
              inferProps_st_ex_return_success; init_state_def; get_next_uvar_success;
              check_dups_success; add_constraints_success; TYSYS2AUX_apply_subst_list_success;
              n_fresh_uvar_success; PAIR_EQ; injectivity "exc"; EXISTS_PAIR_THM] THEN
         CASE_REWRITE_TAC[])) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INFER1AUX_init_infer_state; infer_st_rewrs; ADD_CLAUSES;
                              LENGTH_MAP; LENGTH_COUNT_LIST; ETA_AX]) THEN
  INFER1AUX_RUN_WITNESS_TAC ["infer_funs",INFER1AUX_succ_shape] THEN
  EXISTS_TAC `st2:infer_st` THEN
  INFER1AUX_RUN_WITNESS_TAC ["generalise_list",INFER1AUX_triple_shape] THEN
  ASM_REWRITE_TAC[]);;

(* list identities for the environments of a Letrec *)
let INFER1AUX_MAP2_fxe = prove
 (CASE_TERM `!(g:infer_t->B) (funs:(mlstring#mlstring#exp)list) (ts:infer_t list).
     LENGTH funs = LENGTH ts
     ==> MAP2 (\fxe t. match fxe with (f,x,e) -> (f,g t)) funs ts =
         ZIP (MAP FST funs) (MAP g ts)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MAP; ZIP] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[CONS_11] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST]);;

let INFER1AUX_convert_env_ZIP = prove
 (`!s (a:mlstring list) (b:infer_t list).
     LENGTH a = LENGTH b
     ==> convert_env s (ZIP a b) = ZIP a (MAP (convert_t o t_walkstar s) b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[convert_env_def; ZIP_MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[o_THM]);;

let INFER1AUX_walk_compat_map = prove
 (`!s s' (l1:infer_t list) l2.
     t_compat s s' /\ MAP (t_walkstar s) l1 = MAP (t_walkstar s) l2
     ==> MAP (t_walkstar s') l1 = MAP (t_walkstar s') l2`,
  REWRITE_TAC[t_compat_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `MAP (t_walkstar (s':(num,infer_t)fmap))`) THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN ASM_REWRITE_TAC[ETA_AX]);;

let INFER1AUX_ids_dletrec = prove
 (CASE_TERM `!tenv ienv locs funs st1 funs_ts st3 st4 num_gen s2 ts'.
     envRel_env_rel tenv ienv /\ start_type_id <= infer_st_next_id st1 /\
     ALL_DISTINCT (MAP FST funs) /\
     infer_funs (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                      (MAP Infer_Tuvar (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv)
       funs
       (infer_st_next_uvar_fupd (K (LENGTH funs)) (init_infer_state st1)) =
       (M_success funs_ts,st3) /\
     LENGTH funs = LENGTH funs_ts /\
     infer_st_next_uvar st3 = infer_st_next_uvar st4 /\
     infer_st_next_id st3 = infer_st_next_id st4 /\
     pure_add_constraints (infer_st_subst st3)
       (ZIP (MAP Infer_Tuvar (COUNT_LIST (LENGTH funs))) funs_ts) (infer_st_subst st4) /\
     generalise_list 0 0 FEMPTY
       (MAP (t_walkstar (infer_st_subst st4)) (MAP Infer_Tuvar (COUNT_LIST (LENGTH funs)))) =
       (num_gen,s2,ts')
     ==> type_d T tenv (Dletrec locs funs)
           (set_ids (infer_st_next_id st1) (infer_st_next_id st4))
           (ienv_to_tenv
              (inf_env_REC
                 (alist_to_ns
                    (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(num_gen,t))) funs ts'))
                 nsEmpty nsEmpty))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `loc = loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)` THEN
  ABBREV_TAC `us = MAP Infer_Tuvar (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))` THEN
  SUBGOAL_THEN `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`
    ASSUME_TAC THENL
   [EXPAND_TAC "us" THEN REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. MEM t us <=>
                    ?k. k < LENGTH (funs:(mlstring#mlstring#exp)list) /\ t = Infer_Tuvar k`
    ASSUME_TAC THENL
   [EXPAND_TAC "us" THEN REWRITE_TAC[MEM_MAP; MEM_COUNT_LIST] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP INFER1AUX_MAP2_funs (SYM th)]) THEN
  ABBREV_TAC `bindings = ZIP (MAP FST (funs:(mlstring#mlstring#exp)list)) (us:infer_t list)` THEN
  ABBREV_TAC (CASE_TERM `ienv1 = inf_env_inf_v_fupd
      (K (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) bindings))
                   (inf_env_inf_v ienv))) ienv`) THEN
  ABBREV_TAC `st0 = infer_st_next_uvar_fupd (K (LENGTH (funs:(mlstring#mlstring#exp)list)))
                      (init_infer_state st1)` THEN
  SUBGOAL_THEN `infer_st_next_uvar st0 = LENGTH (funs:(mlstring#mlstring#exp)list) /\
                infer_st_subst st0 = FEMPTY /\ infer_st_next_id st0 = infer_st_next_id st1`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "st0" THEN
    REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM; INFER1AUX_init_infer_state];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[envRel_env_rel_def] o
    check (fun th -> INFER1AUX_ec_is_app "envRel_env_rel" (concl th))) THEN
  SUBGOAL_THEN `ienv_val_ok (count 0) (inf_env_inf_v ienv) /\
                tenv_ctor_ok (inf_env_inf_c ienv) /\ tenv_abbrev_ok (inf_env_inf_t ienv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN REWRITE_TAC[ienv_ok_def; COUNT_ZERO]; ALL_TAC] THEN
  (* next ids *)
  SUBGOAL_THEN `infer_st_next_id st4 = infer_st_next_id st1` SUBST1_TAC THENL
   [INFER1AUX_IFN_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_id_const))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[set_ids_same] THEN
  (* the extended environment *)
  SUBGOAL_THEN `ienv_ok (count (LENGTH (funs:(mlstring#mlstring#exp)list))) ienv1`
    ASSUME_TAC THENL
   [EXPAND_TAC "ienv1" THEN REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_pes THEN CONJ_TAC THENL
     [EXPAND_TAC "bindings" THEN ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[check_t_def; IN_COUNT];
      MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_mono THEN EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC[COUNT_ZERO; LE_0]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th =
    `LENGTH (funs:(mlstring#mlstring#exp)list) = LENGTH (funs_ts:infer_t list)`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th =
    `infer_st_next_uvar st3 = infer_st_next_uvar st4`)) THEN
  (* properties of the run of infer_funs *)
  SUBGOAL_THEN `t_wfs (infer_st_subst st3)` ASSUME_TAC THENL
   [INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_wfs)))) THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (funs:(mlstring#mlstring#exp)list) <= infer_st_next_uvar st3`
    ASSUME_TAC THENL
   [INFER1AUX_IFN_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_uvar_mono))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (count (infer_st_next_uvar st3))) funs_ts` ASSUME_TAC THENL
   [INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_t)))) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ienv_ok (count (LENGTH (funs:(mlstring#mlstring#exp)list))) ienv1` THEN
    ASM_SIMP_TAC[ienv_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (count (infer_st_next_uvar st3)) (infer_st_subst st3)` ASSUME_TAC THENL
   [INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_s)))) THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[check_s_def; FDOM_FEMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st4)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (count (infer_st_next_uvar st3))) us` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (count (infer_st_next_uvar st3)) (infer_st_subst st4)` ASSUME_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_check_s THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st3`; `ZIP (us:infer_t list) (funs_ts:infer_t list)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_ALL_ZIP THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the completion of the generalisation *)
  MP_TAC(ISPECL [`0`; `infer_st_subst st4`; `us:infer_t list`; `num_gen:num`;
                 `s2:(num,num)fmap`; `ts':infer_t list`; `infer_st_next_uvar st3`; `0`;
                 `{}:num->bool`] generalise_complete) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec1:(infer_t#infer_t)list` (X_CHOOSE_THEN
    `last_sub:(num,infer_t)fmap` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `sub_completion num_gen (infer_st_next_uvar st3) (infer_st_subst st3)
                  (APPEND (ZIP (us:infer_t list) (funs_ts:infer_t list)) ec1) last_sub` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_add_constraints THEN
    EXISTS_TAC `infer_st_subst st4` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o check (fun th ->
    INFER1AUX_ec_is_app "sub_completion" (concl th) &&
    rand(rator(concl th)) = `ec1:(infer_t#infer_t)list`)) THEN
  SUBGOAL_THEN `env_rel_sound last_sub ienv tenv (bind_tvar num_gen Empty)` ASSUME_TAC THENL
   [MATCH_MP_TAC env_rel_e_sound_empty_to THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC env_rel_sound_extend_tvs THEN ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `env_rel_sound last_sub ienv1 tenv
                  (bind_var_list 0 (convert_env last_sub bindings) (bind_tvar num_gen Empty))`
    ASSUME_TAC THENL
   [EXPAND_TAC "ienv1" THEN MATCH_MP_TAC env_rel_sound_merge0 THEN
    ASM_REWRITE_TAC[bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
    EXPAND_TAC "bindings" THEN REWRITE_TAC[every_shim] THEN
    SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP;
             ASSUME `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`] THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[check_t_def] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `count (infer_st_next_uvar st3) SUBSET FDOM (last_sub:(num,infer_t)fmap)`)) THEN
    REWRITE_TAC[IN_COUNT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* soundness of the inferred typing of the functions *)
  INFER1AUX_IFN_TAC (REWRITE_RULE[IMP_CONJ] (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_sound)))) THEN
  DISCH_THEN(MP_TAC o SPECL [`tenv:type_env`;
    `bind_var_list 0 (convert_env last_sub bindings) (bind_tvar num_gen Empty)`;
    `APPEND (ZIP (us:infer_t list) (funs_ts:infer_t list)) ec1`; `last_sub:(num,infer_t)fmap`]) THEN
  ASM_REWRITE_TAC[t_wfs_FEMPTY; num_tvs_bind_var_list; bind_tvar_rewrites; num_tvs_def;
                  ADD_CLAUSES] THEN
  ASM_SIMP_TAC[INFER1AUX_MAP2_fxe] THEN REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
  (* the walks of the function variables and of the inferred types agree *)
  SUBGOAL_THEN `MAP (t_walkstar (infer_st_subst st4)) us =
                MAP (t_walkstar (infer_st_subst st4)) funs_ts` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`infer_st_subst st3`; `ZIP (us:infer_t list) (funs_ts:infer_t list)`;
                   `infer_st_subst st4`] pure_add_constraints_apply) THEN
    ASM_SIMP_TAC[MAP_o; MAP_FST_ZIP; MAP_SND_ZIP];
    ALL_TAC] THEN
  SUBGOAL_THEN `convert_env last_sub bindings =
                ZIP (MAP FST (funs:(mlstring#mlstring#exp)list))
                    (MAP (convert_t o t_walkstar last_sub) funs_ts)` ASSUME_TAC THENL
   [EXPAND_TAC "bindings" THEN
    SIMP_TAC[INFER1AUX_convert_env_ZIP; LENGTH_MAP;
             ASSUME `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`] THEN
    REWRITE_TAC[MAP_o] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INFER1AUX_walk_compat_map THEN
    EXISTS_TAC `infer_st_subst st4` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> INFER1AUX_ec_is_app "type_funs" (concl th))) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
    try lhs(concl th) = `convert_env last_sub (bindings:(mlstring#infer_t)list)` with Failure _ -> false)) THEN
  DISCH_TAC THEN
  (* the type environment of the generalised functions *)
  SUBGOAL_THEN (CASE_TERM
    `ienv_to_tenv (inf_env_REC
        (alist_to_ns (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(num_gen:num,t)))
                        (funs:(mlstring#mlstring#exp)list)
                        (MAP (t_walkstar last_sub) (us:infer_t list)))) nsEmpty nsEmpty) =
     type_env_REC (alist_to_ns (tenv_add_tvs num_gen (convert_env last_sub bindings)))
       nsEmpty nsEmpty`) SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INFER1AUX_ienv_to_tenv_let] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "bindings" THEN
    SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP;
             ASSUME `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC INFER1AUX_MAP2_fxe THEN ASM_REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  MATCH_MP_TAC(el 2 (CONJUNCTS type_d_rules)) THEN ASM_REWRITE_TAC[] THEN
  (* the extra check: the generalisation is the most general typing *)
  MAP_EVERY X_GEN_TAC [`tvs':num`; `bindings':(mlstring#t)list`] THEN DISCH_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
    try lhs(concl th) = `convert_env last_sub (bindings:(mlstring#infer_t)list)`
    with Failure _ -> false)) THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `tenv:type_env`; `tvs':num`;
                `funs:(mlstring#mlstring#exp)list`; `bindings':(mlstring#t)list`; `st1:infer_st`]
    infer_funs_complete) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[INFER1AUX_init_infer_state; ADD_CLAUSES] THEN REWRITE_TAC[ETA_AX] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP INFER1AUX_MAP2_funs (SYM (ASSUME
    `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`))] THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `fts:infer_t list` (X_CHOOSE_THEN `sta:infer_st`
    (X_CHOOSE_THEN `sta':infer_st` (X_CHOOSE_THEN `constr:(infer_t#infer_t)list`
     (X_CHOOSE_THEN `sb:(num,infer_t)fmap` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `funs_ts:infer_t list = fts`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `st3:infer_st = sta`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `infer_st_next_uvar st3 = infer_st_next_uvar sta'`)) THEN
  SUBGOAL_THEN `infer_st_subst sta' = infer_st_subst st4` ASSUME_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_functional THEN
    MAP_EVERY EXISTS_TAC [`ZIP (us:infer_t list) (funs_ts:infer_t list)`; `infer_st_subst st3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sub_completion tvs' (infer_st_next_uvar st3) (infer_st_subst st4) constr sb`
    ASSUME_TAC THENL
   [UNDISCH_TAC `sub_completion tvs' (infer_st_next_uvar sta') (infer_st_subst sta') constr sb` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (t_walkstar sb) us = MAP (t_walkstar sb) (funs_ts:infer_t list)` ASSUME_TAC THENL
   [MATCH_MP_TAC INFER1AUX_walk_compat_map THEN EXISTS_TAC `infer_st_subst st4` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[sub_completion_def] o check (fun th ->
      concl th = `sub_completion tvs' (infer_st_next_uvar st3) (infer_st_subst st4) constr sb`)) THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  SUBGOAL_THEN `bindings' = convert_env sb (bindings:(mlstring#infer_t)list)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `bindings':(mlstring#t)list` (REWRITE_RULE[UNZIP_DEF] ZIP_UNZIP)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFER1AUX_type_funs_facts o check (fun th ->
      concl th = `type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings'`)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "bindings" THEN
    SIMP_TAC[INFER1AUX_convert_env_ZIP; LENGTH_MAP;
             ASSUME `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`] THEN
    ASM_REWRITE_TAC[MAP_o];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
    try lhs(concl th) = `convert_env last_sub (bindings:(mlstring#infer_t)list)`
    with Failure _ -> false)) THEN
  MATCH_MP_TAC INFER1AUX_ALL2_tenv_add_tvs THEN
  EXPAND_TAC "bindings" THEN
  SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP;
           ASSUME `LENGTH (us:infer_t list) = LENGTH (funs:(mlstring#mlstring#exp)list)`] THEN
  MATCH_MP_TAC INFER1AUX_gen_inst THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st4`; `infer_st_next_uvar st3`; `s2:(num,num)fmap`;
                        `ec1:(infer_t#infer_t)list`; `constr:(infer_t#infer_t)list`] THEN
  ASM_REWRITE_TAC[]);;

let INFER1AUX_IDS_DLETREC_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INFER1AUX_dletrec_success o check (fun th ->
    try INFER1AUX_ec_is_app "infer_d" (lhs(concl th)) with Failure _ -> false)) THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER1AUX_ids_dletrec THEN
  MAP_EVERY EXISTS_TAC [`ienv:inf_env`; `funs_ts:infer_t list`; `st3:infer_st`;
                        `s2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[];;

let infer_d_sound = prove
 (`(!d tenv ienv st1 st2 ienv'.
     infer_d ienv d st1 = (M_success ienv',st2) /\
     envRel_env_rel tenv ienv /\
     start_type_id <= infer_st_next_id st1
     ==> type_d T tenv d (set_ids (infer_st_next_id st1) (infer_st_next_id st2))
           (ienv_to_tenv ienv')) /\
   (!ds tenv ienv st1 st2 ienv'.
     infer_ds ienv ds st1 = (M_success ienv',st2) /\
     envRel_env_rel tenv ienv /\
     start_type_id <= infer_st_next_id st1
     ==> type_ds T tenv ds (set_ids (infer_st_next_id st1) (infer_st_next_id st2))
           (ienv_to_tenv ienv'))`,
  MATCH_MP_TAC dec_INDUCT THEN REPEAT CONJ_TAC THENL
   [INFER1AUX_IDS_DLET_TAC; INFER1AUX_IDS_DLETREC_TAC; INFER1AUX_IDS_DTYPE_TAC;
    INFER1AUX_IDS_TABBREV_EXN_TAC 4; INFER1AUX_IDS_TABBREV_EXN_TAC 5; INFER1AUX_IDS_DMOD_TAC;
    INFER1AUX_IDS_DLOCAL_TAC; INFER1AUX_IDS_DENV_TAC; INFER1AUX_IDS_NIL_TAC;
    INFER1AUX_IDS_CONS_TAC]);;

let db_subst_infer_subst_swap2 = prove
 (`(!t (s:(num,infer_t)fmap) tvs (uvar:num) (n:num).
     t_wfs s /\ check_t tvs {} t
     ==> convert_t (t_walkstar s (infer_deBruijn_subst
                    (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs)) t)) =
         deBruijn_subst 0 (MAP (convert_t o t_walkstar s)
                             (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs)))
           (convert_t t)) /\
   (!ts (s:(num,infer_t)fmap) tvs (uvar:num) (n:num).
     t_wfs s /\ ALL (\t. check_t tvs {} t) ts
     ==> MAP (convert_t o t_walkstar s o
              infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs))) ts =
         MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s)
                (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs))) o convert_t) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THENL
   [FS[check_t_def; t_walkstar_eqn1; infer_deBruijn_subst_alt; convert_t_def; LT;
       deBruijn_subst_def; LENGTH_MAP; LENGTH_COUNT_LIST; el_map_count; EL_MAP;
       MAP_MAP_o; o_THM; SUB_0; ADD_CLAUSES];
    RULE_ASSUM_TAC(REWRITE_RULE[MAP_MAP_o; check_t_def]) THEN
    ASM_SIMP_TAC[t_walkstar_eqn1; infer_deBruijn_subst_alt; convert_t_def;
                 deBruijn_subst_def; MAP_MAP_o; injectivity "t"] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    RULE_ASSUM_TAC(REWRITE_RULE[check_t_def; NOT_IN_EMPTY]) THEN FIRST_ASSUM CONTR_TAC;
    REWRITE_TAC[MAP];
    REWRITE_TAC[MAP; CONS_11; o_THM] THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
    ASM_MESON_TAC[]]);;
