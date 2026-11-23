(* ========================================================================= *)
(* inferComplete: port of HOL4                                               *)
(* compiler/inference/proofs/inferCompleteScript.sml (CakeML v3479).         *)
(* Proves completeness of the type inferencer, i.e. if there is a type for   *)
(* the program, then the type inferencer will find a type (the most general  *)
(* type).                                                                    *)
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
needs "compiler/inference/proofs/type_dCanon.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Records: st.next_id is infer_st_next_id st, ienv.inf_v is              *)
(*   inf_env_inf_v ienv, tenv.v is type_env_v tenv; the record literals      *)
(*   <| v := ..; c := ..; t := .. |> are type_env_REC and inf_env_REC.       *)
(* - HOL4 EVERY is ALL, LIST_REL is ALL2, set is set_of_list, GENLIST f n is *)
(*   list_of_seq f n, ZIP (l1,l2) is ZIP l1 l2.                              *)
(* - The free variables of a HOL4 statement are universally quantified       *)
(*   (also arb and TC_int of the two binding lemmas, which are variables,   *)
(*   not constants, in HOL4 too).                                            *)
(* - HOL4 [local] theorems are kept (they are ordinary theorems here).       *)
(* - Helper lemmas that are not HOL4 theorems are INFER2AUX_.                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local] *)
let generalise_no_uvars = prove
 (`(!t m n (s:(num,num)fmap) dbvars.
      check_t dbvars {} t ==> generalise m n s t = (0,s,t)) /\
   (!ts m n (s:(num,num)fmap) dbvars.
      ALL (check_t dbvars {}) ts ==> generalise_list m n s ts = (0,s,ts))`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; ALL; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_REWRITE_TAC[generalise_def] THEN CASE_REWRITE_TAC[ADD_CLAUSES]);;

(* HOL4: val t_ind = t_induction |> Q.SPECL [P, EVERY P] |> ... is an ML     *)
(* binding of the same theorem as inferProps' t_ind, which is used below.   *)

let INFER2AUX_ALOOKUP_ZIP_find_index = prove
 (`!(l:A list) (vs:B list) x m i.
     LENGTH vs = LENGTH l /\ find_index x l m = SOME (m + i)
     ==> ALOOKUP (ZIP l vs) x = SOME (EL i vs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; option_DISTINCT] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[ARITH_RULE `m = m + i <=> i = 0`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EL; HD];
    STRIP_TAC THEN
    SUBGOAL_THEN `?j. i = SUC j` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP find_index_LESS_LENGTH) THEN
      DISCH_TAC THEN EXISTS_TAC `i - 1` THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `m + 1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN ARITH_TAC]);;

let INFER2AUX_ALOOKUP_ZIP_MEM = prove
 (`!(l:A list) (vs:B list) x.
     LENGTH vs = LENGTH l /\ MEM x l
     ==> ?i. find_index x l 0 = SOME i /\ i < LENGTH l /\ EL i l = x /\
             ALOOKUP (ZIP l vs) x = SOME (EL i vs)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP find_index_MEM) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INFER2AUX_ALOOKUP_ZIP_find_index THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

let env_rel_binding_lemma = prove
 (CASE_TERM `!t fvs fvs' subst arb.
     check_freevars 0 fvs' t /\
     set_of_list fvs' SUBSET set_of_list fvs /\
     ALL_DISTINCT fvs'
     ==> infer_deBruijn_subst subst
           (infer_type_subst (ZIP fvs' (MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) t) =
         infer_deBruijn_subst
           (list_of_seq (\n. infer_deBruijn_subst subst
                               (match find_index (EL n fvs) fvs' 0 with
                                  NONE -> Infer_Tapp [] arb
                                | SOME k -> Infer_Tvar_db k)) (LENGTH fvs))
           (infer_type_subst (ZIP fvs (list_of_seq (\x. Infer_Tvar_db x) (LENGTH fvs))) t)`,
  MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[infer_type_subst_alt; check_freevars_def; LT] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`name:mlstring`; `fvs:mlstring list`; `fvs':mlstring list`;
                         `subst:infer_t list`; `arb:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`fvs':mlstring list`;
                   `MAP Infer_Tvar_db (COUNT_LIST (LENGTH (fvs':mlstring list)))`;
                   `name:mlstring`] INFER2AUX_ALOOKUP_ZIP_MEM) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`fvs:mlstring list`;
                   `list_of_seq (\x. Infer_Tvar_db x) (LENGTH (fvs:mlstring list))`;
                   `name:mlstring`] INFER2AUX_ALOOKUP_ZIP_MEM) THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_SET_OF_LIST]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; EL_LIST_OF_SEQ;
                 LENGTH_LIST_OF_SEQ; infer_deBruijn_subst_alt] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[infer_deBruijn_subst_alt];
    X_GEN_TAC `l:t list` THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[infer_deBruijn_subst_alt; injectivity "infer_t"; GSYM MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[]]);;

let env_rel_binding_lemma2 = prove
 (CASE_TERM `!t fvs fvs' subst TC_int.
     check_freevars 0 fvs' t /\
     set_of_list fvs' SUBSET set_of_list fvs /\
     ALL_DISTINCT fvs'
     ==> infer_deBruijn_subst subst
           (infer_type_subst (ZIP fvs (list_of_seq (\x. Infer_Tvar_db x) (LENGTH fvs))) t) =
         infer_deBruijn_subst
           (list_of_seq (\n. infer_deBruijn_subst subst
                               (match find_index (EL n fvs') fvs 0 with
                                  NONE -> Infer_Tapp [] TC_int
                                | SOME k -> Infer_Tvar_db k)) (LENGTH fvs'))
           (infer_type_subst (ZIP fvs' (MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) t)`,
  MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[infer_type_subst_alt; check_freevars_def; LT] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`name:mlstring`; `fvs:mlstring list`; `fvs':mlstring list`;
                         `subst:infer_t list`; `TC_int:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`fvs':mlstring list`;
                   `MAP Infer_Tvar_db (COUNT_LIST (LENGTH (fvs':mlstring list)))`;
                   `name:mlstring`] INFER2AUX_ALOOKUP_ZIP_MEM) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`fvs:mlstring list`;
                   `list_of_seq (\x. Infer_Tvar_db x) (LENGTH (fvs:mlstring list))`;
                   `name:mlstring`] INFER2AUX_ALOOKUP_ZIP_MEM) THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_SET_OF_LIST]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; EL_LIST_OF_SEQ;
                 LENGTH_LIST_OF_SEQ; infer_deBruijn_subst_alt] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[infer_deBruijn_subst_alt];
    X_GEN_TAC `l:t list` THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[infer_deBruijn_subst_alt; injectivity "infer_t"; GSYM MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[]]);;

let unconvert_type_subst = prove
 (`(!t (subst:(mlstring#t)list) fvs.
      check_freevars 0 fvs t /\ set_of_list fvs SUBSET set_of_list (MAP FST subst)
      ==> unconvert_t (type_subst (alist_to_fmap subst) t) =
          infer_type_subst (MAP (\(x,y). (x,unconvert_t y)) subst) t) /\
   (!ts (subst:(mlstring#t)list) fvs.
      ALL (check_freevars 0 fvs) ts /\ set_of_list fvs SUBSET set_of_list (MAP FST subst)
      ==> MAP (unconvert_t o type_subst (alist_to_fmap subst)) ts =
          MAP (infer_type_subst (MAP (\(x,y). (x,unconvert_t y)) subst)) ts)`,
  MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[check_freevars_def; LT; ALL; MAP; type_subst_def; infer_type_subst_alt;
              unconvert_t_def; ALOOKUP_EQ_FLOOKUP; ALOOKUP_MAP; o_THM] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `~(ALOOKUP (subst:(mlstring#t)list) a = NONE)` MP_TAC THENL
     [REWRITE_TAC[ALOOKUP_NONE] THEN ASM_MESON_TAC[SUBSET; IN_SET_OF_LIST]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `ALOOKUP (subst:(mlstring#t)list) a` (cases "option")) THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[];
    REWRITE_TAC[injectivity "infer_t"; GSYM MAP_o] THEN ASM_MESON_TAC[];
    REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]]);;

let INFER2AUX_MAP_PAIR_ZIP = prove
 (`!(f:B->C) (l1:A list) (l2:B list).
     LENGTH l1 = LENGTH l2 ==> MAP (\(x,y). x,f y) (ZIP l1 l2) = ZIP l1 (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; ZIP; MAP; SUC_INJ; CONS_11] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]);;

let INFER2AUX_unconvert_ts = prove
 (`!fvs fvs' t.
     check_freevars 0 fvs' t /\ set_of_list fvs' SUBSET set_of_list fvs
     ==> unconvert_t (type_subst (alist_to_fmap
                       (ZIP fvs (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs))))) t) =
         infer_type_subst (ZIP fvs (list_of_seq (\x. Infer_Tvar_db x) (LENGTH fvs))) t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:t`;
                 `ZIP (fvs:mlstring list) (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs)))`;
                 `fvs':mlstring list`] (CONJUNCT1 unconvert_type_subst)) THEN
  ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP; LENGTH_LIST_OF_SEQ; INFER2AUX_MAP_PAIR_ZIP] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF; unconvert_t_def]);;

let INFER2AUX_erb_approx1 = prove
 (`!fvs fvs' t.
     check_freevars 0 fvs' t /\ set_of_list fvs' SUBSET set_of_list fvs
     ==> tscheme_approx 0 FEMPTY
           (LENGTH (list_nub fvs'),
            infer_type_subst
              (ZIP (list_nub fvs') (MAP Infer_Tvar_db (COUNT_LIST (LENGTH (list_nub fvs'))))) t)
           (LENGTH fvs,
            unconvert_t (type_subst (alist_to_fmap
              (ZIP fvs (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs))))) t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`fvs:mlstring list`; `fvs':mlstring list`; `t:t`] INFER2AUX_unconvert_ts) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[tscheme_approx_def; t_walkstar_FEMPTY; ADD_CLAUSES; FDOM_FEMPTY] THEN
  EXISTS_TAC (CASE_TERM
    `list_of_seq (\n. match find_index (EL n fvs) (list_nub fvs') 0 with
                        NONE -> Infer_Tapp [] Tint_num
                      | SOME k -> Infer_Tvar_db k) (LENGTH (fvs:mlstring list))`) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; EVERY_GENLIST] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`list_nub fvs':mlstring list`; `EL i (fvs:mlstring list)`; `0`]
      find_index_LESS_LENGTH) THEN
    STRUCT_CASES_TAC(ISPEC `find_index (EL i (fvs:mlstring list)) (list_nub fvs') 0`
      (cases "option")) THEN
    CASE_REWRITE_TAC[check_t_def; ALL; option_INJ] THEN
    MESON_TAC[ARITH_RULE `0 <= a /\ a < 0 + b ==> a < b`];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  MATCH_MP_TAC env_rel_binding_lemma THEN REWRITE_TAC[all_distinct_nub; nub_set] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MATCH_MP check_freevars_more
    (ASSUME `check_freevars 0 fvs' t`)) THEN
  REWRITE_TAC[nub_set; SUBSET_REFL]);;

let INFER2AUX_erb_approx2 = prove
 (`!fvs fvs' t.
     check_freevars 0 fvs' t /\ set_of_list fvs' SUBSET set_of_list fvs
     ==> tscheme_approx 0 FEMPTY
           (LENGTH fvs,
            unconvert_t (type_subst (alist_to_fmap
              (ZIP fvs (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs))))) t))
           (LENGTH (list_nub fvs'),
            infer_type_subst
              (ZIP (list_nub fvs') (MAP Infer_Tvar_db (COUNT_LIST (LENGTH (list_nub fvs'))))) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`fvs:mlstring list`; `fvs':mlstring list`; `t:t`] INFER2AUX_unconvert_ts) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[tscheme_approx_def; t_walkstar_FEMPTY; ADD_CLAUSES; FDOM_FEMPTY] THEN
  EXISTS_TAC (CASE_TERM
    `list_of_seq (\n. match find_index (EL n (list_nub fvs')) fvs 0 with
                        NONE -> Infer_Tapp [] Tint_num
                      | SOME k -> Infer_Tvar_db k) (LENGTH (list_nub (fvs':mlstring list)))`) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; EVERY_GENLIST] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`fvs:mlstring list`; `EL i (list_nub fvs':mlstring list)`; `0`]
      find_index_LESS_LENGTH) THEN
    STRUCT_CASES_TAC(ISPEC `find_index (EL i (list_nub fvs':mlstring list)) fvs 0`
      (cases "option")) THEN
    CASE_REWRITE_TAC[check_t_def; ALL; option_INJ] THEN
    MESON_TAC[ARITH_RULE `0 <= a /\ a < 0 + b ==> a < b`];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  MATCH_MP_TAC env_rel_binding_lemma2 THEN REWRITE_TAC[all_distinct_nub; nub_set] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MATCH_MP check_freevars_more
    (ASSUME `check_freevars 0 fvs' t`)) THEN
  REWRITE_TAC[nub_set; SUBSET_REFL]);;

let env_rel_binding = prove
 (`!fvs t fvs' name.
     check_freevars 0 fvs' t /\ set_of_list fvs' SUBSET set_of_list fvs
     ==> envRel_env_rel
           (type_env_REC
              (nsSing name
                 (LENGTH fvs,
                  type_subst
                    (alist_to_fmap (ZIP fvs (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs)))))
                    t))
              nsEmpty nsEmpty)
           (inf_env_REC
              (nsSing name
                 (LENGTH (list_nub fvs'),
                  infer_type_subst
                    (ZIP (list_nub fvs') (MAP Infer_Tvar_db (COUNT_LIST (LENGTH (list_nub fvs')))))
                    t))
              nsEmpty nsEmpty)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `check_freevars 0 (list_nub fvs') t` ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP check_freevars_more (ASSUME `check_freevars 0 fvs' t`)) THEN
    REWRITE_TAC[nub_set; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `check_freevars (LENGTH fvs) []
       (type_subst (alist_to_fmap (ZIP fvs (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs))))) t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC check_freevars_subst_single THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ; ALL_MAP; o_DEF; EVERY_GENLIST;
                check_freevars_def] THEN
    SIMP_TAC[] THEN
    MATCH_MP_TAC(MATCH_MP check_freevars_more
      (MATCH_MP (MATCH_MP check_freevars_add (ASSUME `check_freevars 0 fvs' t`))
         (ARITH_RULE `LENGTH (fvs:mlstring list) >= 0`))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `check_t (LENGTH (list_nub fvs')) {}
       (infer_type_subst (ZIP (list_nub fvs') (MAP Infer_Tvar_db (COUNT_LIST (LENGTH (list_nub fvs'))))) t)`
    ASSUME_TAC THENL
   [ASM_CASES_TAC `list_nub (fvs':mlstring list) = []` THENL
     [ASM_REWRITE_TAC[LENGTH; COUNT_LIST_def; MAP; ZIP] THEN
      MATCH_MP_TAC(CONJUNCT1 infer_type_subst_empty_check) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC check_t_infer_type_subst_dbs THEN
      MAP_EVERY EXISTS_TAC [`0`; `list_nub fvs':mlstring list`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[envRel_env_rel_def; ienv_ok_def; ienv_val_ok_def; tenv_ok_def; tenv_val_ok_def;
              env_rel_sound_def; env_rel_complete_def; inf_env_INFO.ri_accessors;
              type_env_INFO.ri_accessors; nsAll_nsSing; nsLookup_nsSing; nsLookupMod_nsSing;
              tenv_ctor_ok_nsEmpty; tenv_abbrev_ok_def; nsAll_nsEmpty] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT];
    MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `ts:num#infer_t`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN
    CASE_REWRITE_TAC[tveLookup_def; nsLookup_nsSing; num_tvs_def; type_env_INFO.ri_accessors] THEN
    MAP_EVERY EXISTS_TAC [`LENGTH (fvs:mlstring list)`;
      `type_subst (alist_to_fmap (ZIP fvs (MAP Tvar_db (list_of_seq (\x. x) (LENGTH fvs)))))
         t`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC INFER2AUX_erb_approx1 THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `tvs:num`; `tt:t`] THEN
    REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN
    MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[tveLookup_def; nsLookup_nsSing; num_tvs_def; type_env_INFO.ri_accessors] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`LENGTH (list_nub fvs':mlstring list)`;
      `infer_type_subst
         (ZIP (list_nub fvs') (MAP Infer_Tvar_db (COUNT_LIST (LENGTH (list_nub fvs'))))) t`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INFER2AUX_erb_approx2 THEN ASM_REWRITE_TAC[]]);;

(* HOL4 [local] env_rel_complete_bind *)
let inferComplete_env_rel_complete_bind = prove
 (`!ienv tenv tvs.
     env_rel_complete FEMPTY ienv tenv Empty
     ==> env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFER1AUX_erc_bind_tvar THEN
  ASM_REWRITE_TAC[t_wfs_FEMPTY]);;

let INFER2AUX_ALL_PAIR_CONJ = prove
 (`!(P:B->bool) (Q:B->bool) (l:(A#B)list).
     ALL (P o SND) l /\ ALL (\(x,y). Q y) l ==> ALL (\(x,y). P y /\ Q y) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]);;

let INFER2AUX_convert_env_set_tids = prove
 (`!tids sx (bindings:(mlstring#infer_t)list) m.
     t_wfs sx /\ inf_set_tids_subst tids sx /\
     ALL (\(x,tt). inf_set_tids_subset tids tt /\ check_t m {} (t_walkstar sx tt)) bindings
     ==> ALL (\(k,t). set_tids_subset tids t) (convert_env sx bindings)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[convert_env_def; ALL_MAP; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> INFER1AUX_is_app "ALL" (concl th))) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `tt:infer_t`] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN REWRITE_TAC[set_tids_subset_def; GSYM inf_set_tids_unconvert] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP check_t_empty_unconvert_convert_id) THEN
  REWRITE_TAC[GSYM inf_set_tids_subset_def] THEN
  MATCH_MP_TAC t_walkstar_set_tids THEN
  MAP_EVERY EXISTS_TAC [`sx:(num,infer_t)fmap`; `tt:infer_t`] THEN ASM_REWRITE_TAC[]);;

let type_pe_determ_canon_infer_e = prove
 (`!loc ienv p e st st' t t' new_bindings s tenv ss.
     ALL_DISTINCT (MAP FST new_bindings) /\
     env_rel_sound FEMPTY ienv tenv Empty /\
     ienv_ok {} ienv /\
     start_type_id <= infer_st_next_id ss /\
     inf_set_tids_ienv (pred_set_count (infer_st_next_id ss)) ienv /\
     infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
     infer_p loc ienv p st = (M_success (t',new_bindings),st') /\
     t_unify (infer_st_subst st') t t' = SOME s /\
     type_pe_determ_canon (infer_st_next_id ss) tenv Empty p e
     ==> ALL (\(n:mlstring,t). check_t 0 {} (t_walkstar s t)) new_bindings`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `infer_st_next_uvar (init_infer_state ss) = 0 /\
                infer_st_subst (init_infer_state ss) = FEMPTY` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `ienv_val_ok (pred_set_count 0) (inf_env_inf_v ienv) /\
                tenv_ctor_ok (inf_env_inf_c ienv) /\ tenv_abbrev_ok (inf_env_inf_t ienv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN REWRITE_TAC[ienv_ok_def; COUNT_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv /\ inf_env_inf_c ienv = type_env_c tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_sound_def]; ALL_TAC] THEN
  (* well-formedness and closedness of the inferred substitutions and types *)
  SUBGOAL_THEN `t_wfs (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `new_bindings:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `infer_st_next_uvar st <= infer_st_next_uvar st'` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_next_uvar_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st)) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st)) (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY; check_s_def; FDOM_FEMPTY; NOT_IN_EMPTY; COUNT_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st')) (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `new_bindings:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_check_t)
    (ASSUME `infer_p loc ienv p st = (M_success (t',new_bindings),st')`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more4)
      (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st)) t`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st')) s` ASSUME_TAC THENL
   [MATCH_MP_TAC t_unify_check_s THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'`; `t:infer_t`; `t':infer_t`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar s t = t_walkstar s t'` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_unifier]; ALL_TAC] THEN
  (* the unconstrained variables, and two completions instantiating them differently *)
  SUBGOAL_THEN `?l. set_of_list l =
                    pred_set_count (infer_st_next_uvar st') DIFF FDOM (s:(num,infer_t)fmap) /\
                    ALL_DISTINCT l` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `list_of_set (pred_set_count (infer_st_next_uvar st') DIFF FDOM (s:(num,infer_t)fmap))` THEN
    SIMP_TAC[SET_OF_LIST_OF_SET; FMAPAUX_ALL_DISTINCT_LIST_OF_SET; FINITE_DIFF; FINITE_COUNT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `infer_st_next_uvar st'`; `l:num list`; `Tbool_num`]
    INFER1AUX_const_completion) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s1 = (s:(num,infer_t)fmap) |++ MAP (\m. (m,Infer_Tapp [] Tbool_num)) l` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `infer_st_next_uvar st'`; `l:num list`; `Tint_num`]
    INFER1AUX_const_completion) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s2 = (s:(num,infer_t)fmap) |++ MAP (\m. (m,Infer_Tapp [] Tint_num)) l` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap) /\ t_wfs (s2:(num,infer_t)fmap) /\
                t_compat s s1 /\ t_compat s s2` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  (* the soundness of inference for any completion of s *)
  SUBGOAL_THEN
    `!sx csx. sub_completion 0 (infer_st_next_uvar st') s csx sx
              ==> type_e tenv Empty e (convert_t (t_walkstar sx t)) /\
                  type_p 0 tenv p (convert_t (t_walkstar sx t)) (convert_env sx new_bindings)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `t_wfs (sx:(num,infer_t)fmap) /\ t_compat s sx` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
      ASM_MESON_TAC[pure_add_constraints_success];
      ALL_TAC] THEN
    SUBGOAL_THEN `t_walkstar sx t = t_walkstar sx t'` ASSUME_TAC THENL
     [UNDISCH_TAC `t_compat s (sx:(num,infer_t)fmap)` THEN REWRITE_TAC[t_compat_def] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sub_completion 0 (infer_st_next_uvar st') (infer_st_subst st')
                    (CONS (t,t') csx) sx` ASSUME_TAC THENL
     [MATCH_MP_TAC sub_completion_unify2 THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP (CONJUNCT1 infer_p_constraints)
      (ASSUME `infer_p loc ienv p st = (M_success (t',new_bindings),st')`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `ts:(infer_t#infer_t)list`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 infer_e_sound) THEN
      MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `init_infer_state ss`;
                            `st:infer_st`; `APPEND ts (CONS (t:infer_t,t':infer_t) csx)`] THEN
      ASM_REWRITE_TAC[COUNT_ZERO; t_wfs_FEMPTY; num_tvs_def] THEN CONJ_TAC THENL
       [MATCH_MP_TAC env_rel_sound_weaken THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC sub_completion_add_constraints THEN
      EXISTS_TAC `infer_st_subst st'` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `sub_completion 0 (infer_st_next_uvar st') (infer_st_subst st')
                     (CONS (t,t') csx) sx` THEN
      REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `t_walkstar sx t = t_walkstar sx t'`)) THEN
      MATCH_MP_TAC(CONJUNCT1 infer_p_sound) THEN
      MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `st:infer_st`; `st':infer_st`;
                            `CONS (t:infer_t,t':infer_t) csx`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the type identifiers of the inferred types are below next_id *)
  ABBREV_TAC `tids = pred_set_count (infer_st_next_id ss)` THEN
  SUBGOAL_THEN `prim_tids T tids` ASSUME_TAC THENL
   [EXPAND_TAC "tids" THEN MATCH_MP_TAC start_type_id_prim_tids_count THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `tids:num->bool` infer_e_inf_set_tids) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME
    `infer_e loc ienv e (init_infer_state ss) = (M_success t,st)`)) THEN
  ASM_REWRITE_TAC[t_wfs_FEMPTY; inf_set_tids_subst_def; FRANGE_FEMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM inf_set_tids_subst_def] THEN STRIP_TAC THEN
  MP_TAC(SPEC `tids:num->bool` infer_p_inf_set_tids) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME
    `infer_p loc ienv p st = (M_success (t',new_bindings),st')`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inf_set_tids_subst tids (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [MP_TAC(SPEC `tids:num->bool` t_unify_set_tids) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPECL [`infer_st_subst st'`; `t:infer_t`; `t':infer_t`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inf_set_tids_subst tids (s1:(num,infer_t)fmap) /\
                inf_set_tids_subst tids (s2:(num,infer_t)fmap)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC pure_add_constraints_set_tids THEN
    EXISTS_TAC `s:(num,infer_t)fmap` THENL
     [EXISTS_TAC `MAP (\m. (Infer_Tuvar m,Infer_Tapp [] Tbool_num)) l`;
      EXISTS_TAC `MAP (\m. (Infer_Tuvar m,Infer_Tapp [] Tint_num)) l`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAP_MAP_o; o_DEF; ALL_MAP; GSYM ALL_MEM; inf_set_tids_subset_def;
                inf_set_tids_def; MAP; set_of_list; UNIONS_0; EMPTY_SUBSET] THEN
    UNDISCH_TAC `prim_tids T tids` THEN
    REWRITE_TAC[prim_tids_def; ALL; prim_type_nums_def; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* the inferred types of the bindings are closed by any completion of s *)
  SUBGOAL_THEN `!sx csx. sub_completion 0 (infer_st_next_uvar st') s csx sx /\
                         check_s 0 (pred_set_count (infer_st_next_uvar st')) sx
                         ==> ALL (\(x:mlstring,tt). check_t 0 {} (t_walkstar sx tt))
                                 new_bindings` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (pred_set_count (infer_st_next_uvar st')) t)
                     new_bindings` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    X_GEN_TAC `tt:infer_t` THEN DISCH_TAC THEN
    MATCH_MP_TAC t_walkstar_check THEN REWRITE_TAC[UNION_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[pure_add_constraints_wfs];
      MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt`)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\(x:mlstring,tt). check_t 0 {} (t_walkstar s1 tt)) new_bindings /\
                ALL (\(x:mlstring,tt). check_t 0 {} (t_walkstar s2 tt)) new_bindings`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [EXISTS_TAC `MAP (\m. (Infer_Tuvar m,Infer_Tapp [] Tbool_num)) l`;
      EXISTS_TAC `MAP (\m. (Infer_Tuvar m,Infer_Tapp [] Tint_num)) l`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL (\(k:mlstring,t). set_tids_subset tids t) (convert_env s1 new_bindings) /\
     ALL (\(k:mlstring,t). set_tids_subset tids t) (convert_env s2 new_bindings)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INFER2AUX_convert_env_set_tids THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER2AUX_ALL_PAIR_CONJ THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the two typings, and determinism *)
  SUBGOAL_THEN
    `convert_env s1 (new_bindings:(mlstring#infer_t)list) = convert_env s2 new_bindings`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun ih ->
      if is_forall(concl ih) &&
         (try fst(dest_var(fst(dest_forall(concl ih)))) = "sx" with Failure _ -> false)
      then MAP_EVERY (fun v -> FIRST_ASSUM(fun sc ->
             if INFER1AUX_is_app "sub_completion" (concl sc) && rand(concl sc) = v &&
                rand(rator(rator(concl sc))) = `s:(num,infer_t)fmap`
             then MP_TAC(MATCH_MP ih sc) else failwith ""))
             [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`]
      else failwith "") THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[type_pe_determ_canon_def] o
      check (fun th -> INFER1AUX_is_app "type_pe_determ_canon" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`convert_t (t_walkstar s1 t)`; `convert_t (t_walkstar s2 t)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:mlstring`; `tt:infer_t`] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_CASES_TAC `check_t 0 {} (t_walkstar s tt)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (pred_set_count (infer_st_next_uvar st')) t)
                     new_bindings` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(x:mlstring,tt:infer_t)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) (t_walkstar s tt)` ASSUME_TAC THENL
   [MATCH_MP_TAC t_walkstar_check THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt`)) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `t_walkstar s tt` (CONJUNCT1 (INST [`pred_set_count (infer_st_next_uvar st')`,`s:num->bool`]
    t_vars_check_t))) THEN
  ASM_REWRITE_TAC[IN_COUNT] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `MEM (n':num) l` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[IN_DIFF; IN_COUNT] THEN
    MATCH_MP_TAC(MATCH_MP t_walkstar_vars_notin (ASSUME `t_wfs (s:(num,infer_t)fmap)`)) THEN
    EXISTS_TAC `tt:infer_t` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`; `n':num`] t_walkstar_diff) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[injectivity "infer_t"; typeSystem_Tbool_num_def; typeSystem_Tint_num_def] THEN
    ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `t_walkstar s tt` o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!sx. t_compat s sx ==> t_walkstar sx (t_walkstar s tt) = t_walkstar sx tt`
    (fun th -> ASM_SIMP_TAC[th]) THENL
   [SIMP_TAC[t_compat_def]; ALL_TAC] THEN
  SUBGOAL_THEN `!sx csx. sub_completion 0 (infer_st_next_uvar st') s csx sx /\
                         check_s 0 (pred_set_count (infer_st_next_uvar st')) sx
                         ==> check_t 0 {} (t_walkstar sx tt)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN
    MATCH_MP_TAC t_walkstar_check THEN REWRITE_TAC[UNION_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[pure_add_constraints_wfs];
      MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5)
        (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st')) tt`)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 {} (t_walkstar s1 tt) /\ check_t 0 {} (t_walkstar s2 tt)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convert_t (t_walkstar s1 tt) = convert_t (t_walkstar s2 tt)` MP_TAC THENL
   [UNDISCH_TAC
      `convert_env s1 (new_bindings:(mlstring#infer_t)list) = convert_env s2 new_bindings` THEN
    REWRITE_TAC[convert_env_def; MAP_EQ_f] THEN
    DISCH_THEN(MP_TAC o SPEC `(x:mlstring,tt:infer_t)`) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `unconvert_t`) THEN
  MP_TAC(SPECL [`t_walkstar s1 tt`; `0`] check_t_empty_unconvert_convert_id) THEN
  MP_TAC(SPECL [`t_walkstar s2 tt`; `0`] check_t_empty_unconvert_convert_id) THEN
  ASM_SIMP_TAC[]);;


(* HOL4: fun str_assums is an ML tactic (not ported; its one use below is AP_TERM). *)

(* HOL4 [local] *)
let ap_lemma = prove
 (`!(f:A->B) (x:A) y. x = y ==> f x = f y`,
  MESON_TAC[]);;

let INFER2AUX_inf_set_tids_subset_mono = prove
 (`!m n t. inf_set_tids_subset (pred_set_count m) t /\ m <= n ==> inf_set_tids_subset (pred_set_count n) t`,
  REWRITE_TAC[inf_set_tids_subset_def; SUBSET; IN_COUNT] THEN
  MESON_TAC[LTE_TRANS]);;

let inf_set_tids_extend_dec_ienv = prove
 (`!n m ienv2 ienv.
     inf_set_tids_ienv (pred_set_count n) ienv2 /\ inf_set_tids_ienv (pred_set_count m) ienv /\ m <= n
     ==> inf_set_tids_ienv (pred_set_count n) (extend_dec_ienv ienv2 ienv)`,
  REWRITE_TAC[inf_set_tids_ienv_def; extend_dec_ienv_def; inf_env_INFO.ri_accessors] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC nsAll_mono) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[INFER2AUX_inf_set_tids_subset_mono; ALL_MEM; IN_COUNT; LTE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Evaluating the inferencer's monadic code on known successful steps.       *)
(* ------------------------------------------------------------------------- *)

let INFER2AUX_bind_succ = prove
 (`!(x:S->(A,E)exc#S) (f:A->S->(B,E)exc#S) st y st'.
     x st = (M_success y,st') ==> st_ex_bind x f st = f y st'`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[st_ex_bind_def] THEN CASE_REWRITE_TAC[]);;

let INFER2AUX_ibind_succ = prove
 (`!(x:S->(A,E)exc#S) (f:S->(B,E)exc#S) st y st'.
     x st = (M_success y,st') ==> st_ex_ignore_bind x f st = f st'`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[st_ex_ignore_bind_def] THEN CASE_REWRITE_TAC[]);;

(* one step of evaluation: the goal is  st_ex_bind x f st = r  (or           *)
(* st_ex_ignore_bind), x st is computed by rewriting with thl and the        *)
(* assumptions to M_success y,st', and the goal becomes  f y st' = r         *)
let INFER2AUX_BIND_TAC (thl:thm list) : tactic =
  fun (asl,w as g) ->
    let l = lhs w in
    let h,args = strip_comb l in
    let n = try fst(dest_const h) with Failure _ -> "" in
    if (n = "st_ex_bind" || n = "st_ex_ignore_bind") && length args = 3 then
      let x = el 0 args and st = el 2 args in
      let th = (REWRITE_CONV (thl @ map snd asl) THENC CASE_REWRITE_CONV []) (mk_comb(x,st)) in
      let lem = if n = "st_ex_bind" then INFER2AUX_bind_succ else INFER2AUX_ibind_succ in
      let th2 = MATCH_MP lem th in
      (GEN_REWRITE_TAC LAND_CONV [th2] THEN
       CONV_TAC(LAND_CONV(TOP_DEPTH_CONV GEN_BETA_CONV THENC CASE_REWRITE_CONV []))) g
    else failwith "INFER2AUX_BIND_TAC";;

let INFER2AUX_init_infer_state = prove
 (`!st. infer_st_next_uvar (init_infer_state st) = 0 /\
        infer_st_subst (init_infer_state st) = FEMPTY /\
        infer_st_next_id (init_infer_state st) = infer_st_next_id st`,
  REWRITE_TAC[init_infer_state_def; infer_st_INFO.ri_accfupds; K_THM]);;

let INFER2AUX_infer_d_Dlet = prove
 (`!ienv locs p e st1 t st t' nb st' s ntvs smap ts'.
     infer_e (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv e
       (init_infer_state st1) = (M_success t,st) /\
     infer_p (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv p st =
       (M_success (t',nb),st') /\
     ALL_DISTINCT (MAP FST nb) /\
     t_unify (infer_st_subst st') t t' = SOME s /\
     generalise_list 0 0 FEMPTY (MAP (t_walkstar s) (MAP SND nb)) = (ntvs,smap,ts') /\
     (ntvs = 0 \/ is_value e)
     ==> infer_d ienv (Dlet locs p e) st1 =
         (M_success (inf_env_REC (alist_to_ns (ZIP (MAP FST nb) (MAP (\t. (ntvs,t)) ts')))
                       nsEmpty nsEmpty),
          infer_st_subst_fupd (K s) st')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[infer_d_def] THEN
  INFER2AUX_BIND_TAC[init_state_def] THEN
  INFER2AUX_BIND_TAC[get_next_uvar_def; INFER2AUX_init_infer_state] THEN
  INFER2AUX_BIND_TAC[] THEN INFER2AUX_BIND_TAC[] THEN
  FIRST_ASSUM(fun th -> INFER2AUX_BIND_TAC[MATCH_MP INFER1AUX_check_dups_ok th]) THEN
  INFER2AUX_BIND_TAC[add_constraint_def] THEN
  INFER2AUX_BIND_TAC[apply_subst_list_def; st_ex_bind_def; infer_read_def; st_ex_return_def;
                     infer_st_INFO.ri_accfupds; K_THM] THEN
  INFER2AUX_BIND_TAC[st_ex_return_def] THEN
  REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  INFER2AUX_BIND_TAC[infer_guard_def; st_ex_return_def] THEN
  REWRITE_TAC[st_ex_return_def]);;

(* ------------------------------------------------------------------------- *)
(* The environment relation for a list of new bindings.                     *)
(* ------------------------------------------------------------------------- *)

let INFER2AUX_ALOOKUP_ZIP_DISTINCT = prove
 (`!(keys:A list) (vals:B list) x v.
     ALL_DISTINCT keys /\ LENGTH vals = LENGTH keys
     ==> (ALOOKUP (ZIP keys vals) x = SOME v <=>
          ?k. k < LENGTH keys /\ x = EL k keys /\ v = EL k vals)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`ZIP (keys:A list) (vals:B list)`; `k:num`] ALOOKUP_ALL_DISTINCT_EL) THEN
    ASM_SIMP_TAC[LENGTH_ZIP; MAP_ZIP; EL_ZIP]]);;

let INFER2AUX_nsLookup_ZIP = prove
 (`!(names:mlstring list) (vals:B list) x v.
     ALL_DISTINCT names /\ LENGTH vals = LENGTH names
     ==> (nsLookup (alist_to_ns (ZIP names vals):(mlstring,mlstring,B)namespace) x = SOME v <=>
          ?k. k < LENGTH names /\ x = Short (EL k names) /\ v = EL k vals)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nsLookup_alist_to_ns_some] THEN
  ASM_SIMP_TAC[INFER2AUX_ALOOKUP_ZIP_DISTINCT] THEN MESON_TAC[]);;

let INFER2AUX_env_rel_bindings = prove
 (`!(names:mlstring list) (tss:infer_t list) (cts:t list) ntvs tvs.
     ALL_DISTINCT names /\ LENGTH tss = LENGTH names /\ LENGTH cts = LENGTH names /\
     (!k. k < LENGTH names
          ==> check_t ntvs {} (EL k tss) /\ check_freevars tvs [] (EL k cts) /\
              tscheme_approx 0 FEMPTY (ntvs,EL k tss) (tvs,unconvert_t (EL k cts)) /\
              tscheme_approx 0 FEMPTY (tvs,unconvert_t (EL k cts)) (ntvs,EL k tss))
     ==> envRel_env_rel
           (type_env_REC (alist_to_ns (ZIP names (MAP (\t. (tvs,t)) cts))) nsEmpty nsEmpty)
           (inf_env_REC (alist_to_ns (ZIP names (MAP (\t. (ntvs,t)) tss))) nsEmpty nsEmpty)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[envRel_env_rel_def; ienv_ok_def; ienv_val_ok_def; tenv_ok_def; tenv_val_ok_def;
              env_rel_sound_def; env_rel_complete_def; inf_env_INFO.ri_accessors;
              type_env_INFO.ri_accessors; tenv_ctor_ok_nsEmpty; tenv_abbrev_ok_def;
              nsAll_nsEmpty; INFER1AUX_lookup_var_Empty; num_tvs_def; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[nsAll_def; INFER2AUX_nsLookup_ZIP; LENGTH_MAP] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[EL_MAP] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[EL_MAP] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    GEN_TAC THEN MP_TAC(ISPEC `x:mlstring list` list_CASES) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[nsLookupMod_alist_to_ns] THEN
    REWRITE_TAC[nsLookupMod_def; option_DISTINCT];
    MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `ts:num#infer_t`] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`tvs:num`; `EL k (cts:t list)`] THEN
    ASM_SIMP_TAC[EL_MAP] THEN EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[EL_MAP];
    MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `tvs0:num`; `t0:t`] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_pair(lhs(concl th)))) THEN
    ASM_SIMP_TAC[EL_MAP; PAIR_EQ] THEN STRIP_TAC THEN
    CONJ_TAC THENL [EXISTS_TAC `tvs:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ntvs:num`; `EL k (tss:infer_t list)`] THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[EL_MAP]]);;

(* walking an inferred type with a checked substitution keeps it checked *)
let INFER2AUX_walkstar_check_count = prove
 (`!s nu t. t_wfs s /\ check_s 0 (pred_set_count nu) s /\ check_t 0 (pred_set_count nu) t
            ==> check_t 0 (pred_set_count nu) (t_walkstar s t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC t_walkstar_check THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC check_s_more5 THEN EXISTS_TAC `pred_set_count nu` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5) (ASSUME `check_t 0 (pred_set_count nu) t`)) THEN
    SET_TAC[]]);;

(* a completion of a substitution closes the types over its domain *)
let INFER2AUX_completion_closed = prove
 (`!tvs nu s ec sx t.
     t_wfs s /\ sub_completion tvs nu s ec sx /\ check_t 0 (pred_set_count nu) t
     ==> check_t tvs {} (t_walkstar sx t)`,
  REWRITE_TAC[sub_completion_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (sx:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MP_TAC(SPECL [`sx:(num,infer_t)fmap`; `tvs:num`; `pred_set_count nu`] check_t_less) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:infer_t` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `pred_set_count nu SUBSET FDOM (sx:(num,infer_t)fmap)` THEN
  REWRITE_TAC[COMPL_DEF] THEN SET_TAC[]);;

let INFER2AUX_t_vars_UNIONS = prove
 (`!(f:infer_t->infer_t) (l:infer_t list) k x.
     k < LENGTH l /\ x IN t_vars (f (EL k l))
     ==> x IN UNIONS (set_of_list (MAP t_vars (MAP f l)))`,
  REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[MEM_EL]);;
let INFER2AUX_gen_complete_inst = prove
 (`!s sc tvs nu constrs (l:infer_t list) ntvs smap ts'.
     t_wfs s /\ sub_completion tvs nu s constrs sc /\
     check_s 0 (pred_set_count nu) s /\ ALL (check_t 0 (pred_set_count nu)) l /\
     generalise_list 0 0 FEMPTY (MAP (t_walkstar s) l) = (ntvs,smap,ts')
     ==> LENGTH ts' = LENGTH l /\
         !k. k < LENGTH l
             ==> check_t ntvs {} (EL k ts') /\
                 tscheme_inst (tvs,convert_t (t_walkstar sc (EL k l)))
                              (ntvs,convert_t (EL k ts'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (ts':infer_t list) = LENGTH (l:infer_t list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP generalise_list_length) THEN REWRITE_TAC[LENGTH_MAP];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`0`; `s:(num,infer_t)fmap`; `l:infer_t list`; `ntvs:num`;
                `smap:(num,num)fmap`; `ts':infer_t list`; `nu:num`; `0`;
                `{}:num->bool`] generalise_complete) THEN
  ASM_REWRITE_TAC[ETA_AX; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec1:(infer_t#infer_t)list`
    (X_CHOOSE_THEN `last_sub:(num,infer_t)fmap` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`MAP (t_walkstar s) (l:infer_t list)`; `0`; `0`; `FEMPTY:(num,num)fmap`;
                `ntvs:num`; `smap:(num,num)fmap`; `ts':infer_t list`]
    (CONJUNCT2 generalise_subst)) THEN
  ASM_REWRITE_TAC[FDOM_FEMPTY; UNION_EMPTY; DIFF_EMPTY; LE_0; ADD_CLAUSES;
                  infer_subst_FEMPTY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (sc:(num,infer_t)fmap) /\ (s:(num,infer_t)fmap) SUBMAP sc /\
                pred_set_count nu SUBSET FDOM sc /\
                (!uv. uv IN FDOM sc ==> check_t tvs {} (t_walkstar sc (Infer_Tuvar uv)))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sub_completion tvs nu s constrs sc` THEN REWRITE_TAC[sub_completion_def] THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (pred_set_count nu)) (MAP (t_walkstar s) (l:infer_t list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[ALL_MAP; o_DEF] THEN
    UNDISCH_TAC `ALL (check_t 0 (pred_set_count nu)) (l:infer_t list)` THEN
    MATCH_MP_TAC MONO_ALL THEN ASM_MESON_TAC[INFER2AUX_walkstar_check_count];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sc:(num,infer_t)fmap`; `tvs:num`] generalise_subst_exist) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`MAP (t_walkstar s) (l:infer_t list)`; `[]:infer_t list`; `0`;
                             `FEMPTY:(num,num)fmap`; `ntvs:num`; `smap:(num,num)fmap`;
                             `ts':infer_t list`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[LENGTH; FRANGE_FEMPTY; EMPTY_SUBSET; MEM; FDOM_FEMPTY; NOT_IN_EMPTY;
                  APPEND] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ALL (check_t 0 (pred_set_count nu)) (MAP (t_walkstar s) (l:infer_t list))` THEN
      MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP check_t_t_vars) THEN ASM SET_TAC[];
      UNDISCH_TAC `ALL (check_t 0 (pred_set_count nu)) (MAP (t_walkstar s) (l:infer_t list))` THEN
      MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5) (ASSUME `check_t 0 (pred_set_count nu) x`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subst':infer_t list` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `check_t ntvs {} (EL k (ts':infer_t list))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EL_MAP] THEN MATCH_MP_TAC INFER2AUX_completion_closed THEN
    MAP_EVERY EXISTS_TAC [`nu:num`; `s:(num,infer_t)fmap`; `ec1:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (check_t 0 (pred_set_count nu)) (l:infer_t list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
SUBGOAL_THEN `EL k (MAP (t_walkstar last_sub) l) =
                infer_subst smap (t_walkstar s (EL k (l:infer_t list)))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `EL k:infer_t list->infer_t` o check (fun th ->
      is_eq(concl th) && can (find_term (fun t -> t = `infer_subst smap`)) (lhs(concl th)))) THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[tscheme_inst_def] THEN EXISTS_TAC `MAP convert_t (subst':infer_t list)` THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC check_t_to_check_freevars THEN ASM_MESON_TAC[];
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    ASM_MESON_TAC[check_t_to_check_freevars];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ntvs:num`; `subst':infer_t list`] deBruijn_subst_convert) THEN
  DISCH_THEN(MP_TAC o SPEC `infer_subst smap (t_walkstar s (EL k (l:infer_t list)))` o
    CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`sc:(num,infer_t)fmap`; `smap:(num,num)fmap`; `subst':infer_t list`; `0`;
                `pred_set_count nu`] infer_deBruijn_subst_infer_subst_walkstar) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_FRANGE; IN_COUNT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t_walkstar s (EL k (l:infer_t list))` o CONJUNCT1) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC INFER2AUX_t_vars_UNIONS THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ALL (check_t 0 (pred_set_count nu)) (MAP (t_walkstar s) (l:infer_t list))` THEN
      ASM_SIMP_TAC[GSYM ALL_EL; LENGTH_MAP; EL_MAP];
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC INFER2AUX_t_vars_UNIONS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_MESON_TAC[t_walkstar_SUBMAP]);;

(* ------------------------------------------------------------------------- *)
(* The cases of infer_d_complete_canon.                                      *)
(* ------------------------------------------------------------------------- *)

(* basic facts about a successful inference of an expression and a pattern *)
let INFER2AUX_pe_facts = prove
 (`!loc ienv e p ss t st t' nb st' s.
     ienv_ok {} ienv /\
     infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
     infer_p loc ienv p st = (M_success (t',nb),st') /\
     t_unify (infer_st_subst st') t t' = SOME s
     ==> t_wfs (infer_st_subst st) /\ t_wfs (infer_st_subst st') /\ t_wfs s /\
         infer_st_next_uvar st <= infer_st_next_uvar st' /\
         check_t 0 (pred_set_count (infer_st_next_uvar st')) t /\
         check_t 0 (pred_set_count (infer_st_next_uvar st')) t' /\
         check_s 0 (pred_set_count (infer_st_next_uvar st')) (infer_st_subst st') /\
         check_s 0 (pred_set_count (infer_st_next_uvar st')) s /\
         ALL (\(x:mlstring,t). check_t 0 (pred_set_count (infer_st_next_uvar st')) t) nb /\
         infer_st_next_id st' = infer_st_next_id ss /\
         pat_bindings p = MAP FST nb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ienv_ok_def]) THEN
  MP_TAC(SPEC `ss:infer_st` INFER2AUX_init_infer_state) THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `nb:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (s:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `infer_st_next_uvar st <= infer_st_next_uvar st'` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_next_uvar_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st)) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`] THEN
    ASM_REWRITE_TAC[COUNT_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st)) (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY; check_s_def; FDOM_FEMPTY; NOT_IN_EMPTY; COUNT_ZERO;
                    ienv_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (pred_set_count (infer_st_next_uvar st')) (infer_st_subst st')` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_check_s) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `nb:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_check_t)
    (ASSUME `infer_p loc ienv p st = (M_success (t',nb),st')`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count (infer_st_next_uvar st')) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more4)
      (ASSUME `check_t 0 (pred_set_count (infer_st_next_uvar st)) t`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC t_unify_check_s THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'`; `t:infer_t`; `t':infer_t`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[infer_e_next_id_const; infer_p_next_id_const];
    ASM_MESON_TAC[infer_p_bindings]]);;

(* the inferred types are sound for every completion of the unifier *)
let INFER2AUX_pe_sound_completion = prove
 (`!loc ienv tenv e p ss t st t' nb st' s tvs' csx sx.
     ienv_ok {} ienv /\ env_rel_sound FEMPTY ienv tenv Empty /\
     infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
     infer_p loc ienv p st = (M_success (t',nb),st') /\
     t_unify (infer_st_subst st') t t' = SOME s /\
     sub_completion tvs' (infer_st_next_uvar st') s csx sx
     ==> type_e tenv (bind_tvar tvs' Empty) e (convert_t (t_walkstar sx t)) /\
         type_p tvs' tenv p (convert_t (t_walkstar sx t)) (convert_env sx nb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`; `p:pat`; `ss:infer_st`;
                `t:infer_t`; `st:infer_st`; `t':infer_t`; `nb:(mlstring#infer_t)list`;
                `st':infer_st`; `s:(num,infer_t)fmap`] INFER2AUX_pe_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `ss:infer_st` INFER2AUX_init_infer_state) THEN STRIP_TAC THEN
  SUBGOAL_THEN `inf_env_inf_t ienv = type_env_t tenv /\ inf_env_inf_c ienv = type_env_c tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[env_rel_sound_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ienv_val_ok (pred_set_count 0) (inf_env_inf_v ienv) /\
                tenv_ctor_ok (inf_env_inf_c ienv) /\ tenv_abbrev_ok (inf_env_inf_t ienv)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ienv_ok {} ienv` THEN REWRITE_TAC[ienv_ok_def; COUNT_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (sx:(num,infer_t)fmap) /\ t_compat s sx` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar sx t = t_walkstar sx t'` ASSUME_TAC THENL
   [SUBGOAL_THEN `t_walkstar s t = t_walkstar s t'` MP_TAC THENL
     [ASM_MESON_TAC[t_unify_unifier]; ALL_TAC] THEN
    UNDISCH_TAC `t_compat s (sx:(num,infer_t)fmap)` THEN REWRITE_TAC[t_compat_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sub_completion tvs' (infer_st_next_uvar st') (infer_st_subst st')
                  (CONS (t,t') csx) sx` ASSUME_TAC THENL
   [MATCH_MP_TAC sub_completion_unify2 THEN EXISTS_TAC `s:(num,infer_t)fmap` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (CONJUNCT1 infer_p_constraints)
    (ASSUME `infer_p loc ienv p st = (M_success (t',nb),st')`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `ts:(infer_t#infer_t)list`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_sound) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `init_infer_state ss`;
                          `st:infer_st`; `APPEND ts (CONS (t:infer_t,t':infer_t) csx)`] THEN
    ASM_REWRITE_TAC[COUNT_ZERO; t_wfs_FEMPTY; bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC env_rel_sound_extend_tvs THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC env_rel_e_sound_empty_to THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC sub_completion_add_constraints THEN
    EXISTS_TAC `infer_st_subst st'` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sub_completion tvs' (infer_st_next_uvar st') (infer_st_subst st')
                   (CONS (t,t') csx) sx` THEN
    REWRITE_TAC[sub_completion_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
    ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `t_walkstar sx t = t_walkstar sx t'`)) THEN
    MATCH_MP_TAC(CONJUNCT1 infer_p_sound) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `st:infer_st`; `st':infer_st`;
                          `CONS (t:infer_t,t':infer_t) csx`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let INFER2AUX_tenv_add_tvs_convert_env = prove
 (`!tvs sc (nb:(mlstring#infer_t)list).
     tenv_add_tvs tvs (convert_env sc nb) =
     ZIP (MAP FST nb) (MAP (\t. (tvs,t)) (MAP (convert_t o t_walkstar sc) (MAP SND nb)))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[tenv_add_tvs_def; convert_env_def; MAP; ZIP] THEN
  SPEC_TAC(`h:mlstring#infer_t`,`h:mlstring#infer_t`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tenv_add_tvs_def; convert_env_def]) THEN
  ASM_REWRITE_TAC[CONS_11]);;

(* the type identifiers of the inferred types are below next_id *)
let INFER2AUX_pe_set_tids = prove
 (`!loc ienv e p ss t st t' nb st' s.
     start_type_id <= infer_st_next_id ss /\
     inf_set_tids_ienv (pred_set_count (infer_st_next_id ss)) ienv /\
     infer_e loc ienv e (init_infer_state ss) = (M_success t,st) /\
     infer_p loc ienv p st = (M_success (t',nb),st') /\
     t_unify (infer_st_subst st') t t' = SOME s
     ==> inf_set_tids_subst (pred_set_count (infer_st_next_id ss)) s /\
         ALL (inf_set_tids_subset (pred_set_count (infer_st_next_id ss)) o SND) nb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tids = pred_set_count (infer_st_next_id ss)` THEN
  SUBGOAL_THEN `prim_tids T tids` ASSUME_TAC THENL
   [EXPAND_TAC "tids" THEN MATCH_MP_TAC start_type_id_prim_tids_count THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `ss:infer_st` INFER2AUX_init_infer_state) THEN STRIP_TAC THEN
  MP_TAC(SPEC `tids:num->bool` infer_e_inf_set_tids) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME
    `infer_e loc ienv e (init_infer_state ss) = (M_success t,st)`)) THEN
  ASM_REWRITE_TAC[t_wfs_FEMPTY; inf_set_tids_subst_def; FRANGE_FEMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM inf_set_tids_subst_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state ss`; `t:infer_t`] THEN
    ASM_REWRITE_TAC[t_wfs_FEMPTY];
    ALL_TAC] THEN
  MP_TAC(SPEC `tids:num->bool` infer_p_inf_set_tids) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME
    `infer_p loc ienv p st = (M_success (t',nb),st')`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `tids:num->bool` t_unify_set_tids) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPECL [`infer_st_subst st'`; `t:infer_t`; `t':infer_t`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_p_wfs) THEN
    MAP_EVERY EXISTS_TAC [`loc:loc_err_info`; `ienv:inf_env`; `p:pat`; `st:infer_st`;
                          `t':infer_t`; `nb:(mlstring#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* the Let case with generalisation (is_value e) *)
let INFER2AUX_dlet_poly = prove
 (`!n tvs tenv p e t bindings locs ienv st1.
     is_value e /\ ALL_DISTINCT (pat_bindings p) /\
     type_p tvs tenv p t bindings /\ type_e tenv (bind_tvar tvs Empty) e t /\
     (!tvs' bindings' t'.
        type_p tvs' tenv p t' bindings' /\ type_e tenv (bind_tvar tvs' Empty) e t' /\
        ALL (\(k:mlstring,t). set_tids_subset (pred_set_count n) t) bindings'
        ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
                              (MAP SND (tenv_add_tvs tvs bindings))) /\
     envRel_env_rel tenv ienv /\ inf_set_tids_ienv (pred_set_count n) ienv /\
     infer_st_next_id st1 = n /\ start_type_id <= n
     ==> ?ienv' st2.
           envRel_env_rel
             (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty) ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + 0 /\
           infer_d ienv (Dlet locs p e) st1 = (M_success ienv',st2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ienv_ok {} ienv /\ tenv_ok tenv /\ env_rel_sound FEMPTY ienv tenv Empty /\
                env_rel_complete FEMPTY ienv tenv Empty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `tenv:type_env`; `tvs:num`; `p:pat`; `e:exp`; `t:t`;
                `bindings:(mlstring#t)list`; `st1:infer_st`] infer_pe_complete) THEN
  ASM_SIMP_TAC[inferComplete_env_rel_complete_bind] THEN
  DISCH_THEN(X_CHOOSE_THEN `te:infer_t` (X_CHOOSE_THEN `tq:infer_t`
    (X_CHOOSE_THEN `nb:(mlstring#infer_t)list` (X_CHOOSE_THEN `st:infer_st`
    (X_CHOOSE_THEN `st':infer_st` (X_CHOOSE_THEN `s:(num,infer_t)fmap`
    (X_CHOOSE_THEN `constrs:(infer_t#infer_t)list` (X_CHOOSE_THEN `sc:(num,infer_t)fmap`
       STRIP_ASSUME_TAC)))))))) THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `e:exp`; `p:pat`; `st1:infer_st`; `te:infer_t`; `st:infer_st`;
                `tq:infer_t`; `nb:(mlstring#infer_t)list`; `st':infer_st`;
                `s:(num,infer_t)fmap`] INFER2AUX_pe_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `e:exp`; `p:pat`; `st1:infer_st`; `te:infer_t`; `st:infer_st`;
                `tq:infer_t`; `nb:(mlstring#infer_t)list`; `st':infer_st`;
                `s:(num,infer_t)fmap`] INFER2AUX_pe_set_tids) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `nu = infer_st_next_uvar st'` THEN
  ABBREV_TAC `l = MAP SND (nb:(mlstring#infer_t)list)` THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (nb:(mlstring#infer_t)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (pred_set_count nu)) (l:infer_t list)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
    UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (pred_set_count nu) t) nb` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM];
    ALL_TAC] THEN
  X_CHOOSE_THEN `ntvs:num` (X_CHOOSE_THEN `smap:(num,num)fmap`
    (X_CHOOSE_THEN `ts':infer_t list` ASSUME_TAC))
    (ISPEC `generalise_list 0 0 FEMPTY (MAP (t_walkstar s) (l:infer_t list))`
       BASICAUX_TUPLE3) THEN
  MAP_EVERY EXISTS_TAC
   [`inf_env_REC (alist_to_ns (ZIP (MAP FST (nb:(mlstring#infer_t)list))
                  (MAP (\t. (ntvs,t)) ts'))) nsEmpty nsEmpty`;
    `infer_st_subst_fupd (K s) st'`] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
   [ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; ADD_CLAUSES];
    MATCH_MP_TAC INFER2AUX_infer_d_Dlet THEN
    MAP_EVERY EXISTS_TAC [`te:infer_t`; `st:infer_st`; `tq:infer_t`; `smap:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[]]] THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `sc:(num,infer_t)fmap`; `tvs:num`; `nu:num`;
                `constrs:(infer_t#infer_t)list`; `l:infer_t list`; `ntvs:num`;
                `smap:(num,num)fmap`; `ts':infer_t list`] INFER2AUX_gen_complete_inst) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`0`; `s:(num,infer_t)fmap`; `l:infer_t list`; `ntvs:num`;
                `smap:(num,num)fmap`; `ts':infer_t list`; `nu:num`; `Tbool_num`;
                `pred_set_count n`] generalise_complete) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; IN_COUNT] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec1:(infer_t#infer_t)list`
    (X_CHOOSE_THEN `last_sub:(num,infer_t)fmap`
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `inf_set_tids_subst (pred_set_count n) last_sub` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `start_type_id <= n` THEN
    REWRITE_TAC[start_type_id_def; typeSystem_Tbool_num_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `tenv:type_env`; `e:exp`; `p:pat`; `st1:infer_st`; `te:infer_t`; `st:infer_st`;
                `tq:infer_t`; `nb:(mlstring#infer_t)list`; `st':infer_st`;
                `s:(num,infer_t)fmap`; `ntvs:num`; `ec1:(infer_t#infer_t)list`;
                `last_sub:(num,infer_t)fmap`] INFER2AUX_pe_sound_completion) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ntvs:num`; `convert_env last_sub (nb:(mlstring#infer_t)list)`;
                                `convert_t (t_walkstar last_sub te)`] o
    check (fun th -> is_forall(concl th) &&
      (try fst(dest_var(fst(dest_forall(concl th)))) = "tvs'" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC INFER2AUX_convert_env_set_tids THEN EXISTS_TAC `ntvs:num` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFER2AUX_ALL_PAIR_CONJ THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (pred_set_count nu) t) nb` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INFER2AUX_completion_closed THEN
    MAP_EVERY EXISTS_TAC [`nu:num`; `s:(num,infer_t)fmap`; `ec1:(infer_t#infer_t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (l:infer_t list) = LENGTH (nb:(mlstring#infer_t)list)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `bindings:(mlstring#t)list`)) THEN
  ASM_SIMP_TAC[INFER2AUX_tenv_add_tvs_convert_env; MAP_SND_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAP] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC INFER2AUX_env_rel_bindings THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k < LENGTH (l:infer_t list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; o_THM] THEN
  SUBGOAL_THEN `check_t 0 (pred_set_count nu) (EL k (l:infer_t list))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (check_t 0 (pred_set_count nu)) (l:infer_t list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar sc (EL k (l:infer_t list))) /\
                check_t ntvs {} (t_walkstar last_sub (EL k (l:infer_t list)))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INFER2AUX_completion_closed THEN
    MAP_EVERY EXISTS_TAC [`nu:num`; `s:(num,infer_t)fmap`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `EL k (ts':infer_t list) = t_walkstar last_sub (EL k (l:infer_t list))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `MAP (t_walkstar last_sub) l = ts'`
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    ASM_SIMP_TAC[EL_MAP];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC check_t_to_check_freevars THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `last_sub:(num,infer_t)fmap`)) (concl th))) THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; o_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP tscheme_inst_to_approx) THEN
    MP_TAC(SPECL [`t_walkstar last_sub (EL k (l:infer_t list))`; `ntvs:num`]
      check_t_empty_unconvert_convert_id) THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `sc:(num,infer_t)fmap`)) (concl th) &&
      can (find_term ((=) `ts':infer_t list`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP tscheme_inst_to_approx) THEN
    MP_TAC(SPECL [`t_walkstar last_sub (EL k (l:infer_t list))`; `ntvs:num`]
      check_t_empty_unconvert_convert_id) THEN
    ASM_SIMP_TAC[]]);;

(* the Let case without generalisation (not is_value e) *)
let INFER2AUX_dlet_mono = prove
 (`!n tenv p e t bindings locs ienv st1.
     (~is_value e /\ type_pe_determ_canon n tenv Empty p e) /\
     ALL_DISTINCT (pat_bindings p) /\
     type_p 0 tenv p t bindings /\ type_e tenv Empty e t /\
     envRel_env_rel tenv ienv /\ inf_set_tids_ienv (pred_set_count n) ienv /\
     infer_st_next_id st1 = n /\ start_type_id <= n
     ==> ?ienv' st2.
           envRel_env_rel
             (type_env_REC (alist_to_ns (tenv_add_tvs 0 bindings)) nsEmpty nsEmpty) ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + 0 /\
           infer_d ienv (Dlet locs p e) st1 = (M_success ienv',st2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ienv_ok {} ienv /\ tenv_ok tenv /\ env_rel_sound FEMPTY ienv tenv Empty /\
                env_rel_complete FEMPTY ienv tenv Empty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `tenv:type_env`; `0`; `p:pat`; `e:exp`; `t:t`;
                `bindings:(mlstring#t)list`; `st1:infer_st`] infer_pe_complete) THEN
  ASM_REWRITE_TAC[bind_tvar_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `te:infer_t` (X_CHOOSE_THEN `tq:infer_t`
    (X_CHOOSE_THEN `nb:(mlstring#infer_t)list` (X_CHOOSE_THEN `st:infer_st`
    (X_CHOOSE_THEN `st':infer_st` (X_CHOOSE_THEN `s:(num,infer_t)fmap`
    (X_CHOOSE_THEN `constrs:(infer_t#infer_t)list` (X_CHOOSE_THEN `sc:(num,infer_t)fmap`
       STRIP_ASSUME_TAC)))))))) THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `e:exp`; `p:pat`; `st1:infer_st`; `te:infer_t`; `st:infer_st`;
                `tq:infer_t`; `nb:(mlstring#infer_t)list`; `st':infer_st`;
                `s:(num,infer_t)fmap`] INFER2AUX_pe_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (nb:(mlstring#infer_t)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `p:pat`; `e:exp`; `st:infer_st`; `st':infer_st`; `te:infer_t`; `tq:infer_t`;
                `nb:(mlstring#infer_t)list`; `s:(num,infer_t)fmap`; `tenv:type_env`;
                `st1:infer_st`] type_pe_determ_canon_infer_e) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `l = MAP SND (nb:(mlstring#infer_t)list)` THEN
  SUBGOAL_THEN `LENGTH (l:infer_t list) = LENGTH (nb:(mlstring#infer_t)list)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 {}) (MAP (t_walkstar s) (l:infer_t list))` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
    UNDISCH_TAC `ALL (\(n:mlstring,t). check_t 0 {} (t_walkstar s t)) nb` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (pred_set_count (infer_st_next_uvar st'))) (l:infer_t list)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
    UNDISCH_TAC `ALL (\(x:mlstring,t). check_t 0 (pred_set_count (infer_st_next_uvar st')) t) nb` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `generalise_list 0 0 FEMPTY (MAP (t_walkstar s) l) =
                (0,FEMPTY,MAP (t_walkstar s) (l:infer_t list))` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 generalise_no_uvars) THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`inf_env_REC (alist_to_ns (ZIP (MAP FST (nb:(mlstring#infer_t)list))
                  (MAP (\t. (0,t)) (MAP (t_walkstar s) (l:infer_t list))))) nsEmpty nsEmpty`;
    `infer_st_subst_fupd (K s) st'`] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
   [ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; ADD_CLAUSES];
    MATCH_MP_TAC INFER2AUX_infer_d_Dlet THEN
    MAP_EVERY EXISTS_TAC [`te:infer_t`; `st:infer_st`; `tq:infer_t`;
                          `FEMPTY:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `t_wfs (sc:(num,infer_t)fmap) /\ (s:(num,infer_t)fmap) SUBMAP sc`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sub_completion 0 (infer_st_next_uvar st') s constrs sc` THEN
    REWRITE_TAC[sub_completion_def] THEN ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `bindings:(mlstring#t)list`)) THEN
  ASM_REWRITE_TAC[INFER2AUX_tenv_add_tvs_convert_env] THEN
  MATCH_MP_TAC INFER2AUX_env_rel_bindings THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k < LENGTH (l:infer_t list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; o_THM] THEN
  SUBGOAL_THEN `check_t 0 {} (t_walkstar s (EL k (l:infer_t list)))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (check_t 0 {}) (MAP (t_walkstar s) (l:infer_t list))` THEN
    ASM_SIMP_TAC[GSYM ALL_EL; LENGTH_MAP; EL_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_walkstar sc (EL k (l:infer_t list)) = t_walkstar s (EL k l)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`s:(num,infer_t)fmap`; `sc:(num,infer_t)fmap`; `EL k (l:infer_t list)`]
      t_walkstar_SUBMAP) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC t_walkstar_no_vars THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t_walkstar s (EL k (l:infer_t list))`; `0`]
    check_t_empty_unconvert_convert_id) THEN
  ASM_SIMP_TAC[tscheme_approx_refl; check_t_to_check_freevars]);;

let INFER2AUX_n_fresh_uvar_eval = prove
 (`!n st. (n_fresh_uvar n st:(infer_t list,A)exc#infer_st) =
          (M_success (MAP (\k. Infer_Tuvar (infer_st_next_uvar st + k)) (COUNT_LIST n)),
           infer_st_next_uvar_fupd (K (infer_st_next_uvar st + n)) st)`,
  REWRITE_TAC[n_fresh_uvar_success]);;

let INFER2AUX_infer_d_Dletrec = prove
 (CASE_TERM `!ienv locs funs st1 funs_ts st st' num_gen smap ts'.
     ALL_DISTINCT (MAP FST funs) /\
     infer_funs (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                      (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv)
       funs (infer_st_next_uvar_fupd (K (LENGTH funs)) (init_infer_state st1)) =
       (M_success funs_ts,st) /\
     add_constraints (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
       (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))) funs_ts st = (M_success one,st') /\
     generalise_list 0 0 FEMPTY
       (MAP (t_walkstar (infer_st_subst st'))
          (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))) =
       (num_gen,smap,ts')
     ==> infer_d ienv (Dletrec locs funs) st1 =
         (M_success (inf_env_REC
            (alist_to_ns (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(num_gen,t))) funs ts'))
            nsEmpty nsEmpty),
          st')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[infer_d_def] THEN
  FIRST_ASSUM(fun th -> INFER2AUX_BIND_TAC[MATCH_MP INFER1AUX_check_dups_ok th]) THEN
  INFER2AUX_BIND_TAC[init_state_def] THEN
  INFER2AUX_BIND_TAC[get_next_uvar_def; INFER2AUX_init_infer_state] THEN
  INFER2AUX_BIND_TAC[INFER2AUX_n_fresh_uvar_eval; INFER2AUX_init_infer_state; ADD_CLAUSES] THEN
  INFER2AUX_BIND_TAC[st_ex_return_def] THEN
  INFER2AUX_BIND_TAC[] THEN INFER2AUX_BIND_TAC[] THEN
  INFER2AUX_BIND_TAC[apply_subst_list_def; st_ex_bind_def; infer_read_def; st_ex_return_def] THEN
  INFER2AUX_BIND_TAC[st_ex_return_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[st_ex_return_def]);;

let INFER2AUX_MAP2_triple_ZIP = prove
 (CASE_TERM `!(g:B->C) (funs:(A#D#E)list) (ts:B list).
     LENGTH ts = LENGTH funs
     ==> MAP2 (\fxe t. match fxe with (f,x,e) -> (f,g t)) funs ts =
         ZIP (MAP FST funs) (MAP g ts)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MAP; ZIP] THEN
  DISCH_TAC THEN
  X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:D` (X_CHOOSE_THEN `c:E` SUBST1_TAC))
    (ISPEC `h:A#D#E` BASICAUX_TUPLE3) THEN
  CASE_REWRITE_TAC[CONS_11] THEN ASM_SIMP_TAC[]);;

let INFER2AUX_tenv_add_tvs_ZIP = prove
 (`!tvs (l:(mlstring#t)list).
     tenv_add_tvs tvs l = ZIP (MAP FST l) (MAP (\t. (tvs,t)) (MAP SND l))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[tenv_add_tvs_def; MAP; ZIP] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[CONS_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tenv_add_tvs_def]) THEN ASM_REWRITE_TAC[]);;

let INFER2AUX_pac_walk_eq = prove
 (`!s1 s2 (l1:infer_t list) l2 k.
     t_wfs s1 /\ pure_add_constraints s1 (ZIP l1 l2) s2 /\ LENGTH l1 = LENGTH l2 /\
     k < LENGTH l1
     ==> t_walkstar s2 (EL k l1) = t_walkstar s2 (EL k l2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `ZIP (l1:infer_t list) (l2:infer_t list)`;
                `s2:(num,infer_t)fmap`]
    pure_add_constraints_apply) THEN
  ASM_SIMP_TAC[MAP_ZIP] THEN DISCH_THEN(MP_TAC o AP_TERM `EL k:infer_t list->infer_t`) THEN
  SUBGOAL_THEN `k < LENGTH (l2:infer_t list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_SIMP_TAC[EL_MAP]]);;

let INFER2AUX_letrec_ienv_ok = prove
 (CASE_TERM `!ienv (funs:(mlstring#mlstring#exp)list).
     ienv_ok {} ienv
     ==> ienv_ok (pred_set_count (LENGTH funs))
           (inf_env_inf_v_fupd
              (K (nsAppend
                    (alist_to_ns
                       (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                          (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                    (inf_env_inf_v ienv))) ienv)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ienv_ok_def; ienv_val_ok_def; inf_env_INFO.ri_accfupds;
                                  K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll_nsAppend THEN CONJ_TAC THENL
   [MATCH_MP_TAC nsAll_alist_to_ns THEN
    SIMP_TAC[INFER2AUX_MAP2_triple_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
    SIMP_TAC[GSYM ALL_EL; LENGTH_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST; EL_ZIP; EL_MAP;
             EL_COUNT_LIST] THEN
    CASE_REWRITE_TAC[check_t_def; IN_COUNT] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> INFER1AUX_is_app "nsAll" (concl th))) THEN
    MATCH_MP_TAC nsAll_mono THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MATCH_MP (CONJUNCT1 check_t_more5) (ASSUME `check_t p1 {} p2`)) THEN
    REWRITE_TAC[EMPTY_SUBSET]]);;

let INFER2AUX_letrec_walk_eq = prove
 (`!s1 s2 sx (funs_ts:infer_t list) N.
     t_wfs s1 /\
     pure_add_constraints s1 (ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST N)) funs_ts) s2 /\
     LENGTH funs_ts = N /\ t_compat s2 sx
     ==> !k. k < N ==> t_walkstar sx (Infer_Tuvar k) = t_walkstar sx (EL k funs_ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`;
                `MAP (\n. Infer_Tuvar n) (COUNT_LIST N)`; `funs_ts:infer_t list`; `k:num`]
    INFER2AUX_pac_walk_eq) THEN
  ASM_SIMP_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; EL_MAP; EL_COUNT_LIST] THEN
  DISCH_THEN(MP_TAC o AP_TERM `t_walkstar sx`) THEN
  UNDISCH_TAC `t_compat s2 (sx:(num,infer_t)fmap)` THEN REWRITE_TAC[t_compat_def] THEN
  MESON_TAC[]);;

let INFER2AUX_funs_sound_completion = prove
 (CASE_TERM `!loc ienv tenv (funs:(mlstring#mlstring#exp)list) st1 funs_ts st st' tvs' ec sx.
     ienv_ok {} ienv /\ env_rel_sound FEMPTY ienv tenv Empty /\
     ALL_DISTINCT (MAP FST funs) /\
     infer_funs loc
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                      (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv)
       funs (infer_st_next_uvar_fupd (K (LENGTH funs)) (init_infer_state st1)) =
       (M_success funs_ts,st) /\
     infer_st_next_uvar st = infer_st_next_uvar st' /\
     pure_add_constraints (infer_st_subst st)
       (ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))) funs_ts) (infer_st_subst st') /\
     sub_completion tvs' (infer_st_next_uvar st') (infer_st_subst st') ec sx
     ==> type_funs tenv
           (bind_var_list 0
              (MAP2 (\xyz t. match xyz with (x,y,z) -> (x,(convert_t o t_walkstar sx) t))
                 funs funs_ts)
              (bind_tvar tvs' Empty))
           funs
           (MAP2 (\xyz t. match xyz with (x,y,z) -> (x,(convert_t o t_walkstar sx) t))
              funs funs_ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `N = LENGTH (funs:(mlstring#mlstring#exp)list)` THEN
  MP_TAC(SPEC `st1:infer_st` INFER2AUX_init_infer_state) THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (funs_ts:infer_t list) = N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC infer_funs_length THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_wfs)))) o
    check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; t_wfs_FEMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `N <= infer_st_next_uvar st` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_uvar_mono))) o
      check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
    REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st') /\ t_wfs (sx:(num,infer_t)fmap) /\
                t_compat (infer_st_subst st') sx /\
                pred_set_count (infer_st_next_uvar st') SUBSET FDOM sx /\
                (!uv. uv IN FDOM sx ==> check_t tvs' {} (t_walkstar sx (Infer_Tuvar uv)))`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
     [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
    UNDISCH_TAC `sub_completion tvs' (infer_st_next_uvar st') (infer_st_subst st') ec sx` THEN
    REWRITE_TAC[sub_completion_def] THEN ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `MAP (\n. convert_t (t_walkstar sx (Infer_Tuvar n))) (COUNT_LIST N) =
     MAP (convert_t o t_walkstar sx) (funs_ts:infer_t list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`infer_st_subst st`; `infer_st_subst st'`; `sx:(num,infer_t)fmap`;
                  `funs_ts:infer_t list`; `N:num`] INFER2AUX_letrec_walk_eq) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_COUNT_LIST] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k < N` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_sound))) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)) then
      let args = snd(strip_comb(lhs(concl th))) in
      MAP_EVERY EXISTS_TAC [el 0 args; el 1 args; el 3 args; `st:infer_st`;
         `APPEND (ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST N)) (funs_ts:infer_t list)) ec`]
    else failwith "") THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM; t_wfs_FEMPTY; num_tvs_bind_var_list;
                  bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`ienv:inf_env`; `funs:(mlstring#mlstring#exp)list`] INFER2AUX_letrec_ienv_ok) THEN
  ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`funs:(mlstring#mlstring#exp)list`; `ienv:inf_env`; `tenv:type_env`;
                `bind_tvar tvs' Empty`; `sx:(num,infer_t)fmap`; `0`]
    env_rel_e_sound_letrec_merge0) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; bind_tvar_rewrites; num_tvs_def] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `pred_set_count (infer_st_next_uvar st')` THEN
      ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC env_rel_sound_extend_tvs THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC env_rel_e_sound_empty_to THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INFER2AUX_MAP2_triple_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST; MAP_ID; ETA_AX];
    MATCH_MP_TAC sub_completion_add_constraints THEN
  EXISTS_TAC `infer_st_subst st'` THEN ASM_REWRITE_TAC[]]);;

let INFER2AUX_convert_env_ZIP = prove
 (`!s (l1:mlstring list) (l2:infer_t list).
     LENGTH l1 = LENGTH l2
     ==> convert_env s (ZIP l1 l2) = ZIP l1 (MAP (convert_t o t_walkstar s) l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; convert_env_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[convert_env_def]) THEN
  CASE_REWRITE_TAC[CONS_11; o_THM] THEN ASM_SIMP_TAC[]);;

(* the type identifiers of the inferred types of mutually recursive functions *)
let INFER2AUX_letrec_set_tids = prove
 (CASE_TERM `!loc ienv (funs:(mlstring#mlstring#exp)list) st1 funs_ts st st'.
     start_type_id <= infer_st_next_id st1 /\
     inf_set_tids_ienv (pred_set_count (infer_st_next_id st1)) ienv /\
     infer_funs loc
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                      (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv)
       funs (infer_st_next_uvar_fupd (K (LENGTH funs)) (init_infer_state st1)) =
       (M_success funs_ts,st) /\
     pure_add_constraints (infer_st_subst st)
       (ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))) funs_ts) (infer_st_subst st')
     ==> ALL (inf_set_tids_subset (pred_set_count (infer_st_next_id st1))) funs_ts /\
         inf_set_tids_subst (pred_set_count (infer_st_next_id st1)) (infer_st_subst st')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tids = pred_set_count (infer_st_next_id st1)` THEN
  ABBREV_TAC `N = LENGTH (funs:(mlstring#mlstring#exp)list)` THEN
  SUBGOAL_THEN `prim_tids T tids` ASSUME_TAC THENL
   [EXPAND_TAC "tids" THEN MATCH_MP_TAC start_type_id_prim_tids_count THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `st1:infer_st` INFER2AUX_init_infer_state) THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (funs_ts:infer_t list) = N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC infer_funs_length THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_wfs)))) o
    check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; t_wfs_FEMPTY] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      (CONJUNCT2(CONJUNCT2(CONJUNCT2 (SPEC `tids:num->bool` infer_e_inf_set_tids))))) o
    check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; t_wfs_FEMPTY; inf_set_tids_subst_def;
                  FRANGE_FEMPTY; NOT_IN_EMPTY] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `inf_set_tids_ienv tids ienv` THEN
    REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accfupds; K_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll_nsAppend THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
    ASM_SIMP_TAC[INFER2AUX_MAP2_triple_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
    ASM_SIMP_TAC[GSYM ALL_EL; LENGTH_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST; EL_ZIP; EL_MAP;
                 EL_COUNT_LIST] THEN
    CASE_REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_def; EMPTY_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM inf_set_tids_subst_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC pure_add_constraints_set_tids THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st`;
    `ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST N)) (funs_ts:infer_t list)`] THEN
  ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
  REWRITE_TAC[ALL_MAP; o_DEF; GSYM ALL_MEM; inf_set_tids_subset_def; inf_set_tids_def;
              EMPTY_SUBSET]);;

(* the Letrec case *)
let INFER2AUX_dletrec = prove
 (`!n tenv (funs:(mlstring#mlstring#exp)list) bindings tvs locs ienv st1.
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings /\
     (!tvs' bindings'.
        type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings' /\
        ALL (\(k:mlstring,t). set_tids_subset (pred_set_count n) t) bindings'
        ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
                              (MAP SND (tenv_add_tvs tvs bindings))) /\
     envRel_env_rel tenv ienv /\ inf_set_tids_ienv (pred_set_count n) ienv /\
     infer_st_next_id st1 = n /\ start_type_id <= n
     ==> ?ienv' st2.
           envRel_env_rel
             (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty) ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + 0 /\
           infer_d ienv (Dletrec locs funs) st1 = (M_success ienv',st2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ienv_ok {} ienv /\ tenv_ok tenv /\ env_rel_sound FEMPTY ienv tenv Empty /\
                env_rel_complete FEMPTY ienv tenv Empty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def]; ALL_TAC] THEN
  MP_TAC(SPEC `st1:infer_st` INFER2AUX_init_infer_state) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `tenv:type_env`; `tvs:num`; `funs:(mlstring#mlstring#exp)list`;
                `bindings:(mlstring#t)list`; `st1:infer_st`] infer_funs_complete) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `funs_ts:infer_t list` (X_CHOOSE_THEN `st:infer_st`
    (X_CHOOSE_THEN `st':infer_st` (X_CHOOSE_THEN `constr:(infer_t#infer_t)list`
    (X_CHOOSE_THEN `s:(num,infer_t)fmap` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `N = LENGTH (funs:(mlstring#mlstring#exp)list)` THEN
  ABBREV_TAC `nu = infer_st_next_uvar st'` THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (funs:(mlstring#mlstring#exp)list))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EVALAUX_MAP_FST3] THEN MATCH_MP_TAC type_funs_distinct THEN
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `bind_var_list 0 bindings (bind_tvar tvs Empty)`;
                          `bindings:(mlstring#t)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (funs_ts:infer_t list) = N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC infer_funs_length THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP FST (bindings:(mlstring#t)list) =
                MAP FST (funs:(mlstring#mlstring#exp)list)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC type_funs_MAP_FST THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_wfs)))) o
    check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; t_wfs_FEMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `N <= nu` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_uvar_mono))) o
      check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st')` ASSUME_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `infer_st_next_id st' = n` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_id_const))) o
      check (fun th -> is_eq(concl th) && INFER1AUX_is_app "infer_funs" (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `uvars = MAP (\n. Infer_Tuvar n) (COUNT_LIST N)` THEN
  SUBGOAL_THEN `LENGTH (uvars:infer_t list) = N` ASSUME_TAC THENL
   [EXPAND_TAC "uvars" THEN REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k < N ==> EL k uvars = Infer_Tuvar k` ASSUME_TAC THENL
   [EXPAND_TAC "uvars" THEN SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (pred_set_count nu)) (uvars:infer_t list)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM ALL_EL; check_t_def; IN_COUNT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X_CHOOSE_THEN `num_gen:num` (X_CHOOSE_THEN `smap:(num,num)fmap`
    (X_CHOOSE_THEN `ts':infer_t list` ASSUME_TAC))
    (ISPEC `generalise_list 0 0 FEMPTY (MAP (t_walkstar (infer_st_subst st')) uvars)`
       BASICAUX_TUPLE3) THEN
  MAP_EVERY EXISTS_TAC
   [CASE_TERM `inf_env_REC
      (alist_to_ns (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(num_gen,t)))
                     (funs:(mlstring#mlstring#exp)list) (ts':infer_t list)))
      nsEmpty nsEmpty`;
    `st':infer_st`] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES];
    MATCH_MP_TAC INFER2AUX_infer_d_Dletrec THEN
    MAP_EVERY EXISTS_TAC [`funs_ts:infer_t list`; `st:infer_st`; `smap:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[add_constraints_success] THEN ASM_REWRITE_TAC[]]] THEN
  MP_TAC(SPECL [`infer_st_subst st'`; `s:(num,infer_t)fmap`; `tvs:num`; `nu:num`;
                `constr:(infer_t#infer_t)list`; `uvars:infer_t list`; `num_gen:num`;
                `smap:(num,num)fmap`; `ts':infer_t list`] INFER2AUX_gen_complete_inst) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`0`; `infer_st_subst st'`; `uvars:infer_t list`; `num_gen:num`;
                `smap:(num,num)fmap`; `ts':infer_t list`; `nu:num`; `Tbool_num`;
                `pred_set_count n`] generalise_complete) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; IN_COUNT] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec1:(infer_t#infer_t)list`
    (X_CHOOSE_THEN `last_sub:(num,infer_t)fmap`
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `funs:(mlstring#mlstring#exp)list`; `st1:infer_st`; `funs_ts:infer_t list`;
                `st:infer_st`; `st':infer_st`] INFER2AUX_letrec_set_tids) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inf_set_tids_subst (pred_set_count n) last_sub` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `start_type_id <= n` THEN
    REWRITE_TAC[start_type_id_def; typeSystem_Tbool_num_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t_compat (infer_st_subst st') s /\ t_compat (infer_st_subst st') last_sub`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[sub_completion_def]) THEN
    ASM_MESON_TAC[pure_add_constraints_success];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!k. k < N ==> t_walkstar s (Infer_Tuvar k) = t_walkstar s (EL k funs_ts)) /\
                (!k. k < N ==> t_walkstar last_sub (Infer_Tuvar k) =
                               t_walkstar last_sub (EL k funs_ts))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INFER2AUX_letrec_walk_eq THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st`; `infer_st_subst st'`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)`; `ienv:inf_env`;
                `tenv:type_env`; `funs:(mlstring#mlstring#exp)list`; `st1:infer_st`;
                `funs_ts:infer_t list`; `st:infer_st`; `st':infer_st`; `num_gen:num`;
                `ec1:(infer_t#infer_t)list`; `last_sub:(num,infer_t)fmap`]
    INFER2AUX_funs_sound_completion) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INFER2AUX_MAP2_triple_ZIP] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ETA_AX]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`num_gen:num`;
      `ZIP (MAP FST (funs:(mlstring#mlstring#exp)list))
           (MAP (convert_t o t_walkstar last_sub) (funs_ts:infer_t list))`] o
    check (fun th -> is_forall(concl th) &&
      (try fst(dest_var(fst(dest_forall(concl th)))) = "tvs'" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `ZIP (MAP FST (funs:(mlstring#mlstring#exp)list))
                      (MAP (convert_t o t_walkstar last_sub) (funs_ts:infer_t list)) =
                  convert_env last_sub (ZIP (MAP FST funs) funs_ts)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFER2AUX_convert_env_ZIP THEN
      ASM_REWRITE_TAC[LENGTH_MAP];
      ALL_TAC] THEN
    MATCH_MP_TAC INFER2AUX_convert_env_set_tids THEN EXISTS_TAC `num_gen:num` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM ALL_EL; LENGTH_ZIP; LENGTH_MAP; EL_ZIP] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ALL (inf_set_tids_subset (pred_set_count n)) (funs_ts:infer_t list)` THEN
      ASM_SIMP_TAC[GSYM ALL_EL];
      SUBGOAL_THEN `k < N` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term ((=) `last_sub:(num,infer_t)fmap`)) (concl th) &&
         can (find_term ((=) `funs_ts:infer_t list`)) (concl th)
         then SUBST1_TAC(SYM(MP (SPEC `k:num` th) (ASSUME `k < N`))) else failwith "") THEN
      MATCH_MP_TAC INFER2AUX_completion_closed THEN
      MAP_EVERY EXISTS_TAC [`nu:num`; `infer_st_subst st'`; `ec1:(infer_t#infer_t)list`] THEN
      ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INFER2AUX_tenv_add_tvs_ZIP] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; MAP_FST_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAP] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC INFER2AUX_env_rel_bindings THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k < LENGTH (funs_ts:infer_t list) /\ k < LENGTH (uvars:infer_t list)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; o_THM] THEN
  SUBGOAL_THEN `t_walkstar s (EL k (funs_ts:infer_t list)) = t_walkstar s (Infer_Tuvar k) /\
                t_walkstar last_sub (EL k (funs_ts:infer_t list)) =
                t_walkstar last_sub (Infer_Tuvar k)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t tvs {} (t_walkstar s (Infer_Tuvar k)) /\
                check_t num_gen {} (t_walkstar last_sub (Infer_Tuvar k))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INFER2AUX_completion_closed THEN
    EXISTS_TAC `nu:num` THEN EXISTS_TAC `infer_st_subst st'` THEN
    ASM_REWRITE_TAC[check_t_def; IN_COUNT] THEN ASM_MESON_TAC[LTE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `EL k (ts':infer_t list) = t_walkstar last_sub (Infer_Tuvar k)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `MAP (t_walkstar last_sub) uvars = ts'`
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    ASM_SIMP_TAC[EL_MAP];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC check_t_to_check_freevars THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `last_sub:(num,infer_t)fmap`)) (concl th) &&
      can (find_term ((=) `tscheme_inst`)) (concl th))) THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; o_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP tscheme_inst_to_approx) THEN
    SUBGOAL_THEN `t_walkstar last_sub (EL k (funs_ts:infer_t list)) =
                  t_walkstar last_sub (Infer_Tuvar k)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`t_walkstar last_sub (Infer_Tuvar k)`; `num_gen:num`]
      check_t_empty_unconvert_convert_id) THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `ts':infer_t list`)) (concl th) &&
      can (find_term ((=) `tscheme_inst`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP tscheme_inst_to_approx) THEN
    MP_TAC(SPECL [`t_walkstar last_sub (Infer_Tuvar k)`; `num_gen:num`]
      check_t_empty_unconvert_convert_id) THEN
    ASM_SIMP_TAC[]]);;

let INFER2AUX_check_type_definition_ok = prove
 (`!l tenvT tds (s:infer_st).
     check_ctor_tenv tenvT tds ==> check_type_definition l tenvT tds s = (M_success one,s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[check_type_definition_success]);;

let INFER2AUX_tenv_ok_d = prove
 (`!n tenv d ids tenv'. type_d_canon n tenv d ids tenv' /\ tenv_ok tenv ==> tenv_ok tenv'`,
  MESON_TAC[type_d_canon_tenv_ok]);;

let INFER2AUX_dtype = prove
 (CASE_TERM `!n type_identities tenv tdefs tenvT locs ienv st1.
     ITLIST MAX (CONS Tlist_num (CONS Tbool_num prim_type_nums)) 0 < n /\
     type_identities = list_of_seq (\i. i + n) (LENGTH tdefs) /\
     check_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs /\
     tenvT = alist_to_ns
               (MAP2 (\tdef i. match tdef with
                                 (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                     tdefs type_identities) /\
     envRel_env_rel tenv ienv /\ inf_set_tids_ienv (pred_set_count n) ienv /\
     infer_st_next_id st1 = n /\ start_type_id <= n
     ==> ?ienv' st2.
           envRel_env_rel
             (type_env_REC nsEmpty
                (build_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs type_identities)
                tenvT) ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + LENGTH tdefs /\
           infer_d ienv (Dtype locs tdefs) st1 = (M_success ienv',st2)`,

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "tenvT")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "type_identities")) THEN
  SUBGOAL_THEN `ienv_ok {} ienv /\ tenv_ok tenv /\ inf_env_inf_t ienv = type_env_t tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def; env_rel_sound_def]; ALL_TAC] THEN
  W(fun (asl,w) ->
     let tenv' = rand(rator(lhand(snd(strip_exists w)))) in
     SUBGOAL_THEN (mk_comb(`tenv_ok`,tenv')) ASSUME_TAC THENL
      [MATCH_MP_TAC INFER2AUX_tenv_ok_d THEN
       MAP_EVERY EXISTS_TAC [`n:num`; `tenv:type_env`; `Dtype locs tdefs`;
                             `LENGTH (tdefs:type_def)`] THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(el 3 (CONJUNCTS type_d_canon_rules)) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MAP_EVERY EXISTS_TAC [mk_comb(`tenv_to_ienv`,tenv');
                           `infer_st_next_id_fupd (K (n + LENGTH (tdefs:type_def))) st1`]) THEN
  ASM_SIMP_TAC[env_rel_tenv_to_ienv; infer_st_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `(\x. n + x) = (\i. i + n)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[infer_d_def] THEN
  INFER2AUX_BIND_TAC[n_fresh_id_def] THEN
  INFER2AUX_BIND_TAC[st_ex_return_def] THEN
  INFER2AUX_BIND_TAC[st_ex_return_def] THEN
  FIRST_ASSUM(fun th -> INFER2AUX_BIND_TAC[MATCH_MP INFER2AUX_check_type_definition_ok th]) THEN
  REWRITE_TAC[st_ex_return_def; tenv_to_ienv_def; type_env_INFO.ri_accessors;
              nsMap_nsEmpty; ADD_SYM]);;

let INFER2AUX_dtabbrev = prove
 (`!n tenv tvs tn t locs ienv st1.
     check_freevars_ast tvs t /\ check_type_names (type_env_t tenv) t /\ ALL_DISTINCT tvs /\
     envRel_env_rel tenv ienv /\ inf_set_tids_ienv (pred_set_count n) ienv /\
     infer_st_next_id st1 = n /\ start_type_id <= n
     ==> ?ienv' st2.
           envRel_env_rel
             (type_env_REC nsEmpty nsEmpty (nsSing tn (tvs,type_name_subst (type_env_t tenv) t)))
             ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + 0 /\
           infer_d ienv (Dtabbrev locs tvs tn t) st1 = (M_success ienv',st2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ienv_ok {} ienv /\ tenv_ok tenv /\ inf_env_inf_t ienv = type_env_t tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def; env_rel_sound_def]; ALL_TAC] THEN
  W(fun (asl,w) ->
     let tenv' = rand(rator(lhand(snd(strip_exists w)))) in
     SUBGOAL_THEN (mk_comb(`tenv_ok`,tenv')) ASSUME_TAC THENL
      [MATCH_MP_TAC INFER2AUX_tenv_ok_d THEN
       MAP_EVERY EXISTS_TAC [`n:num`; `tenv:type_env`; `Dtabbrev locs tvs tn t`; `0`] THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(el 4 (CONJUNCTS type_d_canon_rules)) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MAP_EVERY EXISTS_TAC [mk_comb(`tenv_to_ienv`,tenv'); `st1:infer_st`]) THEN
  ASM_SIMP_TAC[env_rel_tenv_to_ienv; ADD_CLAUSES] THEN
  REWRITE_TAC[infer_d_def] THEN
  FIRST_ASSUM(fun th -> INFER2AUX_BIND_TAC[MATCH_MP INFER1AUX_check_dups_ok th]) THEN
  ASM_SIMP_TAC[st_ex_bind_def; type_name_check_subst_comp_thm] THEN
  CASE_REWRITE_TAC[st_ex_return_def; tenv_to_ienv_def; type_env_INFO.ri_accessors;
                   nsMap_nsEmpty; nsMap_nsSing]);;

let INFER2AUX_dexn = prove
 (`!n tenv cn ts locs ienv st1.
     ALL (check_freevars_ast []) ts /\ ALL (check_type_names (type_env_t tenv)) ts /\
     envRel_env_rel tenv ienv /\ inf_set_tids_ienv (pred_set_count n) ienv /\
     infer_st_next_id st1 = n /\ start_type_id <= n
     ==> ?ienv' st2.
           envRel_env_rel
             (type_env_REC nsEmpty
                (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num)) nsEmpty)
             ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + 0 /\
           infer_d ienv (Dexn locs cn ts) st1 = (M_success ienv',st2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ienv_ok {} ienv /\ tenv_ok tenv /\ inf_env_inf_t ienv = type_env_t tenv`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[envRel_env_rel_def; env_rel_sound_def]; ALL_TAC] THEN
  W(fun (asl,w) ->
     let tenv' = rand(rator(lhand(snd(strip_exists w)))) in
     SUBGOAL_THEN (mk_comb(`tenv_ok`,tenv')) ASSUME_TAC THENL
      [MATCH_MP_TAC INFER2AUX_tenv_ok_d THEN
       MAP_EVERY EXISTS_TAC [`n:num`; `tenv:type_env`; `Dexn locs cn ts`; `0`] THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(el 5 (CONJUNCTS type_d_canon_rules)) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MAP_EVERY EXISTS_TAC [mk_comb(`tenv_to_ienv`,tenv'); `st1:infer_st`]) THEN
  ASM_SIMP_TAC[env_rel_tenv_to_ienv; ADD_CLAUSES] THEN
  REWRITE_TAC[infer_d_def] THEN
  ASM_SIMP_TAC[st_ex_bind_def; type_name_check_subst_comp_thm] THEN
  CASE_REWRITE_TAC[st_ex_return_def; tenv_to_ienv_def; type_env_INFO.ri_accessors;
                   nsMap_nsEmpty; nsMap_nsSing]);;

(* ------------------------------------------------------------------------- *)
(* Completeness of declaration inference.                                    *)
(* ------------------------------------------------------------------------- *)

let infer_d_complete_canon = prove
 (`(!d n tenv ids tenv' ienv st1.
      type_d_canon n tenv d ids tenv' /\
      envRel_env_rel tenv ienv /\
      inf_set_tids_ienv (pred_set_count n) ienv /\
      infer_st_next_id st1 = n /\ start_type_id <= n
      ==> ?ienv' st2.
            envRel_env_rel tenv' ienv' /\
            infer_st_next_id st2 = infer_st_next_id st1 + ids /\
            infer_d ienv d st1 = (M_success ienv',st2)) /\
   (!ds n tenv ids tenv' ienv st1.
      type_ds_canon n tenv ds ids tenv' /\
      envRel_env_rel tenv ienv /\
      inf_set_tids_ienv (pred_set_count n) ienv /\
      infer_st_next_id st1 = n /\ start_type_id <= n
      ==> ?ienv' st2.
            envRel_env_rel tenv' ienv' /\
            infer_st_next_id st2 = infer_st_next_id st1 + ids /\
            infer_ds ienv ds st1 = (M_success ienv',st2))`,
  SUBGOAL_THEN
   `(!n tenv d ids tenv'.
       type_d_canon n tenv d ids tenv'
       ==> !ienv st1.
             envRel_env_rel tenv ienv /\
             inf_set_tids_ienv (pred_set_count n) ienv /\
             infer_st_next_id st1 = n /\ start_type_id <= n
             ==> ?ienv' st2.
                   envRel_env_rel tenv' ienv' /\
                   infer_st_next_id st2 = infer_st_next_id st1 + ids /\
                   infer_d ienv d st1 = (M_success ienv',st2)) /\
    (!n tenv ds ids tenv'.
       type_ds_canon n tenv ds ids tenv'
       ==> !ienv st1.
             envRel_env_rel tenv ienv /\
             inf_set_tids_ienv (pred_set_count n) ienv /\
             infer_st_next_id st1 = n /\ start_type_id <= n
             ==> ?ienv' st2.
                   envRel_env_rel tenv' ienv' /\
                   infer_st_next_id st2 = infer_st_next_id st1 + ids /\
                   infer_ds ienv ds st1 = (M_success ienv',st2))`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC type_d_canon_ind THEN REPEAT CONJ_TAC THENL
   [(* Let with generalisation *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC INFER2AUX_dlet_poly THEN ASM_MESON_TAC[];
    (* Let without generalisation *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC INFER2AUX_dlet_mono THEN ASM_MESON_TAC[];
    (* Letrec *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC INFER2AUX_dletrec THEN ASM_MESON_TAC[];
    (* Dtype *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC INFER2AUX_dtype THEN ASM_MESON_TAC[];
    (* Dtabbrev *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC INFER2AUX_dtabbrev THEN ASM_MESON_TAC[];
    (* Dexn *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC INFER2AUX_dexn THEN ASM_MESON_TAC[];
    (* Dmod *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ienv:inf_env`; `st1:infer_st`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ienv1:inf_env` (X_CHOOSE_THEN `st2:infer_st`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`lift_ienv mn ienv1`; `st2:infer_st`] THEN
    ASM_SIMP_TAC[env_rel_lift] THEN REWRITE_TAC[infer_d_def] THEN
    INFER2AUX_BIND_TAC[] THEN REWRITE_TAC[st_ex_return_def];
    (* Dlocal *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`ienv:inf_env`; `st1:infer_st`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ienv1:inf_env` (X_CHOOSE_THEN `st2:infer_st`
      STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`extend_dec_ienv ienv1 ienv`; `st2:infer_st`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[env_rel_extend] THEN
      CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `start_type_id <= n` THEN ARITH_TAC] THEN
      MATCH_MP_TAC inf_set_tids_extend_dec_ienv THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[LE_ADD] THEN
      SUBGOAL_THEN `n + decls1 = infer_st_next_id st2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(CONJUNCT2 infer_d_inf_set_tids) THEN
      MAP_EVERY EXISTS_TAC [`lds:dec list`; `ienv:inf_env`; `st1:infer_st`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ienv2:inf_env` (X_CHOOSE_THEN `st3:infer_st`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ienv2:inf_env`; `st3:infer_st`] THEN
    ASM_REWRITE_TAC[ADD_ASSOC] THEN REWRITE_TAC[infer_d_def] THEN
    INFER2AUX_BIND_TAC[] THEN ASM_REWRITE_TAC[];
    (* [] *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`inf_env_REC nsEmpty nsEmpty nsEmpty`; `st1:infer_st`] THEN
    REWRITE_TAC[env_rel_empty; ADD_CLAUSES; infer_d_def; st_ex_return_def];
    (* CONS *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`ienv:inf_env`; `st1:infer_st`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ienv1:inf_env` (X_CHOOSE_THEN `st2:infer_st`
      STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`extend_dec_ienv ienv1 ienv`; `st2:infer_st`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[env_rel_extend] THEN
      CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `start_type_id <= n` THEN ARITH_TAC] THEN
      MATCH_MP_TAC inf_set_tids_extend_dec_ienv THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[LE_ADD] THEN
      SUBGOAL_THEN `n + decls1 = infer_st_next_id st2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(CONJUNCT1 infer_d_inf_set_tids) THEN
      MAP_EVERY EXISTS_TAC [`d:dec`; `ienv:inf_env`; `st1:infer_st`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ienv2:inf_env` (X_CHOOSE_THEN `st3:infer_st`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`extend_dec_ienv ienv2 ienv1`; `st3:infer_st`] THEN
    ASM_SIMP_TAC[env_rel_extend; ADD_ASSOC] THEN REWRITE_TAC[infer_d_def] THEN
    INFER2AUX_BIND_TAC[] THEN INFER2AUX_BIND_TAC[] THEN REWRITE_TAC[st_ex_return_def]]);;

let infer_ds_complete = prove
 (`!tenv ds ids tenv' ienv st1.
     type_ds T tenv ds ids tenv' /\
     envRel_env_rel tenv ienv /\
     inf_set_tids_ienv (pred_set_count (infer_st_next_id st1)) ienv /\
     set_tids_tenv (pred_set_count (infer_st_next_id st1)) tenv /\
     DISJOINT ids (pred_set_count (infer_st_next_id st1)) /\
     start_type_id <= infer_st_next_id st1
     ==> ?g mapped_tenv' ienv' st2.
           infer_ds ienv ds st1 = (M_success ienv',st2) /\
           tenv_equiv (remap_tenv g tenv') mapped_tenv' /\
           envRel_env_rel mapped_tenv' ienv' /\
           infer_st_next_id st2 = infer_st_next_id st1 + CARD ids`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 type_d_type_d_canon)) THEN
  DISCH_THEN(MP_TAC o SPECL [`pred_set_count (infer_st_next_id st1)`; `I:num->num`;
                             `infer_st_next_id st1`; `tenv:type_env`]) THEN
  ASM_SIMP_TAC[start_type_id_prim_tids_count; good_remap_def; remap_tenv_I; I_THM;
               MAP_I; I_PERMUTES; tenv_equiv_refl] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->num` (X_CHOOSE_THEN `mapped_tenv':type_env`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`ds:dec list`; `infer_st_next_id st1`; `tenv:type_env`; `CARD (ids:num->bool)`;
                `mapped_tenv':type_env`; `ienv:inf_env`; `st1:infer_st`]
    (CONJUNCT2 infer_d_complete_canon)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ienv':inf_env` (X_CHOOSE_THEN `st2:infer_st`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`extend_bij I g (ids:num->bool) (infer_st_next_id st1)`;
                        `mapped_tenv':type_env`; `ienv':inf_env`; `st2:infer_st`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 lines 1446-1788 of inferCompleteScript.sml (check_specs_complete,    *)
(* n_fresh_uvar_rw, t_walkstar_infer_deBruijn_subst,                         *)
(* infer_deBruijn_subst_check_t, check_tscheme_inst_complete,                *)
(* check_weak_ienv_complete, check_weak_decls_complete) are inside a comment *)
(* in the source: not ported.                                                *)
