(* ========================================================================= *)
(* inferProps: port of HOL4 compiler/inference/inferPropsScript.sml (CakeML  *)
(* v3479).  Various lemmas that are handy in the soundness and completeness  *)
(* proofs of the type inferencer.                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
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
needs "translator/monadic/monad_base/ml_monadBase.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Records: ienv.inf_v is inf_env_inf_v ienv, r with f := v is            *)
(*   R_f_fupd (K v) r, record literals are R_REC (fields in order).          *)
(* - HOL4 BIGUNION is UNIONS, set is set_of_list, EVERY is ALL, LIST_REL is  *)
(*   ALL2, ZIP (l1,l2) is ZIP l1 l2 (HOL Light's ZIP: equal lengths),        *)
(*   COUNT_LIST is rich_list's COUNT_LIST.                                    *)
(* - The free variables of a HOL4 statement are universally quantified.      *)
(* - Names (notes/naming/names.tsv): st_ex_return_success, ...,  hide are    *)
(*   inferProps_st_ex_return_success, ..., inferProps_hide.                  *)
(* - Helper lemmas that are not HOL4 theorems are TYSYS2AUX_.                *)
(* ------------------------------------------------------------------------- *)

let ienv_unchanged = prove
 (`!ienv:inf_env.
     inf_env_inf_v_fupd (K (inf_env_inf_v ienv)) ienv = ienv /\
     inf_env_inf_c_fupd (K (inf_env_inf_c ienv)) ienv = ienv /\
     inf_env_inf_t_fupd (K (inf_env_inf_t ienv)) ienv = ienv`,
  RW[inf_env_component_equality]);;
let _ = cake_add_simps [ienv_unchanged];;

let extend_dec_ienv_empty = prove
 (`!ienv.
     extend_dec_ienv ienv (inf_env_REC nsEmpty nsEmpty nsEmpty) = ienv /\
     extend_dec_ienv (inf_env_REC nsEmpty nsEmpty nsEmpty) ienv = ienv`,
  RW[extend_dec_ienv_def; inf_env_component_equality]);;

(* ---------- Facts about deBruijn increment ---------- *)

let infer_deBruijn_inc0 = prove
 (`!(n:num) t. infer_deBruijn_inc 0 t = t`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_inc_def; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[MAP_EQ_ID]);;

let infer_deBruijn_inc0_id = prove
 (`infer_deBruijn_inc 0 = (\x. x)`,
  REWRITE_TAC[FUN_EQ_THM; infer_deBruijn_inc0]);;

let t_vars_inc = prove
 (`!tvs t. t_vars (infer_deBruijn_inc tvs t) = t_vars t`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_inc_def; t_vars_eqn; GSYM MAP_o] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[MAP_EQ_f; o_THM]);;

let inc_wfs = prove
 (`!tvs (s:(num,infer_t)fmap). t_wfs s ==> t_wfs (infer_deBruijn_inc tvs o_f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[t_wfs_eqn] THEN
  SUBGOAL_THEN `t_vR (s:(num,infer_t)fmap) = t_vR (infer_deBruijn_inc tvs o_f s)`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MAP_EVERY X_GEN_TAC [`y:num`; `x:num`] THEN
  REWRITE_TAC[t_vR_eqn; FLOOKUP_o_f] THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) x` THEN
  REWRITE_TAC[option_CASE; t_vars_inc]);;

let vwalk_inc = prove
 (`!(s:(num,infer_t)fmap) tvs n.
     t_wfs s
     ==> t_vwalk (infer_deBruijn_inc tvs o_f s) n =
         infer_deBruijn_inc tvs (t_vwalk s n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_deBruijn_inc tvs o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[inc_wfs]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind o
              check (fun th -> concl th = `t_wfs (s:(num,infer_t)fmap)`)) THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `infer_deBruijn_inc tvs o_f (s:(num,infer_t)fmap)` t_vwalk_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `s:(num,infer_t)fmap` t_vwalk_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[FLOOKUP_o_f] THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) n` THEN
  REWRITE_TAC[option_CASE; infer_deBruijn_inc_def] THEN
  CASES_ON `a:infer_t` THEN
  REWRITE_TAC[case_def "infer_t"; infer_deBruijn_inc_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let walk_inc = prove
 (`!(s:(num,infer_t)fmap) tvs t.
     t_wfs s
     ==> t_walk (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) =
         infer_deBruijn_inc tvs (t_walk s t)`,
  REPEAT STRIP_TAC THEN CASES_ON `t:infer_t` THEN
  ASM_SIMP_TAC[t_walk_eqn; infer_deBruijn_inc_def; vwalk_inc]);;

let walkstar_inc = prove
 (`!tvs (s:(num,infer_t)fmap) t.
     t_wfs s
     ==> t_walkstar (infer_deBruijn_inc tvs o_f s) (infer_deBruijn_inc tvs t) =
         infer_deBruijn_inc tvs (t_walkstar s t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_deBruijn_inc tvs o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[inc_wfs]; ALL_TAC] THEN
  SPEC_TAC(`t:infer_t`,`t:infer_t`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind o
              check (fun th -> concl th = `t_wfs (s:(num,infer_t)fmap)`)) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN
  MP_TAC(SPEC `infer_deBruijn_inc tvs o_f (s:(num,infer_t)fmap)` t_walkstar_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `s:(num,infer_t)fmap` t_walkstar_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[walk_inc] THEN
  CASES_ON `t_walk (s:(num,infer_t)fmap) t` THEN
  REWRITE_TAC[infer_deBruijn_inc_def; case_def "infer_t"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o; MAP_EQ_f; o_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let walkstar_inc2 = prove
 (`!tvs (s:(num,infer_t)fmap) n.
     t_wfs s
     ==> t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
         infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n))`,
  SIMP_TAC[GSYM walkstar_inc; infer_deBruijn_inc_def]);;

(* ---------- Type substitution ---------- *)

let subst_infer_subst_swap = prove
 (`(!t tvs (s:(num,infer_t)fmap) uvar.
     t_wfs s
     ==> t_walkstar s
           (infer_type_subst
              (ZIP tvs (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs)))) t) =
         infer_type_subst
           (ZIP tvs (MAP (\n. t_walkstar s (Infer_Tuvar (uvar + n)))
                         (COUNT_LIST (LENGTH tvs)))) t) /\
   (!ts tvs (s:(num,infer_t)fmap) uvar.
     t_wfs s
     ==> MAP (t_walkstar s)
           (MAP (infer_type_subst
                   (ZIP tvs (MAP (\n. Infer_Tuvar (uvar + n))
                                 (COUNT_LIST (LENGTH tvs))))) ts) =
         MAP (infer_type_subst
                (ZIP tvs (MAP (\n. t_walkstar s (Infer_Tuvar (uvar + n)))
                              (COUNT_LIST (LENGTH tvs))))) ts)`,
  MATCH_MP_TAC t_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_type_subst_alt; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[t_walkstar_eqn1] THEN
  SUBGOAL_THEN
     `MAP (\n. t_walkstar (s:(num,infer_t)fmap) (Infer_Tuvar (uvar + n)))
          (COUNT_LIST (LENGTH (tvs:mlstring list))) =
      MAP (t_walkstar s) (MAP (\n. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs)))`
     SUBST1_TAC THENL [REWRITE_TAC[GSYM MAP_o; o_DEF]; ALL_TAC] THEN
    SIMP_TAC[ALOOKUP_ZIP_MAP_SND; LENGTH_MAP; LENGTH_COUNT_LIST; o_THM] THEN
    CASES_ON `ALOOKUP (ZIP (tvs:mlstring list) (COUNT_LIST (LENGTH tvs))) a` THEN
    ASM_SIMP_TAC[option_CASE; OPTION_MAP_DEF; t_walkstar_eqn1]);;

let infer_subst_FEMPTY = prove
 (`(!t. infer_subst FEMPTY t = t) /\
   (!ts. MAP (infer_subst FEMPTY) ts = ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[infer_subst_def; MAP; FLOOKUP_EMPTY; option_CASE]);;

let TYSYS2AUX_FLOOKUP_SUBMAP_EQ = prove
 (`!(s1:(A,B)fmap) s2 k.
     s1 SUBMAP s2 /\ (k IN FDOM s1 \/ ~(k IN FDOM s2))
     ==> FLOOKUP s1 k = FLOOKUP s2 k`,
  REWRITE_TAC[SUBMAP_DEF; FLOOKUP_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let infer_subst_submap = prove
 (`(!t (s1:(num,num)fmap) s2 m.
      s1 SUBMAP s2 /\
      {uv | uv IN t_vars t /\ m <= uv} SUBSET FDOM s1 /\
      (!uv. uv IN FDOM s2 DIFF FDOM s1 ==> m <= uv)
      ==> infer_subst s1 t = infer_subst s2 t) /\
   (!ts (s1:(num,num)fmap) s2 m.
      s1 SUBMAP s2 /\
      {uv | ?s. uv IN s /\ MEM s (MAP t_vars ts) /\ m <= uv} SUBSET FDOM s1 /\
      (!uv. uv IN FDOM s2 DIFF FDOM s1 ==> m <= uv)
      ==> MAP (infer_subst s1) ts = MAP (infer_subst s2) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[infer_subst_def];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[infer_subst_def; injectivity "infer_t"] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{uv | uv IN t_vars (Infer_Tapp a0 a1) /\ m <= uv} SUBSET
                 FDOM (s1:(num,num)fmap)` THEN
    REWRITE_TAC[t_vars_eqn; SUBSET; IN_ELIM_THM; IN_UNIONS; IN_SET_OF_LIST] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[infer_subst_def] THEN
    SUBGOAL_THEN `FLOOKUP (s1:(num,num)fmap) a = FLOOKUP s2 a`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC TYSYS2AUX_FLOOKUP_SUBMAP_EQ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{uv | uv IN t_vars (Infer_Tuvar a) /\ m <= uv} SUBSET
                 FDOM (s1:(num,num)fmap)` THEN
    UNDISCH_TAC `!uv. uv IN FDOM (s2:(num,num)fmap) DIFF FDOM (s1:(num,num)fmap)
                     ==> m <= uv` THEN
    REWRITE_TAC[t_vars_eqn; SUBSET; IN_ELIM_THM; IN_SING; IN_DIFF] THEN
    MESON_TAC[];
    REWRITE_TAC[MAP];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[MAP; CONS_11] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{uv | ?s. uv IN s /\ MEM s (MAP t_vars (CONS a0 a1)) /\ m <= uv}
                 SUBSET FDOM (s1:(num,num)fmap)` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; MAP; MEM] THEN MESON_TAC[]]);;

let generalise_list_length = prove
 (`!a b c d e f g.
     generalise_list a b c d = (e,f,g) ==> LENGTH g = LENGTH d`,
  SUBGOAL_THEN
   `!d a b c e f g. generalise_list a b c d = (e,f,g) ==> LENGTH g = LENGTH d`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[generalise_def; PAIR_EQ] THENL
   [MESON_TAC[LENGTH]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `generalise a b c (h:infer_t)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `p1:(num,num)fmap#infer_t`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `p1:(num,num)fmap#infer_t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN `t1:infer_t`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `generalise_list a (n1 + b) s1 (t:infer_t list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `p2:(num,num)fmap#(infer_t list)`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  MP_TAC(ISPEC `p2:(num,num)fmap#(infer_t list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(num,num)fmap` (X_CHOOSE_THEN `ts2:infer_t list`
    SUBST_ALL_TAC)) THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  ASM_MESON_TAC[]);;

let generalise_subst = prove
 (`(!t m n (s:(num,num)fmap) tvs s' t'.
      generalise m n s t = (tvs,s',t')
      ==> s SUBMAP s' /\
          FDOM s' = FDOM s UNION {uv | uv IN t_vars t /\ m <= uv} /\
          (!uv. uv IN FDOM s' DIFF FDOM s
                ==> ?tv. FAPPLY s' uv = tv /\ n <= tv /\ tv < tvs + n) /\
          (!uv. uv IN t_vars t' ==> uv < m) /\
          infer_subst s' t = infer_subst s t') /\
   (!ts m n (s:(num,num)fmap) tvs s' ts'.
      generalise_list m n s ts = (tvs,s',ts')
      ==> s SUBMAP s' /\
          FDOM s' = FDOM s UNION
                    {uv | uv IN UNIONS (set_of_list (MAP t_vars ts)) /\ m <= uv} /\
          (!uv. uv IN FDOM s' DIFF FDOM s
                ==> ?tv. FAPPLY s' uv = tv /\ n <= tv /\ tv < tvs + n) /\
          (!uv. uv IN UNIONS (set_of_list (MAP t_vars ts')) ==> uv < m) /\
          MAP (infer_subst s') ts = MAP (infer_subst s) ts')`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[generalise_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[SUBMAP_REFL; t_vars_eqn; NOT_IN_EMPTY; IN_DIFF; infer_subst_def] THEN
  SET_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[generalise_def] THEN
  X_CHOOSE_THEN `g1:num` (X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN
    `ts1:infer_t list` ASSUME_TAC))
    (ISPEC `generalise_list m n s (a0:infer_t list)` BASICAUX_TUPLE3) THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`m:num`; `n:num`; `s:(num,num)fmap`; `g1:num`;
                                   `s1:(num,num)fmap`; `ts1:infer_t list`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[t_vars_eqn; infer_subst_def; injectivity "infer_t"] THEN SIMP_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def] THEN
  CASES_ON `FLOOKUP (s:(num,num)fmap) a` THEN REWRITE_TAC[option_CASE] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm]) THEN
    ASM_REWRITE_TAC[t_vars_eqn; infer_subst_def; FLOOKUP_UPDATE; option_CASE; IN_SING;
                    NOT_IN_EMPTY; SUBMAP_REFL; FDOM_FUPDATE; IN_DIFF; IN_INSERT] THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
        ASM_MESON_TAC[];
        UNDISCH_TAC `m <= (a:num)` THEN SET_TAC[];
        GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN `uv = (a:num)` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN EXISTS_TAC `n:num` THEN ARITH_TAC];
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(m <= (a:num))` THEN SET_TAC[];
        MESON_TAC[];
        UNDISCH_TAC `~(m <= (a:num))` THEN MESON_TAC[NOT_LE]]];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    ASM_REWRITE_TAC[t_vars_eqn; infer_subst_def; option_CASE; SUBMAP_REFL; IN_DIFF;
                    NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm]) THEN
    UNDISCH_TAC `(a:num) IN FDOM (s:(num,num)fmap) /\ FAPPLY s a = a'` THEN SET_TAC[]];
    REWRITE_TAC[generalise_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[SUBMAP_REFL; MAP; set_of_list; UNIONS_0; NOT_IN_EMPTY; IN_DIFF] THEN
    SET_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iht") (LABEL_TAC "ihts")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def] THEN
  X_CHOOSE_THEN `g1:num` (X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN
    `t1:infer_t` ASSUME_TAC))
    (ISPEC `generalise m n s (a0:infer_t)` BASICAUX_TUPLE3) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  X_CHOOSE_THEN `g2:num` (X_CHOOSE_THEN `s2:(num,num)fmap` (X_CHOOSE_THEN
    `ts2:infer_t list` ASSUME_TAC))
    (ISPEC `generalise_list m (g1 + n) s1 (a1:infer_t list)` BASICAUX_TUPLE3) THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REMOVE_THEN "iht" (MP_TAC o SPECL [`m:num`; `n:num`; `s:(num,num)fmap`; `g1:num`;
                                    `s1:(num,num)fmap`; `t1:infer_t`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihts" (MP_TAC o SPECL [`m:num`; `g1 + n:num`; `s1:(num,num)fmap`; `g2:num`;
                                     `s2:(num,num)fmap`; `ts2:infer_t list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBMAP_TRANS];
    ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT] THEN SET_TAC[];
    X_GEN_TAC `uv:num` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  ASM_CASES_TAC `uv IN FDOM (s1:(num,num)fmap)` THENL
   [UNDISCH_TAC `!uv. uv IN FDOM (s1:(num,num)fmap) DIFF FDOM (s:(num,num)fmap)
                      ==> (?tv. FAPPLY s1 uv = tv /\ (n:num) <= tv /\ tv < g1 + n)` THEN
    DISCH_THEN(MP_TAC o SPEC `uv:num`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tv:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tv:num` THEN
    SUBGOAL_THEN `FAPPLY (s2:(num,num)fmap) uv = FAPPLY s1 uv` SUBST1_TAC THENL
     [ASM_MESON_TAC[SUBMAP_DEF]; ASM_ARITH_TAC];
    UNDISCH_TAC `!uv. uv IN FDOM (s2:(num,num)fmap) DIFF
                      (FDOM (s:(num,num)fmap) UNION {uv | uv IN t_vars a0 /\ (m:num) <= uv})
                      ==> (?tv. FAPPLY s2 uv = tv /\ g1 + (n:num) <= tv /\ tv < g2 + g1 + n)` THEN
    DISCH_THEN(MP_TAC o SPEC `uv:num`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `tv:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `tv:num` THEN ASM_ARITH_TAC]];
    REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; IN_UNION] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MAP; CONS_11] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `infer_subst (s2:(num,num)fmap) a0 = infer_subst s1 a0` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC (CONJUNCT1 infer_subst_submap) THEN
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SET_TAC[];
        UNDISCH_TAC `FDOM (s2:(num,num)fmap) =
           (FDOM (s:(num,num)fmap) UNION {uv | uv IN t_vars a0 /\ (m:num) <= uv}) UNION
           {uv | uv IN UNIONS (set_of_list (MAP t_vars a1)) /\ m <= uv}` THEN
        SET_TAC[]];
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC (CONJUNCT2 infer_subst_submap) THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!uv. uv IN UNIONS (set_of_list (MAP t_vars ts2)) ==> uv < (m:num)` THEN
      REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST] THEN
      DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
      SET_TAC[]]]]]);;

let generalise_subst_empty = prove
 (`!n ts tvs (s:(num,num)fmap) ts'.
     generalise_list 0 n FEMPTY ts = (tvs,s,ts')
     ==> FDOM s = {uv | uv IN UNIONS (set_of_list (MAP t_vars ts))} /\
         (!uv. uv IN FDOM s ==> ?tv. FAPPLY s uv = tv /\ tv < tvs + n) /\
         UNIONS (set_of_list (MAP t_vars ts')) = {} /\
         ts' = MAP (infer_subst s) ts`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT2 generalise_subst)) THEN
  REWRITE_TAC[FDOM_FEMPTY; UNION_EMPTY; LE_0; IN_DIFF; NOT_IN_EMPTY; LT;
              infer_subst_FEMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]]);;

(* ---------- Dealing with the monad ---------- *)

let infer_st_rewrs = prove
 (`(!st. infer_st_next_uvar_fupd (K (infer_st_next_uvar st)) st = st) /\
   (!st. infer_st_subst_fupd (K (infer_st_subst st)) st = st) /\
   (!st s. infer_st_subst (infer_st_subst_fupd (K s) st) = s) /\
   (!st s. infer_st_next_uvar (infer_st_subst_fupd (K s) st) = infer_st_next_uvar st) /\
   (!st uv. infer_st_next_uvar (infer_st_next_uvar_fupd (K uv) st) = uv) /\
   (!st uv. infer_st_subst (infer_st_next_uvar_fupd (K uv) st) = infer_st_subst st)`,
  RW[infer_st_component_equality]);;

let inferProps_st_ex_return_success = prove
 (`!(v:A) (st:S) v' st'.
     st_ex_return v st = (M_success v':(A,E)exc,st') <=> v = v' /\ st = st'`,
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"]);;

let inferProps_st_ex_bind_success = prove
 (`!(f:S->(A,E)exc#S) (g:A->S->(B,E)exc#S) st st' v.
     st_ex_bind f g st = (M_success v,st') <=>
     ?v' st''. f st = (M_success v',st'') /\ g v' st'' = (M_success v,st')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[st_ex_bind_def] THEN
  MP_TAC(ISPEC `(f:S->(A,E)exc#S) st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A,E)exc` (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  CASES_ON `q:(A,E)exc` THEN
  REWRITE_TAC[pair_CASE; case_def "exc"; PAIR_EQ; injectivity "exc";
              distinctness "exc"] THEN
  MESON_TAC[]);;

let st_ex_ignore_bind_success = prove
 (`!(f:S->(A,E)exc#S) (g:S->(B,E)exc#S) st st' v.
     st_ex_ignore_bind f g st = (M_success v,st') <=>
     ?v' st''. f st = (M_success v',st'') /\ g st'' = (M_success v,st')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[st_ex_ignore_bind_def] THEN
  MP_TAC(ISPEC `(f:S->(A,E)exc#S) st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A,E)exc` (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  CASES_ON `q:(A,E)exc` THEN
  REWRITE_TAC[pair_CASE; case_def "exc"; PAIR_EQ; injectivity "exc";
              distinctness "exc"] THEN
  MESON_TAC[]);;

let fresh_uvar_success = prove
 (`!st t st'.
     fresh_uvar st = (M_success t:(infer_t,E)exc,st') <=>
     t = Infer_Tuvar (infer_st_next_uvar st) /\
     st' = infer_st_next_uvar_fupd (K (infer_st_next_uvar st + 1)) st`,
  REWRITE_TAC[fresh_uvar_def; PAIR_EQ; injectivity "exc"] THEN MESON_TAC[]);;

let n_fresh_uvar_success = prove
 (`!n st ts st'.
     n_fresh_uvar n st = (M_success ts:(infer_t list,E)exc,st') <=>
     ts = MAP (\n. Infer_Tuvar (infer_st_next_uvar st + n)) (COUNT_LIST n) /\
     st' = infer_st_next_uvar_fupd (K (infer_st_next_uvar st + n)) st`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[n_fresh_uvar_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1] THENL
   [REWRITE_TAC[inferProps_st_ex_return_success; COUNT_LIST_DEF; MAP; ADD_CLAUSES;
                infer_st_rewrs] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[inferProps_st_ex_bind_success; fresh_uvar_success;
                  inferProps_st_ex_return_success] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[infer_st_rewrs; COUNT_LIST_DEF; MAP; GSYM MAP_o; o_DEF; ADD_CLAUSES] THEN
  RW[ARITH_RULE `(a + 1) + n = a + SUC n`; ARITH_RULE `(a + 1) + k = SUC (a + k)`] THEN
  MESON_TAC[]);;

let apply_subst_success = prove
 (`!t1 st1 t2 st2.
     apply_subst t1 st1 = (M_success t2:(infer_t,E)exc,st2) <=>
     st2 = st1 /\ t2 = t_walkstar (infer_st_subst st1) t1`,
  REWRITE_TAC[apply_subst_def; inferProps_st_ex_bind_success; infer_read_def;
              inferProps_st_ex_return_success; PAIR_EQ; injectivity "exc"] THEN
  MESON_TAC[]);;

let add_constraint_success = prove
 (`!(l:loc_err_info) t1 t2 st st' x.
     add_constraint l t1 t2 st = (M_success x,st') <=>
     x = one /\ ?s. t_unify (infer_st_subst st) t1 t2 = SOME s /\
                    st' = infer_st_subst_fupd (K s) st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[add_constraint_def] THEN
  CASES_ON `t_unify (infer_st_subst st) t1 t2` THEN
  REWRITE_TAC[option_CASE; PAIR_EQ; injectivity "exc"; distinctness "exc";
              option_DISTINCT; injectivity "option"] THEN
  MESON_TAC[one]);;

let add_constraints_success = prove
 (`!(l:loc_err_info) ts1 ts2 st st' x.
     add_constraints l ts1 ts2 st = (M_success x,st') <=>
     LENGTH ts1 = LENGTH ts2 /\
     x = one /\
     infer_st_next_uvar st = infer_st_next_uvar st' /\
     infer_st_next_id st = infer_st_next_id st' /\
     pure_add_constraints (infer_st_subst st) (ZIP ts1 ts2) (infer_st_subst st')`,
  MATCH_MP_TAC add_constraints_ind THEN
  REWRITE_TAC[add_constraints_def; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP;
              pure_add_constraints_def; inferProps_st_ex_return_success; failwith_def;
              PAIR_EQ; distinctness "exc"] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[infer_st_component_equality] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[inferProps_st_ex_bind_success; add_constraint_success;
                    inferProps_st_ex_return_success] THEN
    SIMP[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    MESON_TAC[one]]);;

let add_constraints_nil2_success = prove
 (`!(l:loc_err_info) ts1 st x st'.
     add_constraints l ts1 [] st = (M_success x,st') <=> ts1 = [] /\ st = st'`,
  REPEAT GEN_TAC THEN CASES_ON `ts1:infer_t list` THEN
  REWRITE_TAC[add_constraints_def; failwith_def; inferProps_st_ex_return_success;
              PAIR_EQ; distinctness "exc"; NOT_CONS_NIL] THEN
  MESON_TAC[one]);;

let add_constraints_cons2_success = prove
 (`!(l:loc_err_info) ts1 t2 ts2 st x st'.
     add_constraints l ts1 (CONS t2 ts2) st = (M_success x,st') <=>
     ?t1 tl1 st''. ts1 = CONS t1 tl1 /\
                   add_constraint l t1 t2 st = (M_success one,st'') /\
                   add_constraints l tl1 ts2 st'' = (M_success x,st')`,
  REPEAT GEN_TAC THEN CASES_ON `ts1:infer_t list` THEN
  REWRITE_TAC[add_constraints_def; failwith_def; inferProps_st_ex_return_success;
              inferProps_st_ex_bind_success; PAIR_EQ; distinctness "exc";
              NOT_CONS_NIL; CONS_11] THEN
  SIMP[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
  MESON_TAC[one]);;

let failwith_success = prove
 (`!(l:loc_err_info) (m:A) (st:S) (v:B) st'.
     failwith l m st = (M_success v,st') <=> F`,
  REWRITE_TAC[failwith_def; PAIR_EQ; distinctness "exc"]);;

let lookup_st_ex_success = prove
 (`!(loc:loc_err_info) x err (l:(mlstring,mlstring,V)namespace) (st:S) v st'.
     lookup_st_ex loc err x l st = (M_success v,st') <=>
     nsLookup l x = SOME v /\ st = st'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_st_ex_def] THEN
  CASES_ON `nsLookup (l:(mlstring,mlstring,V)namespace) x` THEN
  REWRITE_TAC[option_CASE; PAIR_EQ; distinctness "exc"; injectivity "exc";
              option_DISTINCT; injectivity "option"] THEN
  MESON_TAC[]);;

let UNCURRY_rator = prove
 (`!(f:A->B->C->D) x y. UNCURRY f x y = UNCURRY (\a b. f a b y) x`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:A#B` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[UNCURRY_DEF]);;

(* HOL4's constrain_op_success is the value of a conversion on             *)
(* constrain_op l op ts st = (M_success v,st') (after splitting on op with  *)
(* the local constrain_op_op_case).  Here it is the conjunction of the      *)
(* results of the conversion TYSYS2AUX_constrain_op_success_conv on         *)
(* constrain_op l (C x1 .. xn) ts st = (M_success v,st') for each           *)
(* constructor C of op.                                                      *)

let TYSYS2AUX_constrain_op_success_conv =
  REWRITE_CONV[constrain_op_def; op_simple_constraints_def] THENC
  CASE_REWRITE_CONV[] THENC
  REWRITE_CONV([inferProps_st_ex_bind_success; inferProps_st_ex_return_success;
                add_constraint_success; add_constraints_cons2_success;
                add_constraints_nil2_success; failwith_success; fresh_uvar_success;
                LENGTH; MAP; I_THM; PAIR_EQ] @ all_case_eqs()) THENC
  CAKE_SIMP_CONV[];;

let constrain_op_success =
  let nch = nchotomy_of_type `:op` in
  let disjs = disjuncts (snd(dest_forall(concl nch))) in
  let pats = map (fun d -> rand(snd(strip_exists d))) disjs in
  let mk p =
    let lhs = list_mk_comb(`constrain_op (l:loc_err_info)`,
                           [p; `ts:infer_t list`; `st:infer_st`]) in
    let tm = mk_eq(lhs, `(M_success v:(infer_t,locs option#mlstring)exc,st':infer_st)`) in
    GEN_ALL(TYSYS2AUX_constrain_op_success_conv tm) in
  end_itlist CONJ (map mk pats);;

let get_next_uvar_success = prove
 (`!st v st'.
     get_next_uvar st = (M_success v:(num,E)exc,st') <=>
     v = infer_st_next_uvar st /\ st = st'`,
  REWRITE_TAC[get_next_uvar_def; PAIR_EQ; injectivity "exc"] THEN MESON_TAC[]);;

(* HOL4: val apply_subst_list_success (an ML value used in success_eqns) *)

let TYSYS2AUX_apply_subst_list_success = prove
 (`!ts st v st'.
     apply_subst_list ts st = (M_success v:(infer_t list,E)exc,st') <=>
     MAP (t_walkstar (infer_st_subst st)) ts = v /\ st = st'`,
  REWRITE_TAC[apply_subst_list_def; inferProps_st_ex_bind_success; infer_read_def;
              inferProps_st_ex_return_success; PAIR_EQ; injectivity "exc"] THEN
  MESON_TAC[]);;

let guard_success = prove
 (`!P (l:loc_err_info) (m:A) (st:S) v st'.
     infer_guard P l m st = (M_success v,st') <=> P /\ v = one /\ st = st'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[infer_guard_def; st_ex_return_def; failwith_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"] THEN
  MESON_TAC[one]);;

let check_dups_success = prove
 (`!(l:loc_err_info) (f:A->B) ls (s:S) r s'.
     check_dups l f ls s = (M_success r,s') <=> s' = s /\ ALL_DISTINCT ls`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[check_dups_def; st_ex_return_def; failwith_def; ALL_DISTINCT;
                  PAIR_EQ; injectivity "exc"; distinctness "exc"] THENL
   [MESON_TAC[one]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ; distinctness "exc"]);;

let TYSYS2AUX_TNC_TAC =
  ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[inferProps_st_ex_return_success; PAIR_EQ; distinctness "exc"] THEN
  SIMP[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
  TRY(MESON_TAC[]);;

let type_name_check_subst_success = prove
 (`(!t (l:loc_err_info) f (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tvs r
      (s:S) s'.
     type_name_check_subst l f tenvT tvs t s = (M_success r,s') <=>
     s = s' /\ r = type_name_subst tenvT t /\
     check_freevars_ast tvs t /\ check_type_names tenvT t) /\
   (!ts (l:loc_err_info) f (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tvs r
      (s:S) s'.
     type_name_check_subst_list l f tenvT tvs ts s = (M_success r,s') <=>
     s = s' /\ r = MAP (type_name_subst tenvT) ts /\
     ALL (check_freevars_ast tvs) ts /\ ALL (check_type_names tenvT) ts)`,
  MATCH_MP_TAC ast_t_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[type_name_check_subst_def; ignore_bind_guard; st_ex_ignore_bind_success;
              inferProps_st_ex_bind_success; inferProps_st_ex_return_success;
              lookup_st_ex_success; guard_success; type_name_subst_def;
              check_freevars_ast_def; check_type_names_def; MAP; ALL] THENL
   [TYSYS2AUX_TNC_TAC;
    TYSYS2AUX_TNC_TAC;
    TYSYS2AUX_TNC_TAC;
    ASM_REWRITE_TAC[] THEN
    CASES_ON `nsLookup (tenvT:(mlstring,mlstring,mlstring list#t)namespace) a1` THEN
    REWRITE_TAC[option_CASE; option_DISTINCT; injectivity "option"; LET_DEF;
                LET_END_DEF] THEN
    SIMP[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    MP_TAC(ISPEC `a:mlstring list#t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `tvs1:mlstring list` (X_CHOOSE_THEN `t1:t` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[inferProps_st_ex_return_success; PAIR_EQ; distinctness "exc"] THEN
    MESON_TAC[];
    MESON_TAC[];
    TYSYS2AUX_TNC_TAC]);;

let check_ctor_types_success = prove
 (CASE_TERM `!(l:loc_err_info) (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
     tvs ts (s:S) s'.
     check_ctor_types l tenvT tvs ts s = (M_success one,s') <=>
     s = s' /\
     ALL (\p. match p with
                (cn,ts) -> ALL (check_freevars_ast tvs) ts /\
                           ALL (check_type_names tenvT) ts) ts`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[check_ctor_types_def; inferProps_st_ex_return_success; ALL] THEN
  MP_TAC(ISPEC `h:mlstring#ast_t list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cn:mlstring` (X_CHOOSE_THEN `ts1:ast_t list`
    SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[check_ctor_types_def; st_ex_ignore_bind_success;
                  type_name_check_subst_success; pair_CASE] THEN
  MESON_TAC[]);;

let inferProps_check_dup_ctors_thm = prove
 (`!tvs tn condefs.
     check_dup_ctors (tvs,tn,condefs) <=> ALL_DISTINCT (MAP FST condefs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_dup_ctors_def; LET_DEF; LET_END_DEF] THEN
  AP_TERM_TAC THEN SPEC_TAC(`condefs:(mlstring#ast_t list)list`,
                            `condefs:(mlstring#ast_t list)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAP] THEN
  MP_TAC(ISPEC `h:mlstring#ast_t list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:mlstring` (X_CHOOSE_THEN `ts:ast_t list`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE; FST]);;

let TYSYS2AUX_MAP_SND_FST = prove
 (CASE_TERM `!tds:(A#B#C)list.
     MAP (\p. match p with (_,tn,_) -> tn) tds = MAP (FST o SND) tds`,
  REWRITE_TAC[MAP_EQ_f; o_THM] THEN REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `c:C` SUBST1_TAC))
    (ISPEC `e:A#B#C` BASICAUX_TUPLE3) THEN
  REWRITE_TAC[pair_CASE; FST; SND]);;

let check_ctors_success = prove
 (`!(l:loc_err_info) (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tds
    (s:S) s'.
     ALL_DISTINCT (MAP (FST o SND) tds)
     ==> (check_ctors l tenvT tds s = (M_success one,s') <=>
          s' = s /\ check_ctor_tenv tenvT tds)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[check_ctors_def; check_ctor_tenv_def; inferProps_st_ex_return_success] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `tn:mlstring` (X_CHOOSE_THEN
    `ctors:(mlstring#ast_t list)list` SUBST1_TAC))
    (ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` BASICAUX_TUPLE3) THEN
  REWRITE_TAC[MAP; o_THM; FST; SND; ALL_DISTINCT; check_ctors_def;
              check_ctor_tenv_def; st_ex_ignore_bind_success; check_dups_success;
              inferProps_check_dup_ctors_thm; TYSYS2AUX_MAP_SND_FST] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl o SPEC_ALL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s1 (s2:S) v. check_ctor_types l tenvT tvs ctors s1 = (M_success v,s2) <=>
       s1 = s2 /\
       ALL (\cnts. pair_CASE cnts (\cn ts. ALL (check_freevars_ast tvs) ts /\
                                        ALL (check_type_names tenvT) ts)) ctors`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MESON[one] `(v:1) = one`] THEN
    REWRITE_TAC[check_ctor_types_success];
    SIMP[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    MESON_TAC[]]);;

let TYSYS2AUX_check_ctor_tenv_distinct = prove
 (`!(tenvT:(mlstring,mlstring,mlstring list#t)namespace) tds.
     check_ctor_tenv tenvT tds ==> ALL_DISTINCT (MAP (FST o SND) tds)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `tn:mlstring` (X_CHOOSE_THEN
    `ctors:(mlstring#ast_t list)list` SUBST1_TAC))
    (ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` BASICAUX_TUPLE3) THEN
  REWRITE_TAC[check_ctor_tenv_def; o_THM; FST; SND; TYSYS2AUX_MAP_SND_FST] THEN
  ASM_MESON_TAC[]);;

let check_type_definition_success = prove
 (`!(l:loc_err_info) (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tds
    (s:S) r s'.
     check_type_definition l tenvT tds s = (M_success r,s') <=>
     s' = s /\ check_ctor_tenv tenvT tds`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[check_type_definition_def; st_ex_ignore_bind_success; check_dups_success] THEN
  ONCE_REWRITE_TAC[MESON[one] `(r:1) = one`] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th))))) THEN
    MP_TAC(ISPECL [`l:loc_err_info`; `tenvT:(mlstring,mlstring,mlstring list#t)namespace`;
                   `tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                   `s:S`; `s':S`] check_ctors_success) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN EXISTS_TAC `s:S` THEN
    SUBGOAL_THEN `ALL_DISTINCT (MAP (FST o SND)
                   (tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list))`
      ASSUME_TAC THENL [ASM_MESON_TAC[TYSYS2AUX_check_ctor_tenv_distinct]; ALL_TAC] THEN
    ASM_SIMP_TAC[check_ctors_success]]);;

let inferProps_option_case_eq = prove
 (CASE_TERM `!(opt:A option) (f:S->(B,E)exc#S) g v st st'.
     (match opt with NONE -> f | SOME x -> g x) st = (M_success v,st') <=>
     (opt = NONE /\ f st = (M_success v,st')) \/
     (?x. opt = SOME x /\ g x st = (M_success v,st'))`,
  REPEAT GEN_TAC THEN CASES_ON `opt:A option` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; injectivity "option"] THEN MESON_TAC[]);;

(* HOL4's success_eqns also contains oneTheory.one (!v. v = ()), which      *)
(* loops as a rewrite in HOL Light: left out                                *)

let success_eqns = end_itlist CONJ
  [inferProps_st_ex_return_success; inferProps_st_ex_bind_success;
   st_ex_ignore_bind_success; fresh_uvar_success; apply_subst_success;
   add_constraint_success; lookup_st_ex_success; n_fresh_uvar_success;
   failwith_success; add_constraints_success; check_type_definition_success;
   get_next_uvar_success; TYSYS2AUX_apply_subst_list_success; guard_success;
   infer_read_def; inferProps_option_case_eq; check_dups_success;
   type_name_check_subst_success; check_ctor_types_success; check_ctors_success];;

let remove_pair_lem = prove
 (CASE_TERM `(!(f:A->B->C) v. (\p. match p with (x,y) -> f x y) v = f (FST v) (SND v)) /\
   (!(f:A->B->D->C) v. (\p. match p with (x,y,z) -> f x y z) v =
                       f (FST v) (FST (SND v)) (SND (SND v)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MP_TAC(ISPEC `v:A#B` PAIR_SURJECTIVE) THEN STRIP_TAC;
    X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `c:D` SUBST1_TAC))
      (ISPEC `v:A#B#D` BASICAUX_TUPLE3)] THEN
  ASM_REWRITE_TAC[pair_CASE; FST; SND]);;

let infer_funs_length = prove
 (`!l ienv funs ts st1 st2.
     infer_funs l ienv funs st1 = (M_success ts,st2) ==> LENGTH funs = LENGTH ts`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[infer_e_def; success_eqns] THEN MESON_TAC[LENGTH];
    X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `x:mlstring`
      (X_CHOOSE_THEN `e:exp` SUBST1_TAC))
      (ISPEC `h:mlstring#mlstring#exp` BASICAUX_TUPLE3) THEN
    REWRITE_TAC[infer_e_def; success_eqns] THEN REPEAT STRIP_TAC THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]]);;

(* State preservation through the monad combinators, for                    *)
(* type_name_check_subst_state                                               *)

let TYSYS2AUX_bind_state = prove
 (`!(m:S->(A,E)exc#S) (g:A->S->(B,E)exc#S) st r st'.
     (!st r st'. m st = (r,st') ==> st = st') /\
     (!x st r st'. g x st = (r,st') ==> st = st')
     ==> st_ex_bind m g st = (r,st') ==> st = st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[st_ex_bind_def] THEN
  MP_TAC(ISPEC `(m:S->(A,E)exc#S) st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A,E)exc` (X_CHOOSE_THEN `s1:S`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `q:(A,E)exc` THEN REWRITE_TAC[pair_CASE; case_def "exc"; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let TYSYS2AUX_ignore_bind_state = prove
 (`!(m:S->(A,E)exc#S) (g:S->(B,E)exc#S) st r st'.
     (!st r st'. m st = (r,st') ==> st = st') /\
     (!st r st'. g st = (r,st') ==> st = st')
     ==> st_ex_ignore_bind m g st = (r,st') ==> st = st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[st_ex_ignore_bind_def] THEN
  MP_TAC(ISPEC `(m:S->(A,E)exc#S) st` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A,E)exc` (X_CHOOSE_THEN `s1:S`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASES_ON `q:(A,E)exc` THEN REWRITE_TAC[pair_CASE; case_def "exc"; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let TYSYS2AUX_pair_case_state = prove
 (CASE_TERM `!(p:A#B) (f:A->B->S->(C,E)exc#S) st r st'.
     (!a b st r st'. f a b st = (r,st') ==> st = st')
     ==> (match p with (a,b) -> f a b) st = (r,st') ==> st = st'`,
  GEN_TAC THEN MP_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN MESON_TAC[]);;

let TYSYS2AUX_return_state = prove
 (`!(x:A) (st:S) r st'. (st_ex_return x st = (r,st'):(A,E)exc#S) ==> st = st'`,
  REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN MESON_TAC[]);;

let TYSYS2AUX_guard_state = prove
 (`!P (l:loc_err_info) (msg:A) (st:S) r st'.
     infer_guard P l msg st = (r,st') ==> st = st'`,
  REWRITE_TAC[infer_guard_def; st_ex_return_def; failwith_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let TYSYS2AUX_lookup_state = prove
 (`!(l:loc_err_info) err id (ienv:(mlstring,mlstring,V)namespace) (st:S) r st'.
     lookup_st_ex l err id ienv st = (r,st') ==> st = st'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_st_ex_def] THEN
  CASES_ON `nsLookup (ienv:(mlstring,mlstring,V)namespace) id` THEN
  REWRITE_TAC[option_CASE; PAIR_EQ] THEN MESON_TAC[]);;

let TYSYS2AUX_STATE_TAC =
  REPEAT(REPEAT GEN_TAC THEN BETA_TAC THEN
         FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
                MAP_FIRST MATCH_ACCEPT_TAC
                  [TYSYS2AUX_return_state; TYSYS2AUX_guard_state;
                   TYSYS2AUX_lookup_state];
                MATCH_MP_TAC TYSYS2AUX_bind_state THEN CONJ_TAC;
                MATCH_MP_TAC TYSYS2AUX_ignore_bind_state THEN CONJ_TAC;
                MATCH_MP_TAC TYSYS2AUX_pair_case_state]);;

let type_name_check_subst_state = prove
 (`(!t l err tenvT fvs (st:S) r st'.
      type_name_check_subst l err tenvT fvs t st = (r,st') ==> st = st') /\
   (!ts l err tenvT fvs (st:S) r st'.
      type_name_check_subst_list l err tenvT fvs ts st = (r,st') ==> st = st')`,
  MATCH_MP_TAC ast_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; GEN_TAC THEN GEN_TAC THEN STRIP_TAC; GEN_TAC THEN DISCH_TAC;
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC; ALL_TAC;
    GEN_TAC THEN GEN_TAC THEN STRIP_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[type_name_check_subst_def] THEN
  TYSYS2AUX_STATE_TAC);;

let infer_p_bindings = prove
 (`(!l cenv p st t env st'.
      infer_p l cenv p st = (M_success (t,env),st') ==> pat_bindings p = MAP FST env) /\
   (!l cenv ps st ts env st'.
      infer_ps l cenv ps st = (M_success (ts,env),st') ==>
      pats_bindings ps = MAP FST env)`,
  MATCH_MP_TAC infer_p_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  REWRITE_TAC[pat_bindings_def; infer_p_def; success_eqns; PAIR_EQ;
              EXISTS_PAIR_THM; pair_CASE] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN GVS[MAP_APPEND; MAP; FST]);;

let pure_add_constraints_append2 = prove
 (`!s1 ts s2 t1 t2.
     t_wfs s1 /\ pure_add_constraints s1 ts s2 /\ t_walkstar s1 t1 = t_walkstar s1 t2
     ==> t_walkstar s2 t1 = t_walkstar s2 t2`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[];
    MP_TAC(ISPEC `h:infer_t#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:infer_t` (X_CHOOSE_THEN `b:infer_t` SUBST1_TAC)) THEN
    REWRITE_TAC[pure_add_constraints_def] THEN
    ASM_MESON_TAC[t_unify_wfs; t_unify_apply2]]);;

let pure_add_constraints_apply = prove
 (`!s1 ts s2.
     t_wfs s1 /\ pure_add_constraints s1 ts s2
     ==> MAP (t_walkstar s2 o FST) ts = MAP (t_walkstar s2 o SND) ts`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:infer_t#infer_t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:infer_t` (X_CHOOSE_THEN `b:infer_t` SUBST1_TAC)) THEN
  REWRITE_TAC[pure_add_constraints_def; MAP; o_THM; CONS_11] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC pure_add_constraints_append2 THEN
    EXISTS_TAC `s2':(num,infer_t)fmap` THEN EXISTS_TAC `t:(infer_t#infer_t)list` THEN
    ASM_MESON_TAC[t_unify_wfs; t_unify_apply];
    ASM_MESON_TAC[t_unify_wfs]]);;

let pure_add_constraints_append = prove
 (`!s1 ts1 s3 ts2.
     pure_add_constraints s1 (APPEND ts1 ts2) s3 <=>
     ?s2. pure_add_constraints s1 ts1 s2 /\ pure_add_constraints s2 ts2 s3`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def; APPEND] THEN MESON_TAC[];
    MP_TAC(ISPEC `h:infer_t#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:infer_t` (X_CHOOSE_THEN `b:infer_t` SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[pure_add_constraints_def; APPEND] THEN MESON_TAC[]]);;

(* Preservation of a relation between the initial and the final state by  *)
(* successful runs of a state-exception computation: a local device that  *)
(* proves infer_p_constraints, infer_e_constraints, ..._next_uvar_mono    *)
(* and ..._wfs from one induction each (TYSYS2AUX_infer_p_pres,            *)
(* TYSYS2AUX_infer_e_pres).                                                *)

let TYSYS2AUX_pres_def = new_definition
 `TYSYS2AUX_pres (R:S->S->bool) (m:S->(A,E)exc#S) <=>
    !st v st'. m st = (M_success v,st') ==> R st st'`;;

let TYSYS2AUX_pres_bind = prove
 (`!R (m:S->(A,E)exc#S) (g:A->S->(B,E)exc#S).
     (!a b c. R a b /\ R b c ==> R a c) /\ TYSYS2AUX_pres R m /\
     (!x. TYSYS2AUX_pres R (g x))
     ==> TYSYS2AUX_pres R (st_ex_bind m g)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; inferProps_st_ex_bind_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_ignore_bind = prove
 (`!R (m:S->(A,E)exc#S) (g:S->(B,E)exc#S).
     (!a b c. R a b /\ R b c ==> R a c) /\ TYSYS2AUX_pres R m /\ TYSYS2AUX_pres R g
     ==> TYSYS2AUX_pres R (st_ex_ignore_bind m g)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; st_ex_ignore_bind_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_return = prove
 (`!R (x:A). (!s. R s s) ==> TYSYS2AUX_pres R (st_ex_return x:S->(A,E)exc#S)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; inferProps_st_ex_return_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_failwith = prove
 (`!R (l:loc_err_info) (msg:A).
     TYSYS2AUX_pres R (failwith l msg:S->(B,locs option#A)exc#S)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; failwith_success]);;

let TYSYS2AUX_pres_guard = prove
 (`!R P (l:loc_err_info) (msg:A).
     (!s. R s s) ==> TYSYS2AUX_pres R (infer_guard P l msg:S->(1,locs option#A)exc#S)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; guard_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_lookup = prove
 (`!R (l:loc_err_info) err id (ienv:(mlstring,mlstring,V)namespace).
     (!s:S. R s s) ==> TYSYS2AUX_pres R (lookup_st_ex l err id ienv:S->(V,locs option#mlstring)exc#S)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; lookup_st_ex_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_check_dups = prove
 (`!R (l:loc_err_info) (f:A->B) ls.
     (!s:S. R s s) ==> TYSYS2AUX_pres R (check_dups l f ls:S->(1,locs option#B)exc#S)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; check_dups_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_tncs = prove
 (`!R (l:loc_err_info) f tenvT fvs t.
     (!s:S. R s s) ==> TYSYS2AUX_pres R (type_name_check_subst l f tenvT fvs t:S->(t,locs option#mlstring)exc#S)`,
  REWRITE_TAC[TYSYS2AUX_pres_def; type_name_check_subst_success] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_cond = prove
 (`!R b (m1:S->(A,E)exc#S) m2.
     (b ==> TYSYS2AUX_pres R m1) /\ (~b ==> TYSYS2AUX_pres R m2)
     ==> TYSYS2AUX_pres R (if b then m1 else m2)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let TYSYS2AUX_pres_pair = prove
 (CASE_TERM `!R (p:A#B) (f:A->B->S->(C,E)exc#S).
     (!a b. TYSYS2AUX_pres R (f a b))
     ==> TYSYS2AUX_pres R (match p with (a,b) -> f a b)`,
  GEN_TAC THEN GEN_TAC THEN MP_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN MESON_TAC[]);;

let TYSYS2AUX_pres_option = prove
 (CASE_TERM `!R (opt:A option) (f:S->(C,E)exc#S) g.
     (opt = NONE ==> TYSYS2AUX_pres R f) /\
     (!x. opt = SOME x ==> TYSYS2AUX_pres R (g x))
     ==> TYSYS2AUX_pres R (match opt with NONE -> f | SOME x -> g x)`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `opt:A option` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; injectivity "option"] THEN MESON_TAC[]);;

let TYSYS2AUX_PRES_TAC =
  let refl_lemmas = [TYSYS2AUX_pres_return; TYSYS2AUX_pres_guard; TYSYS2AUX_pres_lookup;
                     TYSYS2AUX_pres_check_dups; TYSYS2AUX_pres_tncs] in
  REPEAT(REPEAT GEN_TAC THEN BETA_TAC THEN
         FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
                MATCH_ACCEPT_TAC TYSYS2AUX_pres_failwith;
                MATCH_MP_TAC TYSYS2AUX_pres_bind THEN REPEAT CONJ_TAC;
                MATCH_MP_TAC TYSYS2AUX_pres_ignore_bind THEN REPEAT CONJ_TAC;
                MATCH_MP_TAC TYSYS2AUX_pres_cond THEN CONJ_TAC;
                MATCH_MP_TAC TYSYS2AUX_pres_pair;
                MATCH_MP_TAC TYSYS2AUX_pres_option THEN CONJ_TAC;
                MAP_FIRST MATCH_MP_TAC refl_lemmas;
                FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_MESON_TAC[]);
                DISCH_TAC]);;

let TYSYS2AUX_infer_p_pres = prove
 (`!R. (!s. R s s) /\ (!a b c. R a b /\ R b c ==> R a c) /\
       TYSYS2AUX_pres R (fresh_uvar:infer_st->(infer_t,locs option#mlstring)exc#infer_st) /\
       (!n. TYSYS2AUX_pres R
              (n_fresh_uvar n:infer_st->(infer_t list,locs option#mlstring)exc#infer_st)) /\
       (!l t1 t2. TYSYS2AUX_pres R (add_constraint l t1 t2)) /\
       (!l ts1 ts2. TYSYS2AUX_pres R (add_constraints l ts1 ts2))
       ==> (!l ienv p. TYSYS2AUX_pres R (infer_p l ienv p)) /\
           (!l ienv ps. TYSYS2AUX_pres R (infer_ps l ienv ps))`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC infer_p_ind THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[])) THEN
  REWRITE_TAC[infer_p_def] THEN TYSYS2AUX_PRES_TAC);;

let TYSYS2AUX_infer_e_pres = prove
 (`!R. (!s. R s s) /\ (!a b c. R a b /\ R b c ==> R a c) /\
       TYSYS2AUX_pres R (fresh_uvar:infer_st->(infer_t,locs option#mlstring)exc#infer_st) /\
       (!n. TYSYS2AUX_pres R
              (n_fresh_uvar n:infer_st->(infer_t list,locs option#mlstring)exc#infer_st)) /\
       (!l t1 t2. TYSYS2AUX_pres R (add_constraint l t1 t2)) /\
       (!l ts1 ts2. TYSYS2AUX_pres R (add_constraints l ts1 ts2)) /\
       (!l op ts. TYSYS2AUX_pres R (constrain_op l op ts))
       ==> (!l ienv e. TYSYS2AUX_pres R (infer_e l ienv e)) /\
           (!l ienv es. TYSYS2AUX_pres R (infer_es l ienv es)) /\
           (!l ienv pes t1 t2. TYSYS2AUX_pres R (infer_pes l ienv pes t1 t2)) /\
           (!l ienv funs. TYSYS2AUX_pres R (infer_funs l ienv funs))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `R:infer_st->infer_st->bool` TYSYS2AUX_infer_p_pres) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC infer_e_ind THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[])) THEN
  REWRITE_TAC[infer_e_def] THEN TYSYS2AUX_PRES_TAC);;

let TYSYS2AUX_pac_nil = prove
 (`!s. pure_add_constraints s [] s`,
  REWRITE_TAC[pure_add_constraints_def]);;

let TYSYS2AUX_pac_cons = prove
 (`!s s' s'' t1 t2 cs.
     t_unify s t1 t2 = SOME s' /\ pure_add_constraints s' cs s''
     ==> pure_add_constraints s (CONS (t1,t2) cs) s''`,
  REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[]);;

let TYSYS2AUX_constrain_op_state = prove
 (`!l op ts st v st'.
     constrain_op l op ts st = (M_success v,st')
     ==> infer_st_next_uvar st <= infer_st_next_uvar st' /\
         ?cs. pure_add_constraints (infer_st_subst st) cs (infer_st_subst st')`,
  GEN_TAC THEN X_GEN_TAC `op:op` THEN CASES_ON `op:op` THEN
  REWRITE_TAC[constrain_op_success; add_constraints_success] THEN
  REPEAT STRIP_TAC THEN GVS[infer_st_rewrs] THEN
  ASM_MESON_TAC[TYSYS2AUX_pac_nil; TYSYS2AUX_pac_cons]);;

let TYSYS2AUX_PRES_INST_TAC pres_thm rel prims =
  MP_TAC(ISPEC rel pres_thm) THEN REWRITE_TAC[TYSYS2AUX_pres_def] THEN BETA_TAC THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fresh_uvar_success; n_fresh_uvar_success; add_constraint_success;
                add_constraints_success] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_rewrs] THEN
    ASM_MESON_TAC prims;
    MESON_TAC[]];;

let infer_p_constraints = prove
 (`(!l cenv p st t env st'.
      infer_p l cenv p st = (M_success (t,env),st')
      ==> ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st')) /\
   (!l cenv ps st ts env st'.
      infer_ps l cenv ps st = (M_success (ts,env),st')
      ==> ?ts'. pure_add_constraints (infer_st_subst st) ts' (infer_st_subst st'))`,
  TYSYS2AUX_PRES_INST_TAC TYSYS2AUX_infer_p_pres
    `\st st'. ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st')`
    [TYSYS2AUX_pac_nil; TYSYS2AUX_pac_cons; pure_add_constraints_append]);;

let infer_e_constraints = prove
 (`(!l ienv e st st' t.
      infer_e l ienv e st = (M_success t,st')
      ==> ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st')) /\
   (!l ienv es st st' ts.
      infer_es l ienv es st = (M_success ts,st')
      ==> ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st')) /\
   (!l ienv pes t1 t2 st st'.
      infer_pes l ienv pes t1 t2 st = (M_success one,st')
      ==> ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st')) /\
   (!l ienv funs st st' ts'.
      infer_funs l ienv funs st = (M_success ts',st')
      ==> ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st'))`,
  TYSYS2AUX_PRES_INST_TAC TYSYS2AUX_infer_e_pres
    `\st st'. ?ts. pure_add_constraints (infer_st_subst st) ts (infer_st_subst st')`
    [TYSYS2AUX_pac_nil; TYSYS2AUX_pac_cons; pure_add_constraints_append;
     TYSYS2AUX_constrain_op_state]);;

let pure_add_constraints_wfs = prove
 (`!s1 ts s2. pure_add_constraints s1 ts s2 /\ t_wfs s1 ==> t_wfs s2`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[];
    MP_TAC(ISPEC `h:infer_t#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:infer_t` (X_CHOOSE_THEN `b:infer_t` SUBST1_TAC)) THEN
    REWRITE_TAC[pure_add_constraints_def] THEN ASM_MESON_TAC[t_unify_wfs]]);;

let infer_p_next_uvar_mono = prove
 (`(!l cenv p st t env st'.
      infer_p l cenv p st = (M_success (t,env),st')
      ==> infer_st_next_uvar st <= infer_st_next_uvar st') /\
   (!l cenv ps st ts env st'.
      infer_ps l cenv ps st = (M_success (ts,env),st')
      ==> infer_st_next_uvar st <= infer_st_next_uvar st')`,
  TYSYS2AUX_PRES_INST_TAC TYSYS2AUX_infer_p_pres
    `\st st'. infer_st_next_uvar st <= infer_st_next_uvar st'`
    [LE_REFL; LE_TRANS; LE_ADD; ARITH_RULE `n <= n + 1`]);;

let infer_e_next_uvar_mono = prove
 (`(!l ienv e st st' t.
      infer_e l ienv e st = (M_success t,st')
      ==> infer_st_next_uvar st <= infer_st_next_uvar st') /\
   (!l ienv es st st' ts.
      infer_es l ienv es st = (M_success ts,st')
      ==> infer_st_next_uvar st <= infer_st_next_uvar st') /\
   (!l ienv pes t1 t2 st st'.
      infer_pes l ienv pes t1 t2 st = (M_success one,st')
      ==> infer_st_next_uvar st <= infer_st_next_uvar st') /\
   (!l ienv funs st st' ts.
      infer_funs l ienv funs st = (M_success ts,st')
      ==> infer_st_next_uvar st <= infer_st_next_uvar st')`,
  TYSYS2AUX_PRES_INST_TAC TYSYS2AUX_infer_e_pres
    `\st st'. infer_st_next_uvar st <= infer_st_next_uvar st'`
    [LE_REFL; LE_TRANS; LE_ADD; ARITH_RULE `n <= n + 1`;
     TYSYS2AUX_constrain_op_state]);;

let infer_p_wfs = prove
 (`(!l cenv p st t env st'.
      t_wfs (infer_st_subst st) /\ infer_p l cenv p st = (M_success (t,env),st')
      ==> t_wfs (infer_st_subst st')) /\
   (!l cenv ps st ts env st'.
      t_wfs (infer_st_subst st) /\ infer_ps l cenv ps st = (M_success (ts,env),st')
      ==> t_wfs (infer_st_subst st'))`,
  TYSYS2AUX_PRES_INST_TAC TYSYS2AUX_infer_p_pres
    `\st st'. t_wfs (infer_st_subst st) ==> t_wfs (infer_st_subst st')`
    [t_unify_wfs; pure_add_constraints_wfs]);;

let infer_e_wfs = prove
 (`(!l ienv e st st' t.
      infer_e l ienv e st = (M_success t,st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st')) /\
   (!l ienv es st st' ts.
      infer_es l ienv es st = (M_success ts,st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st')) /\
   (!l ienv pes t1 t2 st st'.
      infer_pes l ienv pes t1 t2 st = (M_success one,st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st')) /\
   (!l ienv funs st st' ts'.
      infer_funs l ienv funs st = (M_success ts',st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st'))`,
  TYSYS2AUX_PRES_INST_TAC TYSYS2AUX_infer_e_pres
    `\st st'. t_wfs (infer_st_subst st) ==> t_wfs (infer_st_subst st')`
    [t_unify_wfs; pure_add_constraints_wfs; TYSYS2AUX_constrain_op_state]);;

let check_t_more = prove
 (`(!t tvs. check_t tvs {} t ==> !uvs. check_t tvs uvs t) /\
   (!ts tvs. ALL (check_t tvs {}) ts ==> !uvs. ALL (check_t tvs uvs) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; ALL; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let check_t_more2 = prove
 (`(!t tvs uvs. check_t tvs uvs t ==> !tvs'. check_t (tvs' + tvs) uvs t) /\
   (!ts tvs uvs. ALL (check_t tvs uvs) ts ==> !tvs'. ALL (check_t (tvs' + tvs) uvs) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REWRITE_TAC[check_t_def; ALL] THEN
  MESON_TAC[ARITH_RULE `n < m ==> n < k + m:num`]);;

let check_t_more3 = prove
 (`(!t uvs tvs. check_t tvs (count uvs) t ==> !uvs'. check_t tvs (count (uvs + uvs')) t) /\
   (!ts uvs tvs. ALL (check_t tvs (count uvs)) ts ==>
                 !uvs'. ALL (check_t tvs (count (uvs + uvs'))) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REWRITE_TAC[check_t_def; ALL; IN_COUNT] THEN
  MESON_TAC[ARITH_RULE `n < m ==> n < m + k:num`]);;

let check_t_more4 = prove
 (`(!t uvs tvs. check_t tvs (count uvs) t ==>
                !uvs'. uvs <= uvs' ==> check_t tvs (count uvs') t) /\
   (!ts uvs tvs. ALL (check_t tvs (count uvs)) ts ==>
                 !uvs'. uvs <= uvs' ==> ALL (check_t tvs (count uvs')) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REWRITE_TAC[check_t_def; ALL; IN_COUNT] THEN
  MESON_TAC[LTE_TRANS]);;

let check_t_more5 = prove
 (`(!t uvs tvs. check_t tvs uvs t ==> !uvs'. uvs SUBSET uvs' ==> check_t tvs uvs' t) /\
   (!ts uvs tvs. ALL (check_t tvs uvs) ts ==>
                 !uvs'. uvs SUBSET uvs' ==> ALL (check_t tvs uvs') ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REWRITE_TAC[check_t_def; ALL; SUBSET] THEN
  MESON_TAC[]);;

let check_t_t_vars = prove
 (`!tvs uvs t. check_t tvs uvs t ==> t_vars t SUBSET uvs`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[t_vars_eqn; check_t_def; EMPTY_SUBSET; SING_SUBSET; GSYM ALL_MEM] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

let check_s_more = prove
 (`!s tvs uvs. check_s tvs (count uvs) s ==> check_s tvs (count (uvs + 1)) s`,
  REWRITE_TAC[check_s_def] THEN MESON_TAC[check_t_more3]);;

let check_s_more2 = prove
 (`!tvs s uvs.
     check_s tvs (count uvs) s ==> !uvs'. uvs <= uvs' ==> check_s tvs (count uvs') s`,
  REWRITE_TAC[check_s_def] THEN MESON_TAC[check_t_more4]);;

let check_s_more3 = prove
 (`!tvs s uvs. check_s tvs uvs s ==> !uvs'. uvs SUBSET uvs' ==> check_s tvs uvs' s`,
  REWRITE_TAC[check_s_def] THEN MESON_TAC[check_t_more5]);;

let check_s_more5 = prove
 (`!s uvs tvs uvs'. check_s tvs uvs s /\ uvs SUBSET uvs' ==> check_s tvs uvs' s`,
  REWRITE_TAC[check_s_def] THEN MESON_TAC[check_t_more5]);;

let check_t_deBruijn_inc2 = prove
 (`!tvs inc t s. check_t tvs s t ==> check_t (inc + tvs) s (infer_deBruijn_inc inc t)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[check_t_def; infer_deBruijn_inc_def; ALL_MAP; o_THM; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[ARITH_RULE `m < tvs ==> m + inc < inc + tvs:num`]);;

let check_t_deBruijn_inc = prove
 (`!inc t. check_t 0 UNIV t ==> infer_deBruijn_inc inc t = t`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[check_t_def; infer_deBruijn_inc_def; LT; injectivity "infer_t";
              GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let infer_deBruijn_subst_twice = prove
 (`!subst1 subst2 uvs.
   (!t. check_t (LENGTH subst2) uvs t ==>
        infer_deBruijn_subst subst1 (infer_deBruijn_subst subst2 t) =
        infer_deBruijn_subst (MAP (infer_deBruijn_subst subst1) subst2) t) /\
   (!ts. ALL (check_t (LENGTH subst2) uvs) ts ==>
         MAP (infer_deBruijn_subst subst1 o infer_deBruijn_subst subst2) ts =
         MAP (infer_deBruijn_subst (MAP (infer_deBruijn_subst subst1) subst2)) ts)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[check_t_def; infer_deBruijn_subst_alt; LENGTH_MAP] THEN SIMP_TAC[EL_MAP];
    REWRITE_TAC[check_t_def; infer_deBruijn_subst_alt; GSYM MAP_o] THEN MESON_TAC[];
    REWRITE_TAC[infer_deBruijn_subst_alt];
    REWRITE_TAC[MAP];
    REWRITE_TAC[ALL; MAP; CONS_11; o_THM] THEN MESON_TAC[]]);;

let check_t_subst = prove
 (`!tvs (tvs':num->bool) t s.
     t_wfs s /\ check_t tvs {} t ==> t = t_walkstar (infer_deBruijn_inc tvs o_f s) t`,
  MATCH_MP_TAC check_t_ind THEN REWRITE_TAC[check_t_def; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `t_wfs (infer_deBruijn_inc n o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
    [ASM_MESON_TAC[inc_wfs]; ALL_TAC]) THEN
  ASM_SIMP_TAC[t_walkstar_eqn1; injectivity "infer_t"] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  ASM_MESON_TAC[]);;

let t_vwalk_check = prove
 (`!s. t_wfs s ==>
     !n tvs uvs (t:infer_t).
       n IN uvs /\ check_s tvs uvs s ==> check_t tvs uvs (t_vwalk s n)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. !tvs uvs. n IN uvs /\ check_s tvs uvs s
                              ==> check_t tvs uvs (t_vwalk s n)`
    (fun th -> MESON_TAC[th]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn th]) THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) v` THEN
  CASE_REWRITE_TAC[check_t_def] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [flookup_thm]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `check_t tvs uvs (a:infer_t)` MP_TAC THENL
   [ASM_MESON_TAC[check_s_def]; ALL_TAC] THEN
  CASES_ON `a:infer_t` THEN CASE_REWRITE_TAC[check_t_def] THEN
  ASM_MESON_TAC[]);;

let TYSYS2AUX_t_walk_check = prove
 (`!s tvs uvs t.
     t_wfs s /\ check_s tvs uvs s /\ check_t tvs uvs t ==> check_t tvs uvs (t_walk s t)`,
  REPEAT GEN_TAC THEN CASES_ON `t:infer_t` THEN REWRITE_TAC[t_walk_eqn; check_t_def] THEN
  MESON_TAC[t_vwalk_check]);;

let TYSYS2AUX_t_walk_to_var = prove
 (`!s t v. t_wfs s /\ t_walk s t = Infer_Tuvar v ==> ~(v IN FDOM s)`,
  REPEAT GEN_TAC THEN CASES_ON `t:infer_t` THEN
  REWRITE_TAC[t_walk_eqn; distinctness "infer_t"] THEN MESON_TAC[t_vwalk_to_var]);;

let t_walkstar_check' = prove
 (`!s. t_wfs s ==>
     !t tvs uvs.
       check_s tvs (uvs UNION FDOM s) s /\ check_t tvs (uvs UNION FDOM s) t
       ==> check_t tvs uvs (t_walkstar s t)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP t_walkstar_eqn th]) THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `tvs:num`; `uvs UNION FDOM (s:(num,infer_t)fmap)`;
                `t:infer_t`] TYSYS2AUX_t_walk_check) THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `t:infer_t`] TYSYS2AUX_t_walk_to_var) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  SPEC_TAC(`t_walk (s:(num,infer_t)fmap) t`,`w:infer_t`) THEN
  X_GEN_TAC `w:infer_t` THEN CASES_ON `w:infer_t` THEN
  CASE_REWRITE_TAC[check_t_def; injectivity "infer_t"; distinctness "infer_t"; IN_UNION;
                   ALL_MAP; o_THM; GSYM ALL_MEM] THEN
  ASM_MESON_TAC[]);;

let t_walkstar_check = prove
 (`!s t tvs uvs.
     t_wfs s /\ check_s tvs (uvs UNION FDOM s) s /\ check_t tvs (uvs UNION FDOM s) t
     ==> check_t tvs uvs (t_walkstar s t)`,
  MESON_TAC[t_walkstar_check']);;

let TYSYS2AUX_t_walkstar_uvar_notin = prove
 (`!s n. t_wfs s /\ ~(n IN FDOM s) ==> t_walkstar s (Infer_Tuvar n) = Infer_Tuvar n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP t_walkstar_eqn th]) THEN
  REWRITE_TAC[t_walk_eqn] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn th]) THEN
  SUBGOAL_THEN `FLOOKUP (s:(num,infer_t)fmap) n = NONE` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[flookup_thm]; CASE_REWRITE_TAC[]]);;

let t_walkstar_uncheck_lem = prove
 (`!s. t_wfs s ==>
     !t max_tvs uvs.
       check_t max_tvs uvs (t_walkstar s t) ==> check_t max_tvs (uvs UNION FDOM s) t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `t:infer_t` THEN ASM_SIMP_TAC[t_walkstar_eqn1; check_t_def] THENL
   [REWRITE_TAC[ALL_MAP; o_THM; GSYM ALL_MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[t_walk_eqn; injectivity "infer_t"]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `a IN FDOM (s:(num,infer_t)fmap)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[TYSYS2AUX_t_walkstar_uvar_notin; check_t_def]]);;

let t_walkstar_uncheck = prove
 (`!s t max_tvs uvs.
     check_t max_tvs uvs (t_walkstar s t) /\ t_wfs s
     ==> check_t max_tvs (uvs UNION FDOM s) t`,
  MESON_TAC[t_walkstar_uncheck_lem]);;

let TYSYS2AUX_check_s_FUPDATE = prove
 (`!tvs uvs s v t.
     check_s tvs uvs s /\ check_t tvs uvs t ==> check_s tvs uvs (s |+ (v,t))`,
  REWRITE_TAC[check_s_def; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let t_unify_check_s_help = prove
 (`(!s t1 t2. t_wfs s ==>
      !tvs uvs s'. check_s tvs uvs s /\ check_t tvs uvs t1 /\ check_t tvs uvs t2 /\
                   t_unify s t1 t2 = SOME s'
                   ==> check_s tvs uvs s') /\
   (!s ts1 ts2. t_wfs s ==>
      !tvs uvs s'. check_s tvs uvs s /\ ALL (check_t tvs uvs) ts1 /\
                   ALL (check_t tvs uvs) ts2 /\ ts_unify s ts1 ts2 = SOME s'
                   ==> check_s tvs uvs s')`,
  MATCH_MP_TAC t_unify_strongind THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `t_unify s t1 t2 = SOME (s':(num,infer_t)fmap)` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_unify_eqn th]) THEN
    MP_TAC(SPECL [`s:(num,infer_t)fmap`; `tvs:num`; `uvs:num->bool`; `t1:infer_t`]
             TYSYS2AUX_t_walk_check) THEN
    MP_TAC(SPECL [`s:(num,infer_t)fmap`; `tvs:num`; `uvs:num->bool`; `t2:infer_t`]
             TYSYS2AUX_t_walk_check) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    SPEC_TAC(`t_walk (s:(num,infer_t)fmap) t1`,`w1:infer_t`) THEN
    SPEC_TAC(`t_walk (s:(num,infer_t)fmap) t2`,`w2:infer_t`) THEN
    X_GEN_TAC `w2:infer_t` THEN X_GEN_TAC `w1:infer_t` THEN
    CASES_ON `w1:infer_t` THEN CASES_ON `w2:infer_t` THEN
    CASE_REWRITE_TAC[t_ext_s_check_eqn; injectivity "infer_t"; distinctness "infer_t";
                     bool_case_eq; option_DISTINCT; injectivity "option"; check_t_def] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[TYSYS2AUX_check_s_FUPDATE; check_t_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    CASES_ON `ts1:infer_t list` THEN CASES_ON `ts2:infer_t list` THEN
    REWRITE_TAC([ts_unify_def; ALL; option_DISTINCT; injectivity "option"] @
                all_case_eqs()) THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

let check_t_walkstar = prove
 (`(!t tvs s.
      t_wfs s /\ check_t tvs (FDOM s) t /\
      (!uv. uv IN FDOM s ==> check_t tvs {} (t_walkstar s (Infer_Tuvar uv)))
      ==> check_t tvs {} (t_walkstar s t)) /\
   (!ts tvs s.
      t_wfs s /\ ALL (check_t tvs (FDOM s)) ts /\
      (!uv. uv IN FDOM s ==> check_t tvs {} (t_walkstar s (Infer_Tuvar uv)))
      ==> ALL (check_t tvs {} o t_walkstar s) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  SIMP_TAC[check_t_def; t_walkstar_eqn1; ALL; ALL_MAP; o_THM] THEN MESON_TAC[]);;

(* HOL4 proves a local t_walkstar_no_vars and then the theorem of the same *)
(* name; the local one is TYSYS2AUX_t_walkstar_no_vars here                *)

let TYSYS2AUX_t_walkstar_no_vars = prove
 (`!tvs uvs t s. t_wfs s /\ uvs = {} /\ check_t tvs uvs t ==> t_walkstar s t = t`,
  MATCH_MP_TAC check_t_ind THEN REWRITE_TAC[check_t_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[t_walkstar_eqn1; injectivity "infer_t"] THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]);;

let t_walkstar_no_vars = prove
 (`!tvs t s. t_wfs s /\ check_t tvs {} t ==> t_walkstar s t = t`,
  MESON_TAC[TYSYS2AUX_t_walkstar_no_vars]);;

let t_unify_check_s = prove
 (`!s1 tvs uvs t1 t2 s2.
     t_unify s1 t1 t2 = SOME s2 /\ t_wfs s1 /\ check_s tvs uvs s1 /\
     check_t tvs uvs t1 /\ check_t tvs uvs t2
     ==> check_s tvs uvs s2`,
  MESON_TAC[t_unify_check_s_help]);;

let pure_add_constraints_check_s = prove
 (`!s1 tvs uvs ts s2.
     pure_add_constraints s1 ts s2 /\ t_wfs s1 /\
     ALL (\(t1,t2). check_t tvs (count uvs) t1 /\ check_t tvs (count uvs) t2) ts /\
     check_s tvs (count uvs) s1
     ==> check_s tvs (count uvs) s2`,
  SUBGOAL_THEN
   `!ts s1 tvs uvs s2.
      pure_add_constraints s1 ts s2 /\ t_wfs s1 /\
      ALL (\(t1,t2). check_t tvs (count uvs) t1 /\ check_t tvs (count uvs) t2) ts /\
      check_s tvs (count uvs) s1
      ==> check_s tvs (count uvs) s2`
    (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[];
    MP_TAC(ISPEC `h:infer_t#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:infer_t` (X_CHOOSE_THEN `b:infer_t` SUBST1_TAC)) THEN
    REWRITE_TAC[pure_add_constraints_def; ALL] THEN
    ASM_MESON_TAC[t_unify_wfs; t_unify_check_s]]);;

let TYSYS2AUX_check_t_mono = prove
 (`(!t n m. check_t 0 (count n) t /\ n <= m ==> check_t 0 (count m) t) /\
   (!ts n m. ALL (check_t 0 (count n)) ts /\ n <= m ==> ALL (check_t 0 (count m)) ts)`,
  MESON_TAC[check_t_more4]);;

let infer_p_check_t = prove
 (`(!l cenv p st t env st'.
      infer_p l cenv p st = (M_success (t,env),st')
      ==> ALL (\(x,t). check_t 0 (count (infer_st_next_uvar st')) t) env /\
          check_t 0 (count (infer_st_next_uvar st')) t) /\
   (!l cenv ps st ts env st'.
      infer_ps l cenv ps st = (M_success (ts,env),st')
      ==> ALL (\(x,t). check_t 0 (count (infer_st_next_uvar st')) t) env /\
          ALL (check_t 0 (count (infer_st_next_uvar st'))) ts)`,
  REWRITE_TAC[every_shim; ETA_AX] THEN
  MATCH_MP_TAC infer_p_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  REWRITE_TAC[infer_p_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE] THEN
  REPEAT STRIP_TAC THEN
  GVS[infer_st_rewrs; check_t_def; ALL; ALL_APPEND; IN_COUNT; MAP_APPEND; MAP; SND] THEN
  TRY(REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; MEM_COUNT_LIST; o_THM; check_t_def; IN_COUNT] THEN
      REPEAT STRIP_TAC THEN ASM_ARITH_TAC) THEN
  RES_TAC THEN
  ASM_MESON_TAC[TYSYS2AUX_check_t_mono; infer_p_next_uvar_mono;
                ARITH_RULE `a + b = c ==> a <= c:num`]);;

let check_infer_type_subst = prove
 (`(!t tvs uvs.
      check_freevars 0 tvs t
      ==> check_t 0 (count (LENGTH tvs + uvs))
            (infer_type_subst
               (ZIP tvs (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH tvs)))) t)) /\
   (!ts tvs uvs.
      ALL (check_freevars 0 tvs) ts
      ==> ALL (\t. check_t 0 (count (LENGTH tvs + uvs))
                     (infer_type_subst
                        (ZIP tvs (MAP (\n. Infer_Tuvar (uvs + n))
                                      (COUNT_LIST (LENGTH tvs)))) t)) ts)`,
  MATCH_MP_TAC t_INDUCT THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `tv:mlstring` THEN REWRITE_TAC[check_freevars_def; infer_type_subst_alt] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN X_GEN_TAC `uvs:num` THEN
    REWRITE_TAC[LENGTH; COUNT_LIST_DEF; MAP; ZIP; ALOOKUP_THM; GSYM MAP_o; o_DEF] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[check_t_def; IN_COUNT] THENL
     [DISCH_TAC THEN ARITH_TAC;
      STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC uvs`) THEN ASM_REWRITE_TAC[ADD_CLAUSES]];
    REWRITE_TAC[check_freevars_def; LT];
    REWRITE_TAC[check_freevars_def; infer_type_subst_alt; check_t_def; ALL_MAP; o_DEF] THEN
    MESON_TAC[];
    REWRITE_TAC[ALL];
    REWRITE_TAC[ALL] THEN MESON_TAC[]]);;

let infer_type_subst_empty_check = prove
 (`(!t. check_freevars 0 [] t ==> check_t 0 {} (infer_type_subst [] t)) /\
   (!ts. ALL (check_freevars 0 []) ts ==> ALL (check_t 0 {}) (MAP (infer_type_subst []) ts))`,
  MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[check_freevars_def; infer_type_subst_alt; check_t_def; MEM; LT; ALL; MAP] THEN
  MESON_TAC[]);;

let type_name_check_subst_thm = prove
 (`(!t l err tenvT fvs (st:S) r st'.
      type_name_check_subst l err tenvT fvs t st = (M_success r,st')
      ==> check_freevars_ast fvs t /\ check_type_names tenvT t /\
          r = type_name_subst tenvT t) /\
   (!ts l err tenvT fvs (st:S) rs st'.
      type_name_check_subst_list l err tenvT fvs ts st = (M_success rs,st')
      ==> ALL (check_freevars_ast fvs) ts /\ ALL (check_type_names tenvT) ts /\
          rs = MAP (type_name_subst tenvT) ts)`,
  SIMP_TAC[type_name_check_subst_success]);;

let type_name_check_subst_comp_thm = prove
 (`(!t l err tenvT fvs (st:S) (r:t).
      check_freevars_ast fvs t /\ check_type_names tenvT t
      ==> type_name_check_subst l err tenvT fvs t st =
          (M_success (type_name_subst tenvT t),st)) /\
   (!ts l err tenvT fvs (st:S) (rs:t list) (st':S).
      ALL (check_freevars_ast fvs) ts /\ ALL (check_type_names tenvT) ts
      ==> type_name_check_subst_list l err tenvT fvs ts st =
          (M_success (MAP (type_name_subst tenvT) ts),st))`,
  SIMP_TAC[type_name_check_subst_success]);;

let TYSYS2AUX_check_t_lift = prove
 (`(!t n m tvs. check_t 0 (count n) t /\ n <= m ==> check_t tvs (count m) t) /\
   (!ts n m tvs. ALL (check_t 0 (count n)) ts /\ n <= m ==> ALL (check_t tvs (count m)) ts)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`t:infer_t`; `0`; `count n`] (CONJUNCT1 check_t_more2));
    MP_TAC(SPECL [`ts:infer_t list`; `0`; `count n`] (CONJUNCT2 check_t_more2))] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(MP_TAC o SPEC `tvs:num`) THEN
  ASM_MESON_TAC[check_t_more4]);;

let TYSYS2AUX_check_s_Pcon = prove
 (`!s1 s2 tvs n1 tvs' ts ts'' tenvC (cn:(mlstring,mlstring)id) tn.
     t_wfs s1 /\ tenv_ctor_ok tenvC /\ nsLookup tenvC cn = SOME (tvs',ts,tn) /\
     check_s tvs (count n1) s1 /\ ALL (check_t 0 (count n1)) ts'' /\
     LENGTH ts'' = LENGTH ts /\
     pure_add_constraints s1
       (ZIP ts'' (MAP (infer_type_subst
                         (ZIP tvs' (MAP (\n. Infer_Tuvar (n1 + n))
                                        (COUNT_LIST (LENGTH tvs'))))) ts)) s2
     ==> check_s tvs (count (n1 + LENGTH tvs')) s2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC pure_add_constraints_check_s THEN
  MAP_EVERY EXISTS_TAC
   [`s1:(num,infer_t)fmap`;
    `ZIP (ts'':infer_t list)
       (MAP (infer_type_subst
               (ZIP (tvs':mlstring list) (MAP (\n. Infer_Tuvar (n1 + n))
                                              (COUNT_LIST (LENGTH tvs'))))) (ts:t list))`] THEN
  ASM_REWRITE_TAC[every_shim2] THEN
  SUBGOAL_THEN `LENGTH (ts'':infer_t list) =
                LENGTH (MAP (infer_type_subst
                  (ZIP (tvs':mlstring list) (MAP (\n. Infer_Tuvar (n1 + n))
                                 (COUNT_LIST (LENGTH tvs'))))) (ts:t list))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[every_zip_fst; every_zip_snd; LENGTH_MAP] THEN
  REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 TYSYS2AUX_check_t_lift) THEN EXISTS_TAC `n1:num` THEN
    ASM_REWRITE_TAC[LE_ADD];
    MP_TAC(SPECL [`tenvC:(mlstring,mlstring,mlstring list#t list#type_ident)namespace`;
                  `cn:(mlstring,mlstring)id`; `tvs':mlstring list`; `ts:t list`;
                  `tn:type_ident`] tenv_ctor_ok_lookup) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n1:num` o MATCH_MP (CONJUNCT2 check_infer_type_subst)) THEN
    REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
    GEN_TAC THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC(CONJUNCT1 TYSYS2AUX_check_t_lift) THEN
    EXISTS_TAC `LENGTH (tvs':mlstring list) + n1` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    FIRST_ASSUM(MP_TAC o MATCH_MP check_s_more2) THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LE_ADD]]);;

let TYSYS2AUX_check_s_Ptannot = prove
 (`!s1 s2 tvs n t' t tenvT.
     t_wfs s1 /\ check_s tvs (count n) s1 /\ check_t 0 (count n) t' /\
     tenv_abbrev_ok tenvT /\ check_freevars_ast [] t /\ check_type_names tenvT t /\
     t_unify s1 t' (infer_type_subst [] (type_name_subst tenvT t)) = SOME s2
     ==> check_s tvs (count n) s2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC t_unify_check_s THEN
  MAP_EVERY EXISTS_TAC [`s1:(num,infer_t)fmap`; `t':infer_t`;
                        `infer_type_subst [] (type_name_subst tenvT t)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[TYSYS2AUX_check_t_lift; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 {} (infer_type_subst [] (type_name_subst tenvT t))` MP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_type_subst_empty_check) THEN
    ASM_MESON_TAC[check_freevars_type_name_subst];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `count n` o MATCH_MP (CONJUNCT1 check_t_more)) THEN
  MESON_TAC[TYSYS2AUX_check_t_lift; LE_REFL]);;

let TYSYS2AUX_SUBST_VARS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (lhs c) && not (free_in (lhs c) (rhs c)) then SUBST_ALL_TAC th
    else if is_eq c && is_var (rhs c) && not (free_in (rhs c) (lhs c))
    then SUBST_ALL_TAC (SYM th)
    else failwith "TYSYS2AUX_SUBST_VARS_TAC"));;

let infer_p_check_s = prove
 (`(!l ienv p st t env st' tvs.
      infer_p l ienv p st = (M_success (t,env),st') /\
      t_wfs (infer_st_subst st) /\
      tenv_ctor_ok (inf_env_inf_c ienv) /\
      tenv_abbrev_ok (inf_env_inf_t ienv) /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
      ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st')) /\
   (!l ienv ps st ts env st' tvs.
      infer_ps l ienv ps st = (M_success (ts,env),st') /\
      t_wfs (infer_st_subst st) /\
      tenv_ctor_ok (inf_env_inf_c ienv) /\
      tenv_abbrev_ok (inf_env_inf_t ienv) /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
      ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st'))`,
  MATCH_MP_TAC infer_p_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[infer_p_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE] THEN
  REPEAT STRIP_TAC THEN TYSYS2AUX_SUBST_VARS_TAC THEN
  REWRITE_TAC[infer_st_rewrs] THEN RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs]) THENL
   [ASM_SIMP_TAC[check_s_more];
    ASM_SIMP_TAC[check_s_more];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    (* Pcon SOME *)
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_const(fst(strip_comb(rhs(concl th))))) = "infer_st_next_uvar"
      with Failure _ -> false)) THEN
    MATCH_MP_TAC TYSYS2AUX_check_s_Pcon THEN
    MAP_EVERY EXISTS_TAC
     [`infer_st_subst st'''`; `p1':t list`; `p1'':infer_t list`;
      `inf_env_inf_c ienv`; `cn:(mlstring,mlstring)id`; `p2:type_ident`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[infer_p_wfs]; ASM_MESON_TAC[]; ASM_MESON_TAC[infer_p_check_t]];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    (* Ptannot *)
    MATCH_MP_TAC TYSYS2AUX_check_s_Ptannot THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'''`; `t':infer_t`; `t:ast_t`;
                          `inf_env_inf_t ienv`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[infer_p_wfs]; ASM_MESON_TAC[]; ASM_MESON_TAC[infer_p_check_t]];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[infer_p_wfs]]);;

let check_env_more = prove
 (CASE_TERM `!uvs (e:(mlstring,mlstring,num#infer_t)namespace).
     nsAll (\x p. match p with (tvs,t) -> check_t tvs (count uvs) t) e
     ==> !uvs'. uvs <= uvs'
                ==> nsAll (\x p. match p with (tvs,t) -> check_t tvs (count uvs') t) e`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> GEN_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC nsAll_mono THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[check_t_more4]);;

let check_env_letrec_lem = prove
 (CASE_TERM `!uvs (funs:(mlstring#mlstring#exp)list) uvs'.
     (funs = [] \/ uvs' + LENGTH funs <= uvs)
     ==> nsAll (\x p. match p with (tvs,t) -> check_t tvs (count uvs) t)
           (alist_to_ns
              (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                    (MAP (\n. Infer_Tuvar (n + uvs')) (COUNT_LIST (LENGTH funs))))
            :(mlstring,mlstring,num#infer_t)namespace)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`uvs':num`,`uvs':num`) THEN
  SPEC_TAC(`funs:(mlstring#mlstring#exp)list`,`funs:(mlstring#mlstring#exp)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; COUNT_LIST_DEF; MAP; MAP2; ALL; NOT_CONS_NIL] THEN
  X_GEN_TAC `u:num` THEN
  X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `e:exp`
    SUBST_ALL_TAC)) (ISPEC `h:mlstring#mlstring#exp` BASICAUX_TUPLE3) THEN
  BETA_TAC THEN CASE_REWRITE_TAC[check_t_def; IN_COUNT; GSYM MAP_o; o_DEF] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC u`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let check_t_infer_db_subst = prove
 (`(!t uvs tvs.
      check_t 0 (count (uvs + tvs))
        (infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs)) t) <=>
      check_t tvs (count (uvs + tvs)) t) /\
   (!ts uvs tvs.
      ALL (check_t 0 (count (uvs + tvs)) o
           infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs))) ts <=>
      ALL (check_t tvs (count (uvs + tvs))) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; infer_deBruijn_subst_alt; LENGTH_MAP; LENGTH_COUNT_LIST;
              ALL_MAP; ALL; o_THM] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; check_t_def; IN_COUNT] THEN
  ASM_ARITH_TAC);;

let check_t_infer_db_subst2 = prove
 (`(!t tvs1 tvs2.
      check_t tvs1 (count tvs2)
        (infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs2)) t) <=>
      check_t (tvs1 + tvs2) (count tvs2) t) /\
   (!ts tvs1 tvs2.
      ALL (check_t tvs1 (count tvs2) o
           infer_deBruijn_subst (MAP (\n. Infer_Tuvar n) (COUNT_LIST tvs2))) ts <=>
      ALL (check_t (tvs1 + tvs2) (count tvs2)) ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; infer_deBruijn_subst_alt; LENGTH_MAP; LENGTH_COUNT_LIST;
              ALL_MAP; ALL; o_THM] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; check_t_def; IN_COUNT] THEN
  ASM_ARITH_TAC);;

(* constrain_op_check_t comes after infer_e_check_t in the HOL4 script;  *)
(* it is proved here because the proof of infer_e_check_t uses it         *)

let constrain_op_check_t = prove
 (`!l (tvs:num) op ts t st st'.
     constrain_op l op ts st = (M_success t,st') /\
     ALL (check_t 0 (count (infer_st_next_uvar st))) ts
     ==> check_t 0 (count (infer_st_next_uvar st')) t`,
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `op:op` THEN CASES_ON `op:op` THEN
  REWRITE_TAC[constrain_op_success; add_constraints_success] THEN
  REPEAT STRIP_TAC THEN GVS[infer_st_rewrs; check_t_def; ALL; IN_COUNT] THEN
  ASM_ARITH_TAC);;

let TYSYS2AUX_ienv_val_ok_mono = prove
 (`!n m env. ienv_val_ok (count n) env /\ n <= m ==> ienv_val_ok (count m) env`,
  REWRITE_TAC[ienv_val_ok_def] THEN MESON_TAC[check_env_more]);;

let TYSYS2AUX_ienv_val_ok_nsBind = prove
 (`!n x t env.
     ienv_val_ok (count n) env /\ check_t 0 (count n) t
     ==> ienv_val_ok (count n) (nsBind x (0,t) env)`,
  REWRITE_TAC[ienv_val_ok_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC nsAll_nsBind THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let TYSYS2AUX_ienv_val_ok_nsOptBind = prove
 (`!n xo t env.
     ienv_val_ok (count n) env /\ check_t 0 (count n) t
     ==> ienv_val_ok (count n) (nsOptBind xo (0,t) env)`,
  REWRITE_TAC[ienv_val_ok_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC nsAll_nsOptBind THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[option_nchotomy]);;

let TYSYS2AUX_ienv_val_ok_letrec = prove
 (CASE_TERM `!m u (funs:(mlstring#mlstring#exp)list) env.
     ienv_val_ok (count u) env /\ u + LENGTH funs <= m
     ==> ienv_val_ok (count m)
           (nsAppend
              (alist_to_ns
                 (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                       (MAP (\n. Infer_Tuvar (u + n)) (COUNT_LIST (LENGTH funs)))))
              env)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ienv_val_ok_def] THEN
  MATCH_MP_TAC nsAll_nsAppend THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC check_env_letrec_lem THEN
    DISJ2_TAC THEN ASM_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[ienv_val_ok_def]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP check_env_more) THEN ASM_ARITH_TAC]);;

(* A small Hoare logic for successful runs of state-exception computations, *)
(* used for infer_e_check_t and infer_e_check_s: G is an invariant of the  *)
(* state, R a preorder between the initial and the final state, P a        *)
(* precondition that R preserves, and Q a postcondition on the result and *)
(* the final state.                                                        *)

let TYSYS2AUX_hoare_def = new_definition
 `TYSYS2AUX_hoare (G:S->bool) (R:S->S->bool) (P:S->bool) (m:S->(A,E)exc#S)
                  (Q:A->S->bool) <=>
    !st v st'. G st /\ P st /\ m st = (M_success v,st') ==> G st' /\ R st st' /\ Q v st'`;;

let TYSYS2AUX_ignore_bind_eq = prove
 (`!(m:S->(A,E)exc#S) (g:S->(B,E)exc#S).
     st_ex_ignore_bind m g = st_ex_bind m (\u. g)`,
  REWRITE_TAC[st_ex_ignore_bind_def; st_ex_bind_def]);;

let TYSYS2AUX_hoare_return = prove
 (`!G R P (x:A) Q.
     (!s. R s s) /\ (!st. G st /\ P st ==> Q x st)
     ==> TYSYS2AUX_hoare G R P (st_ex_return x:S->(A,E)exc#S) Q`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; inferProps_st_ex_return_success] THEN MESON_TAC[]);;

let TYSYS2AUX_hoare_failwith = prove
 (`!G R P (l:loc_err_info) (msg:A) Q.
     TYSYS2AUX_hoare G R P (failwith l msg:S->(B,locs option#A)exc#S) Q`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; failwith_success]);;

let TYSYS2AUX_hoare_cond = prove
 (`!G R P b (m1:S->(A,E)exc#S) m2 Q.
     (b ==> TYSYS2AUX_hoare G R P m1 Q) /\ (~b ==> TYSYS2AUX_hoare G R P m2 Q)
     ==> TYSYS2AUX_hoare G R P (if b then m1 else m2) Q`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let TYSYS2AUX_hoare_pair = prove
 (CASE_TERM `!G R P (p:A#B) (f:A->B->S->(C,E)exc#S) Q.
     (!a b. p = (a,b) ==> TYSYS2AUX_hoare G R P (f a b) Q)
     ==> TYSYS2AUX_hoare G R P (match p with (a,b) -> f a b) Q`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN MESON_TAC[]);;

let TYSYS2AUX_hoare_option = prove
 (CASE_TERM `!G R P (opt:A option) (f:S->(C,E)exc#S) g Q.
     (opt = NONE ==> TYSYS2AUX_hoare G R P f Q) /\
     (!x. opt = SOME x ==> TYSYS2AUX_hoare G R P (g x) Q)
     ==> TYSYS2AUX_hoare G R P (match opt with NONE -> f | SOME x -> g x) Q`,
  REPEAT GEN_TAC THEN CASES_ON `opt:A option` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; injectivity "option"] THEN MESON_TAC[]);;

let TYSYS2AUX_hoare_bindw = prove
 (`!G R P P0 (m:S->(A,E)exc#S) (g:A->S->(B,E)exc#S) Q1 Q.
     TYSYS2AUX_hoare G R P0 m Q1
     ==> (!a b c. R a b /\ R b c ==> R a c) /\
         (!st st'. P st /\ R st st' ==> P st') /\
         (!st. P st ==> P0 st) /\
         (!x. TYSYS2AUX_hoare G R (\st. P st /\ Q1 x st) (g x) Q)
         ==> TYSYS2AUX_hoare G R P (st_ex_bind m g) Q`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; inferProps_st_ex_bind_success] THEN MESON_TAC[]);;

let TYSYS2AUX_hoare_weakenw = prove
 (`!G R P P0 (m:S->(A,E)exc#S) Q0 Q.
     TYSYS2AUX_hoare G R P0 m Q0
     ==> (!st. P st ==> P0 st) /\ (!v st. Q0 v st ==> Q v st)
         ==> TYSYS2AUX_hoare G R P m Q`,
  REWRITE_TAC[TYSYS2AUX_hoare_def] THEN MESON_TAC[]);;

(* The tactic: decompose a goal TYSYS2AUX_hoare G R P m Q along the monadic *)
(* structure of m; the triples of the primitive computations come from the *)
(* list prims and from the assumptions (induction hypotheses); the side     *)
(* conditions go to closer.                                                 *)

let TYSYS2AUX_is_hoare tm =
  let tm' = snd(strip_forall tm) in
  try fst(dest_const(fst(strip_comb tm'))) = "TYSYS2AUX_hoare" with Failure _ -> false;;

let TYSYS2AUX_triple_for asl prims m =
  let try_th lconsts th =
    let th' = SPEC_ALL th in
    let c = concl th' in
    let (hc,args) = strip_comb c in
    if not (is_const hc && fst(dest_const hc) = "TYSYS2AUX_hoare") then failwith "no"
    else
      let mpat = el 3 args in
      INSTANTIATE (term_match lconsts mpat m) th' in
  try tryfind (fun (_,th) -> try_th (frees(concl th)) th) asl
  with Failure _ -> tryfind (try_th []) prims;;

let TYSYS2AUX_BIND_TAC prims (asl,w as g) =
  let (_,args) = strip_comb w in
  let mtm = el 3 args in
  let (bc,bargs) = strip_comb mtm in
  if not (is_const bc && fst(dest_const bc) = "st_ex_bind") then failwith "BIND_TAC"
  else
    let th_m = TYSYS2AUX_triple_for asl prims (hd bargs) in
    (MATCH_MP_TAC (MATCH_MP TYSYS2AUX_hoare_bindw th_m) THEN REPEAT CONJ_TAC) g;;

let TYSYS2AUX_WEAKEN_TAC prims (asl,w as g) =
  let (_,args) = strip_comb w in
  let th_m = TYSYS2AUX_triple_for asl prims (el 3 args) in
  (MATCH_MP_TAC (MATCH_MP TYSYS2AUX_hoare_weakenw th_m) THEN CONJ_TAC) g;;

let TYSYS2AUX_COND_DISCH_TAC =
  DISCH_THEN(fun c ->
    RULE_ASSUM_TAC(REWRITE_RULE[c; injectivity "option"; option_DISTINCT;
                                FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
    ASSUME_TAC c);;

let TYSYS2AUX_VCG_STEP_TAC prims =
  REPEAT GEN_TAC THEN BETA_TAC THEN
  FIRST [MATCH_ACCEPT_TAC TYSYS2AUX_hoare_failwith;
         MATCH_MP_TAC TYSYS2AUX_hoare_return THEN CONJ_TAC;
         TYSYS2AUX_BIND_TAC prims;
         MATCH_MP_TAC TYSYS2AUX_hoare_cond THEN CONJ_TAC THEN TYSYS2AUX_COND_DISCH_TAC;
         MATCH_MP_TAC TYSYS2AUX_hoare_pair THEN REPEAT GEN_TAC THEN
           DISCH_THEN(fun th -> SUBST_ALL_TAC th ORELSE ASSUME_TAC th);
         MATCH_MP_TAC TYSYS2AUX_hoare_option THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
           TYSYS2AUX_COND_DISCH_TAC;
         TYSYS2AUX_WEAKEN_TAC prims];;

let rec TYSYS2AUX_VCG_TAC prims closer (asl,w as g) =
  if TYSYS2AUX_is_hoare w
  then (TYSYS2AUX_VCG_STEP_TAC prims THEN TYSYS2AUX_VCG_TAC prims closer) g
  else closer g;;

let TYSYS2AUX_nle_def = new_definition
 `TYSYS2AUX_nle (st:infer_st) st' <=> infer_st_next_uvar st <= infer_st_next_uvar st'`;;

let TYSYS2AUX_nle_trans = prove
 (`!a b c. TYSYS2AUX_nle a b /\ TYSYS2AUX_nle b c ==> TYSYS2AUX_nle a c`,
  REWRITE_TAC[TYSYS2AUX_nle_def] THEN ARITH_TAC);;

let TYSYS2AUX_nle_refl = prove
 (`!s. TYSYS2AUX_nle s s`,
  REWRITE_TAC[TYSYS2AUX_nle_def; LE_REFL]);;

(* Triples of the primitive computations, with the trivial invariant *)

let TYSYS2AUX_ht_fresh_uvar = prove
 (`TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
     (fresh_uvar:infer_st->(infer_t,locs option#mlstring)exc#infer_st)
     (\v st. check_t 0 (count (infer_st_next_uvar st)) v)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; fresh_uvar_success] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_rewrs; check_t_def; IN_COUNT] THEN
  ARITH_TAC);;

let TYSYS2AUX_ht_n_fresh_uvar = prove
 (`!n. TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
         (n_fresh_uvar n:infer_st->(infer_t list,locs option#mlstring)exc#infer_st)
         (\v st. ALL (check_t 0 (count (infer_st_next_uvar st))) v /\ LENGTH v = n)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; n_fresh_uvar_success] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[infer_st_rewrs; LENGTH_MAP; LENGTH_COUNT_LIST; ALL_MAP; o_DEF;
                  check_t_def; IN_COUNT; LE_ADD] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_COUNT_LIST] THEN ARITH_TAC);;

let TYSYS2AUX_ht_add_constraint = prove
 (`!l t1 t2. TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
               (add_constraint l t1 t2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; add_constraint_success] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_rewrs; LE_REFL]);;

let TYSYS2AUX_ht_add_constraints = prove
 (`!l ts1 ts2. TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
                 (add_constraints l ts1 ts2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; add_constraints_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_ht_constrain_op = prove
 (`!l op ts. TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle
               (\st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts)
               (constrain_op l op ts) (\t st. check_t 0 (count (infer_st_next_uvar st)) t)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def] THEN
  MESON_TAC[TYSYS2AUX_constrain_op_state; constrain_op_check_t]);;

let TYSYS2AUX_ht_lookup = prove
 (`!l err id (env:(mlstring,mlstring,V)namespace).
     TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
       (lookup_st_ex l err id env:infer_st->(V,locs option#mlstring)exc#infer_st)
       (\v st. nsLookup env id = SOME v)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; lookup_st_ex_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_ht_check_dups = prove
 (`!l (f:mlstring->mlstring) ls.
     TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
       (check_dups l f ls:infer_st->(1,locs option#mlstring)exc#infer_st) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; check_dups_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_ht_tncs = prove
 (`!l f tenvT fvs t.
     TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
       (type_name_check_subst l f tenvT fvs t)
       (\v st. v = type_name_subst tenvT t /\ check_freevars_ast fvs t /\
               check_type_names tenvT t)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; type_name_check_subst_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_ht_guard = prove
 (`!P l (msg:mlstring).
     TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
       (infer_guard P l msg:infer_st->(1,locs option#mlstring)exc#infer_st) (\v st. P)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; guard_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_ht_infer_p = prove
 (`!l ienv p.
     TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T) (infer_p l ienv p)
       (\v st. check_t 0 (count (infer_st_next_uvar st)) (FST v) /\
               ALL (\(x,t). check_t 0 (count (infer_st_next_uvar st)) t) (SND v))`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; FORALL_PAIR_THM] THEN
  MESON_TAC[infer_p_check_t; infer_p_next_uvar_mono]);;

let TYSYS2AUX_ht_infer_pes = prove
 (`!l ienv pes t1 t2.
     TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
       (infer_pes l ienv pes t1 t2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; FORALL_ONE_THM] THEN
  MESON_TAC[infer_e_next_uvar_mono]);;

(* check_t_infer_deBruijn_subst is HOL4's theorem (stated further down in the *)
(* HOL4 script); it is proved here because infer_e_check_t uses it            *)

let check_t_infer_deBruijn_subst = prove
 (`!subst t tvs uvs.
     check_t (tvs + LENGTH subst) uvs t /\ ALL (check_t tvs uvs) subst
     ==> check_t tvs uvs (infer_deBruijn_subst subst t)`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_subst_alt; check_t_def] THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_EL]) THEN ASM_MESON_TAC[];
      REWRITE_TAC[check_t_def] THEN ASM_ARITH_TAC];
    REWRITE_TAC[ALL_MAP; o_DEF] THEN
    UNDISCH_TAC `ALL (check_t (tvs + LENGTH (subst:infer_t list)) uvs) l` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]]);;

let TYSYS2AUX_ht_return = prove
 (`!G (x:A).
     TYSYS2AUX_hoare G TYSYS2AUX_nle (\st. T)
       (st_ex_return x:infer_st->(A,locs option#mlstring)exc#infer_st) (\v st. v = x)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; inferProps_st_ex_return_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_ienv_val_ok_letrec2 = prove
 (CASE_TERM `!m (funs:(mlstring#mlstring#exp)list) uvars env.
     ALL (check_t 0 (count m)) uvars /\ LENGTH uvars = LENGTH funs /\
     ienv_val_ok (count m) env
     ==> ienv_val_ok (count m)
           (nsAppend
              (alist_to_ns
                 (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs uvars))
              env)`,
  GEN_TAC THEN REWRITE_TAC[ienv_val_ok_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`uvars:infer_t list`,`uvars:infer_t list`) THEN
  SPEC_TAC(`funs:(mlstring#mlstring#exp)list`,`funs:(mlstring#mlstring#exp)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP2; ALL; LENGTH; NOT_SUC; SUC_INJ] THEN
  X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `e:exp`
    SUBST_ALL_TAC)) (ISPEC `h:mlstring#mlstring#exp` BASICAUX_TUPLE3) THEN
  BETA_TAC THEN CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let TYSYS2AUX_ienv_val_ok_lookup = prove
 (`!n env id tvs t.
     ienv_val_ok (count n) env /\ nsLookup env id = SOME (tvs,t)
     ==> check_t tvs (count n) t`,
  REWRITE_TAC[ienv_val_ok_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP nsLookup_nsAll) THEN BETA_TAC THEN CASE_REWRITE_TAC[]);;

let TYSYS2AUX_check_t_db0 = prove
 (`!subst t uvs.
     check_t (LENGTH subst) uvs t /\ ALL (check_t 0 uvs) subst
     ==> check_t 0 uvs (infer_deBruijn_subst subst t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC check_t_infer_deBruijn_subst THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let TYSYS2AUX_CT_PRIMS =
  [TYSYS2AUX_ht_fresh_uvar; TYSYS2AUX_ht_n_fresh_uvar; TYSYS2AUX_ht_add_constraint;
   TYSYS2AUX_ht_add_constraints; TYSYS2AUX_ht_constrain_op; TYSYS2AUX_ht_lookup;
   TYSYS2AUX_ht_check_dups; TYSYS2AUX_ht_tncs; TYSYS2AUX_ht_guard; TYSYS2AUX_ht_infer_p;
   TYSYS2AUX_ht_infer_pes; TYSYS2AUX_ht_return];;

let TYSYS2AUX_CT_CLOSER =
  FIRST [MATCH_ACCEPT_TAC TYSYS2AUX_nle_trans;
         MATCH_ACCEPT_TAC TYSYS2AUX_nle_refl;
         REWRITE_TAC[TYSYS2AUX_nle_def; inf_env_INFO.ri_accfupds; K_THM] THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[check_t_def; ALL; IN_COUNT] THEN
         ASM_MESON_TAC[TYSYS2AUX_check_t_mono; TYSYS2AUX_ienv_val_ok_mono;
                       TYSYS2AUX_ienv_val_ok_nsBind; TYSYS2AUX_ienv_val_ok_nsOptBind;
                       TYSYS2AUX_ienv_val_ok_letrec2; TYSYS2AUX_ienv_val_ok_lookup;
                       TYSYS2AUX_check_t_db0]];;

let TYSYS2AUX_infer_e_hoare_t = prove
 (`(!l ienv e.
      TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle
        (\st. ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv))
        (infer_e l ienv e) (\t st. check_t 0 (count (infer_st_next_uvar st)) t)) /\
   (!l ienv es.
      TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle
        (\st. ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv))
        (infer_es l ienv es) (\ts st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts)) /\
   (!l ienv pes t1 t2.
      TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle (\st. T)
        (infer_pes l ienv pes t1 t2) (\v st. T)) /\
   (!l ienv funs.
      TYSYS2AUX_hoare (\st:infer_st. T) TYSYS2AUX_nle
        (\st. ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv))
        (infer_funs l ienv funs)
        (\ts st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts))`,
  MATCH_MP_TAC infer_e_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY(DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[])) THEN
  TRY(MATCH_ACCEPT_TAC TYSYS2AUX_ht_infer_pes) THEN
  REWRITE_TAC[infer_e_def; TYSYS2AUX_ignore_bind_eq] THEN
  TYSYS2AUX_VCG_TAC TYSYS2AUX_CT_PRIMS TYSYS2AUX_CT_CLOSER);;

let infer_e_check_t = prove
 (`(!l ienv e st st' t.
      infer_e l ienv e st = (M_success t,st') /\
      ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv)
      ==> check_t 0 (count (infer_st_next_uvar st')) t) /\
   (!l ienv es st st' ts.
      infer_es l ienv es st = (M_success ts,st') /\
      ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv)
      ==> ALL (check_t 0 (count (infer_st_next_uvar st'))) ts) /\
   (!l ienv pes t1 t2 st st'.
      infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
      ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv)
      ==> T) /\
   (!l ienv funs st st' ts'.
      infer_funs l ienv funs st = (M_success ts',st') /\
      ienv_val_ok (count (infer_st_next_uvar st)) (inf_env_inf_v ienv)
      ==> ALL (check_t 0 (count (infer_st_next_uvar st'))) ts')`,
  MP_TAC TYSYS2AUX_infer_e_hoare_t THEN REWRITE_TAC[TYSYS2AUX_hoare_def] THEN
  MESON_TAC[]);;

let constrain_op_wfs = prove
 (`!l (tvs:num) op ts t st st'.
     constrain_op l op ts st = (M_success t,st') /\ t_wfs (infer_st_subst st)
     ==> t_wfs (infer_st_subst st')`,
  MESON_TAC[TYSYS2AUX_constrain_op_state; pure_add_constraints_wfs]);;

let TYSYS2AUX_cs_step = prove
 (`!s1 s2 t1 t2 tvs uvs.
     t_unify s1 t1 t2 = SOME s2
     ==> t_wfs s1 /\ check_s tvs uvs s1 /\ check_t tvs uvs t1 /\ check_t tvs uvs t2
         ==> t_wfs s2 /\ check_s tvs uvs s2`,
  MESON_TAC[t_unify_check_s; t_unify_wfs]);;

let TYSYS2AUX_SPLIT_ASM_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then CONJUNCTS_THEN ASSUME_TAC th else failwith "split"));;

let TYSYS2AUX_CONTRA_TAC =
  FIRST_ASSUM(fun th ->
    if is_neg(concl th) then
      FIRST_ASSUM(fun th' ->
        if aconv (concl th') (dest_neg(concl th)) then CONTR_TAC(MP (NOT_ELIM th) th')
        else failwith "contra")
    else failwith "contra");;

(* Closing a goal check_s tvs (count N) s after a successful run started in  *)
(* the state st: the facts at count (infer_st_next_uvar st) are lifted to    *)
(* count N, then the unifications are chained (or the constraint list of     *)
(* pure_add_constraints is checked)                                          *)

let TYSYS2AUX_CHECK_S_CHAIN_TAC : tactic = fun (asl,w as g) ->
  let is_app nm tm = try fst(dest_const(fst(strip_comb tm))) = nm with Failure _ -> false in
  let tvs = rand(rator(rator w)) and cn = rand(rator w) in
  let n = rand cn in
  let n0 = `infer_st_next_uvar st` in
  let cn0 = mk_comb(`count`,n0) in
  let le = mk_binop `(<=):num->num->bool` n0 n in
  let lift_tac =
    SUBGOAL_THEN le ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_app "check_t" c && rand(rator c) = cn0 && rand(rator(rator c)) = `0`
      then ASSUME_TAC(MATCH_MP (CONJUNCT1 TYSYS2AUX_check_t_lift) (CONJ th (ASSUME le)))
      else if is_app "ALL" c &&
              (let p = rand(rator c) in
               is_app "check_t" p && rand p = cn0 && rand(rator p) = `0`)
      then ASSUME_TAC(MATCH_MP (CONJUNCT2 TYSYS2AUX_check_t_lift) (CONJ th (ASSUME le)))
      else failwith "lift")) THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_app "check_s" c && rand(rator c) = cn0
      then ASSUME_TAC(MP (SPEC n (MATCH_MP check_s_more2 th)) (ASSUME le))
      else failwith "lift_s") in
  let chain_tac =
    REPEAT(FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && is_app "t_unify" (lhs c)
      then MP_TAC(SPECL [tvs; cn] (MATCH_MP TYSYS2AUX_cs_step th)) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[check_t_def; ALL; IN_COUNT] THEN ASM_ARITH_TAC;
             STRIP_TAC]
      else failwith "chain")) in
  let pac_tac =
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_app "pure_add_constraints" c then
        let args = snd(strip_comb c) in
        MATCH_MP_TAC pure_add_constraints_check_s THEN
        EXISTS_TAC (el 0 args) THEN EXISTS_TAC (el 1 args) THEN
        ASM_SIMP_TAC[every_shim2; every_zip_fst; every_zip_snd] THEN
        REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[EVERY_REPLICATE; check_t_def; ALL]
      else failwith "pac") in
  (lift_tac THEN chain_tac THEN FIRST [FIRST_ASSUM ACCEPT_TAC; pac_tac]) g;;

let constrain_op_check_s = prove
 (`!l tvs op ts t st st'.
     constrain_op l op ts st = (M_success t,st') /\
     t_wfs (infer_st_subst st) /\
     ALL (check_t 0 (count (infer_st_next_uvar st))) ts /\
     check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
     ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st')`,
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `op:op` THEN CASES_ON `op:op` THEN
  REWRITE_TAC[constrain_op_success; add_constraints_success] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(CHANGED_TAC(RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; ALL; infer_st_rewrs]) THEN
                     TYSYS2AUX_SPLIT_ASM_TAC THEN TYSYS2AUX_SUBST_VARS_TAC)) THEN
  REWRITE_TAC[infer_st_rewrs] THEN
  FIRST [TYSYS2AUX_CONTRA_TAC; FIRST_ASSUM ACCEPT_TAC; TYSYS2AUX_CHECK_S_CHAIN_TAC]);;

let ienv_ok_def = cake_def
  `ienv_ok (uvars:num->bool) (ienv:inf_env) <=>
     ienv_val_ok uvars (inf_env_inf_v ienv) /\
     tenv_ctor_ok (inf_env_inf_c ienv) /\
     tenv_abbrev_ok (inf_env_inf_t ienv)`;;

let ienv_ok_more = prove
 (`!uv uv' ienv. ienv_ok (count uv) ienv /\ uv <= uv' ==> ienv_ok (count uv') ienv`,
  REWRITE_TAC[ienv_ok_def; ienv_val_ok_def] THEN MESON_TAC[check_env_more]);;

let TYSYS2AUX_gs_def = new_definition
 `TYSYS2AUX_gs tvs (st:infer_st) <=>
    t_wfs (infer_st_subst st) /\
    check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)`;;

let TYSYS2AUX_hs_fresh_uvar = prove
 (`!tvs. TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle (\st. T)
           (fresh_uvar:infer_st->(infer_t,locs option#mlstring)exc#infer_st)
           (\v st. check_t 0 (count (infer_st_next_uvar st)) v)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gs_def;
              fresh_uvar_success] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_rewrs; check_t_def; IN_COUNT] THEN
  ASM_SIMP_TAC[check_s_more] THEN ARITH_TAC);;

let TYSYS2AUX_hs_n_fresh_uvar = prove
 (`!tvs n. TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle (\st. T)
             (n_fresh_uvar n:infer_st->(infer_t list,locs option#mlstring)exc#infer_st)
             (\v st. ALL (check_t 0 (count (infer_st_next_uvar st))) v /\ LENGTH v = n)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gs_def;
              n_fresh_uvar_success] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[infer_st_rewrs; LENGTH_MAP; LENGTH_COUNT_LIST; ALL_MAP; o_DEF;
                  check_t_def; IN_COUNT; LE_ADD] THEN
  FIRST [ASM_MESON_TAC[check_s_more2; LE_ADD];
         REWRITE_TAC[GSYM ALL_MEM; MEM_COUNT_LIST] THEN ARITH_TAC]);;

let TYSYS2AUX_hs_add_constraint = prove
 (`!tvs l t1 t2.
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
       (\st. check_t 0 (count (infer_st_next_uvar st)) t1 /\
             check_t 0 (count (infer_st_next_uvar st)) t2)
       (add_constraint l t1 t2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gs_def;
              add_constraint_success] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_rewrs; LE_REFL] THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  MATCH_MP_TAC t_unify_check_s THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st`; `t1:infer_t`; `t2:infer_t`] THEN
  ASM_MESON_TAC[TYSYS2AUX_check_t_lift; LE_REFL]);;

let TYSYS2AUX_hs_add_constraints = prove
 (`!tvs l ts1 ts2.
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
       (\st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts1 /\
             ALL (check_t 0 (count (infer_st_next_uvar st))) ts2)
       (add_constraints l ts1 ts2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gs_def;
              add_constraints_success] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "infer_st_next_uvar"
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MATCH_MP_TAC pure_add_constraints_check_s THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st`; `ZIP (ts1:infer_t list) (ts2:infer_t list)`] THEN
  ASM_SIMP_TAC[every_shim2; every_zip_fst; every_zip_snd] THEN
  REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  MATCH_MP_TAC(CONJUNCT2 TYSYS2AUX_check_t_lift) THEN
  EXISTS_TAC `infer_st_next_uvar st` THEN ASM_REWRITE_TAC[LE_REFL]);;

let TYSYS2AUX_hs_constrain_op = prove
 (`!tvs l op ts.
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
       (\st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts)
       (constrain_op l op ts) (\t st. check_t 0 (count (infer_st_next_uvar st)) t)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gs_def] THEN
  MESON_TAC[TYSYS2AUX_constrain_op_state; constrain_op_check_t; constrain_op_wfs;
            constrain_op_check_s]);;

let TYSYS2AUX_hs_lookup = prove
 (`!tvs l err id (env:(mlstring,mlstring,V)namespace).
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle (\st. T)
       (lookup_st_ex l err id env:infer_st->(V,locs option#mlstring)exc#infer_st)
       (\v st. nsLookup env id = SOME v)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; lookup_st_ex_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hs_check_dups = prove
 (`!tvs l (f:mlstring->mlstring) ls.
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle (\st. T)
       (check_dups l f ls:infer_st->(1,locs option#mlstring)exc#infer_st) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; check_dups_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hs_tncs = prove
 (`!tvs l f tenvT fvs t.
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle (\st. T)
       (type_name_check_subst l f tenvT fvs t)
       (\v st. v = type_name_subst tenvT t /\ check_freevars_ast fvs t /\
               check_type_names tenvT t)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; type_name_check_subst_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hs_guard = prove
 (`!tvs P l (msg:mlstring).
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle (\st. T)
       (infer_guard P l msg:infer_st->(1,locs option#mlstring)exc#infer_st) (\v st. P)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; guard_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hs_infer_p = prove
 (`!tvs l ienv p.
     TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
       (\st. tenv_ctor_ok (inf_env_inf_c ienv) /\ tenv_abbrev_ok (inf_env_inf_t ienv))
       (infer_p l ienv p)
       (\v st. check_t 0 (count (infer_st_next_uvar st)) (FST v) /\
               ALL (check_t 0 (count (infer_st_next_uvar st))) (MAP SND (SND v)))`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gs_def; FORALL_PAIR_THM] THEN
  MESON_TAC[REWRITE_RULE[every_shim; ETA_AX] infer_p_check_t; infer_p_next_uvar_mono;
            infer_p_wfs; infer_p_check_s]);;

let TYSYS2AUX_check_t_infer_type_subst = prove
 (`(!t tvs (ts':infer_t list) uvs.
      check_freevars 0 tvs t /\ LENGTH tvs = LENGTH ts' /\ ALL (check_t 0 uvs) ts'
      ==> check_t 0 uvs (infer_type_subst (ZIP tvs ts') t)) /\
   (!ts tvs (ts':infer_t list) uvs.
      ALL (check_freevars 0 tvs) ts /\ LENGTH tvs = LENGTH ts' /\ ALL (check_t 0 uvs) ts'
      ==> ALL (check_t 0 uvs) (MAP (infer_type_subst (ZIP tvs ts')) ts))`,
  MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[check_freevars_def; infer_type_subst_alt; check_t_def; ALL; MAP; LT] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`tvs:mlstring list`; `ts':infer_t list`; `a:mlstring`]
             ALOOKUP_ZIP_FAIL) THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `ALOOKUP (ZIP (tvs:mlstring list) (ts':infer_t list)) a` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN ASM_SIMP_TAC[MEM_ZIP] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_EL]) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let TYSYS2AUX_check_t_tannot = prove
 (`!tenvT t n.
     tenv_abbrev_ok tenvT /\ check_freevars_ast [] t /\ check_type_names tenvT t
     ==> check_t 0 (count n) (infer_type_subst [] (type_name_subst tenvT t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `check_t 0 {} (infer_type_subst [] (type_name_subst tenvT t))` MP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_type_subst_empty_check) THEN
    ASM_MESON_TAC[check_freevars_type_name_subst];
    MESON_TAC[check_t_more]]);;

let TYSYS2AUX_ienv_val_ok_pes = prove
 (CASE_TERM `!m (env':(mlstring#infer_t)list) env.
     ALL (check_t 0 (count m)) (MAP SND env') /\ ienv_val_ok (count m) env
     ==> ienv_val_ok (count m)
           (nsAppend (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) env')) env)`,
  REWRITE_TAC[ienv_val_ok_def; ALL_MAP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN REWRITE_TAC[ALL_MAP] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_comb(concl th) &&
    (try fst(dest_const(fst(strip_comb(concl th)))) = "nsAll" with Failure _ -> false))) THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

let TYSYS2AUX_CS_PRIMS =
  [TYSYS2AUX_hs_fresh_uvar; TYSYS2AUX_hs_n_fresh_uvar; TYSYS2AUX_hs_add_constraint;
   TYSYS2AUX_hs_add_constraints; TYSYS2AUX_hs_constrain_op; TYSYS2AUX_hs_lookup;
   TYSYS2AUX_hs_check_dups; TYSYS2AUX_hs_tncs; TYSYS2AUX_hs_guard; TYSYS2AUX_hs_infer_p;
   TYSYS2AUX_ht_return];;

let TYSYS2AUX_CS_CLOSER =
  FIRST [MATCH_ACCEPT_TAC TYSYS2AUX_nle_trans;
         MATCH_ACCEPT_TAC TYSYS2AUX_nle_refl;
         REWRITE_TAC[TYSYS2AUX_nle_def; ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM; FST; SND] THEN
         BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[check_t_def; ALL; IN_COUNT] THEN
         ASM_MESON_TAC[TYSYS2AUX_check_t_mono; TYSYS2AUX_ienv_val_ok_mono;
                       TYSYS2AUX_ienv_val_ok_nsBind; TYSYS2AUX_ienv_val_ok_nsOptBind;
                       TYSYS2AUX_ienv_val_ok_letrec2; TYSYS2AUX_ienv_val_ok_lookup;
                       TYSYS2AUX_check_t_db0; TYSYS2AUX_ienv_val_ok_pes;
                       TYSYS2AUX_check_t_tannot; tenv_ctor_ok_lookup;
                       CONJUNCT2 TYSYS2AUX_check_t_infer_type_subst]];;

let TYSYS2AUX_infer_e_hoare_s = prove
 (`!tvs.
   (!l ienv e.
      TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
        (\st. ienv_ok (count (infer_st_next_uvar st)) ienv)
        (infer_e l ienv e) (\t st. check_t 0 (count (infer_st_next_uvar st)) t)) /\
   (!l ienv es.
      TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
        (\st. ienv_ok (count (infer_st_next_uvar st)) ienv)
        (infer_es l ienv es) (\ts st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts)) /\
   (!l ienv pes t1 t2.
      TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
        (\st. ienv_ok (count (infer_st_next_uvar st)) ienv /\
              check_t 0 (count (infer_st_next_uvar st)) t1 /\
              check_t 0 (count (infer_st_next_uvar st)) t2)
        (infer_pes l ienv pes t1 t2) (\v st. T)) /\
   (!l ienv funs.
      TYSYS2AUX_hoare (TYSYS2AUX_gs tvs) TYSYS2AUX_nle
        (\st. ienv_ok (count (infer_st_next_uvar st)) ienv)
        (infer_funs l ienv funs)
        (\ts st. ALL (check_t 0 (count (infer_st_next_uvar st))) ts))`,
  GEN_TAC THEN MATCH_MP_TAC infer_e_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY(DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[])) THEN
  REWRITE_TAC[infer_e_def; TYSYS2AUX_ignore_bind_eq] THEN
  TYSYS2AUX_VCG_TAC TYSYS2AUX_CS_PRIMS TYSYS2AUX_CS_CLOSER);;

let infer_e_check_s = prove
 (`(!l ienv e st st' t tvs.
      infer_e l ienv e st = (M_success t,st') /\
      t_wfs (infer_st_subst st) /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
      ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st')) /\
   (!l ienv es st st' ts tvs.
      infer_es l ienv es st = (M_success ts,st') /\
      t_wfs (infer_st_subst st) /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
      ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st')) /\
   (!l ienv pes t1 t2 st st' tvs.
      infer_pes l ienv pes t1 t2 st = (M_success one,st') /\
      t_wfs (infer_st_subst st) /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      check_t 0 (count (infer_st_next_uvar st)) t1 /\
      check_t 0 (count (infer_st_next_uvar st)) t2 /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
      ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st')) /\
   (!l ienv funs st st' ts' tvs.
      infer_funs l ienv funs st = (M_success ts',st') /\
      t_wfs (infer_st_subst st) /\
      ienv_ok (count (infer_st_next_uvar st)) ienv /\
      check_s tvs (count (infer_st_next_uvar st)) (infer_st_subst st)
      ==> check_s tvs (count (infer_st_next_uvar st')) (infer_st_subst st'))`,
  MP_TAC TYSYS2AUX_infer_e_hoare_s THEN
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_gs_def] THEN MESON_TAC[]);;

(* ---------- Completeness of generalisation: helper lemmas ---------- *)

let generalise_complete_lemma = prove
 (`!tvs (ts:(num#num)list).
     (!uv. uv IN FDOM (FEMPTY |++ ts) ==> ?tv. FAPPLY (FEMPTY |++ ts) uv = tv /\ tv < tvs)
     ==> (!uv. uv IN FDOM (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts)
               ==> ?tv. FAPPLY (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts) uv =
                        Infer_Tvar_db tv /\ tv < tvs)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `uv IN FDOM (FEMPTY |++ (ts:(num#num)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `uv IN FDOM (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv))
                                        (ts:(num#num)list))` THEN
    REWRITE_TAC[FDOM_FUPDATE_LIST; map_fst; FDOM_FEMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[fupdate_list_map; injectivity "infer_t"] THEN ASM_MESON_TAC[]);;

let generalise_complete_lemma2 = prove
 (`!s (ts:(num#infer_t)list) TC_unit.
     t_wfs s /\ ALL_DISTINCT (MAP FST ts) /\
     ALL (\t. t = Infer_Tapp [] TC_unit \/ ?tvs. t = Infer_Tvar_db tvs) (MAP SND ts) /\
     DISJOINT (FDOM s) (FDOM (FEMPTY |++ ts))
     ==> pure_add_constraints s (MAP (\(uv,t). (Infer_Tuvar uv,t)) ts) (s |++ ts)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; pure_add_constraints_def; FUPDATE_LIST_THM] THEN
  MP_TAC(ISPEC `h:num#infer_t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:num` (X_CHOOSE_THEN `h1:infer_t` SUBST1_TAC)) THEN
  REWRITE_TAC[pure_add_constraints_def; ALL; ALL_DISTINCT; MAP; FST; SND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `~(h0 IN FDOM (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "DISJOINT" with Failure _ -> false)) THEN
    REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FUPDATE; MAP; FST; set_of_list; FDOM_FEMPTY;
                UNION_EMPTY] THEN
    SET_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `t_unify s (Infer_Tuvar h0) h1 = SOME (s |+ (h0,h1))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_unify_eqn th]) THEN
    REWRITE_TAC[t_walk_eqn] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn th]) THEN
    SUBGOAL_THEN `FLOOKUP (s:(num,infer_t)fmap) h0 = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[flookup_thm]; ALL_TAC] THEN
    ASM_REWRITE_TAC[t_walk_eqn] THEN CASE_REWRITE_TAC[t_ext_s_check_eqn] THEN
    ASM_SIMP_TAC[oc_unit; oc_tvar_db];
    ALL_TAC]) THEN
  EXISTS_TAC `(s:(num,infer_t)fmap) |+ (h0,h1)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`(s:(num,infer_t)fmap) |+ (h0,h1)`; `TC_unit:num`]) THEN
  ASM_REWRITE_TAC[] THEN (CONJ_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC]) THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "DISJOINT" with Failure _ -> false)) THEN
  UNDISCH_TAC `~MEM (h0:num) (MAP FST (t:(num#infer_t)list))` THEN
  REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FUPDATE; MAP; FST; set_of_list; FDOM_FEMPTY;
              UNION_EMPTY; GSYM IN_SET_OF_LIST] THEN
  SET_TAC[]);;

let infer_subst_var_def = cake_def
  `(infer_subst_var (s:(num,num)fmap) (Infer_Tuvar n) =
      match FLOOKUP s n with
        NONE -> Infer_Tuvar n
      | SOME tv -> Infer_Tvar_db tv) /\
   (infer_subst_var s (Infer_Tvar_db m) = Infer_Tvar_db m) /\
   (infer_subst_var s (Infer_Tapp ts tc) = Infer_Tapp ts tc)`;;

let generalise_complete_lemma4 = prove
 (`!s. t_wfs s ==>
     !t (s':(num#num)list).
       t_wfs (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s') /\
       ALL_DISTINCT (MAP FST s') /\
       DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s'))
       ==> infer_subst_var (FEMPTY |++ s') (t_vwalk s t) =
           t_vwalk (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s') t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN X_GEN_TAC `l:(num#num)list` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [MATCH_MP t_vwalk_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`)] THEN
  GEN_REWRITE_TAC RAND_CONV
    [MATCH_MP t_vwalk_eqn (ASSUME `t_wfs ((s:(num,infer_t)fmap) |++
                                          MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) l)`)] THEN
  REWRITE_TAC[flookup_fupdate_list; MAP_REVERSE; ALOOKUP_MAP; o_THM; FLOOKUP_EMPTY] THEN
  ASM_CASES_TAC `v IN FDOM (s:(num,infer_t)fmap)` THENL
   [SUBGOAL_THEN `ALOOKUP (REVERSE (l:(num#num)list)) v = NONE` SUBST1_TAC THENL
     [REWRITE_TAC[ALOOKUP_NONE; GSYM MAP_REVERSE; MEM_REVERSE] THEN
      FIRST_ASSUM(MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "DISJOINT" with Failure _ -> false)) THEN
      REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY; map_fst] THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[option_CASE; OPTION_MAP_DEF] THEN
    CASES_ON `FLOOKUP (s:(num,infer_t)fmap) v` THEN CASE_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[flookup_thm]; ALL_TAC] THEN
    CASES_ON `a:infer_t` THEN CASE_REWRITE_TAC[infer_subst_var_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Infer_Tuvar a'`; `a':num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `FLOOKUP (s:(num,infer_t)fmap) v = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[flookup_thm]; ALL_TAC] THEN
    CASE_REWRITE_TAC[infer_subst_var_def; flookup_fupdate_list; FLOOKUP_EMPTY] THEN
    CASES_ON `ALOOKUP (REVERSE (l:(num#num)list)) v` THEN
    CASE_REWRITE_TAC[OPTION_MAP_DEF; option_CASE]]);;

let generalise_complete_lemma5 = prove
 (`!s. t_wfs s ==>
     !t (s':(num#num)list).
       t_wfs (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s')
       ==> ALL_DISTINCT (MAP FST s') /\
           DISJOINT (FDOM s) (FDOM (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s'))
           ==> infer_subst (FEMPTY |++ s') (t_walkstar s t) =
               t_walkstar (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) s') t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN X_GEN_TAC `l:(num#num)list` THEN
  REPEAT STRIP_TAC THEN CASES_ON `t:infer_t` THENL
   [ASM_SIMP_TAC[t_walkstar_eqn1; infer_subst_def];
    ASM_SIMP_TAC[t_walkstar_eqn1; infer_subst_def; injectivity "infer_t"; GSYM MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[t_walk_eqn; injectivity "infer_t"]) THEN
    ASM_MESON_TAC[];
    MP_TAC(SPEC `s:(num,infer_t)fmap` generalise_complete_lemma4) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`a:num`; `l:(num#num)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [MATCH_MP t_walkstar_eqn (ASSUME `t_wfs (s:(num,infer_t)fmap)`)] THEN
    GEN_REWRITE_TAC RAND_CONV
      [MATCH_MP t_walkstar_eqn (ASSUME `t_wfs ((s:(num,infer_t)fmap) |++
                                          MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) l)`)] THEN
    REWRITE_TAC[t_walk_eqn] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[t_walk_eqn]) THEN
    CASES_ON `t_vwalk (s:(num,infer_t)fmap) a` THEN
    CASE_REWRITE_TAC[infer_subst_var_def; infer_subst_def] THEN
    TRY(REWRITE_TAC[injectivity "infer_t"; GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
        REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "infer_t"]) THEN ASM_MESON_TAC[]) THEN
    CASES_ON `FLOOKUP (FEMPTY |++ (l:(num#num)list)) a'` THEN CASE_REWRITE_TAC[]]);;

let fst_lem = prove
 (`(FST:A#B->A) = (\(x,y). x)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST]);;

let t_ind = prove
 (`!P. (!s. P (Tvar s)) /\ (!n. P (Tvar_db n)) /\
       (!l. ALL P l ==> !t. P (Tapp l t))
       ==> !t. P t`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:t->bool`; `ALL (P:t->bool)`] t_INDUCT) THEN
  ASM_REWRITE_TAC[ALL] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]);;

(* Rename (type_system) type identifiers with a function *)

let ts_tid_rename_def = cake_def
  `(ts_tid_rename (f:num->num) (Tapp ts tn) = Tapp (MAP (ts_tid_rename f) ts) (f tn)) /\
   (ts_tid_rename f (Tvar v) = Tvar v) /\
   (ts_tid_rename f (Tvar_db n) = Tvar_db n)`;;

let ts_tid_rename_ind = cake_ind "ts_tid_rename";;

let ts_tid_rename_I = prove
 (`ts_tid_rename I = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM] THEN MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[ts_tid_rename_def; I_THM; injectivity "t"] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [ts_tid_rename_I];;

(* All type ids in a type belonging to a set *)

let set_tids_def = cake_def
  `(set_tids (Tapp ts tn) = (tn:num) INSERT UNIONS (set_of_list (MAP set_tids ts))) /\
   (set_tids (Tvar v) = {}) /\
   (set_tids (Tvar_db n) = {})`;;

let set_tids_ind = cake_ind "set_tids";;

let set_tids_ts_tid_rename = prove
 (`!f t. set_tids (ts_tid_rename f t) = IMAGE f (set_tids t)`,
  GEN_TAC THEN MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[ts_tid_rename_def; set_tids_def; IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `MAP set_tids (MAP (ts_tid_rename f) l) = MAP (IMAGE f o set_tids) l`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    FIRST_X_ASSUM(MP_TAC) THEN MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[o_THM];
    REWRITE_TAC[SET_OF_LIST_MAP; IMAGE_UNIONS; IMAGE_o]]);;

let set_tids_subset_def = cake_def
  `set_tids_subset (tids:num->bool) t <=> set_tids t SUBSET tids`;;

let set_tids_subset_type_subst = prove
 (`!s t tids.
     FEVERY (set_tids_subset tids o SND) s /\ set_tids_subset tids t
     ==> set_tids_subset tids (type_subst s t)`,
  MATCH_MP_TAC type_subst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[type_subst_def] THEN
    CASES_ON `FLOOKUP (s:(mlstring,t)fmap) tv` THEN CASE_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP FEVERY_FLOOKUP o
      CONJ (ASSUME `FEVERY (set_tids_subset tids o SND) (s:(mlstring,t)fmap)`)) THEN
    REWRITE_TAC[o_THM];
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[type_subst_def; set_tids_subset_def; set_tids_def; INSERT_SUBSET;
                UNIONS_SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[set_tids_subset_def]) THEN ASM_MESON_TAC[];
    REWRITE_TAC[type_subst_def] THEN MESON_TAC[]]);;

let unconvert_t_def = cake_def
  `(unconvert_t (Tvar_db n) = Infer_Tvar_db n) /\
   (unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc) /\
   (unconvert_t (Tvar v) = Infer_Tuvar ARB)`;;

let unconvert_t_ind = cake_ind "unconvert_t";;

(* Properties about inferencer type identifiers *)

let inf_set_tids_def = cake_def
  `(inf_set_tids (Infer_Tapp ts tn) =
      (tn:num) INSERT UNIONS (set_of_list (MAP inf_set_tids ts))) /\
   (inf_set_tids (Infer_Tvar_db n) = {}) /\
   (inf_set_tids (Infer_Tuvar n) = {})`;;

let inf_set_tids_ind = cake_ind "inf_set_tids";;

let inf_set_tids_subset_def = cake_def
  `inf_set_tids_subset (tids:num->bool) t <=> inf_set_tids t SUBSET tids`;;

let typeSystem_t_ind = prove
 (`!P. (!tv. P (Tvar tv)) /\ (!n. P (Tvar_db n)) /\
       (!ts' tn. (!a. MEM a ts' ==> P a) ==> P (Tapp ts' tn))
       ==> !t. P t`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\(skip:num) (ts:t list) (x:t). (P:t->bool) x` deBruijn_subst_ind) THEN
  BETA_TAC THEN ASM_SIMP_TAC[]);;

let TYSYS2AUX_UNIONS_MAP_SUBSET = prove
 (`!(f:A->B->bool) g U l.
     (!a. MEM a l ==> f a SUBSET g a UNION U)
     ==> UNIONS (set_of_list (MAP f l)) SUBSET UNIONS (set_of_list (MAP g l)) UNION U`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

let inf_set_tids_infer_type_subst_SUBSET = prove
 (`!subst (t:t).
     inf_set_tids (infer_type_subst subst t) SUBSET
     set_tids t UNION UNIONS (IMAGE inf_set_tids (set_of_list (MAP SND subst)))`,
  GEN_TAC THEN MATCH_MP_TAC typeSystem_t_ind THEN
  REWRITE_TAC[infer_type_subst_alt; set_tids_def; inf_set_tids_def] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    CASES_ON `ALOOKUP (subst:(mlstring#infer_t)list) tv` THEN
    CASE_REWRITE_TAC[inf_set_tids_def; EMPTY_SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:num->bool) IN t ==> s SUBSET {} UNION UNIONS t`) THEN
    REWRITE_TAC[IN_IMAGE; IN_SET_OF_LIST; MEM_MAP] THEN
    EXISTS_TAC `a:infer_t` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `(tv:mlstring,a:infer_t)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EMPTY_SUBSET];
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
    MATCH_MP_TAC(SET_RULE `(A:num->bool) SUBSET B UNION U
                           ==> tn INSERT A SUBSET (tn INSERT B) UNION U`) THEN
    MATCH_MP_TAC TYSYS2AUX_UNIONS_MAP_SUBSET THEN ASM_REWRITE_TAC[o_THM]]);;

let inf_set_tids_infer_deBruijn_subst_SUBSET = prove
 (`!subst t.
     inf_set_tids (infer_deBruijn_subst subst t) SUBSET
     inf_set_tids t UNION UNIONS (IMAGE inf_set_tids (set_of_list subst))`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_subst_alt; inf_set_tids_def] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[inf_set_tids_def; EMPTY_SUBSET; UNION_EMPTY] THEN
    MATCH_MP_TAC(SET_RULE `(s:num->bool) IN t ==> s SUBSET UNIONS t`) THEN
    REWRITE_TAC[IN_IMAGE; IN_SET_OF_LIST] THEN ASM_MESON_TAC[MEM_EL];
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
    MATCH_MP_TAC(SET_RULE `(A:num->bool) SUBSET B UNION U
                           ==> tn INSERT A SUBSET (tn INSERT B) UNION U`) THEN
    MATCH_MP_TAC TYSYS2AUX_UNIONS_MAP_SUBSET THEN ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[EMPTY_SUBSET]]);;

let inf_set_tids_unconvert = prove
 (`!t. inf_set_tids (unconvert_t t) = set_tids t`,
  MATCH_MP_TAC t_ind THEN
  REWRITE_TAC[unconvert_t_def; inf_set_tids_def; set_tids_def; GSYM MAP_o] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_REWRITE_TAC[]);;

(* all the tids used in a tenv *)

let inf_set_tids_ienv_def = cake_def
  `inf_set_tids_ienv tids (ienv:inf_env) <=>
     nsAll (\i p. match p with (ls,t) -> inf_set_tids_subset tids (unconvert_t t))
       (inf_env_inf_t ienv) /\
     nsAll (\i p. match p with
                    (ls,ts,tid) ->
                      ALL (\t. inf_set_tids_subset tids (unconvert_t t)) ts /\ tid IN tids)
       (inf_env_inf_c ienv) /\
     nsAll (\i p. match p with (n,t) -> inf_set_tids_subset tids t) (inf_env_inf_v ienv)`;;

let inf_set_tids_subst_def = cake_def
  `inf_set_tids_subst tids (subst:(num,infer_t)fmap) <=>
     !t. t IN FRANGE subst ==> inf_set_tids_subset tids t`;;

let prim_tids_def = cake_def
  `prim_tids contain (tids:num->bool) <=>
     ALL (\x. x IN tids <=> contain) (CONS Tlist_num (CONS Tbool_num prim_type_nums))`;;

(* HOL4's set_tids_subset_type_name_subst relies on HOL4's truncating ZIP in  *)
(* type_name_subst (ZIP tvs args at a type application): the HOL Light       *)
(* statement adds check_type_names tenvt t, which gives the equal lengths   *)
(* (its uses have it from type_name_check_subst)                            *)

let TYSYS2AUX_NSALL_TAC =
  FIRST_ASSUM(fun a ->
    if (try fst(dest_const(fst(strip_comb(concl a)))) = "nsAll" with Failure _ -> false)
    then FIRST_ASSUM(fun b -> MP_TAC(MATCH_MP nsLookup_nsAll (CONJ a b)))
    else failwith "TYSYS2AUX_NSALL_TAC") THEN
  BETA_TAC THEN CASE_REWRITE_TAC[];;

let TYSYS2AUX_prim_tids_T = prove
 (`!tids. prim_tids T tids
          ==> Ttup_num IN tids /\ Tfn_num IN tids`,
  REWRITE_TAC[prim_tids_def; prim_type_nums_def; ALL] THEN MESON_TAC[]);;

let set_tids_subset_type_name_subst = prove
 (CASE_TERM `!tenvt t tids.
     prim_tids T tids /\
     nsAll (\i p. match p with (ls,t) -> set_tids_subset tids t) tenvt /\
     check_type_names tenvt t
     ==> set_tids_subset tids (type_name_subst tenvt t)`,
  MATCH_MP_TAC type_name_subst_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[type_name_subst_def; set_tids_subset_def; set_tids_def; EMPTY_SUBSET];
    REWRITE_TAC[type_name_subst_def; typeSystem_Ttup_def; set_tids_subset_def;
                set_tids_def; INSERT_SUBSET; GSYM MAP_o; UNIONS_SUBSET; IN_SET_OF_LIST;
                MEM_MAP; o_THM] THEN
    ASM_SIMP_TAC[TYSYS2AUX_prim_tids_T] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[set_tids_subset_def; check_type_names_def;
                                GSYM ALL_MEM]) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[type_name_subst_def; typeSystem_Tfn_def; set_tids_subset_def;
                set_tids_def; INSERT_SUBSET; UNIONS_SUBSET; set_of_list; MAP;
                IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[TYSYS2AUX_prim_tids_T] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[set_tids_subset_def; check_type_names_def]) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `check_type_names tenvT (Atapp ts tc)` THEN
    REWRITE_TAC[type_name_subst_def; check_type_names_def; LET_DEF; LET_END_DEF] THEN
    CASES_ON `nsLookup (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tc` THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a:mlstring list#t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `t0:t` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC set_tids_subset_type_subst THEN CONJ_TAC THENL
     [MATCH_MP_TAC FEVERY_alist_to_fmap THEN
      SUBGOAL_THEN `LENGTH (tvs:mlstring list) =
                    LENGTH (MAP (type_name_subst tenvT) (ts:ast_t list))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
      REWRITE_TAC[o_DEF] THEN ASM_SIMP_TAC[every_zip_snd; LENGTH_MAP] THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      TYSYS2AUX_NSALL_TAC]]);;

let TYSYS2AUX_FLOOKUP_FEMPTY_FUPDATE_LIST = prove
 (`!(l:(A#B)list) k. FLOOKUP (FEMPTY |++ l) k = ALOOKUP (REVERSE l) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flookup_fupdate_list; FLOOKUP_EMPTY] THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (REVERSE (l:(A#B)list)) k` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

let TYSYS2AUX_t_wfs_FUPDATE_LIST_novars = prove
 (`!s (l:(num#infer_t)list).
     t_wfs s /\ ALL (\p. t_vars (SND p) = {}) l ==> t_wfs (s |++ l)`,
  REWRITE_TAC[t_wfs_eqn] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WF_SUBSET THEN EXISTS_TAC `t_vR (s:(num,infer_t)fmap)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[t_vR_eqn; flookup_fupdate_list] THEN REPEAT GEN_TAC THEN
  CASES_ON `ALOOKUP (REVERSE (l:(num#infer_t)list)) y` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_REVERSE] THEN
  DISCH_TAC THEN UNDISCH_TAC `ALL (\p:num#infer_t. t_vars (SND p) = {}) l` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(y:num,a:infer_t)`) THEN
  ASM_REWRITE_TAC[SND] THEN ASM SET_TAC[]);;

let TYSYS2AUX_gc_flookup = prove
 (`!(s:(num,infer_t)fmap) (ts1:(num#num)list) (ts2:(num#infer_t)list) unc
    (g:num->infer_t) x.
     FINITE unc /\ FEMPTY |++ ts2 = FUN_FMAP g unc
     ==> FLOOKUP (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2) x =
         if x IN unc then SOME (g x)
         else option_CASE (OPTION_MAP Infer_Tvar_db (FLOOKUP (FEMPTY |++ ts1) x))
                (FLOOKUP s x) (\v. SOME v)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[flookup_fupdate_list; MAP_REVERSE; ALOOKUP_MAP; o_THM; FLOOKUP_EMPTY;
              SPTAUX_optcase_lemma] THEN
  REWRITE_TAC[GSYM TYSYS2AUX_FLOOKUP_FEMPTY_FUPDATE_LIST] THEN
  ASM_SIMP_TAC[FLOOKUP_FUN_FMAP] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let TYSYS2AUX_FLOOKUP_FUPDATE_LIST_MEM = prove
 (`!(l:(A#B)list) k v.
     ALL_DISTINCT (MAP FST l) /\ MEM (k,v) l ==> FLOOKUP (FEMPTY |++ l) k = SOME v`,
  REWRITE_TAC[TYSYS2AUX_FLOOKUP_FEMPTY_FUPDATE_LIST] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
  ASM_REWRITE_TAC[MEM_REVERSE; GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE]);;

let TYSYS2AUX_REWRITE_ASM_LHS_TAC tm =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && aconv (lhs(concl th)) tm then REWRITE_TAC[th]
    else failwith "TYSYS2AUX_REWRITE_ASM_LHS_TAC");;

let TYSYS2AUX_EXPAND_DIFF_TAC v =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && rhs c = v &&
       (try fst(dest_const(fst(strip_comb(lhs c)))) = "DIFF" with Failure _ -> false)
    then REWRITE_TAC[SYM th] else failwith "TYSYS2AUX_EXPAND_DIFF_TAC");;

let TYSYS2AUX_DROP_ASM_LHS_TAC tm =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && aconv (lhs(concl th)) tm then ALL_TAC
    else failwith "TYSYS2AUX_DROP_ASM_LHS_TAC");;

let generalise_complete = prove
 (`!n s l tvs (s':(num,num)fmap) ts next_uvar (TC_unit:num) tids.
     generalise_list 0 n FEMPTY (MAP (t_walkstar s) l) = (tvs,s',ts) /\
     t_wfs s /\ check_s 0 (count next_uvar) s /\
     ALL (\t. check_t 0 (count next_uvar) t) l
     ==> ?ec1 last_sub.
           ts = MAP (t_walkstar last_sub) l /\ t_wfs last_sub /\
           sub_completion (tvs + n) next_uvar s ec1 last_sub /\
           (TC_unit IN tids /\ inf_set_tids_subst tids s
            ==> inf_set_tids_subst tids last_sub)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP generalise_subst_empty) THEN
  SUBGOAL_THEN `DISJOINT (FDOM (s:(num,infer_t)fmap)) (FDOM (s':(num,num)fmap))` ASSUME_TAC THENL
   [TYSYS2AUX_REWRITE_ASM_LHS_TAC `FDOM (s':(num,num)fmap)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM; IN_UNIONS;
                IN_SET_OF_LIST; MEM_MAP] THEN
    ASM_MESON_TAC[t_walkstar_vars_notin]; ALL_TAC] THEN
  TYSYS2AUX_DROP_ASM_LHS_TAC `FDOM (s':(num,num)fmap)` THEN
  MP_TAC(ISPEC `s':(num,num)fmap` fmap_to_list) THEN
  DISCH_THEN(X_CHOOSE_THEN `ts1:(num#num)list` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `unc = count next_uvar DIFF
                    (FDOM (s:(num,infer_t)fmap) UNION FDOM (s':(num,num)fmap))` THEN
  SUBGOAL_THEN `FINITE (unc:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "unc" THEN MATCH_MP_TAC FINITE_DIFF THEN REWRITE_TAC[FINITE_COUNT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `FUN_FMAP (\x:num. Infer_Tapp [] TC_unit) unc` fmap_to_list) THEN
  DISCH_THEN(X_CHOOSE_THEN `ts2:(num#infer_t)list` (STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN `FDOM (FEMPTY |++ (ts2:(num#infer_t)list)) = unc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FDOM_FMAP]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\p. SND p = Infer_Tapp [] TC_unit /\ FST p IN unc)
                    (ts2:(num#infer_t)list)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `v:infer_t`] THEN DISCH_TAC THEN REWRITE_TAC[FST; SND] THEN
    MP_TAC(ISPECL [`ts2:(num#infer_t)list`; `k:num`; `v:infer_t`]
             TYSYS2AUX_FLOOKUP_FUPDATE_LIST_MEM) THEN
    ASM_SIMP_TAC[FLOOKUP_FUN_FMAP] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; injectivity "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TYSYS2AUX_t_wfs_FUPDATE_LIST_novars THEN ASM_REWRITE_TAC[ALL_MAP] THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; t_vars_eqn];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t_wfs ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TYSYS2AUX_t_wfs_FUPDATE_LIST_novars THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `TC_unit:num` (concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    SIMP_TAC[t_vars_eqn; MAP; set_of_list; UNIONS_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(num,infer_t)fmap`; `ts1:(num#num)list`; `ts2:(num#infer_t)list`;
                 `unc:num->bool`; `\x:num. Infer_Tapp [] TC_unit`] TYSYS2AUX_gc_flookup) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `set_of_list (MAP FST (ts1:(num#num)list)) = FDOM (s':(num,num)fmap)`
    ASSUME_TAC THENL
   [TYSYS2AUX_REWRITE_ASM_LHS_TAC `s':(num,num)fmap` THEN
    REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `set_of_list (MAP FST (ts2:(num#infer_t)list)) = unc` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `FDOM (FEMPTY |++ (ts2:(num#infer_t)list))` then MP_TAC th
       else failwith "") THEN
    REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) (ts1:(num#num)list)) =
                FDOM (s':(num,num)fmap)` ASSUME_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE_LIST; map_fst; FDOM_FEMPTY; UNION_EMPTY] THEN
    TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts1:(num#num)list))`;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FDOM ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2) =
    FDOM s UNION FDOM (s':(num,num)fmap) UNION unc` ASSUME_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE_LIST; map_fst; GSYM UNION_ASSOC] THEN
    TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts1:(num#num)list))` THEN
    TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts2:(num#infer_t)list))`;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x v. FLOOKUP ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2) x =
          SOME v
          ==> (x IN unc /\ v = Infer_Tapp [] TC_unit) \/
              (?tv. FLOOKUP (s':(num,num)fmap) x = SOME tv /\ v = Infer_Tvar_db tv) \/
              FLOOKUP s x = SOME v` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        (let c = snd(dest_forall(concl th)) in is_eq c &&
         (try fst(dest_const(fst(strip_comb(lhs c)))) = "FLOOKUP" with Failure _ -> false))
      then REWRITE_TAC[th] else failwith "") THEN
    TYSYS2AUX_REWRITE_ASM_LHS_TAC `s':(num,num)fmap` THEN
    COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"] THENL
     [MESON_TAC[]; ALL_TAC] THEN
    CASES_ON `FLOOKUP (FEMPTY |++ (ts1:(num#num)list)) x` THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_CASE; injectivity "option"; option_DISTINCT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND (MAP (\(uv,tv). (Infer_Tuvar uv,Infer_Tvar_db tv)) (ts1:(num#num)list))
                     (MAP (\(uv,t). (Infer_Tuvar uv,t)) (ts2:(num#infer_t)list))` THEN
  EXISTS_TAC `(s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
    X_GEN_TAC `e:infer_t` THEN DISCH_TAC THEN
    MP_TAC(SPEC `s:(num,infer_t)fmap` generalise_complete_lemma5) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`e:infer_t`; `ts1:(num#num)list`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        TYSYS2AUX_REWRITE_ASM_LHS_TAC
          `FDOM (FEMPTY |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) (ts1:(num#num)list))` THEN
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)] THEN
    MP_TAC(SPEC `(s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1`
             no_vars_extend_subst) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`e:infer_t`; `ts2:(num#infer_t)list`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[FDOM_FUPDATE_LIST; map_fst; FDOM_FEMPTY; UNION_EMPTY] THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts1:(num#num)list))` THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts2:(num#infer_t)list))` THEN
        TYSYS2AUX_EXPAND_DIFF_TAC `unc:num->bool` THEN SET_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "infer_subst"
           with Failure _ -> false))) THEN
        UNDISCH_TAC `UNIONS (set_of_list (MAP t_vars (ts:infer_t list))) = {}` THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `ts:infer_t list` THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `s':(num,num)fmap` THEN
        REWRITE_TAC[EMPTY_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]];
      DISCH_THEN(ACCEPT_TAC o SYM)];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[sub_completion_def] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `APPEND (MAP (\(uv,tv). (Infer_Tuvar uv,Infer_Tvar_db tv)) (ts1:(num#num)list))
               (MAP (\(uv,t). (Infer_Tuvar uv,t)) (ts2:(num#infer_t)list)) =
        MAP (\(uv,t). (Infer_Tuvar uv,t))
            (APPEND (MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1) ts2)` SUBST1_TAC THENL
       [REWRITE_TAC[MAP_APPEND; GSYM MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM FUPDATE_LIST_APPEND] THEN
      MATCH_MP_TAC generalise_complete_lemma2 THEN EXISTS_TAC `TC_unit:num` THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[MAP_APPEND; map_fst; ALL_DISTINCT_APPEND] THEN
        REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts1:(num#num)list))` THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts2:(num#infer_t)list))` THEN
        TYSYS2AUX_EXPAND_DIFF_TAC `unc:num->bool` THEN SET_TAC[];
        REWRITE_TAC[MAP_APPEND; ALL_APPEND; GSYM MAP_o; ALL_MAP] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN MESON_TAC[];
          FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `TC_unit:num` (concl th) &&
            (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
          MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN MESON_TAC[]];
        REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY; MAP_APPEND;
                    SET_OF_LIST_APPEND; map_fst] THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts1:(num#num)list))` THEN
        TYSYS2AUX_REWRITE_ASM_LHS_TAC `set_of_list (MAP FST (ts2:(num#infer_t)list))` THEN
        TYSYS2AUX_EXPAND_DIFF_TAC `unc:num->bool` THEN
        UNDISCH_TAC `DISJOINT (FDOM (s:(num,infer_t)fmap)) (FDOM (s':(num,num)fmap))` THEN
        SET_TAC[]];
      TYSYS2AUX_REWRITE_ASM_LHS_TAC
       `FDOM ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2)` THEN
      TYSYS2AUX_EXPAND_DIFF_TAC `unc:num->bool` THEN SET_TAC[];
      SUBGOAL_THEN `count next_uvar SUBSET
                    FDOM ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2)`
        ASSUME_TAC THENL
       [TYSYS2AUX_REWRITE_ASM_LHS_TAC
         `FDOM ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2)` THEN
        TYSYS2AUX_EXPAND_DIFF_TAC `unc:num->bool` THEN SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `uv:num` THEN DISCH_TAC THEN MATCH_MP_TAC t_walkstar_check THEN
      REWRITE_TAC[UNION_EMPTY] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC;
        REWRITE_TAC[check_t_def] THEN FIRST_ASSUM ACCEPT_TAC] THEN
      REWRITE_TAC[check_s_def] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
      (SUBGOAL_THEN
        `FLOOKUP ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2) x =
         SOME (FAPPLY (s |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2) x)`
        ASSUME_TAC THENL
        [REWRITE_TAC[flookup_thm] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
      POP_ASSUM (fun th -> FIRST_ASSUM(fun lem ->
          if is_forall(concl lem) &&
             (try fst(dest_const(fst(strip_comb(lhs(fst(dest_imp(snd(strip_forall(concl lem))))))))) = "FLOOKUP"
              with Failure _ -> false)
          then STRIP_ASSUME_TAC(MATCH_MP lem th) else failwith "")) THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `Infer_Tapp [] TC_unit`)) THEN
        REWRITE_TAC[check_t_def; ALL];
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          (try fst(dest_const(fst(strip_comb(rhs(concl th))))) = "Infer_Tvar_db"
           with Failure _ -> false))) THEN
        REWRITE_TAC[check_t_def] THEN ASM_MESON_TAC[flookup_thm];
        SUBGOAL_THEN `check_t 0 (count next_uvar) (FAPPLY (s:(num,infer_t)fmap) x)` ASSUME_TAC THENL
         [UNDISCH_TAC `check_s 0 (count next_uvar) (s:(num,infer_t)fmap)` THEN
          REWRITE_TAC[check_s_def] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_MESON_TAC[flookup_thm];
          ALL_TAC] THEN
        SUBGOAL_THEN `FAPPLY ((s:(num,infer_t)fmap) |++ MAP (\(uv,tv). (uv,Infer_Tvar_db tv)) ts1 |++ ts2) x =
                      FAPPLY s x` SUBST1_TAC THENL
         [ASM_MESON_TAC[flookup_thm; injectivity "option"]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `tvs + n:num` o MATCH_MP (CONJUNCT1 check_t_more2)) THEN
        REWRITE_TAC[ADD_CLAUSES] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 check_t_more5)) THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    STRIP_TAC THEN REWRITE_TAC[inf_set_tids_subst_def; IN_FRANGE_FLOOKUP] THEN
    X_GEN_TAC `t:infer_t` THEN DISCH_THEN(X_CHOOSE_THEN `k:num` (fun th -> FIRST_ASSUM(fun lem ->
          if is_forall(concl lem) &&
             (try fst(dest_const(fst(strip_comb(lhs(fst(dest_imp(snd(strip_forall(concl lem))))))))) = "FLOOKUP"
              with Failure _ -> false)
          then STRIP_ASSUME_TAC(MATCH_MP lem th) else failwith ""))) THEN
    ASM_REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_def; MAP; set_of_list; UNIONS_0;
                    EMPTY_SUBSET] THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `inf_set_tids_subst tids (s:(num,infer_t)fmap)` THEN
      REWRITE_TAC[inf_set_tids_subst_def; IN_FRANGE_FLOOKUP; inf_set_tids_subset_def] THEN
      ASM_MESON_TAC[]]]);;

let init_infer_state_wfs = prove
 (`!st. t_wfs (infer_st_subst (init_infer_state st)) /\
        check_s 0 {} (infer_st_subst (init_infer_state st))`,
  REWRITE_TAC[init_infer_state_def; infer_st_rewrs; check_s_def; FDOM_FEMPTY;
              NOT_IN_EMPTY; t_wfs_def; o_f_FEMPTY; wfs_FEMPTY]);;

let init_infer_state_next_uvar = prove
 (`!st. infer_st_next_uvar (init_infer_state st) = 0`,
  REWRITE_TAC[init_infer_state_def; infer_st_rewrs]);;

let init_infer_state_subst = prove
 (`!st. infer_st_subst (init_infer_state st) = FEMPTY`,
  REWRITE_TAC[init_infer_state_def; infer_st_rewrs]);;

let t_wfs_FEMPTY = prove
 (`t_wfs FEMPTY`,
  REWRITE_TAC[t_wfs_def; o_f_FEMPTY; wfs_FEMPTY]);;

let t_wfs_init_infer_state = prove
 (`!s. t_wfs (infer_st_subst (init_infer_state s))`,
  REWRITE_TAC[init_infer_state_subst; t_wfs_FEMPTY]);;

let _ = cake_add_simps [init_infer_state_next_uvar; init_infer_state_subst; t_wfs_FEMPTY;
                        t_wfs_init_infer_state];;

(* HOL4's let_tac (an ML tactic used in infer_d_check) is not ported *)

let eta2_thm = prove
 (`!(f:A->B->C->D) a b. (\x. f a b x) = f a b`,
  REWRITE_TAC[ETA_AX]);;

let check_env_letrec_lem2 = prove
 (CASE_TERM `!funs:(mlstring#mlstring#exp)list.
     nsAll (\x p. match p with (tvs,t) -> check_t tvs (count (LENGTH funs)) t)
       (alist_to_ns
          (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))))
        :(mlstring,mlstring,num#infer_t)namespace)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`LENGTH (funs:(mlstring#mlstring#exp)list)`;
                `funs:(mlstring#mlstring#exp)list`; `0`] check_env_letrec_lem) THEN
  REWRITE_TAC[ADD_CLAUSES; LE_REFL]);;

let ienv_ok_extend_dec_ienv = prove
 (`!e1 e2 n. ienv_ok n e1 /\ ienv_ok n e2 ==> ienv_ok n (extend_dec_ienv e1 e2)`,
  REWRITE_TAC[ienv_ok_def; ienv_val_ok_def; tenv_ctor_ok_def; tenv_abbrev_ok_def;
              extend_dec_ienv_def; inf_env_INFO.ri_accessors] THEN
  MESON_TAC[nsAll_nsAppend]);;

let TYSYS2AUX_generalise_check = prove
 (`!s l nu ntvs (s':(num,num)fmap) ts'.
     t_wfs s /\ check_s 0 (count nu) s /\ ALL (check_t 0 (count nu)) l /\
     generalise_list 0 0 FEMPTY (MAP (t_walkstar s) l) = (ntvs,s',ts')
     ==> ALL (check_t ntvs {}) ts'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`0`; `s:(num,infer_t)fmap`; `l:infer_t list`; `ntvs:num`;
                `s':(num,num)fmap`; `ts':infer_t list`; `nu:num`; `0`; `{}:num->bool`]
           (REWRITE_RULE[ETA_AX] generalise_complete)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; sub_completion_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ALL_MAP] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
  MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC `t:infer_t` THEN REWRITE_TAC[o_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC(CONJUNCT1 check_t_walkstar) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`t:infer_t`; `0`; `count nu`] (CONJUNCT1 check_t_more2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `ntvs:num`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 check_t_more5)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let TYSYS2AUX_ienv_val_ok_alist_zip = prove
 (`!(xs:mlstring list) ts n.
     LENGTH xs = LENGTH ts /\ ALL (check_t n {}) ts
     ==> ienv_val_ok {} (alist_to_ns (ZIP xs (MAP (\t. (n,t)) ts)))`,
  REWRITE_TAC[ienv_val_ok_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ts:infer_t list`,`ts:infer_t list`) THEN
  SPEC_TAC(`xs:mlstring list`,`xs:mlstring list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; ALL] THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_ienv_val_ok_alist_map2 = prove
 (CASE_TERM `!(funs:(mlstring#mlstring#exp)list) ts n.
     LENGTH funs = LENGTH ts /\ ALL (check_t n {}) ts
     ==> ienv_val_ok {}
           (alist_to_ns (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(n,t))) funs ts))`,
  REWRITE_TAC[ienv_val_ok_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ts:infer_t list`,`ts:infer_t list`) THEN
  SPEC_TAC(`funs:(mlstring#mlstring#exp)list`,`funs:(mlstring#mlstring#exp)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; ALL] THEN
  X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `e:exp`
    SUBST_ALL_TAC)) (ISPEC `h:mlstring#mlstring#exp` BASICAUX_TUPLE3) THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_init_facts = prove
 (`!st1 ienv.
     ienv_ok {} ienv
     ==> ienv_ok (count (infer_st_next_uvar (init_infer_state st1))) ienv /\
         t_wfs (infer_st_subst (init_infer_state st1)) /\
         check_s 0 (count (infer_st_next_uvar (init_infer_state st1)))
           (infer_st_subst (init_infer_state st1))`,
  SIMP_TAC[init_infer_state_next_uvar; COUNT_ZERO; init_infer_state_wfs]);;

let TYSYS2AUX_dlet_facts = prove
 (`!l ienv e p st1 t1 st4 t2 env' st5 s.
     ienv_ok {} ienv /\
     infer_e l ienv e (init_infer_state st1) = (M_success t1,st4) /\
     infer_p l ienv p st4 = (M_success (t2,env'),st5) /\
     t_unify (infer_st_subst st5) t1 t2 = SOME s
     ==> t_wfs s /\ check_s 0 (count (infer_st_next_uvar st5)) s /\
         ALL (check_t 0 (count (infer_st_next_uvar st5))) (MAP SND env')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `st1:infer_st` o MATCH_MP
    (ONCE_REWRITE_RULE[SWAP_FORALL_THM] TYSYS2AUX_init_facts)) THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st4)` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `check_s 0 (count (infer_st_next_uvar st4)) (infer_st_subst st4)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_s) THEN
    MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state st1`; `t1:infer_t`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `check_t 0 (count (infer_st_next_uvar st4)) t1` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 infer_e_check_t) THEN
    MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv:inf_env`; `e:exp`;
                          `init_infer_state st1`] THEN
    ASM_MESON_TAC[ienv_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st5) /\
                check_s 0 (count (infer_st_next_uvar st5)) (infer_st_subst st5) /\
                check_t 0 (count (infer_st_next_uvar st5)) t2 /\
                ALL (check_t 0 (count (infer_st_next_uvar st5))) (MAP SND (env':(mlstring#infer_t)list)) /\
                infer_st_next_uvar st4 <= infer_st_next_uvar st5`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[infer_p_wfs];
      MATCH_MP_TAC(CONJUNCT1 infer_p_check_s) THEN
      MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv:inf_env`; `p:pat`; `st4:infer_st`;
                            `t2:infer_t`; `env':(mlstring#infer_t)list`] THEN
      ASM_MESON_TAC[ienv_ok_def];
      ASM_MESON_TAC[infer_p_check_t];
      ASM_MESON_TAC[REWRITE_RULE[every_shim; ETA_AX] infer_p_check_t];
      ASM_MESON_TAC[infer_p_next_uvar_mono]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[t_unify_wfs]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC t_unify_check_s THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st5`; `t1:infer_t`; `t2:infer_t`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[TYSYS2AUX_check_t_mono]);;

let TYSYS2AUX_count_list_check = prove
 (`!k m. k <= m ==> ALL (check_t 0 (count m)) (MAP (\n. Infer_Tuvar n) (COUNT_LIST k))`,
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; MEM_COUNT_LIST; o_THM; check_t_def; IN_COUNT] THEN
  ARITH_TAC);;

let TYSYS2AUX_ALL_ZIP_pair = prove
 (`!(l1:A list) l2 P.
     LENGTH l1 = LENGTH l2 /\ ALL P l1 /\ ALL P l2
     ==> ALL (\(t1,t2). P t1 /\ P t2) (ZIP l1 l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; ALL] THEN
  ASM_MESON_TAC[]);;

let TYSYS2AUX_dletrec_facts = prove
 (CASE_TERM `!l ienv (funs:(mlstring#mlstring#exp)list) st0 ts st7 st2.
     ienv_ok {} ienv /\
     infer_funs l
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                         (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv)
       funs st0 = (M_success ts,st7) /\
     infer_st_next_uvar st0 = LENGTH funs /\ infer_st_subst st0 = FEMPTY /\
     LENGTH funs = LENGTH ts /\
     infer_st_next_uvar st7 = infer_st_next_uvar st2 /\
     pure_add_constraints (infer_st_subst st7)
       (ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))) ts) (infer_st_subst st2)
     ==> t_wfs (infer_st_subst st2) /\
         check_s 0 (count (infer_st_next_uvar st2)) (infer_st_subst st2) /\
         ALL (check_t 0 (count (infer_st_next_uvar st2)))
           (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (CASE_TERM `ienv' = inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar)))
                         (funs:(mlstring#mlstring#exp)list)
                         (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv`) THEN
  SUBGOAL_THEN `ienv_ok (count (infer_st_next_uvar st0)) ienv'` ASSUME_TAC THENL
   [EXPAND_TAC "ienv'" THEN
    TYSYS2AUX_REWRITE_ASM_LHS_TAC `infer_st_next_uvar st0` THEN
    UNDISCH_TAC `ienv_ok {} ienv` THEN
    REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accfupds; K_THM] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[ienv_val_ok_def] THEN
    MATCH_MP_TAC nsAll_nsAppend THEN REWRITE_TAC[check_env_letrec_lem2] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ienv_val_ok_def; GSYM COUNT_ZERO]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP check_env_more) THEN REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st0) /\
                check_s 0 (count (infer_st_next_uvar st0)) (infer_st_subst st0)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[t_wfs_FEMPTY; check_s_def; FDOM_FEMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st7) /\
                check_s 0 (count (infer_st_next_uvar st7)) (infer_st_subst st7) /\
                ALL (check_t 0 (count (infer_st_next_uvar st7))) ts /\
                infer_st_next_uvar st0 <= infer_st_next_uvar st7`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[infer_e_wfs];
      MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_s))) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv':inf_env`;
                            `funs:(mlstring#mlstring#exp)list`; `st0:infer_st`;
                            `ts:infer_t list`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_check_t))) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`l:loc_err_info`; `ienv':inf_env`;
                            `funs:(mlstring#mlstring#exp)list`; `st0:infer_st`] THEN
      ASM_MESON_TAC[ienv_ok_def];
      ASM_MESON_TAC[infer_e_next_uvar_mono]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (check_t 0 (count (infer_st_next_uvar st7)))
                    (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TYSYS2AUX_count_list_check THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `infer_st_next_uvar st2`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MATCH_MP_TAC pure_add_constraints_check_s THEN
  MAP_EVERY EXISTS_TAC
   [`infer_st_subst st7`;
    `ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))
         (ts:infer_t list)`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC TYSYS2AUX_ALL_ZIP_pair THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let TYSYS2AUX_asm_head asl nm =
  snd(find (fun (_,th) ->
    let c = concl th in
    let t = if is_eq c then lhs c else c in
    (try fst(dest_const(fst(strip_comb t))) = nm with Failure _ -> false)) asl);;

let TYSYS2AUX_DLET_TAC : tactic = fun (asl,w as g) ->
  let a1 = TYSYS2AUX_asm_head asl "ienv_ok" and a2 = TYSYS2AUX_asm_head asl "infer_e"
  and a3 = TYSYS2AUX_asm_head asl "infer_p" and a4 = TYSYS2AUX_asm_head asl "t_unify"
  and a5 = TYSYS2AUX_asm_head asl "generalise_list" in
  let f = MATCH_MP TYSYS2AUX_dlet_facts (end_itlist CONJ [a1;a2;a3;a4]) in
  let gc = MATCH_MP TYSYS2AUX_generalise_check
             (REWRITE_RULE[GSYM CONJ_ASSOC] (CONJ f a5)) in
  let ln = REWRITE_RULE[LENGTH_MAP] (MATCH_MP generalise_list_length a5) in
  (REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accessors; tenv_ctor_ok_def;
               tenv_abbrev_ok_def; nsAll_nsEmpty] THEN
   MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_alist_zip THEN
   REWRITE_TAC[LENGTH_MAP; ln; gc]) g;;

let TYSYS2AUX_DLETREC_TAC : tactic = fun (asl,w as g) ->
  let a1 = TYSYS2AUX_asm_head asl "ienv_ok" and a2 = TYSYS2AUX_asm_head asl "infer_funs"
  and a3 = TYSYS2AUX_asm_head asl "LENGTH" and a4 = TYSYS2AUX_asm_head asl "infer_st_next_uvar"
  and a5 = TYSYS2AUX_asm_head asl "pure_add_constraints"
  and a6 = TYSYS2AUX_asm_head asl "generalise_list" in
  let len = REWRITE_RULE[LENGTH_MAP; LENGTH_COUNT_LIST] a3 in
  let st0 = rand(lhs(concl a2)) in
  let st0n = EQT_ELIM(REWRITE_CONV[infer_st_rewrs; init_infer_state_subst]
               (mk_eq(mk_comb(`infer_st_next_uvar`,st0), lhs(concl len)))) in
  let st0s = EQT_ELIM(REWRITE_CONV[infer_st_rewrs; init_infer_state_subst]
               (mk_eq(mk_comb(`infer_st_subst`,st0), `FEMPTY:(num,infer_t)fmap`))) in
  let f = MATCH_MP TYSYS2AUX_dletrec_facts (end_itlist CONJ [a1;a2;st0n;st0s;len;a4;a5]) in
  let gc = MATCH_MP TYSYS2AUX_generalise_check
             (REWRITE_RULE[GSYM CONJ_ASSOC] (CONJ f a6)) in
  let ln = REWRITE_RULE[LENGTH_MAP; LENGTH_COUNT_LIST] (MATCH_MP generalise_list_length a6) in
  (REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accessors; tenv_ctor_ok_def;
               tenv_abbrev_ok_def; nsAll_nsEmpty] THEN
   MATCH_MP_TAC TYSYS2AUX_ienv_val_ok_alist_map2 THEN
   REWRITE_TAC[ln; gc]) g;;

let infer_d_check = prove
 (`(!ienv d st1 st2 ienv'.
      infer_d ienv d st1 = (M_success ienv',st2) /\ ienv_ok {} ienv ==> ienv_ok {} ienv') /\
   (!ienv ds st1 st2 ienv'.
      infer_ds ienv ds st1 = (M_success ienv',st2) /\ ienv_ok {} ienv ==> ienv_ok {} ienv')`,
  MATCH_MP_TAC infer_d_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[infer_d_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE;
              TYSYS2AUX_ignore_bind_eq; init_state_def] THEN
  REPEAT STRIP_TAC THEN TYSYS2AUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[init_infer_state_next_uvar; infer_st_rewrs; ADD_CLAUSES]) THENL
   [TYSYS2AUX_DLET_TAC; TYSYS2AUX_DLET_TAC; TYSYS2AUX_DLETREC_TAC;
    (* Dtype *)
    RULE_ASSUM_TAC(REWRITE_RULE[ienv_ok_def]) THEN
    REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accessors; ienv_val_ok_def; nsAll_nsEmpty;
                TPROPSAUX_tenv_abbrev_ok_tdefs] THEN
    MATCH_MP_TAC check_ctor_tenv_ok THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "n_fresh_id"
         with Failure _ -> false))) THEN
      REWRITE_TAC[n_fresh_id_def; PAIR_EQ; injectivity "exc"] THEN
      MESON_TAC[LENGTH_LIST_OF_SEQ];
      REWRITE_TAC[tenv_abbrev_ok_def] THEN MATCH_MP_TAC nsAll_nsAppend THEN
      RULE_ASSUM_TAC(REWRITE_RULE[tenv_abbrev_ok_def]) THEN
      ASM_REWRITE_TAC[REWRITE_RULE[tenv_abbrev_ok_def] TPROPSAUX_tenv_abbrev_ok_tdefs]];
    (* Dtabbrev *)
    RULE_ASSUM_TAC(REWRITE_RULE[ienv_ok_def]) THEN
    REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accessors; ienv_val_ok_def; tenv_ctor_ok_def;
                tenv_abbrev_ok_def; nsAll_nsEmpty; nsAll_nsSing] THEN
    CASE_REWRITE_TAC[] THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
    ASM_REWRITE_TAC[];
    (* Dexn *)
    RULE_ASSUM_TAC(REWRITE_RULE[ienv_ok_def]) THEN
    REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accessors; ienv_val_ok_def; tenv_ctor_ok_def;
                tenv_abbrev_ok_def; nsAll_nsEmpty; nsAll_nsSing] THEN
    CASE_REWRITE_TAC[ALL_MAP; o_DEF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    ASM_MESON_TAC[check_freevars_type_name_subst];
    (* Dmod *)
    SUBGOAL_THEN `ienv_ok {} v'` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ienv_ok_def; lift_ienv_def; inf_env_INFO.ri_accessors; ienv_val_ok_def;
                tenv_ctor_ok_def; tenv_abbrev_ok_def; nsAll_nsLift] THEN
    BETA_TAC THEN REWRITE_TAC[];
    (* Dlocal *)
    ASM_MESON_TAC[ienv_ok_extend_dec_ienv];
    (* [] *)
    REWRITE_TAC[ienv_ok_def; inf_env_INFO.ri_accessors; ienv_val_ok_def; tenv_ctor_ok_def;
                tenv_abbrev_ok_def; nsAll_nsEmpty];
    (* CONS *)
    ASM_MESON_TAC[ienv_ok_extend_dec_ienv]]);;

let TYSYS2AUX_constrain_op_next_id = prove
 (`!l op ts st v st'.
     constrain_op l op ts st = (M_success v,st')
     ==> infer_st_next_id st' = infer_st_next_id st`,
  GEN_TAC THEN X_GEN_TAC `op:op` THEN CASES_ON `op:op` THEN
  REWRITE_TAC[constrain_op_success; add_constraints_success] THEN
  REPEAT STRIP_TAC THEN GVS[infer_st_INFO.ri_accfupds]);;

let infer_p_next_id_const = prove
 (`(!l cenv p st t env st'.
      infer_p l cenv p st = (M_success (t,env),st')
      ==> infer_st_next_id st = infer_st_next_id st') /\
   (!l cenv ps st ts env st'.
      infer_ps l cenv ps st = (M_success (ts,env),st')
      ==> infer_st_next_id st = infer_st_next_id st')`,
  MP_TAC(ISPEC `\st st'. infer_st_next_id st = infer_st_next_id st'` TYSYS2AUX_infer_p_pres) THEN
  REWRITE_TAC[TYSYS2AUX_pres_def] THEN BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fresh_uvar_success; n_fresh_uvar_success; add_constraint_success;
                add_constraints_success] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds];
    MESON_TAC[]]);;

let infer_e_next_id_const = prove
 (`(!l ienv e st st' t.
      infer_e l ienv e st = (M_success t,st')
      ==> infer_st_next_id st = infer_st_next_id st') /\
   (!l ienv es st st' ts.
      infer_es l ienv es st = (M_success ts,st')
      ==> infer_st_next_id st = infer_st_next_id st') /\
   (!l ienv pes t1 t2 st st'.
      infer_pes l ienv pes t1 t2 st = (M_success one,st')
      ==> infer_st_next_id st = infer_st_next_id st') /\
   (!l ienv funs st st' ts.
      infer_funs l ienv funs st = (M_success ts,st')
      ==> infer_st_next_id st = infer_st_next_id st')`,
  MP_TAC(ISPEC `\st st'. infer_st_next_id st = infer_st_next_id st'` TYSYS2AUX_infer_e_pres) THEN
  REWRITE_TAC[TYSYS2AUX_pres_def] THEN BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fresh_uvar_success; n_fresh_uvar_success; add_constraint_success;
                add_constraints_success] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds] THEN
    ASM_MESON_TAC[TYSYS2AUX_constrain_op_next_id];
    MESON_TAC[]]);;

let infer_d_next_id_mono = prove
 (`(!d ienv st t st'.
      infer_d ienv d st = (M_success t,st')
      ==> infer_st_next_id st <= infer_st_next_id st') /\
   (!ds ienv st ts st'.
      infer_ds ienv ds st = (M_success ts,st')
      ==> infer_st_next_id st <= infer_st_next_id st')`,
  SUBGOAL_THEN
   `(!ienv d st t st'.
      infer_d ienv d st = (M_success t,st')
      ==> infer_st_next_id st <= infer_st_next_id st') /\
    (!ienv ds st ts st'.
      infer_ds ienv ds st = (M_success ts,st')
      ==> infer_st_next_id st <= infer_st_next_id st')`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC infer_d_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[infer_d_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE;
              TYSYS2AUX_ignore_bind_eq; init_state_def] THEN
  REPEAT STRIP_TAC THEN TYSYS2AUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[infer_st_INFO.ri_accfupds; init_infer_state_def; K_THM]) THEN
  REWRITE_TAC[infer_st_INFO.ri_accfupds; init_infer_state_def; K_THM] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "n_fresh_id"
         with Failure _ -> false))) THEN
      REWRITE_TAC[n_fresh_id_def; PAIR_EQ] THEN STRIP_TAC THEN
      TYSYS2AUX_SUBST_VARS_TAC THEN
      REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM]) THEN
  ASM_MESON_TAC[infer_e_next_id_const; infer_p_next_id_const; LE_REFL; LE_TRANS; LE_ADD;
                infer_st_INFO.ri_accfupds]);;

let count_list_one = prove
 (`COUNT_LIST 1 = [0]`,
  REWRITE_TAC[num_CONV `1`; COUNT_LIST_DEF; MAP]);;

let check_freevars_more_append = prove
 (`(!t x fvs1 fvs2.
      check_freevars x fvs1 t
      ==> check_freevars x (APPEND fvs2 fvs1) t /\ check_freevars x (APPEND fvs1 fvs2) t) /\
   (!ts x fvs1 fvs2.
      ALL (check_freevars x fvs1) ts
      ==> ALL (check_freevars x (APPEND fvs2 fvs1)) ts /\
          ALL (check_freevars x (APPEND fvs1 fvs2)) ts)`,
  MATCH_MP_TAC t_INDUCT THEN REWRITE_TAC[check_freevars_def; ALL; MEM_APPEND] THEN
  MESON_TAC[]);;

let check_freevars_more = prove
 (`!a b c. check_freevars a b c
           ==> !b'. set_of_list b SUBSET set_of_list b' ==> check_freevars a b' c`,
  MATCH_MP_TAC check_freevars_ind THEN
  REWRITE_TAC[check_freevars_def; SUBSET; IN_SET_OF_LIST; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let check_t_infer_type_subst_dbs = prove
 (`!m w t n u ls.
     check_freevars m w t /\ m + LENGTH ls <= n /\ (ls = [] ==> 0 < m)
     ==> check_t n u
           (infer_type_subst (ZIP ls (MAP Infer_Tvar_db (COUNT_LIST (LENGTH ls)))) t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  REWRITE_TAC[check_freevars_def; infer_type_subst_alt; check_t_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN
    CASES_ON `ALOOKUP (ZIP (ls:mlstring list) (MAP Infer_Tvar_db (COUNT_LIST (LENGTH ls)))) tv` THEN
    CASE_REWRITE_TAC[check_t_def] THENL
     [ASM_CASES_TAC `ls:mlstring list = []` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
      SIMP_TAC[MEM_ZIP; LENGTH_MAP; LENGTH_COUNT_LIST] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[EL_MAP; LENGTH_COUNT_LIST; EL_COUNT_LIST; check_t_def] THEN
      ASM_ARITH_TAC];
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN MESON_TAC[];
    ARITH_TAC]);;

let nub_eq_nil = prove
 (`!ls:A list. nub ls = [] <=> ls = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[nub_DEF; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  ASM_MESON_TAC[MEM]);;

let ienv_ok_lift = prove
 (`!mn ienv n. ienv_ok n ienv ==> ienv_ok n (lift_ienv mn ienv)`,
  REWRITE_TAC[lift_ienv_def; ienv_ok_def; inf_env_INFO.ri_accessors; ienv_val_ok_def;
              tenv_ctor_ok_def; tenv_abbrev_ok_def; nsAll_nsLift] THEN
  BETA_TAC THEN REWRITE_TAC[]);;

let sub_completion_wfs = prove
 (`!n uvars s1 ts s2. t_wfs s1 /\ sub_completion n uvars s1 ts s2 ==> t_wfs s2`,
  REWRITE_TAC[sub_completion_def] THEN MESON_TAC[pure_add_constraints_wfs]);;

let infer_deBruijn_subst_id = prove
 (`(!t. infer_deBruijn_subst [] t = t) /\ (!ts. MAP (infer_deBruijn_subst []) ts = ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[infer_deBruijn_subst_alt; LENGTH; LT; SUB_0; MAP] THEN
  SIMP_TAC[]);;

let deBruijn_subst_nothing = prove
 (`(!t. deBruijn_subst 0 [] t = t) /\ (!ts. MAP (deBruijn_subst 0 []) ts = ts)`,
  MATCH_MP_TAC t_INDUCT THEN
  REWRITE_TAC[deBruijn_subst_def; LENGTH; LT; SUB_0; ADD_CLAUSES; MAP] THEN
  SIMP_TAC[]);;

(* HOL4's GENLIST is HOL Light's list_of_seq *)

let infer_deBruijn_subst_id2 = prove
 (`!tvs.
   (!t. check_t tvs {} t ==> infer_deBruijn_subst (list_of_seq Infer_Tvar_db tvs) t = t) /\
   (!ts. ALL (check_t tvs {}) ts
         ==> MAP (infer_deBruijn_subst (list_of_seq Infer_Tvar_db tvs)) ts = ts)`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; infer_deBruijn_subst_alt; LENGTH_LIST_OF_SEQ; ALL; MAP;
              NOT_IN_EMPTY] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; injectivity "infer_t"; CONS_11]);;

let infer_deBruijn_subst_uncheck = prove
 (`!s t max_tvs uvs.
     check_t max_tvs uvs (infer_deBruijn_subst s t) ==> check_t (max_tvs + LENGTH s) uvs t`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[check_t_def; infer_deBruijn_subst_alt] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[check_t_def] THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN UNDISCH_TAC `ALL (check_t max_tvs uvs)
      (MAP (infer_deBruijn_subst (s:infer_t list)) l)` THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[]]);;

let db_subst_inc_id = prove
 (`!inst t. infer_deBruijn_subst inst (infer_deBruijn_inc (LENGTH inst) t) = t`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN
  REWRITE_TAC[infer_deBruijn_inc_def; infer_deBruijn_subst_alt; GSYM MAP_o;
              injectivity "infer_t"; ARITH_RULE `~(n + l < l:num)`; ADD_SUB] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; o_THM]);;

let t_walkstar_db_subst = prove
 (`!inst t s.
     t_wfs s
     ==> t_walkstar s (infer_deBruijn_subst inst t) =
         infer_deBruijn_subst (MAP (t_walkstar s) inst)
           (t_walkstar (infer_deBruijn_inc (LENGTH inst) o_f s) t)`,
  GEN_TAC THEN MATCH_MP_TAC infer_t_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `t_wfs (infer_deBruijn_inc (LENGTH (inst:infer_t list)) o_f
                        (s:(num,infer_t)fmap))` ASSUME_TAC THENL
    [ASM_MESON_TAC[inc_wfs]; ALL_TAC]) THENL
   [ASM_SIMP_TAC[infer_deBruijn_subst_alt; t_walkstar_eqn1; LENGTH_MAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MAP; t_walkstar_eqn1];
    ASM_SIMP_TAC[infer_deBruijn_subst_alt; t_walkstar_eqn1; LENGTH_MAP;
                 injectivity "infer_t"; GSYM MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[infer_deBruijn_subst_alt; walkstar_inc2] THEN
    MESON_TAC[db_subst_inc_id; LENGTH_MAP]]);;

let TYSYS2AUX_SUBST_OUT_TAC names =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (rhs c) && mem (fst(dest_var(rhs c))) names
    then SUBST_ALL_TAC(SYM th) else failwith "TYSYS2AUX_SUBST_OUT_TAC"));;

let generalise_subst_exist = prove
 (`!s tvs.
     t_wfs s /\ (!uv. uv IN FDOM s ==> check_t tvs {} (t_walkstar s (Infer_Tuvar uv)))
     ==> (!t subst n (smap:(num,num)fmap) a b t'.
            LENGTH subst = n /\ FRANGE smap SUBSET count n /\
            (!x. MEM x subst ==> check_t tvs {} x) /\
            t_vars t SUBSET FDOM s /\ check_t 0 (FDOM s) t /\
            (!x. x IN FDOM smap ==> EL (FAPPLY smap x) subst = t_walkstar s (Infer_Tuvar x)) /\
            generalise 0 n smap t = (a,b,t')
            ==> ?subst'. LENGTH subst' = a /\ (!x. MEM x subst' ==> check_t tvs {} x) /\
                         (!x. x IN FDOM b
                              ==> EL (FAPPLY b x) (APPEND subst subst') =
                                  t_walkstar s (Infer_Tuvar x))) /\
         (!ts subst n (smap:(num,num)fmap) a b ts'.
            LENGTH subst = n /\ FRANGE smap SUBSET count n /\
            (!x. MEM x subst ==> check_t tvs {} x) /\
            ALL (\t. t_vars t SUBSET FDOM s) ts /\ ALL (check_t 0 (FDOM s)) ts /\
            (!x. x IN FDOM smap ==> EL (FAPPLY smap x) subst = t_walkstar s (Infer_Tuvar x)) /\
            generalise_list 0 n smap ts = (a,b,ts')
            ==> ?subst'. LENGTH subst' = a /\ (!x. MEM x subst' ==> check_t tvs {} x) /\
                         (!x. x IN FDOM b
                              ==> EL (FAPPLY b x) (APPEND subst subst') =
                                  t_walkstar s (Infer_Tuvar x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def; PAIR_EQ] THEN STRIP_TAC THEN
    TYSYS2AUX_SUBST_OUT_TAC ["a";"b";"t'"] THEN
    EXISTS_TAC `[]:infer_t list` THEN ASM_REWRITE_TAC[LENGTH; MEM; APPEND_NIL];
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[generalise_def] THEN
    X_CHOOSE_THEN `g1:num` (X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN
      `ts1:infer_t list` ASSUME_TAC))
      (ISPEC `generalise_list 0 n smap (a0:infer_t list)` BASICAUX_TUPLE3) THEN
    ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
    TYSYS2AUX_SUBST_OUT_TAC ["a";"b";"t'"] THEN
    REMOVE_THEN "ih" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `smap:(num,num)fmap`; `ts1:infer_t list`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[t_vars_eqn; check_t_def; UNIONS_SUBSET; IN_SET_OF_LIST;
                                MEM_MAP]) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:num->bool`)) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `uv:num` THEN REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def; LE_0] THEN
    CASES_ON `FLOOKUP (smap:(num,num)fmap) uv` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN TYSYS2AUX_SUBST_OUT_TAC ["a";"a'";"b";"t'"] THENL
     [EXISTS_TAC `[t_walkstar s (Infer_Tuvar uv)]` THEN
      REWRITE_TAC[LENGTH; ONE; MEM] THEN CONJ_TAC THENL
       [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(ASSUME `!uv. uv IN FDOM (s:(num,infer_t)fmap)
                                  ==> check_t tvs {} (t_walkstar s (Infer_Tuvar uv))`) THEN
        UNDISCH_TAC `t_vars (Infer_Tuvar uv) SUBSET FDOM (s:(num,infer_t)fmap)` THEN
        REWRITE_TAC[t_vars_eqn] THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
      X_GEN_TAC `x:num` THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD];
        COND_CASES_TAC THENL
         [ASM_REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]; ALL_TAC] THEN
        SUBGOAL_THEN `FAPPLY (smap:(num,num)fmap) x < LENGTH (subst:infer_t list)` ASSUME_TAC
        THENL
         [UNDISCH_TAC `FRANGE (smap:(num,num)fmap) SUBSET count n` THEN
          ASM_REWRITE_TAC[SUBSET; IN_FRANGE; IN_COUNT] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[EL_APPEND]];
      EXISTS_TAC `[]:infer_t list` THEN ASM_REWRITE_TAC[LENGTH; MEM; APPEND_NIL]];
    REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def; PAIR_EQ] THEN STRIP_TAC THEN
    TYSYS2AUX_SUBST_OUT_TAC ["a";"b";"ts'"] THEN
    EXISTS_TAC `[]:infer_t list` THEN ASM_REWRITE_TAC[LENGTH; MEM; APPEND_NIL];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iht") (LABEL_TAC "ihts")) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def] THEN
    X_CHOOSE_THEN `g1:num` (X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN
      `t1:infer_t` ASSUME_TAC))
      (ISPEC `generalise 0 n smap (a0:infer_t)` BASICAUX_TUPLE3) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    X_CHOOSE_THEN `g2:num` (X_CHOOSE_THEN `s2:(num,num)fmap` (X_CHOOSE_THEN
      `ts2:infer_t list` ASSUME_TAC))
      (ISPEC `generalise_list 0 (g1 + n) s1 (a1:infer_t list)` BASICAUX_TUPLE3) THEN
    ASM_REWRITE_TAC[pair_CASE; PAIR_EQ; ALL] THEN STRIP_TAC THEN
    TYSYS2AUX_SUBST_OUT_TAC ["a";"b";"ts'"] THEN
    REMOVE_THEN "iht" (MP_TAC o SPECL [`subst:infer_t list`; `n:num`; `smap:(num,num)fmap`;
                                      `g1:num`; `s1:(num,num)fmap`; `t1:infer_t`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `sub1:infer_t list` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `FRANGE (s1:(num,num)fmap) SUBSET count (g1 + n)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`a0:infer_t`; `0`; `n:num`; `smap:(num,num)fmap`; `g1:num`;
                    `s1:(num,num)fmap`; `t1:infer_t`] (CONJUNCT1 generalise_subst)) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_FRANGE; IN_COUNT; SUBMAP_DEF; IN_DIFF] THEN STRIP_TAC THEN
      UNDISCH_TAC `FRANGE (smap:(num,num)fmap) SUBSET count n` THEN
      REWRITE_TAC[SUBSET; IN_FRANGE; IN_COUNT] THEN DISCH_TAC THEN
      X_GEN_TAC `y:num` THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `k IN FDOM (smap:(num,num)fmap)` THENL
       [ASM_MESON_TAC[ARITH_RULE `x < n ==> x < g + n:num`];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REMOVE_THEN "ihts" (MP_TAC o SPECL [`APPEND subst sub1:infer_t list`; `g1 + n:num`;
                                       `s1:(num,num)fmap`; `g2:num`; `s2:(num,num)fmap`;
                                       `ts2:infer_t list`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; MEM_APPEND] THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `sub2:infer_t list` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `APPEND sub1 sub2:infer_t list` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; MEM_APPEND; APPEND_ASSOC] THEN ASM_MESON_TAC[]]);;

let infer_deBruijn_subst_infer_subst_walkstar = prove
 (`!s b subst (n:num) m.
     FRANGE b SUBSET count (LENGTH subst) /\ t_wfs s
     ==> (!t. (!x. x IN t_vars t ==> EL (FAPPLY b x) subst = t_walkstar s (Infer_Tuvar x)) /\
              check_t 0 m t /\ t_vars t SUBSET FDOM b
              ==> infer_deBruijn_subst subst (infer_subst b t) = t_walkstar s t) /\
         (!ts. ALL (\t. !x. x IN t_vars t
                            ==> EL (FAPPLY b x) subst = t_walkstar s (Infer_Tuvar x)) ts /\
               ALL (check_t 0 m) ts /\ ALL (\t. t_vars t SUBSET FDOM b) ts
               ==> MAP (infer_deBruijn_subst subst o infer_subst b) ts =
                   MAP (t_walkstar s) ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC infer_t_INDUCT THEN
  REWRITE_TAC[check_t_def; LT; ALL; MAP] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[infer_subst_def; t_walkstar_eqn1; infer_deBruijn_subst_alt;
                 injectivity "infer_t"; GSYM MAP_o] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[t_vars_eqn; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP;
                                UNIONS_SUBSET]) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:num` THEN REWRITE_TAC[t_vars_eqn; IN_SING; SING_SUBSET] THEN
    STRIP_TAC THEN REWRITE_TAC[infer_subst_def] THEN
    SUBGOAL_THEN `FLOOKUP (b:(num,num)fmap) x = SOME (FAPPLY b x)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[flookup_thm]; ALL_TAC] THEN
    CASE_REWRITE_TAC[infer_deBruijn_subst_alt] THEN
    SUBGOAL_THEN `FAPPLY (b:(num,num)fmap) x < LENGTH (subst:infer_t list)` ASSUME_TAC THENL
     [UNDISCH_TAC `FRANGE (b:(num,num)fmap) SUBSET count (LENGTH (subst:infer_t list))` THEN
      REWRITE_TAC[SUBSET; IN_FRANGE; IN_COUNT] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[CONS_11; o_THM] THEN ASM_MESON_TAC[]]);;

let remap_tenv_def = cake_def
  `remap_tenv (f:num->num) (tenv:type_env) =
     type_env_REC
       (nsMap (\p. match p with (n,t) -> (n,ts_tid_rename f t)) (type_env_v tenv))
       (nsMap (\p. match p with (ls,ts,tid) -> (ls,MAP (ts_tid_rename f) ts,f tid))
          (type_env_c tenv))
       (nsMap (\p. match p with (ls,t) -> (ls,ts_tid_rename f t)) (type_env_t tenv))`;;

let remap_tenv_I = prove
 (`remap_tenv I = I`,
  REWRITE_TAC[FUN_EQ_THM; remap_tenv_def; ts_tid_rename_I; I_THM; MAP_I] THEN
  X_GEN_TAC `tenv:type_env` THEN
  SUBGOAL_THEN (CASE_TERM
   `(\p:num#t. match p with (n,t) -> (n,t)) = I /\
    (\p:mlstring list#t list#num. match p with (ls,ts,tid) -> (ls,ts,tid)) = I /\
    (\p:mlstring list#t. match p with (ls,t) -> (ls,t)) = I`)
    (fun th -> REWRITE_TAC[th; nsMap_I]) THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; I_THM] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[type_env_component_equality; type_env_INFO.ri_accessors]);;
let _ = cake_add_simps [remap_tenv_I];;

let t_vwalk_set_tids = prove
 (`!tids s. t_wfs s ==>
     !v. inf_set_tids_subst tids s ==> inf_set_tids (t_vwalk s v) SUBSET tids`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind) THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP t_vwalk_eqn th]) THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) v` THEN
  CASE_REWRITE_TAC[inf_set_tids_def; EMPTY_SUBSET] THEN
  CASES_ON `a:infer_t` THEN CASE_REWRITE_TAC[inf_set_tids_def; EMPTY_SUBSET] THENL
   [UNDISCH_TAC `inf_set_tids_subst tids (s:(num,infer_t)fmap)` THEN
    REWRITE_TAC[inf_set_tids_subst_def; IN_FRANGE_FLOOKUP; inf_set_tids_subset_def] THEN
    DISCH_THEN(MP_TAC o SPEC `Infer_Tapp a0 a1`) THEN REWRITE_TAC[inf_set_tids_def] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let t_walk_set_tids = prove
 (`!tids s t t'.
     t_wfs s /\ inf_set_tids_subst tids s /\ inf_set_tids_subset tids t /\ t_walk s t = t'
     ==> inf_set_tids_subset tids t'`,
  REPEAT GEN_TAC THEN CASES_ON `t:infer_t` THEN REWRITE_TAC[t_walk_eqn] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[inf_set_tids_subset_def] THEN ASM_MESON_TAC[t_vwalk_set_tids]);;

let t_walkstar_set_tids = prove
 (`!tids s t t'.
     t_wfs s /\ inf_set_tids_subst tids s /\ inf_set_tids_subset tids t /\
     t_walkstar s t = t'
     ==> inf_set_tids_subset tids t'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)))) THEN
  SPEC_TAC(`t:infer_t`,`t:infer_t`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tids:num->bool`; `s:(num,infer_t)fmap`; `t:infer_t`;
                `t_walk (s:(num,infer_t)fmap) t`] t_walk_set_tids) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_walkstar_eqn th]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  SPEC_TAC(`t_walk (s:(num,infer_t)fmap) t`,`w:infer_t`) THEN
  X_GEN_TAC `w:infer_t` THEN CASES_ON `w:infer_t` THEN
  CASE_REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_def; EMPTY_SUBSET;
                   injectivity "infer_t"] THEN
  REWRITE_TAC[INSERT_SUBSET; UNIONS_SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_inf_set_tids_subst_FUPDATE = prove
 (`!tids s v t.
     inf_set_tids_subst tids s /\ inf_set_tids_subset tids t
     ==> inf_set_tids_subst tids (s |+ (v,t))`,
  REWRITE_TAC[inf_set_tids_subst_def; IN_FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_inf_set_tids_subset_eqn = prove
 (`(!tids ts tn. inf_set_tids_subset tids (Infer_Tapp ts tn) <=>
                 tn IN tids /\ ALL (inf_set_tids_subset tids) ts) /\
   (!tids n. inf_set_tids_subset tids (Infer_Tuvar n) <=> T) /\
   (!tids n. inf_set_tids_subset tids (Infer_Tvar_db n) <=> T)`,
  REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_def; INSERT_SUBSET; UNIONS_SUBSET;
              IN_SET_OF_LIST; MEM_MAP; GSYM ALL_MEM; EMPTY_SUBSET] THEN
  MESON_TAC[]);;

let t_unify_set_tids = prove
 (`!tids.
   (!s t1 t2. t_wfs s ==>
      !s'. inf_set_tids_subst tids s /\ inf_set_tids_subset tids t1 /\
           inf_set_tids_subset tids t2 /\ t_unify s t1 t2 = SOME s'
           ==> inf_set_tids_subst tids s') /\
   (!s ts1 ts2. t_wfs s ==>
      !s'. inf_set_tids_subst tids s /\ ALL (inf_set_tids_subset tids) ts1 /\
           ALL (inf_set_tids_subset tids) ts2 /\ ts_unify s ts1 ts2 = SOME s'
           ==> inf_set_tids_subst tids s')`,
  GEN_TAC THEN MATCH_MP_TAC t_unify_strongind THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `t_unify s t1 t2 = SOME (s':(num,infer_t)fmap)` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_unify_eqn th]) THEN
    MP_TAC(SPECL [`tids:num->bool`; `s:(num,infer_t)fmap`; `t1:infer_t`;
                  `t_walk (s:(num,infer_t)fmap) t1`] t_walk_set_tids) THEN
    MP_TAC(SPECL [`tids:num->bool`; `s:(num,infer_t)fmap`; `t2:infer_t`;
                  `t_walk (s:(num,infer_t)fmap) t2`] t_walk_set_tids) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    SPEC_TAC(`t_walk (s:(num,infer_t)fmap) t1`,`w1:infer_t`) THEN
    SPEC_TAC(`t_walk (s:(num,infer_t)fmap) t2`,`w2:infer_t`) THEN
    X_GEN_TAC `w2:infer_t` THEN X_GEN_TAC `w1:infer_t` THEN
    CASES_ON `w1:infer_t` THEN CASES_ON `w2:infer_t` THEN
    CASE_REWRITE_TAC[t_ext_s_check_eqn; injectivity "infer_t"; distinctness "infer_t";
                     bool_case_eq; option_DISTINCT; injectivity "option";
                     TYSYS2AUX_inf_set_tids_subset_eqn] THEN
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[TYSYS2AUX_inf_set_tids_subst_FUPDATE; TYSYS2AUX_inf_set_tids_subset_eqn];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    CASES_ON `ts1:infer_t list` THEN CASES_ON `ts2:infer_t list` THEN
    REWRITE_TAC([ts_unify_def; ALL; option_DISTINCT; injectivity "option"] @
                all_case_eqs()) THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

let pure_add_constraints_set_tids = prove
 (`!tids s1 ls s2.
     t_wfs s1 /\ ALL (inf_set_tids_subset tids) (MAP FST ls) /\
     ALL (inf_set_tids_subset tids) (MAP SND ls) /\ inf_set_tids_subst tids s1 /\
     pure_add_constraints s1 ls s2
     ==> inf_set_tids_subst tids s2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pure_add_constraints_def] THEN MESON_TAC[];
    MP_TAC(ISPEC `h:infer_t#infer_t` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:infer_t` (X_CHOOSE_THEN `b:infer_t` SUBST1_TAC)) THEN
    REWRITE_TAC[pure_add_constraints_def; MAP; ALL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s2':(num,infer_t)fmap` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[t_unify_set_tids; t_unify_wfs]]);;

(* HOL4: hide *)
let inferProps_hide_def = cake_def
  `inferProps_hide (x:A) = x`;;

let TYSYS2AUX_inf_set_tids_uvar_subst = prove
 (`!tids tvs (f:num->num) l (t:t).
     LENGTH tvs = LENGTH l /\ set_tids t SUBSET tids
     ==> inf_set_tids_subset tids
           (infer_type_subst (ZIP tvs (MAP (\n. Infer_Tuvar (f n)) l)) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inf_set_tids_subset_def] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `set_tids t UNION
    UNIONS (IMAGE inf_set_tids (set_of_list (MAP SND
      (ZIP (tvs:mlstring list) (MAP (\n. Infer_Tuvar ((f:num->num) n)) l)))))` THEN
  REWRITE_TAC[inf_set_tids_infer_type_subst_SUBSET] THEN
  SUBGOAL_THEN `LENGTH (tvs:mlstring list) =
                LENGTH (MAP (\n. Infer_Tuvar ((f:num->num) n)) l)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST; MEM_MAP] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[inf_set_tids_def; EMPTY_SUBSET]);;

let TYSYS2AUX_set_tids_ienv_c = prove
 (`!tids ienv cn (tvs:mlstring list) ts tn.
     inf_set_tids_ienv tids ienv /\
     nsLookup (inf_env_inf_c ienv) cn = SOME (tvs,ts,tn)
     ==> ALL (\t. set_tids t SUBSET tids) ts /\ tn IN tids`,
  REWRITE_TAC[inf_set_tids_ienv_def] THEN REPEAT STRIP_TAC THEN
  TYSYS2AUX_NSALL_TAC THEN
  REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_unconvert] THEN MESON_TAC[]);;

let TYSYS2AUX_set_tids_Pcon = prove
 (`!tids s1 s2 ienv cn (tvs':mlstring list) ts tn ts'' n1.
     t_wfs s1 /\ inf_set_tids_ienv tids ienv /\
     nsLookup (inf_env_inf_c ienv) cn = SOME (tvs',ts,tn) /\
     inf_set_tids_subst tids s1 /\ ALL (inf_set_tids_subset tids) ts'' /\
     LENGTH ts'' = LENGTH ts /\
     pure_add_constraints s1
       (ZIP ts'' (MAP (infer_type_subst
                         (ZIP tvs' (MAP (\n. Infer_Tuvar (n1 + n))
                                        (COUNT_LIST (LENGTH tvs'))))) ts)) s2
     ==> inf_set_tids_subst tids s2 /\ tn IN tids`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tids:num->bool`; `ienv:inf_env`; `cn:(mlstring,mlstring)id`;
                `tvs':mlstring list`; `ts:t list`; `tn:num`] TYSYS2AUX_set_tids_ienv_c) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC pure_add_constraints_set_tids THEN
  MAP_EVERY EXISTS_TAC
   [`s1:(num,infer_t)fmap`;
    `ZIP (ts'':infer_t list)
       (MAP (infer_type_subst
               (ZIP (tvs':mlstring list) (MAP (\n. Infer_Tuvar (n1 + n))
                                              (COUNT_LIST (LENGTH tvs'))))) (ts:t list))`] THEN
  SUBGOAL_THEN `LENGTH (ts'':infer_t list) =
                LENGTH (MAP (infer_type_subst
                  (ZIP (tvs':mlstring list) (MAP (\n. Infer_Tuvar (n1 + n))
                                 (COUNT_LIST (LENGTH tvs'))))) (ts:t list))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[ALL_MAP] THEN
  UNDISCH_TAC `ALL (\t. set_tids t SUBSET tids) (ts:t list)` THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TYSYS2AUX_inf_set_tids_uvar_subst THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]);;

let TYSYS2AUX_set_tids_Ptannot = prove
 (`!tids s1 s2 t' t ienv.
     t_wfs s1 /\ prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
     inf_set_tids_subst tids s1 /\ inf_set_tids_subset tids t' /\
     check_type_names (inf_env_inf_t ienv) t /\
     t_unify s1 t' (infer_type_subst [] (type_name_subst (inf_env_inf_t ienv) t)) = SOME s2
     ==> inf_set_tids_subst tids s2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `t':infer_t`;
                `infer_type_subst [] (type_name_subst (inf_env_inf_t ienv) t)`]
           (CONJUNCT1 (SPEC `tids:num->bool` t_unify_set_tids))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s2:(num,infer_t)fmap`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[inf_set_tids_subset_def] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `set_tids (type_name_subst (inf_env_inf_t ienv) t) UNION
              UNIONS (IMAGE inf_set_tids (set_of_list (MAP SND ([]:(mlstring#infer_t)list))))` THEN
  REWRITE_TAC[inf_set_tids_infer_type_subst_SUBSET] THEN
  REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_0; UNION_EMPTY;
              GSYM set_tids_subset_def] THEN
  MATCH_MP_TAC set_tids_subset_type_name_subst THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inf_set_tids_ienv tids ienv` THEN
  REWRITE_TAC[inf_set_tids_ienv_def; inf_set_tids_subset_def; inf_set_tids_unconvert;
              GSYM set_tids_subset_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let TYSYS2AUX_prim_tids_T_all = prove
 (`!tids. prim_tids T tids
          ==> Tlist_num IN tids /\ Tbool_num IN tids /\ Tarray_num IN tids /\
              Tchar_num IN tids /\ Texn_num IN tids /\ Tfn_num IN tids /\
              Tint_num IN tids /\ Tref_num IN tids /\ Tstring_num IN tids /\
              Ttup_num IN tids /\ Tvector_num IN tids /\ Tword64_num IN tids /\
              Tword8_num IN tids /\ Tword8array_num IN tids /\ Tdouble_num IN tids`,
  REWRITE_TAC[prim_tids_def; prim_type_nums_def; ALL] THEN MESON_TAC[]);;

let TYSYS2AUX_inf_set_tids_subset_uvars = prove
 (`!tids (f:num->num) l. ALL (inf_set_tids_subset tids) (MAP (\n. Infer_Tuvar (f n)) l)`,
  REWRITE_TAC[ALL_MAP; o_DEF; TYSYS2AUX_inf_set_tids_subset_eqn; ALL_T]);;

let TYSYS2AUX_SET_TIDS_IH_TAC =
  FIRST_X_ASSUM(fun ih ->
    if is_forall (concl ih) then
      FIRST_ASSUM(fun eq -> MP_TAC(MATCH_MP ih eq) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[infer_p_wfs]; STRIP_TAC])
    else failwith "TYSYS2AUX_SET_TIDS_IH_TAC");;

let infer_p_inf_set_tids = prove
 (`!tids.
   (!l cenv p st t env st'.
      infer_p l cenv p st = (M_success (t,env),st')
      ==> prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
          inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs (infer_st_subst st)
          ==> inf_set_tids_subset tids t /\
              ALL (inf_set_tids_subset tids o SND) env /\
              inf_set_tids_subst tids (infer_st_subst st')) /\
   (!l cenv ps st ts env st'.
      infer_ps l cenv ps st = (M_success (ts,env),st')
      ==> prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
          inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs (infer_st_subst st)
          ==> ALL (inf_set_tids_subset tids) ts /\
              ALL (inf_set_tids_subset tids o SND) env /\
              inf_set_tids_subst tids (infer_st_subst st'))`,
  GEN_TAC THEN MATCH_MP_TAC infer_p_ind THEN REPEAT CONJ_TAC THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC ORELSE GEN_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[infer_p_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN TYSYS2AUX_SUBST_VARS_TAC THEN
  REWRITE_TAC[infer_st_rewrs] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[infer_st_rewrs; injectivity "option"; option_DISTINCT;
                              GSYM option_DISTINCT; FORALL_UNWIND_THM1;
                              FORALL_UNWIND_THM2]) THEN
  REPEAT TYSYS2AUX_SET_TIDS_IH_TAC THEN
  ASM_SIMP_TAC[TYSYS2AUX_prim_tids_T_all; TYSYS2AUX_inf_set_tids_subset_eqn; ALL;
               ALL_APPEND; o_THM; SND; TYSYS2AUX_inf_set_tids_subset_uvars] THENL
   [(* Pcon SOME *)
    MP_TAC(SPECL [`tids:num->bool`; `infer_st_subst st'''`; `infer_st_subst st'`;
                  `ienv:inf_env`; `cn:(mlstring,mlstring)id`; `p1:mlstring list`;
                  `p1':t list`; `p2:num`; `p1'':infer_t list`;
                  `infer_st_next_uvar st'''`] TYSYS2AUX_set_tids_Pcon) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[infer_p_wfs]; SIMP_TAC[]];
    (* Ptannot *)
    MATCH_MP_TAC TYSYS2AUX_set_tids_Ptannot THEN
    MAP_EVERY EXISTS_TAC [`infer_st_subst st'''`; `t':infer_t`; `t:ast_t`; `ienv:inf_env`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[infer_p_wfs]]);;

let TYSYS2AUX_prim_tids_T_nums = prove
 (`!tids. prim_tids T tids
          ==> (!ty. t_num_of ty IN tids) /\ (!wz. word_tc wz IN tids)`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP TYSYS2AUX_prim_tids_T_all) THEN
  SUBGOAL_THEN `!wz. word_tc wz IN tids /\ t_num_of (WordT wz) IN tids` ASSUME_TAC THENL
   [GEN_TAC THEN CASES_ON `wz:word_size` THEN ASM_REWRITE_TAC[word_tc_def; t_num_of_def];
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN CASES_ON `ty:prim_type` THEN
    ASM_REWRITE_TAC[t_num_of_def]]);;

let TYSYS2AUX_st_step = prove
 (`!tids s1 s2 t1 t2.
     t_unify s1 t1 t2 = SOME s2
     ==> t_wfs s1 /\ inf_set_tids_subst tids s1 /\ inf_set_tids_subset tids t1 /\
         inf_set_tids_subset tids t2
         ==> t_wfs s2 /\ inf_set_tids_subst tids s2`,
  MESON_TAC[t_unify_set_tids; t_unify_wfs]);;

let TYSYS2AUX_SET_TIDS_CHAIN_TAC =
  let is_app nm tm = try fst(dest_const(fst(strip_comb tm))) = nm with Failure _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_app "t_unify" (lhs c)
    then MP_TAC(SPEC `tids:num->bool` (MATCH_MP TYSYS2AUX_st_step th)) THEN
         ANTS_TAC THENL
          [ASM_SIMP_TAC[TYSYS2AUX_prim_tids_T_all; TYSYS2AUX_prim_tids_T_nums;
                        TYSYS2AUX_inf_set_tids_subset_eqn; ALL];
           STRIP_TAC]
    else failwith "TYSYS2AUX_SET_TIDS_CHAIN_TAC"));;

let TYSYS2AUX_SET_TIDS_PAC_TAC =
  let is_app nm tm = try fst(dest_const(fst(strip_comb tm))) = nm with Failure _ -> false in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_app "pure_add_constraints" c then
      let args = snd(strip_comb c) in
      MATCH_MP_TAC pure_add_constraints_set_tids THEN
      EXISTS_TAC (el 0 args) THEN EXISTS_TAC (el 1 args) THEN
      ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; EVERY_REPLICATE;
                   TYSYS2AUX_prim_tids_T_all; TYSYS2AUX_prim_tids_T_nums;
                   TYSYS2AUX_inf_set_tids_subset_eqn; ALL]
    else failwith "TYSYS2AUX_SET_TIDS_PAC_TAC");;

let constrain_op_set_tids = prove
 (`!l op ts t st st' tids.
     constrain_op l op ts st = (M_success t,st') /\
     ALL (inf_set_tids_subset tids) ts /\
     inf_set_tids_subst tids (infer_st_subst st) /\
     t_wfs (infer_st_subst st) /\ prim_tids T tids
     ==> inf_set_tids_subset tids t /\ inf_set_tids_subst tids (infer_st_subst st')`,
  GEN_TAC THEN X_GEN_TAC `op:op` THEN CASES_ON `op:op` THEN
  REWRITE_TAC[constrain_op_success; add_constraints_success] THEN
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REPEAT(CHANGED_TAC(RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; ALL; infer_st_rewrs]) THEN
                     TYSYS2AUX_SPLIT_ASM_TAC THEN TYSYS2AUX_SUBST_VARS_TAC)) THEN
  REWRITE_TAC[infer_st_rewrs] THEN
  TYSYS2AUX_SET_TIDS_CHAIN_TAC THEN
  ASM_SIMP_TAC[TYSYS2AUX_prim_tids_T_all; TYSYS2AUX_prim_tids_T_nums;
               TYSYS2AUX_inf_set_tids_subset_eqn; ALL] THEN
  FIRST [TYSYS2AUX_CONTRA_TAC; FIRST_ASSUM ACCEPT_TAC; TYSYS2AUX_SET_TIDS_PAC_TAC]);;

(* ---------- infer_e_inf_set_tids: helper lemmas ---------- *)

let TYSYS2AUX_sti_fupd_v = prove
 (CASE_TERM `!tids ienv (v:(mlstring,mlstring,num#infer_t)namespace).
     inf_set_tids_ienv tids ienv /\
     nsAll (\i p. match p with (n,t) -> inf_set_tids_subset tids t) v
     ==> inf_set_tids_ienv tids (inf_env_inf_v_fupd (K v) ienv)`,
  REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let TYSYS2AUX_sti_v = prove
 (CASE_TERM `!tids ienv.
     inf_set_tids_ienv tids ienv
     ==> nsAll (\i p. match p with (n,t) -> inf_set_tids_subset tids t)
           (inf_env_inf_v ienv)`,
  REWRITE_TAC[inf_set_tids_ienv_def] THEN MESON_TAC[]);;

let TYSYS2AUX_sti_bind = prove
 (`!tids ienv x (n:num) t.
     inf_set_tids_ienv tids ienv /\ inf_set_tids_subset tids t
     ==> inf_set_tids_ienv tids
           (inf_env_inf_v_fupd (K (nsBind x (n,t) (inf_env_inf_v ienv))) ienv)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYSYS2AUX_sti_fupd_v THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC nsAll_nsBind THEN ASM_SIMP_TAC[TYSYS2AUX_sti_v] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let TYSYS2AUX_sti_optbind = prove
 (`!tids ienv xo (n:num) t.
     inf_set_tids_ienv tids ienv /\ inf_set_tids_subset tids t
     ==> inf_set_tids_ienv tids
           (inf_env_inf_v_fupd (K (nsOptBind xo (n,t) (inf_env_inf_v ienv))) ienv)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYSYS2AUX_sti_fupd_v THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC nsAll_nsOptBind THEN ASM_SIMP_TAC[TYSYS2AUX_sti_v] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[option_nchotomy]);;

let TYSYS2AUX_sti_letrec = prove
 (CASE_TERM `!tids ienv (funs:(mlstring#mlstring#exp)list) uvars.
     inf_set_tids_ienv tids ienv /\ ALL (inf_set_tids_subset tids) uvars /\
     LENGTH uvars = LENGTH funs
     ==> inf_set_tids_ienv tids
           (inf_env_inf_v_fupd
              (K (nsAppend
                    (alist_to_ns
                       (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs uvars))
                    (inf_env_inf_v ienv))) ienv)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYSYS2AUX_sti_fupd_v THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC nsAll_nsAppend THEN ASM_SIMP_TAC[TYSYS2AUX_sti_v] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  SPEC_TAC(`uvars:infer_t list`,`uvars:infer_t list`) THEN
  SPEC_TAC(`funs:(mlstring#mlstring#exp)list`,`funs:(mlstring#mlstring#exp)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP2; ALL; LENGTH; NOT_SUC; SUC_INJ] THEN
  X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `e:exp`
    SUBST_ALL_TAC)) (ISPEC `h:mlstring#mlstring#exp` BASICAUX_TUPLE3) THEN
  BETA_TAC THEN CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let TYSYS2AUX_sti_pes = prove
 (CASE_TERM `!tids ienv (env':(mlstring#infer_t)list).
     inf_set_tids_ienv tids ienv /\ ALL (inf_set_tids_subset tids) (MAP SND env')
     ==> inf_set_tids_ienv tids
           (inf_env_inf_v_fupd
              (K (nsAppend
                    (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) env'))
                    (inf_env_inf_v ienv))) ienv)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYSYS2AUX_sti_fupd_v THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC nsAll_nsAppend THEN ASM_SIMP_TAC[TYSYS2AUX_sti_v] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN REWRITE_TAC[ALL_MAP] THEN
  UNDISCH_TAC `ALL (inf_set_tids_subset tids) (MAP SND (env':(mlstring#infer_t)list))` THEN
  REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

let TYSYS2AUX_sti_lookup_v = prove
 (`!tids ienv id (n:num) t.
     inf_set_tids_ienv tids ienv /\ nsLookup (inf_env_inf_v ienv) id = SOME (n,t)
     ==> inf_set_tids_subset tids t`,
  REWRITE_TAC[inf_set_tids_ienv_def] THEN REPEAT STRIP_TAC THEN
  TYSYS2AUX_NSALL_TAC);;

let TYSYS2AUX_sti_db = prove
 (`!tids uvs t.
     ALL (inf_set_tids_subset tids) uvs /\ inf_set_tids_subset tids t
     ==> inf_set_tids_subset tids (infer_deBruijn_subst uvs t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inf_set_tids_subset_def] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `inf_set_tids t UNION UNIONS (IMAGE inf_set_tids (set_of_list uvs))` THEN
  REWRITE_TAC[inf_set_tids_infer_deBruijn_subst_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[inf_set_tids_subset_def; GSYM ALL_MEM]) THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST] THEN
  ASM_REWRITE_TAC[]);;

let TYSYS2AUX_sti_con = prove
 (`!tids ienv cn (tvs':mlstring list) ts tn ts'.
     inf_set_tids_ienv tids ienv /\
     nsLookup (inf_env_inf_c ienv) cn = SOME (tvs',ts,tn) /\
     ALL (inf_set_tids_subset tids) ts' /\ LENGTH ts' = LENGTH tvs'
     ==> ALL (inf_set_tids_subset tids) (MAP (infer_type_subst (ZIP tvs' ts')) ts) /\
         tn IN tids`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tids:num->bool`; `ienv:inf_env`; `cn:(mlstring,mlstring)id`;
                `tvs':mlstring list`; `ts:t list`; `tn:num`] TYSYS2AUX_set_tids_ienv_c) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL_MAP] THEN
  UNDISCH_TAC `ALL (\t. set_tids t SUBSET tids) (ts:t list)` THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[inf_set_tids_subset_def] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `set_tids x UNION
    UNIONS (IMAGE inf_set_tids (set_of_list (MAP SND
      (ZIP (tvs':mlstring list) (ts':infer_t list)))))` THEN
  REWRITE_TAC[inf_set_tids_infer_type_subst_SUBSET] THEN
  SUBGOAL_THEN `LENGTH (tvs':mlstring list) = LENGTH (ts':infer_t list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MAP_SND_ZIP th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[inf_set_tids_subset_def; GSYM ALL_MEM]) THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST] THEN
  ASM_REWRITE_TAC[]);;

let TYSYS2AUX_sti_tannot = prove
 (`!tids ienv t.
     prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
     check_type_names (inf_env_inf_t ienv) t
     ==> inf_set_tids_subset tids
           (infer_type_subst [] (type_name_subst (inf_env_inf_t ienv) t))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[inf_set_tids_subset_def] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `set_tids (type_name_subst (inf_env_inf_t ienv) t) UNION
              UNIONS (IMAGE inf_set_tids (set_of_list (MAP SND ([]:(mlstring#infer_t)list))))` THEN
  REWRITE_TAC[inf_set_tids_infer_type_subst_SUBSET] THEN
  REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_0; UNION_EMPTY;
              GSYM set_tids_subset_def] THEN
  MATCH_MP_TAC set_tids_subset_type_name_subst THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inf_set_tids_ienv tids ienv` THEN
  REWRITE_TAC[inf_set_tids_ienv_def; inf_set_tids_subset_def; inf_set_tids_unconvert;
              GSYM set_tids_subset_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The invariant for infer_e_inf_set_tids: a well-formed substitution whose *)
(* range uses only the type identifiers tids                               *)

let TYSYS2AUX_gt_def = new_definition
 `TYSYS2AUX_gt tids (st:infer_st) <=>
    t_wfs (infer_st_subst st) /\ inf_set_tids_subst tids (infer_st_subst st)`;;

let TYSYS2AUX_hi_fresh_uvar = prove
 (`!tids. TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle (\st. T)
            (fresh_uvar:infer_st->(infer_t,locs option#mlstring)exc#infer_st)
            (\v st. inf_set_tids_subset tids v)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gt_def;
              fresh_uvar_success] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[infer_st_rewrs; TYSYS2AUX_inf_set_tids_subset_eqn] THEN ARITH_TAC);;

let TYSYS2AUX_hi_n_fresh_uvar = prove
 (`!tids n. TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle (\st. T)
              (n_fresh_uvar n:infer_st->(infer_t list,locs option#mlstring)exc#infer_st)
              (\v st. ALL (inf_set_tids_subset tids) v /\ LENGTH v = n)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gt_def;
              n_fresh_uvar_success] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[infer_st_rewrs; LENGTH_MAP; LENGTH_COUNT_LIST; LE_ADD;
                  TYSYS2AUX_inf_set_tids_subset_uvars]);;

let TYSYS2AUX_hi_add_constraint = prove
 (`!tids l t1 t2.
     TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
       (\st. inf_set_tids_subset tids t1 /\ inf_set_tids_subset tids t2)
       (add_constraint l t1 t2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gt_def;
              add_constraint_success] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[infer_st_rewrs; LE_REFL] THEN
  ASM_MESON_TAC[TYSYS2AUX_st_step]);;

let TYSYS2AUX_hi_add_constraints = prove
 (`!tids l ts1 ts2.
     TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
       (\st. ALL (inf_set_tids_subset tids) ts1 /\ ALL (inf_set_tids_subset tids) ts2)
       (add_constraints l ts1 ts2) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gt_def;
              add_constraints_success] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "infer_st_next_uvar"
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pure_add_constraints_wfs]; ALL_TAC] THEN
  MATCH_MP_TAC pure_add_constraints_set_tids THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st`; `ZIP (ts1:infer_t list) (ts2:infer_t list)`] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP]);;

let TYSYS2AUX_hi_constrain_op = prove
 (`!tids l op ts.
     TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
       (\st. ALL (inf_set_tids_subset tids) ts /\ prim_tids T tids)
       (constrain_op l op ts) (\t st. inf_set_tids_subset tids t)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gt_def] THEN
  MESON_TAC[TYSYS2AUX_constrain_op_state; constrain_op_wfs; constrain_op_set_tids]);;

let TYSYS2AUX_hi_infer_p = prove
 (`!tids l ienv p.
     TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
       (\st. prim_tids T tids /\ inf_set_tids_ienv tids ienv)
       (infer_p l ienv p)
       (\v st. inf_set_tids_subset tids (FST v) /\
               ALL (inf_set_tids_subset tids) (MAP SND (SND v)))`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; TYSYS2AUX_gt_def; FORALL_PAIR_THM;
              FST; SND; ALL_MAP] THEN
  MESON_TAC[infer_p_inf_set_tids; infer_p_wfs; infer_p_next_uvar_mono]);;

(* Triples of the computations that do not change the state, for any G *)

let TYSYS2AUX_hg_lookup = prove
 (`!G l err id (env:(mlstring,mlstring,V)namespace).
     TYSYS2AUX_hoare G TYSYS2AUX_nle (\st. T)
       (lookup_st_ex l err id env:infer_st->(V,locs option#mlstring)exc#infer_st)
       (\v st. nsLookup env id = SOME v)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; lookup_st_ex_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hg_check_dups = prove
 (`!G l (f:mlstring->mlstring) ls.
     TYSYS2AUX_hoare G TYSYS2AUX_nle (\st. T)
       (check_dups l f ls:infer_st->(1,locs option#mlstring)exc#infer_st) (\v st. T)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; check_dups_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hg_tncs = prove
 (`!G l f tenvT fvs t.
     TYSYS2AUX_hoare G TYSYS2AUX_nle (\st. T)
       (type_name_check_subst l f tenvT fvs t)
       (\v st. v = type_name_subst tenvT t /\ check_freevars_ast fvs t /\
               check_type_names tenvT t)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; type_name_check_subst_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_hg_guard = prove
 (`!G P l (msg:mlstring).
     TYSYS2AUX_hoare G TYSYS2AUX_nle (\st. T)
       (infer_guard P l msg:infer_st->(1,locs option#mlstring)exc#infer_st) (\v st. P)`,
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_nle_def; guard_success] THEN
  MESON_TAC[LE_REFL]);;

let TYSYS2AUX_SI_PRIMS =
  [TYSYS2AUX_hi_fresh_uvar; TYSYS2AUX_hi_n_fresh_uvar; TYSYS2AUX_hi_add_constraint;
   TYSYS2AUX_hi_add_constraints; TYSYS2AUX_hi_constrain_op; TYSYS2AUX_hg_lookup;
   TYSYS2AUX_hg_check_dups; TYSYS2AUX_hg_tncs; TYSYS2AUX_hg_guard; TYSYS2AUX_hi_infer_p;
   TYSYS2AUX_ht_return];;

let TYSYS2AUX_SI_CLOSER =
  FIRST [MATCH_ACCEPT_TAC TYSYS2AUX_nle_trans;
         MATCH_ACCEPT_TAC TYSYS2AUX_nle_refl;
         REWRITE_TAC[TYSYS2AUX_nle_def; FST; SND] THEN BETA_TAC THEN
         REPEAT STRIP_TAC THEN
         ASM_SIMP_TAC[TYSYS2AUX_prim_tids_T_all; TYSYS2AUX_prim_tids_T_nums;
                      TYSYS2AUX_inf_set_tids_subset_eqn; ALL] THEN
         ASM_MESON_TAC[TYSYS2AUX_sti_bind; TYSYS2AUX_sti_optbind; TYSYS2AUX_sti_letrec;
                       TYSYS2AUX_sti_pes; TYSYS2AUX_sti_db; TYSYS2AUX_sti_lookup_v;
                       TYSYS2AUX_sti_con; TYSYS2AUX_sti_tannot]];;

let TYSYS2AUX_infer_e_hoare_i = prove
 (`!tids.
   (!l ienv e.
      TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
        (\st. prim_tids T tids /\ inf_set_tids_ienv tids ienv)
        (infer_e l ienv e) (\t st. inf_set_tids_subset tids t)) /\
   (!l ienv es.
      TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
        (\st. prim_tids T tids /\ inf_set_tids_ienv tids ienv)
        (infer_es l ienv es) (\ts st. ALL (inf_set_tids_subset tids) ts)) /\
   (!l ienv pes t1 t2.
      TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
        (\st. prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
              inf_set_tids_subset tids t1 /\ inf_set_tids_subset tids t2)
        (infer_pes l ienv pes t1 t2) (\v st. T)) /\
   (!l ienv funs.
      TYSYS2AUX_hoare (TYSYS2AUX_gt tids) TYSYS2AUX_nle
        (\st. prim_tids T tids /\ inf_set_tids_ienv tids ienv)
        (infer_funs l ienv funs)
        (\ts st. ALL (inf_set_tids_subset tids) ts))`,
  GEN_TAC THEN MATCH_MP_TAC infer_e_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY(DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[])) THEN
  REWRITE_TAC[infer_e_def; TYSYS2AUX_ignore_bind_eq] THEN
  TYSYS2AUX_VCG_TAC TYSYS2AUX_SI_PRIMS TYSYS2AUX_SI_CLOSER);;

let infer_e_inf_set_tids = prove
 (`!tids.
   (!l cenv p st t st'.
      infer_e l cenv p st = (M_success t,st')
      ==> prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
          inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs (infer_st_subst st)
          ==> inf_set_tids_subset tids t /\
              inf_set_tids_subst tids (infer_st_subst st')) /\
   (!l cenv ps st ts st'.
      infer_es l cenv ps st = (M_success ts,st')
      ==> prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
          inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs (infer_st_subst st)
          ==> ALL (inf_set_tids_subset tids) ts /\
              inf_set_tids_subst tids (infer_st_subst st')) /\
   (!l cenv ps t1 t2 st st'.
      infer_pes l cenv ps t1 t2 st = (M_success one,st')
      ==> prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
          inf_set_tids_subst tids (infer_st_subst st) /\
          inf_set_tids_subset tids t1 /\ inf_set_tids_subset tids t2 /\
          t_wfs (infer_st_subst st)
          ==> inf_set_tids_subst tids (infer_st_subst st')) /\
   (!l cenv funs st ts st'.
      infer_funs l cenv funs st = (M_success ts,st')
      ==> prim_tids T tids /\ inf_set_tids_ienv tids cenv /\
          inf_set_tids_subst tids (infer_st_subst st) /\ t_wfs (infer_st_subst st)
          ==> ALL (inf_set_tids_subset tids) ts /\
              inf_set_tids_subst tids (infer_st_subst st'))`,
  GEN_TAC THEN MP_TAC(SPEC `tids:num->bool` TYSYS2AUX_infer_e_hoare_i) THEN
  REWRITE_TAC[TYSYS2AUX_hoare_def; TYSYS2AUX_gt_def] THEN MESON_TAC[]);;

let generalise_inf_set_tids = prove
 (`(!d a b c e f g. generalise a b c d = (e,f,g) ==> inf_set_tids g = inf_set_tids d) /\
   (!d a b c e f g. generalise_list a b c d = (e,f,g)
                    ==> ALL2 (inv_image (=) inf_set_tids) d g)`,
  REWRITE_TAC[inv_image] THEN MATCH_MP_TAC infer_t_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[generalise_def; PAIR_EQ] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def] THEN
    X_CHOOSE_THEN `g1:num` (X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN
      `ts1:infer_t list` ASSUME_TAC))
      (ISPEC `generalise_list a b c (a0:infer_t list)` BASICAUX_TUPLE3) THEN
    ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[inf_set_tids_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`; `c:(num,num)fmap`; `g1:num`;
                                  `s1:(num,num)fmap`; `ts1:infer_t list`] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP MAP_EQ_ALL2) THEN
    REWRITE_TAC[];
    X_GEN_TAC `uv:num` THEN REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def] THEN
    CASES_ON `FLOOKUP (c:(num,num)fmap) uv` THEN CASE_REWRITE_TAC[] THEN
    TRY COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[inf_set_tids_def];
    REWRITE_TAC[generalise_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ALL2];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[generalise_def] THEN
    X_CHOOSE_THEN `g1:num` (X_CHOOSE_THEN `s1:(num,num)fmap` (X_CHOOSE_THEN
      `t1:infer_t` ASSUME_TAC))
      (ISPEC `generalise a b c (a0:infer_t)` BASICAUX_TUPLE3) THEN
    X_CHOOSE_THEN `g2:num` (X_CHOOSE_THEN `s2:(num,num)fmap` (X_CHOOSE_THEN
      `ts2:infer_t list` ASSUME_TAC))
      (ISPEC `generalise_list a (g1 + b) s1 (a1:infer_t list)` BASICAUX_TUPLE3) THEN
    ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ALL2] THEN
    ASM_MESON_TAC[]]);;

let start_type_id_prim_tids_count = prove
 (`!n. start_type_id <= n ==> prim_tids T (count n)`,
  REWRITE_TAC[prim_tids_def; prim_type_nums_def; start_type_id_def; ALL; IN_COUNT;
              typeSystem_Tarray_num_def; typeSystem_Tbool_num_def; typeSystem_Tchar_num_def;
              typeSystem_Texn_num_def; typeSystem_Tfn_num_def; typeSystem_Tint_num_def;
              typeSystem_Tlist_num_def; typeSystem_Tref_num_def; typeSystem_Tstring_num_def;
              typeSystem_Ttup_num_def; typeSystem_Tvector_num_def;
              typeSystem_Tword64_num_def; typeSystem_Tword8_num_def;
              typeSystem_Tword8array_num_def; typeSystem_Tdouble_num_def] THEN
  ARITH_TAC);;

let inf_set_tids_subst_FEMPTY = prove
 (`!tids. inf_set_tids_subst tids (FEMPTY:(num,infer_t)fmap)`,
  REWRITE_TAC[inf_set_tids_subst_def; FRANGE_FEMPTY; NOT_IN_EMPTY]);;
let _ = cake_add_simps [inf_set_tids_subst_FEMPTY];;

let build_ctor_tenv_FOLDR = prove
 (CASE_TERM `!(tenvT:(mlstring,mlstring,mlstring list#t)namespace)
              (tds:(C#D#(B#ast_t list)list)list) (ids:E list).
     LENGTH tds = LENGTH ids
     ==> build_ctor_tenv tenvT tds ids =
         ITLIST (flip nsAppend)
           (MAP (alist_to_ns o REVERSE)
              (MAP2 (\x id. match x with
                              (tvs,tn,ctors) ->
                                MAP (\cnts. match cnts with
                                              (cn,ts) ->
                                                (cn,(tvs,MAP (type_name_subst tenvT) ts,id)))
                                    ctors)
                    tds ids))
           (alist_to_ns []:(A,B,C#t list#E)namespace)`,
  MATCH_MP_TAC build_ctor_tenv_ind THEN
  REWRITE_TAC[build_ctor_tenv_def; LENGTH; NOT_SUC; SUC_INJ; MAP2; MAP; ITLIST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[o_THM; flip_DEF]);;

let build_ctor_tenv_FOLDL = prove
 (CASE_TERM `!(tenvT:(mlstring,mlstring,mlstring list#t)namespace)
              (tds:(C#D#(B#ast_t list)list)list) (ids:E list).
     LENGTH tds = LENGTH ids
     ==> build_ctor_tenv tenvT tds ids =
         FOLDL nsAppend (alist_to_ns []:(A,B,C#t list#E)namespace)
           (REVERSE
              (MAP (alist_to_ns o REVERSE)
                 (MAP2 (\x id. match x with
                                 (tvs,tn,ctors) ->
                                   MAP (\cnts. match cnts with
                                                 (cn,ts) ->
                                                   (cn,(tvs,MAP (type_name_subst tenvT) ts,id)))
                                       ctors)
                       tds ids)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[build_ctor_tenv_FOLDR; FOLDL_FOLDR_REVERSE; REVERSE_REVERSE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; flip_DEF]);;

let nsMap_FOLDL_nsAppend = prove
 (`!(f:V->W) ls (ns:(M,N,V)namespace).
     nsMap f (FOLDL nsAppend ns ls) = FOLDL nsAppend (nsMap f ns) (MAP (nsMap f) ls)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; MAP; nsMap_nsAppend]);;

let nsAll_FOLDL_nsAppend = prove
 (`!P ls (ns:(M,N,V)namespace).
     nsAll P ns /\ ALL (nsAll P) ls ==> nsAll P (FOLDL nsAppend ns ls)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; ALL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[nsAll_nsAppend]);;

(* ---------- infer_d_inf_set_tids: helper lemmas ---------- *)

let TYSYS2AUX_sti_mono = prove
 (`!tids1 tids2 ienv.
     tids1 SUBSET tids2 /\ inf_set_tids_ienv tids1 ienv ==> inf_set_tids_ienv tids2 ienv`,
  REWRITE_TAC[inf_set_tids_ienv_def; nsAll_def; FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[inf_set_tids_subset_def; GSYM ALL_MEM] THEN
  MESON_TAC[SUBSET_TRANS; SUBSET]);;

let TYSYS2AUX_sti_extend = prove
 (`!tids a b.
     inf_set_tids_ienv tids a /\ inf_set_tids_ienv tids b
     ==> inf_set_tids_ienv tids (extend_dec_ienv a b)`,
  REWRITE_TAC[inf_set_tids_ienv_def; extend_dec_ienv_def; inf_env_INFO.ri_accessors] THEN
  MESON_TAC[nsAll_nsAppend]);;

let TYSYS2AUX_sti_lift = prove
 (`!tids mn ienv. inf_set_tids_ienv tids ienv ==> inf_set_tids_ienv tids (lift_ienv mn ienv)`,
  REWRITE_TAC[inf_set_tids_ienv_def; lift_ienv_def; inf_env_INFO.ri_accessors;
              nsAll_nsLift] THEN
  BETA_TAC THEN MESON_TAC[]);;

let TYSYS2AUX_sti_empty = prove
 (`!tids. inf_set_tids_ienv tids (inf_env_REC nsEmpty nsEmpty nsEmpty)`,
  REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accessors; nsAll_nsEmpty]);;

let TYSYS2AUX_sti_alist_zip = prove
 (`!tids (xs:mlstring list) ts n.
     LENGTH xs = LENGTH ts /\ ALL (inf_set_tids_subset tids) ts
     ==> inf_set_tids_ienv tids
           (inf_env_REC (alist_to_ns (ZIP xs (MAP (\t. (n,t)) ts))) nsEmpty nsEmpty)`,
  REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ts:infer_t list`,`ts:infer_t list`) THEN
  SPEC_TAC(`xs:mlstring list`,`xs:mlstring list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP; ALL] THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_sti_alist_map2 = prove
 (CASE_TERM `!tids (funs:(mlstring#mlstring#exp)list) ts n.
     LENGTH funs = LENGTH ts /\ ALL (inf_set_tids_subset tids) ts
     ==> inf_set_tids_ienv tids
           (inf_env_REC
              (alist_to_ns (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(n,t))) funs ts))
              nsEmpty nsEmpty)`,
  REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ts:infer_t list`,`ts:infer_t list`) THEN
  SPEC_TAC(`funs:(mlstring#mlstring#exp)list`,`funs:(mlstring#mlstring#exp)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; ALL] THEN
  X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `x:mlstring` (X_CHOOSE_THEN `e:exp`
    SUBST_ALL_TAC)) (ISPEC `h:mlstring#mlstring#exp` BASICAUX_TUPLE3) THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_generalise_tids = prove
 (`!tids a b c ts e f ts'.
     generalise_list a b c ts = (e,f,ts') /\ ALL (inf_set_tids_subset tids) ts
     ==> ALL (inf_set_tids_subset tids) ts'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MAP_EQ_ALL2 o REWRITE_RULE[inv_image] o
                MATCH_MP (CONJUNCT2 generalise_inf_set_tids)) THEN
  SUBGOAL_THEN `!l. ALL (inf_set_tids_subset tids) l <=>
                    ALL (\s. s SUBSET tids) (MAP inf_set_tids l)`
    (fun th -> RULE_ASSUM_TAC(ONCE_REWRITE_RULE[th]) THEN ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ALL_MAP; o_DEF] THEN REWRITE_TAC[GSYM inf_set_tids_subset_def; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let TYSYS2AUX_sti_build_ctor = prove
 (CASE_TERM `!tids (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
              (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) (ids:num list).
     prim_tids T tids /\
     nsAll (\i p. match p with (ls,t) -> set_tids_subset tids t) tenvT /\
     check_ctor_tenv tenvT tdefs /\ ALL (\i. i IN tids) ids
     ==> nsAll (\i p. match p with
                        (ls,ts,tid) ->
                          ALL (\t. inf_set_tids_subset tids (unconvert_t t)) ts /\ tid IN tids)
           (build_ctor_tenv tenvT tdefs ids:(mlstring,mlstring,mlstring list#t list#num)namespace)`,
  GEN_TAC THEN MATCH_MP_TAC build_ctor_tenv_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[build_ctor_tenv_def] THEN
  TRY(MATCH_MP_TAC nsAll_alist_to_ns THEN REWRITE_TAC[ALL] THEN NO_TAC) THEN
  REWRITE_TAC[check_ctor_tenv_def; ALL] THEN STRIP_TAC THEN
  MATCH_MP_TAC nsAll_nsAppend THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_REVERSE; MEM_MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `x:mlstring#mlstring list#t list#num` THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`cn:mlstring`; `ts:ast_t list`] THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[MEM_MAP; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_unconvert; GSYM set_tids_subset_def] THEN
  MATCH_MP_TAC set_tids_subset_type_name_subst THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(cn:mlstring,ts:ast_t list)`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let TYSYS2AUX_sti_tdefs = prove
 (CASE_TERM `!tids (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) (ids:num list).
     LENGTH tdefs = LENGTH ids /\ ALL (\i. i IN tids) ids
     ==> nsAll (\i p. match p with (ls,t) -> set_tids_subset tids t)
           (alist_to_ns
              (MAP2 (\tvtnc i. match tvtnc with (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                    tdefs ids)
            :(mlstring,mlstring,mlstring list#t)namespace)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN BETA_TAC THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ids:num list`,`ids:num list`) THEN
  SPEC_TAC(`tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`,
           `tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; ALL] THEN
  X_CHOOSE_THEN `tvs:mlstring list` (X_CHOOSE_THEN `tn:mlstring`
    (X_CHOOSE_THEN `ctors:(mlstring#ast_t list)list` SUBST_ALL_TAC))
    (ISPEC `h:mlstring list#mlstring#(mlstring#ast_t list)list` BASICAUX_TUPLE3) THEN
  REPEAT STRIP_TAC THENL
   [CASE_REWRITE_TAC[set_tids_subset_def; set_tids_def; INSERT_SUBSET; GSYM MAP_o;
                     o_DEF; UNIONS_SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[EMPTY_SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let TYSYS2AUX_sti_dtype = prove
 (CASE_TERM `!tids ienv (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list)
              (ids:num list).
     prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
     LENGTH tdefs = LENGTH ids /\ ALL (\i. i IN tids) ids /\
     check_ctor_tenv
       (nsAppend
          (alist_to_ns
             (MAP2 (\tvtnc i. match tvtnc with (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                   tdefs ids))
          (inf_env_inf_t ienv)) tdefs
     ==> inf_set_tids_ienv tids
           (inf_env_REC nsEmpty
              (build_ctor_tenv
                 (nsAppend
                    (alist_to_ns
                       (MAP2 (\tvtnc i. match tvtnc with
                                          (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                             tdefs ids))
                    (inf_env_inf_t ienv)) tdefs ids)
              (alist_to_ns
                 (MAP2 (\tvtnc i. match tvtnc with (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                       tdefs ids)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM `nsAll (\i p. match p with (ls,t) -> set_tids_subset tids t)
                  (inf_env_inf_t ienv)`) ASSUME_TAC THENL
   [UNDISCH_TAC `inf_set_tids_ienv tids ienv` THEN
    REWRITE_TAC[inf_set_tids_ienv_def; inf_set_tids_subset_def; inf_set_tids_unconvert;
                GSYM set_tids_subset_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tids:num->bool`; `tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                `ids:num list`] TYSYS2AUX_sti_tdefs) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accessors; nsAll_nsEmpty] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[inf_set_tids_subset_def; inf_set_tids_unconvert; GSYM set_tids_subset_def] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC TYSYS2AUX_sti_build_ctor THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[]]);;

let TYSYS2AUX_dlet_tids = prove
 (`!tids l ienv e p st1 t1 st4 t2 env' st5 s.
     prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
     infer_e l ienv e (init_infer_state st1) = (M_success t1,st4) /\
     infer_p l ienv p st4 = (M_success (t2,env'),st5) /\
     t_unify (infer_st_subst st5) t1 t2 = SOME s
     ==> ALL (inf_set_tids_subset tids) (MAP (t_walkstar s) (MAP SND env'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st1:infer_st` init_infer_state_wfs) THEN STRIP_TAC THEN
  SUBGOAL_THEN `inf_set_tids_subst tids (infer_st_subst (init_infer_state st1))`
    ASSUME_TAC THENL
   [REWRITE_TAC[init_infer_state_subst; inf_set_tids_subst_FEMPTY]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:loc_err_info`; `ienv:inf_env`; `e:exp`; `init_infer_state st1`;
                `t1:infer_t`; `st4:infer_st`]
           (CONJUNCT1 (SPEC `tids:num->bool` infer_e_inf_set_tids))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st4)` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_wfs]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:loc_err_info`; `ienv:inf_env`; `p:pat`; `st4:infer_st`;
                `t2:infer_t`; `env':(mlstring#infer_t)list`; `st5:infer_st`]
           (CONJUNCT1 (SPEC `tids:num->bool` infer_p_inf_set_tids))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st5)` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_p_wfs]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tids:num->bool` o MATCH_MP TYSYS2AUX_st_step o
                check (fun th -> is_eq(concl th) &&
                  (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "t_unify"
                   with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ALL (inf_set_tids_subset tids o SND) (env':(mlstring#infer_t)list)` THEN
  REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
  X_GEN_TAC `x:mlstring#infer_t` THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC t_walkstar_set_tids THEN
  MAP_EVERY EXISTS_TAC [`s:(num,infer_t)fmap`; `SND (x:mlstring#infer_t)`] THEN
  ASM_REWRITE_TAC[]);;

let TYSYS2AUX_dletrec_tids = prove
 (CASE_TERM `!tids l ienv (funs:(mlstring#mlstring#exp)list) st0 ts st7 st2.
     prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
     infer_funs l
       (inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs
                         (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv)
       funs st0 = (M_success ts,st7) /\
     infer_st_subst st0 = FEMPTY /\ LENGTH funs = LENGTH ts /\
     pure_add_constraints (infer_st_subst st7)
       (ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))) ts) (infer_st_subst st2)
     ==> ALL (inf_set_tids_subset tids)
           (MAP (t_walkstar (infer_st_subst st2))
                (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (CASE_TERM `ienv' = inf_env_inf_v_fupd
          (K (nsAppend
                (alist_to_ns
                   (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar)))
                         (funs:(mlstring#mlstring#exp)list)
                         (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH funs)))))
                (inf_env_inf_v ienv))) ienv`) THEN
  SUBGOAL_THEN `inf_set_tids_ienv tids ienv'` ASSUME_TAC THENL
   [EXPAND_TAC "ienv'" THEN MATCH_MP_TAC TYSYS2AUX_sti_letrec THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST; TYSYS2AUX_inf_set_tids_subset_uvars];
    ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st0) /\ inf_set_tids_subst tids (infer_st_subst st0)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[t_wfs_FEMPTY; inf_set_tids_subst_FEMPTY]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:loc_err_info`; `ienv':inf_env`; `funs:(mlstring#mlstring#exp)list`;
                `st0:infer_st`; `ts:infer_t list`; `st7:infer_st`]
           (CONJUNCT2(CONJUNCT2(CONJUNCT2 (SPEC `tids:num->bool` infer_e_inf_set_tids))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st7)` ASSUME_TAC THENL
   [ASM_MESON_TAC[infer_e_wfs]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list)))) =
                LENGTH (ts:infer_t list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `t_wfs (infer_st_subst st2) /\ inf_set_tids_subst tids (infer_st_subst st2)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[pure_add_constraints_wfs];
      MATCH_MP_TAC pure_add_constraints_set_tids THEN
      MAP_EVERY EXISTS_TAC
       [`infer_st_subst st7`;
        `ZIP (MAP (\n. Infer_Tuvar n) (COUNT_LIST (LENGTH (funs:(mlstring#mlstring#exp)list))))
             (ts:infer_t list)`] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th]) THEN
      ASM_REWRITE_TAC[TYSYS2AUX_inf_set_tids_subset_uvars]];
    ALL_TAC] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC t_walkstar_set_tids THEN
  MAP_EVERY EXISTS_TAC [`infer_st_subst st2`; `Infer_Tuvar x`] THEN
  ASM_REWRITE_TAC[TYSYS2AUX_inf_set_tids_subset_eqn]);;

let TYSYS2AUX_sti_mono_le = prove
 (`!a b ienv. a <= b /\ inf_set_tids_ienv (count a) ienv ==> inf_set_tids_ienv (count b) ienv`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYSYS2AUX_sti_mono THEN
  EXISTS_TAC `count a` THEN ASM_REWRITE_TAC[SUBSET; IN_COUNT] THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let TYSYS2AUX_sti_tns = prove
 (`!tids ienv t.
     prim_tids T tids /\ inf_set_tids_ienv tids ienv /\
     check_type_names (inf_env_inf_t ienv) t
     ==> inf_set_tids (unconvert_t (type_name_subst (inf_env_inf_t ienv) t)) SUBSET tids`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[inf_set_tids_unconvert; GSYM set_tids_subset_def] THEN
  MATCH_MP_TAC set_tids_subset_type_name_subst THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inf_set_tids_ienv tids ienv` THEN
  REWRITE_TAC[inf_set_tids_ienv_def; inf_set_tids_subset_def; inf_set_tids_unconvert;
              GSYM set_tids_subset_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let TYSYS2AUX_DLET_TIDS_TAC : tactic = fun (asl,w as g) ->
  let a_ienv = TYSYS2AUX_asm_head asl "inf_set_tids_ienv"
  and a_e = TYSYS2AUX_asm_head asl "infer_e" and a_p = TYSYS2AUX_asm_head asl "infer_p"
  and a_u = TYSYS2AUX_asm_head asl "t_unify" and a_g = TYSYS2AUX_asm_head asl "generalise_list"
  and a_le = TYSYS2AUX_asm_head asl "<=" in
  let pt = MATCH_MP start_type_id_prim_tids_count a_le in
  let ids1 = MATCH_MP (CONJUNCT1 infer_e_next_id_const) a_e in
  let ids2 = MATCH_MP (CONJUNCT1 infer_p_next_id_const) a_p in
  let f = MATCH_MP TYSYS2AUX_dlet_tids (end_itlist CONJ [pt; a_ienv; a_e; a_p; a_u]) in
  let gt = MATCH_MP TYSYS2AUX_generalise_tids (CONJ a_g f) in
  let ln = REWRITE_RULE[LENGTH_MAP] (MATCH_MP generalise_list_length a_g) in
  (REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM; GSYM ids2; GSYM ids1;
                init_infer_state_def] THEN
   MATCH_MP_TAC TYSYS2AUX_sti_alist_zip THEN REWRITE_TAC[LENGTH_MAP; ln; gt]) g;;

let TYSYS2AUX_DLETREC_TIDS_TAC : tactic = fun (asl,w as g) ->
  let a_ienv = TYSYS2AUX_asm_head asl "inf_set_tids_ienv"
  and a_f = TYSYS2AUX_asm_head asl "infer_funs" and a_len = TYSYS2AUX_asm_head asl "LENGTH"
  and a_nid = TYSYS2AUX_asm_head asl "infer_st_next_id"
  and a_pac = TYSYS2AUX_asm_head asl "pure_add_constraints"
  and a_g = TYSYS2AUX_asm_head asl "generalise_list"
  and a_le = TYSYS2AUX_asm_head asl "<=" in
  let pt = MATCH_MP start_type_id_prim_tids_count a_le in
  let len = REWRITE_RULE[LENGTH_MAP; LENGTH_COUNT_LIST] a_len in
  let st0 = rand(lhs(concl a_f)) in
  let st0s = EQT_ELIM(REWRITE_CONV[infer_st_rewrs; init_infer_state_subst]
               (mk_eq(mk_comb(`infer_st_subst`,st0), `FEMPTY:(num,infer_t)fmap`))) in
  let f = MATCH_MP TYSYS2AUX_dletrec_tids (end_itlist CONJ [pt; a_ienv; a_f; st0s; len; a_pac]) in
  let gt = MATCH_MP TYSYS2AUX_generalise_tids (CONJ a_g f) in
  let ln = REWRITE_RULE[LENGTH_MAP; LENGTH_COUNT_LIST] (MATCH_MP generalise_list_length a_g) in
  let ids = MATCH_MP (CONJUNCT2(CONJUNCT2(CONJUNCT2 infer_e_next_id_const))) a_f in
  (REWRITE_TAC[GSYM a_nid] THEN REWRITE_TAC[GSYM ids] THEN
   REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM; init_infer_state_def] THEN
   MATCH_MP_TAC TYSYS2AUX_sti_alist_map2 THEN REWRITE_TAC[ln; gt]) g;;

let TYSYS2AUX_DTYPE_TIDS_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "n_fresh_id"
     with Failure _ -> false))) THEN
  REWRITE_TAC[n_fresh_id_def; PAIR_EQ; injectivity "exc"] THEN STRIP_TAC THEN
  TYSYS2AUX_SUBST_VARS_TAC THEN REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC TYSYS2AUX_sti_dtype THEN ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC start_type_id_prim_tids_count THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `infer_st_next_id st` THEN ASM_REWRITE_TAC[LE_ADD];
    MATCH_MP_TAC TYSYS2AUX_sti_mono_le THEN
    EXISTS_TAC `infer_st_next_id st` THEN ASM_REWRITE_TAC[LE_ADD];
    REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ; IN_COUNT] THEN ARITH_TAC];;

let infer_d_inf_set_tids = prove
 (`(!d ienv st ienv' st'.
      infer_d ienv d st = (M_success ienv',st') /\
      start_type_id <= infer_st_next_id st /\
      inf_set_tids_ienv (count (infer_st_next_id st)) ienv
      ==> inf_set_tids_ienv (count (infer_st_next_id st')) ienv') /\
   (!ds ienv st ienv' st'.
      infer_ds ienv ds st = (M_success ienv',st') /\
      start_type_id <= infer_st_next_id st /\
      inf_set_tids_ienv (count (infer_st_next_id st)) ienv
      ==> inf_set_tids_ienv (count (infer_st_next_id st')) ienv')`,
  SUBGOAL_THEN
   `(!ienv d st ienv' st'.
      infer_d ienv d st = (M_success ienv',st') /\
      start_type_id <= infer_st_next_id st /\
      inf_set_tids_ienv (count (infer_st_next_id st)) ienv
      ==> inf_set_tids_ienv (count (infer_st_next_id st')) ienv') /\
    (!ienv ds st ienv' st'.
      infer_ds ienv ds st = (M_success ienv',st') /\
      start_type_id <= infer_st_next_id st /\
      inf_set_tids_ienv (count (infer_st_next_id st)) ienv
      ==> inf_set_tids_ienv (count (infer_st_next_id st')) ienv')`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC infer_d_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[infer_d_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE;
              TYSYS2AUX_ignore_bind_eq; init_state_def] THEN
  REPEAT STRIP_TAC THEN TYSYS2AUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[init_infer_state_next_uvar; infer_st_rewrs; ADD_CLAUSES]) THENL
   [TYSYS2AUX_DLET_TIDS_TAC; TYSYS2AUX_DLET_TIDS_TAC; TYSYS2AUX_DLETREC_TIDS_TAC;
    TYSYS2AUX_DTYPE_TIDS_TAC;
    (* Dtabbrev *)
    REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accessors; nsAll_nsEmpty;
                nsAll_nsSing] THEN
    CASE_REWRITE_TAC[inf_set_tids_subset_def] THEN
    MATCH_MP_TAC TYSYS2AUX_sti_tns THEN ASM_SIMP_TAC[start_type_id_prim_tids_count];
    (* Dexn *)
    REWRITE_TAC[inf_set_tids_ienv_def; inf_env_INFO.ri_accessors; nsAll_nsEmpty;
                nsAll_nsSing] THEN
    CASE_REWRITE_TAC[inf_set_tids_subset_def; ALL_MAP; o_DEF] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TYSYS2AUX_prim_tids_T_all o
                MATCH_MP start_type_id_prim_tids_count o
                check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "<="
                                 with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TYSYS2AUX_sti_tns THEN
    ASM_SIMP_TAC[start_type_id_prim_tids_count];
    (* Dmod *)
    ASM_MESON_TAC[TYSYS2AUX_sti_lift];
    (* Dlocal *)
    ASM_MESON_TAC[infer_d_next_id_mono; TYSYS2AUX_sti_mono_le; TYSYS2AUX_sti_extend; LE_TRANS];
    (* [] *)
    REWRITE_TAC[TYSYS2AUX_sti_empty];
    (* CONS *)
    ASM_MESON_TAC[infer_d_next_id_mono; TYSYS2AUX_sti_mono_le; TYSYS2AUX_sti_extend;
                  LE_TRANS]]);;

let TYSYS2AUX_init_uvar_wfs = prove
 (`!st n. t_wfs (infer_st_subst (infer_st_next_uvar_fupd (K n) (init_infer_state st)))`,
  REWRITE_TAC[infer_st_rewrs; init_infer_state_wfs]);;

let infer_d_wfs = prove
 (`(!d ienv st ienv' st'.
      infer_d ienv d st = (M_success ienv',st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st')) /\
   (!ds ienv st ienv' st'.
      infer_ds ienv ds st = (M_success ienv',st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st'))`,
  SUBGOAL_THEN
   `(!ienv d st ienv' st'.
      infer_d ienv d st = (M_success ienv',st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st')) /\
    (!ienv ds st ienv' st'.
      infer_ds ienv ds st = (M_success ienv',st') /\ t_wfs (infer_st_subst st)
      ==> t_wfs (infer_st_subst st'))`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC infer_d_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[infer_d_def; success_eqns; PAIR_EQ; EXISTS_PAIR_THM; pair_CASE;
              TYSYS2AUX_ignore_bind_eq; init_state_def] THEN
  REPEAT STRIP_TAC THEN TYSYS2AUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[init_infer_state_next_uvar; infer_st_rewrs; ADD_CLAUSES]) THEN
  REWRITE_TAC[infer_st_rewrs; infer_st_INFO.ri_accfupds; K_THM] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "n_fresh_id"
         with Failure _ -> false))) THEN
      REWRITE_TAC[n_fresh_id_def; PAIR_EQ] THEN STRIP_TAC THEN
      TYSYS2AUX_SUBST_VARS_TAC THEN
      ASM_REWRITE_TAC[infer_st_INFO.ri_accfupds; K_THM] THEN NO_TAC) THEN
  ASM_MESON_TAC[infer_e_wfs; infer_p_wfs; t_unify_wfs; pure_add_constraints_wfs;
                init_infer_state_wfs; TYSYS2AUX_init_uvar_wfs]);;
