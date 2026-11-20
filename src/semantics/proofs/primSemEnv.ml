(* ========================================================================= *)
(* primSemEnv: port of HOL4 semantics/proofs/primSemEnvScript.sml            *)
(* (CakeML v3479).  Proof about the primitive semantic environment.          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/typeSysProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Ancestors also list semantics; no name of it is used here, so   *)
(*   semantics/semantics.ml is not loaded.                                   *)
(* - The mlstring literal of x is implode "x"; record literals are written  *)
(*   with their constructors (state_REC, sem_env_REC); {a; b} is {a, b}.    *)
(* - prim_sem_env_eq is computed, as HOL4's EVAL computes it: the            *)
(*   definitions are unfolded, evaluate_decs is run on the declarations of  *)
(*   prim_types_program, and the namespaces are left as Bind lists.          *)
(* ------------------------------------------------------------------------- *)

(* HOL4: EVAL ``prim_sem_env (ffi:'ffi ffi_state)``; the same computation: *)
(* unfolding of the definitions, evaluate_decs on the declarations, and   *)
(* the namespaces written with Bind, as EVAL leaves them                   *)
let prim_sem_env_eq =
  let th1 = REWRITE_CONV[prim_sem_env_def; add_to_sem_env_def; prim_types_program_def]
              `prim_sem_env (ffi:(FFI)ffi_state)` in
  let th2 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV
              [evaluate_decs_def; fix_clock_def; combine_dec_result_def;
               extend_dec_env_def; check_dup_ctors_def; build_tdefs_def;
               build_constrs_def; injectivity "char"])) th1 in
  CONV_RULE (RAND_CONV (REWRITE_CONV[nsBind_def; nsSing_def; nsEmpty_def])) th2;;

(* HOL4's statement has ffi free *)
let prim_type_sound_invariants = prove
 (`!type_ids sem_st prim_env.
     (sem_st,prim_env) = THE (prim_sem_env (ffi:(FFI)ffi_state)) /\
     DISJOINT type_ids {Tlist_num, Tbool_num, Texn_num}
     ==> ?ctMap. type_sound_invariant sem_st prim_env ctMap FEMPTY type_ids prim_tenv /\
                 FRANGE ((SND o SND) o_f ctMap) SUBSET prim_type_ids`,
  let TYNUMS = [typeSystem_Tarray_num_def; typeSystem_Tbool_num_def;
    typeSystem_Tchar_num_def; typeSystem_Texn_num_def; typeSystem_Tfn_num_def;
    typeSystem_Tint_num_def; typeSystem_Tlist_num_def; typeSystem_Tref_num_def;
    typeSystem_Tstring_num_def; typeSystem_Ttup_num_def; typeSystem_Tvector_num_def;
    typeSystem_Tword64_num_def; typeSystem_Tword8_num_def;
    typeSystem_Tword8array_num_def; typeSystem_Tdouble_num_def] in
  let STAMPS = [bind_stamp_def; div_stamp_def; chr_stamp_def; subscript_stamp_def;
                list_type_num_def; bool_type_num_def] in
  let FRANGE_TAC =
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP TPROPSAUX_FRANGE_fupdate_list) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_REVERSE; MEM; PAIR_EQ] THEN STRIP_TAC THEN GVS[] in
  REWRITE_TAC[type_sound_invariant_def; prim_sem_env_eq; THE_DEF; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC (rand `x = FEMPTY |++ REVERSE
     [(bind_stamp, ([]:mlstring list,[]:t list,Texn_num));
      (div_stamp, ([],[],Texn_num));
      (chr_stamp, ([],[],Texn_num));
      (subscript_stamp, ([],[],Texn_num));
      (TypeStamp (implode "[]") list_type_num, ([implode "'a"],[],Tlist_num));
      (TypeStamp (implode "::") list_type_num,
         ([implode "'a"],[Tvar (implode "'a"); Tlist (Tvar (implode "'a"))], Tlist_num));
      (TypeStamp (implode "True") bool_type_num, ([],[], Tbool_num));
      (TypeStamp (implode "False") bool_type_num, ([],[], Tbool_num))]`) THEN
  REPEAT CONJ_TAC THENL
   [(* tenv_ok *)
    REWRITE_TAC[tenv_ok_def; prim_tenv_def; type_env_INFO.ri_accessors;
                tenv_val_ok_nsEmpty; tenv_ctor_ok_def; tenv_abbrev_ok_def] THEN
    CONJ_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
    SIMP_NOASM[REVERSE; ALL; check_freevars_def; MEM; injectivity "char"];
    (* good_ctMap *)
    REWRITE_TAC([good_ctMap_def; ctMap_ok_def; ctMap_has_bools_def; ctMap_has_exns_def;
                 ctMap_has_lists_def; FEVERY_ALL_FLOOKUP; flookup_fupdate_list;
                 REVERSE_REVERSE; FLOOKUP_EMPTY; SPTAUX_optcase_lemma;
                 ALOOKUP_THM] @ STAMPS) THEN
    REPEAT CONJ_TAC THEN
    TPROPSAUX_RW([COND_CASE_EQ; injectivity "char"; prim_type_nums_def; same_type_def;
                  check_freevars_def; MEM] @ TYNUMS);
    (* consistent_ctMap *)
    REWRITE_TAC([consistent_ctMap_def; FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY;
                 MAP; REVERSE; APPEND; IN_SET_OF_LIST; MEM; state_INFO.ri_accessors] @
                STAMPS) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_DISJOINT; NOT_EXISTS_THM] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TPROPSAUX_FRANGE_fupdate_list) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
      REWRITE_TAC[MEM_REVERSE; MEM; PAIR_EQ] THEN STRIP_TAC THEN
      GVS[] THEN FS[IN_DISJOINT; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      TPROPSAUX_RW[injectivity "char"] THEN ARITH_TAC];
    (* type_all_env *)
    REWRITE_TAC[type_all_env_def; prim_tenv_def; type_env_INFO.ri_accessors;
                sem_env_INFO.ri_accessors; alist_to_ns_def; REVERSE; APPEND] THEN
    REWRITE_TAC[GSYM nsBind_def; GSYM nsEmpty_def] THEN CONJ_TAC THENL
     [REPEAT (MATCH_MP_TAC nsAll2_nsBind THEN CONJ_TAC) THEN
      REWRITE_TAC[nsAll2_nsEmpty] THEN
      REWRITE_TAC([type_ctor_def; flookup_fupdate_list; FLOOKUP_EMPTY; ALOOKUP_THM;
                   REVERSE; APPEND; SPTAUX_optcase_lemma; LENGTH] @ STAMPS) THEN
      SIMP_NOASM[injectivity "char"];
      REWRITE_TAC[nsAll2_nsEmpty]];
    (* type_s *)
    REWRITE_TAC[type_s_def; state_INFO.ri_accessors; FLOOKUP_EMPTY; store_lookup_def;
                LENGTH; LT; option_DISTINCT; NOT_EXISTS_THM];
    (* the range of the constructor map *)
    REWRITE_TAC[SUBSET; prim_type_ids_def; IN_SET_OF_LIST; prim_type_nums_def; MEM] THEN
    X_GEN_TAC `x:num` THEN FRANGE_TAC]);;
