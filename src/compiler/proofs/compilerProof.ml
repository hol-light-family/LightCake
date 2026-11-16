(* ========================================================================= *)
(* compilerProof: port of HOL4 compiler/proofs/compilerProofScript.sml      *)
(* (CakeML v3479), HOL4 lines 1-306.  Prove top-level correctness theorem   *)
(* for complete compiler, i.e. the combination of parsing, type inference, *)
(* compiler backend.                                                         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as in names.tsv: compiler$compile is compiler_compile, its config *)
(*   record compiler_config (fields compiler_config_asm_config ...),        *)
(*   backend$compile backend_compile, infer$init_config infer_init_config,  *)
(*   envRel's env_rel envRel_env_rel; this script's read_limits,             *)
(*   is_safe_for_space, compile_correct_lemma and compile_correct are        *)
(*   compilerProof_read_limits ... compilerProof_compile_correct; the        *)
(*   pegresult constructors Success, Failure are peg_Success, Failure.       *)
(* - The headline statements: compile_correct_statement.ml (needs) binds   *)
(*   HOL4's two statements as the OCaml terms compile_correct_statement and  *)
(*   compile_correct_safe_for_space_statement; it also has this script's     *)
(*   definitions config_ok, read_limits and is_safe_for_space (HOL4 lines    *)
(*   15, 97, 101), which the statements use.  After                          *)
(*   compile_correct_safe_for_space and compilerProof_compile_correct a     *)
(*   check fails loudly unless the theorem has no hypotheses and its        *)
(*   conclusion is alpha-equivalent to the term.  HOL4 checks               *)
(*   compile_correct with check_thm (an ML check of the theorem).            *)
(* - HOL4 case expressions are match (HOL4 semantics: M_failure             *)
(*   (StaticError _), not covered, is ARB as in HOL4).                       *)
(* - parse_prog_correct follows from HOL4 parserProof's                      *)
(*   parse_prog_correct0 (parserProof is not ported): it is proved here as  *)
(*   CPPAUX_parse_prog_correct0, as in HOL4, with four lemmas for its       *)
(*   steps.  HOL4's EVAL steps of compile_correct_lemma are the lemmas       *)
(*   CPPAUX_prim_type_ids_count and CPPAUX_set_tids_tenv_prim_tenv.          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "semantics/semantics.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/typeSound.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "compiler/parsing/proofs/pegSound.ml";;
needs "compiler/parsing/proofs/pegComplete.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/inference/proofs/type_dCanon.ml";;
needs "compiler/inference/proofs/inferSound.ml";;
needs "compiler/inference/proofs/inferComplete.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/semantics/targetProps.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/compiler.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/proofs/compile_correct_statement.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-306 ===== *)

(* HOL4 line 13: simpset setting (diminish_srw_ss) *)

(* HOL4 line 15: config_ok_def is in compile_correct_statement.ml (the     *)
(* headline statements use it)                                               *)

(* HOL4 line 28 *)
let initial_condition_def = cake_def
  `initial_condition (st:(FFI)semantics_state) (cc:(A)compiler_config)
                     (mc:(A,B,C)machine_config) <=>
     (semantics_state_sem_st st,semantics_state_sem_env st) =
       THE (prim_sem_env (state_ffi (semantics_state_sem_st st))) /\
     (?ctMap. type_sound_invariant (semantics_state_sem_st st) (semantics_state_sem_env st)
                ctMap FEMPTY {} (semantics_state_tenv st) /\
              FRANGE ((SND o SND) o_f ctMap) SUBSET semantics_state_type_ids st) /\
     envRel_env_rel (semantics_state_tenv st) (compiler_config_inferencer_config cc) /\
     semantics_state_type_ids st = count start_type_id /\
     set_tids_tenv (count start_type_id) (semantics_state_tenv st) /\
     inf_set_tids_ienv (count start_type_id) (compiler_config_inferencer_config cc) /\
     ~compiler_config_input_is_sexp cc /\
     ~compiler_config_exclude_prelude cc /\
     ~compiler_config_skip_type_inference cc /\
     ~compiler_config_only_print_types cc /\
     ~compiler_config_only_print_sexp cc /\
     backend_config_ok (compiler_config_asm_config cc) (compiler_config_backend_config cc) /\
     mc_conf_ok mc /\
     mc_init_ok (compiler_config_asm_config cc) (compiler_config_backend_config cc) mc`;;

(* HOL4 parserProof (compiler/parsing/proofs/parserProofScript.sml, not     *)
(* ported): parse_prog_correct0, line 11, as the local helper               *)
(* CPPAUX_parse_prog_correct0, with four lemmas for its steps.              *)

(* the PEG run on the whole input succeeds with the tree of any parse *)
let CPPAUX_peg_eval_complete = prove
 (`!(s:(token#locs)list) pt r.
     peg_eval cmlPEG (s,nt (INL nTopLevelDecs) I) r /\
     valid_lptree cmlG pt /\ ptree_head pt = NT (INL nTopLevelDecs) /\
     real_fringe pt = MAP (TOK ## I) s
     ==> ?eo. r = peg_Success [] [pt] eo`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`pt:mlptree`; `nTopLevelDecs`; `s:(token#locs)list`;
                `[]:(token#locs)list`] completeness) THEN
  ASM_REWRITE_TAC[APPEND_NIL; FDOM_cmlPEG_nts] THEN
  DISCH_THEN(X_CHOOSE_TAC `eo:(locs#string)option`) THEN
  EXISTS_TAC `eo:(locs#string)option` THEN
  ASM_MESON_TAC[peg_deterministic]);;

(* a successful run on the whole input gives a parse tree *)
let CPPAUX_peg_eval_sound = prove
 (`!(s:(token#locs)list) pts eo.
     peg_eval cmlPEG (s,nt (INL nTopLevelDecs) I) (peg_Success [] pts eo)
     ==> ?pt. pts = [pt] /\ valid_lptree cmlG pt /\
              ptree_head pt = NT (INL nTopLevelDecs) /\
              real_fringe pt = MAP (TOK ## I) s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP peg_sound) THEN
  REWRITE_TAC[MAP; APPEND_NIL] THEN MESON_TAC[]);;

(* the PEG run on any input terminates *)
let CPPAUX_peg_eval_total = prove
 (`!s:(token#locs)list. ?r. peg_eval cmlPEG (s,nt (INL nTopLevelDecs) I) r`,
  GEN_TAC THEN MP_TAC (ISPEC `cmlPEG` peg_eval_total) THEN
  REWRITE_TAC[PEG_wellformed] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:(token#locs)list`;
    `nt (INL nTopLevelDecs) I:(token,MMLnonT,(mlptree)list,string)pegsym`]) THEN
  REWRITE_TAC[REWRITE_RULE[pnt_def] NTS_in_PEG_exprs]);;

(* parse_prog in terms of the result of the PEG run *)
let CPPAUX_parse_prog_exec = prove
 (CASE_TERM
  `!s:(token#locs)list r.
     peg_eval cmlPEG (s,nt (INL nTopLevelDecs) I) r
     ==> parse_prog s =
         (match destResult (Result r:(token,MMLnonT,(mlptree)list,string)evalcase)
                 :((token#locs)list,(mlptree)list,string)pegresult with
            peg_Success toks' x eo ->
              (match optlift (oHD x) toks' with
                 peg_Success toks' x eo -> optlift (ptree_TopLevelDecs x) toks'
               | Failure fl fe -> Failure fl fe)
          | Failure fl fe -> Failure fl fe)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[parse_prog_def; pegresult_bind_def; o_THM; pnt_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pegexec th]));;

(* HOL4 parserProof line 11 *)
let CPPAUX_parse_prog_correct0 = prove
 (`!s fl fe s' a eo.
     (parse_prog s = Failure fl fe ==> parse s = NONE) /\
     (parse_prog s = peg_Success s' a eo ==> parse s = SOME a /\ s' = [])`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_TAC `r:((token#locs)list,(mlptree)list,string)pegresult`
    (SPEC `s:(token#locs)list` CPPAUX_peg_eval_total) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CPPAUX_parse_prog_exec th]) THEN
  REWRITE_TAC[parse_def] THEN
  ASM_CASES_TAC
   `?pt. valid_lptree cmlG pt /\ ptree_head pt = NT (INL nTopLevelDecs) /\
         real_fringe pt = MAP (TOK ## I) (s:(token#locs)list)` THENL
   [(* a parse tree exists: it is the unique one, found by the PEG *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `pt:mlptree` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!pt2. valid_lptree cmlG pt2 /\ ptree_head pt2 = NT (INL nTopLevelDecs) /\
            real_fringe pt2 = MAP (TOK ## I) (s:(token#locs)list) <=> pt2 = pt`
     (fun th -> REWRITE_TAC[th; some_EQ]) THENL
     [GEN_TAC THEN EQ_TAC THENL
       [STRIP_TAC THEN
        MP_TAC(SPECL [`s:(token#locs)list`; `pt:mlptree`;
          `r:((token#locs)list,(mlptree)list,string)pegresult`]
          CPPAUX_peg_eval_complete) THEN
        MP_TAC(SPECL [`s:(token#locs)list`; `pt2:mlptree`;
          `r:((token#locs)list,(mlptree)list,string)pegresult`]
          CPPAUX_peg_eval_complete) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[pegresult_inject; CONS_11] THEN MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`s:(token#locs)list`; `pt:mlptree`;
      `r:((token#locs)list,(mlptree)list,string)pegresult`]
      CPPAUX_peg_eval_complete) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[destResult_def; oHD_DEF; optlift_def] THEN
    CASES_ON `ptree_TopLevelDecs pt` THEN CASE_REWRITE_TAC[optlift_def] THEN
    REWRITE_TAC[pegresult_distinct; pegresult_inject] THEN MESON_TAC[];
    (* no parse tree: parse_prog cannot succeed *)
    ASM_REWRITE_TAC[some_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(p ==> T) <=> T`; option_DISTINCT] THEN
    CASES_ON `r:((token#locs)list,(mlptree)list,string)pegresult` THEN
    CASE_REWRITE_TAC[destResult_def; pegresult_distinct] THEN
    CASES_ON `a0:(token#locs)list` THENL
     [CASE_REWRITE_TAC[destResult_def] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP CPPAUX_peg_eval_sound) THEN
      DISCH_THEN(X_CHOOSE_THEN `pt:mlptree` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPEC `a0':token#locs` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:token` (X_CHOOSE_THEN `l0:locs` SUBST_ALL_TAC)) THEN
      CASE_REWRITE_TAC[destResult_def; pegresult_distinct]]]);;

(* HOL4 line 49 *)
let parse_prog_correct = prove
 (`!s y1 y2 x1 a x2.
     (parse_prog s = Failure y1 y2 ==> parse s = NONE) /\
   (parse_prog s = peg_Success x1 a x2 ==> parse s = SOME a)`,
  MESON_TAC[CPPAUX_parse_prog_correct0]);;

(* HOL4 line 56 *)
let infertype_prog_correct = prove
 (`!st ienv p.
     envRel_env_rel (semantics_state_tenv (st:(FFI)semantics_state)) ienv /\
   semantics_state_type_ids st = count start_type_id /\
   inf_set_tids_ienv (count start_type_id) ienv /\
   set_tids_tenv (count start_type_id) (semantics_state_tenv st)
   ==> ?c' x. infertype_prog ienv p =
              (if can_type_prog st p then M_success c' else M_failure x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[infertype_prog_def] THEN
  SUBGOAL_THEN
   `infer_st_next_id (init_infer_state (infer_st_REC 0 FEMPTY start_type_id)) =
    start_type_id` ASSUME_TAC THENL
   [SIMP_NOASM[init_infer_state_def]; ALL_TAC] THEN
  MP_TAC(ISPEC `infer_ds ienv p (init_infer_state (infer_st_REC 0 FEMPTY start_type_id))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:(inf_env,locs option#mlstring)exc`
    (X_CHOOSE_TAC `st2:infer_st`)) THEN
  ASM_REWRITE_TAC[FST] THEN
  CASES_ON `res:(inf_env,locs option#mlstring)exc` THEN CASE_REWRITE_TAC[] THENL
   [(* inference succeeds: the program has a type (soundness) *)
    SUBGOAL_THEN `can_type_prog (st:(FFI)semantics_state) p` (fun th -> REWRITE_TAC[th])
    THENL [ALL_TAC; MESON_TAC[]] THEN
    REWRITE_TAC[can_type_prog_def] THEN
    MAP_EVERY EXISTS_TAC [`set_ids start_type_id (infer_st_next_id st2)`; `ienv_to_tenv a`] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[set_ids_def; DISJOINT; EXTENSION; IN_COUNT; IN_INTER; NOT_IN_EMPTY;
                      IN_ELIM_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (CONJUNCT2 infer_d_sound))) THEN
    DISCH_THEN(MP_TAC o SPEC `semantics_state_tenv (st:(FFI)semantics_state)`) THEN
    ASM_REWRITE_TAC[LE_REFL];
    (* inference fails: the program has no type (completeness) *)
    SUBGOAL_THEN `~can_type_prog (st:(FFI)semantics_state) p` (fun th -> REWRITE_TAC[th])
    THENL [ALL_TAC; MESON_TAC[]] THEN
    REWRITE_TAC[can_type_prog_def; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`ids:num->bool`; `tenv':type_env`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`semantics_state_tenv (st:(FFI)semantics_state)`; `p:dec list`;
      `ids:num->bool`; `tenv':type_env`; `ienv:inf_env`;
      `init_infer_state (infer_st_REC 0 FEMPTY start_type_id)`] infer_ds_complete) THEN
    ASM_REWRITE_TAC[LE_REFL; PAIR_EQ; distinctness "exc"] THEN
    ASM_MESON_TAC[DISJOINT_SYM]]);;

(* HOL4 line 89 *)
let compile_tap_compile = prove
 (`!asm_conf conf p res td.
     compile_tap (asm_conf:(A)asm_config) conf p = (res,td)
     ==> backend_compile asm_conf conf p = res`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[backend_passes_compile_alt; FST]);;

(* HOL4 lines 97 and 101: compilerProof_read_limits_def and               *)
(* compilerProof_is_safe_for_space_def are in compile_correct_statement.ml  *)

(* the invariant of the initial state holds for the type identifiers of a  *)
(* program that are disjoint from the initial ones                         *)
let CPPAUX_type_sound_invariant_tids = prove
 (`!(s:(FFI)state) env ctMap tenvS tenv ids tids.
     type_sound_invariant s env ctMap tenvS {} tenv /\
     FRANGE ((SND o SND) o_f ctMap) SUBSET ids /\ DISJOINT ids tids
     ==> type_sound_invariant s env ctMap tenvS tids tenv`,
  REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* HOL4 line 105 *)
let compile_correct_gen = prove
 (CASE_TERM
  `!(st:(FFI)semantics_state) (cc:(A)compiler_config) prelude input
    (mc:(A,B,C)machine_config) data_sp cbspace.
     initial_condition st cc mc
     ==> (match FST (compiler_compile cc prelude input) with
            M_failure (ParseError e) -> semantics st prelude input = CannotParse
          | M_failure (TypeError e) -> semantics st prelude input = IllTyped
          | M_failure AssembleError -> T
          | M_failure (ConfigError e) -> T
          | M_success (code,data,c) ->
              ?behaviours source_decs.
                semantics st prelude input = Execute behaviours /\
                parse (lexer_fun input) = SOME source_decs /\
                !ms. installed code cbspace data data_sp
                       (lab_to_target_config_ffi_names (backend_config_lab_conf c))
                       (heap_regs (stack_to_lab_config_reg_names
                                     (backend_config_stack_conf
                                        (compiler_config_backend_config cc)))) mc
                       (lab_to_target_config_shmem_extra (backend_config_lab_conf c)) ms
                     ==> machine_sem mc (state_ffi (semantics_state_sem_st st)) ms SUBSET
                         extend_with_resource_limit'
                           (compilerProof_is_safe_for_space
                              (state_ffi (semantics_state_sem_st st)) cc
                              (APPEND prelude source_decs)
                              (compilerProof_read_limits cc mc ms))
                           behaviours)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[initial_condition_def] THEN STRIP_TAC THEN
  REWRITE_TAC[compiler_compile_def; compilerProof_read_limits_def;
              compilerProof_is_safe_for_space_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[parse_cml_input_def] THEN
  CASES_ON `parse_prog (lexer_fun input)` THEN CASE_REWRITE_TAC[] THENL
   [(* the parser succeeds *)
    SUBGOAL_THEN `parse (lexer_fun input) = SOME (a1:dec list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[parse_prog_correct]; ALL_TAC] THEN
    MP_TAC(ISPECL [`st:(FFI)semantics_state`;
                   `compiler_config_inferencer_config (cc:(A)compiler_config)`;
                   `APPEND prelude (a1:dec list)`] infertype_prog_correct) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ic:inf_env` (X_CHOOSE_THEN `err:locs option#mlstring`
      SUBST1_TAC)) THEN
    ASM_CASES_TAC `can_type_prog (st:(FFI)semantics_state) (APPEND prelude a1)` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [(* the program has a type: the backend *)
      MP_TAC(ISPEC `compile_tap (compiler_config_asm_config (cc:(A)compiler_config))
                      (compiler_config_backend_config cc) (APPEND prelude a1)`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `res:(((8)word)list#((A)word)list#backend_config)option`
        (X_CHOOSE_THEN `td:(mlstring)app_list` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      CASES_ON `res:(((8)word)list#((A)word)list#backend_config)option` THEN
      CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `a:((8)word)list#((A)word)list#backend_config` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `bytes:((8)word)list`
        (X_CHOOSE_THEN `y:((A)word)list#backend_config` SUBST_ALL_TAC)) THEN
      MP_TAC(ISPEC `y:((A)word)list#backend_config` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `data:((A)word)list` (X_CHOOSE_THEN `c:backend_config`
        SUBST_ALL_TAC)) THEN
      CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC
       [`semantics_prog (semantics_state_sem_st (st:(FFI)semantics_state))
           (semantics_state_sem_env st) (APPEND prelude a1)`; `a1:dec list`] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[semantics_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[] THEN X_GEN_TAC `ms:B` THEN DISCH_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_tap_compile) THEN
      SUBGOAL_THEN `~semantics_prog (semantics_state_sem_st (st:(FFI)semantics_state))
          (semantics_state_sem_env st) (APPEND prelude a1) Fail` ASSUME_TAC THENL
       [MP_TAC(ASSUME `can_type_prog (st:(FFI)semantics_state) (APPEND prelude a1)`) THEN
        REWRITE_TAC[can_type_prog_def] THEN
        DISCH_THEN(X_CHOOSE_THEN `new_tids:num->bool` (X_CHOOSE_THEN `new_tenv:type_env`
          STRIP_ASSUME_TAC)) THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL [`semantics_state_sem_st (st:(FFI)semantics_state)`;
          `semantics_state_sem_env (st:(FFI)semantics_state)`;
          `APPEND prelude (a1:dec list)`; `Fail`; `T`; `ctMap:ctMap`; `FEMPTY:tenv_store`;
          `semantics_state_tenv (st:(FFI)semantics_state)`; `new_tenv:type_env`;
          `new_tids:num->bool`] semantics_type_sound) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CPPAUX_type_sound_invariant_tids THEN
        EXISTS_TAC `semantics_state_type_ids (st:(FFI)semantics_state)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`compiler_config_asm_config (cc:(A)compiler_config)`;
        `compiler_config_backend_config (cc:(A)compiler_config)`;
        `APPEND prelude (a1:dec list)`; `bytes:((8)word)list`; `data:((A)word)list`;
        `c:backend_config`; `state_ffi (semantics_state_sem_st (st:(FFI)semantics_state))`;
        `NONE:((backend_config)compiler_instance)option`; `mc:(A,B,C)machine_config`;
        `cbspace:num`; `data_sp:num`; `ms:B`] compile_correct') THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM(ASSUME `semantics_state_sem_st st,semantics_state_sem_env st =
        THE (prim_sem_env (state_ffi (semantics_state_sem_st (st:(FFI)semantics_state))))`)] THEN
      CASE_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[add_eval_state_def; opt_eval_config_wf_def];
      (* the program has no type *)
      MP_TAC(ISPEC `err:locs option#mlstring` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `locs:locs option` (X_CHOOSE_THEN `msg:mlstring`
        SUBST1_TAC)) THEN
      CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[semantics_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
    (* the parser fails *)
    SUBGOAL_THEN `parse (lexer_fun input) = NONE` ASSUME_TAC THENL
     [ASM_MESON_TAC[parse_prog_correct]; ALL_TAC] THEN
    ASM_REWRITE_TAC[semantics_def] THEN CASE_REWRITE_TAC[]]);;

(* the type numbers of the primitive types (HOL4 EVAL) *)
let CPPAUX_TYNUMS =
  [typeSystem_Tarray_num_def; typeSystem_Tbool_num_def; typeSystem_Tchar_num_def;
   typeSystem_Texn_num_def; typeSystem_Tfn_num_def; typeSystem_Tint_num_def;
   typeSystem_Tlist_num_def; typeSystem_Tref_num_def; typeSystem_Tstring_num_def;
   typeSystem_Ttup_num_def; typeSystem_Tvector_num_def; typeSystem_Tword64_num_def;
   typeSystem_Tword8_num_def; typeSystem_Tword8array_num_def;
   typeSystem_Tdouble_num_def];;

(* HOL4 compile_correct_lemma: EVAL of prim_type_ids = count start_type_id *)
let CPPAUX_prim_type_ids_count = prove
 (`prim_type_ids = count start_type_id`,
  REWRITE_TAC([prim_type_ids_def; prim_type_nums_def; start_type_id_def; EXTENSION;
               IN_COUNT; IN_SET_OF_LIST; MEM] @ CPPAUX_TYNUMS) THEN
  ARITH_TAC);;

(* HOL4 compile_correct_lemma: EVAL of set_tids_tenv (count start_type_id)  *)
(* prim_tenv                                                                *)
let CPPAUX_set_tids_tenv_prim_tenv = prove
 (`set_tids_tenv (count start_type_id) prim_tenv`,
  REWRITE_TAC[set_tids_tenv_def; prim_tenv_def; type_env_INFO.ri_accessors;
              nsAll_nsEmpty] THEN
  CONJ_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[REVERSE; APPEND; ALL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC([ALL; set_tids_subset_def; set_tids_def; typeSystem_Tlist_def; MAP;
               set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; INSERT_SUBSET;
               EMPTY_SUBSET; IN_COUNT; start_type_id_def] @ CPPAUX_TYNUMS) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* the semantic state of the primitives keeps the ffi state *)
let CPPAUX_prim_sem_env_ffi = prove
 (`!ffi:(FFI)ffi_state. state_ffi (FST (THE (prim_sem_env ffi))) = ffi`,
  REWRITE_TAC[prim_sem_env_eq; THE_DEF; FST; state_INFO.ri_accessors]);;

(* HOL4 line 179 *)
let compilerProof_compile_correct_lemma = prove
 (CASE_TERM
  `!(ffi:(FFI)ffi_state) prelude input (cc:(A)compiler_config)
    (mc:(A,B,C)machine_config) data_sp cbspace.
     config_ok cc mc
     ==> (match FST (compiler_compile cc prelude input) with
            M_failure (ParseError e) -> semantics_init ffi prelude input = CannotParse
          | M_failure (TypeError e) -> semantics_init ffi prelude input = IllTyped
          | M_failure AssembleError -> T
          | M_failure (ConfigError e) -> T
          | M_success (code,data,c) ->
              ?behaviours source_decs.
                semantics_init ffi prelude input = Execute behaviours /\
                parse (lexer_fun input) = SOME source_decs /\
                !ms. installed code cbspace data data_sp
                       (lab_to_target_config_ffi_names (backend_config_lab_conf c))
                       (heap_regs (stack_to_lab_config_reg_names
                                     (backend_config_stack_conf
                                        (compiler_config_backend_config cc)))) mc
                       (lab_to_target_config_shmem_extra (backend_config_lab_conf c)) ms
                     ==> machine_sem mc ffi ms SUBSET
                         extend_with_resource_limit'
                           (compilerProof_is_safe_for_space ffi cc
                              (APPEND prelude source_decs)
                              (compilerProof_read_limits cc mc ms))
                           behaviours)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[semantics_init_def] THEN
  MP_TAC(ISPECL [`semantics_state_REC prim_tenv prim_type_ids
                    (FST (THE (prim_sem_env (ffi:(FFI)ffi_state))))
                    (SND (THE (prim_sem_env ffi)))`;
                 `cc:(A)compiler_config`; `prelude:dec list`; `input:string`;
                 `mc:(A,B,C)machine_config`; `data_sp:num`; `cbspace:num`]
                compile_correct_gen) THEN
  REWRITE_TAC[semantics_state_INFO.ri_accessors; CPPAUX_prim_sem_env_ffi] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[config_ok_def]) THEN
  REWRITE_TAC[initial_condition_def; semantics_state_INFO.ri_accessors;
              CPPAUX_prim_sem_env_ffi; PAIR; CPPAUX_set_tids_tenv_prim_tenv] THEN
  MP_TAC(ISPECL [`{}:num->bool`; `FST (THE (prim_sem_env (ffi:(FFI)ffi_state)))`;
                 `SND (THE (prim_sem_env (ffi:(FFI)ffi_state)))`]
                prim_type_sound_invariants) THEN
  REWRITE_TAC[PAIR; DISJOINT_EMPTY] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CPPAUX_prim_type_ids_count]) THEN
  ASM_REWRITE_TAC[CPPAUX_prim_type_ids_count]);;

(* HOL4 line 232 *)
let compile_correct_safe_for_space = prove
 (`!(ffi:(FFI)ffi_state) prelude input (cc:(A)compiler_config)
    (mc:(A,B,C)machine_config) data_sp cbspace code data c c'.
     config_ok cc mc
     ==> compiler_compile cc prelude input = (M_success (code,data,c),c')
     ==> ?behaviours source_decs.
           semantics_init ffi prelude input = Execute behaviours /\
           parse (lexer_fun input) = SOME source_decs /\
           !ms. compilerProof_is_safe_for_space ffi cc (APPEND prelude source_decs)
                  (compilerProof_read_limits cc mc ms) /\
                installed code cbspace data data_sp
                  (lab_to_target_config_ffi_names (backend_config_lab_conf c))
                  (heap_regs (stack_to_lab_config_reg_names
                                (backend_config_stack_conf
                                   (compiler_config_backend_config cc)))) mc
                  (lab_to_target_config_shmem_extra (backend_config_lab_conf c)) ms
                ==> machine_sem mc ffi ms = behaviours`,
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `prelude:dec list`; `input:string`;
                `cc:(A)compiler_config`; `mc:(A,B,C)machine_config`; `data_sp:num`;
                `cbspace:num`] compilerProof_compile_correct_lemma) THEN
  ASM_REWRITE_TAC[FST] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `behaviours:behaviour->bool`
    (X_CHOOSE_THEN `source_decs:dec list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`behaviours:behaviour->bool`; `source_decs:dec list`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `ms:B` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ms:B`) THEN
  ASM_REWRITE_TAC[extend_with_resource_limit'_def] THEN DISCH_TAC THEN
  (* the semantics is deterministic: one behaviour, and the machine has one *)
  SUBGOAL_THEN `state_invariant (semantics_state_REC prim_tenv prim_type_ids
      (FST (THE (prim_sem_env (ffi:(FFI)ffi_state)))) (SND (THE (prim_sem_env ffi))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[state_invariant_def; semantics_state_INFO.ri_accessors] THEN
    MP_TAC(ISPECL [`{}:num->bool`; `FST (THE (prim_sem_env (ffi:(FFI)ffi_state)))`;
                   `SND (THE (prim_sem_env (ffi:(FFI)ffi_state)))`]
                  prim_type_sound_invariants) THEN
    REWRITE_TAC[PAIR; DISJOINT_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (MATCH_MP semantics_deterministic (ASSUME
    `state_invariant (semantics_state_REC prim_tenv prim_type_ids
      (FST (THE (prim_sem_env (ffi:(FFI)ffi_state)))) (SND (THE (prim_sem_env ffi))))`))
    (REWRITE_RULE[semantics_init_def]
      (ASSUME `semantics_init (ffi:(FFI)ffi_state) prelude input = Execute behaviours`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:behaviour` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MP_TAC(INST [`ffi:(FFI)ffi_state`,`st:(FFI)ffi_state`] machine_sem_total) THEN
  DISCH_THEN(X_CHOOSE_TAC `b':behaviour`) THEN
  UNDISCH_TAC
    `machine_sem (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) SUBSET {b}` THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_SING] THEN REWRITE_TAC[IN] THEN ASM_MESON_TAC[]);;

(* the headline check: the theorem is the statement of the statement file *)
let () =
  if hyp compile_correct_safe_for_space = [] &&
     aconv (concl compile_correct_safe_for_space) compile_correct_safe_for_space_statement
  then () else failwith "compile_correct_safe_for_space is not the headline statement";;

(* HOL4 line 264 (Theorem compile_correct = Q.prove (...) |> check_thm) *)
let compilerProof_compile_correct = prove
 (CASE_TERM
  `!(ffi:(FFI)ffi_state) prelude input (cc:(A)compiler_config)
    (mc:(A,B,C)machine_config) data_sp cbspace.
     config_ok cc mc
     ==> (match FST (compiler_compile cc prelude input) with
            M_failure (ParseError e) -> semantics_init ffi prelude input = CannotParse
          | M_failure (TypeError e) -> semantics_init ffi prelude input = IllTyped
          | M_failure AssembleError -> T
          | M_failure (ConfigError e) -> T
          | M_success (code,data,c) ->
              ?behaviours.
                semantics_init ffi prelude input = Execute behaviours /\
                !ms. installed code cbspace data data_sp
                       (lab_to_target_config_ffi_names (backend_config_lab_conf c))
                       (heap_regs (stack_to_lab_config_reg_names
                                     (backend_config_stack_conf
                                        (compiler_config_backend_config cc)))) mc
                       (lab_to_target_config_shmem_extra (backend_config_lab_conf c)) ms
                     ==> machine_sem mc ffi ms SUBSET
                         extend_with_resource_limit behaviours)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `prelude:dec list`; `input:string`;
                `cc:(A)compiler_config`; `mc:(A,B,C)machine_config`; `data_sp:num`;
                `cbspace:num`] compilerProof_compile_correct_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`FST (compiler_compile (cc:(A)compiler_config) prelude input)`,
           `r:(((8)word)list#((A)word)list#backend_config,compile_error)exc`) THEN
  GEN_TAC THEN
  CASES_ON `r:(((8)word)list#((A)word)list#backend_config,compile_error)exc` THEN
  CASE_REWRITE_TAC[] THEN
  (* the failure cases are the same in both; the success case: *)
  MP_TAC(ISPEC `a:((8)word)list#((A)word)list#backend_config` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `code:((8)word)list`
    (X_CHOOSE_THEN `y:((A)word)list#backend_config` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `y:((A)word)list#backend_config` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `data:((A)word)list` (X_CHOOSE_THEN `c:backend_config`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `behaviours:behaviour->bool`
    (X_CHOOSE_THEN `source_decs:dec list` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `behaviours:behaviour->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `ms:B` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `extend_with_resource_limit'
                (compilerProof_is_safe_for_space (ffi:(FFI)ffi_state) (cc:(A)compiler_config)
                   (APPEND prelude source_decs)
                   (compilerProof_read_limits cc (mc:(A,B,C)machine_config) (ms:B)))
                behaviours` THEN
  ASM_SIMP_TAC[extend_with_resource_limit'_SUBSET]);;

(* the headline check: the theorem is the statement of the statement file *)
let () =
  if hyp compilerProof_compile_correct = [] &&
     aconv (concl compilerProof_compile_correct) compile_correct_statement
  then () else failwith "compilerProof_compile_correct is not the headline statement";;

(* HOL4 line 291 *)
let type_config_ok = prove
 (`envRel_env_rel prim_tenv infer_init_config /\
   inf_set_tids_ienv prim_type_ids infer_init_config`,
    SUBGOAL_THEN `tenv_ctor_ok (type_env_c prim_tenv) /\ tenv_abbrev_ok (type_env_t prim_tenv)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[tenv_ctor_ok_def; tenv_abbrev_ok_def; prim_tenv_def;
                type_env_INFO.ri_accessors] THEN
    CONJ_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
    SIMP_NOASM[REVERSE; ALL; check_freevars_def; MEM; injectivity "char"];
    ALL_TAC] THEN
  REWRITE_TAC[envRel_env_rel_def; inf_set_tids_ienv_def; ienv_ok_def; ienv_val_ok_def;
              tenv_ok_def; env_rel_sound_def; env_rel_complete_def; infer_init_config_def;
              inf_env_INFO.ri_accessors; INFER1AUX_lookup_var_Empty] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[prim_tenv_def; type_env_INFO.ri_accessors; nsAll_nsEmpty; nsLookup_nsEmpty;
              tenv_val_ok_nsEmpty; option_DISTINCT] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:mlstring list` list_CASES) THEN
    REWRITE_TAC[nsLookupMod_def; nsLookupMod_nsEmpty; option_DISTINCT];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[REVERSE; APPEND; ALL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC([ALL; inf_set_tids_subset_def; unconvert_t_def; inf_set_tids_def; MAP;
               set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; INSERT_SUBSET;
               EMPTY_SUBSET; typeSystem_Tlist_def; CPPAUX_prim_type_ids_count; IN_COUNT;
               start_type_id_def] @ CPPAUX_TYNUMS) THEN
  CONV_TAC NUM_REDUCE_CONV);;
