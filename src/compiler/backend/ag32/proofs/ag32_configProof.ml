(* ========================================================================= *)
(* ag32_configProof: port of HOL4                                            *)
(* compiler/backend/ag32/proofs/ag32_configProofScript.sml (CakeML v3479).   *)
(* For ag32, prove that the compiler configuration is well formed, and      *)
(* instantiate the compiler correctness theorem.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - is_ag32_machine_config_def is in ag32_compile_correct_statement.ml     *)
(*   (the headline statement uses it), which this file loads.               *)
(* - HOL4 backendProof compile_correct is backendProof_compile_correct;     *)
(*   ag32_compile_correct is derived by HOL4's steps (instantiation,         *)
(*   discharge of backend_config_ok, mc_conf_ok and mc_init_ok, evaluation  *)
(*   of heap_regs) and checked against ag32_compile_correct_statement.      *)
(* - HOL4's EVAL_TAC steps are rewriting with the definitions and numeral  *)
(*   and word conversions; its names_tac (tlookup of the empty name map) is *)
(*   AG32AUX_TLOOKUP_LN and AG32AUX_NAMES_OK.                                *)
(* - The free variables of a HOL4 statement are universally quantified,     *)
(*   after the quantified ones (get_shmem_info_LENGTH: t1 t2;               *)
(*   compile_imp_ffi_names: all, in order of occurrence).                    *)
(* - HOL4 [local] theorems are global bindings here (port convention).       *)
(* - Helpers that are not HOL4 theorems have the prefix AG32AUX_.            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/backend/ag32/proofs/ag32_compile_correct_statement.ml";;
needs "compiler/encoders/ag32/proofs/ag32_targetProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 line 11: is_ag32_machine_config_def, see ag32_compile_correct_statement.ml *)

(* HOL4 names_tac: the register names of ag32 are the empty map *)

let AG32AUX_TLOOKUP_LN = prove
 (`!k. tlookup LN k = k`,
  REWRITE_TAC[tlookup_def; lookup_def] THEN SIMP[]);;

let AG32AUX_NAMES_OK = prove
 (`BIJ (tlookup LN) (:num) (:num) /\ stack_names_names_ok LN 64 [63]`,
  REWRITE_TAC[stack_names_names_ok_def; BIJ; INJ; SURJ; IN_UNIV] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ALL_DISTINCT_GENLIST; EVERY_GENLIST; LENGTH; MEM; AG32AUX_TLOOKUP_LN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL [MESON_TAC[]; MESON_TAC[]; ARITH_TAC]);;

(* the offsets of the stack_remove store (HOL4: case analysis on store_pos) *)

let AG32AUX_INDEX_FIND_LT = prove
 (`!(l:A list) i P j x. INDEX_FIND i P l = SOME (j,x) ==> j < i + LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[INDEX_FIND_def; LENGTH; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THENL
   [ARITH_TAC;
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN ARITH_TAC]);;

let AG32AUX_STORE_POS = prove
 (`!s. store_pos s <= 48`,
  GEN_TAC THEN REWRITE_TAC[store_pos_def] THEN
  MP_TAC(ISPECL [`stack_remove_store_list`; `0`; `\n:store_name. n = s`]
           AG32AUX_INDEX_FIND_LT) THEN
  SUBGOAL_THEN `LENGTH stack_remove_store_list = 48` SUBST1_TAC THENL
   [REWRITE_TAC[stack_remove_store_list_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SPEC_TAC(`INDEX_FIND 0 (\n:store_name. n = s) stack_remove_store_list`,
           `r:(num#store_name)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  MESON_TAC[ARITH_RULE `0 <= 48`; ARITH_RULE `a + 0 < 48 ==> a + 1 <= 48`; ADD_CLAUSES]);;

let AG32AUX_STORE_OFFSET = prove
 (`!s. word_ile (word 4286578689) (store_offset s:int32) /\
       word_ile (store_offset s:int32) (word 8388607)`,
  GEN_TAC THEN REWRITE_TAC[store_offset_def; word_offset_def; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MP_TAC(SPEC `s:store_name` AG32AUX_STORE_POS) THEN
  SPEC_TAC(`store_pos s`,`k:num`) THEN
  REWRITE_TAC[ARITH_RULE `k <= 48 <=> k < 49`] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN REWRITE_TAC[]);;

let ag32_backend_config_ok = prove
 (`backend_config_ok ag32_config ag32_backend_config`,
  REWRITE_TAC[backend_config_ok_def; ag32_backend_config_def; ag32_config] THEN SIMP[] THEN
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def;
              conf_ok_def; max_heap_limit_def; shift_length_def; backend_common_word_shift_def;
              max_stack_alloc_def; DIMINDEX_32; asm_offset_ok_def; aligned_0; ag32_names_def;
              fixed_names_def; ag32_config] THEN
  SIMP[] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[AG32AUX_NAMES_OK; AG32AUX_STORE_OFFSET] THEN CONJ_TAC THENL
   [BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `n <= 255 <=> n < 256`] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN REWRITE_TAC[]]);;

let ag32_machine_config_ok = prove
 (`!mc. is_ag32_machine_config mc ==> mc_conf_ok mc`,
  REWRITE_TAC[mc_conf_ok_def; is_ag32_machine_config_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ag32_encoder_correct; AG32AUX_TARGET_FIELDS; reg_ok_def; ag32_config;
                  good_dimindex_def; DIMINDEX_32; MEM] THEN
  CAKE_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC ag32_target_ok THEN SIMP[target_ok_def; AG32AUX_TARGET_FIELDS]);;

let ag32_init_ok = prove
 (`!mc. is_ag32_machine_config mc ==> mc_init_ok ag32_config ag32_backend_config mc`,
  REWRITE_TAC[mc_init_ok_def; is_ag32_machine_config_def] THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[AG32AUX_TARGET_FIELDS; ag32_config; ag32_backend_config_def] THEN
  SIMP[ag32_names_def; AG32AUX_TLOOKUP_LN; ALL; MEM; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4: CONV_RULE (ONCE_DEPTH_CONV (EVAL o assert (same_const heap_regs ...))) *)

let AG32AUX_HEAP_REGS = prove
 (`heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf ag32_backend_config)) =
   (2,4)`,
  REWRITE_TAC[ag32_backend_config_def; heap_regs_def] THEN
  SIMP[ag32_names_def; AG32AUX_TLOOKUP_LN]);;

let ag32_compile_correct =
  let proj_ty = `:int32#((6)word->int32)#(int32#byte->bool)#bool#bool` in
  let mc = mk_var("mc",mk_type("machine_config",[`:32`;`:ag32_state`;proj_ty])) in
  let is_mc = mk_comb(`is_ag32_machine_config`,mc) in
  let th1 = ISPECL [`ag32_config`; `ag32_backend_config`] backendProof_compile_correct in
  let th2 = INST_TYPE [`:ag32_state`,`:B`; proj_ty,`:C`] (SPEC_ALL th1) in
  let th3 = REWRITE_RULE [ag32_backend_config_ok; UNDISCH(SPEC mc ag32_machine_config_ok);
                          UNDISCH(SPEC mc ag32_init_ok); AG32AUX_HEAP_REGS]
              (ADD_ASSUM is_mc th2) in
  let th4 = DISCH is_mc th3 in
  let vs = frees (concl th4) in
  let order = ["mc";"prog";"bytes";"bitmaps";"c'";"ffi";"cbspace";"data_sp";"ms"] in
  GENL (map (fun n -> find (fun v -> fst(dest_var v) = n) vs) order) th4;;

let () =
  if hyp ag32_compile_correct = [] &&
     aconv (concl ag32_compile_correct) ag32_compile_correct_statement
  then () else failwith "ag32_compile_correct is not the headline statement";;

let get_shmem_info_LENGTH = prove
 (`!(xs:((A)sec)list) c l1 l2 t1 t2.
     get_shmem_info xs c l1 l2 = (t1,t2) /\ LENGTH l1 = LENGTH l2
     ==> LENGTH t1 = LENGTH t2`,
  MATCH_MP_TAC get_shmem_info_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_shmem_info_def; PAIR_EQ] THEN
  W(fun (_,w) ->
    if can (find_term (fun t -> try fst(dest_const t) = "get_memop_info"
                                with Failure _ -> false)) w
    then DISCH_TAC THEN
         SUBGOAL_THEN `?name nb. get_memop_info m = (name,nb:byte)` STRIP_ASSUME_TAC THENL
          [MESON_TAC[PAIR]; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
         FIRST_X_ASSUM(MP_TAC o SPECL [`name:shmem_op`; `nb:byte`]) THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN REPEAT STRIP_TAC THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
    else MESON_TAC[]));;

let IMP_EVERY_list_add_if_fresh = prove
 (`!xs (x:A) p. p x /\ ALL p xs ==> ALL p (list_add_if_fresh x xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_add_if_fresh_def; ALL] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL]);;

let find_ffi_names_ExtCall = prove
 (`!(xs:((A)sec)list). ALL (\x. ?i. ExtCall i = x) (find_ffi_names xs)`,
  MATCH_MP_TAC find_ffi_names_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[find_ffi_names_def; ALL] THEN DISCH_TAC THEN
  REPEAT TOP_CASE_TAC THEN FS[] THEN
  MATCH_MP_TAC IMP_EVERY_list_add_if_fresh THEN FS[] THEN MESON_TAC[]);;

let MAP_ExtCall_ffinames = prove
 (`!xs. ALL (\x. ?i. ExtCall i = x) xs ==> xs = MAP ExtCall (ffinames_to_string_list xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ffinames_to_string_list_def; MAP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:mlstring` (SUBST_ALL_TAC o SYM)) ASSUME_TAC) THEN
  REWRITE_TAC[ffinames_to_string_list_def; MAP; CONS_11] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* the lab_to_target configuration of a compilation (HOL4: unfolding        *)
(* backend compile_def and attach_bitmaps)                                    *)

let AG32AUX_COMPILE_LAB = prove
 (`!asm_conf c prog b bm c1.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c1)
     ==> ?p. lab_to_target_compile asm_conf (backend_config_lab_conf c) p =
             SOME (b,backend_config_lab_conf c1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backend_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "backend_config").ri_accfupds;
                              (record_info "backend_config").ri_accessors; K_THM]) THEN
  ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "lab_to_target_compile"
       with Failure _ -> false)
      then EXISTS_TAC (rand(lhs(concl th))) THEN ACCEPT_TAC th else failwith ""));;

let compile_imp_ffi_names = prove
 (`!asm_conf c p b d c1 f.
     backend_compile (asm_conf:(A)asm_config) c p = SOME (b,d,c1) /\
     lab_to_target_config_shmem_extra (backend_config_lab_conf c1) = [] /\ ~(f = []) /\
     lab_to_target_config_ffi_names (backend_config_lab_conf c) = NONE /\
     ffinames_to_string_list
       (misc_the [] (lab_to_target_config_ffi_names (backend_config_lab_conf c1))) = f
     ==> lab_to_target_config_ffi_names (backend_config_lab_conf c1) =
         SOME (MAP ExtCall f)`,
  let lab_rwts = [(record_info "lab_to_target_config").ri_accfupds;
                  (record_info "lab_to_target_config").ri_accessors; K_THM] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `q:((A)sec)list` o MATCH_MP AG32AUX_COMPILE_LAB) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[lab_to_target_compile_def; compile_lab_def] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CAKE_REWRITE_TAC[] THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(rator(rhs(concl th)))) = "backend_config_lab_conf"
       with Failure _ -> false)
      then SUBST_ALL_TAC(SYM th) else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE lab_rwts) THEN REWRITE_TAC lab_rwts THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_eq c && is_var(lhs c) && is_const(rhs c) && fst(dest_const(rhs c)) = "NIL"
      then SUBST_ALL_TAC th else failwith "") THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] get_shmem_info_LENGTH) th)) THEN
  REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[APPEND_NIL; misc_the_def; option_INJ] THEN MATCH_MP_TAC MAP_ExtCall_ffinames THEN
  REWRITE_TAC[find_ffi_names_ExtCall]);;
