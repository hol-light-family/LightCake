(* ========================================================================= *)
(* word_removeProof: port of HOL4 compiler/backend/proofs/                   *)
(* word_removeProofScript.sml (CakeML v3479).                                *)
(* Correctness proof for word_remove.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem and wordProps are those of their files  *)
(*   (wl_evaluate, wl_get_var, wl_state_locals, ...): HOL4 s.f is           *)
(*   wl_state_f s, s with f := v is wl_state_f_fupd (K v) s.                 *)
(* - HOL4 compile_state is one record update of five fields; here nested    *)
(*   fupds with the clock innermost.  HOL4 EVAL_TAC proofs are rewriting     *)
(*   with compile_state_def and the record theorems.                        *)
(* - word_remove_correct follows HOL4: induction with wl_evaluate_ind (HOL4 *)
(*   recInduct evaluate_ind), RW with evaluate and remove_must_terminate,    *)
(*   then one tactic per clause in the order of the definition: a common one *)
(*   for the clauses without a subprogram and for If (HOL4's TRY step; with  *)
(*   the helper share_inst_compile_state also for ShareInst), and HOL4's     *)
(*   proofs of MustTerminate, Seq, Loop (HOL4's suspended case), Install and *)
(*   Call.  WPROOF1AUX_ names are local helpers; the last five are used by  *)
(*   word_to_wordProof.                                                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

type_invention_error := true;;
let compile_state_def = cake_def
 `compile_state clk c (s:(A,C,FFI)wl_state) =
    wl_state_compile_fupd (combin_K c)
     (wl_state_compile_oracle_fupd
        (combin_K ((I ## MAP (I ## I ## remove_must_terminate)) o wl_state_compile_oracle s))
      (wl_state_code_fupd (combin_K (sptree_map (I ## remove_must_terminate) (wl_state_code s)))
       (wl_state_termdep_fupd (combin_K 0)
        (wl_state_clock_fupd (combin_K (wl_state_clock s + clk)) s))))`;;

let compile_state_const = prove
 (`wl_state_locals (compile_state clk c s) = wl_state_locals (s:(A,C,FFI)wl_state) /\
   wl_state_permute (compile_state clk c s) = wl_state_permute s /\
   wl_state_ffi (compile_state clk c s) = wl_state_ffi s /\
   wl_state_code_buffer (compile_state clk c s) = wl_state_code_buffer s /\
   wl_state_data_buffer (compile_state clk c s) = wl_state_data_buffer s /\
   wl_state_code (compile_state clk c s) =
     sptree_map (I ## remove_must_terminate) (wl_state_code s) /\
   wl_state_clock (compile_state clk c s) = wl_state_clock s + clk /\
   wl_state_termdep (compile_state clk c s) = 0 /\
   wl_state_compile_oracle (compile_state clk c s) =
     (I ## MAP (I ## I ## remove_must_terminate)) o wl_state_compile_oracle s /\
   wl_state_compile (compile_state clk c s) = c /\
   wl_state_stack (compile_state clk c s) = wl_state_stack s /\
   wl_state_store (compile_state clk c s) = wl_state_store s /\
   wl_state_fp_regs (compile_state clk c s) = wl_state_fp_regs s /\
   wl_state_memory (compile_state clk c s) = wl_state_memory s /\
   wl_state_mdomain (compile_state clk c s) = wl_state_mdomain s /\
   wl_state_sh_mdomain (compile_state clk c s) = wl_state_sh_mdomain s /\
   wl_state_be (compile_state clk c s) = wl_state_be s /\
   wl_state_gc_fun (compile_state clk c s) = wl_state_gc_fun s /\
   wl_state_handler (compile_state clk c s) = wl_state_handler s /\
   wl_state_locals_size (compile_state clk c s) = wl_state_locals_size s /\
   wl_state_stack_size (compile_state clk c s) = wl_state_stack_size s /\
   wl_state_stack_max (compile_state clk c s) = wl_state_stack_max s /\
   wl_state_stack_limit (compile_state clk c s) = wl_state_stack_limit s`,
  SIMP[compile_state_def]);;
let _ = cake_add_simps [compile_state_const];;

let find_code_map_I = prove
 (`wl_find_code d (l:((A)word_loc)list) (sptree_map (I ## (f:B->D)) (t:(num#B)spt))
                (lsz:(L)spt) =
   OPTION_MAP (I ## f ## I) (wl_find_code d l t lsz)`,
  QCASES_ON "d" THEN RW[wl_find_code_def; lookup_map] THEN
  REPEAT(TOP_CASE_TAC THEN FS[]));;
let _ = cake_add_simps [find_code_map_I];;

let compile_state_update = prove
 (`wl_state_stack_fupd (combin_K f1) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_fupd (combin_K f1) (s:(A,C,FFI)wl_state)) /\
   wl_state_permute_fupd (combin_K f2) (compile_state clk c s) =
     compile_state clk c (wl_state_permute_fupd (combin_K f2) s) /\
   wl_state_ffi_fupd (combin_K f10) (compile_state clk c s) =
     compile_state clk c (wl_state_ffi_fupd (combin_K f10) s) /\
   wl_state_data_buffer_fupd (combin_K f9) (compile_state clk c s) =
     compile_state clk c (wl_state_data_buffer_fupd (combin_K f9) s) /\
   wl_state_code_buffer_fupd (combin_K f8) (compile_state clk c s) =
     compile_state clk c (wl_state_code_buffer_fupd (combin_K f8) s) /\
   wl_state_memory_fupd (combin_K f7) (compile_state clk c s) =
     compile_state clk c (wl_state_memory_fupd (combin_K f7) s) /\
   wl_state_locals_fupd (combin_K f6) (compile_state clk c s) =
     compile_state clk c (wl_state_locals_fupd (combin_K f6) s) /\
   wl_state_memory_fupd (combin_K f5) (compile_state clk c s) =
     compile_state clk c (wl_state_memory_fupd (combin_K f5) s) /\
   wl_state_store_fupd (combin_K f4) (compile_state clk c s) =
     compile_state clk c (wl_state_store_fupd (combin_K f4) s) /\
   wl_state_fp_regs_fupd (combin_K f11) (compile_state clk c s) =
     compile_state clk c (wl_state_fp_regs_fupd (combin_K f11) s) /\
   wl_state_handler_fupd (combin_K f3) (compile_state clk c s) =
     compile_state clk c (wl_state_handler_fupd (combin_K f3) s) /\
   wl_state_locals_size_fupd (combin_K f12) (compile_state clk c s) =
     compile_state clk c (wl_state_locals_size_fupd (combin_K f12) s) /\
   wl_state_stack_size_fupd (combin_K f13) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_size_fupd (combin_K f13) s) /\
   wl_state_stack_max_fupd (combin_K f14) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_max_fupd (combin_K f14) s) /\
   wl_state_stack_limit_fupd (combin_K f15) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_limit_fupd (combin_K f15) s)`,
  SIMP[compile_state_def]);;
let _ = cake_add_simps [compile_state_update];;

let get_var_compile_state = prove
 (`wl_get_var x (compile_state clk c s) = wl_get_var x (s:(A,C,FFI)wl_state)`,
  SIMP[wl_get_var_def]);;
let _ = cake_add_simps [get_var_compile_state];;

let get_fp_var_compile_state = prove
 (`wl_get_fp_var x (compile_state clk c s) = wl_get_fp_var x (s:(A,C,FFI)wl_state)`,
  SIMP[wl_get_fp_var_def]);;
let _ = cake_add_simps [get_fp_var_compile_state];;

let get_vars_compile_state = prove
 (`wl_get_vars xs (compile_state clk c s) = wl_get_vars xs (s:(A,C,FFI)wl_state)`,
  INDUCT_ON `xs:num list` THEN SIMP[wl_get_vars_def]);;
let _ = cake_add_simps [get_vars_compile_state];;

let set_var_compile_state = prove
 (`wl_set_var x y (compile_state clk c s) =
   compile_state clk c (wl_set_var x y (s:(A,C,FFI)wl_state))`,
  SIMP[wl_set_var_def]);;
let _ = cake_add_simps [set_var_compile_state];;

let unset_var_compile_state = prove
 (`wl_unset_var x (compile_state clk c s) =
   compile_state clk c (wl_unset_var x (s:(A,C,FFI)wl_state))`,
  SIMP[wl_unset_var_def]);;
let _ = cake_add_simps [unset_var_compile_state];;

let set_fp_var_compile_state = prove
 (`wl_set_fp_var x y (compile_state clk c s) =
   compile_state clk c (wl_set_fp_var x y (s:(A,C,FFI)wl_state))`,
  SIMP[wl_set_fp_var_def]);;
let _ = cake_add_simps [set_fp_var_compile_state];;

let set_vars_compile_state = prove
 (`wl_set_vars xs ys (compile_state clk c s) =
   compile_state clk c (wl_set_vars xs ys (s:(A,C,FFI)wl_state))`,
  SIMP[wl_set_vars_def]);;
let _ = cake_add_simps [set_vars_compile_state];;

let get_store_compile_state = prove
 (`wl_get_store x (compile_state clk c s) = wl_get_store x (s:(A,C,FFI)wl_state)`,
  SIMP[wl_get_store_def]);;
let _ = cake_add_simps [get_store_compile_state];;

let set_store_compile_state = prove
 (`wl_set_store x y (compile_state clk c s) =
   compile_state clk c (wl_set_store x y (s:(A,C,FFI)wl_state))`,
  SIMP[wl_set_store_def]);;
let _ = cake_add_simps [set_store_compile_state];;

let push_env_compile_state = prove
 (`wl_push_env env h (compile_state clk c s) =
   compile_state clk c (wl_push_env env h (s:(A,C,FFI)wl_state))`,
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`,`h:(num#(A)wl_prog#num#num)option`) THEN
  SIMP[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN SIMP[]);;
let _ = cake_add_simps [push_env_compile_state];;

let pop_env_compile_state = prove
 (`wl_pop_env (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_pop_env (s:(A,C,FFI)wl_state))`,
  SIMP[wl_pop_env_def] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]));;
let _ = cake_add_simps [pop_env_compile_state];;

let call_env_compile_state = prove
 (`wl_call_env x lsz (compile_state clk c z) =
   compile_state clk c (wl_call_env x lsz (z:(A,C,FFI)wl_state))`,
  SIMP[wl_call_env_def]);;
let _ = cake_add_simps [call_env_compile_state];;

let flush_state_compile_state = prove
 (`wl_flush_state x (compile_state clk c z) =
   compile_state clk c (wl_flush_state x (z:(A,C,FFI)wl_state))`,
  QCASES_ON "x" THEN SIMP[wl_flush_state_def]);;
let _ = cake_add_simps [flush_state_compile_state];;

let has_space_compile_state = prove
 (`wl_has_space n (compile_state clk c s) = wl_has_space n (s:(A,C,FFI)wl_state)`,
  SIMP[wl_has_space_def]);;
let _ = cake_add_simps [has_space_compile_state];;

let gc_compile_state = prove
 (`wl_gc (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_gc (s:(A,C,FFI)wl_state))`,
  SIMP[wl_gc_def] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]));;
let _ = cake_add_simps [gc_compile_state];;

let alloc_compile_state = prove
 (`wl_alloc w names (compile_state clk c s) =
   (I ## compile_state clk c) (wl_alloc w names (s:(A,C,FFI)wl_state))`,
  SIMP[wl_alloc_def] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]));;
let _ = cake_add_simps [alloc_compile_state];;

let mem_load_compile_state = prove
 (`wl_mem_load w (compile_state clk c s) = wl_mem_load w (s:(A,C,FFI)wl_state)`,
  SIMP[wl_mem_load_def]);;
let _ = cake_add_simps [mem_load_compile_state];;

let mem_store_compile_state = prove
 (`wl_mem_store x y (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_mem_store x y (s:(A,C,FFI)wl_state))`,
  SIMP[wl_mem_store_def] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]));;
let _ = cake_add_simps [mem_store_compile_state];;

let word_exp_compile_state = prove
 (`!(s:(A,C,FFI)wl_state) y. wl_word_exp (compile_state clk c s) y = wl_word_exp s y`,
  SIMP[compile_state_def]);;
let _ = cake_add_simps [word_exp_compile_state];;

let assign_compile_state = prove
 (`wl_assign x y (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_assign x y (s:(A,C,FFI)wl_state))`,
  SIMP[wl_assign_def] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]));;
let _ = cake_add_simps [assign_compile_state];;

let inst_compile_state = prove
 (`wl_inst i (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_inst i (s:(A,C,FFI)wl_state))`,
  IL2AUX_INST_SPLIT_TAC THEN SIMP[wl_inst_def] THEN EVERY_CASE_TAC THEN
  REPEAT (PAIRARG_TAC THEN FS[]) THEN FS[]);;
let _ = cake_add_simps [inst_compile_state];;

let cut_state_compile_state = prove
 (`wl_cut_state names (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_cut_state names (s:(A,C,FFI)wl_state))`,
  SIMP[wl_cut_state_def] THEN TOP_CASE_TAC THEN SIMP[]);;
let _ = cake_add_simps [cut_state_compile_state];;

(* HOL4 [local] *)

let evaluate_add_clock_compile_state = prove
 (`wl_evaluate (p, compile_state clk c s) = (res, compile_state 0 c s') /\
   ~(res = SOME wl_TimeOut) ==>
   !extra. wl_evaluate (p, compile_state (clk + extra) c (s:(A,C,FFI)wl_state)) =
           (res, compile_state extra c s')`,
  STRIP_TAC THEN DRULE wl_evaluate_add_clock THEN SIMP[] THEN
  DISCH_THEN(fun th -> GEN_TAC THEN MP_TAC(SPEC_ALL th)) THEN
  SIMP[compile_state_def; wl_state_component_equality; ADD_AC]);;

let compile_state_dec_clock = prove
 (`~(wl_state_clock s = 0) ==>
   compile_state clk c (wl_dec_clock s) =
   wl_dec_clock (compile_state clk c (s:(A,C,FFI)wl_state))`,
  SIMP[compile_state_def; wl_dec_clock_def; wl_state_component_equality] THEN ARITH_TAC);;
let _ = cake_add_simps [compile_state_dec_clock];;

let jump_exc_compile_state = prove
 (`wl_jump_exc (compile_state clk c s) =
   OPTION_MAP (compile_state clk c ## I) (wl_jump_exc (s:(A,C,FFI)wl_state))`,
  SIMP[wl_jump_exc_def] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]));;
let _ = cake_add_simps [jump_exc_compile_state];;

let get_var_imm_compile_state = prove
 (`wl_get_var_imm x (compile_state clk c s) = wl_get_var_imm x (s:(A,C,FFI)wl_state)`,
  QCASES_ON "x" THEN SIMP[wl_get_var_imm_def]);;
let _ = cake_add_simps [get_var_imm_compile_state];;

let push_env_case_handler = prove
 (CASE_TERM
  `wl_push_env x (match handler with
                    NONE -> NONE
                  | SOME (v,prog,l1,l2) -> SOME (v, (f:(A)wl_prog->(A)wl_prog) prog,l1,l2)) =
   (wl_push_env x handler:(A,C,FFI)wl_state->(A,C,FFI)wl_state)`,
  QCASES_ON "handler" THEN SIMP[] THEN
  SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
  SIMP[FORALL_PAIR_THM; FUN_EQ_THM; wl_push_env_def]);;
let _ = cake_add_simps [push_env_case_handler];;

(* HOL4 [local] *)

let pair_map_I = prove
 (`(\(k:A,v:B). (k,(f:B->C) v)) = (I ## f) /\
   (\(k:B,v:D). (f k,v)) = (f ## I)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers for word_remove_correct (WPROOF1AUX_ names).                *)
(* ------------------------------------------------------------------------- *)

let WPROOF1AUX_sh_mem_set_var_compile_state = prove
 (`sh_mem_set_var r v (compile_state clk c s) =
   (I ## compile_state clk c)
     (sh_mem_set_var r v (s:(A,C,FFI)wl_state):((W)wl_result)option#(A,C,FFI)wl_state)`,
  QCASES_ON "r" THEN SIMP[sh_mem_set_var_def] THEN
  QCASES_ON "a" THEN SIMP[sh_mem_set_var_def]);;

let WPROOF1AUX_share_inst_compile_state = prove
 (`share_inst op v ad (compile_state clk c s) =
   (I ## compile_state clk c)
     (share_inst op v ad (s:(A,C,FFI)wl_state):((W)wl_result)option#(A,C,FFI)wl_state)`,
  QCASES_ON "op" THEN
  SIMP[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
       wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
       wl_sh_mem_store_byte_def; wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[WPROOF1AUX_sh_mem_set_var_compile_state]));;

let WPROOF1AUX_push_env_some = prove
 (`wl_push_env envs (SOME (n, remove_must_terminate p, l1, l2)) (s:(A,C,FFI)wl_state) =
   wl_push_env envs (SOME (n,p,l1,l2)) s`,
  REWRITE_TAC[wl_push_env_def]);;

(* the leaves of the Call case: no run, one run (an induction hypothesis),   *)
(* or two runs (the callee, then the return or exception handler)           *)

let WPROOF1AUX_CALL_LEAF_TAC : tactic =
  let rws = [GSYM compile_state_dec_clock; push_env_compile_state; call_env_compile_state;
             WPROOF1AUX_push_env_some] in
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST [EXISTS_TAC `0` THEN SIMP[] THEN NO_TAC;
         RFS[] THEN QEXISTS_TAC "clk" THEN ASM_SIMP_TAC rws THEN SIMP[] THEN NO_TAC;
         IMP_RES_TAC wl_pop_env_const THEN IMP_RES_TAC wl_evaluate_consts THEN RFS[] THEN
         QEXISTS_TAC "clk' + clk" THEN IMP_RES_TAC evaluate_add_clock_compile_state THEN
         ASM_SIMP_TAC rws THEN SIMP[]];;

let word_remove_correct = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst.
     wl_evaluate (prog,st) = (res,rst) /\
     wl_state_compile st = (\cfg. c cfg o MAP (I ## I ## remove_must_terminate)) /\
     ~(res = SOME wl_Error)
     ==> ?clk. wl_evaluate (remove_must_terminate prog, compile_state clk c st) =
               (res, compile_state 0 c rst)`,
  let simple_tac =
    GVS[wl_case_eq_thms; domain_map; WPROOF1AUX_share_inst_compile_state] THEN
    ASM_MESON_TAC[] in
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN
  RW[wl_evaluate_def; remove_must_terminate_def] THENL
  (replicate simple_tac 12 @   (* Skip .. Store, Tick (two goals) *)
   [(* MustTerminate *)
    PAIRARG_TAC THEN GVS[wl_case_eq_thms] THEN
    QSPEC_THEN "remove_must_terminate p" DRULE evaluate_dec_clock THEN STRIP_TAC THEN
    DRULE wl_evaluate_add_clock THEN SIMP[] THEN
    DISCH_THEN(QSPEC_THEN "wl_state_clock s" MP_TAC) THEN STRIP_TAC THEN
    QEXISTS_TAC "(clk + MustTerminate_limit (:A)) - wl_state_clock s1" THEN
    SAME_RUN_TAC[compile_state_def] THEN SIMP[compile_state_def; wl_state_component_equality];
    (* Seq *)
    PAIRARG_TAC THEN GVS[wl_case_eq_thms] THENL
     [IMP_RES_TAC wl_evaluate_consts THEN RFS[] THEN QEXISTS_TAC "clk + clk'" THEN
      IMP_RES_TAC evaluate_add_clock_compile_state THEN SIMP[];
      ASM_EXISTS_TAC THEN SIMP[]]] @
   replicate simple_tac 5 @   (* Return, Raise, Break, Continue, If *)
   [(* Loop *)
    QCASES_ON "wl_cut_state (names,LN) s" THEN FS[] THEN
    IMP_RES_TAC cut_state_const THEN GVS[] THEN PAIRARG_TAC THEN FS[] THEN
    QCASES_ON "wl_cont_loop res'" THEN FS[] THENL
     [SUBGOAL_THEN `~(res' = SOME (wl_Error:(A)wl_result)) /\ ~(res' = SOME wl_TimeOut)`
        STRIP_ASSUME_TAC THENL [CONJ_TAC THEN STRIP_TAC THEN FS[]; ALL_TAC] THEN
      IMP_RES_TAC wl_evaluate_consts THEN RFS[] THEN
      QCASES_ON "wl_state_clock s1 = 0" THEN FS[] THENL
       [QEXISTS_TAC "clk" THEN RVEQ_TAC THEN SIMP[];
        FIRST_X_ASSUM DRULE THEN SIMP[] THEN STRIP_TAC THEN
        FS[wl_STOP_def; remove_must_terminate_def] THEN QEXISTS_TAC "clk + clk'" THEN
        IMP_RES_TAC evaluate_add_clock_compile_state THEN SIMP[]];
      QCASES_ON "res' = SOME wl_Error" THEN GVS[] THEN
      QEXISTS_TAC "clk" THEN SIMP[] THEN EVERY_CASE_TAC THEN GVS[]];
    simple_tac;   (* LocValue *)
    (* Install *)
    GVS[wl_case_eq_thms] THEN EXISTS_TAC `0` THEN
    SIMP[shift_seq_def; compile_state_def; wl_state_component_equality; map_union;
         map_fromAList; map_insert; FUN_EQ_THM; pair_map_I; ETA_AX]] @
   replicate simple_tac 4 @   (* CodeBufferWrite, DataBufferWrite, FFI, ShareInst *)
   [(* Call *)
    QCASES_ON "ret" THEN QCASES_ON "handler" THEN
    REPEAT PAIRARG_TAC THEN FS[add_ret_loc_def] THEN
    QPAT_X_ASSUM "_ = (res,rst)" MP_TAC THEN
    REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[PAIR_MAP_THM; I_THM]) THEN SIMP[] THEN
    WPROOF1AUX_CALL_LEAF_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Helpers used by word_to_wordProof.                                        *)
(* ------------------------------------------------------------------------- *)

(* strip the outer universal quantifiers of the goal, naming them ns *)

let WPROOF1AUX_NAMED_GEN_TAC (ns:string list) : tactic =
  MAP_EVERY (fun n (asl,w as g) ->
    let v,_ = dest_forall w in X_GEN_TAC (mk_var(n, type_of v)) g) ns;;

(* split the first subterm t of the goal with head constant c (and no bound  *)
(* variables) into t = NONE and t = SOME pat, pat a variable or a triple      *)

let WPROOF1AUX_OCASES_TAC (c:string) (pat:term) : tactic = fun (asl,w as g) ->
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let ok t = let h,_ = strip_comb t in
             is_const h && fst(dest_const h) = c && subset (frees t) fvs in
  let t = find_term ok w in
  let th0 = if is_var pat then ISPEC t (cases "option")
            else ISPEC t BASICAUX_option3_cases in
  let vs = if is_var pat then [pat] else
           let a,bc = dest_pair pat in let b,cc = dest_pair bc in [a;b;cc] in
  let USE th = REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN ASSUME_TAC th in
  DISJ_CASES_THEN2 USE (fun th ->
      X_CHOOSE_THEN (hd vs)
        (if length vs = 1 then USE else
         X_CHOOSE_THEN (el 1 vs) (X_CHOOSE_THEN (el 2 vs) USE)) th) th0 g;;
