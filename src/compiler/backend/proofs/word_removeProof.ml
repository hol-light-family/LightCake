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
(* - word_remove_correct is proved by induction with wl_evaluate_ind (HOL4  *)
(*   recInduct evaluate_ind), one local tactic per clause of evaluate; the   *)
(*   HOL4 suspend/Resume Loop case is one of them.  WPROOF1AUX_ names are    *)
(*   local helpers.                                                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

type_invention_error := true;;
let compile_state_def = cake_def
 `compile_state clk c (s:(A,C,FFI)wl_state) =
    wl_state_compile_fupd (K c)
     (wl_state_compile_oracle_fupd
        (K ((I ## MAP (I ## I ## remove_must_terminate)) o wl_state_compile_oracle s))
      (wl_state_code_fupd (K (map (I ## remove_must_terminate) (wl_state_code s)))
       (wl_state_termdep_fupd (K 0)
        (wl_state_clock_fupd (K (wl_state_clock s + clk)) s))))`;;

let compile_state_const = prove
 (`wl_state_locals (compile_state clk c s) = wl_state_locals (s:(A,C,FFI)wl_state) /\
   wl_state_permute (compile_state clk c s) = wl_state_permute s /\
   wl_state_ffi (compile_state clk c s) = wl_state_ffi s /\
   wl_state_code_buffer (compile_state clk c s) = wl_state_code_buffer s /\
   wl_state_data_buffer (compile_state clk c s) = wl_state_data_buffer s /\
   wl_state_code (compile_state clk c s) =
     map (I ## remove_must_terminate) (wl_state_code s) /\
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
  REWRITE_TAC[compile_state_def] THEN SIMP[]);;
let _ = cake_add_simps [compile_state_const];;

let find_code_map_I = prove
 (`wl_find_code d (l:((A)word_loc)list) (map (I ## (f:B->D)) (t:(num#B)spt))
                (lsz:(L)spt) =
   OPTION_MAP (I ## f ## I) (wl_find_code d l t lsz)`,
  CASES_ON `d:num option` THEN RW[wl_find_code_def; lookup_map] THEN
  REPEAT(TOP_CASE_TAC THEN FS[]));;
let _ = cake_add_simps [find_code_map_I];;

let compile_state_update = prove
 (`wl_state_stack_fupd (K f1) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_fupd (K f1) (s:(A,C,FFI)wl_state)) /\
   wl_state_permute_fupd (K f2) (compile_state clk c s) =
     compile_state clk c (wl_state_permute_fupd (K f2) s) /\
   wl_state_ffi_fupd (K f10) (compile_state clk c s) =
     compile_state clk c (wl_state_ffi_fupd (K f10) s) /\
   wl_state_data_buffer_fupd (K f9) (compile_state clk c s) =
     compile_state clk c (wl_state_data_buffer_fupd (K f9) s) /\
   wl_state_code_buffer_fupd (K f8) (compile_state clk c s) =
     compile_state clk c (wl_state_code_buffer_fupd (K f8) s) /\
   wl_state_memory_fupd (K f7) (compile_state clk c s) =
     compile_state clk c (wl_state_memory_fupd (K f7) s) /\
   wl_state_locals_fupd (K f6) (compile_state clk c s) =
     compile_state clk c (wl_state_locals_fupd (K f6) s) /\
   wl_state_memory_fupd (K f5) (compile_state clk c s) =
     compile_state clk c (wl_state_memory_fupd (K f5) s) /\
   wl_state_store_fupd (K f4) (compile_state clk c s) =
     compile_state clk c (wl_state_store_fupd (K f4) s) /\
   wl_state_fp_regs_fupd (K f11) (compile_state clk c s) =
     compile_state clk c (wl_state_fp_regs_fupd (K f11) s) /\
   wl_state_handler_fupd (K f3) (compile_state clk c s) =
     compile_state clk c (wl_state_handler_fupd (K f3) s) /\
   wl_state_locals_size_fupd (K f12) (compile_state clk c s) =
     compile_state clk c (wl_state_locals_size_fupd (K f12) s) /\
   wl_state_stack_size_fupd (K f13) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_size_fupd (K f13) s) /\
   wl_state_stack_max_fupd (K f14) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_max_fupd (K f14) s) /\
   wl_state_stack_limit_fupd (K f15) (compile_state clk c s) =
     compile_state clk c (wl_state_stack_limit_fupd (K f15) s)`,
  REWRITE_TAC[compile_state_def; wl_state_component_equality] THEN SIMP[]);;
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
  SPEC_TAC(`xs:num list`,`xs:num list`) THEN LIST_INDUCT_TAC THEN
  SIMP[wl_get_vars_def]);;
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
  CASES_ON `h:(num#(A)wl_prog#num#num)option` THENL
   [ALL_TAC;
    SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
    REWRITE_TAC[FORALL_PAIR_THM]] THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[] THEN REPEAT GEN_TAC THEN PAIRARG_TAC THEN SIMP[]);;
let _ = cake_add_simps [push_env_compile_state];;

let pop_env_compile_state = prove
 (`wl_pop_env (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_pop_env (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_pop_env_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]));;
let _ = cake_add_simps [pop_env_compile_state];;

let call_env_compile_state = prove
 (`wl_call_env x lsz (compile_state clk c z) =
   compile_state clk c (wl_call_env x lsz (z:(A,C,FFI)wl_state))`,
  SIMP[wl_call_env_def]);;
let _ = cake_add_simps [call_env_compile_state];;

let flush_state_compile_state = prove
 (`wl_flush_state x (compile_state clk c z) =
   compile_state clk c (wl_flush_state x (z:(A,C,FFI)wl_state))`,
  CASES_ON `x:bool` THEN SIMP[wl_flush_state_def]);;
let _ = cake_add_simps [flush_state_compile_state];;

let has_space_compile_state = prove
 (`wl_has_space n (compile_state clk c s) = wl_has_space n (s:(A,C,FFI)wl_state)`,
  SIMP[wl_has_space_def]);;
let _ = cake_add_simps [has_space_compile_state];;

let gc_compile_state = prove
 (`wl_gc (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_gc (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]));;
let _ = cake_add_simps [gc_compile_state];;

let alloc_compile_state = prove
 (`wl_alloc w names (compile_state clk c s) =
   (I ## compile_state clk c) (wl_alloc w names (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_alloc_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]));;
let _ = cake_add_simps [alloc_compile_state];;

let mem_load_compile_state = prove
 (`wl_mem_load w (compile_state clk c s) = wl_mem_load w (s:(A,C,FFI)wl_state)`,
  SIMP[wl_mem_load_def]);;
let _ = cake_add_simps [mem_load_compile_state];;

let mem_store_compile_state = prove
 (`wl_mem_store x y (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_mem_store x y (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_mem_store_def] THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[OPTION_MAP_DEF]);;
let _ = cake_add_simps [mem_store_compile_state];;

let word_exp_compile_state = prove
 (`!(s:(A,C,FFI)wl_state) y. wl_word_exp (compile_state clk c s) y = wl_word_exp s y`,
  SIMP[compile_state_def]);;
let _ = cake_add_simps [word_exp_compile_state];;

let assign_compile_state = prove
 (`wl_assign x y (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_assign x y (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_assign_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]));;
let _ = cake_add_simps [assign_compile_state];;

let inst_compile_state = prove
 (`wl_inst i (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_inst i (s:(A,C,FFI)wl_state))`,
  IL2AUX_INST_SPLIT_TAC THEN
  SIMP[wl_inst_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]) THEN REPEAT PAIRARG_TAC THEN
  SIMP[OPTION_MAP_DEF]);;
let _ = cake_add_simps [inst_compile_state];;

let cut_state_compile_state = prove
 (`wl_cut_state names (compile_state clk c s) =
   OPTION_MAP (compile_state clk c) (wl_cut_state names (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_cut_state_def] THEN SIMP[] THEN
  CASES_ON `wl_cut_env names (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
  SIMP[OPTION_MAP_DEF]);;
let _ = cake_add_simps [cut_state_compile_state];;

(* HOL4 [local] *)

let evaluate_add_clock_compile_state = prove
 (`wl_evaluate (p, compile_state clk c s) = (res, compile_state 0 c s') /\
   ~(res = SOME wl_TimeOut) ==>
   !extra. wl_evaluate (p, compile_state (clk + extra) c (s:(A,C,FFI)wl_state)) =
           (res, compile_state extra c s')`,
  STRIP_TAC THEN X_GEN_TAC `extra:num` THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `compile_state clk c (s:(A,C,FFI)wl_state)`;
                 `res:((A)wl_result)option`;
                 `compile_state 0 c (s':(A,C,FFI)wl_state)`]
         (INST [`extra:num`,`extra:num`] wl_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `wl_state_clock_fupd (K (wl_state_clock (compile_state clk c s) + extra))
      (compile_state clk c s) = compile_state (clk + extra) c (s:(A,C,FFI)wl_state) /\
    wl_state_clock_fupd (K (wl_state_clock (compile_state 0 c s') + extra))
      (compile_state 0 c s') = compile_state extra c (s':(A,C,FFI)wl_state)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[compile_state_def; wl_state_component_equality] THEN SIMP[] THEN
  ARITH_TAC);;

let compile_state_dec_clock = prove
 (`~(wl_state_clock s = 0) ==>
   compile_state clk c (wl_dec_clock s) =
   wl_dec_clock (compile_state clk c (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[compile_state_def; wl_dec_clock_def; wl_state_component_equality] THEN
  SIMP[] THEN ARITH_TAC);;
let _ = cake_add_simps [compile_state_dec_clock];;

let jump_exc_compile_state = prove
 (`wl_jump_exc (compile_state clk c s) =
   OPTION_MAP (compile_state clk c ## I) (wl_jump_exc (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]));;
let _ = cake_add_simps [jump_exc_compile_state];;

let get_var_imm_compile_state = prove
 (`wl_get_var_imm x (compile_state clk c s) = wl_get_var_imm x (s:(A,C,FFI)wl_state)`,
  CASES_ON `x:(A)reg_imm` THEN SIMP[wl_get_var_imm_def]);;
let _ = cake_add_simps [get_var_imm_compile_state];;

let push_env_case_handler = prove
 (CASE_TERM
  `wl_push_env x (match handler with
                    NONE -> NONE
                  | SOME (v,prog,l1,l2) -> SOME (v, (f:(A)wl_prog->(A)wl_prog) prog,l1,l2)) =
   (wl_push_env x handler:(A,C,FFI)wl_state->(A,C,FFI)wl_state)`,
  CASES_ON `handler:(num#(A)wl_prog#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; wl_push_env_def]);;
let _ = cake_add_simps [push_env_case_handler];;

(* HOL4 [local] *)

let pair_map_I = prove
 (`(\(k:A,v:B). (k,(f:B->C) v)) = (I ## f) /\
   (\(k:B,v:D). (f k,v)) = (f ## I)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers for word_remove_correct (WPROOF1AUX_ names).  The proof is  *)
(* by induction with wl_evaluate_ind, one tactic per clause of evaluate.     *)
(* ------------------------------------------------------------------------- *)

let WPROOF1AUX_sh_mem_set_var_compile_state = prove
 (`sh_mem_set_var r v (compile_state clk c s) =
   (I ## compile_state clk c)
     (sh_mem_set_var r v (s:(A,C,FFI)wl_state):((W)wl_result)option#(A,C,FFI)wl_state)`,
  CASES_ON `r:((FFI)ffi_result)option` THEN SIMP[sh_mem_set_var_def; PAIR_MAP_THM; I_THM] THEN
  CASES_ON `a:(FFI)ffi_result` THEN SIMP[sh_mem_set_var_def; PAIR_MAP_THM; I_THM]);;

let WPROOF1AUX_share_inst_compile_state = prove
 (`share_inst op v ad (compile_state clk c s) =
   (I ## compile_state clk c)
     (share_inst op v ad (s:(A,C,FFI)wl_state):((W)wl_result)option#(A,C,FFI)wl_state)`,
  CASES_ON `op:memop` THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
              wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
              wl_sh_mem_store_byte_def; wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  SIMP[WPROOF1AUX_sh_mem_set_var_compile_state] THEN
  REPEAT (TOP_CASE_TAC THEN
          SIMP[PAIR_MAP_THM; I_THM; WPROOF1AUX_sh_mem_set_var_compile_state]));;

let WPROOF1AUX_commute_imp = prove
 (`!p (s:(A,C,FFI)wl_state) r t.
     wl_evaluate (p, compile_state 0 c s) =
     (I ## compile_state 0 c) (wl_evaluate (p, s)) ==>
     wl_evaluate (p, s) = (r,t) ==>
     wl_evaluate (p, compile_state 0 c s) = (r, compile_state 0 c t)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM]);;

let WPROOF1AUX_is_eval_eq th =
  let c = concl th in
  is_eq c && (let l = lhs c in is_comb l && is_const (rator l) &&
                               fst(dest_const(rator l)) = "wl_evaluate");;

(* the clauses that remove_must_terminate leaves alone and that do not run  *)
(* a subprogram: the clock 0 witness, evaluation commutes with compile_state *)

let WPROOF1AUX_NONREC_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[remove_must_terminate_def] THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_is_eval_eq) THEN
  MATCH_MP_TAC WPROOF1AUX_commute_imp THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[WPROOF1AUX_share_inst_compile_state] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[PAIR_MAP_THM; I_THM; OPTION_MAP_DEF; domain_map]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_MAP_THM; I_THM; PAIR_EQ]) THEN ASM_REWRITE_TAC[];;

(* an evaluation (SOME wl_Error,_) = (res,rst) against ~(res = SOME wl_Error) *)

let WPROOF1AUX_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;;

(* compile_state and the clock *)

let WPROOF1AUX_cs_clock = prove
 (`compile_state clk c (wl_state_clock_fupd (K k) s) =
   wl_state_clock_fupd (K (k + clk)) (compile_state 0 c (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[compile_state_def; wl_state_component_equality] THEN SIMP[]);;

let WPROOF1AUX_cs_termdep = prove
 (`compile_state clk c (wl_state_termdep_fupd (K t) s) =
   compile_state clk c (s:(A,C,FFI)wl_state)`,
  REWRITE_TAC[compile_state_def; wl_state_component_equality] THEN SIMP[]);;

let WPROOF1AUX_cs_clk = prove
 (`compile_state clk c s =
   wl_state_clock_fupd (K (wl_state_clock s + clk)) (compile_state 0 c (s:(A,C,FFI)wl_state))`,
  REWRITE_TAC[compile_state_def; wl_state_component_equality] THEN SIMP[]);;

let WPROOF1AUX_clock_clock = prove
 (`wl_state_clock_fupd (K a) (wl_state_clock_fupd (K b) (r:(A,C,FFI)wl_state)) =
   wl_state_clock_fupd (K a) r`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* the clock adjustment of MustTerminate: evaluate_dec_clock, then        *)
(* evaluate_add_clock                                                       *)

let WPROOF1AUX_clock_shift = prove
 (`!q a k (s0:(A,C,FFI)wl_state) s1 res.
     wl_evaluate (q, wl_state_clock_fupd (K a) s0) = (res, s1) /\
     ~(res = SOME wl_TimeOut) ==>
     wl_evaluate (q, wl_state_clock_fupd (K (k + (a - wl_state_clock s1))) s0) =
     (res, wl_state_clock_fupd (K k) s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_dec_clock) THEN
  SIMP[WPROOF1AUX_clock_clock] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q:(A)wl_prog`;
                 `wl_state_clock_fupd (K (a - wl_state_clock (s1:(A,C,FFI)wl_state)))
                    (s0:(A,C,FFI)wl_state)`;
                 `res:((A)wl_result)option`;
                 `wl_state_clock_fupd (K 0) (s1:(A,C,FFI)wl_state)`]
        (INST [`k:num`,`extra:num`] wl_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[WPROOF1AUX_clock_clock; ADD_CLAUSES] THEN
  SUBGOAL_THEN `k + (a - wl_state_clock (s1:(A,C,FFI)wl_state)) =
                (a - wl_state_clock s1) + k` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[]]);;

let WPROOF1AUX_MT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[remove_must_terminate_def] THEN
  COND_CASES_TAC THENL [WPROOF1AUX_ERR_TAC; ALL_TAC] THEN
  PAIRARG_TAC THEN
  COND_CASES_TAC THENL [WPROOF1AUX_ERR_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
  SIMP[] THEN
  REWRITE_TAC[WPROOF1AUX_cs_clock; WPROOF1AUX_cs_termdep] THEN
  DISCH_THEN(X_CHOOSE_THEN `clk:num` (fun th ->
    MP_TAC(MATCH_MP WPROOF1AUX_clock_shift
      (CONJ th (ASSUME `~(res = SOME (wl_TimeOut:(A)wl_result))`))))) THEN
  DISCH_THEN(MP_TAC o SPEC `wl_state_clock (s:(A,C,FFI)wl_state)`) THEN
  DISCH_TAC THEN
  EXISTS_TAC `(MustTerminate_limit (:A) + clk) -
              wl_state_clock (compile_state 0 c (s1:(A,C,FFI)wl_state))` THEN
  ONCE_REWRITE_TAC[WPROOF1AUX_cs_clk] THEN
  ASM_REWRITE_TAC[WPROOF1AUX_cs_clock; WPROOF1AUX_cs_termdep; WPROOF1AUX_clock_clock;
                  ADD_CLAUSES];;

let WPROOF1AUX_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[remove_must_terminate_def] THEN
  MP_TAC(ISPEC `wl_evaluate (c1:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] o
                check (fun th -> is_forall (concl th) &&
                                 not (is_imp (snd (strip_forall (concl th))) &&
                                      is_forall (rand (snd (strip_forall (concl th))))))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1:((A)wl_result)option = NONE` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    DISCH_THEN(X_CHOOSE_TAC `clk1:num`) THEN
    SUBGOAL_THEN `wl_state_compile (s1:(A,C,FFI)wl_state) =
                  wl_state_compile (s:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL [ASM_MESON_TAC[wl_evaluate_consts]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s1:(A,C,FFI)wl_state` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `clk2:num`) THEN
    EXISTS_TAC `clk1 + clk2` THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    MP_TAC(MATCH_MP evaluate_add_clock_compile_state
      (CONJ (ASSUME `wl_evaluate (remove_must_terminate c1,
                                  compile_state clk1 c (s:(A,C,FFI)wl_state)) =
                     (NONE:((A)wl_result)option, compile_state 0 c (s1:(A,C,FFI)wl_state))`)
            (prove(`~(NONE = SOME (wl_TimeOut:(A)wl_result))`,
                   REWRITE_TAC[option_DISTINCT])))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; pair_CASE]) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `clk:num`) THEN
    EXISTS_TAC `clk:num` THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[pair_CASE]];;

(* use an induction hypothesis whose conclusion matches the goal *)

let WPROOF1AUX_IH_TAC : tactic =
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th) THEN
    ASM_MESON_TAC[]);;

(* case split on the first subterm of the goal whose head is the constant  *)
(* named c and which has no bound variables                                 *)

let WPROOF1AUX_CASES_HEAD_TAC (c:string) : tactic = fun (asl,w as g) ->
  let fvs = frees w in
  let ok t = let h,_ = strip_comb t in
             is_const h && fst(dest_const h) = c &&
             subset (frees t) (fvs @ freesl (map (concl o snd) asl)) in
  let t = find_term ok w in
  (CASES_ON t THEN CASE_REWRITE_TAC[]) g;;

let WPROOF1AUX_IF_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_must_terminate_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[] THEN
  WPROOF1AUX_CASES_HEAD_TAC "wl_get_var" THEN TRY WPROOF1AUX_ERR_TAC THEN
  WPROOF1AUX_CASES_HEAD_TAC "wl_get_var_imm" THEN TRY WPROOF1AUX_ERR_TAC THEN
  WPROOF1AUX_CASES_HEAD_TAC "wl_word_cmp" THEN TRY WPROOF1AUX_ERR_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN WPROOF1AUX_IH_TAC;;

(* strip the outer universal quantifiers of the goal, naming them ns *)

let WPROOF1AUX_NAMED_GEN_TAC (ns:string list) : tactic =
  MAP_EVERY (fun n (asl,w as g) ->
    let v,_ = dest_forall w in X_GEN_TAC (mk_var(n, type_of v)) g) ns;;

let WPROOF1AUX_LOOP_TAC : tactic =
  WPROOF1AUX_NAMED_GEN_TAC ["names"; "body"; "exit_names"; "s"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[remove_must_terminate_def] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  WPROOF1AUX_CASES_HEAD_TAC "wl_cut_state" THEN TRY WPROOF1AUX_ERR_TAC THEN
  MP_TAC(ISPEC `wl_evaluate (body:(A)wl_prog,a:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_compile (a:(A,C,FFI)wl_state) =
                wl_state_compile (s:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_state_const) THEN ASM_REWRITE_TAC[] THEN
    SIMP[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_compile (s1:(A,C,FFI)wl_state) =
                wl_state_compile (s:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[wl_evaluate_consts]; ALL_TAC] THEN
  ASM_CASES_TAC `res1 = SOME (wl_Error:(A)wl_result)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(res = SOME (wl_Error:(A)wl_result))` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    SIMP[wl_cont_loop_def; wl_exit_loop_def] THEN NO_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `a:(A,C,FFI)wl_state`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `clk:num`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_CASES_TAC `wl_cont_loop (res1:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(res1 = SOME (wl_TimeOut:(A)wl_result))` ASSUME_TAC THENL
     [ASM_MESON_TAC[cont_loop_not_timeout]; ALL_TAC] THEN
    ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `clk:num` THEN ASM_REWRITE_TAC[pair_CASE] THEN SIMP[];
      DISCH_TAC THEN
      REMOVE_THEN "ih1" (MP_TAC o SPECL [`a:(A,C,FFI)wl_state`;
         `res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `clk2:num`) THEN
      EXISTS_TAC `clk + clk2` THEN
      MP_TAC(SPEC `clk2:num` (MATCH_MP evaluate_add_clock_compile_state
        (CONJ (ASSUME `wl_evaluate (remove_must_terminate body,
                                    compile_state clk c (a:(A,C,FFI)wl_state)) =
                       res1,compile_state 0 c (s1:(A,C,FFI)wl_state)`)
              (ASSUME `~(res1 = SOME (wl_TimeOut:(A)wl_result))`)))) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
        `wl_evaluate (remove_must_terminate (wl_STOP (wl_Loop names body exit_names)),
                      compile_state clk2 c (wl_dec_clock (s1:(A,C,FFI)wl_state))) =
         res,compile_state 0 c (rst:(A,C,FFI)wl_state)` THEN
      ASM_SIMP_TAC[compile_state_dec_clock; wl_STOP_def; remove_must_terminate_def] THEN
      SIMP[ADD_EQ_0]];
    DISCH_TAC THEN EXISTS_TAC `clk:num` THEN ASM_REWRITE_TAC[pair_CASE] THEN
    POP_ASSUM MP_TAC THEN SIMP[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(WPROOF1AUX_CASES_HEAD_TAC "wl_cut_state") THEN
    REWRITE_TAC[PAIR_EQ; OPTION_MAP_DEF] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
    ASM_REWRITE_TAC[]];;

let WPROOF1AUX_list_pair_cases = prove
 (`!l:(A#B)list. l = [] \/ ?k p t. l = CONS (k,p) t`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `l:(A#B)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM EXISTS_PAIR_THM] THEN MESON_TAC[]);;

let WPROOF1AUX_FST_I_MAP = prove
 (`!(g:B->C) (p:A#B). FST ((I ## g) p) = FST p`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]);;

let WPROOF1AUX_INSTALL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[remove_must_terminate_def] THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_is_eval_eq) THEN
  MATCH_MP_TAC WPROOF1AUX_commute_imp THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_state_compile_oracle (s:(A,C,FFI)wl_state) 0` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cfg:C`; `progs:(num#num#(A)wl_prog)list`] THEN DISCH_TAC THEN
  SIMP[o_THM; PAIR_MAP_THM; I_THM] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `progs:(num#num#(A)wl_prog)list` WPROOF1AUX_list_pair_cases) THEN
  SIMP[MAP; PAIR_MAP_THM; I_THM; shift_seq_def; o_THM; WPROOF1AUX_FST_I_MAP] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[PAIR_MAP_THM; I_THM; OPTION_MAP_DEF; MAP]) THEN
  REWRITE_TAC[compile_state_def; wl_state_component_equality] THEN SIMP[] THEN
  REWRITE_TAC[map_union; map_insert; map_fromAList; pair_map_I; PAIR_MAP_THM; I_THM] THEN
  REWRITE_TAC[FUN_EQ_THM; shift_seq_def; o_THM; ETA_AX];;

(* the Call clause *)

let WPROOF1AUX_tuple5 = prove
 (`!x:A#B#C#D#E. ?a b c d e. x = (a,b,c,d,e)`,
  MESON_TAC[PAIR_SURJECTIVE]);;

let WPROOF1AUX_tuple4 = prove
 (`!x:A#B#C#D. ?a b c d. x = (a,b,c,d)`,
  MESON_TAC[PAIR_SURJECTIVE]);;

let WPROOF1AUX_option_cases3 = prove
 (`!x:(A#B#C)option. x = NONE \/ ?a b c. x = SOME (a,b,c)`,
  REWRITE_TAC[FORALL_OPTION_THM; option_DISTINCT; option_INJ; GSYM EXISTS_PAIR_THM] THEN
  MESON_TAC[]);;

(* split the first subterm t of the goal with head constant c (and no bound  *)
(* variables) into t = NONE and t = SOME pat, pat a variable or a triple      *)

let WPROOF1AUX_OCASES_TAC (c:string) (pat:term) : tactic = fun (asl,w as g) ->
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let ok t = let h,_ = strip_comb t in
             is_const h && fst(dest_const h) = c && subset (frees t) fvs in
  let t = find_term ok w in
  let th0 = if is_var pat then ISPEC t (cases "option")
            else ISPEC t WPROOF1AUX_option_cases3 in
  let vs = if is_var pat then [pat] else
           let a,bc = dest_pair pat in let b,cc = dest_pair bc in [a;b;cc] in
  let USE th = REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN ASSUME_TAC th in
  DISJ_CASES_THEN2 USE (fun th ->
      X_CHOOSE_THEN (hd vs)
        (if length vs = 1 then USE else
         X_CHOOSE_THEN (el 1 vs) (X_CHOOSE_THEN (el 2 vs) USE)) th) th0 g;;

(* split the first evaluation wl_evaluate (p,X) of the goal (no bound        *)
(* variables) into the pair (r,t)                                            *)

let WPROOF1AUX_EVAL_SPLIT_TAC (p:term) (r:term) (t:term) : tactic = fun (asl,w as g) ->
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let ok tm = is_comb tm && is_const (rator tm) &&
              fst(dest_const(rator tm)) = "wl_evaluate" &&
              fst(dest_pair(rand tm)) = p && subset (frees tm) fvs in
  let tm = find_term ok w in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   X_GEN_TAC r THEN X_GEN_TAC t THEN DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE]) g;;

(* from an assumption wl_evaluate (p, compile_state k c s) =                *)
(* (r, compile_state 0 c t) with r not TimeOut (by SIMP), add the clock     *)
(* extra                                                                    *)

let WPROOF1AUX_ADD_CLOCK_TAC (extra:term) : tactic =
  FIRST_ASSUM(fun th ->
    let r = fst(dest_pair(rhs(concl th))) in
    let nto = prove(mk_neg(mk_eq(r, `SOME (wl_TimeOut:(A)wl_result)`)), SIMP[]) in
    MP_TAC(SPEC extra (MATCH_MP evaluate_add_clock_compile_state (CONJ th nto))));;

let WPROOF1AUX_PAIR_SUBST_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC);;

let WPROOF1AUX_PAIR_SUBST_SYM_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM));;

let WPROOF1AUX_push_env_some = prove
 (`wl_push_env envs (SOME (n, remove_must_terminate p, l1, l2)) (s:(A,C,FFI)wl_state) =
   wl_push_env envs (SOME (n,p,l1,l2)) s`,
  REWRITE_TAC[wl_push_env_def]);;

(* split ret and handler, unfold the clause on both sides *)

let WPROOF1AUX_CALL0_TAC : tactic =
  WPROOF1AUX_NAMED_GEN_TAC ["ret"; "dest"; "args"; "handler"; "s"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihT") (CONJUNCTS_THEN2 (LABEL_TAC "ihR")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihE") (LABEL_TAC "ihB")))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `rv:num list#cutsets#(A)wl_prog#num#num` SUBST_ALL_TAC)
   (ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `hv:num#(A)wl_prog#num#num` SUBST_ALL_TAC)
   (ISPEC `handler:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  TRY(MP_TAC(ISPEC `rv:num list#cutsets#(A)wl_prog#num#num` WPROOF1AUX_tuple5) THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num list` (X_CHOOSE_THEN `names:cutsets`
        (X_CHOOSE_THEN `rh:(A)wl_prog` (X_CHOOSE_THEN `l1:num`
          (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)))))) THEN
  TRY(MP_TAC(ISPEC `hv:num#(A)wl_prog#num#num` WPROOF1AUX_tuple4) THEN
      DISCH_THEN(X_CHOOSE_THEN `hn:num` (X_CHOOSE_THEN `hp:(A)wl_prog`
        (X_CHOOSE_THEN `hl1:num` (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC))))) THEN
  REWRITE_TAC[remove_must_terminate_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[add_ret_loc_def];;

(* get_vars, bad_dest_args, find_code *)

let WPROOF1AUX_CALL_PRE_TAC : tactic =
  WPROOF1AUX_OCASES_TAC "wl_get_vars" `xs:((A)word_loc)list` THEN
  TRY WPROOF1AUX_ERR_TAC THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THEN ASM_REWRITE_TAC[] THEN
  TRY WPROOF1AUX_ERR_TAC THEN
  WPROOF1AUX_OCASES_TAC "wl_find_code"
    `(args1:((A)word_loc)list,prog:(A)wl_prog,ss:num option)` THEN
  TRY WPROOF1AUX_ERR_TAC THEN SIMP[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM];;

(* a tail call *)

let WPROOF1AUX_CALL_TAIL_TAC : tactic =
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (prog:(A)wl_prog,
                  wl_call_env args1 ss (wl_dec_clock (s:(A,C,FFI)wl_state)))`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:((A)wl_result)option`; `t:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THENL [WPROOF1AUX_ERR_TAC; ALL_TAC] THEN
  WPROOF1AUX_PAIR_SUBST_TAC THEN
  REMOVE_THEN "ihT" (MP_TAC o SPECL [`xs:((A)word_loc)list`; `prog:(A)wl_prog`;
                                     `args1:((A)word_loc)list`; `ss:num option`]) THEN
  ASM_REWRITE_TAC[add_ret_loc_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMP[wl_dec_clock_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `clk:num`) THEN EXISTS_TAC `clk:num` THEN
  ASM_SIMP_TAC[GSYM compile_state_dec_clock; call_env_compile_state; pair_CASE];;

(* a call with a return: the results that are passed on *)

let WPROOF1AUX_CALL_PLAIN_TAC : tactic =
  REMOVE_THEN "ihB2" MP_TAC THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_TAC `clk:num`) THEN
  WPROOF1AUX_PAIR_SUBST_SYM_TAC THEN
  EXISTS_TAC `clk:num` THEN ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[];;

(* ... a result: the return handler runs *)

let WPROOF1AUX_CALL_RESULT_TAC : tactic =
  COND_CASES_TAC THENL [WPROOF1AUX_ERR_TAC; ALL_TAC] THEN
  WPROOF1AUX_OCASES_TAC "wl_pop_env" `s1:(A,C,FFI)wl_state` THEN TRY WPROOF1AUX_ERR_TAC THEN
  COND_CASES_TAC THENL [ALL_TAC; WPROOF1AUX_ERR_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wl_state_compile (s1:(A,C,FFI)wl_state) =
                wl_state_compile (s:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP wl_pop_env_const o
                check (fun th -> can (term_match []
                                        `wl_pop_env (x:(A,C,FFI)wl_state) = SOME y`)
                                     (concl th))) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_consts o
                check (fun th -> WPROOF1AUX_is_eval_eq th &&
                                 snd (dest_pair (rhs (concl th))) = `s2:(A,C,FFI)wl_state`)) THEN
    SIMP[wl_dec_clock_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ihR" (MP_TAC o SPECL [`xs:((A)word_loc)list`; `names:cutsets`;
     `prog:(A)wl_prog`; `args1:((A)word_loc)list`; `ss:num option`; `a0:(A)word_loc`;
     `l1:num`; `l2:num`; `s2:(A,C,FFI)wl_state`;
     `envs:((A)word_loc)spt#((A)word_loc)spt`; `rh:(A)wl_prog`;
     `n:num list`; `a1:((A)word_loc)list`; `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[add_ret_loc_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMP[wl_set_vars_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `clk2:num`) THEN
  REMOVE_THEN "ihB2" MP_TAC THEN SIMP[] THEN DISCH_THEN(X_CHOOSE_TAC `clk1:num`) THEN
  EXISTS_TAC `clk1 + clk2` THEN WPROOF1AUX_ADD_CLOCK_TAC `clk2:num` THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[] THEN
  SIMP[OPTION_MAP_DEF];;

(* ... an exception caught by the handler *)

let WPROOF1AUX_CALL_EXC_TAC : tactic =
  COND_CASES_TAC THENL [WPROOF1AUX_ERR_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; WPROOF1AUX_ERR_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wl_state_compile (s2:(A,C,FFI)wl_state) =
                wl_state_compile (s:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_consts o
                check (fun th -> WPROOF1AUX_is_eval_eq th &&
                                 snd (dest_pair (rhs (concl th))) = `s2:(A,C,FFI)wl_state`)) THEN
    SIMP[wl_dec_clock_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ihE" (MP_TAC o SPECL [`xs:((A)word_loc)list`; `rh:(A)wl_prog`; `l1:num`;
     `l2:num`; `n:num list`; `names:cutsets`; `prog:(A)wl_prog`;
     `args1:((A)word_loc)list`; `ss:num option`; `a0:(A)word_loc`; `hl1:num`; `hl2:num`;
     `envs:((A)word_loc)spt#((A)word_loc)spt`; `hp:(A)wl_prog`; `hn:num`;
     `a1:(A)word_loc`; `s2:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[add_ret_loc_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMP[wl_set_var_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `clk2:num`) THEN
  REMOVE_THEN "ihB2" MP_TAC THEN SIMP[] THEN DISCH_THEN(X_CHOOSE_TAC `clk1:num`) THEN
  EXISTS_TAC `clk1 + clk2` THEN WPROOF1AUX_ADD_CLOCK_TAC `clk2:num` THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[] THEN
  SIMP[OPTION_MAP_DEF];;

(* a call with a return *)

let WPROOF1AUX_CALL_RET_TAC : tactic =
  COND_CASES_TAC THENL [WPROOF1AUX_ERR_TAC; ALL_TAC] THEN
  WPROOF1AUX_OCASES_TAC "cut_envs" `envs:((A)word_loc)spt#((A)word_loc)spt` THEN
  TRY WPROOF1AUX_ERR_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[] THEN SIMP[WPROOF1AUX_push_env_some]; ALL_TAC] THEN
  ASM_SIMP_TAC[WPROOF1AUX_push_env_some; GSYM compile_state_dec_clock;
               push_env_compile_state; call_env_compile_state] THEN
  WPROOF1AUX_EVAL_SPLIT_TAC `prog:(A)wl_prog` `r:((A)wl_result)option`
    `s2:(A,C,FFI)wl_state` THEN
  REMOVE_THEN "ihB" (MP_TAC o SPECL [`xs:((A)word_loc)list`; `rh:(A)wl_prog`; `l1:num`;
     `l2:num`; `n:num list`; `names:cutsets`; `prog:(A)wl_prog`;
     `args1:((A)word_loc)list`; `ss:num option`;
     `envs:((A)word_loc)spt#((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC[add_ret_loc_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[IMP_CONJ] THEN ANTS_TAC THENL [SIMP[wl_dec_clock_def]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ihB2") THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)
   (ISPEC `r:((A)wl_result)option` (cases "option")) THEN CASE_REWRITE_TAC[] THEN
  TRY WPROOF1AUX_ERR_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `rr:(A)wl_result` (cases "wl_result")) THEN CASE_REWRITE_TAC[] THEN
  TRY WPROOF1AUX_ERR_TAC THEN
  FIRST [WPROOF1AUX_CALL_PLAIN_TAC THEN NO_TAC; WPROOF1AUX_CALL_RESULT_TAC THEN NO_TAC;
         WPROOF1AUX_CALL_EXC_TAC THEN NO_TAC];;

let WPROOF1AUX_CALL_TAC : tactic =
  WPROOF1AUX_CALL0_TAC THEN WPROOF1AUX_CALL_PRE_TAC THEN
  FIRST [WPROOF1AUX_CALL_TAIL_TAC THEN NO_TAC; WPROOF1AUX_CALL_RET_TAC];;

let word_remove_correct = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst.
     wl_evaluate (prog,st) = (res,rst) /\
     wl_state_compile st = (\cfg. c cfg o MAP (I ## I ## remove_must_terminate)) /\
     ~(res = SOME wl_Error)
     ==> ?clk. wl_evaluate (remove_must_terminate prog, compile_state clk c st) =
               (res, compile_state 0 c rst)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate WPROOF1AUX_NONREC_TAC 11 @
    [WPROOF1AUX_MT_TAC; WPROOF1AUX_SEQ_TAC] @
    replicate WPROOF1AUX_NONREC_TAC 4 @
    [WPROOF1AUX_IF_TAC; WPROOF1AUX_LOOP_TAC; WPROOF1AUX_NONREC_TAC;
     WPROOF1AUX_INSTALL_TAC] @
    replicate WPROOF1AUX_NONREC_TAC 4 @
    [WPROOF1AUX_CALL_TAC]));;
