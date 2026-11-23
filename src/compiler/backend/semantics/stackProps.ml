(* ========================================================================= *)
(* stackProps: port of HOL4 compiler/backend/semantics/stackPropsScript.sml  *)
(* (CakeML v3479).                                                           *)
(* Properties about stackLang and its semantics.                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: case_eq_thms (the case equations, as AllCaseEqs()) *)

let stack_case_eq_thms = end_itlist CONJ
  [pair_case_eq; COND_CASE_EQ; option_case_eq; list_case_eq;
   case_eq "word_loc"; case_eq "inst"; case_eq "binop"; case_eq "reg_imm";
   case_eq "asm_arith"; case_eq "addr"; case_eq "memop";
   case_eq "stack_result"; case_eq "ffi_result"];;

let stack_set_store_const = prove
 (`stack_state_ffi (stack_set_store x y (z:(A,C,FFI)stack_state)) =
     stack_state_ffi z /\
   stack_state_clock (stack_set_store x y z) = stack_state_clock z /\
   stack_state_use_alloc (stack_set_store x y z) = stack_state_use_alloc z /\
   stack_state_use_store (stack_set_store x y z) = stack_state_use_store z /\
   stack_state_use_stack (stack_set_store x y z) = stack_state_use_stack z /\
   stack_state_code (stack_set_store x y z) = stack_state_code z /\
   stack_state_be (stack_set_store x y z) = stack_state_be z /\
   stack_state_gc_fun (stack_set_store x y z) = stack_state_gc_fun z /\
   stack_state_memory (stack_set_store x y z) = stack_state_memory z /\
   stack_state_mdomain (stack_set_store x y z) = stack_state_mdomain z /\
   stack_state_sh_mdomain (stack_set_store x y z) = stack_state_sh_mdomain z /\
   stack_state_bitmaps (stack_set_store x y z) = stack_state_bitmaps z /\
   stack_state_data_buffer (stack_set_store x y z) = stack_state_data_buffer z /\
   stack_state_code_buffer (stack_set_store x y z) = stack_state_code_buffer z /\
   stack_state_compile (stack_set_store x y z) = stack_state_compile z /\
   stack_state_compile_oracle (stack_set_store x y z) =
     stack_state_compile_oracle z /\
   stack_state_stack_space (stack_set_store x y z) = stack_state_stack_space z /\
   stack_state_stack (stack_set_store x y z) = stack_state_stack z`,
  REWRITE_TAC[stack_set_store_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_set_store_const];;

let stack_set_store_with_const = prove
 (`stack_set_store x y (stack_state_clock_fupd (K a) (z:(A,C,FFI)stack_state)) =
   stack_state_clock_fupd (K a) (stack_set_store x y z)`,
  REWRITE_TAC[stack_set_store_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_set_store_with_const];;

let stack_set_var_const = prove
 (`stack_state_ffi (stack_set_var x y (z:(A,C,FFI)stack_state)) =
     stack_state_ffi z /\
   stack_state_clock (stack_set_var x y z) = stack_state_clock z /\
   stack_state_use_alloc (stack_set_var x y z) = stack_state_use_alloc z /\
   stack_state_use_store (stack_set_var x y z) = stack_state_use_store z /\
   stack_state_use_stack (stack_set_var x y z) = stack_state_use_stack z /\
   stack_state_code (stack_set_var x y z) = stack_state_code z /\
   stack_state_be (stack_set_var x y z) = stack_state_be z /\
   stack_state_fp_regs (stack_set_var x y z) = stack_state_fp_regs z /\
   stack_state_data_buffer (stack_set_var x y z) = stack_state_data_buffer z /\
   stack_state_code_buffer (stack_set_var x y z) = stack_state_code_buffer z /\
   stack_state_gc_fun (stack_set_var x y z) = stack_state_gc_fun z /\
   stack_state_memory (stack_set_var x y z) = stack_state_memory z /\
   stack_state_mdomain (stack_set_var x y z) = stack_state_mdomain z /\
   stack_state_sh_mdomain (stack_set_var x y z) = stack_state_sh_mdomain z /\
   stack_state_bitmaps (stack_set_var x y z) = stack_state_bitmaps z /\
   stack_state_compile (stack_set_var x y z) = stack_state_compile z /\
   stack_state_compile_oracle (stack_set_var x y z) =
     stack_state_compile_oracle z /\
   stack_state_store (stack_set_var x y z) = stack_state_store z /\
   stack_state_stack (stack_set_var x y z) = stack_state_stack z /\
   stack_state_stack_space (stack_set_var x y z) = stack_state_stack_space z`,
  REWRITE_TAC[stack_set_var_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_set_var_const];;

let stack_set_var_with_const = prove
 (`stack_set_var x y (stack_state_clock_fupd (K clk) (z:(A,C,FFI)stack_state)) =
     stack_state_clock_fupd (K clk) (stack_set_var x y z) /\
   stack_set_var x y (stack_state_memory_fupd (K m) z) =
     stack_state_memory_fupd (K m) (stack_set_var x y z) /\
   stack_set_var x y (stack_state_ffi_fupd (K ffi) z) =
     stack_state_ffi_fupd (K ffi) (stack_set_var x y z) /\
   stack_set_var x y (stack_state_stack_fupd (K stk) z) =
     stack_state_stack_fupd (K stk) (stack_set_var x y z) /\
   stack_set_var x y (stack_state_stack_space_fupd (K stk_space) z) =
     stack_state_stack_space_fupd (K stk_space) (stack_set_var x y z)`,
  REWRITE_TAC[stack_set_var_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_set_var_with_const];;

(* HOL4 [local] *)

let stack_set_fp_var_with_const = prove
 (`stack_set_fp_var x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   stack_state_clock_fupd (K k) (stack_set_fp_var x y z)`,
  REWRITE_TAC[stack_set_fp_var_def] THEN SIMP[]);;

(* HOL4 [local] set_fp_var_const, rebound later in the script by the        *)
(* exported set_fp_var_const (stack_set_fp_var_const below)                 *)

let STACKPROPSAUX_set_fp_var_const = prove
 (`stack_state_ffi (stack_set_fp_var x y (z:(A,C,FFI)stack_state)) =
     stack_state_ffi z /\
   stack_state_clock (stack_set_fp_var x y z) = stack_state_clock z /\
   stack_state_use_alloc (stack_set_fp_var x y z) = stack_state_use_alloc z /\
   stack_state_use_store (stack_set_fp_var x y z) = stack_state_use_store z /\
   stack_state_use_stack (stack_set_fp_var x y z) = stack_state_use_stack z /\
   stack_state_code (stack_set_fp_var x y z) = stack_state_code z /\
   stack_state_be (stack_set_fp_var x y z) = stack_state_be z /\
   stack_state_gc_fun (stack_set_fp_var x y z) = stack_state_gc_fun z /\
   stack_state_mdomain (stack_set_fp_var x y z) = stack_state_mdomain z /\
   stack_state_sh_mdomain (stack_set_fp_var x y z) = stack_state_sh_mdomain z /\
   stack_state_bitmaps (stack_set_fp_var x y z) = stack_state_bitmaps z /\
   stack_state_compile (stack_set_fp_var x y z) = stack_state_compile z /\
   stack_state_compile_oracle (stack_set_fp_var x y z) =
     stack_state_compile_oracle z /\
   stack_state_stack (stack_set_fp_var x y z) = stack_state_stack z /\
   stack_state_stack_space (stack_set_fp_var x y z) = stack_state_stack_space z`,
  REWRITE_TAC[stack_set_fp_var_def] THEN SIMP[]);;

(* HOL4 [local] *)

let stack_get_fp_var_with_const = prove
 (`stack_get_fp_var x (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
   stack_get_fp_var x y`,
  REWRITE_TAC[stack_get_fp_var_def] THEN SIMP[]);;

let stack_get_var_with_const = prove
 (`stack_get_var r (stack_state_clock_fupd (K clk) (t:(A,C,FFI)stack_state)) =
     stack_get_var r t /\
   stack_get_var r (stack_state_stack_space_fupd (K stk_space) t) =
     stack_get_var r t`,
  REWRITE_TAC[stack_get_var_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_get_var_with_const];;

(* HOL4 [local] *)

let stack_get_vars_with_const = prove
 (`!xs. stack_get_vars xs (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
        stack_get_vars xs y`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[stack_get_vars_def; stack_get_var_with_const]);;

let stack_get_var_imm_with_const = prove
 (`stack_get_var_imm x (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
   stack_get_var_imm x y`,
  CASES_ON `x:(A)reg_imm` THEN
  REWRITE_TAC[stack_get_var_imm_def; stack_get_var_with_const]);;
let _ = cake_add_simps [stack_get_var_imm_with_const];;

let stack_set_fp_var_const = prove
 (`stack_state_stack_space (stack_set_fp_var x y (z:(A,C,FFI)stack_state)) =
     stack_state_stack_space z /\
   stack_state_stack (stack_set_fp_var x y z) = stack_state_stack z`,
  REWRITE_TAC[stack_set_fp_var_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_set_fp_var_const];;

let empty_env_const = prove
 (`stack_state_ffi (stack_empty_env (x:(A,C,FFI)stack_state)) = stack_state_ffi x /\
   stack_state_clock (stack_empty_env x) = stack_state_clock x /\
   stack_state_use_alloc (stack_empty_env (z:(A,C,FFI)stack_state)) =
     stack_state_use_alloc z /\
   stack_state_use_store (stack_empty_env z) = stack_state_use_store z /\
   stack_state_use_stack (stack_empty_env z) = stack_state_use_stack z /\
   stack_state_code (stack_empty_env z) = stack_state_code z /\
   stack_state_be (stack_empty_env z) = stack_state_be z /\
   stack_state_gc_fun (stack_empty_env z) = stack_state_gc_fun z /\
   stack_state_mdomain (stack_empty_env z) = stack_state_mdomain z /\
   stack_state_sh_mdomain (stack_empty_env z) = stack_state_sh_mdomain z /\
   stack_state_bitmaps (stack_empty_env z) = stack_state_bitmaps z /\
   stack_state_data_buffer (stack_empty_env z) = stack_state_data_buffer z /\
   stack_state_code_buffer (stack_empty_env z) = stack_state_code_buffer z /\
   stack_state_compile (stack_empty_env z) = stack_state_compile z /\
   stack_state_compile_oracle (stack_empty_env z) = stack_state_compile_oracle z`,
  REWRITE_TAC[stack_empty_env_def] THEN SIMP[]);;
let _ = cake_add_simps [empty_env_const];;

let empty_env_with_const = prove
 (`stack_empty_env (stack_state_clock_fupd (K y) (x:(A,C,FFI)stack_state)) =
   stack_state_clock_fupd (K y) (stack_empty_env x)`,
  REWRITE_TAC[stack_empty_env_def] THEN SIMP[]);;
let _ = cake_add_simps [empty_env_with_const];;

let stack_alloc_const = prove
 (`stackSem_alloc w (s:(A,C,FFI)stack_state) = (r,t) ==>
   stack_state_ffi t = stack_state_ffi s /\
   stack_state_clock t = stack_state_clock s /\
   stack_state_use_alloc t = stack_state_use_alloc s /\
   stack_state_use_store t = stack_state_use_store s /\
   stack_state_use_stack t = stack_state_use_stack s /\
   stack_state_code t = stack_state_code s /\
   stack_state_be t = stack_state_be s /\
   stack_state_gc_fun t = stack_state_gc_fun s /\
   stack_state_mdomain t = stack_state_mdomain s /\
   stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
   stack_state_bitmaps t = stack_state_bitmaps s /\
   stack_state_compile t = stack_state_compile s /\
   stack_state_data_buffer t = stack_state_data_buffer s /\
   stack_state_code_buffer t = stack_state_code_buffer s /\
   stack_state_compile_oracle t = stack_state_compile_oracle s`,
  REWRITE_TAC[stackSem_alloc_def; stack_gc_def; LET_DEF; LET_END_DEF] THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN SIMP[]);;

let store_const_sem_const = prove
 (`store_const_sem t1 t2 (s:(A,C,FFI)stack_state) = (r,t) ==>
   stack_state_ffi t = stack_state_ffi s /\
   stack_state_clock t = stack_state_clock s /\
   stack_state_use_alloc t = stack_state_use_alloc s /\
   stack_state_use_store t = stack_state_use_store s /\
   stack_state_use_stack t = stack_state_use_stack s /\
   stack_state_code t = stack_state_code s /\
   stack_state_be t = stack_state_be s /\
   stack_state_gc_fun t = stack_state_gc_fun s /\
   stack_state_mdomain t = stack_state_mdomain s /\
   stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
   stack_state_bitmaps t = stack_state_bitmaps s /\
   stack_state_compile t = stack_state_compile s /\
   stack_state_store t = stack_state_store s /\
   stack_state_data_buffer t = stack_state_data_buffer s /\
   stack_state_code_buffer t = stack_state_code_buffer s /\
   stack_state_compile_oracle t = stack_state_compile_oracle s`,
  REWRITE_TAC[store_const_sem_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[stack_unset_var_def; I_THM] THEN SIMP[]);;

let stack_gc_with_const = prove
 (`stack_gc (stack_state_clock_fupd (K k) (x:(A,C,FFI)stack_state)) =
   OPTION_MAP (\s. stack_state_clock_fupd (K k) s) (stack_gc x)`,
  REWRITE_TAC[stack_gc_def; LET_DEF; LET_END_DEF] THEN SIMP[] THEN
  EVERY_CASE_TAC THEN SIMP[OPTION_MAP_DEF]);;
let _ = cake_add_simps [stack_gc_with_const];;

let stack_alloc_with_const = prove
 (`stackSem_alloc x (stack_state_clock_fupd (K z) (y:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K z) s)) (stackSem_alloc x y)`,
  REWRITE_TAC[stackSem_alloc_def] THEN SIMP[] THEN
  CASES_ON `stack_gc (stack_set_store AllocSize (wl_Word x) (y:(A,C,FFI)stack_state))` THEN
  SIMP[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM] THEN EVERY_CASE_TAC THEN
  SIMP[PAIR_MAP_THM; I_THM]);;
let _ = cake_add_simps [stack_alloc_with_const];;

let store_const_sem_with_const = prove
 (`store_const_sem t1 t2 (stack_state_clock_fupd (K z) (y:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K z) s)) (store_const_sem t1 t2 y)`,
  REWRITE_TAC[store_const_sem_def; stack_get_var_def] THEN SIMP[] THEN
  EVERY_CASE_TAC THEN
  SIMP[PAIR_MAP_THM; I_THM; stack_unset_var_def; stack_set_var_def]);;
let _ = cake_add_simps [store_const_sem_with_const];;

(* HOL4: mem_load_with_const (a statement about mem_store) *)

let stack_mem_load_with_const = prove
 (`stack_mem_store x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   OPTION_MAP (\s. stack_state_clock_fupd (K k) s) (stack_mem_store x y z)`,
  REWRITE_TAC[stack_mem_store_def] THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[OPTION_MAP_DEF]);;
let _ = cake_add_simps [stack_mem_load_with_const];;

let STACKPROPSAUX_SH_WITH_TAC def : tactic =
  REWRITE_TAC[def; stack_get_var_def] THEN SIMP[] THEN EVERY_CASE_TAC THEN
  SIMP[PAIR_MAP_THM; I_THM];;

let stack_sh_mem_load_with_const = prove
 (`stack_sh_mem_load r x (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_load r x y)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_load_def);;
let _ = cake_add_simps [stack_sh_mem_load_with_const];;

let stack_sh_mem_store_with_const = prove
 (`stack_sh_mem_store x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_store x y z)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_store_def);;
let _ = cake_add_simps [stack_sh_mem_store_with_const];;

let stack_sh_mem_load32_with_const = prove
 (`stack_sh_mem_load32 r x (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_load32 r x y)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_load32_def);;
let _ = cake_add_simps [stack_sh_mem_load32_with_const];;

let stack_sh_mem_store32_with_const = prove
 (`stack_sh_mem_store32 x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_store32 x y z)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_store32_def);;
let _ = cake_add_simps [stack_sh_mem_store32_with_const];;

let stack_sh_mem_load16_with_const = prove
 (`stack_sh_mem_load16 r x (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_load16 r x y)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_load16_def);;
let _ = cake_add_simps [stack_sh_mem_load16_with_const];;

let stack_sh_mem_store16_with_const = prove
 (`stack_sh_mem_store16 x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_store16 x y z)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_store16_def);;
let _ = cake_add_simps [stack_sh_mem_store16_with_const];;

let stack_sh_mem_load_byte_with_const = prove
 (`stack_sh_mem_load_byte r x (stack_state_clock_fupd (K k) (y:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_load_byte r x y)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_load_byte_def);;
let _ = cake_add_simps [stack_sh_mem_load_byte_with_const];;

let stack_sh_mem_store_byte_with_const = prove
 (`stack_sh_mem_store_byte x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (stack_sh_mem_store_byte x y z)`,
  STACKPROPSAUX_SH_WITH_TAC stack_sh_mem_store_byte_def);;
let _ = cake_add_simps [stack_sh_mem_store_byte_with_const];;

(* HOL4 [local] *)

let sh_mem_op_with_const = prove
 (`sh_mem_op op x y (stack_state_clock_fupd (K k) (z:(A,C,FFI)stack_state)) =
   (I ## (\s. stack_state_clock_fupd (K k) s)) (sh_mem_op op x y z)`,
  CASES_ON `op:memop` THEN REWRITE_TAC[sh_mem_op_def] THEN
  REWRITE_TAC[stack_sh_mem_load_with_const; stack_sh_mem_store_with_const;
              stack_sh_mem_load32_with_const; stack_sh_mem_store32_with_const;
              stack_sh_mem_load16_with_const; stack_sh_mem_store16_with_const;
              stack_sh_mem_load_byte_with_const; stack_sh_mem_store_byte_with_const]);;

(* the HOL4 [local,simp] theorems: not registered (the simpset of the files *)
(* that load this one would get them), given to the proofs below instead    *)

let STACKPROPSAUX_local_simps =
  [stack_set_fp_var_with_const; STACKPROPSAUX_set_fp_var_const;
   stack_get_fp_var_with_const; stack_get_vars_with_const; sh_mem_op_with_const];;

let stack_word_exp_with_const = prove
 (`!s y k. stack_word_exp (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) y =
           stack_word_exp s y`,
  MATCH_MP_TAC stack_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[stack_word_exp_def];
    REWRITE_TAC[stack_word_exp_def] THEN SIMP[];
    REWRITE_TAC[stack_word_exp_def] THEN SIMP[];
    DISCH_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    ASM_REWRITE_TAC[stack_mem_load_def] THEN SIMP[];
    DISCH_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    SUBGOAL_THEN
     `MAP (stack_word_exp (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)))
          wexps = MAP (stack_word_exp s) wexps`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[];
    STRIP_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    ASM_REWRITE_TAC[]]);;
let _ = cake_add_simps [stack_word_exp_with_const];;

let stack_assign_with_const = prove
 (`stack_assign x y (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
   OPTION_MAP (\s. stack_state_clock_fupd (K k) s) (stack_assign x y s)`,
  REWRITE_TAC[stack_assign_def; stack_word_exp_with_const] THEN
  CASES_ON `stack_word_exp (s:(A,C,FFI)stack_state) y` THEN
  SIMP[OPTION_MAP_DEF]);;
let _ = cake_add_simps [stack_assign_with_const];;

let stack_inst_const = prove
 (`stack_inst i (s:(A,C,FFI)stack_state) = SOME t ==>
   stack_state_ffi t = stack_state_ffi s /\
   stack_state_clock t = stack_state_clock s /\
   stack_state_use_alloc t = stack_state_use_alloc s /\
   stack_state_use_store t = stack_state_use_store s /\
   stack_state_use_stack t = stack_state_use_stack s /\
   stack_state_code t = stack_state_code s /\
   stack_state_be t = stack_state_be s /\
   stack_state_gc_fun t = stack_state_gc_fun s /\
   stack_state_mdomain t = stack_state_mdomain s /\
   stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
   stack_state_bitmaps t = stack_state_bitmaps s /\
   stack_state_compile t = stack_state_compile s /\
   stack_state_compile_oracle t = stack_state_compile_oracle s`,
  REWRITE_TAC[stack_inst_def; stack_assign_def; stack_mem_store_def;
              LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP STACKPROPSAUX_local_simps);;

let STACKPROPSAUX_mem_load_with_const = prove
 (`stack_mem_load a (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
   stack_mem_load a s`,
  REWRITE_TAC[stack_mem_load_def] THEN SIMP[]);;

let stack_inst_with_const = prove
 (`stack_inst i (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
   OPTION_MAP (\s. stack_state_clock_fupd (K k) s) (stack_inst i s)`,
  REWRITE_TAC[stack_inst_def] THEN
  SIMP(STACKPROPSAUX_mem_load_with_const :: STACKPROPSAUX_local_simps) THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF; LET_DEF; LET_END_DEF]) THEN
  FS[OPTION_MAP_DEF]);;
let _ = cake_add_simps [stack_inst_with_const];;

let stack_dec_clock_const = prove
 (`stack_state_ffi (stack_dec_clock (s:(A,C,FFI)stack_state)) = stack_state_ffi s /\
   stack_state_use_alloc (stack_dec_clock (z:(A,C,FFI)stack_state)) =
     stack_state_use_alloc z /\
   stack_state_use_store (stack_dec_clock z) = stack_state_use_store z /\
   stack_state_use_stack (stack_dec_clock z) = stack_state_use_stack z /\
   stack_state_stack (stack_dec_clock z) = stack_state_stack z /\
   stack_state_store (stack_dec_clock z) = stack_state_store z /\
   stack_state_code (stack_dec_clock z) = stack_state_code z /\
   stack_state_data_buffer (stack_dec_clock z) = stack_state_data_buffer z /\
   stack_state_code_buffer (stack_dec_clock z) = stack_state_code_buffer z /\
   stack_state_fp_regs (stack_dec_clock z) = stack_state_fp_regs z /\
   stack_state_be (stack_dec_clock z) = stack_state_be z /\
   stack_state_gc_fun (stack_dec_clock z) = stack_state_gc_fun z /\
   stack_state_memory (stack_dec_clock z) = stack_state_memory z /\
   stack_state_mdomain (stack_dec_clock z) = stack_state_mdomain z /\
   stack_state_sh_mdomain (stack_dec_clock z) = stack_state_sh_mdomain z /\
   stack_state_bitmaps (stack_dec_clock z) = stack_state_bitmaps z /\
   stack_state_stack_space (stack_dec_clock z) = stack_state_stack_space z /\
   stack_state_compile (stack_dec_clock z) = stack_state_compile z /\
   stack_state_compile_oracle (stack_dec_clock z) = stack_state_compile_oracle z`,
  REWRITE_TAC[stack_dec_clock_def] THEN SIMP[]);;
let _ = cake_add_simps [stack_dec_clock_const];;

(* HOL4 [simp]; a conditional rewrite with variables of its hypothesis that *)
(* its conclusion lacks: not registered                                      *)

let sh_mem_op_const = prove
 (`sh_mem_op op a r (s:(A,C,FFI)stack_state) = (res,t) ==>
   stack_state_clock t = stack_state_clock s /\
   stack_state_use_alloc t = stack_state_use_alloc s /\
   stack_state_use_store t = stack_state_use_store s /\
   stack_state_use_stack t = stack_state_use_stack s /\
   stack_state_code t = stack_state_code s /\
   stack_state_be t = stack_state_be s /\
   stack_state_gc_fun t = stack_state_gc_fun s /\
   stack_state_mdomain t = stack_state_mdomain s /\
   stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
   stack_state_bitmaps t = stack_state_bitmaps s /\
   stack_state_compile t = stack_state_compile s /\
   stack_state_compile_oracle t = stack_state_compile_oracle s`,
  CASES_ON `op:memop` THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_load_def;
              stack_sh_mem_store32_def; stack_sh_mem_load32_def;
              stack_sh_mem_load16_def; stack_sh_mem_store16_def;
              stack_sh_mem_store_byte_def; stack_sh_mem_load_byte_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[]);;

(* ------------------------------------------------------------------------- *)
(* Proof machinery for the theorems about stack_evaluate proved by           *)
(* induction (stack_evaluate_ind), in the style of stackSem.ml's proof of    *)
(* stack_evaluate_clock: unfold the evaluate assumption of the clause once,  *)
(* split it into its cases, and instantiate the induction hypotheses at the  *)
(* evaluate assumptions.                                                     *)
(* ------------------------------------------------------------------------- *)

(* prove ?vs. A1 /\ ... /\ An from the assumptions: each existential       *)
(* variable is found by matching a conjunct with an assumption (or the two  *)
(* sides of an equation); the instance is proved conjunct by conjunct, by  *)
(* an assumption or by the tactic side                                      *)

let STACKPROPSAUX_EXISTS_ASM_TAC (side:tactic) : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let facts = map (concl o snd) asl in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let fvs = filter (fun v -> mem v vs && not (can (rev_assoc v) theta))
                         (frees c') in
        if fvs = [] then go theta rest else
        let try_m p t =
          let (_,tmi,tyi) = term_match [] p t in
          if forall (fun (t,v) -> mem v fvs || t = v) tmi &&
             forall (fun (a,b) -> a = b) tyi
          then filter (fun (t,v) -> mem v fvs) tmi else failwith "" in
        let tmi = try tryfind (try_m c') facts
                  with Failure _ ->
                    try let l,r = dest_eq c' in
                        (try try_m r l with Failure _ -> try_m l r)
                    with Failure _ -> [] in
        go (tmi @ theta) rest in
  let theta = go [] (conjuncts body) in
  let wits = map (fun v -> try rev_assoc v theta with Failure _ -> v) vs in
  (MAP_EVERY EXISTS_TAC wits THEN REPEAT CONJ_TAC THEN
   (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE side)) g;;

(* for every induction hypothesis (an implication with evaluate equations   *)
(* in its antecedent), match all its evaluate equations with evaluate       *)
(* assumptions, and add the instance of its conclusion when its other       *)
(* antecedents follow (STACKPROPSAUX_EXISTS_ASM_TAC side)                   *)

let STACKPROPSAUX_USE_IHS_TAC (side:tactic) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> STACKPAUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists STACKPAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  (* the fresh names also avoid the variables of the hypotheses of the     *)
  (* assumptions (an instance must not change them: VALID)                 *)
  let avoid = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
  let insts_of ih0 =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = SPECL vs1 ih0 in
    let ant,_ = dest_imp (concl ih) in
    let ecjs = filter STACKPAUX_is_eval_eq (conjuncts ant) in
    let rec go theta cjs =
      match cjs with
        [] -> [theta]
      | c::rest ->
          let c' = vsubst theta c in
          flat (map (fun e ->
            try let (_,tmi,tyi) = term_match [] c' (concl e) in
                if exists (fun (a,b) -> not (a = b)) tyi ||
                   exists (fun (t,v) -> not (mem v vs1) && not (t = v)) tmi
                then [] else
                go (filter (fun (t,v) -> mem v vs1 && not (t = v)) tmi @ theta) rest
            with Failure _ -> []) evs) in
    map (fun theta ->
        let ihi = SPECL (map (fun v -> try rev_assoc v theta with Failure _ -> v) vs1)
                        ih0 in
        let a,c = dest_imp (concl ihi) in
        let rest = filter (fun v -> mem v vs1) (subtract (frees a) (frees c)) in
        c, GENL rest ihi) (go [] ecjs) in
  let insts = flat (map insts_of ihs) in
  MAP_EVERY (fun (c,th) ->
      TRY (fun (asl,w as g) ->
             let th' = TAC_PROOF((asl,c),
                         MATCH_MP_TAC th THEN STACKPROPSAUX_EXISTS_ASM_TAC side THEN
                         NO_TAC) in
             STRIP_ASSUME_TAC th' g))
    insts g;;

(* the start of each case: strip, unfold the evaluate assumption (the last  *)
(* one) once, split it into its cases                                       *)

let STACKPROPSAUX_SPLIT_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  REWRITE_TAC(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC;;

(* induction on the program and state of stack_evaluate: the statement     *)
(* !c s. Q c s is proved by stack_evaluate_ind on the pair                   *)

let STACKPROPSAUX_PAIR_IND = prove
 (`!P:(A)stack_prog->(A,C,FFI)stack_state->bool.
     (!p. P (FST p) (SND p)) ==> (!c s. P c s)`,
  MESON_TAC[FST; SND]);;

let STACKPROPSAUX_EVAL_IND_TAC : tactic =
  MATCH_MP_TAC STACKPROPSAUX_PAIR_IND THEN MATCH_MP_TAC stack_evaluate_ind THEN
  REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC;;

(* the facts MATCH_MP th a for every assumption a and every th of ths       *)
(* (the assumptions are kept)                                               *)

let STACKPROPSAUX_FACTS_TAC (ths:thm list) : tactic =
  ASSUM_LIST (fun asms ->
    MAP_EVERY (fun a -> MAP_EVERY (fun th g ->
        try STRIP_ASSUME_TAC (MATCH_MP th a) g with Failure _ -> ALL_TAC g) ths) asms);;

let STACKPROPSAUX_CONST_FACTS_TAC : tactic =
  STACKPROPSAUX_FACTS_TAC
    [stack_alloc_const; stack_inst_const; store_const_sem_const; sh_mem_op_const];;

let STACKPROPSAUX_DROP_IHS_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th -> if is_forall (concl th) then ALL_TAC
                                   else failwith "keep"));;

let STACKPROPSAUX_CONSTS_TAC : tactic =
  STACKPROPSAUX_SPLIT_TAC THEN
  STACKPROPSAUX_USE_IHS_TAC (ASM_REWRITE_TAC[]) THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  STACKPROPSAUX_CONST_FACTS_TAC THEN
  ASM_REWRITE_TAC[] THEN SIMP[stack_unset_var_def; stack_dec_clock_def; I_THM];;

let stack_evaluate_consts = prove
 (`!c (s:(A,C,FFI)stack_state) r s1.
      stack_evaluate (c,s) = (r,s1) ==>
      stack_state_use_alloc s1 = stack_state_use_alloc s /\
      stack_state_use_store s1 = stack_state_use_store s /\
      stack_state_use_stack s1 = stack_state_use_stack s /\
      stack_state_be s1 = stack_state_be s /\
      stack_state_gc_fun s1 = stack_state_gc_fun s /\
      stack_state_mdomain s1 = stack_state_mdomain s /\
      stack_state_sh_mdomain s1 = stack_state_sh_mdomain s /\
      stack_state_compile s1 = stack_state_compile s`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_CONSTS_TAC);;

let STACKPROPSAUX_shift_seq_0 = prove
 (`!co:num->A. shift_seq 0 co = co`,
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES; ETA_AX]);;

let STACKPROPSAUX_code_bitmaps_trans = prove
 (`!(co:num->C#(num#(A)stack_prog)list#(A word)list) code bm n1 n2.
     shift_seq n2 (shift_seq n1 co) = shift_seq (n2 + n1) co /\
     FOLDL sptree_union (FOLDL sptree_union code (MAP (fromAList o FST o SND) (list_of_seq co n1)))
       (MAP (fromAList o FST o SND) (list_of_seq (shift_seq n1 co) n2)) =
     FOLDL sptree_union code (MAP (fromAList o FST o SND) (list_of_seq co (n2 + n1))) /\
     APPEND (APPEND bm (FLAT (MAP (SND o SND) (list_of_seq co n1))))
       (FLAT (MAP (SND o SND) (list_of_seq (shift_seq n1 co) n2))) =
     APPEND bm (FLAT (MAP (SND o SND) (list_of_seq co (n2 + n1))))`,
  REWRITE_TAC[GENLIST_APPEND; MAP_APPEND; FOLDL_APPEND; FLAT_APPEND; APPEND_ASSOC] THEN
  REWRITE_TAC[shift_seq_def; FUN_EQ_THM; ADD_ASSOC]);;

let STACKPROPSAUX_CB_TAC : tactic =
  STACKPROPSAUX_SPLIT_TAC THEN
  STACKPROPSAUX_USE_IHS_TAC (ASM_REWRITE_TAC[]) THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  STACKPROPSAUX_CONST_FACTS_TAC THEN
  ASM_REWRITE_TAC[] THEN SIMP[stack_unset_var_def; I_THM] THEN
  FIRST
   [EXISTS_TAC `0` THEN
    SIMP[STACKPROPSAUX_shift_seq_0; list_of_seq; MAP; FOLDL; FLAT; APPEND_NIL] THEN
    NO_TAC;
    EXISTS_TAC `1` THEN
    SIMP[LISTAUX_list_of_seq_1; MAP; FOLDL; FLAT; APPEND_NIL; o_THM] THEN
    NO_TAC;
    MESON_TAC[STACKPROPSAUX_code_bitmaps_trans]];;

let evaluate_code_bitmaps = prove
 (`!c (s:(A,C,FFI)stack_state) r s1.
     stack_evaluate (c,s) = (r,s1) ==>
     ?n. stack_state_compile_oracle s1 = shift_seq n (stack_state_compile_oracle s) /\
         stack_state_code s1 =
           FOLDL sptree_union (stack_state_code s)
             (MAP (fromAList o FST o SND) (list_of_seq (stack_state_compile_oracle s) n)) /\
         stack_state_bitmaps s1 =
           APPEND (stack_state_bitmaps s)
             (FLAT (MAP (SND o SND) (list_of_seq (stack_state_compile_oracle s) n)))`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_CB_TAC);;

let stack_evaluate_mono = prove
 (`!c (s:(A,C,FFI)stack_state) r s1.
     stack_evaluate (c,s) = (r,s1) ==>
     isPREFIX (stack_state_bitmaps s) (stack_state_bitmaps s1) /\
     subspt (stack_state_code s) (stack_state_code s1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP evaluate_code_bitmaps) THEN
  ASM_REWRITE_TAC[IS_PREFIX_APPEND3; subspt_FOLDL_union]);;

(* a call_FFI that returns only appends to the io_events (a fact of HOL4's *)
(* ffiProps)                                                                *)

let STACKPROPSAUX_sh_mem_op_io = prove
 (`sh_mem_op op r a (s:(A,C,FFI)stack_state) = (res,t) ==>
   isPREFIX (ffi_state_io_events (stack_state_ffi s))
            (ffi_state_io_events (stack_state_ffi t))`,
  CASES_ON `op:memop` THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_load_def;
              stack_sh_mem_store32_def; stack_sh_mem_load32_def;
              stack_sh_mem_load16_def; stack_sh_mem_store16_def;
              stack_sh_mem_store_byte_def; stack_sh_mem_load_byte_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[IS_PREFIX_REFL] THEN
  FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SEM2AUX_call_FFI_io_events));;

let STACKPROPSAUX_IO_FACTS_TAC : tactic =
  STACKPROPSAUX_FACTS_TAC [SEM2AUX_call_FFI_io_events; STACKPROPSAUX_sh_mem_op_io];;

let STACKPROPSAUX_IO_TAC : tactic =
  STACKPROPSAUX_SPLIT_TAC THEN
  STACKPROPSAUX_USE_IHS_TAC (ASM_REWRITE_TAC[]) THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  STACKPROPSAUX_IO_FACTS_TAC THEN STACKPROPSAUX_CONST_FACTS_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[stack_unset_var_def; I_THM; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL];;

let stack_evaluate_io_events_mono = prove
 (`!exps (s1:(A,C,FFI)stack_state) res s2.
     stack_evaluate (exps,s1) = (res,s2) ==>
     isPREFIX (ffi_state_io_events (stack_state_ffi s1))
              (ffi_state_io_events (stack_state_ffi s2))`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_IO_TAC);;

(* HOL4: pair_map_eq, the theorem of hol4/basic.ml (the same statement) *)

let pair_map_eq = pair_map_eq;;

let bad_fun_return_IMP = prove
 (`!res:((A)stack_result)option.
     stack_bad_fun_return res ==>
     res = NONE \/ ?n. res = SOME (stackSem_Break n) \/ res = SOME (stackSem_Continue n)`,
  GEN_TAC THEN CASES_ON `res:((A)stack_result)option` THEN
  REWRITE_TAC[stack_bad_fun_return_def] THEN
  CASES_ON `a:(A)stack_result` THEN
  REWRITE_TAC[stack_bad_fun_return_def; option_INJ; injectivity "stack_result";
              distinctness "stack_result"] THEN MESON_TAC[]);;

let cont_loop_IMP = prove
 (`!res:((A)stack_result)option.
     stack_cont_loop res ==> res = NONE \/ res = SOME (stackSem_Continue 0)`,
  GEN_TAC THEN CASES_ON `res:((A)stack_result)option` THEN
  REWRITE_TAC[stack_cont_loop_def] THEN
  CASES_ON `a:(A)stack_result` THEN
  REWRITE_TAC[stack_cont_loop_def; option_INJ; injectivity "stack_result";
              distinctness "stack_result"] THEN MESON_TAC[]);;

(* the clock of a run with extra clock: the normal form used below *)

let STACKPROPSAUX_dec_clock_clock = prove
 (`stack_state_clock (stack_dec_clock (s:(A,C,FFI)stack_state)) = stack_state_clock s - 1`,
  REWRITE_TAC[stack_dec_clock_def] THEN SIMP[]);;

let STACKPROPSAUX_dec_clock_add = prove
 (`~(n = 0) ==>
   stack_dec_clock (stack_state_clock_fupd (K (n + extra)) (s:(A,C,FFI)stack_state)) =
   stack_state_clock_fupd (K ((n - 1) + extra)) (stack_dec_clock s)`,
  REWRITE_TAC[stack_dec_clock_def] THEN SIMP[] THEN DISCH_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* the side conditions of the induction hypotheses: an assumption, a        *)
(* distinctness, or ~(x = SOME stack_TimeOut) from a fact about x           *)

let STACKPROPSAUX_SIDE_TAC : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "stack_result"] THEN NO_TAC;
         DISCH_THEN SUBST_ALL_TAC THEN
         RULE_ASSUM_TAC(REWRITE_RULE[stack_cont_loop_def; stack_bad_fun_return_def;
                                     stack_exit_loop_def;
                                     option_DISTINCT; option_INJ;
                                     distinctness "stack_result"]) THEN
         FIRST_ASSUM CONTR_TAC];;

let STACKPROPSAUX_exit_loop_timeout = prove
 (`!x:((A)stack_result)option.
     stack_exit_loop x = SOME stack_TimeOut <=> x = SOME stack_TimeOut`,
  GEN_TAC THEN CASES_ON `x:((A)stack_result)option` THEN
  REWRITE_TAC[stack_exit_loop_def; option_DISTINCT] THEN
  CASES_ON `a:(A)stack_result` THEN
  REWRITE_TAC[stack_exit_loop_def; option_DISTINCT; option_INJ;
              distinctness "stack_result"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ;
                                  distinctness "stack_result"]);;

(* tidy the assumptions after a case split: constructor equations, strip   *)
(* the conjunctions, existentials and disjunctions that this makes,         *)
(* eliminate variable equations, until nothing changes; F closes the goal   *)

let STACKPROPSAUX_TIDY_TAC : tactic =
  REPEAT (CHANGED_TAC
   (RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; PAIR_EQ; DE_MORGAN_THM;
                                STACKPROPSAUX_exit_loop_timeout;
                                distinctness "stack_result";
                                injectivity "stack_result"]) THEN
    REPEAT (FIRST_X_ASSUM (fun th ->
      let c = concl th in
      if is_conj c || is_exists c || is_disj c || c = `F`
      then CAKE_STRIP_ASSUME_TAC th else failwith "keep")) THEN
    RVEQ_TAC));;

let STACKPROPSAUX_ADD_CLOCK_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (STACKPAUX_is_eval_eq o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[stack_evaluate_def] THENC
           REWRITE_CONV(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_TIDY_TAC THEN
  STACKPROPSAUX_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  STACKPROPSAUX_CONST_FACTS_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[STACKPROPSAUX_dec_clock_clock]) THEN RVEQ_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SIMP(STACKPROPSAUX_local_simps @
       [STACKPROPSAUX_dec_clock_clock; STACKPROPSAUX_dec_clock_add; PAIR_MAP_THM; I_THM;
        OPTION_MAP_DEF; stack_empty_env_def; stack_unset_var_def; LET_DEF; LET_END_DEF]);;

let stack_evaluate_add_clock = prove
 (`!p (s:(A,C,FFI)stack_state) r s'.
     stack_evaluate (p,s) = (r,s') /\ ~(r = SOME stack_TimeOut) ==>
     stack_evaluate (p,stack_state_clock_fupd (K (stack_state_clock s + extra)) s) =
     (r,stack_state_clock_fupd (K (stack_state_clock s' + extra)) s')`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_ADD_CLOCK_TAC);;

let stack_with_clock_ffi = prove
 (`stack_state_ffi (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
   stack_state_ffi s`,
  SIMP[]);;

(* evaluate_add_clock_io_events_mono: the run that times out, by induction   *)
(* (STACKPROPSAUX_timeout_io); the other runs by evaluate_add_clock          *)

let STACKPROPSAUX_is_clock_state tm =
  try let f,_ = dest_comb tm in let c,_ = dest_comb f in
      fst(dest_const c) = "stack_state_clock_fupd"
  with Failure _ -> false;;

let STACKPROPSAUX_eval_state tm = snd(dest_pair(rand(lhs tm)));;

(* the facts stack_evaluate (c,t+) = (res,t1+) of evaluate_add_clock for     *)
(* the evaluate assumptions stack_evaluate (c,t) = (res,t1) whose result is  *)
(* not a time out                                                           *)

let STACKPROPSAUX_ADD_CLOCK_FACTS_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> STACKPAUX_is_eval_eq (concl th) &&
                     not (STACKPROPSAUX_is_clock_state
                            (STACKPROPSAUX_eval_state (concl th)))) (map snd asl) in
  MAP_EVERY (fun e (asl,w as g) ->
      try let res = fst(dest_pair(rhs(concl e))) in
          let nt = mk_neg(mk_eq(res,`SOME (stack_TimeOut:(A)stack_result)`)) in
          let nth = TAC_PROOF((asl,nt), STACKPROPSAUX_SIDE_TAC) in
          STRIP_ASSUME_TAC (MATCH_MP stack_evaluate_add_clock (CONJ e nth)) g
      with Failure _ -> ALL_TAC g) evs g;;

let STACKPROPSAUX_TIMEOUT_IO_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> STACKPAUX_is_eval_eq (concl th) &&
                   STACKPROPSAUX_is_clock_state (STACKPROPSAUX_eval_state (concl th)))) THEN
  FIRST_X_ASSUM (MP_TAC o check (STACKPAUX_is_eval_eq o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[stack_evaluate_def] THENC
           REWRITE_CONV(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_TIDY_TAC THEN
  STACKPROPSAUX_ADD_CLOCK_FACTS_TAC THEN
  STACKPROPSAUX_CONST_FACTS_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[STACKPROPSAUX_dec_clock_clock]) THEN RVEQ_TAC THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[stack_evaluate_def])) THEN
  SIMP(STACKPROPSAUX_local_simps @
       [STACKPROPSAUX_dec_clock_clock; STACKPROPSAUX_dec_clock_add; PAIR_MAP_THM; I_THM;
        OPTION_MAP_DEF; LET_DEF; LET_END_DEF]) THEN
  REWRITE_TAC(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_TIDY_TAC THEN
  STACKPROPSAUX_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  STACKPROPSAUX_FACTS_TAC [stack_evaluate_io_events_mono] THEN
  STACKPROPSAUX_IO_FACTS_TAC THEN STACKPROPSAUX_CONST_FACTS_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  SIMP[stack_unset_var_def; I_THM; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL];;

let STACKPROPSAUX_timeout_io = prove
 (`!e (s:(A,C,FFI)stack_state) t.
     stack_evaluate (e,s) = (SOME stack_TimeOut,t) ==>
     !q t'. stack_evaluate (e,stack_state_clock_fupd (K (stack_state_clock s + extra)) s) =
            (q,t') ==>
            isPREFIX (ffi_state_io_events (stack_state_ffi t))
                     (ffi_state_io_events (stack_state_ffi t'))`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_TIMEOUT_IO_TAC);;

let stack_evaluate_add_clock_io_events_mono = prove
 (`!e (s:(A,C,FFI)stack_state).
     isPREFIX
       (ffi_state_io_events (stack_state_ffi (SND (stack_evaluate (e,s)))))
       (ffi_state_io_events (stack_state_ffi (SND (stack_evaluate
          (e,stack_state_clock_fupd (K (stack_state_clock s + extra)) s)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `stack_evaluate (e:(A)stack_prog,s:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:((A)stack_result)option`; `r:(A,C,FFI)stack_state`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `stack_evaluate (e:(A)stack_prog,
                  stack_state_clock_fupd (K (stack_state_clock s + extra))
                    (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q':((A)stack_result)option`; `r':(A,C,FFI)stack_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[SND] THEN
  ASM_CASES_TAC `q = SOME (stack_TimeOut:(A)stack_result)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[STACKPROPSAUX_timeout_io];
    MP_TAC(ISPECL [`e:(A)stack_prog`; `s:(A,C,FFI)stack_state`;
                   `q:((A)stack_result)option`; `r:(A,C,FFI)stack_state`]
             stack_evaluate_add_clock) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SIMP[IS_PREFIX_REFL]]);;

let clock_neutral_def = sem1aux_def_wf
  `MEASURE (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(clock_neutral (stack_Seq p1 p2:(A)stack_prog) <=>
      clock_neutral p1 /\ clock_neutral p2) /\
   (clock_neutral (stack_LocValue _ _ _) <=> T) /\
   (clock_neutral (stack_Halt _) <=> T) /\
   (clock_neutral (stack_Inst _) <=> T) /\
   (clock_neutral stack_Skip <=> T) /\
   (clock_neutral (stack_If _ _ _ p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
   (clock_neutral r <=> F)`;;

let clock_neutral_ind = cake_ind "clock_neutral";;

(* HOL4 [local] *)

let inst_clock_neutral = prove
 (`(stack_inst i (s:(A,C,FFI)stack_state) = SOME t ==>
    stack_inst i (stack_state_clock_fupd (K k) s) = SOME (stack_state_clock_fupd (K k) t)) /\
   (stack_inst i s = NONE ==> stack_inst i (stack_state_clock_fupd (K k) s) = NONE)`,
  REWRITE_TAC[stack_inst_with_const] THEN CONJ_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF]);;

(* stack_word_exp reads only the registers, the store and the memory *)

let STACKPROPSAUX_word_exp_frame = prove
 (`!(s:(A,C,FFI)stack_state) e (t:(A,C,FFI)stack_state).
     stack_state_regs t = stack_state_regs s /\
     stack_state_store t = stack_state_store s /\
     stack_state_memory t = stack_state_memory s /\
     stack_state_mdomain t = stack_state_mdomain s
     ==> stack_word_exp t e = stack_word_exp s e`,
  MATCH_MP_TAC stack_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[stack_word_exp_def];
    STRIP_TAC THEN ASM_REWRITE_TAC[stack_word_exp_def];
    STRIP_TAC THEN ASM_REWRITE_TAC[stack_word_exp_def];
    DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:(A,C,FFI)stack_state`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[stack_mem_load_def];
    DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    SUBGOAL_THEN
     `MAP (stack_word_exp (t:(A,C,FFI)stack_state)) wexps =
      MAP (stack_word_exp (s:(A,C,FFI)stack_state)) wexps`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `a:(A)wl_exp` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)wl_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `t:(A,C,FFI)stack_state`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);;

let STACKPROPSAUX_word_exp_with_ffi = prove
 (`stack_word_exp (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) e =
   stack_word_exp s e`,
  MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN SIMP[]);;

let STACKPROPSAUX_ffi_rws = prove
 (`(!r. stack_get_var r (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
        stack_get_var r s) /\
   (!xs. stack_get_vars xs (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
         stack_get_vars xs s) /\
   (!r. stack_get_fp_var r (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
        stack_get_fp_var r s) /\
   (!a. stack_mem_load a (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
        stack_mem_load a s) /\
   (!a w. stack_mem_store a w (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
          OPTION_MAP (\s. stack_state_ffi_fupd (K k) s) (stack_mem_store a w s)) /\
   (!x y. stack_set_fp_var x y (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
          stack_state_ffi_fupd (K k) (stack_set_fp_var x y s)) /\
   (!x y. stack_assign x y (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
          OPTION_MAP (\s. stack_state_ffi_fupd (K k) s) (stack_assign x y s))`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[stack_get_var_def] THEN SIMP[];
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[stack_get_vars_def; stack_get_var_def] THEN
    SIMP[];
    REWRITE_TAC[stack_get_fp_var_def] THEN SIMP[];
    REWRITE_TAC[stack_mem_load_def] THEN SIMP[];
    REWRITE_TAC[stack_mem_store_def] THEN SIMP[] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN SIMP[OPTION_MAP_DEF];
    REWRITE_TAC[stack_set_fp_var_def] THEN SIMP[];
    REWRITE_TAC[stack_assign_def; STACKPROPSAUX_word_exp_with_ffi] THEN
    REPEAT GEN_TAC THEN
    CASES_ON `stack_word_exp (s:(A,C,FFI)stack_state) y` THEN
    SIMP[OPTION_MAP_DEF]]);;

let STACKPROPSAUX_inst_with_ffi = prove
 (`stack_inst i (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
   OPTION_MAP (\s. stack_state_ffi_fupd (K k) s) (stack_inst i s)`,
  REWRITE_TAC[stack_inst_def] THEN
  SIMP[STACKPROPSAUX_ffi_rws; STACKPROPSAUX_word_exp_with_ffi] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF; LET_DEF; LET_END_DEF]) THEN
  FS[OPTION_MAP_DEF]);;

(* HOL4 [local] *)

let inst_clock_neutral_ffi = prove
 (`(stack_inst i (s:(A,C,FFI)stack_state) = SOME t ==>
    stack_inst i (stack_state_ffi_fupd (K k) s) = SOME (stack_state_ffi_fupd (K k) t)) /\
   (stack_inst i s = NONE ==> stack_inst i (stack_state_ffi_fupd (K k) s) = NONE)`,
  REWRITE_TAC[STACKPROPSAUX_inst_with_ffi] THEN CONJ_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF]);;

let STACKPROPSAUX_NEUTRAL_TAC (rws:thm list) : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (STACKPAUX_is_eval_eq o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[stack_evaluate_def] THENC
           REWRITE_CONV(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clock_neutral_def]) THEN
  STACKPROPSAUX_TIDY_TAC THEN
  STACKPROPSAUX_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SIMP(rws @ [PAIR_MAP_THM; I_THM; OPTION_MAP_DEF; LET_DEF; LET_END_DEF]);;

let evaluate_clock_neutral = prove
 (`!prog (s:(A,C,FFI)stack_state) res t.
     stack_evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
     stack_evaluate (prog,stack_state_clock_fupd (K c) s) =
     (res,stack_state_clock_fupd (K c) t)`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_NEUTRAL_TAC []);;

let STACKPROPSAUX_neutral_ffi_rws = prove
 (`(!x. stack_get_var_imm x (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
        stack_get_var_imm x s) /\
   stack_empty_env (stack_state_ffi_fupd (K k) (s:(A,C,FFI)stack_state)) =
   stack_state_ffi_fupd (K k) (stack_empty_env s)`,
  CONJ_TAC THENL
   [GEN_TAC THEN CASES_ON `x:(A)reg_imm` THEN
    REWRITE_TAC[stack_get_var_imm_def; STACKPROPSAUX_ffi_rws];
    REWRITE_TAC[stack_empty_env_def] THEN SIMP[]]);;

let evaluate_ffi_neutral = prove
 (`!prog (s:(A,C,FFI)stack_state) res t.
     stack_evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
     stack_evaluate (prog,stack_state_ffi_fupd (K c) s) =
     (res,stack_state_ffi_fupd (K c) t)`,
  STACKPROPSAUX_EVAL_IND_TAC THEN
  STACKPROPSAUX_NEUTRAL_TAC [STACKPROPSAUX_ffi_rws; STACKPROPSAUX_inst_with_ffi;
                             STACKPROPSAUX_neutral_ffi_rws]);;

let semantics_Terminate_IMP_PREFIX = prove
 (`stack_semantics start (s1:(A,C,FFI)stack_state) = Terminate x l ==>
   isPREFIX (ffi_state_io_events (stack_state_ffi s1)) l`,
  REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_CASE; distinctness "behaviour"] THEN
  FIRST_X_ASSUM(fun th -> DISCH_THEN(fun eq -> MP_TAC(REWRITE_RULE[eq] (SELECT_RULE th)))) THEN
  REWRITE_TAC[injectivity "behaviour"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP stack_evaluate_io_events_mono) THEN SIMP[]);;

let semantics_Diverge_IMP_LPREFIX = prove
 (`stack_semantics start (s1:(A,C,FFI)stack_state) = Diverge l ==>
   LPREFIX (llist_fromList (ffi_state_io_events (stack_state_ffi s1))) l`,
  REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_CASE] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE o check (is_exists o concl)) THEN
    ASM_REWRITE_TAC[distinctness "behaviour"];
    ALL_TAC] THEN
  REWRITE_TAC[injectivity "behaviour"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  ABBREV_TAC `f = \k. ffi_state_io_events (stack_state_ffi (SND (stack_evaluate
                   (stack_Call NONE (INL start) NONE:(A)stack_prog,
                    stack_state_clock_fupd (K k) (s1:(A,C,FFI)stack_state)))))` THEN
  SUBGOAL_THEN
   `IMAGE (\k. llist_fromList (ffi_state_io_events (stack_state_ffi (SND (stack_evaluate
       (stack_Call NONE (INL start) NONE:(A)stack_prog,
        stack_state_clock_fupd (K k) (s1:(A,C,FFI)stack_state))))))) (:num) =
    IMAGE llist_fromList (IMAGE f (:num))`
   SUBST1_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `llist_fromList (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state))) IN
      IMAGE llist_fromList (IMAGE (f:num->io_event list) (:num)) /\
    lprefix_chain (IMAGE llist_fromList (IMAGE (f:num->io_event list) (:num)))`
   MP_TAC THENL
   [ALL_TAC;
    MESON_TAC[build_lprefix_lub_thm; lprefix_lub_def]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    EXISTS_TAC `ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `0` THEN EXPAND_TAC "f" THEN
    ONCE_REWRITE_TAC[stack_evaluate_def] THEN SIMP[] THEN
    TOP_CASE_TAC THEN SIMP[];
    ALL_TAC] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
              IN_UNIV] THEN
  SUBGOAL_THEN `!k1 k2. k1 <= k2 ==> isPREFIX ((f:num->io_event list) k1) (f k2)`
    (fun th -> MESON_TAC[th; LE_CASES]) THEN
  EXPAND_TAC "f" THEN REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                 `stack_state_clock_fupd (K k1) (s1:(A,C,FFI)stack_state)`]
          (INST [`d:num`,`extra:num`] stack_evaluate_add_clock_io_events_mono)) THEN
  SIMP[]);;

let map_bitmap_length = prove
 (`!a (b:A list) c x y z.
     map_bitmap a b c = SOME (x,y,z) ==>
     LENGTH c = LENGTH x + LENGTH z /\ LENGTH x = LENGTH a`,
  MATCH_MP_TAC map_bitmap_ind THEN REWRITE_TAC[map_bitmap_def] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; LENGTH] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let dec_stack_length = prove
 (`!bs (enc:((A)word_loc)list) orig_stack new_stack.
     stack_dec_stack bs enc orig_stack = SOME new_stack ==>
     LENGTH orig_stack = LENGTH new_stack`,
  MATCH_MP_TAC stack_dec_stack_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[stack_dec_stack_def; option_DISTINCT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_dec_stack_def] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP map_bitmap_length) THEN
  RES_TAC THEN ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

(* HOL4: extract_labels_def; HOL4 ++ is left associative *)

let stack_extract_labels_def = sem1aux_def_wf
  `MEASURE (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(stack_extract_labels (stack_Call ret dest h:(A)stack_prog) =
      match ret with
        NONE -> []
      | SOME (ret_handler,_,l1,l2) ->
          let ret_rest = stack_extract_labels ret_handler in
          (match h with
             NONE -> APPEND [(l1,l2)] ret_rest
           | SOME (prog,l1',l2') ->
               let h_rest = stack_extract_labels prog in
               APPEND (APPEND [(l1,l2); (l1',l2')] ret_rest) h_rest)) /\
   (stack_extract_labels (stack_Loop s1) = stack_extract_labels s1) /\
   (stack_extract_labels (stack_Seq s1 s2) =
      APPEND (stack_extract_labels s1) (stack_extract_labels s2)) /\
   (stack_extract_labels (stack_If cmp r1 ri e2 e3) =
      APPEND (stack_extract_labels e2) (stack_extract_labels e3)) /\
   (stack_extract_labels _ = [])`;;

let stack_extract_labels_ind = cake_ind "stack_extract_labels";;

let find_code_IMP_get_labels = prove
 (`stack_find_code d (r:(num,(B)word_loc)fmap) (code:((A)stack_prog)spt) = SOME e ==>
   stack_get_labels e SUBSET loc_check code`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN
  CASES_ON `d:num+num` THEN REWRITE_TAC[stack_find_code_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[loc_check_def] THEN DISJ2_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 addr_offset_ok c, hw_offset_ok c, byte_offset_ok c are written out   *)
(* (asm.ml: asm_offset_ok 0 (asm_config_addr_offset c), ...)                *)

let addr_ok_def = cake_def
  `addr_ok op (Addr a (w:A word)) (c:(A)asm_config) <=>
     reg_ok a c /\
     (if op IN {asm_Load, asm_Store, asm_Load32, asm_Store32}
      then asm_offset_ok 0 (asm_config_addr_offset c) w
      else if op IN {Load16, Store16}
      then asm_offset_ok 0 (asm_config_hw_offset c) w /\ ~(asm_config_ISA c = Ag32)
      else asm_offset_ok 0 (asm_config_byte_offset c) w)`;;

(* TODO: This is not updated for Install, CBW and DBW *)
(* asm_ok out of stack_names *)

let stack_asm_ok_def = sem1aux_def_wf
  `MEASURE (\x:(A)asm_config#(A)stack_prog. stack_prog_size (\x:A. 0) (SND x))`
  SEM1AUX_TC_TAC
  `(stack_asm_ok (c:(A)asm_config) (stack_Inst i:(A)stack_prog) <=> inst_ok i c) /\
   (stack_asm_ok c (ShMemOp op r ad) <=> reg_ok r c /\ addr_ok op ad c) /\
   (stack_asm_ok c (stack_CodeBufferWrite r1 r2) <=>
      r1 < asm_config_reg_count c /\ r2 < asm_config_reg_count c /\
      ~MEM r1 (asm_config_avoid_regs c) /\ ~MEM r2 (asm_config_avoid_regs c)) /\
   (stack_asm_ok c (stack_Seq p1 p2) <=> stack_asm_ok c p1 /\ stack_asm_ok c p2) /\
   (stack_asm_ok c (stack_If cmp n ri p p') <=> stack_asm_ok c p /\ stack_asm_ok c p') /\
   (stack_asm_ok c (stack_Loop p) <=> stack_asm_ok c p) /\
   (stack_asm_ok c (stack_Raise n) <=>
      n < asm_config_reg_count c /\ ~MEM n (asm_config_avoid_regs c)) /\
   (stack_asm_ok c (stack_Return n) <=>
      n < asm_config_reg_count c /\ ~MEM n (asm_config_avoid_regs c)) /\
   (stack_asm_ok c (stack_Call ret tar h) <=>
      (match tar with
         INR r -> r < asm_config_reg_count c /\ ~MEM r (asm_config_avoid_regs c)
       | _ -> T) /\
      (match ret with
         SOME (p,_,_,_) ->
           stack_asm_ok c p /\
           (match h with
              SOME (p',_,_) -> stack_asm_ok c p'
            | _ -> T)
       | _ -> T)) /\
   (stack_asm_ok c _ <=> T)`;;

let stack_asm_ok_ind = cake_ind "stack_asm_ok";;

let reg_name_def = cake_def
  `reg_name r (c:(A)asm_config) <=>
     r < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)`;;

(* inst requirements just before stack_names *)

let reg_imm_name_def = cake_def
  `(reg_imm_name b (Reg r) (c:(A)asm_config) <=> reg_name r c) /\
   (reg_imm_name b (Imm (w:A word)) c <=> asm_config_valid_imm c b w)`;;

let arith_name_def = cake_def
  `(arith_name (Binop b r1 r2 ri) (c:(A)asm_config) <=>
      (asm_config_two_reg_arith c ==> r1 = r2 \/ b = asm_Or /\ ri = Reg r2) /\
      reg_name r1 c /\ reg_name r2 c /\ reg_imm_name (INL b) ri c) /\
   (arith_name (asm_Shift l r1 r2 (Imm (i:A word))) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name r2 c /\
      (i = word 0 ==> l = Lsl) /\ val i < dimindex (:A)) /\
   (arith_name (asm_Shift l r1 r2 (Reg r3)) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
      reg_name r2 c /\ reg_name r3 c /\ (asm_config_ISA c = x86_64 ==> r3 = 4)) /\
   (arith_name (asm_Div r1 r2 r3) c <=>
      reg_name r1 c /\ reg_name r2 c /\ reg_name r3 c /\
      asm_config_ISA c IN {ARMv8, MIPS, RISC_V}) /\
   (arith_name (LongMul r1 r2 r3 r4) c <=>
      reg_name r1 c /\ reg_name r2 c /\ reg_name r3 c /\ reg_name r4 c /\
      (asm_config_ISA c = x86_64 ==> r1 = 3 /\ r2 = 0 /\ r3 = 0) /\
      (asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
      (asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/ asm_config_ISA c = Ag32
       ==> ~(r1 = r3) /\ ~(r1 = r4))) /\
   (arith_name (LongDiv r1 r2 r3 r4 r5) c <=>
      asm_config_ISA c = x86_64 /\ r1 = 0 /\ r2 = 3 /\ r3 = 3 /\ r4 = 0 /\
      reg_name r5 c) /\
   (arith_name (asm_AddCarry r1 r2 r3 r4) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name r2 c /\
      reg_name r3 c /\ reg_name r4 c /\
      (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V
       ==> ~(r1 = r3) /\ ~(r1 = r4))) /\
   (arith_name (AddOverflow r1 r2 r3 r4) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name r2 c /\
      reg_name r3 c /\ reg_name r4 c /\
      (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 = r3))) /\
   (arith_name (SubOverflow r1 r2 r3 r4) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name r2 c /\
      reg_name r3 c /\ reg_name r4 c /\
      (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 = r3)))`;;

(* We could actually almost use fp_ok, except this needs to check reg_ok for *)
(* some registers as well                                                    *)

let fp_name_def = cake_def
  `(fp_name (FPLess r d1 d2) (c:(A)asm_config) <=>
      reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPLessEqual r d1 d2) c <=>
      reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPEqual r d1 d2) c <=>
      reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPAbs d1 d2) c <=>
      (asm_config_two_reg_arith c ==> ~(d1 = d2)) /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPNeg d1 d2) c <=>
      (asm_config_two_reg_arith c ==> ~(d1 = d2)) /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPSqrt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPAdd d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPSub d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPMul d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPDiv d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPFma d1 d2 d3) c <=>
      asm_config_ISA c = ARMv7 /\
      2 < asm_config_fp_reg_count c /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPMov d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPMovToReg r1 r2 d) c <=>
      reg_name r1 c /\ (dimindex(:A) = 32 ==> ~(r1 = r2) /\ reg_name r2 c) /\
      fp_reg_ok d c) /\
   (fp_name (FPMovFromReg d r1 r2) c <=>
      reg_name r1 c /\ (dimindex(:A) = 32 ==> ~(r1 = r2) /\ reg_name r2 c) /\
      fp_reg_ok d c) /\
   (fp_name (FPToInt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPFromInt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c)`;;

let addr_name_def = cake_def
  `addr_name m (Addr r (w:A word)) (c:(A)asm_config) <=>
     reg_name r c /\
     (if m IN {asm_Load, asm_Store, asm_Load32, asm_Store32}
      then asm_offset_ok 0 (asm_config_addr_offset c) w
      else if m IN {Load16, Store16}
      then asm_offset_ok 0 (asm_config_hw_offset c) w /\ ~(asm_config_ISA c = Ag32)
      else asm_offset_ok 0 (asm_config_byte_offset c) w)`;;

let inst_name_def = cake_def
  `(inst_name (c:(A)asm_config) (asm_Const r (w:A word)) <=> reg_name r c) /\
   (inst_name c (Mem m r a) <=> reg_name r c /\ addr_name m a c) /\
   (inst_name c (asm_Arith x) <=> arith_name x c) /\
   (inst_name c (FP f) <=> fp_name f c) /\
   (inst_name _ _ <=> T)`;;

let stack_asm_name_def = sem1aux_def_wf
  `MEASURE (\x:(A)asm_config#(A)stack_prog. stack_prog_size (\x:A. 0) (SND x))`
  SEM1AUX_TC_TAC
  `(stack_asm_name (c:(A)asm_config) (stack_Inst i:(A)stack_prog) <=> inst_name c i) /\
   (stack_asm_name c (stack_OpCurrHeap b r1 r2) <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name r2 c) /\
   (stack_asm_name c (ShMemOp op r a) <=> reg_name r c /\ addr_name op a c) /\
   (stack_asm_name c (stack_CodeBufferWrite r1 r2) <=> reg_name r1 c /\ reg_name r2 c) /\
   (stack_asm_name c (stack_DataBufferWrite r1 r2) <=> reg_name r1 c /\ reg_name r2 c) /\
   (stack_asm_name c (stack_Seq p1 p2) <=> stack_asm_name c p1 /\ stack_asm_name c p2) /\
   (stack_asm_name c (stack_If cmp n ri p p') <=>
      stack_asm_name c p /\ stack_asm_name c p') /\
   (stack_asm_name c (stack_Loop p) <=> stack_asm_name c p) /\
   (stack_asm_name c (stack_Raise n) <=> reg_name n c) /\
   (stack_asm_name c (stack_Return n) <=> reg_name n c) /\
   (stack_asm_name c (stack_Call ret tar h) <=>
      (match tar with INR r -> reg_name r c | _ -> T) /\
      (match ret with
         SOME (p,_,_,_) ->
           stack_asm_name c p /\
           (match h with
              SOME (p',_,_) -> stack_asm_name c p'
            | _ -> T)
       | _ -> T)) /\
   (stack_asm_name c _ <=> T)`;;

let stack_asm_name_ind = cake_ind "stack_asm_name";;

(* HOL4 Overload find_name = tlookup *)

let fixed_names_def = cake_def
  `fixed_names names (c:(A)asm_config) <=>
     if asm_config_ISA c = x86_64 then
       tlookup names 3 = 2 /\
       tlookup names 4 = 1 /\
       tlookup names 0 = 0
     else T`;;

let stack_asm_remove_def = sem1aux_def_wf
  `MEASURE (\x:(A)asm_config#(A)stack_prog. stack_prog_size (\x:A. 0) (SND x))`
  SEM1AUX_TC_TAC
  `(stack_asm_remove (c:(A)asm_config) (stack_Get n s:(A)stack_prog) <=> reg_name n c) /\
   (stack_asm_remove c (stack_OpCurrHeap binop v src) <=>
      reg_name v c /\ reg_name src c) /\
   (stack_asm_remove c (stack_Set s n) <=> reg_name n c) /\
   (stack_asm_remove c (StackStore n n0) <=> reg_name n c) /\
   (stack_asm_remove c (StackStoreAny n n0) <=> reg_name n c /\ reg_name n0 c) /\
   (stack_asm_remove c (StackLoad n n0) <=> reg_name n c) /\
   (stack_asm_remove c (StackLoadAny n n0) <=> reg_name n c /\ reg_name n0 c) /\
   (stack_asm_remove c (StackGetSize n) <=> reg_name n c) /\
   (stack_asm_remove c (StackSetSize n) <=> reg_name n c) /\
   (stack_asm_remove c (BitmapLoad n n0) <=> reg_name n c /\ reg_name n0 c) /\
   (stack_asm_remove c (stack_StoreConsts n n0 _) <=> reg_name n c /\ reg_name n0 c) /\
   (stack_asm_remove c (stack_Seq p1 p2) <=>
      stack_asm_remove c p1 /\ stack_asm_remove c p2) /\
   (stack_asm_remove c (stack_If cmp n ri p p') <=>
      stack_asm_remove c p /\ stack_asm_remove c p') /\
   (stack_asm_remove c (stack_Loop p) <=> stack_asm_remove c p) /\
   (stack_asm_remove c (stack_Call ret tar h) <=>
      (match ret with
         SOME (p,_,_,_) ->
           stack_asm_remove c p /\
           (match h with
              SOME (p',_,_) -> stack_asm_remove c p'
            | _ -> T)
       | _ -> T)) /\
   (stack_asm_remove c _ <=> T)`;;

let stack_asm_remove_ind = cake_ind "stack_asm_remove";;

(* Various syntactic properties required for correctness of the stackLang   *)
(* passes. All of these are trivially preserved from word_to_stack until    *)
(* the pass that they are used.                                              *)

(* stack_alloc requires that Allocs have a fixed argument                   *)
(* TODO: this can also be a semantic check...                               *)

let alloc_arg_def = sem1aux_def_wf
  `MEASURE (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(alloc_arg (stack_Alloc v:(A)stack_prog) <=> v = 1) /\
   (alloc_arg (stack_Seq p1 p2) <=> alloc_arg p1 /\ alloc_arg p2) /\
   (alloc_arg (stack_If c r ri p1 p2) <=> alloc_arg p1 /\ alloc_arg p2) /\
   (alloc_arg (stack_Loop p1) <=> alloc_arg p1) /\
   (alloc_arg (stack_Call x1 _ x2) <=>
      (match x1 with SOME (y,r,_,_) -> alloc_arg y | NONE -> T) /\
      (match x2 with SOME (y,_,_) -> alloc_arg y | NONE -> T)) /\
   (alloc_arg _ <=> T)`;;

let alloc_arg_ind = cake_ind "alloc_arg";;

(* stack_remove requires that all register arguments are bounded by k *)

(* HOL4: Termination WF_REL_TAC measure ((exp_size ARB) o FST) *)

let reg_bound_exp_def = sem1aux_def_wf
  `MEASURE (\x:(A)wl_exp#num. wl_exp_size (\x:A. 0) (FST x))`
  SEM1AUX_TC_TAC
  `(reg_bound_exp (wl_Var n:(A)wl_exp) k <=> n < k) /\
   (reg_bound_exp (wl_Load e) k <=> reg_bound_exp e k) /\
   (reg_bound_exp (wl_Shift _ e1 e2) k <=> reg_bound_exp e1 k /\ reg_bound_exp e2 k) /\
   (reg_bound_exp (Lookup _) _ <=> F) /\
   (reg_bound_exp (wl_Op _ es) k <=> ALL (\e. reg_bound_exp e k) es) /\
   (reg_bound_exp _ _ <=> T)`;;

let reg_bound_exp_ind = cake_ind "reg_bound_exp";;
let _ = cake_add_simps [reg_bound_exp_def];;

let reg_bound_inst_def = sem1aux_def
  `(reg_bound_inst (Mem _ n (Addr a _):(A)inst) k <=> n < k /\ a < k) /\
   (reg_bound_inst (asm_Const n _) k <=> n < k) /\
   (reg_bound_inst (asm_Arith (asm_Shift _ n r2 ri)) k <=>
      r2 < k /\ n < k /\ (match ri with Reg r -> r < k | _ -> T)) /\
   (reg_bound_inst (asm_Arith (Binop _ n r2 ri)) k <=>
      r2 < k /\ n < k /\ (match ri with Reg r1 -> r1 < k | _ -> T)) /\
   (reg_bound_inst (asm_Arith (asm_Div r1 r2 r3)) k <=> r1 < k /\ r2 < k /\ r3 < k) /\
   (reg_bound_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) k <=>
      r1 < k /\ r2 < k /\ r3 < k /\ r4 < k) /\
   (reg_bound_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) k <=>
      r1 < k /\ r2 < k /\ r3 < k /\ r4 < k) /\
   (reg_bound_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) k <=>
      r1 < k /\ r2 < k /\ r3 < k /\ r4 < k) /\
   (reg_bound_inst (asm_Arith (LongMul r1 r2 r3 r4)) k <=>
      r1 < k /\ r2 < k /\ r3 < k /\ r4 < k) /\
   (reg_bound_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) k <=>
      r1 < k /\ r2 < k /\ r3 < k /\ r4 < k /\ r5 < k) /\
   (reg_bound_inst (FP (FPLess r f1 f2)) k <=> r < k) /\
   (reg_bound_inst (FP (FPLessEqual r f1 f2)) k <=> r < k) /\
   (reg_bound_inst (FP (FPEqual r f1 f2)) k <=> r < k) /\
   (reg_bound_inst (FP (FPMovToReg r1 r2 d)) k <=> r1 < k /\ r2 < k) /\
   (reg_bound_inst (FP (FPMovFromReg d r1 r2)) k <=> r1 < k /\ r2 < k) /\
   (reg_bound_inst _ _ <=> T)`;;
let _ = cake_add_simps [reg_bound_inst_def];;

(* HOL4 reg_bound_def has two inaccessible clauses (a second Halt and a      *)
(* second StackStore clause), which HOL4's TFL ignores: they are left out    *)

let reg_bound_def = sem1aux_def_wf
  `MEASURE (\x:(A)stack_prog#num. stack_prog_size (\x:A. 0) (FST x))`
  SEM1AUX_TC_TAC
  `(reg_bound (stack_Halt v1:(A)stack_prog) k <=> v1 < k) /\
   (reg_bound (stack_Raise v1) k <=> v1 < k) /\
   (reg_bound (stack_Get v1 n) k <=> v1 < k) /\
   (reg_bound (stack_OpCurrHeap op v1 v2) k <=> v1 < k /\ v2 < k) /\
   (reg_bound (stack_Set n v1) k <=> v1 < k /\ ~(n = BitmapBase)) /\
   (reg_bound (stack_LocValue v1 l1 l2) k <=> v1 < k) /\
   (reg_bound (stack_StoreConsts t1 t2 _) k <=> 3 < k /\ t1 < k /\ t2 < k) /\
   (reg_bound (stack_Return v1) k <=> v1 < k) /\
   (reg_bound (JumpLower v1 v2 d) k <=> v1 < k /\ v2 < k) /\
   (reg_bound (stack_Seq p1 p2) k <=> reg_bound p1 k /\ reg_bound p2 k) /\
   (reg_bound (stack_If c r ri p1 p2) k <=>
      r < k /\ (match ri with Reg n -> n < k | _ -> T) /\
      reg_bound p1 k /\ reg_bound p2 k) /\
   (reg_bound (stack_Loop p1) k <=> reg_bound p1 k) /\
   (reg_bound (stack_FFI ffi_index ptr' len' ptr2' len2' ret') k <=>
      ptr' < k /\ len' < k /\ ptr2' < k /\ len2' < k /\ ret' < k) /\
   (reg_bound (stack_Call x1 dest x2) k <=>
      (match dest with INR i -> i < k | _ -> T) /\
      (match x1 with
         NONE -> T
       | SOME (y,r,_,_) ->
           reg_bound y k /\ r < k /\
           (match x2 with SOME (y,_,_) -> reg_bound y k | NONE -> T))) /\
   (reg_bound (stack_Install ptr len dptr dlen ret) k <=>
      ptr < k /\ len < k /\ dptr < k /\ dlen < k /\ ret < k) /\
   (reg_bound (ShMemOp mop r (Addr a _)) k <=> r < k /\ a < k) /\
   (reg_bound (stack_CodeBufferWrite r1 r2) k <=> r1 < k /\ r2 < k) /\
   (reg_bound (stack_DataBufferWrite r1 r2) k <=> r1 < k /\ r2 < k) /\
   (reg_bound (BitmapLoad r v) k <=> r < k /\ v < k) /\
   (reg_bound (stack_Inst i) k <=> reg_bound_inst i k) /\
   (reg_bound (StackStore r _) k <=> r < k) /\
   (reg_bound (StackSetSize r) k <=> r < k) /\
   (reg_bound (StackGetSize r) k <=> r < k) /\
   (reg_bound (StackLoad r m) k <=> r < k) /\
   (reg_bound (StackLoadAny r r2) k <=> r < k /\ r2 < k) /\
   (reg_bound (StackStoreAny r r2) k <=> r < k /\ r2 < k) /\
   (reg_bound _ k <=> T)`;;

let reg_bound_ind = cake_ind "reg_bound";;

(* Finally, stack_to_lab requires correct arguments for Call/FFI/Install calls *)

let call_args_def = sem1aux_def_wf
  `MEASURE (\x:(A)stack_prog#num#num#num#num#num. stack_prog_size (\x:A. 0) (FST x))`
  SEM1AUX_TC_TAC
  `(call_args (stack_Seq p1 p2:(A)stack_prog) ptr len ptr2 len2 ret <=>
      call_args p1 ptr len ptr2 len2 ret /\
      call_args p2 ptr len ptr2 len2 ret) /\
   (call_args (stack_If c r ri p1 p2) ptr len ptr2 len2 ret <=>
      call_args p1 ptr len ptr2 len2 ret /\
      call_args p2 ptr len ptr2 len2 ret) /\
   (call_args (stack_Loop p1) ptr len ptr2 len2 ret <=>
      call_args p1 ptr len ptr2 len2 ret) /\
   (call_args (stack_Halt n) ptr len ptr2 len2 ret <=> n = ptr) /\
   (call_args (stack_FFI ffi_index ptr' len' ptr2' len2' ret') ptr len ptr2 len2 ret <=>
      ptr' = ptr /\ len' = len /\ ptr2' = ptr2 /\ len2' = len2 /\ ret' = ret) /\
   (call_args (stack_Call x1 _ x2) ptr len ptr2 len2 ret <=>
      (match x1 with
         NONE -> T
       | SOME (y,r,_,_) ->
           call_args y ptr len ptr2 len2 ret /\ r = ret /\
           (match x2 with
              SOME (y,_,_) -> call_args y ptr len ptr2 len2 ret
            | NONE -> T))) /\
   (call_args (stack_Install ptr' len' _ _ ret') ptr len ptr2 len2 ret <=>
      ptr' = ptr /\ len' = len /\ ret' = ret) /\
   (call_args _ ptr len ptr2 len2 ret <=> T)`;;

let call_args_ind = cake_ind "call_args";;

(* TODO: remove "stack_" prefix from these functions *)

let stack_get_handler_labels_def = sem1aux_def_wf
  `MEASURE (\x:num#(A)stack_prog. stack_prog_size (\x:A. 0) (SND x))`
  SEM1AUX_TC_TAC
  `(stack_get_handler_labels n (stack_Call r d h:(A)stack_prog) =
      match r with
        SOME (x,_,_) ->
          stack_get_handler_labels n x UNION
          (match h with
             SOME (x,l1,l2) ->
               (if l1 = n then {(l1,l2)} else {}) UNION stack_get_handler_labels n x
           | _ -> {})
      | _ -> {}) /\
   (stack_get_handler_labels n (stack_Seq p1 p2) =
      stack_get_handler_labels n p1 UNION stack_get_handler_labels n p2) /\
   (stack_get_handler_labels n (stack_If _ _ _ p1 p2) =
      stack_get_handler_labels n p1 UNION stack_get_handler_labels n p2) /\
   (stack_get_handler_labels n (stack_Loop p) = stack_get_handler_labels n p) /\
   (stack_get_handler_labels n _ = {})`;;

let stack_get_handler_labels_ind = cake_ind "stack_get_handler_labels";;
let _ = cake_add_simps [stack_get_handler_labels_def];;

(* HOL4: get_code_labels_def; HOL4 UNION is left associative *)

let stack_get_code_labels_def = sem1aux_def_wf
  `MEASURE (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(stack_get_code_labels (stack_Call r d h:(A)stack_prog) =
      ((match d with INL x -> {(x,0)} | _ -> {}) UNION
       (match r with SOME (x,_,_) -> stack_get_code_labels x | _ -> {})) UNION
      (match h with SOME (x,_,_) -> stack_get_code_labels x | _ -> {})) /\
   (stack_get_code_labels (stack_Seq p1 p2) =
      stack_get_code_labels p1 UNION stack_get_code_labels p2) /\
   (stack_get_code_labels (stack_If _ _ _ p1 p2) =
      stack_get_code_labels p1 UNION stack_get_code_labels p2) /\
   (stack_get_code_labels (stack_Loop p) = stack_get_code_labels p) /\
   (stack_get_code_labels (JumpLower _ _ t) = {(t,0)}) /\
   (stack_get_code_labels (RawCall t) = {(t,1)}) /\
   (stack_get_code_labels (stack_LocValue _ l1 l2) = {(l1,l2)}) /\
   (stack_get_code_labels (stack_StoreConsts _ _ (SOME l)) = {(l,0)}) /\
   (stack_get_code_labels _ = {})`;;

let stack_get_code_labels_ind = cake_ind "stack_get_code_labels";;
let _ = cake_add_simps [stack_get_code_labels_def];;

(* elabs gives a set of existing code labels *)

let stack_good_code_labels_def = cake_def
  `stack_good_code_labels (p:(num#(A)stack_prog)list) elabs <=>
     UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND p))) SUBSET
     ((((UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) p)) UNION
         IMAGE (\n. n,0) (set_of_list (MAP FST p))) UNION
        IMAGE (\n. n,0) elabs) UNION
       IMAGE (\n. n,1) (set_of_list (MAP FST p))) UNION
      IMAGE (\n. n,1) elabs)`;;

let stack_good_handler_labels_def = cake_def
  `stack_good_handler_labels (p:(num#(A)stack_prog)list) <=>
     restrict_nonzero (UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND p))))
     SUBSET
     (UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) p)) UNION
      IMAGE (\n. n,1) (set_of_list (MAP FST p)))`;;

let stack_no_install_def = sem1aux_def_wf
  `MEASURE (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(stack_no_install (stack_Call r d h:(A)stack_prog) <=>
      (match r with SOME (x,_,_) -> stack_no_install x | _ -> T) /\
      (match h with SOME (x,_,_) -> stack_no_install x | _ -> T)) /\
   (stack_no_install (stack_Seq p1 p2) <=> stack_no_install p1 /\ stack_no_install p2) /\
   (stack_no_install (stack_If _ _ _ p1 p2) <=>
      stack_no_install p1 /\ stack_no_install p2) /\
   (stack_no_install (stack_Loop p) <=> stack_no_install p) /\
   (stack_no_install (stack_Install _ _ _ _ _) <=> F) /\
   (stack_no_install _ <=> T)`;;

let stack_no_install_ind = cake_ind "stack_no_install";;

let no_shmemop_def = sem1aux_def_wf
  `MEASURE (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(no_shmemop (stack_Call r d h:(A)stack_prog) <=>
      (match r with SOME (x,_,_) -> no_shmemop x | _ -> T) /\
      (match h with SOME (x,_,_) -> no_shmemop x | _ -> T)) /\
   (no_shmemop (stack_Seq p1 p2) <=> no_shmemop p1 /\ no_shmemop p2) /\
   (no_shmemop (stack_If _ _ _ p1 p2) <=> no_shmemop p1 /\ no_shmemop p2) /\
   (no_shmemop (stack_Loop p) <=> no_shmemop p) /\
   (no_shmemop (ShMemOp _ _ _) <=> F) /\
   (no_shmemop _ <=> T)`;;

let no_shmemop_ind = cake_ind "no_shmemop";;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let STACKPROPSAUX_io_mono = prove
 (`!p (x:(A,C,FFI)stack_state) k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k1) x)))))
       (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k2) x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (x:(A,C,FFI)stack_state)`]
          (INST [`d:num`,`extra:num`] stack_evaluate_add_clock_io_events_mono)) THEN
  SIMP[]);;

let STACKPROPSAUX_io_chain = prove
 (`!p (x:(A,C,FFI)stack_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k) x)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[STACKPROPSAUX_io_mono; LE_CASES]);;
