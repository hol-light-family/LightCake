(* ========================================================================= *)
(* wordProps: port of HOL4 compiler/backend/semantics/wordPropsScript.sml    *)
(* (CakeML v3479).                                                           *)
(* Properties about wordLang and its semantics.                              *)
(*                                                                           *)
(* Main lemmas:                                                              *)
(* 0) Clock lemmas (add_clock, dec_clock, IO monotonicity)                   *)
(* 1) Code table constancy across eval                                       *)
(* 2) Swapping stack for one with identical values (but different keys)     *)
(* 3) Thms to handle the permutation oracle                                  *)
(* 4) Effect of extra locals (locals_rel)                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang and wordSem are those of wordLang.ml and          *)
(*   wordSem.ml (wl_get_var, wl_state_locals, ...): HOL4 s.f is             *)
(*   wl_state_f s, s with f := v is wl_state_f_fupd (K v) s.                 *)
(* - HOL4 case_eq_thms (the case equations of pair, bool, option, list,     *)
(*   word_loc, inst, arith, addr, memop, result and ffi_result) is the list  *)
(*   wl_case_eq_thms.                                                        *)
(* - The HOL4 Overload PERM_STACK is written out where used.                 *)
(* - Variables whose types HOL4 leaves free keep their own type variables:  *)
(*   the state t of gc_s_val_eq_gen, push_env_pop_env_s_key_eq and          *)
(*   get_vars_stack_swap is (A,D,E)wl_state, the unused x of gc_s_val_eq is  *)
(*   x:B, the size table of the find_code lemmas is (L)spt.                  *)
(* - The proofs over evaluate use the induction wl_evaluate_ind on the pair *)
(*   (prog,state) (IL2AUX_EVAL_IND_TAC) and local tactics (IL2AUX_...) that  *)
(*   split the evaluation, instantiate the induction hypotheses at the      *)
(*   evaluations of the branch, and shift clocks with evaluate_add_clock.    *)
(* - In wl_evaluate_stack_swap the HOL4 marker Abbrev (m = s1.locals_size) *)
(*   is the plain equation (Abbrev is the identity).                         *)
(* - Every Definition and Theorem of the HOL4 script is ported.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;

prioritize_num();;
type_invention_error := true;;

(* TODO move *)

let domain_fromAList_toAList = prove
 (`domain (fromAList (toAList (l:(A)spt))) = domain l`,
  REWRITE_TAC[domain_fromAList; set_MAP_FST_toAList_domain]);;

(* TODO: move *)

let mem_list_rearrange = prove
 (`!ls (x:A) f. MEM x (list_rearrange f ls) <=> MEM x ls`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_rearrange_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MEM_GENLIST] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BIJ_IFF_INV; pred_set_count_DEF; IN_ELIM_THM]) THEN
  ASM_MESON_TAC[]);;

let PERM_list_rearrange = prove
 (`!f (xs:A list). ALL_DISTINCT xs ==> PERM xs (list_rearrange f xs)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  ASM_REWRITE_TAC[mem_list_rearrange] THEN
  REWRITE_TAC[list_rearrange_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BIJ_DEF; INJ; SURJ; pred_set_count_DEF;
                                                IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EL_ALL_DISTINCT_EL_EQ]) THEN
  ASM_MESON_TAC[]);;

let PERM_ALL_DISTINCT_MAP = prove
 (`!xs ys. PERM xs ys ==>
           ALL_DISTINCT (MAP (f:A->B) xs) ==>
           ALL_DISTINCT (MAP f ys) /\ !x. MEM x ys <=> MEM x xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `PERM (MAP (f:A->B) xs) (MAP f ys)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERM_MAP]; ALL_TAC] THEN
  ASM_MESON_TAC[ALL_DISTINCT_PERM; MEM_PERM]);;

let ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME = prove
 (`ALL_DISTINCT (MAP FST (xs:(A#B)list)) /\ MEM (x,y) xs ==> ALOOKUP xs x = SOME y`,
  SPEC_TAC(`y:B`,`y:B`) THEN SPEC_TAC(`x:A`,`x:A`) THEN
  SPEC_TAC(`xs:(A#B)list`,`xs:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `MEM (x:A) (MAP FST (t:(A#B)list))` MP_TAC THENL
       [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[FST];
        ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]]]);;

(* Clock lemmas *)

(* HOL4: case_eq_thms; line 90 *)
let wl_case_eq_thms = end_itlist CONJ
  ([pair_case_eq; COND_CASE_EQ; option_case_eq; list_case_eq] @
   map case_eq ["word_loc"; "inst"; "asm_arith"; "addr"; "memop"; "wl_result";
                "ffi_result"]);;

(* the state functions of wordSem, for the record lemmas below *)

let IL2AUX_state_defs =
  [wl_get_var_def; wl_set_var_def; wl_unset_var_def; wl_set_vars_def; wl_get_store_def;
   wl_set_store_def; wl_call_env_def; wl_get_fp_var_def; wl_set_fp_var_def;
   wl_mem_load_def; wl_mem_store_def; wl_dec_clock_def; wl_get_var_imm_def;
   wl_has_space_def];;

(* F .. = SOME s' ==> ... (or = (r,s')): split the cases of F, substitute *)

let IL2AUX_SOME_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[];;

(* F .. (s with f := v) = OPTION_MAP (\s. s with f := v) (F .. s) and the like *)

let IL2AUX_WITH_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC defs THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[] THEN REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

(* the cases of an instruction, down to the constructors of asm_arith,     *)
(* memop and fp *)

let IL2AUX_INST_SPLIT_TAC : tactic =
  STRUCT_CASES_TAC (ISPEC `i:(A)inst` (cases "inst")) THENL
   [ALL_TAC; ALL_TAC;
    STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith"));
    STRUCT_CASES_TAC (ISPEC `a0:memop` (cases "memop")) THEN
    STRUCT_CASES_TAC (ISPEC `a2:(A)addr` (cases "addr"));
    STRUCT_CASES_TAC (ISPEC `a:fp` (cases "fp"))];;

(* line 103 [simp] *)
let state_const = prove
 (`((wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state)) = (wl_state_locals_fupd (K l') s) <=> l
     = l') /\
   ((wl_state_permute_fupd (K p) s) = (wl_state_permute_fupd (K p') s) <=> p = p') /\
   ((wl_state_clock_fupd (K clk) s) = (wl_state_clock_fupd (K clk') s) <=> clk = clk') /\
   ((wl_state_stack_fupd (K xs) s) = (wl_state_stack_fupd (K xs') s) <=> xs = xs')`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let _ = cake_add_simps [state_const];;

(* line 112 [simp] *)
let PAIR_MAP_EQ_PAIR = prove
 (`((f:A->C) ## (g:B->D)) p = (a,b) <=> ?x y. p = (x,y) /\ f x = a /\ g y = b`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; PAIR_EQ] THEN MESON_TAC[]);;

let _ = cake_add_simps [PAIR_MAP_EQ_PAIR];;

(* HOL4: OPTION_CASE_OPTION_MAP[simp]; line 122 *)
let wl_OPTION_CASE_OPTION_MAP = prove
 (`(option_CASE (OPTION_MAP (f:A->B) a) (e:C) g) = option_CASE a e (\x. g (f x))`,
  STRUCT_CASES_TAC (ISPEC `a:A option` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE]);;

let _ = cake_add_simps [wl_OPTION_CASE_OPTION_MAP];;

(* line 130 *)
let OPTION_CASE_MAP = prove
 (`option_CASE (x:A option) NONE (\x. SOME ((f:A->B) x)) = OPTION_MAP f x`,
  STRUCT_CASES_TAC (ISPEC `x:A option` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE]);;

(* HOL4: get_var_with_const[simp]; line 137 *)
let wl_get_var_with_const = prove
 (`wl_get_var x (wl_state_locals_size_fupd (K ls) (y:(A,C,FFI)wl_state)) = wl_get_var x y /\
   wl_get_var x (wl_state_fp_regs_fupd (K fp) y) = wl_get_var x y /\
   wl_get_var x (wl_state_store_fupd (K store) y) = wl_get_var x y /\
   wl_get_var x (wl_state_stack_fupd (K xs) y) = wl_get_var x y /\
   wl_get_var x (wl_state_stack_limit_fupd (K sl) y) = wl_get_var x y /\
   wl_get_var x (wl_state_stack_max_fupd (K sm) y) = wl_get_var x y /\
   wl_get_var x (wl_state_stack_size_fupd (K ssize) y) = wl_get_var x y /\
   wl_get_var x (wl_state_memory_fupd (K m) y) = wl_get_var x y /\
   wl_get_var x (wl_state_mdomain_fupd (K md) y) = wl_get_var x y /\
   wl_get_var x (wl_state_sh_mdomain_fupd (K smd) y) = wl_get_var x y /\
   wl_get_var x (wl_state_permute_fupd (K p) y) = wl_get_var x y /\
   wl_get_var x (wl_state_compile_fupd (K c) y) = wl_get_var x y /\
   wl_get_var x (wl_state_compile_oracle_fupd (K co) y) = wl_get_var x y /\
   wl_get_var x (wl_state_code_buffer_fupd (K cb) y) = wl_get_var x y /\
   wl_get_var x (wl_state_data_buffer_fupd (K db) y) = wl_get_var x y /\
   wl_get_var x (wl_state_gc_fun_fupd (K g) y) = wl_get_var x y /\
   wl_get_var x (wl_state_handler_fupd (K hd) y) = wl_get_var x y /\
   wl_get_var x (wl_state_clock_fupd (K clk) y) = wl_get_var x y /\
   wl_get_var x (wl_state_termdep_fupd (K tdep) y) = wl_get_var x y /\
   wl_get_var x (wl_state_code_fupd (K cd) y) = wl_get_var x y /\
   wl_get_var x (wl_state_be_fupd (K b) y) = wl_get_var x y /\
   wl_get_var x (wl_state_ffi_fupd (K ffi) y) = wl_get_var x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_get_var_with_const];;

(* HOL4: get_vars_with_const[simp]; line 164 *)
let wl_get_vars_with_const = prove
 (`wl_get_vars x (wl_state_locals_size_fupd (K ls) (y:(A,C,FFI)wl_state)) = wl_get_vars x y /\
   wl_get_vars x (wl_state_fp_regs_fupd (K fp) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_store_fupd (K store) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_stack_fupd (K xs) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_stack_limit_fupd (K sl) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_stack_max_fupd (K sm) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_stack_size_fupd (K ssize) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_memory_fupd (K m) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_mdomain_fupd (K md) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_sh_mdomain_fupd (K smd) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_permute_fupd (K p) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_compile_fupd (K c) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_compile_oracle_fupd (K co) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_code_buffer_fupd (K cb) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_data_buffer_fupd (K db) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_gc_fun_fupd (K g) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_handler_fupd (K hd) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_clock_fupd (K clk) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_termdep_fupd (K tdep) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_code_fupd (K cd) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_be_fupd (K b) y) = wl_get_vars x y /\
   wl_get_vars x (wl_state_ffi_fupd (K ffi) y) = wl_get_vars x y`,
  SPEC_TAC(`x:num list`,`x:num list`) THEN LIST_INDUCT_TAC THEN
  SIMP[wl_get_vars_def]);;

let _ = cake_add_simps [wl_get_vars_with_const];;

(* HOL4: set_var_const[simp]; line 191 *)
let wl_set_var_const = prove
 (`(wl_state_locals_size (wl_set_var x y (z:(A,C,FFI)wl_state))) = (wl_state_locals_size z) /\
   (wl_state_fp_regs (wl_set_var x y z)) = (wl_state_fp_regs z) /\
   (wl_state_store (wl_set_var x y z)) = (wl_state_store z) /\
   (wl_state_stack (wl_set_var x y z)) = (wl_state_stack z) /\
   (wl_state_stack_limit (wl_set_var x y z)) = (wl_state_stack_limit z) /\
   (wl_state_stack_max (wl_set_var x y z)) = (wl_state_stack_max z) /\
   (wl_state_stack_size (wl_set_var x y z)) = (wl_state_stack_size z) /\
   (wl_state_memory (wl_set_var x y z)) = (wl_state_memory z) /\
   (wl_state_mdomain (wl_set_var x y z)) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain (wl_set_var x y z)) = (wl_state_sh_mdomain z) /\
   (wl_state_permute (wl_set_var x y z)) = (wl_state_permute z) /\
   (wl_state_compile (wl_set_var x y z)) = (wl_state_compile z) /\
   (wl_state_compile_oracle (wl_set_var x y z)) = (wl_state_compile_oracle z) /\
   (wl_state_code_buffer (wl_set_var x y z)) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer (wl_set_var x y z)) = (wl_state_data_buffer z) /\
   (wl_state_gc_fun (wl_set_var x y z)) = (wl_state_gc_fun z) /\
   (wl_state_handler (wl_set_var x y z)) = (wl_state_handler z) /\
   (wl_state_clock (wl_set_var x y z)) = (wl_state_clock z) /\
   (wl_state_termdep (wl_set_var x y z)) = (wl_state_termdep z) /\
   (wl_state_code (wl_set_var x y z)) = (wl_state_code z) /\
   (wl_state_be (wl_set_var x y z)) = (wl_state_be z) /\
   (wl_state_ffi (wl_set_var x y z)) = (wl_state_ffi z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_var_const];;

(* HOL4: set_var_with_const[simp]; line 218 *)
let wl_set_var_with_const = prove
 (`wl_set_var x y (wl_state_locals_size_fupd (K ls) (z:(A,C,FFI)wl_state))
     = wl_state_locals_size_fupd (K ls) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_fp_regs_fupd (K fp) z)
       = wl_state_fp_regs_fupd (K fp) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_store_fupd (K store) z)
       = wl_state_store_fupd (K store) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_stack_fupd (K xs) z) = wl_state_stack_fupd (K xs) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_stack_limit_fupd (K sl) z)
       = wl_state_stack_limit_fupd (K sl) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_stack_max_fupd (K sm) z)
       = wl_state_stack_max_fupd (K sm) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_stack_size_fupd (K ssize) z)
       = wl_state_stack_size_fupd (K ssize) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_memory_fupd (K m) z) = wl_state_memory_fupd (K m) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_mdomain_fupd (K md) z)
       = wl_state_mdomain_fupd (K md) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_sh_mdomain_fupd (K smd) z)
       = wl_state_sh_mdomain_fupd (K smd) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_permute_fupd (K p) z)
       = wl_state_permute_fupd (K p) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_compile_fupd (K c) z)
       = wl_state_compile_fupd (K c) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_compile_oracle_fupd (K co) z)
       = wl_state_compile_oracle_fupd (K co) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_code_buffer_fupd (K cb) z)
       = wl_state_code_buffer_fupd (K cb) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_data_buffer_fupd (K db) z)
       = wl_state_data_buffer_fupd (K db) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_gc_fun_fupd (K g) z) = wl_state_gc_fun_fupd (K g) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_handler_fupd (K hd) z)
       = wl_state_handler_fupd (K hd) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_clock_fupd (K clk) z)
       = wl_state_clock_fupd (K clk) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_termdep_fupd (K tdep) z)
       = wl_state_termdep_fupd (K tdep) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_code_fupd (K cd) z) = wl_state_code_fupd (K cd) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_be_fupd (K b) z) = wl_state_be_fupd (K b) (wl_set_var x y z) /\
   wl_set_var x y (wl_state_ffi_fupd (K ffi) z) = wl_state_ffi_fupd (K ffi) (wl_set_var x y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_var_with_const];;

(* line 245 [simp] *)
let unset_var_const = prove
 (`(wl_state_locals_size (wl_unset_var x (z:(A,C,FFI)wl_state))) = (wl_state_locals_size z) /\
   (wl_state_fp_regs (wl_unset_var x z)) = (wl_state_fp_regs z) /\
   (wl_state_store (wl_unset_var x z)) = (wl_state_store z) /\
   (wl_state_stack (wl_unset_var x z)) = (wl_state_stack z) /\
   (wl_state_stack_limit (wl_unset_var x z)) = (wl_state_stack_limit z) /\
   (wl_state_stack_max (wl_unset_var x z)) = (wl_state_stack_max z) /\
   (wl_state_stack_size (wl_unset_var x z)) = (wl_state_stack_size z) /\
   (wl_state_memory (wl_unset_var x z)) = (wl_state_memory z) /\
   (wl_state_mdomain (wl_unset_var x z)) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain (wl_unset_var x z)) = (wl_state_sh_mdomain z) /\
   (wl_state_permute (wl_unset_var x z)) = (wl_state_permute z) /\
   (wl_state_compile (wl_unset_var x z)) = (wl_state_compile z) /\
   (wl_state_compile_oracle (wl_unset_var x z)) = (wl_state_compile_oracle z) /\
   (wl_state_code_buffer (wl_unset_var x z)) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer (wl_unset_var x z)) = (wl_state_data_buffer z) /\
   (wl_state_gc_fun (wl_unset_var x z)) = (wl_state_gc_fun z) /\
   (wl_state_handler (wl_unset_var x z)) = (wl_state_handler z) /\
   (wl_state_clock (wl_unset_var x z)) = (wl_state_clock z) /\
   (wl_state_termdep (wl_unset_var x z)) = (wl_state_termdep z) /\
   (wl_state_code (wl_unset_var x z)) = (wl_state_code z) /\
   (wl_state_be (wl_unset_var x z)) = (wl_state_be z) /\
   (wl_state_ffi (wl_unset_var x z)) = (wl_state_ffi z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [unset_var_const];;

(* line 272 [simp] *)
let unset_var_with_const = prove
 (`wl_unset_var x (wl_state_locals_size_fupd (K ls) (z:(A,C,FFI)wl_state))
     = wl_state_locals_size_fupd (K ls) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_fp_regs_fupd (K fp) z)
       = wl_state_fp_regs_fupd (K fp) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_store_fupd (K store) z)
       = wl_state_store_fupd (K store) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_stack_fupd (K xs) z) = wl_state_stack_fupd (K xs) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_stack_limit_fupd (K sl) z)
       = wl_state_stack_limit_fupd (K sl) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_stack_max_fupd (K sm) z)
       = wl_state_stack_max_fupd (K sm) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_stack_size_fupd (K ssize) z)
       = wl_state_stack_size_fupd (K ssize) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_memory_fupd (K m) z) = wl_state_memory_fupd (K m) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_mdomain_fupd (K md) z)
       = wl_state_mdomain_fupd (K md) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_sh_mdomain_fupd (K smd) z)
       = wl_state_sh_mdomain_fupd (K smd) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_permute_fupd (K p) z)
       = wl_state_permute_fupd (K p) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_compile_fupd (K c) z)
       = wl_state_compile_fupd (K c) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_compile_oracle_fupd (K co) z)
       = wl_state_compile_oracle_fupd (K co) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_code_buffer_fupd (K cb) z)
       = wl_state_code_buffer_fupd (K cb) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_data_buffer_fupd (K db) z)
       = wl_state_data_buffer_fupd (K db) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_gc_fun_fupd (K g) z) = wl_state_gc_fun_fupd (K g) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_handler_fupd (K hd) z)
       = wl_state_handler_fupd (K hd) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_clock_fupd (K clk) z)
       = wl_state_clock_fupd (K clk) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_termdep_fupd (K tdep) z)
       = wl_state_termdep_fupd (K tdep) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_code_fupd (K cd) z) = wl_state_code_fupd (K cd) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_be_fupd (K b) z) = wl_state_be_fupd (K b) (wl_unset_var x z) /\
   wl_unset_var x (wl_state_ffi_fupd (K ffi) z) = wl_state_ffi_fupd (K ffi) (wl_unset_var x z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [unset_var_with_const];;

(* HOL4: set_vars_const[simp]; line 299 *)
let wl_set_vars_const = prove
 (`(wl_state_locals_size (wl_set_vars x y (z:(A,C,FFI)wl_state))) = (wl_state_locals_size z) /\
   (wl_state_fp_regs (wl_set_vars x y z)) = (wl_state_fp_regs z) /\
   (wl_state_store (wl_set_vars x y z)) = (wl_state_store z) /\
   (wl_state_stack (wl_set_vars x y z)) = (wl_state_stack z) /\
   (wl_state_stack_limit (wl_set_vars x y z)) = (wl_state_stack_limit z) /\
   (wl_state_stack_max (wl_set_vars x y z)) = (wl_state_stack_max z) /\
   (wl_state_stack_size (wl_set_vars x y z)) = (wl_state_stack_size z) /\
   (wl_state_memory (wl_set_vars x y z)) = (wl_state_memory z) /\
   (wl_state_mdomain (wl_set_vars x y z)) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain (wl_set_vars x y z)) = (wl_state_sh_mdomain z) /\
   (wl_state_permute (wl_set_vars x y z)) = (wl_state_permute z) /\
   (wl_state_compile (wl_set_vars x y z)) = (wl_state_compile z) /\
   (wl_state_compile_oracle (wl_set_vars x y z)) = (wl_state_compile_oracle z) /\
   (wl_state_code_buffer (wl_set_vars x y z)) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer (wl_set_vars x y z)) = (wl_state_data_buffer z) /\
   (wl_state_gc_fun (wl_set_vars x y z)) = (wl_state_gc_fun z) /\
   (wl_state_handler (wl_set_vars x y z)) = (wl_state_handler z) /\
   (wl_state_clock (wl_set_vars x y z)) = (wl_state_clock z) /\
   (wl_state_termdep (wl_set_vars x y z)) = (wl_state_termdep z) /\
   (wl_state_code (wl_set_vars x y z)) = (wl_state_code z) /\
   (wl_state_be (wl_set_vars x y z)) = (wl_state_be z) /\
   (wl_state_ffi (wl_set_vars x y z)) = (wl_state_ffi z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_vars_const];;

(* HOL4: set_vars_with_const[simp]; line 326 *)
let wl_set_vars_with_const = prove
 (`wl_set_vars x y (wl_state_locals_size_fupd (K ls) (z:(A,C,FFI)wl_state))
     = wl_state_locals_size_fupd (K ls) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_fp_regs_fupd (K fp) z)
       = wl_state_fp_regs_fupd (K fp) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_store_fupd (K store) z)
       = wl_state_store_fupd (K store) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_stack_fupd (K xs) z)
       = wl_state_stack_fupd (K xs) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_stack_limit_fupd (K sl) z)
       = wl_state_stack_limit_fupd (K sl) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_stack_max_fupd (K sm) z)
       = wl_state_stack_max_fupd (K sm) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_stack_size_fupd (K ssize) z)
       = wl_state_stack_size_fupd (K ssize) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_memory_fupd (K m) z)
       = wl_state_memory_fupd (K m) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_mdomain_fupd (K md) z)
       = wl_state_mdomain_fupd (K md) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_sh_mdomain_fupd (K smd) z)
       = wl_state_sh_mdomain_fupd (K smd) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_permute_fupd (K p) z)
       = wl_state_permute_fupd (K p) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_compile_fupd (K c) z)
       = wl_state_compile_fupd (K c) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_compile_oracle_fupd (K co) z)
       = wl_state_compile_oracle_fupd (K co) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_code_buffer_fupd (K cb) z)
       = wl_state_code_buffer_fupd (K cb) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_data_buffer_fupd (K db) z)
       = wl_state_data_buffer_fupd (K db) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_gc_fun_fupd (K g) z)
       = wl_state_gc_fun_fupd (K g) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_handler_fupd (K hd) z)
       = wl_state_handler_fupd (K hd) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_clock_fupd (K clk) z)
       = wl_state_clock_fupd (K clk) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_termdep_fupd (K tdep) z)
       = wl_state_termdep_fupd (K tdep) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_code_fupd (K cd) z) = wl_state_code_fupd (K cd) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_be_fupd (K b) z) = wl_state_be_fupd (K b) (wl_set_vars x y z) /\
   wl_set_vars x y (wl_state_ffi_fupd (K ffi) z) = wl_state_ffi_fupd (K ffi) (wl_set_vars x y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_vars_with_const];;

(* line 353 [simp] *)
let get_store_with_const = prove
 (`wl_get_store x (wl_state_locals_fupd (K l) (y:(A,C,FFI)wl_state)) = wl_get_store x y /\
   wl_get_store x (wl_state_locals_size_fupd (K ls) y) = wl_get_store x y /\
   wl_get_store x (wl_state_fp_regs_fupd (K fp) y) = wl_get_store x y /\
   wl_get_store x (wl_state_stack_fupd (K xs) y) = wl_get_store x y /\
   wl_get_store x (wl_state_stack_limit_fupd (K sl) y) = wl_get_store x y /\
   wl_get_store x (wl_state_stack_max_fupd (K sm) y) = wl_get_store x y /\
   wl_get_store x (wl_state_stack_size_fupd (K ssize) y) = wl_get_store x y /\
   wl_get_store x (wl_state_memory_fupd (K m) y) = wl_get_store x y /\
   wl_get_store x (wl_state_mdomain_fupd (K md) y) = wl_get_store x y /\
   wl_get_store x (wl_state_sh_mdomain_fupd (K smd) y) = wl_get_store x y /\
   wl_get_store x (wl_state_permute_fupd (K p) y) = wl_get_store x y /\
   wl_get_store x (wl_state_compile_fupd (K c) y) = wl_get_store x y /\
   wl_get_store x (wl_state_compile_oracle_fupd (K co) y) = wl_get_store x y /\
   wl_get_store x (wl_state_code_buffer_fupd (K cb) y) = wl_get_store x y /\
   wl_get_store x (wl_state_data_buffer_fupd (K db) y) = wl_get_store x y /\
   wl_get_store x (wl_state_gc_fun_fupd (K g) y) = wl_get_store x y /\
   wl_get_store x (wl_state_handler_fupd (K hd) y) = wl_get_store x y /\
   wl_get_store x (wl_state_clock_fupd (K clk) y) = wl_get_store x y /\
   wl_get_store x (wl_state_termdep_fupd (K tdep) y) = wl_get_store x y /\
   wl_get_store x (wl_state_code_fupd (K cd) y) = wl_get_store x y /\
   wl_get_store x (wl_state_be_fupd (K b) y) = wl_get_store x y /\
   wl_get_store x (wl_state_ffi_fupd (K ffi) y) = wl_get_store x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [get_store_with_const];;

(* HOL4: set_store_const[simp]; line 380 *)
let wl_set_store_const = prove
 (`(wl_state_locals (wl_set_store x y (z:(A,C,FFI)wl_state))) = (wl_state_locals z) /\
   (wl_state_locals_size (wl_set_store x y z)) = (wl_state_locals_size z) /\
   (wl_state_fp_regs (wl_set_store x y z)) = (wl_state_fp_regs z) /\
   (wl_state_stack (wl_set_store x y z)) = (wl_state_stack z) /\
   (wl_state_stack_limit (wl_set_store x y z)) = (wl_state_stack_limit z) /\
   (wl_state_stack_max (wl_set_store x y z)) = (wl_state_stack_max z) /\
   (wl_state_stack_size (wl_set_store x y z)) = (wl_state_stack_size z) /\
   (wl_state_memory (wl_set_store x y z)) = (wl_state_memory z) /\
   (wl_state_mdomain (wl_set_store x y z)) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain (wl_set_store x y z)) = (wl_state_sh_mdomain z) /\
   (wl_state_permute (wl_set_store x y z)) = (wl_state_permute z) /\
   (wl_state_compile (wl_set_store x y z)) = (wl_state_compile z) /\
   (wl_state_compile_oracle (wl_set_store x y z)) = (wl_state_compile_oracle z) /\
   (wl_state_code_buffer (wl_set_store x y z)) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer (wl_set_store x y z)) = (wl_state_data_buffer z) /\
   (wl_state_gc_fun (wl_set_store x y z)) = (wl_state_gc_fun z) /\
   (wl_state_handler (wl_set_store x y z)) = (wl_state_handler z) /\
   (wl_state_clock (wl_set_store x y z)) = (wl_state_clock z) /\
   (wl_state_termdep (wl_set_store x y z)) = (wl_state_termdep z) /\
   (wl_state_code (wl_set_store x y z)) = (wl_state_code z) /\
   (wl_state_be (wl_set_store x y z)) = (wl_state_be z) /\
   (wl_state_ffi (wl_set_store x y z)) = (wl_state_ffi z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_store_const];;

(* HOL4: set_store_with_const[simp]; line 407 *)
let wl_set_store_with_const = prove
 (`wl_set_store x y (wl_state_locals_fupd (K l) (z:(A,C,FFI)wl_state))
     = wl_state_locals_fupd (K l) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_locals_size_fupd (K ls) z)
       = wl_state_locals_size_fupd (K ls) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_fp_regs_fupd (K fp) z)
       = wl_state_fp_regs_fupd (K fp) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_stack_fupd (K xs) z)
       = wl_state_stack_fupd (K xs) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_stack_limit_fupd (K sl) z)
       = wl_state_stack_limit_fupd (K sl) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_stack_max_fupd (K sm) z)
       = wl_state_stack_max_fupd (K sm) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_stack_size_fupd (K ssize) z)
       = wl_state_stack_size_fupd (K ssize) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_memory_fupd (K m) z)
       = wl_state_memory_fupd (K m) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_mdomain_fupd (K md) z)
       = wl_state_mdomain_fupd (K md) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_sh_mdomain_fupd (K smd) z)
       = wl_state_sh_mdomain_fupd (K smd) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_permute_fupd (K p) z)
       = wl_state_permute_fupd (K p) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_compile_fupd (K c) z)
       = wl_state_compile_fupd (K c) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_compile_oracle_fupd (K co) z)
       = wl_state_compile_oracle_fupd (K co) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_code_buffer_fupd (K cb) z)
       = wl_state_code_buffer_fupd (K cb) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_data_buffer_fupd (K db) z)
       = wl_state_data_buffer_fupd (K db) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_gc_fun_fupd (K g) z)
       = wl_state_gc_fun_fupd (K g) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_handler_fupd (K hd) z)
       = wl_state_handler_fupd (K hd) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_clock_fupd (K clk) z)
       = wl_state_clock_fupd (K clk) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_termdep_fupd (K tdep) z)
       = wl_state_termdep_fupd (K tdep) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_code_fupd (K cd) z)
       = wl_state_code_fupd (K cd) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_be_fupd (K b) z) = wl_state_be_fupd (K b) (wl_set_store x y z) /\
   wl_set_store x y (wl_state_ffi_fupd (K ffi) z) = wl_state_ffi_fupd (K ffi) (wl_set_store x y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_store_with_const];;

(* HOL4: push_env_const[simp]; line 435 *)
let wl_push_env_const = prove
 (`(wl_state_clock (wl_push_env x y (z:(A,C,FFI)wl_state))) = (wl_state_clock z) /\
   (wl_state_memory (wl_push_env x y z)) = (wl_state_memory z) /\
   (wl_state_store (wl_push_env x y z)) = (wl_state_store z) /\
   (wl_state_handler (wl_push_env x NONE z)) = (wl_state_handler z) /\
   (wl_state_ffi (wl_push_env x y z)) = (wl_state_ffi z) /\
   (wl_state_termdep (wl_push_env x y z)) = (wl_state_termdep z) /\
   (wl_state_data_buffer (wl_push_env x y z)) = (wl_state_data_buffer z) /\
   (wl_state_code_buffer (wl_push_env x y z)) = (wl_state_code_buffer z) /\
   (wl_state_compile (wl_push_env x y z)) = (wl_state_compile z) /\
   (wl_state_compile_oracle (wl_push_env x y z)) = (wl_state_compile_oracle z) /\
   (wl_state_mdomain (wl_push_env x y z)) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain (wl_push_env x y z)) = (wl_state_sh_mdomain z) /\
   (wl_state_gc_fun (wl_push_env x y z)) = (wl_state_gc_fun z) /\
   (wl_state_be (wl_push_env x y z)) = (wl_state_be z) /\
   (wl_state_fp_regs (wl_push_env x y z)) = (wl_state_fp_regs z) /\
   (wl_state_code (wl_push_env x y z)) = (wl_state_code z) /\
   (wl_state_stack_limit (wl_push_env x y z)) = (wl_state_stack_limit z) /\
   (wl_state_stack_size (wl_push_env x y z)) = (wl_state_stack_size z)`,
  SPEC_TAC(`y:(num#(A)wl_prog#num#num)option`,`y:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN SIMP[]);;

let _ = cake_add_simps [wl_push_env_const];;

(* HOL4: push_env_with_const[simp]; line 461 *)
let wl_push_env_with_const = prove
 (`(wl_push_env x y (wl_state_clock_fupd (K k) (z:(A,C,FFI)wl_state))
     = wl_state_clock_fupd (K k) (wl_push_env x y z)) /\
   (wl_push_env x y (wl_state_compile_fupd (K c) z)
       = wl_state_compile_fupd (K c) (wl_push_env x y z)) /\
   (wl_push_env x y (wl_state_compile_oracle_fupd (K co) z)
       = wl_state_compile_oracle_fupd (K co) (wl_push_env x y z)) /\
   (wl_push_env x y (wl_state_code_fupd (K code) z)
       = wl_state_code_fupd (K code) (wl_push_env x y z)) /\
   (wl_push_env x y (wl_state_termdep_fupd (K termdep) z)
       = wl_state_termdep_fupd (K termdep) (wl_push_env x y z)) /\
   (wl_push_env x y (wl_state_locals_fupd (K l) z)
       = wl_state_locals_fupd (K l) (wl_push_env x y z))`,
  SPEC_TAC(`y:(num#(A)wl_prog#num#num)option`,`y:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN SIMP[]);;

let _ = cake_add_simps [wl_push_env_with_const];;

(* HOL4: pop_env_const; line 475 *)
let wl_pop_env_const = prove
 (`wl_pop_env x = SOME (y:(A,C,FFI)wl_state) ==>
   (wl_state_clock y) = (wl_state_clock x) /\
   (wl_state_ffi y) = (wl_state_ffi x) /\
   (wl_state_be y) = (wl_state_be x) /\
   (wl_state_compile y) = (wl_state_compile x) /\
   (wl_state_compile_oracle y) = (wl_state_compile_oracle x) /\
   (wl_state_memory y) = (wl_state_memory x) /\
   (wl_state_mdomain y) = (wl_state_mdomain x) /\
   (wl_state_sh_mdomain y) = (wl_state_sh_mdomain x) /\
   (wl_state_store y) = (wl_state_store x) /\
   (wl_state_fp_regs y) = (wl_state_fp_regs x) /\
   (wl_state_gc_fun y) = (wl_state_gc_fun x) /\
   (wl_state_termdep y) = (wl_state_termdep x) /\
   (wl_state_permute y) = (wl_state_permute x) /\
   (wl_state_data_buffer y) = (wl_state_data_buffer x) /\
   (wl_state_code_buffer y) = (wl_state_code_buffer x) /\
   (wl_state_code y) = (wl_state_code x) /\
   (wl_state_stack_limit y) = (wl_state_stack_limit x) /\
   (wl_state_stack_max y) = (wl_state_stack_max x) /\
   (wl_state_stack_size y) = (wl_state_stack_size x)`,
  IL2AUX_SOME_TAC[wl_pop_env_def]);;

(* HOL4: pop_env_with_const[simp]; line 501 *)
let wl_pop_env_with_const = prove
 (`wl_pop_env (wl_state_clock_fupd (K k) (z:(A,C,FFI)wl_state))
     = OPTION_MAP (\s. wl_state_clock_fupd (K k) s) (wl_pop_env z) /\
   wl_pop_env (wl_state_compile_fupd (K c) z)
       = OPTION_MAP (\s. wl_state_compile_fupd (K c) s) (wl_pop_env z) /\
   wl_pop_env (wl_state_compile_oracle_fupd (K co) z)
       = OPTION_MAP (\s. wl_state_compile_oracle_fupd (K co) s) (wl_pop_env z) /\
   wl_pop_env (wl_state_code_fupd (K code) z)
       = OPTION_MAP (\s. wl_state_code_fupd (K code) s) (wl_pop_env z) /\
   wl_pop_env (wl_state_termdep_fupd (K termdep) z)
       = OPTION_MAP (\s. wl_state_termdep_fupd (K termdep) s) (wl_pop_env z) /\
   wl_pop_env (wl_state_permute_fupd (K perm) z)
       = OPTION_MAP (\s. wl_state_permute_fupd (K perm) s) (wl_pop_env z) /\
   wl_pop_env (wl_state_locals_fupd (K l) z) = wl_pop_env z /\
   wl_pop_env (wl_state_locals_size_fupd (K ls) z) = wl_pop_env z`,
  IL2AUX_WITH_TAC[wl_pop_env_def]);;

let _ = cake_add_simps [wl_pop_env_with_const];;

(* line 516 *)
let pop_env_code_gc_fun_clock = prove
 (`wl_pop_env (r:(A,C,FFI)wl_state) = SOME x ==>
   (wl_state_code r) = (wl_state_code x) /\
   (wl_state_code_buffer r) = (wl_state_code_buffer x) /\
   (wl_state_data_buffer r) = (wl_state_data_buffer x) /\
   (wl_state_gc_fun r) = (wl_state_gc_fun x) /\
   (wl_state_clock r) = (wl_state_clock x) /\
   (wl_state_be r) = (wl_state_be x) /\
   (wl_state_mdomain r) = (wl_state_mdomain x) /\
   (wl_state_sh_mdomain r) = (wl_state_sh_mdomain x) /\
   (wl_state_compile r) = (wl_state_compile x) /\
   (wl_state_compile_oracle r) = (wl_state_compile_oracle x) /\
   (wl_state_stack_limit r) = (wl_state_stack_limit x) /\
   (wl_state_stack_max r) = (wl_state_stack_max x) /\
   (wl_state_stack_size r) = (wl_state_stack_size x)`,
  IL2AUX_SOME_TAC[wl_pop_env_def]);;

(* HOL4: call_env_const[simp]; line 535 *)
let wl_call_env_const = prove
 (`(wl_state_store (wl_call_env x ss (y:(A,C,FFI)wl_state))) = (wl_state_store y) /\
   (wl_state_termdep (wl_call_env x ss y)) = (wl_state_termdep y) /\
   (wl_state_clock (wl_call_env x ss y)) = (wl_state_clock y) /\
   (wl_state_handler (wl_call_env x ss y)) = (wl_state_handler y) /\
   (wl_state_stack (wl_call_env x ss y)) = (wl_state_stack y) /\
   (wl_state_compile_oracle (wl_call_env x ss y)) = (wl_state_compile_oracle y) /\
   (wl_state_compile (wl_call_env x ss y)) = (wl_state_compile y) /\
   (wl_state_be (wl_call_env x ss y)) = (wl_state_be y) /\
   (wl_state_memory (wl_call_env x ss y)) = (wl_state_memory y) /\
   (wl_state_mdomain (wl_call_env x ss y)) = (wl_state_mdomain y) /\
   (wl_state_sh_mdomain (wl_call_env x ss y)) = (wl_state_sh_mdomain y) /\
   (wl_state_gc_fun (wl_call_env x ss y)) = (wl_state_gc_fun y) /\
   (wl_state_ffi (wl_call_env x ss y)) = (wl_state_ffi y) /\
   (wl_state_code (wl_call_env x ss y)) = (wl_state_code y) /\
   (wl_state_code_buffer (wl_call_env x ss y)) = (wl_state_code_buffer y) /\
   (wl_state_data_buffer (wl_call_env x ss y)) = (wl_state_data_buffer y) /\
   (wl_state_stack_limit (wl_call_env x ss y)) = (wl_state_stack_limit y) /\
   (wl_state_stack_size (wl_call_env x ss y)) = (wl_state_stack_size y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_call_env_const];;

(* HOL4: call_env_with_const[simp]; line 558 *)
let wl_call_env_with_const = prove
 (`wl_call_env x ss (wl_state_locals_fupd (K l) (y:(A,C,FFI)wl_state)) = wl_call_env x ss y /\
   wl_call_env x ss (wl_state_clock_fupd (K k) y)
       = wl_state_clock_fupd (K k) (wl_call_env x ss y) /\
   wl_call_env x ss (wl_state_termdep_fupd (K termdep) y)
       = wl_state_termdep_fupd (K termdep) (wl_call_env x ss y) /\
   wl_call_env x ss (wl_state_compile_fupd (K c) y)
       = wl_state_compile_fupd (K c) (wl_call_env x ss y) /\
   wl_call_env x ss (wl_state_compile_oracle_fupd (K co) y)
       = wl_state_compile_oracle_fupd (K co) (wl_call_env x ss y) /\
   wl_call_env x ss (wl_state_code_fupd (K code) y)
       = wl_state_code_fupd (K code) (wl_call_env x ss y) /\
   wl_call_env x ss (wl_state_handler_fupd (K k) y)
       = wl_state_handler_fupd (K k) (wl_call_env x ss y) /\
   wl_call_env x ss (wl_state_permute_fupd (K perm) y)
       = wl_state_permute_fupd (K perm) (wl_call_env x ss y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_call_env_with_const];;

(* line 571 [simp] *)
let flush_state_const = prove
 (`(wl_state_clock (wl_flush_state b (y:(A,C,FFI)wl_state))) = (wl_state_clock y) /\
   (wl_state_compile_oracle (wl_flush_state b y)) = (wl_state_compile_oracle y) /\
   (wl_state_compile (wl_flush_state b y)) = (wl_state_compile y) /\
   (wl_state_be (wl_flush_state b y)) = (wl_state_be y) /\
   (wl_state_gc_fun (wl_flush_state b y)) = (wl_state_gc_fun y) /\
   (wl_state_ffi (wl_flush_state b y)) = (wl_state_ffi y) /\
   (wl_state_code (wl_flush_state b y)) = (wl_state_code y) /\
   (wl_state_code_buffer (wl_flush_state b y)) = (wl_state_code_buffer y) /\
   (wl_state_data_buffer (wl_flush_state b y)) = (wl_state_data_buffer y) /\
   (wl_state_stack_limit (wl_flush_state b y)) = (wl_state_stack_limit y) /\
   (wl_state_stack_size (wl_flush_state b y)) = (wl_state_stack_size y) /\
   (wl_state_stack (wl_flush_state F y)) = (wl_state_stack y)`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[]);;

let _ = cake_add_simps [flush_state_const];;

(* line 588 [simp] *)
let flush_state_with_const = prove
 (`wl_flush_state b (wl_state_locals_fupd (K l) (y:(A,C,FFI)wl_state)) = wl_flush_state b y /\
   wl_flush_state b (wl_state_locals_size_fupd (K ls) y) = wl_flush_state b y /\
   wl_flush_state T (wl_state_stack_fupd (K xs) y) = wl_flush_state T y /\
   wl_flush_state b (wl_state_permute_fupd (K p) y)
       = wl_state_permute_fupd (K p) (wl_flush_state b y) /\
   wl_flush_state b (wl_state_stack_max_fupd (K sm) y)
       = wl_state_stack_max_fupd (K sm) (wl_flush_state b y) /\
   wl_flush_state b (wl_state_clock_fupd (K k) y) = wl_state_clock_fupd (K k) (wl_flush_state b y)`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[]);;

let _ = cake_add_simps [flush_state_with_const];;

(* line 599 [simp] *)
let has_space_with_const = prove
 (`wl_has_space x (wl_state_clock_fupd (K k) (y:(A,C,FFI)wl_state)) = wl_has_space x y /\
   wl_has_space x (wl_state_compile_fupd (K c) y) = wl_has_space x y /\
   wl_has_space x (wl_state_compile_oracle_fupd (K co) y) = wl_has_space x y /\
   wl_has_space x (wl_state_code_fupd (K code) y) = wl_has_space x y /\
   wl_has_space x (wl_state_termdep_fupd (K termdep) y) = wl_has_space x y /\
   wl_has_space x (wl_state_locals_fupd (K l) y) = wl_has_space x y /\
   wl_has_space x (wl_state_locals_size_fupd (K ls) y) = wl_has_space x y /\
   wl_has_space x (wl_state_stack_fupd (K xs) y) = wl_has_space x y`,
  REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [has_space_with_const];;

(* line 612 *)
let gc_const = prove
 (`wl_gc x = SOME (y:(A,C,FFI)wl_state) ==>
   (wl_state_clock y) = (wl_state_clock x) /\
   (wl_state_ffi y) = (wl_state_ffi x) /\
   (wl_state_code y) = (wl_state_code x) /\
   (wl_state_be y) = (wl_state_be x) /\
   (wl_state_code_buffer y) = (wl_state_code_buffer x) /\
   (wl_state_data_buffer y) = (wl_state_data_buffer x) /\
   (wl_state_compile y) = (wl_state_compile x) /\
   (wl_state_handler y) = (wl_state_handler x) /\
   (wl_state_compile_oracle y) = (wl_state_compile_oracle x) /\
   (wl_state_locals_size y) = (wl_state_locals_size x) /\
   (wl_state_stack_limit y) = (wl_state_stack_limit x) /\
   (wl_state_stack_max y) = (wl_state_stack_max x) /\
   (wl_state_stack_size y) = (wl_state_stack_size x)`,
  IL2AUX_SOME_TAC[wl_gc_def]);;

(* HOL4: gc_with_const[simp]; line 632 *)
let wl_gc_with_const = prove
 (`wl_gc (wl_state_clock_fupd (K k) (x:(A,C,FFI)wl_state))
     = OPTION_MAP (\s. wl_state_clock_fupd (K k) s) (wl_gc x) /\
   wl_gc (wl_state_compile_fupd (K c) x)
       = OPTION_MAP (\s. wl_state_compile_fupd (K c) s) (wl_gc x) /\
   wl_gc (wl_state_compile_oracle_fupd (K co) x)
       = OPTION_MAP (\s. wl_state_compile_oracle_fupd (K co) s) (wl_gc x) /\
   wl_gc (wl_state_code_fupd (K code) x)
       = OPTION_MAP (\s. wl_state_code_fupd (K code) s) (wl_gc x) /\
   wl_gc (wl_state_permute_fupd (K perm) x)
       = OPTION_MAP (\s. wl_state_permute_fupd (K perm) s) (wl_gc x) /\
   wl_gc (wl_state_termdep_fupd (K t) x)
       = OPTION_MAP (\s. wl_state_termdep_fupd (K t) s) (wl_gc x) /\
   wl_gc (wl_state_locals_fupd (K l) x) = OPTION_MAP (\s. wl_state_locals_fupd (K l) s) (wl_gc x) /\
   wl_gc (wl_state_locals_size_fupd (K ls) x)
       = OPTION_MAP (\s. wl_state_locals_size_fupd (K ls) s) (wl_gc x)`,
  IL2AUX_WITH_TAC[wl_gc_def]);;

let _ = cake_add_simps [wl_gc_with_const];;

(* the fields that gc does not change *)

let IL2AUX_gc_all = prove
 (`wl_gc (x:(A,C,FFI)wl_state) = SOME y ==>
   wl_state_clock y = wl_state_clock x /\ wl_state_ffi y = wl_state_ffi x /\
   wl_state_code y = wl_state_code x /\ wl_state_be y = wl_state_be x /\
   wl_state_code_buffer y = wl_state_code_buffer x /\
   wl_state_data_buffer y = wl_state_data_buffer x /\
   wl_state_compile y = wl_state_compile x /\ wl_state_handler y = wl_state_handler x /\
   wl_state_compile_oracle y = wl_state_compile_oracle x /\
   wl_state_locals_size y = wl_state_locals_size x /\
   wl_state_stack_limit y = wl_state_stack_limit x /\
   wl_state_stack_max y = wl_state_stack_max x /\
   wl_state_stack_size y = wl_state_stack_size x /\
   wl_state_gc_fun y = wl_state_gc_fun x /\ wl_state_mdomain y = wl_state_mdomain x /\
   wl_state_sh_mdomain y = wl_state_sh_mdomain x /\
   wl_state_permute y = wl_state_permute x /\
   wl_state_termdep y = wl_state_termdep x /\ wl_state_fp_regs y = wl_state_fp_regs x /\
   wl_state_locals y = wl_state_locals x`,
  IL2AUX_SOME_TAC[wl_gc_def]);;

(* HOL4: alloc_const; line 649 *)
let wl_alloc_const = prove
 (`wl_alloc c names (s:(A,C,FFI)wl_state) = (r,s') ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_ffi s') = (wl_state_ffi s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_size s') = (wl_state_stack_size s)`,
  IL2AUX_SOME_TAC[wl_alloc_def] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_gc_all)) THEN
  FS[wl_flush_state_def]);;

(* line 670 *)
let alloc_code_gc_fun_const = prove
 (`wl_alloc x names s = (res,(t:(A,C,FFI)wl_state)) ==>
   (wl_state_code t) = (wl_state_code s) /\
   (wl_state_code_buffer t) = (wl_state_code_buffer s) /\
   (wl_state_data_buffer t) = (wl_state_data_buffer s) /\
   (wl_state_gc_fun t) = (wl_state_gc_fun s) /\
   (wl_state_mdomain t) = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain t) = (wl_state_sh_mdomain s) /\
   (wl_state_be t) = (wl_state_be s) /\
   (wl_state_compile t) = (wl_state_compile s) /\
   (wl_state_compile_oracle t) = (wl_state_compile_oracle s) /\
   (wl_state_stack_limit t) = (wl_state_stack_limit s) /\
   (wl_state_stack_size t) = (wl_state_stack_size s)`,
  IL2AUX_SOME_TAC[wl_alloc_def] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_gc_all)) THEN
  FS[wl_flush_state_def]);;

(* HOL4: alloc_with_const[simp]; line 690 *)
let wl_alloc_with_const = prove
 (`wl_alloc c names (wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state))
     = (I ## (\s. wl_state_clock_fupd (K k) s)) (wl_alloc c names s) /\
   wl_alloc c names (wl_state_termdep_fupd (K t) s)
       = (I ## (\s. wl_state_termdep_fupd (K t) s)) (wl_alloc c names s) /\
   wl_alloc c names (wl_state_code_fupd (K code) s)
       = (I ## (\s. wl_state_code_fupd (K code) s)) (wl_alloc c names s) /\
   wl_alloc c names (wl_state_compile_oracle_fupd (K compile_oracle) s)
       = (I ## (\s. wl_state_compile_oracle_fupd (K compile_oracle) s)) (wl_alloc c names s) /\
   wl_alloc c names (wl_state_compile_fupd (K comp) s)
       = (I ## (\s. wl_state_compile_fupd (K comp) s)) (wl_alloc c names s)`,
  IL2AUX_WITH_TAC[wl_alloc_def; wl_flush_state_def]);;

let _ = cake_add_simps [wl_alloc_with_const];;

(* HOL4: get_fp_var_with_const[simp]; line 700 *)
let wl_get_fp_var_with_const = prove
 (`wl_get_fp_var x (wl_state_locals_fupd (K l) (y:(A,C,FFI)wl_state)) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_locals_size_fupd (K ls) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_store_fupd (K store) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_stack_fupd (K xs) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_stack_limit_fupd (K sl) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_stack_max_fupd (K sm) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_stack_size_fupd (K ssize) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_memory_fupd (K m) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_mdomain_fupd (K md) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_sh_mdomain_fupd (K smd) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_permute_fupd (K p) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_compile_fupd (K c) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_compile_oracle_fupd (K co) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_code_buffer_fupd (K cb) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_data_buffer_fupd (K db) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_gc_fun_fupd (K g) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_handler_fupd (K hd) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_clock_fupd (K clk) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_termdep_fupd (K tdep) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_code_fupd (K cd) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_be_fupd (K b) y) = wl_get_fp_var x y /\
   wl_get_fp_var x (wl_state_ffi_fupd (K ffi) y) = wl_get_fp_var x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_get_fp_var_with_const];;

(* HOL4: set_fp_var_const[simp]; line 727 *)
let wl_set_fp_var_const = prove
 (`(wl_state_locals (wl_set_fp_var x y (z:(A,C,FFI)wl_state))) = (wl_state_locals z) /\
   (wl_state_locals_size (wl_set_fp_var x y z)) = (wl_state_locals_size z) /\
   (wl_state_store (wl_set_fp_var x y z)) = (wl_state_store z) /\
   (wl_state_stack (wl_set_fp_var x y z)) = (wl_state_stack z) /\
   (wl_state_stack_limit (wl_set_fp_var x y z)) = (wl_state_stack_limit z) /\
   (wl_state_stack_max (wl_set_fp_var x y z)) = (wl_state_stack_max z) /\
   (wl_state_stack_size (wl_set_fp_var x y z)) = (wl_state_stack_size z) /\
   (wl_state_memory (wl_set_fp_var x y z)) = (wl_state_memory z) /\
   (wl_state_mdomain (wl_set_fp_var x y z)) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain (wl_set_fp_var x y z)) = (wl_state_sh_mdomain z) /\
   (wl_state_permute (wl_set_fp_var x y z)) = (wl_state_permute z) /\
   (wl_state_compile (wl_set_fp_var x y z)) = (wl_state_compile z) /\
   (wl_state_compile_oracle (wl_set_fp_var x y z)) = (wl_state_compile_oracle z) /\
   (wl_state_code_buffer (wl_set_fp_var x y z)) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer (wl_set_fp_var x y z)) = (wl_state_data_buffer z) /\
   (wl_state_gc_fun (wl_set_fp_var x y z)) = (wl_state_gc_fun z) /\
   (wl_state_handler (wl_set_fp_var x y z)) = (wl_state_handler z) /\
   (wl_state_clock (wl_set_fp_var x y z)) = (wl_state_clock z) /\
   (wl_state_termdep (wl_set_fp_var x y z)) = (wl_state_termdep z) /\
   (wl_state_code (wl_set_fp_var x y z)) = (wl_state_code z) /\
   (wl_state_be (wl_set_fp_var x y z)) = (wl_state_be z) /\
   (wl_state_ffi (wl_set_fp_var x y z)) = (wl_state_ffi z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_fp_var_const];;

(* HOL4: set_fp_var_with_const[simp]; line 754 *)
let wl_set_fp_var_with_const = prove
 (`wl_set_fp_var x y (wl_state_locals_fupd (K l) (z:(A,C,FFI)wl_state))
     = wl_state_locals_fupd (K l) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_locals_size_fupd (K ls) z)
       = wl_state_locals_size_fupd (K ls) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_store_fupd (K store) z)
       = wl_state_store_fupd (K store) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_stack_fupd (K xs) z)
       = wl_state_stack_fupd (K xs) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_stack_limit_fupd (K sl) z)
       = wl_state_stack_limit_fupd (K sl) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_stack_max_fupd (K sm) z)
       = wl_state_stack_max_fupd (K sm) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_stack_size_fupd (K ssize) z)
       = wl_state_stack_size_fupd (K ssize) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_memory_fupd (K m) z)
       = wl_state_memory_fupd (K m) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_mdomain_fupd (K md) z)
       = wl_state_mdomain_fupd (K md) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_sh_mdomain_fupd (K smd) z)
       = wl_state_sh_mdomain_fupd (K smd) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_permute_fupd (K p) z)
       = wl_state_permute_fupd (K p) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_compile_fupd (K c) z)
       = wl_state_compile_fupd (K c) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_compile_oracle_fupd (K co) z)
       = wl_state_compile_oracle_fupd (K co) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_code_buffer_fupd (K cb) z)
       = wl_state_code_buffer_fupd (K cb) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_data_buffer_fupd (K db) z)
       = wl_state_data_buffer_fupd (K db) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_gc_fun_fupd (K g) z)
       = wl_state_gc_fun_fupd (K g) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_handler_fupd (K hd) z)
       = wl_state_handler_fupd (K hd) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_clock_fupd (K clk) z)
       = wl_state_clock_fupd (K clk) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_termdep_fupd (K tdep) z)
       = wl_state_termdep_fupd (K tdep) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_code_fupd (K cd) z)
       = wl_state_code_fupd (K cd) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_be_fupd (K b) z) = wl_state_be_fupd (K b) (wl_set_fp_var x y z) /\
   wl_set_fp_var x y (wl_state_ffi_fupd (K ffi) z)
       = wl_state_ffi_fupd (K ffi) (wl_set_fp_var x y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_set_fp_var_with_const];;

(* HOL4: mem_load_with_const[simp]; line 781 *)
let wl_mem_load_with_const = prove
 (`wl_mem_load x (wl_state_locals_fupd (K l) (y:(A,C,FFI)wl_state)) = wl_mem_load x y /\
   wl_mem_load x (wl_state_termdep_fupd (K td) y) = wl_mem_load x y /\
   wl_mem_load x (wl_state_clock_fupd (K k) y) = wl_mem_load x y /\
   wl_mem_load x (wl_state_stack_fupd (K xs) y) = wl_mem_load x y /\
   wl_mem_load x (wl_state_permute_fupd (K perm) y) = wl_mem_load x y /\
   wl_mem_load x (wl_state_code_fupd (K c) y) = wl_mem_load x y /\
   wl_mem_load x (wl_state_compile_oracle_fupd (K co) y) = wl_mem_load x y /\
   wl_mem_load x (wl_state_compile_fupd (K cc) y) = wl_mem_load x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_mem_load_with_const];;

(* line 794 *)
let mem_store_const = prove
 (`wl_mem_store x y z = SOME (a:(A,C,FFI)wl_state) ==>
   (wl_state_locals a) = (wl_state_locals z) /\
   (wl_state_clock a) = (wl_state_clock z) /\
   (wl_state_be a) = (wl_state_be z) /\
   (wl_state_gc_fun a) = (wl_state_gc_fun z) /\
   (wl_state_mdomain a) = (wl_state_mdomain z) /\
   (wl_state_sh_mdomain a) = (wl_state_sh_mdomain z) /\
   (wl_state_ffi a) = (wl_state_ffi z) /\
   (wl_state_handler a) = (wl_state_handler z) /\
   (wl_state_code a) = (wl_state_code z) /\
   (wl_state_code_buffer a) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer a) = (wl_state_data_buffer z) /\
   (wl_state_compile a) = (wl_state_compile z) /\
   (wl_state_compile_oracle a) = (wl_state_compile_oracle z) /\
   (wl_state_stack a) = (wl_state_stack z) /\
   (wl_state_locals_size a) = (wl_state_locals_size z) /\
   (wl_state_stack_limit a) = (wl_state_stack_limit z) /\
   (wl_state_stack_max a) = (wl_state_stack_max z) /\
   (wl_state_stack_size a) = (wl_state_stack_size z)`,
  IL2AUX_SOME_TAC[wl_mem_store_def]);;

(* line 819 [simp] *)
let mem_store_with_const = prove
 (`wl_mem_store x z (wl_state_locals_fupd (K l) (y:(A,C,FFI)wl_state))
     = OPTION_MAP (\s. wl_state_locals_fupd (K l) s) (wl_mem_store x z y) /\
   wl_mem_store x z (wl_state_clock_fupd (K k) y)
       = OPTION_MAP (\s. wl_state_clock_fupd (K k) s) (wl_mem_store x z y) /\
   wl_mem_store x z (wl_state_code_fupd (K code) y)
       = OPTION_MAP (\s. wl_state_code_fupd (K code) s) (wl_mem_store x z y) /\
   wl_mem_store x z (wl_state_compile_fupd (K c) y)
       = OPTION_MAP (\s. wl_state_compile_fupd (K c) s) (wl_mem_store x z y) /\
   wl_mem_store x z (wl_state_compile_oracle_fupd (K co) y)
       = OPTION_MAP (\s. wl_state_compile_oracle_fupd (K co) s) (wl_mem_store x z y) /\
   wl_mem_store x z (wl_state_permute_fupd (K perm) y)
       = OPTION_MAP (\s. wl_state_permute_fupd (K perm) s) (wl_mem_store x z y) /\
   wl_mem_store x z (wl_state_stack_fupd (K xs) y)
       = OPTION_MAP (\s. wl_state_stack_fupd (K xs) s) (wl_mem_store x z y)`,
  IL2AUX_WITH_TAC[wl_mem_store_def]);;

let _ = cake_add_simps [mem_store_with_const];;

(* word_exp depends only on locals, store, memory and mdomain *)

let IL2AUX_word_exp_cong = prove
 (`!(s1:(A,C,FFI)wl_state) e (s2:(A,C,FFI)wl_state).
     wl_state_locals s1 = wl_state_locals s2 /\ wl_state_store s1 = wl_state_store s2 /\
     wl_state_memory s1 = wl_state_memory s2 /\ wl_state_mdomain s1 = wl_state_mdomain s2
     ==> wl_word_exp s1 e = wl_word_exp s2 e`,
  MATCH_MP_TAC wl_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_word_exp_def] THEN
  ASM_REWRITE_TAC[wl_get_var_def; wl_get_store_def; wl_mem_load_def] THENL
   [SUBGOAL_THEN `wl_word_exp (s:(A,C,FFI)wl_state) addr =
                  wl_word_exp (s2:(A,C,FFI)wl_state) addr` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REFL_TAC];
    SUBGOAL_THEN `MAP (wl_word_exp (s:(A,C,FFI)wl_state)) wexps =
                  MAP (wl_word_exp (s2:(A,C,FFI)wl_state)) wexps` SUBST1_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      REFL_TAC];
    SUBGOAL_THEN `wl_word_exp (s:(A,C,FFI)wl_state) wexp =
                  wl_word_exp (s2:(A,C,FFI)wl_state) wexp /\
                  wl_word_exp s wexp1 = wl_word_exp s2 wexp1`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[]; REFL_TAC]]);;

(* HOL4: word_exp_with_const[simp]; line 831 *)
let wl_word_exp_with_const = prove
 (`!(x:(A,C,FFI)wl_state) y.
   wl_word_exp (wl_state_clock_fupd (K k) x) y = wl_word_exp x y /\
   wl_word_exp (wl_state_stack_fupd (K xs) x) y = wl_word_exp x y /\
   wl_word_exp (wl_state_permute_fupd (K perm) x) y = wl_word_exp x y /\
   wl_word_exp (wl_state_termdep_fupd (K termdep) x) y = wl_word_exp x y /\
   wl_word_exp (wl_state_code_fupd (K c) x) y = wl_word_exp x y /\
   wl_word_exp (wl_state_compile_oracle_fupd (K co) x) y = wl_word_exp x y /\
   wl_word_exp (wl_state_compile_fupd (K cc) x) y = wl_word_exp x y`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC IL2AUX_word_exp_cong THEN
  SIMP[]);;

let _ = cake_add_simps [wl_word_exp_with_const];;

(* line 850 *)
let assign_const_full = prove
 (`wl_assign x y z = SOME (a:(A,C,FFI)wl_state) ==>
   (wl_state_code a) = (wl_state_code z) /\
   (wl_state_code_buffer a) = (wl_state_code_buffer z) /\
   (wl_state_data_buffer a) = (wl_state_data_buffer z) /\
   (wl_state_compile a) = (wl_state_compile z) /\
   (wl_state_compile_oracle a) = (wl_state_compile_oracle z) /\
   (wl_state_clock a) = (wl_state_clock z) /\
   (wl_state_ffi a) = (wl_state_ffi z) /\
   (wl_state_handler a) = (wl_state_handler z) /\
   (wl_state_stack a) = (wl_state_stack z) /\
   (wl_state_locals_size a) = (wl_state_locals_size z) /\
   (wl_state_stack_limit a) = (wl_state_stack_limit z) /\
   (wl_state_stack_max a) = (wl_state_stack_max z) /\
   (wl_state_stack_size a) = (wl_state_stack_size z)`,
  IL2AUX_SOME_TAC[wl_assign_def; wl_set_var_def]);;

(* line 869 *)
let assign_const = prove
 (`wl_assign x y z = SOME (a:(A,C,FFI)wl_state) ==>
   (wl_state_clock a) = (wl_state_clock z) /\
   (wl_state_ffi a) = (wl_state_ffi z)`,
  MESON_TAC[assign_const_full]);;

(* HOL4: assign_with_const[simp]; line 877 *)
let wl_assign_with_const = prove
 (`wl_assign x y (wl_state_clock_fupd (K k) (z:(A,C,FFI)wl_state))
     = OPTION_MAP (\s. wl_state_clock_fupd (K k) s) (wl_assign x y z) /\
   wl_assign x y (wl_state_code_fupd (K code) z)
       = OPTION_MAP (\s. wl_state_code_fupd (K code) s) (wl_assign x y z) /\
   wl_assign x y (wl_state_compile_fupd (K c) z)
       = OPTION_MAP (\s. wl_state_compile_fupd (K c) s) (wl_assign x y z) /\
   wl_assign x y (wl_state_compile_oracle_fupd (K co) z)
       = OPTION_MAP (\s. wl_state_compile_oracle_fupd (K co) s) (wl_assign x y z) /\
   wl_assign x y (wl_state_permute_fupd (K perm) z)
       = OPTION_MAP (\s. wl_state_permute_fupd (K perm) s) (wl_assign x y z) /\
   wl_assign x y (wl_state_stack_fupd (K xs) z)
       = OPTION_MAP (\s. wl_state_stack_fupd (K xs) s) (wl_assign x y z)`,
  IL2AUX_WITH_TAC[wl_assign_def]);;

let _ = cake_add_simps [wl_assign_with_const];;

(* HOL4: inst_with_const[simp]; line 888 *)
let wl_inst_with_const = prove
 (`wl_inst i (wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state))
     = OPTION_MAP (\s. wl_state_clock_fupd (K k) s) (wl_inst i s) /\
   wl_inst i (wl_state_code_fupd (K code) s)
       = OPTION_MAP (\s. wl_state_code_fupd (K code) s) (wl_inst i s) /\
   wl_inst i (wl_state_compile_fupd (K c) s)
       = OPTION_MAP (\s. wl_state_compile_fupd (K c) s) (wl_inst i s) /\
   wl_inst i (wl_state_compile_oracle_fupd (K co) s)
       = OPTION_MAP (\s. wl_state_compile_oracle_fupd (K co) s) (wl_inst i s) /\
   wl_inst i (wl_state_permute_fupd (K perm) s)
       = OPTION_MAP (\s. wl_state_permute_fupd (K perm) s) (wl_inst i s) /\
   wl_inst i (wl_state_stack_fupd (K xs) s)
       = OPTION_MAP (\s. wl_state_stack_fupd (K xs) s) (wl_inst i s)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN IL2AUX_INST_SPLIT_TAC THEN
  SIMP[wl_inst_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]) THEN REPEAT PAIRARG_TAC THEN
  SIMP[OPTION_MAP_DEF]);;

let _ = cake_add_simps [wl_inst_with_const];;

(* line 900 *)
let inst_const_full = prove
 (`wl_inst i (s:(A,C,FFI)wl_state) = SOME s' ==>
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_ffi s') = (wl_state_ffi s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack s') = (wl_state_stack s) /\
   (wl_state_locals_size s') = (wl_state_locals_size s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (wl_state_stack_size s') = (wl_state_stack_size s)`,
  IL2AUX_INST_SPLIT_TAC THEN SIMP[wl_inst_def] THEN
  REWRITE_TAC(wl_assign_def :: IL2AUX_state_defs) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[]);;

(* line 924 [local] *)
let inst_code_gc_fun_const = prove
 (`wl_inst i (s:(A,C,FFI)wl_state) = SOME t ==>
   (wl_state_code s) = (wl_state_code t) /\ (wl_state_gc_fun s) = (wl_state_gc_fun t) /\
       (wl_state_sh_mdomain s) = (wl_state_sh_mdomain t) /\
       (wl_state_mdomain s) = (wl_state_mdomain t) /\ (wl_state_be s) = (wl_state_be t)
   /\ (wl_state_compile s) = (wl_state_compile t) /\
       (wl_state_stack_size s) = (wl_state_stack_size t) /\
       (wl_state_stack_limit s) = (wl_state_stack_limit t)`,
  IL2AUX_INST_SPLIT_TAC THEN SIMP[wl_inst_def] THEN
  REWRITE_TAC(wl_assign_def :: IL2AUX_state_defs) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[]);;

(* HOL4: inst_const; line 935 *)
let wl_inst_const = prove
 (`wl_inst i (s:(A,C,FFI)wl_state) = SOME s' ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_ffi s') = (wl_state_ffi s)`,
  MESON_TAC[inst_const_full]);;

(* line 943 *)
let jump_exc_const = prove
 (`wl_jump_exc (s:(A,C,FFI)wl_state) = SOME (s',y) ==>
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_ffi s') = (wl_state_ffi s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (wl_state_stack_size s') = (wl_state_stack_size s)`,
  IL2AUX_SOME_TAC[wl_jump_exc_def]);;

(* HOL4: jump_exc_with_const[simp]; line 963 *)
(* the paired lambda of HOL4 is a match on the pair (pair_CASE)          *)
let wl_jump_exc_with_const = prove
 (CASE_TERM
  `wl_jump_exc (wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state)) =
     OPTION_MAP (\x. match x with (s,t) -> (wl_state_clock_fupd (K k) s, t))
       (wl_jump_exc s) /\
   wl_jump_exc (wl_state_permute_fupd (K perm) s) =
     OPTION_MAP (\x. match x with (s,t) -> (wl_state_permute_fupd (K perm) s, t))
       (wl_jump_exc s)`,
  IL2AUX_WITH_TAC[wl_jump_exc_def]);;

let _ = cake_add_simps [wl_jump_exc_with_const];;

(* HOL4: get_var_imm_with_const[simp]; line 970 *)
let wl_get_var_imm_with_const = prove
 (`wl_get_var_imm x (wl_state_clock_fupd (K k) (y:(A,C,FFI)wl_state)) = wl_get_var_imm x y /\
   wl_get_var_imm x (wl_state_code_fupd (K code) y) = wl_get_var_imm x y /\
   wl_get_var_imm x (wl_state_compile_fupd (K compile) y) = wl_get_var_imm x y /\
   wl_get_var_imm x (wl_state_compile_oracle_fupd (K compile_oracle) y) = wl_get_var_imm x y /\
   wl_get_var_imm x (wl_state_termdep_fupd (K td) y) = wl_get_var_imm x y /\
   wl_get_var_imm x (wl_state_stack_fupd (K xs) y) = wl_get_var_imm x y /\
   wl_get_var_imm x (wl_state_permute_fupd (K perm) y) = wl_get_var_imm x y`,
  STRUCT_CASES_TAC (ISPEC `x:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[wl_get_var_imm_def] THEN SIMP[wl_get_var_def]);;

let _ = cake_add_simps [wl_get_var_imm_with_const];;

(* HOL4: dec_clock_const[simp]; line 982 *)
let wl_dec_clock_const = prove
 (`(wl_state_locals (wl_dec_clock (s:(A,C,FFI)wl_state))) = (wl_state_locals s) /\
   (wl_state_locals_size (wl_dec_clock s)) = (wl_state_locals_size s) /\
   (wl_state_fp_regs (wl_dec_clock s)) = (wl_state_fp_regs s) /\
   (wl_state_store (wl_dec_clock s)) = (wl_state_store s) /\
   (wl_state_stack (wl_dec_clock s)) = (wl_state_stack s) /\
   (wl_state_stack_limit (wl_dec_clock s)) = (wl_state_stack_limit s) /\
   (wl_state_stack_max (wl_dec_clock s)) = (wl_state_stack_max s) /\
   (wl_state_stack_size (wl_dec_clock s)) = (wl_state_stack_size s) /\
   (wl_state_memory (wl_dec_clock s)) = (wl_state_memory s) /\
   (wl_state_mdomain (wl_dec_clock s)) = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain (wl_dec_clock s)) = (wl_state_sh_mdomain s) /\
   (wl_state_permute (wl_dec_clock s)) = (wl_state_permute s) /\
   (wl_state_compile (wl_dec_clock s)) = (wl_state_compile s) /\
   (wl_state_compile_oracle (wl_dec_clock s)) = (wl_state_compile_oracle s) /\
   (wl_state_code_buffer (wl_dec_clock s)) = (wl_state_code_buffer s) /\
   (wl_state_data_buffer (wl_dec_clock s)) = (wl_state_data_buffer s) /\
   (wl_state_gc_fun (wl_dec_clock s)) = (wl_state_gc_fun s) /\
   (wl_state_handler (wl_dec_clock s)) = (wl_state_handler s) /\
   (wl_state_termdep (wl_dec_clock s)) = (wl_state_termdep s) /\
   (wl_state_code (wl_dec_clock s)) = (wl_state_code s) /\
   ((wl_state_be (wl_dec_clock s)) <=> (wl_state_be s)) /\
   (wl_state_ffi (wl_dec_clock s)) = (wl_state_ffi s) /\
   (wl_state_clock (wl_dec_clock (wl_state_locals_fupd (K locs) s)))
       = (wl_state_clock (wl_dec_clock s)) /\
   (wl_state_clock (wl_dec_clock (wl_state_permute_fupd (K p) s)))
       = (wl_state_clock (wl_dec_clock s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC IL2AUX_state_defs THEN SIMP[]);;

let _ = cake_add_simps [wl_dec_clock_const];;

(* line 1011 *)
let sh_mem_set_var_const = prove
 (`sh_mem_set_var r v (s:(A,C,FFI)wl_state) = (x:((W)wl_result)option,s') ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_permute s') = (wl_state_permute s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (r = NONE ==> (wl_state_ffi s') = (wl_state_ffi s)) /\
   (r = SOME (FFI_final outcome) ==> (wl_state_ffi s') = (wl_state_ffi s)) /\
   (r = NONE ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (r = SOME (FFI_return f l) ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (r = NONE ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (r = SOME (FFI_return f l) ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (r = NONE ==> (wl_state_stack_size s') = (wl_state_stack_size s)) /\
   (r = SOME (FFI_return f l) ==> (wl_state_stack_size s') = (wl_state_stack_size s))`,
  STRUCT_CASES_TAC (ISPEC `r:((FFI)ffi_result)option` (cases "option")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ; option_DISTINCT; option_INJ;
              distinctness "ffi_result"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[wl_set_var_def; wl_flush_state_def]);;

(* line 1045 *)
let sh_mem_store_const = prove
 (`wl_sh_mem_store ad v (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s') ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_permute s') = (wl_state_permute s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (res = SOME wl_Error ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = NONE ==> (wl_state_stack_size s') = (wl_state_stack_size s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_size s') = (wl_state_stack_size s))`,
  REWRITE_TAC[wl_sh_mem_store_def] THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[wl_flush_state_def]);;

(* line 1074 *)
let sh_mem_store_byte_const = prove
 (`wl_sh_mem_store_byte ad v (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s') ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_permute s') = (wl_state_permute s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (res = SOME wl_Error ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = NONE ==> (wl_state_stack_size s') = (wl_state_stack_size s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_size s') = (wl_state_stack_size s))`,
  REWRITE_TAC[wl_sh_mem_store_byte_def] THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[wl_flush_state_def]);;

(* line 1103 *)
let sh_mem_store16_const = prove
 (`wl_sh_mem_store16 ad v (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s') ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_permute s') = (wl_state_permute s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (res = SOME wl_Error ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = NONE ==> (wl_state_stack_size s') = (wl_state_stack_size s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_size s') = (wl_state_stack_size s))`,
  REWRITE_TAC[wl_sh_mem_store16_def] THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[wl_flush_state_def]);;

(* line 1132 *)
let sh_mem_store32_const = prove
 (`wl_sh_mem_store32 ad v (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s') ==>
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_permute s') = (wl_state_permute s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s) /\
   (res = SOME wl_Error ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_locals_size s') = (wl_state_locals_size s)) /\
   (res = NONE ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_max s') = (wl_state_stack_max s)) /\
   (res = NONE ==> (wl_state_stack_size s') = (wl_state_stack_size s)) /\
   (res = SOME wl_Error ==> (wl_state_stack_size s') = (wl_state_stack_size s))`,
  REWRITE_TAC[wl_sh_mem_store32_def] THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[wl_flush_state_def]);;

(* line 1161 *)
let share_inst_const = prove
 (`share_inst op v c (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s') ==>
   (wl_state_be s') = (wl_state_be s) /\
   (wl_state_gc_fun s') = (wl_state_gc_fun s) /\
   (wl_state_mdomain s') = (wl_state_mdomain s) /\
   (wl_state_sh_mdomain s') = (wl_state_sh_mdomain s) /\
   (wl_state_code s') = (wl_state_code s) /\
   (wl_state_code_buffer s') = (wl_state_code_buffer s) /\
   (wl_state_data_buffer s') = (wl_state_data_buffer s) /\
   (wl_state_compile s') = (wl_state_compile s) /\
   (wl_state_compile_oracle s') = (wl_state_compile_oracle s) /\
   (wl_state_permute s') = (wl_state_permute s) /\
   (wl_state_clock s') = (wl_state_clock s) /\
   (wl_state_handler s') = (wl_state_handler s) /\
   (wl_state_stack_limit s') = (wl_state_stack_limit s) /\
   (wl_state_stack_max s') = (wl_state_stack_max s)`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def] THEN
  TRY (DISCH_THEN(MP_TAC o MATCH_MP sh_mem_set_var_const) THEN SIMP[] THEN NO_TAC) THEN
  EVERY_CASE_TAC THEN TRY (REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    SIMP[] THEN NO_TAC) THEN
  REWRITE_TAC[wl_sh_mem_store_def; wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[wl_flush_state_def]);;

(* line 1187 [simp] *)
let sh_mem_set_var_with_const = prove
 (`sh_mem_set_var res v (wl_state_permute_fupd (K p) (s:(A,C,FFI)wl_state)) =
   (I ## (\s. wl_state_permute_fupd (K p) s)) (sh_mem_set_var res v
       s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   sh_mem_set_var res v (wl_state_clock_fupd (K k) s) =
   (I ## (\s. wl_state_clock_fupd (K k) s)) (sh_mem_set_var res v
       s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  STRUCT_CASES_TAC (ISPEC `res:((FFI)ffi_result)option` (cases "option")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  IL2AUX_WITH_TAC[sh_mem_set_var_def; wl_set_var_def; wl_flush_state_def]);;

let _ = cake_add_simps [sh_mem_set_var_with_const];;

(* HOL4: sh_mem_load_with_const[simp]; line 1200 *)
let wl_sh_mem_load_with_const = prove
 (`wl_sh_mem_load a (wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state)) = wl_sh_mem_load a s /\
   wl_sh_mem_load a (wl_state_permute_fupd (K p) s) = wl_sh_mem_load a s /\
   wl_sh_mem_load a (wl_state_clock_fupd (K k) s) = wl_sh_mem_load a s /\
   wl_sh_mem_load a (wl_state_stack_fupd (K xs) s) = wl_sh_mem_load a s`,
  SIMP[wl_sh_mem_load_def]);;

let _ = cake_add_simps [wl_sh_mem_load_with_const];;

(* HOL4: sh_mem_load_byte_with_const[simp]; line 1209 *)
let wl_sh_mem_load_byte_with_const = prove
 (`wl_sh_mem_load_byte a (wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state))
     = wl_sh_mem_load_byte a s /\
   wl_sh_mem_load_byte a (wl_state_permute_fupd (K p) s) = wl_sh_mem_load_byte a s /\
   wl_sh_mem_load_byte a (wl_state_clock_fupd (K k) s) = wl_sh_mem_load_byte a s /\
   wl_sh_mem_load_byte a (wl_state_stack_fupd (K xs) s) = wl_sh_mem_load_byte a s`,
  SIMP[wl_sh_mem_load_byte_def]);;

let _ = cake_add_simps [wl_sh_mem_load_byte_with_const];;

(* HOL4: sh_mem_load16_with_const[simp]; line 1218 *)
let wl_sh_mem_load16_with_const = prove
 (`wl_sh_mem_load16 a (wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state)) = wl_sh_mem_load16 a s /\
   wl_sh_mem_load16 a (wl_state_permute_fupd (K p) s) = wl_sh_mem_load16 a s /\
   wl_sh_mem_load16 a (wl_state_clock_fupd (K k) s) = wl_sh_mem_load16 a s /\
   wl_sh_mem_load16 a (wl_state_stack_fupd (K xs) s) = wl_sh_mem_load16 a s`,
  SIMP[wl_sh_mem_load16_def]);;

let _ = cake_add_simps [wl_sh_mem_load16_with_const];;

(* HOL4: sh_mem_load32_with_const[simp]; line 1227 *)
let wl_sh_mem_load32_with_const = prove
 (`wl_sh_mem_load32 a (wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state)) = wl_sh_mem_load32 a s /\
   wl_sh_mem_load32 a (wl_state_permute_fupd (K p) s) = wl_sh_mem_load32 a s /\
   wl_sh_mem_load32 a (wl_state_clock_fupd (K k) s) = wl_sh_mem_load32 a s /\
   wl_sh_mem_load32 a (wl_state_stack_fupd (K xs) s) = wl_sh_mem_load32 a s`,
  SIMP[wl_sh_mem_load32_def]);;

let _ = cake_add_simps [wl_sh_mem_load32_with_const];;

(* HOL4: sh_mem_store_with_const[simp]; line 1236 *)
let wl_sh_mem_store_with_const = prove
 (`wl_sh_mem_store a w (wl_state_permute_fupd (K p) (s:(A,C,FFI)wl_state)) =
   (I ## (\s. wl_state_permute_fupd (K p) s)) (wl_sh_mem_store a w
       s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   wl_sh_mem_store a w (wl_state_clock_fupd (K k) s) =
   (I ## (\s. wl_state_clock_fupd (K k) s)) (wl_sh_mem_store a w
       s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  IL2AUX_WITH_TAC[wl_sh_mem_store_def; wl_flush_state_def]);;

let _ = cake_add_simps [wl_sh_mem_store_with_const];;

(* HOL4: sh_mem_store_byte_with_const[simp]; line 1245 *)
let wl_sh_mem_store_byte_with_const = prove
 (`wl_sh_mem_store_byte a w (wl_state_permute_fupd (K p) (s:(A,C,FFI)wl_state)) =
   (I ## (\s. wl_state_permute_fupd (K p) s)) (wl_sh_mem_store_byte a w
       s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   wl_sh_mem_store_byte a w (wl_state_clock_fupd (K k) s) =
   (I ## (\s. wl_state_clock_fupd (K k) s)) (wl_sh_mem_store_byte a w
       s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  IL2AUX_WITH_TAC[wl_sh_mem_store_byte_def; wl_flush_state_def]);;

let _ = cake_add_simps [wl_sh_mem_store_byte_with_const];;

(* HOL4: sh_mem_store16_with_const[simp]; line 1254 *)
let wl_sh_mem_store16_with_const = prove
 (`wl_sh_mem_store16 a w (wl_state_permute_fupd (K p) (s:(A,C,FFI)wl_state)) =
   (I ## (\s. wl_state_permute_fupd (K p) s)) (wl_sh_mem_store16 a w
       s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   wl_sh_mem_store16 a w (wl_state_clock_fupd (K k) s) =
   (I ## (\s. wl_state_clock_fupd (K k) s)) (wl_sh_mem_store16 a w
       s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  IL2AUX_WITH_TAC[wl_sh_mem_store16_def; wl_flush_state_def]);;

let _ = cake_add_simps [wl_sh_mem_store16_with_const];;

(* HOL4: sh_mem_store32_with_const[simp]; line 1263 *)
let wl_sh_mem_store32_with_const = prove
 (`wl_sh_mem_store32 a w (wl_state_permute_fupd (K p) (s:(A,C,FFI)wl_state)) =
   (I ## (\s. wl_state_permute_fupd (K p) s)) (wl_sh_mem_store32 a w
       s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   wl_sh_mem_store32 a w (wl_state_clock_fupd (K k) s) =
   (I ## (\s. wl_state_clock_fupd (K k) s)) (wl_sh_mem_store32 a w
       s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  IL2AUX_WITH_TAC[wl_sh_mem_store32_def; wl_flush_state_def]);;

let _ = cake_add_simps [wl_sh_mem_store32_with_const];;

(* line 1272 [simp] *)
let share_inst_with_const = prove
 (`share_inst op v c (wl_state_permute_fupd (K p) (s:(A,C,FFI)wl_state)) =
   (I ## (\s. wl_state_permute_fupd (K p) s)) (share_inst op v c
       s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   share_inst op v c (wl_state_clock_fupd (K k) s) =
   (I ## (\s. wl_state_clock_fupd (K k) s)) (share_inst op v c
       s:((W)wl_result)option#(A,C,FFI)wl_state)`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  IL2AUX_WITH_TAC[share_inst_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
                  wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_flush_state_def]);;

let _ = cake_add_simps [share_inst_with_const];;

(* line 1281 [simp] *)
let cut_state_with_const = prove
 (`wl_cut_state x (wl_state_clock_fupd (K k) (z:(A,C,FFI)wl_state))
     = OPTION_MAP (\s. wl_state_clock_fupd (K k) s) (wl_cut_state x z) /\
   wl_cut_state x (wl_state_code_fupd (K code) z)
       = OPTION_MAP (\s. wl_state_code_fupd (K code) s) (wl_cut_state x z) /\
   wl_cut_state x (wl_state_compile_fupd (K c) z)
       = OPTION_MAP (\s. wl_state_compile_fupd (K c) s) (wl_cut_state x z) /\
   wl_cut_state x (wl_state_compile_oracle_fupd (K co) z)
       = OPTION_MAP (\s. wl_state_compile_oracle_fupd (K co) s) (wl_cut_state x z) /\
   wl_cut_state x (wl_state_permute_fupd (K perm) z)
       = OPTION_MAP (\s. wl_state_permute_fupd (K perm) s) (wl_cut_state x z) /\
   wl_cut_state x (wl_state_stack_fupd (K xs) z)
       = OPTION_MAP (\s. wl_state_stack_fupd (K xs) s) (wl_cut_state x z)`,
  IL2AUX_WITH_TAC[wl_cut_state_def]);;

let _ = cake_add_simps [cut_state_with_const];;

(* line 1293 *)
let cut_state_const = prove
 (`wl_cut_state x (s:(A,C,FFI)wl_state) = SOME s' ==>
   ?l. s' = wl_state_locals_fupd (K l) s`,
  REWRITE_TAC[wl_cut_state_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN MESON_TAC[]);;



(* ------------------------------------------------------------------------- *)
(* The clock of the statements without recursive calls                      *)
(* ------------------------------------------------------------------------- *)

(* the induction goals of evaluate_ind for a predicate goal on (p,s), as     *)
(* HOL4 computes them (ISPEC and paired beta reduction), and those of the    *)
(* given statement constructors                                              *)

let IL2AUX_ind_goals (goal:term) =
  let th = ISPEC goal wl_evaluate_ind in
  let th = CONV_RULE (DEPTH_CONV GEN_BETA_CONV) th in
  conjuncts (lhand (concl th));;

let IL2AUX_select_goals (gls:term list) (cons:string list) =
  list_mk_conj (map (fun c ->
      find (fun g -> can (find_term (fun t -> is_const t &&
                                       fst(dest_const t) = c)) g) gls) cons);;

let IL2AUX_nonrec_cons =
  ["wl_Skip"; "wl_Alloc"; "wl_StoreConsts"; "wl_Move"; "wl_Inst"; "wl_Assign";
   "wl_Get"; "wl_Set"; "wl_OpCurrHeap"; "wl_Store"; "wl_Return"; "wl_Raise";
   "wl_Break"; "wl_Continue"; "wl_LocValue"; "wl_Install"; "wl_CodeBufferWrite";
   "wl_DataBufferWrite"; "wl_FFI"; "ShareInst"];;

(* IL2AUX_clock_case_eqs (wordSem.ml): the cases of the evaluate result *)

(* HOL4 [local] *)

let evaluate_clock_const = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !r s'. wl_evaluate (p, s) = (r, s') ==> wl_state_clock s' = wl_state_clock s`)
    IL2AUX_nonrec_cons,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY (fun th -> REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL o MATCH_MP th)))
    [wl_alloc_const; wl_inst_const; mem_store_const; jump_exc_const; share_inst_const;
     IL2AUX_cut_state_clock_termdep] THEN
  FS[wl_flush_state_def; wl_unset_var_def; wl_set_var_def; wl_set_vars_def;
     wl_set_store_def]);;

(* split the free variables of product type of the goal *)

let IL2AUX_SPLIT_PAIR_VARS_TAC : tactic = fun (asl,w as g) ->
  let pvs = filter (fun v -> match type_of v with Tyapp("prod",_) -> true | _ -> false)
                   (frees w) in
  if pvs = [] then failwith "IL2AUX_SPLIT_PAIR_VARS_TAC" else
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v PAIR_SURJECTIVE)) pvs g;;

(* HOL4 [local]; HOL4's (\(r,s). (r,s with clock := k)) (evaluate (p,s)) is   *)
(* the pair_CASE of the evaluation here                                       *)

let evaluate_clock_with_const = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !k. wl_evaluate (p, wl_state_clock_fupd (K k) s) =
              pair_CASE (wl_evaluate (p,s)) (\r s. (r, wl_state_clock_fupd (K k) s))`)
    IL2AUX_nonrec_cons,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  FIRST
   [REPEAT ((TOP_CASE_TAC ORELSE PAIRARG_TAC) THEN SIMP[PAIR_MAP_THM; I_THM]) THEN
    SIMP[PAIR_MAP_THM; I_THM] THEN NO_TAC;
    CASES_ON `wl_get_var n (s:(A,C,FFI)wl_state)` THEN SIMP[] THEN
    CASES_ON `wl_jump_exc (s:(A,C,FFI)wl_state)` THEN SIMP[] THEN
    REPEAT IL2AUX_SPLIT_PAIR_VARS_TAC THEN SIMP[]]);;

(* ******CONST LEMMAS END ***** *)

(* TODO complete for all get set variaents *)

let get_var_set_store = prove
 (`wl_get_var v1 (wl_set_store v2 x (s:(A,C,FFI)wl_state)) = wl_get_var v1 s`,
  SIMP[wl_set_store_def; wl_get_var_def]);;

let _ = cake_add_simps [get_var_set_store];;

let get_var_set_fp_var = prove
 (`wl_get_var v1 (wl_set_fp_var v2 x (s:(A,C,FFI)wl_state)) = wl_get_var v1 s`,
  SIMP[wl_set_fp_var_def; wl_get_var_def]);;

let _ = cake_add_simps [get_var_set_fp_var];;

(* HOL4: get_var_set_var *)

let wl_get_var_set_var = prove
 (`wl_get_var v1 (wl_set_var v2 x (s:(A,C,FFI)wl_state)) =
   if v1 = v2 then SOME x else wl_get_var v1 s`,
  SIMP[wl_get_var_def; wl_set_var_def; lookup_insert]);;

let get_store_set_store = prove
 (`wl_get_store v1 (wl_set_store v2 x (s:(A,C,FFI)wl_state)) =
   if v1 = v2 then SOME x else wl_get_store v1 s`,
  SIMP[wl_get_store_def; wl_set_store_def; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

let get_fp_var_set_fp_var = prove
 (`wl_get_fp_var v1 (wl_set_fp_var v2 x (s:(A,C,FFI)wl_state)) =
   if v1 = v2 then SOME x else wl_get_fp_var v1 s`,
  SIMP[wl_get_fp_var_def; wl_set_fp_var_def; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The clock lemmas                                                           *)
(* ------------------------------------------------------------------------- *)

(* induction on the pair (p,s) of a goal !p s. Q p s with evaluate_ind *)

let IL2AUX_EVAL_IND_TAC (ind:thm) : tactic = fun (asl,w as g) ->
  let p,b = dest_forall w in
  let s,body = dest_forall b in
  let x = mk_var("x", mk_type("prod",[type_of p; type_of s])) in
  let body' = subst [mk_icomb(mk_const("FST",[]),x), p;
                     mk_icomb(mk_const("SND",[]),x), s] body in
  let w' = mk_forall(x, body') in
  (SUBGOAL_THEN w' MP_TAC THENL
    [MATCH_MP_TAC ind THEN REWRITE_TAC[FST; SND];
     REWRITE_TAC[FORALL_PAIR_THM; FST; SND]]) g;;

(* IL2AUX_EXISTS_ASM_TAC and IL2AUX_USE_IHS_TAC of wordSem.ml, with extra    *)
(* rewrites for the side conditions                                          *)

let IL2AUX_EXISTS_ASM_RW_TAC (rws:thm list) : tactic = fun (asl,w as g) ->
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
  (MAP_EVERY EXISTS_TAC wits THEN ASM_REWRITE_TAC rws) g;;

let IL2AUX_USE_IHS_RW_TAC (rws:thm list) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> IL2AUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists IL2AUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let inst_of ih0 e =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = GENL vs1 (SPECL vs1 ih0) in
    let vs,bod = strip_forall (concl ih) in
    let ant,_ = dest_imp bod in
    let cjs = filter IL2AUX_is_eval_eq (conjuncts ant) in
    tryfind (fun cj ->
      let (_,tmi,tyi) = term_match [] cj (concl e) in
      if exists (fun (a,b) -> not (a = b)) tyi ||
         exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi then failwith "" else
      let ihi = INST tmi (SPEC_ALL ih) in
      let a,c = dest_imp (concl ihi) in
      let rest = filter (fun v -> mem v vs) (subtract (frees a) (frees c)) in
      if exists (fun v -> mem v vs) (frees c) then failwith "" else
      c, GENL rest ihi) cjs in
  let insts = flat (map (fun e -> mapfilter (fun ih -> inst_of ih e) ihs) evs) in
  MAP_EVERY (fun (c,th) ->
      TRY (SUBGOAL_THEN c STRIP_ASSUME_TAC THENL
            [MATCH_MP_TAC th THEN IL2AUX_EXISTS_ASM_RW_TAC rws THEN NO_TAC; ALL_TAC]))
    insts g;;

let IL2AUX_bad_fun_return_TO = prove
 (`!r. wl_bad_fun_return r ==> ~(r = SOME (wl_TimeOut:(W)wl_result))`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((W)wl_result)option` (cases "option")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(W)wl_result` (cases "wl_result"))) THEN
  SIMP[]);;

let IL2AUX_res_rws =
  [option_DISTINCT; option_INJ; distinctness "wl_result"; injectivity "wl_result"];;

(* the facts of the assumptions bad_fun_return r and pop_env s = SOME s' *)

let IL2AUX_BFR_TAC : tactic =
  ASSUM_LIST (fun ths -> MAP_EVERY (ASSUME_TAC o MATCH_MP IL2AUX_bad_fun_return_TO)
    (filter (fun th -> try fst(dest_const(rator(concl th))) = "wl_bad_fun_return"
                       with Failure _ -> false) ths));;

let IL2AUX_POP_CONST_TAC : tactic =
  ASSUM_LIST (fun ths -> MAP_EVERY (STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const)
    (filter (can (MATCH_MP wl_pop_env_const)) ths));;

let IL2AUX_ADD_SUB1 = prove
 (`!n e. ~(n = 0) ==> (n + e) - 1 = (n - 1) + e`,
  ARITH_TAC);;

(* the cases of evaluate_add_clock *)

let IL2AUX_NONREC_CLOCK_TAC : tactic =
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_clock_with_const; pair_CASE] THEN
  MAP_FIRST (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th))
            (CONJUNCTS evaluate_clock_const) THEN
  SIMP_TAC[];;

let IL2AUX_ADD_CLOCK_TICK_TAC : tactic =
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_CASES_TAC `wl_state_clock (s:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[ADD_EQ_0; wl_dec_clock_def; wl_state_component_equality] THEN ASM_ARITH_TAC;;

let IL2AUX_ADD_CLOCK_MT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_CASES_TAC `wl_state_termdep (s:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT PAIRARG_TAC THEN SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[];;

let IL2AUX_ADD_CLOCK_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_evaluate (c1:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`NONE:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[pair_CASE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:((A)wl_result)option`; `s':(A,C,FFI)wl_state`] o
                  check (fun th -> is_forall (concl th) &&
                         can (find_term (fun t -> t = `c1:(A)wl_prog`)) (concl th) &&
                         not (can (find_term (fun t -> t = `c2:(A)wl_prog`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[pair_CASE]];;

let IL2AUX_ADD_CLOCK_IF_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; COND_CASE_EQ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  ASM_MESON_TAC[];;
let IL2AUX_ADD_CLOCK_LOOP_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN
  SIMP[OPTION_MAP_DEF; cut_state_with_const] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_clock_termdep o
     check (fun th -> is_eq (concl th) && is_comb (rhs (concl th)))) THEN
  MP_TAC(ISPEC `wl_evaluate (c:(A)wl_prog,a:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(res = SOME (wl_TimeOut:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] o
    REWRITE_RULE[] o SPEC `a:(A,C,FFI)wl_state` o
    check (fun th -> is_forall (concl th) &&
             not (can (find_term (fun t -> t = `wl_cont_loop:((A)wl_result)option->bool`))
                      (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `wl_cont_loop (res:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SIMP[ADD_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:(A,C,FFI)wl_state`; `res:((A)wl_result)option`;
                                    `s1:(A,C,FFI)wl_state`] o
                    check (fun th -> can (find_term (fun t ->
                             t = `wl_cont_loop:((A)wl_result)option->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`r:((A)wl_result)option`; `s':(A,C,FFI)wl_state`]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `wl_dec_clock (wl_state_clock_fupd (K (wl_state_clock s1 + extra))
                        (s1:(A,C,FFI)wl_state)) =
        wl_state_clock_fupd (K (wl_state_clock (wl_dec_clock s1) + extra))
          (wl_dec_clock s1)` SUBST1_TAC THENL
       [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
        REWRITE_TAC[]]];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[cut_state_with_const] THENL
     [CASES_ON `wl_cut_state (exit_names,LN) (s1:(A,C,FFI)wl_state)` THEN
      REWRITE_TAC[OPTION_MAP_DEF; option_CASE; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      REWRITE_TAC[] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_clock_termdep) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]]];;

let IL2AUX_ADD_CLOCK_CALL_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN IL2AUX_BFR_TAC THEN IL2AUX_POP_CONST_TAC THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN
  (* the induction hypotheses have been used (instantiated) by now: dropping *)
  (* them makes the SIMP and FS steps below much faster                      *)
  REPEAT (FIRST_X_ASSUM (fun th -> if is_forall (concl th) then ALL_TAC
                                   else failwith "")) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[IL2AUX_ADD_SUB1; ADD_EQ_0; wl_dec_clock_def] THEN
  FS[IL2AUX_ADD_SUB1; wl_dec_clock_def];;

(* Standard add clock lemma for FBS *)

let wl_evaluate_add_clock = prove
 (`!p (s:(A,C,FFI)wl_state) r s'.
     wl_evaluate (p,s) = (r,s') /\ ~(r = SOME wl_TimeOut)
     ==> wl_evaluate (p, wl_state_clock_fupd (K (wl_state_clock s + extra)) s) =
         (r, wl_state_clock_fupd (K (wl_state_clock s' + extra)) s')`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate IL2AUX_NONREC_CLOCK_TAC 10 @
    [IL2AUX_ADD_CLOCK_TICK_TAC; IL2AUX_ADD_CLOCK_MT_TAC; IL2AUX_ADD_CLOCK_SEQ_TAC] @
    replicate IL2AUX_NONREC_CLOCK_TAC 4 @
    [IL2AUX_ADD_CLOCK_IF_TAC; IL2AUX_ADD_CLOCK_LOOP_TAC] @
    replicate IL2AUX_NONREC_CLOCK_TAC 6 @
    [IL2AUX_ADD_CLOCK_CALL_TAC]));;


(* This lemma is interesting in wordLang because of the use of              *)
(* MustTerminate.  To remove MustTerminate, we need to inject an exact      *)
(* number of clock ticks corresponding to the ticks used in the             *)
(* MustTerminate block.  The number of clock ticks is fixed for any         *)
(* program, and can be characterized by st.clock - rst.clock                *)

let with_locals_same_clock = prove
 (`wl_state_locals_fupd (K l)
     (wl_state_clock_fupd (K (wl_state_clock (s:(A,C,FFI)wl_state))) s) =
   wl_state_locals_fupd (K l) s`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let _ = cake_add_simps [with_locals_same_clock];;

(* HOL4 [local] *)

let cont_loop_not_timeout = prove
 (`wl_cont_loop res ==> ~(res = SOME (wl_TimeOut:(W)wl_result))`,
  STRUCT_CASES_TAC (ISPEC `res:((W)wl_result)option` (cases "option")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(W)wl_result` (cases "wl_result"))) THEN SIMP[]);;

(* HOL4 [local] *)

let evaluate_add_clock_body = prove
 (`wl_evaluate (c,s:(A,C,FFI)wl_state) = (res,s') /\ wl_cont_loop res ==>
   !extra.
     wl_evaluate (c, wl_state_clock_fupd (K (wl_state_clock s + extra)) s) =
     (res, wl_state_clock_fupd (K (wl_state_clock s' + extra)) s')`,
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP cont_loop_not_timeout) THEN
  GEN_TAC THEN MATCH_MP_TAC wl_evaluate_add_clock THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_dec_clock.  The proof is by the evaluate induction; the         *)
(* recursive cases use the tactics below: the clock that a call of          *)
(* evaluate consumes, st.clock - rst.clock, is shifted to a larger start    *)
(* clock with evaluate_add_clock (IL2AUX_add_clock_shift, IL2AUX_SHIFT_TAC). *)
(* ------------------------------------------------------------------------- *)

let IL2AUX_NONREC_DEC_TAC : tactic =
  REPEAT STRIP_TAC THEN
  MAP_FIRST (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
    (CONJUNCTS evaluate_clock_const) THEN
  ASM_REWRITE_TAC[SUB_REFL; evaluate_clock_with_const; pair_CASE];;

let IL2AUX_DEC_CLOCK_TICK_TAC : tactic =
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_CASES_TAC `wl_state_clock (s:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[wl_dec_clock_def; wl_flush_state_def] THEN
  SUBGOAL_THEN `wl_state_clock (s:(A,C,FFI)wl_state) - (wl_state_clock s - 1) = 1`
    SUBST1_TAC THENL
   [ASM_ARITH_TAC; SIMP[]];;

let IL2AUX_DEC_CLOCK_MT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_CASES_TAC `wl_state_termdep (s:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[SUB_REFL]; ALL_TAC] THEN
  REPEAT PAIRARG_TAC THEN SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[SUB_REFL];;

let IL2AUX_add_clock_shift = prove
 (`!p (s:(A,C,FFI)wl_state) r s' a c.
     wl_evaluate (p, wl_state_clock_fupd (K a) s) =
       (r, wl_state_clock_fupd (K 0) s') /\
     ~(r = SOME wl_TimeOut) /\ a <= c
     ==> wl_evaluate (p, wl_state_clock_fupd (K c) s) =
         (r, wl_state_clock_fupd (K (c - a)) s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    MATCH_MP (INST [`c - a:num`,`extra:num`] wl_evaluate_add_clock) o
    REWRITE_RULE[GSYM CONJ_ASSOC] o
    C CONJ (ASSUME `~(r = SOME (wl_TimeOut:(A)wl_result))`)) THEN
  SIMP[ADD_CLAUSES] THEN
  SUBGOAL_THEN `a + c - a = c:num` SUBST1_TAC THENL [ASM_ARITH_TAC; SIMP[]]);;

(* t = wl_state_clock_fupd (K a) s  gives  (a,s) *)

let IL2AUX_dest_clock_upd t =
  let f,args = strip_comb t in
  if fst(dest_const f) = "wl_state_clock_fupd" && length args = 2 then
    let k = hd args in
    if fst(dest_const(rator k)) = "K" then rand k, el 1 args else failwith ""
  else failwith "";;

(* for an assumption evaluate (p, s with clock := a) = (r, y with clock := 0) *)
(* and a goal term evaluate (p, s with clock := c): add the assumption       *)
(* evaluate (p, s with clock := c) = (r, y with clock := c - a), when the    *)
(* arithmetic facts give a <= c                                              *)

let IL2AUX_SHIFT_TAC : tactic = fun (asl,w as g) ->
  let evs = mapfilter (fun (_,th) ->
      let c = concl th in
      if not (IL2AUX_is_eval_eq c) then failwith "" else
      let p,st = dest_pair (rand (lhs c)) in
      let a,s = IL2AUX_dest_clock_upd st in
      let r,st' = dest_pair (rhs c) in
      let z,y = IL2AUX_dest_clock_upd st' in
      if not (z = `0`) then failwith "" else (p,a,s,r,st')) asl in
  let targets = setify (find_terms (fun t ->
      try fst(dest_const(rator t)) = "wl_evaluate" &&
          let _,st = dest_pair (rand t) in can IL2AUX_dest_clock_upd st
      with Failure _ -> false) w) in
  let todo = flat (map (fun t ->
      let p,st = dest_pair (rand t) in
      let c,s = IL2AUX_dest_clock_upd st in
      mapfilter (fun (p',a,s',r,st') ->
          if p' = p && s' = s && not (a = c) then (t,a,c,r,st') else failwith "") evs)
      targets) in
  MAP_EVERY (fun (t,a,c,r,st') ->
      let fupd = rator(rator st') and k0 = rand(rator st') and y = rand st' in
      let st2 = mk_comb(mk_comb(fupd, mk_comb(rator k0,
                  mk_binop `(-):num->num->num` c a)), y) in
      TRY (SUBGOAL_THEN (mk_eq(t, mk_pair(r, st2))) ASSUME_TAC THENL
            [MATCH_MP_TAC IL2AUX_add_clock_shift THEN
             ASM_REWRITE_TAC IL2AUX_res_rws THEN
             REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_num_fact o concl))) THEN
             ARITH_TAC; ALL_TAC])) todo g;;

(* the clock facts of wl_evaluate_clock for the evaluate assumptions *)

let IL2AUX_CLOCK_FACTS_TAC : tactic =
  ASSUM_LIST (fun ths -> MAP_EVERY (STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_clock)
     (filter (can (MATCH_MP wl_evaluate_clock)) ths));;

(* replace a goal clock c by the clock a of an evaluate assumption on the  *)
(* same program and state, when the arithmetic facts give c = a            *)

let IL2AUX_CLOCK_MATCH_TAC : tactic = fun (asl,w as g) ->
  let evs = mapfilter (fun (_,th) ->
      let c = concl th in
      if not (IL2AUX_is_eval_eq c) then failwith "" else
      let p,st = dest_pair (rand (lhs c)) in
      let a,s = IL2AUX_dest_clock_upd st in (p,a,s)) asl in
  let targets = setify (find_terms (fun t ->
      try fst(dest_const(rator t)) = "wl_evaluate" &&
          let _,st = dest_pair (rand t) in can IL2AUX_dest_clock_upd st
      with Failure _ -> false) w) in
  let eqs = flat (map (fun t ->
      let p,st = dest_pair (rand t) in
      let c,s = IL2AUX_dest_clock_upd st in
      mapfilter (fun (p',a,s') ->
          if p' = p && s' = s && not (a = c) then mk_eq(c,a) else failwith "") evs)
      targets) in
  MAP_EVERY (fun e ->
      TRY (SUBGOAL_THEN e SUBST1_TAC THENL
            [REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_num_fact o concl))) THEN
             ARITH_TAC; ALL_TAC])) eqs g;;

let IL2AUX_CUT_CONST_TAC : tactic =
  ASSUM_LIST (fun ths ->
    MAP_EVERY (STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_clock_termdep)
      (filter (can (MATCH_MP IL2AUX_cut_state_clock_termdep)) ths));;

let IL2AUX_CONT_TAC : tactic =
  ASSUM_LIST (fun ths -> MAP_EVERY (ASSUME_TAC o MATCH_MP cont_loop_not_timeout)
    (filter (can (MATCH_MP cont_loop_not_timeout)) ths));;

(* decide the numeric conditions of the goal by the arithmetic facts *)

let IL2AUX_ARITH_COND_TAC : tactic = fun (asl,w as g) ->
  let conds = setify (map (fun t -> fst(dest_cond t))
                 (find_terms (fun t -> is_cond t &&
                                       IL2AUX_is_num_fact (fst(dest_cond t))) w)) in
  let arith = REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_num_fact o concl))) THEN
              ARITH_TAC in
  MAP_EVERY (fun c ->
     FIRST [SUBGOAL_THEN (mk_neg c) (fun th -> REWRITE_TAC[th]) THENL [arith; ALL_TAC];
            SUBGOAL_THEN c (fun th -> REWRITE_TAC[th]) THENL [arith; ALL_TAC];
            ALL_TAC]) conds g;;

let IL2AUX_NUM_ARITH_TAC : tactic =
  TRY (REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_num_fact o concl))) THEN
       ARITH_TAC);;

let IL2AUX_dec_rws =
  [wl_dec_clock_def; wl_STOP_def; wl_state_INFO.ri_accfupds;
   wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM; wl_call_env_const;
   wl_call_env_with_const; wl_push_env_const; wl_push_env_with_const;
   wl_set_var_const; wl_set_var_with_const; wl_set_vars_const;
   wl_set_vars_with_const; flush_state_const];;

(* the branches that end before any recursive call (the simplifier is    *)
(* slow on them)                                                           *)

let IL2AUX_DEC_QUICK_TAC : tactic =
  ASM_REWRITE_TAC[wl_get_vars_with_const; SUB_REFL; option_CASE; pair_CASE;
                  wl_state_INFO.ri_accfupds; K_THM; wl_state_INFO.ri_fupdfupds;
                  K_o_THM] THEN NO_TAC;;

(* the recursive cases Seq, If, Loop and Call *)

let IL2AUX_DEC_GEN_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_BFR_TAC THEN IL2AUX_CONT_TAC THEN IL2AUX_POP_CONST_TAC THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN
  (* the induction hypotheses have been used (instantiated) by now: dropping *)
  (* them makes the rewriting, SIMP and FS steps below much faster           *)
  REPEAT (FIRST_X_ASSUM (fun th -> if is_forall (concl th) then ALL_TAC
                                   else failwith "")) THEN
  IL2AUX_CLOCK_FACTS_TAC THEN
  IL2AUX_CUT_CONST_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_dec_rws) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  FIRST
   [IL2AUX_DEC_QUICK_TAC;
    SIMP[wl_dec_clock_def; wl_STOP_def; cut_state_with_const; OPTION_MAP_DEF] THEN
    IL2AUX_SHIFT_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
    SIMP[wl_dec_clock_def] THEN IL2AUX_ARITH_COND_TAC THEN IL2AUX_CLOCK_MATCH_TAC THEN
    ASM_REWRITE_TAC[] THEN FS[SUB_REFL; wl_dec_clock_def] THEN IL2AUX_NUM_ARITH_TAC];;

let evaluate_dec_clock = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst.
     wl_evaluate (prog,st) = (res,rst)
     ==> wl_evaluate (prog, wl_state_clock_fupd
                              (K (wl_state_clock st - wl_state_clock rst)) st) =
         (res, wl_state_clock_fupd (K 0) rst)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate IL2AUX_NONREC_DEC_TAC 10 @
    [IL2AUX_DEC_CLOCK_TICK_TAC; IL2AUX_DEC_CLOCK_MT_TAC; IL2AUX_DEC_GEN_TAC] @
    replicate IL2AUX_NONREC_DEC_TAC 4 @
    [IL2AUX_DEC_GEN_TAC; IL2AUX_DEC_GEN_TAC] @
    replicate IL2AUX_NONREC_DEC_TAC 6 @
    [IL2AUX_DEC_GEN_TAC]));;

(* ------------------------------------------------------------------------- *)
(* evaluate_io_events_mono                                                   *)
(* ------------------------------------------------------------------------- *)

(* the io_events of call_FFI and of share_inst only grow *)

let IL2AUX_CALL_FFI_CASES_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try let f,args = strip_comb t in
                              fst(dest_const f) = "call_FFI" && length args = 4
                              with Failure _ -> false) w in
  CASES_ON t g;;

let IL2AUX_share_inst_io_events = prove
 (`share_inst op v c (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s')
   ==> ffi_state_io_events (wl_state_ffi s) <<= ffi_state_io_events (wl_state_ffi s')`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
              wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
              wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC ORELSE IL2AUX_CALL_FFI_CASES_TAC) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[IS_PREFIX_REFL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SEM2AUX_call_FFI_io_events) THEN SIMP[]);;

(* the facts of the lemmas lems for the assumptions they match *)

let IL2AUX_FACTS_TAC (lems:thm list) : tactic =
  ASSUM_LIST (fun ths ->
    EVERY (flat (map (fun th ->
      mapfilter (fun lem -> STRIP_ASSUME_TAC (MATCH_MP lem th)) lems) ths)));;

let IL2AUX_DROP_IHS_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_forall (concl th) then ALL_TAC else failwith ""));;

let IL2AUX_is_prefix tm =
  try fst(dest_const(fst(strip_comb tm))) = "isPREFIX" with Failure _ -> false;;

let IL2AUX_io_facts =
  [wl_alloc_const; wl_inst_const; mem_store_const; jump_exc_const; assign_const;
   gc_const; IL2AUX_share_inst_io_events; SEM2AUX_call_FFI_io_events;
   cut_state_const];;

(* an IH whose conclusion is the goal (the instance would close the goal   *)
(* inside IL2AUX_USE_IHS_RW_TAC)                                            *)

let IL2AUX_IH_GOAL_TAC (rws:thm list) : tactic =
  FIRST_ASSUM (fun ih ->
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] ih) THEN
    IL2AUX_EXISTS_ASM_RW_TAC rws THEN NO_TAC);;

let IL2AUX_IO_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY (IL2AUX_IH_GOAL_TAC IL2AUX_res_rws) THEN
  IL2AUX_POP_CONST_TAC THEN IL2AUX_FACTS_TAC IL2AUX_io_facts THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN IL2AUX_DROP_IHS_TAC THEN
  FS[IS_PREFIX_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_prefix o concl))) THEN
  MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_REFL];;

(* HOL4: evaluate_io_events_mono; line 1585 *)
let wl_evaluate_io_events_mono = prove
 (`!exps (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (exps,s1) = (res,s2)
     ==> ffi_state_io_events (wl_state_ffi s1) <<=
         ffi_state_io_events (wl_state_ffi s2)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN IL2AUX_IO_TAC);;

(* ------------------------------------------------------------------------- *)
(* evaluate_add_clock_io_events_mono                                         *)
(* ------------------------------------------------------------------------- *)

(* HOL4: SND_alt_def [local]; line 1631 (the paired lambda is a match)       *)
let SND_alt_def = prove
 (CASE_TERM `!c:A#B. SND c = (\x. match x with (a,b) -> b) c`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[]);;

(* The proof is by the evaluate induction on the run from s, for a fixed    *)
(* extra (IL2AUX_acio_lemma): a sub-run that does not time out is shifted   *)
(* by evaluate_add_clock; after a sub-run that times out, the run with more *)
(* clock only adds io_events (evaluate_io_events_mono).                     *)

let IL2AUX_add_clock_extra = prove
 (`!p (s:(A,C,FFI)wl_state) r s'.
     wl_evaluate (p,s) = (r,s') /\ ~(r = SOME wl_TimeOut)
     ==> wl_evaluate (p, wl_state_clock_fupd (K (wl_state_clock s + extra)) s) =
         (r, wl_state_clock_fupd (K (wl_state_clock s' + extra)) s')`,
  REWRITE_TAC[wl_evaluate_add_clock]);;

(* the facts of IL2AUX_add_clock_extra for the evaluate assumptions *)

let IL2AUX_ADDC_FACTS_TAC : tactic =
  ASSUM_LIST (fun ths -> EVERY (mapfilter (fun th ->
     let c = concl th in
     if not (IL2AUX_is_eval_eq c) then failwith "" else
     let q,t = dest_pair (rand (lhs c)) and r,t' = dest_pair (rhs c) in
     let lem = ISPECL [q;t;r;t'] IL2AUX_add_clock_extra in
     let b = rand (concl lem) in
     TRY (SUBGOAL_THEN b ASSUME_TAC THENL
           [MATCH_MP_TAC lem THEN ASM_REWRITE_TAC IL2AUX_res_rws THEN NO_TAC;
            ALL_TAC])) ths));;

(* name the results of the evaluate terms of the goal *)

let IL2AUX_SPLIT_EVALS_TAC : tactic = fun (asl,w as g) ->
  let evs = setify (find_terms (fun t ->
      try fst(dest_const(rator t)) = "wl_evaluate" with Failure _ -> false) w) in
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC (ISPEC t PAIR_SURJECTIVE)) evs g;;

(* substitute the assumptions t = v and v = t, v a variable not free in t *)

let IL2AUX_SUBST_VARS_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let l,r = dest_eq (concl th) in
    if is_var r && not (free_in r l) then SUBST_ALL_TAC (SYM th)
    else if is_var l && not (free_in l r) then SUBST_ALL_TAC th
    else failwith ""));;

(* rewrite the prefix facts with the evaluate assumptions *)

let IL2AUX_PREFIX_NORM_TAC : tactic =
  ASSUM_LIST (fun ths ->
    let evs = filter (IL2AUX_is_eval_eq o concl) ths in
    RULE_ASSUM_TAC (fun th ->
      if IL2AUX_is_prefix (concl th) then REWRITE_RULE (evs @ [SND; FST]) th
      else th));;

(* (n + e) - 1 = (n - 1) + e for the assumptions ~(n = 0) *)

let IL2AUX_SUB1_NORM_TAC : tactic =
  ASSUM_LIST (fun ths ->
    let rws = mapfilter (MATCH_MP IL2AUX_ADD_SUB1) ths in
    if rws = [] then ALL_TAC
    else RULE_ASSUM_TAC (REWRITE_RULE rws) THEN REWRITE_TAC rws);;

let IL2AUX_ACIO_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_BFR_TAC THEN IL2AUX_CONT_TAC THEN IL2AUX_POP_CONST_TAC THEN
  IL2AUX_FACTS_TAC IL2AUX_io_facts THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN IL2AUX_DROP_IHS_TAC THEN
  IL2AUX_ADDC_FACTS_TAC THEN IL2AUX_FACTS_TAC [wl_evaluate_io_events_mono] THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_dec_rws) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[wl_dec_clock_def; wl_STOP_def; cut_state_with_const; OPTION_MAP_DEF;
       IL2AUX_ADD_SUB1; ADD_EQ_0] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN TRY(IL2AUX_FACTS_TAC [wl_evaluate_io_events_mono])) THEN
  IL2AUX_POP_CONST_TAC THEN IL2AUX_FACTS_TAC IL2AUX_io_facts THEN IL2AUX_SUB1_NORM_TAC THEN
    IL2AUX_SPLIT_EVALS_TAC THEN IL2AUX_FACTS_TAC [wl_evaluate_io_events_mono] THEN
  FS[IS_PREFIX_REFL; wl_dec_clock_def] THEN IL2AUX_SUBST_VARS_TAC THEN
  FS[IS_PREFIX_REFL] THEN IL2AUX_SUB1_NORM_TAC THEN IL2AUX_PREFIX_NORM_TAC THEN
  FS[IS_PREFIX_REFL] THEN IL2AUX_SUBST_VARS_TAC THEN FS[IS_PREFIX_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_prefix o concl))) THEN
  MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_REFL];;

let IL2AUX_NONREC_ACIO_TAC : tactic =
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_clock_with_const; pair_CASE] THEN
  SIMP[IS_PREFIX_REFL];;

let IL2AUX_acio_lemma = prove
 (`!p (s:(A,C,FFI)wl_state) r1 s1.
     wl_evaluate (p,s) = (r1,s1)
     ==> ffi_state_io_events (wl_state_ffi s1) <<=
         ffi_state_io_events (wl_state_ffi (SND (wl_evaluate
           (p, wl_state_clock_fupd (K (wl_state_clock s + extra)) s))))`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate IL2AUX_NONREC_ACIO_TAC 10 @ replicate IL2AUX_ACIO_TAC 3 @
    replicate IL2AUX_NONREC_ACIO_TAC 4 @ replicate IL2AUX_ACIO_TAC 2 @
    replicate IL2AUX_NONREC_ACIO_TAC 6 @ [IL2AUX_ACIO_TAC]));;

(* HOL4: evaluate_add_clock_io_events_mono; line 1639 *)
let wl_evaluate_add_clock_io_events_mono = prove
 (`!exps (s:(A,C,FFI)wl_state) extra.
     ffi_state_io_events (wl_state_ffi (SND (wl_evaluate (exps,s)))) <<=
     ffi_state_io_events (wl_state_ffi (SND (wl_evaluate
       (exps, wl_state_clock_fupd (K (wl_state_clock s + extra)) s))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `wl_evaluate (exps:(A)wl_prog, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP IL2AUX_acio_lemma) THEN SIMP[]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_consts                                                           *)
(* ------------------------------------------------------------------------- *)

let IL2AUX_consts_facts =
  [alloc_code_gc_fun_const; inst_code_gc_fun_const; mem_store_const;
   jump_exc_const; share_inst_const; pop_env_code_gc_fun_clock; cut_state_const];;

let IL2AUX_CONSTS_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  DISCH_THEN (REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  TRY (IL2AUX_IH_GOAL_TAC IL2AUX_res_rws) THEN
  IL2AUX_POP_CONST_TAC THEN IL2AUX_FACTS_TAC IL2AUX_consts_facts THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN IL2AUX_DROP_IHS_TAC THEN
  IL2AUX_SUBST_VARS_TAC THEN FS[wl_dec_clock_def; wl_flush_state_def] THEN
  ASM_MESON_TAC[];;

(* HOL4: evaluate_consts; line 1740 *)
let wl_evaluate_consts = prove
 (`!xs (s1:(A,C,FFI)wl_state) vs s2.
     wl_evaluate (xs,s1) = (vs,s2)
     ==> wl_state_gc_fun s1 = wl_state_gc_fun s2 /\
         wl_state_mdomain s1 = wl_state_mdomain s2 /\
         wl_state_sh_mdomain s1 = wl_state_sh_mdomain s2 /\
         wl_state_be s1 = wl_state_be s2 /\
         wl_state_compile s1 = wl_state_compile s2 /\
         wl_state_stack_limit s1 = wl_state_stack_limit s2`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN IL2AUX_CONSTS_TAC);;

(* HOL4: get_vars_length_lemma; line 1765 *)
let get_vars_length_lemma = prove
 (`!ls (s:(A,C,FFI)wl_state) y. wl_get_vars ls s = SOME y ==> LENGTH y = LENGTH ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  SIMP[option_INJ; LENGTH] THEN REPEAT GEN_TAC THEN
  REPEAT TOP_CASE_TAC THEN SIMP[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

(* HOL4: stack_size_eq; line 1776 *)
let stack_size_eq = prove
 (`(wl_stack_size (CONS (StackFrame n l1 l2 NONE) (stack:((A)stack_frame)list)) =
      OPTION_MAP2 (+) n (wl_stack_size stack)) /\
   (wl_stack_size (CONS (StackFrame n l1 l2 (SOME handler)) (stack:((A)stack_frame)list)) =
      OPTION_MAP2 (+) (OPTION_MAP ((+) 3) n) (wl_stack_size stack)) /\
   (wl_stack_size ([]:((A)stack_frame)list) = SOME 1)`,
  REWRITE_TAC[wl_stack_size_def; stack_size_frame_def; ITLIST; o_THM]);;

(* HOL4: stack_size_eq2; line 1785 *)
let stack_size_eq2 = prove
 (`(wl_stack_size (CONS sfrm (stack:((A)stack_frame)list)) =
      OPTION_MAP2 (+) (stack_size_frame sfrm) (wl_stack_size stack)) /\
   (wl_stack_size ([]:((A)stack_frame)list) = SOME 1)`,
  REWRITE_TAC[wl_stack_size_def; ITLIST; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Stack Swap Lemma                                                          *)
(* ------------------------------------------------------------------------- *)

(* Stacks look the same to the GC except for the keys (e.g. recoloured and   *)
(* in order)                                                                 *)

let s_frame_val_eq_def = sem1aux_def
  `(s_frame_val_eq (StackFrame n ls1 ls NONE:(A)stack_frame)
                   (StackFrame n' ls1' ls' NONE) <=>
      MAP SND ls = MAP SND ls' /\ n = n') /\
   (s_frame_val_eq (StackFrame n ls1 ls (SOME y):(A)stack_frame)
                   (StackFrame n' ls1' ls' (SOME y')) <=>
      MAP SND ls = MAP SND ls' /\ y = y' /\ n = n') /\
   (s_frame_val_eq (_:(A)stack_frame) _ <=> F)`;;

let s_frame_val_eq_ind = IL2AUX_case_ind s_frame_val_eq_def;;

let s_frame_val_eq_def2 = prove
 (`s_frame_val_eq (StackFrame n ls0 ls y:(A)stack_frame) (StackFrame n' ls0' ls' y') <=>
     MAP SND ls = MAP SND ls' /\ y = y' /\ n = n'`,
  STRUCT_CASES_TAC (ISPEC `y:(num#num#num)option` (cases "option")) THEN
  STRUCT_CASES_TAC (ISPEC `y':(num#num#num)option` (cases "option")) THEN
  REWRITE_TAC[s_frame_val_eq_def; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let s_val_eq_def = sem1aux_def
  `(s_val_eq ([]:((A)stack_frame)list) [] <=> T) /\
   (s_val_eq (CONS x xs) (CONS y ys) <=> s_val_eq xs ys /\ s_frame_val_eq x y) /\
   (s_val_eq (_:((A)stack_frame)list) _ <=> F)`;;

let s_val_eq_ind = cake_ind "s_val_eq";;

(* Stacks look the same except for the values of the GC-ed cutsets (e.g.    *)
(* result of gc)                                                             *)

let s_frame_key_eq_def = sem1aux_def
  `(s_frame_key_eq (StackFrame n ls0 ls NONE:(A)stack_frame)
                   (StackFrame n' ls0' ls' NONE) <=>
      MAP FST ls = MAP FST ls' /\ ls0 = ls0' /\ n = n') /\
   (s_frame_key_eq (StackFrame n ls0 ls (SOME y):(A)stack_frame)
                   (StackFrame n' ls0' ls' (SOME y')) <=>
      MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 = ls0' /\ n = n') /\
   (s_frame_key_eq (_:(A)stack_frame) _ <=> F)`;;

let s_frame_key_eq_def2 = prove
 (`s_frame_key_eq (StackFrame n ls0 ls y:(A)stack_frame) (StackFrame n' ls0' ls' y') <=>
     MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 = ls0' /\ n = n'`,
  STRUCT_CASES_TAC (ISPEC `y:(num#num#num)option` (cases "option")) THEN
  STRUCT_CASES_TAC (ISPEC `y':(num#num#num)option` (cases "option")) THEN
  REWRITE_TAC[s_frame_key_eq_def; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let s_key_eq_def = sem1aux_def
  `(s_key_eq ([]:((A)stack_frame)list) [] <=> T) /\
   (s_key_eq (CONS x xs) (CONS y ys) <=> s_key_eq xs ys /\ s_frame_key_eq x y) /\
   (s_key_eq (_:((A)stack_frame)list) _ <=> F)`;;

let s_key_eq_ind = cake_ind "s_key_eq";;

let s_key_eq_def2 = prove
 (`!l1 l2:((A)stack_frame)list. s_key_eq l1 l2 <=> ALL2 s_frame_key_eq l1 l2`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[s_key_eq_def; ALL2] THEN MESON_TAC[]);;

let s_val_eq_def2 = prove
 (`!l1 l2:((A)stack_frame)list. s_val_eq l1 l2 <=> ALL2 s_frame_val_eq l1 l2`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[s_val_eq_def; ALL2] THEN MESON_TAC[]);;

(* Reflexive *)

let IL2AUX_FRAME_CASES_TAC (vs:term list) : tactic =
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "stack_frame"))) vs;;

let s_frame_key_eq_refl = prove
 (`!ls:(A)stack_frame. s_frame_key_eq ls ls <=> T`,
  GEN_TAC THEN IL2AUX_FRAME_CASES_TAC [`ls:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_key_eq_def2]);;

let s_frame_val_eq_refl = prove
 (`!ls:(A)stack_frame. s_frame_val_eq ls ls <=> T`,
  GEN_TAC THEN IL2AUX_FRAME_CASES_TAC [`ls:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_val_eq_def2]);;

let s_key_eq_refl = prove
 (`!ls:((A)stack_frame)list. s_key_eq ls ls <=> T`,
  GEN_TAC THEN REWRITE_TAC[s_key_eq_def2] THEN MATCH_MP_TAC EVERY2_refl THEN
  REWRITE_TAC[s_frame_key_eq_refl]);;

let s_val_eq_refl = prove
 (`!ls:((A)stack_frame)list. s_val_eq ls ls <=> T`,
  GEN_TAC THEN REWRITE_TAC[s_val_eq_def2] THEN MATCH_MP_TAC EVERY2_refl THEN
  REWRITE_TAC[s_frame_val_eq_refl]);;

(* transitive *)

(* HOL4 [local] *)
let s_frame_key_eq_trans = prove
 (`!a b c:(A)stack_frame. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
                          s_frame_key_eq a c`,
  REPEAT GEN_TAC THEN
  IL2AUX_FRAME_CASES_TAC [`a:(A)stack_frame`; `b:(A)stack_frame`; `c:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_key_eq_def2] THEN MESON_TAC[]);;

let s_key_eq_trans = prove
 (`!a b c:((A)stack_frame)list. s_key_eq a b /\ s_key_eq b c ==> s_key_eq a c`,
  REWRITE_TAC[s_key_eq_def2] THEN MATCH_MP_TAC EVERY2_trans THEN
  ACCEPT_TAC s_frame_key_eq_trans);;

(* HOL4 [local] *)
let s_frame_val_eq_trans = prove
 (`!a b c:(A)stack_frame. s_frame_val_eq a b /\ s_frame_val_eq b c ==>
                          s_frame_val_eq a c`,
  REPEAT GEN_TAC THEN
  IL2AUX_FRAME_CASES_TAC [`a:(A)stack_frame`; `b:(A)stack_frame`; `c:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_val_eq_def2] THEN MESON_TAC[]);;

let s_val_eq_trans = prove
 (`!a b c:((A)stack_frame)list. s_val_eq a b /\ s_val_eq b c ==> s_val_eq a c`,
  REWRITE_TAC[s_val_eq_def2] THEN MATCH_MP_TAC EVERY2_trans THEN
  ACCEPT_TAC s_frame_val_eq_trans);;

(* Symmetric *)

(* HOL4 [local] *)
let s_frame_key_eq_sym = prove
 (`!a b:(A)stack_frame. s_frame_key_eq a b <=> s_frame_key_eq b a`,
  REPEAT GEN_TAC THEN
  IL2AUX_FRAME_CASES_TAC [`a:(A)stack_frame`; `b:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_key_eq_def2] THEN MESON_TAC[]);;

let s_key_eq_sym = prove
 (`!a b:((A)stack_frame)list. s_key_eq a b <=> s_key_eq b a`,
  REWRITE_TAC[s_key_eq_def2] THEN LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  ASM_MESON_TAC[s_frame_key_eq_sym]);;

(* HOL4 [local] *)
let s_frame_val_eq_sym = prove
 (`!a b:(A)stack_frame. s_frame_val_eq a b <=> s_frame_val_eq b a`,
  REPEAT GEN_TAC THEN
  IL2AUX_FRAME_CASES_TAC [`a:(A)stack_frame`; `b:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_val_eq_def2] THEN MESON_TAC[]);;

let s_val_eq_sym = prove
 (`!a b:((A)stack_frame)list. s_val_eq a b <=> s_val_eq b a`,
  REWRITE_TAC[s_val_eq_def2] THEN LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  ASM_MESON_TAC[s_frame_val_eq_sym]);;

(* HOL4 [local] *)
let s_frame_val_and_key_eq = prove
 (`!s t:(A)stack_frame. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t`,
  REPEAT GEN_TAC THEN
  IL2AUX_FRAME_CASES_TAC [`s:(A)stack_frame`; `t:(A)stack_frame`] THEN
  REWRITE_TAC[s_frame_val_eq_def2; s_frame_key_eq_def2; injectivity "stack_frame"] THEN
  MESON_TAC[LIST_EQ_MAP_PAIR]);;

let LIST_REL_CONJ2 = prove
 (`ALL2 (\a b. (P:A->B->bool) a b /\ Q a b) l1 l2 <=> ALL2 P l1 l2 /\ ALL2 Q l1 l2`,
  REWRITE_TAC[AND_ALL2]);;

let s_val_and_key_eq = prove
 (`!s t:((A)stack_frame)list. s_val_eq s t /\ s_key_eq s t ==> s = t`,
  REWRITE_TAC[s_val_eq_def2; s_key_eq_def2; AND_ALL2] THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; CONS_11] THEN
  ASM_MESON_TAC[s_frame_val_and_key_eq]);;

(* the clauses of wl_dec_stack for any list of values *)

let IL2AUX_dec_stack_nil = prove
 (`!xs:((A)word_loc)list.
     wl_dec_stack xs ([]:((A)stack_frame)list) = if xs = [] then SOME [] else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_dec_stack_def; NOT_CONS_NIL]);;

let IL2AUX_dec_stack_cons = prove
 (CASE_TERM `!xs n l0 l handler (st:((A)stack_frame)list).
     wl_dec_stack xs (CONS (StackFrame n l0 l handler) st) =
       if LENGTH xs < LENGTH l then NONE else
       match wl_dec_stack (DROP (LENGTH l) xs) st with
         NONE -> NONE
       | SOME s -> SOME (CONS (StackFrame n l0 (ZIP (MAP FST l) (TAKE (LENGTH l) xs))
                                          handler) s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_dec_stack_def]);;

(* case splits on the free stack frames of the goal *)

let IL2AUX_ALL_FRAME_CASES_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> try fst(dest_type(type_of v)) = "stack_frame"
                            with Failure _ -> false) (frees w) in
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "stack_frame"))) vs g;;

(* HOL4 [local] *)
let dec_stack_stack_key_eq = prove
 (`!wl (st:((A)stack_frame)list) st'. wl_dec_stack wl st = SOME st' ==> s_key_eq st st'`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[IL2AUX_dec_stack_nil] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[s_key_eq_def];
    IL2AUX_FRAME_CASES_TAC [`h:(A)stack_frame`] THEN
    REWRITE_TAC[IL2AUX_dec_stack_cons] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[s_key_eq_def; s_frame_key_eq_def2] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MAP_FST_ZIP THEN
      REWRITE_TAC[LENGTH_MAP] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC]]);;

(* gc preserves the stack_key relation *)

let gc_s_key_eq = prove
 (`!(s:(A,C,FFI)wl_state) x.
     wl_gc s = SOME x ==> s_key_eq (wl_state_stack s) (wl_state_stack x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def; LET_DEF; LET_END_DEF] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[] THEN ASM_MESON_TAC[dec_stack_stack_key_eq]);;

(* HOL4 [local] *)
let s_val_eq_enc_stack = prove
 (`!st st':((A)stack_frame)list. s_val_eq st st' ==> wl_enc_stack st = wl_enc_stack st'`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[s_val_eq_def] THEN IL2AUX_ALL_FRAME_CASES_TAC THEN
  REWRITE_TAC[wl_enc_stack_def; s_frame_val_eq_def2] THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)
let s_val_eq_dec_stack = prove
 (`!q (st:((A)stack_frame)list) st' x.
     s_val_eq st st' /\ wl_dec_stack q st = SOME x
     ==> ?y. wl_dec_stack q st' = SOME y /\ s_val_eq x y`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[s_val_eq_def] THEN
  IL2AUX_ALL_FRAME_CASES_TAC THEN
  REWRITE_TAC[IL2AUX_dec_stack_nil; IL2AUX_dec_stack_cons; s_frame_val_eq_def2] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:((A)stack_frame)list` THEN
    REWRITE_TAC[s_val_eq_def];
    ALL_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (a2':(num#(A)word_loc)list) = LENGTH (a2:(num#(A)word_loc)list)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_MAP]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_dec_stack (DROP (LENGTH (a2:(num#(A)word_loc)list)) q)
              (t:((A)stack_frame)list)` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`DROP (LENGTH (a2:(num#(A)word_loc)list)) (q:((A)word_loc)list)`;
                               `t':((A)stack_frame)list`; `a:((A)stack_frame)list`] o
                 check (fun th -> is_forall (concl th) &&
                   not (can (find_term (fun x -> x = `h:(A)stack_frame`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; option_INJ] THEN
  EXISTS_TAC `CONS (StackFrame a0' a1' (ZIP (MAP FST (a2':(num#(A)word_loc)list))
                     (TAKE (LENGTH (a2:(num#(A)word_loc)list)) q)) a3')
                   (y:((A)stack_frame)list)` THEN
  ASM_REWRITE_TAC[s_val_eq_def; s_frame_val_eq_def2] THEN
  SUBGOAL_THEN `LENGTH (TAKE (LENGTH (a2:(num#(A)word_loc)list)) (q:((A)word_loc)list)) =
                LENGTH a2` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP]);;

(* gc succeeds on all stacks related by stack_val and there are relations   *)
(* in the result                                                             *)

let gc_s_val_eq = prove
 (`!(s:(A,C,FFI)wl_state) (x:B) st y.
     s_val_eq (wl_state_stack s) st /\ wl_gc s = SOME y
     ==> ?z. wl_gc (wl_state_stack_fupd (K st) s) = SOME (wl_state_stack_fupd (K z) y) /\
             s_val_eq (wl_state_stack y) z /\ s_key_eq z st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o
    REWRITE_RULE[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ])) THEN
  RVEQ_TAC THEN SIMP[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP s_val_eq_enc_stack) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `wl_state_stack (s:(A,C,FFI)wl_state)`;
                 `st:((A)stack_frame)list`; `a':((A)stack_frame)list`]
                s_val_eq_dec_stack) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z0:((A)stack_frame)list` THEN ASM_REWRITE_TAC[option_CASE] THEN
  ONCE_REWRITE_TAC[s_key_eq_sym] THEN ASM_MESON_TAC[dec_stack_stack_key_eq]);;

(* Slightly more general theorem allows the unused locals to be differnt *)

let gc_s_val_eq_word_state = prove
 (`!(s:(A,C,FFI)wl_state) tlocs tstack y.
     s_val_eq (wl_state_stack s) tstack /\ wl_gc s = SOME y
     ==> ?zlocs zstack.
           wl_gc (wl_state_locals_fupd (K tlocs) (wl_state_stack_fupd (K tstack) s)) =
           SOME (wl_state_locals_fupd (K zlocs) (wl_state_stack_fupd (K zstack) y)) /\
           s_val_eq (wl_state_stack y) zstack /\ s_key_eq zstack tstack`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o
    REWRITE_RULE[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ])) THEN
  RVEQ_TAC THEN SIMP[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP s_val_eq_enc_stack) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `wl_state_stack (s:(A,C,FFI)wl_state)`;
                 `tstack:((A)stack_frame)list`; `a':((A)stack_frame)list`]
                s_val_eq_dec_stack) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`tlocs:((A)word_loc)spt`; `z0:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[option_CASE; option_INJ] THEN REPEAT CONJ_TAC THEN
  TRY (REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN NO_TAC) THEN
  ONCE_REWRITE_TAC[s_key_eq_sym] THEN ASM_MESON_TAC[dec_stack_stack_key_eq]);;

(* Most generalised gc_s_val_eq *)

let gc_s_val_eq_gen = prove
 (`!(s:(A,C,FFI)wl_state) (t:(A,D,E)wl_state) s'.
     wl_state_gc_fun s = wl_state_gc_fun t /\
     wl_state_memory s = wl_state_memory t /\
     wl_state_mdomain s = wl_state_mdomain t /\
     wl_state_store s = wl_state_store t /\
     s_val_eq (wl_state_stack s) (wl_state_stack t) /\
     wl_state_stack_size s = wl_state_stack_size t /\
     wl_state_stack_max s = wl_state_stack_max t /\
     wl_state_stack_limit s = wl_state_stack_limit t /\
     wl_gc s = SOME s'
     ==> ?t'. wl_gc t = SOME t' /\
              s_val_eq (wl_state_stack s') (wl_state_stack t') /\
              s_key_eq (wl_state_stack t) (wl_state_stack t') /\
              wl_state_memory t' = wl_state_memory s' /\
              wl_state_store t' = wl_state_store s' /\
              wl_state_stack_size t' = wl_state_stack_size s' /\
              wl_state_stack_max t' = wl_state_stack_max s' /\
              wl_state_stack_limit t' = wl_state_stack_limit s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
    STRIP_ASSUME_TAC (REWRITE_RULE[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ]
                       (last (CONJUNCTS th)))) THEN
  RVEQ_TAC THEN SIMP[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP s_val_eq_enc_stack) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    [ASSUME `wl_state_gc_fun (s:(A,C,FFI)wl_state) = wl_state_gc_fun (t:(A,D,E)wl_state)`;
     ASSUME `wl_state_memory (s:(A,C,FFI)wl_state) = wl_state_memory (t:(A,D,E)wl_state)`;
     ASSUME `wl_state_mdomain (s:(A,C,FFI)wl_state) = wl_state_mdomain (t:(A,D,E)wl_state)`;
     ASSUME `wl_state_store (s:(A,C,FFI)wl_state) = wl_state_store (t:(A,D,E)wl_state)`]) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `wl_state_stack (s:(A,C,FFI)wl_state)`;
                 `wl_state_stack (t:(A,D,E)wl_state)`; `a':((A)stack_frame)list`]
                s_val_eq_dec_stack) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_CASE; option_INJ] THEN SIMP[] THEN
  ASM_MESON_TAC[dec_stack_stack_key_eq]);;

(* pushing and popping maintain the stack_key relation *)

let IL2AUX_push_env_stack = prove
 (`!x b (s:(A,C,FFI)wl_state). ?h.
     wl_state_stack (wl_push_env x b s) =
     CONS (StackFrame (wl_state_locals_size s) (toAList (FST x))
                      (FST (env_to_list (SND x) (wl_state_permute s))) h)
          (wl_state_stack s)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN SIMP[] THEN MESON_TAC[]);;

let IL2AUX_env_to_list_domain = prove
 (`!(env:((A)word_loc)spt) bij.
     set_of_list (MAP FST (FST (env_to_list env bij))) = domain env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM set_MAP_FST_toAList_domain; EXTENSION; IN_SET_OF_LIST; MEM_MAP] THEN
  REWRITE_TAC[mem_list_rearrange; sort_MEM]);;

let IL2AUX_pop_env_cons = prove
 (`!(t:(A,C,FFI)wl_state) m e0 e h ls.
     wl_state_stack t = CONS (StackFrame m e0 e h) ls
     ==> ?y. wl_pop_env t = SOME y /\
             wl_state_locals y = sptree_union (fromAList e) (fromAList e0) /\
             wl_state_stack y = ls`,
  REWRITE_TAC[wl_pop_env_def] THEN REPEAT GEN_TAC THEN
  SPEC_TAC(`h:(num#num#num)option`,`h:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let push_env_pop_env_s_key_eq = prove
 (`!x b (s:(A,C,FFI)wl_state) (t:(A,D,E)wl_state).
     s_key_eq (wl_state_stack (wl_push_env x b s)) (wl_state_stack t)
     ==> ?n l ls opt.
           wl_state_stack t = CONS (StackFrame n (toAList (FST x)) l opt) ls /\
           ?y. wl_pop_env t = SOME y /\
               wl_state_locals y = sptree_union (fromAList l) (fromAList (toAList (FST x))) /\
               domain (SND x) UNION domain (FST x) = domain (wl_state_locals y) /\
               s_key_eq (wl_state_stack s) (wl_state_stack y)`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `h:(num#num#num)option` SUBST1_TAC (SPEC_ALL IL2AUX_push_env_stack) THEN
  MP_TAC (ISPEC `wl_state_stack (t:(A,D,E)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `ls:((A)stack_frame)list`
       ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[s_key_eq_def] THEN
  STRIP_ASSUME_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[s_frame_key_eq_def2] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a0:num option`; `a2:(num#(A)word_loc)list`;
                        `ls:((A)stack_frame)list`; `a3:(num#num#num)option`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> rand (concl th) = `a1:(num#(A)word_loc)list`)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IL2AUX_pop_env_cons o
    check (fun th -> is_eq (concl th) && is_comb (rhs (concl th)) &&
                     fst(dest_const(fst(strip_comb(rhs(concl th))))) = "CONS")) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A,D,E)wl_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:(A,D,E)wl_state` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[domain_union; domain_fromAList_toAList; domain_fromAList] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> is_eq (concl th) &&
                     rand(rand(concl th)) = `a2:(num#(A)word_loc)list`)) THEN
  REWRITE_TAC[IL2AUX_env_to_list_domain]);;

(* HOL4 [local] *)
let get_vars_stack_swap = prove
 (`!l (s:(A,C,FFI)wl_state) (t:(A,D,E)wl_state).
     wl_state_locals s = wl_state_locals t ==> wl_get_vars l s = wl_get_vars l t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`l:num list`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[wl_get_vars_def; wl_get_var_def]);;

let s_val_eq_length = prove
 (`!s t:((A)stack_frame)list. s_val_eq s t ==> LENGTH s = LENGTH t`,
  REWRITE_TAC[s_val_eq_def2] THEN MESON_TAC[LIST_REL_LENGTH]);;

let s_key_eq_length = prove
 (`!s t:((A)stack_frame)list. s_key_eq s t ==> LENGTH s = LENGTH t`,
  REWRITE_TAC[s_key_eq_def2] THEN MESON_TAC[LIST_REL_LENGTH]);;

(* HOL4 [local] *)
let s_val_eq_APPEND = prove
 (`!s t x y:((A)stack_frame)list.
     s_val_eq s t /\ s_val_eq x y ==> s_val_eq (APPEND s x) (APPEND t y)`,
  REWRITE_TAC[s_val_eq_def2] THEN MESON_TAC[LIST_REL_APPEND_suff]);;

(* HOL4 [local] *)
let s_val_eq_REVERSE = prove
 (`!s t:((A)stack_frame)list. s_val_eq s t ==> s_val_eq (REVERSE s) (REVERSE t)`,
  REWRITE_TAC[s_val_eq_def2] THEN MESON_TAC[EVERY2_REVERSE]);;

(* HOL4 [local] *)
let s_val_eq_TAKE = prove
 (`!s t:((A)stack_frame)list n. s_val_eq s t ==> s_val_eq (TAKE n s) (TAKE n t)`,
  REWRITE_TAC[s_val_eq_def2] THEN MESON_TAC[EVERY2_TAKE]);;

(* HOL4 [local] *)
let s_val_eq_LASTN = prove
 (`!s t:((A)stack_frame)list n. s_val_eq s t ==> s_val_eq (LASTN n s) (LASTN n t)`,
  REWRITE_TAC[s_val_eq_def2; LASTN_DEF] THEN MESON_TAC[EVERY2_REVERSE; EVERY2_TAKE]);;

(* HOL4 [local] *)
let s_key_eq_APPEND = prove
 (`!s t x y:((A)stack_frame)list.
     s_key_eq s t /\ s_key_eq x y ==> s_key_eq (APPEND s x) (APPEND t y)`,
  REWRITE_TAC[s_key_eq_def2] THEN MESON_TAC[LIST_REL_APPEND_suff]);;

(* HOL4 [local] *)
let s_key_eq_REVERSE = prove
 (`!s t:((A)stack_frame)list. s_key_eq s t ==> s_key_eq (REVERSE s) (REVERSE t)`,
  REWRITE_TAC[s_key_eq_def2] THEN MESON_TAC[EVERY2_REVERSE]);;

(* HOL4 [local] *)
let s_key_eq_TAKE = prove
 (`!s t:((A)stack_frame)list n. s_key_eq s t ==> s_key_eq (TAKE n s) (TAKE n t)`,
  REWRITE_TAC[s_key_eq_def2] THEN MESON_TAC[EVERY2_TAKE]);;

(* HOL4: s_key_eq_LASTN [local] *)
let wl_s_key_eq_LASTN = prove
 (`!s t:((A)stack_frame)list n. s_key_eq s t ==> s_key_eq (LASTN n s) (LASTN n t)`,
  REWRITE_TAC[s_key_eq_def2; LASTN_DEF] THEN MESON_TAC[EVERY2_REVERSE; EVERY2_TAKE]);;

let s_key_eq_tail = prove
 (`!a b c d:((A)stack_frame)list. s_key_eq (CONS a b) (CONS c d) ==> s_key_eq b d`,
  SIMP[s_key_eq_def]);;

(* HOL4 [local] *)
let s_val_eq_tail = prove
 (`!a b c d:((A)stack_frame)list. s_val_eq (CONS a b) (CONS c d) ==> s_val_eq b d`,
  SIMP[s_val_eq_def]);;

(* HOL4 [local] *)
let s_key_eq_LASTN_exists = prove
 (`!s t:((A)stack_frame)list n m e0 e y xs.
     s_key_eq s t /\ LASTN n s = CONS (StackFrame m e0 e (SOME y)) xs
     ==> ?e' ls. LASTN n t = CONS (StackFrame m e0 e' (SOME y)) ls /\
                 MAP FST e' = MAP FST e /\ s_key_eq xs ls`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP wl_s_key_eq_LASTN) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPEC `LASTN n (t:((A)stack_frame)list)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `ls:((A)stack_frame)list`
       SUBST1_TAC))) THEN
  REWRITE_TAC[s_key_eq_def] THEN
  STRUCT_CASES_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_key_eq_def2; injectivity "stack_frame"; CONS_11] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

let s_val_eq_LASTN_exists = prove
 (`!s t:((A)stack_frame)list n m e0 e y xs.
     s_val_eq s t /\ LASTN n s = CONS (StackFrame m e0 e (SOME y)) xs
     ==> ?e0' e' ls. LASTN n t = CONS (StackFrame m e0' e' (SOME y)) ls /\
                     MAP SND e' = MAP SND e /\ s_val_eq xs ls`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP s_val_eq_LASTN) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPEC `LASTN n (t:((A)stack_frame)list)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `ls:((A)stack_frame)list`
       SUBST1_TAC))) THEN
  REWRITE_TAC[s_val_eq_def] THEN
  STRUCT_CASES_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_val_eq_def2; injectivity "stack_frame"; CONS_11] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

let LASTN_LENGTH_cond = prove
 (`!n xs:A list. n = LENGTH xs ==> LASTN n xs = xs`,
  MESON_TAC[LASTN_LENGTH_ID]);;

(* HOL4 [local] *)
let handler_eq = prove
 (`wl_state_handler_fupd (K (wl_state_handler x)) (x:(A,C,FFI)wl_state) = x`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_stack_size_frame_alt = prove
 (`!n l0 l h. stack_size_frame (StackFrame n l0 l h:(A)stack_frame) =
              if h = NONE then n else OPTION_MAP ((+) 3) n`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `h:(num#num#num)option` (cases "option")) THEN
  REWRITE_TAC[stack_size_frame_def; option_DISTINCT]);;

let s_val_eq_stack_size = prove
 (`!xs ys:((A)stack_frame)list. s_val_eq xs ys ==> wl_stack_size xs = wl_stack_size ys`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[s_val_eq_def; stack_size_eq2] THEN IL2AUX_ALL_FRAME_CASES_TAC THEN
  REWRITE_TAC[s_frame_val_eq_def2; IL2AUX_stack_size_frame_alt] THEN STRIP_TAC THEN
  RVEQ_TAC THEN ASM_MESON_TAC[]);;

(* HOL4: s_key_eq_stack_size *)
let wl_s_key_eq_stack_size = prove
 (`!xs ys:((A)stack_frame)list. s_key_eq xs ys ==> wl_stack_size xs = wl_stack_size ys`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[s_key_eq_def; stack_size_eq2] THEN IL2AUX_ALL_FRAME_CASES_TAC THEN
  REWRITE_TAC[s_frame_key_eq_def2; IL2AUX_stack_size_frame_alt] THEN STRIP_TAC THEN
  RVEQ_TAC THEN ASM_MESON_TAC[]);;

let s_val_append_eq_stack_size = prove
 (`!stk stk' (frm:(A)stack_frame).
     s_val_eq stk stk' ==> wl_stack_size (CONS frm stk) = wl_stack_size (CONS frm stk')`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP s_val_eq_stack_size) THEN
  ASM_REWRITE_TAC[stack_size_eq2]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_stack_swap.  The statement is proved in the form                 *)
(* wl_evaluate (c,s) = (r,s1) ==> IL2AUX_ss c s r s1 by the evaluate          *)
(* induction, where IL2AUX_ss splits the HOL4 case on the result into three  *)
(* kinds: IL2AUX_ss_stop (TimeOut, NotEnoughSpace, FinalFFI: the final stack *)
(* is empty and the run on a stack with the same values gives the same       *)
(* result), IL2AUX_ss_exc (Exception) and IL2AUX_ss_norm (the other results:  *)
(* the run on a stack with the same values gives a final stack with the same *)
(* values).  Kind transfer lemmas, sequential composition (IL2AUX_ss_aseq)   *)
(* and the lemmas of Alloc, Raise, MustTerminate, Loop and Call handle the    *)
(* cases.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* forward chaining through an induction hypothesis: its antecedents are    *)
(* discharged by the facts, or by rewriting when they have no bound variable *)

let IL2AUX_fwd (facts:thm list) (ih:thm) : thm =
  let rec go th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = fst (dest_imp bod) in
    try tryfind (fun f -> go (MATCH_MP th f)) facts
    with Failure _ ->
      if exists (fun v -> vfree_in v ant) vs then failwith "IL2AUX_fwd" else
      let ath = EQT_ELIM (REWRITE_CONV IL2AUX_res_rws ant) in
      go (MP (SPEC_ALL th) ath) in
  go (REWRITE_RULE[IMP_CONJ] ih);;

(* an antecedent pattern = term, discharged by instantiating the pattern *)

let IL2AUX_fwd_eq (th:thm) : thm =
  let vs,bod = strip_forall (concl th) in
  let ant = fst (dest_imp bod) in
  let l,r = dest_eq ant in
  let try_dir p t =
    let (_,tmi,tyi) = term_match [] p t in
    if exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi ||
       exists (fun (a,b) -> not (a = b)) tyi then failwith "IL2AUX_fwd_eq" else tmi in
  let tmi = try try_dir l r with Failure _ -> try_dir r l in
  let tmi' = filter (fun (t,v) -> mem v vs) tmi in
  let th1 = INST tmi' (SPECL vs th) in
  let a1 = fst (dest_imp (concl th1)) in
  let th2 = MP th1 (EQT_ELIM (REWRITE_CONV [] a1)) in
  GENL (filter (fun v -> not (mem v (map snd tmi'))) vs) th2;;

(* IL2AUX_fwd with antecedents also proved by rewriting with the theorems fb *)

let IL2AUX_fwd_r (rws:thm list) (fb:thm list) (facts:thm list) (ih:thm) : thm =
  let rec go th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = fst (dest_imp bod) in
    try tryfind (fun f -> go (REWRITE_RULE rws (MATCH_MP th f))) facts
    with Failure _ ->
    try go (IL2AUX_fwd_eq th) with Failure _ ->
      if exists (fun v -> vfree_in v ant) vs then failwith "IL2AUX_fwd_r" else
      let ath = EQT_ELIM (REWRITE_CONV (IL2AUX_res_rws @ fb) ant) in
      go (MP (SPEC_ALL th) ath) in
  go (REWRITE_RULE[IMP_CONJ] ih);;

let IL2AUX_ss_stop_def = cake_def
 `IL2AUX_ss_stop (c:(A)wl_prog) (s:(A,C,FFI)wl_state) r s1 <=>
    wl_state_stack s1 = [] /\ wl_state_locals s1 = LN /\
    (!xs. s_val_eq (wl_state_stack s) xs
          ==> wl_evaluate (c,wl_state_stack_fupd (K xs) s) = (r,s1))`;;

let IL2AUX_ss_norm_def = cake_def
 `IL2AUX_ss_norm (c:(A)wl_prog) (s:(A,C,FFI)wl_state) r s1 <=>
    s_key_eq (wl_state_stack s) (wl_state_stack s1) /\
    wl_state_handler s1 = wl_state_handler s /\
    (!xs. s_val_eq (wl_state_stack s) xs
          ==> ?st. wl_evaluate (c,wl_state_stack_fupd (K xs) s) =
                     (r,wl_state_stack_fupd (K st) s1) /\
                   s_val_eq (wl_state_stack s1) st /\ s_key_eq xs st)`;;

let IL2AUX_ss_exc_def = cake_def
 `IL2AUX_ss_exc (c:(A)wl_prog) (s:(A,C,FFI)wl_state) x y s1 <=>
    wl_state_handler s < LENGTH (wl_state_stack s) /\
    (?e0 e n ls m lss.
       LASTN (wl_state_handler s + 1) (wl_state_stack s) =
         CONS (StackFrame m e0 e (SOME n)) ls /\
       m = wl_state_locals_size s1 /\
       (MAP FST e = MAP FST lss /\
        wl_state_locals s1 = sptree_union (fromAList lss) (fromAList e0)) /\
       s_key_eq (wl_state_stack s1) ls /\
       wl_state_handler s1 = (match n with (a,b,d) -> a) /\
       (!xs e0' e' ls'.
          LASTN (wl_state_handler s + 1) xs = CONS (StackFrame m e0' e' (SOME n)) ls' /\
          s_val_eq (wl_state_stack s) xs
          ==> ?st locs.
                wl_evaluate (c,wl_state_stack_fupd (K xs) s) =
                  (SOME (wl_Exception x y),
                   wl_state_stack_fupd (K st)
                     (wl_state_handler_fupd (K (match n with (a,b,d) -> a))
                        (wl_state_locals_fupd (K locs) s1))) /\
                (?lss'. MAP FST e' = MAP FST lss' /\
                        locs = sptree_union (fromAList lss') (fromAList e0') /\
                        MAP SND lss = MAP SND lss') /\
                s_val_eq (wl_state_stack s1) st /\ s_key_eq ls' st))`;;

let IL2AUX_ss_def = cake_def
 `IL2AUX_ss (c:(A)wl_prog) (s:(A,C,FFI)wl_state) r s1 <=>
    match r with
      SOME wl_Error -> T
    | SOME (wl_FinalFFI e) -> IL2AUX_ss_stop c s r s1
    | SOME wl_TimeOut -> IL2AUX_ss_stop c s r s1
    | SOME NotEnoughSpace -> IL2AUX_ss_stop c s r s1
    | SOME (wl_Exception x y) -> IL2AUX_ss_exc c s x y s1
    | _ -> IL2AUX_ss_norm c s r s1`;;

let IL2AUX_ss_thms = prove
 (`(IL2AUX_ss c (s:(A,C,FFI)wl_state) NONE s1 <=> IL2AUX_ss_norm c s NONE s1) /\
   (IL2AUX_ss c s (SOME (wl_Result w ws)) s1 <=>
      IL2AUX_ss_norm c s (SOME (wl_Result w ws)) s1) /\
   (IL2AUX_ss c s (SOME (wl_Exception x y)) s1 <=> IL2AUX_ss_exc c s x y s1) /\
   (IL2AUX_ss c s (SOME (wordSem_Break n)) s1 <=>
      IL2AUX_ss_norm c s (SOME (wordSem_Break n)) s1) /\
   (IL2AUX_ss c s (SOME (wordSem_Continue n)) s1 <=>
      IL2AUX_ss_norm c s (SOME (wordSem_Continue n)) s1) /\
   (IL2AUX_ss c s (SOME wl_TimeOut) s1 <=> IL2AUX_ss_stop c s (SOME wl_TimeOut) s1) /\
   (IL2AUX_ss c s (SOME NotEnoughSpace) s1 <=> IL2AUX_ss_stop c s (SOME NotEnoughSpace) s1) /\
   (IL2AUX_ss c s (SOME (wl_FinalFFI e)) s1 <=>
      IL2AUX_ss_stop c s (SOME (wl_FinalFFI e)) s1) /\
   (IL2AUX_ss c s (SOME wl_Error) s1 <=> T)`,
  REWRITE_TAC[IL2AUX_ss_def] THEN SIMP[]);;

let IL2AUX_ss_norm_transfer = prove
 (`!P p (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) r r' s1 s2.
     IL2AUX_ss_norm p s' r s1 /\
     wl_state_stack s' = wl_state_stack s /\ wl_state_handler s' = wl_state_handler s /\
     wl_state_stack s2 = wl_state_stack s1 /\ wl_state_handler s2 = wl_state_handler s1 /\
     (!xs st. s_val_eq (wl_state_stack s) xs /\
              wl_evaluate (p, wl_state_stack_fupd (K xs) s') =
                (r, wl_state_stack_fupd (K st) s1)
              ==> wl_evaluate (P, wl_state_stack_fupd (K xs) s) =
                    (r', wl_state_stack_fupd (K st) s2))
     ==> IL2AUX_ss_norm P s r' s2`,
  REWRITE_TAC[IL2AUX_ss_norm_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `wl_state_stack (s':(A,C,FFI)wl_state) =
                                      wl_state_stack (s:(A,C,FFI)wl_state)`;
                              ASSUME `wl_state_handler (s':(A,C,FFI)wl_state) =
                                      wl_state_handler (s:(A,C,FFI)wl_state)`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let IL2AUX_ss_stop_transfer = prove
 (`!P p (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) r r' s1 s2.
     IL2AUX_ss_stop p s' r s1 /\ wl_state_stack s' = wl_state_stack s /\
     wl_state_stack s2 = [] /\ wl_state_locals s2 = LN /\
     (!xs. s_val_eq (wl_state_stack s) xs /\
           wl_evaluate (p, wl_state_stack_fupd (K xs) s') = (r,s1)
           ==> wl_evaluate (P, wl_state_stack_fupd (K xs) s) = (r',s2))
     ==> IL2AUX_ss_stop P s r' s2`,
  REWRITE_TAC[IL2AUX_ss_stop_def] THEN MESON_TAC[]);;

let IL2AUX_ss_exc_transfer = prove
 (`!P p (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) x y s1 s2.
     IL2AUX_ss_exc p s' x y s1 /\
     wl_state_stack s' = wl_state_stack s /\ wl_state_handler s' = wl_state_handler s /\
     wl_state_stack s2 = wl_state_stack s1 /\ wl_state_handler s2 = wl_state_handler s1 /\
     wl_state_locals s2 = wl_state_locals s1 /\
     wl_state_locals_size s2 = wl_state_locals_size s1 /\
     (!xs st h locs.
        s_val_eq (wl_state_stack s) xs /\
        wl_evaluate (p, wl_state_stack_fupd (K xs) s') =
          (SOME (wl_Exception x y),
           wl_state_stack_fupd (K st)
             (wl_state_handler_fupd (K h) (wl_state_locals_fupd (K locs) s1)))
        ==> wl_evaluate (P, wl_state_stack_fupd (K xs) s) =
              (SOME (wl_Exception x y),
               wl_state_stack_fupd (K st)
                 (wl_state_handler_fupd (K h) (wl_state_locals_fupd (K locs) s2))))
     ==> IL2AUX_ss_exc P s x y s2`,
  REWRITE_TAC[IL2AUX_ss_exc_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `wl_state_stack (s':(A,C,FFI)wl_state) =
                                      wl_state_stack (s:(A,C,FFI)wl_state)`;
                              ASSUME `wl_state_handler (s':(A,C,FFI)wl_state) =
                                      wl_state_handler (s:(A,C,FFI)wl_state)`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`e0:(num#(A)word_loc)list`; `e:(num#(A)word_loc)list`;
    `n:num#num#num`; `ls:((A)stack_frame)list`; `m:num option`;
    `lss:(num#(A)word_loc)list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;


let IL2AUX_has_tm (tm:term) (th:thm) = can (find_term (fun t -> t = tm)) (concl th);;

let IL2AUX_PICK_TAC (yes:term list) (no:term list) (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th ->
    if is_forall (concl th) && forall (fun t -> IL2AUX_has_tm t th) yes &&
       not (exists (fun t -> IL2AUX_has_tm t th) no)
    then ttac th else failwith "IL2AUX_PICK_TAC");;

(* sequential composition: a first part from s to s1 that keeps the stack    *)
(* keys and the handler, then c2 from s1b, a state with the stack of s1      *)

let IL2AUX_ss_aseq_stop = prove
 (`!P c2 (s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) (s1b:(A,C,FFI)wl_state) r
     (s2:(A,C,FFI)wl_state).
     wl_state_stack s1b = wl_state_stack s1 /\
     (!xs. s_val_eq (wl_state_stack s) xs
           ==> ?st1. s_val_eq (wl_state_stack s1) st1 /\ s_key_eq xs st1 /\
                     wl_evaluate (P, wl_state_stack_fupd (K xs) s) =
                     wl_evaluate (c2, wl_state_stack_fupd (K st1) s1b)) /\
     IL2AUX_ss_stop c2 s1b r s2
     ==> IL2AUX_ss_stop P s r s2`,
  REWRITE_TAC[IL2AUX_ss_stop_def] THEN MESON_TAC[]);;

let IL2AUX_ss_aseq_norm = prove
 (`!P c2 (s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) (s1b:(A,C,FFI)wl_state) r
     (s2:(A,C,FFI)wl_state).
     s_key_eq (wl_state_stack s) (wl_state_stack s1) /\
     wl_state_handler s1 = wl_state_handler s /\
     wl_state_stack s1b = wl_state_stack s1 /\ wl_state_handler s1b = wl_state_handler s1 /\
     (!xs. s_val_eq (wl_state_stack s) xs
           ==> ?st1. s_val_eq (wl_state_stack s1) st1 /\ s_key_eq xs st1 /\
                     wl_evaluate (P, wl_state_stack_fupd (K xs) s) =
                     wl_evaluate (c2, wl_state_stack_fupd (K st1) s1b)) /\
     IL2AUX_ss_norm c2 s1b r s2
     ==> IL2AUX_ss_norm P s r s2`,
  REWRITE_TAC[IL2AUX_ss_norm_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[s_key_eq_trans];
    ASM_MESON_TAC[];
    X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC] THEN
  IL2AUX_PICK_TAC [`P:(A)wl_prog`] [] (MP_TAC o SPEC `xs:((A)stack_frame)list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  IL2AUX_PICK_TAC [`s1b:(A,C,FFI)wl_state`] [`P:(A)wl_prog`]
    (MP_TAC o SPEC `st1:((A)stack_frame)list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st2:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `st2:((A)stack_frame)list` THEN ASM_MESON_TAC[s_key_eq_trans]);;

let IL2AUX_ss_aseq_exc = prove
 (`!P c2 (s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) (s1b:(A,C,FFI)wl_state) x y
     (s2:(A,C,FFI)wl_state).
     s_key_eq (wl_state_stack s) (wl_state_stack s1) /\
     wl_state_handler s1 = wl_state_handler s /\
     wl_state_stack s1b = wl_state_stack s1 /\ wl_state_handler s1b = wl_state_handler s1 /\
     (!xs. s_val_eq (wl_state_stack s) xs
           ==> ?st1. s_val_eq (wl_state_stack s1) st1 /\ s_key_eq xs st1 /\
                     wl_evaluate (P, wl_state_stack_fupd (K xs) s) =
                     wl_evaluate (c2, wl_state_stack_fupd (K st1) s1b)) /\
     IL2AUX_ss_exc c2 s1b x y s2
     ==> IL2AUX_ss_exc P s x y s2`,
  REWRITE_TAC[IL2AUX_ss_exc_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_handler (s1b:(A,C,FFI)wl_state) = wl_state_handler (s:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s_key_eq (wl_state_stack (s1b:(A,C,FFI)wl_state))
                         (wl_state_stack (s:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[s_key_eq_sym]; ALL_TAC] THEN
  MP_TAC (ISPECL [`wl_state_stack (s1b:(A,C,FFI)wl_state)`;
                  `wl_state_stack (s:(A,C,FFI)wl_state)`;
                  `wl_state_handler (s:(A,C,FFI)wl_state) + 1`; `m:num option`;
                  `e0:(num#(A)word_loc)list`; `e:(num#(A)word_loc)list`; `n:num#num#num`;
                  `ls:((A)stack_frame)list`] s_key_eq_LASTN_exists) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `es:(num#(A)word_loc)list`
    (X_CHOOSE_THEN `lsx:((A)stack_frame)list` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[s_key_eq_length]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e0:(num#(A)word_loc)list`; `es:(num#(A)word_loc)list`;
    `n:num#num#num`; `lsx:((A)stack_frame)list`; `m:num option`;
    `lss:(num#(A)word_loc)list`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[s_key_eq_trans]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`xs:((A)stack_frame)list`; `e0':(num#(A)word_loc)list`;
                       `e':(num#(A)word_loc)list`; `ls':((A)stack_frame)list`] THEN
  STRIP_TAC THEN
  IL2AUX_PICK_TAC [`P:(A)wl_prog`] [] (MP_TAC o SPEC `xs:((A)stack_frame)list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  MP_TAC (ISPECL [`xs:((A)stack_frame)list`; `st1:((A)stack_frame)list`;
                  `wl_state_handler (s:(A,C,FFI)wl_state) + 1`; `m:num option`;
                  `e0':(num#(A)word_loc)list`; `e':(num#(A)word_loc)list`; `n:num#num#num`;
                  `ls':((A)stack_frame)list`] s_key_eq_LASTN_exists) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:(num#(A)word_loc)list`
    (X_CHOOSE_THEN `ls1:((A)stack_frame)list` STRIP_ASSUME_TAC)) THEN
  IL2AUX_PICK_TAC [`s1b:(A,C,FFI)wl_state`] []
    (MP_TAC o SPECL [`st1:((A)stack_frame)list`; `e0':(num#(A)word_loc)list`;
                     `e1:(num#(A)word_loc)list`; `ls1:((A)stack_frame)list`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)stack_frame)list`
    (X_CHOOSE_THEN `locs:((A)word_loc)spt` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`st:((A)stack_frame)list`; `locs:((A)word_loc)spt`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `lss':(num#(A)word_loc)list` THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[s_key_eq_trans]]);;

let IL2AUX_res_cases = prove
 (`!r:((A)wl_result)option.
     r = NONE \/ (?w ws. r = SOME (wl_Result w ws)) \/ (?x y. r = SOME (wl_Exception x y)) \/
     (?n. r = SOME (wordSem_Break n)) \/ (?n. r = SOME (wordSem_Continue n)) \/
     r = SOME wl_TimeOut \/ r = SOME NotEnoughSpace \/ (?e. r = SOME (wl_FinalFFI e)) \/
     r = SOME wl_Error`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; UNWIND_THM1; EXISTS_REFL] THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC[distinctness "wl_result"; injectivity "wl_result"] THEN MESON_TAC[]);;

let IL2AUX_ss_aseq = prove
 (`!P c2 (s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) (s1b:(A,C,FFI)wl_state) r
     (s2:(A,C,FFI)wl_state).
     s_key_eq (wl_state_stack s) (wl_state_stack s1) /\
     wl_state_handler s1 = wl_state_handler s /\
     wl_state_stack s1b = wl_state_stack s1 /\ wl_state_handler s1b = wl_state_handler s1 /\
     (!xs. s_val_eq (wl_state_stack s) xs
           ==> ?st1. s_val_eq (wl_state_stack s1) st1 /\ s_key_eq xs st1 /\
                     wl_evaluate (P, wl_state_stack_fupd (K xs) s) =
                     wl_evaluate (c2, wl_state_stack_fupd (K st1) s1b)) /\
     IL2AUX_ss c2 s1b r s2
     ==> IL2AUX_ss P s r s2`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` IL2AUX_res_cases) THEN
  REWRITE_TAC[IL2AUX_ss_thms] THEN STRIP_TAC THEN
  FIRST [MATCH_MP_TAC IL2AUX_ss_aseq_norm; MATCH_MP_TAC IL2AUX_ss_aseq_stop;
         MATCH_MP_TAC IL2AUX_ss_aseq_exc] THEN
  MAP_EVERY EXISTS_TAC [`c2:(A)wl_prog`; `s1:(A,C,FFI)wl_state`; `s1b:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[]);;

(* the kind transfer lemmas with the same result and the same final state *)

let IL2AUX_KIND_TRANSFER_TAC (p:term) (s':term) : tactic = fun (asl,w as g) ->
  let f,args = strip_comb w in
  let nm = fst (dest_const f) in
  let fin = last args in
  if nm = "IL2AUX_ss_exc" then
    (MATCH_MP_TAC IL2AUX_ss_exc_transfer THEN MAP_EVERY EXISTS_TAC [p; s'; fin]) g
  else
    let r = el 2 args in
    let lem = if nm = "IL2AUX_ss_norm" then IL2AUX_ss_norm_transfer
              else IL2AUX_ss_stop_transfer in
    (MATCH_MP_TAC lem THEN MAP_EVERY EXISTS_TAC [p; s'; r; fin]) g;;

let IL2AUX_ss_transfer = prove
 (`!P p (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) r (s1:(A,C,FFI)wl_state).
     wl_state_stack s' = wl_state_stack s /\ wl_state_handler s' = wl_state_handler s /\
     (!xs t. s_val_eq (wl_state_stack s) xs /\
             wl_evaluate (p, wl_state_stack_fupd (K xs) s') = (r,t)
             ==> wl_evaluate (P, wl_state_stack_fupd (K xs) s) = (r,t)) /\
     IL2AUX_ss p s' r s1
     ==> IL2AUX_ss P s r s1`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` IL2AUX_res_cases) THEN
  REWRITE_TAC[IL2AUX_ss_thms] THEN STRIP_TAC THEN
  IL2AUX_KIND_TRANSFER_TAC `p:(A)wl_prog` `s':(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[] THEN
  TRY (FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IL2AUX_ss_stop_def] o
         check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "IL2AUX_ss_stop"
                          with Failure _ -> false)) THEN ASM_REWRITE_TAC[]) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* the statements whose evaluation does not depend on the stack: the run   *)
(* on a swapped stack gives the same result and the swapped final state,    *)
(* or the same final state for the results that flush the stack             *)

let IL2AUX_transp_cons =
  ["wl_Skip"; "wl_StoreConsts"; "wl_Move"; "wl_Inst"; "wl_Assign"; "wl_Get"; "wl_Set";
   "wl_OpCurrHeap"; "wl_Store"; "wl_Tick"; "wl_Return"; "wl_Break"; "wl_Continue";
   "wl_LocValue"; "wl_Install"; "wl_CodeBufferWrite"; "wl_DataBufferWrite"; "wl_FFI";
   "ShareInst"];;

let IL2AUX_stopr_def = cake_def
 `IL2AUX_stopr (r:((A)wl_result)option) <=>
    match r with
      SOME wl_TimeOut -> T
    | SOME NotEnoughSpace -> T
    | SOME (wl_FinalFFI e) -> T
    | _ -> F`;;

let IL2AUX_stopr_thms = prove
 (`(IL2AUX_stopr (NONE:((A)wl_result)option) <=> F) /\
   (IL2AUX_stopr (SOME (wl_Result (w:(A)word_loc) ws)) <=> F) /\
   (IL2AUX_stopr (SOME (wl_Exception (x:(A)word_loc) y)) <=> F) /\
   (IL2AUX_stopr (SOME (wordSem_Break n:(A)wl_result)) <=> F) /\
   (IL2AUX_stopr (SOME (wordSem_Continue n:(A)wl_result)) <=> F) /\
   (IL2AUX_stopr (SOME (wl_TimeOut:(A)wl_result)) <=> T) /\
   (IL2AUX_stopr (SOME (NotEnoughSpace:(A)wl_result)) <=> T) /\
   (IL2AUX_stopr (SOME (wl_FinalFFI e:(A)wl_result)) <=> T) /\
   (IL2AUX_stopr (SOME (wl_Error:(A)wl_result)) <=> F)`,
  REWRITE_TAC[IL2AUX_stopr_def] THEN SIMP[]);;

let IL2AUX_dec_clock_stack = prove
 (`!(s:(A,C,FFI)wl_state) xs.
     wl_dec_clock (wl_state_stack_fupd (K xs) s) = wl_state_stack_fupd (K xs) (wl_dec_clock s)`,
  REWRITE_TAC[wl_dec_clock_def; wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_share_inst_stack = prove
 (`!op v ad (s:(A,C,FFI)wl_state) r t xs.
     share_inst op v ad s = (r:((A)wl_result)option,t)
     ==> share_inst op v ad (wl_state_stack_fupd (K xs) s) =
         (r, if IL2AUX_stopr r then t else wl_state_stack_fupd (K xs) t)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
              wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
              wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN REPEAT GEN_TAC THEN SIMP[] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC ORELSE IL2AUX_CALL_FFI_CASES_TAC) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IL2AUX_stopr_thms]) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SIMP[sh_mem_set_var_def; IL2AUX_stopr_thms; wl_flush_state_def; wl_set_var_def]);;

let IL2AUX_share_inst_facts = prove
 (`!op v ad (s:(A,C,FFI)wl_state) r t.
     share_inst op v ad s = (r:((A)wl_result)option,t)
     ==> (IL2AUX_stopr r ==> wl_state_stack t = [] /\ wl_state_locals t = LN) /\
         (~IL2AUX_stopr r /\ ~(r = SOME wl_Error)
          ==> wl_state_stack t = wl_state_stack s /\ wl_state_handler t = wl_state_handler s) /\
         (!x y. ~(r = SOME (wl_Exception x y)))`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
              wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
              wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC ORELSE IL2AUX_CALL_FFI_CASES_TAC) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE([IL2AUX_stopr_thms] @ IL2AUX_res_rws)) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SIMP[IL2AUX_stopr_thms; wl_flush_state_def; wl_set_var_def]);;

let IL2AUX_SW_TAC : tactic =
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[IL2AUX_stopr_thms; IL2AUX_dec_clock_stack] THEN
  REPEAT ((TOP_CASE_TAC ORELSE PAIRARG_TAC) THEN
          SIMP[PAIR_MAP_THM; I_THM; IL2AUX_stopr_thms; wl_flush_state_def;
               IL2AUX_dec_clock_stack]) THEN
  TRY (FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP IL2AUX_share_inst_stack th])) THEN
  SIMP[PAIR_MAP_THM; I_THM; IL2AUX_stopr_thms; wl_flush_state_def; IL2AUX_dec_clock_stack];;

let IL2AUX_evaluate_stack_with = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !xs. wl_evaluate (p, wl_state_stack_fupd (K xs) s) =
               pair_CASE (wl_evaluate (p,s))
                 (\r t. (r, if IL2AUX_stopr r then t else wl_state_stack_fupd (K xs) t))`)
    IL2AUX_transp_cons,
  REPEAT CONJ_TAC THEN IL2AUX_SW_TAC);;

let IL2AUX_ss_simple = prove
 (`!p (s:(A,C,FFI)wl_state) r t.
     (!xs. wl_evaluate (p, wl_state_stack_fupd (K xs) s) =
           (r, if IL2AUX_stopr r then t else wl_state_stack_fupd (K xs) t)) /\
     (IL2AUX_stopr r ==> wl_state_stack t = [] /\ wl_state_locals t = LN) /\
     (~IL2AUX_stopr r /\ ~(r = SOME wl_Error)
      ==> wl_state_stack t = wl_state_stack s /\ wl_state_handler t = wl_state_handler s) /\
     (!x y. ~(r = SOME (wl_Exception x y)))
     ==> IL2AUX_ss p s r t`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` IL2AUX_res_cases) THEN
  REWRITE_TAC([IL2AUX_ss_thms; IL2AUX_stopr_thms; IL2AUX_ss_stop_def; IL2AUX_ss_norm_def] @
              IL2AUX_res_rws) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[s_key_eq_refl] THEN
  TRY (EXISTS_TAC `xs:((A)stack_frame)list`) THEN ASM_REWRITE_TAC[s_key_eq_refl] THEN
  ASM_MESON_TAC[]);;

let IL2AUX_SST_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IL2AUX_ss_simple THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IL2AUX_evaluate_stack_with] THEN ASM_REWRITE_TAC[pair_CASE];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE([IL2AUX_stopr_thms] @ IL2AUX_res_rws)) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  IL2AUX_FACTS_TAC [inst_const_full; mem_store_const; IL2AUX_share_inst_facts] THEN
  REWRITE_TAC([IL2AUX_stopr_thms] @ IL2AUX_res_rws) THEN
  FS[wl_flush_state_def; wl_dec_clock_def; IL2AUX_stopr_thms] THEN
  ASM_MESON_TAC[];;

let IL2AUX_ss_transp = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !r t. wl_evaluate (p,s) = (r,t) ==> IL2AUX_ss p s r t`)
    IL2AUX_transp_cons,
  REPEAT CONJ_TAC THEN IL2AUX_SST_TAC);;

(* If and Seq *)

let IL2AUX_ss_if = prove
 (`!cmp r1 ri c1 c2 (s:(A,C,FFI)wl_state) x y b r (s1:(A,C,FFI)wl_state).
     wl_get_var r1 s = SOME x /\ wl_get_var_imm ri s = SOME y /\
     wl_word_cmp cmp x y = SOME b /\ IL2AUX_ss (if b then c1 else c2) s r s1
     ==> IL2AUX_ss (wl_If cmp r1 ri c1 c2) s r s1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IL2AUX_ss_transfer THEN
  MAP_EVERY EXISTS_TAC [`if b then c1 else c2:(A)wl_prog`; `s:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  COND_CASES_TAC THEN SIMP[]);;

let IL2AUX_ss_seq_some = prove
 (`!c1 c2 (s:(A,C,FFI)wl_state) r (s1:(A,C,FFI)wl_state).
     ~(r = NONE) /\ IL2AUX_ss c1 s r s1 ==> IL2AUX_ss (wl_Seq c1 c2) s r s1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IL2AUX_ss_transfer THEN
  MAP_EVERY EXISTS_TAC [`c1:(A)wl_prog`; `s:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE]);;

let IL2AUX_ss_seq_none = prove
 (`!c1 c2 (s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) r (s2:(A,C,FFI)wl_state).
     IL2AUX_ss_norm c1 s NONE s1 /\ IL2AUX_ss c2 s1 r s2
     ==> IL2AUX_ss (wl_Seq c1 c2) s r s2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IL2AUX_ss_aseq THEN
  MAP_EVERY EXISTS_TAC [`c2:(A)wl_prog`; `s1:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IL2AUX_ss_norm_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "IL2AUX_ss_norm"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xs:((A)stack_frame)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `st1:((A)stack_frame)list` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE]);;

(* MustTerminate *)

let IL2AUX_KIND_TRANSFER2_TAC (p:term) (s':term) (s1:term) : tactic = fun (asl,w as g) ->
  let f,args = strip_comb w in
  let nm = fst (dest_const f) in
  if nm = "IL2AUX_ss_exc" then
    (MATCH_MP_TAC IL2AUX_ss_exc_transfer THEN MAP_EVERY EXISTS_TAC [p; s'; s1]) g
  else
    let r = el 2 args in
    let lem = if nm = "IL2AUX_ss_norm" then IL2AUX_ss_norm_transfer
              else IL2AUX_ss_stop_transfer in
    (MATCH_MP_TAC lem THEN MAP_EVERY EXISTS_TAC [p; s'; r; s1]) g;;

let IL2AUX_ss_mt = prove
 (`!p (s:(A,C,FFI)wl_state) r (s1:(A,C,FFI)wl_state).
     ~(wl_state_termdep s = 0) /\ ~(r = SOME wl_TimeOut) /\
     IL2AUX_ss p (wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                    (wl_state_termdep_fupd (K (wl_state_termdep s - 1)) s)) r s1
     ==> IL2AUX_ss (MustTerminate p) s r
           (wl_state_clock_fupd (K (wl_state_clock s))
              (wl_state_termdep_fupd (K (wl_state_termdep s)) s1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` IL2AUX_res_cases) THEN
  REWRITE_TAC([IL2AUX_ss_thms] @ IL2AUX_res_rws) THEN STRIP_TAC THEN
  (ABBREV_TAC `s0 = wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                     (wl_state_termdep_fupd (K (wl_state_termdep s - 1))
                        (s:(A,C,FFI)wl_state))` THEN
  SUBGOAL_THEN
   `!xs. wl_evaluate (MustTerminate p, wl_state_stack_fupd (K xs) s) =
         pair_CASE (wl_evaluate (p, wl_state_stack_fupd (K xs) s0))
           (\res t. if res = SOME wl_TimeOut
                    then (SOME wl_Error, wl_state_stack_fupd (K xs) (s:(A,C,FFI)wl_state))
                    else (res, wl_state_clock_fupd (K (wl_state_clock s))
                                 (wl_state_termdep_fupd (K (wl_state_termdep s)) t)))`
   ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN EXPAND_TAC "s0" THEN
    ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_stack (s0:(A,C,FFI)wl_state) = wl_state_stack (s:(A,C,FFI)wl_state) /\
                wl_state_handler s0 = wl_state_handler (s:(A,C,FFI)wl_state)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN SIMP[]; ALL_TAC] THEN
  IL2AUX_KIND_TRANSFER2_TAC `p:(A)wl_prog` `s0:(A,C,FFI)wl_state` `s1:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  TRY (FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IL2AUX_ss_stop_def] o
         check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "IL2AUX_ss_stop"
                          with Failure _ -> false)) THEN ASM_REWRITE_TAC[]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN SIMP[]));;

(* Loop *)

let IL2AUX_cut_state_stack_handler = prove
 (`!x (s:(A,C,FFI)wl_state) s'.
     wl_cut_state x s = SOME s'
     ==> wl_state_stack s' = wl_state_stack s /\ wl_state_handler s' = wl_state_handler s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP cut_state_const) THEN
  SIMP[]);;

let IL2AUX_is_norm th =
  try fst(dest_const(fst(strip_comb(concl th)))) = "IL2AUX_ss_norm" with Failure _ -> false;;

let IL2AUX_ss_loop_timeout = prove
 (`!names c exit_names (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) res
     (s1:(A,C,FFI)wl_state).
     wl_cut_state (names,LN) s = SOME s' /\ wl_cont_loop res /\
     IL2AUX_ss_norm c s' res s1 /\ wl_state_clock s1 = 0
     ==> IL2AUX_ss (wl_Loop names c exit_names) s (SOME wl_TimeOut) (wl_flush_state T s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_stack_handler) THEN
  REWRITE_TAC[IL2AUX_ss_thms; IL2AUX_ss_stop_def] THEN SIMP[wl_flush_state_def] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IL2AUX_ss_norm_def] o check IL2AUX_is_norm) THEN
  DISCH_THEN(MP_TAC o SPEC `xs:((A)stack_frame)list` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  SIMP[wl_flush_state_def]);;

let IL2AUX_ss_loop_rec = prove
 (`!names c exit_names (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) res
     (s1:(A,C,FFI)wl_state) r (s2:(A,C,FFI)wl_state).
     wl_cut_state (names,LN) s = SOME s' /\ wl_cont_loop res /\
     IL2AUX_ss_norm c s' res s1 /\ ~(wl_state_clock s1 = 0) /\
     IL2AUX_ss (wl_STOP (wl_Loop names c exit_names)) (wl_dec_clock s1) r s2
     ==> IL2AUX_ss (wl_Loop names c exit_names) s r s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_stack_handler) THEN
  MATCH_MP_TAC IL2AUX_ss_aseq THEN
  MAP_EVERY EXISTS_TAC [`wl_STOP (wl_Loop names c exit_names):(A)wl_prog`;
                        `s1:(A,C,FFI)wl_state`; `wl_dec_clock (s1:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[wl_dec_clock_const] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IL2AUX_ss_norm_def] o check IL2AUX_is_norm) THEN
  REPEAT CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xs:((A)stack_frame)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `st1:((A)stack_frame)list` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP[IL2AUX_dec_clock_stack]);;

let IL2AUX_ss_loop_break0 = prove
 (`!names c exit_names (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state)
     (s2:(A,C,FFI)wl_state).
     wl_cut_state (names,LN) s = SOME s' /\
     IL2AUX_ss_norm c s' (SOME (wordSem_Break 0)) s1 /\
     wl_cut_state (exit_names,LN) s1 = SOME s2
     ==> IL2AUX_ss (wl_Loop names c exit_names) s NONE s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_stack_handler o
    check (fun th -> IL2AUX_has_tm `s':(A,C,FFI)wl_state` th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_stack_handler o
    check (fun th -> IL2AUX_has_tm `s2:(A,C,FFI)wl_state` th)) THEN
  REWRITE_TAC[IL2AUX_ss_thms] THEN MATCH_MP_TAC IL2AUX_ss_norm_transfer THEN
  MAP_EVERY EXISTS_TAC [`c:(A)wl_prog`; `s':(A,C,FFI)wl_state`;
                        `SOME (wordSem_Break 0):((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  SIMP[]);;

(* the transfer lemma of the kind of the goal, with the program, the state, *)
(* the result and the final state of the kind assumption of that kind       *)

let IL2AUX_kind_name tm =
  try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "";;

let IL2AUX_KIND_FROM_TAC : tactic = fun (asl,w as g) ->
  let nm = IL2AUX_kind_name w in
  let kth = snd (find (fun (_,th) -> IL2AUX_kind_name (concl th) = nm) asl) in
  let kargs = snd (strip_comb (concl kth)) in
  if nm = "IL2AUX_ss_exc" then
    (MATCH_MP_TAC IL2AUX_ss_exc_transfer THEN
     MAP_EVERY EXISTS_TAC [el 0 kargs; el 1 kargs; el 4 kargs]) g
  else
    let lem = if nm = "IL2AUX_ss_norm" then IL2AUX_ss_norm_transfer
              else IL2AUX_ss_stop_transfer in
    (MATCH_MP_TAC lem THEN
     MAP_EVERY EXISTS_TAC [el 0 kargs; el 1 kargs; el 2 kargs; el 3 kargs]) g;;

let IL2AUX_ss_loop_exit = prove
 (`!names c exit_names (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) res
     (s1:(A,C,FFI)wl_state).
     wl_cut_state (names,LN) s = SOME s' /\ ~wl_cont_loop res /\
     ~(res = SOME (wordSem_Break 0)) /\ IL2AUX_ss c s' res s1
     ==> IL2AUX_ss (wl_Loop names c exit_names) s (wl_exit_loop res) s1`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` IL2AUX_res_cases) THEN
  SIMP[wl_cont_loop_def; wl_exit_loop_def; IL2AUX_ss_thms] THEN STRIP_TAC THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_cut_state_stack_handler) THEN
   IL2AUX_KIND_FROM_TAC THEN ASM_REWRITE_TAC[] THEN
   TRY (FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IL2AUX_ss_stop_def] o
          check (fun th -> IL2AUX_kind_name (concl th) = "IL2AUX_ss_stop")) THEN
        ASM_REWRITE_TAC[]) THEN
   REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
   ASM_REWRITE_TAC[pair_CASE] THEN SIMP[wl_cont_loop_def; wl_exit_loop_def]));;

(* Raise *)

let IL2AUX_ss_raise = prove
 (`!n (s:(A,C,FFI)wl_state) w (t:(A,C,FFI)wl_state) l1 l2.
     wl_get_var n s = SOME w /\ wl_jump_exc s = SOME (t,l1,l2)
     ==> IL2AUX_ss_exc (wl_Raise n) s (wl_Loc l1 l2) w t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC (ISPEC `LASTN (wl_state_handler (s:(A,C,FFI)wl_state) + 1) (wl_state_stack s)`
            list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN SIMP[])
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `tl:((A)stack_frame)list`
       ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_ASSUME_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC (ISPEC `a3:(num#num#num)option` (cases "option")) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN SIMP[] THEN
  STRIP_ASSUME_TAC (ISPEC `a:num#num#num` PAIR_SURJECTIVE) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC (ISPEC `y:num#num` PAIR_SURJECTIVE) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[IL2AUX_ss_exc_def] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`a1:(num#(A)word_loc)list`; `a2:(num#(A)word_loc)list`;
    `(x:num,l1:num,l2:num)`; `tl:((A)stack_frame)list`; `a0:num option`;
    `a2:(num#(A)word_loc)list`] THEN
  ASM_REWRITE_TAC[] THEN SIMP[s_key_eq_refl] THEN
  MAP_EVERY X_GEN_TAC [`xs:((A)stack_frame)list`; `e0':(num#(A)word_loc)list`;
                       `e':(num#(A)word_loc)list`; `ls':((A)stack_frame)list`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ls':((A)stack_frame)list`;
                        `sptree_union (fromAList (e':(num#(A)word_loc)list)) (fromAList e0')`] THEN
  MP_TAC (ISPECL [`wl_state_stack (s:(A,C,FFI)wl_state)`; `xs:((A)stack_frame)list`;
                  `wl_state_handler (s:(A,C,FFI)wl_state) + 1`] s_val_eq_LASTN) THEN
  ASM_REWRITE_TAC[s_val_eq_def; s_frame_val_eq_def2] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[s_key_eq_refl] THEN
  CONJ_TAC THENL
   [ALL_TAC; EXISTS_TAC `e':(num#(A)word_loc)list` THEN ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN SIMP[wl_jump_exc_def] THEN
  SUBGOAL_THEN `LENGTH (xs:((A)stack_frame)list) = LENGTH (wl_state_stack (s:(A,C,FFI)wl_state))`
    SUBST1_TAC THENL [ASM_MESON_TAC[s_val_eq_length]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* push_env, call_env and pop_env on a stack with the same values *)

let IL2AUX_push_env_stack_swap = prove
 (`!envs b (s:(A,C,FFI)wl_state) xs.
     s_val_eq (wl_state_stack s) xs
     ==> wl_push_env envs b (wl_state_stack_fupd (K xs) s) =
         wl_state_stack_fupd (K (CONS (HD (wl_state_stack (wl_push_env envs b s))) xs))
           (wl_push_env envs b s) /\
         s_val_eq (wl_state_stack (wl_push_env envs b s))
                  (CONS (HD (wl_state_stack (wl_push_env envs b s))) xs)`,
  GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP s_val_eq_stack_size) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP s_val_eq_length) THEN
  SIMP[stack_size_eq2; s_val_eq_def; s_frame_val_eq_refl; HD] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[stack_size_eq2]);;

let IL2AUX_call_env_stack_swap = prove
 (`!args ss (s:(A,C,FFI)wl_state) xs.
     s_val_eq (wl_state_stack s) xs
     ==> wl_call_env args ss (wl_state_stack_fupd (K xs) s) =
         wl_state_stack_fupd (K xs) (wl_call_env args ss s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP s_val_eq_stack_size) THEN
  REWRITE_TAC[wl_call_env_def; wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_pop_env_stack_swap = prove
 (`!(t:(A,C,FFI)wl_state) t1 f rest rest'.
     wl_pop_env t = SOME t1 /\ wl_state_stack t = CONS f rest
     ==> wl_pop_env (wl_state_stack_fupd (K (CONS f rest')) t) =
         SOME (wl_state_stack_fupd (K rest') t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  STRUCT_CASES_TAC (ISPEC `f:(A)stack_frame` (cases "stack_frame")) THEN
  STRUCT_CASES_TAC (ISPEC `a3:(num#num#num)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:num#num#num` PAIR_SURJECTIVE)) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `y:num#num` PAIR_SURJECTIVE)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_pop_env_handler = prove
 (`!(t:(A,C,FFI)wl_state) t1 m e0 e h rest.
     wl_pop_env t = SOME t1 /\ wl_state_stack t = CONS (StackFrame m e0 e h) rest
     ==> wl_state_handler t1 =
           (match h with NONE -> wl_state_handler t | SOME (n,l1,l2) -> n) /\
         wl_state_stack t1 = rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  STRUCT_CASES_TAC (ISPEC `h:(num#num#num)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:num#num#num` PAIR_SURJECTIVE)) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `y:num#num` PAIR_SURJECTIVE)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

(* a stack with the keys of CONS f xs and the values of CONS f2 rest2 *)

let IL2AUX_stack_swap_head = prove
 (`!(f:(A)stack_frame) f2 xs rest2 st.
     s_key_eq (CONS f xs) st /\ s_val_eq (CONS f2 rest2) st /\ s_frame_key_eq f f2
     ==> ?st'. st = CONS f2 st' /\ s_key_eq xs st' /\ s_val_eq rest2 st'`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `st:((A)stack_frame)list` list_CASES) THEN
  REWRITE_TAC[s_key_eq_def; s_val_eq_def; CONS_11] THEN STRIP_TAC THEN
  EXISTS_TAC `t:((A)stack_frame)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC s_frame_val_and_key_eq THEN
  ASM_MESON_TAC[s_frame_key_eq_sym; s_frame_key_eq_trans; s_frame_val_eq_sym]);;


(* Alloc *)

let IL2AUX_push_env_none_stack = prove
 (`!envs (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s) =
       CONS (StackFrame (wl_state_locals_size s) (toAList (FST envs))
               (FST (env_to_list (SND envs) (wl_state_permute s))) NONE)
            (wl_state_stack s) /\
     wl_state_handler (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s) =
       wl_state_handler s`,
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN SIMP[]);;

let IL2AUX_s_key_eq_frame = prove
 (`!m e0 e (h:(num#num#num)option) xs (ys:((A)stack_frame)list).
     s_key_eq (CONS (StackFrame m e0 e h) xs) ys <=>
     ?e' zs. ys = CONS (StackFrame m e0 e' h) zs /\ MAP FST e = MAP FST e' /\ s_key_eq xs zs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  REWRITE_TAC[s_key_eq_def; NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC (ISPEC `h':(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_key_eq_def2; injectivity "stack_frame"] THEN MESON_TAC[]);;

let IL2AUX_alloc_stack_swap = prove
 (`!w (s:(A,C,FFI)wl_state) envs (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state) xs.
     wl_gc (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
              (wl_set_store AllocSize (wl_Word w) s)) = SOME s1 /\
     wl_pop_env s1 = SOME s2 /\ s_val_eq (wl_state_stack s) xs
     ==> s_key_eq (wl_state_stack s) (wl_state_stack s2) /\
         wl_state_handler s2 = wl_state_handler s /\
         ?z1 z. wl_gc (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
                         (wl_state_stack_fupd (K xs) (wl_set_store AllocSize (wl_Word w) s))) =
                SOME (wl_state_stack_fupd (K z1) s1) /\
                wl_pop_env (wl_state_stack_fupd (K z1) s1) =
                  SOME (wl_state_stack_fupd (K z) s2) /\
                s_val_eq (wl_state_stack s2) z /\ s_key_eq xs z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = wl_set_store AllocSize (wl_Word w) (s:(A,C,FFI)wl_state)` THEN
  SUBGOAL_THEN `wl_state_stack (u:(A,C,FFI)wl_state) = wl_state_stack (s:(A,C,FFI)wl_state) /\
                wl_state_handler u = wl_state_handler s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN SIMP[wl_set_store_def]; ALL_TAC] THEN
  ABBREV_TAC `v = wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) (u:(A,C,FFI)wl_state)` THEN
  ABBREV_TAC `fr = HD (wl_state_stack (v:(A,C,FFI)wl_state))` THEN
  SUBGOAL_THEN `wl_state_stack (v:(A,C,FFI)wl_state)
      = CONS fr (wl_state_stack (u:(A,C,FFI)wl_state)) /\
                wl_state_handler v = wl_state_handler u /\
                (?m e0 e. fr = StackFrame m e0 e (NONE:(num#num#num)option))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fr"; "v"] THEN REWRITE_TAC[IL2AUX_push_env_none_stack; HD] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `NONE:(num#(A)wl_prog#num#num)option`; `u:(A,C,FFI)wl_state`;
                  `xs:((A)stack_frame)list`] IL2AUX_push_env_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`v:(A,C,FFI)wl_state`; `ARB:bool`; `CONS (fr:(A)stack_frame) xs`;
                  `s1:(A,C,FFI)wl_state`] gc_s_val_eq) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s_key_eq (wl_state_stack (v:(A,C,FFI)wl_state)) (wl_state_stack
      (s1:(A,C,FFI)wl_state))`
    MP_TAC THENL [MATCH_MP_TAC gc_s_key_eq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IL2AUX_s_key_eq_frame] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:(num#(A)word_loc)list` (X_CHOOSE_THEN `rest2:((A)stack_frame)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC (ISPECL [`StackFrame m e0 e (NONE:(num#num#num)option):(A)stack_frame`;
                  `StackFrame m e0 e2 (NONE:(num#num#num)option):(A)stack_frame`;
                  `xs:((A)stack_frame)list`; `rest2:((A)stack_frame)list`;
                  `z1:((A)stack_frame)list`] IL2AUX_stack_swap_head) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[s_frame_key_eq_def2] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[s_key_eq_sym] THEN ASM_REWRITE_TAC[];
                    FIRST_X_ASSUM(fun th -> if IL2AUX_has_tm `z1:((A)stack_frame)list` th &&
                       IL2AUX_kind_name (concl th) = "s_val_eq"
                       then MP_TAC th else failwith "") THEN
                    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  MP_TAC (ISPECL [`s1:(A,C,FFI)wl_state`; `s2:(A,C,FFI)wl_state`; `m:num option`;
                  `e0:(num#(A)word_loc)list`; `e2:(num#(A)word_loc)list`;
                  `NONE:(num#num#num)option`; `rest2:((A)stack_frame)list`]
                 IL2AUX_pop_env_handler) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gc_const o
    check (fun th -> IL2AUX_kind_name (lhs (concl th)) = "wl_gc" &&
                     not (IL2AUX_has_tm `xs:((A)stack_frame)list` th))) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `z:((A)stack_frame)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IL2AUX_pop_env_stack_swap THEN
  EXISTS_TAC `rest2:((A)stack_frame)list` THEN ASM_REWRITE_TAC[]);;

let IL2AUX_ss_alloc = prove
 (`!n names (s:(A,C,FFI)wl_state) w r (t:(A,C,FFI)wl_state).
     wl_get_var n s = SOME (wl_Word w) /\ wl_alloc w names s = (r,t)
     ==> IL2AUX_ss (wl_Alloc n names) s r t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_alloc_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[IL2AUX_ss_thms; IL2AUX_ss_norm_def; IL2AUX_ss_stop_def] THEN
  FIRST_ASSUM(fun gc -> if IL2AUX_kind_name (lhs (concl gc)) = "wl_gc" then
    FIRST_ASSUM(fun pop -> if IL2AUX_kind_name (lhs (concl pop)) = "wl_pop_env" then
      ASSUME_TAC (GEN `xs:((A)stack_frame)list`
        (DISCH `s_val_eq (wl_state_stack (s:(A,C,FFI)wl_state)) xs`
          (MATCH_MP IL2AUX_alloc_stack_swap
             (CONJ gc (CONJ pop (ASSUME `s_val_eq (wl_state_stack (s:(A,C,FFI)wl_state)) xs`))))))
      else failwith "")
    else failwith "") THEN
  FIRST_ASSUM(fun th ->
    let th' = REWRITE_RULE[s_val_eq_refl] (SPEC `wl_state_stack (s:(A,C,FFI)wl_state)` th) in
    ASSUME_TAC (CONJUNCT1 th') THEN ASSUME_TAC (CONJUNCT1 (CONJUNCT2 th'))) THEN
  ASM_REWRITE_TAC[] THEN SIMP[wl_flush_state_def] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `xs:((A)stack_frame)list` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:((A)stack_frame)list` (X_CHOOSE_THEN `y:((A)stack_frame)list`
    STRIP_ASSUME_TAC)) THEN
  TRY (EXISTS_TAC `y:((A)stack_frame)list`) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  REWRITE_TAC[wl_alloc_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[wl_flush_state_def]);;

(* Call: the callee state of a call from a swapped stack *)

let IL2AUX_call_stack_swap = prove
 (`!args1 ss envs b (s:(A,C,FFI)wl_state) xs.
     s_val_eq (wl_state_stack s) xs
     ==> wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock (wl_state_stack_fupd (K xs) s))) =
         wl_state_stack_fupd
           (K (CONS (HD (wl_state_stack (wl_push_env envs b (wl_dec_clock s)))) xs))
           (wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock s))) /\
         s_val_eq (wl_state_stack (wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock s))))
                  (CONS (HD (wl_state_stack (wl_push_env envs b (wl_dec_clock s)))) xs) /\
         wl_state_stack (wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock s))) =
           CONS (HD (wl_state_stack (wl_push_env envs b (wl_dec_clock s)))) (wl_state_stack s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IL2AUX_dec_clock_stack] THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `b:(num#(A)wl_prog#num#num)option`;
                  `wl_dec_clock (s:(A,C,FFI)wl_state)`; `xs:((A)stack_frame)list`]
                 IL2AUX_push_env_stack_swap) THEN
  ASM_REWRITE_TAC[wl_dec_clock_const] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
                  `wl_push_env envs b (wl_dec_clock (s:(A,C,FFI)wl_state))`;
                  `CONS (HD (wl_state_stack (wl_push_env envs b (wl_dec_clock
                      (s:(A,C,FFI)wl_state)))))
                        xs`] IL2AUX_call_env_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wl_call_env_const] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `b:(num#(A)wl_prog#num#num)option`;
                  `wl_dec_clock (s:(A,C,FFI)wl_state)`] IL2AUX_push_env_stack) THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[HD; wl_dec_clock_const]);;

let IL2AUX_ss_call_tail0 = prove
 (`!dest args (s:(A,C,FFI)wl_state) vs args1 prog ss.
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (NONE:(num list#cutsets#(A)wl_prog#num#num)option) vs)
         (wl_state_code s) (wl_state_stack_size s) =
       SOME (args1,prog,ss) /\
     wl_state_clock s = 0
     ==> IL2AUX_ss_stop (wl_Call NONE dest args NONE) s (SOME wl_TimeOut)
           (wl_flush_state T s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IL2AUX_ss_stop_def] THEN
  SIMP[wl_flush_state_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN SIMP[wl_flush_state_def]);;

let IL2AUX_ss_call_tail = prove
 (`!dest args (s:(A,C,FFI)wl_state) vs args1 prog ss r (s1:(A,C,FFI)wl_state).
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (NONE:(num list#cutsets#(A)wl_prog#num#num)option) vs)
         (wl_state_code s) (wl_state_stack_size s) =
       SOME (args1,prog,ss) /\
     ~(wl_state_clock s = 0) /\ ~wl_bad_fun_return r /\
     IL2AUX_ss prog (wl_call_env args1 ss (wl_dec_clock s)) r s1
     ==> IL2AUX_ss (wl_Call NONE dest args NONE) s r s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IL2AUX_ss_transfer THEN
  MAP_EVERY EXISTS_TAC [`prog:(A)wl_prog`;
                        `wl_call_env args1 ss (wl_dec_clock (s:(A,C,FFI)wl_state))`] THEN
  ASM_REWRITE_TAC[wl_call_env_const; wl_dec_clock_const] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  REWRITE_TAC[IL2AUX_dec_clock_stack] THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`; `wl_dec_clock (s:(A,C,FFI)wl_state)`;
                  `xs:((A)stack_frame)list`] IL2AUX_call_env_stack_swap) THEN
  ASM_REWRITE_TAC[wl_dec_clock_const] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[pair_CASE]);;

let IL2AUX_ss_call_ret0 = prove
 (`!n names rh l1 l2 dest args handler (s:(A,C,FFI)wl_state) vs args1 prog ss envs.
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (n,names,rh,l1,l2)) vs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     ~(domain (FST names) = {} \/ ~ALL_DISTINCT n) /\
     cut_envs names (wl_state_locals s) = SOME envs /\ wl_state_clock s = 0
     ==> IL2AUX_ss_stop (wl_Call (SOME (n,names,rh,l1,l2)) dest args handler) s
           (SOME wl_TimeOut)
           (wl_flush_state T
              (wl_state_stack_fupd (K [])
                 (wl_state_stack_max_fupd
                    (K (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs handler s))))
                    s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IL2AUX_ss_stop_def] THEN
  SIMP[wl_flush_state_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `handler:(num#(A)wl_prog#num#num)option`; `s:(A,C,FFI)wl_state`;
                  `xs:((A)stack_frame)list`] IL2AUX_push_env_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
                  `wl_push_env envs handler (s:(A,C,FFI)wl_state)`;
                  `CONS (HD (wl_state_stack (wl_push_env envs handler (s:(A,C,FFI)wl_state)))) xs`]
                 IL2AUX_call_env_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[wl_flush_state_def]);;

(* the Call clause at a swapped stack: the kit simplifier is slow on it,   *)
(* so it is evaluated by rewriting with the assumptions and the case        *)
(* rewrites                                                                  *)

let IL2AUX_CALL_UNFOLD_TAC : tactic =
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_vars_with_const] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

let IL2AUX_ss_call_stop = prove
 (`!n names rh l1 l2 dest args handler (s:(A,C,FFI)wl_state) vs args1 prog ss envs r
     (s2:(A,C,FFI)wl_state).
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (n,names,rh,l1,l2)) vs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     ~(domain (FST names) = {} \/ ~ALL_DISTINCT n) /\
     cut_envs names (wl_state_locals s) = SOME envs /\ ~(wl_state_clock s = 0) /\
     IL2AUX_stopr r /\
     IL2AUX_ss_stop prog (wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock s))) r s2
     ==> IL2AUX_ss_stop (wl_Call (SOME (n,names,rh,l1,l2)) dest args handler) s r s2`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` IL2AUX_res_cases) THEN
  REWRITE_TAC[IL2AUX_stopr_thms; IL2AUX_ss_stop_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
                  `envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `handler:(num#(A)wl_prog#num#num)option`; `s:(A,C,FFI)wl_state`;
                  `xs:((A)stack_frame)list`] IL2AUX_call_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `CONS (HD (wl_state_stack (wl_push_env envs handler (wl_dec_clock (s:(A,C,FFI)wl_state))))) xs`
    o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  IL2AUX_CALL_UNFOLD_TAC);;

let IL2AUX_s_key_eq_cons = prove
 (`!(f:(A)stack_frame) xs ys.
     s_key_eq (CONS f xs) ys <=> ?g zs. ys = CONS g zs /\ s_frame_key_eq f g /\ s_key_eq xs zs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  REWRITE_TAC[s_key_eq_def; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let IL2AUX_push_env_some_stack = prove
 (`!envs w h l1 l2 (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_push_env envs (SOME (w,h,l1,l2)) s) =
       CONS (StackFrame (wl_state_locals_size s) (toAList (FST envs))
               (FST (env_to_list (SND envs) (wl_state_permute s)))
               (SOME (wl_state_handler s,l1,l2)))
            (wl_state_stack s) /\
     wl_state_handler (wl_push_env envs (SOME (w,h,l1,l2)) s) = LENGTH (wl_state_stack s)`,
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN SIMP[]);;

let IL2AUX_pop_env_stack = prove
 (`!(t:(A,C,FFI)wl_state) t1 f rest.
     wl_pop_env t = SOME t1 /\ wl_state_stack t = CONS f rest ==> wl_state_stack t1 = rest`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `f:(A)stack_frame` (cases "stack_frame")) THEN
  MESON_TAC[IL2AUX_pop_env_handler]);;

(* the handler after the pop_env of the frame of a call *)

let IL2AUX_push_pop_handler = prove
 (`!envs b (s:(A,C,FFI)wl_state) (t:(A,C,FFI)wl_state) t1.
     s_key_eq (wl_state_stack (wl_push_env envs b s)) (wl_state_stack t) /\
     wl_state_handler t = wl_state_handler (wl_push_env envs b s) /\
     wl_pop_env t = SOME t1
     ==> wl_state_handler t1 = wl_state_handler s`,
  GEN_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; IL2AUX_push_env_none_stack;
              IL2AUX_push_env_some_stack; IL2AUX_s_key_eq_frame] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IL2AUX_pop_env_handler o
    CONJ (ASSUME `wl_pop_env (t:(A,C,FFI)wl_state) = SOME t1`)) THEN
  SIMP[] THEN ASM_MESON_TAC[]);;

(* the call part of a returning call: the callee returns normally and the   *)
(* frame of the call is popped                                               *)

let IL2AUX_call_pop_facts = prove
 (`!args1 ss envs handler (s:(A,C,FFI)wl_state) prog r2 (s2:(A,C,FFI)wl_state)
     (s1:(A,C,FFI)wl_state).
     IL2AUX_ss_norm prog (wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock s)))
       r2 s2 /\
     wl_pop_env s2 = SOME s1
     ==> s_key_eq (wl_state_stack s) (wl_state_stack s1) /\
         wl_state_handler s1 = wl_state_handler s /\
         !xs. s_val_eq (wl_state_stack s) xs
              ==> ?st2 st1.
                    wl_evaluate (prog, wl_call_env args1 ss (wl_push_env envs handler
                                   (wl_dec_clock (wl_state_stack_fupd (K xs) s)))) =
                      (r2, wl_state_stack_fupd (K st2) s2) /\
                    wl_pop_env (wl_state_stack_fupd (K st2) s2) =
                      SOME (wl_state_stack_fupd (K st1) s1) /\
                    s_val_eq (wl_state_stack s1) st1 /\ s_key_eq xs st1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IL2AUX_ss_norm_def] THEN STRIP_TAC THEN
  MP_TAC (REWRITE_RULE[s_val_eq_refl]
    (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
             `envs:((A)word_loc)spt#((A)word_loc)spt`;
             `handler:(num#(A)wl_prog#num#num)option`; `s:(A,C,FFI)wl_state`;
             `wl_state_stack (s:(A,C,FFI)wl_state)`] IL2AUX_call_stack_swap)) THEN
  ABBREV_TAC `fr = HD (wl_state_stack (wl_push_env envs handler
                      (wl_dec_clock (s:(A,C,FFI)wl_state))))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?f2 rest2. wl_state_stack (s2:(A,C,FFI)wl_state) = CONS f2 rest2 /\
                           s_frame_key_eq (fr:(A)stack_frame) f2 /\
                           s_key_eq (wl_state_stack (s:(A,C,FFI)wl_state)) rest2`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> IL2AUX_kind_name (concl th) = "s_key_eq" &&
      IL2AUX_has_tm `s2:(A,C,FFI)wl_state` th)) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) &&
        IL2AUX_kind_name (lhs (concl th)) = "wl_state_stack" &&
        IL2AUX_has_tm `fr:(A)stack_frame` th
      then REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[IL2AUX_s_key_eq_cons] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_stack (s1:(A,C,FFI)wl_state) = rest2` ASSUME_TAC THENL
   [MATCH_MP_TAC IL2AUX_pop_env_stack THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `wl_state_handler (s1:(A,C,FFI)wl_state) =
                  wl_state_handler (wl_dec_clock (s:(A,C,FFI)wl_state))`
      (fun th -> REWRITE_TAC[th; wl_dec_clock_const]) THEN
    MATCH_MP_TAC IL2AUX_push_pop_handler THEN
    MAP_EVERY EXISTS_TAC [`envs:((A)word_loc)spt#((A)word_loc)spt`;
      `handler:(num#(A)wl_prog#num#num)option`; `s2:(A,C,FFI)wl_state`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_call_env_const]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
                  `envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `handler:(num#(A)wl_prog#num#num)option`; `s:(A,C,FFI)wl_state`;
                  `xs:((A)stack_frame)list`] IL2AUX_call_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CONS (fr:(A)stack_frame) xs` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  MP_TAC (ISPECL [`fr:(A)stack_frame`; `f2:(A)stack_frame`; `xs:((A)stack_frame)list`;
                  `rest2:((A)stack_frame)list`; `st:((A)stack_frame)list`]
                 IL2AUX_stack_swap_head) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if IL2AUX_kind_name (concl th) = "s_val_eq" &&
      IL2AUX_has_tm `st:((A)stack_frame)list` th then MP_TAC th else failwith "") THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`st:((A)stack_frame)list`; `st1:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IL2AUX_pop_env_stack_swap THEN
  EXISTS_TAC `rest2:((A)stack_frame)list` THEN ASM_REWRITE_TAC[]);;

let IL2AUX_ss_call_result = prove
 (`!n names rh l1 l2 dest args handler (s:(A,C,FFI)wl_state) vs args1 prog ss envs x ys
     (s2:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) r (s3:(A,C,FFI)wl_state).
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (n,names,rh,l1,l2)) vs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     ~(domain (FST names) = {} \/ ~ALL_DISTINCT n) /\
     cut_envs names (wl_state_locals s) = SOME envs /\ ~(wl_state_clock s = 0) /\
     IL2AUX_ss_norm prog (wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock s)))
       (SOME (wl_Result x ys)) s2 /\
     ~(~(x = wl_Loc l1 l2) \/ ~(LENGTH ys = LENGTH n)) /\
     wl_pop_env s2 = SOME s1 /\
     domain (wl_state_locals s1) = domain (FST envs) UNION domain (SND envs) /\
     IL2AUX_ss rh (wl_set_vars n ys s1) r s3
     ==> IL2AUX_ss (wl_Call (SOME (n,names,rh,l1,l2)) dest args handler) s r s3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun nm -> if IL2AUX_kind_name (concl nm) = "IL2AUX_ss_norm" then
    FIRST_ASSUM(fun pop -> if IL2AUX_kind_name (lhs (concl pop)) = "wl_pop_env" then
      STRIP_ASSUME_TAC (MATCH_MP IL2AUX_call_pop_facts (CONJ nm pop)) else failwith "")
    else failwith "") THEN
  MATCH_MP_TAC IL2AUX_ss_aseq THEN
  MAP_EVERY EXISTS_TAC [`rh:(A)wl_prog`; `s1:(A,C,FFI)wl_state`;
                        `wl_set_vars n ys (s1:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[wl_set_vars_const] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  IL2AUX_PICK_TAC [`s1:(A,C,FFI)wl_state`; `prog:(A)wl_prog`] []
    (MP_TAC o SPEC `xs:((A)stack_frame)list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st2:((A)stack_frame)list` (X_CHOOSE_THEN `st1:((A)stack_frame)list`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `st1:((A)stack_frame)list` THEN ASM_REWRITE_TAC[] THEN
  IL2AUX_CALL_UNFOLD_TAC THEN SIMP[]);;

(* the call part of a returning call whose callee raises an exception that *)
(* the handler of the call catches                                          *)

let IL2AUX_call_exc_facts = prove
 (`!args1 ss envs hn h hl1 hl2 (s:(A,C,FFI)wl_state) prog x y (s2:(A,C,FFI)wl_state).
     IL2AUX_ss_exc prog
       (wl_call_env args1 ss (wl_push_env envs (SOME (hn,h,hl1,hl2)) (wl_dec_clock s))) x y s2
     ==> s_key_eq (wl_state_stack s) (wl_state_stack s2) /\
         wl_state_handler s2 = wl_state_handler s /\
         !xs. s_val_eq (wl_state_stack s) xs
              ==> ?st. wl_evaluate (prog, wl_call_env args1 ss (wl_push_env envs
                         (SOME (hn,h,hl1,hl2)) (wl_dec_clock (wl_state_stack_fupd (K xs) s)))) =
                         (SOME (wl_Exception x y), wl_state_stack_fupd (K st) s2) /\
                       s_val_eq (wl_state_stack s2) st /\ s_key_eq xs st`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `cs = wl_call_env args1 ss (wl_push_env envs (SOME (hn,h,hl1,hl2))
                     (wl_dec_clock (s:(A,C,FFI)wl_state)))` THEN
  SUBGOAL_THEN
   `wl_state_stack (cs:(A,C,FFI)wl_state) =
      CONS (StackFrame (wl_state_locals_size (s:(A,C,FFI)wl_state))
              (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt)))
              (FST (env_to_list (SND envs) (wl_state_permute s)))
              (SOME (wl_state_handler s,hl1,hl2))) (wl_state_stack s) /\
    wl_state_handler cs = LENGTH (wl_state_stack s)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cs" THEN
    REWRITE_TAC[wl_call_env_const; IL2AUX_push_env_some_stack; wl_dec_clock_const];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(f:(A)stack_frame) l. LENGTH l = LENGTH (wl_state_stack (s:(A,C,FFI)wl_state))
                  ==> LASTN (LENGTH (wl_state_stack s) + 1) (CONS f l) = CONS f l`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LASTN_LENGTH_cond THEN ASM_REWRITE_TAC[LENGTH] THEN
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IL2AUX_ss_exc_def] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    IL2AUX_kind_name (lhs (concl th)) = "LASTN" &&
    IL2AUX_has_tm `ls:((A)stack_frame)list` th)) THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[CONS_11; injectivity "stack_frame"; option_INJ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pair_CASE]) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[s_key_eq_sym] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
                  `envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `SOME (hn,h,hl1,hl2):(num#(A)wl_prog#num#num)option`; `s:(A,C,FFI)wl_state`;
                  `xs:((A)stack_frame)list`] IL2AUX_call_stack_swap) THEN
  ASM_REWRITE_TAC[IL2AUX_push_env_some_stack; wl_dec_clock_const; HD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (xs:((A)stack_frame)list) = LENGTH (wl_state_stack (s:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL [ASM_MESON_TAC[s_val_eq_length]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`CONS (StackFrame (wl_state_locals_size (s:(A,C,FFI)wl_state))
              (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt)))
              (FST (env_to_list (SND envs) (wl_state_permute s)))
              (SOME (wl_state_handler s,hl1:num,hl2:num))) xs`;
     `toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))`;
     `FST (env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
             (wl_state_permute (s:(A,C,FFI)wl_state)))`;
     `xs:((A)stack_frame)list`] o
    check (fun th -> is_forall (concl th) && IL2AUX_has_tm `prog:(A)wl_prog` th)) THEN
  ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)stack_frame)list` (X_CHOOSE_THEN `locs:((A)word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lss':(num#(A)word_loc)list = lss` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC LIST_EQ_MAP_PAIR THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `st:((A)stack_frame)list` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_ss_call_exc_h = prove
 (`!n names rh l1 l2 dest args (s:(A,C,FFI)wl_state) vs args1 prog ss envs hn h hl1 hl2 y
     (s2:(A,C,FFI)wl_state) r (s3:(A,C,FFI)wl_state).
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (n,names,rh,l1,l2)) vs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     ~(domain (FST names) = {} \/ ~ALL_DISTINCT n) /\
     cut_envs names (wl_state_locals s) = SOME envs /\ ~(wl_state_clock s = 0) /\
     IL2AUX_ss_exc prog
       (wl_call_env args1 ss (wl_push_env envs (SOME (hn,h,hl1,hl2)) (wl_dec_clock s)))
       (wl_Loc hl1 hl2) y s2 /\
     domain (wl_state_locals s2) = domain (FST envs) UNION domain (SND envs) /\
     IL2AUX_ss h (wl_set_var hn y s2) r s3
     ==> IL2AUX_ss (wl_Call (SOME (n,names,rh,l1,l2)) dest args (SOME (hn,h,hl1,hl2))) s r s3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_call_exc_facts o
    check (fun th -> IL2AUX_kind_name (concl th) = "IL2AUX_ss_exc")) THEN
  MATCH_MP_TAC IL2AUX_ss_aseq THEN
  MAP_EVERY EXISTS_TAC [`h:(A)wl_prog`; `s2:(A,C,FFI)wl_state`;
                        `wl_set_var hn y (s2:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[wl_set_var_const] THEN
  X_GEN_TAC `xs:((A)stack_frame)list` THEN DISCH_TAC THEN
  IL2AUX_PICK_TAC [`s2:(A,C,FFI)wl_state`; `prog:(A)wl_prog`] []
    (MP_TAC o SPEC `xs:((A)stack_frame)list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `st:((A)stack_frame)list` THEN ASM_REWRITE_TAC[] THEN
  IL2AUX_CALL_UNFOLD_TAC THEN SIMP[]);;

let IL2AUX_ss_call_exc_noh = prove
 (`!n names rh l1 l2 dest args (s:(A,C,FFI)wl_state) vs args1 prog ss envs x y
     (s2:(A,C,FFI)wl_state).
     wl_get_vars args s = SOME vs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (n,names,rh,l1,l2)) vs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     ~(domain (FST names) = {} \/ ~ALL_DISTINCT n) /\
     cut_envs names (wl_state_locals s) = SOME envs /\ ~(wl_state_clock s = 0) /\
     IL2AUX_ss_exc prog
       (wl_call_env args1 ss (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
          (wl_dec_clock s))) x y s2
     ==> IL2AUX_ss_exc (wl_Call (SOME (n,names,rh,l1,l2)) dest args NONE) s x y s2`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `cs = wl_call_env args1 ss (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
                     (wl_dec_clock (s:(A,C,FFI)wl_state)))` THEN
  ABBREV_TAC `fr = StackFrame (wl_state_locals_size (s:(A,C,FFI)wl_state))
                     (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt)))
                     (FST (env_to_list (SND envs) (wl_state_permute s)))
                     (NONE:(num#num#num)option)` THEN
  SUBGOAL_THEN `wl_state_stack (cs:(A,C,FFI)wl_state)
      = CONS fr (wl_state_stack (s:(A,C,FFI)wl_state)) /\
                wl_state_handler cs = wl_state_handler s` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cs"; "fr"] THEN
    REWRITE_TAC[wl_call_env_const; IL2AUX_push_env_none_stack; wl_dec_clock_const];
    ALL_TAC] THEN
  REWRITE_TAC[IL2AUX_ss_exc_def] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_handler (s:(A,C,FFI)wl_state) < LENGTH (wl_state_stack s)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> IL2AUX_kind_name (concl th) = "<")) THEN
    REWRITE_TAC[LENGTH; LT_SUC_LE; LE_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      IL2AUX_kind_name (lhs (concl th)) = "LASTN")) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (wl_state_stack (s:(A,C,FFI)wl_state)) + 1 =
                  LENGTH (CONS (fr:(A)stack_frame) (wl_state_stack s))` SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH; ADD1]; ALL_TAC] THEN
    REWRITE_TAC[LASTN_LENGTH_ID; CONS_11] THEN EXPAND_TAC "fr" THEN
    REWRITE_TAC[injectivity "stack_frame"; option_DISTINCT];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_eq (concl th) && IL2AUX_kind_name (lhs (concl th)) = "LASTN"
                           then REWRITE_RULE[MATCH_MP LASTN_TL
                                  (ASSUME `wl_state_handler (s:(A,C,FFI)wl_state) <
                                           LENGTH (wl_state_stack s)`)] th else th) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`e0:(num#(A)word_loc)list`; `e:(num#(A)word_loc)list`;
    `n':num#num#num`; `ls:((A)stack_frame)list`; `m:num option`;
    `lss:(num#(A)word_loc)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`xs:((A)stack_frame)list`; `e0':(num#(A)word_loc)list`;
                       `e':(num#(A)word_loc)list`; `ls':((A)stack_frame)list`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_handler (s:(A,C,FFI)wl_state) < LENGTH (xs:((A)stack_frame)list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[s_val_eq_length]; ALL_TAC] THEN
  MP_TAC (ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
                  `envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `NONE:(num#(A)wl_prog#num#num)option`; `s:(A,C,FFI)wl_state`;
                  `xs:((A)stack_frame)list`] IL2AUX_call_stack_swap) THEN
  ASM_REWRITE_TAC[IL2AUX_push_env_none_stack; wl_dec_clock_const; HD] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (fr:(A)stack_frame) xs`; `e0':(num#(A)word_loc)list`;
                                `e':(num#(A)word_loc)list`; `ls':((A)stack_frame)list`] o
    check (fun th -> is_forall (concl th) && IL2AUX_has_tm `prog:(A)wl_prog` th)) THEN
  ASM_SIMP_TAC[LASTN_TL] THEN
  TRY (ANTS_TAC THENL [REWRITE_TAC[s_val_eq_def; s_frame_val_eq_refl] THEN ASM_REWRITE_TAC[];
                       ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)stack_frame)list` (X_CHOOSE_THEN `locs:((A)word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`st:((A)stack_frame)list`; `locs:((A)word_loc)spt`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [IL2AUX_CALL_UNFOLD_TAC;
    EXISTS_TAC `lss':(num#(A)word_loc)list` THEN ASM_REWRITE_TAC[]]);;

let IL2AUX_ss_if2 = prove
 (`!cmp r1 ri c1 c2 (s:(A,C,FFI)wl_state) x y b r (s1:(A,C,FFI)wl_state).
     wl_get_var r1 s = SOME x /\ wl_get_var_imm ri s = SOME y /\
     wl_word_cmp cmp x y = SOME b /\ (b ==> IL2AUX_ss c1 s r s1) /\
     (~b ==> IL2AUX_ss c2 s r s1)
     ==> IL2AUX_ss (wl_If cmp r1 ri c1 c2) s r s1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IL2AUX_ss_if THEN
  MAP_EVERY EXISTS_TAC [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let IL2AUX_ss_cont_norm = prove
 (`!c (s:(A,C,FFI)wl_state) res (t:(A,C,FFI)wl_state).
     wl_cont_loop res /\ IL2AUX_ss c s res t ==> IL2AUX_ss_norm c s res t`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` IL2AUX_res_cases) THEN
  SIMP[wl_cont_loop_def; IL2AUX_ss_thms]);;

(* the induction on evaluate *)

let IL2AUX_SS_SPLIT_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[IL2AUX_ss_thms];;

(* the instances of the induction hypotheses at the evaluations of the branch *)

let IL2AUX_SS_IH_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) then failwith "" else
    let th = IL2AUX_fwd_r [] [] (map snd asl) ih in
    ASSUME_TAC (REWRITE_RULE[IL2AUX_ss_thms] th) g)) THEN
  IL2AUX_DROP_IHS_TAC;;

let IL2AUX_SS_LEMMAS_TAC (lems:thm list) : tactic =
  FIRST (map (fun lem -> MATCH_MP_TAC lem THEN
                         IL2AUX_EXISTS_ASM_RW_TAC [IL2AUX_ss_thms; IL2AUX_stopr_thms] THEN
                         NO_TAC) lems);;

let IL2AUX_SS_TRANSP_TAC : tactic =
  FIRST (map MATCH_ACCEPT_TAC (CONJUNCTS IL2AUX_ss_transp));;

let IL2AUX_SS_NONREC_TAC (lem:thm) : tactic =
  IL2AUX_SS_SPLIT_TAC THEN MATCH_MP_TAC lem THEN ASM_MESON_TAC[];;

let IL2AUX_SS_REC_TAC (lems:thm list) : tactic =
  IL2AUX_SS_SPLIT_TAC THEN IL2AUX_SS_IH_TAC THEN IL2AUX_SS_LEMMAS_TAC lems;;

let IL2AUX_CONT_NORM_TAC : tactic =
  TRY (FIRST_ASSUM(fun cl ->
    if IL2AUX_kind_name (concl cl) = "wl_cont_loop" then
      FIRST_ASSUM(fun ss -> if IL2AUX_kind_name (concl ss) = "IL2AUX_ss" then
        ASSUME_TAC (MATCH_MP IL2AUX_ss_cont_norm (CONJ cl ss)) else failwith "")
    else failwith ""));;

let IL2AUX_SS_LOOP_TAC : tactic =
  IL2AUX_SS_SPLIT_TAC THEN IL2AUX_SS_IH_TAC THEN IL2AUX_CONT_NORM_TAC THEN
  IL2AUX_SS_LEMMAS_TAC
    [REWRITE_RULE[IL2AUX_ss_thms] IL2AUX_ss_loop_timeout; IL2AUX_ss_loop_rec;
     REWRITE_RULE[IL2AUX_ss_thms] IL2AUX_ss_loop_break0; IL2AUX_ss_loop_exit];;

let IL2AUX_evaluate_stack_swap = prove
 (`!c (s:(A,C,FFI)wl_state) r s1. wl_evaluate (c,s) = (r,s1) ==> IL2AUX_ss c s r s1`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   ([IL2AUX_SS_TRANSP_TAC; IL2AUX_SS_NONREC_TAC IL2AUX_ss_alloc] @
    replicate IL2AUX_SS_TRANSP_TAC 9 @
    [IL2AUX_SS_REC_TAC [IL2AUX_ss_mt];
     IL2AUX_SS_REC_TAC [IL2AUX_ss_seq_none; IL2AUX_ss_seq_some];
     IL2AUX_SS_TRANSP_TAC; IL2AUX_SS_NONREC_TAC IL2AUX_ss_raise] @
    replicate IL2AUX_SS_TRANSP_TAC 2 @
    [IL2AUX_SS_REC_TAC [IL2AUX_ss_if2]; IL2AUX_SS_LOOP_TAC] @
    replicate IL2AUX_SS_TRANSP_TAC 6 @
    [IL2AUX_SS_REC_TAC
       [IL2AUX_ss_call_tail0; IL2AUX_ss_call_tail; IL2AUX_ss_call_ret0; IL2AUX_ss_call_result;
        IL2AUX_ss_call_exc_noh; IL2AUX_ss_call_exc_h; IL2AUX_ss_call_stop]]));;

(* Stack swap theorem for evaluate *)

let wl_evaluate_stack_swap = prove
 (CASE_TERM
  `!c (s:(A,C,FFI)wl_state).
     match wl_evaluate (c,s) with
       (SOME wl_Error,s1) -> T
     | (SOME (wl_FinalFFI e),s1) ->
         wl_state_stack s1 = [] /\ wl_state_locals s1 = LN /\
         (!xs. s_val_eq (wl_state_stack s) xs
               ==> wl_evaluate (c,wl_state_stack_fupd (K xs) s) = (SOME (wl_FinalFFI e),s1))
     | (SOME wl_TimeOut,s1) ->
         wl_state_stack s1 = [] /\ wl_state_locals s1 = LN /\
         (!xs. s_val_eq (wl_state_stack s) xs
               ==> wl_evaluate (c,wl_state_stack_fupd (K xs) s) = (SOME wl_TimeOut,s1))
     | (SOME NotEnoughSpace,s1) ->
         wl_state_stack s1 = [] /\ wl_state_locals s1 = LN /\
         (!xs. s_val_eq (wl_state_stack s) xs
               ==> wl_evaluate (c,wl_state_stack_fupd (K xs) s) = (SOME NotEnoughSpace,s1))
     | (SOME (wl_Exception x y),s1) ->
         wl_state_handler s < LENGTH (wl_state_stack s) /\
         (?e0 e n ls m lss.
            LASTN (wl_state_handler s + 1) (wl_state_stack s) =
              CONS (StackFrame m e0 e (SOME n)) ls /\
            m = wl_state_locals_size s1 /\
            (MAP FST e = MAP FST lss /\
             wl_state_locals s1 = sptree_union (fromAList lss) (fromAList e0)) /\
            s_key_eq (wl_state_stack s1) ls /\
            wl_state_handler s1 = (match n with (a,b,c) -> a) /\
            (!xs e0' e' ls'.
               LASTN (wl_state_handler s + 1) xs = CONS (StackFrame m e0' e' (SOME n)) ls' /\
               s_val_eq (wl_state_stack s) xs
               ==> ?st locs.
                     wl_evaluate (c,wl_state_stack_fupd (K xs) s) =
                       (SOME (wl_Exception x y),
                        wl_state_stack_fupd (K st)
                          (wl_state_handler_fupd (K (match n with (a,b,c) -> a))
                             (wl_state_locals_fupd (K locs) s1))) /\
                     (?lss'. MAP FST e' = MAP FST lss' /\
                             locs = sptree_union (fromAList lss') (fromAList e0') /\
                             MAP SND lss = MAP SND lss') /\
                     s_val_eq (wl_state_stack s1) st /\ s_key_eq ls' st))
     | (res,s1) ->
         s_key_eq (wl_state_stack s) (wl_state_stack s1) /\
         wl_state_handler s1 = wl_state_handler s /\
         (!xs. s_val_eq (wl_state_stack s) xs
               ==> ?st. wl_evaluate (c,wl_state_stack_fupd (K xs) s) =
                          (res,wl_state_stack_fupd (K st) s1) /\
                        s_val_eq (wl_state_stack s1) st /\ s_key_eq xs st)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`c:(A)wl_prog`; `s:(A,C,FFI)wl_state`] IL2AUX_evaluate_stack_swap) THEN
  SPEC_TAC(`wl_evaluate (c:(A)wl_prog,s:(A,C,FFI)wl_state)`,
           `p:((A)wl_result)option#(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN
  MAP_EVERY X_GEN_TAC [`r:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
  REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `r:((A)wl_result)option` IL2AUX_res_cases) THEN
  REWRITE_TAC[IL2AUX_ss_thms; IL2AUX_ss_stop_def; IL2AUX_ss_norm_def; IL2AUX_ss_exc_def] THEN
  SIMP[]);;

(* ------------------------------------------------------------------------- *)
(* permute_swap_lemma: the permutation oracle can be changed in the initial  *)
(* state so that the final state gets any given oracle.  The proof is by the *)
(* evaluate induction: push_env consumes the first permutation of the       *)
(* oracle, so the new initial oracle starts with the old first permutation  *)
(* and continues with the oracle that the call needs (IL2AUX_alloc_permute,  *)
(* IL2AUX_call_push_permute).                                                *)
(* ------------------------------------------------------------------------- *)

(* the programs that do not touch the permutation oracle *)

let IL2AUX_evaluate_permute_with_const = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !k. wl_evaluate (p, wl_state_permute_fupd (K k) s) =
              pair_CASE (wl_evaluate (p,s)) (\r s. (r, wl_state_permute_fupd (K k) s))`)
    (filter (fun c -> c <> "wl_Alloc") IL2AUX_nonrec_cons),
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  FIRST
   [REPEAT ((TOP_CASE_TAC ORELSE PAIRARG_TAC) THEN SIMP[PAIR_MAP_THM; I_THM]) THEN
    SIMP[PAIR_MAP_THM; I_THM] THEN NO_TAC;
    CASES_ON `wl_get_var n (s:(A,C,FFI)wl_state)` THEN SIMP[] THEN
    CASES_ON `wl_jump_exc (s:(A,C,FFI)wl_state)` THEN SIMP[] THEN
    REPEAT IL2AUX_SPLIT_PAIR_VARS_TAC THEN SIMP[]]);;

(* push_env consumes the first permutation of the oracle *)

let IL2AUX_push_env_permute = prove
 (`!envs b (s:(A,C,FFI)wl_state) q.
     q 0 = wl_state_permute s 0
     ==> wl_push_env envs b (wl_state_permute_fupd (K q) s) =
         wl_state_permute_fupd (K (\n. q (n + 1))) (wl_push_env envs b s)`,
  GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_alloc_permute = prove
 (`!w names (st:(A,C,FFI)wl_state) res rst q.
     wl_alloc w names st = (res,rst) /\ ~(res = SOME wl_Error) /\
     q 0 = wl_state_permute st 0
     ==> wl_alloc w names (wl_state_permute_fupd (K q) st) =
         (res, wl_state_permute_fupd (K (\n. q (n + 1))) rst)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_alloc" with Failure _ -> false)) THEN
  REWRITE_TAC[wl_alloc_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  REWRITE_TAC[wl_alloc_def] THEN SIMP[IL2AUX_push_env_permute] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_has_space_def]) THEN SIMP[wl_has_space_def] THEN
  ASM_MESON_TAC[]);;

let IL2AUX_alloc_permute2 = prove
 (`!w names (st:(A,C,FFI)wl_state) res rst perm.
     wl_alloc w names st = (res,rst) /\ ~(res = SOME wl_Error)
     ==> wl_alloc w names
           (wl_state_permute_fupd
              (K (\x. if x = 0 then wl_state_permute st 0 else perm (x - 1))) st) =
         (res, wl_state_permute_fupd (K perm) rst)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`w:A word`; `names:cutsets`; `st:(A,C,FFI)wl_state`;
                  `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`;
                  `\x. if x = 0 then wl_state_permute (st:(A,C,FFI)wl_state) 0 else perm (x - 1)`]
                 IL2AUX_alloc_permute) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `~(n + 1 = 0) /\ (n + 1) - 1 = n`]);;

(* the calls: dec_clock, push_env and call_env with a changed oracle *)

let IL2AUX_dec_clock_permute = prove
 (`!(s:(A,C,FFI)wl_state) q.
     wl_dec_clock (wl_state_permute_fupd (K q) s) = wl_state_permute_fupd (K q) (wl_dec_clock s)`,
  REWRITE_TAC[wl_dec_clock_def; wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_call_push_permute = prove
 (`!args1 ss envs b (s:(A,C,FFI)wl_state) pc.
     wl_call_env args1 ss
       (wl_push_env envs b
          (wl_dec_clock
             (wl_state_permute_fupd
                (K (\x. if x = 0 then wl_state_permute s 0 else pc (x - 1))) s))) =
     wl_state_permute_fupd (K pc) (wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IL2AUX_dec_clock_permute] THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `b:(num#(A)wl_prog#num#num)option`;
                  `wl_dec_clock (s:(A,C,FFI)wl_state)`;
                  `\x. if x = 0 then wl_state_permute (s:(A,C,FFI)wl_state) 0 else pc (x - 1)`]
                 IL2AUX_push_env_permute) THEN
  REWRITE_TAC[wl_dec_clock_const] THEN BETA_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(\n. if n + 1 = 0 then wl_state_permute (s:(A,C,FFI)wl_state) 0
                     else pc ((n + 1) - 1)) = (pc:num->num->num)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ARITH_RULE `~(n + 1 = 0) /\ (n + 1) - 1 = n`]; ALL_TAC] THEN
  REWRITE_TAC[wl_call_env_with_const]);;

let IL2AUX_push_env_permute_sm = prove
 (`!envs b (s:(A,C,FFI)wl_state) q.
     wl_state_stack_max (wl_push_env envs b (wl_state_permute_fupd (K q) s)) =
       wl_state_stack_max (wl_push_env envs b s) /\
     wl_stack_size (wl_state_stack (wl_push_env envs b (wl_state_permute_fupd (K q) s))) =
       wl_stack_size (wl_state_stack (wl_push_env envs b s))`,
  GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  SIMP[stack_size_eq2; stack_size_frame_def]);;

let IL2AUX_call_push_sm_permute = prove
 (`!args1 ss envs b (s:(A,C,FFI)wl_state) q.
     wl_state_stack_max
       (wl_call_env args1 ss (wl_push_env envs b (wl_state_permute_fupd (K q) s))) =
     wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs b s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_call_env_def] THEN SIMP[IL2AUX_push_env_permute_sm]);;

(* the cases of the induction; perm is the oracle wanted at the end *)

let IL2AUX_eval_state tm = snd (dest_pair (rand (lhs tm)));;

let IL2AUX_NONREC_PS_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN EXISTS_TAC `perm:num->num->num` THEN
  ASM_REWRITE_TAC[IL2AUX_evaluate_permute_with_const; pair_CASE];;

let IL2AUX_ALLOC_PS_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  (fun (asl,w as g) ->
     let ev = find (fun (_,th) -> IL2AUX_is_eval_eq (concl th)) asl in
     let s = IL2AUX_eval_state (concl (snd ev)) in
     let wit = vsubst [s, `s:(A,C,FFI)wl_state`]
       `\x. if x = 0 then wl_state_permute (s:(A,C,FFI)wl_state) 0 else perm (x - 1)` in
     EXISTS_TAC wit g) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  FIRST_ASSUM (fun th ->
    if (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_alloc"
        with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP IL2AUX_alloc_permute2
                       (CONJ th (ASSUME `~(res = SOME (wl_Error:(A)wl_result))`))]
    else failwith "");;

let IL2AUX_TICK_PS_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN EXISTS_TAC `perm:num->num->num` THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[wl_dec_clock_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[wl_dec_clock_def];;

(* the instances at perm of the induction hypotheses *)

let IL2AUX_PS_IH_TAC (perm:term) : tactic =
  ASSUM_LIST (fun ths ->
    let ihs = filter (fun th -> is_forall (concl th) || is_imp (concl th)) ths in
    let insts = mapfilter (fun ih -> SPEC perm (IL2AUX_fwd ths ih)) ihs in
    MAP_EVERY (fun th -> MP_TAC th) insts);;

let IL2AUX_MT_PS_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `perm:num->num->num` THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  IL2AUX_PS_IH_TAC `perm:num->num->num` THEN
  DISCH_THEN(X_CHOOSE_TAC `perm':num->num->num`) THEN
  EXISTS_TAC `perm':num->num->num` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[];;

(* the instance at perm of the hypothesis for the program prog, with the   *)
(* chosen oracle called v                                                    *)

let IL2AUX_PS_IH_FOR_TAC (prog:term) (perm:term) (v:string) : tactic =
  ASSUM_LIST (fun ths ->
    let ihs = filter (fun th -> is_forall (concl th) || is_imp (concl th)) ths in
    let insts = mapfilter (fun ih ->
        let th = SPEC perm (IL2AUX_fwd ths ih) in
        let _,bod = dest_exists (concl th) in
        let p' = fst (dest_pair (rand (lhs bod))) in
        if p' = prog then th else failwith "") ihs in
    X_CHOOSE_TAC (mk_var(v, `:num->num->num`)) (hd insts));;

let IL2AUX_PS_SPLIT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `perm:num->num->num` THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`)));;

let IL2AUX_PS_FIN_TAC (v:string) : tactic =
  EXISTS_TAC (mk_var(v, `:num->num->num`)) THEN
  RULE_ASSUM_TAC (fun th -> if IL2AUX_is_eval_eq (concl th)
                            then CAKE_SIMP_RULE [wl_dec_clock_def; wl_STOP_def] th else th) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[wl_dec_clock_def; wl_STOP_def] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP[wl_dec_clock_def; wl_STOP_def];;

let IL2AUX_SEQ_PS_TAC : tactic =
  IL2AUX_PS_SPLIT_TAC THEN
  FIRST [IL2AUX_PS_IH_FOR_TAC `c2:(A)wl_prog` `perm:num->num->num` "p2" THEN
         IL2AUX_PS_IH_FOR_TAC `c1:(A)wl_prog` `p2:num->num->num` "p1" THEN
         IL2AUX_PS_FIN_TAC "p1" THEN NO_TAC;
         IL2AUX_PS_IH_FOR_TAC `c1:(A)wl_prog` `perm:num->num->num` "p1" THEN
         IL2AUX_PS_FIN_TAC "p1"];;

let IL2AUX_IF_PS_TAC : tactic =
  IL2AUX_PS_SPLIT_TAC THEN
  FIRST [IL2AUX_PS_IH_FOR_TAC `c1:(A)wl_prog` `perm:num->num->num` "p1";
         IL2AUX_PS_IH_FOR_TAC `c2:(A)wl_prog` `perm:num->num->num` "p1"] THEN
  IL2AUX_PS_FIN_TAC "p1";;

(* ~(r = SOME wl_Error) for the results r of the evaluations of the branch *)

let IL2AUX_NOERR_TAC : tactic =
  ASSUM_LIST (fun ths ->
    let evs = filter (fun th -> IL2AUX_is_eval_eq (concl th)) ths in
    MAP_EVERY (fun th ->
      let r = fst (dest_pair (rhs (concl th))) in
      if not (is_var r) then ALL_TAC else
      TRY (SUBGOAL_THEN (vsubst [r, `r0:((A)wl_result)option`]
                           `~(r0 = SOME (wl_Error:(A)wl_result))`)
             ASSUME_TAC THENL
           [DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
            FS[wl_cont_loop_def; wl_exit_loop_def] THEN NO_TAC; ALL_TAC])) evs);;

let IL2AUX_LOOP_PS_TAC : tactic =
  IL2AUX_PS_SPLIT_TAC THEN IL2AUX_NOERR_TAC THEN
  FIRST [IL2AUX_PS_IH_FOR_TAC `wl_STOP (wl_Loop names c exit_names):(A)wl_prog`
           `perm:num->num->num` "p2" THEN
         IL2AUX_PS_IH_FOR_TAC `c:(A)wl_prog` `p2:num->num->num` "p1" THEN
         IL2AUX_PS_FIN_TAC "p1" THEN NO_TAC;
         IL2AUX_PS_IH_FOR_TAC `c:(A)wl_prog` `perm:num->num->num` "p1" THEN
         IL2AUX_PS_FIN_TAC "p1"];;

(* Call: the instance at perm of the hypothesis whose state is made by the  *)
(* function h0 (wl_call_env for the callee, wl_set_vars and wl_set_var for  *)
(* the handlers)                                                             *)

let IL2AUX_PS_IH_ST_TAC (h0:string) (perm:term) (v:string) : tactic =
  ASSUM_LIST (fun ths ->
    let ihs = filter (fun th -> is_forall (concl th) || is_imp (concl th)) ths in
    let insts = mapfilter (fun ih ->
        let th = SPEC perm (IL2AUX_fwd_r [] [] ths ih) in
        let _,bod = dest_exists (concl th) in
        let st = rand (snd (dest_pair (rand (lhs bod)))) in
        if fst (dest_const (fst (strip_comb st))) = h0 then th else failwith "") ihs in
    X_CHOOSE_TAC (mk_var(v, `:num->num->num`)) (hd insts));;

(* the initial oracle of a returning call whose callee needs the oracle v *)

let IL2AUX_call_wit (v:string) : term -> term = fun w ->
  let _,bod = dest_exists w in
  let s = rand (snd (dest_pair (rand (lhs bod)))) in
  vsubst [s, `s:(A,C,FFI)wl_state`; mk_var(v, `:num->num->num`), `pc:num->num->num`]
    `\x. if x = 0 then wl_state_permute (s:(A,C,FFI)wl_state) 0 else pc (x - 1)`;;

let IL2AUX_CALL_FIN_TAC (wit:term) : tactic =
  EXISTS_TAC wit THEN IL2AUX_DROP_IHS_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[IL2AUX_call_push_permute] THEN
  REWRITE_TAC[IL2AUX_dec_clock_permute; IL2AUX_call_push_sm_permute] THEN
  SIMP[] THEN ASM_REWRITE_TAC[pair_CASE] THEN SIMP[];;

let IL2AUX_CALL_RET_FIN_TAC (v:string) : tactic = fun (asl,w as g) ->
  IL2AUX_CALL_FIN_TAC (IL2AUX_call_wit v w) g;;

let IL2AUX_is_clock0 th =
  let c = concl th in
  is_eq c && rhs c = `0` &&
  (try fst(dest_const(rator(lhs c))) = "wl_state_clock" with Failure _ -> false);;

let IL2AUX_TAIL_CHECK : tactic = fun (asl,w as g) ->
  let _,bod = dest_exists w in
  let prog = fst (dest_pair (rand (lhs bod))) in
  let ret = hd (snd (strip_comb prog)) in
  if is_const ret && fst (dest_const ret) = "NONE" then ALL_TAC g
  else failwith "IL2AUX_TAIL_CHECK";;

let IL2AUX_CALL_PS_TAC : tactic =
  IL2AUX_PS_SPLIT_TAC THEN IL2AUX_NOERR_TAC THEN
  FIRST [FIRST_ASSUM (fun th -> if IL2AUX_is_clock0 th then ALL_TAC else failwith "") THEN
         IL2AUX_CALL_FIN_TAC `perm:num->num->num` THEN NO_TAC;
         IL2AUX_PS_IH_ST_TAC "wl_set_vars" `perm:num->num->num` "p2" THEN
         IL2AUX_PS_IH_ST_TAC "wl_call_env" `p2:num->num->num` "p1" THEN
         IL2AUX_CALL_RET_FIN_TAC "p1" THEN NO_TAC;
         IL2AUX_PS_IH_ST_TAC "wl_set_var" `perm:num->num->num` "p2" THEN
         IL2AUX_PS_IH_ST_TAC "wl_call_env" `p2:num->num->num` "p1" THEN
         IL2AUX_CALL_RET_FIN_TAC "p1" THEN NO_TAC;
         IL2AUX_PS_IH_ST_TAC "wl_call_env" `perm:num->num->num` "p1" THEN
         FIRST [IL2AUX_TAIL_CHECK THEN IL2AUX_CALL_FIN_TAC `p1:num->num->num` THEN NO_TAC;
                IL2AUX_CALL_RET_FIN_TAC "p1" THEN NO_TAC]];;

let IL2AUX_permute_swap = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst.
     wl_evaluate (prog,st) = (res,rst) /\ ~(res = SOME wl_Error)
     ==> !perm. ?perm'. wl_evaluate (prog, wl_state_permute_fupd (K perm') st) =
                        (res, wl_state_permute_fupd (K perm) rst)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   ([IL2AUX_NONREC_PS_TAC; IL2AUX_ALLOC_PS_TAC] @ replicate IL2AUX_NONREC_PS_TAC 8 @
    [IL2AUX_TICK_PS_TAC; IL2AUX_MT_PS_TAC; IL2AUX_SEQ_PS_TAC] @
    replicate IL2AUX_NONREC_PS_TAC 4 @ [IL2AUX_IF_PS_TAC; IL2AUX_LOOP_PS_TAC] @
    replicate IL2AUX_NONREC_PS_TAC 6 @ [IL2AUX_CALL_PS_TAC]));;

let permute_swap_lemma = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) perm.
     let (res,rst) = wl_evaluate (prog,st) in
       ~(res = SOME wl_Error)
       ==> ?perm'. wl_evaluate (prog,wl_state_permute_fupd (K perm') st) =
                   (res,wl_state_permute_fupd (K perm) rst)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`] IL2AUX_permute_swap) THEN
  SPEC_TAC(`wl_evaluate (prog:(A)wl_prog,st:(A,C,FFI)wl_state)`,
           `p:((A)wl_result)option#(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Effect of extra locals (locals_rel)                                       *)
(* ------------------------------------------------------------------------- *)

let locals_rel_def = cake_def
  `locals_rel temp (s:((A)word_loc)spt) t <=> (!x. x < temp ==> lookup x s = lookup x t)`;;

let the_words_EVERY_IS_SOME = prove
 (`!ls x. the_words ls = SOME (x:(A word)list) ==> ALL IS_SOME ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[the_words_def; ALL] THEN GEN_TAC THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; IS_SOME_DEF] THEN
  ASM_MESON_TAC[]);;

let locals_rel_get_vars = prove
 (`!ls vs.
     wl_get_vars ls (st:(A,C,FFI)wl_state) = SOME vs /\
     ALL (\x. x < temp) ls /\
     locals_rel temp (wl_state_locals st) loc
     ==> wl_get_vars ls (wl_state_locals_fupd (K loc) st) = SOME vs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!l. ALL (\x. x < temp) l
                    ==> wl_get_vars l (wl_state_locals_fupd (K loc) st) =
                        wl_get_vars l (st:(A,C,FFI)wl_state)`
    (fun th -> ASM_SIMP_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; ALL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[wl_get_var_def] THEN SIMP[] THEN
  SUBGOAL_THEN `lookup h (loc:((A)word_loc)spt) = lookup h (wl_state_locals (st:(A,C,FFI)wl_state))`
    SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[locals_rel_def]) THEN ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let locals_rel_alist_insert = prove
 (`!ls vs s t.
     locals_rel temp s t /\ ALL (\x. x < temp) ls
     ==> locals_rel temp (alist_insert ls vs s) (alist_insert ls (vs:((A)word_loc)list) t)`,
  MATCH_MP_TAC alist_insert_ind THEN REWRITE_TAC[alist_insert_def; ALL] THEN
  REWRITE_TAC[locals_rel_def; lookup_insert] THEN MESON_TAC[]);;

let locals_rel_get_var = prove
 (`r < temp /\ wl_get_var r (st:(A,C,FFI)wl_state) = SOME x /\
   locals_rel temp (wl_state_locals st) loc
   ==> wl_get_var r (wl_state_locals_fupd (K loc) st) = SOME x`,
  REWRITE_TAC[wl_get_var_def; locals_rel_def] THEN SIMP[] THEN MESON_TAC[]);;

let locals_rel_get_var_simp = prove
 (`r < temp /\ locals_rel temp (wl_state_locals (st:(A,C,FFI)wl_state)) loc
   ==> wl_get_var r (wl_state_locals_fupd (K loc) st) = wl_get_var r st`,
  REWRITE_TAC[wl_get_var_def; locals_rel_def] THEN SIMP[] THEN MESON_TAC[]);;

let locals_rel_get_vars_simp = prove
 (`ALL (\x. x < temp) l /\ locals_rel temp (wl_state_locals (st:(A,C,FFI)wl_state)) loc
   ==> wl_get_vars l (wl_state_locals_fupd (K loc) st) = wl_get_vars l st`,
  SPEC_TAC(`l:num list`,`l:num list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[wl_get_vars_def; ALL] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `wl_get_var h (wl_state_locals_fupd (K loc) st) =
                wl_get_var h (st:(A,C,FFI)wl_state)` SUBST1_TAC THENL
   [MATCH_MP_TAC (GEN_ALL locals_rel_get_var_simp) THEN EXISTS_TAC `temp:num` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let locals_rel_get_var_imm = prove
 (`every_var_imm (\x. x < temp) r /\ wl_get_var_imm r (st:(A,C,FFI)wl_state) = SOME x /\
   locals_rel temp (wl_state_locals st) loc
   ==> wl_get_var_imm r (wl_state_locals_fupd (K loc) st) = SOME x`,
  STRUCT_CASES_TAC (ISPEC `r:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[wl_get_var_imm_def; every_var_imm_def] THEN
  MESON_TAC[locals_rel_get_var]);;

let locals_rel_get_var_imm_simp = prove
 (`every_var_imm (\x. x < temp) r /\ locals_rel temp (wl_state_locals (st:(A,C,FFI)wl_state)) loc
   ==> wl_get_var_imm r (wl_state_locals_fupd (K loc) st) = wl_get_var_imm r st`,
  STRUCT_CASES_TAC (ISPEC `r:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[wl_get_var_imm_def; every_var_imm_def] THEN
  MESON_TAC[locals_rel_get_var_simp]);;

(* the equation of locals_rel_word_exp_simp, for locals_rel_word_exp *)

let IL2AUX_locals_rel_word_exp_eq = prove
 (`!s exp.
     every_var_exp (\x. x < temp) exp /\ locals_rel temp (wl_state_locals s) loc
     ==> wl_word_exp (wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state)) exp =
         wl_word_exp s exp`,
  MATCH_MP_TAC wl_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[every_var_exp_def] THEN ONCE_REWRITE_TAC[wl_word_exp_def] THEN
  REPEAT STRIP_TAC THEN
  TRY (MATCH_MP_TAC (GEN_ALL locals_rel_get_var_simp) THEN EXISTS_TAC `temp:num` THEN
       ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_SIMP_TAC[] THEN SIMP[] THEN
  SUBGOAL_THEN `MAP (wl_word_exp (wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state))) wexps =
                MAP (wl_word_exp s) wexps` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `a:(A)wl_exp` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)wl_exp` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ALL (every_var_exp (\x. x < temp)) (wexps:((A)wl_exp)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

let locals_rel_word_exp = prove
 (`!s exp w.
     every_var_exp (\x. x < temp) exp /\ wl_word_exp s exp = SOME w /\
     locals_rel temp (wl_state_locals s) loc
     ==> wl_word_exp (wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state)) exp = SOME w`,
  MESON_TAC[IL2AUX_locals_rel_word_exp_eq]);;

let locals_rel_word_exp_simp = prove
 (`!s exp.
     every_var_exp (\x. x < temp) exp /\ locals_rel temp (wl_state_locals s) loc
     ==> wl_word_exp (wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state)) exp =
         wl_word_exp s exp`,
  ACCEPT_TAC IL2AUX_locals_rel_word_exp_eq);;

(* HOL4 [local] *)
let locals_rel_set_var = prove
 (`!n s t. locals_rel temp s t
           ==> locals_rel temp (insert n (v:(A)word_loc) s) (insert n v t)`,
  REWRITE_TAC[locals_rel_def; lookup_insert] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let locals_rel_delete = prove
 (`!n s t. locals_rel temp (s:((A)word_loc)spt) t
           ==> locals_rel temp (delete n s) (delete n t)`,
  REWRITE_TAC[locals_rel_def; lookup_delete] THEN MESON_TAC[]);;

(* cut_names of a name set with keys below temp *)

let IL2AUX_locals_rel_cut_names = prove
 (`!temp loc loc' (ns:(B)spt) (e:((A)word_loc)spt).
     locals_rel temp loc loc' /\ ALL (\x. x < temp) (MAP FST (toAList ns)) /\
     cut_names ns loc = SOME e
     ==> cut_names ns loc' = SOME e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; locals_rel_def] THEN
  REWRITE_TAC[GSYM ALL_MEM; toAList_domain] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k IN domain (ns:(B)spt) ==> lookup k loc = lookup k (loc':((A)word_loc)spt)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `domain (ns:(B)spt) SUBSET domain (loc':((A)word_loc)spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `domain (ns:(B)spt) SUBSET domain (loc:((A)word_loc)spt)` THEN
    REWRITE_TAC[SUBSET] THEN REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[domain_lookup];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC (ISPECL [`sptree_inter (loc':((A)word_loc)spt) (ns:(B)spt)`;
                  `sptree_inter (loc:((A)word_loc)spt) (ns:(B)spt)`] spt_eq_thm) THEN
  REWRITE_TAC[wf_inter] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_inter_alt] THEN ASM_MESON_TAC[]);;

let locals_rel_cut_envs = prove
 (`locals_rel temp loc loc' /\ every_name (\x. x < temp) names /\
   cut_envs names loc = SOME (x:((A)word_loc)spt#((A)word_loc)spt)
   ==> cut_envs names loc' = SOME x`,
  REWRITE_TAC[cut_envs_def; every_name_def] THEN
  MP_TAC (ISPEC `names:cutsets` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num_set` (X_CHOOSE_THEN `n2:num_set` SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `cut_names (n1:num_set) (loc':((A)word_loc)spt) = cut_names n1 loc /\
                cut_names (n2:num_set) (loc':((A)word_loc)spt) = cut_names n2 loc`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[IL2AUX_locals_rel_cut_names]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let locals_rel_cut_env = prove
 (`locals_rel temp loc loc' /\ every_name (\x. x < temp) names /\
   wl_cut_env names loc = SOME (x:((A)word_loc)spt)
   ==> wl_cut_env names loc' = SOME x`,
  REWRITE_TAC[wl_cut_env_def] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `cut_envs names (loc':((A)word_loc)spt)
      = SOME (x',y)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC (GEN_ALL locals_rel_cut_envs) THEN ASM_MESON_TAC[]; SIMP[]]);;

(* locals_rel_evaluate_thm *)

(* the locals_rel lemmas as conditional rewrites for a fixed locals_rel *)

let IL2AUX_lr_get_var = prove
 (`!temp (st:(A,C,FFI)wl_state) loc. locals_rel temp (wl_state_locals st) loc
     ==> !r. r < temp ==> wl_get_var r (wl_state_locals_fupd (K loc) st) = wl_get_var r st`,
  MESON_TAC[locals_rel_get_var_simp]);;

let IL2AUX_lr_get_vars = prove
 (`!temp (st:(A,C,FFI)wl_state) loc. locals_rel temp (wl_state_locals st) loc
     ==> !l. ALL (\x. x < temp) l
             ==> wl_get_vars l (wl_state_locals_fupd (K loc) st) = wl_get_vars l st`,
  MESON_TAC[locals_rel_get_vars_simp]);;

let IL2AUX_lr_get_var_imm = prove
 (`!temp (st:(A,C,FFI)wl_state) loc. locals_rel temp (wl_state_locals st) loc
     ==> !r. every_var_imm (\x. x < temp) r
             ==> wl_get_var_imm r (wl_state_locals_fupd (K loc) st) = wl_get_var_imm r st`,
  MESON_TAC[locals_rel_get_var_imm_simp]);;

let IL2AUX_lr_word_exp = prove
 (`!temp (st:(A,C,FFI)wl_state) loc. locals_rel temp (wl_state_locals st) loc
     ==> !e. every_var_exp (\x. x < temp) e
             ==> wl_word_exp (wl_state_locals_fupd (K loc) st) e = wl_word_exp st e`,
  MESON_TAC[locals_rel_word_exp_simp]);;

let IL2AUX_lr_cut_envs = prove
 (`!temp (loc:((A)word_loc)spt) loc'. locals_rel temp loc loc'
     ==> !names x. every_name (\x. x < temp) names /\ cut_envs names loc = SOME x
                   ==> cut_envs names loc' = SOME x`,
  MESON_TAC[locals_rel_cut_envs]);;

let IL2AUX_lr_cut_env = prove
 (`!temp (loc:((A)word_loc)spt) loc'. locals_rel temp loc loc'
     ==> !names x. every_name (\x. x < temp) names /\ wl_cut_env names loc = SOME x
                   ==> wl_cut_env names loc' = SOME x`,
  MESON_TAC[locals_rel_cut_env]);;

let IL2AUX_is_lr tm =
  try fst(dest_const(fst(strip_comb tm))) = "locals_rel" with Failure _ -> false;;

(* the cut_envs and cut_env facts for the related locals *)

let IL2AUX_LR_CUT_FACTS_TAC : tactic =
  ASSUM_LIST (fun ths ->
    let hd_is n th = try fst(dest_const(fst(strip_comb(concl th)))) = n
                     with Failure _ -> false in
    let lrs = filter (hd_is "locals_rel") ths in
    let ens = filter (hd_is "every_name") ths in
    let cuts = filter (fun th ->
      try let f = fst(dest_const(fst(strip_comb(lhs(concl th))))) in
          f = "cut_envs" || f = "wl_cut_env"
      with Failure _ -> false) ths in
    let facts = flat (map (fun lr -> flat (map (fun en -> mapfilter (fun c ->
        let a = CONJ lr (CONJ en c) in
        try MATCH_MP locals_rel_cut_envs a with Failure _ ->
        MATCH_MP locals_rel_cut_env a) cuts) ens)) lrs) in
    MAP_EVERY ASSUME_TAC facts);;

let IL2AUX_LR_RWS_TAC : tactic =
  FIRST_ASSUM (fun lr ->
    if not (IL2AUX_is_lr (concl lr)) then failwith "" else
    let rws = map (fun l -> MATCH_MP l lr)
                [IL2AUX_lr_get_var; IL2AUX_lr_get_vars; IL2AUX_lr_get_var_imm;
                 IL2AUX_lr_word_exp] in
    let cuts = map (fun l -> MATCH_MP l lr) [IL2AUX_lr_cut_envs; IL2AUX_lr_cut_env] in
    MAP_EVERY ASSUME_TAC cuts THEN IL2AUX_LR_CUT_FACTS_TAC THEN
    SIMP (rws @ [every_var_exp_def; every_var_imm_def; every_name_def; ALL;
                 wl_dec_clock_def]));;

let IL2AUX_is_every_var tm =
  try fst(dest_const(fst(strip_comb tm))) = "wl_every_var" with Failure _ -> false;;

let IL2AUX_LR_WITNESS_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let c1 = hd (conjuncts bod) in
  let l,r = dest_eq c1 in
  let l = if is_comb l && (try fst(dest_const(rator l)) = "SOME" with Failure _ -> false)
          then rand l else l in
  let lst = if is_pair l then snd (dest_pair l)
            else if (try fst(dest_type(type_of l)) = "prod" with Failure _ -> false)
            then mk_icomb(mk_const("SND",[]), l)
            else l in
  EXISTS_TAC (mk_icomb(mk_const("wl_state_locals",[]), lst)) g;;

let IL2AUX_locals_rel_refl = prove
 (`!temp (l:((A)word_loc)spt). locals_rel temp l l`,
  REWRITE_TAC[locals_rel_def]);;

let IL2AUX_LR_REL_TAC : tactic =
  REWRITE_TAC[IL2AUX_locals_rel_refl] THEN
  REPEAT ((MATCH_MP_TAC locals_rel_set_var ORELSE MATCH_MP_TAC locals_rel_delete ORELSE
           MATCH_MP_TAC locals_rel_alist_insert) THEN TRY CONJ_TAC) THEN
  ASM_REWRITE_TAC[IL2AUX_locals_rel_refl];;

let IL2AUX_jump_exc_locals = prove
 (`!l (s:(A,C,FFI)wl_state). wl_jump_exc (wl_state_locals_fupd (K l) s) = wl_jump_exc s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]));;

let IL2AUX_alloc_locals = prove
 (`!w names (s:(A,C,FFI)wl_state) loc.
     cut_envs names loc = cut_envs names (wl_state_locals s)
     ==> wl_alloc w names (wl_state_locals_fupd (K loc) s) = wl_alloc w names s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wl_alloc_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]));;

let IL2AUX_alloc_lr = prove
 (`!temp (s:(A,C,FFI)wl_state) loc. locals_rel temp (wl_state_locals s) loc
     ==> !w names res rst. wl_alloc w names s = (res,rst) ==> ~(res = SOME wl_Error) ==>
         every_name (\x. x < temp) names
         ==> wl_alloc w names (wl_state_locals_fupd (K loc) s) = (res,rst)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `cut_envs (names:cutsets) (wl_state_locals (s:(A,C,FFI)wl_state))` THENL
   [REWRITE_TAC[wl_alloc_def] THEN ASM_REWRITE_TAC[option_CASE; PAIR_EQ] THEN MESON_TAC[];
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)))) THEN
    MATCH_MP_TAC IL2AUX_alloc_locals THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (GEN_ALL locals_rel_cut_envs) THEN ASM_MESON_TAC[]]);;

let IL2AUX_LR_ALLOC_TAC : tactic =
  FIRST_ASSUM (fun lr ->
    if not (IL2AUX_is_lr (concl lr)) then failwith "" else
    let th1 = MATCH_MP IL2AUX_alloc_lr lr in
    FIRST_ASSUM (fun al -> MP_TAC (MATCH_MP th1 al))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let IL2AUX_IH_FWD_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) then failwith "" else
    let th = IL2AUX_fwd (map snd asl) (REWRITE_RULE IL2AUX_dec_rws ih) in
    STRIP_ASSUME_TAC (CAKE_SIMP_RULE [] th) g));;

let IL2AUX_toAList_LN = prove
 (`toAList (LN:A spt) = []`,
  REWRITE_TAC[toAList_def; SPTAUX_foldi_thm]);;

let IL2AUX_loop_lr = prove
 (`!names c exit_names (s:(A,C,FFI)wl_state) res rst temp loc.
     wl_evaluate (wl_Loop names c exit_names, s) = (res,rst) /\ ~(res = SOME wl_Error) /\
     ALL (\x. x < temp) (MAP FST (toAList names)) /\ locals_rel temp (wl_state_locals s) loc
     ==> wl_evaluate (wl_Loop names c exit_names, wl_state_locals_fupd (K loc) s) = (res,rst)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[option_CASE] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wl_cut_state (names,LN) (wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state)) =
                SOME a` (fun th -> ASM_REWRITE_TAC[th; option_CASE]) THEN
  UNDISCH_TAC `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state) = SOME a` THEN
  REWRITE_TAC[wl_cut_state_def] THEN SIMP[] THEN
  CASES_ON `wl_cut_env (names,LN) (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `wl_cut_env (names,LN) (loc:((A)word_loc)spt) = SOME a'`
    (fun th -> REWRITE_TAC[th; option_CASE] THEN SIMP[]) THEN
  MATCH_MP_TAC (GEN_ALL locals_rel_cut_env) THEN
  MAP_EVERY EXISTS_TAC [`temp:num`; `wl_state_locals (s:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[every_name_def; IL2AUX_toAList_LN; MAP; ALL]);;

let IL2AUX_LR_FIN_TAC : tactic =
  TRY (IL2AUX_LR_WITNESS_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
  REPEAT CONJ_TAC THEN
  TRY (REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN SIMP[wl_set_var_def; wl_set_vars_def; wl_unset_var_def] THEN
  IL2AUX_LR_REL_TAC THEN REPEAT TOP_CASE_TAC THEN REWRITE_TAC[IL2AUX_locals_rel_refl];;

let IL2AUX_LR_LOOP_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[wl_every_var_def; ALL] o
                 check (IL2AUX_is_every_var o concl)) THEN
  ASSUM_LIST (fun ths -> ASSUME_TAC (IL2AUX_fwd ths IL2AUX_loop_lr)) THEN
  ASM_REWRITE_TAC[] THEN IL2AUX_LR_FIN_TAC;;

let IL2AUX_ALL_REGIMM_CASES_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> try fst(dest_type(type_of v)) = "reg_imm"
                            with Failure _ -> false) (frees w) in
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "reg_imm"))) vs g;;

let IL2AUX_INST_LR_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[every_var_inst_def; every_var_imm_def] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_inst" with Failure _ -> false)) THEN
  REWRITE_TAC[wl_inst_def; wl_assign_def] THEN SIMP[] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [option_INJ; option_DISTINCT; PAIR_EQ; LET_DEF;
                                       LET_END_DEF]) THEN
  DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  TRY (FIRST_X_ASSUM (fun th -> if is_cond (concl th) then MP_TAC th else failwith "") THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  IL2AUX_FACTS_TAC [mem_store_const] THEN
  REWRITE_TAC[wl_inst_def; wl_assign_def] THEN IL2AUX_LR_RWS_TAC THEN
  IL2AUX_LR_FIN_TAC;;

let IL2AUX_share_inst_lr = prove
 (CASE_TERM
  `!op v ad (s:(A,C,FFI)wl_state) (res:((A)wl_result)option) rst temp loc.
     share_inst op v ad s = (res,rst) /\ ~(res = SOME wl_Error) /\ v < temp /\
     locals_rel temp (wl_state_locals s) loc
     ==> ?loc'. share_inst op v ad (wl_state_locals_fupd (K loc) s) =
                (res, wl_state_locals_fupd (K loc') rst) /\
                (match res with
                   NONE -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Break _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Continue _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME _ -> wl_state_locals rst = loc')`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "share_inst"
    with Failure _ -> false)) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
              wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
              wl_sh_mem_store_byte_def; wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  IL2AUX_LR_RWS_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC ORELSE IL2AUX_CALL_FFI_CASES_TAC) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SIMP[] THEN IL2AUX_LR_FIN_TAC);;

let IL2AUX_LR_SPLIT_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[wl_every_var_def; ALL] o
                 check (IL2AUX_is_every_var o concl)) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else REWRITE_RULE IL2AUX_dec_rws (CASE_REWRITE_RULE [] th)) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let IL2AUX_inst_lr = prove
 (`!i (s:(A,C,FFI)wl_state) rst temp loc.
     wl_inst i s = SOME rst /\ every_var_inst (\x. x < temp) i /\
     locals_rel temp (wl_state_locals s) loc
     ==> ?loc'. wl_inst i (wl_state_locals_fupd (K loc) s) =
                SOME (wl_state_locals_fupd (K loc') rst) /\
                locals_rel temp (wl_state_locals rst) loc'`,
  GEN_TAC THEN IL2AUX_INST_SPLIT_TAC THEN IL2AUX_ALL_REGIMM_CASES_TAC THEN
  IL2AUX_INST_LR_TAC);;

let IL2AUX_LEMMA_FWD_TAC (lems:thm list) : tactic =
  ASSUM_LIST (fun ths ->
    EVERY (mapfilter (fun l -> STRIP_ASSUME_TAC (IL2AUX_fwd ths l)) lems));;

let IL2AUX_LR_TAC : tactic =
  IL2AUX_LR_SPLIT_TAC THEN
  IL2AUX_FACTS_TAC [mem_store_const] THEN TRY IL2AUX_LR_ALLOC_TAC THEN
  IL2AUX_LEMMA_FWD_TAC [IL2AUX_inst_lr; IL2AUX_share_inst_lr] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[IL2AUX_jump_exc_locals] THEN IL2AUX_LR_RWS_TAC THEN IL2AUX_LR_FIN_TAC;;

let IL2AUX_LR_REC_TAC : tactic =
  IL2AUX_LR_SPLIT_TAC THEN IL2AUX_IH_FWD_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN IL2AUX_LR_RWS_TAC THEN IL2AUX_LR_FIN_TAC;;

(* Extra temporaries not mentioned in program do not affect evaluation       *)

let locals_rel_evaluate_thm = prove
 (CASE_TERM
  `!prog (st:(A,C,FFI)wl_state) res rst loc temp.
     wl_evaluate (prog,st) = (res,rst) /\ ~(res = SOME wl_Error) /\
     wl_every_var (\x. x < temp) prog /\ locals_rel temp (wl_state_locals st) loc
     ==> ?loc'. wl_evaluate (prog, wl_state_locals_fupd (K loc) st) =
                (res, wl_state_locals_fupd (K loc') rst) /\
                (match res with
                   NONE -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Break _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Continue _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME _ -> wl_state_locals rst = loc')`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate IL2AUX_LR_TAC 11 @ [IL2AUX_LR_REC_TAC; IL2AUX_LR_REC_TAC] @
    replicate IL2AUX_LR_TAC 4 @ [IL2AUX_LR_REC_TAC; IL2AUX_LR_LOOP_TAC] @
    replicate IL2AUX_LR_TAC 7));;

(* ------------------------------------------------------------------------- *)
(* gc_fun_ok and the stack_max lemmas                                        *)
(* ------------------------------------------------------------------------- *)

let gc_fun_ok_def = cake_def
  `gc_fun_ok (f:((A)word_loc)list#((A)word->(A)word_loc)#((A)word->bool)#
                 (store_name,(A)word_loc)fmap ->
                (((A)word_loc)list#((A)word->(A)word_loc)#
                 (store_name,(A)word_loc)fmap)option) <=>
     !wl m d s wl1 m1 s1.
       Handler IN FDOM s /\ f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)
       ==> LENGTH wl = LENGTH wl1 /\ ~(Handler IN FDOM s1) /\
           f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler, FAPPLY s Handler))`;;

let push_env_dec_clock_stack = prove
 (`wl_state_stack_max (wl_push_env y opt (wl_dec_clock (t:(A,C,FFI)wl_state))) =
   wl_state_stack_max (wl_push_env y opt t) /\
   wl_state_stack (wl_push_env y opt (wl_dec_clock t)) = wl_state_stack (wl_push_env y opt t)`,
  REWRITE_TAC[wl_dec_clock_def] THEN SIMP[]);;

let set_store_stack_max_greater_bound = prove
 (`!v x (s:(A,C,FFI)wl_state) t.
     wl_set_store v x s = t /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[wl_set_store_def] THEN SIMP[]);;

let stack_size_some_at_least_one = prove
 (`!stk:((A)stack_frame)list sz. wl_stack_size stk = SOME sz ==> 1 <= sz`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[stack_size_eq2; option_INJ] THENL
   [ARITH_TAC; REWRITE_TAC[OPTION_MAP2_SOME] THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN ASM_ARITH_TAC]);;

(* y <= MAX x y on options *)

let IL2AUX_option_le_max = prove
 (`!a b:num option. option_le b (OPTION_MAP2 MAX a b)`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

let push_call_option_le_stack_max_preserved = prove
 (`!args sz env handler (s:(A,C,FFI)wl_state).
     option_le
       (OPTION_MAP2 (+)
          (wl_stack_size (wl_state_stack (wl_call_env args sz (wl_push_env env handler s))))
          (wl_state_locals_size (wl_call_env args sz (wl_push_env env handler s))))
       (wl_state_stack_max (wl_call_env args sz (wl_push_env env handler s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_call_env_def] THEN SIMP[IL2AUX_option_le_max]);;

let pop_env_option_le_stack_max_preserved = prove
 (`!(s:(A,C,FFI)wl_state) t.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s) /\
     wl_pop_env s = SOME t
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  MP_TAC (ISPEC `wl_state_stack (s:(A,C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `ls:((A)stack_frame)list`
       SUBST1_TAC))) THEN
  SIMP[] THEN
  STRUCT_CASES_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  SPEC_TAC(`a3:(num#num#num)option`,`a3:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[stack_size_eq2; stack_size_frame_def] THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`a0:num option`; `wl_stack_size (ls:((A)stack_frame)list)`;
    `wl_state_locals_size (s:(A,C,FFI)wl_state)`; `wl_state_stack_max (s:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def; OPTION_MAP_DEF] THEN ARITH_TAC);;


(* dec_stack keeps the frame sizes *)

let IL2AUX_dec_stack_size = prove
 (`!xs (stk:((A)stack_frame)list) stk'.
     wl_dec_stack xs stk = SOME stk' ==> wl_stack_size stk' = wl_stack_size stk`,
  MESON_TAC[dec_stack_stack_key_eq; wl_s_key_eq_stack_size]);;

let dec_stack_stack_size_some_not_none = prove
 (`!xs (stk:((A)stack_frame)list) stk' x.
     wl_dec_stack xs stk = SOME stk' /\ wl_stack_size stk = SOME x
     ==> ~(wl_stack_size stk' = NONE)`,
  MESON_TAC[IL2AUX_dec_stack_size; option_DISTINCT]);;

let dec_stack_stack_size_not_none_not_none = prove
 (`!xs (stk:((A)stack_frame)list) stk'.
     wl_dec_stack xs stk = SOME stk' /\ ~(wl_stack_size stk = NONE)
     ==> ~(wl_stack_size stk' = NONE)`,
  MESON_TAC[IL2AUX_dec_stack_size]);;

let dec_stack_stack_size_some_leq = prove
 (`!xs (stk:((A)stack_frame)list) stk' x y.
     wl_dec_stack xs stk = SOME stk' /\ wl_stack_size stk = SOME x /\
     wl_stack_size stk' = SOME y
     ==> y <= x`,
  MESON_TAC[IL2AUX_dec_stack_size; option_INJ; LE_REFL]);;

let flush_state_option_le_stack_max_preserved = prove
 (`!(s:(A,C,FFI)wl_state) p.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s)
     ==> let t = wl_flush_state p s in
         option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[] THEN
  REWRITE_TAC[stack_size_eq2] THEN
  CASES_ON `wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state))` THEN
  TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP stack_size_some_at_least_one)) THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`wl_state_locals_size (s:(A,C,FFI)wl_state)`; `wl_state_stack_max (s:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ASM_ARITH_TAC);;

(* the frame sizes of a suffix of the stack *)

let IL2AUX_stack_size_DROP = prove
 (`!(stack:((A)stack_frame)list) k x.
     wl_stack_size stack = SOME x /\ k <= LENGTH stack
     ==> ?y. wl_stack_size (DROP k stack) = SOME y /\ y <= x`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[DROP; LENGTH; LE_SUC; ARITH_RULE `~(SUC n <= 0)`] THEN
  TRY (MESON_TAC[LE_REFL]) THEN
  REWRITE_TAC[stack_size_eq2; OPTION_MAP2_SOME] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x2:num`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LASTN_stack_size_SOME = prove
 (`!n (stack:((A)stack_frame)list) stack' x.
     LASTN n stack = stack' /\ wl_stack_size stack = SOME x /\ n <= LENGTH stack
     ==> ?y. wl_stack_size stack' = SOME y /\ y <= x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_var (rhs (concl th)))) THEN
  ASM_SIMP_TAC[LASTN_DROP] THEN MATCH_MP_TAC IL2AUX_stack_size_DROP THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* I'm pretty sure this is defined somewhere else too *)

let OPTION_MAP2_ADD_0 = prove
 (`OPTION_MAP2 (+) m (SOME 0) = m /\ OPTION_MAP2 (+) (SOME 0) m = m`,
  STRUCT_CASES_TAC (ISPEC `m:num option` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP2_THM; ADD_CLAUSES]);;

(* HOL4 [local] *)
let option_le_stack_size_nil = prove
 (`option_le (wl_stack_size ([]:((A)stack_frame)list))
             (OPTION_MAP2 (+) (wl_stack_size (xs:((A)stack_frame)list)) opt)`,
  CASES_ON `wl_stack_size (xs:((A)stack_frame)list)` THEN
  TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP stack_size_some_at_least_one)) THEN
  STRUCT_CASES_TAC (ISPEC `opt:num option` (cases "option")) THEN
  REWRITE_TAC[stack_size_eq2; OPTION_MAP2_THM; option_le_def] THEN ASM_ARITH_TAC);;



(* copies of push_env_stack_max_eq and call_push_env_option_le_stack_max,  *)
(* which come later in the script                                           *)

let IL2AUX_push_env_stack_max = prove
 (`wl_state_stack_max (wl_push_env env handler (s:(A,C,FFI)wl_state)) =
   OPTION_MAP2 MAX (wl_state_stack_max s)
     (wl_stack_size (wl_state_stack (wl_push_env env handler s)))`,
  SPEC_TAC(`handler:(num#(A)wl_prog#num#num)option`,
           `handler:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN SIMP[]);;

let IL2AUX_call_push_sm = prove
 (`option_le (wl_state_stack_max (s:(A,C,FFI)wl_state))
             (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs handler s)))`,
  REWRITE_TAC[wl_call_env_def] THEN SIMP[IL2AUX_push_env_stack_max] THEN
  REWRITE_TAC[option_le_max_right; option_le_refl]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_option_le_stack_max_preserved.  The invariant is preserved by   *)
(* flush_state, jump_exc, alloc, share_inst, call_env and pop_env (helpers  *)
(* below); the proof is by the evaluate induction with forward chaining     *)
(* through the induction hypotheses.                                         *)
(* ------------------------------------------------------------------------- *)

let IL2AUX_flush_inv = prove
 (`!(s:(A,C,FFI)wl_state) p.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (wl_flush_state p s)))
                                    (wl_state_locals_size (wl_flush_state p s)))
                   (wl_state_stack_max (wl_flush_state p s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `p:bool` o MATCH_MP flush_state_option_le_stack_max_preserved) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let IL2AUX_jump_inv_arith = prove
 (`!ss ls sm m sxs x y.
     option_le (OPTION_MAP2 (+) ss ls) sm /\ ss = SOME x /\
     OPTION_MAP2 (+) (OPTION_MAP ((+) 3) m) sxs = SOME y /\ y <= x
     ==> option_le (OPTION_MAP2 (+) sxs m) (sm:num option)`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MAP2_THM; option_le_def; OPTION_MAP_DEF;
              option_INJ; option_DISTINCT] THEN
  ARITH_TAC);;

let IL2AUX_jump_exc_inv = prove
 (`!(s:(A,C,FFI)wl_state) t l.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s) /\
     wl_jump_exc s = SOME (t,l)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC (ISPEC `LASTN (wl_state_handler (s:(A,C,FFI)wl_state) + 1) (wl_state_stack s)`
            list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN SIMP[])
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `tl:((A)stack_frame)list`
       ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_ASSUME_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC (ISPEC `a3:(num#num#num)option` (cases "option")) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN SIMP[] THEN
  STRIP_ASSUME_TAC (ISPEC `a:num#num#num` PAIR_SURJECTIVE) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC (ISPEC `y:num#num` PAIR_SURJECTIVE) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  MP_TAC (ISPEC `wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x0:num` ASSUME_TAC)) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "option_le" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF] THEN
    STRUCT_CASES_TAC (ISPEC `wl_state_stack_max (s:(A,C,FFI)wl_state)` (cases "option")) THEN
    REWRITE_TAC[option_le_def];
    ALL_TAC] THEN
  MATCH_MP_TAC IL2AUX_jump_inv_arith THEN
  MAP_EVERY EXISTS_TAC [`wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state))`;
                        `wl_state_locals_size (s:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  MP_TAC (ISPECL [`wl_state_handler (s:(A,C,FFI)wl_state) + 1`;
                  `wl_state_stack (s:(A,C,FFI)wl_state)`;
                  `CONS (StackFrame a0 a1 a2 (SOME (x,x',y'))) (tl:((A)stack_frame)list)`;
                  `x0:num`] LASTN_stack_size_SOME) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[stack_size_eq2; stack_size_frame_def] THEN MESON_TAC[]);;

(* the state after the gc and the pop_env of alloc *)

let IL2AUX_alloc_pop = prove
 (`!envs (s:(A,C,FFI)wl_state) y z.
     wl_gc (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s) = SOME y /\
     wl_pop_env y = SOME z
     ==> wl_stack_size (wl_state_stack z) = wl_stack_size (wl_state_stack s) /\
         wl_state_locals_size z = wl_state_locals_size s /\
         wl_state_stack_max z =
           OPTION_MAP2 MAX (wl_state_stack_max s)
             (OPTION_MAP2 (+) (wl_state_locals_size s) (wl_stack_size (wl_state_stack s)))`,
  let hd_is n th = try fst(dest_const(fst(strip_comb(concl th)))) = n with Failure _ -> false in
  let lhs_is n th =
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = n with Failure _ -> false in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gc_const) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP gc_s_key_eq) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const) THEN
  FIRST_X_ASSUM (MP_TAC o check (hd_is "s_key_eq")) THEN
  FIRST_X_ASSUM (MP_TAC o check (lhs_is "wl_pop_env")) THEN
  REWRITE_TAC[wl_pop_env_def] THEN
  MP_TAC (ISPEC `wl_state_stack (y:(A,C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `tl:((A)stack_frame)list`
       SUBST1_TAC))) THEN
  SIMP[] THEN
  STRUCT_CASES_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[IL2AUX_push_env_stack_max] THEN
  REWRITE_TAC[wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[s_key_eq_def; s_frame_key_eq_def2] THEN
  REPEAT STRIP_TAC THEN IL2AUX_SUBST_VARS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_eq (concl th) && is_var (rand (rhs (concl th))) &&
    (try fst(dest_const(rator(rhs(concl th)))) = "SOME" with Failure _ -> false))) THEN
  SIMP[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[] THEN
  FIRST_ASSUM(fun th -> if hd_is "s_key_eq" th
                        then ASSUME_TAC (MATCH_MP wl_s_key_eq_stack_size th)
                        else failwith "") THEN
  ASM_REWRITE_TAC[stack_size_eq2; stack_size_frame_def]);;

let IL2AUX_alloc_pop_inv = prove
 (`!envs (s:(A,C,FFI)wl_state) y z.
     wl_gc (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s) = SOME y /\
     wl_pop_env y = SOME z
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack z)) (wl_state_locals_size z))
                   (wl_state_stack_max z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_alloc_pop) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [option_add_comm] THEN
  REWRITE_TAC[IL2AUX_option_le_max]);;

let IL2AUX_alloc_inv = prove
 (`!w names (s:(A,C,FFI)wl_state) r t.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s) /\
     wl_alloc w names s = (r,t)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY (MATCH_MP_TAC IL2AUX_flush_inv THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY (FIRST_ASSUM (MP_TAC o MATCH_MP push_env_pop_env_s_key_eq o MATCH_MP gc_s_key_eq o
         check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_gc"
                          with Failure _ -> false)) THEN
       ASM_REWRITE_TAC[option_DISTINCT] THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC IL2AUX_flush_inv) THEN
  ASM_MESON_TAC[IL2AUX_alloc_pop_inv]);;

let IL2AUX_share_inst_inv = prove
 (`!op v ad (s:(A,C,FFI)wl_state) (r:((W)wl_result)option) t.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s) /\
     share_inst op v ad s = (r,t)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
              wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
              wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC ORELSE IL2AUX_CALL_FFI_CASES_TAC) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY (MATCH_MP_TAC IL2AUX_flush_inv) THEN SIMP[wl_set_var_def]);;

let IL2AUX_IH_FWD_R_TAC (rws:thm list) (fb:thm list) : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) then failwith "" else
    let th = IL2AUX_fwd_r rws fb (map snd asl) (REWRITE_RULE rws ih) in
    STRIP_ASSUME_TAC (CAKE_SIMP_RULE [] th) g));;

let IL2AUX_call_env_inv = prove
 (`!args sz (s:(A,C,FFI)wl_state).
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (wl_call_env args sz s)))
                                (wl_state_locals_size (wl_call_env args sz s)))
               (wl_state_stack_max (wl_call_env args sz s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_call_env_def] THEN SIMP[IL2AUX_option_le_max]);;

let IL2AUX_inv_nil = prove
 (`!s:(A,C,FFI)wl_state.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size ([]:((A)stack_frame)list))
                                    (wl_state_locals_size s))
                   (wl_state_stack_max s)`,
  GEN_TAC THEN REWRITE_TAC[stack_size_eq2] THEN
  CASES_ON `wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state))` THEN
  TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP stack_size_some_at_least_one)) THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`wl_state_locals_size (s:(A,C,FFI)wl_state)`; `wl_state_stack_max (s:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ASM_ARITH_TAC);;

let IL2AUX_SMP_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else REWRITE_RULE IL2AUX_dec_rws th) THEN
  IL2AUX_FACTS_TAC [inst_const_full; mem_store_const; cut_state_const] THEN
  IL2AUX_SUBST_VARS_TAC THEN
  IL2AUX_LEMMA_FWD_TAC [IL2AUX_alloc_inv; IL2AUX_jump_exc_inv; IL2AUX_share_inst_inv] THEN
  IL2AUX_IH_FWD_R_TAC IL2AUX_dec_rws
    (map (REWRITE_RULE IL2AUX_dec_rws)
      [push_call_option_le_stack_max_preserved; IL2AUX_call_env_inv]) THEN
  IL2AUX_LEMMA_FWD_TAC [pop_env_option_le_stack_max_preserved] THEN
  IL2AUX_IH_FWD_R_TAC IL2AUX_dec_rws
    (map (REWRITE_RULE IL2AUX_dec_rws)
      [push_call_option_le_stack_max_preserved; IL2AUX_call_env_inv]) THEN
  IL2AUX_DROP_IHS_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE IL2AUX_dec_rws) THEN
  TRY (MATCH_MP_TAC IL2AUX_flush_inv) THEN
  FS[wl_dec_clock_def; option_le_def] THEN
  ASM_MESON_TAC[option_le_trans; IL2AUX_inv_nil; IL2AUX_call_push_sm];;

let evaluate_option_le_stack_max_preserved = prove
 (`!p (s:(A,C,FFI)wl_state) r t.
     wl_evaluate (p,s) = (r,t) /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) (wl_state_locals_size s))
               (wl_state_stack_max s)
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
                   (wl_state_stack_max t)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN IL2AUX_SMP_TAC);;



let push_env_stack_max_eq = prove
 (`wl_state_stack_max (wl_push_env env handler (s:(A,C,FFI)wl_state)) =
   OPTION_MAP2 MAX (wl_state_stack_max s)
     (wl_stack_size (wl_state_stack (wl_push_env env handler s)))`,
  SPEC_TAC(`handler:(num#(A)wl_prog#num#num)option`,
           `handler:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN SIMP[]);;

(* HOL4 [local] *)
let call_env_option_le_stack_max = prove
 (`option_le (wl_state_stack_max (s:(A,C,FFI)wl_state))
             (wl_state_stack_max (wl_call_env args1 ss s))`,
  REWRITE_TAC[wl_call_env_def] THEN SIMP[option_le_max_right; option_le_refl]);;

(* HOL4 [local] *)
let call_push_env_option_le_stack_max = prove
 (`option_le (wl_state_stack_max (s:(A,C,FFI)wl_state))
             (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs handler s)))`,
  REWRITE_TAC[wl_call_env_def] THEN SIMP[push_env_stack_max_eq] THEN
  REWRITE_TAC[option_le_max_right; option_le_refl]);;

(* alloc only grows stack_max *)

let IL2AUX_alloc_stack_max_le = prove
 (`!w names (s:(A,C,FFI)wl_state) r t.
     wl_alloc w names s = (r,t) ==> option_le (wl_state_stack_max s) (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_FACTS_TAC [gc_const; wl_pop_env_const] THEN
  FS[option_le_refl; push_env_stack_max_eq; option_le_max_right; wl_flush_state_def]);;

let IL2AUX_is_option_le tm =
  try fst(dest_const(fst(strip_comb tm))) = "option_le" with Failure _ -> false;;

let IL2AUX_sm_facts =
  [inst_const_full; mem_store_const; jump_exc_const; share_inst_const; cut_state_const;
   IL2AUX_alloc_stack_max_le];;

let IL2AUX_SM_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY (IL2AUX_IH_GOAL_TAC IL2AUX_res_rws) THEN
  IL2AUX_POP_CONST_TAC THEN IL2AUX_FACTS_TAC IL2AUX_sm_facts THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN IL2AUX_DROP_IHS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_dec_rws) THEN
  FS[option_le_refl; wl_dec_clock_def; wl_flush_state_def] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_option_le o concl))) THEN
  MESON_TAC[option_le_trans; option_le_refl; call_env_option_le_stack_max;
            call_push_env_option_le_stack_max];;

let evaluate_stack_max_le = prove
 (`!c (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (c,s1) = (res,s2)
     ==> option_le (wl_state_stack_max s1) (wl_state_stack_max s2)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN IL2AUX_SM_TAC);;


let evaluate_stack_max = prove
 (CASE_TERM
  `!c (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (c,s1) = (res,s2)
     ==> match wl_state_stack_max s1 with
           NONE -> wl_state_stack_max s2 = NONE
         | SOME stack_max -> misc_the stack_max (wl_state_stack_max s2) >= stack_max`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP evaluate_stack_max_le) THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`wl_state_stack_max (s1:(A,C,FFI)wl_state)`;
    `wl_state_stack_max (s2:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_le_def; option_CASE; misc_the_def] THEN ARITH_TAC);;

let evaluate_stack_max_IS_SOME = prove
 (`!c (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (c,s1) = (res,s2) /\ IS_SOME (wl_state_stack_max s2)
     ==> IS_SOME (wl_state_stack_max s1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o MATCH_MP evaluate_stack_max_le) MP_TAC) THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`wl_state_stack_max (s1:(A,C,FFI)wl_state)`;
    `wl_state_stack_max (s2:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_le_def; IS_SOME_DEF]);;

(* HOL4: evaluate_stack_limit *)
let wl_evaluate_stack_limit = prove
 (`!c (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (c,s1) = (res,s2) ==> wl_state_stack_limit s2 = wl_state_stack_limit s1`,
  MESON_TAC[wl_evaluate_consts]);;

let evaluate_stack_limit_stack_max_eq = prove
 (`!c (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (c,s1) = (res,s2) /\
     misc_the (wl_state_stack_limit s1) (wl_state_stack_max s1) >= wl_state_stack_limit s1
     ==> misc_the (wl_state_stack_limit s2) (wl_state_stack_max s2) >= wl_state_stack_limit s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MP_TAC (MATCH_MP evaluate_stack_max_le th) THEN
                                       MP_TAC (MATCH_MP wl_evaluate_stack_limit th)) MP_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN SUBST1_TAC THEN MP_TAC th) THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`wl_state_stack_max (s1:(A,C,FFI)wl_state)`;
    `wl_state_stack_max (s2:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_le_def; misc_the_def] THEN ARITH_TAC);;

let evaluate_stack_limit_stack_max = prove
 (`!c (s1:(A,C,FFI)wl_state) res s2.
     wl_evaluate (c,s1) = (res,s2) /\
     misc_the (wl_state_stack_limit s1 + 1) (wl_state_stack_max s1) > wl_state_stack_limit s1
     ==> misc_the (wl_state_stack_limit s2 + 1) (wl_state_stack_max s2) > wl_state_stack_limit s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MP_TAC (MATCH_MP evaluate_stack_max_le th) THEN
                                       MP_TAC (MATCH_MP wl_evaluate_stack_limit th)) MP_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN SUBST1_TAC THEN MP_TAC th) THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
   [`wl_state_stack_max (s1:(A,C,FFI)wl_state)`;
    `wl_state_stack_max (s2:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_le_def; misc_the_def] THEN ARITH_TAC);;

(* HOL4: inc_clock_def *)
let wl_inc_clock_def = cake_def
  `wl_inc_clock n (t:(A,C,FFI)wl_state) =
     wl_state_clock_fupd (K (wl_state_clock t + n)) t`;;

(* HOL4: inc_clock_0[simp] *)
let wl_inc_clock_0 = prove
 (`!t:(A,C,FFI)wl_state. wl_inc_clock 0 t = t`,
  REWRITE_TAC[wl_inc_clock_def; wl_state_component_equality] THEN SIMP[]);;

let _ = cake_add_simps [wl_inc_clock_0];;

(* HOL4: inc_clock_inc_clock[simp] *)
let wl_inc_clock_inc_clock = prove
 (`!t:(A,C,FFI)wl_state. wl_inc_clock n (wl_inc_clock m t) = wl_inc_clock (n + m) t`,
  REWRITE_TAC[wl_inc_clock_def; wl_state_component_equality] THEN SIMP[] THEN ARITH_TAC);;

let _ = cake_add_simps [wl_inc_clock_inc_clock];;

let evaluate_call_push_dec_option_le_stack_max = prove
 (`!p args sz env handler (s:(A,C,FFI)wl_state) res t ck.
     wl_evaluate (p, wl_call_env args sz
                       (wl_push_env env handler
                          (wl_dec_clock (wl_state_clock_fupd (K ck) s)))) = (res,t)
     ==> option_le (wl_state_stack_max (wl_call_env args sz (wl_push_env env handler s)))
                   (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP evaluate_stack_max_le) THEN
  REWRITE_TAC[wl_dec_clock_def] THEN SIMP[]);;


(* rewrite the facts of a relation with the evaluate assumptions *)

let IL2AUX_REL_NORM_TAC (is_rel:term->bool) : tactic =
  ASSUM_LIST (fun ths ->
    let evs = filter (IL2AUX_is_eval_eq o concl) ths in
    RULE_ASSUM_TAC (fun th ->
      if is_rel (concl th) then REWRITE_RULE (evs @ [SND; FST]) th else th));;

let IL2AUX_SMOG_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_BFR_TAC THEN IL2AUX_CONT_TAC THEN IL2AUX_POP_CONST_TAC THEN
  IL2AUX_FACTS_TAC IL2AUX_sm_facts THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN IL2AUX_DROP_IHS_TAC THEN
  IL2AUX_ADDC_FACTS_TAC THEN IL2AUX_FACTS_TAC [evaluate_stack_max_le] THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_dec_rws) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[wl_dec_clock_def; wl_STOP_def; cut_state_with_const; OPTION_MAP_DEF;
       IL2AUX_ADD_SUB1; ADD_EQ_0] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN TRY(IL2AUX_FACTS_TAC [evaluate_stack_max_le])) THEN
  IL2AUX_POP_CONST_TAC THEN IL2AUX_FACTS_TAC IL2AUX_sm_facts THEN
  IL2AUX_SUB1_NORM_TAC THEN IL2AUX_SPLIT_EVALS_TAC THEN
  IL2AUX_FACTS_TAC [evaluate_stack_max_le] THEN
  FS[option_le_refl; wl_dec_clock_def; wl_flush_state_def] THEN IL2AUX_SUBST_VARS_TAC THEN
  FS[option_le_refl] THEN IL2AUX_SUB1_NORM_TAC THEN
  IL2AUX_REL_NORM_TAC IL2AUX_is_option_le THEN
  FS[option_le_refl; wl_flush_state_def] THEN IL2AUX_SUBST_VARS_TAC THEN
  FS[option_le_refl] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_option_le o concl))) THEN
  MESON_TAC[option_le_trans; option_le_refl; call_env_option_le_stack_max;
            call_push_env_option_le_stack_max];;

let IL2AUX_NONREC_SMOG_TAC : tactic =
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[evaluate_clock_with_const; pair_CASE] THEN
  SIMP[option_le_refl];;


let IL2AUX_smog_lemma = prove
 (`!p (s:(A,C,FFI)wl_state) r1 s1.
     wl_evaluate (p,s) = (r1,s1)
     ==> option_le (wl_state_stack_max s1)
           (wl_state_stack_max (SND (wl_evaluate
              (p, wl_state_clock_fupd (K (wl_state_clock s + extra)) s))))`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate IL2AUX_NONREC_SMOG_TAC 10 @ replicate IL2AUX_SMOG_TAC 3 @
    replicate IL2AUX_NONREC_SMOG_TAC 4 @ replicate IL2AUX_SMOG_TAC 2 @
    replicate IL2AUX_NONREC_SMOG_TAC 6 @ [IL2AUX_SMOG_TAC]));;

let evaluate_stack_max_only_grows = prove
 (`!p (s:(A,C,FFI)wl_state) r t ck r' t'.
     wl_evaluate (p,s) = (r,t) /\ wl_evaluate (p, wl_inc_clock ck s) = (r',t')
     ==> option_le (wl_state_stack_max t) (wl_state_stack_max t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inc_clock_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (INST [`ck:num`,`extra:num`] IL2AUX_smog_lemma) o
    check (fun th -> not (can (find_term ((=) `ck:num`)) (concl th)))) THEN
  ASM_REWRITE_TAC[]);;


let IL2AUX_is_subspt tm =
  try fst(dest_const(fst(strip_comb tm))) = "subspt" with Failure _ -> false;;

let IL2AUX_code_facts =
  [wl_alloc_const; inst_const_full; mem_store_const; jump_exc_const; share_inst_const;
   cut_state_const];;

let IL2AUX_CODE_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY (IL2AUX_IH_GOAL_TAC IL2AUX_res_rws) THEN
  IL2AUX_POP_CONST_TAC THEN IL2AUX_FACTS_TAC IL2AUX_code_facts THEN
  IL2AUX_USE_IHS_RW_TAC IL2AUX_res_rws THEN IL2AUX_DROP_IHS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_dec_rws) THEN
  FS[subspt_refl; subspt_union; wl_dec_clock_def; wl_flush_state_def] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_subspt o concl))) THEN
  MESON_TAC[subspt_trans; subspt_refl];;

let evaluate_code_only_grows = prove
 (`!p (s:(A,C,FFI)wl_state) r t.
     wl_evaluate (p,s) = (r,t) ==> subspt (wl_state_code s) (wl_state_code t)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN IL2AUX_CODE_TAC);;


let evaluate_NONE_stack_size_const = prove
 (`!p (s:(A,C,FFI)wl_state) t.
     wl_evaluate (p,s) = (NONE,t)
     ==> wl_stack_size (wl_state_stack t) = wl_stack_size (wl_state_stack s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`p:(A)wl_prog`; `s:(A,C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP[] THEN
  MESON_TAC[wl_s_key_eq_stack_size]);;

(* ------------------------------------------------------------------------- *)
(* env_to_list                                                               *)
(* ------------------------------------------------------------------------- *)

(* the list of env_to_list is a permutation of toAList, with distinct keys  *)

let IL2AUX_env_to_list_perm = prove
 (`!(y:((A)word_loc)spt) f. PERM (toAList y) (FST (env_to_list y f))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST] THEN
  MATCH_MP_TAC PERM_TRANS THEN
  EXISTS_TAC `sort key_val_compare (toAList (y:((A)word_loc)spt))` THEN
  REWRITE_TAC[sort_PERM] THEN MATCH_MP_TAC PERM_list_rearrange THEN
  MP_TAC (ISPECL [`key_val_compare:num#(A)word_loc->num#(A)word_loc->bool`;
                  `toAList (y:((A)word_loc)spt)`] sort_PERM) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP ALL_DISTINCT_PERM th)]) THEN
  MATCH_MP_TAC (ISPEC `FST:num#(A)word_loc->num` ALL_DISTINCT_MAP) THEN
  REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]);;

let IL2AUX_env_to_list_distinct = prove
 (`!(y:((A)word_loc)spt) f. ALL_DISTINCT (MAP FST (FST (env_to_list y f)))`,
  REPEAT GEN_TAC THEN
  MP_TAC (MATCH_MP (ISPEC `FST:num#(A)word_loc->num` PERM_MAP)
            (ISPECL [`y:((A)word_loc)spt`; `f:num->num->num`] IL2AUX_env_to_list_perm)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP ALL_DISTINCT_PERM th)]) THEN
  REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]);;

let env_to_list_lookup_equiv = prove
 (`env_to_list (y:((A)word_loc)spt) f = (q,r)
   ==> (!n. ALOOKUP q n = lookup n y) /\
       (!x1 x2. MEM (x1,x2) q ==> lookup x1 y = SOME x2)`,
  DISCH_THEN(SUBST1_TAC o SYM o REWRITE_RULE[FST] o
    AP_TERM `FST:(num#(A)word_loc)list#(num->num->num)->(num#(A)word_loc)list`) THEN
  SUBGOAL_THEN `!x1 x2. MEM (x1,x2) (FST (env_to_list (y:((A)word_loc)spt) f)) <=>
                        lookup x1 y = SOME x2` ASSUME_TAC THENL
   [REWRITE_TAC[env_to_list_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[FST; mem_list_rearrange; sort_MEM; MEM_toAList];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  CASES_ON `lookup n (y:((A)word_loc)spt)` THENL
   [REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    ASM_MESON_TAC[option_DISTINCT];
    MATCH_MP_TAC ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME THEN
    ASM_REWRITE_TAC[IL2AUX_env_to_list_distinct]]);;

let env_to_list_ALL_DISTINCT = prove
 (`env_to_list (y:((A)word_loc)spt) perm = (vs,other) ==> ALL_DISTINCT (MAP FST vs)`,
  MESON_TAC[IL2AUX_env_to_list_distinct; FST]);;

let env_to_list_ALL_DISTINCT_FST = prove
 (`ALL_DISTINCT (MAP FST (FST (env_to_list (y:((A)word_loc)spt) perm)))`,
  REWRITE_TAC[IL2AUX_env_to_list_distinct]);;

(* ------------------------------------------------------------------------- *)
(* Code tables without Alloc, Install or MustTerminate                       *)
(* ------------------------------------------------------------------------- *)

let no_alloc_code_def = cake_def
  `no_alloc_code (code:(num#(A)wl_prog)spt) <=>
     !k n p. lookup k code = SOME (n,p) ==> no_alloc p`;;

(* the cases of find_code *)

let IL2AUX_find_code_lookup = prove
 (`!dest (args:((A)word_loc)list) (code:(num#(A)wl_prog)spt) (lsize:(L)spt) args1 expr ps.
     wl_find_code dest args code lsize = SOME (args1,expr,ps)
     ==> ?k n. lookup k code = SOME (n,expr)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[wl_find_code_def] THEN REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

let no_alloc_find_code = prove
 (`!code dest (args:((A)word_loc)list) (lsize:(L)spt) args1 expr ps.
     wl_find_code dest args code lsize = SOME (args1,expr,ps) /\
     no_alloc_code (code:(num#(A)wl_prog)spt)
     ==> no_alloc expr`,
  REWRITE_TAC[no_alloc_code_def] THEN MESON_TAC[IL2AUX_find_code_lookup]);;

let no_install_code_def = cake_def
  `no_install_code (code:(num#(A)wl_prog)spt) <=>
     !k n p. lookup k code = SOME (n,p) ==> wordConvs_no_install p`;;

let no_install_find_code = prove
 (`!code dest (args:((A)word_loc)list) (lsize:(L)spt) args1 expr ps.
     no_install_code (code:(num#(A)wl_prog)spt) /\
     wl_find_code dest args code lsize = SOME (args1,expr,ps)
     ==> wordConvs_no_install expr`,
  REWRITE_TAC[no_install_code_def] THEN MESON_TAC[IL2AUX_find_code_lookup]);;

(* IL2AUX_fwd with antecedents also proved by MESON from the non-IH facts *)

let IL2AUX_fwd_m (rws:thm list) (facts:thm list) (ih:thm) : thm =
  let simple = filter (fun th -> not (is_forall (concl th)) && not (is_imp (concl th))) facts in
  let rec go th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = fst (dest_imp bod) in
    try tryfind (fun f -> go (REWRITE_RULE rws (MATCH_MP th f))) facts
    with Failure _ ->
    try go (IL2AUX_fwd_eq th) with Failure _ ->
      if exists (fun v -> vfree_in v ant) vs then failwith "IL2AUX_fwd_m" else
      let ath = try EQT_ELIM (REWRITE_CONV IL2AUX_res_rws ant)
                with Failure _ ->
                  if (try fst(dest_const(fst(strip_comb ant))) = "no_install_code"
                      with Failure _ -> false)
                  then MESON simple ant else failwith "IL2AUX_fwd_m" in
      go (MP (SPEC_ALL th) ath) in
  go (REWRITE_RULE[IMP_CONJ] ih);;

let IL2AUX_IH_FWD_M_TAC (rws:thm list) : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) then failwith "" else
    let th = IL2AUX_fwd_m rws (map snd asl) (REWRITE_RULE rws ih) in
    STRIP_ASSUME_TAC (CAKE_SIMP_RULE [] th) g));;

let IL2AUX_NI_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else CASE_REWRITE_RULE []
                                   (REWRITE_RULE (wordConvs_no_install_def :: IL2AUX_dec_rws)
                                      (CASE_REWRITE_RULE [] th))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (injectivity "wl_prog" :: distinctness "wl_prog" ::
                               IL2AUX_res_rws)) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  IL2AUX_POP_CONST_TAC THEN
  IL2AUX_FACTS_TAC [wl_alloc_const; inst_const_full; mem_store_const; jump_exc_const;
                    share_inst_const; cut_state_const] THEN
  IL2AUX_LEMMA_FWD_TAC [no_install_find_code] THEN IL2AUX_SUBST_VARS_TAC THEN
  IL2AUX_IH_FWD_M_TAC (wordConvs_no_install_def :: IL2AUX_dec_rws) THEN
  IL2AUX_DROP_IHS_TAC THEN
  FS[wl_flush_state_def; wl_dec_clock_def] THEN ASM_MESON_TAC[];;

let no_install_evaluate_const_code = prove
 (`!prog (s:(A,C,FFI)wl_state) result s1.
     wl_evaluate (prog,s) = (result,s1) /\ wordConvs_no_install prog /\
     no_install_code (wl_state_code s)
     ==> wl_state_code s = wl_state_code s1`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN IL2AUX_NI_TAC);;

let get_code_labels_not_created = prove
 (`!p x. x IN wordConvs_get_code_labels (p:(A)wl_prog) <=>
         ~(not_created_subprogs (\sp. ~(sp = wl_Call NONE (SOME x) [] NONE) /\
                                      ~(sp = wl_LocValue 0 x)) p)`,
  MATCH_MP_TAC wordConvs_get_code_labels_ind THEN REPEAT CONJ_TAC THEN
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  REWRITE_TAC[wordConvs_get_code_labels_def; not_created_subprogs_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN
  SIMP[IN_UNION; IN_SING; NOT_IN_EMPTY; injectivity "wl_prog"; distinctness "wl_prog";
           option_INJ; option_DISTINCT] THEN
  ASM_MESON_TAC[]);;

let no_mt_code_def = cake_def
  `no_mt_code (code:(num#(A)wl_prog)spt) <=>
     !k n p. lookup k code = SOME (n,p) ==> no_mt p`;;

let no_mt_find_code = prove
 (`!code dest (args:((A)word_loc)list) (lsize:(L)spt) args1 expr ps.
     wl_find_code dest args code lsize = SOME (args1,expr,ps) /\
     no_mt_code (code:(num#(A)wl_prog)spt)
     ==> no_mt expr`,
  REWRITE_TAC[no_mt_code_def] THEN MESON_TAC[IL2AUX_find_code_lookup]);;

(* ------------------------------------------------------------------------- *)
(* permute_swap for no_install and no_alloc                                  *)
(* HOL4 Overload PERM_STACK (written out where used):                        *)
(*   PERM_STACK = \s1 s2. match (s1,s2) with                                 *)
(*     (StackFrame ss l env h, StackFrame ss' l' env' h') ->                  *)
(*       ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\                     *)
(*       ALL_DISTINCT (MAP FST env)                                          *)
(* ------------------------------------------------------------------------- *)

let PERM_fromAList = prove
 (`!l1 l2:(num#A)list.
     PERM l1 l2 /\ ALL_DISTINCT (MAP FST l1) ==> fromAList l1 = fromAList l2`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`fromAList (l1:(num#A)list)`; `fromAList (l2:(num#A)list)`] spt_eq_thm) THEN
  REWRITE_TAC[wf_fromAList] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_fromAList] THEN X_GEN_TAC `n:num` THEN
  CASES_ON `ALOOKUP (l2:(num#A)list) n` THENL
   [UNDISCH_TAC `ALOOKUP (l2:(num#A)list) n = NONE` THEN REWRITE_TAC[ALOOKUP_NONE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ISPEC `FST:num#A->num` PERM_MAP)) THEN
    MESON_TAC[MEM_PERM];
    MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN ASM_MESON_TAC[MEM_PERM]]);;

let stack_size_perm = prove
 (CASE_TERM
  `!l1 l2:((A)stack_frame)list.
     ALL2 (\s1 s2. match (s1,s2) with
                     (StackFrame ss l env h, StackFrame ss' l' env' h') ->
                       ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\
                       ALL_DISTINCT (MAP FST env)) l1 l2
     ==> wl_stack_size l1 = wl_stack_size l2`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; stack_size_eq2] THEN IL2AUX_ALL_FRAME_CASES_TAC THEN
  SIMP[IL2AUX_stack_size_frame_alt] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;

let env_to_list_PERM = prove
 (`PERM (FST (env_to_list (env:((A)word_loc)spt) perm)) (FST (env_to_list env perm'))`,
  MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `toAList (env:((A)word_loc)spt)` THEN
  ONCE_REWRITE_TAC[PERM_SYM] THEN REWRITE_TAC[IL2AUX_env_to_list_perm] THEN
  ONCE_REWRITE_TAC[PERM_SYM] THEN REWRITE_TAC[IL2AUX_env_to_list_perm]);;

(* ------------------------------------------------------------------------- *)
(* permute_swap_lemma2 and permute_swap_lemma3: without Alloc and Install,  *)
(* a run from another oracle and a stack related by PERM_STACK (written out *)
(* where used; IL2AUX_permf here) gives the same result, with some oracle   *)
(* and a related final stack.  The proof is by the evaluate induction; the  *)
(* induction hypotheses are instantiated at the evaluations of each branch  *)
(* (IL2AUX_fwd_ps2) and then at the oracles and stacks of the new run.      *)
(* ------------------------------------------------------------------------- *)

let IL2AUX_permf_def = cake_def
 `IL2AUX_permf (s1:(A)stack_frame) s2 <=>
    match (s1,s2) with
      (StackFrame ss l env h, StackFrame ss' l' env' h') ->
        ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\ ALL_DISTINCT (MAP FST env)`;;

let IL2AUX_permf_thm = prove
 (`IL2AUX_permf (StackFrame ss l env h:(A)stack_frame) (StackFrame ss' l' env' h') <=>
     ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\ ALL_DISTINCT (MAP FST env)`,
  REWRITE_TAC[IL2AUX_permf_def] THEN SIMP[]);;

(* the statements without recursive calls: the results that flush the stack *)
(* and the others, which keep the stack and the handler                      *)

let IL2AUX_evaluate_transp_facts = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !r t. wl_evaluate (p,s) = (r,t) /\ ~(r = SOME wl_Error)
                ==> (IL2AUX_stopr r ==> wl_state_stack t = [] /\ wl_state_locals t = LN) /\
                    (~IL2AUX_stopr r
                     ==> wl_state_stack t = wl_state_stack s /\
                         wl_state_handler t = wl_state_handler s) /\
                    (!x y. ~(r = SOME (wl_Exception x y)))`)
    IL2AUX_transp_cons,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE([IL2AUX_stopr_thms] @ IL2AUX_res_rws)) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  IL2AUX_FACTS_TAC [inst_const_full; mem_store_const; IL2AUX_share_inst_facts] THEN
  REWRITE_TAC([IL2AUX_stopr_thms] @ IL2AUX_res_rws) THEN
  FS[wl_flush_state_def; wl_dec_clock_def; IL2AUX_stopr_thms] THEN
  ASM_MESON_TAC[]);;

(* the run with another oracle and a related stack *)

let IL2AUX_evaluate_ps_with = prove
 (IL2AUX_select_goals
    (IL2AUX_ind_goals
       `\(p:(A)wl_prog,s:(A,C,FFI)wl_state).
          !q xs. wl_evaluate (p, wl_state_permute_fupd (K q) (wl_state_stack_fupd (K xs) s)) =
                 pair_CASE (wl_evaluate (p,s))
                   (\r t. (r, wl_state_permute_fupd (K q)
                                (if IL2AUX_stopr r then t else wl_state_stack_fupd (K xs) t)))`)
    IL2AUX_transp_cons,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IL2AUX_evaluate_permute_with_const] THEN
  REWRITE_TAC[IL2AUX_evaluate_stack_with] THEN
  TRY (ONCE_REWRITE_TAC[wl_evaluate_def] THEN
       SIMP[IL2AUX_stopr_thms; IL2AUX_dec_clock_stack; IL2AUX_dec_clock_permute] THEN
       COND_CASES_TAC THEN SIMP[IL2AUX_stopr_thms; IL2AUX_dec_clock_stack; IL2AUX_dec_clock_permute;
                                 wl_flush_state_def] THEN NO_TAC) THEN
  W(fun (_,w) -> let t = find_term (fun t -> IL2AUX_kind_name t = "wl_evaluate") w in
     SPEC_TAC (t, `pp:((A)wl_result)option#(A,C,FFI)wl_state`)) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let IL2AUX_stack_fupd_nil = prove
 (`!t:(A,C,FFI)wl_state. wl_state_stack t = [] ==> wl_state_stack_fupd (K []) t = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let IL2AUX_ps2_simple = prove
 (`!p (s:(A,C,FFI)wl_state) r t.
     (!q xs. wl_evaluate (p, wl_state_permute_fupd (K q) (wl_state_stack_fupd (K xs) s)) =
             (r, wl_state_permute_fupd (K q)
                   (if IL2AUX_stopr r then t else wl_state_stack_fupd (K xs) t))) /\
     (IL2AUX_stopr r ==> wl_state_stack t = []) /\
     (~IL2AUX_stopr r ==> wl_state_stack t = wl_state_stack s)
     ==> !perm stack.
           ALL2 IL2AUX_permf stack (wl_state_stack s)
           ==> ?perm' stack'.
                 wl_evaluate (p, wl_state_permute_fupd (K perm) (wl_state_stack_fupd (K stack) s)) =
                 (r, wl_state_permute_fupd (K perm') (wl_state_stack_fupd (K stack') t)) /\
                 ALL2 IL2AUX_permf stack' (wl_state_stack t)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `perm:num->num->num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `IL2AUX_stopr (r:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `[]:((A)stack_frame)list` THEN
    FIRST_X_ASSUM(fun th -> if is_imp (concl th) then
      ASSUME_TAC (MP th (ASSUME `IL2AUX_stopr (r:((A)wl_result)option)`)) else failwith "") THEN
    ASM_SIMP_TAC[IL2AUX_stack_fupd_nil; ALL2];
    EXISTS_TAC `stack:((A)stack_frame)list` THEN ASM_MESON_TAC[]]);;

(* Raise: jump_exc on a related stack *)

let IL2AUX_ALL2_CONS_R = prove
 (`!(P:A->B->bool) l y ys.
     ALL2 P l (CONS y ys) <=> ?x xs. l = CONS x xs /\ P x y /\ ALL2 P xs ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let IL2AUX_jump_exc_permf = prove
 (`!(s:(A,C,FFI)wl_state) t l1 l2 q stack.
     wl_jump_exc s = SOME (t,l1,l2) /\ ALL2 IL2AUX_permf stack (wl_state_stack s)
     ==> ?stack'. wl_jump_exc (wl_state_permute_fupd (K q) (wl_state_stack_fupd (K stack) s)) =
                    SOME (wl_state_permute_fupd (K q) (wl_state_stack_fupd (K stack') t),l1,l2) /\
                  ALL2 IL2AUX_permf stack' (wl_state_stack t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_jump_exc_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; case_eq "stack_frame"] @ IL2AUX_res_rws) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  MP_TAC (ISPECL [`IL2AUX_permf:(A)stack_frame->(A)stack_frame->bool`; `stack:((A)stack_frame)list`;
                  `wl_state_stack (s:(A,C,FFI)wl_state)`; `wl_state_handler (s:(A,C,FFI)wl_state)
                      + 1`]
                 list_rel_lastn) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[IL2AUX_ALL2_CONS_R] THEN
  DISCH_THEN(X_CHOOSE_THEN `fr:(A)stack_frame` (X_CHOOSE_THEN `tl:((A)stack_frame)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC (ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  DISCH_THEN(X_CHOOSE_THEN `m':num option` (X_CHOOSE_THEN `e0':(num#(A)word_loc)list`
    (X_CHOOSE_THEN `e':(num#(A)word_loc)list` (X_CHOOSE_THEN `h':(num#num#num)option`
       SUBST_ALL_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IL2AUX_permf_thm]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    IL2AUX_has_tm `h':(num#num#num)option` th)) THEN
  RVEQ_TAC THEN EXISTS_TAC `tl:((A)stack_frame)list` THEN
  REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  TRY (AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC PERM_fromAList THEN
       ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC PERM_fromAList THEN ASM_REWRITE_TAC[]);;

(* the stack relation keeps the stack size *)

let IL2AUX_permf_eq = prove
 (CASE_TERM
  `(\s1 s2:(A)stack_frame. match (s1,s2) with
      (StackFrame ss l env h, StackFrame ss' l' env' h') ->
        ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\ ALL_DISTINCT (MAP FST env)) =
   IL2AUX_permf`,
  REWRITE_TAC[FUN_EQ_THM; IL2AUX_permf_def]);;

let IL2AUX_stack_size_permf = prove
 (`!l1 l2:((A)stack_frame)list.
     ALL2 IL2AUX_permf l1 l2 ==> wl_stack_size l1 = wl_stack_size l2`,
  REWRITE_TAC[GSYM IL2AUX_permf_eq; stack_size_perm]);;

let IL2AUX_call_env_stack_size = prove
 (`!args ss (s:(A,C,FFI)wl_state) xs.
     wl_stack_size xs = wl_stack_size (wl_state_stack s)
     ==> wl_call_env args ss (wl_state_stack_fupd (K xs) s) =
         wl_state_stack_fupd (K xs) (wl_call_env args ss s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wl_call_env_def; wl_state_component_equality] THEN SIMP[]);;

(* push_env with another oracle and a related stack *)

let IL2AUX_push_env_ps2 = prove
 (`!envs b (s:(A,C,FFI)wl_state) perm stack.
     ALL2 IL2AUX_permf stack (wl_state_stack s)
     ==> ?fr. wl_push_env envs b (wl_state_permute_fupd (K perm) (wl_state_stack_fupd (K stack)
         s)) =
              wl_state_permute_fupd (K (\n. perm (n + 1)))
                (wl_state_stack_fupd (K (CONS fr stack)) (wl_push_env envs b s)) /\
              ALL2 IL2AUX_permf (CONS fr stack) (wl_state_stack (wl_push_env envs b s))`,
  GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IL2AUX_stack_size_permf) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  SIMP[] THEN
  W(fun (_,w) -> let tm = find_term (fun t -> is_comb t && IL2AUX_kind_name t = "CONS" &&
                                               rand t = `stack:((A)stack_frame)list`) w in
                 EXISTS_TAC (rand (rator tm))) THEN
  REWRITE_TAC[ALL2; IL2AUX_permf_thm] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REWRITE_RULE[FST] (CONV_RULE (TOP_DEPTH_CONV let_CONV)
                (REWRITE_RULE[env_to_list_def] env_to_list_PERM));
              REWRITE_RULE[FST] (CONV_RULE (TOP_DEPTH_CONV let_CONV)
                (REWRITE_RULE[env_to_list_def] env_to_list_ALL_DISTINCT_FST))] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[stack_size_eq2; stack_size_frame_def]);;

let IL2AUX_call_ps2 = prove
 (`!args1 ss envs b (s:(A,C,FFI)wl_state) perm stack.
     ALL2 IL2AUX_permf stack (wl_state_stack s)
     ==> ?fr. wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock
                (wl_state_permute_fupd (K perm) (wl_state_stack_fupd (K stack) s)))) =
              wl_state_permute_fupd (K (\n. perm (n + 1)))
                (wl_state_stack_fupd (K (CONS fr stack))
                   (wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock s)))) /\
              ALL2 IL2AUX_permf (CONS fr stack)
                (wl_state_stack (wl_call_env args1 ss (wl_push_env envs b (wl_dec_clock s))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IL2AUX_dec_clock_permute; IL2AUX_dec_clock_stack] THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `b:(num#(A)wl_prog#num#num)option`;
                  `wl_dec_clock (s:(A,C,FFI)wl_state)`; `perm:num->num->num`;
                  `stack:((A)stack_frame)list`] IL2AUX_push_env_ps2) THEN
  ASM_REWRITE_TAC[wl_dec_clock_const] THEN
  DISCH_THEN(X_CHOOSE_THEN `fr:(A)stack_frame` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fr:(A)stack_frame` THEN ASM_REWRITE_TAC[wl_call_env_const] THEN
  REWRITE_TAC[wl_call_env_with_const] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IL2AUX_call_env_stack_size THEN
  MATCH_MP_TAC IL2AUX_stack_size_permf THEN ASM_REWRITE_TAC[]);;

let IL2AUX_pop_env_ps2 = prove
 (`!(t:(A,C,FFI)wl_state) t1 q stk.
     wl_pop_env t = SOME t1 /\ ALL2 IL2AUX_permf stk (wl_state_stack t)
     ==> ?stk1. wl_pop_env (wl_state_permute_fupd (K q) (wl_state_stack_fupd (K stk) t)) =
                  SOME (wl_state_permute_fupd (K q) (wl_state_stack_fupd (K stk1) t1)) /\
                ALL2 IL2AUX_permf stk1 (wl_state_stack t1)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `wl_state_stack (t:(A,C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[wl_pop_env_def; th] THEN SIMP[])
    (X_CHOOSE_THEN `f:(A)stack_frame` (X_CHOOSE_THEN `rest:((A)stack_frame)list`
       ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[IL2AUX_ALL2_CONS_R] THEN STRIP_TAC THEN
  EXISTS_TAC `xs:((A)stack_frame)list` THEN
  MP_TAC (ISPECL [`t:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`; `f:(A)stack_frame`;
                  `rest:((A)stack_frame)list`] IL2AUX_pop_env_stack) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> IL2AUX_kind_name (lhs (concl th)) = "wl_pop_env")) THEN
  MP_TAC (ISPEC `f:(A)stack_frame` (cases "stack_frame")) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `l0:(num#(A)word_loc)list`
    (X_CHOOSE_THEN `e:(num#(A)word_loc)list` (X_CHOOSE_THEN `h:(num#num#num)option`
       SUBST_ALL_TAC)))) THEN
  MP_TAC (ISPEC `x:(A)stack_frame` (cases "stack_frame")) THEN
  DISCH_THEN(X_CHOOSE_THEN `m':num option` (X_CHOOSE_THEN `l0':(num#(A)word_loc)list`
    (X_CHOOSE_THEN `e':(num#(A)word_loc)list` (X_CHOOSE_THEN `h':(num#num#num)option`
       SUBST_ALL_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IL2AUX_permf_thm]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[wl_pop_env_def] THEN SIMP[] THEN
  STRUCT_CASES_TAC (ISPEC `h:(num#num#num)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:num#num#num` PAIR_SURJECTIVE)) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `y:num#num` PAIR_SURJECTIVE)) THEN
  SIMP[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  (SUBGOAL_THEN `fromAList (e':(num#(A)word_loc)list) = fromAList e` SUBST1_TAC THENL
    [MATCH_MP_TAC PERM_fromAList THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[option_INJ; wl_state_component_equality] THEN SIMP[]));;

(* the callee state of a tail call and the stack_max of a call at clock 0, *)
(* with another oracle and a related stack                                  *)

let IL2AUX_call_dec_ps2 = prove
 (`!args ss (s:(A,C,FFI)wl_state) perm stack.
     wl_stack_size stack = wl_stack_size (wl_state_stack s)
     ==> wl_call_env args ss (wl_dec_clock (wl_state_permute_fupd (K perm)
                                             (wl_state_stack_fupd (K stack) s))) =
         wl_state_permute_fupd (K perm)
           (wl_state_stack_fupd (K stack) (wl_call_env args ss (wl_dec_clock s)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IL2AUX_dec_clock_permute; IL2AUX_dec_clock_stack] THEN
  REWRITE_TAC[wl_call_env_with_const] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IL2AUX_call_env_stack_size THEN ASM_REWRITE_TAC[wl_dec_clock_const]);;

let IL2AUX_call_sm_ps2 = prove
 (`!args1 ss envs b (s:(A,C,FFI)wl_state) perm stack.
     ALL2 IL2AUX_permf stack (wl_state_stack s)
     ==> wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs b
           (wl_state_permute_fupd (K perm) (wl_state_stack_fupd (K stack) s)))) =
         wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs b s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `b:(num#(A)wl_prog#num#num)option`;
                  `s:(A,C,FFI)wl_state`; `perm:num->num->num`; `stack:((A)stack_frame)list`]
                 IL2AUX_push_env_ps2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `fr:(A)stack_frame` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[wl_call_env_with_const] THEN
  SUBGOAL_THEN
   `wl_call_env args1 ss (wl_state_stack_fupd (K (CONS (fr:(A)stack_frame) stack))
      (wl_push_env envs b (s:(A,C,FFI)wl_state))) =
    wl_state_stack_fupd (K (CONS fr stack)) (wl_call_env args1 ss (wl_push_env envs b s))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC IL2AUX_call_env_stack_size THEN
    MATCH_MP_TAC IL2AUX_stack_size_permf THEN ASM_REWRITE_TAC[];
    SIMP[]]);;

let IL2AUX_cut_state_code = prove
 (`!x (s:(A,C,FFI)wl_state) s'.
     wl_cut_state x s = SOME s' ==> wl_state_code s' = wl_state_code s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP cut_state_const) THEN
  SIMP[]);;

(* the tactics of the cases *)

let IL2AUX_PS2_SPLIT_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`)));;

let IL2AUX_TRANSP_FACTS_TAC : tactic =
  FIRST_ASSUM(fun ev -> if IL2AUX_is_eval_eq (concl ev) then
    FIRST_ASSUM(fun ne -> if is_neg (concl ne) &&
                             IL2AUX_kind_name (rhs (rand (concl ne))) = "SOME" then
      FIRST (map (fun th -> try STRIP_ASSUME_TAC (MATCH_MP th (CONJ ev ne))
                            with Failure _ -> NO_TAC)
              (CONJUNCTS IL2AUX_evaluate_transp_facts))
    else failwith "") else failwith "");;
let IL2AUX_PS2_TRANSP_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN IL2AUX_TRANSP_FACTS_TAC THEN
  MATCH_MP_TAC IL2AUX_ps2_simple THEN
  REWRITE_TAC[IL2AUX_evaluate_ps_with] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_MESON_TAC[];;

let IL2AUX_PS2_RAISE_TAC : tactic =
  IL2AUX_PS2_SPLIT_TAC THEN
  FIRST_ASSUM(fun j -> if IL2AUX_kind_name (lhs (concl j)) = "wl_jump_exc" then
    FIRST_ASSUM(fun a -> if IL2AUX_kind_name (concl a) = "ALL2" then
      MP_TAC (SPEC `perm:num->num->num` (MATCH_MP IL2AUX_jump_exc_permf (CONJ j a)))
      else failwith "") else failwith "") THEN
  DISCH_THEN(X_CHOOSE_THEN `stk':((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`perm:num->num->num`; `stk':((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[];;

let IL2AUX_PS2_RWS = no_alloc_def :: wordConvs_no_install_def :: IL2AUX_dec_rws;;

(* forward chaining through the induction hypotheses of permute_swap_lemma2: *)
(* the antecedents are discharged by the facts, by pattern equations and by  *)
(* rewriting with the facts; the stack relation stays an antecedent and the  *)
(* conclusion is not rewritten                                                *)

let IL2AUX_PS2_ACC_RWS = IL2AUX_res_rws @
  [wl_state_INFO.ri_accfupds; K_THM; wl_call_env_const; wl_push_env_const; wl_dec_clock_const;
   wl_set_var_const; wl_set_vars_const; flush_state_const; wl_STOP_def; no_alloc_def;
   wordConvs_no_install_def];;

let IL2AUX_fwd_ps2 (facts:thm list) (ih:thm) : thm =
  let simple = filter (fun th -> not (is_forall (concl th)) && not (is_imp (concl th))) facts in
  let rec go th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = fst (dest_imp bod) in
    if IL2AUX_kind_name ant = "ALL2" then th else
    try tryfind (fun f -> go (MATCH_MP th f)) facts
    with Failure _ ->
    try go (IL2AUX_fwd_eq th) with Failure _ ->
      if exists (fun v -> vfree_in v ant) vs then failwith "IL2AUX_fwd_ps2" else
      let ath = EQT_ELIM (REWRITE_CONV (IL2AUX_PS2_ACC_RWS @ simple) ant) in
      go (MP (SPEC_ALL th) ath) in
  go (REWRITE_RULE[IMP_CONJ] ih);;

let IL2AUX_is_ps2_inst th =
  let vs,bod = strip_forall (concl th) in
  is_imp bod && IL2AUX_kind_name (fst (dest_imp bod)) = "ALL2";;

let IL2AUX_PS2_IHS_TAC : tactic =
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else CASE_REWRITE_RULE []
                                   (REWRITE_RULE [no_alloc_def; wordConvs_no_install_def]
                                      (CASE_REWRITE_RULE [] th))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) || IL2AUX_is_ps2_inst ih
    then failwith "" else
    let th = IL2AUX_fwd_ps2 (map snd asl) ih in
    if IL2AUX_is_ps2_inst th then ASSUME_TAC th g else failwith "")) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if (is_forall (concl th) || is_imp (concl th)) &&
                                      not (IL2AUX_is_ps2_inst th) then ALL_TAC
                                   else failwith ""));;

(* the code of the final state of an evaluation is the code of its initial *)
(* state (no_install_evaluate_const_code), oriented from the later state    *)

let IL2AUX_PS2_CODE_TAC : tactic = fun (asl,w as g) ->
  let simple = filter (fun th -> not (is_forall (concl th)) && not (is_imp (concl th)))
                 (map snd asl) in
  let evs = filter (fun th -> IL2AUX_is_eval_eq (concl th)) simple in
  let derive ev =
    let p = fst (dest_pair (rand (lhs (concl ev)))) in
    let s' = snd (dest_pair (rand (lhs (concl ev)))) in
    let ni = find (fun th -> IL2AUX_kind_name (concl th) = "wordConvs_no_install" &&
                             rand (concl th) = p) simple in
    let nic_tm = mk_comb (`no_install_code:(num#(A)wl_prog)spt->bool`,
                   mk_comb (`wl_state_code:(A,C,FFI)wl_state->(num#(A)wl_prog)spt`, s')) in
    let nic = EQT_ELIM (REWRITE_CONV (IL2AUX_PS2_ACC_RWS @ simple) nic_tm) in
    REWRITE_RULE IL2AUX_PS2_ACC_RWS
      (SYM (MATCH_MP no_install_evaluate_const_code (CONJ ev (CONJ ni nic)))) in
  MAP_EVERY (fun ev -> try ASSUME_TAC (derive ev) with Failure _ -> ALL_TAC) evs g;;

let IL2AUX_PS2_PREP_TAC : tactic =
  IL2AUX_PS2_SPLIT_TAC THEN IL2AUX_NOERR_TAC THEN
  IL2AUX_FACTS_TAC [IL2AUX_cut_state_code; IL2AUX_cut_state_stack_handler] THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else CASE_REWRITE_RULE []
                                   (REWRITE_RULE [no_alloc_def; wordConvs_no_install_def]
                                      (CASE_REWRITE_RULE [] th))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  IL2AUX_LEMMA_FWD_TAC [no_alloc_find_code; no_install_find_code] THEN
  IL2AUX_POP_CONST_TAC THEN
  IL2AUX_PS2_CODE_TAC THEN IL2AUX_PS2_CODE_TAC THEN IL2AUX_PS2_IHS_TAC;;

let IL2AUX_PS2_IH_FOR_TAC (prog:term) (perm:term) (stk:term) (pv:string) (sv:string) : tactic =
  fun (asl,w as g) ->
    let ih = snd (find (fun (_,th) -> IL2AUX_is_ps2_inst th &&
      (let vs,bod = strip_forall (concl th) in
       let _,eb = strip_exists (snd (dest_imp bod)) in
       fst (dest_pair (rand (lhs (fst (dest_conj eb))))) = prog)) asl) in
    let th = SPECL [perm; stk] ih in
    let ant = fst (dest_imp (concl th)) in
    (SUBGOAL_THEN ant (fun ath ->
       X_CHOOSE_THEN (mk_var(pv, `:num->num->num`))
         (X_CHOOSE_THEN (mk_var(sv, `:((A)stack_frame)list`)) STRIP_ASSUME_TAC) (MP th ath))
     THENL [ASM_REWRITE_TAC IL2AUX_PS2_RWS THEN SIMP[] THEN NO_TAC; ALL_TAC]) g;;

let IL2AUX_PS2_FIN1_TAC (pv:term) (sv:term) : tactic =
  MAP_EVERY EXISTS_TAC [pv; sv] THEN
  RULE_ASSUM_TAC (fun th -> if IL2AUX_is_eval_eq (concl th)
                            then CAKE_SIMP_RULE [wl_dec_clock_def; wl_STOP_def] th else th) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[wl_dec_clock_def; wl_STOP_def] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP[wl_dec_clock_def; wl_STOP_def; wl_flush_state_def; ALL2] THEN
  NO_TAC;;
let IL2AUX_PS2_FIN_TAC (pv:string) (sv:string) : tactic =
  FIRST [IL2AUX_PS2_FIN1_TAC (mk_var(pv, `:num->num->num`)) (mk_var(sv, `:((A)stack_frame)list`));
         IL2AUX_PS2_FIN1_TAC (mk_var(pv, `:num->num->num`)) `[]:((A)stack_frame)list`];;
let IL2AUX_PS2_SEQ_TAC : tactic =
  IL2AUX_PS2_PREP_TAC THEN
  FIRST [IL2AUX_PS2_IH_FOR_TAC `c1:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
           "p1" "st1" THEN
         IL2AUX_PS2_IH_FOR_TAC `c2:(A)wl_prog` `p1:num->num->num` `st1:((A)stack_frame)list`
           "p2" "st2" THEN
         IL2AUX_PS2_FIN_TAC "p2" "st2" THEN NO_TAC;
         IL2AUX_PS2_IH_FOR_TAC `c1:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
           "p1" "st1" THEN
         IL2AUX_PS2_FIN_TAC "p1" "st1"];;
let IL2AUX_PS2_IF_TAC : tactic =
  IL2AUX_PS2_PREP_TAC THEN
  FIRST [IL2AUX_PS2_IH_FOR_TAC `c1:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
           "p1" "st1";
         IL2AUX_PS2_IH_FOR_TAC `c2:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
           "p1" "st1"] THEN
  IL2AUX_PS2_FIN_TAC "p1" "st1";;
let IL2AUX_PS2_LOOP_TAC : tactic =
  IL2AUX_PS2_PREP_TAC THEN
  FIRST [IL2AUX_PS2_IH_FOR_TAC `c:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
           "p1" "st1" THEN
         IL2AUX_PS2_IH_FOR_TAC `wl_STOP (wl_Loop names c exit_names):(A)wl_prog`
           `p1:num->num->num` `st1:((A)stack_frame)list` "p2" "st2" THEN
         IL2AUX_PS2_FIN_TAC "p2" "st2" THEN NO_TAC;
         IL2AUX_PS2_IH_FOR_TAC `c:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
           "p1" "st1" THEN
         IL2AUX_PS2_FIN_TAC "p1" "st1"];;
let IL2AUX_PS2_MT_TAC : tactic =
  IL2AUX_PS2_PREP_TAC THEN
  IL2AUX_PS2_IH_FOR_TAC `p:(A)wl_prog` `perm:num->num->num` `stack:((A)stack_frame)list`
    "p1" "st1" THEN
  IL2AUX_PS2_FIN_TAC "p1" "st1";;

(* Call: the instance at perm and stk of the hypothesis whose state is made *)
(* by the function h0, with the chosen oracle and stack called pv and sv     *)

let IL2AUX_PS2_IH_ST_TAC (h0:string) (perm:term) (stk:term) (pv:string) (sv:string) : tactic =
  fun (asl,w as g) ->
    let ih = snd (find (fun (_,th) -> IL2AUX_is_ps2_inst th &&
      (let vs,bod = strip_forall (concl th) in
       let _,eb = strip_exists (snd (dest_imp bod)) in
       let st = snd (dest_pair (rand (lhs (fst (dest_conj eb))))) in
       IL2AUX_kind_name (rand (rand st)) = h0)) asl) in
    let th = SPECL [perm; stk] ih in
    let ant = fst (dest_imp (concl th)) in
    (SUBGOAL_THEN ant (fun ath ->
       X_CHOOSE_THEN (mk_var(pv, `:num->num->num`))
         (X_CHOOSE_THEN (mk_var(sv, `:((A)stack_frame)list`)) STRIP_ASSUME_TAC) (MP th ath))
     THENL [ASM_REWRITE_TAC IL2AUX_PS2_RWS THEN SIMP[] THEN NO_TAC; ALL_TAC]) g;;

(* the callee state of a returning call *)

let IL2AUX_PS2_CALLSTATE_TAC : tactic = fun (asl,w as g) ->
  let facts = map (concl o snd) asl in
  let fc = find (fun t -> is_eq t && IL2AUX_kind_name (lhs t) = "wl_find_code") facts in
  let args1,rest = dest_pair (rand (rhs fc)) in
  let prog,ss = dest_pair rest in
  let ce = find (fun t -> is_eq t && IL2AUX_kind_name (lhs t) = "cut_envs") facts in
  let envs = rand (rhs ce) in
  let _,bod = strip_exists w in
  let callp = fst (dest_pair (rand (lhs (fst (dest_conj bod))))) in
  let handler = rand callp in
  let st0 = snd (dest_pair (rand (lhs (fst (dest_conj bod))))) in
  let perm = rand (rand (rator st0)) in
  let stk = rand (rand (rator (rand st0))) in
  let s = rand (rand st0) in
  let th = ISPECL [args1; ss; envs; handler; s; perm; stk] IL2AUX_call_ps2 in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `fr:(A)stack_frame` STRIP_ASSUME_TAC)) g;;

let IL2AUX_PS2_POP_TAC (q:term) : tactic =
  FIRST_ASSUM(fun pop -> if IL2AUX_kind_name (lhs (concl pop)) = "wl_pop_env" then
    FIRST_ASSUM(fun a -> if IL2AUX_kind_name (concl a) = "ALL2" &&
                            not (IL2AUX_is_ps2_inst a) &&
                            rand (concl a) =
                              mk_comb (`wl_state_stack:(A,C,FFI)wl_state->((A)stack_frame)list`,
                                       rand (lhs (concl pop)))
      then X_CHOOSE_THEN `stk1:((A)stack_frame)list` STRIP_ASSUME_TAC
             (SPEC q (MATCH_MP IL2AUX_pop_env_ps2 (CONJ pop a)))
      else failwith "") else failwith "");;

(* the stack size of the new stack and the call states of the new run *)

let IL2AUX_PS2_CALLRW_TAC : tactic =
  FIRST_ASSUM(fun a -> if IL2AUX_kind_name (concl a) = "ALL2" && not (IL2AUX_is_ps2_inst a) &&
                          rand (concl a) = `wl_state_stack (s:(A,C,FFI)wl_state)`
    then ASSUME_TAC (GEN_ALL (MATCH_MP IL2AUX_call_dec_ps2
                                (MATCH_MP IL2AUX_stack_size_permf a))) THEN
         ASSUME_TAC (GEN_ALL (MATCH_MP IL2AUX_call_sm_ps2 a))
    else failwith "");;

let IL2AUX_PS2_CALL_FIN_TAC (pv:term) (sv:term) : tactic =
  MAP_EVERY EXISTS_TAC [pv; sv] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_vars_with_const] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SIMP[wl_flush_state_def; ALL2] THEN
  RULE_ASSUM_TAC (fun th -> if IL2AUX_is_eval_eq (concl th) then CAKE_SIMP_RULE [] th else th) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN NO_TAC;;

let IL2AUX_PS2_CALL_TAC : tactic =
  IL2AUX_PS2_PREP_TAC THEN IL2AUX_PS2_CALLRW_TAC THEN
  FIRST
   [IL2AUX_PS2_CALL_FIN_TAC `perm:num->num->num` `[]:((A)stack_frame)list`;
    IL2AUX_PS2_IH_ST_TAC "wl_call_env" `perm:num->num->num` `stack:((A)stack_frame)list`
      "p1" "st1" THEN
    IL2AUX_PS2_CALL_FIN_TAC `p1:num->num->num` `st1:((A)stack_frame)list`;
    IL2AUX_PS2_CALLSTATE_TAC THEN
    IL2AUX_PS2_IH_ST_TAC "wl_call_env" `\n. (perm:num->num->num) (n + 1)`
      `CONS (fr:(A)stack_frame) stack` "p2" "st2" THEN
    FIRST
     [IL2AUX_PS2_POP_TAC `p2:num->num->num` THEN
      IL2AUX_PS2_IH_ST_TAC "wl_set_vars" `p2:num->num->num` `stk1:((A)stack_frame)list`
        "p3" "st3" THEN
      IL2AUX_PS2_CALL_FIN_TAC `p3:num->num->num` `st3:((A)stack_frame)list`;
      IL2AUX_PS2_IH_ST_TAC "wl_set_var" `p2:num->num->num` `st2:((A)stack_frame)list`
        "p3" "st3" THEN
      IL2AUX_PS2_CALL_FIN_TAC `p3:num->num->num` `st3:((A)stack_frame)list`;
      IL2AUX_PS2_CALL_FIN_TAC `p2:num->num->num` `st2:((A)stack_frame)list`]];;

let IL2AUX_PS2_ALLOC_TAC : tactic = REPEAT GEN_TAC THEN REWRITE_TAC[no_alloc_def];;

let IL2AUX_permute_swap2 = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst.
     wl_evaluate (prog,st) = (res,rst) /\ ~(res = SOME wl_Error) /\
     no_alloc_code (wl_state_code st) /\ no_alloc prog /\
     no_install_code (wl_state_code st) /\ wordConvs_no_install prog
     ==> !perm stack.
           ALL2 IL2AUX_permf stack (wl_state_stack st)
           ==> ?perm' stack'.
                 wl_evaluate (prog, wl_state_permute_fupd (K perm)
                                      (wl_state_stack_fupd (K stack) st)) =
                 (res, wl_state_permute_fupd (K perm') (wl_state_stack_fupd (K stack') rst)) /\
                 ALL2 IL2AUX_permf stack' (wl_state_stack rst)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   ([IL2AUX_PS2_TRANSP_TAC; IL2AUX_PS2_ALLOC_TAC] @ replicate IL2AUX_PS2_TRANSP_TAC 9 @
    [IL2AUX_PS2_MT_TAC; IL2AUX_PS2_SEQ_TAC; IL2AUX_PS2_TRANSP_TAC; IL2AUX_PS2_RAISE_TAC] @
    replicate IL2AUX_PS2_TRANSP_TAC 2 @ [IL2AUX_PS2_IF_TAC; IL2AUX_PS2_LOOP_TAC] @
    replicate IL2AUX_PS2_TRANSP_TAC 6 @ [IL2AUX_PS2_CALL_TAC]));;

let permute_swap_lemma2 = prove
 (CASE_TERM
  `!prog (st:(A,C,FFI)wl_state) perm stack.
     let (res,rst) = wl_evaluate (prog,st) in
       ~(res = SOME wl_Error) /\ no_alloc_code (wl_state_code st) /\ no_alloc prog /\
       no_install_code (wl_state_code st) /\ wordConvs_no_install prog /\
       ALL2 (\s1 s2. match (s1,s2) with
                       (StackFrame ss l env h, StackFrame ss' l' env' h') ->
                         ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\
                         ALL_DISTINCT (MAP FST env))
            stack (wl_state_stack st)
       ==> ?perm' stack'.
             wl_evaluate (prog, wl_state_permute_fupd (K perm)
                                  (wl_state_stack_fupd (K stack) st)) =
               (res, wl_state_permute_fupd (K perm') (wl_state_stack_fupd (K stack') rst)) /\
             ALL2 (\s1 s2. match (s1,s2) with
                             (StackFrame ss l env h, StackFrame ss' l' env' h') ->
                               ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\
                               ALL_DISTINCT (MAP FST env))
                  stack' (wl_state_stack rst)`,
  REWRITE_TAC[IL2AUX_permf_eq] THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`] IL2AUX_permute_swap2) THEN
  SPEC_TAC(`wl_evaluate (prog:(A)wl_prog,st:(A,C,FFI)wl_state)`,
           `p:((A)wl_result)option#(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

let permute_swap_lemma3 = prove
 (CASE_TERM
  `!prog (st:(A,C,FFI)wl_state) perm (stack:((A)stack_frame)list).
     let (res,rst) = wl_evaluate (prog,st) in
       ~(res = SOME wl_Error) /\ no_alloc_code (wl_state_code st) /\ no_alloc prog /\
       no_install_code (wl_state_code st) /\ wordConvs_no_install prog /\
       ALL (\fr. match fr with StackFrame _ _ vs handler -> ALL_DISTINCT (MAP FST vs))
           (wl_state_stack st)
       ==> ?perm' stack'.
             wl_evaluate (prog, wl_state_permute_fupd (K perm) st) =
               (res, wl_state_permute_fupd (K perm') (wl_state_stack_fupd (K stack') rst)) /\
             ALL2 (\s1 s2. match (s1,s2) with
                             (StackFrame ss l env h, StackFrame ss' l' env' h') ->
                               ss = ss' /\ h = h' /\ l = l' /\ PERM env env' /\
                               ALL_DISTINCT (MAP FST env))
                  stack' (wl_state_stack rst)`,
  REWRITE_TAC[IL2AUX_permf_eq] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN (CASE_TERM
   `!l:((A)stack_frame)list.
      ALL (\fr. match fr with StackFrame _ _ vs handler -> ALL_DISTINCT (MAP FST vs)) l
      ==> ALL2 IL2AUX_permf l l`) ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ALL2] THEN
    STRUCT_CASES_TAC (ISPEC `h:(A)stack_frame` (cases "stack_frame")) THEN
    SIMP[IL2AUX_permf_thm; PERM_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`] IL2AUX_permute_swap2) THEN
  SPEC_TAC(`wl_evaluate (prog:(A)wl_prog,st:(A,C,FFI)wl_state)`,
           `p:((A)wl_result)option#(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p1:((A)wl_result)option`; `p2:(A,C,FFI)wl_state`] o
    check (fun th -> is_forall (concl th) && IL2AUX_has_tm `prog:(A)wl_prog` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`perm:num->num->num`; `wl_state_stack (st:(A,C,FFI)wl_state)`]) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_stack_fupd (K (wl_state_stack st)) (st:(A,C,FFI)wl_state) = st`
    SUBST1_TAC THENL
   [REWRITE_TAC[wl_state_component_equality] THEN SIMP[]; REWRITE_TAC[]]);;

let word_cmp_Word_Word = prove
 (`wl_word_cmp cmp (wl_Word (c:A word)) (wl_Word c') = SOME (asm_word_cmp cmp c c')`,
  STRUCT_CASES_TAC (ISPEC `cmp:cmp` (cases "cmp")) THEN
  REWRITE_TAC[wl_word_cmp_def; asm_word_cmp_def]);;

let _ = cake_add_simps [word_cmp_Word_Word];;
