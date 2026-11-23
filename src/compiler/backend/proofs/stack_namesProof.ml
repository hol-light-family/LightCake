(* ========================================================================= *)
(* stack_namesProof: port of HOL4 compiler/backend/proofs/                  *)
(* stack_namesProofScript.sml (CakeML v3479).                                *)
(* Correctness proof for stack_names.                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 Overload find_name = tlookup (stack_names.ml): written out.        *)
(* - HOL4 s with <| f1 := v1; ... |> is stack_state_f1_fupd (K v1) (...),    *)
(*   in the order of the HOL4 record literal.                               *)
(* - STACKPROPSAUX_ names are local helpers (the unit's helper prefix).      *)

let rename_state_def = cake_def
  `rename_state compile_rest f (s:(A,C,FFI)stack_state) =
     stack_state_regs_fupd (K (MAP_KEYS (tlookup f) (stack_state_regs s)))
       (stack_state_code_fupd
          (K (fromAList (stack_names_compile f (toAList (stack_state_code s)))))
       (stack_state_compile_fupd (K compile_rest)
       (stack_state_compile_oracle_fupd
          (K ((I ## stack_names_compile f ## I) o stack_state_compile_oracle s))
       (stack_state_ffi_save_regs_fupd
          (K (IMAGE (tlookup f) (stack_state_ffi_save_regs s))) s))))`;;

let rename_state_with_clock = prove
 (`rename_state c f (stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
   stack_state_clock_fupd (K k) (rename_state c f s)`,
  REWRITE_TAC[rename_state_def] THEN SIMP[]);;

let rename_state_const = prove
 (`stack_state_memory (rename_state c f (s:(A,C,FFI)stack_state)) = stack_state_memory s /\
   stack_state_be (rename_state c f s) = stack_state_be s /\
   stack_state_mdomain (rename_state c f s) = stack_state_mdomain s /\
   stack_state_sh_mdomain (rename_state c f s) = stack_state_sh_mdomain s /\
   stack_state_code_buffer (rename_state c f s) = stack_state_code_buffer s /\
   stack_state_clock (rename_state c f s) = stack_state_clock s /\
   stack_state_compile (rename_state c f s) = c /\
   stack_state_use_stack (rename_state c f s) = stack_state_use_stack s /\
   stack_state_fp_regs (rename_state c f s) = stack_state_fp_regs s`,
  REWRITE_TAC[rename_state_def] THEN SIMP[]);;
let _ = cake_add_simps [rename_state_const];;

let rename_state_with_memory = prove
 (`rename_state c f (stack_state_memory_fupd (K k) (s:(A,C,FFI)stack_state)) =
   stack_state_memory_fupd (K k) (rename_state c f s)`,
  REWRITE_TAC[rename_state_def] THEN SIMP[]);;

let dec_clock_rename_state = prove
 (`stack_dec_clock (rename_state c x (y:(A,C,FFI)stack_state)) =
   rename_state c x (stack_dec_clock y)`,
  REWRITE_TAC[rename_state_def; stack_dec_clock_def] THEN SIMP[]);;

let mem_load_rename_state = prove
 (`stack_mem_load x (rename_state c f (s:(A,C,FFI)stack_state)) = stack_mem_load x s`,
  REWRITE_TAC[stack_mem_load_def] THEN SIMP[]);;
let _ = cake_add_simps [mem_load_rename_state];;

let mem_store_rename_state = prove
 (`stack_mem_store x y (rename_state c f (s:(A,C,FFI)stack_state)) =
   OPTION_MAP (rename_state c f) (stack_mem_store x y s)`,
  REWRITE_TAC[stack_mem_store_def] THEN SIMP[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ; rename_state_def] THEN SIMP[]);;
let _ = cake_add_simps [mem_store_rename_state];;

(* a bijection is injective on any set *)

let STACKPROPSAUX_BIJ_INJ = prove
 (`!(f:A->B) s. BIJ f UNIV UNIV ==> INJ f s UNIV`,
  REWRITE_TAC[BIJ; INJ; IN_UNIV] THEN MESON_TAC[]);;

let get_var_find_name = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_get_var (tlookup f v) (rename_state c f (s:(A,C,FFI)stack_state)) =
   stack_get_var v s`,
  REWRITE_TAC[stack_get_var_def; rename_state_def] THEN SIMP[] THEN
  DISCH_TAC THEN MATCH_MP_TAC FLOOKUP_MAP_KEYS_MAPPED THEN
  ASM_SIMP_TAC[STACKPROPSAUX_BIJ_INJ]);;
let _ = cake_add_simps [get_var_find_name];;


let get_var_imm_find_name = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_get_var_imm (ri_find_name f ri) (rename_state c f (s:(A,C,FFI)stack_state)) =
   stack_get_var_imm ri s`,
  DISCH_TAC THEN CASES_ON `ri:(A)reg_imm` THEN
  ASM_SIMP_TAC[ri_find_name_def; stack_get_var_imm_def; get_var_find_name]);;
let _ = cake_add_simps [get_var_imm_find_name];;

let FLOOKUP_rename_state_find_name = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   FLOOKUP (stack_state_regs (rename_state c f (s:(A,C,FFI)stack_state))) (tlookup f k) =
   FLOOKUP (stack_state_regs s) k`,
  REWRITE_TAC[rename_state_def] THEN SIMP[] THEN
  DISCH_TAC THEN MATCH_MP_TAC FLOOKUP_MAP_KEYS_MAPPED THEN
  ASM_SIMP_TAC[STACKPROPSAUX_BIJ_INJ]);;
let _ = cake_add_simps [FLOOKUP_rename_state_find_name];;

let STACKPROPSAUX_SH_RENAME_TAC def : tactic =
  DISCH_TAC THEN
  REWRITE_TAC[def; stack_get_var_def; rename_state_def] THEN
  SIMP[MAP_KEYS_FUPDATE; FLOOKUP_MAP_KEYS_MAPPED; STACKPROPSAUX_BIJ_INJ] THEN
  EVERY_CASE_TAC THEN
  SIMP[MAP_KEYS_FUPDATE; FLOOKUP_MAP_KEYS_MAPPED; STACKPROPSAUX_BIJ_INJ];;

let sh_mem_load_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_load (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_load x y s),rename_state c f (SND (stack_sh_mem_load x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_load_def);;
let _ = cake_add_simps [sh_mem_load_rename_state];;

let sh_mem_store_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_store (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_store x y s):((A)stack_result)option,
    rename_state c f (SND (stack_sh_mem_store x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_store_def);;
let _ = cake_add_simps [sh_mem_store_rename_state];;

let sh_mem_load_byte_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_load_byte (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_load_byte x y s),
    rename_state c f (SND (stack_sh_mem_load_byte x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_load_byte_def);;
let _ = cake_add_simps [sh_mem_load_byte_rename_state];;

let sh_mem_store_byte_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_store_byte (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_store_byte x y s),
    rename_state c f (SND (stack_sh_mem_store_byte x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_store_byte_def);;
let _ = cake_add_simps [sh_mem_store_byte_rename_state];;

let sh_mem_load16_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_load16 (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_load16 x y s),
    rename_state c f (SND (stack_sh_mem_load16 x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_load16_def);;
let _ = cake_add_simps [sh_mem_load16_rename_state];;

let sh_mem_store16_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_store16 (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_store16 x y s),
    rename_state c f (SND (stack_sh_mem_store16 x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_store16_def);;
let _ = cake_add_simps [sh_mem_store16_rename_state];;

let sh_mem_load32_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_load32 (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_load32 x y s),
    rename_state c f (SND (stack_sh_mem_load32 x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_load32_def);;
let _ = cake_add_simps [sh_mem_load32_rename_state];;

let sh_mem_store32_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_sh_mem_store32 (tlookup f x) y (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (stack_sh_mem_store32 x y s),
    rename_state c f (SND (stack_sh_mem_store32 x y s)))`,
  STACKPROPSAUX_SH_RENAME_TAC stack_sh_mem_store32_def);;
let _ = cake_add_simps [sh_mem_store32_rename_state];;

let sh_mem_op_rename_store = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   sh_mem_op op (tlookup f r) a (rename_state c f (s:(A,C,FFI)stack_state)) =
   (FST (sh_mem_op op r a s),rename_state c f (SND (sh_mem_op op r a s)))`,
  DISCH_TAC THEN CASES_ON `op:memop` THEN REWRITE_TAC[sh_mem_op_def] THEN
  ASM_SIMP_TAC[sh_mem_load_rename_state; sh_mem_store_rename_state;
               sh_mem_load_byte_rename_state; sh_mem_store_byte_rename_state;
               sh_mem_load16_rename_state; sh_mem_store16_rename_state;
               sh_mem_load32_rename_state; sh_mem_store32_rename_state]);;
let _ = cake_add_simps [sh_mem_op_rename_store];;

(* HOL4 [local] *)

let stack_namesProof_prog_comp_eta = prove
 (`stack_names_prog_comp f = \(x,y:(A)stack_prog). (x,stack_names_comp f y)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; stack_names_prog_comp_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let STACKPROPSAUX_lookup_rename_code = prove
 (`!n. lookup n (stack_state_code (rename_state c f (s:(A,C,FFI)stack_state))) =
       OPTION_MAP (stack_names_comp f) (lookup n (stack_state_code s))`,
  REWRITE_TAC[rename_state_def] THEN SIMP[] THEN
  REWRITE_TAC[lookup_fromAList; stack_names_compile_def; stack_namesProof_prog_comp_eta;
              ALOOKUP_MAP; o_THM; ALOOKUP_toAList; ETA_AX]);;

let find_code_rename_state = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_find_code (dest_find_name f dest)
     (stack_state_regs (rename_state c f (s:(A,C,FFI)stack_state)))
     (stack_state_code (rename_state c f s)) =
   OPTION_MAP (stack_names_comp f)
     (stack_find_code dest (stack_state_regs s) (stack_state_code s))`,
  DISCH_TAC THEN CASES_ON `dest:num+num` THEN
  REWRITE_TAC[dest_find_name_def; stack_find_code_def;
              STACKPROPSAUX_lookup_rename_code] THEN
  ASM_SIMP_TAC[FLOOKUP_rename_state_find_name] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; STACKPROPSAUX_lookup_rename_code]);;
let _ = cake_add_simps [find_code_rename_state];;

let set_var_find_name = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   rename_state c f (stack_set_var x y (z:(A,C,FFI)stack_state)) =
   stack_set_var (tlookup f x) y (rename_state c f z)`,
  DISCH_TAC THEN REWRITE_TAC[stack_set_var_def; rename_state_def] THEN
  SIMP[MAP_KEYS_FUPDATE; STACKPROPSAUX_BIJ_INJ]);;

let set_fp_var_find_name = prove
 (`rename_state c f (stack_set_fp_var x y (z:(A,C,FFI)stack_state)) =
   stack_set_fp_var x y (rename_state c f z)`,
  REWRITE_TAC[stack_set_fp_var_def; rename_state_def] THEN SIMP[]);;

(* rewrites that move rename_state outwards, for inst_rename *)

let STACKPROPSAUX_rename_rws = prove
 (`(BIJ (tlookup f) UNIV UNIV ==>
    !x y. (tlookup f x = tlookup f y <=> x = y)) /\
   (BIJ (tlookup f) UNIV UNIV ==>
    !x y. stack_set_var (tlookup f x) y (rename_state c f (z:(A,C,FFI)stack_state)) =
          rename_state c f (stack_set_var x y z)) /\
   (!x y. stack_set_fp_var x y (rename_state c f (z:(A,C,FFI)stack_state)) =
          rename_state c f (stack_set_fp_var x y z)) /\
   (!m. stack_state_memory_fupd (K m) (rename_state c f (z:(A,C,FFI)stack_state)) =
        rename_state c f (stack_state_memory_fupd (K m) z)) /\
   (!d. stack_get_fp_var d (rename_state c f (z:(A,C,FFI)stack_state)) =
        stack_get_fp_var d z)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIJ; INJ; IN_UNIV] THEN MESON_TAC[];
    MESON_TAC[set_var_find_name];
    REWRITE_TAC[set_fp_var_find_name];
    REWRITE_TAC[rename_state_with_memory];
    REWRITE_TAC[stack_get_fp_var_def] THEN SIMP[]]);;

let STACKPROPSAUX_INST_RENAME_TAC : tactic =
  REWRITE_TAC[inst_find_name_def; ri_find_name_def; stack_inst_def] THEN
  CASE_REWRITE_TAC[] THEN
  SIMP[STACKPROPSAUX_rename_rws; stack_word_exp_def; FLOOKUP_rename_state_find_name;
       ri_find_name_def; stack_assign_def; stack_get_vars_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC THEN
          SIMP[STACKPROPSAUX_rename_rws; OPTION_MAP_DEF; LET_DEF; LET_END_DEF]) THEN
  FS[OPTION_MAP_DEF];;

let inst_rename = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_inst (inst_find_name f i) (rename_state c f (s:(A,C,FFI)stack_state)) =
   OPTION_MAP (rename_state c f) (stack_inst i s)`,
  DISCH_TAC THEN CASES_ON `i:(A)inst` THENL
   [STACKPROPSAUX_INST_RENAME_TAC;
    STACKPROPSAUX_INST_RENAME_TAC;
    CASES_ON `a:(A)asm_arith` THEN
    TRY (CASES_ON `a3:(A)reg_imm`) THEN STACKPROPSAUX_INST_RENAME_TAC;
    CASES_ON `a2:(A)addr` THEN CASES_ON `a0:memop` THEN STACKPROPSAUX_INST_RENAME_TAC;
    CASES_ON `a:fp` THEN STACKPROPSAUX_INST_RENAME_TAC]);;

(* the equations of stack_names_comp for each constructor *)

let STACKPROPSAUX_comp_thms =
  let ci = case_info_of_tyname "stack_prog" in
  let ty = `:(A)stack_prog` in
  let f = `f:num spt` in
  let c = `stack_names_comp:num spt->(A)stack_prog->(A)stack_prog` in
  end_itlist CONJ
   (map (fun (vs,pat) ->
          let tyi = type_match (type_of pat) ty [] in
          let pat = inst tyi pat in
          let tm = mk_comb(mk_comb(c,f),pat) in
          GEN_ALL ((REWR_CONV stack_names_comp_def THENC CASE_REWRITE_CONV[]) tm))
        ci.ci_pats);;

let stack_namesProof_MAP_FST_compile = prove
 (`MAP FST (stack_names_compile f (c:(num#(A)stack_prog)list)) = MAP FST c`,
  REWRITE_TAC[stack_names_compile_def; MAP_MAP_o] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM;
                                       stack_names_prog_comp_def]);;
let _ = cake_add_simps [stack_namesProof_MAP_FST_compile];;

let domain_rename_state_code = prove
 (`domain (stack_state_code (rename_state c f (s:(A,C,FFI)stack_state))) =
   domain (stack_state_code s)`,
  REWRITE_TAC[rename_state_def] THEN SIMP[] THEN
  REWRITE_TAC[domain_fromAList; stack_namesProof_MAP_FST_compile;
              set_MAP_FST_toAList_domain]);;
let _ = cake_add_simps [domain_rename_state_code];;

(* HOL4 [local] *)

let comp_STOP_Loop = prove
 (`stack_names_comp f (stack_STOP (stack_Loop c1)) =
   stack_STOP (stack_Loop (stack_names_comp f (c1:(A)stack_prog)))`,
  REWRITE_TAC[stack_STOP_def; STACKPROPSAUX_comp_thms]);;

(* the induction hypotheses of stack_names_comp_ind after a case split *)

let STACKPROPSAUX_IH_RWS =
  [distinctness "stack_prog"; injectivity "stack_prog"; option_INJ;
   option_DISTINCT; PAIR_EQ; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
   FORALL_UNWIND_THM2];;

(* HOL4 [local] *)

let stack_namesProof_get_labels_comp = prove
 (`!f (p:(A)stack_prog). stack_get_labels (stack_names_comp f p) = stack_get_labels p`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_IH_RWS) THEN
  SIMP[stack_get_labels_def]);;

(* HOL4 [local] *)

let loc_check_rename_state = prove
 (`loc_check (stack_state_code (rename_state c f (s:(A,C,FFI)stack_state))) (l1,l2) =
   loc_check (stack_state_code s) (l1,l2)`,
  REWRITE_TAC[loc_check_def; domain_rename_state_code; STACKPROPSAUX_lookup_rename_code] THEN
  REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN
  MESON_TAC[stack_namesProof_get_labels_comp]);;

(* the fields that rename_state keeps, and helpers for comp_correct *)

let STACKPROPSAUX_rename_acc = prove
 (`stack_state_fp_regs (rename_state c f (s:(A,C,FFI)stack_state)) =
     stack_state_fp_regs s /\
   stack_state_store (rename_state c f s) = stack_state_store s /\
   stack_state_stack (rename_state c f s) = stack_state_stack s /\
   stack_state_stack_space (rename_state c f s) = stack_state_stack_space s /\
   stack_state_memory (rename_state c f s) = stack_state_memory s /\
   stack_state_mdomain (rename_state c f s) = stack_state_mdomain s /\
   stack_state_sh_mdomain (rename_state c f s) = stack_state_sh_mdomain s /\
   stack_state_bitmaps (rename_state c f s) = stack_state_bitmaps s /\
   stack_state_code_buffer (rename_state c f s) = stack_state_code_buffer s /\
   stack_state_data_buffer (rename_state c f s) = stack_state_data_buffer s /\
   stack_state_gc_fun (rename_state c f s) = stack_state_gc_fun s /\
   stack_state_use_stack (rename_state c f s) = stack_state_use_stack s /\
   stack_state_use_store (rename_state c f s) = stack_state_use_store s /\
   stack_state_use_alloc (rename_state c f s) = stack_state_use_alloc s /\
   stack_state_clock (rename_state c f s) = stack_state_clock s /\
   stack_state_ffi (rename_state c f s) = stack_state_ffi s /\
   stack_state_be (rename_state c f s) = stack_state_be s /\
   stack_state_compile (rename_state c f s) = c /\
   stack_state_regs (rename_state c f s) = MAP_KEYS (tlookup f) (stack_state_regs s) /\
   stack_state_ffi_save_regs (rename_state c f s) =
     IMAGE (tlookup f) (stack_state_ffi_save_regs s) /\
   stack_state_compile_oracle (rename_state c f s) =
     (I ## stack_names_compile f ## I) o stack_state_compile_oracle s`,
  REWRITE_TAC[rename_state_def] THEN SIMP[]);;

let STACKPROPSAUX_empty_env_rename = prove
 (`stack_empty_env (rename_state c f (s:(A,C,FFI)stack_state)) =
   rename_state c f (stack_empty_env s)`,
  REWRITE_TAC[stack_empty_env_def; rename_state_def] THEN SIMP[MAP_KEYS_FEMPTY]);;

let STACKPROPSAUX_find_code_rename_gen = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_find_code (dest_find_name f dest) (MAP_KEYS (tlookup f) (R:(num,(A)word_loc)fmap))
     (stack_state_code (rename_state c f (s:(A,C,FFI)stack_state))) =
   OPTION_MAP (stack_names_comp f) (stack_find_code dest R (stack_state_code s))`,
  DISCH_TAC THEN CASES_ON `dest:num+num` THEN
  REWRITE_TAC[dest_find_name_def; stack_find_code_def;
              STACKPROPSAUX_lookup_rename_code] THEN
  ASM_SIMP_TAC[FLOOKUP_MAP_KEYS_MAPPED; STACKPROPSAUX_BIJ_INJ] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; STACKPROPSAUX_lookup_rename_code]);;

let STACKPROPSAUX_find_code_INL_rename = prove
 (`stack_find_code (INL d) (stack_state_regs (rename_state c f (s:(A,C,FFI)stack_state)))
     (stack_state_code (rename_state c f s)) =
   OPTION_MAP (stack_names_comp f)
     (stack_find_code (INL d) (stack_state_regs s) (stack_state_code s))`,
  REWRITE_TAC[stack_find_code_def; STACKPROPSAUX_lookup_rename_code]);;

let STACKPROPSAUX_dest_Seq_comp = prove
 (`!p:(A)stack_prog.
     stack_dest_Seq (stack_names_comp f p) =
     OPTION_MAP (\(a,b). (stack_names_comp f a,stack_names_comp f b)) (stack_dest_Seq p)`,
  GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms; stack_dest_Seq_def; OPTION_MAP_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[stack_dest_Seq_def]);;

let STACKPROPSAUX_lookup_compile = prove
 (`!n (t:((A)stack_prog)spt).
     lookup n (fromAList (stack_names_compile f (toAList t))) =
     OPTION_MAP (stack_names_comp f) (lookup n t)`,
  REWRITE_TAC[lookup_fromAList; stack_names_compile_def; stack_namesProof_prog_comp_eta;
              ALOOKUP_MAP; o_THM; ALOOKUP_toAList; ETA_AX]);;

let STACKPROPSAUX_install_code = prove
 (`fromAList (stack_names_compile f
      (toAList (sptree_union (t:((A)stack_prog)spt) (insert k p (fromAList l))))) =
   sptree_union (fromAList (stack_names_compile f (toAList t)))
     (insert k (stack_names_comp f p) (fromAList (stack_names_compile f l)))`,
  W(fun (_,w) -> MP_TAC(ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  SIMP_TAC[wf_fromAList; wf_union; wf_insert] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[STACKPROPSAUX_lookup_compile; lookup_union; lookup_insert] THEN
  REWRITE_TAC[lookup_fromAList; stack_names_compile_def; stack_namesProof_prog_comp_eta;
              ALOOKUP_MAP; o_THM; ETA_AX] THEN
  CASES_ON `lookup n (t:((A)stack_prog)spt)` THEN
  REWRITE_TAC[option_CASE; OPTION_MAP_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF]);;

let STACKPROPSAUX_dec_clock_rename_rev = prove
 (`stack_dec_clock (rename_state c f (s:(A,C,FFI)stack_state)) =
   rename_state c f (stack_dec_clock s)`,
  REWRITE_TAC[dec_clock_rename_state]);;

let STACKPROPSAUX_word_exp_rename_addr = prove
 (`BIJ (tlookup f) UNIV UNIV ==>
   stack_word_exp (rename_state c f (s:(A,C,FFI)stack_state))
     (wl_Op asm_Add [wl_Var (tlookup f a); wl_Const w]) =
   stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w])`,
  DISCH_TAC THEN REWRITE_TAC[stack_word_exp_def; MAP; ALL] THEN
  ASM_SIMP_TAC[FLOOKUP_rename_state_find_name]);;

let STACKPROPSAUX_compile_clauses = prove
 (`stack_names_compile f ([]:(num#(A)stack_prog)list) = [] /\
   stack_names_compile f (CONS (k,p:(A)stack_prog) l) =
   CONS (k,stack_names_comp f p) (stack_names_compile f l)`,
  REWRITE_TAC[stack_names_compile_def; MAP; stack_names_prog_comp_def]);;

(* rewrite the assumptions with an assumption stack_state_compile s = g *)

let STACKPROPSAUX_COMPILE_EQ_TAC : tactic =
  ASSUM_LIST (fun ths ->
    let ceqs = filter (fun th -> is_eq (concl th) &&
                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                      "stack_state_compile" with Failure _ -> false) &&
                 is_abs (rhs (concl th))) ths in
    if ceqs = [] then ALL_TAC else
    RULE_ASSUM_TAC (fun a -> if exists (fun c -> concl c = concl a) ceqs then a
                             else REWRITE_RULE (o_THM :: STACKPROPSAUX_compile_clauses ::
                                                ceqs) a));;

let STACKPROPSAUX_COMP_SIMPS =
  [STACKPROPSAUX_rename_rws; STACKPROPSAUX_rename_acc; STACKPROPSAUX_empty_env_rename;
   STACKPROPSAUX_find_code_rename_gen; STACKPROPSAUX_find_code_INL_rename;
   STACKPROPSAUX_dest_Seq_comp; STACKPROPSAUX_lookup_rename_code;
   STACKPROPSAUX_dec_clock_rename_rev; comp_STOP_Loop; inst_rename;
   loc_check_rename_state; get_var_find_name; get_var_imm_find_name;
   sh_mem_op_rename_store; DOMSUB_MAP_KEYS; DRESTRICT_MAP_KEYS_IMAGE;
   STACKPROPSAUX_BIJ_INJ; FLOOKUP_MAP_KEYS_MAPPED; STACKPROPSAUX_word_exp_rename_addr;
   dest_find_name_def;
   ri_find_name_def; STACKPROPSAUX_compile_clauses; OPTION_MAP_DEF; PAIR_MAP_THM; I_THM;
   shift_seq_def; o_THM; FST_PAIR_MAP; SND_PAIR_MAP; LET_DEF; LET_END_DEF];;

(* close a goal whose assumptions contain some p and ~p *)

let STACKPROPSAUX_CONTR_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  try let th' = find (fun th' -> is_neg (concl th') &&
                        exists (fun th -> concl th = dest_neg (concl th')) ths) ths in
      let th = find (fun th -> concl th = dest_neg (concl th')) ths in
      CONTR_TAC (MP (NOT_ELIM th') th) g
  with Failure _ -> ALL_TAC g;;

let STACKPROPSAUX_not_none = prove
 (`!x:A option. ~(x = NONE) <=> ?y. x = SOME y`,
  GEN_TAC THEN CASES_ON `x:A option` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let STACKPROPSAUX_NOT_NONE_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    match concl th with
      Comb(Const("~",_),Comb(Comb(Const("=",_),v),Const("NONE",_))) when is_var v ->
        CAKE_STRIP_ASSUME_TAC (REWRITE_RULE[STACKPROPSAUX_not_none] th)
    | _ -> failwith "keep")) THEN RVEQ_TAC;;

(* normalise the unfolded goal by rewriting (the kit's SIMP can fail with  *)
(* CHOOSE on a pair_CASE of an evaluation that an assumption decides): the *)
(* lemmas that move rename_state outwards, instantiated at the BIJ         *)
(* assumption, then the assumptions and the case rewrites                  *)

let STACKPROPSAUX_COMP_NORM_TAC : tactic =
  ASSUM_LIST (fun ths ->
    let bij = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "BIJ"
                                with Failure _ -> false) ths in
    let conds = CONJUNCTS STACKPROPSAUX_rename_rws @
                [STACKPROPSAUX_find_code_rename_gen; get_var_find_name;
                 get_var_imm_find_name; sh_mem_op_rename_store; DOMSUB_MAP_KEYS;
                 DRESTRICT_MAP_KEYS_IMAGE; inst_rename;
                 STACKPROPSAUX_word_exp_rename_addr] in
    let insts = flat (map (fun b -> mapfilter (fun l -> MATCH_MP l b) conds) bij) in
    REWRITE_TAC (insts @
      [STACKPROPSAUX_dec_clock_rename_rev; STACKPROPSAUX_empty_env_rename;
       STACKPROPSAUX_find_code_INL_rename; STACKPROPSAUX_dest_Seq_comp;
       STACKPROPSAUX_lookup_rename_code; comp_STOP_Loop; loc_check_rename_state;
       STACKPROPSAUX_compile_clauses; dest_find_name_def; ri_find_name_def])) THEN
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]));;

let STACKPROPSAUX_COMP_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (STACKPAUX_is_eval_eq o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[stack_evaluate_def] THENC
           REWRITE_CONV(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_TIDY_TAC THEN
  STACKPROPSAUX_NOT_NONE_TAC THEN REPEAT PAIRARG_TAC THEN RVEQ_TAC THEN
  STACKPROPSAUX_CONTR_TAC THEN STACKPROPSAUX_COMPILE_EQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES]) THEN
  STACKPROPSAUX_FACTS_TAC [stack_evaluate_consts] THEN
  STACKPROPSAUX_USE_IHS_TAC (SIMP[] THEN NO_TAC) THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[comp_STOP_Loop]) THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  REPEAT PAIRARG_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  STACKPROPSAUX_COMP_NORM_TAC THEN
  SIMP STACKPROPSAUX_COMP_SIMPS THEN
  TRY (REWRITE_TAC[rename_state_def] THEN
       SIMP[MAP_KEYS_FUPDATE; STACKPROPSAUX_BIJ_INJ; STACKPROPSAUX_install_code;
            o_DEF]);;

(* HOL4 [local] *)

let stack_namesProof_comp_correct = prove
 (`!p (s:(A,C,FFI)stack_state) r t.
     stack_evaluate (p,s) = (r,t) /\ BIJ (tlookup f) UNIV UNIV /\
     ~stack_state_use_alloc s /\ ~stack_state_use_store s /\ ~stack_state_use_stack s /\
     stack_state_compile s = (\cfg. c cfg o stack_names_compile f)
     ==> stack_evaluate (stack_names_comp f p,rename_state c f s) =
         (r,rename_state c f t)`,
  STACKPROPSAUX_EVAL_IND_TAC THEN STACKPROPSAUX_COMP_TAC);;

(* the runs of the semantics: comp_correct for the program of stack_semantics *)

let STACKPROPSAUX_semantics_run = prove
 (`BIJ (tlookup f) UNIV UNIV /\ ~stack_state_use_alloc s /\ ~stack_state_use_store s /\
   ~stack_state_use_stack s /\
   stack_state_compile s = (\cfg. c cfg o stack_names_compile f)
   ==> !k. stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                           stack_state_clock_fupd (K k) (rename_state c f s)) =
           (FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                 stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))),
            rename_state c f (SND (stack_evaluate (stack_Call NONE (INL start) NONE,
                                                   stack_state_clock_fupd (K k) s))))`,
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM rename_state_with_clock] THEN
  MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                 `stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)`;
                 `FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                       stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)))`;
                 `SND (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                       stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)))`]
          (INST [`c:C->(num#(A)stack_prog)list->(byte list#C)option`,
                 `c:C->(num#(A)stack_prog)list->(byte list#C)option`]
                stack_namesProof_comp_correct)) THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms; dest_find_name_def] THEN CASE_REWRITE_TAC[] THEN
  SIMP[]);;

let stack_namesProof_compile_semantics = prove
 (`BIJ (tlookup f) UNIV UNIV /\ ~stack_state_use_alloc s /\ ~stack_state_use_store s /\
   ~stack_state_use_stack s /\
   stack_state_compile s = (\cfg. c cfg o stack_names_compile f)
   ==> stack_semantics start (rename_state c f (s:(A,C,FFI)stack_state)) =
       stack_semantics start s`,
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP STACKPROPSAUX_semantics_run th)) THEN
  ASM_REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[FST; SND; STACKPROPSAUX_rename_acc] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `res:behaviour` THEN
  REWRITE_TAC[PAIR_EQ] THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`k:num`;
      `SND (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                            stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)))`;
      `r:(A)stack_result`; `outcome:outcome`] THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[STACKPROPSAUX_rename_acc; BASICAUX_PAIR_SND];
    MAP_EVERY EXISTS_TAC
     [`k:num`; `rename_state c f (t:(A,C,FFI)stack_state)`;
      `r:(A)stack_result`; `outcome:outcome`] THEN
    ASM_REWRITE_TAC[STACKPROPSAUX_rename_acc]]);;

(* HOL4 [local] *)

let compile_semantics_alt = prove
 (`!(s:(A,C,FFI)stack_state) t.
     BIJ (tlookup f) UNIV UNIV /\ rename_state (stack_state_compile t) f s = t /\
     stack_state_compile s = (\c. stack_state_compile t c o stack_names_compile f) /\
     ~stack_state_use_alloc s /\ ~stack_state_use_store s /\ ~stack_state_use_stack s
     ==> stack_semantics start t = stack_semantics start s`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "rename_state"
                     with Failure _ -> false)) THEN
  MATCH_MP_TAC stack_namesProof_compile_semantics THEN ASM_REWRITE_TAC[]);;

let stack_namesProof_make_init_def = cake_def
  `stack_namesProof_make_init f code oracle (s:(A,C,FFI)stack_state) =
     stack_state_code_fupd (K code)
     (stack_state_regs_fupd (K (MAP_KEYS (LINV (tlookup f) UNIV) (stack_state_regs s)))
     (stack_state_compile_fupd
        (K (\cfg. stack_state_compile s cfg o stack_names_compile f))
     (stack_state_compile_oracle_fupd (K oracle)
     (stack_state_ffi_save_regs_fupd
        (K (IMAGE (LINV (tlookup f) UNIV) (stack_state_ffi_save_regs s))) s))))`;;

(* HOL4 finite_map MAP_KEYS_BIJ_LINV (a theorem of the finite_map library *)
(* that hol4/finite_map.ml lacks)                                          *)

let STACKPROPSAUX_MAP_KEYS_BIJ_LINV = prove
 (`!f (t:(num,B)fmap).
     BIJ (f:num->num) UNIV UNIV ==> MAP_KEYS f (MAP_KEYS (LINV f UNIV) t) = t`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun bij ->
    let inv = REWRITE_RULE[IN_UNIV] (MATCH_MP BIJ_LINV_INV bij) in
    let bijg = MATCH_MP BIJ_LINV_BIJ bij in
    let injf = SPEC `(:num)` (MATCH_MP STACKPROPSAUX_BIJ_INJ bij) in
    let injg = SPEC `(:num)` (MATCH_MP STACKPROPSAUX_BIJ_INJ bijg) in
    REWRITE_TAC[fmap_eq_flookup] THEN X_GEN_TAC `x:num` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM (SPEC `x:num` inv)] THEN
    REWRITE_TAC[MATCH_MP FLOOKUP_MAP_KEYS_MAPPED injf;
                MATCH_MP FLOOKUP_MAP_KEYS_MAPPED injg]));;

let STACKPROPSAUX_IMAGE_LINV = prove
 (`!f (s:num->bool).
     BIJ (f:num->num) UNIV UNIV ==> IMAGE f (IMAGE (LINV f UNIV) s) = s`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun bij ->
    let inv = REWRITE_RULE[IN_UNIV] (MATCH_MP BIJ_LINV_INV bij) in
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; inv; IMAGE_ID]));;

let stack_namesProof_make_init_semantics = prove
 (`~stack_state_use_alloc s /\ ~stack_state_use_store s /\ ~stack_state_use_stack s /\
   BIJ (tlookup f) UNIV UNIV /\ ALL_DISTINCT (MAP FST code) /\
   stack_state_code s = fromAList (stack_names_compile f code) /\
   stack_state_compile_oracle s = (I ## stack_names_compile f ## I) o oracle
   ==> stack_semantics start (s:(A,C,FFI)stack_state) =
       stack_semantics start (stack_namesProof_make_init f (fromAList code) oracle s)`,
  STRIP_TAC THEN MATCH_MP_TAC compile_semantics_alt THEN
  ASM_REWRITE_TAC[stack_namesProof_make_init_def] THEN SIMP[] THEN
  REWRITE_TAC[rename_state_def; stack_state_component_equality] THEN SIMP[] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_MAP_KEYS_BIJ_LINV; STACKPROPSAUX_IMAGE_LINV] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  SIMP_TAC[wf_fromAList] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_lookup_compile; lookup_fromAList; stack_names_compile_def;
              stack_namesProof_prog_comp_eta; ALOOKUP_MAP; o_THM; ETA_AX]);;

let stack_names_lab_pres = prove
 (`!f (p:(A)stack_prog).
     stack_extract_labels p = stack_extract_labels (stack_names_comp f p)`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_IH_RWS) THEN
  SIMP[stack_extract_labels_def; LET_DEF; LET_END_DEF]);;

(* HOL4 [local] *)

let names_ok_imp = prove
 (`stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) ==>
   !n. reg_name n (c:(A)asm_config) ==> reg_ok (tlookup f n) c`,
  REWRITE_TAC[stack_names_names_ok_def; LET_DEF; LET_END_DEF; EVERY_GENLIST;
              reg_name_def; reg_ok_def] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)

let names_ok_imp2 = prove
 (`stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
   ~(n = n') /\ reg_name n (c:(A)asm_config) /\ reg_name n' c ==>
   ~(tlookup f n = tlookup f n')`,
  REWRITE_TAC[stack_names_names_ok_def; LET_DEF; LET_END_DEF; ALL_DISTINCT_GENLIST;
              reg_name_def] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_tlookup_inj_name = prove
 (`stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
   reg_name n (c:(A)asm_config) /\ reg_name n' c
   ==> (tlookup f n = tlookup f n' <=> n = n')`,
  MESON_TAC[names_ok_imp2]);;

let STACKPROPSAUX_reg_ok_name = prove
 (`stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
   reg_name n (c:(A)asm_config) ==> reg_ok (tlookup f n) c`,
  MESON_TAC[names_ok_imp]);;

(* case split on a boolean term t, rewriting the goal and the other        *)
(* assumptions with t or ~t                                                 *)

let STACKPROPSAUX_BOOL_CASES_TAC (t:term) : tactic =
  ASM_CASES_TAC t THEN
  FIRST_ASSUM (fun th ->
    if concl th = t || concl th = mk_neg t then
      RULE_ASSUM_TAC (fun a -> if concl a = concl th then a else REWRITE_RULE[th] a)
    else failwith "") THEN
  ASM_REWRITE_TAC[];;

(* the facts reg_ok (tlookup f n) c and (tlookup f n = tlookup f n' <=>     *)
(* n = n') for the assumptions reg_name n c, as rewrites of the goal        *)

let STACKPROPSAUX_NAME_FACTS_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let is_c n th = try fst(dest_const(fst(strip_comb(concl th)))) = n
                  with Failure _ -> false in
  let nok = find (is_c "stack_names_names_ok") ths in
  let rns = filter (is_c "reg_name") ths in
  let oks = map (fun rn -> MATCH_MP STACKPROPSAUX_reg_ok_name (CONJ nok rn)) rns in
  let injs = flat (map (fun rn -> map (fun rn' ->
                 MATCH_MP STACKPROPSAUX_tlookup_inj_name (CONJ nok (CONJ rn rn'))) rns)
               rns) in
  let oks' = flat (map (CONJUNCTS o REWRITE_RULE[reg_ok_def]) oks) in
  REWRITE_TAC (oks @ oks' @ injs) g;;

(* the Inst case of stack_names_comp_stack_asm_ok *)

let STACKPROPSAUX_inst_name_ok = prove
 (`stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
   fixed_names f (c:(A)asm_config) /\ inst_name c i
   ==> inst_ok (inst_find_name f i) c`,
  STRIP_TAC THEN
  SUBGOAL_THEN `asm_config_ISA (c:(A)asm_config) = x86_64 ==>
                tlookup f 3 = 2 /\ tlookup f 4 = 1 /\ tlookup f 0 = 0` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `fixed_names f (c:(A)asm_config)` THEN
    ASM_REWRITE_TAC[fixed_names_def]; ALL_TAC] THEN
  UNDISCH_TAC `inst_name c (i:(A)inst)` THEN
  CASES_ON `i:(A)inst` THENL
   [REWRITE_TAC[inst_find_name_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[inst_ok_def];
    REWRITE_TAC[inst_find_name_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[inst_ok_def; inst_name_def] THEN DISCH_TAC THEN
    STACKPROPSAUX_NAME_FACTS_TAC;
    CASES_ON `a:(A)asm_arith` THEN TRY (CASES_ON `a3:(A)reg_imm`) THEN
    REWRITE_TAC[inst_find_name_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[inst_ok_def; inst_name_def; arith_name_def;
                arith_ok_def; ri_find_name_def; reg_imm_name_def; reg_imm_ok_def;
                IN_INSERT; NOT_IN_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "reg_imm"; distinctness "reg_imm"]) THEN
    REWRITE_TAC[injectivity "reg_imm"; distinctness "reg_imm"] THEN
    STACKPROPSAUX_NAME_FACTS_TAC THEN
    STACKPROPSAUX_BOOL_CASES_TAC `asm_config_ISA (c:(A)asm_config) = x86_64` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[distinctness "architecture"]) THEN
    ASM_REWRITE_TAC[distinctness "architecture"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
    STACKPROPSAUX_NAME_FACTS_TAC THEN ASM_MESON_TAC[];
    CASES_ON `a2:(A)addr` THEN
    REWRITE_TAC[inst_find_name_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[inst_ok_def; inst_name_def; addr_name_def] THEN
    STRIP_TAC THEN STACKPROPSAUX_NAME_FACTS_TAC THEN ASM_REWRITE_TAC[];
    CASES_ON `a:fp` THEN
    REWRITE_TAC[inst_find_name_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[inst_ok_def; inst_name_def; fp_name_def; fp_ok_def] THEN STRIP_TAC THEN
    STACKPROPSAUX_BOOL_CASES_TAC `dimindex(:A) = 32` THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    STACKPROPSAUX_NAME_FACTS_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)

let stack_names_comp_stack_asm_ok = prove
 (`!f (p:(A)stack_prog).
     stack_asm_name c p /\
     stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
     fixed_names f c ==> stack_asm_ok c (stack_names_comp f p)`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  TRY (REWRITE_TAC[stack_asm_ok_def] THEN MATCH_MP_TAC STACKPROPSAUX_inst_name_ok THEN
       ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
         try fst(dest_const t) = "stack_asm_name" with Failure _ -> false)) (concl th) &&
         not (is_forall (concl th)))) THEN
       REWRITE_TAC[stack_asm_name_def] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (stack_asm_name_def :: addr_name_def :: STACKPROPSAUX_IH_RWS)) THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o
                 REWRITE_RULE (stack_asm_name_def :: addr_name_def :: STACKPROPSAUX_IH_RWS)) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[stack_asm_ok_def; addr_ok_def; dest_find_name_def; GSYM reg_ok_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_asm_ok_def; addr_ok_def; dest_find_name_def; GSYM reg_ok_def] THEN
  STACKPROPSAUX_NAME_FACTS_TAC THEN ASM_REWRITE_TAC[] THEN
  RES_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let stack_names_stack_asm_ok = prove
 (`ALL (\(n,p). stack_asm_name c p) (prog:(num#(A)stack_prog)list) /\
   stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
   fixed_names f c ==>
   ALL (\(n,p). stack_asm_ok c p) (stack_names_compile f prog)`,
  REWRITE_TAC[stack_names_compile_def; ALL_MAP] THEN STRIP_TAC THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\(n:num,p:(A)stack_prog). stack_asm_name c p` THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_names_prog_comp_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC stack_names_comp_stack_asm_ok THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_call_args_comp = prove
 (`!f (q:(A)stack_prog).
     call_args q 1 2 3 4 0 ==>
     call_args (stack_names_comp f q) (tlookup f 1) (tlookup f 2) (tlookup f 3)
       (tlookup f 4) (tlookup f 0)`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[call_args_def] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE (call_args_def :: STACKPROPSAUX_IH_RWS)) THEN
  REWRITE_TAC[call_args_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RES_TAC THEN ASM_REWRITE_TAC[]);;

let stack_names_call_args = prove
 (`stack_names_compile f p = p' /\
   ALL (\p. call_args p 1 2 3 4 0) (MAP SND (p:(num#(A)stack_prog)list)) ==>
   ALL (\p. call_args p (tlookup f 1) (tlookup f 2) (tlookup f 3) (tlookup f 4)
                        (tlookup f 0)) (MAP SND p')`,
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[stack_names_compile_def; MAP_MAP_o; ALL_MAP] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; SND;
                                         stack_names_prog_comp_def] THEN
  REWRITE_TAC[STACKPROPSAUX_call_args_comp]);;
