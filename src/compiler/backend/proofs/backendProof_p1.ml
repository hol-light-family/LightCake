(* ========================================================================= *)
(* backendProof_p1: part 1 of 2 (HOL4 lines 1-2278) of the port of HOL4     *)
(* compiler/backend/proofs/backendProofScript.sml (CakeML v3479).  Composes *)
(* the correctness theorems for all of the compiler phases.                  *)
(* The parts _p1 and _p2 are loaded one after the other (_p2 needs this     *)
(* one).  BKP1AUX_ names are local helpers of this part.                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as in names.tsv: backend's compile is backend_compile, its       *)
(*   config record backend_config (fields backend_config_source_conf ...),  *)
(*   its progs record backend_progs; the passes are called by their port    *)
(*   names (clos_known$compile is clos_known_compile, clos_to_bvl$compile   *)
(*   clos_to_bvl_compile, clos_to_bvl$compile_inc clos_to_bvl_compile_inc'  *)
(*   (clos_to_bvl$clos_to_bvl_compile_inc is clos_to_bvl_compile_inc),     *)
(*   word_to_word$compile word_to_word_compile, word_to_stack$compile and   *)
(*   compile_prog word_to_stack_compile ..., stack_to_lab$compile           *)
(*   stack_to_lab_compile, lab_to_target$compile lab_to_target_compile,     *)
(*   data_to_word$compile data_to_word_compile, bvl_to_bvi$compile_prog     *)
(*   bvl_to_bvi_compile_prog, the prog_comp of stack_remove, stack_alloc,   *)
(*   stack_names stack_remove_prog_comp ...).  This script's               *)
(*   is_safe_for_space, read_limits and compile_correct are                 *)
(*   backendProof_is_safe_for_space, backendProof_read_limits and           *)
(*   backendProof_compile_correct.                                           *)
(* - The local Overloads of the script (HOL4 lines 175-199: bvl_inline_     *)
(*   compile_prog ... no_mti, and mk_flat_install_conf at line 3046) are    *)
(*   abbreviations of names that the port has anyway.                        *)
(* - find_name (stack_names Overload) is tlookup; f PERMUTES s is           *)
(*   BIJ f s s; addr_offset_ok c w, hw_offset_ok, byte_offset_ok (asm       *)
(*   Overloads) are asm_offset_ok 0 (asm_config_addr_offset c) w and so on; *)
(*   the asm binops Add, Sub are asm_Add, asm_Sub; n2w is word, w2n val,    *)
(*   -8w is word_neg (word 8), <= on words word_ile; "NOTFOUND" is          *)
(*   implode "NOTFOUND"; max_heap_limit and conf_ok take the universe (:A). *)
(* - Library: EVERY = ALL, LIST_REL = ALL2, set = set_of_list, BIGUNION =    *)
(*   UNIONS, FOLDR f e l = ITLIST f l e, GENLIST = list_of_seq; ++ is       *)
(*   APPEND (left-associative); r with f := x is RECTYPE_f_fupd (K x) r, r  *)
(*   with f updated_by g is RECTYPE_f_fupd g r, r with <| f1 := x; f2 := y |>*)
(*   is RECTYPE_f1_fupd (K x) (RECTYPE_f2_fupd (K y) r); Abbrev (x = e) is  *)
(*   x = e; ZIP (l1,l2) is ZIP l1 l2 (compile_word_to_stack_sfs_aux zips    *)
(*   lists of equal lengths).                                                *)
(* - ML values that are terms (cake_orac_config_inv_f, line 404) are         *)
(*   written out where HOL4 antiquotes them; ML values that are theorems    *)
(*   are stated and proved (cake_orac_config_tuple_eq_step) or derived as    *)
(*   HOL4 derives them (the eight conjuncts source_to_flat_orac_eq ...       *)
(*   stack_to_lab_orac_eq of cake_orac_eqs, simple_orac_eqs and the other    *)
(*   derived bindings); lists of theorems (semantics_thms, from_EXS) and     *)
(*   tactics are comments.                                                   *)
(* - HOL4's unused binders are left out (EVERY_no_mti_IMP_obeys_max_app e3, *)
(*   cake_configs_eq i).                                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/proofs/primSemEnv.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/proofs/source_to_sourceProof.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
needs "compiler/backend/proofs/source_to_flatProof.ml";;
needs "compiler/backend/proofs/flat_to_closProof.ml";;
needs "compiler/backend/proofs/clos_to_bvlProof.ml";;
needs "compiler/backend/proofs/bvl_to_bviProof.ml";;
needs "compiler/backend/proofs/bvi_to_dataProof.ml";;
needs "compiler/backend/proofs/data_to_wordProof.ml";;
needs "compiler/backend/proofs/stack_to_labProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2278 ===== *)

(* HOL4 lines 15-26: simpset settings and the grammar ancestry *)

(* HOL4 line 29 *)
let byte_aligned_mult = prove
 (`!a i.
     good_dimindex (:A)
   ==> (byte_aligned (word_add a (word_mul bytes_in_word (word i))) <=>
        byte_aligned (a:A word))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  REWRITE_TAC[byte_aligned_def; bytes_in_word_def; GSYM WORD_MUL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_DIV_CONV) THEN
  CONV_TAC(DEPTH_CONV LOG2_CONV) THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[ARITH_RULE `4 = 2 EXP 2 /\ 8 = 2 EXP 3`; aligned_add_pow]);;

(* HOL4 line 39 *)
let byte_aligned_MOD = prove
 (`good_dimindex (:A)
   ==> !x:A word. x IN byte_aligned ==> val x MOD (dimindex (:A) DIV 8) = 0`,
  REWRITE_TAC[IN; byte_aligned_def; aligned_w2n; good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_DIV_CONV) THEN
  CONV_TAC(DEPTH_CONV LOG2_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 51: val compile_tap_def = backend_passesTheory.compile_tap_def *)
(* (an alias)                                                                *)

(* HOL4 line 53 *)
let backend_config_ok_def = cake_def
  `backend_config_ok (asm_conf:(A)asm_config) (c:backend_config) <=>
     backend_config_source_conf c = prim_src_config /\
     0 < clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
     bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c) = bvl_num_stubs + 2 /\
     LENGTH (asm_config_avoid_regs asm_conf) + 13 <= asm_config_reg_count asm_conf /\
     lab_to_target_config_pos (backend_config_lab_conf c) = 0 /\
     lab_to_target_config_labels (backend_config_lab_conf c) = LN /\
     conf_ok (:A) (backend_config_data_conf c) /\
     (data_to_word_config_has_longdiv (backend_config_data_conf c)
      ==> asm_config_ISA asm_conf = x86_64) /\
     (data_to_word_config_has_div (backend_config_data_conf c)
      ==> asm_config_ISA asm_conf = ARMv8 \/ asm_config_ISA asm_conf = MIPS \/
          asm_config_ISA asm_conf = RISC_V) /\
     (data_to_word_config_has_fp_tern (backend_config_data_conf c) <=>
      asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf) /\
     (data_to_word_config_has_fp_ops (backend_config_data_conf c) <=>
      1 < asm_config_fp_reg_count asm_conf) /\
     max_stack_alloc <= (2 * max_heap_limit (:A) (backend_config_data_conf c)) - 1 /\
     stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F /\
     asm_offset_ok 0 (asm_config_addr_offset asm_conf) (word 0) /\
     asm_offset_ok 0 (asm_config_hw_offset asm_conf) (word 0) /\
     (!w. word_ile (word_neg (word 8)) w /\ word_ile w (word 8)
          ==> asm_offset_ok 0 (asm_config_byte_offset asm_conf) w) /\
     asm_config_valid_imm asm_conf (INL asm_Add) (word 8) /\
     asm_config_valid_imm asm_conf (INL asm_Add) (word 4) /\
     asm_config_valid_imm asm_conf (INL asm_Add) (word 1) /\
     asm_config_valid_imm asm_conf (INL asm_Sub) (word 1) /\
     OPTION_ALL (ALL (\x. ?s. x = ExtCall s))
       (lab_to_target_config_ffi_names (backend_config_lab_conf c)) /\
     BIJ (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)))
       UNIV UNIV /\
     stack_names_names_ok (stack_to_lab_config_reg_names (backend_config_stack_conf c))
       (asm_config_reg_count asm_conf) (asm_config_avoid_regs asm_conf) /\
     fixed_names (stack_to_lab_config_reg_names (backend_config_stack_conf c)) asm_conf /\
     (!s. asm_offset_ok 0 (asm_config_addr_offset asm_conf) (store_offset s)) /\
     (!s. asm_offset_ok 0 (asm_config_hw_offset asm_conf) (store_offset s)) /\
     (!n. n <= max_stack_alloc
          ==> asm_config_valid_imm asm_conf (INL asm_Sub) (word (n * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm asm_conf (INL asm_Add) (word (n * (dimindex (:A) DIV 8))))`;;

(* HOL4 line 90 *)
let backend_config_ok_with_bvl_conf_updated = prove
 (`!f cc asm_conf.
     bvl_to_bvi_config_next_name2 (f (backend_config_bvl_conf cc)) =
   bvl_to_bvi_config_next_name2 (backend_config_bvl_conf cc)
   ==> (backend_config_ok (asm_conf:(A)asm_config) (backend_config_bvl_conf_fupd f cc) <=>
        backend_config_ok asm_conf cc)`,
  RW[backend_config_ok_def]);;
let _ = cake_add_simps [backend_config_ok_with_bvl_conf_updated];;

(* HOL4 line 97 *)
let backend_config_ok_with_word_to_word_conf_updated = prove
 (`!asm_conf f cc.
     backend_config_ok (asm_conf:(A)asm_config) (backend_config_word_to_word_conf_fupd f cc) <=>
   backend_config_ok asm_conf cc`,
  RW[backend_config_ok_def]);;
let _ = cake_add_simps [backend_config_ok_with_word_to_word_conf_updated];;

(* HOL4 line 103 *)
let backend_config_ok_call_empty_ffi = prove
 (`!asm_conf x cc.
     backend_config_ok (asm_conf:(A)asm_config)
     (backend_config_data_conf_fupd (\c. data_to_word_config_call_empty_ffi_fupd x c) cc) <=>
   backend_config_ok asm_conf cc`,
  FS[backend_config_ok_def; conf_ok_def; shift_length_def; max_heap_limit_def]);;
let _ = cake_add_simps [backend_config_ok_call_empty_ffi];;

(* HOL4 line 113 *)
let mc_init_ok_def = cake_def
  `mc_init_ok (asm_conf:(A)asm_config) (c:backend_config) (mc:(A,B,C)machine_config) <=>
     ALL (\r. MEM (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c))
                     ((r + asm_config_reg_count (target_config (machine_config_target mc))) -
                      (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc)))
                       + 5)))
                  (machine_config_callee_saved_regs mc)) [2;3;4] /\
     tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4 =
       machine_config_len2_reg mc /\
     tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 3 =
       machine_config_ptr2_reg mc /\
     tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2 =
       machine_config_len_reg mc /\
     tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 1 =
       machine_config_ptr_reg mc /\
     tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 0 =
       (match asm_config_link_reg (target_config (machine_config_target mc)) with
          NONE -> 0
        | SOME n -> n) /\
     data_to_word_config_be (backend_config_data_conf c) =
       asm_config_big_endian (target_config (machine_config_target mc)) /\
     ~((match asm_config_link_reg (target_config (machine_config_target mc)) with
          NONE -> 0
        | SOME n -> n) = machine_config_len_reg mc) /\
     ~((match asm_config_link_reg (target_config (machine_config_target mc)) with
          NONE -> 0
        | SOME n -> n) = machine_config_ptr_reg mc) /\
     ~((match asm_config_link_reg (target_config (machine_config_target mc)) with
          NONE -> 0
        | SOME n -> n) = machine_config_len2_reg mc) /\
     ~((match asm_config_link_reg (target_config (machine_config_target mc)) with
          NONE -> 0
        | SOME n -> n) = machine_config_ptr2_reg mc) /\
     ~MEM (match asm_config_link_reg (target_config (machine_config_target mc)) with
             NONE -> 0
           | SOME n -> n) (machine_config_callee_saved_regs mc) /\
     asm_conf = target_config (machine_config_target mc)`;;

(* HOL4 line 132 *)
let mc_init_ok_with_bvl_conf_updated = prove
 (`!asm_conf f cc mc.
     mc_init_ok (asm_conf:(A)asm_config) (backend_config_bvl_conf_fupd f cc)
     (mc:(A,B,C)machine_config) <=>
   mc_init_ok asm_conf cc mc`,
  RW[mc_init_ok_def]);;
let _ = cake_add_simps [mc_init_ok_with_bvl_conf_updated];;

(* HOL4 line 139 *)
let mc_init_ok_with_word_to_word_conf_updated = prove
 (`!asm_conf f cc mc.
     mc_init_ok (asm_conf:(A)asm_config) (backend_config_word_to_word_conf_fupd f cc)
     (mc:(A,B,C)machine_config) <=>
   mc_init_ok asm_conf cc mc`,
  RW[mc_init_ok_def]);;
let _ = cake_add_simps [mc_init_ok_with_word_to_word_conf_updated];;

(* HOL4 line 146 *)
let mc_init_ok_with_clos_conf_updated = prove
 (`!asm_conf f cc mc.
     mc_init_ok (asm_conf:(A)asm_config) (backend_config_clos_conf_fupd f cc)
     (mc:(A,B,C)machine_config) <=>
   mc_init_ok asm_conf cc mc`,
  RW[mc_init_ok_def]);;
let _ = cake_add_simps [mc_init_ok_with_clos_conf_updated];;

(* HOL4 line 153 (the second conjunct equates functions of the machine     *)
(* configuration, as in HOL4)                                                *)
let set_oracle_simp = prove
 (`!asm_conf c x.
     (backend_config_ok (asm_conf:(A)asm_config) (set_oracle c x) <=>
    backend_config_ok asm_conf c) /\
   (mc_init_ok asm_conf (set_oracle c x):(A,B,C)machine_config->bool) =
   mc_init_ok asm_conf c /\
   backend_config_stack_conf (set_oracle c x) = backend_config_stack_conf c`,
  GVS[set_oracle_def; mc_init_ok_def; FUN_EQ_THM; backend_config_ok_def]);;
let _ = cake_add_simps [set_oracle_simp];;

(* HOL4 line 161 *)
let mc_init_ok_call_empty_ffi = prove
 (`!asm_conf x cc.
     (mc_init_ok (asm_conf:(A)asm_config)
      (backend_config_data_conf_fupd (\c. data_to_word_config_call_empty_ffi_fupd x c) cc)
    :(A,B,C)machine_config->bool) =
   mc_init_ok asm_conf cc`,
  FS[mc_init_ok_def; conf_ok_def; shift_length_def; FUN_EQ_THM]);;
let _ = cake_add_simps [mc_init_ok_call_empty_ffi];;

(* HOL4 line 170 *)
let heap_regs_def = cake_def
  `heap_regs reg_names = (tlookup reg_names 2, tlookup reg_names 4)`;;

(* HOL4 lines 175-199: local Overloads (abbreviations of the port's names) *)

(* HOL4 line 201 *)
let no_mti_IMP_obeys_max_app = prove
 (`!m exp. 0 < m /\ no_mti exp ==> obeys_max_app m exp`,
  MATCH_MP_TAC obeys_max_app_ind THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[no_mti_def; obeys_max_app_def] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN TRY ASM_ARITH_TAC THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o check (is_forall o concl))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[GSYM ALL_MEM]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 213 (HOL4's unused binder e3 is left out) *)
let EVERY_no_mti_IMP_obeys_max_app = prove
 (`!m exps.
     0 < m /\ ALL no_mti exps ==> ALL (obeys_max_app m) exps`,
  MESON_TAC[ALL_IMP; no_mti_IMP_obeys_max_app]);;

(* BKP1AUX: the syntactic invariants of compile_common, pass by pass *)
let BKP1AUX_ALL_SND_SND = prove
 (`!(f:clos_exp->bool) (aux:(num#num#clos_exp)list).
     ALL (\(x1,x2,x3). f x3) aux <=> ALL f (MAP (SND o SND) aux)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_MAP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]);;

let BKP1AUX_mti_syntax = prove
 (`!b m es.
     (ALL no_Labels es ==> ALL no_Labels (clos_mti_compile b m es)) /\
     (0 < m /\ ALL no_mti es ==> ALL (obeys_max_app m) (clos_mti_compile b m es))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; intro_multi_no_Labels;
              EVERY_no_mti_IMP_obeys_max_app] THEN
  MESON_TAC[intro_multi_obeys_max_app; LT_REFL]);;

let BKP1AUX_known_syntax = prove
 (`!kc es kc' es' m.
     clos_known_compile kc es = (kc',es')
     ==> (ALL no_Labels es ==> ALL no_Labels es') /\
         (ALL (obeys_max_app m) es ==> ALL (obeys_max_app m) es') /\
         (every_Fn_SOME es ==> every_Fn_SOME es')`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `kc:clos_known_config option` (cases "option")) THENL
   [REWRITE_TAC[clos_known_compile_def; PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`a:clos_known_config`; `es:clos_exp list`; `kc':clos_known_config option`;
                   `es':clos_exp list`] compile_no_Labels) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MP_TAC(ISPECL [`m:num`; `a:clos_known_config`; `es:clos_exp list`;
                   `kc':clos_known_config option`; `es':clos_exp list`] compile_obeys_max_app) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[clos_known_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`a:clos_known_config`; `clos_fvs_compile es`; `[]:val_approx list`;
                 `LN:(val_approx)spt`] known_every_Fn_SOME) THEN
  SPEC_TAC(`clos_known_known a (clos_fvs_compile es) [] LN`,
           `p:(clos_exp#val_approx)list#(val_approx)spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_fvs_compile_def; remove_fvs_every_Fn_SOME; ALL;
              globals_approx_every_Fn_SOME_def; lookup_def; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[let_op_every_Fn_SOME; remove_ticks_every_Fn_SOME] THEN
  ASM_MESON_TAC[]);;
let BKP1AUX_call_syntax = prove
 (`!b es es' g aux m.
     clos_call_compile b es = (es',g,aux)
     ==> (ALL no_Labels es
          ==> ALL no_Labels es' /\ ALL no_Labels (MAP (SND o SND) aux)) /\
         (ALL (obeys_max_app m) es
          ==> ALL (obeys_max_app m) es' /\
              ALL (obeys_max_app m) (MAP (SND o SND) aux)) /\
         (every_Fn_SOME es
          ==> every_Fn_SOME es' /\ every_Fn_SOME (MAP (SND o SND) aux))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[clos_call_compile_def] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[MAP; ALL; every_Fn_SOME_def]] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_call_calls es (LN,[])` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list`
    (X_CHOOSE_THEN `g1:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`es:clos_exp list`; `(LN,[]):num_set#(num#num#clos_exp)list`;
                   `es':clos_exp list`; `(g,aux):num_set#(num#num#clos_exp)list`]
      calls_no_Labels);
    MP_TAC(INST [`m:num`,`k:num`] (ISPECL [`es:clos_exp list`;
      `(LN,[]):num_set#(num#num#clos_exp)list`; `es':clos_exp list`;
      `(g,aux):num_set#(num#num#clos_exp)list`] calls_obeys_max_app));
    MP_TAC(ISPECL [`es:clos_exp list`; `(LN,[]):num_set#(num#num#clos_exp)list`;
                   `es':clos_exp list`; `(g,aux):num_set#(num#num#clos_exp)list`]
      calls_preserves_every_Fn_SOME)] THEN
  ASM_REWRITE_TAC[state_syntax_def; BKP1AUX_ALL_SND_SND; MAP; ALL; SND; ETA_AX;
                  every_Fn_SOME_def]);;

(* HOL4 line 220 *)
let compile_common_syntax = prove
 (`!cf e3 cf1 e4.
     compile_common cf e3 = (cf1,e4)
     ==> (ALL no_Labels e3 ==> ALL no_Labels (MAP (SND o SND) e4)) /\
         (0 < clos_to_bvl_config_max_app cf /\ ALL no_mti e3
          ==> ALL (obeys_max_app (clos_to_bvl_config_max_app cf)) (MAP (SND o SND) e4)) /\
         every_Fn_SOME (MAP (SND o SND) e4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_common_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `clos_to_bvl_config_max_app cf` o
                MATCH_MP BKP1AUX_call_syntax) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `clos_to_bvl_config_max_app cf` o
                MATCH_MP BKP1AUX_known_syntax) THEN
  FIRST_X_ASSUM(fun th ->
    let a1,a2 = match snd(strip_comb(lhs(concl th))) with [a1;a2] -> a1,a2
                | _ -> failwith "args" in
    MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] (CONJUNCT1 renumber_code_locs_no_Labels)) th) THEN
    MP_TAC(SPEC `clos_to_bvl_config_max_app cf`
      (MATCH_MP (REWRITE_RULE[IMP_CONJ]
         (GEN `m:num` (CONJUNCT1 renumber_code_locs_obeys_max_app))) th)) THEN
    MP_TAC(REWRITE_RULE[th; SND]
      (ISPECL [a1;a2] (CONJUNCT1 renumber_code_locs_every_Fn_SOME)))) THEN
  MP_TAC(ISPECL [`clos_to_bvl_config_do_mti cf`; `clos_to_bvl_config_max_app cf`;
                 `e3:clos_exp list`]
    BKP1AUX_mti_syntax) THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC no_Labels_ann THEN REWRITE_TAC[MAP_APPEND; ALL_APPEND] THEN
    ASM_MESON_TAC[chain_exps_no_Labels];
    MATCH_MP_TAC obeys_max_app_ann THEN REWRITE_TAC[MAP_APPEND; ALL_APPEND] THEN
    ASM_MESON_TAC[chain_exps_obeys_max_app];
    MATCH_MP_TAC every_Fn_SOME_ann THEN REWRITE_TAC[MAP_APPEND; every_Fn_SOME_APPEND] THEN
    ASM_MESON_TAC[chain_exps_every_Fn_SOME]]);;

(* HOL4 line 300 *)
let word_list_exists_imp = prove
 (`!dm a n m1.
     dm = addresses a n /\ (dimindex (:A) DIV 8) * n < dimword (:A) /\ good_dimindex (:A)
   ==> word_list_exists a n (fun2set ((m1:A word->B),(dm:A word->bool)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC word_list_exists_addresses THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 308: val semantics_thms (an ML list of the compile_semantics   *)
(* theorems of the passes and full_make_init_semantics)                      *)

(* HOL4 line 317 *)
let cake_configs_def = cake_def
  `cake_configs (asm_conf:(A)asm_config) (c:backend_config) source =
     state_orac_states (compile_inc_progs T asm_conf) c source`;;

(* HOL4 line 322 *)
let cake_orac_def = cake_def
  `cake_orac (asm_conf:(A)asm_config) (c:backend_config) source (f:backend_config->B)
             (g:(A)backend_progs->D) i =
     let c = cake_configs asm_conf c source i in
     (match compile_inc_progs T asm_conf c (source i) with
        (_,progs) -> (f c,g progs))`;;

(* HOL4 line 329 *)
let config_tuple2_def = cake_def
  `config_tuple2 (c:backend_config) =
     (bvl_to_bvi_config_inlines (backend_config_bvl_conf c),
      bvl_to_bvi_config_next_name1 (backend_config_bvl_conf c),
      bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c),
      bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c),
      bvl_to_bvi_config_bvi_inlines (backend_config_bvl_conf c),
      word_to_stack_config_bitmaps_length (backend_config_word_conf c),
      backend_config_lab_conf c)`;;

(* HOL4 line 335 *)
let config_tuple1_def = cake_def
  `config_tuple1 (c:backend_config) =
     (backend_config_source_conf c,
      clos_to_bvl_config_next_loc (backend_config_clos_conf c),
      option_val_approx_spt (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
      FST (clos_to_bvl_config_call_state (backend_config_clos_conf c)),
      config_tuple2 c)`;;

(* HOL4 line 341 (HOL4's unused binder i of the last conjunct is left out) *)
let cake_configs_eq = prove
 (`!f asm_conf c prog b bm c' src x.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
       (f:backend_config->B) c' = f c /\
       (!c p. f (FST (compile_inc_progs T asm_conf c p)) = f c)
       ==> f c' = f c /\ f (cake_configs asm_conf c' src x) = f c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[cake_configs_def] THEN
  SPEC_TAC(`x:num`,`x:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[state_orac_states_def]);;

(* HOL4 line 353 *)
let PAIR_MAP_EQ_EQ = prove
 (`!f g x y.
     ((f:A->B) ## (g:C->D)) x = y <=> (?x0 x1. x = (x0,x1) /\ (f x0,g x1) = y)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:A#C` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_MAP_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 359 *)
let backendProof_known_compile_IS_SOME = prove
 (`!kc es kc' es'.
     clos_known_compile kc es = (kc',es') ==> (IS_SOME kc' <=> IS_SOME kc)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `kc:clos_known_config option` (cases "option")) THEN
  REWRITE_TAC[clos_known_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`clos_known_known a (clos_fvs_compile es) [] LN`,
           `p:(clos_exp#val_approx)list#(val_approx)spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[IS_SOME_DEF]);;

(* HOL4 line 368 *)
let attach_bitmaps_SOME = prove
 (`!names c bm v r.
     attach_bitmaps names c (bm:B) v = SOME r
   ==> ?bytes c'. v = SOME (bytes,c') /\
                  r = (bytes,bm,
                       backend_config_lab_conf_fupd (K c')
                         (backend_config_symbols_fupd
                            (K (MAP (\(n,p,l). (lookup_any n names (implode "NOTFOUND"),p,l))
                                  (lab_to_target_config_sec_pos_len c'))) c))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `v:(byte list#lab_to_target_config)option` (cases "option")) THEN
  REWRITE_TAC[attach_bitmaps_def; distinctness "option"] THEN
  STRUCT_CASES_TAC(ISPEC `a:byte list#lab_to_target_config` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[attach_bitmaps_def; option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 376 *)
let known_compile_static_conf = prove
 (`!kc es kc' es'.
     clos_known_compile kc es = (kc',es') ==> known_static_conf kc' = known_static_conf kc`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `kc:clos_known_config option` (cases "option")) THEN
  REWRITE_TAC[clos_known_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`clos_known_known a (clos_fvs_compile es) [] LN`,
           `p:(clos_exp#val_approx)list#(val_approx)spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  SIMP[known_static_conf_def; reset_inline_factor_def]);;

(* HOL4 line 385 *)
let known_option_upd_val_spt_eq = prove
 (`!spt kc.
     (IS_SOME (option_upd_val_spt spt kc) <=> IS_SOME kc) /\
   known_static_conf (option_upd_val_spt spt kc) = known_static_conf kc`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  SIMP[known_static_conf_def; option_upd_val_spt_def; reset_inline_factor_def; IS_SOME_DEF]);;

(* HOL4 line 394 *)
let source_compile_pattern_cfg = prove
 (`!c p c' p' env_id.
     (source_to_flat_compile c p = (c',p')
    ==> source_to_flat_config_pattern_cfg c' = source_to_flat_config_pattern_cfg c) /\
   (inc_compile env_id c p = (c',p')
    ==> source_to_flat_config_pattern_cfg c' = source_to_flat_config_pattern_cfg c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[source_to_flat_compile_def; inc_compile_def; source_to_flat_compile_prog_def;
              inc_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONJ_TAC THEN REPEAT PAIRARG_TAC THEN
  REPEAT STRIP_TAC THEN GVS[]);;

(* BKP1AUX: the configuration components that the passes preserve *)
let BKP1AUX_compile_common_conf = prove
 (`!c es c1 prog.
     compile_common c es = (c1,prog)
     ==> clos_to_bvl_config_max_app c1 = clos_to_bvl_config_max_app c /\
         clos_to_bvl_config_do_call c1 = clos_to_bvl_config_do_call c /\
         (IS_SOME (clos_to_bvl_config_known_conf c1) <=>
          IS_SOME (clos_to_bvl_config_known_conf c)) /\
         known_static_conf (clos_to_bvl_config_known_conf c1) =
           known_static_conf (clos_to_bvl_config_known_conf c) /\
         clos_to_bvl_config_do_mti c1 = clos_to_bvl_config_do_mti c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_common_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP backendProof_known_compile_IS_SOME) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP known_compile_static_conf) THEN
  GVS[]);;

let BKP1AUX_clos_to_bvl_compile_conf = prove
 (`!c es c1 prog names.
     clos_to_bvl_compile c es = (c1,prog,names)
     ==> clos_to_bvl_config_max_app c1 = clos_to_bvl_config_max_app c /\
         clos_to_bvl_config_do_call c1 = clos_to_bvl_config_do_call c /\
         (IS_SOME (clos_to_bvl_config_known_conf c1) <=>
          IS_SOME (clos_to_bvl_config_known_conf c)) /\
         known_static_conf (clos_to_bvl_config_known_conf c1) =
           known_static_conf (clos_to_bvl_config_known_conf c) /\
         clos_to_bvl_config_do_mti c1 = clos_to_bvl_config_do_mti c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BKP1AUX_compile_common_conf) THEN
  GVS[]);;

let BKP1AUX_clos_to_bvl_compile_inc_conf = prove
 (`!c p c1 p1.
     clos_to_bvl_compile_inc c p = (c1,p1)
     ==> clos_to_bvl_config_max_app c1 = clos_to_bvl_config_max_app c /\
         clos_to_bvl_config_do_call c1 = clos_to_bvl_config_do_call c /\
         (IS_SOME (clos_to_bvl_config_known_conf c1) <=>
          IS_SOME (clos_to_bvl_config_known_conf c)) /\
         known_static_conf (clos_to_bvl_config_known_conf c1) =
           known_static_conf (clos_to_bvl_config_known_conf c) /\
         clos_to_bvl_config_do_mti c1 = clos_to_bvl_config_do_mti c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT STRIP_TAC THEN GVS[known_option_upd_val_spt_eq]);;

let BKP1AUX_bvl_to_bvi_compile_inc_all_conf = prove
 (`!c p c1 p1.
     bvl_to_bvi_compile_inc_all c p = (c1,p1)
     ==> bvl_to_bvi_config_inline_size_limit c1 = bvl_to_bvi_config_inline_size_limit c /\
         bvl_to_bvi_config_split_main_at_seq c1 = bvl_to_bvi_config_split_main_at_seq c /\
         bvl_to_bvi_config_exp_cut c1 = bvl_to_bvi_config_exp_cut c /\
         bvl_to_bvi_config_do_tailrec c1 = bvl_to_bvi_config_do_tailrec c /\
         bvl_to_bvi_config_do_tmc c1 = bvl_to_bvi_config_do_tmc c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT STRIP_TAC THEN GVS[]);;
let BKP1AUX_compile_inc_progs_conf = prove
 (`!k asm_conf c p.
      source_to_flat_config_pattern_cfg
        (backend_config_source_conf (FST (compile_inc_progs k (asm_conf:(A)asm_config) c p))) =
        source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
      clos_to_bvl_config_max_app
        (backend_config_clos_conf (FST (compile_inc_progs k asm_conf c p))) =
        clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
      clos_to_bvl_config_do_call
        (backend_config_clos_conf (FST (compile_inc_progs k asm_conf c p))) =
        clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
      (IS_SOME (clos_to_bvl_config_known_conf
                  (backend_config_clos_conf (FST (compile_inc_progs k asm_conf c p)))) <=>
       IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
      known_static_conf (clos_to_bvl_config_known_conf
                           (backend_config_clos_conf (FST (compile_inc_progs k asm_conf c p)))) =
        known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
      clos_to_bvl_config_do_mti
        (backend_config_clos_conf (FST (compile_inc_progs k asm_conf c p))) =
        clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
      bvl_to_bvi_config_inline_size_limit
        (backend_config_bvl_conf (FST (compile_inc_progs k asm_conf c p))) =
        bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_split_main_at_seq
        (backend_config_bvl_conf (FST (compile_inc_progs k asm_conf c p))) =
        bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_exp_cut
        (backend_config_bvl_conf (FST (compile_inc_progs k asm_conf c p))) =
        bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_do_tailrec
        (backend_config_bvl_conf (FST (compile_inc_progs k asm_conf c p))) =
        bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_do_tmc
        (backend_config_bvl_conf (FST (compile_inc_progs k asm_conf c p))) =
        bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
      backend_config_data_conf (FST (compile_inc_progs k asm_conf c p)) =
        backend_config_data_conf c /\
      word_to_word_config_reg_alg
        (backend_config_word_to_word_conf (FST (compile_inc_progs k asm_conf c p))) =
        word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
      backend_config_stack_conf (FST (compile_inc_progs k asm_conf c p)) =
        backend_config_stack_conf c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inc_progs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT2 (SPEC_ALL source_compile_pattern_cfg))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BKP1AUX_clos_to_bvl_compile_inc_conf) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BKP1AUX_bvl_to_bvi_compile_inc_all_conf) THEN
  ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM]);;

let BKP1AUX_backend_compile_conf = prove
 (`!asm_conf c prog b bm c1.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c1) ==>

      source_to_flat_config_pattern_cfg
        (backend_config_source_conf c1) =
        source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
      clos_to_bvl_config_max_app
        (backend_config_clos_conf c1) =
        clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
      clos_to_bvl_config_do_call
        (backend_config_clos_conf c1) =
        clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
      (IS_SOME (clos_to_bvl_config_known_conf
                  (backend_config_clos_conf c1)) <=>
       IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
      known_static_conf (clos_to_bvl_config_known_conf
                           (backend_config_clos_conf c1)) =
        known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
      clos_to_bvl_config_do_mti
        (backend_config_clos_conf c1) =
        clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
      bvl_to_bvi_config_inline_size_limit
        (backend_config_bvl_conf c1) =
        bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_split_main_at_seq
        (backend_config_bvl_conf c1) =
        bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_exp_cut
        (backend_config_bvl_conf c1) =
        bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_do_tailrec
        (backend_config_bvl_conf c1) =
        bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_do_tmc
        (backend_config_bvl_conf c1) =
        bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
      backend_config_data_conf c1 =
        backend_config_data_conf c /\
      word_to_word_config_reg_alg
        (backend_config_word_to_word_conf c1) =
        word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
      backend_config_stack_conf c1 =
        backend_config_stack_conf c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backend_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT1 (SPEC_ALL source_compile_pattern_cfg))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BKP1AUX_clos_to_bvl_compile_conf) THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM;
                  (record_info "clos_to_bvl_config").ri_accfupds;
                  (record_info "bvl_to_bvi_config").ri_accfupds;
                  (record_info "word_to_word_config").ri_accfupds]);;

(* HOL4 line 404: val cake_orac_config_inv_f, the term                     *)
(*   (\(sc,cc,bc,mc). (sc.pattern_cfg, cc.max_app, cc.do_call,              *)
(*      IS_SOME cc.known_conf, known_static_conf cc.known_conf, cc.do_mti,  *)
(*      bc.inline_size_limit, bc.split_main_at_seq, bc.exp_cut,             *)
(*      bc.do_tailrec, bc.do_tmc, mc)) o                                    *)
(*   (\c. (c.source_conf, c.clos_conf, c.bvl_conf, c.data_conf,             *)
(*         c.word_to_word_conf.reg_alg, c.stack_conf, asm_conf))            *)
(* written out (beta-reduced, as HOL4's SIMP_RULE std_ss leaves it) where   *)
(* HOL4 antiquotes it                                                        *)

(* HOL4 line 411: val cake_orac_config_tuple_eq_step = ISPEC                *)
(* cake_orac_config_inv_f cake_configs_eq |> SIMP_RULE std_ss [] (the       *)
(* tuple equations split into their components)                              *)
let cake_orac_config_tuple_eq_step = prove
 (`!asm_conf c prog b bm c' src x.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   (source_to_flat_config_pattern_cfg (backend_config_source_conf c') =
      source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
    clos_to_bvl_config_max_app (backend_config_clos_conf c') =
      clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
    clos_to_bvl_config_do_call (backend_config_clos_conf c') =
      clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
    (IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c')) <=>
     IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
    known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c')) =
      known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
    clos_to_bvl_config_do_mti (backend_config_clos_conf c') =
      clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
    bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c') =
      bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
    bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c') =
      bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
    bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c') =
      bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
    bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c') =
      bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
    bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c') =
      bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
    backend_config_data_conf c' = backend_config_data_conf c /\
    word_to_word_config_reg_alg (backend_config_word_to_word_conf c') =
      word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
    backend_config_stack_conf c' = backend_config_stack_conf c) /\
   (!c p.
      source_to_flat_config_pattern_cfg
        (backend_config_source_conf (FST (compile_inc_progs T asm_conf c p))) =
        source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
      clos_to_bvl_config_max_app
        (backend_config_clos_conf (FST (compile_inc_progs T asm_conf c p))) =
        clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
      clos_to_bvl_config_do_call
        (backend_config_clos_conf (FST (compile_inc_progs T asm_conf c p))) =
        clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
      (IS_SOME (clos_to_bvl_config_known_conf
                  (backend_config_clos_conf (FST (compile_inc_progs T asm_conf c p)))) <=>
       IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
      known_static_conf (clos_to_bvl_config_known_conf
                           (backend_config_clos_conf (FST (compile_inc_progs T asm_conf c p)))) =
        known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
      clos_to_bvl_config_do_mti
        (backend_config_clos_conf (FST (compile_inc_progs T asm_conf c p))) =
        clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
      bvl_to_bvi_config_inline_size_limit
        (backend_config_bvl_conf (FST (compile_inc_progs T asm_conf c p))) =
        bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_split_main_at_seq
        (backend_config_bvl_conf (FST (compile_inc_progs T asm_conf c p))) =
        bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_exp_cut
        (backend_config_bvl_conf (FST (compile_inc_progs T asm_conf c p))) =
        bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_do_tailrec
        (backend_config_bvl_conf (FST (compile_inc_progs T asm_conf c p))) =
        bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
      bvl_to_bvi_config_do_tmc
        (backend_config_bvl_conf (FST (compile_inc_progs T asm_conf c p))) =
        bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
      backend_config_data_conf (FST (compile_inc_progs T asm_conf c p)) =
        backend_config_data_conf c /\
      word_to_word_config_reg_alg
        (backend_config_word_to_word_conf (FST (compile_inc_progs T asm_conf c p))) =
        word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
      backend_config_stack_conf (FST (compile_inc_progs T asm_conf c p)) =
        backend_config_stack_conf c)
   ==> (source_to_flat_config_pattern_cfg (backend_config_source_conf c') =
          source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
        clos_to_bvl_config_max_app (backend_config_clos_conf c') =
          clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
        clos_to_bvl_config_do_call (backend_config_clos_conf c') =
          clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
        (IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c')) <=>
         IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
        known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c')) =
          known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
        clos_to_bvl_config_do_mti (backend_config_clos_conf c') =
          clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
        bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c') =
          bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c') =
          bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c') =
          bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c') =
          bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c') =
          bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
        backend_config_data_conf c' = backend_config_data_conf c /\
        word_to_word_config_reg_alg (backend_config_word_to_word_conf c') =
          word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
        backend_config_stack_conf c' = backend_config_stack_conf c) /\
       (source_to_flat_config_pattern_cfg
          (backend_config_source_conf (cake_configs asm_conf c' src x)) =
          source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
        clos_to_bvl_config_max_app
          (backend_config_clos_conf (cake_configs asm_conf c' src x)) =
          clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
        clos_to_bvl_config_do_call
          (backend_config_clos_conf (cake_configs asm_conf c' src x)) =
          clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
        (IS_SOME (clos_to_bvl_config_known_conf
                    (backend_config_clos_conf (cake_configs asm_conf c' src x))) <=>
         IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
        known_static_conf (clos_to_bvl_config_known_conf
                             (backend_config_clos_conf (cake_configs asm_conf c' src x))) =
          known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
        clos_to_bvl_config_do_mti
          (backend_config_clos_conf (cake_configs asm_conf c' src x)) =
          clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
        bvl_to_bvi_config_inline_size_limit
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_split_main_at_seq
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_exp_cut
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tailrec
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tmc
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
        backend_config_data_conf (cake_configs asm_conf c' src x) =
          backend_config_data_conf c /\
        word_to_word_config_reg_alg
          (backend_config_word_to_word_conf (cake_configs asm_conf c' src x)) =
          word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
        backend_config_stack_conf (cake_configs asm_conf c' src x) =
          backend_config_stack_conf c)`,
  MATCH_ACCEPT_TAC(REWRITE_RULE[PAIR_EQ] (BETA_RULE (ISPEC
    `\c:backend_config.
       (source_to_flat_config_pattern_cfg (backend_config_source_conf c),
        clos_to_bvl_config_max_app (backend_config_clos_conf c),
        clos_to_bvl_config_do_call (backend_config_clos_conf c),
        IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
        known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
        clos_to_bvl_config_do_mti (backend_config_clos_conf c),
        bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c),
        bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c),
        bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c),
        bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c),
        bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c),
        backend_config_data_conf c,
        word_to_word_config_reg_alg (backend_config_word_to_word_conf c),
        backend_config_stack_conf c)`
    cake_configs_eq))));;

(* HOL4 line 414: val orac_eq_prop (the term A ==> P of                    *)
(* cake_orac_config_tuple_eq_step, A /\ B /\ C ==> P), stated below          *)

(* HOL4 line 419: ^orac_eq_prop *)
let cake_orac_config_eqs = prove
 (`!asm_conf c prog b bm c' src x.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> (source_to_flat_config_pattern_cfg (backend_config_source_conf c') =
          source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
        clos_to_bvl_config_max_app (backend_config_clos_conf c') =
          clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
        clos_to_bvl_config_do_call (backend_config_clos_conf c') =
          clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
        (IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c')) <=>
         IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
        known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c')) =
          known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
        clos_to_bvl_config_do_mti (backend_config_clos_conf c') =
          clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
        bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c') =
          bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c') =
          bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c') =
          bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c') =
          bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c') =
          bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
        backend_config_data_conf c' = backend_config_data_conf c /\
        word_to_word_config_reg_alg (backend_config_word_to_word_conf c') =
          word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
        backend_config_stack_conf c' = backend_config_stack_conf c) /\
       (source_to_flat_config_pattern_cfg
          (backend_config_source_conf (cake_configs asm_conf c' src x)) =
          source_to_flat_config_pattern_cfg (backend_config_source_conf c) /\
        clos_to_bvl_config_max_app
          (backend_config_clos_conf (cake_configs asm_conf c' src x)) =
          clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
        clos_to_bvl_config_do_call
          (backend_config_clos_conf (cake_configs asm_conf c' src x)) =
          clos_to_bvl_config_do_call (backend_config_clos_conf c) /\
        (IS_SOME (clos_to_bvl_config_known_conf
                    (backend_config_clos_conf (cake_configs asm_conf c' src x))) <=>
         IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))) /\
        known_static_conf (clos_to_bvl_config_known_conf
                             (backend_config_clos_conf (cake_configs asm_conf c' src x))) =
          known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)) /\
        clos_to_bvl_config_do_mti
          (backend_config_clos_conf (cake_configs asm_conf c' src x)) =
          clos_to_bvl_config_do_mti (backend_config_clos_conf c) /\
        bvl_to_bvi_config_inline_size_limit
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_split_main_at_seq
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_exp_cut
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tailrec
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c) /\
        bvl_to_bvi_config_do_tmc
          (backend_config_bvl_conf (cake_configs asm_conf c' src x)) =
          bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c) /\
        backend_config_data_conf (cake_configs asm_conf c' src x) =
          backend_config_data_conf c /\
        word_to_word_config_reg_alg
          (backend_config_word_to_word_conf (cake_configs asm_conf c' src x)) =
          word_to_word_config_reg_alg (backend_config_word_to_word_conf c) /\
        backend_config_stack_conf (cake_configs asm_conf c' src x) =
          backend_config_stack_conf c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL cake_orac_config_tuple_eq_step) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP BKP1AUX_backend_compile_conf);
      REWRITE_TAC[BKP1AUX_compile_inc_progs_conf]];
    DISCH_THEN ACCEPT_TAC]);;

(* HOL4 line 444 *)
let decide_inline_reset_spt = prove
 (`!f kc.
     decide_inline (clos_known_config_val_approx_spt_fupd f kc) = decide_inline kc`,
  REWRITE_TAC[FUN_EQ_THM; decide_inline_def; (record_info "clos_known_config").ri_accfupds]);;

(* BKP1AUX: helpers for known_reset_spt *)
let BKP1AUX_dec_inline_factor_spt = prove
 (`!f c. dec_inline_factor (clos_known_config_val_approx_spt_fupd f c) =
         clos_known_config_val_approx_spt_fupd f (dec_inline_factor c)`,
  REWRITE_TAC[dec_inline_factor_def; (record_info "clos_known_config").ri_component_equality;
              (record_info "clos_known_config").ri_accfupds; K_THM]);;

(* BKP1AUX: rewrite the MAP over the functions of a clos_Letrec by the     *)
(* induction hypothesis (an OCaml helper for known_reset_spt)              *)
let BKP1AUX_MAP_TAC : tactic = fun (asl,w) ->
  let l,r = dest_eq w in
  let is_map t = is_comb t && is_comb(rator t) &&
                 (try fst(dest_const(rator(rator t))) = "MAP" with Failure _ -> false) in
  let has_upd t = can (find_term (fun u ->
      try fst(dest_const u) = "clos_known_config_val_approx_spt_fupd"
      with Failure _ -> false)) t in
  let m1 = find_term (fun t -> is_map t && has_upd t) l in
  let m2 = find_term (fun t -> is_map t && rand t = rand m1 && not (has_upd t)) r in
  (SUBGOAL_THEN (mk_eq(m1,m2)) SUBST1_TAC THENL
    [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
     REPEAT STRIP_TAC THEN CASE_REWRITE_TAC[] THEN REPEAT AP_TERM_TAC THEN
     ASM_MESON_TAC[];
     REFL_TAC]) (asl,w);;

let BKP1AUX_known_reset_spt = prove
 (`!f kc xs vs g.
     clos_known_known (clos_known_config_val_approx_spt_fupd f kc) xs vs g = clos_known_known kc xs vs g`,
  GEN_TAC THEN MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[clos_known_known_def] THEN
  REPEAT(PAIRARG_TAC THEN GVS[decide_inline_reset_spt]) THEN
  GVS[decide_inline_reset_spt] THEN
  FIRST
   [BKP1AUX_MAP_TAC;
    REWRITE_TAC[BKP1AUX_dec_inline_factor_spt] THEN
    CASES_ON `decide_inline c a1 loc_opt (LENGTH (xs:clos_exp list))` THEN
    CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

(* HOL4 line 450 *)
let known_reset_spt = prove
 (`!kc f. clos_known_known (clos_known_config_val_approx_spt_fupd f kc) = clos_known_known kc`,
  REWRITE_TAC[FUN_EQ_THM; BKP1AUX_known_reset_spt]);;

(* HOL4 line 465 *)
let known_reset_to_static_conf = prove
 (`!kc.
     clos_known_known (reset_inline_factor kc) = clos_known_known (THE (known_static_conf (SOME kc)))`,
  REWRITE_TAC[known_static_conf_def] THEN CASE_REWRITE_TAC[THE_DEF; known_reset_spt]);;

(* BKP1AUX: resetting the inline factor of a reset configuration *)
let BKP1AUX_reset_spt_reset = prove
 (`!f c. reset_inline_factor
           (clos_known_config_val_approx_spt_fupd f (reset_inline_factor c)) =
         clos_known_config_val_approx_spt_fupd f (reset_inline_factor c)`,
  REWRITE_TAC[reset_inline_factor_def; (record_info "clos_known_config").ri_component_equality;
              (record_info "clos_known_config").ri_accfupds; K_THM]);;

(* HOL4 line 471 *)
let known_co_eq_state_co_inc = prove
 (`!kc co.
     known_co kc (co:num->((val_approx)spt#B)#clos_prog) =
   state_co (known_compile_inc (known_static_conf kc)) co`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `kc:clos_known_config option` (cases "option")) THEN
  REWRITE_TAC[known_co_def; known_static_conf_def; FUN_EQ_THM] THEN CASE_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[state_co_def; o_THM; pure_co_def] THEN
  MP_TAC(ISPEC `(co:num->((val_approx)spt#B)#clos_prog) n` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sc:(val_approx)spt#B` (X_CHOOSE_THEN `p:clos_prog` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `sc:(val_approx)spt#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(val_approx)spt` (X_CHOOSE_THEN `cfg:B` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[known_compile_inc_def; PAIR_MAP_THM; I_THM; CURRY_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[kcompile_inc_uncurry] THEN
  CASE_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN
  REWRITE_TAC[BKP1AUX_reset_spt_reset; known_reset_spt]);;

(* HOL4 line 487 *)
let keep_progs_T = prove
 (`keep_progs T = (I:A list->A list)`,
  REWRITE_TAC[FUN_EQ_THM; keep_progs_def; I_THM]);;

(* HOL4 line 493: LIST_CONJ [compile_inc_progs_def, keep_progs_T] *)
let compile_inc_progs_defs = CONJ compile_inc_progs_def keep_progs_T;;

(* BKP1AUX: the programs that compile_inc_progs T produces, field by field *)
let BKP1AUX_compile_inc_progs_progs = prove
 (`!asm_conf c env_id p.
     let ps = SND (compile_inc_progs T (asm_conf:(A)asm_config) c (env_id,p)) in
     backend_progs_env_id ps = env_id /\
     backend_progs_source_prog ps = p /\
     backend_progs_flat_prog ps =
       SND (inc_compile env_id (backend_config_source_conf c) (source_to_source_compile p)) /\
     backend_progs_clos_prog ps = inc_compile_decs (backend_progs_flat_prog ps) /\
     backend_progs_bvl_prog ps =
       SND (clos_to_bvl_compile_inc (backend_config_clos_conf c) (backend_progs_clos_prog ps)) /\
     backend_progs_bvi_prog ps =
       SND (bvl_to_bvi_compile_inc_all (backend_config_bvl_conf c) (backend_progs_bvl_prog ps)) /\
     backend_progs_data_prog ps = bvi_to_data_compile_prog (backend_progs_bvi_prog ps) /\
     backend_progs_word_prog ps =
       MAP (\p. full_compile_single (asm_config_two_reg_arith asm_conf)
                  (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)))
                  (word_to_word_config_reg_alg (backend_config_word_to_word_conf c))
                  asm_conf (p,NONE))
         (MAP (data_to_word_compile_part (ensure_fp_conf_ok asm_conf (backend_config_data_conf c)))
            (backend_progs_data_prog ps)) /\
     backend_progs_stack_prog ps =
       FST (compile_word_to_stack asm_conf
              (stack_to_lab_config_perf_calls (backend_config_stack_conf c))
              (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)))
              (backend_progs_word_prog ps)
              (Nil,word_to_stack_config_bitmaps_length (backend_config_word_conf c))) /\
     backend_progs_cur_bm ps =
       append (FST (SND (SND (compile_word_to_stack asm_conf
              (stack_to_lab_config_perf_calls (backend_config_stack_conf c))
              (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)))
              (backend_progs_word_prog ps)
              (Nil,word_to_stack_config_bitmaps_length (backend_config_word_conf c)))))) /\
     backend_progs_lab_prog ps =
       compile_no_stubs (stack_to_lab_config_reg_names (backend_config_stack_conf c))
         (stack_to_lab_config_jump (backend_config_stack_conf c))
         (asm_config_addr_offset asm_conf)
         (asm_config_reg_count asm_conf - (3 + LENGTH (asm_config_avoid_regs asm_conf)))
         (backend_progs_stack_prog ps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inc_progs_def; keep_progs_T; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "backend_config").ri_accfupds;
                              (record_info "backend_config").ri_accessors; K_THM]) THEN
  ASM_REWRITE_TAC[(record_info "backend_progs").ri_accfupds;
                  (record_info "backend_progs").ri_accessors;
                  (record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM; PAIR_MAP_THM; I_THM; SND;
                  PAIR_MAP_I]);;
(* BKP1AUX: cake_orac without the lets *)
let BKP1AUX_cake_orac_thm = prove
 (`!asm_conf c src (f:backend_config->B) (g:(A)backend_progs->D) i.
     cake_orac (asm_conf:(A)asm_config) c src f g i =
     (f (cake_configs asm_conf c src i),
      g (SND (compile_inc_progs T asm_conf (cake_configs asm_conf c src i) (src i))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cake_orac_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `compile_inc_progs T (asm_conf:(A)asm_config)
                  (cake_configs asm_conf c src i) (src i)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;
(* BKP1AUX: the common first steps of the conjuncts of cake_orac_eqs: the  *)
(* point i (introduced before), the configuration C reached there, and the programs at i       *)
let BKP1AUX_ORAC_SETUP_TAC : tactic =
  SPEC_TAC(`cake_configs (asm_conf:(A)asm_config) c' (src:num->(num#num)#(dec)list) i`,
           `C:backend_config`) THEN
  SPEC_TAC(`(src:num->(num#num)#(dec)list) i`,`q:(num#num)#(dec)list`) THEN
  X_GEN_TAC `q:(num#num)#(dec)list` THEN X_GEN_TAC `C:backend_config` THEN
  MP_TAC(ISPEC `q:(num#num)#(dec)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num#num` (X_CHOOSE_THEN `p:(dec)list` SUBST1_TAC)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `C:backend_config`; `e:num#num`; `p:(dec)list`]
       BKP1AUX_compile_inc_progs_progs)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[];;

let BKP1AUX_source_to_flat_orac_eq = prove
 (`!asm_conf c' src.
     state_co (\c (env_id,decs). inc_compile env_id c (source_to_source_compile decs))
     (cake_orac (asm_conf:(A)asm_config) c' src config_tuple1
        (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps))) =
   cake_orac asm_conf c' src (SND o config_tuple1) (\ps. backend_progs_flat_prog ps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; state_co_def] THEN
  X_GEN_TAC `i:num` THEN BKP1AUX_ORAC_SETUP_TAC THEN REWRITE_TAC[config_tuple1_def] THEN
  CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN PAIRARG_TAC THEN ASM_REWRITE_TAC[SND]);;

let BKP1AUX_flat_to_clos_orac_eq = prove
 (`!asm_conf c' src f1.
   pure_co inc_compile_decs o
     cake_orac (asm_conf:(A)asm_config) c' src (f1:backend_config->B)
       (\ps. backend_progs_flat_prog ps) =
   cake_orac asm_conf c' src f1 (\ps. backend_progs_clos_prog ps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; pure_co_def] THEN
  X_GEN_TAC `i:num` THEN BKP1AUX_ORAC_SETUP_TAC THEN REWRITE_TAC[PAIR_MAP_THM; I_THM]);;

let BKP1AUX_bvi_to_data_orac_eq = prove
 (`!asm_conf c' src f3.
   pure_co bvi_to_data_compile_prog o
     cake_orac (asm_conf:(A)asm_config) c' src (f3:backend_config->D)
       (\ps. backend_progs_bvi_prog ps) =
   cake_orac asm_conf c' src f3 (\ps. backend_progs_data_prog ps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; pure_co_def] THEN
  X_GEN_TAC `i:num` THEN BKP1AUX_ORAC_SETUP_TAC THEN REWRITE_TAC[PAIR_MAP_THM; I_THM]);;
(* BKP1AUX: split the pair cases of the goal, both sides at once *)
let BKP1AUX_PAIRS_TAC : tactic =
  REPEAT(PAIRARG_TAC THEN
         REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
         REPEAT VAR_EQ_TAC);;

(* BKP1AUX: split the argument of a paired lambda (GABS) application into a  *)
(* tuple of fresh variables, component by component, then beta-reduce      *)
let BKP1AUX_GABS_TAC : tactic = fun (asl,w) ->
  let is_prod ty = can (fun ty -> match dest_type ty with "prod",[_;_] -> () | _ -> failwith "")
                       ty in
  let rec unsplit tm =
    if not (is_prod (type_of tm)) then None
    else if is_pair tm then
      (match unsplit (fst(dest_pair tm)) with
         Some x -> Some x
       | None -> unsplit (snd(dest_pair tm)))
    else Some tm in
  let is_gabs_app t =
    is_comb t && is_comb(rator t) && is_const(rator(rator t)) &&
    fst(dest_const(rator(rator t))) = "GABS" && unsplit (rand t) <> None in
  let t = find_term is_gabs_app w in
  let x = match unsplit (rand t) with Some x -> x | None -> failwith "BKP1AUX_GABS_TAC" in
  let a,b = match dest_type(type_of x) with "prod",[a;b] -> a,b | _ -> failwith "prod" in
  let avoid = frees w @ freesl (map (concl o snd) asl) in
  let v = variant avoid (mk_var("q",a)) in
  let r = variant (v::avoid) (mk_var("r",b)) in
  (MP_TAC(ISPEC x PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN v (X_CHOOSE_THEN r SUBST_ALL_TAC)) THEN
   TRY (CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV))) (asl,w);;

let BKP1AUX_clos_to_bvl_orac_eq = prove
 (`!asm_conf c prog b bm c' src clos_c.
   backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   clos_c = backend_config_clos_conf c
    ==> pure_co (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app clos_c)) o
        pure_co clos_annotate_compile_inc o
        state_co (cond_call_compile_inc (clos_to_bvl_config_do_call clos_c))
          (known_co (clos_to_bvl_config_known_conf clos_c)
             (state_co (ignore_table clos_number_compile_inc)
                (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti clos_c)
                            (clos_to_bvl_config_max_app clos_c)) o
                 cake_orac asm_conf c' src (SND o config_tuple1)
                   (\ps. backend_progs_clos_prog ps)))) =
        cake_orac asm_conf c' src config_tuple2 (\ps. backend_progs_bvl_prog ps)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[known_co_eq_state_co_inc] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; pure_co_def; state_co_def] THEN
  X_GEN_TAC `i:num` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`src:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  BKP1AUX_ORAC_SETUP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[config_tuple1_def; PAIR_MAP_THM; I_THM; clos_to_bvl_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  BKP1AUX_PAIRS_TAC THEN ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; SND]);;

let BKP1AUX_bvl_to_bvi_orac_eq = prove
 (`!asm_conf c prog b bm c' src bvl_c.
   backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   bvl_c = backend_config_bvl_conf c
    ==> full_co bvl_c (cake_orac asm_conf c' src config_tuple2 (\ps. backend_progs_bvl_prog ps)) =
        cake_orac asm_conf c' src (SND o SND o SND o SND o SND o config_tuple2)
          (\ps. backend_progs_bvi_prog ps)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[full_co_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; pure_co_def; state_co_def] THEN
  X_GEN_TAC `i:num` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`src:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  BKP1AUX_ORAC_SETUP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[config_tuple2_def; PAIR_MAP_THM; I_THM; bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[(record_info "bvl_to_bvi_config").ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  BKP1AUX_PAIRS_TAC THEN ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; SND]);;

let BKP1AUX_data_to_word_orac_eq = prove
 (`!asm_conf c prog b bm c' src dc tr_c reg_c reg_alg f4.
   backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
    dc = ensure_fp_conf_ok asm_conf (backend_config_data_conf c) /\
    tr_c = asm_config_two_reg_arith asm_conf /\
    reg_c = asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5) /\
    reg_alg = word_to_word_config_reg_alg (backend_config_word_to_word_conf c)
    ==> pure_co (MAP (\p. full_compile_single tr_c reg_c reg_alg asm_conf (p,NONE))) o
        pure_co (MAP (data_to_word_compile_part dc)) o
        cake_orac asm_conf c' src (f4:backend_config->E) (\ps. backend_progs_data_prog ps) =
        cake_orac asm_conf c' src f4 (\ps. backend_progs_word_prog ps)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; pure_co_def] THEN
  X_GEN_TAC `i:num` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`src:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  BKP1AUX_ORAC_SETUP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN REWRITE_TAC[ADD_SYM]);;

let BKP1AUX_word_to_stack_orac_eq = prove
 (`!asm_conf c prog b bm c' src.
   backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
    stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F
    ==> (\((bm0,cfg),prg).
           (\(prg2,fs,bm). (cfg,prg2,append (FST bm)))
             (compile_word_to_stack asm_conf F
                (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
                prg (Nil,bm0))) o
        cake_orac asm_conf c' src (SND o SND o SND o SND o SND o config_tuple2)
          (\ps. backend_progs_word_prog ps) =
        cake_orac asm_conf c' src (SND o SND o SND o SND o SND o SND o config_tuple2)
          (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm] THEN
  X_GEN_TAC `i:num` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`src:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  BKP1AUX_ORAC_SETUP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[config_tuple2_def; SND] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ADD_SYM] THEN REPEAT BKP1AUX_GABS_TAC THEN REWRITE_TAC[FST; SND]);;

let BKP1AUX_stack_to_lab_orac_eq = prove
 (`!asm_conf c prog b bm c' src reg_nm jump sp offs f5.
   backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
    reg_nm = stack_to_lab_config_reg_names (backend_config_stack_conf c) /\
    jump = stack_to_lab_config_jump (backend_config_stack_conf c) /\
    sp = asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3) /\
    offs = asm_config_addr_offset asm_conf
    ==> pure_co (compile_no_stubs reg_nm jump offs sp o FST) o
        cake_orac asm_conf c' src (f5:backend_config->G)
          (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) =
        cake_orac asm_conf c' src f5 (\ps. backend_progs_lab_prog ps)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; pure_co_def] THEN
  X_GEN_TAC `i:num` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`src:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  BKP1AUX_ORAC_SETUP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; o_THM; FST] THEN REWRITE_TAC[ADD_SYM]);;

(* HOL4 line 496: eight equations of the oracles of the passes (named by    *)
(* the val at HOL4 line 583)                                                 *)
let cake_orac_eqs = prove
 (`!c asm_conf c' src f1 prog b bm clos_c bvl_c f3 dc tr_c reg_c reg_alg f4 reg_nm jump sp offs f5.
     state_co (\c (env_id,decs). inc_compile env_id c (source_to_source_compile decs))
     (cake_orac (asm_conf:(A)asm_config) c' src config_tuple1
        (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps))) =
   cake_orac asm_conf c' src (SND o config_tuple1) (\ps. backend_progs_flat_prog ps) /\
   pure_co inc_compile_decs o
     cake_orac asm_conf c' src (f1:backend_config->B) (\ps. backend_progs_flat_prog ps) =
   cake_orac asm_conf c' src f1 (\ps. backend_progs_clos_prog ps) /\
   (backend_compile asm_conf c prog = SOME (b,bm,c') /\ clos_c = backend_config_clos_conf c
    ==> pure_co (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app clos_c)) o
        pure_co clos_annotate_compile_inc o
        state_co (cond_call_compile_inc (clos_to_bvl_config_do_call clos_c))
          (known_co (clos_to_bvl_config_known_conf clos_c)
             (state_co (ignore_table clos_number_compile_inc)
                (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti clos_c)
                            (clos_to_bvl_config_max_app clos_c)) o
                 cake_orac asm_conf c' src (SND o config_tuple1)
                   (\ps. backend_progs_clos_prog ps)))) =
        cake_orac asm_conf c' src config_tuple2 (\ps. backend_progs_bvl_prog ps)) /\
   (backend_compile asm_conf c prog = SOME (b,bm,c') /\ bvl_c = backend_config_bvl_conf c
    ==> full_co bvl_c (cake_orac asm_conf c' src config_tuple2 (\ps. backend_progs_bvl_prog ps)) =
        cake_orac asm_conf c' src (SND o SND o SND o SND o SND o config_tuple2)
          (\ps. backend_progs_bvi_prog ps)) /\
   pure_co bvi_to_data_compile_prog o
     cake_orac asm_conf c' src (f3:backend_config->D) (\ps. backend_progs_bvi_prog ps) =
   cake_orac asm_conf c' src f3 (\ps. backend_progs_data_prog ps) /\
   (backend_compile asm_conf c prog = SOME (b,bm,c') /\
    dc = ensure_fp_conf_ok asm_conf (backend_config_data_conf c) /\
    tr_c = asm_config_two_reg_arith asm_conf /\
    reg_c = asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5) /\
    reg_alg = word_to_word_config_reg_alg (backend_config_word_to_word_conf c)
    ==> pure_co (MAP (\p. full_compile_single tr_c reg_c reg_alg asm_conf (p,NONE))) o
        pure_co (MAP (data_to_word_compile_part dc)) o
        cake_orac asm_conf c' src (f4:backend_config->E) (\ps. backend_progs_data_prog ps) =
        cake_orac asm_conf c' src f4 (\ps. backend_progs_word_prog ps)) /\
   (backend_compile asm_conf c prog = SOME (b,bm,c') /\
    stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F
    ==> (\((bm0,cfg),prg).
           (\(prg2,fs,bm). (cfg,prg2,append (FST bm)))
             (compile_word_to_stack asm_conf F
                (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
                prg (Nil,bm0))) o
        cake_orac asm_conf c' src (SND o SND o SND o SND o SND o config_tuple2)
          (\ps. backend_progs_word_prog ps) =
        cake_orac asm_conf c' src (SND o SND o SND o SND o SND o SND o config_tuple2)
          (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))) /\
   (backend_compile asm_conf c prog = SOME (b,bm,c') /\
    reg_nm = stack_to_lab_config_reg_names (backend_config_stack_conf c) /\
    jump = stack_to_lab_config_jump (backend_config_stack_conf c) /\
    sp = asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3) /\
    offs = asm_config_addr_offset asm_conf
    ==> pure_co (compile_no_stubs reg_nm jump offs sp o FST) o
        cake_orac asm_conf c' src (f5:backend_config->G)
          (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) =
        cake_orac asm_conf c' src f5 (\ps. backend_progs_lab_prog ps))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC BKP1AUX_source_to_flat_orac_eq;
    MATCH_ACCEPT_TAC BKP1AUX_flat_to_clos_orac_eq;
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP BKP1AUX_clos_to_bvl_orac_eq);
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP BKP1AUX_bvl_to_bvi_orac_eq);
    MATCH_ACCEPT_TAC BKP1AUX_bvi_to_data_orac_eq;
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP BKP1AUX_data_to_word_orac_eq);
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP BKP1AUX_word_to_stack_orac_eq);
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP BKP1AUX_stack_to_lab_orac_eq)]);;

(* HOL4 line 583: val [source_to_flat_orac_eq, ..., stack_to_lab_orac_eq] =  *)
(* map GEN_ALL (CONJUNCTS cake_orac_eqs) (derived here in the same way)     *)
let source_to_flat_orac_eq,flat_to_clos_orac_eq,clos_to_bvl_orac_eq,
    bvl_to_bvi_orac_eq,bvi_to_data_orac_eq,data_to_word_orac_eq,
    word_to_stack_orac_eq,stack_to_lab_orac_eq =
  match map GEN_ALL (CONJUNCTS (SPEC_ALL cake_orac_eqs)) with
    [a;b;c;d;e;f;g;h] -> a,b,c,d,e,f,g,h
  | _ -> failwith "cake_orac_eqs: eight conjuncts expected";;

(* HOL4 line 588: val simple_orac_eqs = LIST_CONJ [source_to_flat_orac_eq, *)
(* flat_to_clos_orac_eq, bvi_to_data_orac_eq]                                *)
let simple_orac_eqs =
  end_itlist CONJ [source_to_flat_orac_eq; flat_to_clos_orac_eq; bvi_to_data_orac_eq];;

(* HOL4 line 591 *)
let cake_orac_0 = prove
 (`!asm_conf c' src f g.
     cake_orac (asm_conf:(A)asm_config) c' src (f:backend_config->B) (g:(A)backend_progs->D) 0 =
   (f c',g (SND (compile_inc_progs T asm_conf c' (src 0))))`,
  REWRITE_TAC[BKP1AUX_cake_orac_thm; cake_configs_def; state_orac_states_def]);;

(* HOL4 line 598 *)
let cake_orac_SUC = prove
 (CASE_TERM
  `!asm_conf c' src f g i.
     cake_orac (asm_conf:(A)asm_config) c' src (f:backend_config->B) (g:(A)backend_progs->D)
     (SUC i) =
   (let (c'',ps) = cake_orac asm_conf c' src I I i in
    let c''' = FST (compile_inc_progs T asm_conf c'' (src i)) in
    (f c''',g (SND (compile_inc_progs T asm_conf c''' (src (SUC i))))))`,
  REWRITE_TAC[BKP1AUX_cake_orac_thm; cake_configs_def; state_orac_states_def; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 608 *)
let compile_inc_progs_src_env_tup = prove
 (`!asm_conf cfg p cfg' progs.
     compile_inc_progs T (asm_conf:(A)asm_config) cfg p = (cfg',progs)
   ==> backend_progs_env_id progs = FST p /\ backend_progs_source_prog progs = SND p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cfg:backend_config`; `FST (p:(num#num)#(dec)list)`;
             `SND (p:(num#num)#(dec)list)`] BKP1AUX_compile_inc_progs_progs)) THEN
  ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[]);;

(* HOL4 line 617 *)
let cake_orac_SUC2 = prove
 (CASE_TERM
  `!asm_conf c' src f g i.
     cake_orac (asm_conf:(A)asm_config) c' src (f:backend_config->B) (g:(A)backend_progs->D)
     (SUC i) =
   (let (c'',ps) = cake_orac asm_conf c' src I I i in
    let c''' = FST (compile_inc_progs T asm_conf c''
                      (backend_progs_env_id ps,backend_progs_source_prog ps)) in
    (f c''',g (SND (compile_inc_progs T asm_conf c''' (src (SUC i))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cake_orac_SUC] THEN
  REWRITE_TAC[BKP1AUX_cake_orac_thm; I_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' src i`;
             `FST ((src:num->(num#num)#(dec)list) i)`;
             `SND ((src:num->(num#num)#(dec)list) i)`] BKP1AUX_compile_inc_progs_progs)) THEN
  REWRITE_TAC[PAIR] THEN SIMP_TAC[]);;

(* HOL4 line 630 *)
let from_clos_conf_EX = prove
 (`!asm_conf c p v.
     from_clos (asm_conf:(A)asm_config) c p = v
   ==> ?cc names p. from_bvl asm_conf (backend_config_clos_conf_fupd (K cc) c) names p = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_clos_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT PAIRARG_TAC THEN MESON_TAC[]);;

(* HOL4 line 639 *)
let from_bvl_conf_EX = prove
 (`!asm_conf c names p v.
     from_bvl (asm_conf:(A)asm_config) c names p = v
   ==> ?st bvlcu (names:mlstring spt) p.
         from_bvi asm_conf
           (backend_config_bvl_conf_fupd bvlcu
              (backend_config_clos_conf_fupd (\c. clos_to_bvl_config_start_fupd (K st) c) c))
           names p = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_bvl_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT PAIRARG_TAC THEN MESON_TAC[]);;

(* HOL4 line 650 *)
let from_bvi_conf_EX = prove
 (`!asm_conf c names p v.
     from_bvi (asm_conf:(A)asm_config) c names p = v
   ==> ?p. from_data asm_conf c names p = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_bvi_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MESON_TAC[]);;

(* HOL4 line 658 *)
let from_data_conf_EX = prove
 (`!asm_conf c names p v.
     from_data (asm_conf:(A)asm_config) c names p = v
   ==> ?wcu p. from_word asm_conf (backend_config_word_to_word_conf_fupd wcu c) names p = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_data_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT PAIRARG_TAC THEN MESON_TAC[]);;

(* HOL4 line 667 *)
let from_word_conf_EX = prove
 (`!asm_conf c names p v.
     from_word (asm_conf:(A)asm_config) c names p = v
   ==> ?wc p bm. from_stack asm_conf (backend_config_word_conf_fupd (K wc) c) names p bm = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_word_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT PAIRARG_TAC THEN MESON_TAC[]);;

(* HOL4 line 676 *)
let from_stack_conf_EX = prove
 (`!asm_conf c names p bm v.
     from_stack (asm_conf:(A)asm_config) c names p (bm:B) = v
   ==> ?p. from_lab asm_conf c names p bm = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_stack_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MESON_TAC[]);;

(* HOL4 line 684 *)
let from_lab_conf_EX = prove
 (`!asm_conf c names p bm bytes bitmap c'.
     from_lab (asm_conf:(A)asm_config) c names p (bm:B) = SOME (bytes,bitmap,c')
   ==> ?lc. c' = backend_config_lab_conf_fupd (K lc)
                   (backend_config_symbols_fupd
                      (K (MAP (\(n,p,l). (lookup_any n names (implode "NOTFOUND"),p,l))
                            (lab_to_target_config_sec_pos_len lc))) c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[from_lab_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 694: val from_EXS (an ML list of the seven theorems above) *)

(* HOL4 line 714 *)
let oracle_monotonic_globals_flat_to_clos = prove
 (`!p orac.
     no_Mat_decs p /\
   (!n. no_Mat_decs (SND ((orac:num->C#flat_exp list) n))) /\
   oracle_monotonic (IMAGE SUC o SET_OF_BAG o flat_elist_globals o SND) (<)
     (0 INSERT IMAGE SUC (SET_OF_BAG (flat_elist_globals p))) orac
   ==> oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
         (SET_OF_BAG (clos_elist_globals (flat_to_clos_compile_prog p)))
         (pure_co inc_compile_decs o orac)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC oracle_monotonic_subset THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[compile_prog_set_globals] THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_BAG; BAG_IN_BAG_UNION; BAG_IN_BAG_INSERT; NOT_IN_EMPTY_BAG;
                IN_INSERT; IN_IMAGE] THEN
    SIMP_TAC[BAG_IN_FINITE_BAG_IMAGE; flat_FINITE_BAG_set_globals] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[o_THM; SND_pure_co; inc_compile_decs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; elist_globals_insert_interp; clos_elist_globals_append] THEN
  SUBGOAL_THEN `no_Mat_decs [flat_Con backend_common_None NONE []]` ASSUME_TAC THENL
   [SIMP[no_Mat_def]; ALL_TAC] THEN
  ASM_SIMP_TAC[compile_decs_set_globals] THEN
  SIMP[flat_set_globals_def; BAG_IMAGE_EMPTY; BAG_UNION_EMPTY] THEN
  REWRITE_TAC[SUBSET; IN_SET_OF_BAG; IN_IMAGE] THEN
  SIMP_TAC[BAG_IN_FINITE_BAG_IMAGE; flat_FINITE_BAG_set_globals] THEN MESON_TAC[]);;

(* HOL4 line 735 *)
let cake_orac_eq_I = prove
 (`!f g asm_conf c syntax. cake_orac (asm_conf:(A)asm_config) c syntax (f:backend_config->B)
           (g:(A)backend_progs->D) =
         (f ## g) o cake_orac asm_conf c syntax I I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; BKP1AUX_cake_orac_thm; PAIR_MAP_THM; I_THM]);;

(* HOL4 line 741 *)
let cake_orac_invariant = prove
 (`!P f c asm_conf syntax g.
     P ((f:backend_config->B) c) /\
   (!c prog. P (f c) ==> P (f (FST (compile_inc_progs T (asm_conf:(A)asm_config) c prog))))
   ==> (!i. P (FST (cake_orac asm_conf c syntax f (g:(A)backend_progs->D) i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[BKP1AUX_cake_orac_thm; cake_configs_def] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[state_orac_states_def]);;

(* HOL4 lines 753-758: fun conseq, fun qsubpat_x_assum (tactics) *)

(* BKP1AUX: the namespace arithmetic of the bvl_to_bvi next names *)
let BKP1AUX_ns_add = prove
 (`!x k. (x + bvl_to_bvi_namespaces * k) MOD bvl_to_bvi_namespaces =
         x MOD bvl_to_bvi_namespaces`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let BKP1AUX_tailrec_next_ns = prove
 (`!b n xs. (bvl_num_stubs <= n ==> bvl_num_stubs <= FST (bvi_tailrec_compile_prog b n xs)) /\
            (!j. bvl_to_bviProof_in_ns j n ==> bvl_to_bviProof_in_ns j (FST (bvi_tailrec_compile_prog b n xs)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `bvi_tailrec_compile_prog b n xs` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_compile_prog_next_mono) THEN
  ASM_REWRITE_TAC[bvl_to_bviProof_in_ns_def; BKP1AUX_ns_add] THEN ARITH_TAC);;

let BKP1AUX_tmc_next_ns = prove
 (`!b n xs. (bvl_num_stubs <= n ==> bvl_num_stubs <= FST (bvi_tmc_compile_prog b n xs)) /\
            (!j. bvl_to_bviProof_in_ns j n ==> bvl_to_bviProof_in_ns j (FST (bvi_tmc_compile_prog b n xs)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `bvi_tmc_compile_prog b n xs` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_prog_next_mono) THEN
  ASM_REWRITE_TAC[bvl_to_bviProof_in_ns_def; BKP1AUX_ns_add] THEN ARITH_TAC);;

let BKP1AUX_tailrec_next = prove
 (`!b n xs. ?k. FST (bvi_tailrec_compile_prog b n xs) = n + bvl_to_bvi_namespaces * k`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `bvi_tailrec_compile_prog b n xs` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
  ASM_MESON_TAC[bvi_tailrecProof_compile_prog_next_mono]);;

let BKP1AUX_tmc_next = prove
 (`!b n xs. ?k. FST (bvi_tmc_compile_prog b n xs) = n + bvl_to_bvi_namespaces * k`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `bvi_tmc_compile_prog b n xs` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
  ASM_MESON_TAC[bvi_tmcProof_compile_prog_next_mono]);;

(* BKP1AUX: does a theorem mention the constant named c (an OCaml helper) *)
let bkp1aux_tm_mentions c tm =
  can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false)) tm;;
let bkp1aux_mentions c th = bkp1aux_tm_mentions c (concl th);;

(* HOL4 line 760 *)
let bvl_to_bvi_compile_semantics2 = prove
 (`!start c names prog start' prog' inlines bvi_inlines n1 n2 n3 names1 co ffi0 cc.
     bvl_to_bvi_compile start c names prog =
     (start',prog',inlines,bvi_inlines,n1,n2,n3,names1) /\
   (?v. FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#
                     (num#num#bvl_exp)list) 0) =
        (inlines,n1,n2,n3,bvi_inlines,v)) /\
   (!n. ALL_DISTINCT (MAP FST (SND (co n)))) /\
   ALL_DISTINCT (MAP FST prog) /\
   is_state_oracle (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c))
     (state_co bvl_to_bvi_compile_inc
        (state_co (bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit c)
                     (bvl_to_bvi_config_split_main_at_seq c) (bvl_to_bvi_config_exp_cut c))
           co)) /\
   is_state_oracle (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c))
     (state_co (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c))
        (state_co bvl_to_bvi_compile_inc
           (state_co (bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit c)
                        (bvl_to_bvi_config_split_main_at_seq c) (bvl_to_bvi_config_exp_cut c))
              co)))
   ==> ~(bvl_semantics ffi0 (fromAList prog) co (full_cc c cc) start = Fail)
   ==> bvi_semantics ffi0 (fromAList prog') (full_co c co) cc start' =
       bvl_semantics (ffi0:(FFI)ffi_state) (fromAList prog) co (full_cc c cc) start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`start:num`; `c:bvl_to_bvi_config`; `names:(mlstring)spt`;
    `prog:(num#num#bvl_exp)list`; `start':num`; `prog':(num#num#bvi_exp)list`;
    `inlines:(num#bvl_exp)spt`; `bvi_inlines:(num#bvi_exp)spt`; `n1:num`; `n2:num`; `n3:num`;
    `names1:(mlstring)spt`;
    `co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list`;
    `ffi0:(FFI)ffi_state`;
    `cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option`]
    bvl_to_bviProof_compile_semantics) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `?k2 k3. n2 = (bvl_num_stubs + 2) + bvl_to_bvi_namespaces * k2 /\
                       n3 = (bvl_num_stubs + 3) + bvl_to_bvi_namespaces * k3`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      bkp1aux_tm_mentions "bvl_to_bvi_compile" (lhs(concl th)))) THEN
    REWRITE_TAC[bvl_to_bvi_compile_def] THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th))))) THEN
    IMP_RES_TAC bvi_tailrecProof_compile_prog_next_mono THEN
    IMP_RES_TAC bvi_tmcProof_compile_prog_next_mono THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[FST; SND; bvl_to_bviProof_in_ns_def; BKP1AUX_ns_add] THEN
    REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
                stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[is_state_oracle_def] o
    check (bkp1aux_mentions "bvi_tmc_compile_prog")) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[is_state_oracle_def] o
    check (fun th -> bkp1aux_mentions "is_state_oracle" th &&
                     not (bkp1aux_mentions "bvi_tmc_compile_prog" th))) THEN
  REWRITE_TAC[FST_state_co] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[BKP1AUX_tailrec_next_ns; BKP1AUX_tmc_next_ns]);;

(* HOL4 line 822 *)
let compile_no_stubs_wrap_pure_co = prove
 (`!coracle rn j offs sp.
     (\n. let (c,p,b) = coracle n in (c,compile_no_stubs rn j offs sp p)) =
   (pure_co (compile_no_stubs rn j (offs:A word#A word) sp o FST) o
    (coracle:num->C#(num#(A)stack_prog)list#B))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def] THEN X_GEN_TAC `n:num` THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `(coracle:num->C#(num#(A)stack_prog)list#B) n` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:C` (X_CHOOSE_THEN `pb:(num#(A)stack_prog)list#B`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `pb:(num#(A)stack_prog)list#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(num#(A)stack_prog)list` (X_CHOOSE_THEN `b:B` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; o_THM; FST]);;

(* HOL4 line 832: full_make_init_semantics |> REWRITE_RULE                 *)
(* [compile_no_stubs_wrap_pure_co] (derived here in the same way)            *)
let full_make_init_semantics2 =
  REWRITE_RULE [compile_no_stubs_wrap_pure_co] full_make_init_semantics;;

(* BKP1AUX: the next names that bvl_to_bvi_compile returns *)
let BKP1AUX_bvl_to_bvi_compile_nn = prove
 (`!start c names prog s p l bl n1 n2 n3 names'.
     bvl_to_bvi_compile start c names prog = (s,p,l,bl,n1,n2,n3,names')
     ==> ?k2 k3. n2 = (bvl_num_stubs + 2) + bvl_to_bvi_namespaces * k2 /\
                 n3 = (bvl_num_stubs + 3) + bvl_to_bvi_namespaces * k3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th))))) THEN
  IMP_RES_TAC bvi_tailrecProof_compile_prog_next_mono THEN
  IMP_RES_TAC bvi_tmcProof_compile_prog_next_mono THEN ASM_MESON_TAC[]);;

(* HOL4 line 835 *)
let data_num_stubs_LE_tailrec_compile = prove
 (`!nn2 orac n do_it.
     data_num_stubs <= nn2 /\ ALL (\x. data_num_stubs <= x) (MAP FST (orac n))
   ==> ALL (\x. data_num_stubs <= x)
         (MAP FST (state_co_progs (bvi_tailrec_compile_prog do_it) nn2 orac n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[state_co_progs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. data_num_stubs <=
                    state_orac_states (bvi_tailrec_compile_prog do_it) nn2 orac m`
    ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[state_orac_states_def] THEN
    MP_TAC(ISPECL [`do_it:bool`;
      `state_orac_states (bvi_tailrec_compile_prog do_it) nn2 orac m`;
      `(orac:num->(num#num#bvi_exp)list) m`] BKP1AUX_tailrec_next) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_tailrec_compile_prog do_it
     (state_orac_states (bvi_tailrec_compile_prog do_it) nn2 orac n)
     ((orac:num->(num#num#bvi_exp)list) n)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `ys:(num#num#bvi_exp)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  MP_TAC(INST [`do_it:bool`,`b:bool`;
    `state_orac_states (bvi_tailrec_compile_prog do_it) nn2 orac n`,`n:num`;
    `(orac:num->(num#num#bvi_exp)list) n`,`xs:(num#num#bvi_exp)list`;
    `n1:num`,`n1:num`; `ys:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
    `e:num`,`e:num`] bvi_tailrecProof_compile_prog_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC]);;

(* HOL4 line 861 *)
let data_num_stubs_LE_bvl_bvi_compile = prove
 (`!nn1 orac n.
     ALL (\x. data_num_stubs <= x)
     (MAP FST (state_co_progs bvl_to_bvi_compile_inc nn1 orac n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_co_progs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `bvl_to_bvi_compile_inc
     (state_orac_states bvl_to_bvi_compile_inc nn1 orac n)
     ((orac:num->(num#num#bvl_exp)list) n)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `ys:(num#num#bvi_exp)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`state_orac_states bvl_to_bvi_compile_inc nn1 orac n`;
    `(orac:num->(num#num#bvl_exp)list) n`; `n2:num`; `ys:(num#num#bvi_exp)list`; `e:num`]
    compile_inc_next_range) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `data_num_stubs <= bvl_num_stubs` MP_TAC THENL
   [REWRITE_TAC[bvl_num_stubs_def] THEN ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

(* BKP1AUX: how compile_inc_progs changes the bvl_to_bvi configuration *)
let BKP1AUX_compile_inc_progs_bvl_conf = prove
 (`!k asm_conf c p.
     ?q. backend_config_bvl_conf (FST (compile_inc_progs k (asm_conf:(A)asm_config) c p)) =
         FST (bvl_to_bvi_compile_inc_all (backend_config_bvl_conf c) q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inc_progs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "backend_config").ri_accfupds;
                              (record_info "backend_config").ri_accessors; K_THM]) THEN
  ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM] THEN
  FIRST_X_ASSUM(fun th -> if bkp1aux_mentions "bvl_to_bvi_compile_inc_all" th
                          then (EXISTS_TAC (rand(lhs(concl th))) THEN
                                REWRITE_TAC[th; FST])
                          else NO_TAC));;

let BKP1AUX_compile_inc_all_nn = prove
 (`!c p c1 p1.
     bvl_to_bvi_compile_inc_all c p = (c1,p1)
     ==> (?xs. bvl_to_bvi_config_next_name2 c1 =
               FST (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
                      (bvl_to_bvi_config_next_name2 c) xs)) /\
         (?xs. bvl_to_bvi_config_next_name3 c1 =
               FST (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
                      (bvl_to_bvi_config_next_name3 c) xs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "bvl_to_bvi_config").ri_accfupds;
                              (record_info "bvl_to_bvi_config").ri_accessors; K_THM]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th))))) THEN
  REWRITE_TAC[(record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors; K_THM] THEN
  CONJ_TAC THEN ASM_MESON_TAC[FST]);;

(* HOL4 line 876 *)
let configs_nn2_MULT_namespaces = prove
 (`!asm_conf c' syntax n.
     ?k. bvl_to_bvi_config_next_name2
         (backend_config_bvl_conf (cake_configs (asm_conf:(A)asm_config) c' syntax n)) =
       bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c') + k * bvl_to_bvi_namespaces`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def] THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o REWRITE_RULE[cake_configs_def]) THEN
  MP_TAC(ISPECL [`T`; `asm_conf:(A)asm_config`;
    `state_orac_states (compile_inc_progs T (asm_conf:(A)asm_config)) c' syntax n`;
    `(syntax:num->(num#num)#(dec)list) n`] BKP1AUX_compile_inc_progs_bvl_conf) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(num#num#bvl_exp)list` SUBST1_TAC) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "bvl_to_bvi_compile_inc_all" with Failure _ -> false) w in
    MP_TAC(MATCH_MP BKP1AUX_compile_inc_all_nn (SYM(ISPEC t PAIR)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(num#num#bvi_exp)list` SUBST1_TAC o CONJUNCT1) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "bvi_tailrec_compile_prog" with Failure _ -> false) w in
    let b,n,xs = match snd(strip_comb t) with [b;n;xs] -> b,n,xs | _ -> failwith "args" in
    MP_TAC(ISPECL [b;n;xs] BKP1AUX_tailrec_next)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k':num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `k + k':num` THEN ARITH_TAC);;

(* HOL4 line 890 *)
let configs_nn2_MOD_namespaces = prove
 (`!asm_conf c' syntax n.
     bvl_to_bvi_config_next_name2
     (backend_config_bvl_conf (cake_configs (asm_conf:(A)asm_config) c' syntax n))
     MOD bvl_to_bvi_namespaces =
   bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c') MOD bvl_to_bvi_namespaces`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC_ALL configs_nn2_MULT_namespaces) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* HOL4 line 900 *)
let configs_nn3_MULT_namespaces = prove
 (`!asm_conf c' syntax n.
     ?k. bvl_to_bvi_config_next_name3
         (backend_config_bvl_conf (cake_configs (asm_conf:(A)asm_config) c' syntax n)) =
       bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c') + k * bvl_to_bvi_namespaces`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def] THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o REWRITE_RULE[cake_configs_def]) THEN
  MP_TAC(ISPECL [`T`; `asm_conf:(A)asm_config`;
    `state_orac_states (compile_inc_progs T (asm_conf:(A)asm_config)) c' syntax n`;
    `(syntax:num->(num#num)#(dec)list) n`] BKP1AUX_compile_inc_progs_bvl_conf) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(num#num#bvl_exp)list` SUBST1_TAC) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "bvl_to_bvi_compile_inc_all" with Failure _ -> false) w in
    MP_TAC(MATCH_MP BKP1AUX_compile_inc_all_nn (SYM(ISPEC t PAIR)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(num#num#bvi_exp)list` SUBST1_TAC o CONJUNCT2) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "bvi_tmc_compile_prog" with Failure _ -> false) w in
    let b,n,xs = match snd(strip_comb t) with [b;n;xs] -> b,n,xs | _ -> failwith "args" in
    MP_TAC(ISPECL [b;n;xs] BKP1AUX_tmc_next)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k':num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `k + k':num` THEN ARITH_TAC);;

(* HOL4 line 914 *)
let configs_nn3_MOD_namespaces = prove
 (`!asm_conf c' syntax n.
     bvl_to_bvi_config_next_name3
     (backend_config_bvl_conf (cake_configs (asm_conf:(A)asm_config) c' syntax n))
     MOD bvl_to_bvi_namespaces =
   bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c') MOD bvl_to_bvi_namespaces`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC_ALL configs_nn3_MULT_namespaces) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* BKP1AUX: the next names of the configuration that backend_compile returns *)
let BKP1AUX_backend_compile_nn = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> ?k2 k3.
           bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c') =
             (bvl_num_stubs + 2) + bvl_to_bvi_namespaces * k2 /\
           bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c') =
             (bvl_num_stubs + 3) + bvl_to_bvi_namespaces * k3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backend_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[(record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM;
              (record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors] THEN
  FIRST_X_ASSUM(fun th -> if bkp1aux_mentions "bvl_to_bvi_compile" th
                          then ACCEPT_TAC(MATCH_MP BKP1AUX_bvl_to_bvi_compile_nn th)
                          else NO_TAC));;

(* HOL4 line 924 *)
let configs_nn2_MOD_namespaces_ok = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> bvl_to_bvi_config_next_name2 (backend_config_bvl_conf c') MOD
       bvl_to_bvi_namespaces = 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn o
                                 CONJUNCT1) THEN
  ASM_REWRITE_TAC[BKP1AUX_ns_add] THEN
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 938 *)
let configs_nn3_MOD_namespaces_ok = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> bvl_to_bvi_config_next_name3 (backend_config_bvl_conf c') MOD
       bvl_to_bvi_namespaces = 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn o
                                 CONJUNCT1) THEN
  ASM_REWRITE_TAC[BKP1AUX_ns_add] THEN
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 952 *)
let bvl_to_bvi_compile_inc_all_num_stubs_LE = prove
 (`!c bvl c' bvi.
     bvl_to_bvi_compile_inc_all c bvl = (c',bvi)
   ==> bvl_num_stubs <= bvl_to_bvi_config_next_name2 c /\
       bvl_num_stubs <= bvl_to_bvi_config_next_name3 c
   ==> ALL (\x. bvl_num_stubs <= x) (MAP FST bvi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "bvl_to_bvi_config").ri_accfupds;
                              (record_info "bvl_to_bvi_config").ri_accessors; K_THM]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    type_of(rhs(concl th)) = `:(num#num#bvi_exp)list`)) THEN
  FIRST_ASSUM(fun th -> if bkp1aux_mentions "bvi_inline_compile_inc" th
                        then SUBST1_TAC(MATCH_MP compile_inc_MAP_FST th) else NO_TAC) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if bkp1aux_mentions "bvi_tmc_compile_prog" th
                        then MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] bvi_tmcProof_compile_prog_MEM)
                                       th)
                        else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
  FIRST_ASSUM(fun th -> if bkp1aux_mentions "bvi_tailrec_compile_prog" th
                        then MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ]
                                                bvi_tailrecProof_compile_prog_MEM) th)
                        else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
  FIRST_ASSUM(fun th -> if bkp1aux_mentions "bvl_to_bvi_compile_inc" th &&
                           not (bkp1aux_mentions "bvl_to_bvi_compile_inc_all" th)
                        then MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] compile_inc_next_range) th)
                        else NO_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

(* HOL4 line 978 *)
let bvl_num_stubs_LE_bvi_prog = prove
 (`!asm_conf c prog b bm c' syntax f n.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> ALL (\x. bvl_num_stubs <= x)
         (MAP FST (SND (cake_orac asm_conf c' syntax (f:backend_config->B)
                          (\ps. backend_progs_bvi_prog ps) n)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[BKP1AUX_cake_orac_thm; SND] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_progs)) THEN
  REWRITE_TAC[PAIR] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "bvl_to_bvi_compile_inc_all" with Failure _ -> false) w in
    MP_TAC(MATCH_MP bvl_to_bvi_compile_inc_all_num_stubs_LE (SYM(ISPEC t PAIR)))) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn) THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
                 `syntax:num->(num#num)#(dec)list`; `n:num`] configs_nn2_MULT_namespaces) THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
                 `syntax:num->(num#num)#(dec)list`; `n:num`] configs_nn3_MULT_namespaces) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 1003: stack_to_lab_orac_eq |> SIMP_RULE std_ss [] |> SPEC_ALL *)
(* |> UNDISCH_ALL |> GSYM |> DISCH_ALL (derived here in the same way, then  *)
(* GEN_ALL; the SIMP_RULE std_ss [] is left out: in HOL4 it eliminates the  *)
(* variables fixed by equations among the hypotheses, which stay hypotheses *)
(* here, an equivalent statement)                                            *)
let stack_to_lab_orac_eq_std_sym =
  GEN_ALL (DISCH_ALL (GSYM (UNDISCH_ALL (SPEC_ALL stack_to_lab_orac_eq))));;

(* HOL4 line 1007 *)
let state_co_fun_def = cake_def
  `state_co_fun (f_inc:S->P->T#Q) (x:(S#C)#P) =
     let ((cfg1,cfg2),p) = x in
     let (x1,p') = f_inc cfg1 p in
     (cfg2,p')`;;

(* HOL4 line 1014 *)
let state_co_eq_comp = prove
 (`!f_inc orac.
     state_co (f_inc:S->P->T#Q) (orac:num->(S#C)#P) = state_co_fun f_inc o orac`,
  REWRITE_TAC[FUN_EQ_THM; state_co_def; state_co_fun_def; o_THM]);;

(* BKP1AUX: the configuration that compile_inc_progs T returns, by component *)
let BKP1AUX_compile_inc_progs_confs = prove
 (`!asm_conf c env_id p.
     let c1 = FST (compile_inc_progs T (asm_conf:(A)asm_config) c (env_id,p)) in
     let ps = SND (compile_inc_progs T asm_conf c (env_id,p)) in
     backend_config_source_conf c1 =
       FST (inc_compile env_id (backend_config_source_conf c) (source_to_source_compile p)) /\
     backend_config_clos_conf c1 =
       FST (clos_to_bvl_compile_inc (backend_config_clos_conf c) (backend_progs_clos_prog ps)) /\
     backend_config_bvl_conf c1 =
       FST (bvl_to_bvi_compile_inc_all (backend_config_bvl_conf c) (backend_progs_bvl_prog ps))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inc_progs_def; keep_progs_T; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "backend_config").ri_accfupds;
                              (record_info "backend_config").ri_accessors; K_THM]) THEN
  ASM_REWRITE_TAC[(record_info "backend_progs").ri_accfupds;
                  (record_info "backend_progs").ri_accessors;
                  (record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM; PAIR_MAP_THM; I_THM;
                  FST; SND; PAIR_MAP_I]);;

(* HOL4 line 1020 *)
let is_state_oracle_cake_orac_comp = prove
 (CASE_TERM
  `!asm_conf c' syntax f g h f_inc.
     (!i ps'.
      let (c'',ps) = compile_inc_progs T (asm_conf:(A)asm_config)
                       (cake_configs asm_conf c' syntax i) (syntax i) in
      let ((f_c,x1),f_p) =
        (f:B#D->(S#E)#P) ((g:backend_config->B) (cake_configs asm_conf c' syntax i),
                          (h:(A)backend_progs->D) ps) in
      let ((f_c',x2),x3) = f (g c'',ps') in
      f_c' = FST ((f_inc:S->P->S#Q) f_c f_p))
   ==> is_state_oracle f_inc (f o cake_orac asm_conf c' syntax g h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[is_state_oracle_def; o_THM; BKP1AUX_cake_orac_thm] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`;
    `(h:(A)backend_progs->D) (SND (compile_inc_progs T (asm_conf:(A)asm_config)
       (cake_configs asm_conf c' syntax (SUC n)) (syntax (SUC n))))`]) THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BKP1AUX_PAIRS_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

(* HOL4 line 1039: is_state_oracle_cake_orac_comp |> Q.GEN `f` |> Q.ISPEC  *)
(* `I : (('x # 'y) # 'z -> ('x # 'y) # 'z)` |> REWRITE_RULE [I_o_ID]        *)
(* (derived here in the same way, then GEN_ALL; 'x 'y 'z are X Y Z)           *)
let is_state_oracle_cake_orac =
  let th = SPEC_ALL is_state_oracle_cake_orac_comp in
  let f = find (fun v -> fst (dest_var v) = "f") (frees (concl th)) in
  GEN_ALL (REWRITE_RULE [I_O_ID]
             (ISPEC `I:(X#Y)#Z->(X#Y)#Z` (GEN f th)));;

(* HOL4 line 1043 *)
let cake_orac_clos_is_state = prove
 (`!asm_conf c' syntax.
     is_state_oracle clos_to_bvl_compile_inc
     (cake_orac (asm_conf:(A)asm_config) c' syntax
        (\c. (backend_config_clos_conf c,one)) (\ps. backend_progs_clos_prog ps))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC is_state_oracle_cake_orac THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`cake_configs (asm_conf:(A)asm_config) c' syntax i`,`C:backend_config`) THEN
  SPEC_TAC(`(syntax:num->(num#num)#(dec)list) i`,`q:(num#num)#(dec)list`) THEN
  X_GEN_TAC `q:(num#num)#(dec)list` THEN X_GEN_TAC `C:backend_config` THEN
  MP_TAC(ISPEC `q:(num#num)#(dec)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num#num` (X_CHOOSE_THEN `p:(dec)list` SUBST1_TAC)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `C:backend_config`; `e:num#num`; `p:(dec)list`]
       BKP1AUX_compile_inc_progs_confs)) THEN
  SPEC_TAC(`compile_inc_progs T (asm_conf:(A)asm_config) C (e,p)`,
           `r:backend_config#(A)backend_progs`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN
  CASE_REWRITE_TAC[I_THM] THEN SIMP_TAC[]);;

(* HOL4 line 1054 *)
let cake_orac_source_is_state = prove
 (`!asm_conf c' syntax.
     is_state_oracle
     (\c (env_id,decs). inc_compile env_id c (source_to_source_compile decs))
     (cake_orac (asm_conf:(A)asm_config) c' syntax config_tuple1
        (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC is_state_oracle_cake_orac THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`cake_configs (asm_conf:(A)asm_config) c' syntax i`,`C:backend_config`) THEN
  SPEC_TAC(`(syntax:num->(num#num)#(dec)list) i`,`q:(num#num)#(dec)list`) THEN
  X_GEN_TAC `q:(num#num)#(dec)list` THEN X_GEN_TAC `C:backend_config` THEN
  MP_TAC(ISPEC `q:(num#num)#(dec)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num#num` (X_CHOOSE_THEN `p:(dec)list` SUBST1_TAC)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `C:backend_config`; `e:num#num`; `p:(dec)list`]
       BKP1AUX_compile_inc_progs_confs)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `C:backend_config`; `e:num#num`; `p:(dec)list`]
       BKP1AUX_compile_inc_progs_progs)) THEN
  MP_TAC(ISPEC `compile_inc_progs T (asm_conf:(A)asm_config) C (e,p)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:backend_config` (X_CHOOSE_THEN `ps:(A)backend_progs`
    SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[config_tuple1_def] THEN
  CASE_REWRITE_TAC[I_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1066: REWRITE_CONV [inc_compile_decs_def] of                  *)
(* SND (flat_to_clos_inc_compile p) (derived here in the same way, then      *)
(* GEN_ALL)                                                                  *)
let SND_flat_to_clos_inc_compile =
  GEN_ALL (REWRITE_CONV [inc_compile_decs_def] `SND (inc_compile_decs p)`);;

(* HOL4 line 1070 (^cake_orac_config_inv_f c'' = ^cake_orac_config_inv_f c *)
(* is written out as the equality of the twelve components)                  *)
let is_state_oracle_cake_orac_to_comp = prove
 (CASE_TERM
  `!f_inc asm_conf c' syntax st_f ps_f c prog b bm adj g h g_inc.
     is_state_oracle (f_inc:S->P->S#Q)
     (cake_orac (asm_conf:(A)asm_config) c' syntax (st_f:backend_config->S#C)
        (ps_f:(A)backend_progs->P))
   ==> backend_compile asm_conf c prog = SOME (b,bm,c')
   ==> (!c'' ps c''' g_p'.
          (source_to_flat_config_pattern_cfg (backend_config_source_conf c''),
           clos_to_bvl_config_max_app (backend_config_clos_conf c''),
           clos_to_bvl_config_do_call (backend_config_clos_conf c''),
           IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c'')),
           known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c'')),
           clos_to_bvl_config_do_mti (backend_config_clos_conf c''),
           bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c''),
           bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c''),
           bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c''),
           bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c''),
           bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c''),
           backend_config_data_conf c'',
           word_to_word_config_reg_alg (backend_config_word_to_word_conf c''),
           backend_config_stack_conf c'',asm_conf) =
          (source_to_flat_config_pattern_cfg (backend_config_source_conf c),
           clos_to_bvl_config_max_app (backend_config_clos_conf c),
           clos_to_bvl_config_do_call (backend_config_clos_conf c),
           IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
           known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
           clos_to_bvl_config_do_mti (backend_config_clos_conf c),
           bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c),
           bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c),
           bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c),
           bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c),
           bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c),
           backend_config_data_conf c,
           word_to_word_config_reg_alg (backend_config_word_to_word_conf c),
           backend_config_stack_conf c,asm_conf)
          ==> let (f_c',x1) = f_inc (FST (st_f c'')) (ps_f ps) in
              let ((g_c,x2),g_p) =
                (adj:G#H->(U#V)#W) ((g:backend_config->G) c'',(h:(A)backend_progs->H) ps) in
              let (g_c',x3) = (g_inc:U->W->U#Z) g_c g_p in
              f_c' = FST (st_f c''') ==> g_c' = FST (FST (adj (g c''',g_p'))))
   ==> is_state_oracle g_inc (adj o cake_orac asm_conf c' syntax g h)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[is_state_oracle_def; o_THM] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`cake_configs (asm_conf:(A)asm_config) c' syntax n`;
     `SND (compile_inc_progs T (asm_conf:(A)asm_config)
             (cake_configs asm_conf c' syntax n) (syntax n))`;
     `cake_configs (asm_conf:(A)asm_config) c' syntax (SUC n)`;
     `(h:(A)backend_progs->H) (SND (compile_inc_progs T (asm_conf:(A)asm_config)
             (cake_configs asm_conf c' syntax (SUC n)) (syntax (SUC n))))`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o SPECL [`syntax:num->(num#num)#(dec)list`; `n:num`] o
                MATCH_MP cake_orac_config_eqs);
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[is_state_oracle_def]) THEN
  REWRITE_TAC[BKP1AUX_cake_orac_thm; FST; SND] THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def] THEN
  BKP1AUX_PAIRS_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[]);;

(* HOL4 line 1094 *)
let BAG_ALL_DISTINCT_BAG_IMAGE_SUC = prove
 (`!s.
     BAG_ALL_DISTINCT s ==> BAG_ALL_DISTINCT (BAG_IMAGE SUC s)`,
  GEN_TAC THEN REWRITE_TAC[BAG_ALL_DISTINCT; LSORTAUX_BAG_IMAGE_APPLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:num` THEN
  SUBGOAL_THEN `BAG_FILTER (\e0. SUC e0 = e) s = EMPTY_BAG \/
                ?n. BAG_FILTER (\e0. SUC e0 = e) s = BAG_INSERT n EMPTY_BAG`
    STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[FINITE_EMPTY_BAG; BAG_CARD_EMPTY] THEN ARITH_TAC;
    ASM_SIMP_TAC[FINITE_BAG_THM; BAG_CARD_THM] THEN ARITH_TAC] THEN
  STRUCT_CASES_TAC(SPEC `e:num` num_CASES) THENL
   [DISJ1_TAC THEN REWRITE_TAC[BAG_FILTER_DEF; EMPTY_BAG; FUN_EQ_THM; K_THM; NOT_SUC];
    ALL_TAC] THEN
  REWRITE_TAC[SUC_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `x <= 1 <=> x = 0 \/ x = 1`] THEN STRIP_TAC THENL
   [DISJ1_TAC; DISJ2_TAC THEN EXISTS_TAC `n:num`] THEN
  REWRITE_TAC[BAG_FILTER_DEF; EMPTY_BAG; BAG_INSERT; FUN_EQ_THM; K_THM] THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num = n` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;
let _ = cake_add_simps [BAG_ALL_DISTINCT_BAG_IMAGE_SUC];;

(* HOL4 line 1113 *)
let BAG_ALL_DISTINCT_BAG_IMAGE_SUC' = prove
 (`!s.
     BAG_ALL_DISTINCT s
   ==> BAG_ALL_DISTINCT (BAG_UNION (BAG_INSERT 0 EMPTY_BAG) (BAG_IMAGE SUC s))`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BAG_ALL_DISTINCT_BAG_UNION; BAG_ALL_DISTINCT_BAG_IMAGE_SUC;
               BAG_ALL_DISTINCT_THM; NOT_IN_EMPTY_BAG] THEN
  REWRITE_TAC[BAG_DISJOINT_BAG_IN; BAG_IN_BAG_INSERT; NOT_IN_EMPTY_BAG] THEN
  GEN_TAC THEN ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LSORTAUX_BAG_IN_ALT; LSORTAUX_BAG_IMAGE_APPLY] THEN
  SUBGOAL_THEN `BAG_FILTER (\e0. SUC e0 = 0) s = EMPTY_BAG` SUBST1_TAC THENL
   [REWRITE_TAC[BAG_FILTER_DEF; EMPTY_BAG; FUN_EQ_THM; K_THM; NOT_SUC]; ALL_TAC] THEN
  REWRITE_TAC[FINITE_EMPTY_BAG; BAG_CARD_EMPTY]);;
let _ = cake_add_simps [BAG_ALL_DISTINCT_BAG_IMAGE_SUC'];;

(* BKP1AUX: the closLang programs of the oracle and of to_clos *)
let BKP1AUX_cake_orac_clos_prog = prove
 (`!asm_conf c' syntax (f:backend_config->B) n.
     ?e cfg p.
       SND (cake_orac (asm_conf:(A)asm_config) c' syntax f (\ps. backend_progs_clos_prog ps) n) =
       inc_compile_decs (SND (inc_compile e cfg (source_to_source_compile p)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BKP1AUX_cake_orac_thm; SND] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_progs)) THEN
  REWRITE_TAC[PAIR] THEN MESON_TAC[]);;

let BKP1AUX_SND_inc_compile_decs = prove
 (`!p. SND (inc_compile_decs p) = []`,
  REWRITE_TAC[inc_compile_decs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SND]);;

let BKP1AUX_inc_compile_decs_props = prove
 (`!e cfg q max_app.
     let xs = FST (inc_compile_decs (SND (inc_compile e cfg q))) in
     ALL no_mti xs /\ every_Fn_vs_NONE xs /\
     (0 < max_app ==> ~contains_App_SOME max_app xs) /\
     BAG_ALL_DISTINCT (clos_elist_globals xs) /\ ALL clos_esgc_free xs`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST_inc_compile_syntactic_props] THEN
  SIMP_TAC[FST_inc_compile_set_globals; inc_compile_no_Mat; BAG_ALL_DISTINCT_BAG_IMAGE_SUC;
           inc_compile_globals_BAG_ALL_DISTINCT] THEN
  MATCH_MP_TAC FST_inc_compile_esgc_free THEN
  REWRITE_TAC[inc_compile_no_Mat; inc_compile_esgc_free]);;

let BKP1AUX_to_clos_props = prove
 (`!c prog max_app.
     let es = SND (to_clos c prog) in
     ALL no_mti es /\ every_Fn_vs_NONE es /\
     (0 < max_app ==> ~contains_App_SOME max_app es) /\
     clos_knownProof_syntax_ok es`,
  REPEAT GEN_TAC THEN REWRITE_TAC[to_clos_def; to_flat_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BKP1AUX_PAIRS_TAC THEN
  REWRITE_TAC[SND] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM(fun th -> if bkp1aux_mentions "source_to_flat_compile" th
    then ASSUME_TAC(REWRITE_RULE[SND] (AP_TERM `SND:source_to_flat_config#(flat_exp)list->
                                                   (flat_exp)list` th)) else NO_TAC) THEN
  REWRITE_TAC[compile_prog_syntactic_props; clos_knownProof_syntax_ok_def] THEN
  SUBGOAL_THEN `no_Mat_decs p /\ ALL flat_esgc_free p /\
                BAG_ALL_DISTINCT (flat_elist_globals p)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[compile_no_Mat; source_to_flatProof_compile_esgc_free;
                compile_globals_BAG_ALL_DISTINCT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[compile_prog_set_globals; BAG_ALL_DISTINCT_BAG_IMAGE_SUC';
               flat_to_closProof_compile_prog_esgc_free]);;

(* BKP1AUX: components of the configuration that clos_to_bvl_compile_inc returns *)
let BKP1AUX_clos_compile_inc_next_loc = prove
 (`!cc p.
     clos_to_bvl_config_next_loc (FST (clos_to_bvl_compile_inc cc p)) =
     FST (ignore_table clos_number_compile_inc (clos_to_bvl_config_next_loc cc)
            (cond_mti_compile_inc (clos_to_bvl_config_do_mti cc)
               (clos_to_bvl_config_max_app cc) p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BKP1AUX_PAIRS_TAC THEN
  ASM_REWRITE_TAC[FST; (record_info "clos_to_bvl_config").ri_accfupds;
                  (record_info "clos_to_bvl_config").ri_accessors; K_THM]);;

let BKP1AUX_clos_compile_inc_call_state = prove
 (`!cc p.
     FST (clos_to_bvl_config_call_state (FST (clos_to_bvl_compile_inc cc p))) =
     FST (cond_call_compile_inc (clos_to_bvl_config_do_call cc)
            (FST (clos_to_bvl_config_call_state cc))
            (SND (known_compile_inc (known_static_conf (clos_to_bvl_config_known_conf cc))
                    (option_val_approx_spt (clos_to_bvl_config_known_conf cc))
                    (SND (ignore_table clos_number_compile_inc (clos_to_bvl_config_next_loc cc)
                            (cond_mti_compile_inc (clos_to_bvl_config_do_mti cc)
                               (clos_to_bvl_config_max_app cc) p))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds;
              (record_info "clos_to_bvl_config").ri_accessors; K_THM] THEN
  BKP1AUX_PAIRS_TAC THEN
  ASM_REWRITE_TAC[FST; SND; (record_info "clos_to_bvl_config").ri_accfupds;
                  (record_info "clos_to_bvl_config").ri_accessors; K_THM]);;

let BKP1AUX_clos_compile_inc_spt = prove
 (`!cc p.
     IS_SOME (clos_to_bvl_config_known_conf cc)
     ==> option_val_approx_spt (clos_to_bvl_config_known_conf (FST (clos_to_bvl_compile_inc cc p))) =
         FST (known_compile_inc (known_static_conf (clos_to_bvl_config_known_conf cc))
                (option_val_approx_spt (clos_to_bvl_config_known_conf cc))
                (SND (ignore_table clos_number_compile_inc (clos_to_bvl_config_next_loc cc)
                        (cond_mti_compile_inc (clos_to_bvl_config_do_mti cc)
                           (clos_to_bvl_config_max_app cc) p))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds;
              (record_info "clos_to_bvl_config").ri_accessors; K_THM] THEN
  BKP1AUX_PAIRS_TAC THEN
  ASM_REWRITE_TAC[FST; SND; (record_info "clos_to_bvl_config").ri_accfupds;
                  (record_info "clos_to_bvl_config").ri_accessors; K_THM] THEN
  SPEC_TAC(`clos_to_bvl_config_known_conf cc`,`kc:clos_known_config option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[IS_SOME_DEF; option_upd_val_spt_def; option_val_approx_spt_def] THEN
  CASE_REWRITE_TAC[] THEN SIMP[]);;

let BKP1AUX_cake_orac_clos_props = prove
 (`!asm_conf c' syntax (f:backend_config->B) n max_app.
     let xs = FST (SND (cake_orac (asm_conf:(A)asm_config) c' syntax f
                          (\ps. backend_progs_clos_prog ps) n)) in
     SND (SND (cake_orac asm_conf c' syntax f (\ps. backend_progs_clos_prog ps) n)) = [] /\
     ALL no_mti xs /\ every_Fn_vs_NONE xs /\
     (0 < max_app ==> ~contains_App_SOME max_app xs) /\
     BAG_ALL_DISTINCT (clos_elist_globals xs) /\ ALL clos_esgc_free xs`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
                `syntax:num->(num#num)#(dec)list`; `f:backend_config->B`; `n:num`]
    BKP1AUX_cake_orac_clos_prog) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[BKP1AUX_SND_inc_compile_decs] THEN
  MP_TAC(SPECL [`e:num#num`; `cfg:source_to_flat_config`; `source_to_source_compile p`;
                `max_app:num`] BKP1AUX_inc_compile_decs_props) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[]);;

(* BKP1AUX: the is_state_oracle facts of syntax_oracle_ok for the oracle of *)
(* cake_orac_clos_syntax_oracle_ok                                          *)
let BKP1AUX_orac_number = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> is_state_oracle (ignore_table clos_number_compile_inc)
           (pure_co (cond_mti_compile_inc
                       (clos_to_bvl_config_do_mti (backend_config_clos_conf c))
                       (clos_to_bvl_config_max_app (backend_config_clos_conf c))) o
            cake_orac asm_conf c' syntax (SND o config_tuple1)
              (\ps. backend_progs_clos_prog ps))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC (MATCH_MP (MATCH_MP is_state_oracle_cake_orac_to_comp
    (ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
             `syntax:num->(num#num)#(dec)list`] cake_orac_clos_is_state)) th)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP_THM; I_THM; config_tuple1_def;
              pair_CASE_def; FST; SND] THEN
  MP_TAC(ISPECL [`backend_config_clos_conf c''`; `backend_progs_clos_prog (ps:(A)backend_progs)`]
    BKP1AUX_clos_compile_inc_next_loc) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let BKP1AUX_orac_call = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
     clos_to_bvl_config_do_call (backend_config_clos_conf c)
     ==> is_state_oracle clos_call_compile_inc
           (known_co (clos_to_bvl_config_known_conf (backend_config_clos_conf c))
              (state_co (ignore_table clos_number_compile_inc)
                 (pure_co (cond_mti_compile_inc
                             (clos_to_bvl_config_do_mti (backend_config_clos_conf c))
                             (clos_to_bvl_config_max_app (backend_config_clos_conf c))) o
                  cake_orac asm_conf c' syntax (SND o config_tuple1)
                    (\ps. backend_progs_clos_prog ps))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[known_co_eq_state_co_inc; state_co_eq_comp; o_ASSOC] THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC (MATCH_MP (MATCH_MP is_state_oracle_cake_orac_to_comp
    (ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
             `syntax:num->(num#num)#(dec)list`] cake_orac_clos_is_state)) th)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP_THM; I_THM; config_tuple1_def;
              state_co_fun_def; pair_CASE_def; FST; SND] THEN
  MP_TAC(ISPECL [`backend_config_clos_conf c''`; `backend_progs_clos_prog (ps:(A)backend_progs)`]
    BKP1AUX_clos_compile_inc_call_state) THEN
  ASM_REWRITE_TAC[cond_call_compile_inc_def] THEN MESON_TAC[]);;

let BKP1AUX_known_compile_inc_SOME = prove
 (`!k spt p.
     FST (known_compile_inc (known_static_conf (SOME k)) spt (p:clos_prog)) =
     FST (clos_known_compile_inc k spt (clos_fvs_compile_inc p:clos_prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[known_static_conf_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[known_compile_inc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def; FST; kcompile_inc_uncurry] THEN
  REWRITE_TAC[BKP1AUX_reset_spt_reset; known_reset_spt]);;

let BKP1AUX_orac_known = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
     IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c))
     ==> is_state_oracle
           (clos_known_compile_inc
              (THE (clos_to_bvl_config_known_conf (backend_config_clos_conf c))))
           (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o
              state_co (ignore_table clos_number_compile_inc)
                (pure_co (cond_mti_compile_inc
                            (clos_to_bvl_config_do_mti (backend_config_clos_conf c))
                            (clos_to_bvl_config_max_app (backend_config_clos_conf c))) o
                 cake_orac asm_conf c' syntax (SND o config_tuple1)
                   (\ps. backend_progs_clos_prog ps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:clos_known_config` o REWRITE_RULE[IS_SOME_EXISTS]) THEN
  ASM_REWRITE_TAC[THE_DEF] THEN
  REWRITE_TAC[state_co_eq_comp; o_ASSOC] THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC (MATCH_MP (MATCH_MP is_state_oracle_cake_orac_to_comp
    (ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
             `syntax:num->(num#num)#(dec)list`] cake_orac_clos_is_state)) th)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP_THM; I_THM; config_tuple1_def;
              state_co_fun_def; pair_CASE_def; FST; SND] THEN
  MP_TAC(ISPECL [`backend_config_clos_conf c''`; `backend_progs_clos_prog (ps:(A)backend_progs)`]
    BKP1AUX_clos_compile_inc_spt) THEN
  ASM_REWRITE_TAC[IS_SOME_DEF; BKP1AUX_known_compile_inc_SOME] THEN MESON_TAC[]);;

let BKP1AUX_backend_compile_source_conf = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> backend_config_source_conf c' =
         FST (source_to_flat_compile (backend_config_source_conf c)
                (source_to_source_compile prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backend_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[(record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM] THEN
  FIRST_X_ASSUM(fun th -> if bkp1aux_mentions "source_to_flat_compile" th
                          then REWRITE_TAC[th; FST] else NO_TAC));;

let BKP1AUX_to_clos_eq = prove
 (`!c prog.
     SND (to_clos c prog) =
     flat_to_clos_compile_prog
       (SND (source_to_flat_compile (backend_config_source_conf c)
               (source_to_source_compile prog)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[to_clos_def; to_flat_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND]);;

let BKP1AUX_SND_source_inc = prove
 (`!c0 (q:(num#num)#(dec)list).
     SND ((\c (env_id,decs). inc_compile env_id c (source_to_source_compile decs)) c0 q) =
     SND (inc_compile (FST q) c0 (source_to_source_compile (SND q)))`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND]);;

let BKP1AUX_orac_mono = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
           (SET_OF_BAG (clos_elist_globals (SND (to_clos c prog))))
           (cake_orac asm_conf c' syntax (SND o config_tuple1) (\ps. backend_progs_clos_prog ps))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM BKP1AUX_flat_to_clos_orac_eq; GSYM BKP1AUX_source_to_flat_orac_eq] THEN
  REWRITE_TAC[BKP1AUX_to_clos_eq] THEN
  MATCH_MP_TAC oracle_monotonic_globals_flat_to_clos THEN
  REWRITE_TAC[compile_no_Mat; SND_state_co; BKP1AUX_SND_source_inc; inc_compile_no_Mat] THEN
  MATCH_MP_TAC monotonic_globals_state_co_compile THEN
  EXISTS_TAC `backend_config_source_conf c` THEN
  EXISTS_TAC `source_to_source_compile prog` THEN
  EXISTS_TAC `FST (source_to_flat_compile (backend_config_source_conf c)
                     (source_to_source_compile prog))` THEN
  REWRITE_TAC[PAIR; cake_orac_source_is_state; cake_orac_0; config_tuple1_def; FST] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP BKP1AUX_backend_compile_source_conf));;

(* HOL4 line 1120 *)
let cake_orac_clos_syntax_oracle_ok = prove
 (`!asm_conf c prog b bm c' c2 clos_prog clos_c' clos_prog' syntax.
     backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (b,bm,c') /\
   clos_to_bvl_compile c2 clos_prog = (clos_c',clos_prog') /\
   (?st. backend_config_clos_conf c' = clos_to_bvl_config_start_fupd (K st) clos_c') /\
   c2 = backend_config_clos_conf c /\ clos_prog = SND (to_clos c prog) /\
   1 <= clos_to_bvl_config_max_app (backend_config_clos_conf c) /\
   backend_config_source_conf c = prim_src_config
   ==> clos_to_bvlProof_syntax_oracle_ok (backend_config_clos_conf c) clos_c' clos_prog
         (cake_orac asm_conf c' syntax (SND o config_tuple1)
            (\ps. backend_progs_clos_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  SUBGOAL_THEN `0 < clos_to_bvl_config_max_app (backend_config_clos_conf c)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPECL [`c:backend_config`; `prog:(dec)list`;
    `clos_to_bvl_config_max_app (backend_config_clos_conf c)`] BKP1AUX_to_clos_props)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (GEN `n:num` (ISPECL
    [`asm_conf:(A)asm_config`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
     `SND o config_tuple1`; `n:num`;
     `clos_to_bvl_config_max_app (backend_config_clos_conf c)`]
    BKP1AUX_cake_orac_clos_props))) THEN
  ASM_REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_syntax_oracle_ok_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cake_orac_0; o_THM; config_tuple1_def; SND] THEN
    ASM_REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds] THEN MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC BKP1AUX_orac_call THEN ASM_MESON_TAC[];
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[BKP1AUX_orac_mono];
      MATCH_MP_TAC BKP1AUX_orac_known THEN ASM_MESON_TAC[]];
    ASM_MESON_TAC[BKP1AUX_orac_number]]);;

(* HOL4 line 1197 *)
let cake_orac_bvl_ALL_DISTINCT = prove
 (`!asm_conf c prog b bm c' syntax f n.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> ALL_DISTINCT (MAP FST (SND (cake_orac asm_conf c' syntax (f:backend_config->B)
                                    (\ps. backend_progs_bvl_prog ps) n)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `SND (cake_orac (asm_conf:(A)asm_config) c' syntax (f:backend_config->B)
                       (\ps. backend_progs_bvl_prog ps) n) =
                SND (cake_orac asm_conf c' syntax config_tuple2
                       (\ps. backend_progs_bvl_prog ps) n)` SUBST1_TAC THENL
   [REWRITE_TAC[BKP1AUX_cake_orac_thm]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP BKP1AUX_clos_to_bvl_orac_eq
    (CONJ th (REFL `backend_config_clos_conf c`)))]) THEN
  REWRITE_TAC[o_THM; SND_pure_co; SND_state_co] THEN
  MATCH_MP_TAC compile_inc_phases_all_distinct THEN
  REWRITE_TAC[o_THM; SND_pure_co; SND_cond_mti_compile_inc] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (ISPECL
    [`asm_conf:(A)asm_config`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
     `SND o config_tuple1`; `n:num`; `0`] BKP1AUX_cake_orac_clos_props)) THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT1));;

(* HOL4 line 1215 *)
let compile_lab_LENGTH = prove
 (`!asm_conf c secs bytes c'.
     compile_lab (asm_conf:(A)asm_config) c secs = SOME (bytes,c')
   ==> lab_to_target_config_pos c' = LENGTH bytes + lab_to_target_config_pos c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_lab_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[(record_info "lab_to_target_config").ri_accfupds;
              (record_info "lab_to_target_config").ri_accessors; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1223 *)
let bvl_to_bvi_compile_inc_all_DISTINCT = prove
 (`!c p c' p'.
     bvl_to_bvi_compile_inc_all c p = (c',p') /\
   ALL_DISTINCT (MAP FST p) /\
   bvl_to_bvi_config_next_name2 c MOD bvl_to_bvi_namespaces = 2 /\
   bvl_to_bvi_config_next_name3 c MOD bvl_to_bvi_namespaces = 3
   ==> ALL_DISTINCT (MAP FST p')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(K ((bvl_to_bvi_config_inlines c, bvl_to_bvi_config_next_name1 c,
                       bvl_to_bvi_config_next_name2 c, bvl_to_bvi_config_next_name3 c,
                       bvl_to_bvi_config_bvi_inlines c, one), p)):
                   num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#1)#(num#num#bvl_exp)list`;
                 `0`; `c:bvl_to_bvi_config`] ALL_DISTINCT_MAP_FST_SND_full_co) THEN
  ASM_REWRITE_TAC[K_THM; FST; SND] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> bkp1aux_mentions "bvl_to_bvi_compile_inc_all" th)) THEN
  REWRITE_TAC[bvl_to_bvi_compile_inc_all_def; full_co_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[state_co_def; K_THM; pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[(record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors; K_THM; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def; FST; SND; PAIR_EQ;
              (record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* BKP1AUX: the passes from bvi to word keep the function names *)
let BKP1AUX_MAP_FST_word_data = prove
 (`!tr rc alg (ac:(A)asm_config) dc ps.
     MAP FST (MAP (\p. full_compile_single tr rc alg ac (p,NONE))
                (MAP (data_to_word_compile_part dc) (bvi_to_data_compile_prog ps))) =
     MAP FST ps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_data_compile_prog_def] THEN
  SPEC_TAC(`ps:(num#num#bvi_exp)list`,`ps:(num#num#bvi_exp)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:num#num#bvi_exp`,`h:num#num#bvi_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; bvi_to_data_compile_part_def; data_to_word_compile_part_def;
              full_compile_single_def; word_to_word_compile_single_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def; FST]);;

(* HOL4 line 1240 *)
let cake_orac_stack_ALL_DISTINCT = prove
 (`!asm_conf c prog b bm c' syntax n.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> ALL_DISTINCT (MAP FST (FST (SND (cake_orac asm_conf c' syntax
                                         (SND o SND o SND o SND o SND o SND o config_tuple2)
                                         (\ps. (backend_progs_stack_prog ps,
                                                backend_progs_cur_bm ps)) n))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`syntax:num->(num#num)#(dec)list`; `config_tuple2`; `n:num`] o
              MATCH_MP cake_orac_bvl_ALL_DISTINCT) THEN
  REWRITE_TAC[BKP1AUX_cake_orac_thm; FST; SND] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_progs)) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "compile_word_to_stack" with Failure _ -> false) w in
    MP_TAC(MATCH_MP MAP_FST_compile_word_to_stack (SYM(ISPEC t PAIR)))) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BKP1AUX_MAP_FST_word_data] THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "bvl_to_bvi_compile_inc_all" with Failure _ -> false) w in
    let c0,p0 = match snd(strip_comb t) with [c0;p0] -> c0,p0 | _ -> failwith "args" in
    MATCH_MP_TAC bvl_to_bvi_compile_inc_all_DISTINCT THEN
    MAP_EVERY EXISTS_TAC [c0; p0; mk_icomb(mk_const("FST",[]),t)]) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  REWRITE_TAC[configs_nn2_MOD_namespaces; configs_nn3_MOD_namespaces] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn) THEN
  ASM_REWRITE_TAC[BKP1AUX_ns_add] THEN
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* BKP1AUX: zipping with a constant list *)
let BKP1AUX_ZIP_REPLICATE = prove
 (`!(l:A list) (x:B). ZIP l (REPLICATE (LENGTH l) x) = MAP (\p. (p,x)) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ZIP; LENGTH; REPLICATE; MAP]);;

(* HOL4 line 1269 *)
let MAP_full_compile_single_to_compile = prove
 (`!pp asm_c reg_count reg_alg pp0.
     pp = MAP (\p. full_compile_single (asm_config_two_reg_arith asm_c) reg_count reg_alg
                   asm_c (p,NONE)) pp0 /\
   reg_count = asm_config_reg_count (asm_c:(A)asm_config) -
               (LENGTH (asm_config_avoid_regs asm_c) + 5)
   ==> ?wc ign. word_to_word_compile wc asm_c pp0 = (ign,pp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `word_to_word_config_REC reg_alg []` THEN
  ASM_REWRITE_TAC[word_to_word_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[next_n_oracle_def; (record_info "word_to_word_config").ri_accessors;
              LENGTH; LE] THEN
  ASM_CASES_TAC `LENGTH (pp0:(num#num#(A)wl_prog)list) = 0` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[LENGTH_EQ_NIL]) THEN
    REWRITE_TAC[TAKE; DROP; MAP; ZIP; pair_CASE] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[BKP1AUX_ZIP_REPLICATE; MAP_MAP_o; o_DEF] THEN
  REWRITE_TAC[ADD_SYM] THEN MESON_TAC[]);;

(* HOL4 line 1284 (HOL4's wildcard _ of the first equation is col) *)
let compile_to_word_conventions2 = prove
 (`!wc ac p col ps.
     word_to_word_compile wc (ac:(A)asm_config) p = (col,ps) /\
   ALL (\(x1,x2,prg). no_share_inst prg \/ ~(asm_config_ISA ac = Ag32)) p
   ==> MAP FST ps = MAP FST p /\
       ALL2 labels_rel (MAP (wordConvs_extract_labels o SND o SND) p)
                       (MAP (wordConvs_extract_labels o SND o SND) ps) /\
       ALL (\(n,m,prog).
              flat_exp_conventions prog /\
              post_alloc_conventions
                (asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs ac))) prog /\
              (ALL (\(n,m,prog). every_inst (inst_ok_less ac) prog) p /\
               asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
               asm_offset_ok 0 (asm_config_hw_offset ac) (word 0) /\
               asm_offset_ok 0 (asm_config_byte_offset ac) (word 0)
               ==> full_inst_ok_less ac prog) /\
              (asm_config_two_reg_arith ac ==> every_inst two_reg_inst prog) /\
              (no_share_inst prog \/ ~(asm_config_ISA ac = Ag32))) ps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(num#num#(A)wl_prog)list`; `ac:(A)asm_config`; `wc:word_to_word_config`]
    compile_to_word_conventions) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* BKP1AUX: the labels of a section with sec_labels_ok are its own *)
let BKP1AUX_sec_labels_ok_FST = prove
 (`!(s:(A)sec) x.
     sec_labels_ok s /\ MEM x (lab_extract_labels (Section_lines s))
     ==> FST x = Section_num s`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `s:(A)sec` (cases "sec")) THEN
  REWRITE_TAC[sec_labels_ok_def; lab_Section_num_def; lab_Section_lines_def] THEN
  REWRITE_TAC[GSYM EVERY_sec_label_ok; GSYM ALL_MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN MESON_TAC[]);;

(* HOL4 line 1309 *)
let sec_labels_ok_FST_code_labels_Section_num = prove
 (`!code.
     ALL sec_labels_ok (code:((A)sec)list)
   ==> IMAGE FST (lab_get_code_labels code) = set_of_list (MAP Section_num code)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[get_code_labels_extract_labels] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_SET_OF_LIST; MEM_MAP; MEM_FLAT; o_THM] THEN
  X_GEN_TAC `k:num` THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN EXISTS_TAC `(k:num,0)` THEN REWRITE_TAC[FST] THEN ASM_MESON_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  ASM_MESON_TAC[FST; BKP1AUX_sec_labels_ok_FST]);;

(* HOL4 line 1330 *)
let stack_labels_ok_FST_code_labels_Section_num = prove
 (`!code.
     labels_ok (code:((A)sec)list)
   ==> IMAGE FST (lab_get_code_labels code) = set_of_list (MAP Section_num code)`,
  MESON_TAC[sec_labels_ok_FST_code_labels_Section_num; labels_ok_imp]);;

(* BKP1AUX: the label invariants of the stack-to-lab passes *)
let BKP1AUX_compile_no_stubs_labels_ok = prove
 (`!f jump (offs:A word#A word) sp (prog:(num#(A)stack_prog)list).
     ALL_DISTINCT (MAP FST prog) /\
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) prog
     ==> labels_ok (compile_no_stubs f jump offs sp prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compile_no_stubs_def] THEN
  MATCH_MP_TAC prog_to_section_labels_ok THEN
  REWRITE_TAC[stack_names_compile_def; MAP_MAP_o] THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `(FST o (stack_names_prog_comp f o stack_remove_prog_comp jump offs sp) o
                   stack_alloc_prog_comp) = (FST:num#(A)stack_prog->num)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; stack_alloc_prog_comp_def;
                  stack_remove_prog_comp_def; stack_names_prog_comp_def; FST];
      ASM_REWRITE_TAC[]]] THEN
  REWRITE_TAC[ALL_MAP] THEN
  UNDISCH_TAC `ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                             (stack_extract_labels p) /\
                           ALL_DISTINCT (stack_extract_labels (p:(A)stack_prog))) prog` THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `p:(A)stack_prog`] THEN
  REWRITE_TAC[stack_alloc_prog_comp_def; stack_remove_prog_comp_def;
              stack_names_prog_comp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM stack_names_lab_pres; GSYM stack_remove_lab_pres] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC_ALL (ISPECL [`n:num`; `next_lab (p:(A)stack_prog) 2`; `p:(A)stack_prog`]
    stack_alloc_lab_pres)) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  REPEAT BKP1AUX_GABS_TAC THEN REWRITE_TAC[FST; SND] THEN SIMP_TAC[]);;
(* BKP1AUX: the labels of a compiled word function *)
let BKP1AUX_fcs_labels = prove
 (`!(asm_conf:(A)asm_config) reg_alg dc (d:num#num#data_prog).
     let y = full_compile_single (asm_config_two_reg_arith asm_conf)
               (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
               reg_alg asm_conf (data_to_word_compile_part dc d,NONE) in
     ALL (\(l1,l2). l1 = FST y /\ ~(l2 = 0) /\ ~(l2 = 1))
       (wordConvs_extract_labels (SND (SND y))) /\
     ALL_DISTINCT (wordConvs_extract_labels (SND (SND y)))`,
REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`d:num#num#data_prog`,`d:num#num#data_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `a:num`; `p:data_prog`] THEN
  REWRITE_TAC[data_to_word_compile_part_def] THEN
  MP_TAC(ISPECL [`dc:data_to_word_config`; `n:num`; `2`; `p:data_prog`]
    data_to_word_lab_pres_lem) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`dc:data_to_word_config`; `n:num`; `2`; `p:data_prog`]
    comp_no_share_inst) THEN
  SPEC_TAC(`data_to_word_comp dc n 2 p:(A)wl_prog#num`,`r:(A)wl_prog#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN MAP_EVERY X_GEN_TAC [`cp:(A)wl_prog`; `l':num`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o SPECL [`cp:(A)wl_prog`; `l':num`]) THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`MAP (\p. full_compile_single (asm_config_two_reg_arith asm_conf)
               (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
               reg_alg asm_conf (p,NONE)) [n:num,a + 1,cp:(A)wl_prog]`; `asm_conf:(A)asm_config`;
    `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
    `reg_alg:num`; `[n:num,a + 1,cp:(A)wl_prog]`] MAP_full_compile_single_to_compile) THEN
  REWRITE_TAC[MAP] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] compile_to_word_conventions2)) THEN
  ASM_REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[MAP; ALL2; o_THM; labels_rel_def; CONS_11] THEN
  SPEC_TAC(`full_compile_single (asm_config_two_reg_arith asm_conf)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
       reg_alg (asm_conf:(A)asm_config) ((n,a + 1,cp),NONE)`,`y:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; SUBSET; IN_SET_OF_LIST; FORALL_PAIR_THM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_MESON_TAC[ARITH_RULE `2 <= l ==> ~(l = 0) /\ ~(l = 1)`]);;

(* BKP1AUX: the labels of the word programs of the oracle *)
let BKP1AUX_word_prog_labels = prove
 (`!(asm_conf:(A)asm_config) reg_alg dc (data:(num#num#data_prog)list).
     ALL (\(l,m,e). ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1))
                      (wordConvs_extract_labels e) /\
                    ALL_DISTINCT (wordConvs_extract_labels e))
       (MAP (\p. full_compile_single (asm_config_two_reg_arith asm_conf)
                   (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)))
                   reg_alg asm_conf (p,NONE))
          (MAP (data_to_word_compile_part dc) data))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  X_GEN_TAC `d:num#num#data_prog` THEN DISCH_TAC THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (ISPECL
    [`asm_conf:(A)asm_config`; `reg_alg:num`; `dc:data_to_word_config`; `d:num#num#data_prog`]
    BKP1AUX_fcs_labels)) THEN
  SPEC_TAC(`full_compile_single (asm_config_two_reg_arith asm_conf)
               (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
               reg_alg (asm_conf:(A)asm_config) (data_to_word_compile_part dc d,NONE)`,
           `y:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN ASM_MESON_TAC[]);;

(* HOL4 line 1337 *)
let lab_labels_ok_oracle = prove
 (`!asm_conf c prog b bm c' syntax i cfg code.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o config_tuple2)
     (\ps. backend_progs_lab_prog ps) i = (cfg,code)
   ==> labels_ok code`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`syntax:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_stack_ALL_DISTINCT) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:(lab_to_target_config)#((A)sec)list->((A)sec)list`) THEN
  REWRITE_TAC[BKP1AUX_cake_orac_thm; SND; FST] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax i`;
             `FST ((syntax:num->(num#num)#(dec)list) i)`;
             `SND ((syntax:num->(num#num)#(dec)list) i)`] BKP1AUX_compile_inc_progs_progs)) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  MATCH_MP_TAC BKP1AUX_compile_no_stubs_labels_ok THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "compile_word_to_stack" with Failure _ -> false) w in
    MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] compile_word_to_stack_lab_pres)
                          (SYM(ISPEC t PAIR)))) THEN
  REWRITE_TAC[BKP1AUX_word_prog_labels]);;

(* HOL4 line 1421 *)
let compile_lab_domain_labels = prove
 (`!asm_conf c prog b c'.
     compile_lab (asm_conf:(A)asm_config) c prog = SOME (b,c')
   ==> domain (lab_to_target_config_labels c') =
       IMAGE FST (lab_get_code_labels prog) UNION domain (lab_to_target_config_labels c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_lab_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[(record_info "lab_to_target_config").ri_accfupds;
              (record_info "lab_to_target_config").ri_accessors; K_THM] THEN
  FIRST_X_ASSUM(fun th -> if bkp1aux_mentions "remove_labels" th
    then MP_TAC th THEN STRUCT_CASES_TAC(ISPEC (rand(rand(concl th))) PAIR_SURJECTIVE)
    else NO_TAC) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN(MP_TAC o MATCH_MP remove_labels_domain_labs) THEN
  REWRITE_TAC[]);;

(* BKP1AUX: the lab_to_target configuration after compile_inc_progs T *)
let BKP1AUX_compile_inc_progs_lab_conf = prove
 (CASE_TERM
  `!asm_conf c p.
     backend_config_lab_conf (FST (compile_inc_progs T (asm_conf:(A)asm_config) c p)) =
     (match lab_to_target_compile asm_conf (backend_config_lab_conf c)
              (backend_progs_lab_prog (SND (compile_inc_progs T asm_conf c p))) with
        NONE -> backend_config_lab_conf c
      | SOME (bytes,c') -> c')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inc_progs_def; keep_progs_T; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "backend_config").ri_accfupds;
                              (record_info "backend_config").ri_accessors; K_THM]) THEN
  ASM_REWRITE_TAC[(record_info "backend_progs").ri_accfupds;
                  (record_info "backend_progs").ri_accessors;
                  (record_info "backend_config").ri_accfupds;
                  (record_info "backend_config").ri_accessors; K_THM; PAIR_MAP_THM; I_THM;
                  FST; SND; PAIR_MAP_I] THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "lab_to_target_compile" with Failure _ -> false) w in
    SPEC_TAC(t,`t:(byte list#lab_to_target_config)option`)) THEN
  MATCH_MP_TAC option_INDUCT THEN CASE_REWRITE_TAC[I_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[K_THM]);;
(* BKP1AUX: compile_lab_domain_labels for lab_to_target_compile *)
let BKP1AUX_lab_to_target_domain_labels = prove
 (`!asm_conf c p b c'.
     lab_to_target_compile (asm_conf:(A)asm_config) c p = SOME (b,c')
     ==> domain (lab_to_target_config_labels c') =
         IMAGE FST (lab_get_code_labels p) UNION domain (lab_to_target_config_labels c)`,
  REWRITE_TAC[lab_to_target_compile_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP compile_lab_domain_labels) THEN
  REWRITE_TAC[get_code_labels_filter_skip]);;

(* HOL4 line 1432 *)
let accum_lab_conf_labels = prove
 (`!asm_conf c prog b bm c' syntax i.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> domain (lab_to_target_config_labels
                 (backend_config_lab_conf (cake_configs asm_conf c' syntax i))) SUBSET
       domain (lab_to_target_config_labels (backend_config_lab_conf c')) UNION
       UNIONS (set_of_list
                 (MAP (set_of_list o MAP Section_num o SND o
                       cake_orac asm_conf c' syntax
                         (SND o SND o SND o SND o SND o SND o config_tuple2)
                         (\ps. backend_progs_lab_prog ps))
                      (COUNT_LIST i)))`,
  (REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[cake_configs_def; state_orac_states_def; COUNT_LIST_SNOC; MAP; set_of_list;
                UNIONS_0; UNION_EMPTY; SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[COUNT_LIST_SNOC; MAP_SNOC; LIST_TO_SET_SNOC] THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def] THEN
  REWRITE_TAC[GSYM cake_configs_def] THEN
  REWRITE_TAC[BKP1AUX_compile_inc_progs_lab_conf]) THEN
  (REWRITE_TAC[o_THM; BKP1AUX_cake_orac_thm; SND] THEN
  SUBGOAL_THEN `labels_ok (backend_progs_lab_prog (SND (compile_inc_progs T (asm_conf:(A)asm_config)
                   (cake_configs asm_conf c' syntax i) (syntax i))))` MP_TAC THENL
   [MATCH_MP_TAC lab_labels_ok_oracle THEN
    MAP_EVERY EXISTS_TAC [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`;
      `b:byte list`; `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
      `i:num`;
      `FST (cake_orac (asm_conf:(A)asm_config) c' syntax
              (SND o SND o SND o SND o SND o SND o config_tuple2)
              (\ps. backend_progs_lab_prog ps) i)`] THEN
    ASM_REWRITE_TAC[BKP1AUX_cake_orac_thm];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP stack_labels_ok_FST_code_labels_Section_num)) THEN
  (W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                     "lab_to_target_compile" with Failure _ -> false) w in
    MP_TAC(ISPEC t (cases "option")) THEN
    MP_TAC(ISPECL (snd(strip_comb t)) BKP1AUX_lab_to_target_domain_labels)) THEN
  REWRITE_TAC[UNIONS_INSERT] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `a:byte list#lab_to_target_config` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bytes:byte list` (X_CHOOSE_THEN `lc:lab_to_target_config`
    SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  DISCH_THEN(MP_TAC o SPECL [`bytes:byte list`; `lc:lab_to_target_config`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM SET_TAC[]));;

(* BKP1AUX: MAP FST through a name-preserving map *)
let BKP1AUX_MAP_FST_MAP = prove
 (`!(f:A#B->A#C) l. (!x. FST (f x) = FST x) ==> MAP FST (MAP f l) = MAP FST l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP]);;

let BKP1AUX_stack_to_lab_names = prove
 (`!scc dc max_heap sp (offset:A word#A word) (prog:(num#(A)stack_prog)list).
     MAP Section_num (stack_to_lab_compile scc dc max_heap sp offset prog) =
     APPEND [0; 1; 2] (APPEND [gc_stub_location] (MAP FST prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_lab_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP_prog_to_section_Section_num; stack_names_compile_def] THEN
  W(fun (asl,w) -> MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(rator(lhs w),rand(rand(lhs w)))) THEN CONJ_TAC) THENL
   [MATCH_MP_TAC BKP1AUX_MAP_FST_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM; stack_names_prog_comp_def; FST];
    ALL_TAC] THEN
  REWRITE_TAC[stack_remove_compile_def; stack_remove_init_stubs_def; MAP_APPEND; MAP; FST] THEN
  REWRITE_TAC[APPEND] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  W(fun (asl,w) -> MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(rator(lhs w),rand(rand(lhs w)))) THEN CONJ_TAC) THENL
   [MATCH_MP_TAC BKP1AUX_MAP_FST_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM; stack_remove_prog_comp_def; FST];
    ALL_TAC] THEN
  REWRITE_TAC[stack_alloc_compile_def; stack_alloc_stubs_def; MAP_APPEND; MAP; FST; APPEND] THEN
  AP_TERM_TAC THEN
  W(fun (asl,w) -> MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(rator(lhs w),rand(rand(lhs w)))) THEN CONJ_TAC) THENL
   [MATCH_MP_TAC BKP1AUX_MAP_FST_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM; stack_alloc_prog_comp_def; FST];
    ALL_TAC] THEN
  REWRITE_TAC[stack_rawcall_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC BKP1AUX_MAP_FST_MAP THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST]);;

(* HOL4 line 1469 *)
let MAP_Section_num_stack_to_lab_SUBSET = prove
 (`!prog labs scc dc max_heap sp offset.
     set_of_list (MAP FST (prog:(num#(A)stack_prog)list)) SUBSET labs /\
   pred_set_count (SUC gc_stub_location) SUBSET labs
   ==> set_of_list (MAP Section_num (stack_to_lab_compile scc dc max_heap sp offset prog))
       SUBSET labs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BKP1AUX_stack_to_lab_names; SET_OF_LIST_APPEND;
                                  gc_stub_location_eq] THEN
  REWRITE_TAC[set_of_list; UNION_SUBSET; INSERT_SUBSET; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_COUNT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* BKP1AUX: |- t = (FST t, FST (SND t), ...) for a tuple-valued term t *)
let bkp1aux_tuple_eq t =
  let rec expand tm =
    match dest_type(type_of tm) with
      "prod",[_;_] ->
        mk_pair(mk_icomb(mk_const("FST",[]),tm), expand (mk_icomb(mk_const("SND",[]),tm)))
    | _ -> tm in
  prove(mk_eq(t,expand t), REWRITE_TAC[PAIR]);;

let BKP1AUX_find_app c tm =
  find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = c with Failure _ -> false) tm;;

(* HOL4 line 1481 *)
let to_data_labels_ok = prove
 (CASE_TERM
  `!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> let (x1,p,x2) = to_data c prog in
       ALL (\n. data_num_stubs <= n) (MAP FST p) /\ ALL_DISTINCT (MAP FST p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[to_data_def; to_bvi_def; to_bvl_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; bvi_to_dataProof_MAP_FST_compile_prog] THEN
  REWRITE_TAC[(record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM] THEN
  W(fun (asl,w) ->
    let t = BKP1AUX_find_app "bvl_to_bvi_compile" w in
    MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] compile_distinct_names) (bkp1aux_tuple_eq t))) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN ANTS_TAC THENL
   [W(fun (asl,w) ->
      let t = BKP1AUX_find_app "clos_to_bvl_compile" w in
      ACCEPT_TAC(MATCH_MP compile_all_distinct_locs (bkp1aux_tuple_eq t)));
    ALL_TAC] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; to_clos_def; to_flat_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; (record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[backend_config_ok_def]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1499 *)
let data_to_word_stubs_above_store_consts_stub = prove
 (`!dc.
     ALL (\n. n > wl_store_consts_stub_location) (MAP FST (data_to_word_stubs (:A) dc))`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_stubs_DEF; generated_bignum_stubs_eq; MAP; APPEND; FST] THEN
  REWRITE_TAC D2WAUX_location_defs THEN
  REWRITE_TAC[wl_store_consts_stub_location_def; word_num_stubs_def; stack_num_stubs_def; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1505 *)
let to_word_labels_ok = prove
 (CASE_TERM
  `!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> let (x1,p,x2) = to_word asm_conf c prog in
       ALL_DISTINCT (MAP FST p) /\
       ALL (\n. n > wl_store_consts_stub_location) (MAP FST p) /\
       ALL (\(n,m,p).
              let labs = wordConvs_extract_labels p in
              ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\ ALL_DISTINCT labs) p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP to_data_labels_ok) THEN
  REWRITE_TAC[to_word_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let t = BKP1AUX_find_app "data_to_word_compile" w in
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (ISPECL (snd(strip_comb t)) data_to_word_compile_lab_pres))) THEN
  REWRITE_TAC[pair_CASE_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_APPEND; ALL_DISTINCT_MAP_FST_stubs;
              data_to_word_stubs_above_store_consts_stub] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_store_consts_stub_location < data_num_stubs` ASSUME_TAC THENL
   [REWRITE_TAC[wl_store_consts_stub_location_def; data_num_stubs_def; word_num_stubs_def;
                stack_num_stubs_def] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM; GT] THEN
  CONJ_TAC THEN X_GEN_TAC `e:num` THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`e:num`; `(:A)`;
                   `backend_config_data_conf (FST (to_data c prog))`] MAP_FST_stubs_bound) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o check (fun th -> is_forall(concl th) &&
      bkp1aux_mentions "data_num_stubs" th)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o check (fun th -> is_forall(concl th) &&
      bkp1aux_mentions "data_num_stubs" th)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `wl_store_consts_stub_location < data_num_stubs` THEN
    ARITH_TAC]);;

(* BKP1AUX: the stack configuration is not changed before word_to_stack *)
let BKP1AUX_to_bvi_stack_conf = prove
 (`!c prog. backend_config_stack_conf (FST (to_bvi c prog)) = backend_config_stack_conf c`,
  REWRITE_TAC[to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  REWRITE_TAC[FST; SND; (record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM]);;

(* HOL4 line 1531 *)
let to_bvi_perf_calls = prove
 (`!c c' prog p n.
     to_bvi c prog = (c',p,n)
     ==> stack_to_lab_config_perf_calls (backend_config_stack_conf c) =
         stack_to_lab_config_perf_calls (backend_config_stack_conf c')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM
    `FST:backend_config#(num#num#bvi_exp)list#(mlstring)spt->backend_config`) THEN
  REWRITE_TAC[FST; BKP1AUX_to_bvi_stack_conf] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BKP1AUX_to_bvi_stack_conf]);;

let BKP1AUX_to_data_stack_conf = prove
 (`!c prog. backend_config_stack_conf (FST (to_data c prog)) = backend_config_stack_conf c`,
  REWRITE_TAC[to_data_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def; FST; BKP1AUX_to_bvi_stack_conf]);;

(* HOL4 line 1541 *)
let to_data_perf_calls = prove
 (`!c c' prog p n.
     to_data c prog = (c',p,n)
     ==> stack_to_lab_config_perf_calls (backend_config_stack_conf c) =
         stack_to_lab_config_perf_calls (backend_config_stack_conf c')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM
    `FST:backend_config#(num#num#data_prog)list#(mlstring)spt->backend_config`) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BKP1AUX_to_data_stack_conf]);;

let BKP1AUX_to_word_stack_conf = prove
 (`!(asm_conf:(A)asm_config) c prog.
     backend_config_stack_conf (FST (to_word asm_conf c prog)) = backend_config_stack_conf c`,
  REWRITE_TAC[to_word_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; (record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM;
              BKP1AUX_to_data_stack_conf]);;

(* HOL4 line 1552 *)
let to_word_perf_calls = prove
 (`!c c' prog p n asm_conf.
     to_word (asm_conf:(A)asm_config) c prog = (c',p,n)
     ==> stack_to_lab_config_perf_calls (backend_config_stack_conf c) =
         stack_to_lab_config_perf_calls (backend_config_stack_conf c')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM
    `FST:backend_config#(num#num#(A)wl_prog)list#(mlstring)spt->backend_config`) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BKP1AUX_to_word_stack_conf]);;

(* BKP1AUX: the word_to_stack stub names in front of names above 6 *)
let BKP1AUX_stub_names = prove
 (`!L. ALL_DISTINCT L /\ ALL (\n. n > 6) L
       ==> ALL (\n. ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 4)) (CONS 5 (CONS 6 L)) /\
           ALL_DISTINCT (CONS 5 (CONS 6 L))`,
  GEN_TAC THEN REWRITE_TAC[ALL; ALL_DISTINCT; MEM; GSYM ALL_MEM; GT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 1563 *)
let to_lab_labels_ok = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> labels_ok (FST (SND (SND (to_lab asm_conf c prog))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP to_word_labels_ok) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[backend_config_ok_def] o CONJUNCT2) THEN
  REWRITE_TAC[to_lab_def; to_stack_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; BKP1AUX_to_word_stack_conf; (record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC stack_to_lab_compile_lab_pres THEN
  W(fun (asl,w) ->
    let t = BKP1AUX_find_app "word_to_stack_compile" w in
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (ISPECL [rand t; `asm_conf:(A)asm_config`] word_to_stack_compile_lab_pres))) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> bkp1aux_mentions "wl_store_consts_stub_location" th &&
     bkp1aux_mentions "to_word" th && not (bkp1aux_mentions "word_to_stack_compile" th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> bkp1aux_mentions "ALL_DISTINCT" th &&
     bkp1aux_mentions "to_word" th && not (bkp1aux_mentions "word_to_stack_compile" th) &&
     not (bkp1aux_mentions "wordConvs_extract_labels" th))) THEN
  SPEC_TAC(`MAP FST (FST (SND (to_word (asm_conf:(A)asm_config) c prog)))`,`L:num list`) THEN
  REWRITE_TAC[raise_stub_location_def; wl_store_consts_stub_location_def; word_num_stubs_def;
              stack_num_stubs_def; gc_stub_location_eq] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[BKP1AUX_stub_names]);;

(* HOL4 line 1589 *)
let oracle_monotonic_slice = prove
 (`!g f init_s orac. (!z. oracle_monotonic (\x. (f:A->B->bool) x INTER PREIMAGE (g:B->C) {z})
              (\x y. ~(x = y)) (init_s INTER PREIMAGE g {z}) orac)
       ==> oracle_monotonic f (\x y. ~(x = y)) init_s orac`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oracle_monotonic_def; IN_INTER; IN_PREIMAGE; IN_SING] THEN
  MESON_TAC[]);;

(* HOL4 line 1610 *)
let oracle_monotonic_rel_mono = prove
 (`!R R' f init_s orac. (!x y. R x y ==> R' x y) /\ oracle_monotonic (f:A->B->bool) R init_s orac
          ==> oracle_monotonic f R' init_s orac`,
  REWRITE_TAC[oracle_monotonic_def] THEN MESON_TAC[]);;

(* HOL4 line 1617 *)
let backendProof_oracle_monotonic_state_with_inv = prove
 (`!P n_f orac St f_inc f.
     P (FST (FST ((orac:num->(S#E)#P0) 0))) /\
     (!x. x IN St ==> x < n_f (FST (FST (orac 0)))) /\
     (!i st prog st' prog' st_ex.
        (f_inc:S->P0->S#Q) st prog = (st',prog') /\ P st /\ orac i = ((st,st_ex),prog)
        ==> P st' /\ n_f st <= n_f st' /\
            (!cfg x. x IN (f:E#Q->num->bool) (cfg,prog') ==> n_f st <= x /\ x < n_f st')) /\
     is_state_oracle f_inc orac
     ==> oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. P (FST (FST ((orac:num->(S#E)#P0) i))) /\
        n_f (FST (FST (orac i))) <= n_f (FST (FST (orac (SUC i)))) /\
        (!x. x IN (f:E#Q->num->bool) (state_co (f_inc:S->P0->S#Q) orac i)
             ==> n_f (FST (FST (orac i))) <= x /\ x < n_f (FST (FST (orac (SUC i)))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!i. P (FST (FST ((orac:num->(S#E)#P0) i))) ==>
          P (FST (FST (orac (SUC i)))) /\
          n_f (FST (FST (orac i))) <= n_f (FST (FST (orac (SUC i)))) /\
          (!x. x IN (f:E#Q->num->bool) (state_co (f_inc:S->P0->S#Q) orac i)
               ==> n_f (FST (FST (orac i))) <= x /\ x < n_f (FST (FST (orac (SUC i)))))`
     ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `FST (FST ((orac:num->(S#E)#P0) i))`;
        `SND ((orac:num->(S#E)#P0) i)`;
        `FST ((f_inc:S->P0->S#Q) (FST (FST ((orac:num->(S#E)#P0) i))) (SND (orac i)))`;
        `SND ((f_inc:S->P0->S#Q) (FST (FST ((orac:num->(S#E)#P0) i))) (SND (orac i)))`;
        `SND (FST ((orac:num->(S#E)#P0) i))`]) THEN
      ASM_REWRITE_TAC[PAIR] THEN
      FIRST_ASSUM(fun th -> if bkp1aux_mentions "is_state_oracle" th
        then REWRITE_TAC[REWRITE_RULE[is_state_oracle_def] th] else NO_TAC) THEN
      REWRITE_TAC[state_co_def; pair_CASE_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!i. P (FST (FST ((orac:num->(S#E)#P0) i)))` ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i <= j ==> n_f (FST (FST ((orac:num->(S#E)#P0) i))) <=
                                 n_f (FST (FST (orac j)))` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THEN
    ASM_MESON_TAC[LE_REFL; LE_TRANS];
    ALL_TAC] THEN
  REWRITE_TAC[oracle_monotonic_def] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `n_f (FST (FST ((orac:num->(S#E)#P0) (SUC i)))):num` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n_f (FST (FST ((orac:num->(S#E)#P0) j))):num` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_MESON_TAC[]];
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `n_f (FST (FST ((orac:num->(S#E)#P0) 0))):num` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n_f (FST (FST ((orac:num->(S#E)#P0) i))):num` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ASM_MESON_TAC[]]]);;

(* HOL4 line 1644 *)
let oracle_monotonic_bounded_state = prove
 (`!n_f St orac f.
     (!x. x IN St ==> x < n_f ((orac:num->A) 0)) /\
     (!i. n_f (orac i) <= n_f (orac (SUC i)) /\
          (!x. x IN f (orac i) ==> n_f (orac i) <= x /\ x < n_f (orac (SUC i))))
     ==> oracle_monotonic f (<) (St:num->bool) orac`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i j. i <= j ==> n_f ((orac:num->A) i) <= n_f (orac j)` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THEN
    ASM_MESON_TAC[LE_REFL; LE_TRANS];
    ALL_TAC] THEN
  REWRITE_TAC[oracle_monotonic_def] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `n_f ((orac:num->A) (SUC i)):num` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n_f ((orac:num->A) j):num` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_MESON_TAC[]];
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `n_f ((orac:num->A) 0):num` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n_f ((orac:num->A) i):num` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ASM_MESON_TAC[]]]);;

(* HOL4 line 1666 *)
let backendProof_compile_prog_avoids_nss_2 = prove
 (`!start f prog loc code new_state k.
     bvl_to_bvi_compile_prog start f prog = (loc,code,new_state) /\
   MEM k (MAP FST code) /\ k MOD bvl_to_bvi_namespaces = 2
   ==> k < bvl_num_stubs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    fst(dest_var(rhs(concl th))) = "code")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_APPEND; MEM_APPEND; bvl_to_bvi_stubs_def; MAP; MEM]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[AllocGlobal_location_eq; CopyGlobals_location_eq;
       InitGlobals_location_eq; ListLength_location_eq; FromListByte_location_eq;
       ToListByte_location_eq; SumListLength_location_eq; ConcatByte_location_eq]) THEN
    REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
                stack_num_stubs_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num`; `prog:(num#num#bvl_exp)list`;
                 `FST (bvl_to_bvi_compile_list f prog)`;
                 `SND (bvl_to_bvi_compile_list f prog)`] compile_list_code_labels_domain) THEN
  REWRITE_TAC[PAIR] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s:num->bool. (k:num) IN s` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try fst(dest_var(lhs(concl th))) = "k" with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(rator(rator(lhs(concl th))))) = "MOD" with Failure _ -> false)) THEN
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
  CONV_TAC NUM_REDUCE_CONV THENL
   [REWRITE_TAC[ARITH_RULE `72 + k * 4 = (18 + k) * 4 + 0`];
    REWRITE_TAC[ARITH_RULE `(72 + k * 4) + 1 = (18 + k) * 4 + 1`]] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1680 *)
let tailrec_compile_prog_MEM_not_nss_2 = prove
 (`!ys xs n1 n e do_it.
     bvi_tailrec_compile_prog do_it n xs = (n1,ys) /\ MEM e (MAP FST ys) /\
     n MOD bvl_to_bvi_namespaces = 2 /\ ~(e MOD bvl_to_bvi_namespaces = 2)
     ==> MEM e (MAP FST xs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    bvi_tailrecProof_compile_prog_MEM)) o check (bkp1aux_mentions "bvi_tailrec_compile_prog")) THEN
  DISCH_THEN(MP_TAC o SPEC `e:num`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(e MOD bvl_to_bvi_namespaces = 2)` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[BKP1AUX_ns_add]);;

(* HOL4 line 1692 *)
let tmc_compile_prog_MEM_not_nss_3 = prove
 (`!ys xs n1 n e do_it.
     bvi_tmc_compile_prog do_it n xs = (n1,ys) /\ MEM e (MAP FST ys) /\
     n MOD bvl_to_bvi_namespaces = 3 /\ ~(e MOD bvl_to_bvi_namespaces = 3)
     ==> MEM e (MAP FST xs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    bvi_tmcProof_compile_prog_MEM)) o check (bkp1aux_mentions "bvi_tmc_compile_prog")) THEN
  DISCH_THEN(MP_TAC o SPEC `e:num`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(e MOD bvl_to_bvi_namespaces = 3)` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[BKP1AUX_ns_add]);;

(* BKP1AUX: the next names after bvl_to_bvi_compile_inc_all, exactly *)
let BKP1AUX_compile_inc_all_nn_eq = prove
 (`!cc p.
     bvl_to_bvi_config_next_name2 (FST (bvl_to_bvi_compile_inc_all cc p)) =
     FST (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec cc)
            (bvl_to_bvi_config_next_name2 cc)
            (SND (bvl_to_bvi_compile_inc (bvl_to_bvi_config_next_name1 cc)
                    (SND (bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit cc)
                            (bvl_to_bvi_config_split_main_at_seq cc)
                            (bvl_to_bvi_config_exp_cut cc)
                            (bvl_to_bvi_config_inlines cc) p))))) /\
     bvl_to_bvi_config_next_name3 (FST (bvl_to_bvi_compile_inc_all cc p)) =
     FST (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc cc)
            (bvl_to_bvi_config_next_name3 cc)
            (SND (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec cc)
                    (bvl_to_bvi_config_next_name2 cc)
                    (SND (bvl_to_bvi_compile_inc (bvl_to_bvi_config_next_name1 cc)
                            (SND (bvl_inline_compile_inc
                                    (bvl_to_bvi_config_inline_size_limit cc)
                                    (bvl_to_bvi_config_split_main_at_seq cc)
                                    (bvl_to_bvi_config_exp_cut cc)
                                    (bvl_to_bvi_config_inlines cc) p)))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; (record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors; K_THM]);;

(* HOL4 line 1704 *)
let is_state_oracle_tailrec_cake_orac = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> is_state_oracle
         (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c)))
         (state_co bvl_to_bvi_compile_inc
            (state_co (bvl_inline_compile_inc
                         (bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c))
                         (bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c))
                         (bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c)))
               (cake_orac asm_conf c' syntax config_tuple2
                  (\ps. backend_progs_bvl_prog ps))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[state_co_eq_comp; o_ASSOC] THEN
  MATCH_MP_TAC is_state_oracle_cake_orac_comp THEN
  REPEAT GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`syntax:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  SPEC_TAC(`cake_configs (asm_conf:(A)asm_config) c' syntax i`,`C:backend_config`) THEN
  SPEC_TAC(`(syntax:num->(num#num)#(dec)list) i`,`q:(num#num)#(dec)list`) THEN
  X_GEN_TAC `q:(num#num)#(dec)list` THEN X_GEN_TAC `C:backend_config` THEN
  MP_TAC(ISPEC `q:(num#num)#(dec)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num#num` (X_CHOOSE_THEN `p:(dec)list` SUBST1_TAC)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `C:backend_config`; `e:num#num`; `p:(dec)list`]
       BKP1AUX_compile_inc_progs_confs)) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pair_CASE_def; o_THM; state_co_fun_def; config_tuple2_def; FST; SND] THEN
  ASM_REWRITE_TAC[BKP1AUX_compile_inc_all_nn_eq]);;

(* HOL4 line 1727 *)
let is_state_oracle_tmc_cake_orac = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> is_state_oracle
         (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c)))
         (state_co (bvi_tailrec_compile_prog
                      (bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c)))
            (state_co bvl_to_bvi_compile_inc
               (state_co (bvl_inline_compile_inc
                            (bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c))
                            (bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c))
                            (bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c)))
                  (cake_orac asm_conf c' syntax config_tuple2
                     (\ps. backend_progs_bvl_prog ps)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[state_co_eq_comp; o_ASSOC] THEN
  MATCH_MP_TAC is_state_oracle_cake_orac_comp THEN
  REPEAT GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPECL [`syntax:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP cake_orac_config_eqs) THEN
  SPEC_TAC(`cake_configs (asm_conf:(A)asm_config) c' syntax i`,`C:backend_config`) THEN
  SPEC_TAC(`(syntax:num->(num#num)#(dec)list) i`,`q:(num#num)#(dec)list`) THEN
  X_GEN_TAC `q:(num#num)#(dec)list` THEN X_GEN_TAC `C:backend_config` THEN
  MP_TAC(ISPEC `q:(num#num)#(dec)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num#num` (X_CHOOSE_THEN `p:(dec)list` SUBST1_TAC)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `C:backend_config`; `e:num#num`; `p:(dec)list`]
       BKP1AUX_compile_inc_progs_confs)) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pair_CASE_def; o_THM; state_co_fun_def; config_tuple2_def; FST; SND] THEN
  ASM_REWRITE_TAC[BKP1AUX_compile_inc_all_nn_eq]);;

(* HOL4 line 1752 *)
let inline_compile_inc_names = prove
 (`!l b i spt prog inlines prog3.
     bvl_inline_compile_inc l b i spt prog = (inlines,prog3)
   ==> MAP FST prog3 = MAP FST prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_inline_compile_inc_def; tick_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`l:num`; `spt:(num#bvl_exp)spt`; `prog:(num#num#bvl_exp)list`;
                 `[]:(num#num#bvl_exp)list`;
                 `FST (tick_inline_all l (spt:(num#bvl_exp)spt) prog [])`;
                 `SND (tick_inline_all l (spt:(num#bvl_exp)spt) prog [])`] tick_inline_all_names) THEN
  REWRITE_TAC[PAIR; REVERSE; MAP; APPEND; pair_CASE_def; PAIR_EQ] THEN
  DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[MAP_MAP_o] THEN
  SPEC_TAC(`SND (tick_inline_all l (spt:(num#bvl_exp)spt) prog [])`,`xs:(num#num#bvl_exp)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11; o_THM] THEN
  SPEC_TAC(`h:num#num#bvl_exp`,`h:num#num#bvl_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; bvl_inline_optimise_def; FST]);;

(* HOL4 line 1763 *)
let bvi_inline_state_co_MAP_FST = prove
 (`!co n.
     MAP FST (SND (state_co bvi_inline_compile_inc
                   (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) n)) =
   MAP FST (SND (co n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SND_state_co] THEN
  MATCH_MP_TAC compile_inc_MAP_FST THEN
  MAP_EVERY EXISTS_TAC [`FST (FST ((co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) n))`;
    `FST (bvi_inline_compile_inc (FST (FST ((co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list) n)))
                                  (SND (co n)))`] THEN
  REWRITE_TAC[PAIR]);;
let _ = cake_add_simps [bvi_inline_state_co_MAP_FST];;

(* HOL4 line 1773 *)
let oracle_monotonic_bvi_inline = prove
 (`!R init co.
     oracle_monotonic (set_of_list o MAP FST o SND) R init
     (state_co bvi_inline_compile_inc
        (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)) =
   oracle_monotonic (set_of_list o MAP FST o SND) R init co`,
  REWRITE_TAC[oracle_monotonic_def; o_THM; bvi_inline_state_co_MAP_FST]);;
let _ = cake_add_simps [oracle_monotonic_bvi_inline];;

(* HOL4 line 1783 *)
let oracle_monotonic_bvi_inline_inter = prove
 (`!s R init co.
     oracle_monotonic (\x. set_of_list (MAP FST (SND x)) INTER s) R init
     (state_co bvi_inline_compile_inc
        (co:num->((num#bvi_exp)spt#C)#(num#num#bvi_exp)list)) =
   oracle_monotonic (\x. set_of_list (MAP FST (SND x)) INTER s) R init co`,
  REWRITE_TAC[oracle_monotonic_def; bvi_inline_state_co_MAP_FST]);;
let _ = cake_add_simps [oracle_monotonic_bvi_inline_inter];;

(* HOL4 line 1791 *)
let oracle_monotonic_subset_inject = prove
 (`!g R R' init_set' init_set f' co' f co. (!x y. R ((g:A->B) x) (g y) ==> R' x y) /\
       IMAGE g init_set' SUBSET init_set /\
       (!n. IMAGE g ((f':C->A->bool) ((co':num->C) n)) SUBSET (f:D->B->bool) ((co:num->D) n))
       ==> oracle_monotonic f R init_set co
       ==> oracle_monotonic f' R' init_set' co'`,
  REWRITE_TAC[oracle_monotonic_def; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

(* HOL4 line 1801 *)
let oracle_monotonic_handle_init_component = prove
 (`!D f co R init_set. (!i x y. x IN D /\ y IN (f:A->B->bool) ((co:num->A) i) ==> R x y) /\
       oracle_monotonic f R (init_set DIFF D) co
       ==> oracle_monotonic f R init_set co`,
  REWRITE_TAC[oracle_monotonic_def; IN_DIFF] THEN MESON_TAC[]);;

(* HOL4 line 1810 *)
let oracle_monotonic_cake_orac_to_I = prove
 (`!f cfg_f p_f R init_st asm_conf c' syntax.
     oracle_monotonic (\(cfg,p). (f:B#D->E->bool) ((cfg_f:backend_config->B) cfg,
                                                 (p_f:(A)backend_progs->D) p)) R init_st
     (cake_orac (asm_conf:(A)asm_config) c' syntax I I)
   ==> oracle_monotonic f R init_st (cake_orac asm_conf c' syntax cfg_f p_f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oracle_monotonic_def; BKP1AUX_cake_orac_thm; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 1819 *)
let cake_orac_monotonic_bounded_state = prove
 (CASE_TERM
  `!n_f St c' asm_conf syntax f cfg_f p_f.
     (!x. x IN St ==> x < n_f c') /\
     (!i c2 ps.
        let c1 = cake_configs (asm_conf:(A)asm_config) c' syntax i in
        compile_inc_progs T asm_conf c1 (syntax i) = (c2,ps)
        ==> n_f c1 <= n_f c2 /\
            (!x. x IN (f:B#D->num->bool) ((cfg_f:backend_config->B) c1,
                                          (p_f:(A)backend_progs->D) ps)
                 ==> n_f c1 <= x /\ x < n_f c2))
     ==> oracle_monotonic f (<) (St:num->bool) (cake_orac asm_conf c' syntax cfg_f p_f)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MATCH_MP_TAC oracle_monotonic_cake_orac_to_I THEN
  MATCH_MP_TAC(ISPEC
    `(n_f:backend_config->num) o (FST:backend_config#(A)backend_progs->backend_config)`
    oracle_monotonic_bounded_state) THEN
  REWRITE_TAC[o_THM; BKP1AUX_cake_orac_thm; I_THM; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def] THEN
  REWRITE_TAC[GSYM cake_configs_def] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`;
    `FST (compile_inc_progs T (asm_conf:(A)asm_config) (cake_configs asm_conf c' syntax i)
            (syntax i))`;
    `SND (compile_inc_progs T (asm_conf:(A)asm_config) (cake_configs asm_conf c' syntax i)
            (syntax i))`]) THEN
  REWRITE_TAC[PAIR]);;

(* HOL4 line 1841 *)
let monotonic_DISJOINT_labels_lab = prove
 (`!asm_conf c prog b bm c' syntax i.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   oracle_monotonic (set_of_list o MAP Section_num o SND) (\x y. ~(x = y))
     (domain (lab_to_target_config_labels (backend_config_lab_conf c')))
     (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o config_tuple2)
        (\ps. backend_progs_lab_prog ps))
   ==> DISJOINT
         (domain (lab_to_target_config_labels
                    (backend_config_lab_conf (cake_configs asm_conf c' syntax i))))
         (set_of_list (MAP Section_num
                         (SND (cake_orac asm_conf c' syntax
                                 (SND o SND o SND o SND o SND o SND o config_tuple2)
                                 (\ps. backend_progs_lab_prog ps) i))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`syntax:num->(num#num)#(dec)list`; `i:num`] o
              MATCH_MP accum_lab_conf_labels) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[oracle_monotonic_def; o_THM] o
                check (bkp1aux_mentions "oracle_monotonic")) THEN
  REWRITE_TAC[DISJOINT; SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNION; IN_UNIONS;
              IN_SET_OF_LIST; MEM_MAP; MEM_COUNT_LIST; o_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if bkp1aux_mentions "domain" th && is_forall(concl th)
    then FIRST_X_ASSUM(MP_TAC o MATCH_MP th) else NO_TAC) THEN
  ASM_MESON_TAC[]);;

(* BKP1AUX: the section names of compile_no_stubs *)
let BKP1AUX_compile_no_stubs_names = prove
 (`!f jump (offs:A word#A word) sp (prog:(num#(A)stack_prog)list).
     MAP Section_num (compile_no_stubs f jump offs sp prog) = MAP FST prog`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_no_stubs_def; MAP_prog_to_section_Section_num; stack_names_compile_def] THEN
  REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; stack_alloc_prog_comp_def;
              stack_remove_prog_comp_def; stack_names_prog_comp_def; FST]);;

(* BKP1AUX: to_lab, to_stack and the lab_to_target configuration *)
let BKP1AUX_to_lab_lab_conf = prove
 (`!(asm_conf:(A)asm_config) c prog.
     backend_config_lab_conf (FST (SND (to_lab asm_conf c prog))) = backend_config_lab_conf c`,
  REWRITE_TAC[to_lab_def; to_stack_def; to_word_def; to_data_def; to_bvi_def; to_bvl_def;
              to_clos_def; to_flat_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  REWRITE_TAC[FST; SND; (record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM]);;

let BKP1AUX_to_lab_prog = prove
 (`!(asm_conf:(A)asm_config) c prog.
     ?scc dc mh sp off.
       FST (SND (SND (to_lab asm_conf c prog))) =
       stack_to_lab_compile scc dc mh sp off (FST (SND (SND (to_stack asm_conf c prog))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[to_lab_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN MESON_TAC[]);;

(* HOL4 line 1874 *)
let monotonic_labels_stack_to_lab = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (set_of_list o MAP FST o FST o SND) (\x y. ~(x = y))
         (set_of_list (MAP FST (FST (SND (SND (to_stack asm_conf c prog))))) UNION
          pred_set_count (SUC gc_stub_location))
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)))
   ==> oracle_monotonic (set_of_list o MAP Section_num o SND) (\x y. ~(x = y))
         (domain (lab_to_target_config_labels (backend_config_lab_conf c')))
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_lab_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC oracle_monotonic_subset THEN CONJ_TAC THENL
   [(FIRST_ASSUM(MP_TAC o MATCH_MP to_lab_labels_ok o CONJ
    (ASSUME `backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')`)) THEN
  FIRST_ASSUM(MP_TAC o check (bkp1aux_mentions "backend_compile")) THEN
  REWRITE_TAC[compile_eq_to_target; to_target_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds;
    (record_info "backend_config").ri_accessors; K_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BKP1AUX_lab_to_target_domain_labels o
    check (bkp1aux_mentions "lab_to_target_compile")) THEN
  ASM_SIMP_TAC[stack_labels_ok_FST_code_labels_Section_num; BKP1AUX_to_lab_lab_conf] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[backend_config_ok_def]) THEN ASM_REWRITE_TAC[]) THEN
    (DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[domain_def; UNION_EMPTY] THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`]
    BKP1AUX_to_lab_prog) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MAP_Section_num_stack_to_lab_SUBSET THEN SET_TAC[]);
    GEN_TAC THEN REWRITE_TAC[o_THM; BKP1AUX_cake_orac_thm; FST; SND] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_progs)) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BKP1AUX_compile_no_stubs_names; SUBSET_REFL]]);;

(* HOL4 line 1915 *)
let monotonic_labels_bvi_down_to_stack = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
         (set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION pred_set_count (SUC data_num_stubs))
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_bvi_prog ps))
   ==> oracle_monotonic (set_of_list o MAP FST o FST o SND) (\x y. ~(x = y))
         (set_of_list (MAP FST (FST (SND (SND (to_stack asm_conf c prog))))) UNION
          pred_set_count (SUC gc_stub_location))
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC oracle_monotonic_subset THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN REWRITE_TAC[o_THM; BKP1AUX_cake_orac_thm; FST; SND] THEN
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
               `FST ((syntax:num->(num#num)#(dec)list) n)`;
               `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_progs)) THEN
    REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (asl,w) ->
      let t = BKP1AUX_find_app "compile_word_to_stack" w in
      MP_TAC(MATCH_MP MAP_FST_compile_word_to_stack (SYM(ISPEC t PAIR)))) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BKP1AUX_MAP_FST_word_data; SUBSET_REFL]]) THEN
  (MP_TAC(MATCH_MP to_word_labels_ok (CONJ
    (ASSUME `backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')`)
    (ASSUME `backend_config_ok (asm_conf:(A)asm_config) c`))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[backend_config_ok_def] o
              check (bkp1aux_mentions "backend_config_ok")) THEN
  REWRITE_TAC[to_stack_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; BKP1AUX_to_word_stack_conf] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let t = BKP1AUX_find_app "word_to_stack_compile" w in
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (ISPECL [rand t; `asm_conf:(A)asm_config`] word_to_stack_compile_lab_pres))) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[to_word_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND] THEN
  W(fun (asl,w) ->
    let t = BKP1AUX_find_app "data_to_word_compile" w in
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (ISPECL (snd(strip_comb t)) data_to_word_compile_lab_pres))) THEN
  REWRITE_TAC[pair_CASE_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[to_data_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; bvi_to_dataProof_MAP_FST_compile_prog]) THEN
  (REWRITE_TAC[SUBSET; IN_UNION; IN_COUNT; IN_SET_OF_LIST; MEM; MEM_APPEND] THEN
  X_GEN_TAC `x:num` THEN
  MP_TAC(ISPECL [`x:num`; `(:A)`;
                 `backend_config_data_conf (FST (to_bvi c prog))`] MAP_FST_stubs_bound) THEN
  REWRITE_TAC[raise_stub_location_def; wl_store_consts_stub_location_def; word_num_stubs_def;
              stack_num_stubs_def; gc_stub_location_eq; data_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `MEM (x:num) (MAP FST (FST (SND (to_bvi c prog))))` THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`MEM (x:num) (MAP FST (data_to_word_stubs (:A)
              (backend_config_data_conf (FST (to_bvi c prog)))))`,`m:bool`) THEN
  GEN_TAC THEN BOOL_CASES_TAC `m:bool` THEN REWRITE_TAC[] THEN ARITH_TAC));;

(* BKP1AUX: residues modulo 4 *)
let BKP1AUX_MOD4 = prove
 (`!a k. (a + k * 4) MOD 4 = a MOD 4 /\ (a + 4 * k) MOD 4 = a MOD 4`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let BKP1AUX_bvl_num_stubs = prove
 (`bvl_num_stubs = 72 /\ bvl_to_bvi_namespaces = 4 /\ data_num_stubs = 62`,
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let BKP1AUX_DIV4 = prove
 (`!k. (k * 4) DIV 4 = k`,
  GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[DIV_MULT; ARITH_RULE `~(4 = 0)`]);;

(* BKP1AUX: the function names after bvl_to_bvi, by residue modulo 4 *)
let BKP1AUX_chain_classify = prove
 (`!start p1 code n1 loc dt n2 code2 dm n3 code3 x.
     bvl_to_bvi_compile_prog start 0 p1 = (loc,code,n1) /\
     bvi_tailrec_compile_prog dt (bvl_num_stubs + 2) code = (n2,code2) /\
     bvi_tmc_compile_prog dm (bvl_num_stubs + 3) code2 = (n3,code3) /\
     MEM x (MAP FST code3)
     ==> (x MOD bvl_to_bvi_namespaces = 0
          ==> x < bvl_num_stubs \/
              (bvl_num_stubs <= x /\
               MEM ((x - bvl_num_stubs) DIV bvl_to_bvi_namespaces) (MAP FST p1))) /\
         (x MOD bvl_to_bvi_namespaces = 1 ==> x < bvl_num_stubs + n1 * bvl_to_bvi_namespaces) /\
         (x MOD bvl_to_bvi_namespaces = 2 ==> x < n2) /\
         (x MOD bvl_to_bvi_namespaces = 3 ==> x < n3)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tailrecProof_compile_prog_next_mono o
              check (bkp1aux_mentions "bvi_tailrec_compile_prog")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_prog_next_mono o
              check (bkp1aux_mentions "bvi_tmc_compile_prog")) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    bvi_tmcProof_compile_prog_MEM)) o check (bkp1aux_mentions "bvi_tmc_compile_prog")) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`x:num`; `x:num`] (GEN `y:num` (GEN `x:num` (ISPECL
    [`start:num`; `0`; `p1:(num#num#bvl_exp)list`; `loc:num`;
     `code:(num#num#bvi_exp)list`; `n1:num`; `x:num`; `y:num`]
    compile_prog_code_labels_domain)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `\s:num->bool. x IN s`) THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_SET_OF_LIST; IN_ELIM_THM] THEN
  REWRITE_TAC[bvl_to_bvi_stubs_def; MAP; MEM; AllocGlobal_location_eq; CopyGlobals_location_eq;
       InitGlobals_location_eq; ListLength_location_eq; FromListByte_location_eq;
       ToListByte_location_eq; SumListLength_location_eq; ConcatByte_location_eq] THEN
  DISCH_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[BKP1AUX_bvl_num_stubs]) THEN REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  STRIP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[BKP1AUX_MOD4] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    bvi_tailrecProof_compile_prog_MEM)) o check (bkp1aux_mentions "bvi_tailrec_compile_prog")) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[BKP1AUX_MOD4] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_iff(concl th))) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[ARITH_RULE `(72 + k * 4) + 1 = 73 + k * 4`; BKP1AUX_MOD4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(72 + x * 4) - 72 = x * 4`; BKP1AUX_DIV4; LE_ADD] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> bkp1aux_mentions "MEM" th ||
    bkp1aux_mentions "bvl_to_bvi_compile_prog" th ||
    bkp1aux_mentions "bvi_tailrec_compile_prog" th ||
    bkp1aux_mentions "bvi_tmc_compile_prog" th))) THEN
  ASM_ARITH_TAC));;
(* BKP1AUX: bvi_inline_compile_prog keeps the names *)
let BKP1AUX_bvi_inline_prog_names = prove
 (`!p. MAP FST (SND (bvi_inline_compile_prog p)) = MAP FST p`,
  GEN_TAC THEN REWRITE_TAC[bvi_inline_compile_prog_def] THEN
  MATCH_MP_TAC compile_inc_MAP_FST THEN
  MAP_EVERY EXISTS_TAC [`LN:(num#bvi_exp)spt`;
                        `FST (bvi_inline_compile_inc LN (p:(num#num#bvi_exp)list))`] THEN
  REWRITE_TAC[PAIR]);;

let BKP1AUX_bvl_inline_prog_names = prove
 (`!l b i (prog:(num#num#bvl_exp)list).
     MAP FST (SND (bvl_inline_compile_prog l b i prog)) = MAP FST prog`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC compile_prog_names THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `b:bool`; `i:num`;
                        `FST (bvl_inline_compile_prog l b i (prog:(num#num#bvl_exp)list))`] THEN
  REWRITE_TAC[PAIR]);;

(* BKP1AUX: the function names of to_bvi by residue modulo 4 *)
let BKP1AUX_to_bvi_classify = prove
 (`!c prog x.
     MEM x (MAP FST (FST (SND (to_bvi c prog))))
     ==> (x MOD bvl_to_bvi_namespaces = 0
          ==> x < bvl_num_stubs \/
              (bvl_num_stubs <= x /\
               MEM ((x - bvl_num_stubs) DIV bvl_to_bvi_namespaces)
                   (MAP FST (FST (SND (to_bvl c prog)))))) /\
         (x MOD bvl_to_bvi_namespaces = 1
          ==> x < bvl_num_stubs + bvl_to_bvi_config_next_name1
                    (backend_config_bvl_conf (FST (to_bvi c prog))) * bvl_to_bvi_namespaces) /\
         (x MOD bvl_to_bvi_namespaces = 2
          ==> x < bvl_to_bvi_config_next_name2 (backend_config_bvl_conf (FST (to_bvi c prog)))) /\
         (x MOD bvl_to_bvi_namespaces = 3
          ==> x < bvl_to_bvi_config_next_name3 (backend_config_bvl_conf (FST (to_bvi c prog))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[to_bvi_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; (record_info "backend_config").ri_accfupds;
              (record_info "backend_config").ri_accessors; K_THM;
              (record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors] THEN
  SPEC_TAC(`to_bvl c prog`,`tb:backend_config#(num#num#bvl_exp)list#(mlstring)spt`) THEN
  GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_def] THEN
  REWRITE_TAC[pair_CASE_def] THEN REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[BKP1AUX_bvi_inline_prog_names] THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let tR = BKP1AUX_find_app "bvl_to_bvi_compile_prog" w in
    let tT = BKP1AUX_find_app "bvi_tailrec_compile_prog" w in
    let tM = BKP1AUX_find_app "bvi_tmc_compile_prog" w in
    MP_TAC(MATCH_MP BKP1AUX_chain_classify
      (CONJ (bkp1aux_tuple_eq tR) (CONJ (bkp1aux_tuple_eq tT)
        (CONJ (bkp1aux_tuple_eq tM) (ASSUME (hd (map concl (map snd asl))))))))) THEN
  REWRITE_TAC[BKP1AUX_bvl_inline_prog_names]);;
(* BKP1AUX: the function names after the incremental bvl_to_bvi passes *)
let BKP1AUX_inc_chain = prove
 (`!nn1 P1 nn1' P2 dt nn2 nn2' P3 dm nn3 nn3' P4 x.
     bvl_to_bvi_compile_inc nn1 P1 = (nn1',P2) /\
     bvi_tailrec_compile_prog dt nn2 P2 = (nn2',P3) /\
     bvi_tmc_compile_prog dm nn3 P3 = (nn3',P4) /\
     nn2 MOD bvl_to_bvi_namespaces = 2 /\ nn3 MOD bvl_to_bvi_namespaces = 3 /\
     MEM x (MAP FST P4)
     ==> (x MOD bvl_to_bvi_namespaces = 0
          ==> bvl_num_stubs <= x /\
              MEM ((x - bvl_num_stubs) DIV bvl_to_bvi_namespaces) (MAP FST P1)) /\
         (x MOD bvl_to_bvi_namespaces = 1
          ==> bvl_num_stubs + nn1 * bvl_to_bvi_namespaces <= x /\
              x < bvl_num_stubs + nn1' * bvl_to_bvi_namespaces) /\
         (x MOD bvl_to_bvi_namespaces = 2 ==> nn2 <= x /\ x < nn2') /\
         (x MOD bvl_to_bvi_namespaces = 3 ==> nn3 <= x /\ x < nn3')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    bvi_tmcProof_compile_prog_MEM)) o check (bkp1aux_mentions "bvi_tmc_compile_prog")) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `nn3 MOD bvl_to_bvi_namespaces = 3` THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[BKP1AUX_bvl_num_stubs; BKP1AUX_MOD4] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BKP1AUX_bvl_num_stubs]) THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    bvi_tailrecProof_compile_prog_MEM)) o check (bkp1aux_mentions "bvi_tailrec_compile_prog")) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN STRIP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `nn2 MOD bvl_to_bvi_namespaces = 2` THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[BKP1AUX_bvl_num_stubs; BKP1AUX_MOD4] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BKP1AUX_bvl_num_stubs]) THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL
    compile_inc_next_range)) o check (bkp1aux_mentions "bvl_to_bvi_compile_inc")) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;
let BKP1AUX_bvi_inline_inc_names = prove
 (`!cs p. MAP FST (SND (bvi_inline_compile_inc cs p)) = MAP FST p`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC compile_inc_MAP_FST THEN
  MAP_EVERY EXISTS_TAC [`cs:(num#bvi_exp)spt`;
                        `FST (bvi_inline_compile_inc cs (p:(num#num#bvi_exp)list))`] THEN
  REWRITE_TAC[PAIR]);;

(* BKP1AUX: the names after bvl_to_bvi_compile_inc_all, by residue modulo 4 *)
let BKP1AUX_inc_all_classify = prove
 (`!bc P x.
     bvl_to_bvi_config_next_name2 bc MOD bvl_to_bvi_namespaces = 2 /\
     bvl_to_bvi_config_next_name3 bc MOD bvl_to_bvi_namespaces = 3 /\
     MEM x (MAP FST (SND (bvl_to_bvi_compile_inc_all bc P)))
     ==> (x MOD bvl_to_bvi_namespaces = 0
          ==> bvl_num_stubs <= x /\
              MEM ((x - bvl_num_stubs) DIV bvl_to_bvi_namespaces) (MAP FST P)) /\
         (x MOD bvl_to_bvi_namespaces = 1
          ==> bvl_num_stubs + bvl_to_bvi_config_next_name1 bc * bvl_to_bvi_namespaces <= x /\
              x < bvl_num_stubs + bvl_to_bvi_config_next_name1
                    (FST (bvl_to_bvi_compile_inc_all bc P)) * bvl_to_bvi_namespaces) /\
         (x MOD bvl_to_bvi_namespaces = 2
          ==> bvl_to_bvi_config_next_name2 bc <= x /\
              x < bvl_to_bvi_config_next_name2 (FST (bvl_to_bvi_compile_inc_all bc P))) /\
         (x MOD bvl_to_bvi_namespaces = 3
          ==> bvl_to_bvi_config_next_name3 bc <= x /\
              x < bvl_to_bvi_config_next_name3 (FST (bvl_to_bvi_compile_inc_all bc P)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; (record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors; K_THM;
              BKP1AUX_bvi_inline_inc_names] THEN
  STRIP_TAC THEN
  W(fun (asl,w) ->
    let tR = BKP1AUX_find_app "bvl_to_bvi_compile_inc" w in
    let tT = BKP1AUX_find_app "bvi_tailrec_compile_prog" w in
    let tM = BKP1AUX_find_app "bvi_tmc_compile_prog" w in
    let mem = find (fun th -> bkp1aux_mentions "MEM" th) (map snd asl) in
    MP_TAC(MATCH_MP BKP1AUX_inc_chain
      (CONJ (bkp1aux_tuple_eq tR) (CONJ (bkp1aux_tuple_eq tT)
        (CONJ (bkp1aux_tuple_eq tM) (CONJ (ASSUME `bvl_to_bvi_config_next_name2 bc MOD
                                                    bvl_to_bvi_namespaces = 2`)
          (CONJ (ASSUME `bvl_to_bvi_config_next_name3 bc MOD bvl_to_bvi_namespaces = 3`)
                mem))))))) THEN
  W(fun (asl,w) ->
    let t = BKP1AUX_find_app "bvl_inline_compile_inc" w in
    REWRITE_TAC[MATCH_MP inline_compile_inc_names (bkp1aux_tuple_eq t)]));;
let BKP1AUX_nn_mods = prove
 (`!asm_conf c prog b bm c' syntax n.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> bvl_to_bvi_config_next_name2
           (backend_config_bvl_conf (cake_configs asm_conf c' syntax n))
           MOD bvl_to_bvi_namespaces = 2 /\
         bvl_to_bvi_config_next_name3
           (backend_config_bvl_conf (cake_configs asm_conf c' syntax n))
           MOD bvl_to_bvi_namespaces = 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn) THEN
  ASM_REWRITE_TAC[configs_nn2_MOD_namespaces; configs_nn3_MOD_namespaces; BKP1AUX_ns_add] THEN
  REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN CONV_TAC NUM_REDUCE_CONV);;

(* BKP1AUX: the names of the bvi programs of the oracle, by residue modulo 4 *)
let BKP1AUX_bvi_point_classify = prove
 (`!asm_conf c prog b bm c' syntax n x.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
     MEM x (MAP FST (SND (cake_orac asm_conf c' syntax
                            (SND o SND o SND o SND o SND o config_tuple2)
                            (\ps. backend_progs_bvi_prog ps) n)))
     ==> (x MOD bvl_to_bvi_namespaces = 0
          ==> bvl_num_stubs <= x /\
              MEM ((x - bvl_num_stubs) DIV bvl_to_bvi_namespaces)
                (MAP FST (SND (cake_orac asm_conf c' syntax config_tuple2
                                 (\ps. backend_progs_bvl_prog ps) n)))) /\
         (x MOD bvl_to_bvi_namespaces = 1
          ==> bvl_num_stubs + bvl_to_bvi_config_next_name1
                (backend_config_bvl_conf (cake_configs asm_conf c' syntax n)) *
                bvl_to_bvi_namespaces <= x /\
              x < bvl_num_stubs + bvl_to_bvi_config_next_name1
                (backend_config_bvl_conf (cake_configs asm_conf c' syntax (SUC n))) *
                bvl_to_bvi_namespaces) /\
         (x MOD bvl_to_bvi_namespaces = 2
          ==> bvl_to_bvi_config_next_name2
                (backend_config_bvl_conf (cake_configs asm_conf c' syntax n)) <= x /\
              x < bvl_to_bvi_config_next_name2
                (backend_config_bvl_conf (cake_configs asm_conf c' syntax (SUC n)))) /\
         (x MOD bvl_to_bvi_namespaces = 3
          ==> bvl_to_bvi_config_next_name3
                (backend_config_bvl_conf (cake_configs asm_conf c' syntax n)) <= x /\
              x < bvl_to_bvi_config_next_name3
                (backend_config_bvl_conf (cake_configs asm_conf c' syntax (SUC n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`syntax:num->(num#num)#(dec)list`; `n:num`] o
              MATCH_MP BKP1AUX_nn_mods) THEN
  UNDISCH_TAC `MEM (x:num) (MAP FST (SND (cake_orac (asm_conf:(A)asm_config) c' syntax
                            (SND o SND o SND o SND o SND o config_tuple2)
                            (\ps. backend_progs_bvi_prog ps) n)))` THEN
  REWRITE_TAC[BKP1AUX_cake_orac_thm; SND] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [cake_configs_def] THEN
  REWRITE_TAC[state_orac_states_def; GSYM cake_configs_def] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_progs)) THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_confs)) THEN
  REWRITE_TAC[PAIR] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> bkp1aux_mentions "MEM" th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC BKP1AUX_inc_all_classify THEN ASM_REWRITE_TAC[]);;
(* BKP1AUX: the bvl_to_bvi configuration that backend_compile returns *)
let BKP1AUX_bvl_conf_c' = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> backend_config_bvl_conf c' = backend_config_bvl_conf (FST (to_bvi c prog))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_eq_to_target; to_target_def; to_lab_def; to_stack_def; to_word_def;
              to_data_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds;
    (record_info "backend_config").ri_accessors; K_THM]);;

let BKP1AUX_cake_configs_SUC = prove
 (`!asm_conf c' syntax n.
     cake_configs (asm_conf:(A)asm_config) c' syntax (SUC n) =
     FST (compile_inc_progs T asm_conf (cake_configs asm_conf c' syntax n) (syntax n))`,
  REWRITE_TAC[cake_configs_def; state_orac_states_def]);;

(* BKP1AUX: the next names grow along the oracle *)
let BKP1AUX_nn_mono = prove
 (`!asm_conf c' syntax n.
     bvl_to_bvi_config_next_name1
       (backend_config_bvl_conf (cake_configs (asm_conf:(A)asm_config) c' syntax n)) <=
     bvl_to_bvi_config_next_name1
       (backend_config_bvl_conf (cake_configs asm_conf c' syntax (SUC n))) /\
     bvl_to_bvi_config_next_name2
       (backend_config_bvl_conf (cake_configs asm_conf c' syntax n)) <=
     bvl_to_bvi_config_next_name2
       (backend_config_bvl_conf (cake_configs asm_conf c' syntax (SUC n))) /\
     bvl_to_bvi_config_next_name3
       (backend_config_bvl_conf (cake_configs asm_conf c' syntax n)) <=
     bvl_to_bvi_config_next_name3
       (backend_config_bvl_conf (cake_configs asm_conf c' syntax (SUC n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BKP1AUX_cake_configs_SUC] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`asm_conf:(A)asm_config`; `cake_configs (asm_conf:(A)asm_config) c' syntax n`;
             `FST ((syntax:num->(num#num)#(dec)list) n)`;
             `SND ((syntax:num->(num#num)#(dec)list) n)`] BKP1AUX_compile_inc_progs_confs)) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BKP1AUX_compile_inc_all_nn_eq] THEN
  REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND; (record_info "bvl_to_bvi_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accessors; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [W(fun (asl,w) ->
      let t = BKP1AUX_find_app "bvl_to_bvi_compile_inc" w in
      ACCEPT_TAC(MATCH_MP compile_inc_next (bkp1aux_tuple_eq t)));
    W(fun (asl,w) ->
      let t = BKP1AUX_find_app "bvi_tailrec_compile_prog" w in
      let b,n,xs = match snd(strip_comb t) with [b;n;xs] -> b,n,xs | _ -> failwith "args" in
      MP_TAC(ISPECL [b;n;xs] BKP1AUX_tailrec_next)) THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_ADD];
    W(fun (asl,w) ->
      let t = BKP1AUX_find_app "bvi_tmc_compile_prog" w in
      let b,n,xs = match snd(strip_comb t) with [b;n;xs] -> b,n,xs | _ -> failwith "args" in
      MP_TAC(ISPECL [b;n;xs] BKP1AUX_tmc_next)) THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_ADD]]);;
let BKP1AUX_bvl_to_bvi_ns1 = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (\x. (set_of_list o MAP FST o SND) x INTER
                             PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {1}) (\x y. ~(x = y))
         ((set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION pred_set_count (SUC data_num_stubs))
          INTER PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {1})
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_bvi_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC oracle_monotonic_rel_mono THEN
  EXISTS_TAC `(<):num->num->bool` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC cake_orac_monotonic_bounded_state THEN
  EXISTS_TAC `\cfg. bvl_num_stubs + bvl_to_bvi_config_next_name1 (backend_config_bvl_conf cfg) *
                                    bvl_to_bvi_namespaces` THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [(REWRITE_TAC[IN_INTER; IN_PREIMAGE; IN_SING; IN_UNION; IN_COUNT; IN_SET_OF_LIST] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`c:backend_config`; `prog:(dec)list`; `x:num`] BKP1AUX_to_bvi_classify) THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP BKP1AUX_bvl_conf_c') THEN
    SIMP_TAC[];
    UNDISCH_TAC `x < SUC data_num_stubs` THEN REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN
    ARITH_TAC]);
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `FST:backend_config#(A)backend_progs->backend_config`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:backend_config#(A)backend_progs->(A)backend_progs`) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM BKP1AUX_cake_configs_SUC] THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_ADD_LCANCEL; LE_MULT_RCANCEL; BKP1AUX_nn_mono]; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_INTER; IN_PREIMAGE; IN_SING; o_THM; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
                `i:num`; `x:num`] BKP1AUX_bvi_point_classify) THEN
  ASM_REWRITE_TAC[BKP1AUX_cake_orac_thm; SND] THEN SIMP_TAC[])]);;

let BKP1AUX_bvl_to_bvi_ns2 = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (\x. (set_of_list o MAP FST o SND) x INTER
                             PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {2}) (\x y. ~(x = y))
         ((set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION pred_set_count (SUC data_num_stubs))
          INTER PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {2})
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_bvi_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC oracle_monotonic_rel_mono THEN
  EXISTS_TAC `(<):num->num->bool` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC cake_orac_monotonic_bounded_state THEN
  EXISTS_TAC `\cfg. bvl_to_bvi_config_next_name2 (backend_config_bvl_conf cfg)` THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [(REWRITE_TAC[IN_INTER; IN_PREIMAGE; IN_SING; IN_UNION; IN_COUNT; IN_SET_OF_LIST] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`c:backend_config`; `prog:(dec)list`; `x:num`] BKP1AUX_to_bvi_classify) THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP BKP1AUX_bvl_conf_c') THEN
    SIMP_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn o
      check (bkp1aux_mentions "backend_compile")) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x < SUC data_num_stubs` THEN REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN
    ARITH_TAC]);
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `FST:backend_config#(A)backend_progs->backend_config`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:backend_config#(A)backend_progs->(A)backend_progs`) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM BKP1AUX_cake_configs_SUC] THEN CONJ_TAC THENL
   [REWRITE_TAC[BKP1AUX_nn_mono]; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_INTER; IN_PREIMAGE; IN_SING; o_THM; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
                `i:num`; `x:num`] BKP1AUX_bvi_point_classify) THEN
  ASM_REWRITE_TAC[BKP1AUX_cake_orac_thm; SND] THEN SIMP_TAC[])]);;

let BKP1AUX_bvl_to_bvi_ns3 = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (\x. (set_of_list o MAP FST o SND) x INTER
                             PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {3}) (\x y. ~(x = y))
         ((set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION pred_set_count (SUC data_num_stubs))
          INTER PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {3})
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_bvi_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC oracle_monotonic_rel_mono THEN
  EXISTS_TAC `(<):num->num->bool` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC cake_orac_monotonic_bounded_state THEN
  EXISTS_TAC `\cfg. bvl_to_bvi_config_next_name3 (backend_config_bvl_conf cfg)` THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [(REWRITE_TAC[IN_INTER; IN_PREIMAGE; IN_SING; IN_UNION; IN_COUNT; IN_SET_OF_LIST] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`c:backend_config`; `prog:(dec)list`; `x:num`] BKP1AUX_to_bvi_classify) THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP BKP1AUX_bvl_conf_c') THEN
    SIMP_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BKP1AUX_backend_compile_nn o
      check (bkp1aux_mentions "backend_compile")) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x < SUC data_num_stubs` THEN REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN
    ARITH_TAC]);
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `FST:backend_config#(A)backend_progs->backend_config`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:backend_config#(A)backend_progs->(A)backend_progs`) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM BKP1AUX_cake_configs_SUC] THEN CONJ_TAC THENL
   [REWRITE_TAC[BKP1AUX_nn_mono]; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_INTER; IN_PREIMAGE; IN_SING; o_THM; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
                `i:num`; `x:num`] BKP1AUX_bvi_point_classify) THEN
  ASM_REWRITE_TAC[BKP1AUX_cake_orac_thm; SND] THEN SIMP_TAC[])]);;
let BKP1AUX_bvl_to_bvi_ns0 = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
     backend_config_ok asm_conf c /\
     oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
       (set_of_list (MAP FST (FST (SND (to_bvl c prog)))))
       (cake_orac asm_conf c' syntax config_tuple2 (\ps. backend_progs_bvl_prog ps))
   ==> oracle_monotonic (\x. (set_of_list o MAP FST o SND) x INTER
                             PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {0}) (\x y. ~(x = y))
         ((set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION pred_set_count (SUC data_num_stubs))
          INTER PREIMAGE (\i. i MOD bvl_to_bvi_namespaces) {0})
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_bvi_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[oracle_monotonic_def; o_THM; IN_SET_OF_LIST] o
                check (bkp1aux_mentions "oracle_monotonic")) THEN
  REWRITE_TAC[oracle_monotonic_def; o_THM; IN_INTER; IN_PREIMAGE; IN_SING; IN_SET_OF_LIST;
              IN_UNION; IN_COUNT] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`; `b:byte list`;
                  `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
                  `i:num`; `x:num`] BKP1AUX_bvi_point_classify) THEN
    MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`; `b:byte list`;
                  `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
                  `j:num`; `y:num`] BKP1AUX_bvi_point_classify) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`;
      `(x - bvl_num_stubs) DIV bvl_to_bvi_namespaces`;
      `(y - bvl_num_stubs) DIV bvl_to_bvi_namespaces`] o
      check (fun th -> is_forall(concl th) && bkp1aux_mentions "<" th)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x:num = y` THEN SIMP_TAC[];
    ALL_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:(dec)list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#(dec)list`;
                `i:num`; `y:num`] BKP1AUX_bvi_point_classify) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRY(UNDISCH_TAC `x < SUC data_num_stubs` THEN UNDISCH_TAC `bvl_num_stubs <= y` THEN
      REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN ARITH_TAC) THEN
  MP_TAC(SPECL [`c:backend_config`; `prog:(dec)list`; `x:num`] BKP1AUX_to_bvi_classify) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC `x < bvl_num_stubs` THEN UNDISCH_TAC `bvl_num_stubs <= y` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`;
      `(x - bvl_num_stubs) DIV bvl_to_bvi_namespaces`;
      `(y - bvl_num_stubs) DIV bvl_to_bvi_namespaces`] o
      check (fun th -> is_forall(concl th) && not (bkp1aux_mentions "<" th) &&
                       bkp1aux_mentions "to_bvl" th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4 line 1967 *)
let monotonic_labels_bvl_to_bvi = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
         (set_of_list (MAP FST (FST (SND (to_bvl c prog)))))
         (cake_orac asm_conf c' syntax config_tuple2 (\ps. backend_progs_bvl_prog ps))
   ==> oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
         (set_of_list (MAP FST (FST (SND (to_bvi c prog)))) UNION pred_set_count (SUC data_num_stubs))
         (cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_bvi_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `\i. i MOD bvl_to_bvi_namespaces` oracle_monotonic_slice) THEN
  X_GEN_TAC `z:num` THEN
  ASM_CASES_TAC `z = 0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BKP1AUX_bvl_to_bvi_ns0 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `z = 1` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BKP1AUX_bvl_to_bvi_ns1 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `z = 2` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BKP1AUX_bvl_to_bvi_ns2 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `z = 3` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BKP1AUX_bvl_to_bvi_ns3 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[oracle_monotonic_def; IN_INTER; IN_PREIMAGE; IN_SING] THEN
  SUBGOAL_THEN `!x. ~(x MOD bvl_to_bvi_namespaces = z)` (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN MP_TAC(SPECL [`x:num`; `bvl_to_bvi_namespaces`] MOD_LT_EQ) THEN
  REWRITE_TAC[BKP1AUX_bvl_num_stubs] THEN CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th -> bkp1aux_mentions "z" th ||
    can (find_term (fun t -> t = `z:num`)) (concl th))) THEN
  ARITH_TAC);;
