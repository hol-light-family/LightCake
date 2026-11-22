(* ========================================================================= *)
(* The headline statement of the Pancake compiler of the HOL Light port of   *)
(* CakeML v3479: HOL4 pancake/proofs/pan_to_targetProofScript.sml            *)
(*   pan_to_target_compile_semantics   (line 1257)                           *)
(* bound as the OCaml term pan_to_target_compile_semantics_statement.        *)
(* pan_to_targetProof.ml proves the theorem pan_to_target_compile_semantics  *)
(* and checks (failing loudly otherwise) that it has no hypotheses and that  *)
(* its conclusion is alpha-equivalent to the term here.                      *)
(*                                                                           *)
(* The statement is HOL4's, with its free variables quantified in the order *)
(* of their first occurrence; like HOL4's theorem it is polymorphic: HOL4's *)
(* 'a 'b 'c 'ffi are A B C FFI (A the machine word size, (A,B,C)            *)
(* machine_config the target machine, (A,FFI)pan_state the Pancake state,   *)
(* (FFI)ffi_state the state of the foreign function interface).             *)
(*                                                                           *)
(* Notions used, with the files of the port that define them (paths under   *)
(* src/):                                                                    *)
(*   decl, functions, size_of_eids, size_of_sh_with_ctxt, fun_decl and its   *)
(*     fields: pancake/panLang.ml                                            *)
(*   pan_state and its fields, semantics_decls, decs_stcnames, Word:         *)
(*     pancake/semantics/panSem.ml                                          *)
(*   dec_shapes: pancake/pan_globals.ml                                      *)
(*   pan_to_word_compile_prog: pancake/pan_to_word.ml                        *)
(*   distinct_params, globals_allocatable, good_panops:                      *)
(*     pancake/proofs/pan_to_wordProof.ml                                    *)
(*   wlab_wloc: pancake/proofs/crep_to_loopProof.ml                          *)
(*   word_to_word_compile: compiler/backend/word_to_word.ml                  *)
(*   word_to_stack_compile, word_to_stack_config_stack_frame_size:           *)
(*     compiler/backend/word_to_stack.ml                                     *)
(*   max_depth, full_call_graph: compiler/backend/word_depth.ml              *)
(*   InitGlobals_location: compiler/backend/bvl_to_bvi.ml                    *)
(*   from_stack, backend_config and its fields: compiler/backend/backend.ml  *)
(*   machine_config, machine_sem, good_init_state: compiler/backend/         *)
(*     semantics/targetSem.ml; target_config, target_get_reg,                *)
(*     target_get_pc: compiler/encoders/asm/asm.ml and targetSem.ml          *)
(*   extend_with_resource_limit': semantics/proofs/semanticsProps.ml         *)
(*   backend_config_ok, mc_init_ok, heap_regs, backendProof_read_limits:     *)
(*     compiler/backend/proofs/backendProof.ml                               *)
(*   mc_conf_ok: compiler/backend/proofs/lab_to_targetProof.ml               *)
(*   addresses: compiler/backend/proofs/stack_removeProof.ml;                *)
(*     max_stack_alloc: compiler/backend/stack_remove.ml                     *)
(*   max_heap_limit: compiler/backend/data_to_word.ml;                       *)
(*     backend_common_word_shift: compiler/backend/backend_common.ml          *)
(*   misc_word_list, word_list_exists, bytes_in_word: misc/misc.ml           *)
(*   pancake_good_code, pan_installed, compile_prog_max, option_lt: this file *)
(*     (definitions of pan_to_targetProof, see below)                        *)
(*                                                                           *)
(* The four definitions pancake_good_code_def, pan_installed_def,            *)
(* compile_prog_max_def and option_lt_def are pan_to_targetProof's (HOL4      *)
(* lines 22, 290, 1147 and 1157), placed here because the statement uses     *)
(* them; pan_to_targetProof.ml loads this file with needs and proves the    *)
(* theorem.                                                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "pancake/pan_to_target.ml";;
needs "pancake/proofs/pan_to_wordProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* pan_to_targetProof's definitions used by the statement *)

(* HOL4 line 22 *)
let pancake_good_code_def = cake_def
  `pancake_good_code (pan_code:((A)decl)list) <=> ALL good_panops pan_code`;;

(* HOL4 line 290 *)
let pan_installed_def = cake_def
  `pan_installed bytes cbspace (bitmaps:(A word)list) data_sp ffi_names (r1,r2)
                 (mc_conf:(A,B,C)machine_config) shmem_extra ms
                 (p_mem:A word->(A)word_loc) p_dom sdm' <=>
     ?t m bitmap_ptr bitmaps_dm sdm.
       let heap_stack_dm = {w | word_ule (asm_state_regs t r1) w /\
                                word_ult w (asm_state_regs t r2)} in
       (!a. a IN p_dom ==> m a = p_mem a) /\
       good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm UNION bitmaps_dm)
         sdm /\
       sdm' = sdm INTER byte_aligned /\
       byte_aligned (asm_state_regs t r1) /\
       byte_aligned (asm_state_regs t r2) /\
       byte_aligned bitmap_ptr /\
       word_ule (asm_state_regs t r1) (asm_state_regs t r2) /\
       word_ule (word_mul (word 1024) bytes_in_word)
         (word_sub (asm_state_regs t r2) (asm_state_regs t r1)) /\
       DISJOINT heap_stack_dm bitmaps_dm /\
       m (asm_state_regs t r1) = wl_Word bitmap_ptr /\
       m (word_add (asm_state_regs t r1) bytes_in_word) =
         wl_Word (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       m (word_add (asm_state_regs t r1) (word_mul (word 2) bytes_in_word)) =
         wl_Word (word_add (word_add bitmap_ptr (word_mul bytes_in_word (word data_sp)))
                   (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       m (word_add (asm_state_regs t r1) (word_mul (word 3) bytes_in_word)) =
         wl_Word (word_add (target_get_pc (machine_config_target mc_conf) ms)
                   (word (LENGTH bytes))) /\
       m (word_add (asm_state_regs t r1) (word_mul (word 4) bytes_in_word)) =
         wl_Word (word_add (word_add (target_get_pc (machine_config_target mc_conf) ms)
                              (word cbspace))
                   (word (LENGTH bytes))) /\
       (misc_word_list bitmap_ptr (MAP wl_Word bitmaps) STAR
        word_list_exists
          (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) data_sp)
         (fun2set (m,byte_aligned INTER bitmaps_dm)) /\
       ffi_names = SOME (machine_config_ffi_names mc_conf) /\
       (!i. mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i ==>
            MAP (\rec. val (target_get_pc (machine_config_target mc_conf) ms) +
                       shmem_info_num_entry_pc rec) shmem_extra =
            DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
            machine_config_mmio_info mc_conf =
            ZIP (list_of_seq (\index. index + i) (LENGTH shmem_extra))
                (MAP (\rec. (shmem_info_num_nbytes rec,
                             Addr (shmem_info_num_addr_reg rec)
                                  (word (shmem_info_num_addr_off rec)),
                             shmem_info_num_reg rec,
                             word_add (word (shmem_info_num_exit_pc rec))
                               (target_get_pc (machine_config_target mc_conf) ms)))
                     shmem_extra) /\
            (cbspace + LENGTH bytes) + ffi_offset * (i + 3) < dimword(:A))`;;

(* HOL4 line 1147 *)
let compile_prog_max_def = cake_def
  `compile_prog_max (c:backend_config) (mc:(A,B,C)machine_config) (prog:((A)decl)list) =
     let asm_conf = target_config (machine_config_target mc) in
     let prog = pan_to_word_compile_prog (asm_config_ISA asm_conf) prog in
     let (col,wprog) =
       word_to_word_compile (backend_config_word_to_word_conf c) asm_conf prog in
     let (bm,c',fs,p) = word_to_stack_compile asm_conf F wprog in
     let max = max_depth (word_to_stack_config_stack_frame_size c')
                 (full_call_graph InitGlobals_location (fromAList wprog)) in
       (from_stack asm_conf c LN p bm,max)`;;

(* HOL4 line 1157 [simp] *)
let option_lt_def = cake_def
  `(option_lt (n0:num option) NONE <=> T) /\
   (option_lt NONE (SOME n1) <=> F) /\
   (option_lt (SOME n1) (SOME n2) <=> n1 < n2:num)`;;

let _ = cake_add_simps [option_lt_def];;

(* HOL4 pan_to_target_compile_semantics (pan_to_targetProofScript.sml line 1257) *)
let pan_to_target_compile_semantics_statement =
  `!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) bytes
    (bitmaps:(A word)list) (c':backend_config) stack_max (s:(A,FFI)pan_state) ms
    globals_size heap_len adj_ptr2 adj_ptr4 (ffi:(FFI)ffi_state) cbspace data_sp start.
     compile_prog_max c mc pan_code = (SOME (bytes,bitmaps,c'),stack_max) /\
     pancake_good_code pan_code /\
     distinct_params (functions pan_code) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = FEMPTY /\
     pan_state_locals s = FEMPTY /\
     pan_state_globals s = FEMPTY /\
     size_of_eids pan_code < dimword (:A) /\
     pan_state_eshapes s = FEMPTY /\
     backend_config_ok (target_config (machine_config_target mc)) c /\ mc_conf_ok mc /\
     mc_init_ok (target_config (machine_config_target mc)) c mc /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     word_ult (word 0)
       (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc)) /\
     globals_size = (let dec_shs = dec_shapes pan_code in
                     let struct_ctxt = decs_stcnames [] pan_code in
                     SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) /\
     word_ult (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc))
              (target_get_reg (machine_config_target mc) ms (machine_config_ptr2_reg mc)) /\
     target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc) =
       pan_state_base_addr s /\
     globals_allocatable s pan_code /\
     heap_len =
       val (word_add (target_get_reg (machine_config_target mc) ms (machine_config_ptr2_reg mc))
                     (word_mul (word_neg (word 1)) (pan_state_base_addr s))) DIV
       (dimindex (:A) DIV 8) /\
     pan_state_top_addr s =
       word_sub (word_add (pan_state_base_addr s) (word_mul bytes_in_word (word heap_len)))
                (word ((globals_size * dimindex (:A)) DIV 8)) /\
     globals_size <= heap_len /\
     pan_state_memaddrs s =
       addresses (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc))
                 (heap_len - globals_size) /\
     alignment_aligned (backend_common_word_shift (:A) + 1)
       (word_add (target_get_reg (machine_config_target mc) ms (machine_config_ptr2_reg mc))
                 (word_mul (word_neg (word 1))
                    (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc)))) /\
     adj_ptr2 =
       word_add (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc))
                (word_mul bytes_in_word (word max_stack_alloc)) /\
     adj_ptr4 =
       word_sub (target_get_reg (machine_config_target mc) ms (machine_config_len2_reg mc))
                (word_mul bytes_in_word (word max_stack_alloc)) /\
     word_ule adj_ptr2
       (target_get_reg (machine_config_target mc) ms (machine_config_ptr2_reg mc)) /\
     word_ule (target_get_reg (machine_config_target mc) ms (machine_config_ptr2_reg mc))
       adj_ptr4 /\
     val (word_add (target_get_reg (machine_config_target mc) ms (machine_config_ptr2_reg mc))
                   (word_mul (word_neg (word 1))
                      (target_get_reg (machine_config_target mc) ms
                                      (machine_config_len_reg mc)))) <=
       val (bytes_in_word:A word) *
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1) /\
     val (bytes_in_word:A word) *
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1) < dimword (:A) /\
     pan_state_ffi s = ffi /\
     (asm_config_big_endian (target_config (machine_config_target mc)) <=> pan_state_be s) /\
     OPTION_ALL (ALL (\x. ?s. x = ExtCall s))
       (lab_to_target_config_ffi_names (backend_config_lab_conf c)) /\
     pan_installed bytes cbspace bitmaps data_sp
       (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
       (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf c))) mc
       (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
       (wlab_wloc o pan_state_memory s)
       (pan_state_memaddrs s) (pan_state_sh_memaddrs s) /\
     start = implode "main" /\
     ~(semantics_decls s start pan_code = Fail)
     ==> machine_sem mc ffi ms SUBSET
         extend_with_resource_limit'
           (option_lt stack_max
              (SOME (FST (backendProof_read_limits (target_config (machine_config_target mc))
                                                 c mc ms))))
           {semantics_decls s start pan_code}`;;
