(* ========================================================================= *)
(* The headline statement of the ag32 unit of the HOL Light port of CakeML  *)
(* v3479: HOL4 ag32_compile_correct (compiler/backend/ag32/proofs/           *)
(* ag32_configProofScript.sml), the correctness theorem of the backend       *)
(* (backendProof's compile_correct) instantiated for the ag32 ("Silver")     *)
(* target: asm_conf := ag32_config, c := ag32_backend_config, and a machine  *)
(* configuration mc with is_ag32_machine_config mc.                          *)
(* Bound as the OCaml term ag32_compile_correct_statement.                   *)
(* ag32_configProof.ml proves ag32_compile_correct and checks (failing       *)
(* loudly otherwise) that it has no hypotheses and that its conclusion is    *)
(* alpha-equivalent to the term here.                                        *)
(*                                                                           *)
(* The statement is HOL4's, as HOL4's derivation leaves it: compile_correct  *)
(* (free variables asm_conf c prog bytes bitmaps c' ffi mc cbspace data_sp  *)
(* ms) with asm_conf, c and mc instantiated, the hypotheses                  *)
(* backend_config_ok ag32_config ag32_backend_config, mc_conf_ok mc and      *)
(* mc_init_ok ag32_config ag32_backend_config mc discharged (by              *)
(* ag32_backend_config_ok, and by ag32_machine_config_ok and ag32_init_ok    *)
(* under is_ag32_machine_config mc), heap_regs of the register names of      *)
(* ag32_backend_config evaluated to (2,4), and is_ag32_machine_config mc     *)
(* discharged in front.  HOL4's let (s,env) = THE (prim_sem_env ffi) in .. *)
(* is the case expression of the port (as in backendProof); HOL4's free     *)
(* variables are universally quantified, in the order of their first        *)
(* occurrence.  The type of mc is HOL4's: words of 32 bits, the ag32 state, *)
(* and the projection type of ag32_proj; FFI is HOL4's 'ffi and stays a     *)
(* type variable.                                                            *)
(*                                                                           *)
(* Notions used, with the files of the port that define them (paths under   *)
(* src/):                                                                    *)
(*   is_ag32_machine_config: compiler/backend/ag32/proofs/ag32_configProof.ml *)
(*     (defined here, see below)                                             *)
(*   ag32_config, ag32_target: compiler/encoders/ag32/ag32_target.ml        *)
(*   ag32_state: compiler/encoders/ag32/ag32.ml                              *)
(*   ag32_backend_config: compiler/backend/ag32/ag32_config.ml              *)
(*   backend_compile, backend_config_lab_conf: compiler/backend/backend.ml  *)
(*   lab_to_target_config_ffi_names, lab_to_target_config_shmem_extra:      *)
(*     compiler/backend/lab_to_target.ml                                     *)
(*   prim_sem_env: semantics/primSemEnv.ml; semantics_prog, Fail:            *)
(*     semantics/semantics.ml                                                *)
(*   installed, machine_sem, machine_config fields:                          *)
(*     compiler/backend/semantics/targetSem.ml                               *)
(*   extend_with_resource_limit: semantics/proofs/semanticsProps.ml         *)
(* The definition is_ag32_machine_config_def is the configProof's (HOL4     *)
(* line 11), placed here because the statement uses it; ag32_configProof.ml *)
(* loads this file with needs and proves the theorem.                       *)
(* ========================================================================= *)

needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/encoders/ag32/ag32_target.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 line 11 *)
let is_ag32_machine_config_def = cake_def
  `is_ag32_machine_config
     (mc:(32,ag32_state,int32#((6)word->int32)#(int32#byte->bool)#bool#bool)machine_config) <=>
     machine_config_target mc = ag32_target /\
     machine_config_ptr_reg mc = 1 /\
     machine_config_len_reg mc = 2 /\
     machine_config_ptr2_reg mc = 3 /\
     machine_config_len2_reg mc = 4 /\
     machine_config_callee_saved_regs mc = [60; 61; 62]`;;

(* HOL4 ag32_compile_correct (ag32_configProofScript.sml line 81) *)
let ag32_compile_correct_statement = CASE_TERM
  `!(mc:(32,ag32_state,int32#((6)word->int32)#(int32#byte->bool)#bool#bool)machine_config)
    prog bytes bitmaps c' (ffi:(FFI)ffi_state) cbspace data_sp ms.
     is_ag32_machine_config mc
     ==> backend_compile ag32_config ag32_backend_config prog = SOME (bytes,bitmaps,c')
     ==> let (s,env) = THE (prim_sem_env ffi) in
         ~semantics_prog s env prog Fail /\
         installed bytes cbspace bitmaps data_sp
           (lab_to_target_config_ffi_names (backend_config_lab_conf c')) (2,4) mc
           (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
         ==> machine_sem mc ffi ms SUBSET
             extend_with_resource_limit (semantics_prog s env prog)`;;
