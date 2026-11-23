(* ========================================================================= *)
(* The headline statements of the HOL Light port of CakeML v3479: the       *)
(* end-to-end correctness theorems of the compiler, HOL4                    *)
(* compiler/proofs/compilerProofScript.sml                                   *)
(*   compile_correct                  (line 264)                             *)
(*   compile_correct_safe_for_space   (line 232)                             *)
(* bound as the OCaml terms compile_correct_statement and                    *)
(* compile_correct_safe_for_space_statement.  compilerProof.ml proves the    *)
(* theorems compilerProof_compile_correct and compile_correct_safe_for_space *)
(* and checks (failing loudly otherwise) that each has no hypotheses and     *)
(* that its conclusion is alpha-equivalent to the term here.                 *)
(*                                                                           *)
(* The statements are HOL4's: the same quantifiers (in the same order),     *)
(* types and case analysis (match, with HOL4's semantics: an unmatched      *)
(* value, here M_failure (StaticError _), which compile never returns,      *)
(* gives ARB, as HOL4's case does).  Like HOL4's theorems they are          *)
(* polymorphic: HOL4's type variables 'a 'b 'c 'ffi are A B C FFI           *)
(* ((A)compiler_config is HOL4's 'a compiler$config, A the machine word     *)
(* size, (A,B,C)machine_config the target machine, (FFI)ffi_state the state *)
(* of the foreign function interface), and they stay free in the theorems. *)
(*                                                                           *)
(* Notions used, with the files of the port that define them (paths under   *)
(* src/):                                                                    *)
(*   compiler_compile, compiler_config (fields asm_config, backend_config,   *)
(*     inferencer_config, input_is_sexp, exclude_prelude,                    *)
(*     skip_type_inference, only_print_types, only_print_sexp), the errors   *)
(*     ParseError TypeError AssembleError ConfigError StaticError:           *)
(*     compiler/compiler.ml (the argument type staterr of StaticError:       *)
(*     pancake/panStatic.ml)                                                 *)
(*   M_success, M_failure: translator/monadic/monad_base/ml_monadBase.ml    *)
(*   semantics_init, parse, Execute, CannotParse, IllTyped:                  *)
(*     semantics/semantics.ml                                                *)
(*   lexer_fun: semantics/lexer_fun.ml                                       *)
(*   installed, machine_sem: compiler/backend/semantics/targetSem.ml         *)
(*   extend_with_resource_limit, extend_with_resource_limit':                *)
(*     semantics/proofs/semanticsProps.ml                                    *)
(*   backend_config (fields stack_conf, lab_conf, ...):                      *)
(*     compiler/backend/backend.ml; stack_to_lab_config_reg_names:           *)
(*     compiler/backend/stack_to_lab.ml; lab_to_target_config_ffi_names,    *)
(*     lab_to_target_config_shmem_extra: compiler/backend/lab_to_target.ml  *)
(*   heap_regs, backend_config_ok, mc_init_ok, backendProof_read_limits,     *)
(*     backendProof_is_safe_for_space: compiler/backend/proofs/              *)
(*     backendProof.ml                                                       *)
(*   mc_conf_ok: compiler/backend/proofs/lab_to_targetProof.ml               *)
(*   config_ok, compilerProof_read_limits, compilerProof_is_safe_for_space:  *)
(*     this file (definitions of compilerProof, see below)                   *)
(* and below them (the cone of config_ok): envRel_env_rel                    *)
(*   (compiler/inference/proofs/envRel.ml), inf_set_tids_ienv                *)
(*   (compiler/inference/inferProps.ml), prim_tenv, prim_type_ids           *)
(*   (semantics/primTypes.ml); the definitions of backendProof and          *)
(*   lab_to_targetProof above.                                               *)
(*                                                                           *)
(* The three definitions config_ok_def, compilerProof_read_limits_def and   *)
(* compilerProof_is_safe_for_space_def are compilerProof's (HOL4             *)
(* compilerProofScript.sml lines 15-103, at HOL4 lines 15, 97 and 101),     *)
(* placed here because the statements use them; compilerProof.ml loads     *)
(* this file with needs and proves the theorems.                             *)
(* ========================================================================= *)

needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "semantics/semantics.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/proofs/envRel.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/compiler.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/backendProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* compilerProof's definitions used by the statements *)

(* HOL4 line 15 *)
let config_ok_def = cake_def
  `config_ok (cc:(A)compiler_config) (mc:(A,B,C)machine_config) <=>
     envRel_env_rel prim_tenv (compiler_config_inferencer_config cc) /\
     inf_set_tids_ienv prim_type_ids (compiler_config_inferencer_config cc) /\
     ~compiler_config_input_is_sexp cc /\
     ~compiler_config_exclude_prelude cc /\
     ~compiler_config_skip_type_inference cc /\
     ~compiler_config_only_print_types cc /\
     ~compiler_config_only_print_sexp cc /\
     backend_config_ok (compiler_config_asm_config cc) (compiler_config_backend_config cc) /\
     mc_conf_ok mc /\
     mc_init_ok (compiler_config_asm_config cc) (compiler_config_backend_config cc) mc`;;

(* HOL4 line 97 *)
let compilerProof_read_limits_def = cake_def
  `compilerProof_read_limits (cc:(A)compiler_config) (mc:(A,B,C)machine_config) ms =
     backendProof_read_limits (compiler_config_asm_config cc)
       (compiler_config_backend_config cc) mc ms`;;

(* HOL4 line 101 *)
let compilerProof_is_safe_for_space_def = cake_def
  `compilerProof_is_safe_for_space (ffi:(FFI)ffi_state) (cc:(A)compiler_config) =
     backendProof_is_safe_for_space ffi (compiler_config_asm_config cc)
       (compiler_config_backend_config cc)`;;

(* HOL4 compile_correct (compilerProofScript.sml line 264) *)
let compile_correct_statement = CASE_TERM
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
                         extend_with_resource_limit behaviours)`;;

(* HOL4 compile_correct_safe_for_space (compilerProofScript.sml line 232) *)
let compile_correct_safe_for_space_statement =
  `!(ffi:(FFI)ffi_state) prelude input (cc:(A)compiler_config)
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
                ==> machine_sem mc ffi ms = behaviours`;;
