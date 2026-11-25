(* ========================================================================= *)
(* candle_kernelProg: port of HOL4 candle/prover/candle_kernelProgScript.sml *)
(* (CakeML v3479).  Adds Candle specific functions to the kernel module from *)
(* ml_hol_kernel_funsProg, closes the module and extracts the program:       *)
(*   candle_prog_thm |- Decls ml_init_env (ml_init_state ffi) candle_code    *)
(*                       candle_init_env (candle_init_state ffi)            *)
(* (HOL4 init_env and init_state are ml_init_env and ml_init_state).         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Decision D5 (user, 2026-11-24): the compute functions that HOL4         *)
(*   translates from the PMATCH restatements of compute_pmatch (dest_num,    *)
(*   dest_numeral, dest_numeral_opt, dest_binary) are translated from their  *)
(*   compute_eval definitions (nested one-level Mats where HOL4 has one Mat  *)
(*   with nested patterns).                                                  *)
(* - The CakeML text of the print_thm declaration is HOL4's, verbatim.       *)
(* - HOL4's EVAL in candle_prog_thm normalises the program, the environment  *)
(*   and the state: here ml_progLib's remove_snocs gives the program as a   *)
(*   literal list (checked) and ML_PROG_EVAL_CONV evaluates the environment  *)
(*   and the state (HOL4's EVAL with ml_progLib's compset); the program is  *)
(*   abbreviated without rewriting with it (the term is large: as for        *)
(*   basisProg's basis_Decls_thm).                                           *)
(* - Local helpers that are not HOL4 theorems are CAN1AUX_.                  *)
(* ========================================================================= *)

needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/prover/compute/compute.ml";;
needs "candle/standard/ml_kernel/print_thm.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/standard/ml_kernel/runtime_checkLib.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

(* HOL4 m_translation_extends: the monadic state is part of the snapshot *)
translation_extends "ml_hol_kernel_funsProg";;

use_long_names := false;;

ml_prog_update ml_prog_open_local_block;;

let _ = translate ty_to_v_def;;
let _ = translate term_to_v_def;;
let _ = translate thm_to_v_def;;
let _ = translate update_to_v_def;;
let _ = translate thm_to_string_def;;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml {|
  val print_thm = fn th => case th of Sequent tms c =>
    let
      val ctxt = !the_context
      val str = thm_to_string ctxt th
      val arr = Word8Array.array 0 (Word8.fromInt 0)
    in
      #(kernel_ffi) str arr
    end;
|};;

(* compute primitive *)

ml_prog_update ml_prog_open_local_block;;

(* D5: HOL4 translates compute_pmatch's dest_num_PMATCH, dest_numeral_PMATCH *)
(* and dest_numeral_opt_PMATCH                                               *)
let _ = translate compute_dest_num_def;;
let _ = m_translate compute_dest_numeral_def;;
let _ = translate compute_dest_numeral_opt_def;;
let _ = translate list_dest_comb_def;;
let _ = translate compute_mapOption_def;;
let _ = translate app_type_def;;
let _ = translate compute_dest_cexp_def;;

(* HOL4 [local] *)
let dest_cexp_side = prove
 (`!x. dest_cexp_side x`,
  MATCH_MP_TAC compute_dest_cexp_ind THEN RW[] THEN
  ONCE_REWRITE_TAC[tr_fetch "dest_cexp_side_def"] THEN RW[] THEN
  RFS[MAP; NOT_CONS_NIL]);;

let _ = update_precondition dest_cexp_side;;

let _ = m_translate compute_option_def;;
let _ = m_translate compute_check_def;;
let _ = translate SAFEMOD_def;;
let _ = translate SAFEDIV_def;;
let _ = translate num2bit_def;;
let _ = translate cv2term_def;;

(* HOL4 compute_thms_def |> EVAL_RULE: the equations (===), typeof and   *)
(* codomain evaluated to constructor terms                                  *)
let _ = translate
  (PURE_REWRITE_RULE [equation_def; typeof_def; codomain_def] compute_thms_def);;

(* D5: HOL4 translates compute_pmatch's dest_binary_PMATCH *)
let _ = m_translate compute_dest_binary_def;;

let _ = translate (runtime_check_check ["ths"] compute_init_def);;

let _ = m_translate check_var_def;;

use_mem_intro := true;;
let _ = translate_no_ind check_cexp_closed_def;;

(* HOL4 [local] *)
let candle_check_cexp_closed_ind = prove
 (`check_cexp_closed_ind`,
  REWRITE_TAC[find (fun th -> try fst (dest_const (lhs (concl th))) = "check_cexp_closed_ind"
                              with Failure _ -> false) (definitions ())] THEN
  REPEAT GEN_TAC THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC (latest_ind ()) THEN REPEAT STRIP_TAC THEN
  LAST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  RFS[FORALL_PAIR_THM; GSYM MEMBER_INTRO]);;

let _ = update_precondition candle_check_cexp_closed_ind;;
use_mem_intro := false;;

let _ = translate var_list_def;;

let _ = translate const_list_def;;
let _ = m_translate compute_map_def;;

use_mem_intro := true;;
let _ = m_translate check_consts_def;;
let _ = m_translate check_eqn_def;;
use_mem_intro := false;;

let _ = translate compute_default_clock;;
let _ = translate findi_def;;
let _ = translate compute_monop_fst_def;;
let _ = translate compute_monop_snd_def;;
let _ = translate compute_monop_ispair_def;;
let _ = translate compute_monop_def;;
let _ = translate to_num_def;;
let _ = translate cv_T_def;;
let _ = translate cv_F_def;;
let _ = translate compute_binop_add_def;;
let _ = translate (REWRITE_RULE [GSYM sub_check_def] compute_binop_sub_def);;
let _ = translate compute_binop_mul_def;;
let _ = translate compute_binop_div_def;;
let _ = translate compute_binop_mod_def;;
let _ = translate compute_binop_eq_def;;
let _ = translate compute_binop_less_def;;
let _ = translate compute_binop_def;;
let _ = translate to_ce_def;;
let _ = translate compile_to_ce_def;;
let _ = translate build_funs_def;;
let _ = translate env_lookup_def;;

let _ = m_translate get_code_def;;
let _ = m_translate exec_def;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = m_translate (runtime_check_check ["ths"; "tm"] compute_add_def);;
(* HOL4 SIMP_RULE (srw_ss()) [combinTheory.C_DEF]: C is vocab.ml's flip *)
let _ = m_translate
  (runtime_check_check ["ths"; "ceqs"; "tm"]
     (PURE_REWRITE_RULE [flip_DEF] compute_compute_def));;

ml_prog_update ml_prog_close_local_blocks;;
ml_prog_update (ml_prog_close_module None);;

(* extract the interesting theorem *)

(* HOL4 define_abbrev_conv name tm: |- tm = name vars (the abbreviation is *)
(* added to ml_progLib's compset, HOL4's for_eval)                          *)
let CAN1AUX_define_abbrev_conv name tm =
  let def = ml_prog_define_abbrev true name tm in
  SPEC_ALL (GSYM def);;

(* The program has some 600000 term nodes: the printer elides it (the user *)
(* printer candle_code_prog), so that the bindings below do not print it    *)
let can1aux_elided = ref ([] : term list);;
install_user_printer ("candle_code_prog", fun fmt tm ->
  if exists (fun t -> t == tm) !can1aux_elided
  then pp_print_string fmt "<the candle program>" else failwith "elide");;

let candle_prog_thm =
  let s = ml_prog_remove_snocs (get_ml_prog_state ()) in
  let th = ml_prog_get_Decls_thm s in
  let th = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                        (CAN1AUX_define_abbrev_conv "candle_code")) th in
  let th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                        (ML_PROG_EVAL_CONV THENC
                         CAN1AUX_define_abbrev_conv "candle_init_env")) th in
  CONV_RULE (RAND_CONV
               (ML_PROG_EVAL_CONV THENC
                CAN1AUX_define_abbrev_conv "candle_init_state")) th;;

let candle_code_def =
  let th = ml_prog_fetch "candle_code_def" in
  can1aux_elided := [rhs (concl th)]; th;;

(* HOL4's EVAL leaves a literal program: ml_progLib's remove_snocs gives    *)
(* literal declaration lists at every level; check it (no SNOC or APPEND,   *)
(* no free variables)                                                        *)
let () =
  let p = rhs (concl candle_code_def) in
  let bad t = is_const t && mem (fst (dest_const t)) ["SNOC"; "APPEND"] in
  if can (find_term bad) p || frees p <> []
  then failwith "candle_code is not a closed literal program" else ();;
let candle_init_env_def = ml_prog_fetch "candle_init_env_def";;
let candle_init_state_def = ml_prog_fetch "candle_init_state_def";;

(* extract some other other theorems *)

let EqualityType_TYPE_TYPE = EqualityType_rule [] `:hol_type`;;

let EqualityType_TERM_TYPE = EqualityType_rule [] `:hol_term`;;

let EqualityType_THM_TYPE = EqualityType_rule [] `:thm`;;

let EqualityType_UPDATE_TYPE = EqualityType_rule [] `:update`;;

finalise_translation ();;

(* ------------------------------------------------------------------------- *)
(* The generated theorems that HOL4 saves in the theory, under their HOL4    *)
(* names (doc/reserved_generated.tsv), for the Candle proofs                 *)
(* ------------------------------------------------------------------------- *)

(* can1aux_fetch: ml_hol_kernel_funsProg.ml *)

(* the definition of the induction goal left by translate_no_ind *)
let check_cexp_closed_ind_def =
  find (fun th -> try fst (dest_const (lhs (concl th))) = "check_cexp_closed_ind"
                  with Failure _ -> false) (definitions ());;
let compute_default_clock_refs_def = can1aux_fetch "compute_default_clock_refs_def";;
let compute_thms_refs_def = can1aux_fetch "compute_thms_refs_def";;
let cv_f_refs_def = can1aux_fetch "cv_f_refs_def";;
let cv_t_refs_def = can1aux_fetch "cv_t_refs_def";;
let dest_cexp_side_def = can1aux_fetch "dest_cexp_side_def";;
let candle_Kernel_print_thm_v_def = can1aux_fetch "Kernel_print_thm_v_def";;
let app_type_v_def = can1aux_fetch "app_type_v_def";;
let binop_add_v_def = can1aux_fetch "binop_add_v_def";;
let binop_div_v_def = can1aux_fetch "binop_div_v_def";;
let binop_eq_v_def = can1aux_fetch "binop_eq_v_def";;
let binop_less_v_def = can1aux_fetch "binop_less_v_def";;
let binop_mod_v_def = can1aux_fetch "binop_mod_v_def";;
let binop_mul_v_def = can1aux_fetch "binop_mul_v_def";;
let binop_sub_v_def = can1aux_fetch "binop_sub_v_def";;
let binop_v_def = can1aux_fetch "binop_v_def";;
let build_funs_v_def = can1aux_fetch "build_funs_v_def";;
let check_cexp_closed_v_def = can1aux_fetch "check_cexp_closed_v_def";;
let check_consts_v_def = can1aux_fetch "check_consts_v_def";;
let check_eqn_v_def = can1aux_fetch "check_eqn_v_def";;
let check_v_def = can1aux_fetch "check_v_def";;
let check_var_v_def = can1aux_fetch "check_var_v_def";;
let compile_to_ce_v_def = can1aux_fetch "compile_to_ce_v_def";;
let compute_add_v_def = can1aux_fetch "compute_add_v_def";;
let compute_init_v_def = can1aux_fetch "compute_init_v_def";;
let compute_v_def = can1aux_fetch "compute_v_def";;
let const_list_v_def = can1aux_fetch "const_list_v_def";;
let cv2term_v_def = can1aux_fetch "cv2term_v_def";;
let dest_binary_v_def = can1aux_fetch "dest_binary_v_def";;
let dest_cexp_v_def = can1aux_fetch "dest_cexp_v_def";;
let dest_num_v_def = can1aux_fetch "dest_num_v_def";;
let dest_numeral_opt_v_def = can1aux_fetch "dest_numeral_opt_v_def";;
let dest_numeral_v_def = can1aux_fetch "dest_numeral_v_def";;
let env_lookup_v_def = can1aux_fetch "env_lookup_v_def";;
let exec_v_def = can1aux_fetch "exec_v_def";;
let findi_1_v_def = can1aux_fetch "findi_1_v_def";;
let get_code_v_def = can1aux_fetch "get_code_v_def";;
let list_dest_comb_v_def = can1aux_fetch "list_dest_comb_v_def";;
let map_2_v_def = can1aux_fetch "map_2_v_def";;
let mapoption_v_def = can1aux_fetch "mapoption_v_def";;
let monop_fst_v_def = can1aux_fetch "monop_fst_v_def";;
let monop_ispair_v_def = can1aux_fetch "monop_ispair_v_def";;
let monop_snd_v_def = can1aux_fetch "monop_snd_v_def";;
let monop_v_def = can1aux_fetch "monop_v_def";;
let num2bit_v_def = can1aux_fetch "num2bit_v_def";;
let option_v_def = can1aux_fetch "option_v_def";;
let safediv_v_def = can1aux_fetch "safediv_v_def";;
let safemod_v_def = can1aux_fetch "safemod_v_def";;
let term_to_v_v_def = can1aux_fetch "term_to_v_v_def";;
let thm_to_string_v_def = can1aux_fetch "thm_to_string_v_def";;
let thm_to_v_v_def = can1aux_fetch "thm_to_v_v_def";;
let to_ce_v_def = can1aux_fetch "to_ce_v_def";;
let to_num_v_def = can1aux_fetch "to_num_v_def";;
let ty_to_v_v_def = can1aux_fetch "ty_to_v_v_def";;
let update_to_v_v_def = can1aux_fetch "update_to_v_v_def";;
let var_list_v_def = can1aux_fetch "var_list_v_def";;
let compute_add_v_thm = can1aux_fetch "compute_add_v_thm";;
let compute_default_clock_v_thm = can1aux_fetch "compute_default_clock_v_thm";;
let compute_thms_v_thm = can1aux_fetch "compute_thms_v_thm";;
let compute_v_thm = can1aux_fetch "compute_v_thm";;
let cv_f_v_thm = can1aux_fetch "cv_f_v_thm";;
let cv_t_v_thm = can1aux_fetch "cv_t_v_thm";;
let thm_to_string_v_thm = can1aux_fetch "thm_to_string_v_thm";;
