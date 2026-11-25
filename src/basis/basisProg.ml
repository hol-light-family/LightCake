(* ========================================================================= *)
(* basisProg: port of HOL4 basis/basisProgScript.sml (CakeML v3479), the     *)
(* code part.  Contains the code for the entire CakeML basis library in      *)
(* basisProg_basis_def (HOL4 basis_def; basis is HOL Light's constant of the *)
(* vector bases), with basis_Decls_thm.  HOL4's EVAL of the evaluation of    *)
(* TextIO.print is ml_progLib's lookup conversion and the evaluation lemma   *)
(* BAS1AUX_VAR_evaluate.  The CakeML text of the Quote add_cakeml blocks is  *)
(* HOL4's, verbatim, at HOL4's source positions (add_cakeml_at).  OPEN      *)
(* (M10, decision D2): the CF specifications                                 *)
(* print_app_list_aux_spec, print_app_list_spec, print_int_spec,             *)
(* print_pp_spec.                                                            *)
(* ========================================================================= *)

needs "translator/std_prelude.ml";;
needs "basis/PrettyPrinterProg.ml";;
needs "basis/SexpProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "SexpProg";;

let BAS1AUX_VAR_evaluate = prove
 (`!(env:v sem_env) (s:(FFI)state) id v.
     nsLookup (sem_env_v env) id = SOME v ==> eval_rel s env (Var id) s v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN
  MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s:(FFI)state)`] THEN
  FS[evaluate_def; state_component_equality]);;

let print_e = `Var (Long (implode "TextIO") (Short (implode "print")))`;;

let eval_thm =
  let env = ml_prog_get_env (get_ml_prog_state ())
  and state = ml_prog_get_state (get_ml_prog_state ()) in
  let lookup = ml_prog_lookup_eq_conv (mk_nsLookup_v (env, rand print_e)) in
  MATCH_MP (ISPECL [env; state; rand print_e; rand (rhs (concl lookup))]
              BAS1AUX_VAR_evaluate) lookup;;

ml_prog_update (ml_prog_add_Dlet eval_thm "print");;

ml_prog_update ml_prog_open_local_block;;

use_full_type_names := false;;
let _ = translate sum_sizes_def;;
let _ = translate make_app_list_ann_def;;
let _ = translate shrink_def;;
next_ml_names := ["str_app_list_opt"];;
let _ = translate str_app_list_opt_def;;
use_full_type_names := true;;

add_cakeml_at (37,18) {|
  fun print_app_list_aux ls =
    (case ls of
       Nil => ()
     | List ls => TextIO.print_list ls
     | Append l1 l2 => (print_app_list_aux l1; print_app_list_aux l2))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (47,18) {|
  fun print_app_list ls = print_app_list_aux (str_app_list_opt ls)
|};;

ml_prog_update ml_prog_close_local_blocks;;

(* print_app_list_aux_spec, print_app_list_spec: CF, basisProg_part2.ml (M10) *)

add_cakeml_at (96,18) {|
  fun print_int i = TextIO.print (Int.toString i)
|};;

(* print_int_spec: CF (M10) *)

add_cakeml_at (111,18) {|
  fun print_pp pp = print_app_list (PrettyPrinter.toAppList pp)
|};;

(* print_pp_spec: CF (M10) *)

(* The basis program has some 600000 term nodes: the printer elides it    *)
(* (the user printer basisProg_basis_prog), so that the bindings below do   *)
(* not print it                                                             *)
let basisProg_elided = ref ([] : term list);;
install_user_printer ("basisProg_basis_prog", fun fmt tm ->
  if exists (fun t -> t == tm || t = tm) !basisProg_elided
  then pp_print_string fmt "<the basis program>" else failwith "elide");;

let basis_st = ml_prog_remove_snocs (get_ml_prog_state ());;

let basis_prog =
  let p = ml_prog_get_prog basis_st in basisProg_elided := [p]; p;;

let basisProg_basis_def = new_definition
  (mk_eq (mk_var ("basisProg_basis", type_of basis_prog), basis_prog));;

(* HOL4: REWRITE_RULE [GSYM basis_def]; rewriting with the large program  *)
(* as the pattern overflows the stack: the program argument of Decls is     *)
(* replaced by the constant directly                                        *)
let basis_Decls_thm =
  CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV (K (SYM basisProg_basis_def)))))
    (ml_prog_get_Decls_thm basis_st);;

finalise_translation ();;
