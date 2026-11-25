(* ========================================================================= *)
(* RuntimeProg: port of HOL4 basis/RuntimeProgScript.sml (CakeML v3479).     *)
(* Module that contains a few special functions, e.g. a function for         *)
(* forcing a full GC to run, a function for producing debug output.          *)
(* ========================================================================= *)

needs "characteristic/cfDiv.ml";;
needs "basis/pure/mloption.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "cfDiv";;

ml_prog_update (ml_prog_open_module "Runtime");;

(* HOL4: fullGC *)
let RuntimeProg_fullGC_def = new_definition
  `RuntimeProg_fullGC (u:1) = force_unit_type u (force_gc_to_run (&0) (&0))`;;

next_ml_names := ["fullGC"];;
let _ = translate RuntimeProg_fullGC_def;;

(* HOL4: fail *)
let RuntimeProg_fail_def = new_definition
  `RuntimeProg_fail (u:1) = force_unit_type u (force_out_of_memory_error u)`;;

next_ml_names := ["fail"];;
let _ = translate RuntimeProg_fail_def;;

(* HOL4: debugMsg *)
let RuntimeProg_debugMsg_def = new_definition
  `RuntimeProg_debugMsg s = empty_ffi s`;;

next_ml_names := ["debugMsg"];;
let _ = translate RuntimeProg_debugMsg_def;;

let RuntimeProg_exit =
  `[Dletrec unknown_loc
     [(implode "exit", implode "i",
       Let (SOME (implode "y")) (App (FromTo IntT (WordT W8)) [Var (Short (implode "i"))])
         (Let (SOME (implode "x")) (App Aw8alloc [Lit (IntLit (&1));
                                                  Var (Short (implode "y"))])
              (App (FFI (implode "exit")) [Lit (StrLit (implode ""));
                                           Var (Short (implode "x"))])))]]`;;

append_prog RuntimeProg_exit;;

add_cakeml_at (46,18) {|
  fun abort u = case u of () => exit 1
|};;

add_cakeml_at (50,18) {|
  fun assert cond msg =
    if cond
    then ()
    else (debugMsg msg;
          abort());
|};;

add_cakeml_at (58,18) {|
  fun customFFI str_arg arr_arg = #(custom) str_arg arr_arg;
|};;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
