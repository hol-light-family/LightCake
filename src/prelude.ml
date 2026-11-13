(* ========================================================================= *)
(* Prelude of the CakeML port: the load path, the HOL Light libraries, and   *)
(* the proof kit.  Every file of the port can then be loaded with needs.     *)
(* ========================================================================= *)

let cakeml_src_dir = Filename.concat (Sys.getcwd()) "src";;

if not (mem cakeml_src_dir (!load_path))
then load_path := cakeml_src_dir :: (!load_path);;

needs "Library/words.ml";;
needs "Library/rstc.ml";;
needs "Library/iter.ml";;

prioritize_num();;

type_invention_error := true;;

needs "kit/kit.ml";;
