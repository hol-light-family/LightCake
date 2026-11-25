(* ========================================================================= *)
(* CommandLineProg: port of HOL4 basis/CommandLineProgScript.sml (CakeML    *)
(* v3479).  A module about command-line arguments for the CakeML standard   *)
(* basis library.  The CakeML text of the Quote add_cakeml blocks is HOL4's, *)
(* verbatim, at HOL4's source positions (add_cakeml_at).                      *)
(* HOL4's option_monadsyntax.temp_add_option_monadsyntax is HOL4             *)
(* parser syntax (no counterpart; nothing here uses it).                     *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;
needs "basis/HashtableProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "HashtableProg";;

ml_prog_update (ml_prog_open_module "CommandLine");;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (19,18) {|
  fun read16bit a =
    let
      val w0 = Word8Array.sub a 0
      val w1 = Word8Array.sub a 1
    in Word8.toInt w0 + (Word8.toInt w1 * 256) end
|};;

add_cakeml_at (27,18) {|
  fun write16bit a i =
    (Word8Array.update a 0 (Word8.fromInt i);
     Word8Array.update a 1 (Word8.fromInt (i div 256)))
|};;

add_cakeml_at (33,18) {|
  fun cloop a n acc =
    if n = 0 then acc else
      let
        val n = n - 1
        val u = write16bit a n
        val u = #(get_arg_length) "" a
        val l = read16bit a
        val tmp = Word8Array.array (max 2 l) (Word8.fromInt 0)
        val u = write16bit tmp n
        val u = #(get_arg) "" tmp
        val arg = Word8Array.substring tmp 0 l
      in cloop a n (arg :: acc) end
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (50,18) {|
  fun cline u =
    case u of () => (* in order to make type unit -> ... *)
    let
      val a = Word8Array.array 2 (Word8.fromInt 0)
      val u = #(get_arg_count) "" a
      val n = read16bit a
    in cloop a n [] end
|};;

add_cakeml_at (60,18) {|
  fun name u = List.hd (cline u)
|};;

add_cakeml_at (64,18) {|
  fun arguments u = List.tl (cline u)
|};;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
