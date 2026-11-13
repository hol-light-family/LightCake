(* ========================================================================= *)
(* export_ag32: port of HOL4 compiler/backend/ag32/export_ag32Script.sml     *)
(* (CakeML v3479).  Define the format of the compiler-generated output file *)
(* for ag32.                                                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/export.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* Notation as in export.ml: the mlstring literal syntax is implode "...";  *)
(* word32 is int32.  The arguments exp, ret and pk are unused (type          *)
(* variables, as in HOL4).                                                   *)

let ag32_export_def = cake_def
  `ag32_export (ffi_names:mlstring list) bytes (data:int32 list)
      (syms:(mlstring#num#num) list) (exp:A) (ret:B) (pk:C) =
    SmartAppend
     (split16 (words_line (implode ".data_word ") word_to_string) data)
     (split16 (words_line (implode ".code_byte ") byte_to_string) bytes)`;;
