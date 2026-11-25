(* ========================================================================= *)
(* Word8ArrayProg: port of HOL4 basis/Word8ArrayProgScript.sml (CakeML      *)
(* v3479).  Module about the built-in byte-array type.                      *)
(* ========================================================================= *)

needs "basis/Word8Prog.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "Word8Prog";;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "byte_array") (Atapp [] (Short (implode "word8array")))` I);;

ml_prog_update (ml_prog_open_module "Word8Array");;

append_decs
  `[mlbasicsProg_mk_binop (implode "array") Aw8alloc;
    mlbasicsProg_mk_binop (implode "sub") Aw8sub;
    mlbasicsProg_mk_unop (implode "length") Aw8length;
    Dlet unknown_loc (Pvar (implode "update")) (Fun (implode "x") (Fun (implode "y") (Fun (implode "z")
      (App Aw8update [Var (Short (implode "x")); Var (Short (implode "y")); Var (Short (implode "z"))]))));
    Dlet unknown_loc (Pvar (implode "copy"))
      (Fun (implode "src") (Fun (implode "srcoff") (Fun (implode "len") (Fun (implode "dst") (Fun (implode "dstoff")
      (App CopyAw8Aw8 [Var (Short (implode "src")); Var (Short (implode "srcoff")); Var (Short (implode "len"));
                       Var (Short (implode "dst")); Var (Short (implode "dstoff"))]))))));
    Dlet unknown_loc (Pvar (implode "copyVec"))
      (Fun (implode "src") (Fun (implode "srcoff") (Fun (implode "len") (Fun (implode "dst") (Fun (implode "dstoff")
      (App CopyStrAw8 [Var (Short (implode "src")); Var (Short (implode "srcoff")); Var (Short (implode "len"));
                       Var (Short (implode "dst")); Var (Short (implode "dstoff"))]))))));
    Dlet unknown_loc (Pvar (implode "substring"))
      (Fun (implode "src") (Fun (implode "srcoff") (Fun (implode "len")
      (App CopyAw8Str [Var (Short (implode "src")); Var (Short (implode "srcoff")); Var (Short (implode "len"))]))))]`;;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (37,18) {|
  fun findi_aux f arr max n =
    if n = max
      then None
    else (if f (sub arr n)
        then Some (n, sub arr n)
      else findi_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (48,18) {|
  fun findi f arr =
    findi_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
