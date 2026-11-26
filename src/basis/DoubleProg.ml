(* ========================================================================= *)
(* DoubleProg: port of HOL4 basis/DoubleProgScript.sml (CakeML v3479), the   *)
(* code part.  Module for the built-in double floating-point type.  Defines *)
(* basic arithmetic operations like +,-,*,/, and FMA, logical operations    *)
(* <, <=, >, >=, and = and to-/fromString functions for parsing and         *)
(* pretty-printing constants.                                                *)
(*                                                                           *)
(* HOL4's float records are hol4/binary_ieee.ml's: x.Sign = float_Sign x,   *)
(* <| Sign := s; Exponent := e; Significand := m |> = float_REC s e m.       *)
(* Word operations as in Word64Prog.ml (w2w = word_zx, >>> = word_ushr,     *)
(* << = word_shl, && = word_and, || = word_or, right associative as HOL4's). *)
(* HOL4's EVAL of the                                                        *)
(* allocation of the byte array is the evaluation lemma                      *)
(* BAS1AUX_W8ALLOC_evaluate; the EVALs of fp64_to_float 1w and 0w are        *)
(* WORD_REDUCE_CONV.                                                          *)
(* OPEN (M10, decision D2): the lemmas significand_correct',                 *)
(* exponent_correct', sign_correct, sign_correct', w2w'_11, w2w'_52,         *)
(* w2w'_01, w2w_range_11/52/01, construct_correct, construct_correct',       *)
(* flt_max_correct, word_addR_concat, fp64_word_concat_assoc,               *)
(* next_hi_fnext_hi, next_lo_fnext_lo, maxulp_correct, ABS_REFL',            *)
(* abs_sub_lemma and ffloat_ulp_correct (no code depends on them).           *)
(* significand_correct and exponent_correct are proved here: the translated *)
(* float_is_finite_characterisation and float_is_zero_characterisation need  *)
(* them.                                                                     *)
(* ========================================================================= *)

needs "hol4/words4.ml";;
needs "hol4/binary_ieee.ml";;
needs "hol4/machine_ieee.ml";;
needs "basis/CommandLineProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "CommandLineProg";;

(* Double module -- translated *)

ml_prog_update (ml_prog_open_module "Double");;

(* HOL4 generate_sigs := true: no signatures (see ListProg.ml) *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "double") (Atapp [] (Short (implode "double")))` I);;

ml_prog_update ml_prog_open_local_block;;

(* ------------------------------------------------------------------------- *)
(* Byte array for the FFI communication                                      *)
(* ------------------------------------------------------------------------- *)

let BAS1AUX_W8ALLOC_evaluate = prove
 (`!(env:v sem_env) (s:(FFI)state) n w.
     eval_rel s env (App Aw8alloc [Lit (IntLit (&n)); Lit (Word8 w)])
       (state_refs_fupd (combin_K (APPEND (state_refs s) [W8array (REPLICATE n w)])) s)
       (Loc T (LENGTH (state_refs s)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eval_rel_def] THEN SIMP[] THEN
  MAP_EVERY EXISTS_TAC [`state_clock (s:(FFI)state)`; `state_clock (s:(FFI)state)`] THEN
  FS[evaluate_def; REVERSE; APPEND; getOpClass_def; do_app_def; store_alloc_def; LT;
     list_result_def; state_component_equality; INT_ARITH `~(&n:int < &0)`;
     NUM_OF_INT_OF_NUM]);;

let bytes_eval_thm =
  let env = ml_prog_get_env (get_ml_prog_state ())
  and st = ml_prog_get_state (get_ml_prog_state ()) in
  let th = ISPECL [env; st; `256`; `word 0:byte`] BAS1AUX_W8ALLOC_evaluate in
  let len = rand (rand (concl th)) in
  let len_eq = (ML_PROG_EVAL_CONV THENC REWRITE_CONV [LENGTH_APPEND; LENGTH] THENC
                NUM_REDUCE_CONV) len in
  let th = CONV_RULE (RAND_CONV (RAND_CONV (K len_eq))) th in
  let v_def = ml_prog_define_abbrev false "bytes_loc" (rand (concl th)) in
  PURE_REWRITE_RULE [GSYM v_def] th;;

ml_prog_update (ml_prog_add_Dlet bytes_eval_thm "bytes");;

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

let byte_0_def = new_definition
  `byte_0 (d:int64) = (word_zx d):byte`;;
let byte_1_def = new_definition
  `byte_1 (d:int64) = (word_zx (word_ushr d 8)):byte`;;
let byte_2_def = new_definition
  `byte_2 (d:int64) = (word_zx (word_ushr d 16)):byte`;;
let byte_3_def = new_definition
  `byte_3 (d:int64) = (word_zx (word_ushr d 24)):byte`;;
let byte_4_def = new_definition
  `byte_4 (d:int64) = (word_zx (word_ushr d 32)):byte`;;
let byte_5_def = new_definition
  `byte_5 (d:int64) = (word_zx (word_ushr d 40)):byte`;;
let byte_6_def = new_definition
  `byte_6 (d:int64) = (word_zx (word_ushr d 48)):byte`;;
let byte_7_def = new_definition
  `byte_7 (d:int64) = (word_zx (word_ushr d 56)):byte`;;

let _ = translate byte_0_def;;
let _ = translate byte_1_def;;
let _ = translate byte_2_def;;
let _ = translate byte_3_def;;
let _ = translate byte_4_def;;
let _ = translate byte_5_def;;
let _ = translate byte_6_def;;
let _ = translate byte_7_def;;

let is_0_byte_def = new_definition
  `is_0_byte (c:byte) <=> c = word 0`;;

let _ = translate is_0_byte_def;;

add_cakeml_at (102,18) {|
  fun read_bytes offset =
    let
      val a = Word8Array.sub bytes offset;
      val b = Word8Array.sub bytes (offset + 1);
      val c = Word8Array.sub bytes (offset + 2);
      val d = Word8Array.sub bytes (offset + 3);
      val e = Word8Array.sub bytes (offset + 4);
      val f = Word8Array.sub bytes (offset + 5);
      val g = Word8Array.sub bytes (offset + 6);
      val h = Word8Array.sub bytes (offset + 7);
    in
      Word64.concatAll a b c d e f g h
    end
|};;

add_cakeml_at (118,18) {|
  fun write_bytes offset d =
    let
      val _ = Word8Array.update bytes offset (byte_0 d);
      val _ = Word8Array.update bytes (offset + 1) (byte_1 d);
      val _ = Word8Array.update bytes (offset + 2) (byte_2 d);
      val _ = Word8Array.update bytes (offset + 3) (byte_3 d);
      val _ = Word8Array.update bytes (offset + 4) (byte_4 d);
      val _ = Word8Array.update bytes (offset + 5) (byte_5 d);
      val _ = Word8Array.update bytes (offset + 6) (byte_6 d);
      val _ = Word8Array.update bytes (offset + 7) (byte_7 d);
    in
      ()
    end
|};;

let prepareString_def = new_definition
  `prepareString (s:mlstring) = translate (\c. if c = CHR 126 then CHR 45 else c) s`;;
let _ = translate prepareString_def;;

ml_prog_update ml_prog_open_local_in_block;;

append_prog
  `[Dlet unknown_loc (Pvar (implode "fromWord"))
     (Fun (implode "x") (App (FromTo (WordT W64) Float64T) [Var (Short (implode "x"))]))]`;;

append_prog
  `[Dlet unknown_loc (Pvar (implode "toWord"))
     (Fun (implode "x") (App (FromTo Float64T (WordT W64)) [Var (Short (implode "x"))]))]`;;

(* ------------------------------------------------------------------------- *)
(* Functions that use the FFI                                                *)
(* ------------------------------------------------------------------------- *)

(* 0: Double.fromString *)
add_cakeml_at (154,18) {|
  fun fromString s =
    let
      val _ = #(double_fromString) (preparestring s) bytes;
      val err = Word8Array.sub bytes 0
    in
      if err = Word8.fromInt 0 then
        Some (fromWord (read_bytes 1))
      else
        None
    end
|};;

(* 1: Double.toString *)
add_cakeml_at (168,18) {|
  fun toString d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_toString) "" bytes;
      val n = fst (Option.valOf (Word8Array.findi is_0_byte bytes));
    in
      Word8Array.substring bytes 0 n
    end
|};;

(* 2: Double.fromInt *)
add_cakeml_at (180,18) {|
  fun fromInt n =
    let
      val _ = write_bytes 0 (Word64.fromInt n)
      val _ = #(double_fromInt) "" bytes;
    in
      fromWord (read_bytes 0)
    end
|};;

(* 3: Double.toInt *)
add_cakeml_at (191,18) {|
  fun toInt d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_toInt) "" bytes;
    in
      Word64.toIntSigned (read_bytes 0)
    end
|};;

(* 4: Double.pow *)
add_cakeml_at (202,18) {|
  fun pow x y =
    let
      val _ = write_bytes 0 (toWord x)
      val _ = write_bytes 8 (toWord y)
      val _ = #(double_pow) "" bytes;
    in
      fromWord (read_bytes 0)
    end
|};;

(* 5: Double.ln *)
add_cakeml_at (214,18) {|
  fun ln d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_ln) "" bytes;
    in
      fromWord (read_bytes 0)
    end
|};;

(* 6: Double.exp *)
add_cakeml_at (225,18) {|
  fun exp d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_exp) "" bytes;
    in
      fromWord (read_bytes 0)
    end
|};;

(* 7: Double.floor *)
add_cakeml_at (236,18) {|
  fun floor d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_floor) "" bytes;
    in
      fromWord (read_bytes 0)
    end
|};;

(* ------------------------------------------------------------------------- *)
(* Ternary operations                                                        *)
(* ------------------------------------------------------------------------- *)

append_prog
  `[Dlet unknown_loc (Pvar (implode "fma")) (Fun (implode "x") (Fun (implode "y") (Fun (implode "z")
    (App (Arith FMA Float64T) [Var (Short (implode "z")); Var (Short (implode "x"));
    Var (Short (implode "y"))]))))]`;;

(* ------------------------------------------------------------------------- *)
(* Binary operations                                                         *)
(* ------------------------------------------------------------------------- *)

(* HOL4: fun c nm = the ml_translator constant nm; transc nm cnm = trans nm (c cnm) *)
let transc nm cnm = trans nm (mk_const (cnm, []));;

let _ = transc "+" "float64_add";;
let DoubleProg_Double_plus_def = tr_fetch "Double_plus_def";;
let _ = transc "-" "float64_sub";;
let DoubleProg_Double_minus_def = tr_fetch "Double_minus_def";;
let _ = transc "*" "float64_mul";;
let DoubleProg_Double_times_def = tr_fetch "Double_times_def";;
let _ = transc "/" "float64_div";;
let DoubleProg_Double_div_def = tr_fetch "Double_div_def";;

let _ = transc "<"  "float64_less";;
let DoubleProg_Double_lt_def = tr_fetch "Double_lt_def";;
let _ = transc "<=" "float64_less_equal";;
let DoubleProg_Double_le_def = tr_fetch "Double_le_def";;
let _ = transc ">"  "float64_greater";;
let DoubleProg_Double_gt_def = tr_fetch "Double_gt_def";;
let _ = transc ">=" "float64_greater_equal";;
let DoubleProg_Double_ge_def = tr_fetch "Double_ge_def";;
let _ = transc "="  "float64_equal";;
let DoubleProg_Double_eq_def = tr_fetch "Double_eq_def";;

(* ------------------------------------------------------------------------- *)
(* Unary operations                                                          *)
(* ------------------------------------------------------------------------- *)

let _ = transc "abs" "float64_abs";;
let DoubleProg_Double_abs_def = tr_fetch "Double_abs_def";;
let _ = transc "sqrt" "float64_sqrt";;
let DoubleProg_Double_sqrt_def = tr_fetch "Double_sqrt_def";;
let _ = transc "~" "float64_neg";;
let DoubleProg_Double_uminus_def = tr_fetch "Double_uminus_def";;

(* ------------------------------------------------------------------------- *)
(* Taking floats apart                                                       *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("float64",`:(52,11)float`);;

let DoubleProg_significand_def = new_definition
  `DoubleProg_significand (f:float64) =
     word_and (float_to_fp64 f) (word 4503599627370495)`;;

let significand_correct = prove
 (`!f:float64. DoubleProg_significand f = word_zx (float_Significand f)`,
  GEN_TAC THEN REWRITE_TAC[DoubleProg_significand_def; float_to_fp64_def] THEN
  CONV_TAC WORD_BLAST);;

let DoubleProg_exponent_def = new_definition
  `DoubleProg_exponent (f:float64) =
     word_and (word_ushr (float_to_fp64 f) 52) (word 2047)`;;

let exponent_correct = prove
 (`!f:float64. DoubleProg_exponent f = word_zx (float_Exponent f)`,
  GEN_TAC THEN REWRITE_TAC[DoubleProg_exponent_def; float_to_fp64_def] THEN
  CONV_TAC WORD_BLAST);;

let DoubleProg_sign_def = new_definition
  `DoubleProg_sign (f:float64) =
     word_and (word_ushr (float_to_fp64 f) 63) (word 1)`;;

let _ = translate DoubleProg_significand_def;;
let _ = translate DoubleProg_exponent_def;;
let _ = translate DoubleProg_sign_def;;

(* ------------------------------------------------------------------------- *)
(* Putting a float together from its constituent parts (layout order)        *)
(* ------------------------------------------------------------------------- *)

let DoubleProg_construct_def = new_definition
  `DoubleProg_construct (sgn:int64) (exp:int64) (sgf:int64) =
     fp64_to_float (
       word_or (word_shl (word_and sgn (word 1)) 63)
       (word_or (word_shl (word_and exp (word 2047)) 52)
                (word_and sgf (word 4503599627370495))))`;;

let _ = translate DoubleProg_construct_def;;

let fnext_hi_def = new_definition
  `fnext_hi (f:float64) = fp64_to_float (word_add (float_to_fp64 f) (word 1))`;;

let fnext_lo_def = new_definition
  `fnext_lo (f:float64) = fp64_to_float (word_sub (float_to_fp64 f) (word 1))`;;

let _ = translate fnext_hi_def;;
let _ = translate fnext_lo_def;;

let float_is_finite_characterisation = prove
 (`!f:float64. float_is_finite f <=> ~(DoubleProg_exponent f = word 2047)`,
  GEN_TAC THEN
  REWRITE_TAC[float_is_finite; float_is_subnormal_def; float_is_normal_def;
              float_is_zero; exponent_correct] THEN
  SPEC_TAC (`float_Exponent (f:float64)`, `e:11 word`) THEN
  SPEC_TAC (`float_Significand (f:float64)`, `m:52 word`) THEN
  REWRITE_TAC[word_UINT_MAX] THEN CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let _ = translate float_is_finite_characterisation;;

let float_is_zero_characterisation = prove
 (`!f:float64. float_is_zero f <=>
               DoubleProg_exponent f = word 0 /\ DoubleProg_significand f = word 0`,
  GEN_TAC THEN REWRITE_TAC[float_is_zero; exponent_correct; significand_correct] THEN
  SPEC_TAC (`float_Exponent (f:float64)`, `e:11 word`) THEN
  SPEC_TAC (`float_Significand (f:float64)`, `m:52 word`) THEN
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let _ = translate float_is_zero_characterisation;;

let flt_max_def = new_definition
  `flt_max:float64 = float_REC (word 0) (word 2046) (word 4503599627370495)`;;

let _ = translate flt_max_def;;

let maxulp_def = new_definition
  `maxulp:float64 = float_REC (word 0) (word 1994) (word 0)`;;

let _ = translate maxulp_def;;

let twicemaxulp_def = new_definition
  `twicemaxulp:float64 = float_REC (word 0) (word 1995) (word 0)`;;

let _ = translate twicemaxulp_def;;

let ffloat_ulp_def = new_definition
  `ffloat_ulp (f0:float64) =
     let f = float64_abs f0 in
     if float_is_finite f then
       if f = flt_max then maxulp
       else float64_sub (fnext_hi f) f
     else
       twicemaxulp`;;
let _ = translate ffloat_ulp_def;;

let posinf64_def = new_definition
  `posinf64:float64 = float_REC (word 0) (word 2047) (word 0)`;;
let _ = translate posinf64_def;;

let neginf64_def = new_definition
  `neginf64:float64 = float_REC (word 1) (word 2047) (word 0)`;;
let _ = translate neginf64_def;;

(* HOL4: posmin64 = the EVAL of fp64_to_float 1w *)
let posmin64_def = new_definition (mk_eq (`posmin64:float64`,
  rhs (concl ((REWR_CONV fp64_to_float_def THENC WORD_REDUCE_CONV)
                `fp64_to_float (word 1)`))));;
let _ = translate posmin64_def;;

(* HOL4: poszero64 = the EVAL of fp64_to_float 0w *)
let poszero64_def = new_definition (mk_eq (`poszero64:float64`,
  rhs (concl ((REWR_CONV fp64_to_float_def THENC WORD_REDUCE_CONV)
                `fp64_to_float (word 0)`))));;
let _ = translate poszero64_def;;

(* ------------------------------------------------------------------------- *)
(* Pretty-printer                                                            *)
(* ------------------------------------------------------------------------- *)

append_prog
  `[Dlet unknown_loc
     (Pvar (implode "pp_double"))
     (Fun (implode "x") (App Opapp [
        Var (Long (implode "PrettyPrinter") (Short (implode "token")));
        App Opapp [Var (Short (implode "toString")); Var (Short (implode "x"))]]))]`;;

ml_prog_update ml_prog_close_local_blocks;;
ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
