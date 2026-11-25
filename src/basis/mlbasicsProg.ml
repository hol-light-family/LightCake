(* ========================================================================= *)
(* mlbasicsProg: port of HOL4 basis/mlbasicsProgScript.sml (CakeML v3479),  *)
(* the code part (decision D2).  Translates a variety of basic constructs:   *)
(* binds built-in functions to the names the parser expects (the parser      *)
(* generates a call to a function called "+" when it parses 1+2).  The CF    *)
(* specifications deref_spec and assign_spec (and HOL4's prove_ref_spec)     *)
(* are mlbasicsProg_part2.ml (M10).                                          *)
(* ========================================================================= *)

needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;
needs "basis/StringProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "StringProg";;

(* HOL4: mk_binop *)
let mlbasicsProg_mk_binop_def = new_definition
  `mlbasicsProg_mk_binop name prim =
     Dlet unknown_loc (Pvar name)
       (Fun (implode "x") (Fun (implode "y")
          (App prim [Var (Short (implode "x")); Var (Short (implode "y"))])))`;;

(* HOL4: mk_unop *)
let mlbasicsProg_mk_unop_def = new_definition
  `mlbasicsProg_mk_unop name prim =
     Dlet unknown_loc (Pvar name) (Fun (implode "x") (App prim [Var (Short (implode "x"))]))`;;

(* HOL4's EVAL in append_prog unfolds them *)
basis_add_eval_thms [mlbasicsProg_mk_binop_def; mlbasicsProg_mk_unop_def];;

let _ = trans "+" `int_add`;;
let mlbasicsProg_plus_def = tr_fetch "mlbasicsProg_plus_def";;
let _ = trans "-" `int_sub`;;
let mlbasicsProg_minus_def = tr_fetch "mlbasicsProg_minus_def";;
let _ = trans "*" `int_mul`;;
let mlbasicsProg_times_def = tr_fetch "mlbasicsProg_times_def";;
let _ = trans "div" `int_div`;;
let mlbasicsProg_div_def = tr_fetch "mlbasicsProg_div_def";;
let _ = trans "mod" `integer_int_mod`;;
let mlbasicsProg_mod_def = tr_fetch "mlbasicsProg_mod_def";;
let _ = trans "<" `int_lt`;;
let mlbasicsProg_lt_def = tr_fetch "mlbasicsProg_lt_def";;
let _ = trans ">" `int_gt`;;
let mlbasicsProg_gt_def = tr_fetch "mlbasicsProg_gt_def";;
let _ = trans "<=" `int_le`;;
let mlbasicsProg_le_def = tr_fetch "mlbasicsProg_le_def";;
let _ = trans ">=" `int_ge`;;
let mlbasicsProg_ge_def = tr_fetch "mlbasicsProg_ge_def";;
let _ = trans "~" `\i. --(i:int)`;;
let mlbasicsProg_uminus_def = tr_fetch "mlbasicsProg_uminus_def";;
let _ = trans "@" `APPEND:A list->A list->A list`;;
let mlbasicsProg_append_def = tr_fetch "mlbasicsProg_append_def";;

(* other basics that parser targets -- CF verified *)

let _ = trans "=" `\x1 x2. x1 = (x2:A)`;;
let mlbasicsProg_eq_def = tr_fetch "mlbasicsProg_eq_def";;
let _ = trans "not" `\x. ~(x:bool)`;;
let mlbasicsProg_not_def = tr_fetch "mlbasicsProg_not_def";;
let _ = trans "<>" `\x1 x2. ~(x1 = (x2:A))`;;
let mlbasicsProg_neq_def = tr_fetch "mlbasicsProg_neq_def";;
let _ = trans "^" `strcat`;;
let mlbasicsProg_strcat_def = tr_fetch "mlbasicsProg_strcat_def";;

append_prog
  `[mlbasicsProg_mk_binop (implode ":=") Opassign;
    mlbasicsProg_mk_unop (implode "!") Opderef]`;;

(* prove_ref_spec, deref_spec, assign_spec: CF, mlbasicsProg_part2.ml (M10) *)

let bool_toString_def = new_definition
  `bool_toString b = if b then implode "True" else implode "False"`;;

let bool_fromString_def = new_definition
  `bool_fromString s = if s = implode "True" then SOME T else
                       if s = implode "False" then SOME F else
                       NONE`;;

ml_prog_update (ml_prog_open_module "Bool");;
next_ml_names := ["not"];;
let _ = trans "not" `\x. ~(x:bool)`;;
let mlbasicsProg_Bool_not_def = tr_fetch "Bool_not_def";;
let _ = trans "=" `(=):bool->bool->bool`;;
let mlbasicsProg_Bool_eq_def = tr_fetch "Bool_eq_def";;
next_ml_names := ["toString"];;
let _ = translate bool_toString_def;;
next_ml_names := ["fromString"];;
let _ = translate bool_fromString_def;;
next_ml_names := ["compare"];;
let _ = translate bool_cmp_def;;
ml_prog_update (ml_prog_close_module None);;

let pair_toString_def = cake_def
  `pair_toString (f1:A->mlstring) (f2:B->mlstring) (x,y) =
     mlstring_concat [implode "(";
                      f1 x;
                      implode ", ";
                      f2 y;
                      implode ")"]`;;

ml_prog_update (ml_prog_open_module "Pair");;
next_ml_names := ["map"];;
let _ = translate PAIR_MAP_THM;;
next_ml_names := ["toString"];;
let _ = translate pair_toString_def;;
next_ml_names := ["compare"];;
let _ = translate pair_cmp_def;;
ml_prog_update (ml_prog_close_module None);;

add_cakeml_at (138,18) {|
  exception Fail string
|};;

(* HOL4 val Fail_ (OCaml cannot bind Fail_) *)
let mlbasicsProg_Fail_ = get_exn_conv `implode "Fail"`;;

(* HOL4: Fail_exn_def *)
let mlbasicsProg_Fail_exn_def = new_definition
  (vsubst [mlbasicsProg_Fail_, `fail_stamp:stamp`]
   `Fail_exn s v <=> ?sv. v = Conv (SOME fail_stamp) [sv] /\ STRING_TYPE s sv`);;

finalise_translation ();;
