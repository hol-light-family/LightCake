(* ========================================================================= *)
(* SexpProg: port of HOL4 basis/SexpProgScript.sml (CakeML v3479), the code  *)
(* part.  Module for parsing and pretty-printing s-expressions.             *)
(*                                                                           *)
(* The mlsexp functions are basis/pure/mlsexp.ml's (HOL4 token is            *)
(* mlsexp_token; read_string, lex_aux, lex, parse, fromString, flatten,      *)
(* get_size, annotate are mlsexp_read_string, ...).  The CakeML text of the  *)
(* Quote add_cakeml blocks is HOL4's, verbatim, at HOL4's positions.  OPEN   *)
(* (M10, decision D2): the equivalence proofs to                             *)
(* mlsexp (read_string_aux_imp_post, lex_aux_imp_post and the CF specs       *)
(* read_string_aux_imp_spec .. inputSexp_spec).                              *)
(* ========================================================================= *)

needs "basis/TextIOProg.ml";;
needs "basis/pure/mlsexp.ml";;
needs "translator/ml_translator.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Translation                                                               *)
(* ------------------------------------------------------------------------- *)

translation_extends "TextIOProg";;

ml_prog_update (ml_prog_open_module "Sexp");;

(* Temporarily disable full type names to avoid mlsexp_sexp as the exported *)
(* type name (HOL4 comment; with_flag)                                      *)
use_full_type_names := false;;
register_type `:sexp`;;
use_full_type_names := true;;
use_full_type_names := false;;
register_type `:str_tree`;;
use_full_type_names := true;;

(* Pretty printing function for s-expressions used by the REPL *)
add_cakeml_at (33,18) {|
  fun pp_sexp se = case se of
    Atom s => PrettyPrinter.app_block "Atom" [PrettyPrinter.token s]
  | Expr ses => PrettyPrinter.app_block "Expr" [PrettyPrinter.pp_list pp_sexp ses];
  fun pp_str_tree se = case se of
    Str s => PrettyPrinter.app_block "Str" [PrettyPrinter.token s]
  | Grabline s => PrettyPrinter.app_block "Grabline" [pp_str_tree s]
  | Trees ses => PrettyPrinter.app_block "Trees" [PrettyPrinter.pp_list pp_str_tree ses];
|};;

(* We will define two functions to generate s-expressions: fromString,      *)
(* simple, failing with None, translated from mlsexp; and inputSexp,        *)
(* efficient (buffered input), failing with exceptions, written in CakeML   *)
(* (HOL4 comment, shortened)                                                 *)

ml_prog_update ml_prog_open_local_block;;

(* Shared, but private, helpers and types *)
register_type `:mlsexp_token`;;
let _ = translate parse_aux_def;;

(* Private helpers for fromString *)
let _ = translate read_string_aux_def;;
let _ = translate mlsexp_read_string_def;;
(* HOL4: SRULE [isSpace_def]; the kit's induction theorem is given the same *)
(* rewrite, so that the translator's induction goal matches it             *)
add_ind_thm "read_symbol" (REWRITE_RULE [isSpace_def] (cake_ind "read_symbol"));;
let _ = translate (REWRITE_RULE [isSpace_def] read_symbol_def);;

let _ = translate_no_ind mlsexp_lex_aux_def;;

(* HOL4 fetch "-" "lex_aux_ind_def" (see ListProg.ml mergesortn_tail_ind) *)
let lex_aux_ind_def =
  try tr_fetch "lex_aux_ind_def" with Failure _ ->
  find (fun th -> try fst (dest_const (lhs (concl th))) = "lex_aux_ind"
                  with Failure _ -> false) (definitions ());;

let lex_aux_ind = prove
 (lhs (concl lex_aux_ind_def),
  ONCE_REWRITE_TAC[lex_aux_ind_def] THEN GEN_TAC THEN DISCH_THEN (LABEL_TAC "H") THEN
  MATCH_MP_TAC (latest_ind ()) THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REMOVE_THEN "H" MATCH_MP_TAC THEN REWRITE_TAC[NOT_CONS_NIL];
    STRIP_TAC THEN REMOVE_THEN "H" MATCH_MP_TAC THEN
    REWRITE_TAC[CONS_11] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)) &&
              not (is_var (rhs (concl th)))))) THEN
    ASM_MESON_TAC[NOT_SUC; ARITH_RULE `1 <= SUC n`]]);;

let _ = update_precondition lex_aux_ind;;

let _ = translate mlsexp_lex_def;;
let _ = translate mlsexp_parse_def;;

(* Private helpers for inputSexp *)
add_cakeml_at (90,18) {|
  fun read_string_aux_imp input acc =
    case TextIO.input1 input of
      None => raise Fail "read_string_aux: unterminated string literal"
    | Some c =>
        if c = #"\"" then String.implode (List.rev acc) else
        if c = #"\\" then
          (case TextIO.input1 input of
             None => read_string_aux_imp input acc (* causes error: unterminated string *)
           | Some e =>
               (if e = #"\\" then read_string_aux_imp input (#"\\"::acc) else
                if e = #"\""  then read_string_aux_imp input (#"\""::acc) else
                if e = #"0"  then read_string_aux_imp input (#"\000"::acc) else
                if e = #"n"  then read_string_aux_imp input (#"\n"::acc) else
                if e = #"r"  then read_string_aux_imp input (#"\r"::acc) else
                if e = #"t"  then read_string_aux_imp input (#"\t"::acc) else
                  raise Fail "read_string_aux: unrecognised escape"))
        else
          read_string_aux_imp input (c::acc)
|};;

add_cakeml_at (111,18) {|
  fun read_string_imp input = read_string_aux_imp input []
|};;

add_cakeml_at (115,18) {|
  fun read_symbol_imp input acc =
    case TextIO.peekChar input of
      None => String.implode (List.rev acc)
    | Some c =>
        if c = #")" orelse Char.isSpace c
        then String.implode (List.rev acc)
        else (
          TextIO.input1 input;  (* Consume c *)
          read_symbol_imp input (c::acc))
|};;

add_cakeml_at (127,18) {|
  fun lex_aux_imp depth input acc =
    case TextIO.input1 input of
      None => if depth = 0 then acc
              else raise Fail "lex_aux: missing closing parenthesis"
    | Some c =>
        if Char.isSpace c then lex_aux_imp depth input acc
        else if c = #"(" then lex_aux_imp (depth + 1) input (Open::acc)
        else if c = #")" then
          (if depth = 0 then raise Fail "lex_aux: too many closing parenthesis"
           else if depth = 1 then Close::acc
           else lex_aux_imp (depth - 1) input (Close::acc))
        else if c = #"\"" then
          let val s = read_string_imp input in
            if depth = 0 then [Symbol s]
            else lex_aux_imp depth input ((Symbol s)::acc) end
        else
          let val s = read_symbol_imp input [c] in
            if depth = 0 then [Symbol s]
            else lex_aux_imp depth input ((Symbol s)::acc) end
|};;

add_cakeml_at (149,18) {|
  fun lex_imp input = lex_aux_imp 0 input []
|};;

ml_prog_update ml_prog_open_local_in_block;;

(* Exported functions *)
next_ml_names := ["fromString"];;
let _ = translate mlsexp_fromString_def;;

(* If we were 100% consistent, we should call this parse_imp. Since it      *)
(* isn't a neat name, and parse is already taken by the translated pure     *)
(* version, we use inputSexp. (HOL4 comment)                                 *)
add_cakeml_at (162,18) {|
  fun inputSexp input =
    case parse_aux (lex_imp input) [] [] of
      [] => raise Fail "parse: empty input"
    | (v::_) => v
|};;

ml_prog_update ml_prog_open_local_block;;

let _ = translate mlsexp_flatten_def;;
let _ = translate mlsexp_get_size_def;;
let _ = translate get_next_size_def;;
let _ = translate remove_all_def;;
let _ = translate smart_remove_def;;
let _ = translate mlsexp_annotate_def;;
let _ = translate newlines_def;;
let _ = translate v2pretty_def;;
let _ = translate str_every_def;;
(* HOL4: SRULE [] (MEM of the string literal) *)
let _ = translate (REWRITE_RULE [MEM] is_safe_char_def);;
let _ = translate make_str_safe_def;;

(* HOL4: Cases \\ Induct (on n) \\ Once str_every_side_def: VectorProg's tactic *)
let str_every_side = prove
 (`!x n P. n <= strlen x ==> str_every_side P n x`,
  BAS1AUX_SIDE_TAC "n" (tr_fetch "str_every_side_def"));;

let make_str_safe_side = prove
 (`!x. make_str_safe_side x <=> T`,
  REWRITE_TAC[tr_fetch "make_str_safe_side_def"] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC str_every_side THEN ARITH_TAC);;

let _ = update_precondition make_str_safe_side;;

let _ = translate sexp_to_app_list_def;;
let _ = translate sexp2tree_def;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["str_tree_to_strings"];;
let _ = translate str_tree_to_strs_def;;

next_ml_names := ["toString"];;
let _ = translate sexp_to_string_def;;
next_ml_names := ["toPrettyString"];;
let _ = translate sexp_to_pretty_string_def;;

ml_prog_update ml_prog_close_local_blocks;;
ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
