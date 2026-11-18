(* ========================================================================= *)
(* CakeML kit: independent wildcards in quotations.                          *)
(*                                                                           *)
(* HOL Light reads every _ of a quotation as the same variable "_": the two  *)
(* wildcards of CONS _ (CONS _ t), or the wildcards of two clauses of a      *)
(* definition, are one variable with one type.  HOL4 reads each _ as a new   *)
(* variable.  The parse_term below (which the quotation expander calls)      *)
(* gives each _ token its own name _%wN before parsing, so wildcards are     *)
(* independent variables of independent types.  is_wildcard (pmatch.ml)     *)
(* recognises these names; the definition package and the match compiler   *)
(* never let them reach a theorem.                                           *)
(* ========================================================================= *)

let cake_wild_counter = ref 0;;

(* the lexer glues _ to symbol characters after it (_:num lexes as the     *)
(* identifier "_:" followed by num); such a token is split, so (_:num) is  *)
(* a wildcard of type num                                                   *)

let cake_wild_tokens t =
  let fresh() = incr cake_wild_counter;
                Ident("_%w" ^ string_of_int !cake_wild_counter) in
  match t with
    Ident "_" -> [fresh()]
  | Ident s when String.length s > 1 && String.sub s 0 1 = "_" &&
                 forall issymb (tl(explode s)) ->
      fresh() :: lex(tl(explode s))
  | _ -> [t];;

let parse_term s =
  let ptm,l = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l = [] then (term_of_preterm o (retypecheck [])) ptm
  else failwith "Unparsed input following term";;

(* T and F, the commonest quotations in tactic code that runs once per       *)
(* subterm or per assumption, like concl th = F: made once (a parse costs   *)
(* milliseconds in a session with thousands of constants)                   *)

let parse_term =
  let t_tm = parse_term "T" and f_tm = parse_term "F" in
  fun s -> if s = "T" then t_tm else if s = "F" then f_tm else parse_term s;;
