(* ========================================================================= *)
(* runtime_checkLib: port of HOL4 candle/standard/ml_kernel/                 *)
(* runtime_checkLib.sml (CakeML v3479).  Mechanism for adding runtime type   *)
(* checking annotations, used in the Candle prover soundness proofs:         *)
(*   runtime_check_check ["v1"; "v2"] def                                    *)
(* gives |- f args = pure_seq (check v1) (pure_seq (check v2) rhs) for       *)
(* def |- f args = rhs, the check of each variable chosen by its type        *)
(* (HOL4 check [`v1`,`v2`] def).                                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's names check, type_check, term_check, ... are bound here with the *)
(*   prefix runtime_check_ (one session holds every file: check is a HOL     *)
(*   Light library function, and the others are common words).               *)
(* - HOL4 parses each argument with parse_in_context; the kernel script only *)
(*   checks variables of the definition: here the arguments are the names of *)
(*   free variables of the definition.                                       *)
(* - The checks are HOL4's: case t of Tyvar _ => () | _ => (), case tm of    *)
(*   Const _ _ => () | _ => (), case th of Sequent _ _ => (), strlen s, and  *)
(*   check_ty, check_tm, check_thm, check_ty_ty, check_tm_tm of              *)
(*   runtime_check.ml for lists (HOL4's () is one, Const is hol_Const).      *)
(* ========================================================================= *)

needs "candle/standard/ml_kernel/runtime_check.ml";;

type_invention_error := true;;

let runtime_check_type_pat = CASE_TERM `match (t:hol_type) with Tyvar _ -> one | _ -> one`;;
let runtime_check_term_pat =
  CASE_TERM `match (tm:hol_term) with hol_Const _ _ -> one | _ -> one`;;
let runtime_check_thm_pat = CASE_TERM `match (th:thm) with Sequent _ _ -> one`;;

let runtime_check_mlstring_check s = mk_comb (`strlen`, s);;
let runtime_check_type_check ty = vsubst [ty, `t:hol_type`] runtime_check_type_pat;;
let runtime_check_term_check tm = vsubst [tm, `tm:hol_term`] runtime_check_term_pat;;
let runtime_check_thm_check th = vsubst [th, `th:thm`] runtime_check_thm_pat;;
let runtime_check_ty_list_check ty = mk_comb (`check_ty`, ty);;
let runtime_check_tm_list_check tm = mk_comb (`check_tm`, tm);;
let runtime_check_thm_list_check th = mk_comb (`check_thm`, th);;
let runtime_check_ty_ty_list_check tyty = mk_comb (`check_ty_ty`, tyty);;
let runtime_check_tm_tm_list_check tmtm = mk_comb (`check_tm_tm`, tmtm);;

let runtime_check_guess_check tm =
  let ty = type_of tm in
  if ty = `:mlstring` then runtime_check_mlstring_check else
  if ty = `:hol_type` then runtime_check_type_check else
  if ty = `:hol_term` then runtime_check_term_check else
  if ty = `:thm` then runtime_check_thm_check else
  if ty = `:(hol_type)list` then runtime_check_ty_list_check else
  if ty = `:(hol_term)list` then runtime_check_tm_list_check else
  if ty = `:(thm)list` then runtime_check_thm_list_check else
  if ty = `:(hol_type#hol_type)list` then runtime_check_ty_ty_list_check else
  if ty = `:(hol_term#hol_term)list` then runtime_check_tm_tm_list_check else
  failwith ("runtime_check_guess_check: no check for type " ^ string_of_type ty);;

let runtime_check_add_type_check v f def =
  let def = SPEC_ALL def in
  ISPEC (f v) (MATCH_MP pure_seq_intro def);;

let rec runtime_check_check vs def =
  match vs with
    [] -> SPEC_ALL def
  | v::vs ->
      let def = runtime_check_check vs def in
      let tm = try find (fun x -> fst (dest_var x) = v) (frees (concl def))
               with Failure _ -> failwith ("runtime_check_check: no variable " ^ v) in
      let f = runtime_check_guess_check tm in
      runtime_check_add_type_check tm f def;;
