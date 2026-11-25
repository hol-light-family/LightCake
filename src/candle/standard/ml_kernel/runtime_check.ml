(* ========================================================================= *)
(* runtime_check: port of HOL4 candle/standard/ml_kernel/                    *)
(* runtime_checkScript.sml (CakeML v3479).  Theorems and definitions to     *)
(* support adding runtime type checking annotations.                         *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

let pure_seq_intro = prove
 (`!(x:B) (y:B). x = y ==> !(z:A). x = pure_seq z y`,
  SIMP[pure_seq_def]);;

(* HOL4's script builds the check expressions with its SML functions         *)
(* type_check, term_check and thm_check (also in runtime_checkLib):         *)
(* case t of Tyvar _ => () | _ => (), case tm of Const _ _ => () | _ => ()   *)
(* and case th of Sequent _ _ => (); they are written out below (HOL4's ()   *)
(* is one), and the kit keeps them as case constants with one in every arm. *)

let check_ty_def = cake_def
  `(check_ty [] = one) /\
   (check_ty (CONS t1 l) =
      pure_seq (match t1 with Tyvar _ -> one | _ -> one) (check_ty l))`;;

let check_tm_def = cake_def
  `(check_tm [] = one) /\
   (check_tm (CONS tm l) =
      pure_seq (match tm with hol_Const _ _ -> one | _ -> one) (check_tm l))`;;

let check_thm_def = cake_def
  `(check_thm [] = one) /\
   (check_thm (CONS th l) =
      pure_seq (match th with Sequent _ _ -> one) (check_thm l))`;;

let check_ty_ty_def = cake_def
  `(check_ty_ty [] = one) /\
   (check_ty_ty (CONS (t1,t2) l) =
      pure_seq (match t1 with Tyvar _ -> one | _ -> one)
        (pure_seq (match t2 with Tyvar _ -> one | _ -> one) (check_ty_ty l)))`;;

let check_tm_tm_def = cake_def
  `(check_tm_tm [] = one) /\
   (check_tm_tm (CONS (tm,tm') l) =
      pure_seq (match tm with hol_Const _ _ -> one | _ -> one)
        (pure_seq (match tm' with hol_Const _ _ -> one | _ -> one)
           (check_tm_tm l)))`;;
