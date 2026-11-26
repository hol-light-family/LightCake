(* ========================================================================= *)
(* errorLogMonad: port of HOL4 src/monad/more_monads/errorLogMonadScript.sml *)
(* (HOL4 library).  The error monad with a log: a value or an error, with   *)
(* the list of the messages (warnings) logged so far.                       *)
(*                                                                           *)
(* HOL4 Type M = :('a,'e) error # 'w list (errorLogMonad_M in names.tsv)    *)
(* has type variables, so it is written out where it is used, and HOL4's    *)
(* Overload emret = errorMonad$return is errorMonad_return.  The constants  *)
(* return, error, bind and choice take the prefix errorLogMonad_            *)
(* (errorMonad has them too); silently keeps its name.  Not                 *)
(* ported: the monadsyntax declaration (HOL4 parser support).               *)
(* HOL4 log is errorLogMonad_log (a short or common word; log is also a      *)
(* constant of HOL Light's Multivariate), and log_def is                     *)
(* errorLogMonad_log_def.                                                    *)
(* ========================================================================= *)

needs "hol4/errorMonad.ml";;

type_invention_error := true;;

let M_CASES = prove
 (`!M:(A,E)error#W.
     (?v ms. M = (errorMonad_return v,ms)) \/
     (?e ms. M = (errorMonad_error e,ms))`,
  REWRITE_TAC[FORALL_PAIR_THM; FORALL_ERROR; PAIR_EQ] THEN MESON_TAC[]);;

let errorLogMonad_return_def = cake_def
  `errorLogMonad_return (v:A) = (errorMonad_return v,[]):(A,E)error#(W)list`;;

let errorLogMonad_log_def = cake_def
  `errorLogMonad_log (m:L) = (errorMonad_return one,[m]):(1,E)error#(L)list`;;

let errorLogMonad_error_def = cake_def
  `errorLogMonad_error (e:E) = (errorMonad_error e,[]):(A,E)error#(L)list`;;

let errorLogMonad_bind_def = cake_def
  `errorLogMonad_bind (M:(A,E)error#(L)list) (f:A->(B,E)error#(L)list) =
     match M with
       (errorMonad_return u,ms1) -> (I ## APPEND ms1) (f u)
     | (errorMonad_error e,ms1) -> (errorMonad_error e,ms1)`;;

let bind_IDL = prove
 (`!(v:A) (f:A->(B,E)error#(L)list).
     errorLogMonad_bind (errorLogMonad_return v) f = f v`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `(f:A->(B,E)error#(L)list) v` THEN
  FS[errorLogMonad_bind_def; errorLogMonad_return_def; PAIR_MAP_THM;
     I_THM; APPEND]);;
let _ = cake_add_simps [bind_IDL];;

let bind_IDR = prove
 (`!M:(A,E)error#(L)list. errorLogMonad_bind M errorLogMonad_return = M`,
  REWRITE_TAC[FORALL_PAIR_THM; FORALL_ERROR] THEN
  SIMP[errorLogMonad_bind_def; errorLogMonad_return_def; PAIR_MAP_THM;
       I_THM; APPEND_NIL]);;
let _ = cake_add_simps [bind_IDR];;

let bind_EQ_success = prove
 (`!M (f:A->(B,E)error#(L)list) v ms.
     errorLogMonad_bind M f = (errorMonad_return v,ms) <=>
     ?u ms0 ms1. M = (errorMonad_return u,ms0) /\
                 f u = (errorMonad_return v,ms1) /\ ms = APPEND ms0 ms1`,
  REWRITE_TAC[FORALL_PAIR_THM; FORALL_ERROR] THEN
  SIMP[errorLogMonad_bind_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  PAIR_CASES_ON `(f:A->(B,E)error#(L)list) a` THEN
  SIMP[PAIR_MAP_THM; I_THM] THEN MESON_TAC[]);;

let silently_def = cake_def
  `silently (M:A#B) = (I ## combin_K ([]:(C)list)) M`;;

let errorLogMonad_choice_def = cake_def
  `errorLogMonad_choice (M1:(A,E1)error#(L)list) (M2:(A,E2)error#(L)list) =
     match M1 with
       (errorMonad_return v,ms1) -> (errorMonad_return v,ms1)
     | (errorMonad_error e,ms1) -> (I ## APPEND ms1) M2`;;

let choice_return = prove
 (`!(v:A) (M:(A,E2)error#(L)list).
     errorLogMonad_choice
       (errorLogMonad_return v:(A,E1)error#(L)list) M =
     errorLogMonad_return v`,
  SIMP[errorLogMonad_choice_def; errorLogMonad_return_def]);;
let _ = cake_add_simps [choice_return];;
