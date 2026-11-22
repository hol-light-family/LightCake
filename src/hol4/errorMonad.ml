(* ========================================================================= *)
(* errorMonad: port of HOL4 src/monad/more_monads/errorMonadScript.sml      *)
(* (HOL4 library).  The error monad: a value or an error.                   *)
(*                                                                           *)
(* Names (notes/naming/names.tsv): the type error keeps its name; the       *)
(* constructors return and error and the constants bind, try, choice and    *)
(* guard take the prefix errorMonad_ (errorMonad_return, errorMonad_error,  *)
(* errorMonad_bind, ...; peg, bvi_tmc, cmlPEG and errorLogMonad have        *)
(* those names).  HOL4 () is one.  Not ported: the monadsyntax declaration  *)
(* (HOL4 parser support for do-notation; write errorMonad_bind).            *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

let error_INDUCT,error_RECURSION =
  cake_type "error = errorMonad_return A | errorMonad_error E";;

let EXISTS_ERROR = prove
 (`!P. (?e:(A,E)error. P e) <=>
       (?a. P (errorMonad_return a)) \/ (?e. P (errorMonad_error e))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:(A,E)error` MP_TAC) THEN
    QCASES_ON "e" THEN MESON_TAC[];
    MESON_TAC[]]);;

let FORALL_ERROR = prove
 (`!P. (!e:(A,E)error. P e) <=>
       (!a. P (errorMonad_return a)) /\ (!e. P (errorMonad_error e))`,
  GEN_TAC THEN EQ_TAC THENL [SIMP[]; STRIP_TAC] THEN
  GEN_TAC THEN QCASES_ON "e" THEN ASM_REWRITE_TAC[]);;

let errorMonad_bind_def = cake_def
  `(errorMonad_bind (errorMonad_return v:(A,E)error) (f:A->(B,E)error) = f v) /\
   (errorMonad_bind (errorMonad_error e) f = errorMonad_error e)`;;
let _ = cake_add_simps [errorMonad_bind_def];;

let errorMonad_try_def = cake_def
  `(errorMonad_try (errorMonad_return v:(A,E1)error) (f:E1->(A,E2)error) =
      errorMonad_return v) /\
   (errorMonad_try (errorMonad_error e) f = f e)`;;
let _ = cake_add_simps [errorMonad_try_def];;

let errorMonad_choice_def = cake_def
  `(errorMonad_choice (errorMonad_return v:(A,E1)error) (m:(A,E2)error) =
      errorMonad_return v) /\
   (errorMonad_choice (errorMonad_error e) m = m)`;;

let errorMonad_guard_def = cake_def
  `errorMonad_guard (e:E) b =
     if b then errorMonad_return one else errorMonad_error e`;;

let bind_return = prove
 (`!m:(A,E)error. errorMonad_bind m errorMonad_return = m`,
  GEN_TAC THEN QCASES_ON "m" THEN SIMP[]);;

let bind_EQ_return = prove
 (`!m:(A,E)error f (v:B).
     errorMonad_bind m f = errorMonad_return v <=>
     ?u. m = errorMonad_return u /\ f u = errorMonad_return v`,
  GEN_TAC THEN QCASES_ON "m" THEN SIMP[]);;

let bind_EQ_error = prove
 (`!m:(A,E)error (f:A->(B,E)error) e.
     errorMonad_bind m f = errorMonad_error e <=>
     m = errorMonad_error e \/
     ?u. m = errorMonad_return u /\ f u = errorMonad_error e`,
  GEN_TAC THEN QCASES_ON "m" THEN SIMP[]);;
