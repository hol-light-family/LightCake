(* ========================================================================= *)
(* regexp_compiler: port of the vector part of HOL4                          *)
(* examples/formal-languages/regular/regexp_compilerScript.sml (HOL4         *)
(* library used by CakeML v3479): the output type of the regexp compiler,    *)
(* which basis/pure/mlvectorScript.sml takes over as the type of vectors.   *)
(* The regexp compiler itself is not part of the CakeML closure and is not   *)
(* ported.                                                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 fromList is regexp_compiler_fromList (fromList is the sptree       *)
(*   constant); its theorem fromList_def is regexp_compiler_fromList_def.    *)
(* - The type is :A vector (the HOL Light constant vector of cart.ml lives   *)
(*   in the namespace of constants, the type in that of types).              *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Output of the compiler is in terms of vectors.                            *)
(* ------------------------------------------------------------------------- *)

let vector_INDUCT,vector_RECURSION = cake_type "vector = Vector (A list)";;

(* the theorems HOL4's Datatype makes *)

let vector_induction = prove
 (`!P. (!l:A list. P (Vector l)) ==> !v. P v`,
  REWRITE_TAC[vector_INDUCT]);;

let vector_Axiom = prove
 (`!f:A list->B. ?fn. !a. fn (Vector a) = f a`,
  REWRITE_TAC[vector_RECURSION]);;

let vector_nchotomy = prove
 (`!vv:A vector. ?l. vv = Vector l`,
  REWRITE_TAC[cases "vector"]);;

let vector_11 = prove
 (`!a a':A list. Vector a = Vector a' <=> a = a'`,
  REWRITE_TAC[injectivity "vector"]);;

let vector_case_def = case_def "vector";;

let vector_case_eq = case_eq "vector";;

let vector_size_def = type_size_def "vector";;

let sub_def =
  let th = cake_def `sub (Vector (l:A list)) n = EL n l` in
  prove
   (`!(l:A list) n. sub (Vector l) n = EL n l`,
    REWRITE_TAC[th]);;

let length_def = cake_def
  `length (Vector (l:A list)) = LENGTH l`;;

(* HOL4: fromList_def *)

let regexp_compiler_fromList_def = new_definition
  `regexp_compiler_fromList (l:A list) = Vector l`;;

let fromList_Vector = prove
 (`regexp_compiler_fromList = (Vector:A list->A vector)`,
  REWRITE_TAC[FUN_EQ_THM; regexp_compiler_fromList_def]);;
