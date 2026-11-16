(* ========================================================================= *)
(* compiler/backend/proofs/backendProofScript.sml of CakeML v3479: the      *)
(* composition of the correctness theorems of all the compiler phases       *)
(* (compile_correct and its variants).  The theory is in two consecutive    *)
(* parts, backendProof_p1.ml (HOL4 lines 1-2278) and backendProof_p2.ml     *)
(* (2279-4502), the second loading the first.                               *)
(* ========================================================================= *)

needs "compiler/backend/proofs/backendProof_p2.ml";;
