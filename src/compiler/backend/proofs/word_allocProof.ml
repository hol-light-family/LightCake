(* ========================================================================= *)
(* compiler/backend/proofs/word_allocProofScript.sml of CakeML v3479: the   *)
(* correctness of the register allocator word_alloc and of the SSA pass,    *)
(* and the syntactic conventions they establish.  The theory is in two      *)
(* consecutive parts, word_allocProof_p1.ml (HOL4 lines 1-5707) and         *)
(* word_allocProof_p2.ml (5708-11484), the second loading the first.        *)
(* ========================================================================= *)

needs "compiler/backend/proofs/word_allocProof_p2.ml";;
