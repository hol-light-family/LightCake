(* ========================================================================= *)
(* compiler/backend/proofs/data_to_word_gcProofScript.sml of CakeML v3479:   *)
(* the state relation of data_to_word and its preservation by the garbage   *)
(* collector, allocation and the data_to_word helper programs.  The theory   *)
(* is in three consecutive parts, data_to_word_gcProof_p1.ml (HOL4 lines     *)
(* 1-3000), _p2.ml (3001-5933) and _p3.ml (5934-8850), each loading the one  *)
(* before.                                                                   *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_gcProof_p3.ml";;
