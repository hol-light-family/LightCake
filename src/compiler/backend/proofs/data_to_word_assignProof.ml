(* ========================================================================= *)
(* compiler/backend/proofs/data_to_word_assignProofScript.sml of CakeML      *)
(* v3479: correctness of the compilation of dataLang assignments (assign) by *)
(* data_to_word.  The theory is in six consecutive parts,                   *)
(* data_to_word_assignProof_p1.ml (HOL4 lines 1-2889), _p2.ml (2890-5410),   *)
(* _p3.ml (5411-8193), _p4.ml (8194-11023), _p5.ml (11024-14005) and         *)
(* _p6.ml (14006-16966), each loading the one before.                        *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_assignProof_p6.ml";;
