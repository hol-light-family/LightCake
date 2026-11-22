(* ========================================================================= *)
(* holSyntaxExtra: port of HOL4 candle/standard/syntax/holSyntaxExtraScript  *)
(* .sml (CakeML v3479): some lemmas about the syntactic functions.  The      *)
(* theory is in eight consecutive parts, each loading the one before:        *)
(*   holSyntaxExtra_p1.ml  HOL4 lines    1- 335  type substitution, typing, *)
(*                         alpha-equivalence, subtypes, subterms             *)
(*   holSyntaxExtra_p2.ml  HOL4 lines  336- 965  term ordering and the      *)
(*                         alpha ordering                                    *)
(*   holSyntaxExtra_p3.ml  HOL4 lines  966-1640  hypothesis sets, VSUBST,    *)
(*                         INST_CORE, tyvars and tvars                       *)
(*   holSyntaxExtra_p4.ml  HOL4 lines 1641-2402  equations, type_ok,        *)
(*                         term_ok, de Bruijn terms                          *)
(*   holSyntaxExtra_p5.ml  HOL4 lines 2403-3035  simple substitution and     *)
(*                         instantiation, renaming, fresh names, variant     *)
(*   holSyntaxExtra_p6.ml  HOL4 lines 3036-3400  provable sequents, derived *)
(*                         rules                                             *)
(*   holSyntaxExtra_p7.ml  HOL4 lines 3401-3907  context extensions         *)
(*   holSyntaxExtra_p8.ml  HOL4 lines 3908-4164  types_in, type matching     *)
(* The notes on the rendering are in the header of holSyntaxExtra_p1.ml.     *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra_p1.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p2.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p3.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p4.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p5.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p6.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p7.ml";;
needs "candle/standard/syntax/holSyntaxExtra_p8.ml";;
