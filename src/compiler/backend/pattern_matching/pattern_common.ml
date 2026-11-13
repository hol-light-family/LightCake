(* ========================================================================= *)
(* pattern_common: port of HOL4 compiler/backend/pattern_matching/           *)
(* pattern_commonScript.sml (CakeML v3479).                                  *)
(* Types common to some different parts of the pattern match compiler.       *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* A position describes a path to a sub-term in a term *)

let position_INDUCT,position_RECURSION =
  cake_type "position = EmptyPos | Pos num position";;

(* Results of a pattern match or a multiple pattern match *)

let pmatchResult_INDUCT,pmatchResult_RECURSION =
  cake_type "pmatchResult = PMatchSuccess | PMatchFailure | PTypeFailure";;

(* Pattern matching can return three results :
    - Success, with the number of the right hand side that succeeded
    - MatchFailure, when no branch has matched the value
    - TypeFailure, when there was a type mismatch between the value
      to be matched and the patterns *)

let matchResult_INDUCT,matchResult_RECURSION =
  cake_type "matchResult = MatchSuccess num | MatchFailure";;
