(* ========================================================================= *)
(* holConservative: port of HOL4 candle/standard/syntax/holConservative     *)
(* Script.sml (CakeML v3479).  Functions and proofs about expanding         *)
(* constant definitions.  In v3479 everything after the theory header of    *)
(* the script is one comment (an abandoned development), so the theory has  *)
(* no definitions or theorems (doc/names.tsv: 0 rows).  This file           *)
(* loads the ancestors only, so that the files whose HOL4 theories have     *)
(* holConservative as an ancestor can load it as HOL4 does.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
