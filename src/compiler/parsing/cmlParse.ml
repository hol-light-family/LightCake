(* ========================================================================= *)
(* cmlParse: port of HOL4 compiler/parsing/cmlParseScript.sml (CakeML      *)
(* v3479).  Definition of the overall parsing functions that go from tokens *)
(* to abstract syntax trees.  In other words, these include calls to the    *)
(* functions in ../semantics/cmlPtreeConversion.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's overload cmlpegexec n is written out:                            *)
(*   (\t. peg_exec cmlPEG (cmlPEG_pnt n) t [] NONE [] pegexec_done failed).  *)
(* - HOL4's local type abbreviation M (a parser monad with a type            *)
(*   parameter; names.tsv: cmlParse_M) is written out:                       *)
(*   (token#locs)list->((token#locs)list,A,string)pegresult.                 *)
(* - As in HOL4, destResult is polymorphic in the element type (D) of the   *)
(*   remaining input of its result (the empty list on the right); it is     *)
(*   defined with sem1aux_def (the completed clauses, as HOL4's; cake_def    *)
(*   takes about 130 s on them).                                             *)
(* - The pegresult monad syntax of the script is written out: do x <- m; r  *)
(*   od is pegresult_bind m (\x. r); return a is (\inp. peg_Success inp a    *)
(*   NONE).  The pegresult constructor Success is peg_Success (peg.ml); f $ x *)
(*   is f x; () is one.                                                      *)
(* ========================================================================= *)

needs "compiler/parsing/cmlPEG.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let destResult_def = sem1aux_def
  `(destResult (Result (peg_Success [] x eo):(A,B,C,string)evalcase) =
      peg_Success ([]:D list) x eo) /\
   (destResult (Result (peg_Success (CONS (_,l) _) _ _)) =
      Failure l "Expected to be at EOF") /\
   (destResult (Result (Failure fl fe)) = Failure fl fe) /\
   (destResult _ = Failure unknown_loc "Something catastrophic happened")`;;

let pegresult_bind_def = cake_def
  `pegresult_bind
     (f:(token#locs)list->((token#locs)list,A,string)pegresult)
     (g:A->(token#locs)list->((token#locs)list,B,string)pegresult) =
     \toks. match f toks with
              peg_Success toks' x eo -> g x toks'
            | Failure fl fe -> Failure fl fe`;;

let pegresult_choice_def = cake_def
  `pegresult_choice
     (f:(token#locs)list->((token#locs)list,A,string)pegresult)
     (g:(token#locs)list->((token#locs)list,A,string)pegresult) =
     \toks. match f toks with
              peg_Success toks' x eo -> peg_Success toks' x eo
            | _ -> g toks`;;

let toks_to_loc_def = cake_def
  `(toks_to_loc ([]:(A#locs)list) = unknown_loc) /\
   (toks_to_loc (CONS (h,L) _) = L)`;;

let pegresult_guard_def = cake_def
  `pegresult_guard b =
     \toks:(token#locs)list.
       if b then peg_Success toks one NONE
       else Failure (toks_to_loc toks) "Assert failure"`;;

let optlift_def = cake_def
  `(optlift (NONE:A option) =
      \toks:(token#locs)list. Failure (toks_to_loc toks) "Option = NONE") /\
   (optlift (SOME a) = \toks. peg_Success toks a NONE)`;;

let cmlParseExpr_def = cake_def
  `cmlParseExpr =
     pegresult_bind
       (destResult o (\t. peg_exec cmlPEG (cmlPEG_pnt nE) t [] NONE [] pegexec_done failed))
       (\pts.
        pegresult_bind (optlift (oHD pts)) (\pt.
        pegresult_bind (optlift (ptree_Expr nE pt)) (\ast.
        \inp. peg_Success inp ast NONE)))`;;

let parse_prog_def = cake_def
  `parse_prog =
     pegresult_bind
       (destResult o
        (\t. peg_exec cmlPEG (cmlPEG_pnt nTopLevelDecs) t [] NONE [] pegexec_done failed))
       (\pts.
        pegresult_bind (optlift (oHD pts)) (\pt.
        optlift (ptree_TopLevelDecs pt)))`;;
