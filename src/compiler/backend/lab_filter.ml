(* ========================================================================= *)
(* lab_filter: port of HOL4 compiler/backend/lab_filterScript.sml            *)
(* (CakeML v3479).                                                           *)
(* This compiler phase removes all Skip instructions (generated from Tick   *)
(* in stackLang).                                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/labLang.ml";;

prioritize_num();;
type_invention_error := true;;

let not_skip_def = cake_def
  `not_skip (l:(A)line) <=>
     match l with Asm (Asmi (asm_Inst asm_Skip)) _ _ -> F | _ -> T`;;

let filter_skip_def = cake_def
  `(filter_skip ([]:((A)sec)list) = []) /\
   (filter_skip (CONS (Section n xs) rest) =
      CONS (Section n (FILTER not_skip xs)) (filter_skip rest))`;;

let filter_skip_ind = cake_ind "filter_skip";;

let filter_skip_MAP = prove
 (CASE_TERM
  `!ls:((A)sec)list.
     filter_skip ls =
     MAP (\x. match x with Section n xs -> Section n (FILTER not_skip xs)) ls`,
  LIST_INDUCT_TAC THEN SIMP[filter_skip_def; MAP] THEN
  CASES_ON `h:(A)sec` THEN SIMP[filter_skip_def; MAP]);;
