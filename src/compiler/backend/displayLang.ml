(* ========================================================================= *)
(* displayLang: port of HOL4 compiler/backend/displayLangScript.sml (CakeML  *)
(* v3479).                                                                   *)
(* displayLang is a stepping stone before pretty printing any of the        *)
(* compiler's intermediate languages for inspection by humans.  The design  *)
(* of displayLang is intentionally very simple.  The language supports      *)
(* Tuples, Items (e.g. datatype constructors), and Lists.                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's sExp1_size (the size of an sExp list) is list_size sExp_size;   *)
(*   HOL4 toString on num is num_to_str (mlint); mlstring literals are      *)
(*   implode "...".                                                          *)
(* - In trace_to_json the variables tra and num of the Cons clause are      *)
(*   named tr and n.                                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "basis/pure/mlint.ml";;
needs "compiler/backend/backend_common.ml";;
needs "basis/pure/mlsexp.ml";;

type_invention_error := true;;

let sExp_INDUCT,sExp_RECURSION = cake_type
  "sExp = Item (tra option) mlstring (sExp list)
        | displayLang_String mlstring
        | displayLang_Tuple (sExp list)
        | displayLang_List (sExp list)";;

(* HOL4: val sExp_size_def = fetch "-" "sExp_size_def": type_size_def "sExp" *)

(* display_to_json *)

let trace_to_json_def = cake_def
  `(trace_to_json (backend_common_Cons tr n) =
      Object [(implode "name", jsonLang_String (implode "Cons"));
              (implode "num", jsonLang_String (num_to_str n));
              (implode "trace", trace_to_json tr)]) /\
   (trace_to_json (backend_common_Union tra1 tra2) =
      Object [(implode "name", jsonLang_String (implode "Union"));
              (implode "trace1", trace_to_json tra1);
              (implode "trace2", trace_to_json tra2)]) /\
   (trace_to_json (SourceLoc sr scc er ec) =
      let arr = MAP jsonLang_Int (MAP (\k:num. &k) [sr; scc; er; ec]) in
      Object [(implode "name", jsonLang_String (implode "SourcePos"));
              (implode "pos", Array arr)]) /\
   (trace_to_json backend_common_None = Null)`;;

(* HOL4 sExp1_size es is list_size sExp_size es *)

let MEM_sExp_size = prove
 (`!es a. MEM a es ==> sExp_size a < list_size sExp_size es`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `a:sExp`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Converts a display expression to JSON *)

let display_to_json_def = cake_def_wf
  `MEASURE sExp_size`
  (REWRITE_TAC(WF_REL_THMS) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[type_size_def "sExp"] THEN REWRITE_TAC(size_aux_eqs "sExp") THEN
   FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEM_sExp_size) THEN ASM_ARITH_TAC)
  `(display_to_json (Item tra name es) =
      let es' = MAP display_to_json es in
      let props = [(implode "name", jsonLang_String name);
                   (implode "args", Array es')] in
      let props' = (match tra with
                      NONE -> props
                    | SOME t -> CONS (implode "trace", trace_to_json t) props) in
      Object props') /\
   (display_to_json (displayLang_String s) = jsonLang_String s) /\
   (display_to_json (displayLang_Tuple es) =
      let es' = MAP display_to_json es in
      Object [(implode "isTuple", jsonLang_Bool T); (implode "elements", Array es')]) /\
   (display_to_json (displayLang_List es) = Array (MAP display_to_json es))`;;

let display_to_str_tree_def = cake_def
  `(display_to_str_tree (Item tra name es) =
      Trees (CONS (mlsexp_Str name) (display_to_str_tree_list es))) /\
   (display_to_str_tree (displayLang_String s) = mlsexp_Str s) /\
   (display_to_str_tree (displayLang_Tuple es) =
      if NULL es then mlsexp_Str (implode "()")
      else Trees (display_to_str_tree_list es)) /\
   (display_to_str_tree (displayLang_List es) =
      if NULL es then mlsexp_Str (implode "()")
      else Trees (MAP GrabLine (display_to_str_tree_list es))) /\
   (display_to_str_tree_list [] = []) /\
   (display_to_str_tree_list (CONS x xs) =
      CONS (display_to_str_tree x) (display_to_str_tree_list xs))`;;
