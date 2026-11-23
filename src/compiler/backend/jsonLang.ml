(* ========================================================================= *)
(* jsonLang: port of HOL4 compiler/backend/jsonLangScript.sml (CakeML        *)
(* v3479).  A datatype for representing JSON objects, and related           *)
(* functions.  A JSON object can be an array of objects, a string, an int,  *)
(* a bool or null, or it can be an object enclosed in braces, in which case *)
(* it can be viewed as a key-value store of names (strings) and JSON        *)
(* objects.                                                                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* Notation (as in the basis files): HOL4 strlit and the mlstring literal   *)
(* syntax are implode "..."; a character literal is CHR n (34 is the double *)
(* quote, 92 the backslash); string ++ is APPEND; toString is toString on   *)
(* int and num_to_str on num; concat is mlstring_concat; EVERY is ALL.      *)
(* The local HOL4 overload ++ = misc$Append is written misc_Append, and     *)
(* misc$List is misc_List.  Names (doc/names.tsv): the                      *)
(* constructors String, Int and Bool are jsonLang_String, jsonLang_Int and  *)
(* jsonLang_Bool.                                                            *)

let obj_INDUCT,obj_RECURSION = cake_type
  "obj = Object ((mlstring#obj) list)
       | Array (obj list)
       | jsonLang_String mlstring
       | jsonLang_Int int
       | jsonLang_Bool bool
       | Null";;

let concat_with_def = cake_def
  `(concat_with [] (c:A app_list) = misc_List []) /\
   (concat_with [s] c = s) /\
   (concat_with (CONS s ss) c = misc_Append s (misc_Append c (concat_with ss c)))`;;

let concat_with_ind = cake_ind "concat_with";;

let printable_def = cake_def
  `printable c <=> ORD c >= 32 /\ ORD c < 127 /\ ~(c = CHR 34) /\ ~(c = CHR 92)`;;

let num_to_hex_digit_def = cake_def
  `num_to_hex_digit n =
     if n < 10 then [CHR (48 + n)] else
     if n < 16 then [CHR (55 + n)] else []`;;

(* HOL4: the definition theorem is named n_rev_hex_digs (no _def) *)

let n_rev_hex_digs = cake_def
  `(n_rev_hex_digs 0 x = []) /\
   (n_rev_hex_digs (SUC n) x =
      APPEND (num_to_hex_digit (x MOD 16)) (n_rev_hex_digs n (x DIV 16)))`;;

let encode_str_def = cake_def
  `encode_str unicode s =
     let s2 = explode s in
     if ALL printable s2 then s
     else mlstring_concat
            (MAP (\c. if printable c then implode [c]
                      else if unicode
                      then implode (APPEND "\\u"
                                     (REVERSE (n_rev_hex_digs 4 (ORD c))))
                      else mlstring_concat [implode "\\"; num_to_str (ORD c)])
                 s2)`;;

(* The termination relation: HOL4 proves termination automatically.  The  *)
(* definition is made with MAP (\m. mem_to_string m) mems and              *)
(* MAP (\ob. json_to_mlstring ob) obs (the kit's mutual recursion does not *)
(* accept a defined function that occurs bare) and the clauses are then    *)
(* eta-reduced to HOL4's MAP mem_to_string mems and MAP json_to_mlstring   *)
(* obs.                                                                      *)

let json_to_mlstring_def = CONV_RULE (ONCE_DEPTH_CONV ETA_CONV) (cake_def_wf
  `MEASURE (\x:obj + (mlstring#obj).
              sum_CASE x (\ob. obj_size ob)
                         (\p. pair_size mlstring_size obj_size p))`
  TERM_TAC
  `(json_to_mlstring obj =
      match obj with
        Object mems ->
          misc_Append
            (misc_Append (misc_List [implode "{"])
               (concat_with (MAP (\m. mem_to_string m) mems)
                  (misc_List [implode ","])))
            (misc_List [implode "}"])
      | Array obs ->
          misc_Append
            (misc_Append (misc_List [implode "["])
               (concat_with (MAP (\ob. json_to_mlstring ob) obs)
                  (misc_List [implode ","])))
            (misc_List [implode "]"])
      | jsonLang_String s ->
          misc_List [implode "\""; encode_str T s; implode "\""]
      | jsonLang_Int i -> misc_List [toString i]
      | jsonLang_Bool b ->
          if b then misc_List [implode "true"] else misc_List [implode "false"]
      | Null -> misc_List [implode "null"]) /\
   (mem_to_string n_obj =
      match n_obj with
        (n,obj) ->
          misc_Append (misc_List [implode "\""; n; implode "\":"])
                      (json_to_mlstring obj))`);;

let json_to_mlstring_ind = cake_ind "json_to_mlstring";;
