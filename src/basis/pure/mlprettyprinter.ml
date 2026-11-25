(* ========================================================================= *)
(* mlprettyprinter: port of HOL4 basis/pure/mlprettyprinterScript.sml        *)
(* (CakeML v3479).  Types and pure functions for pretty printing.            *)
(*                                                                           *)
(* Most of these functions are translated in the first phase of the basis    *)
(* setup so that default pretty-printing (c.f. typeDecToPP) will work from   *)
(* then on.                                                                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The mlstring literal of HOL4 (written with French quotes) is            *)
(*   implode "..." (basis/pure/mlstring.ml); s1 ^ s2 is strcat s1 s2; HOL4   *)
(*   concat is mlstring_concat; mlint toString is toString; mlvector toList  *)
(*   is mlvector_toList; HOL4 ++ is APPEND (left associative in HOL4).       *)
(* - app_list (misc/misc.ml): HOL4 List, Append, Nil are misc_List,          *)
(*   misc_Append, Nil.                                                       *)
(* - word8 is byte, word64 is int64, w2i is ival (hol4/words4.ml).           *)
(* - The functions whose arguments HOL4 leaves unused (pp_exn, pp_unit,      *)
(*   pp_array, pp_ref, pp_word8array) are polymorphic in them, as in HOL4.   *)
(* - The termination proof of escape_str_app_list follows HOL4's (the        *)
(*   measure strlen s - i and str_findi_range).                              *)
(* - Helpers that are not HOL4 theorems have the prefix BAS0AUX_.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/words4.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mlvector.ml";;

type_invention_error := true;;

(* Data for pretty-printing.  The bool indicates if this data needs to be  *)
(* wrapped in parens, if this data is given as an argument to an           *)
(* application.                                                            *)

let pp_data_INDUCT,pp_data_RECURSION = cake_type
  "pp_data = PP_Data bool (mlstring app_list)";;

let pp_token_def = cake_def
  `pp_token s = PP_Data F (misc_List [s])`;;

let pp_fun_def = cake_def
  `pp_fun = pp_token (implode "<fun>")`;;

let pp_unprintable_def = cake_def
  `pp_unprintable s =
     PP_Data F (misc_List [implode "<val of unprintable type "; s;
                           implode ">"])`;;

(* there is a plan to replace this with an impure extensible implementation *)

let pp_exn_def = cake_def
  `pp_exn (e:A) = pp_token (implode "<exn>")`;;

let app_intersperse_def = cake_def
  `(app_intersperse (c:A) [] = Nil) /\
   (app_intersperse c [x] = x) /\
   (app_intersperse c (CONS x (CONS y zs)) =
      misc_Append (misc_Append x (misc_List [c]))
                  (app_intersperse c (CONS y zs)))`;;

let pp_contents_def = cake_def
  `pp_contents (PP_Data _ xs) = xs`;;

let pp_no_parens_def = cake_def
  `pp_no_parens pp = PP_Data F (pp_contents pp)`;;

let app_list_wrap_def = cake_def
  `app_list_wrap (l:A) xs r =
     misc_Append (misc_List [l]) (misc_Append xs (misc_List [r]))`;;

let pp_paren_contents_def = cake_def
  `(pp_paren_contents (PP_Data F xs) = xs) /\
   (pp_paren_contents (PP_Data T xs) =
      app_list_wrap (implode "(") xs (implode ")"))`;;

let pp_paren_tuple_def = cake_def
  `pp_paren_tuple pps =
     PP_Data F (app_list_wrap (implode "(")
       (app_intersperse (implode ", ") (MAP pp_contents pps))
       (implode ")"))`;;

let pp_spaced_block_def = cake_def
  `pp_spaced_block xs =
     PP_Data (LENGTH xs > 1)
       (app_intersperse (implode " ") (MAP pp_paren_contents xs))`;;

let pp_app_block_def = cake_def
  `pp_app_block nm xs = pp_spaced_block (CONS (pp_token nm) xs)`;;

let pp_val_eq_def = cake_def
  `pp_val_eq nm (pp_f:A->pp_data) v ty =
     PP_Data F (misc_Append
       (misc_List [implode "val "; nm; implode " = "])
       (misc_Append (pp_contents (pp_f v))
                    (misc_List [implode ": "; ty; implode "\n"])))`;;

let pp_val_hidden_type_def = cake_def
  `pp_val_hidden_type nm ty =
     PP_Data F (misc_List [implode "val "; nm; implode " <not printable> : ";
                           ty; implode "\n"])`;;

let pp_failure_message_def = cake_def
  `pp_failure_message s =
     PP_Data F (misc_List [implode "<failure: "; s; implode ">\n"])`;;

let pp_list_def = cake_def
  `pp_list (f:A->pp_data) xs =
     PP_Data F (app_list_wrap (implode "[")
       (app_intersperse (implode "; ") (MAP (\x. pp_contents (f x)) xs))
       (implode "]"))`;;

let pp_unit_def = cake_def
  `pp_unit (u:A) = pp_token (implode "()")`;;

let escape_str_app_list_def = cake_def_wf
  `MEASURE (\p:num#mlstring. strlen (SND p) - FST p)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   IMP_RES_TAC str_findi_range THEN ASM_ARITH_TAC)
  `escape_str_app_list i s =
     match str_findi (\c. IS_SOME (char_escape_seq c)) i s with
       NONE -> misc_List [substring s i (strlen s - i)]
     | SOME j ->
         misc_Append
           (misc_List [substring s i (j - i);
                       (match char_escape_seq (strsub s j) with
                          NONE -> implode ""
                        | SOME s -> s)])
           (escape_str_app_list (j + 1) s)`;;

let escape_str_app_list_ind = cake_ind "escape_str_app_list";;

(* explode and substring *)

let BAS0AUX_EL_explode = prove
 (`!s i. EL i (explode s) = strsub s i`,
  MATCH_MP_TAC mlstring_INDUCT THEN REWRITE_TAC[explode_thm; strsub_def]);;

let BAS0AUX_DROP_explode = prove
 (`!s i. i < strlen s ==>
         DROP i (explode s) = CONS (strsub s i) (DROP (i + 1) (explode s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BAS0AUX_EL_explode] THEN
  MATCH_MP_TAC DROP_EL_CONS THEN ASM_REWRITE_TAC[LENGTH_explode]);;

let BAS0AUX_explode_substring = prove
 (`!s i n. i + n <= strlen s ==>
           explode (substring s i n) = TAKE n (DROP i (explode s))`,
  MATCH_MP_TAC mlstring_INDUCT THEN
  SIMP_TAC[substring_def; strlen_def; explode_thm; SEG_DEF]);;

let BAS0AUX_explode_substring_DROP = prove
 (`!s i. explode (substring s i (strlen s - i)) = DROP i (explode s)`,
  MATCH_MP_TAC mlstring_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[substring_def; strlen_def; explode_thm] THEN
  ASM_CASES_TAC `i <= LENGTH (a:string)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i <= n ==> i + n - i <= n`; SEG_DEF] THEN
    MATCH_MP_TAC TAKE_LENGTH_TOO_LONG THEN
    REWRITE_TAC[LENGTH_DROP; LE_REFL];
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN
    ASM_ARITH_TAC]);;

(* HOL4: [local] *)

let findi_map_escape = prove
 (CASE_TERM
  `!P i s. P = IS_SOME o char_escape_seq ==>
     FLAT (MAP char_escaped (DROP i (explode s))) =
     match str_findi P i s with
       NONE -> DROP i (explode s)
     | SOME j ->
         APPEND (APPEND (TAKE (j - i) (DROP i (explode s)))
                        (match char_escape_seq (strsub s j) with
                           NONE -> ""
                         | SOME s -> explode s))
                (FLAT (MAP char_escaped (DROP (j + 1) (explode s))))`,
  MATCH_MP_TAC str_findi_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN SUBST_ALL_TAC th) THEN
  ONCE_REWRITE_TAC[str_findi_def] THEN
  ASM_CASES_TAC `i < strlen s` THENL
   [ASM_SIMP_TAC[BAS0AUX_DROP_explode] THEN
    REWRITE_TAC[MAP; FLAT; o_THM; char_escaped_def] THEN
    QCASES_ON "char_escape_seq (strsub s i)" THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; option_CASE] THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[o_THM; IS_SOME_DEF] THEN DISCH_THEN SUBST1_TAC THEN
      NAMED_CASES_ON "str_findi (IS_SOME o char_escape_seq) (i + 1) s"
        ["";"j"] THEN
      REWRITE_TAC[option_CASE; APPEND] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP str_findi_range) THEN STRIP_TAC THEN
      SUBGOAL_THEN `j - i = SUC (j - (i + 1))` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[TAKE_DEF; NOT_SUC; SUC_SUB1; APPEND]];
      REWRITE_TAC[SUB_REFL; TAKE_0; APPEND]];
    ASM_REWRITE_TAC[option_CASE] THEN
    SUBGOAL_THEN `DROP i (explode s) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN REWRITE_TAC[LENGTH_explode] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[MAP; FLAT]]]);;

let escape_str_app_list_thm = prove
 (`!i s. mlstring_concat (append (escape_str_app_list i s)) =
         implode (FLAT (MAP char_escaped (DROP i (explode s))))`,
  MATCH_MP_TAC escape_str_app_list_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[escape_str_app_list_def] THEN
  MP_TAC(ISPECL [`\c. IS_SOME (char_escape_seq c)`; `i:num`; `s:mlstring`]
    findi_map_escape) THEN
  ANTS_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; DISCH_THEN SUBST1_TAC] THEN
  NAMED_CASES_ON "str_findi (\\c. IS_SOME (char_escape_seq c)) i s"
    ["";"j"] THEN
  REWRITE_TAC[option_CASE] THENL
   [REWRITE_TAC[append_thm; concat_thm; MAP; FLAT; APPEND_NIL;
                BAS0AUX_explode_substring_DROP];
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP str_findi_range) THEN STRIP_TAC THEN
    REWRITE_TAC[append_thm; concat_append] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[strcat_thm; concat_thm; explode_thm; MAP; FLAT; APPEND_NIL] THEN
    ASM_SIMP_TAC[BAS0AUX_explode_substring;
                 ARITH_RULE `i <= j /\ j < n ==> i + j - i <= n`] THEN
    QCASES_ON "char_escape_seq (strsub s j)" THEN
    REWRITE_TAC[option_CASE; explode_thm]]);;

let pp_string_def = cake_def
  `pp_string s =
     PP_Data F (app_list_wrap (implode "\"") (escape_str_app_list 0 s)
                              (implode "\""))`;;

let pp_string_thm = prove
 (`mlstring_concat (append (pp_contents (pp_string s))) = escape_str s`,
  REWRITE_TAC[pp_string_def; pp_contents_def; app_list_wrap_def; append_thm;
              concat_append; escape_str_app_list_thm; escape_str_def; DROP_0] THEN
  REWRITE_TAC[strcat_thm; concat_thm; explode_thm; MAP; FLAT; APPEND_NIL;
              APPEND_ASSOC]);;

let pp_bool_def = cake_def
  `pp_bool b =
     PP_Data F (misc_List [if b then implode "True" else implode "False"])`;;

(* pretty-printers for the pretty-printer types *)

let pp_app_list_def = cake_def
  `(pp_app_list (f:A->pp_data) (misc_List xs) =
      pp_app_block (implode "List") [pp_list f xs]) /\
   (pp_app_list f Nil = pp_token (implode "Nil")) /\
   (pp_app_list f (misc_Append x y) =
      pp_app_block (implode "Append") [pp_app_list f x; pp_app_list f y])`;;

let pp_pp_data_def = cake_def
  `pp_pp_data (PP_Data b d) =
     pp_app_block (implode "PP_Data") [pp_bool b; pp_app_list pp_string d]`;;

let pp_char_def = cake_def
  `pp_char c =
     PP_Data F (misc_List [implode "#\"";
                           (match char_escape_seq c with
                              NONE -> implode [c]
                            | SOME s -> s);
                           implode "\""])`;;

let pp_char_thm = prove
 (`mlstring_concat (append (pp_contents (pp_char c))) = escape_char c`,
  REWRITE_TAC[pp_char_def; pp_contents_def; append_thm; escape_char_def;
              char_escaped_def; concat_thm; MAP; FLAT; APPEND_NIL] THEN
  QCASES_ON "char_escape_seq c" THEN
  REWRITE_TAC[option_CASE; explode_thm; APPEND_ASSOC]);;

let pp_int_def = cake_def
  `pp_int (i:int) = pp_token (toString i)`;;

let pp_word8_def = cake_def
  `pp_word8 (w:byte) = pp_app_block (implode "Word8.fromInt") [pp_int (ival w)]`;;

let pp_word64_def = cake_def
  `pp_word64 (w:int64) =
     pp_app_block (implode "Word64.fromInt") [pp_int (ival w)]`;;

(* these initial pure and useless pps might be replaced later *)

let pp_array_def = cake_def
  `pp_array (f:A) (arr:B) = pp_token (implode "<array>")`;;

let pp_ref_def = cake_def
  `pp_ref (f:A) (r:B) = pp_token (implode "<ref>")`;;

let pp_word8array_def = cake_def
  `pp_word8array (arr:A) = pp_token (implode "<w8array>")`;;

let pp_vector_def = cake_def
  `pp_vector (f:A->pp_data) v =
     pp_app_block (implode "Vector.fromList") [pp_list f (mlvector_toList v)]`;;

(* values of this type should never appear in programs.  it is used to     *)
(* monomorphise some expressions so they can be printed safely.            *)

let default_type_INDUCT,default_type_RECURSION = cake_type
  "default_type = Default_Type";;

let pp_default_type_def = cake_def
  `pp_default_type v =
     match v with
       Default_Type ->
         pp_token (implode "<val of default type: this should be impossible>")`;;

let fromRat_def = cake_def
  `fromRat (n:int,d:num) =
     if d = 1 then misc_List [toString n]
     else misc_List [toString n; implode "/"; toString (&d)]`;;

let fromOption_def = cake_def
  `fromOption (f:A->mlstring app_list) opt =
     match opt with
       NONE -> misc_List [implode "NONE"]
     | SOME x -> misc_Append (misc_List [implode "SOME "]) (f x)`;;
