(* ========================================================================= *)
(* mlsexp: port of HOL4 basis/pure/mlsexpScript.sml (CakeML v3479).          *)
(* Definition of a simple mlstring-based s-expression, includes parsing and  *)
(* pretty printing for these s-expressions.                                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definition of s-expression                                                *)
(* ------------------------------------------------------------------------- *)

let sexp_INDUCT,sexp_RECURSION = cake_type "sexp = Atom mlstring | Expr (sexp list)";;

(* ------------------------------------------------------------------------- *)
(* Lexing + parsing                                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4: token *)

let mlsexp_token_INDUCT,mlsexp_token_RECURSION =
  cake_type "mlsexp_token = OPEN | CLOSE | SYMBOL mlstring";;

(* Functions may not consume the entire input (string), so they always      *)
(* return the rest of the string, independent of success or failure.        *)
(* HOL4: Type result[local] = (A # string) + (B # string), written out.     *)
(* HOL4 character literals are written CHR n (string4.ml): the double quote *)
(* is CHR 34, the backslash CHR 92, the digit 0 CHR 48, the letters n, r, t *)
(* CHR 110, 114, 116, the parentheses CHR 40 and CHR 41, the space CHR 32,  *)
(* newline, carriage return and tab CHR 10, CHR 13 and CHR 9, NUL CHR 0.    *)

let read_string_aux_def = cake_def
  `(read_string_aux [] (acc:string) =
      INL (implode "read_string_aux: unterminated string literal", []):
      (mlstring#string)+(mlstring#string)) /\
   (read_string_aux (CONS c rest) acc =
      if c = CHR 34 then INR (implode (REVERSE acc), rest) else
      if c = CHR 92 then
        (match rest with
           [] -> read_string_aux rest acc
         | CONS e rest ->
             (if e = CHR 92 then read_string_aux rest (CONS (CHR 92) acc) else
              if e = CHR 34 then read_string_aux rest (CONS (CHR 34) acc) else
              if e = CHR 48 then read_string_aux rest (CONS (CHR 0) acc) else
              if e = CHR 110 then read_string_aux rest (CONS (CHR 10) acc) else
              if e = CHR 114 then read_string_aux rest (CONS (CHR 13) acc) else
              if e = CHR 116 then read_string_aux rest (CONS (CHR 9) acc) else
                INL (implode "read_string_aux: unrecognised escape", rest)))
      else
        read_string_aux rest (CONS c acc))`;;

let read_string_aux_ind = cake_ind "read_string_aux";;

(* Returns the string until a closing quote, and the rest of the input.     *)
(* Fails with an error message if closing quotes are missing or an          *)
(* unrecognised escape sequence occurs.  HOL4: read_string                  *)

let mlsexp_read_string_def = cake_def
  `mlsexp_read_string (input:string) = read_string_aux input []`;;

let read_string_aux_length = prove
 (`!input acc.
     read_string_aux input acc = INR (s, rest) ==> LENGTH rest <= LENGTH input`,
  MATCH_MP_TAC read_string_aux_ind THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[read_string_aux_def] THEN
  EVERY_CASE_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN GVS[] THEN
  ASM_ARITH_TAC);;

let read_string_length = prove
 (`mlsexp_read_string input = INR (s, rest) ==> LENGTH rest <= LENGTH input`,
  RW[mlsexp_read_string_def] THEN IMP_RES_TAC read_string_aux_length THEN
  ASM_REWRITE_TAC[]);;

(* Returns the string until a closing parenthesis or whitespace, and the    *)
(* rest of the input.  See usage in lex_aux as to why a non-aux function    *)
(* is exposing an accumulator.                                              *)

let read_symbol_def = cake_def
  `(read_symbol [] (acc:string) = (implode (REVERSE acc), []:string)) /\
   (read_symbol (CONS c cs) acc =
      if c = CHR 41 \/ isSpace c then (implode (REVERSE acc), CONS c cs)
      else read_symbol cs (CONS c acc))`;;

let read_symbol_length = prove
 (`!input acc.
     read_symbol input acc = (s, rest) ==> LENGTH rest <= LENGTH input`,
  LIST_INDUCT_TAC THEN SIMP[read_symbol_def] THEN
  RW[read_symbol_def] THEN RES_TAC THEN GVS[] THEN ASM_ARITH_TAC);;

(* By tracking the depth, we can ensure we only lex one S-expression at a  *)
(* time.  HOL4: lex_aux; HOL4's measure on (_, input, _) is written with   *)
(* FST and SND.  In the last case c is not a closing parenthesis or a      *)
(* space, so read_symbol (c::cs) [] is equivalent to read_symbol cs [c]     *)
(* (an implementation detail relevant in the context of streams).          *)

let mlsexp_lex_aux_def = cake_def_wf
  `measure (\p:num#string#mlsexp_token list. LENGTH (FST (SND p)))`
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE (WF_REL_THMS @ [FST; SND])) THEN
   REWRITE_TAC(WF_REL_THMS @ [FST; SND; LENGTH]) THEN
   IMP_RES_TAC read_string_length THEN IMP_RES_TAC read_symbol_length THEN
   IMP_RES_TAC (ONCE_REWRITE_RULE[EQ_SYM_EQ] read_string_length) THEN
   IMP_RES_TAC (ONCE_REWRITE_RULE[EQ_SYM_EQ] read_symbol_length) THEN
   ASM_ARITH_TAC)
  `(mlsexp_lex_aux depth [] acc =
      (if depth = 0 then INR (acc, [])
       else INL (implode "lex_aux: missing closing parenthesis", [])):
      (mlstring#string)+(mlsexp_token list#string)) /\
   (mlsexp_lex_aux depth (CONS c cs) acc =
      if isSpace c then mlsexp_lex_aux depth cs acc
      else if c = CHR 40 then mlsexp_lex_aux (depth + 1) cs (CONS OPEN acc)
      else if c = CHR 41 then
        (if depth = 0
         then INL (implode "lex_aux: too many closing parenthesis", cs)
         else if depth = 1 then INR (CONS CLOSE acc, cs)
         else mlsexp_lex_aux (depth - 1) cs (CONS CLOSE acc))
      else if c = CHR 34 then
        (match mlsexp_read_string cs with
           INL (msg, rest) -> INL (msg, rest)
         | INR (s, rest) ->
             if depth = 0 then INR ([SYMBOL s], rest)
             else mlsexp_lex_aux depth rest (CONS (SYMBOL s) acc))
      else
        (match read_symbol cs [c] with
           (s, rest) ->
             if depth = 0 then INR ([SYMBOL s], rest)
             else mlsexp_lex_aux depth rest (CONS (SYMBOL s) acc)))`;;

let mlsexp_lex_aux_ind = cake_ind "mlsexp_lex_aux";;

let lex_aux_length = prove
 (`!depth input acc e rest.
     mlsexp_lex_aux depth input acc = INR (e,rest) ==> LENGTH rest <= LENGTH input`,
  MATCH_MP_TAC mlsexp_lex_aux_ind THEN RW[] THEN
  GVS(mlsexp_lex_aux_def :: all_case_eqs()) THEN
  IMP_RES_TAC read_string_length THEN GVS[] THEN
  IMP_RES_TAC read_symbol_length THEN GVS[] THEN ASM_ARITH_TAC);;

(* Tokenizes (at most) one S-expression, and returns the rest of the input. *)
(* Fails with an error message if parentheses are unbalanced or            *)
(* read_string fails on a string literal.                                   *)

let lex_def = cake_def
  `lex (input:string) = mlsexp_lex_aux 0 input []`;;

let lex_IMP_LENGTH_LESS = prove
 (`!input x rest.
     lex input = INR (x,rest) ==> LENGTH rest < LENGTH input \/ x = []`,
  SIMP(lex_def :: all_case_eqs()) THEN REPEAT GEN_TAC THEN
  CASES_ON `input:string` THEN
  FS(mlsexp_lex_aux_def :: all_case_eqs()) THEN
  REPEAT STRIP_TAC THEN GVS[] THEN TRY DISJ1_TAC THEN
  IMP_RES_TAC lex_aux_length THEN
  IMP_RES_TAC read_string_length THEN
  IMP_RES_TAC read_symbol_length THEN ASM_ARITH_TAC);;

(* Character facts for the proofs (HOL4 uses EVAL for them): PURE3AUX_     *)
(* CHR_CONV turns CHR of a numeral into the character literal of HOL Light *)
(* (ASCII b7 .. b0, as in string literals), PURE3AUX_ISSPACE_CONV decides  *)
(* isSpace of a literal; PURE3AUX_CHAR_SIMPS has these facts for the       *)
(* characters that occur in this file, and character injectivity.         *)

let PURE3AUX_CHR_CONV tm =
  match tm with
    Comb(Const("CHR",_),n) when is_numeral n ->
      (REWR_CONV CHR_DEF THENC NUM_REDUCE_CONV) tm
  | _ -> failwith "PURE3AUX_CHR_CONV";;

let PURE3AUX_ISSPACE_CONV tm =
  match tm with
    Comb(Const("isSpace",_),c) when can dest_char c ->
      (REWR_CONV isSpace_def THENC REWRITE_CONV[ORD_DEF; BITVAL_CLAUSES] THENC
       NUM_REDUCE_CONV) tm
  | _ -> failwith "PURE3AUX_ISSPACE_CONV";;

let PURE3AUX_CHR_LITS =
  map (fun n -> PURE3AUX_CHR_CONV (mk_comb(`CHR`,mk_small_numeral n)))
      [0;9;10;13;32;34;40;41;48;92;110;114;116];;

let PURE3AUX_ISSPACE_LITS =
  map (fun th -> PURE3AUX_ISSPACE_CONV (mk_comb(`isSpace`,rhs(concl th))))
      PURE3AUX_CHR_LITS;;

let PURE3AUX_CHAR_SIMPS =
  PURE3AUX_CHR_LITS @ PURE3AUX_ISSPACE_LITS @ [injectivity "char"];;

(* HOL4 proves the local tests of this file by EVAL.  Here the evaluator   *)
(* PURE3AUX_EVAL_CONV is the call-by-value conversion of HOL Light         *)
(* (compute.ml) with the equations of this file, added as they are         *)
(* defined, and the character conversions above.                           *)

let PURE3AUX_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  Compute.add_conv (`CHR`,1,PURE3AUX_CHR_CONV) cs;
  Compute.add_conv (`isSpace`,1,PURE3AUX_ISSPACE_CONV) cs;
  Compute.add_conv (`(=):char->char->bool`,2,CHAR_EQ_CONV) cs;
  Compute.add_thms
    [REVERSE; APPEND; list_CASE; sum_CASE; pair_CASE; LET_END_DEF; lex_def;
     mlsexp_lex_aux_def; mlsexp_read_string_def; read_string_aux_def;
     read_symbol_def] cs;
  cs;;

let PURE3AUX_EVAL_CONV tm = Compute.CBV_CONV PURE3AUX_cs tm;;

let test_lex = prove
 (`lex " 1 2   3 " = INR ([SYMBOL (implode "1")], " 2   3 ") /\
   lex "\"\n \" 2" = INR ([SYMBOL (implode "\n ")], " 2") /\
   lex " (1 2) 3 " =
     INR ([CLOSE; SYMBOL (implode "2"); SYMBOL (implode "1"); OPEN], " 3 ") /\
   lex " (1 2) ) " =
     INR ([CLOSE; SYMBOL (implode "2"); SYMBOL (implode "1"); OPEN], " ) ") /\
   lex " (1 2    " = INL (implode "lex_aux: missing closing parenthesis", "") /\
   lex " ) (1 2) " =
     INL (implode "lex_aux: too many closing parenthesis", " (1 2) ")`,
  REPEAT CONJ_TAC THEN CONV_TAC(LAND_CONV PURE3AUX_EVAL_CONV) THEN REFL_TAC);;

let parse_aux_def = cake_def
  `(parse_aux [] (xs:sexp list) (s:(sexp list)list) = xs) /\
   (parse_aux (CONS CLOSE rest) xs s = parse_aux rest [] (CONS xs s)) /\
   (parse_aux (CONS OPEN rest) xs s =
      (match s with
         [] -> parse_aux rest xs s
       | CONS y ys -> parse_aux rest (CONS (Expr xs) y) ys)) /\
   (parse_aux (CONS (SYMBOL sy) rest) xs s = parse_aux rest (CONS (Atom sy) xs) s)`;;

(* Parses (at most) one S-expression, and returns the rest of the input.    *)
(* Fails exactly when lexing fails.  HOL4: parse                            *)

let mlsexp_parse_def = cake_def
  `mlsexp_parse (input:string) =
     (match lex input with
        INL (msg, rest) -> INL (msg, rest)
      | INR (rev_toks, rest) ->
          (match parse_aux rev_toks [] [] with
             [] -> INL (implode "parse: empty input", rest)
           | CONS v _ -> INR (v, rest))):(mlstring#string)+(sexp#string)`;;

let parse_IMP_LENGTH_LESS = prove
 (`!input x rest. mlsexp_parse input = INR (x,rest) ==> LENGTH rest < LENGTH input`,
  RW(mlsexp_parse_def :: all_case_eqs()) THEN
  IMP_RES_TAC lex_IMP_LENGTH_LESS THEN
  GVS[parse_aux_def]);;

let parse_space = prove
 (`mlsexp_parse (CONS (CHR 10) xs) = mlsexp_parse xs`,
  SIMP[mlsexp_parse_def; lex_def] THEN
  ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN
  REWRITE_TAC PURE3AUX_CHAR_SIMPS);;

let () = Compute.add_thms [parse_aux_def; mlsexp_parse_def] PURE3AUX_cs;;

let test_parse = prove
 (`mlsexp_parse " 1 2 3 " = INR (Atom (implode "1"), " 2 3 ") /\
   mlsexp_parse "(1 2 3)" =
     INR (Expr [Atom (implode "1"); Atom (implode "2"); Atom (implode "3")], "") /\
   mlsexp_parse "(()) ()" = INR (Expr [Expr []], " ()")`,
  REPEAT CONJ_TAC THEN CONV_TAC(LAND_CONV PURE3AUX_EVAL_CONV) THEN REFL_TAC);;

(* Function for parsing in the style of the Standard ML basis library.     *)
(* HOL4: fromString                                                         *)

let mlsexp_fromString_def = cake_def
  `mlsexp_fromString (input:mlstring) =
     (match mlsexp_parse (explode input) with
        INL _ -> NONE
      | INR (se, _) -> SOME se)`;;

(* ------------------------------------------------------------------------- *)
(* Pretty printing of str_tree                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4: constructor Str *)

let str_tree_INDUCT,str_tree_RECURSION =
  cake_type "str_tree = mlsexp_Str mlstring | Trees (str_tree list) | GrabLine str_tree";;

(* HOL4: constructors String and Append *)

let pretty_INDUCT,pretty_RECURSION =
  cake_type ("pretty = Parenthesis pretty | mlsexp_String mlstring | " ^
             "mlsexp_Append pretty bool pretty | Size num pretty");;

let newlines_def = cake_def
  `(newlines [] = mlsexp_String (implode "")) /\
   (newlines [x] = x) /\
   (newlines (CONS x xs) = mlsexp_Append x T (newlines xs))`;;

let v2pretty_def = cake_def
  `(v2pretty v =
      match v with
        mlsexp_Str s -> mlsexp_String s
      | GrabLine w -> Size 100000 (v2pretty w)
      | Trees l -> Parenthesis (newlines (vs2pretty l))) /\
   (vs2pretty vs =
      match vs with
        [] -> []
      | CONS v vs -> CONS (v2pretty v) (vs2pretty vs))`;;

(* HOL4: get_size *)

let mlsexp_get_size_def = cake_def
  `(mlsexp_get_size (Size n x) = n) /\
   (mlsexp_get_size (mlsexp_Append x _ y) =
      mlsexp_get_size x + mlsexp_get_size y + 1) /\
   (mlsexp_get_size (Parenthesis x) = mlsexp_get_size x + 2) /\
   (mlsexp_get_size _ = 0)`;;

let get_next_size_def = cake_def
  `(get_next_size (Size n x) = n) /\
   (get_next_size (mlsexp_Append x _ y) = get_next_size x) /\
   (get_next_size (Parenthesis x) = get_next_size x + 2) /\
   (get_next_size _ = 0)`;;

(* HOL4: annotate; the Append case has the comment                         *)
(* Size (get_size b1 + get_size b2 + 1) before its result.  The variables *)
(* of the clauses of one definition share their types in HOL Light: the    *)
(* boolean n of the Append clause is n' here (b' in smart_remove).          *)

let mlsexp_annotate_def = cake_def
  `(mlsexp_annotate (mlsexp_String s) = Size (strlen s) (mlsexp_String s)) /\
   (mlsexp_annotate (Parenthesis b) =
      (let b = mlsexp_annotate b in
         Size (mlsexp_get_size b + 2) (Parenthesis b))) /\
   (mlsexp_annotate (mlsexp_Append b1 n' b2) =
      (let b1 = mlsexp_annotate b1 in
       let b2 = mlsexp_annotate b2 in
         mlsexp_Append b1 n' b2)) /\
   (mlsexp_annotate (Size n b) = Size n (mlsexp_annotate b))`;;

let remove_all_def = cake_def
  `(remove_all (Parenthesis v) = Parenthesis (remove_all v)) /\
   (remove_all (mlsexp_String v1) = mlsexp_String v1) /\
   (remove_all (mlsexp_Append v2 _ v3) =
      mlsexp_Append (remove_all v2) F (remove_all v3)) /\
   (remove_all (Size v4 v5) = remove_all v5)`;;

let smart_remove_def = cake_def
  `(smart_remove i k (Size n b) =
      (if k + n < 70 then remove_all b else smart_remove i k b)) /\
   (smart_remove i k (Parenthesis v) =
      Parenthesis (smart_remove (i + 1) (k + 1) v)) /\
   (smart_remove i k (mlsexp_String v1) = mlsexp_String v1) /\
   (smart_remove i k (mlsexp_Append v2 b' v3) =
      let n2 = mlsexp_get_size v2 in
      let n3 = get_next_size v3 in
        if k + n2 + n3 < 50 then
          mlsexp_Append (smart_remove i k v2) F (smart_remove i (k + n2) v3)
        else
          mlsexp_Append (smart_remove i k v2) T (smart_remove i i v3))`;;

(* HOL4: flatten *)

let mlsexp_flatten_def = cake_def
  `(mlsexp_flatten indent (Size n p) s = mlsexp_flatten indent p s) /\
   (mlsexp_flatten indent (Parenthesis p) s =
      CONS (implode "(")
           (mlsexp_flatten (mlstring_concat [indent; implode "   "]) p
                           (CONS (implode ")") s))) /\
   (mlsexp_flatten indent (mlsexp_String t) s = CONS t s) /\
   (mlsexp_flatten indent (mlsexp_Append p1 b p2) s =
      mlsexp_flatten indent p1
        (CONS (if b then indent else implode " ") (mlsexp_flatten indent p2 s)))`;;

let str_tree_to_strs_def = cake_def
  `str_tree_to_strs end v =
     mlsexp_flatten (implode "\n") (smart_remove 0 0 (mlsexp_annotate (v2pretty v)))
                    [end]`;;

let () =
  Compute.add_thms
    [str_tree_to_strs_def; mlsexp_flatten_def; smart_remove_def; remove_all_def;
     mlsexp_annotate_def; mlsexp_get_size_def; get_next_size_def; v2pretty_def;
     newlines_def; case_def "str_tree"; strlen_def; LENGTH; mlstring_concat_def;
     mlstring_case_def; MAP; FLAT] PURE3AUX_cs;;

let test1_str_tree_to_strs = prove
 (`mlstring_concat (str_tree_to_strs (implode "")
     (Trees [mlsexp_Str (implode "hello"); mlsexp_Str (implode "there")])) =
   implode "(hello there)"`,
  CONV_TAC(LAND_CONV PURE3AUX_EVAL_CONV) THEN REFL_TAC);;

let test2_str_tree_to_strs = prove
 (`mlstring_concat (str_tree_to_strs (implode "")
     (Trees [mlsexp_Str (implode "test"); GrabLine (mlsexp_Str (implode "hi"));
             GrabLine (mlsexp_Str (implode "there"))])) =
   implode "(test\n   hi\n   there)"`,
  CONV_TAC(LAND_CONV PURE3AUX_EVAL_CONV) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Pretty printing of sexp                                                   *)
(* ------------------------------------------------------------------------- *)

let is_safe_char_def = cake_def
  `is_safe_char c <=> ~MEM c "()\"\000" /\ ~isSpace c`;;

let str_every_def = cake_def
  `str_every p n s =
     if n = 0 then T else
       p (strsub s (n - 1)) /\ str_every p (n - 1:num) s`;;

let make_str_safe_def = cake_def
  `make_str_safe s =
     if s = implode "" then implode "\"\"" else
     if str_every is_safe_char (strlen s) s then s else escape_str s`;;

let sexp2tree_def = cake_def
  `(sexp2tree (Atom s) = mlsexp_Str (make_str_safe s)) /\
   (sexp2tree (Expr l) = Trees (sexp2trees l)) /\
   (sexp2trees [] = []) /\
   (sexp2trees (CONS v vs) = CONS (sexp2tree v) (sexp2trees vs))`;;

(* HOL4 app_list constructors List and Append are misc_List, misc_Append *)

let sexp_to_app_list_def = cake_def
  `(sexp_to_app_list (Atom s) = misc_List [make_str_safe s]) /\
   (sexp_to_app_list (Expr l) =
      misc_Append (misc_List [implode "("])
                  (misc_Append (sexps_to_app_list l) (misc_List [implode ")"]))) /\
   (sexps_to_app_list [] = misc_List []) /\
   (sexps_to_app_list (CONS v vs) =
      if NULL vs then sexp_to_app_list v
      else misc_Append (sexp_to_app_list v)
                       (misc_Append (misc_List [implode " "]) (sexps_to_app_list vs)))`;;

let sexp_to_string_def = cake_def
  `sexp_to_string s = mlstring_concat (append (sexp_to_app_list s))`;;

let sexp_to_pretty_string_def = cake_def
  `sexp_to_pretty_string s =
     mlstring_concat (str_tree_to_strs (implode "\n") (sexp2tree s))`;;

(* ------------------------------------------------------------------------- *)
(* Proofs relating parsing with pretty printing                              *)
(* ------------------------------------------------------------------------- *)

let to_tokens_def = cake_def
  `(to_tokens (Atom a) = [SYMBOL a]) /\
   (to_tokens (Expr xs) =
      APPEND (APPEND [OPEN] (FLAT (MAP (\x. to_tokens x) xs))) [CLOSE])`;;

let to_tokens_ind = cake_ind "to_tokens";;

let parse_aux_to_tokens_lemma = prove
 (`!x xs s rest.
     parse_aux (APPEND (REVERSE (to_tokens x)) rest) xs s =
     parse_aux rest (CONS x xs) s`,
  MATCH_MP_TAC to_tokens_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[to_tokens_def; REVERSE; APPEND; parse_aux_def];
    X_GEN_TAC `l:sexp list` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!rest ys s.
        parse_aux (APPEND (REVERSE (FLAT (MAP (\x. to_tokens x) l))) rest) ys s =
        parse_aux rest (APPEND l ys) s`
     ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN SPEC_TAC(`l:sexp list`,`l:sexp list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; REVERSE; APPEND; MEM] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN
       `!xs s rest. parse_aux (APPEND (REVERSE (to_tokens h)) rest) xs s =
                    parse_aux rest (CONS h xs) s`
       ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REVERSE_APPEND; GSYM APPEND_ASSOC];
      REWRITE_TAC[to_tokens_def; REVERSE_APPEND; REVERSE; APPEND;
                  GSYM APPEND_ASSOC] THEN
      SIMP[parse_aux_def; APPEND_NIL]]]);;

let parse_aux_to_tokens_thm = prove
 (`parse_aux (REVERSE (to_tokens x)) [] [] = [x]`,
  MP_TAC(SPECL [`x:sexp`; `[]:sexp list`; `[]:(sexp list)list`;
                `[]:mlsexp_token list`] parse_aux_to_tokens_lemma) THEN
  REWRITE_TAC[APPEND_NIL; parse_aux_def]);;

let str_every_thm = prove
 (`!P i m. str_every P i m /\ i <= strlen m ==> !k. k < i ==> P (EL k (explode m))`,
  GEN_TAC THEN INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[str_every_def] THEN REWRITE_TAC[NOT_SUC; SUC_SUB1; LT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM PURE1AUX_strsub_EL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:mlstring`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM PURE1AUX_strsub_EL] THEN ASM_MESON_TAC[]);;

let read_symbol_thm = prove
 (`!t s acc.
     ALL is_safe_char t /\ (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
     read_symbol (APPEND t s) acc = (implode (APPEND (REVERSE acc) t), s)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ALL; APPEND; APPEND_NIL] THEN
    CASES_ON `s:string` THEN REWRITE_TAC[read_symbol_def; HD; NOT_CONS_NIL] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[ALL; APPEND] THEN STRIP_TAC THEN
    REWRITE_TAC[read_symbol_def] THEN
    SUBGOAL_THEN `~(h = CHR 41 \/ isSpace h)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `is_safe_char h` THEN REWRITE_TAC[is_safe_char_def; MEM] THEN
      REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:string`; `CONS (h:char) acc`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND]]);;

let read_string_aux_thm = prove
 (`!xs s acc.
     read_string_aux (APPEND (APPEND (FLAT (MAP char_escaped xs)) "\"") s) acc =
     INR (implode (APPEND (REVERSE acc) xs), s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; GSYM APPEND_ASSOC; APPEND] THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[read_string_aux_def] THEN
    REWRITE_TAC(APPEND_NIL :: PURE3AUX_CHAR_SIMPS);
    POP_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM APPEND_ASSOC; APPEND]) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[char_escaped_def; char_escape_seq_def] THEN
    REPEAT COND_CASES_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE PURE3AUX_CHAR_SIMPS) THEN
    ASM_REWRITE_TAC[option_CASE; explode_thm; APPEND] THEN
    ONCE_REWRITE_TAC[read_string_aux_def] THEN
    ASM_REWRITE_TAC(list_CASE :: PURE3AUX_CHAR_SIMPS) THEN
    ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND]]);;

let lex_aux_make_str_safe = prove
 (CASE_TERM
  `!m s ts depth.
     (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\
     (depth = 0 ==> ts = []) ==>
     mlsexp_lex_aux depth (APPEND (match make_str_safe m with implode x -> x) s) ts =
     (if depth = 0 then INR (CONS (SYMBOL m) ts, s)
      else mlsexp_lex_aux depth s (CONS (SYMBOL m) ts))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_str_safe_def] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[mlstring_case_def; APPEND] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
    REWRITE_TAC[mlsexp_read_string_def] THEN
    ONCE_REWRITE_TAC[read_string_aux_def] THEN
    REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN REWRITE_TAC[sum_CASE; pair_CASE; REVERSE] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `ALL is_safe_char (explode m)` MP_TAC THENL
     [REWRITE_TAC[EVERY_EL; LENGTH_explode] THEN
      MATCH_MP_TAC str_every_thm THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `~(m = implode "")` THEN
    MP_TAC(SPEC `m:mlstring` (cases "mlstring")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[mlstring_case_def; explode_thm; injectivity "mlstring"] THEN
    CASES_ON `a:string` THEN REWRITE_TAC[ALL; APPEND] THEN STRIP_TAC THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~isSpace a0 /\ ~(a0 = CHR 40) /\ ~(a0 = CHR 41) /\ ~(a0 = CHR 34)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `is_safe_char a0` THEN REWRITE_TAC[is_safe_char_def; MEM] THEN
      REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`a1:string`; `s:string`; `[a0:char]`] read_symbol_thm) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[pair_CASE; REVERSE; APPEND] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[escape_str_def; mlstring_case_def; GSYM APPEND_ASSOC; APPEND] THEN
    ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
    REWRITE_TAC[mlsexp_read_string_def] THEN
    MP_TAC (SPECL [`explode m`; `s:string`; `[]:string`] read_string_aux_thm) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[sum_CASE; pair_CASE; implode_explode] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let flatten_acc = prove
 (`!x indent s. mlsexp_flatten indent x s = APPEND (mlsexp_flatten indent x []) s`,
  MATCH_MP_TAC pretty_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[mlsexp_flatten_def] THEN
    FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
    REWRITE_TAC[mlsexp_flatten_def; APPEND];
    DISCH_THEN(fun th -> REPEAT GEN_TAC THEN REWRITE_TAC[mlsexp_flatten_def] THEN
                         ONCE_REWRITE_TAC[CONJUNCT1 th] THEN
                         ONCE_REWRITE_TAC[CONJUNCT2 th]) THEN
    REWRITE_TAC[APPEND_NIL; APPEND; GSYM APPEND_ASSOC];
    DISCH_THEN(fun th -> REWRITE_TAC[mlsexp_flatten_def] THEN MATCH_ACCEPT_TAC th)]);;

let lex_aux_spaces = prove
 (`!t rest ts depth.
     ALL isSpace t ==>
     mlsexp_lex_aux depth (APPEND t rest) ts = mlsexp_lex_aux depth rest ts`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; APPEND] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN ASM_SIMP_TAC[]);;

(* Local helpers for lex_aux_sexp2tree (HOL4 does these steps by simp). *)

let PURE3AUX_explode_concat = prove
 (`!l. explode (mlstring_concat l) = FLAT (MAP explode l)`,
  REWRITE_TAC[concat_thm; explode_thm]);;

let PURE3AUX_mlstring_case_id = prove
 (CASE_TERM `!t. (match t with implode x -> x) = explode t`,
  MATCH_MP_TAC mlstring_INDUCT THEN REWRITE_TAC[mlstring_case_def; explode_thm]);;

let PURE3AUX_flatten_Append = prove
 (`!indent p1 b p2.
     explode (mlstring_concat (mlsexp_flatten indent (mlsexp_Append p1 b p2) [])) =
     APPEND (explode (mlstring_concat (mlsexp_flatten indent p1 [])))
       (APPEND (explode (if b then indent else implode " "))
               (explode (mlstring_concat (mlsexp_flatten indent p2 []))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlsexp_flatten_def] THEN
  ONCE_REWRITE_TAC[flatten_acc] THEN
  REWRITE_TAC[PURE3AUX_explode_concat; MAP_APPEND; FLAT_APPEND; MAP; FLAT;
              APPEND_NIL]);;

let PURE3AUX_flatten_Parenthesis = prove
 (`!indent p.
     explode (mlstring_concat (mlsexp_flatten indent (Parenthesis p) [])) =
     APPEND "("
       (APPEND (explode (mlstring_concat
                  (mlsexp_flatten (mlstring_concat [indent; implode "   "]) p [])))
               ")")`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlsexp_flatten_def] THEN
  ONCE_REWRITE_TAC[flatten_acc] THEN
  REWRITE_TAC[PURE3AUX_explode_concat; MAP_APPEND; FLAT_APPEND; MAP; FLAT;
              APPEND_NIL; explode_thm]);;

let PURE3AUX_flatten_String = prove
 (`!indent t.
     explode (mlstring_concat (mlsexp_flatten indent (mlsexp_String t) [])) =
     explode t`,
  REWRITE_TAC[mlsexp_flatten_def; PURE3AUX_explode_concat; MAP; FLAT; APPEND_NIL]);;

let PURE3AUX_v2pretty_thms = prove
 (`(!s. v2pretty (mlsexp_Str s) = mlsexp_String s) /\
   (!l. v2pretty (Trees l) = Parenthesis (newlines (vs2pretty l))) /\
   (!w. v2pretty (GrabLine w) = Size 100000 (v2pretty w)) /\
   vs2pretty [] = [] /\
   (!v vs. vs2pretty (CONS v vs) = CONS (v2pretty v) (vs2pretty vs))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [v2pretty_def] THEN
  REWRITE_TAC[case_def "str_tree"; list_CASE]);;

let PURE3AUX_tree_Atom = prove
 (`!a m n.
     smart_remove m n (mlsexp_annotate (v2pretty (sexp2tree (Atom a)))) =
     mlsexp_String (make_str_safe a) /\
     remove_all (mlsexp_annotate (v2pretty (sexp2tree (Atom a)))) =
     mlsexp_String (make_str_safe a)`,
  REWRITE_TAC[sexp2tree_def; PURE3AUX_v2pretty_thms; mlsexp_annotate_def;
              smart_remove_def; remove_all_def; COND_ID]);;

let PURE3AUX_tree_Expr = prove
 (`!xs m n.
     smart_remove m n (mlsexp_annotate (v2pretty (sexp2tree (Expr xs)))) =
     Parenthesis
       (if n + mlsexp_get_size (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs)))) + 2 < 70
        then remove_all (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs))))
        else smart_remove (m + 1) (n + 1)
               (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs))))) /\
     remove_all (mlsexp_annotate (v2pretty (sexp2tree (Expr xs)))) =
     Parenthesis (remove_all (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs)))))`,
  REWRITE_TAC[sexp2tree_def; PURE3AUX_v2pretty_thms; mlsexp_annotate_def;
              LET_DEF; LET_END_DEF; smart_remove_def; remove_all_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[remove_all_def; ADD_ASSOC]);;

let PURE3AUX_trees_Nil = prove
 (`!m n.
     smart_remove m n (mlsexp_annotate (newlines (vs2pretty (sexp2trees [])))) =
     mlsexp_String (implode "") /\
     remove_all (mlsexp_annotate (newlines (vs2pretty (sexp2trees [])))) =
     mlsexp_String (implode "")`,
  REWRITE_TAC[sexp2tree_def; PURE3AUX_v2pretty_thms; newlines_def;
              mlsexp_annotate_def; smart_remove_def; remove_all_def; COND_ID]);;

let PURE3AUX_trees_Sing = prove
 (`!x. mlsexp_annotate (newlines (vs2pretty (sexp2trees [x]))) =
       mlsexp_annotate (v2pretty (sexp2tree x))`,
  REWRITE_TAC[sexp2tree_def; PURE3AUX_v2pretty_thms; newlines_def]);;

let PURE3AUX_trees_Cons2 = prove
 (`!x y ys.
     mlsexp_annotate (newlines (vs2pretty (sexp2trees (CONS x (CONS y ys))))) =
     mlsexp_Append (mlsexp_annotate (v2pretty (sexp2tree x))) T
                   (mlsexp_annotate (newlines (vs2pretty (sexp2trees (CONS y ys)))))`,
  REWRITE_TAC[sexp2tree_def; PURE3AUX_v2pretty_thms; newlines_def;
              mlsexp_annotate_def; LET_DEF; LET_END_DEF]);;

let PURE3AUX_lex_paren = prove
 (`!e s ts depth t0.
     (!s ts depth.
        (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\ ~(depth = 0) ==>
        mlsexp_lex_aux depth (APPEND e s) ts = mlsexp_lex_aux depth s (APPEND t0 ts))
     ==> mlsexp_lex_aux depth (APPEND (APPEND "(" (APPEND e ")")) s) ts =
         (if depth = 0 then INR (CONS CLOSE (APPEND t0 (CONS OPEN ts)), s)
          else mlsexp_lex_aux depth s (CONS CLOSE (APPEND t0 (CONS OPEN ts))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (CHR 41) s`; `CONS OPEN ts`; `depth + 1`]) THEN
  REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; ADD_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ARITH_RULE `depth + 1 = 1 <=> depth = 0`;
              ADD_SUB]);;

let PURE3AUX_lex_Parenthesis = prove
 (`!indent p s ts depth t0.
     (!s ts depth.
        (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\ ~(depth = 0) ==>
        mlsexp_lex_aux depth
          (APPEND (explode (mlstring_concat
             (mlsexp_flatten (mlstring_concat [indent; implode "   "]) p []))) s) ts =
        mlsexp_lex_aux depth s (APPEND t0 ts))
     ==> mlsexp_lex_aux depth
           (APPEND (explode (mlstring_concat
              (mlsexp_flatten indent (Parenthesis p) []))) s) ts =
         (if depth = 0 then INR (CONS CLOSE (APPEND t0 (CONS OPEN ts)), s)
          else mlsexp_lex_aux depth s (CONS CLOSE (APPEND t0 (CONS OPEN ts))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[PURE3AUX_flatten_Parenthesis] THEN
  MATCH_MP_TAC PURE3AUX_lex_paren THEN FIRST_ASSUM ACCEPT_TAC);;

let PURE3AUX_lex_Append = prove
 (`!indent p1 b p2 s ts depth t1 t2.
     ~(indent = implode "") /\ ALL isSpace (explode indent) /\
     (!s ts. (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
        mlsexp_lex_aux depth
          (APPEND (explode (mlstring_concat (mlsexp_flatten indent p1 []))) s) ts =
        mlsexp_lex_aux depth s (APPEND t1 ts)) /\
     (!s ts. (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
        mlsexp_lex_aux depth
          (APPEND (explode (mlstring_concat (mlsexp_flatten indent p2 []))) s) ts =
        mlsexp_lex_aux depth s (APPEND t2 ts)) /\
     (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41)
     ==> mlsexp_lex_aux depth
           (APPEND (explode (mlstring_concat
              (mlsexp_flatten indent (mlsexp_Append p1 b p2) []))) s) ts =
         mlsexp_lex_aux depth s (APPEND t2 (APPEND t1 ts))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ih1") (CONJUNCTS_THEN2 (LABEL_TAC "ih2")
      ASSUME_TAC)))) THEN
  REWRITE_TAC[PURE3AUX_flatten_Append; GSYM APPEND_ASSOC] THEN
  SUBGOAL_THEN
   `?c r. explode (if b then indent else implode " ") = CONS c r /\
          isSpace c /\ ALL isSpace r`
   STRIP_ASSUME_TAC THENL
   [COND_CASES_TAC THENL
     [UNDISCH_TAC `~(indent = implode "")` THEN
      UNDISCH_TAC `ALL isSpace (explode indent)` THEN
      MP_TAC(SPEC `indent:mlstring` (cases "mlstring")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[explode_thm; injectivity "mlstring"] THEN
      CASES_ON `a:string` THEN REWRITE_TAC[ALL; CONS_11] THEN MESON_TAC[];
      REWRITE_TAC[explode_thm] THEN
      MAP_EVERY EXISTS_TAC [`CHR 32`; `[]:string`] THEN
      REWRITE_TAC(ALL :: PURE3AUX_CHAR_SIMPS)];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "ih1" (MP_TAC o SPECL
    [`APPEND (CONS (c:char) r)
        (APPEND (explode (mlstring_concat (mlsexp_flatten indent p2 []))) s)`;
     `ts:mlsexp_token list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND; HD; NOT_CONS_NIL]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`CONS (c:char) r`;
                `APPEND (explode (mlstring_concat (mlsexp_flatten indent p2 []))) s`;
                `APPEND t1 ts:mlsexp_token list`; `depth:num`] lex_aux_spaces) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "ih2" (MP_TAC o SPECL [`s:string`; `APPEND t1 ts:mlsexp_token list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REFL_TAC);;

let PURE3AUX_indent = prove
 (`!indent.
     ALL isSpace (explode indent) ==>
     ~(mlstring_concat [indent; implode "   "] = implode "") /\
     ALL isSpace (explode (mlstring_concat [indent; implode "   "]))`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM explode_11] THEN
  REWRITE_TAC[PURE3AUX_explode_concat; MAP; FLAT; APPEND_NIL; explode_thm;
              ALL_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC(ALL :: PURE3AUX_CHAR_SIMPS));;

let lex_aux_sexp2tree = prove
 (`(!x s ts depth m n indent.
     (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\
     (depth = 0 ==> ts = []) /\
     ~(indent = implode "") /\ ALL isSpace (explode indent) ==>
     mlsexp_lex_aux depth
       (APPEND
        (explode
         (mlstring_concat
          (mlsexp_flatten indent
             (smart_remove m n (mlsexp_annotate (v2pretty (sexp2tree x)))) [])))
        s) ts =
     (if depth = 0 then INR (APPEND (REVERSE (to_tokens x)) ts, s)
      else mlsexp_lex_aux depth s (APPEND (REVERSE (to_tokens x)) ts)) /\
     mlsexp_lex_aux depth
       (APPEND
        (explode
         (mlstring_concat
          (mlsexp_flatten indent
             (remove_all (mlsexp_annotate (v2pretty (sexp2tree x)))) [])))
        s) ts =
     (if depth = 0 then INR (APPEND (REVERSE (to_tokens x)) ts, s)
      else mlsexp_lex_aux depth s (APPEND (REVERSE (to_tokens x)) ts))) /\
  (!xs s ts depth indent m n.
     (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\ ~(depth = 0) /\
     ~(indent = implode "") /\ ALL isSpace (explode indent) ==>
     mlsexp_lex_aux depth
       (APPEND
        (explode
         (mlstring_concat
          (mlsexp_flatten indent
             (smart_remove m n
                (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs))))) [])))
        s) ts =
     mlsexp_lex_aux depth s (APPEND (REVERSE (FLAT (MAP to_tokens xs))) ts) /\
     mlsexp_lex_aux depth
       (APPEND
        (explode
         (mlstring_concat
          (mlsexp_flatten indent
             (remove_all
                (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs))))) [])))
        s) ts =
     mlsexp_lex_aux depth s (APPEND (REVERSE (FLAT (MAP to_tokens xs))) ts))`,
  MATCH_MP_TAC sexp_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Atom *)
    X_GEN_TAC `a:mlstring` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[PURE3AUX_tree_Atom; PURE3AUX_flatten_String; to_tokens_def;
                REVERSE; APPEND] THEN
    MP_TAC(SPECL [`a:mlstring`; `s:string`; `ts:mlsexp_token list`; `depth:num`]
                 lex_aux_make_str_safe) THEN
    ASM_REWRITE_TAC[PURE3AUX_mlstring_case_id] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    (* Expr *)
    X_GEN_TAC `xs:sexp list` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`s:string`; `ts:mlsexp_token list`; `depth:num`;
                         `m:num`; `n:num`; `indent:mlstring`] THEN
    STRIP_TAC THEN REWRITE_TAC[PURE3AUX_tree_Expr] THEN
    SUBGOAL_THEN
     `APPEND (REVERSE (to_tokens (Expr xs))) ts =
      CONS CLOSE (APPEND (REVERSE (FLAT (MAP to_tokens xs))) (CONS OPEN ts))`
     SUBST1_TAC THENL
     [REWRITE_TAC[to_tokens_def; ETA_AX; REVERSE_APPEND; REVERSE; APPEND;
                  GSYM APPEND_ASSOC]; ALL_TAC] THEN
    MP_TAC(SPEC `indent:mlstring` PURE3AUX_indent) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `n + mlsexp_get_size (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs)))) +
      2 < 70` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC PURE3AUX_lex_Parenthesis THEN
    MAP_EVERY X_GEN_TAC [`s1:string`; `ts1:mlsexp_token list`; `d1:num`] THEN
    STRIP_TAC THEN
    (FIRST_X_ASSUM(MP_TAC o SPECL [`s1:string`; `ts1:mlsexp_token list`; `d1:num`;
                                   `mlstring_concat [indent; implode "   "]`;
                                   `m + 1`; `n + 1`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);
    (* [] *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[PURE3AUX_trees_Nil; PURE3AUX_flatten_String; explode_thm; APPEND;
                MAP; FLAT; REVERSE];
    (* CONS *)
    MAP_EVERY X_GEN_TAC [`x:sexp`; `xs:sexp list`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihx") (LABEL_TAC "ihxs")) THEN
    MAP_EVERY X_GEN_TAC [`s:string`; `ts:mlsexp_token list`; `depth:num`;
                         `indent:mlstring`; `m:num`; `n:num`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(!m n s ts.
         (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
         mlsexp_lex_aux depth
           (APPEND (explode (mlstring_concat (mlsexp_flatten indent
              (smart_remove m n (mlsexp_annotate (v2pretty (sexp2tree x)))) [])))
              s) ts =
         mlsexp_lex_aux depth s (APPEND (REVERSE (to_tokens x)) ts)) /\
      (!s ts.
         (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
         mlsexp_lex_aux depth
           (APPEND (explode (mlstring_concat (mlsexp_flatten indent
              (remove_all (mlsexp_annotate (v2pretty (sexp2tree x)))) []))) s) ts =
         mlsexp_lex_aux depth s (APPEND (REVERSE (to_tokens x)) ts))`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`m1:num`; `n1:num`; `s1:string`;
                             `ts1:mlsexp_token list`];
        MAP_EVERY X_GEN_TAC [`s1:string`; `ts1:mlsexp_token list`] THEN
        MAP_EVERY ABBREV_TAC [`m1 = 0`; `n1 = 0`]] THEN
      DISCH_TAC THEN
      USE_THEN "ihx" (MP_TAC o SPECL [`s1:string`; `ts1:mlsexp_token list`;
         `depth:num`; `m1:num`; `n1:num`; `indent:mlstring`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
                                         ASM_REWRITE_TAC[]]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!m n s ts.
         (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
         mlsexp_lex_aux depth
           (APPEND (explode (mlstring_concat (mlsexp_flatten indent
              (smart_remove m n
                 (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs))))) [])))
              s) ts =
         mlsexp_lex_aux depth s (APPEND (REVERSE (FLAT (MAP to_tokens xs))) ts)) /\
      (!s ts.
         (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) ==>
         mlsexp_lex_aux depth
           (APPEND (explode (mlstring_concat (mlsexp_flatten indent
              (remove_all
                 (mlsexp_annotate (newlines (vs2pretty (sexp2trees xs))))) [])))
              s) ts =
         mlsexp_lex_aux depth s (APPEND (REVERSE (FLAT (MAP to_tokens xs))) ts))`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`m1:num`; `n1:num`; `s1:string`;
                             `ts1:mlsexp_token list`];
        MAP_EVERY X_GEN_TAC [`s1:string`; `ts1:mlsexp_token list`] THEN
        MAP_EVERY ABBREV_TAC [`m1 = 0`; `n1 = 0`]] THEN
      DISCH_TAC THEN
      USE_THEN "ihxs" (MP_TAC o SPECL [`s1:string`; `ts1:mlsexp_token list`;
         `depth:num`; `indent:mlstring`; `m1:num`; `n1:num`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]]);
      ALL_TAC] THEN
    REMOVE_THEN "ihx" (K ALL_TAC) THEN REMOVE_THEN "ihxs" (K ALL_TAC) THEN
    DISJ_CASES_TAC(ISPEC `xs:sexp list` list_CASES) THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[PURE3AUX_trees_Sing; MAP; FLAT; APPEND_NIL] THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `y:sexp`
        (X_CHOOSE_THEN `ys:sexp list` SUBST_ALL_TAC)) THEN
      REWRITE_TAC[PURE3AUX_trees_Cons2] THEN
      SUBGOAL_THEN
       `!ts. APPEND (REVERSE (FLAT (MAP to_tokens (CONS x (CONS y ys))))) ts =
             APPEND (REVERSE (FLAT (MAP to_tokens (CONS y ys))))
                    (APPEND (REVERSE (to_tokens x)) ts)`
       (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[MAP; FLAT; REVERSE_APPEND; APPEND_ASSOC]; ALL_TAC] THEN
      REWRITE_TAC[smart_remove_def; remove_all_def; LET_DEF; LET_END_DEF] THEN
      CONJ_TAC THENL [COND_CASES_TAC; ALL_TAC] THEN
      MATCH_MP_TAC PURE3AUX_lex_Append THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

let lex_aux_sexp_to_list = prove
 (`(!x s ts depth.
      (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\
      (depth = 0 ==> ts = []) ==>
      mlsexp_lex_aux depth
        (APPEND (explode (mlstring_concat (append (sexp_to_app_list x)))) s) ts =
      (if depth = 0 then INR (APPEND (REVERSE (to_tokens x)) ts, s)
       else mlsexp_lex_aux depth s (APPEND (REVERSE (to_tokens x)) ts))) /\
   (!xs s ts depth.
      (~(s = []) ==> isSpace (HD s) \/ HD s = CHR 41) /\ ~(depth = 0) ==>
      mlsexp_lex_aux depth
        (APPEND (explode (mlstring_concat (append (sexps_to_app_list xs)))) s) ts =
      mlsexp_lex_aux depth s (APPEND (REVERSE (FLAT (MAP (\x. to_tokens x) xs))) ts))`,
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC sexp_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Atom *)
    X_GEN_TAC `a:mlstring` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[sexp_to_app_list_def; append_thm; concat_sing; to_tokens_def;
                REVERSE; APPEND] THEN
    MP_TAC(SPECL [`a:mlstring`; `s:string`; `ts:mlsexp_token list`; `depth:num`]
                 lex_aux_make_str_safe) THEN
    ASM_REWRITE_TAC[PURE3AUX_mlstring_case_id];
    (* Expr *)
    X_GEN_TAC `xs:sexp list` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`s:string`; `ts:mlsexp_token list`; `depth:num`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `APPEND (REVERSE (to_tokens (Expr xs))) ts =
      CONS CLOSE (APPEND (REVERSE (FLAT (MAP to_tokens xs))) (CONS OPEN ts))`
     SUBST1_TAC THENL
     [REWRITE_TAC[to_tokens_def; ETA_AX; REVERSE_APPEND; REVERSE; APPEND;
                  GSYM APPEND_ASSOC]; ALL_TAC] THEN
    REWRITE_TAC[sexp_to_app_list_def; append_thm; PURE3AUX_explode_concat;
                MAP_APPEND; FLAT_APPEND; MAP; FLAT; APPEND_NIL; explode_thm] THEN
    MATCH_MP_TAC PURE3AUX_lex_paren THEN
    REWRITE_TAC[GSYM PURE3AUX_explode_concat] THEN ASM_REWRITE_TAC[];
    (* [] *)
    REWRITE_TAC[sexp_to_app_list_def; append_thm; concat_nil; explode_thm; APPEND;
                MAP; FLAT; REVERSE];
    (* CONS *)
    MAP_EVERY X_GEN_TAC [`v:sexp`; `vs:sexp list`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihv") (LABEL_TAC "ihvs")) THEN
    MAP_EVERY X_GEN_TAC [`s:string`; `ts:mlsexp_token list`; `depth:num`] THEN
    STRIP_TAC THEN REWRITE_TAC[sexp_to_app_list_def] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[NULL_EQ]) THEN
      REWRITE_TAC[MAP; FLAT; APPEND_NIL] THEN
      USE_THEN "ihv" (MP_TAC o SPECL [`s:string`; `ts:mlsexp_token list`;
                                      `depth:num`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);
      REWRITE_TAC[append_thm; PURE3AUX_explode_concat; MAP_APPEND; FLAT_APPEND;
                  MAP; FLAT; APPEND_NIL; explode_thm] THEN
      REWRITE_TAC[GSYM PURE3AUX_explode_concat; GSYM APPEND_ASSOC; APPEND] THEN
      USE_THEN "ihv" (MP_TAC o SPECL
        [`CONS (CHR 32) (APPEND (explode (mlstring_concat
            (append (sexps_to_app_list vs)))) s)`;
         `ts:mlsexp_token list`; `depth:num`]) THEN
      REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
      (ANTS_TAC THENL
        [ASM_REWRITE_TAC(NOT_CONS_NIL :: HD :: PURE3AUX_CHAR_SIMPS);
         ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC]) THEN
      ONCE_REWRITE_TAC[mlsexp_lex_aux_def] THEN REWRITE_TAC PURE3AUX_CHAR_SIMPS THEN
      USE_THEN "ihvs" (MP_TAC o SPECL [`s:string`;
        `APPEND (REVERSE (to_tokens v)) ts`; `depth:num`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
      REWRITE_TAC[MAP; FLAT; REVERSE_APPEND; APPEND_ASSOC]]]);;

let parse_sexp_to_string = prove
 (`!s x.
     (~(s = []) ==> isSpace (HD s)) ==>
     mlsexp_parse (APPEND (explode (sexp_to_string x)) s) = INR (x, s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sexp_to_string_def; mlsexp_parse_def; lex_def] THEN
  MP_TAC(SPECL [`x:sexp`; `s:string`; `[]:mlsexp_token list`; `0`]
               (CONJUNCT1 lex_aux_sexp_to_list)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[APPEND_NIL; sum_CASE; pair_CASE; parse_aux_to_tokens_thm; list_CASE]);;

let parse_sexp_to_pretty_string = prove
 (`!s x.
     mlsexp_parse (APPEND (explode (sexp_to_pretty_string x)) s) =
     INR (x, APPEND "\n" s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sexp_to_pretty_string_def; str_tree_to_strs_def; mlsexp_parse_def;
              lex_def] THEN
  ONCE_REWRITE_TAC[flatten_acc] THEN
  REWRITE_TAC[concat_append; explode_strcat; concat_sing; explode_thm;
              GSYM APPEND_ASSOC] THEN
  MP_TAC(SPECL [`x:sexp`; `APPEND "\n" s`; `[]:mlsexp_token list`; `0`; `0`; `0`;
                `implode "\n"`] (CONJUNCT1 lex_aux_sexp2tree)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[APPEND; NOT_CONS_NIL; HD; explode_thm; injectivity "mlstring"; ALL] THEN
    REWRITE_TAC PURE3AUX_CHAR_SIMPS;
    DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[APPEND_NIL; sum_CASE; pair_CASE; parse_aux_to_tokens_thm; list_CASE]);;

let fromString_sexp_to_string = prove
 (`mlsexp_fromString (sexp_to_string x) = SOME x`,
  REWRITE_TAC[mlsexp_fromString_def] THEN
  MP_TAC(SPECL [`[]:string`; `x:sexp`] parse_sexp_to_string) THEN
  REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[sum_CASE; pair_CASE]);;

let fromString_sexp_to_pretty_string = prove
 (`mlsexp_fromString (sexp_to_pretty_string x) = SOME x`,
  REWRITE_TAC[mlsexp_fromString_def] THEN
  MP_TAC(SPECL [`[]:string`; `x:sexp`] parse_sexp_to_pretty_string) THEN
  REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[sum_CASE; pair_CASE]);;
