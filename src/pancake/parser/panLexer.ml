(* ========================================================================= *)
(* panLexer: port of HOL4 pancake/parser/panLexerScript.sml (CakeML v3479).  *)
(* A lexer for the Pancake language (inspired by the Spark ADA development; *)
(* Craig McLaughlin, March--April 2022).                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the types token and atom are               *)
(*   panLexer_token and panLexer_atom; the constructors AndT, ArrowT, StarT, *)
(*   IntT, CommaT, ColonT and LexErrorT are panLexer_AndT, ...; get_token,   *)
(*   read_while, next_loc, next_line, skip_comment, unhex_alt,               *)
(*   num_from_dec_string_alt, next_token and init_loc have the prefix       *)
(*   panLexer_ (CakeML's lexer_fun and lexer_impl have them); HOL4           *)
(*   dest_lexErrorT_def is destLexErrorT_def.                                *)
(* - A character literal #"c" is CHR (ORD of c): CHR 10 newline, CHR 42      *)
(*   star, CHR 45 minus, CHR 47 slash, CHR 64 at, CHR 95 underscore; a case *)
(*   on a character literal is the equivalent test; STRING c s is CONS c s; *)
(*   an mlstring literal is implode of a string literal; concat is          *)
(*   mlstring_concat and toString (on a character) chr_to_str; f ## g is    *)
(*   PAIR_MAP (infix ##); HOL4 let (a,b) = e in t is HOL Light's paired let. *)
(* - isLexErrorT and destLexErrorT (a clause and a catch-all in HOL4, which  *)
(*   TFL completes into one clause per constructor) are defined by the      *)
(*   equivalent match; NAME_def is the completed clause form, as in HOL4.    *)
(* - Helpers that are not HOL4 names have the prefix PPARSEAUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/location.ml";;
needs "hol4/string4.ml";;
needs "hol4/ASCIInumbers.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

let keyword_INDUCT,keyword_RECURSION = cake_type
  "keyword = SkipK | StK | StwK | St8K | St16K | St32K | IfK | ElseK | WhileK
           | BrK | ContK | ThrowK | RetK | TicK | VarK | TryK | CatchK | BiwK
           | NamedK | LdsK | Ld8K | LdwK | Ld16K | Ld32K | BaseK | TopK | InK
           | FunK | ExportK | TrueK | FalseK | InlineK | ExceptionK";;

(* ForeignIdent: an @ffi_str identifier, except @base, @biw, @top *)

let panLexer_token_INDUCT,panLexer_token_RECURSION = cake_type
  "panLexer_token =
     panLexer_AndT | OrT | BoolAndT | BoolOrT | XorT | NotT | panLexer_ArrowT
   | EqT | NeqT | LessT | GreaterT | GeqT | LeqT | LowerT | HigherT | HigheqT
   | LoweqT
   | PlusT | MinusT | DotT | panLexer_StarT
   | LslT | LsrT | AsrT | RorT
   | panLexer_IntT int | IdentT string | ForeignIdent string
   | LParT | RParT | panLexer_CommaT | SemiT | panLexer_ColonT | AddrT
   | LBrakT | RBrakT | LCurT | RCurT
   | AssignT
   | StaticT
   | NoinlineT
   | DefaultShT
   | KeywordT keyword
   | AnnotCommentT string
   | panLexer_LexErrorT mlstring";;

let panLexer_atom_INDUCT,panLexer_atom_RECURSION = cake_type
  "panLexer_atom = NumberA int | WordA string | SymA string | ErrA mlstring
                 | AnnotCommentA string";;

let isAtom_singleton_def = cake_def
  `isAtom_singleton c <=> MEM c "+-^*().,;:[]{}"`;;

(* # is only for RorT, and should be removed to avoid a collision with the  *)
(* C preprocessor later                                                     *)

let isAtom_begin_group_def = cake_def
  `isAtom_begin_group c <=> MEM c "#=><!&|"`;;

let isAtom_in_group_def = cake_def
  `isAtom_in_group c <=> MEM c "=<>|&+"`;;

let isAlphaNumOrWild_def = cake_def
  `isAlphaNumOrWild c <=> isAlphaNum c \/ c = CHR 95`;;

(* PPARSEAUX_CASE_CLAUSES th: th is |- !x1 .. xn. f x1 .. xn = rhs with case *)
(* constants on the variables x1 .. xn in rhs; the result is the            *)
(* conjunction of the clauses f pat = rhs' obtained by splitting each such   *)
(* case on the constructors of its type (outermost first) and reducing it   *)
(* with the kit's case net: HOL4's TFL completion of a catch-all clause.     *)
(* (A copy of SEM2AUX_CASE_CLAUSES of semantics/tokenUtils.ml, which is not *)
(* in the needs closure of this file.)                                      *)

let PPARSEAUX_CASE_CLAUSES =
  let fresh avoid v =
    let n0,ty = dest_var v in
    let names = map (fst o dest_var) (!avoid) in
    let rec go n = if mem n names then go (n^"'") else n in
    let v' = mk_var(go n0,ty) in
    avoid := v' :: !avoid; v' in
  let rec take_abs n t acc =
    if n = 0 then rev acc
    else if is_abs t then let v,b = dest_abs t in take_abs (n-1) b (v::acc)
    else failwith "take_abs" in
  let rec split th =
    let l,r = dest_eq(concl th) in
    let pvs = frees l in
    let is_split t =
      is_case_app t &&
      (let _,x,_ = dest_case_app t in is_var x && mem x pvs) in
    match (try Some(find_term is_split r) with Failure _ -> None) with
      None -> [th]
    | Some t ->
        let c,x,fs = dest_case_app t in
        let ci = case_info_of_const c in
        let xty = type_of x in
        flat (map2 (fun (vs,pat) f ->
            let tyi = type_match (type_of pat) xty [] in
            let vs = map (inst tyi) vs and pat = inst tyi pat in
            let pref =
              try map2 (fun v b ->
                          let n = fst(dest_var b) in
                          if String.length n = 0 || String.sub n 0 1 = "_"
                          then v else mk_var(n,type_of v))
                       vs (take_abs (length vs) f [])
              with Failure _ -> vs in
            let avoid = ref (frees (concl th)) in
            let vs' = map (fresh avoid) pref in
            let pat' = vsubst (zip vs' vs) pat in
            let th1 = INST [pat',x] th in
            split (CONV_RULE (RAND_CONV (CAKE_REWRITE_CONV [] THENC
                                         DEPTH_CONV BETA_CONV)) th1))
          ci.ci_pats fs) in
  fun th ->
    let ths = split (SPEC_ALL th) in
    end_itlist CONJ (map (fun th -> GENL (frees (lhs(concl th))) th) ths);;

(* HOL4 defines isLexErrorT and destLexErrorT by a clause and a catch-all,  *)
(* which TFL completes into one clause per constructor; here each is       *)
(* defined by the equivalent match and NAME_def is the completed clause     *)
(* form (the same theorem as HOL4's)                                        *)

let isLexErrorT_def = PPARSEAUX_CASE_CLAUSES (cake_def
  `isLexErrorT t <=> match t with panLexer_LexErrorT _ -> T | _ -> F`);;

(* HOL4: dest_lexErrorT_def *)

let destLexErrorT_def = PPARSEAUX_CASE_CLAUSES (cake_def
  `destLexErrorT t =
     match t with panLexer_LexErrorT msg -> SOME msg | _ -> NONE`);;

let panLexer_get_token_def = cake_def
  `panLexer_get_token s =
     if s = "&&" then BoolAndT else
     if s = "||" then BoolOrT else
     if s = "&" then panLexer_AndT else
     if s = "|" then OrT else
     if s = "^" then XorT else
     if s = "==" then EqT else
     if s = "=>" then panLexer_ArrowT else
     if s = "!=" then NeqT else
     if s = "<" then LessT else
     if s = ">" then GreaterT else
     if s = ">=" then GeqT else
     if s = "<=" then LeqT else
     if s = "<+" then LowerT else
     if s = ">+" then HigherT else
     if s = ">=+" then HigheqT else
     if s = "<=+" then LoweqT else
     if s = "!" then NotT else
     if s = "+" then PlusT else
     if s = "-" then MinusT else
     if s = "*" then panLexer_StarT else
     if s = "." then DotT else
     if s = "<<" then LslT else
     if s = ">>>" then LsrT else
     if s = ">>" then AsrT else
     if s = "#>>" then RorT else
     if s = "(" then LParT else
     if s = ")" then RParT else
     if s = "," then panLexer_CommaT else
     if s = ";" then SemiT else
     if s = ":" then panLexer_ColonT else
     if s = "[" then LBrakT else
     if s = "]" then RBrakT else
     if s = "{" then LCurT else
     if s = "}" then RCurT else
     if s = "=" then AssignT else
     panLexer_LexErrorT
       (mlstring_concat [implode "Unrecognised symbolic token: "; implode s])`;;

(* as in HOL4, "@top" gives the keyword BaseK (not TopK) *)

let get_keyword_def = cake_def
  `get_keyword s =
     if s = "skip" then KeywordT SkipK else
     if s = "st" then KeywordT StK else
     if s = "stw" then KeywordT StwK else
     if s = "st8" then KeywordT St8K else
     if s = "st16" then KeywordT St16K else
     if s = "st32" then KeywordT St32K else
     if s = "if" then KeywordT IfK else
     if s = "else" then KeywordT ElseK else
     if s = "while" then KeywordT WhileK else
     if s = "break" then KeywordT BrK else
     if s = "continue" then KeywordT ContK else
     if s = "throw" then KeywordT ThrowK else
     if s = "return" then KeywordT RetK else
     if s = "tick" then KeywordT TicK else
     if s = "var" then KeywordT VarK else
     if s = "in" then KeywordT InK else
     if s = "try" then KeywordT TryK else
     if s = "catch" then KeywordT CatchK else
     if s = "lds" then KeywordT LdsK else
     if s = "ldw" then KeywordT LdwK else
     if s = "ld8" then KeywordT Ld8K else
     if s = "ld16" then KeywordT Ld16K else
     if s = "ld32" then KeywordT Ld32K else
     if s = "@base" then KeywordT BaseK else
     if s = "@top" then KeywordT BaseK else
     if s = "@biw" then KeywordT BiwK else
     if s = "true" then KeywordT TrueK else
     if s = "false" then KeywordT FalseK else
     if s = "fun" then KeywordT FunK else
     if s = "export" then KeywordT ExportK else
     if s = "inline" then KeywordT InlineK else
     if s = "exception" then KeywordT ExceptionK else
     if s = "struct" then KeywordT NamedK else
     if s = "" then
       panLexer_LexErrorT (implode "Expected keyword, found empty string") else
     if 2 <= LENGTH s /\ EL 0 s = CHR 64 then ForeignIdent (DROP 1 s)
     else IdentT s`;;

let token_of_atom_def = cake_def
  `token_of_atom a =
     match a with
       NumberA i -> panLexer_IntT i
     | WordA s -> get_keyword s
     | SymA s -> panLexer_get_token s
     | ErrA s -> panLexer_LexErrorT s
     | AnnotCommentA s -> AnnotCommentT s`;;

let panLexer_read_while_def = cake_def
  `(panLexer_read_while (P:char->bool) "" s = (IMPLODE (REVERSE s),"")) /\
   (panLexer_read_while P (CONS c cs) s =
      if P c then panLexer_read_while P cs (CONS c s)
      else (IMPLODE (REVERSE s),CONS c cs))`;;

let panLexer_read_while_thm = prove
 (`!P input s s' rest.
     panLexer_read_while P input s = (s',rest) ==> LENGTH rest <= LENGTH input`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[panLexer_read_while_def] THEN
  GVS[] THEN RES_TAC THEN ASM_ARITH_TAC);;

let panLexer_next_loc_def = cake_def
  `(panLexer_next_loc n (POSN r c) = POSN r (c + n)) /\
   (panLexer_next_loc n x = x)`;;

let panLexer_next_line_def = cake_def
  `(panLexer_next_line (POSN r c) = POSN (r + 1) 0) /\
   (panLexer_next_line x = x)`;;

let loc_row_def = cake_def
  `loc_row n = POSN n 1`;;

(* HOL4: case x of #"\n" => .. | _ => .., a test of the literal *)

let panLexer_skip_comment_def = cake_def
  `(panLexer_skip_comment "" (_:locn) (_:num) = NONE:(locn#num)option) /\
   (panLexer_skip_comment (CONS x xs) loc i =
      if x = CHR 10 then SOME (panLexer_next_line loc,i + 1)
      else panLexer_skip_comment xs (panLexer_next_loc 1 loc) (i + 1))`;;

(* SOME (loc,i,j): i characters in the comment; DROP j characters to        *)
(* continue parsing (after the closing star-slash) at loc                   *)

let skip_block_comment_def = cake_def
  `(skip_block_comment "" (_:locn) (_:num) = NONE:(locn#num#num)option) /\
   (skip_block_comment [_] _ _ = NONE) /\
   (skip_block_comment (CONS x (CONS y xs)) loc i =
      if (x = CHR 42 /\ y = CHR 47) \/ (x = CHR 64 /\ y = CHR 47) then
        SOME (panLexer_next_loc 2 loc,i,i + 2)
      else if x = CHR 10 then
        skip_block_comment (CONS y xs) (panLexer_next_line loc) (i + 1)
      else
        skip_block_comment (CONS y xs) (panLexer_next_loc 1 loc) (i + 1))`;;

let panLexer_unhex_alt_def = cake_def
  `panLexer_unhex_alt x = if isHexDigit x then UNHEX x else 0`;;

let panLexer_num_from_dec_string_alt_def = cake_def
  `panLexer_num_from_dec_string_alt = s2n 10 panLexer_unhex_alt`;;

(* the cases: skip a newline or a space; a number; a negative number; a   *)
(* line comment; an annotation block comment; a block comment; a one-     *)
(* character symbol; a group of symbol characters; an identifier; an     *)
(* unrecognised character                                                  *)

let next_atom_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[LENGTH; LENGTH_DROP] THEN ASM_ARITH_TAC)
  `(next_atom "" (_:locn) = NONE) /\
   (next_atom (CONS c cs) loc =
      if c = CHR 10 then
        next_atom cs (panLexer_next_line loc)
      else if isSpace c then
        next_atom cs (panLexer_next_loc 1 loc)
      else if isDigit c then
        let (n,cs') = panLexer_read_while isDigit cs [c] in
        SOME (NumberA (&(panLexer_num_from_dec_string_alt n)),
              Locs loc (panLexer_next_loc (LENGTH n) loc),
              cs')
      else if c = CHR 45 /\ ~(cs = "") /\ isDigit (HD cs) then
        let (n,rest) = panLexer_read_while isDigit cs [] in
        SOME (NumberA (&0 - &(panLexer_num_from_dec_string_alt n)),
              Locs loc (panLexer_next_loc (LENGTH n) loc),
              rest)
      else if isPREFIX "//" (CONS c cs) then
        (match panLexer_skip_comment (TL cs) (panLexer_next_loc 2 loc) 0 with
           NONE -> SOME (ErrA (implode "Malformed comment"),
                         Locs loc (panLexer_next_loc 2 loc),"")
         | SOME (loc',len) -> next_atom (DROP (len + 1) cs) loc')
      else if isPREFIX "/@" (CONS c cs) then
        (match skip_block_comment (TL cs) (panLexer_next_loc 3 loc) 0 with
           NONE -> SOME (ErrA (implode "Malformed comment"),
                         Locs loc (panLexer_next_loc 3 loc),"")
         | SOME (loc',i,len) -> SOME (AnnotCommentA (TAKE i (TL cs)),
                                      Locs loc loc',DROP (len + 1) cs))
      else if isPREFIX "/*" (CONS c cs) then
        (match skip_block_comment (TL cs) (panLexer_next_loc 2 loc) 0 with
           NONE -> SOME (ErrA (implode "Malformed comment"),
                         Locs loc (panLexer_next_loc 2 loc),"")
         | SOME (loc',_,len) -> next_atom (DROP (len + 1) cs) loc')
      else if isAtom_singleton c then
        SOME (SymA [c],Locs loc loc,cs)
      else if isAtom_begin_group c then
        let (n,rest) = panLexer_read_while isAtom_in_group cs [c] in
        SOME (SymA n,Locs loc (panLexer_next_loc (LENGTH n - 1) loc),rest)
      else if isAlpha c \/ c = CHR 64 \/ c = CHR 95 then
        let (n,rest) = panLexer_read_while isAlphaNumOrWild cs [c] in
        SOME (WordA n,Locs loc (panLexer_next_loc (LENGTH n) loc),rest)
      else
        SOME (ErrA (mlstring_concat [implode "Unrecognised symbol: ";
                                     chr_to_str c]),
              Locs loc loc,cs))`;;

let next_atom_ind = cake_ind "next_atom";;

let next_atom_LESS = prove
 (`!input l s l' rest.
     next_atom input l = SOME (s,l',rest) ==> LENGTH rest < LENGTH input`,
  MATCH_MP_TAC next_atom_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[next_atom_def; option_DISTINCT]; ALL_TAC] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[next_atom_def] THEN
  REPEAT TOP_CASE_TAC THEN FS[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC panLexer_read_while_thm THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LENGTH_DROP]) THEN
  REWRITE_TAC[LENGTH; LENGTH_DROP] THEN ASM_ARITH_TAC);;

let panLexer_next_token_def = cake_def
  `panLexer_next_token input loc =
     match next_atom input loc with
       NONE -> NONE
     | SOME (atom,locs,rest) -> SOME (token_of_atom atom,locs,rest)`;;

let panLexer_next_token_LESS = prove
 (`!s l l' rest input.
     panLexer_next_token input l = SOME (s,l',rest)
     ==> LENGTH rest < LENGTH input`,
  RW([panLexer_next_token_def] @ all_case_eqs()) THEN
  ASM_MESON_TAC[next_atom_LESS]);;

let panLexer_init_loc_def = cake_def
  `panLexer_init_loc = POSN 1 1`;;

let pancake_lex_aux_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM; FST] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   IMP_RES_TAC panLexer_next_token_LESS THEN ASM_REWRITE_TAC[])
  `pancake_lex_aux input loc =
     match panLexer_next_token input loc with
       NONE -> []
     | SOME (token,Locs locB locE,rest) ->
         CONS (token,Locs locB locE) (pancake_lex_aux rest locE)`;;

let pancake_lex_aux_ind = cake_ind "pancake_lex_aux";;

let pancake_lex_def = cake_def
  `pancake_lex input = pancake_lex_aux input panLexer_init_loc`;;

let safe_pancake_lex_def = cake_def
  `safe_pancake_lex input =
     let output = pancake_lex input in
     match FILTER (isLexErrorT o FST) output with
       [] -> INL output
     | xs -> INR (MAP ((misc_the (implode "") o destLexErrorT) ## I) xs)`;;
