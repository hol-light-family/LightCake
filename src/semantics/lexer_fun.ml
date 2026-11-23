(* ========================================================================= *)
(* lexer_fun: port of HOL4 semantics/lexer_funScript.sml (CakeML v3479).     *)
(* A functional specification of lexing from strings to token lists.        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The HOL4 datatype symbol of this theory is lexer_fun_symbol (grammar   *)
(*   has a type symbol); IntT, WordT, CharT and Mod are tokens_IntT,         *)
(*   tokens_WordT, tokens_CharT and tokens_Mod (names.tsv).                  *)
(* - A character literal #"c" is CHR (ORD of c): CHR 10 newline, CHR 34      *)
(*   double quote, CHR 39 quote, CHR 92 backslash, CHR 95 underscore, ...;  *)
(*   STRING c s is CONS c s; s1 ++ s2 is APPEND s1 s2; STRLEN is LENGTH.     *)
(* - HOL4 let (a,b) = e in t is written match e with (a,b) -> t; the        *)
(*   variable tok of next_sym is tk (tok was a constructor of peg.ml, now    *)
(*   peg_tok).                                                               *)
(* - HOL4 l with col updated_by (+) n is locn_colupdate ((+) n) l.           *)
(* - read_string_thm and skip_comment_thm are proved by induction on the    *)
(*   length of the string (HOL4 uses the recursion induction theorems,      *)
(*   which are also here).  The local HOL4 values listeq and optioneq       *)
(*   (CaseEq) are not needed.                                                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/location.ml";;
needs "hol4/string4.ml";;
needs "hol4/list.ml";;
needs "semantics/tokens.ml";;
needs "hol4/ASCIInumbers.ml";;

type_invention_error := true;;

(* This script defines the functional spec for the assembly implementation *)
(* of the lexer.  This lexer specification consists of two phases.  The    *)
(* first phase reads a string and returns a list of symbols.  The second   *)
(* phase converts the symbol list into a list of tokens.  The             *)
(* implementation merges these two phases.                                 *)

(* SEM2AUX_MATCH_EITHER th1 th2 is MATCH_MP th1 th2, or else MATCH_MP th1    *)
(* (SYM th2): the termination conditions state their case contexts as       *)
(* e = pattern or as pattern = e, depending on the kit.                     *)

let SEM2AUX_MATCH_EITHER th1 th2 =
  try MATCH_MP th1 th2 with Failure _ -> MATCH_MP th1 (SYM th2);;

(* intermediate symbols *)

let lexer_fun_symbol_INDUCT,lexer_fun_symbol_RECURSION = cake_type
  "lexer_fun_symbol = StringS string
                    | CharS char
                    | NumberS int
                    | WordS num
                    | LongS (string list) string
                    | FFIS string
                    | OtherS string
                    | ErrorS";;

(* helper functions *)

let mkCharS_def = cake_def
  `(mkCharS (StringS s) = if LENGTH s = 1 then CharS (HD s) else ErrorS) /\
   (mkCharS _ = ErrorS)`;;

let read_while_def = cake_def
  `(read_while (P:char->bool) "" s = (IMPLODE (REVERSE s),"")) /\
   (read_while P (CONS c cs) s =
      if P c then read_while P cs (CONS c s)
      else (IMPLODE (REVERSE s),CONS c cs))`;;

let read_while_thm = prove
 (`!P cs s cs' s'. read_while P cs s = (s',cs') ==> LENGTH cs' <= LENGTH cs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[read_while_def] THEN
  RES_TAC THEN ASM_ARITH_TAC);;

let is_single_char_symbol_def = cake_def
  `is_single_char_symbol c <=> MEM c "()[]{},;"`;;

let isSymbol_def = cake_def
  `isSymbol c <=> MEM c (CONS (CHR 96) "!%&$#+-/:<=>?@\\~^|*")`;;

let next_loc_def = cake_def
  `(next_loc n (POSN r c) = POSN r (c + n)) /\
   (next_loc n x = x)`;;

let next_line_def = cake_def
  `(next_line (POSN r c) = POSN (r + 1) 0) /\
   (next_line x = x)`;;

let read_char_as_3digits_def = cake_def
  `read_char_as_3digits (str:string) =
     let ds = TAKE 3 str in
     let rest = DROP 3 str in
     if LENGTH ds < 3 then NONE
     else
       match FOLDL (\A d. match A with
                            NONE -> NONE
                          | SOME A0 -> if isDigit d
                                       then SOME (10 * A0 + (ORD d - 48))
                                       else NONE)
                   (SOME 0) ds with
         NONE -> NONE
       | SOME ci -> if ci < 256 then SOME (CHR ci,rest) else NONE`;;

let read_char_as_3digits_reduces = prove
 (`!str0 c str. read_char_as_3digits str0 = SOME (c,str)
                ==> LENGTH str0 = LENGTH str + 3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[read_char_as_3digits_def; LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN
  GVS([LENGTH_DROP; LENGTH_TAKE_EQ; NOT_LT] @ all_case_eqs()) THEN
  ASM_ARITH_TAC);;

let read_string_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN
   CASES_ON `str:string` THEN GVS[] THEN
   TRY (FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER read_char_as_3digits_reduces)) THEN
   GVS[] THEN ASM_ARITH_TAC)
  `read_string str s (loc:locn) =
     if str = "" then (ErrorS, loc, "") else
     if HD str = CHR 34 then (StringS s, loc, TL str) else
     if HD str = CHR 10 then (ErrorS, next_line loc, TL str) else
     if ~(HD str = CHR 92) then
       read_string (TL str) (APPEND s [HD str]) (next_loc 1 loc)
     else
       match TL str with
         CONS (CHR 92) cs -> read_string cs (APPEND s "\\") (next_loc 2 loc)
       | CONS (CHR 34) cs -> read_string cs (APPEND s "\"") (next_loc 2 loc)
       | CONS (CHR 97) cs -> read_string cs (APPEND s [CHR 7]) (next_loc 2 loc)
       | CONS (CHR 98) cs -> read_string cs (APPEND s [CHR 8]) (next_loc 2 loc)
       | CONS (CHR 116) cs -> read_string cs (APPEND s [CHR 9]) (next_loc 2 loc)
       | CONS (CHR 110) cs -> read_string cs (APPEND s [CHR 10]) (next_loc 2 loc)
       | CONS (CHR 118) cs -> read_string cs (APPEND s [CHR 11]) (next_loc 2 loc)
       | CONS (CHR 102) cs -> read_string cs (APPEND s [CHR 12]) (next_loc 2 loc)
       | CONS (CHR 114) cs -> read_string cs (APPEND s [CHR 13]) (next_loc 2 loc)
       | CONS c cs ->
           if isDigit c then
             (match read_char_as_3digits (CONS c cs) with
                NONE -> (ErrorS, loc, CONS c cs)
              | SOME (c,cs') -> read_string cs' (APPEND s [c]) (next_loc 4 loc))
           else (ErrorS, loc, TL str)
       | _ -> (ErrorS, loc, TL str)`;;

let read_string_ind = cake_ind "read_string";;

let read_string_thm = prove
 (`!s t l l' x1 x2. read_string s t l = (x1,l',x2)
                    ==> LENGTH x2 <= LENGTH s + LENGTH t`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH (s:string)` THEN
  SUBGOAL_THEN
   `!s' t l l' x1 x2. read_string s' t l = (x1,l',x2)
                      ==> LENGTH s' < LENGTH (s:string)
                      ==> LENGTH x2 <= LENGTH s' + LENGTH t`
   MP_TAC THENL [ASM_MESON_TAC[]; POP_ASSUM(K ALL_TAC) THEN DISCH_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[read_string_def] THEN
  CASES_ON `s:string` THEN REWRITE_TAC[NOT_CONS_NIL; HD; TL] THEN
  REPEAT TOP_CASE_TAC THEN
  (DISCH_THEN(fun th -> FIRST_ASSUM(fun ih -> MP_TAC(MATCH_MP ih th))) ORELSE
   (REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC)) THEN
  REPEAT (FIRST_X_ASSUM(MP_TAC o MATCH_MP read_char_as_3digits_reduces)) THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

let skip_comment_def = cake_def
  `(skip_comment "" (d:num) (_:locn) = NONE:(string#locn)option) /\
   (skip_comment [x] d _ = NONE) /\
   (skip_comment (CONS x (CONS y xs)) d loc =
      if [x;y] = "(*" then skip_comment xs (d + 1) (next_loc 2 loc)
      else if [x;y] = "*)" then
        (if d = 0 then SOME (xs,next_loc 2 loc)
         else skip_comment xs (d - 1) (next_loc 2 loc))
      else if ORD x = 10 then skip_comment (CONS y xs) d (next_line loc)
      else skip_comment (CONS y xs) d (next_loc 1 loc))`;;

let skip_comment_ind = cake_ind "skip_comment";;

let skip_comment_thm = prove
 (`!xs d l l' str. skip_comment xs d l = SOME (str,l')
                   ==> LENGTH str <= LENGTH xs`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH (xs:string)` THEN
  SUBGOAL_THEN
   `!xs' d l l' str. skip_comment xs' d l = SOME (str,l')
                     ==> LENGTH xs' < LENGTH (xs:string)
                     ==> LENGTH str <= LENGTH xs'`
   MP_TAC THENL [ASM_MESON_TAC[]; POP_ASSUM(K ALL_TAC) THEN DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `xs:string` THEN REWRITE_TAC[skip_comment_def; option_DISTINCT] THEN
  CASES_ON `a1:string` THEN REWRITE_TAC[skip_comment_def; option_DISTINCT] THEN
  REPEAT TOP_CASE_TAC THEN
  (DISCH_THEN(fun th -> FIRST_ASSUM(fun ih -> MP_TAC(MATCH_MP ih th))) ORELSE
   (REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC)) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let read_FFIcall_def = cake_def
  `(read_FFIcall "" (acc:string) (loc:locn) = (ErrorS,loc,"")) /\
   (read_FFIcall (CONS c s0) acc loc =
      if c = CHR 41 then (FFIS (REVERSE acc),next_loc 2 loc,s0)
      else if c = CHR 10 then (ErrorS,loc,s0)
      else if isSpace c then read_FFIcall s0 acc (next_loc 1 loc)
      else read_FFIcall s0 (CONS c acc) (next_loc 1 loc))`;;

let read_FFIcall_reduces_input = prove
 (`!s0 a l0 t l s. read_FFIcall s0 a l0 = (t,l,s) ==> LENGTH s < LENGTH s0 + 1`,
  LIST_INDUCT_TAC THEN RW[read_FFIcall_def] THEN RES_TAC THEN ASM_ARITH_TAC);;

let read_REPLcommand_def = cake_def
  `(read_REPLcommand "" (acc:string) (loc:locn) = (ErrorS,loc,"")) /\
   (read_REPLcommand (CONS c s0) acc loc =
      if c = CHR 125 then
        (FFIS (REVERSE acc),locn_colupdate ((+) 2) loc,s0)
      else if c = CHR 10 then (ErrorS,loc,s0)
      else if isSpace c then
        read_REPLcommand s0 acc (locn_colupdate ((+) 1) loc)
      else read_REPLcommand s0 (CONS c acc) (locn_colupdate ((+) 1) loc))`;;

let read_REPLcommand_reduces_input = prove
 (`!s0 a l0 t l s. read_REPLcommand s0 a l0 = (t,l,s)
                   ==> LENGTH s < LENGTH s0 + 1`,
  LIST_INDUCT_TAC THEN RW[read_REPLcommand_def] THEN RES_TAC THEN
  ASM_ARITH_TAC);;

let isAlphaNumPrime_def = cake_def
  `isAlphaNumPrime c <=> isAlphaNum c \/ c = CHR 39 \/ c = CHR 95`;;

let read_Ident_ret_def = cake_def
  `read_Ident_ret (acc:string list) (n:string) (new_loc:locn) (rest:string) =
     if NULL acc then (OtherS n,new_loc,rest)
     else (LongS (REVERSE acc) n,new_loc,rest)`;;

let read_Ident_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn#string list->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER read_while_thm) THEN
   GVS[] THEN ARITH_TAC)
  `(read_Ident [] (loc:locn) (acc:string list) = (ErrorS,loc,[])) /\
   (read_Ident (CONS c str) loc acc =
      if is_single_char_symbol c then
        (if NULL acc then (OtherS [c],next_loc 1 loc,str)
         else (ErrorS,loc,str))
      else if isSymbol c then
        (match read_while isSymbol str [c] with
           (n,rest) ->
             let new_loc = next_loc (LENGTH n) loc in
             read_Ident_ret acc n new_loc rest)
      else if isAlpha c then
        (match read_while isAlphaNumPrime str [c] with
           (n,rest) ->
             let new_loc = next_loc (LENGTH n) loc in
             (match rest with
                [] -> read_Ident_ret acc n new_loc rest
              | CONS c1 rest1 ->
                  if c1 = CHR 46 then read_Ident rest1 new_loc (CONS n acc)
                  else read_Ident_ret acc n new_loc rest))
      else (ErrorS,loc,str))`;;

let read_Ident_ind = cake_ind "read_Ident";;

(* next_sym reads the next symbol from a string, returning NONE if at eof *)

let next_sym_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   TRY (FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER skip_comment_thm)) THEN
   CASES_ON `str:string` THEN GVS[isPREFIX] THEN ASM_ARITH_TAC)
  `(next_sym "" (_:locn) = NONE) /\
   (next_sym (CONS c str) loc =
      if c = CHR 10 then next_sym str (next_line loc)
      else if isSpace c then next_sym str (next_loc 1 loc)
      else if isDigit c then
        (if ~(str = "") /\ c = CHR 48 /\ HD str = CHR 119 then
           (if TL str = "" then SOME (ErrorS,Locs loc loc,"")
            else if isDigit (HD (TL str)) then
              (match read_while isDigit (TL str) [] with
                 (n,rest) ->
                   SOME (WordS (num_from_dec_string n),
                         Locs loc (next_loc (LENGTH n + 1) loc),
                         rest))
            else if HD (TL str) = CHR 120 then
              (match read_while isHexDigit (TL (TL str)) [] with
                 (n,rest) ->
                   SOME (WordS (num_from_hex_string n),
                         Locs loc (next_loc (LENGTH n + 2) loc),
                         rest))
            else SOME (ErrorS,Locs loc loc,TL str))
         else
           (if ~(str = "") /\ c = CHR 48 /\ HD str = CHR 120 then
              (match read_while isHexDigit (TL str) [] with
                 (n,rest) ->
                   SOME (NumberS (&(num_from_hex_string n)),
                         Locs loc (next_loc (LENGTH n) loc),
                         rest))
            else
              (match read_while isDigit str [] with
                 (n,rest) ->
                   SOME (NumberS (&(num_from_dec_string (CONS c n))),
                         Locs loc (next_loc (LENGTH n) loc),
                         rest))))
      else if c = CHR 126 /\ ~(str = "") /\ isDigit (HD str) then
        (match read_while isDigit str [] with
           (n,rest) ->
             SOME (NumberS (&0 - &(num_from_dec_string n)),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest))
      else if c = CHR 39 then
        (match read_while isAlphaNumPrime str [c] with
           (n,rest) ->
             SOME (OtherS n,Locs loc (next_loc (LENGTH n - 1) loc),rest))
      else if c = CHR 34 then
        (match read_string str "" (next_loc 1 loc) with
           (t,loc',rest) -> SOME (t,Locs loc loc',rest))
      else if isPREFIX "*)" (CONS c str) then
        SOME (ErrorS,Locs loc (next_loc 2 loc),TL str)
      else if isPREFIX "#\"" (CONS c str) then
        (match read_string (TL str) "" (next_loc 2 loc) with
           (t,loc',rest) -> SOME (mkCharS t,Locs loc loc',rest))
      else if isPREFIX "#(" (CONS c str) then
        (match read_FFIcall (TL str) "" (next_loc 2 loc) with
           (t,loc',rest) -> SOME (t,Locs loc loc',rest))
      else if isPREFIX "(*" (CONS c str) then
        (match skip_comment (TL str) 0 (next_loc 2 loc) with
           NONE -> SOME (ErrorS,Locs loc (next_loc 2 loc),"")
         | SOME (rest,loc') -> next_sym rest loc')
      else if c = CHR 95 then SOME (OtherS "_",Locs loc loc,str)
      else
        (match read_Ident (CONS c str) loc [] with
           (tk,end_loc,rest) -> SOME (tk,Locs loc end_loc,rest)))`;;

let next_sym_ind = cake_ind "next_sym";;

let lem1 = prove
 (CASE_TERM
  `!(z:A->B#C) (f:B->C->D) (P:A->D) a.
     ((match z a with (x,y) -> f x y) = P a) <=>
     (match z a with (x,y) -> f x y = P a)`,
  REPEAT GEN_TAC THEN CASES_ON `(z:A->B#C) a` THEN SIMP[]);;

let lem2 = prove
 (CASE_TERM
  `!(z:A->B#C) (f:B->C->bool) (P:A->bool) a.
     ((match z a with (x,y) -> f x y) ==> P a) <=>
     (match z a with (x,y) -> f x y ==> P a)`,
  REPEAT GEN_TAC THEN CASES_ON `(z:A->B#C) a` THEN SIMP[]);;

let read_while_EMPTY = CONJUNCT1 read_while_def;;
let _ = cake_add_simps [read_while_EMPTY];;

let NOT_NIL_EXISTS_CONS = prove
 (`!(n:A list) P. (~(n = []) <=> ?h t. n = CONS h t) /\
                  (list_CASE n F P <=> ?h t. n = CONS h t /\ P h t)`,
  GEN_TAC THEN CASES_ON `n:A list` THEN SIMP[]);;

let read_Ident_LESS = prove
 (`!xs l acc s loc rest.
     read_Ident xs l acc = (s,loc,rest)
     ==> if xs = [] then rest = [] else LENGTH rest < LENGTH xs`,
  MATCH_MP_TAC read_Ident_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[read_Ident_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[read_Ident_def] THEN
  REWRITE_TAC[NOT_CONS_NIL; LET_DEF; LET_END_DEF; read_Ident_ret_def] THEN
  REPEAT TOP_CASE_TAC THEN
  FS[] THEN STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC read_while_thm THEN
  RES_TAC THEN EVERY_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let next_sym_LESS = prove
 (`!input l s l' rest. next_sym input l = SOME (s,l',rest)
                       ==> LENGTH rest < LENGTH input`,
  MATCH_MP_TAC next_sym_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[next_sym_def; option_DISTINCT]; ALL_TAC] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[next_sym_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT TOP_CASE_TAC THEN
  FS[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC read_while_thm THEN IMP_RES_TAC read_string_thm THEN
  IMP_RES_TAC read_FFIcall_reduces_input THEN IMP_RES_TAC skip_comment_thm THEN
  IMP_RES_TAC read_Ident_LESS THEN RES_TAC THEN
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (is_forall o concl))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  IMP_RES_TAC LENGTH_TL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; NOT_CONS_NIL]) THEN REWRITE_TAC[LENGTH] THEN
  (ASM_ARITH_TAC ORELSE
   (CASES_ON `str:string` THEN FS[isPREFIX; LENGTH] THEN ASM_ARITH_TAC)));;

let init_loc_def = cake_def
  `init_loc = POSN 0 0`;;

(* next_token reads the next token from a string *)

let processIdent_def = cake_def
  `processIdent s =
     match s with
       [] -> LexErrorT
     | CONS c s ->
         if isAlpha c then AlphaT (implode (CONS c s))
         else SymbolT (implode (CONS c s))`;;

let get_token_def = cake_def
  `get_token s =
     if s = "#" then HashT else
     if s = "(" then LparT else
     if s = ")" then RparT else
     if s = "*" then StarT else
     if s = "," then CommaT else
     if s = "->" then ArrowT else
     if s = "..." then DotsT else
     if s = ":" then ColonT else
     if s = ":>" then SealT else
     if s = ";" then SemicolonT else
     if s = "=" then EqualsT else
     if s = "=>" then DarrowT else
     if s = "[" then LbrackT else
     if s = "]" then RbrackT else
     if s = "_" then UnderbarT else
     if s = "{" then LbraceT else
     if s = "}" then RbraceT else
     if s = "|" then BarT else
     if s = "and" then AndT else
     if s = "andalso" then AndalsoT else
     if s = "as" then AsT else
     if s = "case" then CaseT else
     if s = "datatype" then DatatypeT else
     if s = "else" then ElseT else
     if s = "end" then EndT else
     if s = "eqtype" then EqtypeT else
     if s = "exception" then ExceptionT else
     if s = "fn" then FnT else
     if s = "fun" then FunT else
     if s = "handle" then HandleT else
     if s = "if" then IfT else
     if s = "in" then InT else
     if s = "include" then IncludeT else
     if s = "let" then LetT else
     if s = "local" then LocalT else
     if s = "of" then OfT else
     if s = "op" then OpT else
     if s = "open" then OpenT else
     if s = "orelse" then OrelseT else
     if s = "raise" then RaiseT else
     if s = "rec" then RecT else
     if s = "sharing" then SharingT else
     if s = "sig" then SigT else
     if s = "signature" then SignatureT else
     if s = "struct" then StructT else
     if s = "structure" then StructureT else
     if s = "then" then ThenT else
     if s = "type" then TypeT else
     if s = "val" then ValT else
     if s = "where" then WhereT else
     if s = "with" then WithT else
     if s = "withtype" then WithtypeT else
     if ~(s = "") /\ HD s = CHR 39 then TyvarT (implode s) else
     processIdent s`;;

let to_path_def = cake_def
  `(to_path [] = End) /\
   (to_path (CONS x xs) = tokens_Mod x (to_path xs))`;;

let token_of_sym_def = cake_def
  `token_of_sym s =
     match s with
       ErrorS -> LexErrorT
     | StringS s -> StringT (implode s)
     | CharS c -> tokens_CharT c
     | NumberS i -> tokens_IntT i
     | WordS n -> tokens_WordT n
     | LongS xs s -> LongidT (to_path (MAP implode xs)) (implode s)
     | FFIS s -> FFIT (implode s)
     | OtherS s -> get_token s`;;

let next_token_def = cake_def
  `next_token input loc =
     match next_sym input loc with
       NONE -> NONE
     | SOME (sym,locs,rest_of_input) ->
         SOME (token_of_sym sym,locs,rest_of_input)`;;

let next_token_LESS = prove
 (`!s l l' rest input. next_token input l = SOME (s,l',rest)
                       ==> LENGTH rest < LENGTH input`,
  REPEAT GEN_TAC THEN REWRITE_TAC[next_token_def] THEN REPEAT TOP_CASE_TAC THEN
  FS[] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[next_sym_LESS]);;

(* top-level lexer specification *)

let lexer_fun_aux_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER next_token_LESS) THEN SIMP[])
  `lexer_fun_aux input loc =
     match next_token input loc with
       NONE -> []
     | SOME (token,Locs loc' loc'',rest_of_input) ->
         CONS (token,Locs loc' loc'')
              (lexer_fun_aux rest_of_input (next_loc 1 loc''))`;;

let lexer_fun_aux_ind = cake_ind "lexer_fun_aux";;

let lexer_fun_def = cake_def
  `lexer_fun input = lexer_fun_aux input init_loc`;;

(* split a list of tokens at top-level semicolons *)

let toplevel_semi_dex_def = cake_def
  `(toplevel_semi_dex (i:num) (d:num) ([]:(token#A)list) = NONE) /\
   (toplevel_semi_dex i d (CONS (h,l) t) =
      if h = SemicolonT /\ d = 0 then SOME (i + 1)
      else if h = LetT then toplevel_semi_dex (i + 1) (d + 1) t
      else if h = StructT then toplevel_semi_dex (i + 1) (d + 1) t
      else if h = SigT then toplevel_semi_dex (i + 1) (d + 1) t
      else if h = LparT then toplevel_semi_dex (i + 1) (d + 1) t
      else if h = EndT then toplevel_semi_dex (i + 1) (d - 1) t
      else if h = RparT then toplevel_semi_dex (i + 1) (d - 1) t
      else toplevel_semi_dex (i + 1) d t)`;;

let toplevel_semi_dex_non0 = prove
 (`!i d (toks:(token#A)list) j. toplevel_semi_dex i d toks = SOME j ==> 0 < j`,
  SUBGOAL_THEN
   `!(toks:(token#A)list) i d j. toplevel_semi_dex i d toks = SOME j ==> 0 < j`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[toplevel_semi_dex_def; option_DISTINCT] THEN
  CASES_ON `h:token#A` THEN REWRITE_TAC[toplevel_semi_dex_def] THEN
  RW[] THEN RES_TAC THEN ASM_ARITH_TAC);;

let split_top_level_semi_def = cake_def_wf
  `MEASURE (LENGTH:(token#A)list->num)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM (ASSUME_TAC o SEM2AUX_MATCH_EITHER toplevel_semi_dex_non0) THEN
   CASES_ON `toks:(token#A)list` THEN
   FS[toplevel_semi_dex_def; LENGTH_DROP] THEN ASM_ARITH_TAC)
  `split_top_level_semi (toks:(token#A)list) =
     match toplevel_semi_dex 0 0 toks with
       NONE -> []
     | SOME i -> CONS (TAKE i toks) (split_top_level_semi (DROP i toks))`;;

let split_top_level_semi_ind = cake_ind "split_top_level_semi";;
