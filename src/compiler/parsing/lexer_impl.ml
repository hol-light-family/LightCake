(* ========================================================================= *)
(* lexer_impl: port of HOL4 compiler/parsing/lexer_implScript.sml (CakeML    *)
(* v3479).  Definition of the lexer: code for consuming tokens until a       *)
(* top-level semicolon is found (semicolons can be hidden in let-in-end      *)
(* blocks, structures, signatures, and between parentheses).                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/tokens.ml";;
needs "semantics/lexer_fun.ml";;
needs "hol4/ASCIInumbers.ml";;
needs "hol4/location.ml";;
needs "hol4/rich_list.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* get_token_eqn: the lexer's keyword table as a decision tree on the first  *)
(* character.  HOL4 proves it by cases on the first character; here every    *)
(* character test is turned into a test on n = ORD c (LEX2AUX_GT_NORM_TAC)   *)
(* and the 256 values of n are checked one by one (EXPAND_CASES_CONV).        *)
(* HOL4 c <= #";" (chars) is char_le c (CHR 59), c < #"a" is char_lt c       *)
(* (CHR 97).                                                                 *)
(* ------------------------------------------------------------------------- *)

let LEX2AUX_GT_NORM_TAC =
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[get_token_def; CONS_11; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[processIdent_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[char_le_def; char_lt_def; isAlpha_def; isLower_def; isUpper_def;
              GSYM ORD_11; LSTRAUX_ORD_CHR_MOD; ORD_DEF; BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let LEX2AUX_GT_CASES_TAC =
  MP_TAC (SPEC `h:char` ORD_BOUND) THEN SPEC_TAC(`ORD h`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let get_token_eqn = prove
 (CASE_TERM
  `!s. get_token s =
    match s with
      [] -> LexErrorT
    | [c] ->
        if char_le c (CHR 59) then
          if char_le c (CHR 41) then
            if char_le c (CHR 39) then
              if c = CHR 35 then HashT else
              if c = CHR 39 then TyvarT (implode s) else
              SymbolT (implode s)
            else
              if c = CHR 40 then LparT else
              if c = CHR 41 then RparT else
              SymbolT (implode s)
          else
            if char_le c (CHR 44) then
              if c = CHR 42 then StarT else
              if c = CHR 44 then CommaT else
              SymbolT (implode s)
            else
              if c = CHR 58 then ColonT else
              if c = CHR 59 then SemicolonT else
              SymbolT (implode s)
        else
          if char_le c (CHR 93) then
            if char_le c (CHR 90) then
              if char_le (CHR 65) c /\ char_le c (CHR 90) then AlphaT (implode s)
              else
              if c = CHR 61 then EqualsT else
              SymbolT (implode s)
            else
              if c = CHR 91 then LbrackT else
              if c = CHR 93 then RbrackT else
              SymbolT (implode s)
          else
            if char_le c (CHR 123) then
              if c = CHR 95 then UnderbarT else
              if char_le (CHR 97) c /\ char_le c (CHR 122) then AlphaT (implode s)
              else
              if c = CHR 123 then LbraceT else
              SymbolT (implode s)
            else
              if c = CHR 124 then BarT else
              if c = CHR 125 then RbraceT else
              SymbolT (implode s)
    | CONS c s' ->
        if char_lt c (CHR 97) then
          if char_le c (CHR 46) then
            if c = CHR 39 then TyvarT (implode s) else
            if s = "->" then ArrowT else
            if s = "..." then DotsT else
            SymbolT (implode s)
          else
            if s = ":>" then SealT else
            if s = "=>" then DarrowT else
            if char_le (CHR 65) c /\ char_le c (CHR 90) then AlphaT (implode s) else
            SymbolT (implode s)
        else if char_le c (CHR 122) then
          if char_le c (CHR 105) then
            if char_le c (CHR 101) then
              if char_lt c (CHR 101) then
                if s = "and" then AndT else
                if s = "andalso" then AndalsoT else
                if s = "as" then AsT else
                if s = "case" then CaseT else
                if s = "datatype" then DatatypeT else
                AlphaT (implode s)
              else
                if s = "else" then ElseT else
                if s = "end" then EndT else
                if s = "eqtype" then EqtypeT else
                if s = "exception" then ExceptionT else
                AlphaT (implode s)
            else
              if char_le c (CHR 104) then
                if s = "fn" then FnT else
                if s = "fun" then FunT else
                if s = "handle" then HandleT else
                AlphaT (implode s)
              else
                if s = "if" then IfT else
                if s = "in" then InT else
                if s = "include" then IncludeT else
                AlphaT (implode s)
          else
            if char_le c (CHR 114) then
              if c = CHR 108 then
                if s = "let" then LetT else
                if s = "local" then LocalT else
                AlphaT (implode s)
              else if c = CHR 111 then
                if s = "of" then OfT else
                if s = "op" then OpT else
                if s = "open" then OpenT else
                if s = "orelse" then OrelseT else
                AlphaT (implode s)
              else
                if s = "raise" then RaiseT else
                if s = "rec" then RecT else
                AlphaT (implode s)
            else
              if c = CHR 115 then
                if s = "sharing" then SharingT else
                if s = "sig" then SigT else
                if s = "signature" then SignatureT else
                if s = "struct" then StructT else
                if s = "structure" then StructureT else
                AlphaT (implode s)
              else if char_lt c (CHR 119) then
                if s = "then" then ThenT else
                if s = "type" then TypeT else
                if s = "val" then ValT else
                AlphaT (implode s)
              else
                if s = "where" then WhereT else
                if s = "with" then WithT else
                if s = "withtype" then WithtypeT else
                AlphaT (implode s)
        else
          SymbolT (implode s)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `s:string` list_CASES) THENL
   [LEX2AUX_GT_NORM_TAC;
    STRUCT_CASES_TAC (ISPEC `t:string` list_CASES) THEN
    LEX2AUX_GT_NORM_TAC THEN LEX2AUX_GT_CASES_TAC]);;

(* HOL4: computeLib.add_persistent_funs ["get_token_eqn"] (EVAL only) *)

let unhex_alt_def = cake_def
  `unhex_alt x = if isHexDigit x then UNHEX x else 0`;;

let num_from_dec_string_alt_def = cake_def
  `num_from_dec_string_alt = s2n 10 unhex_alt`;;

let num_from_hex_string_alt_def = cake_def
  `num_from_hex_string_alt = s2n 16 unhex_alt`;;

let next_sym_alt_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   TRY (FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER skip_comment_thm)) THEN
   CASES_ON `str:string` THEN GVS[isPREFIX] THEN ASM_ARITH_TAC)
  `(next_sym_alt "" (_:locn) = NONE) /\
   (next_sym_alt (CONS c str) loc =
      if c = CHR 10 then next_sym_alt str (next_line loc)
      else if isSpace c then next_sym_alt str (next_loc 1 loc)
      else if isDigit c then
        (if ~(str = "") /\ c = CHR 48 /\ HD str = CHR 119 then
           (if TL str = "" then SOME (ErrorS,Locs loc loc,"")
            else if isDigit (HD (TL str)) then
              (match read_while isDigit (TL str) [] with
                 (n,rest) ->
                   SOME (WordS (num_from_dec_string_alt n),
                         Locs loc (next_loc (LENGTH n + 1) loc),
                         rest))
            else if HD (TL str) = CHR 120 then
              (match read_while isHexDigit (TL (TL str)) [] with
                 (n,rest) ->
                   SOME (WordS (num_from_hex_string_alt n),
                         Locs loc (next_loc (LENGTH n + 2) loc),
                         rest))
            else SOME (ErrorS,Locs loc loc,TL str))
         else
           (if ~(str = "") /\ c = CHR 48 /\ HD str = CHR 120 then
              (match read_while isHexDigit (TL str) [] with
                 (n,rest) ->
                   SOME (NumberS (&(num_from_hex_string_alt n)),
                         Locs loc (next_loc (LENGTH n) loc),
                         rest))
            else
              (match read_while isDigit str [] with
                 (n,rest) ->
                   SOME (NumberS (&(num_from_dec_string_alt (CONS c n))),
                         Locs loc (next_loc (LENGTH n) loc),
                         rest))))
      else if c = CHR 126 /\ ~(str = "") /\ isDigit (HD str) then
        (match read_while isDigit str [] with
           (n,rest) ->
             SOME (NumberS (&0 - &(num_from_dec_string_alt n)),
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
         | SOME (rest,loc') -> next_sym_alt rest loc')
      else if c = CHR 95 then SOME (OtherS "_",Locs loc loc,str)
      else
        (match read_Ident (CONS c str) loc [] with
           (tk,end_loc,rest) -> SOME (tk,Locs loc end_loc,rest)))`;;

let next_sym_alt_ind = cake_ind "next_sym_alt";;

(* ------------------------------------------------------------------------- *)
(* next_sym = next_sym_alt                                                   *)
(* ------------------------------------------------------------------------- *)

let EVERY_isDigit_imp = prove
 (`!x. ALL isDigit x ==> MAP UNHEX x = MAP unhex_alt x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[unhex_alt_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[isDigit_def]) THEN
  ASM_REWRITE_TAC[isHexDigit_def]);;

let toNum_rw = prove
 (`!x. ALL isDigit x ==> num_from_dec_string x = num_from_dec_string_alt x`,
  REWRITE_TAC[s2n_def; num_from_dec_string_def; num_from_dec_string_alt_def] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EVERY_isDigit_imp THEN
  ASM_MESON_TAC[EVERY_REVERSE]);;

let EVERY_isHexDigit_imp = prove
 (`!x. ALL isHexDigit x ==> MAP UNHEX x = MAP unhex_alt x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[unhex_alt_def]);;

let num_from_hex_string_rw = prove
 (`!x. ALL isHexDigit x ==> num_from_hex_string x = num_from_hex_string_alt x`,
  REWRITE_TAC[s2n_def; num_from_hex_string_def; num_from_hex_string_alt_def] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EVERY_isHexDigit_imp THEN
  ASM_MESON_TAC[EVERY_REVERSE]);;

let EVERY_IMPLODE = prove
 (`!ls (P:char->bool). ALL P (IMPLODE ls) <=> ALL P ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[IMPLODE_def; ALL]);;

let read_while_P_lem = prove
 (`!ls rest P x y. ALL P rest /\ read_while P ls rest = (x,y) ==> ALL P x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[read_while_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[EVERY_IMPLODE; EVERY_REVERSE];
    COND_CASES_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`CONS (h:char) rest`; `y:string`] THEN
      ASM_REWRITE_TAC[ALL];
      REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[EVERY_IMPLODE; EVERY_REVERSE]]]);;

let read_while_P = prove
 (`!ls P x y. read_while P ls "" = (x,y) ==> ALL P x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC read_while_P_lem THEN
  MAP_EVERY EXISTS_TAC [`ls:string`; `"":string`; `y:string`] THEN
  ASM_REWRITE_TAC[ALL]);;

(* the two sides of next_sym_eq are the same tree of conditionals and case  *)
(* expressions: LEX2AUX_LOCKSTEP_TAC descends into both at once, leaving    *)
(* the leaves where they differ (recursive calls, number conversions)        *)

let LEX2AUX_COND_CONG = prove
 (`!b (x1:A) x2 y1 y2. (b ==> x1 = x2) /\ (~b ==> y1 = y2)
     ==> (if b then x1 else y1) = (if b then x2 else y2)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let LEX2AUX_PAIR_CASE_CONG = prove
 (`!(p:A#B) (f:A->B->C) g.
     (!a b. p = (a,b) ==> f a b = g a b) ==> pair_CASE p f = pair_CASE p g`,
  GEN_TAC THEN CASES_ON `p:A#B` THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

let LEX2AUX_OPTION_CASE_CONG = prove
 (`!(x:A option) (a:B) f g.
     (!y. x = SOME y ==> f y = g y) ==> option_CASE x a f = option_CASE x a g`,
  GEN_TAC THEN CASES_ON `x:A option` THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

let rec LEX2AUX_LOCKSTEP_TAC g =
  FIRST
   [REFL_TAC;
    MATCH_MP_TAC LEX2AUX_COND_CONG THEN CONJ_TAC THEN DISCH_TAC THEN
    LEX2AUX_LOCKSTEP_TAC;
    MATCH_MP_TAC LEX2AUX_PAIR_CASE_CONG THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    BETA_TAC THEN LEX2AUX_LOCKSTEP_TAC;
    MATCH_MP_TAC LEX2AUX_OPTION_CASE_CONG THEN GEN_TAC THEN DISCH_TAC THEN
    BETA_TAC THEN LEX2AUX_LOCKSTEP_TAC;
    ALL_TAC] g;;

let next_sym_eq = prove
 (`!x l. next_sym x l = next_sym_alt x l`,
  MATCH_MP_TAC next_sym_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[next_sym_def; next_sym_alt_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[next_sym_def; next_sym_alt_def] THEN
  LEX2AUX_LOCKSTEP_TAC THEN
  TRY (FIRST_ASSUM (ASSUME_TAC o MATCH_MP read_while_P)) THEN
  ASM_SIMP_TAC[toNum_rw; num_from_hex_string_rw; ALL]);;

(* ------------------------------------------------------------------------- *)
(* lex_until_toplevel_semicolon                                              *)
(* ------------------------------------------------------------------------- *)

(* HOL4: lex_aux (names.tsv: lexer_impl_lex_aux) *)

let lexer_impl_lex_aux_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string) o
            (SND:num#string#locn->string#locn) o
            (SND:(token#locs)list#num#string#locn->num#string#locn))`
  (REWRITE_TAC[measure_THM; o_THM; FST; SND] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER next_token_LESS) THEN SIMP[])
  `lexer_impl_lex_aux (acc:(token#locs)list) (d:num) input loc =
     match next_token input loc with
       NONE -> NONE
     | SOME (token,Locs loc' loc'',rest) ->
         let new_acc = CONS (token,Locs loc' loc'') acc in
         let newloc = next_loc 1 loc'' in
         if token = SemicolonT /\ d = 0 then SOME (REVERSE new_acc,newloc,rest)
         else if token = LetT then lexer_impl_lex_aux new_acc (d + 1) rest newloc
         else if token = StructT then lexer_impl_lex_aux new_acc (d + 1) rest newloc
         else if token = SigT then lexer_impl_lex_aux new_acc (d + 1) rest newloc
         else if token = LparT then lexer_impl_lex_aux new_acc (d + 1) rest newloc
         else if token = EndT then lexer_impl_lex_aux new_acc (d - 1) rest newloc
         else if token = RparT then lexer_impl_lex_aux new_acc (d - 1) rest newloc
         else lexer_impl_lex_aux new_acc d rest newloc`;;

let lexer_impl_lex_aux_ind = cake_ind "lexer_impl_lex_aux";;

let lex_until_toplevel_semicolon_def = cake_def
  `lex_until_toplevel_semicolon input = lexer_impl_lex_aux [] 0 input`;;

let LEX2AUX_next_token_SOME = prove
 (`!input loc. ~(next_token input loc = NONE)
     ==> ?token l1 l2 r. next_token input loc = SOME (token,Locs l1 l2,r)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `next_token input loc` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[PAIR_SURJECTIVE; cases "locs"]);;

(* the leaves of lex_aux_LESS and lex_aux_alt_LESS: substitute the case     *)
(* assumptions, resolve the induction hypotheses, arithmetic                *)

let LEX2AUX_LESS_LEAF_TAC =
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  RES_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[NOT_CONS_NIL]) THEN
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (is_forall o concl))) THEN
  TRY COND_CASES_TAC THEN ASM_ARITH_TAC;;

let lex_aux_LESS = prove
 (`!acc d input l ts l' rest.
     lexer_impl_lex_aux acc d input l = SOME (ts,l',rest)
     ==> if acc = [] then LENGTH rest < LENGTH input
         else LENGTH rest <= LENGTH input`,
  MATCH_MP_TAC lexer_impl_lex_aux_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[lexer_impl_lex_aux_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `next_token input loc = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LEX2AUX_next_token_SOME) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP next_token_LESS) THEN
  REPEAT COND_CASES_TAC THEN LEX2AUX_LESS_LEAF_TAC);;

let lex_until_toplevel_semicolon_LESS = prove
 (`!input l ts l' rest.
     lex_until_toplevel_semicolon input l = SOME (ts,l',rest)
     ==> LENGTH rest < LENGTH input`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lex_until_toplevel_semicolon_def] THEN
  DISCH_THEN (MP_TAC o MATCH_MP lex_aux_LESS) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* lex_until_toplevel_semicolon_alt                                          *)
(* ------------------------------------------------------------------------- *)

let lex_aux_alt_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string) o
            (SND:num#string#locn->string#locn) o
            (SND:(lexer_fun_symbol#locs)list#num#string#locn->num#string#locn))`
  (REWRITE_TAC[measure_THM; o_THM; FST; SND] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER next_sym_LESS) THEN SIMP[])
  `lex_aux_alt (acc:(lexer_fun_symbol#locs)list) (d:num) input l =
     match next_sym input l with
       NONE -> NONE
     | SOME (token,Locs loc' loc'',rest) ->
         let new_acc = CONS (token,Locs loc' loc'') acc in
         let newloc = next_loc 1 loc'' in
         if token = OtherS ";" /\ d = 0 then SOME (REVERSE new_acc,newloc,rest)
         else if MEM token [OtherS "let"; OtherS "struct"; OtherS "sig"; OtherS "("]
         then lex_aux_alt new_acc (d + 1) rest newloc
         else if MEM token [OtherS ")"; OtherS "end"]
         then lex_aux_alt new_acc (d - 1) rest newloc
         else lex_aux_alt new_acc d rest newloc`;;

let lex_aux_alt_ind = cake_ind "lex_aux_alt";;

let lex_until_top_semicolon_alt_def = cake_def
  `lex_until_top_semicolon_alt input = lex_aux_alt [] 0 input`;;

let LEX2AUX_next_sym_SOME = prove
 (`!input l. ~(next_sym input l = NONE)
     ==> ?token l1 l2 r. next_sym input l = SOME (token,Locs l1 l2,r)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `next_sym input l` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[PAIR_SURJECTIVE; cases "locs"]);;

let lex_aux_alt_LESS = prove
 (`!acc d input l ts l' rest.
     lex_aux_alt acc d input l = SOME (ts,l',rest)
     ==> if acc = [] then LENGTH rest < LENGTH input
         else LENGTH rest <= LENGTH input`,
  MATCH_MP_TAC lex_aux_alt_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[lex_aux_alt_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `next_sym input l = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LEX2AUX_next_sym_SOME) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP next_sym_LESS) THEN
  REPEAT COND_CASES_TAC THEN LEX2AUX_LESS_LEAF_TAC);;

let lex_until_top_semicolon_alt_LESS = prove
 (`!input l ts l' rest.
     lex_until_top_semicolon_alt input l = SOME (ts,l',rest)
     ==> LENGTH rest < LENGTH input`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lex_until_top_semicolon_alt_def] THEN
  DISCH_THEN (MP_TAC o MATCH_MP lex_aux_alt_LESS) THEN REWRITE_TAC[]);;

(* get_token s is LetT (and so on) exactly for the keyword "let": push the  *)
(* equation into the conditionals of get_token, then the keyword test is    *)
(* the only one left                                                         *)

let LEX2AUX_processIdent_kw = prove
 (`!s. ~(processIdent s = LetT) /\ ~(processIdent s = EndT) /\
       ~(processIdent s = SigT) /\ ~(processIdent s = StructT) /\
       ~(processIdent s = SemicolonT) /\ ~(processIdent s = RparT) /\
       ~(processIdent s = LparT)`,
  GEN_TAC THEN CASES_ON `s:string` THEN REWRITE_TAC[processIdent_def] THEN
  CAKE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN CAKE_REWRITE_TAC[]);;

let LEX2AUX_COND_EQ_PUSH = prove
 (`!b (x:token) y z. ((if b then x else y) = z) <=> (if b then x = z else y = z)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let LEX2AUX_GET_TOKEN_KW tm =
  prove(tm,
    GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [get_token_def] THEN
    REWRITE_TAC[LEX2AUX_COND_EQ_PUSH] THEN
    CAKE_REWRITE_TAC[LEX2AUX_processIdent_kw] THEN
    REWRITE_TAC[TAUT `(if b then F else y) <=> ~b /\ y`;
                TAUT `(if b then T else y) <=> b \/ y`] THEN
    EQ_TAC THENL
     [MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN CONV_TAC (DEPTH_CONV STRING_EQ_CONV) THEN
      REWRITE_TAC[]]);;

let token_of_sym_EQ_LEMMA = prove
 (`!q. (token_of_sym q = LetT <=> q = OtherS "let") /\
       (token_of_sym q = EndT <=> q = OtherS "end") /\
       (token_of_sym q = SigT <=> q = OtherS "sig") /\
       (token_of_sym q = StructT <=> q = OtherS "struct") /\
       (token_of_sym q = SemicolonT <=> q = OtherS ";") /\
       (token_of_sym q = RparT <=> q = OtherS ")") /\
       (token_of_sym q = LparT <=> q = OtherS "(")`,
  let kws = map LEX2AUX_GET_TOKEN_KW
    [`!s. get_token s = LetT <=> s = "let"`;
     `!s. get_token s = EndT <=> s = "end"`;
     `!s. get_token s = SigT <=> s = "sig"`;
     `!s. get_token s = StructT <=> s = "struct"`;
     `!s. get_token s = SemicolonT <=> s = ";"`;
     `!s. get_token s = RparT <=> s = ")"`;
     `!s. get_token s = LparT <=> s = "("`] in
  GEN_TAC THEN CASES_ON `q:lexer_fun_symbol` THEN
  REWRITE_TAC[token_of_sym_def] THEN CAKE_REWRITE_TAC kws);;

let token_of_sym_loc_def = cake_def
  `token_of_sym_loc (t,(l:A)) = (token_of_sym t,l)`;;

(* the conditionals of lexer_impl_lex_aux, with token_of_sym_EQ_LEMMA, in   *)
(* the shape of those of lex_aux_alt                                          *)

let LEX2AUX_LEX_CHAIN = prove
 (`!t d (a:B) b c e.
     (if t = OtherS ";" /\ d = 0 then a else if t = OtherS "let" then b
      else if t = OtherS "struct" then b else if t = OtherS "sig" then b
      else if t = OtherS "(" then b else if t = OtherS "end" then c
      else if t = OtherS ")" then c else e) =
     (if t = OtherS ";" /\ d = 0 then a
      else if MEM t [OtherS "let"; OtherS "struct"; OtherS "sig"; OtherS "("]
      then b
      else if MEM t [OtherS ")"; OtherS "end"] then c else e)`,
  let tac lit =
    ASM_CASES_TAC (mk_eq(`t:lexer_fun_symbol`,
                         mk_comb(`OtherS`,mk_string lit))) THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[MEM] THEN CAKE_REWRITE_TAC[] THEN
      CONV_TAC (DEPTH_CONV (STRING_EQ_CONV ORELSEC CHAR_EQ_CONV)) THEN
      REWRITE_TAC[];
      ALL_TAC] in
  REPEAT GEN_TAC THEN
  MAP_EVERY tac [";"; "let"; "struct"; "sig"; "("; "end"; ")"] THEN
  ASM_REWRITE_TAC[MEM]);;

(* the induction hypotheses of lex_aux_alt_ind for the token at hand *)

let LEX2AUX_ALT_IH_TAC =
  FIRST_ASSUM (fun ih ->
    MP_TAC (SPECL [`token:lexer_fun_symbol`; `l1:locn`; `r:string`; `l2:locn`] ih) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[MAP; token_of_sym_loc_def]] THEN
    NO_TAC);;

(* HOL4: the anonymous lemma that lex_aux_alt_thm specialises *)

let LEX2AUX_lex_aux_alt_thm = prove
 (CASE_TERM `!acc d input l.
      match lex_aux_alt acc d input l with
        NONE -> lexer_impl_lex_aux (MAP token_of_sym_loc acc) d input l = NONE
      | SOME (ts,rest) ->
          lexer_impl_lex_aux (MAP token_of_sym_loc acc) d input l =
          SOME (MAP token_of_sym_loc ts,rest)`,
  MATCH_MP_TAC lex_aux_alt_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[lex_aux_alt_def; lexer_impl_lex_aux_def] THEN
  REWRITE_TAC[next_token_def; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `next_sym input l = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LEX2AUX_next_sym_SOME) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[token_of_sym_EQ_LEMMA] THEN
  REWRITE_TAC[LEX2AUX_LEX_CHAIN] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MAP_REVERSE; MAP; token_of_sym_loc_def] THEN
  LEX2AUX_ALT_IH_TAC);;

(* HOL4: val lex_aux_alt_thm (an ML value, not a stored theorem) *)

let lex_aux_alt_thm =
  REWRITE_RULE[MAP] (SPECL [`[]:(lexer_fun_symbol#locs)list`; `0`]
                       LEX2AUX_lex_aux_alt_thm);;

let lex_until_top_semicolon_alt_thm = prove
 (CASE_TERM `!input l.
    match lex_until_top_semicolon_alt input l with
      NONE -> lex_until_toplevel_semicolon input l = NONE
    | SOME (ts,rest) ->
        lex_until_toplevel_semicolon input l = SOME (MAP token_of_sym_loc ts,rest)`,
  REWRITE_TAC[lex_until_top_semicolon_alt_def; lex_until_toplevel_semicolon_def;
              lex_aux_alt_thm]);;

let lex_impl_all_def = cake_def_wf
  `MEASURE ((LENGTH:string->num) o (FST:string#locn->string))`
  (REWRITE_TAC[measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN GVS[] THEN
   FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER lex_until_toplevel_semicolon_LESS) THEN
   SIMP[])
  `lex_impl_all input l =
     match lex_until_toplevel_semicolon input l with
       NONE -> []
     | SOME (t,loc,input') -> CONS t (lex_impl_all input' loc)`;;

let lex_impl_all_ind = cake_ind "lex_impl_all";;

let lex_aux_tokens_def = cake_def
  `lex_aux_tokens (acc:(token#A)list) (d:num) input =
     match input with
       [] -> NONE
     | CONS (token,locs) rest ->
         let new_acc = CONS (token,locs) acc in
         if token = SemicolonT /\ d = 0 then SOME (REVERSE new_acc,rest)
         else if token = LetT then lex_aux_tokens new_acc (d + 1) rest
         else if token = StructT then lex_aux_tokens new_acc (d + 1) rest
         else if token = SigT then lex_aux_tokens new_acc (d + 1) rest
         else if token = LparT then lex_aux_tokens new_acc (d + 1) rest
         else if token = EndT then lex_aux_tokens new_acc (d - 1) rest
         else if token = RparT then lex_aux_tokens new_acc (d - 1) rest
         else lex_aux_tokens new_acc d rest`;;

let lex_until_toplevel_semicolon_tokens_def = cake_def
  `lex_until_toplevel_semicolon_tokens (input:(token#A)list) =
     lex_aux_tokens [] 0 input`;;

let lex_aux_tokens_LESS = prove
 (`!acc d (input:(token#A)list) t rest.
     lex_aux_tokens acc d input = SOME (t,rest)
     ==> if acc = [] then LENGTH rest < LENGTH input
         else LENGTH rest <= LENGTH input`,
  SUBGOAL_THEN
   `!(input:(token#A)list) acc d t rest.
      lex_aux_tokens acc d input = SOME (t,rest)
      ==> if acc = [] then LENGTH rest < LENGTH input
          else LENGTH rest <= LENGTH input`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[lex_aux_tokens_def] THEN
  CAKE_REWRITE_TAC[] THEN
  SUBST1_TAC (ISPEC `h:token#A` (GSYM PAIR)) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN
  LEX2AUX_LESS_LEAF_TAC);;

let lex_impl_all_tokens_def = cake_def_wf
  `MEASURE (LENGTH:(token#A)list->num)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   GVS[lex_until_toplevel_semicolon_tokens_def] THEN
   FIRST_X_ASSUM (MP_TAC o SEM2AUX_MATCH_EITHER lex_aux_tokens_LESS) THEN SIMP[])
  `lex_impl_all_tokens (input:(token#A)list) =
     match lex_until_toplevel_semicolon_tokens input with
       NONE -> []
     | SOME (t,input') -> CONS t (lex_impl_all_tokens input')`;;

let lex_impl_all_tokens_ind = cake_ind "lex_impl_all_tokens";;

(* ------------------------------------------------------------------------- *)
(* lex_impl_all = lex_impl_all_tokens o lexer_fun_aux                        *)
(* ------------------------------------------------------------------------- *)

(* the clauses of lex_aux_tokens (rewriting with lex_aux_tokens_def itself   *)
(* would loop: its left side has a variable list argument)                   *)

let LEX2AUX_lex_aux_tokens_clauses = prove
 (`(!acc d. lex_aux_tokens (acc:(token#A)list) d [] = NONE) /\
   (!acc d token (locs:A) rest.
      lex_aux_tokens acc d (CONS (token,locs) rest) =
      if token = SemicolonT /\ d = 0 then SOME (REVERSE (CONS (token,locs) acc),rest)
      else if token = LetT then lex_aux_tokens (CONS (token,locs) acc) (d + 1) rest
      else if token = StructT then lex_aux_tokens (CONS (token,locs) acc) (d + 1) rest
      else if token = SigT then lex_aux_tokens (CONS (token,locs) acc) (d + 1) rest
      else if token = LparT then lex_aux_tokens (CONS (token,locs) acc) (d + 1) rest
      else if token = EndT then lex_aux_tokens (CONS (token,locs) acc) (d - 1) rest
      else if token = RparT then lex_aux_tokens (CONS (token,locs) acc) (d - 1) rest
      else lex_aux_tokens (CONS (token,locs) acc) d rest)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lex_aux_tokens_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

(* HOL4 lex_aux_tokens_thm_1 and lex_aux_tokens_thm: the first two of four  *)
(* local theorems; HOL4 rebinds both names below, and so does this file.     *)
(* The induction is done on the form of lex_aux_tokens_thm.                  *)

let LEX2AUX_lex_aux_tokens_thm = prove
 (CASE_TERM `!input l (acc:(token#locs)list) d.
     match lexer_impl_lex_aux acc d input l with
       NONE -> lex_aux_tokens acc d (lexer_fun_aux input l) = NONE
     | SOME (ts,l',rest) ->
         lex_aux_tokens acc d (lexer_fun_aux input l) =
         SOME (ts,lexer_fun_aux rest l')`,
  MATCH_MP_TAC lexer_fun_aux_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[lexer_impl_lex_aux_def] THEN
  SUBST1_TAC (SPECL [`input:string`; `loc:locn`] lexer_fun_aux_def) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `next_token input loc = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[LEX2AUX_lex_aux_tokens_clauses];
    ALL_TAC] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LEX2AUX_next_token_SOME) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[LEX2AUX_lex_aux_tokens_clauses] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN CAKE_REWRITE_TAC[] THEN
  (FIRST_X_ASSUM (MP_TAC o SPECL [`token:token`; `l1:locn`; `r:string`; `l2:locn`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_ACCEPT_TAC]));;

let lex_aux_tokens_thm_1 = prove
 (CASE_TERM `!input l (acc:(token#locs)list) d res1 res2.
     lex_aux_tokens acc d (lexer_fun_aux input l) = res1 /\
     lexer_impl_lex_aux acc d input l = res2
     ==> match res2 with
           NONE -> res1 = NONE
         | SOME (ts,l',rest) -> res1 = SOME (ts,lexer_fun_aux rest l')`,
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[LEX2AUX_lex_aux_tokens_thm]);;

let lex_aux_tokens_thm = prove
 (CASE_TERM `!input l (acc:(token#locs)list) d.
     match lexer_impl_lex_aux acc d input l with
       NONE -> lex_aux_tokens acc d (lexer_fun_aux input l) = NONE
     | SOME (ts,l',rest) ->
         lex_aux_tokens acc d (lexer_fun_aux input l) =
         SOME (ts,lexer_fun_aux rest l')`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`input:string`; `l:locn`; `acc:(token#locs)list`; `d:num`;
                 `lex_aux_tokens (acc:(token#locs)list) d (lexer_fun_aux input l)`;
                 `lexer_impl_lex_aux (acc:(token#locs)list) d input l`]
                lex_aux_tokens_thm_1) THEN
  REWRITE_TAC[]);;

let LEX2AUX_lex_aux_SOME = prove
 (`!(acc:(token#locs)list) d input l.
     ~(lexer_impl_lex_aux acc d input l = NONE)
     ==> ?t loc input'. lexer_impl_lex_aux acc d input l = SOME (t,loc,input')`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `lexer_impl_lex_aux acc d input l` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[PAIR_SURJECTIVE]);;

let lex_impl_all_tokens_thm = prove
 (`!input l. lex_impl_all input l = lex_impl_all_tokens (lexer_fun_aux input l)`,
  MATCH_MP_TAC lex_impl_all_ind THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lex_until_toplevel_semicolon_def] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[lex_impl_all_def] THEN
  GEN_REWRITE_TAC RAND_CONV [lex_impl_all_tokens_def] THEN
  REWRITE_TAC[lex_until_toplevel_semicolon_tokens_def;
              lex_until_toplevel_semicolon_def] THEN
  MP_TAC (SPECL [`input:string`; `l:locn`; `[]:(token#locs)list`; `0`]
                lex_aux_tokens_thm) THEN
  ASM_CASES_TAC `lexer_impl_lex_aux [] 0 input l = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LEX2AUX_lex_aux_SOME) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the second HOL4 lex_aux_tokens_thm_1 and lex_aux_tokens_thm *)

let LEX2AUX_TOKENS_IH_TAC : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t ->
    match strip_comb t with
      (c,[_;_;_]) -> is_const c && fst(dest_const c) = "lex_aux_tokens"
    | _ -> false) w in
  let a,dd = match snd(strip_comb tm) with [a;dd;_] -> a,dd | _ -> fail() in
  (FIRST_X_ASSUM (MP_TAC o SPECL [dd; a]) THEN
   REWRITE_TAC[LENGTH; ADD1; REVERSE; GSYM APPEND_ASSOC; APPEND]) g;;

let lex_aux_tokens_thm_1 = prove
 (CASE_TERM `!(input:(token#A)list) d acc.
     match lex_aux_tokens acc d input with
       NONE -> toplevel_semi_dex (LENGTH acc) d input = NONE
     | SOME (toks,rest) ->
         toplevel_semi_dex (LENGTH acc) d input = SOME (LENGTH toks) /\
         APPEND (REVERSE acc) input = APPEND toks rest`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LEX2AUX_lex_aux_tokens_clauses; toplevel_semi_dex_def] THEN
  CAKE_REWRITE_TAC[] THEN
  SUBST1_TAC (ISPEC `h:token#A` (GSYM PAIR)) THEN
  REWRITE_TAC[LEX2AUX_lex_aux_tokens_clauses; toplevel_semi_dex_def] THEN
  REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_REVERSE; LENGTH; ADD1; REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  LEX2AUX_TOKENS_IH_TAC);;

let lex_aux_tokens_thm =
  GEN `input:(token#A)list`
    (REWRITE_RULE[LENGTH]
      (SPECL [`input:(token#A)list`; `0`; `[]:(token#A)list`] lex_aux_tokens_thm_1));;

let LEX2AUX_lex_aux_tokens_SOME = prove
 (`!(acc:(token#A)list) d input.
     ~(lex_aux_tokens acc d input = NONE)
     ==> ?ts rest. lex_aux_tokens acc d input = SOME (ts,rest)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `lex_aux_tokens (acc:(token#A)list) d input` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[PAIR_SURJECTIVE]);;

let split_top_level_semi_thm = prove
 (`!input:(token#A)list. split_top_level_semi input = lex_impl_all_tokens input`,
  MATCH_MP_TAC split_top_level_semi_ind THEN GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[split_top_level_semi_def] THEN
  GEN_REWRITE_TAC RAND_CONV [lex_impl_all_tokens_def] THEN
  REWRITE_TAC[lex_until_toplevel_semicolon_tokens_def] THEN
  MP_TAC (SPEC `toks:(token#A)list` lex_aux_tokens_thm) THEN
  ASM_CASES_TAC `lex_aux_tokens [] 0 (toks:(token#A)list) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LEX2AUX_lex_aux_tokens_SOME) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[REVERSE; APPEND] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[TAKE_LENGTH_APPEND; DROP_LENGTH_APPEND] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `LENGTH (ts:(token#A)list)`) THEN
  ASM_REWRITE_TAC[DROP_LENGTH_APPEND]);;

let lexer_correct = prove
 (`!input l. split_top_level_semi (lexer_fun_aux input l) = lex_impl_all input l`,
  REWRITE_TAC[lex_impl_all_tokens_thm; split_top_level_semi_thm]);;
