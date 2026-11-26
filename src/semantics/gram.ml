(* ========================================================================= *)
(* gram: port of HOL4 semantics/gramScript.sml (CakeML v3479).               *)
(* Definition of CakeML's Context-Free Grammar.                              *)
(* The grammar specifies how token lists should be converted to syntax       *)
(* trees.                                                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 makes the type of non-terminals MMLnonT and the grammar cmlG with  *)
(*   the ML tool grammarLib (mk_grammar_def) from the BNF text of the        *)
(*   script; the port writes out what the tool defines, as ordinary          *)
(*   definitions:                                                            *)
(*   . MMLnonT has one constructor nX per non-terminal X, in HOL4's order    *)
(*     (the tool folds the ASCII-sorted set of names onto a list, so the     *)
(*     constructors come in reverse ASCII order: nV, nUQTyOp, ...).          *)
(*   . cmlG is grammar_REC (INL nTopLevelDecs) rules, with rules the updates *)
(*     FEMPTY |+ (INL nX, rhs) |+ ... in the order of the BNF rules; rhs is  *)
(*     the union, associated to the left, of one set per alternative of X:   *)
(*     the singleton of the list of its symbols if it has no token classes   *)
(*     (a quoted literal is TOK of the token of HOL4's tokmap, a             *)
(*     non-terminal Y is NT (INL nY)), else the comprehension over the       *)
(*     arguments of its token classes with condition T and HOL4's variable   *)
(*     names (m for mlstring, p path, i int, c char, n num); for an          *)
(*     antiquoted set of tokens, the same set with each token t replaced by  *)
(*     the list [TOK t].                                                     *)
(*   The ML test at the end of the script (valid_ptree cmlG of a sample      *)
(*   tree, computed and checked, nothing stored) is not ported.              *)
(* - HOL4 overloads mkNT (INL on MMLnonT), NN nt (NT (INL nt)) and TK (TOK   *)
(*   on token) are written out; the type abbreviations NT (HOL4 MMLnonT inf) *)
(*   and mlptree are HOL Light type abbreviations.                           *)
(* - HOL4 mlstring literals are implode of a string literal; a character     *)
(*   literal is CHR of its code.                                             *)
(* - Names from doc/names.tsv: the token constructors IntT, WordT            *)
(*   and CharT are tokens_IntT, tokens_WordT and tokens_CharT (tokens.ml);   *)
(*   Ndl_def and Lfl_def are gram_Ndl_def and gram_Lfl_def.                  *)
(* - nt_distinct_ths (HOL4: for computeLib) is built as in HOL4, from the    *)
(*   distinctness theorem of MMLnonT.                                        *)
(* - Helpers that are not HOL4 names have the prefix PARSE1AUX_.             *)
(* ========================================================================= *)

needs "semantics/tokens.ml";;
needs "hol4/grammar.ml";;

type_invention_error := true;;

let validMultSym_def = cake_def
  `validMultSym s <=> "/" <<= s \/ "*" <<= s \/ "%" <<= s \/ "&" <<= s`;;

(* CHR 94 is the caret (HOL4 writes its character literal with an escape)    *)

let validAddSym_def = cake_def
  `validAddSym s <=>
     ~(s = "") /\ HD s IN {CHR 43, CHR 45, CHR 94} \/
     2 <= LENGTH s /\ HD s = CHR 124`;;

let validRelSym_def = cake_def
  `validRelSym s <=>
     "<" <<= s \/ ">" <<= s \/ (2 <= LENGTH s /\ ("=" <<= s \/ "~" <<= s))`;;

let validListSym_def = cake_def
  `validListSym s <=> "@" <<= s \/ (":" <<= s /\ 2 <= LENGTH s /\ ~(s = ":="))`;;

let validPrefixSym_def = cake_def
  `validPrefixSym s <=> s = "~" \/ "!" <<= s \/ "?" <<= s`;;

let disjneq = prove
 (`!(x:A) y P. ~(x = y) \/ P <=> (x = y ==> P)`,
  MESON_TAC[]);;

(* character facts for the proof below (HOL4 splits on the characters with   *)
(* Cases_on): PARSE1AUX_CHR_CONV turns CHR of a numeral into the character   *)
(* literal of HOL Light (ASCII b7 .. b0, as in string literals);             *)
(* PARSE1AUX_CHAR_CASES_TAC h cs splits on h = c for each literal c of cs    *)
(* and decides the literal equations of each case with CHAR_EQ_CONV.         *)

let PARSE1AUX_CHR_CONV tm =
  match tm with
    Comb(Const("CHR",_),n) when is_numeral n ->
      (REWR_CONV CHR_DEF THENC NUM_REDUCE_CONV) tm
  | _ -> failwith "PARSE1AUX_CHR_CONV";;

let PARSE1AUX_CHAR_CASES_TAC (h:term) (cs:term list) : tactic =
  MAP_EVERY (fun c ->
    ASM_CASES_TAC (mk_eq(h,c)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV CHAR_EQ_CONV) THEN
      REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC]) cs THEN
  ASM_REWRITE_TAC[];;

let validSym_incompatibility = prove
 (`!s. ~(validAddSym s /\ validRelSym s) /\
       ~(validAddSym s /\ validListSym s) /\
       ~(validAddSym s /\ validPrefixSym s) /\
       ~(validAddSym s /\ validMultSym s) /\
       ~(validRelSym s /\ validListSym s) /\
       ~(validRelSym s /\ validPrefixSym s) /\
       ~(validRelSym s /\ validMultSym s) /\
       ~(validListSym s /\ validPrefixSym s) /\
       ~(validListSym s /\ validMultSym s) /\
       ~(validPrefixSym s /\ validMultSym s)`,
  GEN_TAC THEN
  REWRITE_TAC[validRelSym_def; validAddSym_def; validMultSym_def;
              validPrefixSym_def; validListSym_def] THEN
  CONV_TAC(DEPTH_CONV PARSE1AUX_CHR_CONV) THEN
  STRUCT_CASES_TAC(ISPEC `s:string` list_CASES) THEN
  REWRITE_TAC[isPREFIX_THM; NOT_CONS_NIL; LENGTH; ARITH_RULE `~(2 <= 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t:string` list_CASES) THEN
  REWRITE_TAC[isPREFIX_THM; NOT_CONS_NIL; CONS_11; LENGTH; HD; IN_INSERT;
              NOT_IN_EMPTY; ARITH_RULE `~(2 <= SUC 0) /\ 2 <= SUC (SUC n)`] THEN
  PARSE1AUX_CHAR_CASES_TAC `h:char`
    (map mk_char ['+'; '-'; '^'; '|'; '<'; '>'; '='; '~'; '@'; ':'; '!'; '?';
                  '/'; '*'; '%'; '&']));;

(* ------------------------------------------------------------------------- *)
(* The grammar (HOL4: mk_grammar_def ginfo applied to the BNF text).         *)
(* ------------------------------------------------------------------------- *)

let MMLnonT_INDUCT,MMLnonT_RECURSION = cake_type
  "MMLnonT =
     nV | nUQTyOp | nUQConstructorName | nTyvarN | nTypeName | nTypeList2
   | nTypeList1 | nTypeDec | nTypeAbbrevDec | nType | nTyVarList | nTyOp
   | nTopLevelDecs | nTbaseList | nTbase | nStructure | nStructName
   | nSpecLineList | nSpecLine | nSignatureValue | nRelOps | nPtuple | nPcons
   | nPbaseList1 | nPbase | nPatternList | nPattern | nPas | nPapp | nPType
   | nPTbase | nPEsfx | nPEs | nPE | nPConApp | nOptionalSignatureAscription
   | nOptTypEqn | nOpID | nNonETopLevelDecs | nMultOps | nListOps | nLetDecs
   | nLetDec | nFQV | nFDecl | nEtyped | nEtuple | nEseq | nErel | nEmult
   | nElogicOR | nElogicAND | nEliteral | nElistop | nElist2 | nElist1
   | nEhandle | nEcomp | nEbefore | nEbase | nEapp | nEadd | nE | nDtypeDecls
   | nDtypeDecl | nDtypeCons | nDecls | nDecl | nDconstructor | nDType
   | nConstructorName | nCompOps | nAndFDecls | nAddOps";;

let cmlG_def = new_definition
`cmlG:(token,MMLnonT)grammar =
   grammar_REC (INL nTopLevelDecs)
  (FEMPTY
   |+ (INL nUQTyOp,
         {[grammar_TOK (AlphaT m)] | m | T} UNION
         {[grammar_TOK (SymbolT m)] | m | T})
   |+ (INL nTyvarN,
         {[grammar_TOK (TyvarT m)] | m | T})
   |+ (INL nTyOp,
         {[grammar_NT (INL nUQTyOp)]} UNION
         {[grammar_TOK (LongidT p m)] | m,p | T})
   |+ (INL nTypeList1,
         {[grammar_NT (INL nType)]} UNION
         {[grammar_NT (INL nType); grammar_TOK CommaT; grammar_NT (INL nTypeList1)]})
   |+ (INL nTypeList2,
         {[grammar_NT (INL nType); grammar_TOK CommaT; grammar_NT (INL nTypeList1)]})
   |+ (INL nTbase,
         (({[grammar_TOK (TyvarT m)] | m | T} UNION
         {[grammar_NT (INL nTyOp)]}) UNION
         {[grammar_TOK LparT; grammar_NT (INL nTypeList2); grammar_TOK RparT; grammar_NT (INL nTyOp)]}) UNION
         {[grammar_TOK LparT; grammar_NT (INL nType); grammar_TOK RparT]})
   |+ (INL nDType,
         {[grammar_NT (INL nDType); grammar_NT (INL nTyOp)]} UNION
         {[grammar_NT (INL nTbase)]})
   |+ (INL nPType,
         {[grammar_NT (INL nDType); grammar_TOK StarT; grammar_NT (INL nPType)]} UNION
         {[grammar_NT (INL nDType)]})
   |+ (INL nType,
         {[grammar_NT (INL nPType)]} UNION
         {[grammar_NT (INL nPType); grammar_TOK ArrowT; grammar_NT (INL nType)]})
   |+ (INL nTbaseList,
         {[]} UNION
         {[grammar_NT (INL nPTbase); grammar_NT (INL nTbaseList)]})
   |+ (INL nPTbase,
         ({[grammar_TOK (TyvarT m)] | m | T} UNION
         {[grammar_NT (INL nTyOp)]}) UNION
         {[grammar_TOK LparT; grammar_NT (INL nType); grammar_TOK RparT]})
   |+ (INL nTypeName,
         ({[grammar_NT (INL nUQTyOp)]} UNION
         {[grammar_TOK LparT; grammar_NT (INL nTyVarList); grammar_TOK RparT; grammar_NT (INL nUQTyOp)]}) UNION
         {[grammar_TOK (TyvarT m); grammar_NT (INL nUQTyOp)] | m | T})
   |+ (INL nTyVarList,
         {[grammar_NT (INL nTyvarN)]} UNION
         {[grammar_NT (INL nTyVarList); grammar_TOK CommaT; grammar_NT (INL nTyvarN)]})
   |+ (INL nDconstructor,
         {[grammar_NT (INL nUQConstructorName); grammar_NT (INL nTbaseList)]})
   |+ (INL nDtypeCons,
         {[grammar_NT (INL nDconstructor)]} UNION
         {[grammar_NT (INL nDtypeCons); grammar_TOK BarT; grammar_NT (INL nDconstructor)]})
   |+ (INL nDtypeDecl,
         {[grammar_NT (INL nTypeName); grammar_TOK EqualsT; grammar_NT (INL nDtypeCons)]})
   |+ (INL nDtypeDecls,
         {[grammar_NT (INL nDtypeDecl)]} UNION
         {[grammar_NT (INL nDtypeDecls); grammar_TOK AndT; grammar_NT (INL nDtypeDecl)]})
   |+ (INL nTypeDec,
         {[grammar_TOK DatatypeT; grammar_NT (INL nDtypeDecls)]})
   |+ (INL nTypeAbbrevDec,
         {[grammar_TOK TypeT; grammar_NT (INL nTypeName); grammar_TOK EqualsT; grammar_NT (INL nType)]})
   |+ (INL nUQConstructorName,
         {[grammar_TOK (AlphaT s)] | s | ~(s = implode "") /\ isUpper (strsub s 0)})
   |+ (INL nConstructorName,
         {[grammar_NT (INL nUQConstructorName)]} UNION
         {[grammar_TOK (LongidT str s)] | str,s |
          ~(s = implode "") /\ isAlpha (strsub s 0) /\ isUpper (strsub s 0)})
   |+ (INL nV,
         {[grammar_TOK (AlphaT s)] | s |
          ~(s IN {implode "before", implode "div", implode "mod", implode "o"}) /\
          ~(s = implode "") /\ ~isUpper (strsub s 0)} UNION
         {[grammar_TOK (SymbolT s)] | s | validPrefixSym (explode s)})
   |+ (INL nFQV,
         {[grammar_NT (INL nV)]} UNION
         {[grammar_TOK (LongidT str s)] | str,s |
          ~(s = implode "") /\ (isAlpha (strsub s 0) ==> ~isUpper (strsub s 0))})
   |+ (INL nOpID,
         ((({[grammar_TOK (LongidT str s)] | str,s | ~(s = implode "")} UNION
         {[grammar_TOK (AlphaT s)] | s | ~(s = implode "")}) UNION
         {[grammar_TOK (SymbolT s)] | s | ~(s = implode "")}) UNION
         {[grammar_TOK StarT]}) UNION
         {[grammar_TOK EqualsT]})
   |+ (INL nEliteral,
         ((({[grammar_TOK (tokens_IntT i)] | i | T} UNION
         {[grammar_TOK (tokens_CharT c)] | c | T}) UNION
         {[grammar_TOK (StringT m)] | m | T}) UNION
         {[grammar_TOK (tokens_WordT n)] | n | T}) UNION
         {[grammar_TOK (FFIT m)] | m | T})
   |+ (INL nEbase,
         (((((((({[grammar_TOK LparT; grammar_NT (INL nEseq); grammar_TOK RparT]} UNION
         {[grammar_NT (INL nEtuple)]}) UNION
         {[grammar_TOK LparT; grammar_TOK RparT]}) UNION
         {[grammar_NT (INL nFQV)]}) UNION
         {[grammar_NT (INL nConstructorName)]}) UNION
         {[grammar_NT (INL nEliteral)]}) UNION
         {[grammar_TOK LetT; grammar_NT (INL nLetDecs); grammar_TOK InT; grammar_NT (INL nEseq); grammar_TOK EndT]}) UNION
         {[grammar_TOK LbrackT; grammar_TOK RbrackT]}) UNION
         {[grammar_TOK LbrackT; grammar_NT (INL nElist1); grammar_TOK RbrackT]}) UNION
         {[grammar_TOK OpT; grammar_NT (INL nOpID)]})
   |+ (INL nEseq,
         {[grammar_NT (INL nE); grammar_TOK SemicolonT; grammar_NT (INL nEseq)]} UNION
         {[grammar_NT (INL nE)]})
   |+ (INL nEtuple,
         {[grammar_TOK LparT; grammar_NT (INL nElist2); grammar_TOK RparT]})
   |+ (INL nElist2,
         {[grammar_NT (INL nE); grammar_TOK CommaT; grammar_NT (INL nElist1)]})
   |+ (INL nElist1,
         {[grammar_NT (INL nE)]} UNION
         {[grammar_NT (INL nE); grammar_TOK CommaT; grammar_NT (INL nElist1)]})
   |+ (INL nEapp,
         {[grammar_NT (INL nEapp); grammar_NT (INL nEbase)]} UNION
         {[grammar_NT (INL nEbase)]})
   |+ (INL nMultOps,
         {[grammar_TOK (AlphaT (implode "div"))], [grammar_TOK (AlphaT (implode "mod"))],
          [grammar_TOK StarT]} UNION
         {[grammar_TOK (SymbolT s)] | s | validMultSym (explode s)})
   |+ (INL nAddOps,
         {[grammar_TOK (SymbolT s)] | s | validAddSym (explode s)})
   |+ (INL nRelOps,
         {[grammar_TOK (SymbolT s)] | s | validRelSym (explode s)} UNION
         {[grammar_TOK EqualsT]})
   |+ (INL nCompOps,
         {[grammar_TOK (AlphaT (implode "o"))]} UNION
         {[grammar_TOK (SymbolT (implode ":="))]})
   |+ (INL nListOps,
         {[grammar_TOK (SymbolT s)] | s | validListSym (explode s)})
   |+ (INL nEmult,
         {[grammar_NT (INL nEmult); grammar_NT (INL nMultOps); grammar_NT (INL nEapp)]} UNION
         {[grammar_NT (INL nEapp)]})
   |+ (INL nEadd,
         {[grammar_NT (INL nEadd); grammar_NT (INL nAddOps); grammar_NT (INL nEmult)]} UNION
         {[grammar_NT (INL nEmult)]})
   |+ (INL nElistop,
         {[grammar_NT (INL nEadd); grammar_NT (INL nListOps); grammar_NT (INL nElistop)]} UNION
         {[grammar_NT (INL nEadd)]})
   |+ (INL nErel,
         {[grammar_NT (INL nErel); grammar_NT (INL nRelOps); grammar_NT (INL nElistop)]} UNION
         {[grammar_NT (INL nElistop)]})
   |+ (INL nEcomp,
         {[grammar_NT (INL nEcomp); grammar_NT (INL nCompOps); grammar_NT (INL nErel)]} UNION
         {[grammar_NT (INL nErel)]})
   |+ (INL nEbefore,
         {[grammar_NT (INL nEbefore); grammar_TOK (AlphaT (implode "before")); grammar_NT (INL nEcomp)]} UNION
         {[grammar_NT (INL nEcomp)]})
   |+ (INL nEtyped,
         {[grammar_NT (INL nEbefore)]} UNION
         {[grammar_NT (INL nEbefore); grammar_TOK ColonT; grammar_NT (INL nType)]})
   |+ (INL nElogicAND,
         {[grammar_NT (INL nElogicAND); grammar_TOK AndalsoT; grammar_NT (INL nEtyped)]} UNION
         {[grammar_NT (INL nEtyped)]})
   |+ (INL nElogicOR,
         {[grammar_NT (INL nElogicOR); grammar_TOK OrelseT; grammar_NT (INL nElogicAND)]} UNION
         {[grammar_NT (INL nElogicAND)]})
   |+ (INL nEhandle,
         {[grammar_NT (INL nElogicOR)]} UNION
         {[grammar_NT (INL nElogicOR); grammar_TOK HandleT; grammar_NT (INL nPEs)]})
   |+ (INL nE,
         ((({[grammar_TOK IfT; grammar_NT (INL nE); grammar_TOK ThenT; grammar_NT (INL nE); grammar_TOK ElseT; grammar_NT (INL nE)]} UNION
         {[grammar_TOK CaseT; grammar_NT (INL nE); grammar_TOK OfT; grammar_NT (INL nPEs)]}) UNION
         {[grammar_TOK FnT; grammar_NT (INL nPattern); grammar_TOK DarrowT; grammar_NT (INL nE)]}) UNION
         {[grammar_TOK RaiseT; grammar_NT (INL nE)]}) UNION
         {[grammar_NT (INL nEhandle)]})
   |+ (INL nFDecl,
         {[grammar_NT (INL nV); grammar_NT (INL nPbaseList1); grammar_TOK EqualsT; grammar_NT (INL nE)]})
   |+ (INL nAndFDecls,
         {[grammar_NT (INL nFDecl)]} UNION
         {[grammar_NT (INL nAndFDecls); grammar_TOK AndT; grammar_NT (INL nFDecl)]})
   |+ (INL nLetDec,
         {[grammar_TOK ValT; grammar_NT (INL nPattern); grammar_TOK EqualsT; grammar_NT (INL nE)]} UNION
         {[grammar_TOK FunT; grammar_NT (INL nAndFDecls)]})
   |+ (INL nLetDecs,
         ({[grammar_NT (INL nLetDec); grammar_NT (INL nLetDecs)]} UNION
         {[grammar_TOK SemicolonT; grammar_NT (INL nLetDecs)]}) UNION
         {[]})
   |+ (INL nPbase,
         (((((((({[grammar_NT (INL nV)]} UNION
         {[grammar_NT (INL nConstructorName)]}) UNION
         {[grammar_TOK (tokens_IntT i)] | i | T}) UNION
         {[grammar_TOK (StringT m)] | m | T}) UNION
         {[grammar_TOK (tokens_CharT c)] | c | T}) UNION
         {[grammar_NT (INL nPtuple)]}) UNION
         {[grammar_TOK UnderbarT]}) UNION
         {[grammar_TOK LbrackT; grammar_TOK RbrackT]}) UNION
         {[grammar_TOK LbrackT; grammar_NT (INL nPatternList); grammar_TOK RbrackT]}) UNION
         {[grammar_TOK OpT; grammar_NT (INL nOpID)]})
   |+ (INL nPConApp,
         {[grammar_NT (INL nConstructorName)]} UNION
         {[grammar_NT (INL nPConApp); grammar_NT (INL nPbase)]})
   |+ (INL nPapp,
         {[grammar_NT (INL nPConApp); grammar_NT (INL nPbase)]} UNION
         {[grammar_NT (INL nPbase)]})
   |+ (INL nPcons,
         {[grammar_NT (INL nPapp); grammar_TOK (SymbolT (implode "::")); grammar_NT (INL nPcons)]} UNION
         {[grammar_NT (INL nPapp)]})
   |+ (INL nPas,
         {[grammar_NT (INL nV); grammar_TOK AsT; grammar_NT (INL nPcons)]} UNION
         {[grammar_NT (INL nPcons)]})
   |+ (INL nPattern,
         {[grammar_NT (INL nPas)]} UNION
         {[grammar_NT (INL nPas); grammar_TOK ColonT; grammar_NT (INL nType)]})
   |+ (INL nPtuple,
         {[grammar_TOK LparT; grammar_TOK RparT]} UNION
         {[grammar_TOK LparT; grammar_NT (INL nPatternList); grammar_TOK RparT]})
   |+ (INL nPatternList,
         {[grammar_NT (INL nPattern)]} UNION
         {[grammar_NT (INL nPattern); grammar_TOK CommaT; grammar_NT (INL nPatternList)]})
   |+ (INL nPbaseList1,
         {[grammar_NT (INL nPbase)]} UNION
         {[grammar_NT (INL nPbase); grammar_NT (INL nPbaseList1)]})
   |+ (INL nPE,
         ((({[grammar_TOK CaseT; grammar_NT (INL nE); grammar_TOK OfT; grammar_NT (INL nPEs)]} UNION
         {[grammar_TOK IfT; grammar_NT (INL nE); grammar_TOK ThenT; grammar_NT (INL nE); grammar_TOK ElseT; grammar_NT (INL nPE)]}) UNION
         {[grammar_TOK FnT; grammar_NT (INL nPattern); grammar_TOK DarrowT; grammar_NT (INL nE)]}) UNION
         {[grammar_TOK RaiseT; grammar_NT (INL nPE)]}) UNION
         {[grammar_NT (INL nElogicOR); grammar_NT (INL nPEsfx)]})
   |+ (INL nPEsfx,
         ({[]} UNION
         {[grammar_TOK HandleT; grammar_NT (INL nPEs)]}) UNION
         {[grammar_TOK BarT; grammar_NT (INL nPEs)]})
   |+ (INL nPEs,
         {[grammar_NT (INL nPattern); grammar_TOK DarrowT; grammar_NT (INL nPE)]})
   |+ (INL nStructName,
         {[grammar_TOK (AlphaT s)] | s | ~(s = implode "")})
   |+ (INL nSpecLine,
         (({[grammar_TOK ValT; grammar_NT (INL nV); grammar_TOK ColonT; grammar_NT (INL nType)]} UNION
         {[grammar_TOK TypeT; grammar_NT (INL nTypeName); grammar_NT (INL nOptTypEqn)]}) UNION
         {[grammar_TOK ExceptionT; grammar_NT (INL nDconstructor)]}) UNION
         {[grammar_NT (INL nTypeDec)]})
   |+ (INL nOptTypEqn,
         {[grammar_TOK EqualsT; grammar_NT (INL nType)]} UNION
         {[]})
   |+ (INL nSpecLineList,
         ({[grammar_NT (INL nSpecLine); grammar_NT (INL nSpecLineList)]} UNION
         {[grammar_TOK SemicolonT; grammar_NT (INL nSpecLineList)]}) UNION
         {[]})
   |+ (INL nSignatureValue,
         {[grammar_TOK SigT; grammar_NT (INL nSpecLineList); grammar_TOK EndT]})
   |+ (INL nOptionalSignatureAscription,
         {[grammar_TOK SealT; grammar_NT (INL nSignatureValue)]} UNION
         {[]})
   |+ (INL nDecl,
         ((((({[grammar_TOK ValT; grammar_NT (INL nPattern); grammar_TOK EqualsT; grammar_NT (INL nE)]} UNION
         {[grammar_TOK FunT; grammar_NT (INL nAndFDecls)]}) UNION
         {[grammar_NT (INL nTypeDec)]}) UNION
         {[grammar_TOK ExceptionT; grammar_NT (INL nDconstructor)]}) UNION
         {[grammar_NT (INL nTypeAbbrevDec)]}) UNION
         {[grammar_TOK LocalT; grammar_NT (INL nDecls); grammar_TOK InT; grammar_NT (INL nDecls); grammar_TOK EndT]}) UNION
         {[grammar_NT (INL nStructure)]})
   |+ (INL nDecls,
         ({[grammar_NT (INL nDecl); grammar_NT (INL nDecls)]} UNION
         {[grammar_TOK SemicolonT; grammar_NT (INL nDecls)]}) UNION
         {[]})
   |+ (INL nStructure,
         {[grammar_TOK StructureT; grammar_NT (INL nStructName);
           grammar_NT (INL nOptionalSignatureAscription); grammar_TOK EqualsT; grammar_TOK StructT;
           grammar_NT (INL nDecls); grammar_TOK EndT]})
   |+ (INL nTopLevelDecs,
         (({[grammar_NT (INL nE); grammar_TOK SemicolonT; grammar_NT (INL nTopLevelDecs)]} UNION
         {[grammar_NT (INL nDecl); grammar_NT (INL nNonETopLevelDecs)]}) UNION
         {[grammar_TOK SemicolonT; grammar_NT (INL nTopLevelDecs)]}) UNION
         {[]})
   |+ (INL nNonETopLevelDecs,
         ({[grammar_NT (INL nDecl); grammar_NT (INL nNonETopLevelDecs)]} UNION
         {[grammar_TOK SemicolonT; grammar_NT (INL nTopLevelDecs)]}) UNION
         {[]}))`
;;

(* HOL4: Type NT = MMLnonT inf                                               *)
new_type_abbrev("NT",`:MMLnonT + num`);;

(* HOL4 overloads mkNT (INL on MMLnonT), NN nt (NT (INL nt)) and TK (TOK on  *)
(* token): written out                                                       *)

(* HOL4: Type mlptree = (token, MMLnonT, locs) parsetree                     *)
new_type_abbrev("mlptree",`:(token,MMLnonT,locs)parsetree`);;

(* HOL4 saves the conjunction of the equations (n1 = n2) <=> F and           *)
(* (n2 = n1) <=> F for every pair of constructors n1 before n2               *)

let nt_distinct_ths =
  let cs = map rhs (disjuncts(snd(dest_forall(concl(cases "MMLnonT"))))) in
  let tbl = Hashtbl.create 6000 in
  let name c = fst(dest_const c) in
  do_list (fun th ->
      let l,r = dest_eq(dest_neg(concl th)) in
      Hashtbl.replace tbl (name l,name r) (EQF_INTRO th);
      Hashtbl.replace tbl (name r,name l) (EQF_INTRO(GSYM th)))
    (CONJUNCTS(distinctness "MMLnonT"));
  let rec recurse l =
    match l with
      [] -> []
    | t::ts ->
        map (fun t' -> Hashtbl.find tbl (name t,name t')) ts @
        map (fun t' -> Hashtbl.find tbl (name t',name t)) ts @ recurse ts in
  end_itlist CONJ (recurse cs);;

let gram_Ndl_def = cake_def
  `Ndl (n:B+num) (l:((A,B,locs)parsetree)list) = grammar_Nd (n,unknown_loc) l`;;

let gram_Lfl_def = cake_def
  `Lfl (t:(A,B)symbol) = grammar_Lf (t,unknown_loc):(A,B,locs)parsetree`;;
