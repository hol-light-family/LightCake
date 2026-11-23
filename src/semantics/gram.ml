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
         {[TOK (AlphaT m)] | m | T} UNION
         {[TOK (SymbolT m)] | m | T})
   |+ (INL nTyvarN,
         {[TOK (TyvarT m)] | m | T})
   |+ (INL nTyOp,
         {[NT (INL nUQTyOp)]} UNION
         {[TOK (LongidT p m)] | m,p | T})
   |+ (INL nTypeList1,
         {[NT (INL nType)]} UNION
         {[NT (INL nType); TOK CommaT; NT (INL nTypeList1)]})
   |+ (INL nTypeList2,
         {[NT (INL nType); TOK CommaT; NT (INL nTypeList1)]})
   |+ (INL nTbase,
         (({[TOK (TyvarT m)] | m | T} UNION
         {[NT (INL nTyOp)]}) UNION
         {[TOK LparT; NT (INL nTypeList2); TOK RparT; NT (INL nTyOp)]}) UNION
         {[TOK LparT; NT (INL nType); TOK RparT]})
   |+ (INL nDType,
         {[NT (INL nDType); NT (INL nTyOp)]} UNION
         {[NT (INL nTbase)]})
   |+ (INL nPType,
         {[NT (INL nDType); TOK StarT; NT (INL nPType)]} UNION
         {[NT (INL nDType)]})
   |+ (INL nType,
         {[NT (INL nPType)]} UNION
         {[NT (INL nPType); TOK ArrowT; NT (INL nType)]})
   |+ (INL nTbaseList,
         {[]} UNION
         {[NT (INL nPTbase); NT (INL nTbaseList)]})
   |+ (INL nPTbase,
         ({[TOK (TyvarT m)] | m | T} UNION
         {[NT (INL nTyOp)]}) UNION
         {[TOK LparT; NT (INL nType); TOK RparT]})
   |+ (INL nTypeName,
         ({[NT (INL nUQTyOp)]} UNION
         {[TOK LparT; NT (INL nTyVarList); TOK RparT; NT (INL nUQTyOp)]}) UNION
         {[TOK (TyvarT m); NT (INL nUQTyOp)] | m | T})
   |+ (INL nTyVarList,
         {[NT (INL nTyvarN)]} UNION
         {[NT (INL nTyVarList); TOK CommaT; NT (INL nTyvarN)]})
   |+ (INL nDconstructor,
         {[NT (INL nUQConstructorName); NT (INL nTbaseList)]})
   |+ (INL nDtypeCons,
         {[NT (INL nDconstructor)]} UNION
         {[NT (INL nDtypeCons); TOK BarT; NT (INL nDconstructor)]})
   |+ (INL nDtypeDecl,
         {[NT (INL nTypeName); TOK EqualsT; NT (INL nDtypeCons)]})
   |+ (INL nDtypeDecls,
         {[NT (INL nDtypeDecl)]} UNION
         {[NT (INL nDtypeDecls); TOK AndT; NT (INL nDtypeDecl)]})
   |+ (INL nTypeDec,
         {[TOK DatatypeT; NT (INL nDtypeDecls)]})
   |+ (INL nTypeAbbrevDec,
         {[TOK TypeT; NT (INL nTypeName); TOK EqualsT; NT (INL nType)]})
   |+ (INL nUQConstructorName,
         {[TOK (AlphaT s)] | s | ~(s = implode "") /\ isUpper (strsub s 0)})
   |+ (INL nConstructorName,
         {[NT (INL nUQConstructorName)]} UNION
         {[TOK (LongidT str s)] | str,s |
          ~(s = implode "") /\ isAlpha (strsub s 0) /\ isUpper (strsub s 0)})
   |+ (INL nV,
         {[TOK (AlphaT s)] | s |
          ~(s IN {implode "before", implode "div", implode "mod", implode "o"}) /\
          ~(s = implode "") /\ ~isUpper (strsub s 0)} UNION
         {[TOK (SymbolT s)] | s | validPrefixSym (explode s)})
   |+ (INL nFQV,
         {[NT (INL nV)]} UNION
         {[TOK (LongidT str s)] | str,s |
          ~(s = implode "") /\ (isAlpha (strsub s 0) ==> ~isUpper (strsub s 0))})
   |+ (INL nOpID,
         ((({[TOK (LongidT str s)] | str,s | ~(s = implode "")} UNION
         {[TOK (AlphaT s)] | s | ~(s = implode "")}) UNION
         {[TOK (SymbolT s)] | s | ~(s = implode "")}) UNION
         {[TOK StarT]}) UNION
         {[TOK EqualsT]})
   |+ (INL nEliteral,
         ((({[TOK (tokens_IntT i)] | i | T} UNION
         {[TOK (tokens_CharT c)] | c | T}) UNION
         {[TOK (StringT m)] | m | T}) UNION
         {[TOK (tokens_WordT n)] | n | T}) UNION
         {[TOK (FFIT m)] | m | T})
   |+ (INL nEbase,
         (((((((({[TOK LparT; NT (INL nEseq); TOK RparT]} UNION
         {[NT (INL nEtuple)]}) UNION
         {[TOK LparT; TOK RparT]}) UNION
         {[NT (INL nFQV)]}) UNION
         {[NT (INL nConstructorName)]}) UNION
         {[NT (INL nEliteral)]}) UNION
         {[TOK LetT; NT (INL nLetDecs); TOK InT; NT (INL nEseq); TOK EndT]}) UNION
         {[TOK LbrackT; TOK RbrackT]}) UNION
         {[TOK LbrackT; NT (INL nElist1); TOK RbrackT]}) UNION
         {[TOK OpT; NT (INL nOpID)]})
   |+ (INL nEseq,
         {[NT (INL nE); TOK SemicolonT; NT (INL nEseq)]} UNION
         {[NT (INL nE)]})
   |+ (INL nEtuple,
         {[TOK LparT; NT (INL nElist2); TOK RparT]})
   |+ (INL nElist2,
         {[NT (INL nE); TOK CommaT; NT (INL nElist1)]})
   |+ (INL nElist1,
         {[NT (INL nE)]} UNION
         {[NT (INL nE); TOK CommaT; NT (INL nElist1)]})
   |+ (INL nEapp,
         {[NT (INL nEapp); NT (INL nEbase)]} UNION
         {[NT (INL nEbase)]})
   |+ (INL nMultOps,
         {[TOK (AlphaT (implode "div"))], [TOK (AlphaT (implode "mod"))],
          [TOK StarT]} UNION
         {[TOK (SymbolT s)] | s | validMultSym (explode s)})
   |+ (INL nAddOps,
         {[TOK (SymbolT s)] | s | validAddSym (explode s)})
   |+ (INL nRelOps,
         {[TOK (SymbolT s)] | s | validRelSym (explode s)} UNION
         {[TOK EqualsT]})
   |+ (INL nCompOps,
         {[TOK (AlphaT (implode "o"))]} UNION
         {[TOK (SymbolT (implode ":="))]})
   |+ (INL nListOps,
         {[TOK (SymbolT s)] | s | validListSym (explode s)})
   |+ (INL nEmult,
         {[NT (INL nEmult); NT (INL nMultOps); NT (INL nEapp)]} UNION
         {[NT (INL nEapp)]})
   |+ (INL nEadd,
         {[NT (INL nEadd); NT (INL nAddOps); NT (INL nEmult)]} UNION
         {[NT (INL nEmult)]})
   |+ (INL nElistop,
         {[NT (INL nEadd); NT (INL nListOps); NT (INL nElistop)]} UNION
         {[NT (INL nEadd)]})
   |+ (INL nErel,
         {[NT (INL nErel); NT (INL nRelOps); NT (INL nElistop)]} UNION
         {[NT (INL nElistop)]})
   |+ (INL nEcomp,
         {[NT (INL nEcomp); NT (INL nCompOps); NT (INL nErel)]} UNION
         {[NT (INL nErel)]})
   |+ (INL nEbefore,
         {[NT (INL nEbefore); TOK (AlphaT (implode "before")); NT (INL nEcomp)]} UNION
         {[NT (INL nEcomp)]})
   |+ (INL nEtyped,
         {[NT (INL nEbefore)]} UNION
         {[NT (INL nEbefore); TOK ColonT; NT (INL nType)]})
   |+ (INL nElogicAND,
         {[NT (INL nElogicAND); TOK AndalsoT; NT (INL nEtyped)]} UNION
         {[NT (INL nEtyped)]})
   |+ (INL nElogicOR,
         {[NT (INL nElogicOR); TOK OrelseT; NT (INL nElogicAND)]} UNION
         {[NT (INL nElogicAND)]})
   |+ (INL nEhandle,
         {[NT (INL nElogicOR)]} UNION
         {[NT (INL nElogicOR); TOK HandleT; NT (INL nPEs)]})
   |+ (INL nE,
         ((({[TOK IfT; NT (INL nE); TOK ThenT; NT (INL nE); TOK ElseT; NT (INL nE)]} UNION
         {[TOK CaseT; NT (INL nE); TOK OfT; NT (INL nPEs)]}) UNION
         {[TOK FnT; NT (INL nPattern); TOK DarrowT; NT (INL nE)]}) UNION
         {[TOK RaiseT; NT (INL nE)]}) UNION
         {[NT (INL nEhandle)]})
   |+ (INL nFDecl,
         {[NT (INL nV); NT (INL nPbaseList1); TOK EqualsT; NT (INL nE)]})
   |+ (INL nAndFDecls,
         {[NT (INL nFDecl)]} UNION
         {[NT (INL nAndFDecls); TOK AndT; NT (INL nFDecl)]})
   |+ (INL nLetDec,
         {[TOK ValT; NT (INL nPattern); TOK EqualsT; NT (INL nE)]} UNION
         {[TOK FunT; NT (INL nAndFDecls)]})
   |+ (INL nLetDecs,
         ({[NT (INL nLetDec); NT (INL nLetDecs)]} UNION
         {[TOK SemicolonT; NT (INL nLetDecs)]}) UNION
         {[]})
   |+ (INL nPbase,
         (((((((({[NT (INL nV)]} UNION
         {[NT (INL nConstructorName)]}) UNION
         {[TOK (tokens_IntT i)] | i | T}) UNION
         {[TOK (StringT m)] | m | T}) UNION
         {[TOK (tokens_CharT c)] | c | T}) UNION
         {[NT (INL nPtuple)]}) UNION
         {[TOK UnderbarT]}) UNION
         {[TOK LbrackT; TOK RbrackT]}) UNION
         {[TOK LbrackT; NT (INL nPatternList); TOK RbrackT]}) UNION
         {[TOK OpT; NT (INL nOpID)]})
   |+ (INL nPConApp,
         {[NT (INL nConstructorName)]} UNION
         {[NT (INL nPConApp); NT (INL nPbase)]})
   |+ (INL nPapp,
         {[NT (INL nPConApp); NT (INL nPbase)]} UNION
         {[NT (INL nPbase)]})
   |+ (INL nPcons,
         {[NT (INL nPapp); TOK (SymbolT (implode "::")); NT (INL nPcons)]} UNION
         {[NT (INL nPapp)]})
   |+ (INL nPas,
         {[NT (INL nV); TOK AsT; NT (INL nPcons)]} UNION
         {[NT (INL nPcons)]})
   |+ (INL nPattern,
         {[NT (INL nPas)]} UNION
         {[NT (INL nPas); TOK ColonT; NT (INL nType)]})
   |+ (INL nPtuple,
         {[TOK LparT; TOK RparT]} UNION
         {[TOK LparT; NT (INL nPatternList); TOK RparT]})
   |+ (INL nPatternList,
         {[NT (INL nPattern)]} UNION
         {[NT (INL nPattern); TOK CommaT; NT (INL nPatternList)]})
   |+ (INL nPbaseList1,
         {[NT (INL nPbase)]} UNION
         {[NT (INL nPbase); NT (INL nPbaseList1)]})
   |+ (INL nPE,
         ((({[TOK CaseT; NT (INL nE); TOK OfT; NT (INL nPEs)]} UNION
         {[TOK IfT; NT (INL nE); TOK ThenT; NT (INL nE); TOK ElseT; NT (INL nPE)]}) UNION
         {[TOK FnT; NT (INL nPattern); TOK DarrowT; NT (INL nE)]}) UNION
         {[TOK RaiseT; NT (INL nPE)]}) UNION
         {[NT (INL nElogicOR); NT (INL nPEsfx)]})
   |+ (INL nPEsfx,
         ({[]} UNION
         {[TOK HandleT; NT (INL nPEs)]}) UNION
         {[TOK BarT; NT (INL nPEs)]})
   |+ (INL nPEs,
         {[NT (INL nPattern); TOK DarrowT; NT (INL nPE)]})
   |+ (INL nStructName,
         {[TOK (AlphaT s)] | s | ~(s = implode "")})
   |+ (INL nSpecLine,
         (({[TOK ValT; NT (INL nV); TOK ColonT; NT (INL nType)]} UNION
         {[TOK TypeT; NT (INL nTypeName); NT (INL nOptTypEqn)]}) UNION
         {[TOK ExceptionT; NT (INL nDconstructor)]}) UNION
         {[NT (INL nTypeDec)]})
   |+ (INL nOptTypEqn,
         {[TOK EqualsT; NT (INL nType)]} UNION
         {[]})
   |+ (INL nSpecLineList,
         ({[NT (INL nSpecLine); NT (INL nSpecLineList)]} UNION
         {[TOK SemicolonT; NT (INL nSpecLineList)]}) UNION
         {[]})
   |+ (INL nSignatureValue,
         {[TOK SigT; NT (INL nSpecLineList); TOK EndT]})
   |+ (INL nOptionalSignatureAscription,
         {[TOK SealT; NT (INL nSignatureValue)]} UNION
         {[]})
   |+ (INL nDecl,
         ((((({[TOK ValT; NT (INL nPattern); TOK EqualsT; NT (INL nE)]} UNION
         {[TOK FunT; NT (INL nAndFDecls)]}) UNION
         {[NT (INL nTypeDec)]}) UNION
         {[TOK ExceptionT; NT (INL nDconstructor)]}) UNION
         {[NT (INL nTypeAbbrevDec)]}) UNION
         {[TOK LocalT; NT (INL nDecls); TOK InT; NT (INL nDecls); TOK EndT]}) UNION
         {[NT (INL nStructure)]})
   |+ (INL nDecls,
         ({[NT (INL nDecl); NT (INL nDecls)]} UNION
         {[TOK SemicolonT; NT (INL nDecls)]}) UNION
         {[]})
   |+ (INL nStructure,
         {[TOK StructureT; NT (INL nStructName);
           NT (INL nOptionalSignatureAscription); TOK EqualsT; TOK StructT;
           NT (INL nDecls); TOK EndT]})
   |+ (INL nTopLevelDecs,
         (({[NT (INL nE); TOK SemicolonT; NT (INL nTopLevelDecs)]} UNION
         {[NT (INL nDecl); NT (INL nNonETopLevelDecs)]}) UNION
         {[TOK SemicolonT; NT (INL nTopLevelDecs)]}) UNION
         {[]})
   |+ (INL nNonETopLevelDecs,
         ({[NT (INL nDecl); NT (INL nNonETopLevelDecs)]} UNION
         {[TOK SemicolonT; NT (INL nTopLevelDecs)]}) UNION
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
  `Ndl (n:B+num) (l:((A,B,locs)parsetree)list) = Nd (n,unknown_loc) l`;;

let gram_Lfl_def = cake_def
  `Lfl (t:(A,B)symbol) = Lf (t,unknown_loc):(A,B,locs)parsetree`;;
