(* ========================================================================= *)
(* cmlPEG: port of HOL4 compiler/parsing/cmlPEGScript.sml (CakeML v3479).    *)
(* Definition of the PEG for CakeML.                                         *)
(* Includes a proof that the PEG is well-formed.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's overloads mkNT (INL on MMLnonT) and TK (TOK on token) and its    *)
(*   monad syntax are written out: do s <- e; assert P od is                 *)
(*   OPTION_BIND e (\s. OPTION_GUARD P), with one for HOL4's ().  FOLDR f e l *)
(*   is ITLIST f l e, (++) is APPEND, mlstring literals are implode of a     *)
(*   string literal, the record literal of cmlPEG is peg_REC with the fields *)
(*   start, anyEOF, tokFALSE, tokEOF, notFAIL, rules.                        *)
(* - cmlPEG's own sumID, choicel, pegf and tokeq keep their HOL4 names (the  *)
(*   PEG library's are peg_choicel and peg_pegf); the definitions are        *)
(*   as polymorphic as HOL4's.  mk_linfix_ind, mk_rinfix_ind and              *)
(*   ptPapply0_ind are the induction theorems of the recursive definitions.  *)
(* - HOL4 computes cmlpeg_rules_applied, FDOM_cmlPEG, cmlPEG_exec_thm, the   *)
(*   peg0_nX theorems, cml_wfpeg_thm, PEG_exprs, FDOM_cmlPEG_nts and         *)
(*   NTS_in_PEG_exprs with ML code; the port proves the same statements with *)
(*   conversions and rewriting, in the same order.  PEG_exprs states         *)
(*   Gexprs cmlPEG as the enumeration of its distinct elements (HOL4's right *)
(*   hand side is the output of its simplifier); owhile_TopLevelDecs_total   *)
(*   is coreloop_TopLevelDecs_total with coreloop_def unfolded by            *)
(*   rewriting (HOL4 also applies srw_ss to it).                             *)
(* - Helpers that are not HOL4 names have the prefix PARSE2AUX_.             *)
(* - HOL4 pnt is cmlPEG_pnt (a short name), and pnt_def is cmlPEG_pnt_def.   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/peg.ml";;
needs "hol4/pegexec.ml";;
needs "semantics/gram.ml";;
needs "semantics/tokenUtils.ml";;

type_invention_error := true;;
let sumID_def = cake_def
  `(sumID (INL (x:A)) = x) /\
   (sumID (INR (y:A)) = y)`;;

let mktokLf_def = cake_def
  `mktokLf (t:token#C) = [Lf (TOK (FST t), SND t):(token,MMLnonT,C)parsetree]`;;

let mkNd_def = cake_def
  `mkNd (ntnm:B+num) (l:((A,B,locs)parsetree)list) =
     Nd (ntnm, ptree_list_loc l) l`;;

let bindNT0_def = cake_def
  `bindNT0 (ntnm:MMLnonT) (l:((A,MMLnonT,locs)parsetree)list) =
     Nd (INL ntnm, ptree_list_loc l) l`;;

let bindNT_def = cake_def
  `bindNT (ntnm:MMLnonT) (l:((A,MMLnonT,locs)parsetree)list) =
     [bindNT0 ntnm l]`;;

let mk_linfix_def = cake_def
  `(mk_linfix (tgt:B+num) (acc:(A,B,locs)parsetree) [] = acc) /\
   (mk_linfix tgt acc [t] = acc) /\
   (mk_linfix tgt acc (CONS opt (CONS t rest)) =
      mk_linfix tgt (mkNd tgt [acc; opt; t]) rest)`;;

let mk_linfix_ind = cake_ind "mk_linfix";;

let mk_rinfix_def = cake_def
  `(mk_rinfix (tgt:B+num) [] = mkNd tgt []:(A,B,locs)parsetree) /\
   (mk_rinfix tgt [t] = mkNd tgt [t]) /\
   (mk_rinfix tgt (CONS t (CONS opt rest)) =
      mkNd tgt [t; opt; mk_rinfix tgt rest])`;;

let mk_rinfix_ind = cake_ind "mk_rinfix";;

let peg_linfix_def = cake_def
  `peg_linfix (tgtnt:B+num)
              (rptsym:(T0,N,((A,B,locs)parsetree)list,E)pegsym) opsym =
     peg_seq rptsym (peg_rpt (peg_seq opsym rptsym APPEND) FLAT)
         (\a b. match a with
                  [] -> []
                | CONS h _ -> [mk_linfix tgtnt (mkNd tgtnt [h]) b])`;;

let choicel_def = cake_def
  `(choicel [] = peg_not (empty []) []:(A,B,(C)list,E)pegsym) /\
   (choicel (CONS h t) = choice h (choicel t) sumID)`;;

let pegf_def = cake_def
  `pegf (sym:(A,B,(C)list,E)pegsym) (f:(C)list->(C)list) =
     peg_seq sym (empty []) (\l1 l2. f l1)`;;

let seql_def = cake_def
  `seql (l:((A,B,(C)list,E)pegsym)list) f =
     pegf (ITLIST (\p acc. peg_seq p acc APPEND) l (empty [])) f`;;

let try_def = cake_def
  `try (sym:(A,B,(C)list,E)pegsym) = choicel [sym; empty []]`;;

let tokeq_def = cake_def
  `tokeq (t:token) = peg_tok ((=) t) mktokLf:(token,B,(mlptree)list,E)pegsym`;;

let tokSymP_def = cake_def
  `tokSymP (P:mlstring->bool) =
     peg_tok (\t. OPTION_BIND (destSymbolT t) (\s. OPTION_GUARD (P s)) = SOME one)
         mktokLf:(token,B,(mlptree)list,E)pegsym`;;

let cmlPEG_pnt_def = cake_def
  `cmlPEG_pnt (ntsym:MMLnonT) = peg_nt (INL ntsym) I:(A,MMLnonT,C,E)pegsym`;;
let peg_UQConstructorName_def = cake_def
  `peg_UQConstructorName =
     peg_tok (\t. OPTION_BIND (destAlphaT t)
                (\s. OPTION_GUARD (~(s = implode "") /\ isUpper (strsub s 0))) =
              SOME one)
         (bindNT nUQConstructorName o mktokLf):(token,B,(mlptree)list,E)pegsym`;;

let peg_TypeDec_def = cake_def
  `peg_TypeDec =
     peg_seq (tokeq DatatypeT)
         (peg_linfix (INL nDtypeDecls) (cmlPEG_pnt nDtypeDecl) (tokeq AndT))
         (\l1 l2. bindNT nTypeDec (APPEND l1 l2))
       :(token,MMLnonT,(mlptree)list,E)pegsym`;;

let peg_V_def = cake_def
  `peg_V =
     choicel [peg_tok (\t. OPTION_BIND (destAlphaT t)
                         (\s. OPTION_GUARD
                                (~(s IN {implode "before", implode "div",
                                         implode "mod", implode "o"}) /\
                                 ~(s = implode "") /\ ~isUpper (strsub s 0))) =
                       SOME one)
                  (bindNT nV o mktokLf);
              pegf (tokSymP (validPrefixSym o explode)) (bindNT nV)]
       :(token,B,(mlptree)list,E)pegsym`;;

let peg_longV_def = cake_def
  `peg_longV =
     peg_tok (\t. OPTION_BIND (destLongidT t)
                (\(str,s). OPTION_GUARD
                             (~(s = implode "") /\
                              (isAlpha (strsub s 0) ==> ~isUpper (strsub s 0)))) =
              SOME one)
         (bindNT nFQV o mktokLf):(token,B,(mlptree)list,E)pegsym`;;

let peg_EbaseParenFn_def = cake_def
  `peg_EbaseParenFn (l:(mlptree)list) =
     match l with
       [lp; es; rp] -> [mkNd (INL nEbase) [lp; mkNd (INL nEseq) [es]; rp]]
     | [lp; e; sep; es; rp] ->
         (match destLf sep with
            NONE -> []
          | SOME t ->
              (match destTOK t with
                 NONE -> []
               | SOME t ->
                   if t = CommaT then
                     [mkNd (INL nEbase)
                        [mkNd (INL nEtuple)
                           [lp; mkNd (INL nElist2) [e; sep; es]; rp]]]
                   else
                     [mkNd (INL nEbase) [lp; mkNd (INL nEseq) [e; sep; es]; rp]]))
     | _ -> []`;;

let peg_EbaseParen_def = cake_def
  `peg_EbaseParen =
     seql [tokeq LparT; cmlPEG_pnt nE;
           choicel [tokeq RparT;
                    seql [tokeq CommaT; cmlPEG_pnt nElist1; tokeq RparT] I;
                    seql [tokeq SemicolonT; cmlPEG_pnt nEseq; tokeq RparT] I]]
          peg_EbaseParenFn:(token,MMLnonT,(mlptree)list,E)pegsym`;;

let peg_StructName_def = cake_def
  `peg_StructName =
     peg_tok (\t. OPTION_BIND (destAlphaT t) (\s. OPTION_GUARD (~(s = implode ""))) =
              SOME one)
         (bindNT nStructName o mktokLf):(token,B,(mlptree)list,E)pegsym`;;

let ptPapply0_def = cake_def
  `(ptPapply0 (c:(A,MMLnonT,locs)parsetree) [] = []) /\
   (ptPapply0 c [pb_pt] = bindNT nPapp [c; pb_pt]) /\
   (ptPapply0 c (CONS pb pbs) = ptPapply0 (bindNT0 nPConApp [c; pb]) pbs)`;;

let ptPapply0_ind = cake_ind "ptPapply0";;

let ptPapply_def = cake_def
  `(ptPapply [] = []:((A,MMLnonT,locs)parsetree)list) /\
   (ptPapply [_] = []) /\
   (ptPapply (CONS c rest) = ptPapply0 (bindNT0 nPConApp [c]) rest)`;;
let cmlPEG_def = cake_def
 `cmlPEG:(token,MMLnonT,(mlptree)list,string)peg =
  peg_REC (cmlPEG_pnt nTopLevelDecs)
    "Didn't expect an EOF"
    "Failed to see expected token"
    "Failed to see expected token; saw EOF instead"
    "Not combinator failed"
    (FEMPTY |++
     [(INL nV, peg_V);
      (INL nTyvarN, pegf (peg_tok isTyvarT mktokLf) (bindNT nTyvarN));
      (INL nFQV, choicel [pegf (cmlPEG_pnt nV) (bindNT nFQV); peg_longV]);
      (INL nEapp,
       seql [cmlPEG_pnt nEbase; peg_rpt (cmlPEG_pnt nEbase) FLAT]
            (\l. match l with
                   [] -> []
                 | CONS h t -> [FOLDL (\a b. mkNd (INL nEapp) [a; b])
                                      (mkNd (INL nEapp) [h]) t]));
      (INL nElist1,
       seql [cmlPEG_pnt nE; try (seql [tokeq CommaT; cmlPEG_pnt nElist1] I)]
            (bindNT nElist1));
      (INL nMultOps,
       pegf (choicel
               (CONS (tokSymP (validMultSym o explode))
                     (MAP tokeq [StarT; AlphaT (implode "mod");
                                 AlphaT (implode "div")])))
            (bindNT nMultOps));
      (INL nAddOps, pegf (tokSymP (validAddSym o explode)) (bindNT nAddOps));
      (INL nRelOps,
       pegf (choicel [tokeq EqualsT; tokSymP (validRelSym o explode)])
            (bindNT nRelOps));
      (INL nListOps, pegf (tokSymP (validListSym o explode)) (bindNT nListOps));
      (INL nCompOps, pegf (choicel [tokeq (SymbolT (implode ":="));
                                    tokeq (AlphaT (implode "o"))])
                          (bindNT nCompOps));
      (INL nOpID,
       choicel [peg_tok (\t. OPTION_BIND (destLongidT t)
                           (\(str,s). OPTION_GUARD (~(s = implode ""))) =
                         SOME one)
                    (bindNT nOpID o mktokLf);
                peg_tok (\t. OPTION_BIND (destSymbolT t)
                           (\s. OPTION_GUARD (~(s = implode ""))) = SOME one)
                    (bindNT nOpID o mktokLf);
                peg_tok (\t. OPTION_BIND (destAlphaT t)
                           (\s. OPTION_GUARD (~(s = implode ""))) = SOME one)
                    (bindNT nOpID o mktokLf);
                pegf (tokeq StarT) (bindNT nOpID);
                pegf (tokeq EqualsT) (bindNT nOpID)]);
      (INL nEliteral,
       choicel [peg_tok isInt (bindNT nEliteral o mktokLf);
                peg_tok isString (bindNT nEliteral o mktokLf);
                peg_tok isCharT (bindNT nEliteral o mktokLf);
                peg_tok isWordT (bindNT nEliteral o mktokLf);
                peg_tok (IS_SOME o destFFIT) (bindNT nEliteral o mktokLf)]);
      (INL nEbase,
       choicel [pegf (cmlPEG_pnt nEliteral) (bindNT nEbase);
                seql [tokeq LparT; tokeq RparT] (bindNT nEbase);
                peg_EbaseParen;
                seql [tokeq LbrackT; try (cmlPEG_pnt nElist1); tokeq RbrackT]
                     (bindNT nEbase);
                seql [tokeq LetT; cmlPEG_pnt nLetDecs; tokeq InT; cmlPEG_pnt nEseq;
                      tokeq EndT] (bindNT nEbase);
                pegf (cmlPEG_pnt nFQV) (bindNT nEbase);
                pegf (cmlPEG_pnt nConstructorName) (bindNT nEbase);
                seql [tokeq OpT; cmlPEG_pnt nOpID] (bindNT nEbase)]);
      (INL nEseq,
       seql [cmlPEG_pnt nE; try (seql [tokeq SemicolonT; cmlPEG_pnt nEseq] I)]
            (bindNT nEseq));
      (INL nEmult,
       peg_linfix (INL nEmult) (cmlPEG_pnt nEapp) (cmlPEG_pnt nMultOps));
      (INL nEadd, peg_linfix (INL nEadd) (cmlPEG_pnt nEmult) (cmlPEG_pnt nAddOps));
      (INL nElistop,
       seql [cmlPEG_pnt nEadd; try (seql [cmlPEG_pnt nListOps; cmlPEG_pnt nElistop] I)]
            (bindNT nElistop));
      (INL nErel, peg_linfix (INL nErel) (cmlPEG_pnt nElistop) (cmlPEG_pnt nRelOps));
      (INL nEcomp, peg_linfix (INL nEcomp) (cmlPEG_pnt nErel) (cmlPEG_pnt nCompOps));
      (INL nEbefore, peg_linfix (INL nEbefore) (cmlPEG_pnt nEcomp)
                                (tokeq (AlphaT (implode "before"))));
      (INL nEtyped, seql [cmlPEG_pnt nEbefore;
                          try (seql [tokeq ColonT; cmlPEG_pnt nType] I)]
                         (bindNT nEtyped));
      (INL nElogicAND,
       peg_linfix (INL nElogicAND) (cmlPEG_pnt nEtyped) (tokeq AndalsoT));
      (INL nElogicOR,
       peg_linfix (INL nElogicOR) (cmlPEG_pnt nElogicAND) (tokeq OrelseT));
      (INL nEhandle,
       seql [cmlPEG_pnt nElogicOR; try (seql [tokeq HandleT; cmlPEG_pnt nPEs] I)]
            (bindNT nEhandle));
      (INL nE,
       choicel [seql [tokeq RaiseT; cmlPEG_pnt nE] (bindNT nE);
                pegf (cmlPEG_pnt nEhandle) (bindNT nE);
                seql [tokeq IfT; cmlPEG_pnt nE; tokeq ThenT; cmlPEG_pnt nE;
                      tokeq ElseT; cmlPEG_pnt nE]
                     (bindNT nE);
                seql [tokeq FnT; cmlPEG_pnt nPattern; tokeq DarrowT; cmlPEG_pnt nE]
                     (bindNT nE);
                seql [tokeq CaseT; cmlPEG_pnt nE; tokeq OfT; cmlPEG_pnt nPEs]
                     (bindNT nE)]);
      (INL nPEs,
       seql [cmlPEG_pnt nPattern; tokeq DarrowT; cmlPEG_pnt nPE] (bindNT nPEs));
      (INL nPE,
       choicel [seql [tokeq IfT; cmlPEG_pnt nE; tokeq ThenT; cmlPEG_pnt nE;
                      tokeq ElseT; cmlPEG_pnt nPE]
                     (bindNT nPE);
                seql [tokeq CaseT; cmlPEG_pnt nE; tokeq OfT; cmlPEG_pnt nPEs]
                     (bindNT nPE);
                seql [tokeq FnT; cmlPEG_pnt nPattern; tokeq DarrowT; cmlPEG_pnt nE]
                     (bindNT nPE);
                seql [tokeq RaiseT; cmlPEG_pnt nPE] (bindNT nPE);
                seql [cmlPEG_pnt nElogicOR; cmlPEG_pnt nPEsfx] (bindNT nPE)]);
      (INL nPEsfx,
       choicel [seql [tokeq HandleT; cmlPEG_pnt nPEs] (bindNT nPEsfx);
                seql [tokeq BarT; cmlPEG_pnt nPEs] (bindNT nPEsfx);
                pegf (empty []) (bindNT nPEsfx)]);
      (INL nAndFDecls,
       peg_linfix (INL nAndFDecls) (cmlPEG_pnt nFDecl) (tokeq AndT));
      (INL nFDecl,
       seql [cmlPEG_pnt nV; cmlPEG_pnt nPbaseList1; tokeq EqualsT; cmlPEG_pnt nE]
            (bindNT nFDecl));
      (INL nPbaseList1,
       seql [cmlPEG_pnt nPbase; try (cmlPEG_pnt nPbaseList1)]
            (bindNT nPbaseList1));
      (INL nType,
       seql [cmlPEG_pnt nPType; try (seql [tokeq ArrowT; cmlPEG_pnt nType] I)]
            (bindNT nType));
      (INL nDType,
       seql [cmlPEG_pnt nTbase; peg_rpt (cmlPEG_pnt nTyOp) FLAT]
            (\subs. match subs with
                      [] -> []
                    | CONS h t -> [FOLDL (\a b. mkNd (INL nDType) [a; b])
                                         (mkNd (INL nDType) [h]) t]));
      (INL nTbase,
       choicel [
         seql [tokeq LparT; cmlPEG_pnt nType; tokeq RparT] (bindNT nTbase);
         seql [tokeq LparT; cmlPEG_pnt nTypeList2; tokeq RparT; cmlPEG_pnt nTyOp]
              (bindNT nTbase);
         peg_tok isTyvarT (bindNT nTbase o mktokLf);
         pegf (cmlPEG_pnt nTyOp) (bindNT nTbase)]);
      (INL nPTbase,
       choicel [
         seql [tokeq LparT; cmlPEG_pnt nType; tokeq RparT] (bindNT nPTbase);
         peg_tok isTyvarT (bindNT nPTbase o mktokLf);
         pegf (cmlPEG_pnt nTyOp) (bindNT nPTbase)]);
      (INL nTypeList2,
       seql [cmlPEG_pnt nType; tokeq CommaT; cmlPEG_pnt nTypeList1]
            (bindNT nTypeList2));
      (INL nTypeList1,
       seql [cmlPEG_pnt nType; try (seql [tokeq CommaT; cmlPEG_pnt nTypeList1] I)]
            (bindNT nTypeList1));
      (INL nTbaseList,
       pegf (try (seql [cmlPEG_pnt nPTbase; cmlPEG_pnt nTbaseList] I))
            (bindNT nTbaseList));
      (INL nTyOp,
       pegf (choicel [cmlPEG_pnt nUQTyOp; peg_tok isLongidT mktokLf])
            (bindNT nTyOp));
      (INL nUQTyOp,
       pegf (peg_tok isAlphaSym mktokLf) (bindNT nUQTyOp));
      (INL nPType,
       seql [cmlPEG_pnt nDType; try (seql [tokeq StarT; cmlPEG_pnt nPType] I)]
            (bindNT nPType));
      (INL nTypeName,
       choicel [pegf (cmlPEG_pnt nUQTyOp) (bindNT nTypeName);
                seql [tokeq LparT; cmlPEG_pnt nTyVarList;
                      tokeq RparT; cmlPEG_pnt nUQTyOp] (bindNT nTypeName);
                seql [peg_tok isTyvarT mktokLf; cmlPEG_pnt nUQTyOp]
                     (bindNT nTypeName)]);
      (INL nTyVarList,
       peg_linfix (INL nTyVarList) (cmlPEG_pnt nTyvarN) (tokeq CommaT));
      (INL nTypeDec, peg_TypeDec);
      (INL nDtypeDecl,
       seql [cmlPEG_pnt nTypeName;
             tokeq EqualsT;
             peg_linfix (INL nDtypeCons) (cmlPEG_pnt nDconstructor) (tokeq BarT)]
            (bindNT nDtypeDecl));
      (INL nDconstructor,
       seql [cmlPEG_pnt nUQConstructorName; cmlPEG_pnt nTbaseList]
            (bindNT nDconstructor));
      (INL nUQConstructorName, peg_UQConstructorName);
      (INL nConstructorName,
       choicel [
         pegf (cmlPEG_pnt nUQConstructorName) (bindNT nConstructorName);
         peg_tok (\t. OPTION_BIND (destLongidT t)
                    (\(str,s). OPTION_GUARD (~(s = implode "") /\
                                             isAlpha (strsub s 0) /\
                                             isUpper (strsub s 0))) =
                  SOME one)
             (bindNT nConstructorName o mktokLf)]);
      (INL nPbase,
       pegf
         (choicel [cmlPEG_pnt nV; cmlPEG_pnt nConstructorName; peg_tok isInt mktokLf;
                   peg_tok isString mktokLf; peg_tok isCharT mktokLf;
                   cmlPEG_pnt nPtuple; tokeq UnderbarT;
                   seql [tokeq LbrackT; try (cmlPEG_pnt nPatternList);
                         tokeq RbrackT] I;
                   seql [tokeq OpT; cmlPEG_pnt nOpID] I])
         (bindNT nPbase));
      (INL nPapp,
       choicel [seql [cmlPEG_pnt nConstructorName; peg_rpt (cmlPEG_pnt nPbase) FLAT]
                 (\pts. if LENGTH pts = 1 then
                           bindNT nPapp (bindNT nPbase pts)
                         else
                           match pts with
                             [] -> []
                           | [c] -> []
                           | _ -> ptPapply pts);
                pegf (cmlPEG_pnt nPbase) (bindNT nPapp)]);
      (INL nPcons,
       seql [cmlPEG_pnt nPapp;
             try (seql [tokeq (SymbolT (implode "::")); cmlPEG_pnt nPcons] I)]
            (bindNT nPcons));
      (INL nPas,
       seql [try (seql [cmlPEG_pnt nV; tokeq AsT] I);
             cmlPEG_pnt nPcons]
            (bindNT nPas));
      (INL nPattern,
       seql [cmlPEG_pnt nPas; try (seql [tokeq ColonT; cmlPEG_pnt nType] I)]
            (bindNT nPattern));
      (INL nPatternList,
       seql [cmlPEG_pnt nPattern;
             try (seql [tokeq CommaT; cmlPEG_pnt nPatternList] I)]
            (bindNT nPatternList));
      (INL nPtuple,
       choicel [seql [tokeq LparT; tokeq RparT] (bindNT nPtuple);
                seql [tokeq LparT; cmlPEG_pnt nPatternList; tokeq RparT]
                     (bindNT nPtuple)]);
      (INL nLetDec,
       choicel [seql [tokeq ValT; cmlPEG_pnt nPattern; tokeq EqualsT; cmlPEG_pnt nE]
                     (bindNT nLetDec);
                seql [tokeq FunT; cmlPEG_pnt nAndFDecls] (bindNT nLetDec)]);
      (INL nLetDecs,
       choicel [seql [cmlPEG_pnt nLetDec; cmlPEG_pnt nLetDecs] (bindNT nLetDecs);
                seql [tokeq SemicolonT; cmlPEG_pnt nLetDecs] (bindNT nLetDecs);
                pegf (empty []) (bindNT nLetDecs)]);
      (INL nDecl,
       choicel [
         seql [tokeq ValT; cmlPEG_pnt nPattern; tokeq EqualsT; cmlPEG_pnt nE]
              (bindNT nDecl);
         seql [tokeq FunT; cmlPEG_pnt nAndFDecls] (bindNT nDecl);
         seql [tokeq ExceptionT; cmlPEG_pnt nDconstructor] (bindNT nDecl);
         seql [tokeq LocalT; cmlPEG_pnt nDecls; tokeq InT; cmlPEG_pnt nDecls;
               tokeq EndT] (bindNT nDecl);
         seql [cmlPEG_pnt nTypeDec] (bindNT nDecl);
         seql [cmlPEG_pnt nTypeAbbrevDec] (bindNT nDecl);
         seql [cmlPEG_pnt nStructure] (bindNT nDecl)]);
      (INL nTypeAbbrevDec,
       seql [tokeq TypeT; cmlPEG_pnt nTypeName; tokeq EqualsT; cmlPEG_pnt nType]
            (bindNT nTypeAbbrevDec));
      (INL nDecls,
       choicel [seql [cmlPEG_pnt nDecl; cmlPEG_pnt nDecls] (bindNT nDecls);
                seql [tokeq SemicolonT; cmlPEG_pnt nDecls] (bindNT nDecls);
                pegf (empty []) (bindNT nDecls)]);
      (INL nOptTypEqn,
       choicel [seql [tokeq EqualsT; cmlPEG_pnt nType] (bindNT nOptTypEqn);
                pegf (empty []) (bindNT nOptTypEqn)]);
      (INL nSpecLine,
       choicel [seql [tokeq ValT; cmlPEG_pnt nV; tokeq ColonT; cmlPEG_pnt nType]
                     (bindNT nSpecLine);
                seql [tokeq TypeT; cmlPEG_pnt nTypeName; cmlPEG_pnt nOptTypEqn]
                     (bindNT nSpecLine);
                seql [tokeq ExceptionT; cmlPEG_pnt nDconstructor] (bindNT nSpecLine);
                pegf (cmlPEG_pnt nTypeDec) (bindNT nSpecLine)]);
      (INL nSpecLineList,
       choicel [seql [cmlPEG_pnt nSpecLine; cmlPEG_pnt nSpecLineList]
                     (bindNT nSpecLineList);
                seql [tokeq SemicolonT; cmlPEG_pnt nSpecLineList]
                     (bindNT nSpecLineList);
                pegf (empty []) (bindNT nSpecLineList)]);
      (INL nSignatureValue,
       seql [tokeq SigT; cmlPEG_pnt nSpecLineList; tokeq EndT]
            (bindNT nSignatureValue));
      (INL nOptionalSignatureAscription,
       pegf (try (seql [tokeq SealT; cmlPEG_pnt nSignatureValue] I))
            (bindNT nOptionalSignatureAscription));
      (INL nStructName, peg_StructName);
      (INL nStructure,
       seql [tokeq StructureT; cmlPEG_pnt nStructName;
             cmlPEG_pnt nOptionalSignatureAscription;
             tokeq EqualsT; tokeq StructT; cmlPEG_pnt nDecls; tokeq EndT]
            (bindNT nStructure));
      (INL nTopLevelDecs,
       choicel [
         seql [cmlPEG_pnt nE; tokeq SemicolonT; cmlPEG_pnt nTopLevelDecs]
              (bindNT nTopLevelDecs);
         seql [cmlPEG_pnt nDecl; cmlPEG_pnt nNonETopLevelDecs]
              (bindNT nTopLevelDecs);
         seql [tokeq SemicolonT; cmlPEG_pnt nTopLevelDecs]
              (bindNT nTopLevelDecs);
         pegf (empty []) (bindNT nTopLevelDecs)]);
      (INL nNonETopLevelDecs,
       choicel [
         seql [cmlPEG_pnt nDecl; cmlPEG_pnt nNonETopLevelDecs]
              (bindNT nNonETopLevelDecs);
         seql [tokeq SemicolonT; cmlPEG_pnt nTopLevelDecs]
              (bindNT nNonETopLevelDecs);
         pegf (empty []) (bindNT nNonETopLevelDecs)])])`;;

(* ------------------------------------------------------------------------- *)
(* The rules of cmlPEG, applied.  HOL4 computes cmlpeg_rules_applied and     *)
(* FDOM_cmlPEG with ML code (SIMP_CONV with FUPDATE_LIST_THM,                *)
(* FAPPLY_FUPDATE_THM and the distinctness of MMLnonT); the port does the    *)
(* same with conversions.  Constructor equations are decided by looking     *)
(* them up in a table of gram's nt_distinct_ths (as gramProps does).          *)
(* ------------------------------------------------------------------------- *)

let PARSE2AUX_nt_eq_tbl =
  let tbl = Hashtbl.create 6000 in
  do_list (fun th ->
      let l,r = dest_eq(lhs(concl th)) in
      Hashtbl.replace tbl (fst(dest_const l),fst(dest_const r)) th)
    (CONJUNCTS nt_distinct_ths);
  tbl;;

let PARSE2AUX_NT_EQ_CONV tm =
  let l,r = dest_eq tm in
  if l = r then EQT_INTRO(REFL l)
  else Hashtbl.find PARSE2AUX_nt_eq_tbl (fst(dest_const l),fst(dest_const r));;

let PARSE2AUX_INL_EQ_CONV =
  REWR_CONV(CONJUNCT1(injectivity "sum")) THENC PARSE2AUX_NT_EQ_CONV;;

let rec PARSE2AUX_FUPDATE_LIST_CONV tm =
  ((REWR_CONV FMAPAUX_FUL_CONS THENC PARSE2AUX_FUPDATE_LIST_CONV) ORELSEC
   REWR_CONV FMAPAUX_FUL_NIL) tm;;

(* peg_rules cmlPEG = FEMPTY |+ (INL nV,peg_V) |+ ... *)

let PARSE2AUX_cmlPEG_rules =
  (RAND_CONV (REWR_CONV cmlPEG_def) THENC
   REWR_CONV (el 5 (CONJUNCTS (record_info "peg").ri_accessors)) THENC
   PARSE2AUX_FUPDATE_LIST_CONV)
  `peg_rules cmlPEG`;;

let rec PARSE2AUX_FAPPLY_UPDATES_CONV tm =
  let th1 = REWR_CONV FAPPLY_FUPDATE_THM tm in
  let th2 = CONV_RULE (RAND_CONV
              (RATOR_CONV(RATOR_CONV(RAND_CONV PARSE2AUX_INL_EQ_CONV)) THENC
               GEN_REWRITE_CONV I [COND_CLAUSES])) th1 in
  let r = rhs(concl th2) in
  if is_comb r && is_comb(rator r) && is_const(rator(rator r)) &&
     fst(dest_const(rator(rator r))) = "FAPPLY" &&
     is_comb(rand(rator r))
  then TRANS th2 (PARSE2AUX_FAPPLY_UPDATES_CONV r) else th2;;

let PARSE2AUX_mmlnonT_constructors =
  map rhs (disjuncts(snd(dest_forall(concl(cases "MMLnonT")))));;

let cmlpeg_rules_applied =
  let app c =
    (RATOR_CONV(RAND_CONV(K PARSE2AUX_cmlPEG_rules)) THENC
     PARSE2AUX_FAPPLY_UPDATES_CONV)
    (mk_comb(mk_comb(`FAPPLY:(MMLnonT+num,(token,MMLnonT,(mlptree)list,string)pegsym)fmap
                             ->MMLnonT+num->(token,MMLnonT,(mlptree)list,string)pegsym`,
                     `peg_rules cmlPEG`),
             mk_comb(`INL:MMLnonT->MMLnonT+num`,c))) in
  end_itlist CONJ (map app PARSE2AUX_mmlnonT_constructors);;

let FDOM_cmlPEG =
  (RAND_CONV (K PARSE2AUX_cmlPEG_rules) THENC
   PURE_REWRITE_CONV[FDOM_FUPDATE; FDOM_FEMPTY])
  `FDOM (peg_rules cmlPEG)`;;

let rec PARSE2AUX_ALLQ_CONV c tm =
  if is_forall tm then BINDER_CONV (PARSE2AUX_ALLQ_CONV c) tm else c tm;;

(* membership of INL c in the domain, decided (T or F) *)

let PARSE2AUX_IN_FDOM_CONV =
  let tor = TAUT `!p. (T \/ p) <=> T` and forr = TAUT `!p. (F \/ p) <=> p` in
  let in_empty = prove(`!x:MMLnonT+num. x IN {} <=> F`, REWRITE_TAC[NOT_IN_EMPTY]) in
  let rec in_enum tm =
    (REWR_CONV in_empty ORELSEC
     (REWR_CONV IN_INSERT THENC LAND_CONV PARSE2AUX_INL_EQ_CONV THENC
      (REWR_CONV tor ORELSEC (REWR_CONV forr THENC in_enum)))) tm in
  RAND_CONV (REWR_CONV FDOM_cmlPEG) THENC in_enum;;

(* the rule of a non-terminal *)

let PARSE2AUX_rule (c:term) =
  find (fun r -> rand(rand(lhs(concl r))) = c) (CONJUNCTS cmlpeg_rules_applied);;

(* HOL4: cmlPEG_exec_thm[compute], peg_nt_thm for each non-terminal *)

let cmlPEG_exec_thm =
  let spec0 = ISPEC `cmlPEG` peg_nt_thm in
  let inl = `INL:MMLnonT->MMLnonT+num` in
  let one c =
    let th = SPEC (mk_comb(inl,c)) spec0 in
    let th1 = CONV_RULE (PARSE2AUX_ALLQ_CONV (RAND_CONV
                (RATOR_CONV(RATOR_CONV(RAND_CONV PARSE2AUX_IN_FDOM_CONV)) THENC
                 GEN_REWRITE_CONV I [COND_CLAUSES]))) th in
    CONV_RULE (PARSE2AUX_ALLQ_CONV (RAND_CONV
                 (ONCE_DEPTH_CONV (REWR_CONV (PARSE2AUX_rule c))))) th1 in
  end_itlist CONJ (map one PARSE2AUX_mmlnonT_constructors);;

(* HOL4: frange_image (local) *)

let frange_image = prove
 (`!fm:(A,B)fmap. FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  REWRITE_TAC[FRANGE_DEF; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

(* HOL4's ML values peg0_rwts, wfpeg_rwts and pegnt_case_ths (the cases of   *)
(* peg0, peggt0, pegfail and wfpeg for each kind of expression) are the     *)
(* clause theorems LPARSEAUX_peg0_clauses, ... of hol4/peg.ml.              *)

(* ------------------------------------------------------------------------- *)
(* peg0 of the derived forms.                                                *)
(* ------------------------------------------------------------------------- *)

let peg0_pegf = prove
 (`!(G:(A,B,(C)list,E)peg) s f. peg0 G (pegf s f) <=> peg0 G s`,
  REWRITE_TAC[pegf_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_pegf];;

let peg0_seql = prove
 (`!(G:(A,B,(C)list,E)peg) h t f.
     (peg0 G (seql [] f) <=> T) /\
     (peg0 G (seql (CONS h t) f) <=> peg0 G h /\ peg0 G (seql t I))`,
  REWRITE_TAC[seql_def; pegf_def; ITLIST; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_seql];;

let peg0_tokeq = prove
 (`!(G:(token,B,(mlptree)list,E)peg) t. peg0 G (tokeq t) <=> F`,
  REWRITE_TAC[tokeq_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_tokeq];;

let peg0_tokSymP = prove
 (`!(G:(token,B,(mlptree)list,E)peg) P. peg0 G (tokSymP P) <=> F`,
  REWRITE_TAC[tokSymP_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_tokSymP];;

let peg0_choicel = prove
 (`!(G:(A,B,(C)list,E)peg) h t.
     (peg0 G (choicel []) <=> F) /\
     (peg0 G (choicel (CONS h t)) <=>
      peg0 G h \/ pegfail G h /\ peg0 G (choicel t))`,
  REWRITE_TAC[choicel_def; LPARSEAUX_peg0_clauses; LPARSEAUX_pegfail_clauses]);;
let _ = cake_add_simps [peg0_choicel];;

(* ------------------------------------------------------------------------- *)
(* Non-terminals that cannot consume nothing (HOL4: the ML function pegnt    *)
(* over a list of non-terminals, each theorem saved as peg0_nX and exported  *)
(* as a rewrite).  As in HOL4, each proof unfolds the rule of the            *)
(* non-terminal once and then uses the theorems proved before it for the     *)
(* non-terminals it mentions (kept as cmlPEG_pnt Y).                        *)
(* ------------------------------------------------------------------------- *)

let PARSE2AUX_peg0_pnt = prove
 (`!(G:(A,MMLnonT,C,E)peg) n.
     peg0 G (cmlPEG_pnt n) <=>
     INL n IN FDOM (peg_rules G) /\ peg0 G (FAPPLY (peg_rules G) (INL n))`,
  REWRITE_TAC[cmlPEG_pnt_def; LPARSEAUX_peg0_nt_clauses]);;

let PARSE2AUX_wfpeg_pnt = prove
 (`!(G:(A,MMLnonT,C,E)peg) n.
     wfpeg G (cmlPEG_pnt n) <=>
     INL n IN FDOM (peg_rules G) /\ wfpeg G (FAPPLY (peg_rules G) (INL n))`,
  REWRITE_TAC[cmlPEG_pnt_def; LPARSEAUX_wfpeg_nt]);;

(* the derived forms and named expressions, unfolded (cmlPEG_pnt is kept) *)

let PARSE2AUX_PEG_DEFS =
  [seql_def; ITLIST; choicel_def; pegf_def; try_def; tokeq_def; tokSymP_def;
   peg_linfix_def; peg_V_def; peg_longV_def; peg_UQConstructorName_def;
   peg_StructName_def; peg_TypeDec_def; peg_EbaseParen_def; MAP];;

let PARSE2AUX_PEG0_RWTS =
  [LPARSEAUX_peg0_clauses; LPARSEAUX_peggt0_clauses; LPARSEAUX_pegfail_clauses];;

let PARSE2AUX_npeg0 = ref ([]:thm list);;

let PARSE2AUX_PEGNT (c:term) =
  let p = mk_comb(`cmlPEG_pnt:MMLnonT->(token,MMLnonT,(mlptree)list,string)pegsym`, c) in
  let g = mk_neg(mk_comb(`peg0 cmlPEG`, p)) in
  let th = prove(g,
    GEN_REWRITE_TAC RAND_CONV [PARSE2AUX_peg0_pnt] THEN
    CONV_TAC(RAND_CONV(LAND_CONV PARSE2AUX_IN_FDOM_CONV)) THEN
    REWRITE_TAC[PARSE2AUX_rule c] THEN
    REWRITE_TAC(PARSE2AUX_PEG_DEFS @ PARSE2AUX_PEG0_RWTS @ !PARSE2AUX_npeg0)) in
  PARSE2AUX_npeg0 := th :: !PARSE2AUX_npeg0;
  REWRITE_RULE[cmlPEG_pnt_def] th;;
let peg0_nTypeDec = PARSE2AUX_PEGNT `nTypeDec`;;
let peg0_nTypeAbbrevDec = PARSE2AUX_PEGNT `nTypeAbbrevDec`;;
let peg0_nOpID = PARSE2AUX_PEGNT `nOpID`;;
let peg0_nStructure = PARSE2AUX_PEGNT `nStructure`;;
let peg0_nDecl = PARSE2AUX_PEGNT `nDecl`;;
let peg0_nV = PARSE2AUX_PEGNT `nV`;;
let peg0_nUQTyOp = PARSE2AUX_PEGNT `nUQTyOp`;;
let peg0_nUQConstructorName = PARSE2AUX_PEGNT `nUQConstructorName`;;
let peg0_nStructName = PARSE2AUX_PEGNT `nStructName`;;
let peg0_nConstructorName = PARSE2AUX_PEGNT `nConstructorName`;;
let peg0_nTypeName = PARSE2AUX_PEGNT `nTypeName`;;
let peg0_nDtypeDecl = PARSE2AUX_PEGNT `nDtypeDecl`;;
let peg0_nDconstructor = PARSE2AUX_PEGNT `nDconstructor`;;
let peg0_nFDecl = PARSE2AUX_PEGNT `nFDecl`;;
let peg0_nTyvarN = PARSE2AUX_PEGNT `nTyvarN`;;
let peg0_nTyOp = PARSE2AUX_PEGNT `nTyOp`;;
let peg0_nTbase = PARSE2AUX_PEGNT `nTbase`;;
let peg0_nPTbase = PARSE2AUX_PEGNT `nPTbase`;;
let peg0_nDType = PARSE2AUX_PEGNT `nDType`;;
let peg0_nPType = PARSE2AUX_PEGNT `nPType`;;
let peg0_nType = PARSE2AUX_PEGNT `nType`;;
let peg0_nTypeList1 = PARSE2AUX_PEGNT `nTypeList1`;;
let peg0_nTypeList2 = PARSE2AUX_PEGNT `nTypeList2`;;
let peg0_nRelOps = PARSE2AUX_PEGNT `nRelOps`;;
let peg0_nPtuple = PARSE2AUX_PEGNT `nPtuple`;;
let peg0_nPbase = PARSE2AUX_PEGNT `nPbase`;;
let peg0_nPapp = PARSE2AUX_PEGNT `nPapp`;;
let peg0_nPcons = PARSE2AUX_PEGNT `nPcons`;;
let peg0_nPas = PARSE2AUX_PEGNT `nPas`;;
let peg0_nPattern = PARSE2AUX_PEGNT `nPattern`;;
let peg0_nPatternList = PARSE2AUX_PEGNT `nPatternList`;;
let peg0_nPbaseList1 = PARSE2AUX_PEGNT `nPbaseList1`;;
let peg0_nLetDec = PARSE2AUX_PEGNT `nLetDec`;;
let peg0_nMultOps = PARSE2AUX_PEGNT `nMultOps`;;
let peg0_nListOps = PARSE2AUX_PEGNT `nListOps`;;
let peg0_nFQV = PARSE2AUX_PEGNT `nFQV`;;
let peg0_nAddOps = PARSE2AUX_PEGNT `nAddOps`;;
let peg0_nCompOps = PARSE2AUX_PEGNT `nCompOps`;;
let peg0_nEliteral = PARSE2AUX_PEGNT `nEliteral`;;
let peg0_nEbase = PARSE2AUX_PEGNT `nEbase`;;
let peg0_nEapp = PARSE2AUX_PEGNT `nEapp`;;
let peg0_nEmult = PARSE2AUX_PEGNT `nEmult`;;
let peg0_nEadd = PARSE2AUX_PEGNT `nEadd`;;
let peg0_nElistop = PARSE2AUX_PEGNT `nElistop`;;
let peg0_nErel = PARSE2AUX_PEGNT `nErel`;;
let peg0_nEcomp = PARSE2AUX_PEGNT `nEcomp`;;
let peg0_nEbefore = PARSE2AUX_PEGNT `nEbefore`;;
let peg0_nEtyped = PARSE2AUX_PEGNT `nEtyped`;;
let peg0_nElogicAND = PARSE2AUX_PEGNT `nElogicAND`;;
let peg0_nElogicOR = PARSE2AUX_PEGNT `nElogicOR`;;
let peg0_nEhandle = PARSE2AUX_PEGNT `nEhandle`;;
let peg0_nE = PARSE2AUX_PEGNT `nE`;;
let peg0_nPE = PARSE2AUX_PEGNT `nPE`;;
let peg0_nPEs = PARSE2AUX_PEGNT `nPEs`;;
let peg0_nElist1 = PARSE2AUX_PEGNT `nElist1`;;
let peg0_nSpecLine = PARSE2AUX_PEGNT `nSpecLine`;;
let _ = cake_add_simps
  [peg0_nTypeDec; peg0_nTypeAbbrevDec; peg0_nOpID; peg0_nStructure;
   peg0_nDecl; peg0_nV; peg0_nUQTyOp; peg0_nUQConstructorName;
   peg0_nStructName; peg0_nConstructorName; peg0_nTypeName; peg0_nDtypeDecl;
   peg0_nDconstructor; peg0_nFDecl; peg0_nTyvarN; peg0_nTyOp; peg0_nTbase;
   peg0_nPTbase; peg0_nDType; peg0_nPType; peg0_nType; peg0_nTypeList1;
   peg0_nTypeList2; peg0_nRelOps; peg0_nPtuple; peg0_nPbase; peg0_nPapp;
   peg0_nPcons; peg0_nPas; peg0_nPattern; peg0_nPatternList;
   peg0_nPbaseList1; peg0_nLetDec; peg0_nMultOps; peg0_nListOps; peg0_nFQV;
   peg0_nAddOps; peg0_nCompOps; peg0_nEliteral; peg0_nEbase; peg0_nEapp;
   peg0_nEmult; peg0_nEadd; peg0_nElistop; peg0_nErel; peg0_nEcomp;
   peg0_nEbefore; peg0_nEtyped; peg0_nElogicAND; peg0_nElogicOR;
   peg0_nEhandle; peg0_nE; peg0_nPE; peg0_nPEs; peg0_nElist1;
   peg0_nSpecLine];;

(* ------------------------------------------------------------------------- *)
(* Well-formedness of the non-terminals (HOL4: the ML function wfnt over     *)
(* topo_nts, a topological order of the non-terminals; each proof unfolds    *)
(* the rule once and uses the theorems proved before it).                   *)
(* ------------------------------------------------------------------------- *)

let PARSE2AUX_wfpeg_acc = ref ([]:thm list);;

let PARSE2AUX_WFNT (c:term) =
  let p = mk_comb(`cmlPEG_pnt:MMLnonT->(token,MMLnonT,(mlptree)list,string)pegsym`, c) in
  let g = mk_comb(`wfpeg cmlPEG`, p) in
  let th = prove(g,
    GEN_REWRITE_TAC I [PARSE2AUX_wfpeg_pnt] THEN
    CONV_TAC(LAND_CONV PARSE2AUX_IN_FDOM_CONV) THEN
    REWRITE_TAC[PARSE2AUX_rule c] THEN
    REWRITE_TAC(PARSE2AUX_PEG_DEFS @ [LPARSEAUX_wfpeg_clauses] @
                PARSE2AUX_PEG0_RWTS @ !PARSE2AUX_npeg0 @ !PARSE2AUX_wfpeg_acc)) in
  PARSE2AUX_wfpeg_acc := th :: !PARSE2AUX_wfpeg_acc; th;;

(* HOL4: LIST_CONJ (List.foldl wfnt [] topo_nts), the last one first *)

let cml_wfpeg_thm =
  let topo_nts =
    [`nV`; `nTyvarN`; `nTypeDec`; `nTypeAbbrevDec`; `nSpecLine`;
     `nSpecLineList`; `nSignatureValue`; `nStructure`; `nDecl`; `nUQTyOp`;
     `nUQConstructorName`; `nStructName`; `nConstructorName`;
     `nTyVarList`; `nTypeName`; `nTyOp`; `nTbase`; `nPTbase`;
     `nTbaseList`; `nDType`; `nPType`; `nListOps`; `nRelOps`; `nPtuple`;
     `nPbase`; `nPapp`; `nPcons`; `nPas`; `nPattern`; `nPatternList`;
     `nPbaseList1`; `nPEs`; `nMultOps`; `nLetDec`; `nLetDecs`; `nFQV`;
     `nFDecl`; `nAddOps`; `nCompOps`; `nOpID`; `nEliteral`; `nEbase`;
     `nEapp`; `nEmult`; `nEadd`; `nElistop`; `nErel`; `nEcomp`;
     `nEbefore`; `nEtyped`; `nElogicAND`; `nElogicOR`; `nPE`; `nPEsfx`;
     `nEhandle`; `nE`; `nType`; `nTypeList1`; `nTypeList2`; `nEseq`;
     `nElist1`; `nDtypeDecl`; `nOptTypEqn`; `nDecls`; `nDconstructor`;
     `nAndFDecls`; `nOptionalSignatureAscription`; `nTopLevelDecs`;
     `nNonETopLevelDecs`] in
  do_list (fun c -> ignore(PARSE2AUX_WFNT c)) topo_nts;
  end_itlist CONJ (!PARSE2AUX_wfpeg_acc);;

(* HOL4: subexprs_pnt (local) *)

let subexprs_pnt = prove
 (`!n. subexprs (cmlPEG_pnt n:(A,MMLnonT,C,E)pegsym) = {cmlPEG_pnt n}`,
  REWRITE_TAC[subexprs_def; cmlPEG_pnt_def]);;

(* HOL4: the ML value peg_start *)

let PARSE2AUX_peg_start = prove
 (`peg_start cmlPEG = cmlPEG_pnt nTopLevelDecs`,
  REWRITE_TAC[cmlPEG_def; (record_info "peg").ri_accessors]);;

(* HOL4: PEG_exprs, computed by SIMP_CONV from Gexprs_def, subexprs_def and  *)
(* the definitions of the derived forms.  Here the derived forms           *)
(* (cmlPEG_pnt kept) are unfolded in the same way and the set is given as   *)
(* the enumeration of                                                       *)
(* its distinct elements, in the order of their first occurrence (the       *)
(* start symbol, then the rules in the order of FDOM_cmlPEG).               *)

let PARSE2AUX_GEXPRS_RAW =
  (REWRITE_CONV[peg_Gexprs_def; PARSE2AUX_peg_start; frange_image; FDOM_cmlPEG;
                IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0] THENC
   REWRITE_CONV[cmlpeg_rules_applied] THENC
   REWRITE_CONV PARSE2AUX_PEG_DEFS THENC
   REWRITE_CONV[subexprs_def; subexprs_pnt] THENC
   REWRITE_CONV[INSERT_UNION_EQ; UNION_EMPTY])
  `Gexprs cmlPEG`;;

let PEG_exprs =
  let els = dest_setenum (rhs(concl PARSE2AUX_GEXPRS_RAW)) in
  let rec dedup seen l =
    match l with
      [] -> []
    | h::t -> if mem h seen then dedup seen t else h :: dedup (h::seen) t in
  let target = mk_setenum(dedup [] els, type_of(hd els)) in
  let th = prove
   (mk_eq(rhs(concl PARSE2AUX_GEXPRS_RAW), target),
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN GEN_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(DISJ_ACI_RULE w))) in
  TRANS PARSE2AUX_GEXPRS_RAW th;;

(* every subexpression of an expression is well-formed, by the form of the  *)
(* expression (for the proof of PEG_wellformed)                             *)

let PARSE2AUX_ALLWF_pnt = prove
 (`!(G:(A,MMLnonT,C,E)peg) n.
     (!x. x IN subexprs (cmlPEG_pnt n) ==> wfpeg G x) <=> wfpeg G (cmlPEG_pnt n)`,
  REWRITE_TAC[subexprs_pnt; IN_SING; FORALL_UNWIND_THM2]);;

let PEG_wellformed = prove
 (`wfG cmlPEG`,
  REWRITE_TAC[wfG_def; LPARSEAUX_FORALL_GEXPRS; PARSE2AUX_peg_start;
              FDOM_cmlPEG; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[cmlpeg_rules_applied] THEN
  REWRITE_TAC(PARSE2AUX_PEG_DEFS @ [LPARSEAUX_ALLWF; PARSE2AUX_ALLWF_pnt] @
              CONJUNCTS cml_wfpeg_thm @ PARSE2AUX_PEG0_RWTS @
              !PARSE2AUX_npeg0));;
let _ = cake_add_simps [PEG_wellformed];;

let parse_TopLevelDecs_total = prove
 (`!i. ?r. peg_exec cmlPEG (cmlPEG_pnt nTopLevelDecs) i [] NONE [] pegexec_done failed =
           Result r`,
  GEN_TAC THEN REWRITE_TAC[GSYM PARSE2AUX_peg_start] THEN
  MATCH_MP_TAC peg_exec_total THEN REWRITE_TAC[PEG_wellformed]);;

let coreloop_TopLevelDecs_total = prove
 (`!i. ?r. coreloop cmlPEG (EV (cmlPEG_pnt nTopLevelDecs) i [] NONE [] pegexec_done failed) =
           SOME (Result r)`,
  GEN_TAC THEN REWRITE_TAC[GSYM PARSE2AUX_peg_start] THEN
  MATCH_MP_TAC coreloop_total THEN REWRITE_TAC[PEG_wellformed]);;

(* HOL4: SIMP_RULE (srw_ss()) [coreloop_def] coreloop_TopLevelDecs_total;   *)
(* here coreloop_def is unfolded by rewriting                               *)

let owhile_TopLevelDecs_total =
  REWRITE_RULE[coreloop_def] coreloop_TopLevelDecs_total;;

(* HOL4: FDOM_cmlPEG_nts and NTS_in_PEG_exprs, one conjunct for each element *)
(* of FDOM_cmlPEG, in the order of the rules                                *)

let PARSE2AUX_FDOM_nts = rev (dest_setenum (rhs(concl FDOM_cmlPEG)));;

let FDOM_cmlPEG_nts =
  let p x = EQT_ELIM (PARSE2AUX_IN_FDOM_CONV
              (mk_comb(mk_comb(`(IN):MMLnonT+num->(MMLnonT+num->bool)->bool`, x),
                       `FDOM (peg_rules cmlPEG)`))) in
  end_itlist CONJ (map p PARSE2AUX_FDOM_nts);;
let _ = cake_add_simps [FDOM_cmlPEG_nts];;

let PARSE2AUX_IN_TAIL = prove
 (`!(x:A) y s. x IN s ==> x IN (y INSERT s)`,
  SIMP_TAC[IN_INSERT]);;

let rec PARSE2AUX_IN_ENUM_PROVE x s =
  let y = lhand s and s' = rand s in
  if aconv x y then ISPECL [x; s'] COMPONENT
  else MP (ISPECL [x; y; s'] PARSE2AUX_IN_TAIL)
                (PARSE2AUX_IN_ENUM_PROVE x s');;

let NTS_in_PEG_exprs =
  let pnt = `cmlPEG_pnt:MMLnonT->(token,MMLnonT,(mlptree)list,string)pegsym` in
  let s = rhs(concl PEG_exprs) in
  let p x =
    let c = rand x in
    let th = PARSE2AUX_IN_ENUM_PROVE (mk_comb(pnt,c)) s in
    REWRITE_RULE[cmlPEG_pnt_def] (CONV_RULE (RAND_CONV (K (SYM PEG_exprs))) th) in
  end_itlist CONJ (map p PARSE2AUX_FDOM_nts);;
let _ = cake_add_simps [NTS_in_PEG_exprs];;
