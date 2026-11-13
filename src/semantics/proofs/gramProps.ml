(* ========================================================================= *)
(* gramProps: port of HOL4 semantics/proofs/gramPropsScript.sml (CakeML      *)
(* v3479).  Properties of the CakeML CFG, including automatically derived    *)
(* nullability results for various non-terminals, and results about the      *)
(* grammar's rules finite map.                                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's overload mkNT is written out (INL on MMLnonT); G.rules is        *)
(*   grammar_rules G, f ' x is FAPPLY f x, derives G is RTC (derive G).      *)
(* - HOL4 computes cmlG_applied, cmlG_FDOM and the nullable_X theorems with  *)
(*   ML code; the port computes or proves the same statements (see below).   *)
(* - GSPEC_INTER and GSPEC_applied are about HOL4's encoding of set          *)
(*   comprehensions; they are stated for HOL Light's (see GSPEC_INTER).      *)
(* - The HOL4 script adds APPEND_EQ_SING (reoriented) to its simpset for     *)
(*   its own proofs; that is not ported (no stored theorem).                 *)
(* - Helpers that are not HOL4 names have the prefix PARSE1AUX_.             *)
(* ========================================================================= *)

needs "semantics/gram.ml";;
needs "hol4/NTproperties.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The rank of a non-terminal (HOL4 NT_rank_def).                            *)
(* ------------------------------------------------------------------------- *)

let NT_rank_def = cake_def
  `NT_rank (N:NT) =
     match N with
       INR _ -> 0
     | INL n ->
         if n = nElist1                 then 16
         else if n = nEseq              then 16
         else if n = nTopLevelDecs      then 16
         else if n = nElist2            then 16
         else if n = nE                 then 15
         else if n = nEhandle           then 14
         else if n = nPE                then 14
         else if n = nElogicOR          then 13
         else if n = nElogicAND         then 12
         else if n = nEtyped            then 11
         else if n = nEbefore           then 10
         else if n = nEcomp             then  9
         else if n = nErel              then  8
         else if n = nElistop           then  7
         else if n = nEadd              then  6
         else if n = nEmult             then  5
         else if n = nEapp              then  4
         else if n = nEbase             then  3
         else if n = nFQV               then  2
         else if n = nV                 then  1
         else if n = nDtypeCons         then  3
         else if n = nDconstructor      then  2
         else if n = nConstructorName   then  2
         else if n = nUQConstructorName then  1
         else if n = nTypeList2         then  8
         else if n = nTypeList1         then  7
         else if n = nType              then  6
         else if n = nPType             then  5
         else if n = nDType             then  4
         else if n = nTbaseList         then  4
         else if n = nPTbase            then  3
         else if n = nTbase             then  3
         else if n = nTyOp              then  2
         else if n = nTypeName          then  2
         else if n = nUQTyOp            then  1
         else if n = nNonETopLevelDecs  then  4
         else if n = nDecls             then  3
         else if n = nStructure         then  1
         else if n = nDecl              then  2
         else if n = nTypeDec           then  1
         else if n = nSpecLineList      then  3
         else if n = nSpecLine          then  2
         else if n = nPtuple            then  2
         else if n = nPbase             then  3
         else if n = nPbaseList1        then  4
         else if n = nPapp              then  4
         else if n = nPcons             then  5
         else if n = nPas               then  6
         else if n = nPattern           then  7
         else if n = nPatternList       then  8
         else if n = nPEs               then  9
         else if n = nLetDecs           then  2
         else if n = nLetDec            then  1
         else if n = nDtypeDecl         then  3
         else if n = nAndFDecls         then  3
         else if n = nFDecl             then  2
         else if n = nTyVarList         then  2
         else if n = nTyvarN            then  1
         else                                0`;;

(* ------------------------------------------------------------------------- *)
(* The rules of cmlG, applied (HOL4 cmlG_applied, cmlG_FDOM).                *)
(* ------------------------------------------------------------------------- *)

let PARSE1AUX_cmlG_rules =
  (RAND_CONV(REWR_CONV cmlG_def) THENC
   REWR_CONV(CONJUNCT2 (record_info "grammar").ri_accessors))
  `grammar_rules cmlG`;;

let PARSE1AUX_nt_eq_tbl =
  let tbl = Hashtbl.create 6000 in
  do_list (fun th ->
      let l,r = dest_eq(lhs(concl th)) in
      Hashtbl.replace tbl (fst(dest_const l),fst(dest_const r)) th)
    (CONJUNCTS nt_distinct_ths);
  tbl;;

let PARSE1AUX_NT_EQ_CONV tm =
  let l,r = dest_eq tm in
  if l = r then EQT_INTRO(REFL l)
  else Hashtbl.find PARSE1AUX_nt_eq_tbl (fst(dest_const l),fst(dest_const r));;

let PARSE1AUX_INL_EQ_CONV =
  REWR_CONV(CONJUNCT1(injectivity "sum")) THENC PARSE1AUX_NT_EQ_CONV;;

let rec PARSE1AUX_FAPPLY_UPDATES_CONV tm =
  let th1 = REWR_CONV FAPPLY_FUPDATE_THM tm in
  let th2 = CONV_RULE (RAND_CONV
              (RATOR_CONV(RATOR_CONV(RAND_CONV PARSE1AUX_INL_EQ_CONV)) THENC
               GEN_REWRITE_CONV I [COND_CLAUSES])) th1 in
  let r = rhs(concl th2) in
  if is_comb r && is_comb(rator r) && is_const(rator(rator r)) &&
     fst(dest_const(rator(rator r))) = "FAPPLY"
  then TRANS th2 (PARSE1AUX_FAPPLY_UPDATES_CONV r) else th2;;

let cmlG_applied =
  let cs = map rhs (disjuncts(snd(dest_forall(concl(cases "MMLnonT"))))) in
  let inl = `INL:MMLnonT->MMLnonT+num` in
  let app c =
    (RATOR_CONV(RAND_CONV(K PARSE1AUX_cmlG_rules)) THENC
     PARSE1AUX_FAPPLY_UPDATES_CONV THENC
     PURE_REWRITE_CONV[INSERT_UNION_EQ; UNION_EMPTY])
    (mk_comb(mk_comb(`FAPPLY:(MMLnonT+num,((token,MMLnonT)symbol)list->bool)fmap
                             ->MMLnonT+num->((token,MMLnonT)symbol)list->bool`,
                     `grammar_rules cmlG`),
             mk_comb(inl,c))) in
  end_itlist CONJ (map app cs);;

let cmlG_FDOM =
  (RAND_CONV(K PARSE1AUX_cmlG_rules) THENC
   PURE_REWRITE_CONV[FDOM_FUPDATE; FDOM_FEMPTY])
  `FDOM (grammar_rules cmlG)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas for the nullability proofs (local in HOL4).                        *)
(* ------------------------------------------------------------------------- *)

let paireq = prove
 (`!(x:A) (y:B) z. (x,y) = z <=> x = FST z /\ y = SND z`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

(* HOL4 states GSPEC_INTER for its GSPEC f (f : B -> A # bool, the set of   *)
(* the FST (f y) with SND (f y)) and the S and o combinators.  HOL Light's   *)
(* GSPEC is the identity on predicates and its comprehensions are built     *)
(* differently, so HOL4's GSPEC f is written as the comprehension over y    *)
(* below, with the combinators beta-reduced.                                *)

let GSPEC_INTER = prove
 (`!(f:B->A#bool) (Q:A->bool).
     {FST (f y) | y | SND (f y)} INTER Q =
     {FST (f y) | y | SND (f y) /\ Q (FST (f y))}`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REWRITE_TAC[IN] THEN
  MESON_TAC[]);;

let RIGHT_INTER_OVER_UNION = prove
 (`!(a:A->bool) b c. (a UNION b) INTER c = (a INTER c) UNION (b INTER c)`,
  SET_TAC[]);;

let GSPEC_applied = prove
 (`!(f:A->bool) x. GSPEC f x <=> x IN GSPEC f`,
  REWRITE_TAC[IN]);;

let nullloop_th = prove
 (`!(G:(A,B)grammar) N sn rest.
     nullableML G (N INSERT sn) (CONS (NT N) rest) <=> F`,
  REWRITE_TAC[nullableML_def; IN_INSERT]);;

let null2 = prove
 (`!(G:(A,B)grammar) sn x y z.
     nullableML G sn (CONS x (CONS y z)) <=>
     nullableML G sn [x] /\ nullableML G sn [y] /\ nullableML G sn z`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [nullableML_by_singletons] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
    [nullableML_by_singletons] THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Nullability of the non-terminals (HOL4 nullable_X).                       *)
(* ------------------------------------------------------------------------- *)

(* HOL4 computes these theorems with an ML procedure (prove_nullable) that   *)
(* unfolds nullableML through cmlG_applied from 32 start symbols, and saves  *)
(* nullable_X (with [simp]) for every non-terminal X that it visits: 59 of   *)
(* the 74, of which TbaseList, PEsfx and TopLevelDecs are nullable.  The     *)
(* port proves the same 59 statements directly (PARSE1AUX_NULLABLE_PROVE,    *)
(* from nullable_CONS_NT), in an order in which the theorems before each one *)
(* decide its right hand sides.                                              *)

let PARSE1AUX_cmlG_FDOM_INL = prove
 (`!n. INL n IN FDOM (grammar_rules cmlG)`,
  REWRITE_TAC[cmlG_FDOM; IN_INSERT; NOT_IN_EMPTY; injectivity "sum"] THEN
  MATCH_MP_TAC MMLnonT_INDUCT THEN REWRITE_TAC[]);;

let PARSE1AUX_nullable_NT = prove
 (`!n. nullable cmlG [NT (INL n)] <=>
       ?r. r IN FAPPLY (grammar_rules cmlG) (INL n) /\ nullable cmlG r`,
  REWRITE_TAC[nullable_CONS_NT; nullable_NIL; PARSE1AUX_cmlG_FDOM_INL]);;

let PARSE1AUX_not_nullable_NT = prove
 (`!n. ~nullable cmlG [NT (INL n)] <=>
       !r. r IN FAPPLY (grammar_rules cmlG) (INL n) ==> ~nullable cmlG r`,
  REWRITE_TAC[PARSE1AUX_nullable_NT] THEN MESON_TAC[]);;

let PARSE1AUX_nullable_CONS2 = prove
 (`!(G:(A,B)grammar) x y z.
     nullable G (CONS x (CONS y z)) <=> nullable G [x] /\ nullable G (CONS y z)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [nullable_by_singletons] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [nullable_by_singletons] THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let PARSE1AUX_nullable_thms = ref ([]:thm list);;

let PARSE1AUX_NULLABLE_PROVE tm =
  let tac =
    if is_neg tm then
      REWRITE_TAC[PARSE1AUX_not_nullable_NT; cmlG_applied] THEN
      REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_UNION; FORALL_IN_GSPEC;
                  NOT_IN_EMPTY] THEN
      REWRITE_TAC([nullable_CONS_TOK; PARSE1AUX_nullable_CONS2] @
                  !PARSE1AUX_nullable_thms)
    else
      REWRITE_TAC[PARSE1AUX_nullable_NT; cmlG_applied] THEN
      EXISTS_TAC `[]:((token,MMLnonT)symbol)list` THEN
      REWRITE_TAC[IN_INSERT; IN_UNION; nullable_NIL] in
  let th = prove(tm,tac) in
  PARSE1AUX_nullable_thms := th :: !PARSE1AUX_nullable_thms; th;;

let nullable_UQConstructorName = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nUQConstructorName)]`;;
let nullable_ConstructorName = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nConstructorName)]`;;
let nullable_Eliteral = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEliteral)]`;;
let nullable_Etuple = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEtuple)]`;;
let nullable_V = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nV)]`;;
let nullable_FQV = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nFQV)]`;;
let nullable_Ebase = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEbase)]`;;
let nullable_Eapp = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEapp)]`;;
let nullable_Emult = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEmult)]`;;
let nullable_Eadd = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEadd)]`;;
let nullable_Elistop = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nElistop)]`;;
let nullable_Erel = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nErel)]`;;
let nullable_Ecomp = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEcomp)]`;;
let nullable_Ebefore = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEbefore)]`;;
let nullable_Etyped = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEtyped)]`;;
let nullable_ElogicAND = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nElogicAND)]`;;
let nullable_ElogicOR = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nElogicOR)]`;;
let nullable_Ehandle = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEhandle)]`;;
let nullable_E = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nE)]`;;
let nullable_UQTyOp = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nUQTyOp)]`;;
let nullable_TyOp = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nTyOp)]`;;
let nullable_PTbase = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPTbase)]`;;
let nullable_TbaseList = PARSE1AUX_NULLABLE_PROVE
  `nullable cmlG [NT (INL nTbaseList)]`;;
let nullable_Tbase = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nTbase)]`;;
let nullable_DType = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nDType)]`;;
let nullable_PType = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPType)]`;;
let nullable_Type = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nType)]`;;
let nullable_TyvarN = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nTyvarN)]`;;
let nullable_TypeDec = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nTypeDec)]`;;
let nullable_SpecLine = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nSpecLine)]`;;
let nullable_Ptuple = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPtuple)]`;;
let nullable_Pbase = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPbase)]`;;
let nullable_PConApp = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPConApp)]`;;
let nullable_LetDec = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nLetDec)]`;;
let nullable_TyVarList = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nTyVarList)]`;;
let nullable_DtypeDecl = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nDtypeDecl)]`;;
let nullable_Structure = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nStructure)]`;;
let nullable_TypeAbbrevDec = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nTypeAbbrevDec)]`;;
let nullable_Decl = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nDecl)]`;;
let nullable_PE = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPE)]`;;
let nullable_Elist1 = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nElist1)]`;;
let nullable_CompOps = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nCompOps)]`;;
let nullable_ListOps = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nListOps)]`;;
let nullable_PEsfx = PARSE1AUX_NULLABLE_PROVE
  `nullable cmlG [NT (INL nPEsfx)]`;;
let nullable_Papp = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPapp)]`;;
let nullable_Pcons = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPcons)]`;;
let nullable_Pas = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPas)]`;;
let nullable_Pattern = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPattern)]`;;
let nullable_PEs = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPEs)]`;;
let nullable_RelOps = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nRelOps)]`;;
let nullable_MultOps = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nMultOps)]`;;
let nullable_AddOps = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nAddOps)]`;;
let nullable_Dconstructor = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nDconstructor)]`;;
let nullable_FDecl = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nFDecl)]`;;
let nullable_PatternList = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPatternList)]`;;
let nullable_PbaseList1 = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nPbaseList1)]`;;
let nullable_Elist2 = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nElist2)]`;;
let nullable_Eseq = PARSE1AUX_NULLABLE_PROVE
  `~nullable cmlG [NT (INL nEseq)]`;;
let nullable_TopLevelDecs = PARSE1AUX_NULLABLE_PROVE
  `nullable cmlG [NT (INL nTopLevelDecs)]`;;

let _ = cake_add_simps (!PARSE1AUX_nullable_thms);;

(* ------------------------------------------------------------------------- *)
(* Fringe lengths and the parsing induction principle.                       *)
(* ------------------------------------------------------------------------- *)

let fringe_lengths_def = cake_def
  `fringe_lengths (G:(A,B)grammar) sf =
     {LENGTH i | i | RTC (derive G) sf (MAP TOK i)}`;;

let fringe_length_ptree = prove
 (`!(G:(A,B)grammar) i (pt:(A,B,C)parsetree).
     ptree_fringe pt = MAP TOK i /\ valid_ptree G pt ==>
     LENGTH i IN fringe_lengths G [ptree_head pt]`,
  REWRITE_TAC[fringe_lengths_def; IN_ELIM_THM] THEN
  MESON_TAC[valid_ptree_derive]);;

let fringe_length_not_nullable = prove
 (`!(G:(A,B)grammar) s.
     ~nullable G [s] ==>
     !pt:(A,B,C)parsetree. ptree_head pt = s ==> valid_ptree G pt ==>
                           0 < LENGTH (ptree_fringe pt)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; LENGTH_EQ_NIL] THEN
  DISCH_TAC THEN UNDISCH_TAC `~nullable (G:(A,B)grammar) [s]` THEN
  REWRITE_TAC[nullable_def] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP valid_ptree_derive) THEN
  ASM_REWRITE_TAC[]);;

let derives_singleTOK = prove
 (`!(G:(A,B)grammar) t l. RTC (derive G) [TOK t] l <=> l = [TOK t]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!y. ~derive (G:(A,B)grammar) [TOK t] y` ASSUME_TAC THENL
   [REWRITE_TAC[derive_def; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:((A,B)symbol)list`; `p:((A,B)symbol)list`;
                         `n:B+num`; `r:((A,B)symbol)list`;
                         `s:((A,B)symbol)list`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `MEM (NT (n:B+num):(A,B)symbol)` o CONJUNCT1) THEN
    REWRITE_TAC[MEM; MEM_APPEND; symbol_distinct];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [RTC_CASES_R] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [derives_singleTOK];;

let fringe_lengths_V = prove
 (`fringe_lengths cmlG [NT (INL nV)] = {1}`,
  SUBGOAL_THEN `!i. ~([NT (INL nV)] = MAP (TOK:token->(token,MMLnonT)symbol) i)`
    ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; symbol_distinct];
    ALL_TAC] THEN
  REWRITE_TAC[fringe_lengths_def; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `x:num` THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  ASM_REWRITE_TAC[derive_1NT; PARSE1AUX_cmlG_FDOM_INL; cmlG_applied; IN_UNION;
                  IN_ELIM_THM] THEN
  EQ_TAC THENL
   [REPEAT STRIP_TAC THEN GVS[derives_singleTOK; MAP_EQ_SING; LENGTH] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `[AlphaT (implode "foo")]` THEN
    REWRITE_TAC[MAP; LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
    EXISTS_TAC `[TOK (AlphaT (implode "foo"))]:((token,MMLnonT)symbol)list` THEN
    REWRITE_TAC[RTC_REFL] THEN DISJ1_TAC THEN EXISTS_TAC `implode "foo"` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; injectivity "mlstring"; strsub_def] THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
    REWRITE_TAC[EL; HD; isUpper_def; ORD_DEF; BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let parsing_ind =
  let r = CASE_TERM
    `inv_image (measure (LENGTH:((token,MMLnonT)symbol#locs)list->num) LEX
                measure (\n:(token,MMLnonT)symbol.
                           match n with TOK _ -> 0 | NT n -> NT_rank n))
               (\pt:mlptree. real_fringe pt,ptree_head pt)` in
  let wf = prove(mk_comb(`WF:(mlptree->mlptree->bool)->bool`,r), WF_TAC) in
  prove
   (CASE_TERM
    `!P. (!x:mlptree.
            (!y. LENGTH (real_fringe y) < LENGTH (real_fringe x) \/
                 real_fringe y = real_fringe x /\
                 (match ptree_head y with TOK _ -> 0 | NT n -> NT_rank n) <
                 (match ptree_head x with TOK _ -> 0 | NT n -> NT_rank n)
                 ==> P y)
            ==> P x)
         ==> !x. P x`,
    GEN_TAC THEN MP_TAC(SPEC `P:mlptree->bool` (REWRITE_RULE[WF_IND] wf)) THEN
    REWRITE_TAC[inv_image_THM; LEX_THM; measure_THM]);;
