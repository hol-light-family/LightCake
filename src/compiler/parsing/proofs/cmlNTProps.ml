(* ========================================================================= *)
(* cmlNTProps: port of HOL4 compiler/parsing/proofs/cmlNTPropsScript.sml    *)
(* (CakeML v3479).                                                           *)
(* Properties (first sets etc) for non-terminals in the CakeML grammar.     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's overloads NN n (NT (INL n)) and mkNT (INL) are written out; the  *)
(*   unions of HOL4's statements associate to the left, as in HOL4 (HOL      *)
(*   Light's UNION associates to the right, so they are parenthesized); set  *)
(*   comprehensions name their bound variables; the free variables of the   *)
(*   HOL4 statements are universally quantified.                            *)
(* - disjImpI (local in HOL4) is cmlNTProps_disjImpI; IMAGE_GSPEC1 and       *)
(*   BIGUNION_singletons are about HOL4's GSPEC and are stated for HOL       *)
(*   Light's comprehensions.                                                 *)
(* - The first sets are proved by unfolding firstSetML_def (firstSet via     *)
(*   firstSetML_eqn) with a conversion, the membership of the seen set      *)
(*   decided from its elements and from the hypotheses ~(INL n IN sn), and   *)
(*   by comparing both sides part by part (HOL4 uses simp with firstSet_NT,  *)
(*   firstSetML_def and the theorems before).  It uses gramProps' helpers    *)
(*   PARSE1AUX_cmlG_FDOM_INL and PARSE1AUX_INL_EQ_CONV.                      *)
(* - Helpers that are not HOL4 names have the prefix PARSE2AUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/gram.ml";;
needs "hol4/NTproperties.ml";;
needs "semantics/proofs/gramProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Helpers (not HOL4 names).  HOL4 proves the first sets with simp, using    *)
(* firstSet_NT or firstSetML_def (with firstSetML_eqn), cmlG_applied and     *)
(* cmlG_FDOM, and the theorems proved before.  The port computes them with  *)
(* a conversion that unfolds firstSetML on explicit sentential forms, with   *)
(* the seen set decided from its explicit elements and from hypotheses     *)
(* ~(INL n IN sn) (as in HOL4, every unfolding step is a rewrite with        *)
(* firstSetML_def); then the two sides are compared by extensionality.      *)
(* gramProps' helpers PARSE1AUX_cmlG_FDOM_INL (every INL n is in the domain) *)
(* and PARSE1AUX_INL_EQ_CONV (equations INL n = INL m decided) are used.    *)
(* ------------------------------------------------------------------------- *)

let PARSE2AUX_FSML_CLAUSES = CONJUNCTS firstSetML_def;;

let PARSE2AUX_UNIONS_FSML_GSPEC1 = prove
 (`!(G:(A,B)grammar) sn (g:C->A) (r:C->((A,B)symbol)list) P.
     UNIONS (IMAGE (firstSetML G sn) {CONS (grammar_TOK (g a)) (r a) | a | P a}) =
     {g a | a | P a}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THEN STRIP_TAC THEN
  GVS[firstSetML_def; IN_SING] THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `{(g:C->A) a}` THEN REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `CONS (grammar_TOK ((g:C->A) a)) ((r:C->((A,B)symbol)list) a)` THEN
    REWRITE_TAC[firstSetML_def] THEN ASM_MESON_TAC[]]);;

let PARSE2AUX_UNIONS_FSML_GSPEC2 = prove
 (`!(G:(A,B)grammar) sn (g:C->D->A) (r:C->D->((A,B)symbol)list) P.
     UNIONS (IMAGE (firstSetML G sn)
                   {CONS (grammar_TOK (g a b)) (r a b) | a,b | P a b}) =
     {g a b | a,b | P a b}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THEN STRIP_TAC THEN
  GVS[firstSetML_def; IN_SING] THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `{(g:C->D->A) a b}` THEN REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `CONS (grammar_TOK ((g:C->D->A) a b)) ((r:C->D->((A,B)symbol)list) a b)` THEN
    REWRITE_TAC[firstSetML_def] THEN ASM_MESON_TAC[]]);;

let PARSE2AUX_NULLABLE =
  [nullable_UQConstructorName; nullable_ConstructorName; nullable_Eliteral;
   nullable_Etuple; nullable_V; nullable_FQV; nullable_Ebase; nullable_Eapp;
   nullable_Emult; nullable_Eadd; nullable_Elistop; nullable_Erel;
   nullable_Ecomp; nullable_Ebefore; nullable_Etyped; nullable_ElogicAND;
   nullable_ElogicOR; nullable_Ehandle; nullable_E; nullable_UQTyOp;
   nullable_TyOp; nullable_PTbase; nullable_TbaseList; nullable_Tbase;
   nullable_DType; nullable_PType; nullable_Type; nullable_TyvarN;
   nullable_TypeDec; nullable_SpecLine; nullable_Ptuple; nullable_Pbase;
   nullable_PConApp; nullable_LetDec; nullable_TyVarList; nullable_DtypeDecl;
   nullable_Structure; nullable_TypeAbbrevDec; nullable_Decl; nullable_PE;
   nullable_Elist1; nullable_CompOps; nullable_ListOps; nullable_PEsfx;
   nullable_Papp; nullable_Pcons; nullable_Pas; nullable_Pattern;
   nullable_PEs; nullable_RelOps; nullable_MultOps; nullable_AddOps;
   nullable_Dconstructor; nullable_FDecl; nullable_PatternList;
   nullable_PbaseList1; nullable_Elist2; nullable_Eseq; nullable_TopLevelDecs];;

(* nullable cmlG [NT (INL n)] decided to T or F, if a theorem says so *)

let PARSE2AUX_NULLABLE_CONV tm =
  try find (fun th -> rand(concl th) = tm || concl th = tm)
           PARSE2AUX_NULLABLE |>
      (fun th -> if concl th = tm then EQT_INTRO th else EQF_INTRO th)
  with Failure _ -> failwith "PARSE2AUX_NULLABLE_CONV";;

(* INL m IN s, for s built with INSERT from the empty set or a variable sn; *)
(* decided from the explicit elements and the hypotheses ~(INL m IN sn)     *)

let PARSE2AUX_SEEN_CONV (hyps:thm list) =
  let tor = TAUT `!p. (T \/ p) <=> T` and forr = TAUT `!p. (F \/ p) <=> p` in
  let in_empty = prove(`!x:MMLnonT+num. x IN {} <=> F`, REWRITE_TAC[NOT_IN_EMPTY]) in
  let rec conv tm =
    (REWR_CONV in_empty ORELSEC
     (REWR_CONV IN_INSERT THENC LAND_CONV PARSE1AUX_INL_EQ_CONV THENC
      (REWR_CONV tor ORELSEC (REWR_CONV forr THENC conv))) ORELSEC
     (fun tm -> EQF_INTRO (find (fun th -> concl th = mk_neg tm) hyps)) ORELSEC
     REFL) tm in
  conv;;

let PARSE2AUX_FSML_SPLIT_RWTS =
  [IMAGE_UNION; IMAGE_CLAUSES; UNIONS_UNION; UNIONS_INSERT; UNIONS_0;
   PARSE2AUX_UNIONS_FSML_GSPEC1; PARSE2AUX_UNIONS_FSML_GSPEC2; UNION_EMPTY];;

let PARSE2AUX_COND_T = prove(`!(x:A) y. (if T then x else y) = x`, REWRITE_TAC[]);;
let PARSE2AUX_COND_F = prove(`!(x:A) y. (if F then x else y) = y`, REWRITE_TAC[]);;

let PARSE2AUX_RULE_CONV tm =
  REWR_CONV (find (fun r -> lhs(concl r) = tm) (CONJUNCTS cmlG_applied)) tm;;

let rec PARSE2AUX_FSML_CONV (hyps:thm list) tm =
  let f,args = strip_comb tm in
  if not (is_const f && fst(dest_const f) = "firstSetML" && length args = 3)
  then failwith "PARSE2AUX_FSML_CONV" else
  let sf = el 2 args in
  if is_const sf then REWR_CONV (el 0 PARSE2AUX_FSML_CLAUSES) tm else
  if not (is_cons sf) then failwith "PARSE2AUX_FSML_CONV: not explicit" else
  let h = hd(snd(strip_comb sf)) in
  if fst(dest_const(fst(strip_comb h))) = "grammar_TOK"
  then REWR_CONV (el 1 PARSE2AUX_FSML_CLAUSES) tm else
  let fdom_conv t =
    let c = lhand(rator t) in
    (RATOR_CONV(RATOR_CONV(RAND_CONV
       (K (EQT_INTRO (SPEC (rand(lhand c)) PARSE1AUX_cmlG_FDOM_INL))))) THENC
     REWR_CONV PARSE2AUX_COND_T) t in
  (* UNIONS (IMAGE (firstSetML cmlG seen') (FAPPLY (grammar_rules cmlG) n)) *)
  let seen_then =
    RAND_CONV (RAND_CONV PARSE2AUX_RULE_CONV) THENC
    PURE_REWRITE_CONV PARSE2AUX_FSML_SPLIT_RWTS THENC
    ONCE_DEPTH_CONV (PARSE2AUX_FSML_CONV hyps) in
  (* if ~(INL n IN seen) then .. else the empty set *)
  let seen_part t =
    let cth = (RAND_CONV (PARSE2AUX_SEEN_CONV hyps) THENC
               TRY_CONV (GEN_REWRITE_CONV I [NOT_CLAUSES])) (lhand(rator t)) in
    let th = RATOR_CONV(RATOR_CONV(RAND_CONV(K cth))) t in
    let d = rhs(concl cth) in
    if d = `T` then
      TRANS th ((REWR_CONV PARSE2AUX_COND_T THENC seen_then) (rhs(concl th)))
    else if d = `F` then TRANS th (REWR_CONV PARSE2AUX_COND_F (rhs(concl th)))
    else TRANS th (LAND_CONV seen_then (rhs(concl th))) in
  (* if nullable cmlG [NT n] then firstSetML cmlG seen rest else empty *)
  let null_part t =
    let c = lhand(rator t) in
    try let cth = PARSE2AUX_NULLABLE_CONV c in
        let th = RATOR_CONV(RATOR_CONV(RAND_CONV(K cth))) t in
        if rhs(concl cth) = `T` then
          TRANS th ((REWR_CONV PARSE2AUX_COND_T THENC
                     TRY_CONV (PARSE2AUX_FSML_CONV hyps)) (rhs(concl th)))
        else TRANS th (REWR_CONV PARSE2AUX_COND_F (rhs(concl th)))
    with Failure _ ->
      (LAND_CONV (TRY_CONV (PARSE2AUX_FSML_CONV hyps)) THENC
       TRY_CONV (REWR_CONV COND_ID)) t in
  (REWR_CONV (el 2 PARSE2AUX_FSML_CLAUSES) THENC fdom_conv THENC
   LAND_CONV seen_part THENC RAND_CONV null_part THENC
   PURE_REWRITE_CONV[UNION_EMPTY]) tm;;

(* A SUBSET C for unions of explicit parts: each part of A is found among   *)
(* the parts of C (up to alpha-conversion), or else proved by first-order   *)
(* reasoning on its own                                                     *)

let PARSE2AUX_COND_SUBSET = prove
 (`!b (s:A->bool) t c.
     (if b then s else t) SUBSET c <=> (b ==> s SUBSET c) /\ (~b ==> t SUBSET c)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let PARSE2AUX_SUBSET_UNION_L = prove
 (`!(a:A->bool) c1 c2. a SUBSET c1 ==> a SUBSET (c1 UNION c2)`,
  SET_TAC[]);;

let PARSE2AUX_SUBSET_UNION_R = prove
 (`!(a:A->bool) c1 c2. a SUBSET c2 ==> a SUBSET (c1 UNION c2)`,
  SET_TAC[]);;

let PARSE2AUX_IN_UNION_L = prove
 (`!(x:A) c1 c2. x IN c1 ==> x IN (c1 UNION c2)`,
  SET_TAC[]);;

let PARSE2AUX_IN_UNION_R = prove
 (`!(x:A) c1 c2. x IN c2 ==> x IN (c1 UNION c2)`,
  SET_TAC[]);;

let PARSE2AUX_IN_INSERT_TAIL = prove
 (`!(x:A) y s. x IN s ==> x IN (y INSERT s)`,
  SIMP_TAC[IN_INSERT]);;

let PARSE2AUX_dest_insert t =
  match t with
    Comb(Comb(Const("INSERT",_),x),s) -> x,s
  | _ -> failwith "PARSE2AUX_dest_insert";;

let PARSE2AUX_is_union t =
  try fst(dest_const(rator(rator t))) = "UNION" with Failure _ -> false;;

(* a SUBSET c, a a part of c; fails if a is not found *)

let rec PARSE2AUX_PART_SUBSET a c =
  if aconv a c then ISPEC a SUBSET_REFL
  else if PARSE2AUX_is_union c then
    let c1 = lhand c and c2 = rand c in
    (try MP (ISPECL [a;c1;c2] PARSE2AUX_SUBSET_UNION_L) (PARSE2AUX_PART_SUBSET a c1)
     with Failure _ ->
       MP (ISPECL [a;c1;c2] PARSE2AUX_SUBSET_UNION_R) (PARSE2AUX_PART_SUBSET a c2))
  else failwith "PARSE2AUX_PART_SUBSET";;

(* x IN c, x an element of an explicit INSERT part of c *)

let rec PARSE2AUX_ELEM_IN x c =
  if PARSE2AUX_is_union c then
    let c1 = lhand c and c2 = rand c in
    (try MP (ISPECL [x;c1;c2] PARSE2AUX_IN_UNION_L) (PARSE2AUX_ELEM_IN x c1)
     with Failure _ ->
       MP (ISPECL [x;c1;c2] PARSE2AUX_IN_UNION_R) (PARSE2AUX_ELEM_IN x c2))
  else
    try let y,s = PARSE2AUX_dest_insert c in
        if aconv x y then ISPECL [x;s] COMPONENT
        else MP (ISPECL [x;y;s] PARSE2AUX_IN_INSERT_TAIL) (PARSE2AUX_ELEM_IN x s)
    with Failure _ -> failwith "PARSE2AUX_ELEM_IN";;

let rec PARSE2AUX_SUBSET_TAC : tactic = fun (asl,w as g) ->
  let a = lhand w and c = rand w in
  if PARSE2AUX_is_union a then
    (GEN_REWRITE_TAC I [UNION_SUBSET] THEN CONJ_TAC THEN PARSE2AUX_SUBSET_TAC) g
  else if is_const a && fst(dest_const a) = "EMPTY" then
    MATCH_ACCEPT_TAC EMPTY_SUBSET g
  else if is_cond a then
    (GEN_REWRITE_TAC I [PARSE2AUX_COND_SUBSET] THEN CONJ_TAC THEN
     DISCH_TAC THEN PARSE2AUX_SUBSET_TAC) g
  else
    (try ACCEPT_TAC (PARSE2AUX_PART_SUBSET a c) g with Failure _ ->
     try let x,s = PARSE2AUX_dest_insert a in
         (GEN_REWRITE_TAC I [INSERT_SUBSET] THEN CONJ_TAC THENL
           [(fun g -> ACCEPT_TAC (PARSE2AUX_ELEM_IN x c) g) ORELSE
            (REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY;
                         COND_RAND; COND_EXPAND_IMP] THEN ASM_MESON_TAC[]);
            PARSE2AUX_SUBSET_TAC]) g
     with Failure _ ->
       (REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY;
                    COND_RAND; COND_EXPAND_IMP] THEN ASM_MESON_TAC[]) g);;

(* HOL4: simp[firstSetML_eqn], simp[Once firstSetML_def, cmlG_applied,       *)
(* cmlG_FDOM] (repeatedly) and dsimp[Once EXTENSION, EQ_IMP_THM]: both       *)
(* sides unfolded, then compared part by part                               *)

let PARSE2AUX_FS_TAC : tactic =
  REPEAT STRIP_TAC THEN REWRITE_TAC[firstSetML_eqn] THEN
  ASSUM_LIST (fun asl -> CONV_TAC (ONCE_DEPTH_CONV (PARSE2AUX_FSML_CONV asl))) THEN
  GEN_REWRITE_TAC I [GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
  PARSE2AUX_SUBSET_TAC;;

(* ------------------------------------------------------------------------- *)
(* The first sets.                                                           *)
(* ------------------------------------------------------------------------- *)

(* HOL4: disjImpI (local) *)

let cmlNTProps_disjImpI = prove
 (`!p q. ~p \/ q <=> (p ==> q)`,
  REPEAT GEN_TAC THEN CONV_TAC TAUT);;

let firstSet_nUQTyOp = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nUQTyOp)) rest) =
          {AlphaT s | s | T} UNION {SymbolT s | s | T}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nUQTyOp];;

let firstSet_nTyOp = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nTyOp)) rest) =
          ({AlphaT s | s | T} UNION {SymbolT s | s | T}) UNION
          {LongidT s1 s2 | s1,s2 | T}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nTyOp];;

let firstSet_nPTbase = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPTbase)) rest) =
          (firstSet cmlG [grammar_NT (INL nTyOp)] UNION {LparT}) UNION
          {TyvarT s | s | T}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPTbase];;

let firstSet_nTbaseList = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nTbaseList)) rest) =
          firstSet cmlG [grammar_NT (INL nPTbase)] UNION firstSet cmlG rest`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nTbaseList];;

let firstSet_nTyVarList = prove
 (`firstSet cmlG [grammar_NT (INL nTyVarList)] = {TyvarT s | s | T}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nTyVarList];;

(* HOL4 adds the first two clauses of firstSetML_def to its simpset for the *)
(* rest of the script (augment_srw_ss, not exported); the proofs here use    *)
(* firstSetML_def directly.                                                 *)

let firstSet_nLetDec = prove
 (`firstSet cmlG [grammar_NT (INL nLetDec)] = {ValT, FunT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nLetDec];;

let firstSet_nLetDecs = prove
 (`firstSet cmlG [grammar_NT (INL nLetDecs)] = {ValT, FunT, SemicolonT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nLetDecs];;

let firstSet_nTypeDec = prove
 (`firstSet cmlG [grammar_NT (INL nTypeDec)] = {DatatypeT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nTypeDec];;

let firstSet_nTypeAbbrevDec = prove
 (`firstSet cmlG [grammar_NT (INL nTypeAbbrevDec)] = {TypeT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nTypeAbbrevDec];;

let firstSet_nStructure = prove
 (`firstSet cmlG [grammar_NT (INL nStructure)] = {StructureT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nStructure];;

let firstSet_nDecl = prove
 (`firstSet cmlG [grammar_NT (INL nDecl)] =
   {ValT, FunT, DatatypeT, ExceptionT, TypeT, LocalT, StructureT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nDecl];;

let firstSet_nDecls = prove
 (`firstSet cmlG [grammar_NT (INL nDecls)] =
   {ValT, DatatypeT, FunT, SemicolonT, ExceptionT, TypeT, LocalT, StructureT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nDecls];;

(* HOL4: IMAGE_GSPEC1 and BIGUNION_singletons (local), about HOL4's GSPEC;  *)
(* stated for the corresponding HOL Light comprehensions                     *)

let IMAGE_GSPEC1 = prove
 (`!(f:B->C) (g:A->B) (P:A->bool).
     IMAGE f {g a | a | P a} = {f (g a) | a | P a}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let BIGUNION_singletons = prove
 (`!(f:A->B) (P:A->bool). UNIONS {{f a} | a | P a} = {f a | a | P a}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:B->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `a:A` THEN ASM_MESON_TAC[IN_SING];
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{(f:A->B) a}` THEN REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]]);;


let firstSet_nMultOps = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nMultOps)) rest) =
          {AlphaT (implode "div"), AlphaT (implode "mod"), StarT} UNION
          {SymbolT s | s | validMultSym (explode s)}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nMultOps];;

let firstSet_nRelOps = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nRelOps)) rest) =
          EqualsT INSERT {SymbolT s | s | validRelSym (explode s)}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nRelOps];;

let firstSet_nAddOps = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nAddOps)) rest) =
          {SymbolT s | s | validAddSym (explode s)}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nAddOps];;

let firstSet_nCompOps = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nCompOps)) rest) =
          {AlphaT (implode "o"), SymbolT (implode ":=")}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nCompOps];;

let firstSet_nListOps = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nListOps)) rest) =
          {SymbolT s | s | validListSym (explode s)}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nListOps];;

let firstSet_nSpecLine = prove
 (`firstSet cmlG [grammar_NT (INL nSpecLine)] = {ValT, DatatypeT, TypeT, ExceptionT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nSpecLine];;

let firstSet_nSpecLineList = prove
 (`firstSet cmlG [grammar_NT (INL nSpecLineList)] =
   {ValT, DatatypeT, TypeT, SemicolonT, ExceptionT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nSpecLineList];;

let firstSet_nV = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nV)) rest) =
          {AlphaT s | s | ~(s = implode "") /\ ~isUpper (strsub s 0) /\
                          ~(s = implode "before") /\ ~(s = implode "div") /\
                          ~(s = implode "mod") /\ ~(s = implode "o")} UNION
          {SymbolT s | s | validPrefixSym (explode s)}`,
  PARSE2AUX_FS_TAC);;

let firstSet_nFQV = prove
 (`firstSet cmlG [grammar_NT (INL nFQV)] =
   firstSet cmlG [grammar_NT (INL nV)] UNION
   {LongidT m i | m,i | ~(i = implode "") /\
                        (isAlpha (strsub i 0) ==> ~isUpper (strsub i 0))}`,
  PARSE2AUX_FS_TAC);;

let firstSet_nUQConstructorName = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nUQConstructorName)) rest) =
          {AlphaT s | s | ~(s = implode "") /\ isUpper (strsub s 0)}`,
  PARSE2AUX_FS_TAC);;

let firstSet_nConstructorName = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nConstructorName)) rest) =
          {LongidT str s | str,s | ~(s = implode "") /\ isAlpha (strsub s 0) /\
                                   isUpper (strsub s 0)} UNION
          {AlphaT s | s | ~(s = implode "") /\ isUpper (strsub s 0)}`,
  PARSE2AUX_FS_TAC);;


let firstSetML_nConstructorName = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nConstructorName)) rest) =
         firstSet cmlG [grammar_NT (INL nConstructorName)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nConstructorName];;

let firstSetML_nV = prove
 (`!sn rest.
     ~(INL nV IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nV)) rest) =
         firstSet cmlG [grammar_NT (INL nV)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nV];;

let firstSetML_nFQV = prove
 (`!sn rest.
     ~(INL nFQV IN sn) /\ ~(INL nV IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nFQV)) rest) =
         firstSet cmlG [grammar_NT (INL nFQV)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nFQV];;

let firstSet_nEtuple = prove
 (`firstSet cmlG [grammar_NT (INL nEtuple)] = {LparT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEtuple];;

let firstSet_nEliteral = prove
 (`firstSet cmlG [grammar_NT (INL nEliteral)] =
   (((({tokens_IntT i | i | T} UNION {StringT s | s | T}) UNION
      {tokens_CharT c | c | T}) UNION {tokens_WordT w | w | T}) UNION
    {FFIT s | s | T})`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEliteral];;

let firstSetML_nEliteral = prove
 (`!sn rest.
     ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEliteral)) rest) =
         firstSet cmlG [grammar_NT (INL nEliteral)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEliteral];;

let firstSet_nEbase = prove
 (`firstSet cmlG [grammar_NT (INL nEbase)] =
   (({LetT, LparT, LbrackT, OpT} UNION firstSet cmlG [grammar_NT (INL nFQV)]) UNION
    firstSet cmlG [grammar_NT (INL nEliteral)]) UNION
   firstSet cmlG [grammar_NT (INL nConstructorName)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEbase];;

let firstSetML_nEbase = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEbase)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEbase];;

let firstSet_nEapp = prove
 (`firstSet cmlG [grammar_NT (INL nEapp)] = firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEapp];;

let firstSetML_nEapp = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEapp)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEapp];;

let firstSet_nEmult = prove
 (`firstSet cmlG [grammar_NT (INL nEmult)] = firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEmult];;

let firstSetML_nEmult = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEmult)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEmult];;

let firstSet_nEadd = prove
 (`firstSet cmlG [grammar_NT (INL nEadd)] = firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEadd];;

let firstSetML_nEadd = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEadd)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEadd];;

let firstSet_nElistop = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nElistop)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nElistop];;

let firstSetML_nElistop = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nElistop)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nElistop];;

let firstSet_nErel = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nErel)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nErel];;

let firstSetML_nErel = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nErel)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nErel];;

let firstSet_nEcomp = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nEcomp)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEcomp];;

let firstSetML_nEcomp = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nElistop IN sn) /\
     ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEcomp)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEcomp];;

let firstSet_nEbefore = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nEbefore)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEbefore];;

let firstSetML_nEbefore = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nEbefore IN sn) /\
     ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEbefore)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEbefore];;

let firstSet_nEtyped = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nEtyped)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEtyped];;

let firstSetML_nEtyped = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nEbefore IN sn) /\
     ~(INL nEtyped IN sn) /\ ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEtyped)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEtyped];;

let firstSet_nElogicAND = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nElogicAND)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nElogicAND];;

let firstSetML_nElogicAND = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nEbefore IN sn) /\
     ~(INL nEtyped IN sn) /\ ~(INL nElogicAND IN sn) /\
     ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nElogicAND)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nElogicAND];;

let firstSet_nElogicOR = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nElogicOR)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nElogicOR];;

let firstSetML_nElogicOR = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nEbefore IN sn) /\
     ~(INL nEtyped IN sn) /\ ~(INL nElogicAND IN sn) /\
     ~(INL nElogicOR IN sn) /\ ~(INL nElistop IN sn) /\
     ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nElogicOR)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nElogicOR];;

let firstSet_nEhandle = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nEhandle)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEhandle];;

let firstSetML_nEhandle = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nEbefore IN sn) /\
     ~(INL nEtyped IN sn) /\ ~(INL nElogicAND IN sn) /\
     ~(INL nElogicOR IN sn) /\ ~(INL nEhandle IN sn) /\
     ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nEhandle)) rest) =
         firstSet cmlG [grammar_NT (INL nEbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nEhandle];;

let firstSet_nE = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nE)) rest) =
          firstSet cmlG [grammar_NT (INL nEbase)] UNION {IfT, CaseT, FnT, RaiseT}`,
  PARSE2AUX_FS_TAC);;

let firstSet_nTopLevelDecs = prove
 (`firstSet cmlG [grammar_NT (INL nTopLevelDecs)] =
   {ValT, FunT, SemicolonT, DatatypeT, StructureT, ExceptionT, TypeT,
    LocalT} UNION
   firstSet cmlG [grammar_NT (INL nE)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nTopLevelDecs];;

let firstSet_nNonETopLevelDecs = prove
 (`firstSet cmlG [grammar_NT (INL nNonETopLevelDecs)] =
   {ValT, FunT, SemicolonT, DatatypeT, StructureT, ExceptionT, TypeT, LocalT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nNonETopLevelDecs];;

let firstSet_nEseq = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nEseq)) rest) =
          firstSet cmlG [grammar_NT (INL nE)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nEseq];;

(* HOL4: simp[firstSet_nE, ...]: the first sets unfolded, then the token     *)
(* equations decided                                                        *)

let PARSE2AUX_NOTIN_TAC (thl:thm list) : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(thl @ [firstSet_nEbase; firstSet_nEliteral; IN_UNION; IN_INSERT;
                     IN_ELIM_THM; NOT_IN_EMPTY]) THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[];;

let NOTIN_firstSet_nE = prove
 (`!rest.
     ~(ValT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(StructureT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(FunT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(DatatypeT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(ExceptionT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(SemicolonT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(RparT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(RbrackT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest)) /\
     ~(TypeT IN firstSet cmlG (CONS (grammar_NT (INL nE)) rest))`,
  PARSE2AUX_NOTIN_TAC [firstSet_nE; firstSet_nFQV; firstSet_nV;
                       firstSet_nConstructorName]);;
let _ = cake_add_simps [NOTIN_firstSet_nE];;

let firstSetML_nE = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nUQConstructorName IN sn) /\
     ~(INL nEbase IN sn) /\ ~(INL nFQV IN sn) /\ ~(INL nV IN sn) /\
     ~(INL nEapp IN sn) /\ ~(INL nEmult IN sn) /\ ~(INL nEadd IN sn) /\
     ~(INL nErel IN sn) /\ ~(INL nEcomp IN sn) /\ ~(INL nEbefore IN sn) /\
     ~(INL nEtyped IN sn) /\ ~(INL nElogicAND IN sn) /\
     ~(INL nElogicOR IN sn) /\ ~(INL nEhandle IN sn) /\ ~(INL nE IN sn) /\
     ~(INL nElistop IN sn) /\ ~(INL nEliteral IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nE)) rest) =
         firstSet cmlG [grammar_NT (INL nE)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nE];;

let firstSet_nElist1 = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nElist1)) rest) =
          firstSet cmlG [grammar_NT (INL nE)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nElist1];;

let firstSet_nElist2 = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nElist2)) rest) =
          firstSet cmlG [grammar_NT (INL nE)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nElist2];;

let firstSetML_nPtuple = prove
 (`!sn rest.
     ~(INL nPtuple IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nPtuple)) rest) = {LparT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nPtuple];;

let firstSet_nPtuple = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPtuple)) rest) = {LparT}`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPtuple];;

let firstSet_nPbase = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPbase)) rest) =
          (((({LparT, UnderbarT, LbrackT, OpT} UNION {tokens_IntT i | i | T}) UNION
             {StringT s | s | T}) UNION {tokens_CharT c | c | T}) UNION
           firstSet cmlG [grammar_NT (INL nConstructorName)]) UNION
          firstSet cmlG [grammar_NT (INL nV)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPbase];;

let firstSetML_nPbase = prove
 (`!sn rest.
     ~(INL nPbase IN sn) /\ ~(INL nV IN sn) /\ ~(INL nConstructorName IN sn) /\
     ~(INL nUQConstructorName IN sn) /\ ~(INL nPtuple IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nPbase)) rest) =
         firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nPbase];;

let firstSet_nPConApp = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPConApp)) rest) =
          firstSet cmlG [grammar_NT (INL nConstructorName)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPConApp];;

let firstSetML_nPConApp = prove
 (`!sn rest.
     ~(INL nConstructorName IN sn) /\ ~(INL nPConApp IN sn) /\
     ~(INL nUQConstructorName IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nPConApp)) rest) =
         firstSet cmlG [grammar_NT (INL nConstructorName)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nPConApp];;

let firstSet_nPapp = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPapp)) rest) =
          firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPapp];;

let firstSetML_nPapp = prove
 (`!sn rest.
     ~(INL nPbase IN sn) /\ ~(INL nV IN sn) /\ ~(INL nConstructorName IN sn) /\
     ~(INL nUQConstructorName IN sn) /\ ~(INL nPtuple IN sn) /\
     ~(INL nPapp IN sn) /\ ~(INL nPConApp IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nPapp)) rest) =
         firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nPapp];;

let firstSet_nPcons = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPcons)) rest) =
          firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPcons];;

let firstSetML_nPcons = prove
 (`!sn rest.
     ~(INL nPbase IN sn) /\ ~(INL nV IN sn) /\ ~(INL nConstructorName IN sn) /\
     ~(INL nUQConstructorName IN sn) /\ ~(INL nPtuple IN sn) /\
     ~(INL nPapp IN sn) /\ ~(INL nPcons IN sn) /\ ~(INL nPConApp IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nPcons)) rest) =
         firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nPcons];;

let firstSet_nPas = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPas)) rest) =
          firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPas];;

let firstSetML_nPas = prove
 (`!sn rest.
     ~(INL nPbase IN sn) /\ ~(INL nV IN sn) /\ ~(INL nConstructorName IN sn) /\
     ~(INL nUQConstructorName IN sn) /\ ~(INL nPtuple IN sn) /\
     ~(INL nPapp IN sn) /\ ~(INL nPcons IN sn) /\ ~(INL nPConApp IN sn) /\
     ~(INL nPas IN sn)
     ==> firstSetML cmlG sn (CONS (grammar_NT (INL nPas)) rest) =
         firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSetML_nPas];;

let firstSet_nPattern = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPattern)) rest) =
          firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPattern];;

let firstSet_nPatternList = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPatternList)) rest) =
          firstSet cmlG [grammar_NT (INL nPattern)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPatternList];;

let firstSet_nPbaseList1 = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPbaseList1)) rest) =
          firstSet cmlG [grammar_NT (INL nPbase)]`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPbaseList1];;

let firstSet_nPEsfx = prove
 (`!rest. firstSet cmlG (CONS (grammar_NT (INL nPEsfx)) rest) =
          BarT INSERT HandleT INSERT firstSet cmlG rest`,
  PARSE2AUX_FS_TAC);;
let _ = cake_add_simps [firstSet_nPEsfx];;

let NOTIN_firstSet_nV = prove
 (`!s i c w.
     ~(CommaT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(LparT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(RparT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(UnderbarT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(BarT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(OpT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(FnT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(IfT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(EqualsT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(DarrowT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(ValT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(ExceptionT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(EndT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(AndT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(FFIT s IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(FunT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(LbrackT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(LocalT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(RbrackT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(InT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(tokens_IntT i IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(StringT s IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(tokens_CharT c IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(ThenT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(ElseT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(CaseT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(LetT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(OfT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(RaiseT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(DatatypeT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(TypeT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(SemicolonT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(ColonT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(StructureT IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(tokens_WordT w IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(SymbolT (implode "::") IN firstSet cmlG [grammar_NT (INL nV)]) /\
     ~(HandleT IN firstSet cmlG [grammar_NT (INL nV)])`,
  PARSE2AUX_NOTIN_TAC [firstSet_nV] THEN CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[explode_implode; validPrefixSym_def] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[isPREFIX_THM] THEN CONV_TAC(DEPTH_CONV CHAR_EQ_CONV) THEN
  REWRITE_TAC[]);;
let _ = cake_add_simps [NOTIN_firstSet_nV];;

let NOTIN_firstSet_nFQV = prove
 (`!s i c w.
     ~(AndT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(BarT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(CaseT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(tokens_CharT c IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(ColonT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(CommaT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(DarrowT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(DatatypeT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(ElseT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(EndT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(EqualsT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(ExceptionT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(FFIT s IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(FnT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(FunT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(IfT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(InT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(tokens_IntT i IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(LbrackT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(LetT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(LocalT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(LparT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(OfT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(OpT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(RaiseT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(RbrackT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(RparT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(SemicolonT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(StringT s IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(StructureT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(ThenT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(TypeT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(UnderbarT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(ValT IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(tokens_WordT w IN firstSet cmlG [grammar_NT (INL nFQV)]) /\
     ~(HandleT IN firstSet cmlG [grammar_NT (INL nV)])`,
  PARSE2AUX_NOTIN_TAC [firstSet_nFQV; firstSet_nV]);;
let _ = cake_add_simps [NOTIN_firstSet_nFQV];;

let NOTIN_firstSet_nConstructorName = prove
 (`!s i c w.
     ~(AndT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(BarT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(ColonT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(CaseT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(tokens_CharT c IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(CommaT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(DarrowT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(DatatypeT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(ElseT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(EndT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(EqualsT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(ExceptionT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(FFIT s IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(FnT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(FunT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(IfT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(InT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(tokens_IntT i IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(LbrackT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(LetT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(LocalT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(LparT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(OfT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(OpT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(RaiseT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(RbrackT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(RparT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(SemicolonT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(StringT s IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(StructureT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(SymbolT (implode "::") IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(SymbolT (implode "ref") IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(ThenT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(TypeT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(UnderbarT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(ValT IN firstSet cmlG [grammar_NT (INL nConstructorName)]) /\
     ~(tokens_WordT w IN firstSet cmlG [grammar_NT (INL nConstructorName)])`,
  PARSE2AUX_NOTIN_TAC [firstSet_nConstructorName]);;
let _ = cake_add_simps [NOTIN_firstSet_nConstructorName];;

let firstSets_nV_nConstructorName = prove
 (`!t. ~(t IN firstSet cmlG [grammar_NT (INL nConstructorName)] /\
         t IN firstSet cmlG [grammar_NT (INL nV)])`,
  GEN_TAC THEN ASM_CASES_TAC `t IN firstSet cmlG [grammar_NT (INL nV)]` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[firstSet_nV]) THEN
  REWRITE_TAC[firstSet_nConstructorName; IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN ASM_MESON_TAC[]);;
