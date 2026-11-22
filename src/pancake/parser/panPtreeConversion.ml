(* ========================================================================= *)
(* panPtreeConversion: port of HOL4                                          *)
(* pancake/parser/panPtreeConversionScript.sml (CakeML v3479).               *)
(* Translating the Pancake parse tree into the Pancake AST (with some        *)
(* inspiration from CakeML's cmlPtreeConversion; Craig McLaughlin, 2022).    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's option monad syntax is written out: do x <- m; r od is           *)
(*   OPTION_BIND m (\x. r), the paired bind do (a,b) <- m; r od is           *)
(*   OPTION_BIND m (\p. match p with (a,b) -> r), m1 ++ m2 is OPTION_CHOICE  *)
(*   m1 m2; the local overloads: lift is OPTION_MAP, lift2 is OPTION_MAP2,   *)
(*   f ' x is OPTION_BIND x f, ptree_size is parsetree_size (\x. 0) (\x. 0)  *)
(*   (\x. 0) (written out), ptree1_size is parsetree_size_aux1.  i2w is     *)
(*   iword, Num is num_of_int (on n >= 0), n2w is word, EXISTS is EX, FOLDR  *)
(*   f e l is ITLIST f l e, () is one, toString on num is num_to_str, ^ is   *)
(*   strcat, concat is mlstring_concat, an mlstring literal is implode of a  *)
(*   string literal, a record literal of fun_decl is fun_decl_REC, fi with   *)
(*   body := b is fun_decl_body_fupd (K b) fi.                               *)
(* - Names (names.tsv): destLf, destTOK and tokcheck have the prefix          *)
(*   panPtreeConversion_ (tokenUtils and cmlPtreeConversion have them); the  *)
(*   constructors of panLang, asm and panLexer are as there (panLang_Const,  *)
(*   asm_Add, NotEqual, panLexer_IntT, ...).                                 *)
(* - conv_Exp_def is one mutual definition of the seven functions, as in     *)
(*   HOL4; its clauses use the argument names tree, ts and res throughout   *)
(*   (HOL4 also has leaf and e).  Paired lambdas of HOL4 inside recursive    *)
(*   definitions (localise_exp, localise_prog) are \p. match p with (a,b) -> *)
(*   .. (pair_CASE), so that the recursive calls get the pattern as context. *)
(* - DEVIATION: butlast_tl has the hypothesis 2 <= LENGTH xs (HOL Light      *)
(*   leaves TL [] unspecified; HOL4's TL [] = [] makes it hold for all xs).  *)
(* - Helpers that are not HOL4 names have the prefix PPARSEAUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mlmap.ml";;
needs "pancake/panLang.ml";;
needs "pancake/parser/panLexer.ml";;
needs "pancake/parser/panPEG.ml";;

type_invention_error := true;;

(* Copied from tokenUtils: prevent a conflict between panLexer's token and  *)
(* CakeML's token (HOL4 [simp])                                             *)

let panPtreeConversion_destLf_def = cake_def
  `(panPtreeConversion_destLf (Lf (x,_)) = SOME (x:(A,B)symbol)) /\
   (panPtreeConversion_destLf (Nd _ _:(A,B,C)parsetree) = NONE)`;;
let _ = cake_add_simps [panPtreeConversion_destLf_def];;

let panPtreeConversion_destTOK_def = cake_def
  `(panPtreeConversion_destTOK (TOK t:(A,B)symbol) = SOME t) /\
   (panPtreeConversion_destTOK (NT _:(A,B)symbol) = NONE)`;;
let _ = cake_add_simps [panPtreeConversion_destTOK_def];;

(* Copied from cmlPtreeConversion *)

let panPtreeConversion_tokcheck_def = cake_def
  `panPtreeConversion_tokcheck (pt:(A,B,C)parsetree) (expected:A) =
     match OPTION_BIND (panPtreeConversion_destLf pt)
                       panPtreeConversion_destTOK with
       SOME actual -> actual = expected
     | NONE -> F`;;

let dest_annot_tok_def = cake_def
  `dest_annot_tok (pt:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf pt)
                       panPtreeConversion_destTOK with
       SOME (AnnotCommentT c) -> SOME c
     | _ -> NONE`;;

let kw_def = cake_def
  `kw k = KeywordT k`;;

let isNT_def = cake_def
  `isNT (nodeNT:(B+num)#C) (ntm:B) <=> FST nodeNT = INL ntm`;;

let argsNT_def = cake_def
  `(argsNT (Lf _:(A,B,C)parsetree) (_:B) = NONE) /\
   (argsNT (Nd nodeNT args) ntm =
      if FST nodeNT = INL ntm then SOME args else NONE)`;;

let is_add_with_carry_def = cake_def
  `is_add_with_carry s <=> s = implode "__add_with_carry__"`;;

let conv_int_def = cake_def
  `conv_int (tree:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf tree)
                       panPtreeConversion_destTOK with
       SOME (panLexer_IntT n) -> SOME n
     | _ -> NONE`;;

let conv_nat_def = cake_def
  `conv_nat (tree:(panLexer_token,B,C)parsetree) =
     match conv_int tree with
       SOME n -> if n >= &0 then SOME (num_of_int n) else NONE
     | _ -> NONE`;;

let conv_const_def = cake_def
  `conv_const (t:(panLexer_token,B,C)parsetree) =
     OPTION_MAP (panLang_Const o iword) (conv_int t):((A)panLang_exp)option`;;

let conv_ident_def = cake_def
  `conv_ident (tree:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf tree)
                       panPtreeConversion_destTOK with
       SOME (IdentT s) -> SOME (implode s)
     | _ -> NONE`;;

let conv_ffi_ident_def = cake_def
  `conv_ffi_ident (tree:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf tree)
                       panPtreeConversion_destTOK with
       SOME (ForeignIdent s) -> SOME (implode s)
     | _ -> NONE`;;

let conv_var_def = cake_def
  `conv_var (t:(panLexer_token,B,C)parsetree) =
     OPTION_MAP (panLang_Var panLang_Global) (conv_ident t)
       :((A)panLang_exp)option`;;

(* Collection of binop expression nodes, n >= 2 *)

let binaryExps_def = cake_def
  `binaryExps = [EOrNT; EXorNT; EAndNT; EAddNT]`;;

let panExps_def = cake_def
  `panExps = [EMulNT]`;;

(* Subtraction must apply to only two subexpressions (see panSem). *)

let isSubOp_def = cake_def
  `(isSubOp (panLang_Op asm_Sub [e1;e2]:(A)panLang_exp) <=> T) /\
   (isSubOp (_:(A)panLang_exp) <=> F)`;;

(* The size of a parse tree, the measure of the recursive conversions        *)
(* (HOL4 local overload ptree_size = parsetree_size (K 0) (K 0) (K 0)); the  *)
(* terms below are written with it unfolded                                  *)

(* Convert a binary operator into its AST representation. *)

let conv_binop_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,C)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:C. 0) t)`
  TERM_TAC
  `(conv_binop (Nd nodeNT args:(panLexer_token,pancakeNT,C)parsetree) =
      if isNT nodeNT AddOpsNT then
        match args with
          [leaf] -> conv_binop leaf
        | _ -> NONE
      else NONE) /\
   (conv_binop leaf =
      if panPtreeConversion_tokcheck leaf PlusT then SOME asm_Add
      else if panPtreeConversion_tokcheck leaf MinusT then SOME asm_Sub
      else if panPtreeConversion_tokcheck leaf panLexer_AndT then SOME asm_And
      else if panPtreeConversion_tokcheck leaf OrT then SOME asm_Or
      else if panPtreeConversion_tokcheck leaf XorT then SOME asm_Xor
      else NONE)`;;

let conv_panop_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,C)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:C. 0) t)`
  TERM_TAC
  `(conv_panop (Nd nodeNT args:(panLexer_token,pancakeNT,C)parsetree) =
      if isNT nodeNT MulOpsNT then
        match args with
          [leaf] -> conv_panop leaf
        | _ -> NONE
      else NONE) /\
   (conv_panop leaf =
      if panPtreeConversion_tokcheck leaf panLexer_StarT then SOME panLang_Mul
      else NONE)`;;

let conv_shift_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,C)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:C. 0) t)`
  TERM_TAC
  `(conv_shift (Nd nodeNT args:(panLexer_token,pancakeNT,C)parsetree) =
      if isNT nodeNT ShiftOpsNT then
        match args with
          [leaf] -> conv_shift leaf
        | _ -> NONE
      else NONE) /\
   (conv_shift leaf =
      if panPtreeConversion_tokcheck leaf LslT then SOME Lsl
      else if panPtreeConversion_tokcheck leaf LsrT then SOME Lsr
      else if panPtreeConversion_tokcheck leaf AsrT then SOME Asr
      else if panPtreeConversion_tokcheck leaf RorT then SOME Ror
      else NONE)`;;

let conv_cmp_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,C)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:C. 0) t)`
  TERM_TAC
  `(conv_cmp (Nd nodeNT args:(panLexer_token,pancakeNT,C)parsetree) =
      if isNT nodeNT CmpOpsNT \/ isNT nodeNT EqOpsNT then
        match args with
          [leaf] -> conv_cmp leaf
        | _ -> NONE
      else NONE) /\
   (conv_cmp leaf =
      if panPtreeConversion_tokcheck leaf EqT then SOME (asm_Equal,F)
      else if panPtreeConversion_tokcheck leaf NeqT then SOME (NotEqual,F)
      else if panPtreeConversion_tokcheck leaf LessT then SOME (asm_Less,F)
      else if panPtreeConversion_tokcheck leaf GeqT then SOME (NotLess,F)
      else if panPtreeConversion_tokcheck leaf GreaterT then SOME (asm_Less,T)
      else if panPtreeConversion_tokcheck leaf LeqT then SOME (NotLess,T)
      else if panPtreeConversion_tokcheck leaf LowerT then SOME (Lower,F)
      else if panPtreeConversion_tokcheck leaf HigherT then SOME (Lower,T)
      else if panPtreeConversion_tokcheck leaf HigheqT then SOME (NotLower,F)
      else if panPtreeConversion_tokcheck leaf LoweqT then SOME (NotLower,T)
      else NONE)`;;

let conv_default_shape_def = cake_def
  `conv_default_shape (tree:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf tree)
                       panPtreeConversion_destTOK with
       SOME DefaultShT -> SOME One
     | _ -> NONE`;;

(* the children that argsNT returns are smaller than the tree (for the       *)
(* termination proofs; HOL4: Cases_on tree, argsNT_def and MEM_list_size)    *)

let PPARSEAUX_argsNT_size = prove
 (`!(t:(A,B,C)parsetree) n ts y fa fb fc.
     argsNT t n = SOME ts /\ MEM y ts
     ==> parsetree_size fa fb fc y < parsetree_size fa fb fc t`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `t:(A,B,C)parsetree` parsetree_nchotomy) THEN
  REWRITE_TAC[argsNT_def; option_DISTINCT] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC(parsetree_size_def :: size_aux_eqs "parsetree") THEN
  FIRST_ASSUM(MP_TAC o SPEC `parsetree_size (fa:A->num) (fb:B->num) (fc:C->num)` o
              MATCH_MP MEM_LIST_SIZE) THEN ARITH_TAC);;

let PPARSEAUX_ARGS_TERM_TAC =
  REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[PPARSEAUX_argsNT_size];;

(* A single tree is smaller than the forest. *)

let conv_Shape_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,C)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:C. 0) t)`
  PPARSEAUX_ARGS_TERM_TAC
  `conv_Shape (tree:(panLexer_token,pancakeNT,C)parsetree) =
     match conv_default_shape tree with
       SOME s -> SOME s
     | _ ->
       (match conv_int tree with
          SOME n ->
            if n < &1 then NONE
            else if n = &1 then SOME One
            else SOME (Comb (REPLICATE (num_of_int n) One))
        | NONE ->
            (match conv_ident tree with
               SOME id -> SOME (Named id)
             | NONE ->
                 (match argsNT tree ShapeCombNT with
                    SOME ts -> OPTION_MAP Comb (OPT_MMAP conv_Shape ts)
                  | _ -> NONE)))`;;

let conv_Shape_ind = cake_ind "conv_Shape";;

let conv_params_def = cake_def
  `conv_params (as:((panLexer_token,pancakeNT,C)parsetree)list) =
     match as with
       CONS s (CONS t ps) ->
         (match conv_Shape s with
            SOME sh ->
              (match conv_ident t with
                 SOME v -> OPTION_MAP (CONS (v,sh)) (conv_params ps)
               | _ -> NONE)
          | _ -> NONE)
     | [] -> SOME []
     | _ -> NONE`;;

(* The measure of the mutual definition below (HOL4's): the size of the     *)
(* tree for conv_ArgList, conv_FieldList, conv_Field and conv_Exp, the size  *)
(* of the list of trees for conv_binaryExps, conv_panops and conv_shifts,    *)
(* on the sum of their argument types (cake_def_wf's encoding)               *)

let PPARSEAUX_tree_size =
  `parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0) (\x:C. 0)`;;

let PPARSEAUX_measure (tys:hol_type list) =
  let arg_size ty =
    let v = mk_var("a",ty) in
    if fst(dest_type ty) = "prod" then
      mk_abs(v,list_mk_icomb "list_size"
                 [PPARSEAUX_tree_size; mk_icomb(mk_const("FST",[]),v)])
    else mk_abs(v,mk_comb(PPARSEAUX_tree_size,v)) in
  let rec combine tys =
    match tys with
      [ty] -> arg_size ty
    | ty::rest ->
        let g = combine rest in
        let sty = mk_type("sum",[ty; fst(dest_fun_ty(type_of g))]) in
        let s = mk_var("s",sty) in
        mk_abs(s,list_mk_icomb "sum_CASE" [s; arg_size ty; g])
    | [] -> failwith "PPARSEAUX_measure" in
  mk_icomb(mk_const("measure",[]),combine tys);;

(* termination: TERM_TAC, after substituting the equations of the context  *)
(* if needed; for a call on a child given by argsNT, the size lemma         *)

let PPARSEAUX_argsNT_size2 = prove
 (`!(t:(A,B,C)parsetree) n ts.
     argsNT t n = SOME ts
     ==> !y fa fb fc. MEM y ts
                      ==> parsetree_size fa fb fc y < parsetree_size fa fb fc t`,
  MESON_TAC[PPARSEAUX_argsNT_size]);;

let PPARSEAUX_size_MEM_Nd = prove
 (`!(p:(B+num)#C) (l:((A,B,C)parsetree)list) y fa fb fc.
     MEM y l ==> parsetree_size fa fb fc y < parsetree_size fa fb fc (Nd p l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `parsetree_size (fa:A->num) (fb:B->num) (fc:C->num)` o
              MATCH_MP MEM_LIST_SIZE) THEN
  REWRITE_TAC(parsetree_size_def :: size_aux_eqs "parsetree") THEN ARITH_TAC);;

let PPARSEAUX_EXP_TERM_TAC =
  TERM_TAC ORELSE
  (REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN TERM_TAC) ORELSE
  (REWRITE_TAC[measure_THM; case_def "sum"] THEN REPEAT STRIP_TAC THEN
   REPEAT VAR_EQ_TAC THEN
   (FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP PPARSEAUX_size_MEM_Nd) ORELSE
    (FIRST_X_ASSUM(MP_TAC o MATCH_MP PPARSEAUX_argsNT_size2) THEN
     ASM_MESON_TAC[MEM])));;

(* Convert an expression parse tree into the corresponding AST.  The        *)
(* definition is slightly complicated by the requirement that subtraction   *)
(* must have exactly two children; all the other binop operations can have  *)
(* two or more arguments (see panSem).  The clauses use the argument names   *)
(* tree, ts and res throughout (HOL4: leaf, e): the recursion package works  *)
(* on the tuple of all the argument variables of a mutual definition.       *)

let conv_Exp_def = cake_def_wf
  (PPARSEAUX_measure
     (let pt = `:(panLexer_token,pancakeNT,C)parsetree` in
      let pl = `:((panLexer_token,pancakeNT,C)parsetree)list#(A)panLang_exp` in
      [pt; pt; pt; pt; pl; pl; pl]))
  PPARSEAUX_EXP_TERM_TAC
  `(conv_ArgList (tree:(panLexer_token,pancakeNT,C)parsetree) =
      if panPtreeConversion_tokcheck tree NotT then SOME []
      else
        match argsNT tree ArgListNT with
          SOME (CONS t ts) -> OPT_MMAP conv_Exp (CONS t ts)
        | _ -> NONE) /\
   (conv_FieldList tree =
      match argsNT tree NmdFieldListNT with
        SOME (CONS t ts) -> OPT_MMAP conv_Field (CONS t ts)
      | _ -> NONE) /\
   (conv_Field tree =
      match argsNT tree NmdFieldNT with
        SOME [t1;t2] -> OPTION_BIND (conv_ident t1) (\fld.
                          OPTION_BIND (conv_Exp t2) (\exp.
                            SOME (fld,exp)))
      | _ -> NONE) /\
   (conv_Exp (Nd nodeNT args) =
      if isNT nodeNT EFieldNT then
        (match args with
           [] -> NONE
         | [t] -> conv_Exp t
         | CONS t ts ->
             FOLDL (\e t. match conv_nat t with
                            SOME n -> OPTION_MAP2 RField (SOME n) e
                          | NONE -> (match conv_ident t with
                                       SOME i -> OPTION_MAP2 NField (SOME i) e
                                     | NONE -> NONE))
                   (conv_Exp t) ts)
      else if isNT nodeNT RawStructNT then
        (match args with
           [ts] -> OPTION_BIND (conv_ArgList ts) (\es. SOME (RStruct es))
         | _ -> NONE)
      else if isNT nodeNT NmdStructNT then
        (match args with
           [t1;t2] -> OPTION_BIND (conv_ident t1) (\nm.
                        OPTION_BIND (conv_FieldList t2) (\flds.
                          SOME (NStruct nm flds)))
         | _ -> NONE)
      else if isNT nodeNT ENotNT then
        (match args with
           [t] -> conv_Exp t
         | [_; t] -> OPTION_MAP (Cmp asm_Equal (panLang_Const (word 0)))
                                (conv_Exp t)
         | _ -> NONE)
      else if isNT nodeNT ELoadByteNT then
        (match args with
           [t] -> OPTION_MAP LoadByte (conv_Exp t)
         | _ -> NONE)
      else if isNT nodeNT ELoad32NT then
        (match args with
           [t] -> OPTION_MAP panLang_Load32 (conv_Exp t)
         | _ -> NONE)
      else if isNT nodeNT ELoadNT then
        (match args with
           [t1; t2] -> OPTION_BIND (conv_Shape t1) (\s.
                         OPTION_BIND (conv_Exp t2) (\e.
                           SOME (panLang_Load s e)))
         | _ -> NONE)
      else if isNT nodeNT ECmpNT \/ isNT nodeNT EEqNT then
        (match args with
           [e] -> conv_Exp e
         | [e1; op; e2] ->
             OPTION_BIND (conv_Exp e1) (\e1'.
             OPTION_BIND (conv_cmp op) (\p. match p with (op',b) ->
             OPTION_BIND (conv_Exp e2) (\e2'.
             SOME (if b then Cmp op' e2' e1' else Cmp op' e1' e2'))))
         | _ -> NONE)
      else if isNT nodeNT ExpNT then
        (match args with
           [e] -> conv_Exp e
         | CONS e1 args' ->
             OPTION_BIND (OPT_MMAP conv_Exp (CONS e1 args')) (\es.
               SOME (Cmp NotEqual (panLang_Const (word 0))
                         (panLang_Op asm_Or es)))
         | _ -> NONE)
      else if isNT nodeNT EBoolAndNT then
        (match args with
           [e] -> conv_Exp e
         | CONS e1 args' ->
             OPTION_BIND (OPT_MMAP conv_Exp (CONS e1 args')) (\es.
               SOME (panLang_Op asm_And
                       (MAP (\e. Cmp NotEqual (panLang_Const (word 0)) e) es)))
         | _ -> NONE)
      else if isNT nodeNT EShiftNT then
        (match args with
           CONS e es -> OPTION_BIND (conv_Exp e) (conv_shifts es)
         | _ -> NONE)
      else if EX (isNT nodeNT) binaryExps then
        (match args with
           [] -> NONE
         | CONS e es -> OPTION_BIND (conv_Exp e) (conv_binaryExps es))
      else if EX (isNT nodeNT) panExps then
        (match args with
           [] -> NONE
         | CONS e es -> OPTION_BIND (conv_Exp e) (conv_panops es))
      else NONE) /\
   (conv_Exp tree =
      if panPtreeConversion_tokcheck tree (kw BaseK) then SOME BaseAddr
      else if panPtreeConversion_tokcheck tree (kw TopK) then SOME TopAddr
      else if panPtreeConversion_tokcheck tree (kw BiwK) then SOME BytesInWord
      else if panPtreeConversion_tokcheck tree (kw TrueK)
      then SOME (panLang_Const (word 1))
      else if panPtreeConversion_tokcheck tree (kw FalseK)
      then SOME (panLang_Const (word 0))
      else OPTION_CHOICE (conv_const tree) (conv_var tree)
        :((A)panLang_exp)option) /\
   (conv_binaryExps [] res = SOME res) /\
   (conv_binaryExps (CONS t1 (CONS t2 ts)) res =
      OPTION_BIND (conv_binop t1) (\op.
      OPTION_BIND (conv_Exp t2) (\e.
        match res with
          panLang_Op bop es ->
            if ~(bop = op) \/ isSubOp res then
              conv_binaryExps ts (panLang_Op op [res; e])
            else conv_binaryExps ts (panLang_Op bop (APPEND es [e]))
        | e' -> conv_binaryExps ts (panLang_Op op [e'; e])))) /\
   (conv_binaryExps _ _ = NONE) /\
   (conv_panops [] res = SOME res) /\
   (conv_panops (CONS t1 (CONS t2 ts)) res =
      OPTION_BIND (conv_panop t1) (\op.
      OPTION_BIND (conv_Exp t2) (\e.
        match res with
          Panop bop es -> conv_panops ts (Panop op [res; e])
        | e' -> conv_panops ts (Panop op [e'; e])))) /\
   (conv_panops _ _ = NONE) /\
   (conv_shifts [] res = SOME res) /\
   (conv_shifts (CONS t1 (CONS t2 ts)) res =
      OPTION_BIND (conv_shift t1) (\op.
      OPTION_BIND (conv_Exp t2) (\e.
        conv_shifts ts (panLang_Shift op res e)))) /\
   (conv_shifts _ _ = NONE)`;;

let conv_Exp_ind = cake_ind "conv_Exp";;

(* Handles all statements which cannot contain Prog nodes as children. *)

let conv_NonRecStmt_def = cake_def
  `(conv_NonRecStmt (Nd nodeNT args:(panLexer_token,pancakeNT,C)parsetree) =
      if isNT nodeNT AssignNT then
        (match args with
           [dst; src] -> OPTION_MAP2 (panLang_Assign panLang_Global)
                                     (conv_ident dst) (conv_Exp src)
         | _ -> NONE)
      else if isNT nodeNT StoreNT then
        (match args with
           [dst; src] -> OPTION_MAP2 panLang_Store (conv_Exp dst) (conv_Exp src)
         | _ -> NONE)
      else if isNT nodeNT StoreByteNT then
        (match args with
           [dst; src] -> OPTION_MAP2 StoreByte (conv_Exp dst) (conv_Exp src)
         | _ -> NONE)
      else if isNT nodeNT Store32NT then
        (match args with
           [dst; src] -> OPTION_MAP2 panLang_Store32 (conv_Exp dst)
                                     (conv_Exp src)
         | _ -> NONE)
      else if isNT nodeNT SharedLoadNT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemLoad OpW panLang_Global)
                                 (conv_ident v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedLoadByteNT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemLoad Op8 panLang_Global)
                                 (conv_ident v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedLoad16NT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemLoad Op16 panLang_Global)
                                 (conv_ident v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedLoad32NT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemLoad Op32 panLang_Global)
                                 (conv_ident v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedStoreNT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemStore OpW) (conv_Exp v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedStoreByteNT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemStore Op8) (conv_Exp v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedStore16NT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemStore Op16) (conv_Exp v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT SharedStore32NT then
        (match args with
           [v; e] -> OPTION_MAP2 (ShMemStore Op32) (conv_Exp v) (conv_Exp e)
         | _ -> NONE)
      else if isNT nodeNT ExtCallNT then
        (match args with
           [name; ptr; clen; array; alen] ->
             OPTION_BIND (conv_ffi_ident name) (\name'.
             OPTION_BIND (conv_Exp ptr) (\ptr'.
             OPTION_BIND (conv_Exp clen) (\clen'.
             OPTION_BIND (conv_Exp array) (\array'.
             OPTION_BIND (conv_Exp alen) (\alen'.
               SOME (panLang_ExtCall name' ptr' clen' array' alen'))))))
         | _ -> NONE)
      else if isNT nodeNT ThrowNT then
        (match args with
           [id; e] -> OPTION_BIND (conv_ident id) (\eid.
                      OPTION_BIND (conv_Exp e) (\e'.
                        SOME (panLang_Raise eid e')))
         | _ -> NONE)
      else if isNT nodeNT ReturnNT then
        (match args with
           [e] -> OPTION_MAP panLang_Return (conv_Exp e)
         | _ -> NONE)
      else NONE) /\
   (conv_NonRecStmt leaf =
      if panPtreeConversion_tokcheck leaf (kw SkipK) then SOME panLang_Skip
      else if panPtreeConversion_tokcheck leaf (kw BrK) then SOME panLang_Break
      else if panPtreeConversion_tokcheck leaf (kw ContK)
      then SOME panLang_Continue
      else if panPtreeConversion_tokcheck leaf (kw TicK) then SOME panLang_Tick
      else (match dest_annot_tok leaf with
              SOME c -> SOME (Annot (implode "@") (implode c))
            | NONE -> NONE):((A)panLang_prog)option)`;;

let butlast_def = cake_def
  `(butlast [] = []:A list) /\
   (butlast (CONS (x:A) xs) = if xs = [] then [] else CONS x (butlast xs))`;;

let butlast_length = prove
 (`!xs:A list. LENGTH (butlast xs) = LENGTH xs - 1`,
  LIST_INDUCT_TAC THEN RW[butlast_def] THEN GVS[] THEN
  CASES_ON `t:A list` THEN GVS[LENGTH; NOT_CONS_NIL] THEN ARITH_TAC);;

(* HOL4 butlast_tl states butlast (TL xs) = TL (butlast xs) for every xs;   *)
(* with HOL Light's TL, which leaves TL [] unspecified, both sides are      *)
(* determined only for lists of two or more elements (DEVIATION)            *)

let butlast_tl = prove
 (`!xs:A list. 2 <= LENGTH xs ==> butlast (TL xs) = TL (butlast xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; TL] THEN
  CASES_ON `t:A list` THEN REWRITE_TAC[LENGTH; TL; butlast_def; NOT_CONS_NIL] THEN
  ARITH_TAC);;
let _ = cake_add_simps [butlast_tl];;

let butlast_append = prove
 (`!xs ys:A list.
     butlast (APPEND xs ys) = if ys = [] then butlast xs
                              else APPEND xs (butlast ys)`,
  LIST_INDUCT_TAC THEN RW[butlast_def; APPEND] THEN GVS[APPEND_EQ_NIL]);;
let _ = cake_add_simps [butlast_append];;

let list_size_butlast = prove
 (`!xs (f:A->num). list_size f (butlast xs) <= list_size f xs`,
  LIST_INDUCT_TAC THEN RW[butlast_def; list_size] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:A->num`) THEN ARITH_TAC);;

let list_size_MEM = prove
 (`!xs x (f:A->num). MEM x xs ==> f x <= list_size f xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `f:A->num`]) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let parsetree_locs_def = cake_def
  `parsetree_locs (tree:(A,B,locs)parsetree) =
     match tree with
       Nd (_,Locs p1 p2) _ -> (p1,p2)
     | Lf (_,Locs p1 p2) -> (p1,p2)`;;

let posn_string_def = cake_def
  `(posn_string (POSN lnum cnum) =
      strcat (strcat (num_to_str lnum) (implode ":")) (num_to_str cnum)) /\
   (posn_string EOFpt = implode "EOF") /\
   (posn_string UNKNOWNpt = implode "UNKNOWN")`;;

let locs_comment_def = cake_def
  `locs_comment (p1,p2) =
     mlstring_concat [implode "(";
                      posn_string p1;
                      implode " ";
                      posn_string p2;
                      implode ")"]`;;

let add_locs_annot_def = cake_def
  `add_locs_annot (ptree:(A,B,locs)parsetree) (prog:(W)panLang_prog) =
     panLang_Seq (Annot (implode "location") (locs_comment (parsetree_locs ptree)))
                 prog`;;

(* HOL4: Nd typed as a node of (token,pancakeNT,locs)parsetree *)

let conv_Dec_def = cake_def
  `(conv_Dec (Nd nodeNT args:(panLexer_token,pancakeNT,locs)parsetree) =
      if isNT nodeNT DecNT then
        (match args with
           [sh; id; e] ->
             OPTION_BIND (conv_Shape sh) (\sh.
             OPTION_BIND (conv_ident id) (\v.
             OPTION_BIND (conv_Exp e) (\e'.
               SOME (sh,v,e'))))
         | _ -> NONE)
      else NONE) /\
   (conv_Dec _ = NONE:(shape#mlstring#(A)panLang_exp)option)`;;

let conv_GlobalDec_def = cake_def
  `(conv_GlobalDec (Nd nodeNT args:(panLexer_token,pancakeNT,locs)parsetree) =
      if isNT nodeNT GlobalDecNT then
        (match args with
           [sh; id; e] ->
             OPTION_BIND (conv_Shape sh) (\sh.
             OPTION_BIND (conv_ident id) (\v.
             OPTION_BIND (conv_Exp e) (\e'.
               SOME (sh,v,e'))))
         | _ -> NONE)
      else NONE) /\
   (conv_GlobalDec _ = NONE:(shape#mlstring#(A)panLang_exp)option)`;;

let conv_ExnDec_def = cake_def
  `conv_ExnDec (tree:(panLexer_token,pancakeNT,C)parsetree) =
     match argsNT tree ExnDecNT with
       SOME [id; sh] ->
         OPTION_BIND (conv_ident id) (\eid.
         OPTION_BIND (conv_Shape sh) (\sh'.
           SOME (eid,sh')))
     | _ -> NONE`;;

let conv_DecCall_def = cake_def
  `(conv_DecCall (Nd nodeNT args:(panLexer_token,pancakeNT,locs)parsetree) =
      if isNT nodeNT DecCallNT then
        (match args with
           CONS s (CONS i (CONS e ts)) ->
             OPTION_BIND (conv_Shape s) (\s'.
             OPTION_BIND (conv_ident i) (\i'.
             OPTION_BIND (conv_ident e) (\e'.
             OPTION_BIND (match ts with
                            [] -> SOME []
                          | CONS args _ -> conv_ArgList args) (\args'.
               SOME (s',i',e',args':((A)panLang_exp)list)))))
         | _ -> NONE)
      else NONE) /\
   (conv_DecCall _ = NONE)`;;

let conv_Ret_def = cake_def
  `conv_Ret (tree:(panLexer_token,pancakeNT,C)parsetree) =
     if panPtreeConversion_tokcheck tree (kw RetK) then SOME NONE
     else if panPtreeConversion_tokcheck tree NotT then SOME (SOME NONE)
     else
       match argsNT tree RetNT with
         SOME [id] -> OPTION_BIND (conv_ident id) (\var.
                        SOME (SOME (SOME (panLang_Global,var))))
       | _ -> NONE`;;

(* sizes for the termination of conv_Prog (HOL4: MEM_list_size,            *)
(* list_size_butlast and list_size_MEM)                                     *)

let PPARSEAUX_MEM_butlast = prove
 (`!(xs:A list) x. MEM x (butlast xs) ==> MEM x xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[butlast_def; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let PPARSEAUX_size_MEM_butlast = prove
 (`!(p:(B+num)#C) (t:(A,B,C)parsetree) ts y fa fb fc.
     MEM y (CONS t (butlast ts))
     ==> parsetree_size fa fb fc y < parsetree_size fa fb fc (Nd p (CONS t ts))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PPARSEAUX_size_MEM_Nd THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MEM] THEN MESON_TAC[PPARSEAUX_MEM_butlast]);;

let PPARSEAUX_size_LAST = prove
 (`!(p:(B+num)#C) (t:(A,B,C)parsetree) ts fa fb fc.
     ~(ts = [])
     ==> parsetree_size fa fb fc (LAST ts) <
         parsetree_size fa fb fc (Nd p (CONS t ts))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PPARSEAUX_size_MEM_Nd THEN
  REWRITE_TAC[MEM] THEN DISJ2_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ts:((A,B,C)parsetree)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; MEM_LAST]);;

let PPARSEAUX_PROG_TERM_TAC =
  TERM_TAC ORELSE
  (REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN TERM_TAC) ORELSE
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
   (FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP PPARSEAUX_size_MEM_Nd) ORELSE
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP PPARSEAUX_size_MEM_butlast) ORELSE
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP PPARSEAUX_size_LAST)));;

let conv_Prog_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,locs)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:locs. 0) t)`
  PPARSEAUX_PROG_TERM_TAC
  `(conv_Prog (Nd nodeNT args:(panLexer_token,pancakeNT,locs)parsetree) =
      let nd = Nd nodeNT args in
      if isNT nodeNT DecNT then
        (match args with
           [d; p] -> OPTION_BIND (conv_Dec d) (\q. match q with (sh,v,e') ->
                       OPTION_BIND (conv_Prog p) (\p'.
                         SOME (add_locs_annot nd (Dec v sh e' p'))))
         | _ -> NONE)
      else if isNT nodeNT IfNT then
        (match args with
           [e; p1; p2] -> OPTION_BIND (conv_Exp e) (\e'.
                          OPTION_BIND (conv_Prog p1) (\p1'.
                          OPTION_BIND (conv_Prog p2) (\p2'.
                            SOME (add_locs_annot nd (panLang_If e' p1' p2')))))
         | _ -> NONE)
      else if isNT nodeNT WhileNT then
        (match args with
           [e; p] -> OPTION_BIND (conv_Exp e) (\e'.
                     OPTION_BIND (conv_Prog p) (\p'.
                       SOME (add_locs_annot nd (While e' p'))))
         | _ -> NONE)
      else if isNT nodeNT DecCallNT then
        (match args with
           [dec; p] ->
             OPTION_BIND (conv_DecCall dec) (\q. match q with (s',i',e',args') ->
             OPTION_BIND (conv_Prog p) (\p'.
               if is_add_with_carry e'
               then SOME (add_locs_annot nd
                           (Dec i' s' (shape_val s')
                              (panLang_Seq (Primitive i' panLang_AddCarry args')
                                           p')))
               else SOME (add_locs_annot nd (DecCall i' s' e' args' p'))))
         | _ -> NONE)
      else if isNT nodeNT HandleNT then
        (match args with
           [ret; f; ts; eid; id; p] ->
             OPTION_BIND (conv_Ret ret) (\r'.
             OPTION_BIND r' (\r''.
             OPTION_BIND (conv_ident f) (\fname.
             OPTION_BIND (conv_ArgList ts) (\args.
             OPTION_BIND (conv_ident eid) (\ename.
             OPTION_BIND (conv_ident id) (\evar.
             OPTION_BIND (conv_Prog p) (\prog.
               SOME (add_locs_annot nd
                      (panLang_Call (SOME (r'',SOME (ename,evar,prog)))
                                    fname args)))))))))
         | _ -> NONE)
      else if isNT nodeNT CallNT then
        (match args with
           [r;e;args] ->
             OPTION_BIND (conv_Ret r) (\r'.
             OPTION_BIND (conv_ident e) (\e'.
             OPTION_BIND (conv_ArgList args) (\args'.
               if is_add_with_carry e' then
                 (match r' with
                    SOME (SOME (_,vn)) ->
                      SOME (add_locs_annot nd
                             (Primitive vn panLang_AddCarry args'))
                  | _ -> NONE)
               else
                 SOME (add_locs_annot nd
                        (panLang_Call (OPTION_MAP (\x. (x,NONE)) r') e' args')))))
         | _ -> NONE)
      else if isNT nodeNT ProgNT then
        (match args with
           CONS t ts ->
             if ~(ts = [])
             then ITLIST (\t' p. OPTION_MAP2 panLang_Seq t' p)
                         (MAP conv_Prog (CONS t (butlast ts)))
                         (conv_Prog (LAST ts))
             else conv_Prog t
         | _ -> NONE)
      else OPTION_MAP (add_locs_annot nd) (conv_NonRecStmt (Nd nodeNT args))) /\
   (conv_Prog leaf =
      OPTION_MAP (add_locs_annot leaf) (conv_NonRecStmt leaf)
        :((A)panLang_prog)option)`;;

let conv_Prog_ind = cake_ind "conv_Prog";;

let conv_inline_def = cake_def
  `conv_inline (tree:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf tree)
                       panPtreeConversion_destTOK with
       SOME (KeywordT InlineK) -> SOME T
     | SOME NoinlineT -> SOME F
     | _ -> NONE`;;

let conv_export_def = cake_def
  `conv_export (tree:(panLexer_token,B,C)parsetree) =
     match OPTION_BIND (panPtreeConversion_destLf tree)
                       panPtreeConversion_destTOK with
       SOME (KeywordT ExportK) -> SOME T
     | SOME StaticT -> SOME F
     | _ -> NONE`;;

let conv_FieldNameList_def = cake_def
  `conv_FieldNameList (tree:(panLexer_token,pancakeNT,C)parsetree) =
     match argsNT tree FieldNameListNT with
       SOME args -> conv_params args
     | _ -> NONE`;;

let conv_StructName_def = cake_def
  `(conv_StructName (Nd nodeNT args:(panLexer_token,pancakeNT,locs)parsetree) =
      if isNT nodeNT StructNameNT then
        (match args with
           [id; flds] ->
             OPTION_BIND (conv_ident id) (\nm.
             OPTION_BIND (conv_FieldNameList flds) (\flds'.
               SOME (nm,flds')))
         | _ -> NONE)
      else NONE) /\
   (conv_StructName _ = NONE)`;;

let conv_TopDec_def = cake_def
  `conv_TopDec (tree:(panLexer_token,pancakeNT,locs)parsetree) =
     match argsNT tree FunNT with
       SOME [i;e;sh;n;ps;c] ->
         (match argsNT ps ParamListNT with
            SOME args ->
              OPTION_BIND (conv_params args) (\ps'.
              OPTION_BIND (conv_Prog c) (\body.
              OPTION_BIND (conv_ident n) (\n'.
              OPTION_BIND (conv_inline i) (\i'.
              OPTION_BIND (conv_export e) (\e'.
              OPTION_BIND (conv_Shape sh) (\sh'.
                SOME (Function (fun_decl_REC n' i' e' ps' body sh'))))))))
          | _ -> NONE)
     | _ ->
         (match conv_GlobalDec tree with
            SOME (sh,v,e) -> SOME (Decl sh v e)
          | _ -> (match conv_StructName tree with
                    SOME (nm,flds) -> SOME (Name nm flds)
                  | _ ->
                      (match conv_ExnDec tree with
                         SOME (eid,sh) -> SOME (ExnDecl eid sh)
                       | NONE -> NONE)))
       :((A)decl)option`;;

let conv_TopDecList_def = cake_def_wf
  `measure (\t:(panLexer_token,pancakeNT,locs)parsetree.
              parsetree_size (\x:panLexer_token. 0) (\x:pancakeNT. 0)
                             (\x:locs. 0) t)`
  PPARSEAUX_EXP_TERM_TAC
  `conv_TopDecList (tree:(panLexer_token,pancakeNT,locs)parsetree) =
     match argsNT tree TopDecListNT with
       SOME [] -> SOME []
     | SOME [f; tree'] ->
         (match dest_annot_tok f with
            NONE ->
              (match conv_TopDec f with
                 SOME f ->
                   (match conv_TopDecList tree' with
                      NONE -> NONE
                    | SOME fs -> SOME (CONS f fs))
               | NONE -> NONE)
          | SOME _ -> conv_TopDecList tree')
     | _ -> NONE:(((A)decl)list)option`;;

let conv_TopDecList_ind = cake_ind "conv_TopDecList";;

let parse_to_ast_def = cake_def
  `parse_to_ast s =
     match parse_statement (pancake_lex s) with
       SOME e -> conv_Prog e
     | _ -> NONE:((A)panLang_prog)option`;;


let collect_globals_def = cake_def
  `(collect_globals [] = mlmap_empty mlstring_compare:(mlstring,1)map) /\
   (collect_globals (CONS (d:(A)decl) ds) =
      match d with
        Decl _ v _ -> mlmap_insert (collect_globals ds) v one
      | _ -> collect_globals ds)`;;

(* the catch-all clause also leaves Load32 unchanged, as in HOL4 *)

let localise_exp_def = cake_def_wf
  `measure (\s:((mlstring,1)map#(A)panLang_exp)+
               ((mlstring,1)map#((A)panLang_exp)list).
     sum_CASE s (\p. panLang_exp_size (\x:A. 0) (SND p))
                (\p. list_size (panLang_exp_size (\x:A. 0)) (SND p)))`
  TERM_TAC
  `(localise_exp (ls:(mlstring,1)map) (panLang_Var varkind varname:(A)panLang_exp) =
      match mlmap_lookup ls varname with
        NONE -> panLang_Var varkind varname
      | SOME _ -> panLang_Var panLang_Local varname) /\
   (localise_exp ls (RStruct exps) = RStruct (localise_exps ls exps)) /\
   (localise_exp ls (RField index exp) = RField index (localise_exp ls exp)) /\
   (localise_exp ls (NStruct nm flds) =
      NStruct nm (MAP (\p. match p with (fld,e) -> (fld,localise_exp ls e)) flds)) /\
   (localise_exp ls (NField fld exp) = NField fld (localise_exp ls exp)) /\
   (localise_exp ls (panLang_Load shape exp) =
      panLang_Load shape (localise_exp ls exp)) /\
   (localise_exp ls (LoadByte exp) = LoadByte (localise_exp ls exp)) /\
   (localise_exp ls (panLang_Op binop exps) =
      panLang_Op binop (localise_exps ls exps)) /\
   (localise_exp ls (Panop panop exps) = Panop panop (localise_exps ls exps)) /\
   (localise_exp ls (Cmp cmp exp1 exp2) =
      Cmp cmp (localise_exp ls exp1) (localise_exp ls exp2)) /\
   (localise_exp ls (panLang_Shift shift exp1 exp2) =
      panLang_Shift shift (localise_exp ls exp1) (localise_exp ls exp2)) /\
   (localise_exp ls e = e) /\
   (localise_exps ls [] = []) /\
   (localise_exps ls (CONS e es) = CONS (localise_exp ls e) (localise_exps ls es))`;;

let localise_exp_ind = cake_ind "localise_exp";;

(* HOL4 writes the lambdas of the Call clause as paired lambdas; here they  *)
(* are \p. match p with (x,y) -> .. (pair_CASE), so that the recursive call *)
(* gets the context of the pattern; the catch-all clause also leaves Store32 *)
(* unchanged, as in HOL4                                                     *)

let localise_prog_def = cake_def_wf
  `measure (\p:(mlstring,1)map#(A)panLang_prog.
              panLang_prog_size (\x:A. 0) (SND p))`
  TERM_TAC
  `(localise_prog (ls:(mlstring,1)map)
                  (Dec varname shape exp prog:(A)panLang_prog) =
      Dec varname shape
          (localise_exp ls exp)
          (localise_prog (mlmap_insert ls varname one) prog)) /\
   (localise_prog ls (panLang_Assign varkind varname exp) =
      panLang_Assign (match mlmap_lookup ls varname with
                        NONE -> varkind
                      | SOME _ -> panLang_Local)
                     varname (localise_exp ls exp)) /\
   (localise_prog ls (Primitive varname pop exps) =
      Primitive varname pop (MAP (localise_exp ls) exps)) /\
   (localise_prog ls (panLang_Store exp1 exp2) =
      panLang_Store (localise_exp ls exp1)
                    (localise_exp ls exp2)) /\
   (localise_prog ls (StoreByte exp1 exp2) =
      StoreByte (localise_exp ls exp1)
                (localise_exp ls exp2)) /\
   (localise_prog ls (panLang_Seq prog1 prog2) =
      panLang_Seq (localise_prog ls prog1)
                  (localise_prog ls prog2)) /\
   (localise_prog ls (panLang_If exp prog1 prog2) =
      panLang_If (localise_exp ls exp)
                 (localise_prog ls prog1)
                 (localise_prog ls prog2)) /\
   (localise_prog ls (While exp prog) =
      While (localise_exp ls exp)
            (localise_prog ls prog)) /\
   (localise_prog ls (panLang_Call call name exps) =
      panLang_Call
        (OPTION_MAP
           (\q. match q with
                  (x,y) ->
                    (OPTION_MAP (\r. match r with
                                       (varkind,varname) ->
                                         ((match mlmap_lookup ls varname with
                                             NONE -> varkind
                                           | SOME _ -> panLang_Local),
                                          varname)) x,
                     OPTION_MAP (\h. match h with
                                       (x,y,z) ->
                                         (x,y,localise_prog
                                                (mlmap_insert ls y one) z)) y))
           call)
        name
        (MAP (localise_exp ls) exps)) /\
   (localise_prog ls (DecCall varname shape fname exps prog) =
      DecCall varname shape
              fname
              (MAP (localise_exp ls) exps)
              (localise_prog (mlmap_insert ls varname one) prog)) /\
   (localise_prog ls (panLang_ExtCall funname exp1 exp2 exp3 exp4) =
      panLang_ExtCall funname
                      (localise_exp ls exp1) (localise_exp ls exp2)
                      (localise_exp ls exp3) (localise_exp ls exp4)) /\
   (localise_prog ls (panLang_Raise eid exp) =
      panLang_Raise eid (localise_exp ls exp)) /\
   (localise_prog ls (panLang_Return exp) =
      panLang_Return (localise_exp ls exp)) /\
   (localise_prog ls (ShMemLoad opsize varkind varname exp) =
      ShMemLoad opsize
                (match mlmap_lookup ls varname with
                   NONE -> varkind
                 | SOME _ -> panLang_Local)
                varname
                (localise_exp ls exp)) /\
   (localise_prog ls (ShMemStore opsize exp1 exp2) =
      ShMemStore opsize (localise_exp ls exp1) (localise_exp ls exp2)) /\
   (localise_prog ls p = p)`;;

let localise_prog_ind = cake_ind "localise_prog";;

let localise_topdec_def = cake_def
  `(localise_topdec (ls:(mlstring,1)map) (Decl sh v e:(A)decl) = Decl sh v e) /\
   (localise_topdec ls (Name nm fld) = Name nm fld) /\
   (localise_topdec ls (ExnDecl nm sh) = ExnDecl nm sh) /\
   (localise_topdec ls (Function fi) =
      Function (fun_decl_body_fupd
                  (K (localise_prog
                        (FOLDL (\m p. mlmap_insert m p one) ls
                               (MAP FST (fun_decl_params fi)))
                        (fun_decl_body fi))) fi))`;;

let localise_topdecs_def = cake_def
  `localise_topdecs (decs:((A)decl)list) =
     MAP (localise_topdec (mlmap_empty mlstring_compare)) decs`;;

let parse_topdecs_to_ast_def = cake_def
  `parse_topdecs_to_ast s =
     match safe_pancake_lex s with
       INL toks ->
         (match panPEG_parse toks with
            INL e ->
              (match conv_TopDecList e with
                 SOME funs -> INL (localise_topdecs funs)
               | NONE -> INR [(implode "Parse tree conversion failed",
                               unknown_loc)])
          | INR err -> INR err)
     | INR err -> INR err:(((A)decl)list)+((mlstring#locs)list)`;;

