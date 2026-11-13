(* ========================================================================= *)
(* cmlPtreeConversion: port of HOL4 semantics/cmlPtreeConversionScript.sml   *)
(* (CakeML v3479).                                                           *)
(* Specification of how to convert parse trees to abstract syntax.          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's option monad syntax is written out: do x <- m; r od is           *)
(*   OPTION_BIND m (\x. r), do m; r od is OPTION_IGNORE_BIND m r, assert is  *)
(*   OPTION_GUARD, return is SOME, fail is NONE, m1 ++ m2 is OPTION_CHOICE   *)
(*   m1 m2 (left associative); the paired bind do (a,b) <- m; r od is         *)
(*   OPTION_BIND m (\p. match p with (a,b) -> r).  The local overloads:      *)
(*   lift is OPTION_MAP, lift2 is OPTION_MAP2, f ' x is OPTION_BIND x f;     *)
(*   mkNT is INL; SINGL is (\x. [x]); FOLDR f e l is ITLIST f l e; an        *)
(*   mlstring literal is implode of a string literal; () is one; n2w is word.*)
(* - HOL4's type abbreviation M (a monad on PCstate0 lists, with a type      *)
(*   parameter) is written out: a HOL Light abbreviation takes no parameter  *)
(*   and a type :M would capture the type variable M of every later file.    *)
(*   The local abbreviation ptree is mlptree.                                *)
(* - The variables nt, tok and seq of HOL4 are the constants nt, tok and seq *)
(*   (pegsym constructors) here: they are nt', tok' and seq'; the variable   *)
(*   pnt of ptree_Expr is patnt (pnt is a constant of cmlPEG, which may be   *)
(*   loaded before this file).                                               *)
(* - As in HOL4, the functions that do not use the locations of the parse    *)
(*   tree (ptree_UQTyop, ptree_Type, ptree_Pattern, ...) are polymorphic in  *)
(*   the location type (C); ptree_Op and singleSymP also in the module name *)
(*   type of the identifier they return (D).                                 *)
(* - maybe_handleRef: HOL4 matches the string literal <<Ref>> in a pattern   *)
(*   (TFL with the classic heuristic); here it is the equivalent test.       *)
(* - Not ported: the computeLib theorems ptree_Pattern_pevaled and           *)
(*   ptree_Expr_pevaled (made by ML partial evaluation) and the local        *)
(*   ptree_Expr_def' from which the latter is computed.                      *)
(* - Names (notes/naming/names.tsv): Papply_def and Eseq_encode_def are       *)
(*   cmlPtreeConversion_Papply_def and cmlPtreeConversion_Eseq_encode_def,   *)
(*   the induction theorem of Eseq_encode cmlPtreeConversion_Eseq_encode_ind,*)
(*   mpop_anonscope_def is mpopscope_def.  NAME_ind theorems are the         *)
(*   induction theorems of the kit (HOL4 has them too, unnamed in the        *)
(*   script).                                                                *)
(* - Helpers that are not HOL4 names have the prefix PTREEAUX_.              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/gram.ml";;
needs "semantics/tokenUtils.ml";;
needs "semantics/namespace.ml";;
needs "semantics/ast.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Termination of the conversion functions: each recursive call is on a     *)
(* child of the parse tree argument.  PTREEAUX_measure tys is the measure     *)
(* on the sum of the argument tuples tys (each a parse tree, or a pair of a  *)
(* non-terminal and a parse tree, as cake_def_wf encodes mutual recursion):  *)
(* the size of the parse tree.                                               *)
(* ------------------------------------------------------------------------- *)

let PTREEAUX_measure (tys:hol_type list) =
  let tree_size t =
    match dest_type (type_of t) with
      "parsetree",[a;b;c] ->
        let zero ty = mk_abs(mk_var("x",ty),`0`) in
        list_mk_icomb "parsetree_size" [zero a; zero b; zero c; t]
    | _ -> failwith "PTREEAUX_measure" in
  let arg_size ty =
    let v = mk_var("a",ty) in
    mk_abs(v,tree_size (if fst(dest_type ty) = "prod"
                        then mk_icomb(mk_const("SND",[]),v) else v)) in
  let rec combine tys =
    match tys with
      [ty] -> arg_size ty
    | ty::rest ->
        let g = combine rest in
        let sty = mk_type("sum",[ty; fst(dest_fun_ty(type_of g))]) in
        let s = mk_var("s",sty) in
        mk_abs(s,list_mk_icomb "sum_CASE" [s; arg_size ty; g])
    | [] -> failwith "PTREEAUX_measure" in
  mk_icomb(mk_const("measure",[]),combine tys);;


(* The recursion package's rule for a case expression on a parse tree,      *)
(* with the components of the product-typed constructor arguments as       *)
(* separate context variables (Lf (y1,y2), Nd (y1,y2) y3): the kit's rule    *)
(* for parsetree_CASE is applied with its pair-typed arm variables split     *)
(* into nested tuples, which the next rule does not match (KIT ISSUE).      *)
(* Registered for this file only (removed at its end).                       *)

let PTREEAUX_ADMISSIBLE_parsetree_CASE = prove
 (`!(<<) (p:(A1->B1)->P->bool) (s:P->A1) (e:(A1->B1)->P->(A,B,C)parsetree)
    (h1:(A1->B1)->P->(A,B)symbol#C->D)
    (h2:(A1->B1)->P->(B+num)#C->((A,B,C)parsetree)list->D).
     admissible (<<) p s e /\
     admissible (<<) (\f (y1,y2,x). p f x /\ e f x = Lf (y1,y2))
                     (\(y1,y2,x). s x) (\f (y1,y2,x). h1 f x (y1,y2)) /\
     admissible (<<) (\f (y1,y2,y3,x). p f x /\ e f x = Nd (y1,y2) y3)
                     (\(y1,y2,y3,x). s x) (\f (y1,y2,y3,x). h2 f x (y1,y2) y3)
     ==> admissible (<<) p s (\f x. parsetree_CASE (e f x) (h1 f x) (h2 f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`f:A1->B1`; `g:A1->B1`; `a:P`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(e:(A1->B1)->P->(A,B,C)parsetree) g a = e f a` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPEC `(e:(A1->B1)->P->(A,B,C)parsetree) f a` parsetree_nchotomy) THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[parsetree_CASE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let PTREEAUX_saved_admissible_rules = !cake_admissible_rules;;

cake_register_admissible "parsetree_CASE" PTREEAUX_ADMISSIBLE_parsetree_CASE;;


(* handling constructor arities gets very complicated when "open" is      *)
(* implemented                                                            *)

let PCstate0_INFO = cake_record "PCstate0"
  ["fixities","(mlstring,num option)fmap";
   "ctr_arities","((mlstring,mlstring)id,num)fmap"];;

let PCstate0_component_equality = PCstate0_INFO.ri_component_equality;;

(* recording a fixity of NONE is what you have to do to represent an      *)
(* explicit nonfix declaration                                            *)

(* HOL4: Type M = :PCstate0 list -> (A # PCstate0 list) option, written    *)
(* out (a HOL Light abbreviation takes no parameter, and :M would capture  *)
(* the type variable M of the other files)                                 *)

let empty_PCstate0_def = cake_def
  `empty_PCstate0 = PCstate0_REC FEMPTY FEMPTY`;;

let mpushPC_scope_def = cake_def
  `mpushPC_scope = \pcs:PCstate0 list. SOME (one,CONS empty_PCstate0 pcs)`;;

let fixity_lookup_def = cake_def
  `fixity_lookup (nm:mlstring) (pcs:PCstate0 list) =
     match pcs with
       [] -> NONE:num option
     | CONS pc0 rest ->
         match FLOOKUP (PCstate0_fixities pc0) nm with
           NONE -> fixity_lookup nm rest
         | SOME NONE -> NONE
         | SOME r -> r`;;

let fixity_lookup_ind = cake_ind "fixity_lookup";;

(* mfixity_lookup : mlstring -> num M  fails if the mlstring has no       *)
(* fixity, even though it is perfectly reasonable for a mlstring to be    *)
(* nonfix                                                                  *)

let mfixity_lookup_def = cake_def
  `mfixity_lookup (nm:mlstring) =
     \pcs:PCstate0 list. OPTION_MAP (\r:num. (r,pcs)) (fixity_lookup nm pcs)`;;

let mFUPD_HD_def = cake_def
  `mFUPD_HD (f:A->A) (pcs:A list) =
     match pcs with
       [] -> NONE
     | CONS h t -> SOME (one,CONS (f h) t)`;;

(* msetfix : mlstring -> num option -> unit M *)

let msetfix_def = cake_def
  `msetfix (nm:mlstring) (fix:num option) =
     mFUPD_HD (\s0. PCstate0_fixities_fupd (\fm. fm |+ (nm,fix)) s0)`;;

(* mpop_anonscope : unit M  (HOL4: mpop_anonscope_def) *)

let mpopscope_def = cake_def
  `mpopscope =
     \pcs:PCstate0 list.
       match pcs with
         [] -> NONE
       | CONS _ t -> SOME (one,t)`;;

let mpop_namedscope_def = cake_def
  `mpop_namedscope (s:mlstring) =
     \pcs:PCstate0 list.
       match pcs with
         [] -> NONE
       | [_] -> NONE
       | CONS curr (CONS next rest) -> SOME (one,CONS next rest)`;;

(* needs to be adjusted so that constructors (only) declared in the       *)
(* current scope get recorded in the next level up with the given name as *)
(* a prefix.  Does nothing different at this stage, when I expect just to *)
(* be handling fixities (which are handled in a non-exportable way).      *)

(* ------------------------------------------------------------------------- *)
(* We'll be using the option monad quite a bit in what follows.             *)
(* ------------------------------------------------------------------------- *)

let ifM_def = cake_def
  `ifM (bM:bool option) (tM:A option) (eM:A option) =
     OPTION_BIND bM (\b. if b then tM else eM)`;;

let mk_binop_def = cake_def
  `mk_binop (a_op:(mlstring,mlstring)id) (a1:exp) (a2:exp) =
     if a_op = Short (implode "::")
     then Con (SOME (Short (implode "::"))) [a1; a2]
     else App Opapp [App Opapp [Var a_op; a1]; a2]`;;

let tokcheck_def = cake_def
  `tokcheck (pt:(A,B,C)parsetree) (tok':A) <=>
     OPTION_BIND (destLf pt) destTOK = SOME tok'`;;

let ptree_UQTyop_def = cake_def
  `(ptree_UQTyop (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_UQTyop (Nd (nt':(MMLnonT+num)#C) args) =
      if ~(FST nt' = INL nUQTyOp) then NONE
      else
        match args with
          [pt] ->
            OPTION_BIND (destLf pt) (\lf.
            OPTION_BIND (destTOK lf) (\tk.
              OPTION_CHOICE (destSymbolT tk) (destAlphaT tk)))
        | _ -> NONE)`;;

let ptree_TyvarN_def = cake_def
  `(ptree_TyvarN (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_TyvarN (Nd (nt':(MMLnonT+num)#C) args) =
      if ~(FST nt' = INL nTyvarN) then NONE
      else
        match args with
          [tyv] -> destTyvarPT tyv
        | _ -> NONE)`;;

let Long_Short_def = cake_def
  `(Long_Short End (s:mlstring) = Short s:(mlstring,mlstring)id) /\
   (Long_Short (tokens_Mod x xs) s = Long x (Long_Short xs s))`;;

let Long_Short_ind = cake_ind "Long_Short";;

let ptree_Tyop_def = cake_def
  `(ptree_Tyop (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_Tyop (Nd (nt':(MMLnonT+num)#C) args) =
      if ~(FST nt' = INL nTyOp) then NONE
      else
        match args with
          [pt] ->
            OPTION_CHOICE
              (OPTION_BIND (OPTION_BIND (OPTION_BIND (destLf pt) destTOK)
                                        destLongidT)
                 (\p. match p with (xs,s) -> SOME (Long_Short xs s)))
              (OPTION_BIND (ptree_UQTyop pt) (\nm. SOME (Short nm)))
        | _ -> NONE)`;;

let tokcheckl_def = cake_def
  `tokcheckl (pts:((A,B,C)parsetree)list) (toks:A list) <=>
     match (pts,toks) with
       ([],[]) -> T
     | (CONS pt prest,CONS tok' tokrest) ->
         tokcheck pt tok' /\ tokcheckl prest tokrest
     | _ -> F`;;

let tokcheckl_ind = cake_ind "tokcheckl";;

let ptree_linfix_def = cake_def_wf
  `measure (\x:MMLnonT#token#(mlptree->A option)#mlptree.
              parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:locs. 0)
                (SND (SND (SND x))))`
  TERM_TAC
  `ptree_linfix (topnt:MMLnonT) (opn:token) (elnt:mlptree->A option)
                (pt:mlptree) =
     match pt with
       Lf _ -> NONE
     | Nd nt' args ->
         if FST nt' = INL topnt then
           match args with
             [pt] -> OPTION_BIND (elnt pt) (\e. SOME [e])
           | [x; op_pt; pt] ->
               OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck op_pt opn))
                 (OPTION_BIND (ptree_linfix topnt opn elnt x) (\front.
                  OPTION_BIND (elnt pt) (\last.
                  SOME (APPEND front [last]))))
           | _ -> NONE
         else NONE`;;

let ptree_linfix_ind = cake_ind "ptree_linfix";;

let tuplify_def = cake_def
  `(tuplify [] = NONE) /\
   (tuplify [ty] = SOME ty) /\
   (tuplify tys = SOME (Attup tys))`;;



let ptree_Type_def = cake_def_wf_clauses
  `measure (\x:(MMLnonT#(token,MMLnonT,C)parsetree) +
               (token,MMLnonT,C)parsetree + (token,MMLnonT,C)parsetree +
               (token,MMLnonT,C)parsetree.
              sum_CASE x
                (\p. parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) (SND p))
                (\y. sum_CASE y
                       (\pt. parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) pt)
                       (\z. sum_CASE z
                              (\pt. parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) pt)
                              (\pt. parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) pt))))`
  TERM_TAC
  [`(ptree_Type:MMLnonT->(token,MMLnonT,C)parsetree->ast_t option) nt' (Lf _) =
      NONE`;
   `(ptree_Type:MMLnonT->(token,MMLnonT,C)parsetree->ast_t option) nm
      (Nd nt' args) =
      if ~(FST nt' = INL nm) then NONE
      else if nm = nType then
        match args with
          [dt] ->
            OPTION_BIND ((ptree_PType:(token,MMLnonT,C)parsetree->(ast_t list)option) dt)
              (\tys. tuplify tys)
        | [dt; arrowt; rt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck arrowt ArrowT))
              (OPTION_BIND (ptree_PType dt) (\dtys.
               OPTION_BIND (tuplify dtys) (\dty.
               OPTION_BIND (ptree_Type nType rt) (\rty.
               SOME (Atfun dty rty)))))
        | _ -> NONE
      else if nm = nDType then
        match args with
          [pt] -> ptree_Type nTbase pt
        | [dt; opn] ->
            OPTION_BIND (ptree_Type nDType dt) (\dty.
            OPTION_BIND (ptree_Tyop opn) (\opname.
            SOME (Atapp [dty] opname)))
        | _ -> NONE
      else if nm = nTbase then
        match args with
          [pt] ->
            OPTION_CHOICE (OPTION_MAP Atvar (destTyvarPT pt))
                          (OPTION_MAP (Atapp []) (ptree_Tyop pt))
        | [lpart; t; rpart] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck lpart LparT /\ tokcheck rpart RparT))
              (ptree_Type nType t)
        | [lpart; tl; rpart; opn] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck lpart LparT /\ tokcheck rpart RparT))
              (OPTION_BIND
                 ((ptree_Typelist2:(token,MMLnonT,C)parsetree->(ast_t list)option) tl)
                 (\tylist.
                  OPTION_BIND (ptree_Tyop opn) (\opname.
                  SOME (Atapp tylist opname))))
        | _ -> NONE
      else NONE`;
   `(ptree_Typelist2:(token,MMLnonT,C)parsetree->(ast_t list)option) ptree =
      match ptree with
        Lf _ -> NONE
      | Nd nt' args ->
          if ~(FST nt' = INL nTypeList2) then NONE
          else
            match args with
              [dt; commat; tl'] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck commat CommaT))
                  (OPTION_BIND
                     ((ptree_Type:MMLnonT->(token,MMLnonT,C)parsetree->ast_t option)
                        nType dt) (\ty.
                   OPTION_BIND
                     ((ptree_TypeList1:(token,MMLnonT,C)parsetree->(ast_t list)option)
                        tl') (\tylist.
                   SOME (CONS ty tylist))))
            | _ -> NONE`;
   `(ptree_TypeList1:(token,MMLnonT,C)parsetree->(ast_t list)option) ptree =
      match ptree with
        Lf _ -> NONE
      | Nd nt' args ->
          if ~(FST nt' = INL nTypeList1) then NONE
          else
            match args with
              [dt] ->
                OPTION_BIND
                  ((ptree_Type:MMLnonT->(token,MMLnonT,C)parsetree->ast_t option)
                     nType dt) (\ty. SOME [ty])
            | [dt; commat; tl] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck commat CommaT))
                  (OPTION_BIND (ptree_Type nType dt) (\ty.
                   OPTION_BIND (ptree_TypeList1 tl) (\tl.
                   SOME (CONS ty tl))))
            | _ -> NONE`;
   `(ptree_PType:(token,MMLnonT,C)parsetree->(ast_t list)option) ptree =
      match ptree with
        Lf _ -> NONE
      | Nd nt' args ->
          if ~(FST nt' = INL nPType) then NONE
          else
            match args with
              [dty_pt] ->
                OPTION_BIND
                  ((ptree_Type:MMLnonT->(token,MMLnonT,C)parsetree->ast_t option)
                     nDType dty_pt) (\dty. SOME [dty])
            | [dty_pt; st; pty_pt] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck st StarT))
                  (OPTION_BIND (ptree_Type nDType dty_pt) (\dty.
                   OPTION_BIND (ptree_PType pty_pt) (\ptys.
                   SOME (CONS dty ptys))))
            | _ -> NONE`];;

let ptree_Type_ind = cake_ind "ptree_Type";;

let ptree_TypeName_def = cake_def
  `ptree_TypeName (ptree:mlptree) =
     match ptree with
       Lf _ -> NONE
     | Nd nt' args ->
         if FST nt' = INL nTypeName then
           match args with
             [opt] -> OPTION_BIND (ptree_UQTyop opt) (\opn. SOME ([],opn))
           | [sym; opt] ->
               OPTION_BIND (destTyvarPT sym) (\tyvn.
               OPTION_BIND (ptree_UQTyop opt) (\opn.
               SOME ([tyvn],opn)))
           | [lp; tyvl; rp; opt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck lp LparT /\ tokcheck rp RparT))
                 (OPTION_BIND (ptree_linfix nTyVarList CommaT ptree_TyvarN tyvl)
                    (\tyvnms.
                     OPTION_BIND (ptree_UQTyop opt) (\opn.
                     SOME (tyvnms,opn))))
           | _ -> NONE
         else NONE`;;

let ptree_UQConstructorName_def = cake_def
  `(ptree_UQConstructorName (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_UQConstructorName (Nd (nm:(MMLnonT+num)#C) args) =
      if ~(FST nm = INL nUQConstructorName) then NONE
      else
        match args with
          [pt] -> OPTION_BIND (OPTION_BIND (destLf pt) destTOK) destAlphaT
        | _ -> NONE)`;;

let ptree_ConstructorName_def = cake_def
  `ptree_ConstructorName (ast:(token,MMLnonT,C)parsetree) =
     match ast with
       Lf _ -> NONE
     | Nd nt' args ->
         if ~(FST nt' = INL nConstructorName) then NONE
         else
           match args with
             [pt] ->
               OPTION_CHOICE
                 (OPTION_BIND (ptree_UQConstructorName pt) (\s. SOME (Short s)))
                 (OPTION_BIND
                    (OPTION_BIND (OPTION_BIND (destLf pt) destTOK) destLongidT)
                    (\p. match p with (xs,s) -> SOME (Long_Short xs s)))
           | _ -> NONE`;;

let detuplify_def = cake_def
  `(detuplify (Attup args) = args) /\
   (detuplify ty = [ty])`;;

let detuplify_ind = prove
 (`!P. (!args. P (Attup args)) /\ (!v. P (Atvar v)) /\
       (!v1 v2. P (Atfun v1 v2)) /\ (!v3 v4. P (Atapp v3 v4))
       ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CASES_ON `v:ast_t` THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 states it with pmatch (first match wins); here the match compiles   *)
(* to the case constant, as every match does                                *)

let detuplify_pmatch = prove
 (CASE_TERM
  `!ty. detuplify ty = match ty with Attup args -> args | ty -> [ty]`,
  GEN_TAC THEN CASES_ON `ty:ast_t` THEN REWRITE_TAC[detuplify_def] THEN
  CASE_REWRITE_TAC[]);;

let ptree_PTbase_def = cake_def
  `ptree_PTbase (ast:(token,MMLnonT,C)parsetree) =
     match ast with
       Lf _ -> NONE
     | Nd nt' args ->
         if FST nt' = INL nPTbase then
           match args with
             [pt] ->
               OPTION_CHOICE (OPTION_MAP Atvar (destTyvarPT pt))
                             (OPTION_MAP (Atapp []) (ptree_Tyop pt))
           | [lpart; t; rpart] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck lpart LparT /\ tokcheck rpart RparT))
                 (ptree_Type nType t)
           | _ -> NONE
         else NONE`;;

let ptree_TbaseList_def = cake_def_wf
  `measure (\pt:(token,MMLnonT,C)parsetree.
              parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) pt)`
  TERM_TAC
  `ptree_TbaseList (ast:(token,MMLnonT,C)parsetree) =
     match ast with
       Lf _ -> NONE
     | Nd nt' args ->
         if FST nt' = INL nTbaseList then
           match args with
             [] -> SOME []
           | [ptb_pt; rest_pt] ->
               OPTION_BIND (ptree_PTbase ptb_pt) (\b.
               OPTION_BIND (ptree_TbaseList rest_pt) (\rest.
               SOME (CONS b rest)))
           | _ -> NONE
         else NONE`;;

let ptree_TbaseList_ind = cake_ind "ptree_TbaseList";;

let ptree_Dconstructor_def = cake_def
  `ptree_Dconstructor (ast:(token,MMLnonT,C)parsetree) =
     match ast with
       Lf x -> NONE
     | Nd nt' args ->
         if FST nt' = INL nDconstructor then
           match args with
             [] -> NONE
           | CONS t ts ->
               OPTION_BIND (ptree_UQConstructorName t) (\cname.
               OPTION_BIND
                 (match ts with
                    [blist] ->
                      OPTION_BIND (ptree_TbaseList blist) (\args. SOME args)
                  | _ -> NONE) (\types.
               SOME (cname,types)))
         else NONE`;;

let ptree_DtypeDecl_def = cake_def
  `ptree_DtypeDecl (pt:mlptree) =
     match pt with
       Lf _ -> NONE
     | Nd nt' args ->
         if FST nt' = INL nDtypeDecl then
           match args with
             [tynm_pt; eqt; dtc_pt] ->
               OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck eqt EqualsT))
                 (OPTION_BIND (ptree_TypeName tynm_pt) (\tynm.
                  OPTION_BIND
                    (ptree_linfix nDtypeCons BarT ptree_Dconstructor dtc_pt)
                    (\dtc. SOME (FST tynm,SND tynm,dtc))))
           | _ -> NONE
         else NONE`;;

let ptree_TypeDec_def = cake_def
  `ptree_TypeDec (ptree:mlptree) =
     match ptree with
       Lf _ -> NONE:type_def option
     | Nd nt' args ->
         if FST nt' = INL nTypeDec then
           match args with
             [datatype_pt; pt] ->
               OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck datatype_pt DatatypeT))
                 (ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt)
           | _ -> NONE
         else NONE`;;

let ptree_TypeAbbrevDec_def = cake_def
  `ptree_TypeAbbrevDec (ptree:mlptree) =
     match ptree with
       Lf _ -> NONE:dec option
     | Nd nt' args ->
         if FST nt' = INL nTypeAbbrevDec then
           match args with
             [typetok; tynm; eqtok; typ_pt] ->
               OPTION_IGNORE_BIND
                 (OPTION_GUARD (tokcheck typetok TypeT /\ tokcheck eqtok EqualsT))
                 (OPTION_BIND (ptree_TypeName tynm) (\p.
                  match p with
                    (vars,nm) ->
                      OPTION_BIND (ptree_Type nType typ_pt) (\typ.
                      SOME (Dtabbrev (SND nt') vars nm typ))))
           | _ -> NONE
         else NONE`;;

let singleSymP_def = cake_def
  `(singleSymP (P:mlstring->bool) [pt:(token,B,C)parsetree] =
      OPTION_BIND (OPTION_BIND (OPTION_BIND (destLf pt) destTOK) destSymbolT)
        (\s. OPTION_IGNORE_BIND (OPTION_GUARD (P s))
               (SOME (Short s:(D,mlstring)id)))) /\
   (singleSymP _ _ = NONE)`;;

let ptree_Op_def = cake_def
  `(ptree_Op (Lf (_:(token,MMLnonT)symbol#C)) = NONE:((D,mlstring)id)option) /\
   (ptree_Op (Nd (nt':(MMLnonT+num)#C) subs) =
      if FST nt' = INL nMultOps then
        if tokcheckl subs [StarT] then SOME (Short (implode "*"))
        else if tokcheckl subs [AlphaT (implode "mod")]
        then SOME (Short (implode "mod"))
        else if tokcheckl subs [AlphaT (implode "div")]
        then SOME (Short (implode "div"))
        else singleSymP (validMultSym o explode) subs
      else if FST nt' = INL nAddOps then singleSymP (validAddSym o explode) subs
      else if FST nt' = INL nListOps then
        singleSymP (validListSym o explode) subs
      else if FST nt' = INL nRelOps then
        OPTION_CHOICE (singleSymP (validRelSym o explode) subs)
          (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheckl subs [EqualsT]))
             (SOME (Short (implode "="))))
      else if FST nt' = INL nCompOps then
        if tokcheckl subs [SymbolT (implode ":=")]
        then SOME (Short (implode ":="))
        else if tokcheckl subs [AlphaT (implode "o")]
        then SOME (Short (implode "o"))
        else NONE
      else NONE)`;;

let ptree_V_def = cake_def
  `(ptree_V (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_V (Nd (nt':(MMLnonT+num)#C) subs) =
      OPTION_IGNORE_BIND (OPTION_GUARD (FST nt' = INL nV))
        (match subs with
           [pt] ->
             OPTION_BIND (OPTION_BIND (destLf pt) destTOK) (\t.
               OPTION_CHOICE (destAlphaT t) (destSymbolT t))
         | _ -> NONE))`;;

let ptree_FQV_def = cake_def
  `(ptree_FQV (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_FQV (Nd (nt':(MMLnonT+num)#C) args) =
      if ~(FST nt' = INL nFQV) then NONE
      else
        match args with
          [pt] ->
            OPTION_CHOICE (OPTION_MAP Short (ptree_V pt))
              (OPTION_BIND
                 (OPTION_BIND (OPTION_BIND (destLf pt) destTOK) destLongidT)
                 (\p. match p with (xs,s) -> SOME (Long_Short xs s)))
        | _ -> NONE)`;;

let isSymbolicConstructor_def = cake_def
  `isSymbolicConstructor (s:string) = SOME (s = "::")`;;

let isConstructor_def = cake_def
  `isConstructor (s:string) =
     ifM (isSymbolicConstructor s) (SOME T)
       (SOME (match oHD s with
                NONE -> F
              | SOME c -> isAlpha c /\ isUpper c))`;;

(* the third clause below will lead to a failure when the environment is   *)
(* consulted to reveal that the long-id given does not correspond to a      *)
(* constructor.  We do this rather than fail to make the totality theorem   *)
(* work                                                                     *)

let EtoPat_def = sem1aux_def (list_mk_conj
  [`EtoPat (Con x args) = if NULL args then SOME (Pcon x []) else NONE`;
   `EtoPat (Var (Short n)) = SOME (Pvar n)`;
   `EtoPat (Var (Long str n)) = SOME (Pcon (SOME (Long str n)) [])`;
   `EtoPat (_:exp) = NONE:pat option`]);;

let ptree_OpID_def = cake_def
  `(ptree_OpID (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_OpID (Nd (nt':(MMLnonT+num)#C) subs) =
      if ~(FST nt' = INL nOpID) then NONE
      else
        match subs with
          [Lf (TOK tk,_)] ->
            OPTION_CHOICE
             (OPTION_CHOICE
              (OPTION_CHOICE
               (OPTION_BIND (destAlphaT tk) (\s.
                  ifM (isConstructor (explode s))
                      (SOME (Con (SOME (Short s)) []))
                      (SOME (Var (Short s)))))
               (OPTION_BIND (destSymbolT tk) (\s.
                  ifM (isSymbolicConstructor (explode s))
                      (SOME (Con (SOME (Short s)) []))
                      (SOME (Var (Short s))))))
              (OPTION_BIND (destLongidT tk) (\p.
                 match p with
                   (path,s) ->
                     ifM (isConstructor (explode s))
                         (SOME (Con (SOME (Long_Short path s)) []))
                         (SOME (Var (Long_Short path s))))))
             (if tk = StarT then
                ifM (isSymbolicConstructor "*")
                    (SOME (Con (SOME (Short (implode "*"))) []))
                    (SOME (Var (Short (implode "*"))))
              else if tk = EqualsT then SOME (Var (Short (implode "=")))
              else NONE)
        | _ -> NONE)`;;

let cmlPtreeConversion_Papply_def = cake_def
  `Papply (pat:pat) (arg:pat) =
     match pat with
       Pcon cn args -> Pcon cn (APPEND args [arg])
     | _ -> pat`;;

(* HOL4 defines maybe_handleRef by the clauses                              *)
(* maybe_handleRef (Pcon (SOME (Short <<Ref>>)) [pat]) = Pref pat and        *)
(* maybe_handleRef p = p, with a string literal in a pattern (TFL with the   *)
(* classic heuristic); here the literal is the equivalent test              *)

let maybe_handleRef_def = cake_def
  `maybe_handleRef (p:pat) =
     match p with
       Pcon (SOME (Short n)) [pat] ->
         if n = implode "Ref" then Pref pat else p
     | _ -> p`;;

let ptree_Pattern_def = cake_def_wf_clauses
  `measure (\x:(MMLnonT#(token,MMLnonT,C)parsetree) + (token,MMLnonT,C)parsetree.
              sum_CASE x
                (\p. parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) (SND p))
                (\pt. parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) pt))`
  TERM_TAC
  [`(ptree_Pattern:MMLnonT->(token,MMLnonT,C)parsetree->pat option) nt' (Lf _) =
      NONE`;
   `(ptree_Pattern:MMLnonT->(token,MMLnonT,C)parsetree->pat option) nt'
      (Nd nm args) =
      if ~(INL nt' = FST nm) then NONE
      else if FST nm = INL nPbase then
        match args with
          [vic] ->
            OPTION_CHOICE
             (OPTION_CHOICE
              (OPTION_CHOICE
               (OPTION_CHOICE
                 (ptree_Pattern nPtuple vic)
                 (OPTION_BIND (ptree_ConstructorName vic) (\cname.
                  SOME (Pcon (SOME cname) []))))
               (OPTION_BIND (ptree_V vic) (\vname. SOME (Pvar vname))))
              (OPTION_BIND (destLf vic) (\lf.
               OPTION_BIND (destTOK lf) (\t.
                 OPTION_CHOICE
                  (OPTION_CHOICE
                    (OPTION_BIND (destIntT t) (\i. SOME (Plit (IntLit i))))
                    (OPTION_BIND (destStringT t) (\s. SOME (Plit (StrLit s)))))
                  (OPTION_BIND (destCharT t) (\c. SOME (Plit (Char c))))))))
             (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck vic UnderbarT))
                (SOME Pany))
        | [lb; rb] ->
            if tokcheckl args [LbrackT; RbrackT]
            then SOME (Pcon (SOME (Short (implode "[]"))) [])
            else if tokcheckl [lb] [OpT]
            then OPTION_BIND (ptree_OpID rb) (\e. EtoPat e)
            else NONE
        | [lb; plistpt; rb] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [lb; rb] [LbrackT; RbrackT]))
              (OPTION_BIND
                 ((ptree_Plist:(token,MMLnonT,C)parsetree->(pat list)option)
                    plistpt) (\plist.
               SOME (ITLIST (\p a. Pcon (SOME (Short (implode "::"))) [p; a])
                       plist (Pcon (SOME (Short (implode "[]"))) []))))
        | _ -> NONE
      else if FST nm = INL nPConApp then
        match args with
          [cn] ->
            OPTION_BIND (ptree_ConstructorName cn) (\cname.
            SOME (Pcon (SOME cname) []))
        | [capp_pt; base_pt] ->
            OPTION_BIND (ptree_Pattern nPConApp capp_pt) (\capp.
            OPTION_BIND (ptree_Pattern nPbase base_pt) (\base.
            SOME (Papply capp base)))
        | _ -> NONE
      else if FST nm = INL nPapp then
        match args with
          [pb] -> ptree_Pattern nPbase pb
        | [capp_pt; ppt] ->
            OPTION_BIND (ptree_Pattern nPConApp capp_pt) (\capp.
            OPTION_BIND (ptree_Pattern nPbase ppt) (\b.
            SOME (maybe_handleRef (Papply capp b))))
        | _ -> NONE
      else if FST nm = INL nPcons then
        match args with
          [papt] -> ptree_Pattern nPapp papt
        | [papt; cons_t; pcons_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheck cons_t (SymbolT (implode "::"))))
              (OPTION_BIND (ptree_Pattern nPapp papt) (\pa.
               OPTION_BIND (ptree_Pattern nPcons pcons_pt) (\patt.
               SOME (Pcon (SOME (Short (implode "::"))) [pa; patt]))))
        | _ -> NONE
      else if FST nm = INL nPas then
        match args with
          [papt] -> ptree_Pattern nPcons papt
        | [vt; as_t; papt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck as_t AsT))
              (OPTION_BIND (ptree_Pattern nPcons papt) (\pa.
               OPTION_BIND (ptree_V vt) (\vtt.
               SOME (Pas pa vtt))))
        | _ -> NONE
      else if FST nm = INL nPattern then
        match args with
          [pas] -> ptree_Pattern nPas pas
        | [pas_pt; colon_t; type_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck colon_t ColonT))
              (OPTION_BIND (ptree_Pattern nPas pas_pt) (\pc.
               OPTION_BIND (ptree_Type nType type_pt) (\ty.
               SOME (Ptannot pc ty))))
        | _ -> NONE
      else if FST nm = INL nPtuple then
        match args with
          [lp; rp] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [lp; rp] [LparT; RparT]))
              (SOME (Pcon NONE []))
        | [lp; pl_pt; rp] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [lp; rp] [LparT; RparT]))
              (OPTION_BIND (ptree_Plist pl_pt) (\pl.
               match pl with
                 [] -> NONE
               | [p] -> SOME p
               | _ -> SOME (Pcon NONE pl)))
        | _ -> NONE
      else NONE`;
   `(ptree_Plist:(token,MMLnonT,C)parsetree->(pat list)option) (Lf _) = NONE`;
   `(ptree_Plist:(token,MMLnonT,C)parsetree->(pat list)option) (Nd nm args) =
      if ~(FST nm = INL nPatternList) then NONE
      else
        match args with
          [p_pt] ->
            OPTION_BIND
              ((ptree_Pattern:MMLnonT->(token,MMLnonT,C)parsetree->pat option)
                 nPattern p_pt) (\p. SOME [p])
        | [p; ct; pl] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck ct CommaT))
              (OPTION_BIND (ptree_Pattern nPattern p) (\hdpat.
               OPTION_BIND (ptree_Plist pl) (\tlpats.
               SOME (CONS hdpat tlpats))))
        | _ -> NONE`];;

let ptree_Pattern_ind = cake_ind "ptree_Pattern";;

(* HOL4: Type ptree[local] = mlptree, and ptree_Pattern_pevaled (computeLib *)
(* only, made by ML partial evaluation) are not ported.                     *)

let ptree_Plist_thm =
  end_itlist CONJ (fst(chop_list 2 (rev(CONJUNCTS ptree_Pattern_def))));;

let ptree_PbaseList1_def = cake_def_wf
  `measure (\pt:(token,MMLnonT,C)parsetree.
              parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:C. 0) pt)`
  TERM_TAC
  `(ptree_PbaseList1 (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_PbaseList1 (Nd (nm:(MMLnonT+num)#C) args) =
      if ~(FST nm = INL nPbaseList1) then NONE
      else
        match args with
          [p_pt] -> OPTION_MAP (\x. [x]) (ptree_Pattern nPbase p_pt)
        | [p_pt; pl_pt] ->
            OPTION_MAP2 CONS (ptree_Pattern nPbase p_pt)
                             (ptree_PbaseList1 pl_pt)
        | _ -> NONE)`;;

let ptree_PbaseList1_ind = cake_ind "ptree_PbaseList1";;

let cmlPtreeConversion_Eseq_encode_def = cake_def
  `(Eseq_encode [] = NONE) /\
   (Eseq_encode [e] = SOME e) /\
   (Eseq_encode (CONS e es) =
      OPTION_BIND (Eseq_encode es) (\body. SOME (Let NONE e body)))`;;

let cmlPtreeConversion_Eseq_encode_ind = cake_ind "Eseq_encode";;

let dest_Conk_def = sem1aux_def
  `(dest_Conk (Con x y) (k:((mlstring,mlstring)id)option->exp list->A) (v:A) =
      k x y) /\
   (dest_Conk _ k v = v)`;;

let destFFIop_def = sem1aux_def
  `(destFFIop (FFI s) = SOME s) /\
   (destFFIop _ = NONE)`;;
let _ = cake_add_simps [destFFIop_def];;

let strip_loc_expr_def = sem1aux_def
  `(strip_loc_expr (Lannot e l) =
      match strip_loc_expr e with (e0,_) -> (e0,SOME l)) /\
   (strip_loc_expr e = (e,NONE))`;;

let strip_loc_expr_ind = cake_ind "strip_loc_expr";;

let merge_locsopt_def = cake_def
  `(merge_locsopt (SOME l1) (SOME l2) = SOME (merge_locs l1 l2)) /\
   (merge_locsopt _ _ = NONE)`;;

let optLannot_def = cake_def
  `(optLannot NONE (e:exp) = e) /\
   (optLannot (SOME l) e = Lannot e l)`;;

let mkAst_App_def = cake_def
  `mkAst_App (a1:exp) (a2:exp) =
     let (a10,loc1) = strip_loc_expr a1 in
     dest_Conk a10
       (\nm_opt args.
          if nm_opt = SOME (Short (implode "Ref")) /\ NULL args
          then App Opref [a2]
          else
            let (a2',loc2) = strip_loc_expr a2 in
            optLannot (merge_locsopt loc1 loc2)
              (Con nm_opt (APPEND args [a2'])))
       (match a10 with
          App opn args ->
            (match destFFIop opn with
               NONE -> App Opapp [a1; a2]
             | SOME s -> App opn (APPEND args [a2]))
        | _ -> App Opapp [a1; a2])`;;

let dePat_def = sem1aux_def
  `(dePat (Pvar v) (b:exp) = (v,b)) /\
   (dePat p b = (implode "",Mat (Var (Short (implode ""))) [(p,b)]))`;;

let mkFun_def = cake_def
  `mkFun (p:pat) (b:exp) = UNCURRY Fun (dePat p b)`;;

let ptree_Eliteral_def = cake_def
  `(ptree_Eliteral (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_Eliteral (Nd (nt':(MMLnonT+num)#C) subs) =
      OPTION_IGNORE_BIND
        (OPTION_GUARD (LENGTH subs = 1 /\ FST nt' = INL nEliteral))
        (OPTION_BIND (destLf (HD subs)) (\lf.
         OPTION_BIND (destTOK lf) (\t.
           OPTION_CHOICE
            (OPTION_CHOICE
             (OPTION_CHOICE
              (OPTION_CHOICE
                (OPTION_BIND (destIntT t) (\i. SOME (Lit (IntLit i))))
                (OPTION_BIND (destCharT t) (\c. SOME (Lit (Char c)))))
              (OPTION_BIND (destStringT t) (\s. SOME (Lit (StrLit s)))))
             (OPTION_BIND (destWordT t) (\n. SOME (Lit (Word64 (word n))))))
            (OPTION_BIND (destFFIT t) (\s. SOME (App (FFI s) [])))))))`;;

let bind_loc_def = sem1aux_def
  `(bind_loc (Lannot e l) (l':locs) = Lannot e l) /\
   (bind_loc e l = Lannot e l)`;;

let letFromPat_def = cake_def
  `letFromPat (p:pat) (rhs:exp) (body:exp) =
     match p with
       Pany -> Let NONE rhs body
     | Pvar v -> Let (SOME v) rhs body
     | _ -> Mat rhs [(p,body)]`;;

(* The clauses of the ten functions share their argument variables (ent,  *)
(* x, nt', loc, subs, nm, ast; HOL4 has wildcards and the names ptree and   *)
(* args in some of them): the recursion package works on the tuple of all   *)
(* the argument variables of a mutual definition, and with distinct names   *)
(* this one takes more than an hour instead of about ten minutes.           *)

let ptree_Expr_def = cake_def_wf_clauses
  (PTREEAUX_measure
     [`:MMLnonT#mlptree`; `:MMLnonT#mlptree`; `:mlptree`; `:mlptree`;
      `:mlptree`; `:mlptree`; `:mlptree`; `:mlptree`; `:mlptree`;
      `:mlptree`])
  TERM_TAC
  [`(ptree_Expr:MMLnonT->mlptree->exp option) ent (Lf x) = NONE`;
   `(ptree_Expr:MMLnonT->mlptree->exp option) ent (Nd (nt',loc) subs) =
      OPTION_BIND
        (if INL ent = nt' then
           if nt' = INL nEbase then
             match subs with
               [lpart; pt; rpart] ->
                 if tokcheck lpart LparT then
                   OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck rpart RparT))
                     (OPTION_BIND
                        ((ptree_Eseq:mlptree->(exp list)option) pt)
                        (\eseq. Eseq_encode eseq))
                 else
                   OPTION_IGNORE_BIND
                     (OPTION_GUARD (tokcheckl [lpart; rpart] [LbrackT; RbrackT]))
                     (OPTION_BIND
                        ((ptree_Exprlist:MMLnonT->mlptree->(exp list)option)
                           nElist1 pt) (\elist.
                      SOME (ITLIST
                              (\e acc. Con (SOME (Short (implode "::"))) [e; acc])
                              elist (Con (SOME (Short (implode "[]"))) []))))
             | [single] ->
                 OPTION_CHOICE
                  (OPTION_CHOICE
                   (OPTION_CHOICE (ptree_Eliteral single)
                     (OPTION_BIND (ptree_FQV single) (\s. SOME (Var s))))
                   (OPTION_BIND (ptree_ConstructorName single) (\cname.
                    SOME (Con (SOME cname) []))))
                  (ptree_Expr nEtuple single)
             | [lp; rp] ->
                 if tokcheckl [lp; rp] [LparT; RparT] then SOME (Con NONE [])
                 else if tokcheckl [lp; rp] [LbrackT; RbrackT]
                 then SOME (Con (SOME (Short (implode "[]"))) [])
                 else if tokcheck lp OpT then ptree_OpID rp
                 else NONE
             | [lett; letdecs_pt; intok; ept; endt] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD
                      (tokcheckl [lett; intok; endt] [LetT; InT; EndT]))
                   (OPTION_BIND
                      ((ptree_LetDecs:mlptree->
                          (((pat#exp)+(mlstring#mlstring#exp)list)list)option)
                         letdecs_pt) (\letdecs.
                    OPTION_BIND (ptree_Eseq ept) (\eseq.
                    OPTION_BIND (Eseq_encode eseq) (\e.
                    SOME (ITLIST
                            (\df acc.
                               match df with
                                 INL (p,e0) -> letFromPat p e0 acc
                               | INR fds -> Letrec fds acc)
                            letdecs e)))))
             | _ -> NONE
           else if nt' = INL nEapp then
             match subs with
               [t1; t2] ->
                 OPTION_BIND (ptree_Expr nEapp t1) (\a1.
                 OPTION_BIND (ptree_Expr nEbase t2) (\a2.
                 SOME (mkAst_App a1 a2)))
             | [t] -> ptree_Expr nEbase t
             | _ -> NONE
           else if nt' = INL nEtuple then
             match subs with
               [lpart; el2; rpart] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheckl [lpart; rpart] [LparT; RparT]))
                   (OPTION_BIND (ptree_Exprlist nElist2 el2) (\es.
                    SOME (Con NONE es)))
             | _ -> NONE
           else if nt' = INL nEmult then
             match subs with
               [t1; opt; t2] ->
                 OPTION_BIND (ptree_Expr nEmult t1) (\a1.
                 OPTION_BIND (ptree_Op opt) (\a_op.
                 OPTION_BIND (ptree_Expr nEapp t2) (\a2.
                 SOME (mk_binop a_op a1 a2))))
             | [t] -> ptree_Expr nEapp t
             | _ -> NONE
           else if nt' = INL nEadd then
             match subs with
               [t1; opt; t2] ->
                 OPTION_BIND (ptree_Expr nEadd t1) (\a1.
                 OPTION_BIND (ptree_Op opt) (\a_op.
                 OPTION_BIND (ptree_Expr nEmult t2) (\a2.
                 SOME (mk_binop a_op a1 a2))))
             | [t] -> ptree_Expr nEmult t
             | _ -> NONE
           else if nt' = INL nElistop then
             match subs with
               [t1; opt; t2] ->
                 OPTION_BIND (ptree_Expr nEadd t1) (\a1.
                 OPTION_BIND (ptree_Op opt) (\a_op.
                 OPTION_BIND (ptree_Expr nElistop t2) (\a2.
                 SOME (mk_binop a_op a1 a2))))
             | [t] -> ptree_Expr nEadd t
             | _ -> NONE
           else if nt' = INL nErel then
             match subs with
               [t1; opt; t2] ->
                 OPTION_BIND (ptree_Expr nErel t1) (\a1.
                 OPTION_BIND (ptree_Op opt) (\a_op.
                 OPTION_BIND (ptree_Expr nElistop t2) (\a2.
                 SOME (mk_binop a_op a1 a2))))
             | [t] -> ptree_Expr nElistop t
             | _ -> NONE
           else if nt' = INL nEcomp then
             match subs with
               [t1; opt; t2] ->
                 OPTION_BIND (ptree_Expr nEcomp t1) (\a1.
                 OPTION_BIND (ptree_Op opt) (\a_op.
                 OPTION_BIND (ptree_Expr nErel t2) (\a2.
                 SOME (mk_binop a_op a1 a2))))
             | [t] -> ptree_Expr nErel t
             | _ -> NONE
           else if nt' = INL nEbefore then
             match subs with
               [t1; opt; t2] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD (tokcheck opt (AlphaT (implode "before"))))
                   (OPTION_BIND (ptree_Expr nEbefore t1) (\a1.
                    OPTION_BIND (ptree_Expr nEcomp t2) (\a2.
                    SOME (mk_binop (Short (implode "before")) a1 a2))))
             | [t] -> ptree_Expr nEcomp t
             | _ -> NONE
           else if nt' = INL nEtyped then
             match subs with
               [e_pt; colon; ty_pt] ->
                 OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck colon ColonT))
                   (OPTION_BIND (ptree_Expr nEbefore e_pt) (\e.
                    OPTION_BIND (ptree_Type nType ty_pt) (\ty.
                    SOME (Tannot e ty))))
             | [t] -> ptree_Expr nEbefore t
             | _ -> NONE
           else if nt' = INL nElogicAND then
             match subs with
               [t1; andt; t2] ->
                 OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck andt AndalsoT))
                   (OPTION_BIND (ptree_Expr nElogicAND t1) (\a1.
                    OPTION_BIND (ptree_Expr nEtyped t2) (\a2.
                    SOME (Log Andalso a1 a2))))
             | [t] -> ptree_Expr nEtyped t
             | _ -> NONE
           else if nt' = INL nElogicOR then
             match subs with
               [t1; ort; t2] ->
                 OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck ort OrelseT))
                   (OPTION_BIND (ptree_Expr nElogicOR t1) (\a1.
                    OPTION_BIND (ptree_Expr nElogicAND t2) (\a2.
                    SOME (Log Orelse a1 a2))))
             | [t] -> ptree_Expr nElogicAND t
             | _ -> NONE
           else if nt' = INL nEhandle then
             match subs with
               [pt] -> ptree_Expr nElogicOR pt
             | [e1pt; handlet; ent'] ->
                 OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck handlet HandleT))
                   (OPTION_BIND (ptree_Expr nElogicOR e1pt) (\e.
                    OPTION_BIND
                      ((ptree_PEs:mlptree->((pat#exp)list)option) ent')
                      (\pes. SOME (Handle e pes))))
             | _ -> NONE
           else if nt' = INL nE then
             match subs with
               [t] -> ptree_Expr nEhandle t
             | [raiset; ept] ->
                 OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck raiset RaiseT))
                   (OPTION_BIND (ptree_Expr nE ept) (\e. SOME (Raise e)))
             | [fnt; patnt; arrowt; ent'] ->
                 OPTION_CHOICE
                   (OPTION_IGNORE_BIND
                      (OPTION_GUARD (tokcheckl [fnt; arrowt] [FnT; DarrowT]))
                      (OPTION_BIND (ptree_Pattern nPattern patnt) (\p.
                       OPTION_BIND (ptree_Expr nE ent') (\e.
                       SOME (mkFun p e)))))
                   (OPTION_IGNORE_BIND
                      (OPTION_GUARD (tokcheckl [fnt; arrowt] [CaseT; OfT]))
                      (OPTION_BIND (ptree_Expr nE patnt) (\e.
                       OPTION_BIND (ptree_PEs ent') (\pes.
                       SOME (Mat e pes)))))
             | [ift; g; thent; te; elset; ee] ->
                 OPTION_IGNORE_BIND
                   (OPTION_GUARD
                      (tokcheckl [ift; thent; elset] [IfT; ThenT; ElseT]))
                   (OPTION_BIND (ptree_Expr nE g) (\a1.
                    OPTION_BIND (ptree_Expr nE te) (\a2.
                    OPTION_BIND (ptree_Expr nE ee) (\a3.
                    SOME (If a1 a2 a3)))))
             | _ -> NONE
           else NONE
         else NONE)
        (\e. SOME (bind_loc e loc))`;
   `(ptree_Exprlist:MMLnonT->mlptree->(exp list)option) nm ast =
      match ast with
        Lf _ -> NONE
      | Nd (nt',_) subs ->
          if nt' = INL nElist1 then
            match subs with
              [sing] ->
                OPTION_BIND ((ptree_Expr:MMLnonT->mlptree->exp option) nE sing)
                  (\e. SOME [e])
            | [e; ct; el1] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck ct CommaT))
                  (OPTION_BIND (ptree_Expr nE e) (\front.
                   OPTION_BIND (ptree_Exprlist nElist1 el1) (\back.
                   SOME (CONS front back))))
            | _ -> NONE
          else if nt' = INL nElist2 then
            match subs with
              [e; ct; el1] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck ct CommaT))
                  (OPTION_BIND (ptree_Expr nE e) (\front.
                   OPTION_BIND (ptree_Exprlist nElist1 el1) (\back.
                   SOME (CONS front back))))
            | _ -> NONE
          else NONE`;
   `(ptree_AndFDecls:mlptree->((mlstring#mlstring#exp)list)option) ast =
      match ast with
        Lf _ -> NONE
      | Nd (nt',_) subs ->
          if nt' = INL nAndFDecls then
            match subs with
              [single] ->
                OPTION_BIND
                  ((ptree_FDecl:mlptree->(mlstring#mlstring#exp)option) single)
                  (\fdec. SOME [fdec])
            | [fdecspt; andt; fdecpt] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck andt AndT))
                  (OPTION_BIND (ptree_AndFDecls fdecspt) (\fdecs.
                   OPTION_BIND (ptree_FDecl fdecpt) (\fdec.
                   SOME (APPEND fdecs [fdec]))))
            | _ -> NONE
          else NONE`;
   `(ptree_FDecl:mlptree->(mlstring#mlstring#exp)option) ast =
      match ast with
        Lf _ -> NONE
      | Nd (nt',_) subs ->
          if nt' = INL nFDecl then
            match subs with
              [fname_pt; pats_pt; eqt; body_pt] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck eqt EqualsT))
                  (OPTION_BIND (ptree_V fname_pt) (\fname.
                   OPTION_BIND (ptree_PbaseList1 pats_pt) (\ps.
                   OPTION_BIND (oHD ps) (\p1.
                   OPTION_BIND
                     ((ptree_Expr:MMLnonT->mlptree->exp option) nE body_pt)
                     (\body0.
                   SOME (fname,dePat p1 (ITLIST mkFun (TL ps) body0)))))))
            | _ -> NONE
          else NONE`;
   `(ptree_LetDecs:mlptree->
       (((pat#exp)+(mlstring#mlstring#exp)list)list)option) ast =
      match ast with
        Lf _ -> NONE
      | Nd (nt',_) args ->
          if ~(nt' = INL nLetDecs) then NONE
          else
            match args with
              [] -> SOME []
            | [ld_pt; lds_pt] ->
                if tokcheck ld_pt SemicolonT then ptree_LetDecs lds_pt
                else
                  OPTION_BIND
                    ((ptree_LetDec:mlptree->
                        ((pat#exp)+(mlstring#mlstring#exp)list)option) ld_pt)
                    (\ld.
                  OPTION_BIND (ptree_LetDecs lds_pt) (\lds.
                  SOME (CONS ld lds)))
            | _ -> NONE`;
   `(ptree_LetDec:mlptree->((pat#exp)+(mlstring#mlstring#exp)list)option)
      ast =
      match ast with
        Lf _ -> NONE
      | Nd (nt',_) args ->
          if ~(nt' = INL nLetDec) then NONE
          else
            match args with
              [funtok; andfdecls_pt] ->
                OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck funtok FunT))
                  (OPTION_BIND
                     ((ptree_AndFDecls:mlptree->
                         ((mlstring#mlstring#exp)list)option) andfdecls_pt)
                     (\fds. SOME (INR fds)))
            | [valtok; p_pt; eqtok; e_pt] ->
                OPTION_IGNORE_BIND
                  (OPTION_GUARD (tokcheckl [valtok; eqtok] [ValT; EqualsT]))
                  (OPTION_BIND (ptree_Pattern nPattern p_pt) (\p.
                   OPTION_BIND
                     ((ptree_Expr:MMLnonT->mlptree->exp option) nE e_pt) (\e.
                   SOME (INL (p,e)))))
            | _ -> NONE`;
   `(ptree_PEs:mlptree->((pat#exp)list)option) (Lf x) = NONE`;
   `(ptree_PEs:mlptree->((pat#exp)list)option) (Nd (nt',loc) subs) =
      if ~(nt' = INL nPEs) then NONE
      else
        match subs with
          [pattern_pt; arrow_pt; pe_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck arrow_pt DarrowT))
              (OPTION_BIND (ptree_Pattern nPattern pattern_pt) (\pat.
               OPTION_BIND
                 ((ptree_PE:mlptree->(exp#(pat#exp)list)option) pe_pt) (\p.
               match p with
                 (e,pes) -> SOME (CONS (pat,e) pes))))
        | _ -> NONE`;
   `(ptree_PE:mlptree->(exp#(pat#exp)list)option) (Lf x) = NONE`;
   `(ptree_PE:mlptree->(exp#(pat#exp)list)option) (Nd (nt',loc) subs) =
      if ~(nt' = INL nPE) then NONE
      else
        match subs with
          [eorraise_pt; pesfx_pt] ->
            OPTION_CHOICE
              (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck eorraise_pt RaiseT))
                 (OPTION_BIND (ptree_PE pesfx_pt) (\p.
                  match p with (e,pes) -> SOME (Raise e,pes))))
              (OPTION_BIND
                 ((ptree_Expr:MMLnonT->mlptree->exp option) nElogicOR
                    eorraise_pt) (\e.
               OPTION_BIND
                 ((ptree_PEsfx:mlptree->(bool#(pat#exp)list)option) pesfx_pt)
                 (\p.
               match p with
                 (handlep,pes) ->
                   SOME (if handlep then (Handle e pes,[]) else (e,pes)))))
        | [fncase_tok; epat_pt; arrowof_tok; last_pt] ->
            OPTION_CHOICE
              (OPTION_IGNORE_BIND
                 (OPTION_GUARD
                    (tokcheckl [fncase_tok; arrowof_tok] [FnT; DarrowT]))
                 (OPTION_BIND (ptree_Pattern nPattern epat_pt) (\pat.
                  OPTION_BIND (ptree_Expr nE last_pt) (\e.
                  SOME (mkFun pat e,[])))))
              (OPTION_IGNORE_BIND
                 (OPTION_GUARD
                    (tokcheckl [fncase_tok; arrowof_tok] [CaseT; OfT]))
                 (OPTION_BIND (ptree_Expr nE epat_pt) (\e.
                  OPTION_BIND ((ptree_PEs:mlptree->((pat#exp)list)option) last_pt)
                    (\pes. SOME (Mat e pes,[])))))
        | [iftok; ge_pt; thentok; then_pt; elsetok; else_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD
                 (tokcheckl [iftok; thentok; elsetok] [IfT; ThenT; ElseT]))
              (OPTION_BIND (ptree_Expr nE ge_pt) (\ge.
               OPTION_BIND (ptree_Expr nE then_pt) (\te.
               OPTION_BIND (ptree_PE else_pt) (\p.
               match p with (ee,rest) -> SOME (If ge te ee,rest)))))
        | _ -> NONE`;
   `(ptree_PEsfx:mlptree->(bool#(pat#exp)list)option) (Lf x) = NONE`;
   `(ptree_PEsfx:mlptree->(bool#(pat#exp)list)option) (Nd (nt',loc) subs) =
      if ~(nt' = INL nPEsfx) then NONE
      else
        match subs with
          [] -> SOME (F,[])
        | [handlebar_tok; pes_pt] ->
            OPTION_CHOICE
              (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck handlebar_tok HandleT))
                 (OPTION_BIND ((ptree_PEs:mlptree->((pat#exp)list)option) pes_pt)
                    (\pes. SOME (T,pes))))
              (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck handlebar_tok BarT))
                 (OPTION_BIND (ptree_PEs pes_pt) (\pes. SOME (F,pes))))
        | _ -> NONE`;
   `(ptree_Eseq:mlptree->(exp list)option) (Lf x) = NONE`;
   `(ptree_Eseq:mlptree->(exp list)option) (Nd (nt',loc) subs) =
      if ~(nt' = INL nEseq) then NONE
      else
        match subs with
          [single] ->
            OPTION_BIND ((ptree_Expr:MMLnonT->mlptree->exp option) nE single)
              (\e. SOME [e])
        | [e_pt; semi; seq_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck semi SemicolonT))
              (OPTION_BIND (ptree_Expr nE e_pt) (\e.
               OPTION_BIND (ptree_Eseq seq_pt) (\seq'.
               SOME (CONS e seq'))))
        | _ -> NONE`];;

let ptree_Expr_ind = cake_ind "ptree_Expr";;

let dumb1 = prove
 (`!(p:A) q (t:B) e. (if p = q then t else e) = (if q = p then t else e)`,
  REWRITE_TAC[EQ_SYM_EQ]);;

let dumb2 = prove
 (`!gd (t:A option). (if gd then t else NONE) = OPTION_IGNORE_BIND (OPTION_GUARD gd) t`,
  GEN_TAC THEN BOOL_CASES_TAC `gd:bool` THEN
  REWRITE_TAC[OPTION_IGNORE_BIND_DEF; OPTION_GUARD_DEF; OPTION_BIND_DEF]);;

(* HOL4: ptree_Expr_def' (local: ptree_Expr_def rewritten by dumb1, SRULE  *)
(* and dumb2) and ptree_Expr_pevaled (computeLib only, made by ML partial   *)
(* evaluation) are not ported.                                              *)

let ptree_Expr_others =
  end_itlist CONJ (snd(chop_list 2 (CONJUNCTS ptree_Expr_def)));;

let ptree_StructName_def = cake_def
  `(ptree_StructName (Lf (_:(token,MMLnonT)symbol#C)) = NONE) /\
   (ptree_StructName (Nd (nm:(MMLnonT+num)#C) args) =
      if ~(FST nm = INL nStructName) then NONE
      else
        match args with
          [pt] -> OPTION_BIND (OPTION_BIND (destLf pt) destTOK) destAlphaT
        | _ -> NONE)`;;

let ptree_OptTypEqn_def = cake_def
  `(ptree_OptTypEqn (Lf (_:(token,MMLnonT)symbol#C)) =
      NONE:(ast_t option)option) /\
   (ptree_OptTypEqn (Nd (nt':(MMLnonT+num)#C) args) =
      if ~(FST nt' = INL nOptTypEqn) then NONE
      else
        match args with
          [] -> SOME NONE
        | [eqtok; typ_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck eqtok EqualsT))
              (OPTION_BIND (ptree_Type nType typ_pt) (\typ.
               SOME (SOME typ)))
        | _ -> NONE)`;;

(* the commented-out results of HOL4 (Stype td, Sexn nm tys, ...) are not   *)
(* computed: every clause returns SOME one, as in HOL4                      *)

let ptree_SpecLine_def = cake_def
  `(ptree_SpecLine (Lf (_:(token,MMLnonT)symbol#locs)) = NONE) /\
   (ptree_SpecLine (Nd (nt':(MMLnonT+num)#locs) args) =
      if ~(FST nt' = INL nSpecLine) then NONE
      else
        match args with
          [td_pt] -> OPTION_BIND (ptree_TypeDec td_pt) (\td. SOME one)
        | [exntok; dcon_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck exntok ExceptionT))
              (OPTION_BIND (ptree_Dconstructor dcon_pt) (\p.
               match p with (nm,tys) -> SOME one))
        | [typetok; tynm_pt; opteqn_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck typetok TypeT))
              (OPTION_BIND (ptree_TypeName tynm_pt) (\p.
               match p with
                 (vs,nm) ->
                   OPTION_BIND (ptree_OptTypEqn opteqn_pt) (\opteqn.
                   SOME one)))
        | [valtok; vname_pt; coltok; type_pt] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [valtok; coltok] [ValT; ColonT]))
              (OPTION_BIND (ptree_V vname_pt) (\vname.
               OPTION_BIND (ptree_Type nType type_pt) (\ty.
               SOME one)))
        | _ -> NONE)`;;

let ptree_SpeclineList_def = cake_def_wf
  `measure (\pt:mlptree.
              parsetree_size (\x:token. 0) (\x:MMLnonT. 0) (\x:locs. 0) pt)`
  TERM_TAC
  `(ptree_SpeclineList (Lf (_:(token,MMLnonT)symbol#locs)) = NONE) /\
   (ptree_SpeclineList (Nd (nt':(MMLnonT+num)#locs) args) =
      if ~(FST nt' = INL nSpecLineList) then NONE
      else
        match args with
          [] -> SOME one
        | [sl_pt; sll_pt] ->
            if tokcheck sl_pt SemicolonT then ptree_SpeclineList sll_pt
            else
              OPTION_BIND (ptree_SpecLine sl_pt) (\sl.
              OPTION_BIND (ptree_SpeclineList sll_pt) (\sll.
              SOME one))
        | _ -> NONE)`;;

let ptree_SpeclineList_ind = cake_ind "ptree_SpeclineList";;

let ptree_SignatureValue_def = cake_def
  `(ptree_SignatureValue (Lf (_:(token,MMLnonT)symbol#locs)) = NONE) /\
   (ptree_SignatureValue (Nd (nt':(MMLnonT+num)#locs) args) =
      if ~(FST nt' = INL nSignatureValue) then NONE
      else
        match args with
          [sigtok; sll_pt; endtok] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD (tokcheckl [sigtok; endtok] [SigT; EndT]))
              (ptree_SpeclineList sll_pt)
        | _ -> NONE)`;;

let ptree_Decl_def = cake_def_wf_clauses
  (PTREEAUX_measure [`:mlptree`; `:mlptree`; `:mlptree`])
  TERM_TAC
  [`(ptree_Decl:mlptree->dec option) pt =
      match pt with
        Lf _ -> NONE
      | Nd (nt',locs) args ->
          if ~(nt' = INL nDecl) then NONE
          else
            match args with
              [dt] ->
                OPTION_CHOICE
                 (OPTION_CHOICE
                   (OPTION_BIND (ptree_TypeDec dt) (\tydec.
                    SOME (Dtype locs tydec)))
                   (ptree_TypeAbbrevDec dt))
                 ((ptree_Structure:mlptree->dec option) dt)
            | [funtok; fdecls] ->
                OPTION_CHOICE
                  (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck funtok FunT))
                     (OPTION_BIND (ptree_AndFDecls fdecls) (\fdecs.
                      SOME (Dletrec locs fdecs))))
                  (OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck funtok ExceptionT))
                     (OPTION_BIND (ptree_Dconstructor fdecls) (\p.
                      match p with (enm,etys) -> SOME (Dexn locs enm etys))))
            | [valtok; patpt; eqtok; ept] ->
                OPTION_IGNORE_BIND
                  (OPTION_GUARD (tokcheckl [valtok; eqtok] [ValT; EqualsT]))
                  (OPTION_BIND (ptree_Pattern nPattern patpt) (\pat.
                   OPTION_BIND (ptree_Expr nE ept) (\e.
                   SOME (Dlet locs pat e))))
            | [localtok; decls1_pt; intok; decls2_pt; endtok] ->
                OPTION_IGNORE_BIND
                  (OPTION_GUARD
                     (tokcheckl [localtok; intok; endtok] [LocalT; InT; EndT]))
                  (OPTION_BIND
                     ((ptree_Decls:mlptree->(dec list)option) decls1_pt)
                     (\decls1.
                   OPTION_BIND (ptree_Decls decls2_pt) (\decls2.
                   SOME (Dlocal decls1 decls2))))
            | _ -> NONE`;
   `(ptree_Decls:mlptree->(dec list)option) (Lf _) = NONE`;
   `(ptree_Decls:mlptree->(dec list)option) (Nd (nt',_) args) =
      if ~(nt' = INL nDecls) then NONE
      else
        match args with
          [] -> SOME []
        | [d_pt; ds_pt] ->
            if tokcheck d_pt SemicolonT then ptree_Decls ds_pt
            else
              OPTION_BIND ((ptree_Decl:mlptree->dec option) d_pt) (\d.
              OPTION_BIND (ptree_Decls ds_pt) (\ds.
              SOME (CONS d ds)))
        | _ -> NONE`;
   `(ptree_Structure:mlptree->dec option) (Lf _) = NONE`;
   `(ptree_Structure:mlptree->dec option) (Nd nt' args) =
      if ~(FST nt' = INL nStructure) then NONE
      else
        match args with
          [structuretok; sname_pt; asc_opt; eqtok; structtok; ds_pt; endtok] ->
            OPTION_IGNORE_BIND
              (OPTION_GUARD
                 (tokcheckl [structtok; structuretok; eqtok; endtok]
                            [StructT; StructureT; EqualsT; EndT]))
              (OPTION_BIND (ptree_StructName sname_pt) (\sname.
               OPTION_BIND
                 (match asc_opt with
                    Lf _ -> NONE
                  | Nd nt'' args' ->
                      if ~(FST nt'' = INL nOptionalSignatureAscription) then NONE
                      else
                        match args' with
                          [] -> SOME NONE
                        | [sealtok; sig_pt] ->
                            OPTION_IGNORE_BIND
                              (OPTION_GUARD (tokcheck sealtok SealT))
                              (OPTION_BIND (ptree_SignatureValue sig_pt)
                                 (\sigv. SOME (SOME sigv)))
                        | _ -> NONE) (\asc.
               OPTION_BIND ((ptree_Decls:mlptree->(dec list)option) ds_pt)
                 (\ds. SOME (Dmod sname ds)))))
        | _ -> NONE`];;

let ptree_Decl_ind = cake_ind "ptree_Decl";;

let ptree_TopLevelDecs_def = cake_def_wf_clauses
  (PTREEAUX_measure [`:mlptree`; `:mlptree`])
  TERM_TAC
  [`(ptree_TopLevelDecs:mlptree->(dec list)option) (Lf _) = NONE`;
   `(ptree_TopLevelDecs:mlptree->(dec list)option) (Nd nt' args) =
      if ~(FST nt' = INL nTopLevelDecs) then NONE
      else
        match args with
          [] -> SOME []
        | [td_pt; tds_pt] ->
            if tokcheck td_pt SemicolonT then ptree_TopLevelDecs tds_pt
            else
              OPTION_BIND (ptree_Decl td_pt) (\td.
              OPTION_BIND
                ((ptree_NonETopLevelDecs:mlptree->(dec list)option) tds_pt)
                (\tds. SOME (CONS td tds)))
        | [e_pt; semitok; tds_pt] ->
            OPTION_IGNORE_BIND (OPTION_GUARD (tokcheck semitok SemicolonT))
              (OPTION_BIND (ptree_Expr nE e_pt) (\e.
               OPTION_BIND (ptree_TopLevelDecs tds_pt) (\tds.
               SOME (CONS (Dlet (SND nt') (Pvar (implode "it")) e) tds))))
        | _ -> NONE`;
   `(ptree_NonETopLevelDecs:mlptree->(dec list)option) (Lf _) = NONE`;
   `(ptree_NonETopLevelDecs:mlptree->(dec list)option) (Nd nt' args) =
      if ~(FST nt' = INL nNonETopLevelDecs) then NONE
      else
        match args with
          [] -> SOME []
        | [pt1; pt2] ->
            if tokcheck pt1 SemicolonT
            then (ptree_TopLevelDecs:mlptree->(dec list)option) pt2
            else
              OPTION_BIND (ptree_Decl pt1) (\td.
              OPTION_BIND (ptree_NonETopLevelDecs pt2) (\tds.
              SOME (CONS td tds)))
        | _ -> NONE`];;

let ptree_TopLevelDecs_ind = cake_ind "ptree_TopLevelDecs";;


(* the rule for parsetree_CASE was for this file only *)

cake_admissible_rules := PTREEAUX_saved_admissible_rules;;
