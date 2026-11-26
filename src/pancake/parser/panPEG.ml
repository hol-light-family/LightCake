(* ========================================================================= *)
(* panPEG: port of HOL4 pancake/parser/panPEGScript.sml (CakeML v3479).      *)
(* The PEG parser for the Pancake language (inspired by the Spark ADA        *)
(* development), with a proof that the PEG is well-formed.                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: choicel, pegf, seql, try, parse,           *)
(*   frange_image, peg0_pegf, peg0_seql, peg0_choicel and PEG_wellformed are *)
(*   panPEG_choicel, ... (cmlPEG and semantics have the bare names); the     *)
(*   token constructors of panLexer.ml (panLexer_CommaT, ...).               *)
(* - FOLDR f e l is ITLIST f l e, (++) is APPEND, f $ x is f x, an mlstring  *)
(*   literal is implode of a string literal; the record literal of           *)
(*   pancake_peg is peg_REC with the fields start, anyEOF, tokFALSE, tokEOF, *)
(*   notFAIL, rules; HOL4 pancake_peg with start := mknt FunNT is            *)
(*   peg_start_fupd (K (mknt FunNT)) pancake_peg; G.rules ' n is            *)
(*   FAPPLY (peg_rules G) n; the pegresult constructor Success is            *)
(*   peg_Success (peg.ml).                                                   *)
(* - HOL4 computes FDOM_pancake_peg, pancake_peg_applied,                    *)
(*   pancake_peg_applied', pancake_exec_thm, the peg0_X and peg1_X theorems, *)
(*   pancake_wfpeg_thm and pancake_wfpeg_FunNT_thm with ML code; the port    *)
(*   proves the same statements with conversions and rewriting, in the same *)
(*   order (as cmlPEG.ml does for CakeML's PEG).                             *)
(* - peg0_keep_nat states peg0 G keep_int = F, as in HOL4 (a typo there: the *)
(*   statement of peg0_keep_int).                                            *)
(* - Helpers that are not HOL4 names have the prefix PPARSEAUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/grammar.ml";;
needs "hol4/peg.ml";;
needs "hol4/pegexec.ml";;
needs "pancake/parser/panLexer.ml";;

type_invention_error := true;;

let pancakeNT_INDUCT,pancakeNT_RECURSION = cake_type
  "pancakeNT = TopDecListNT | StructNameNT | FieldNameListNT
             | FunNT | ProgNT | BlockNT | StmtNT | ExpNT
             | DecNT | GlobalDecNT | AssignNT | StoreNT | StoreByteNT
             | Store32NT
             | IfNT | WhileNT | CallNT | RetNT | HandleNT
             | ExtCallNT | ThrowNT | ReturnNT
             | DecCallNT | RetCallNT
             | ArgListNT
             | ParamListNT
             | EBoolAndNT | EEqNT | ECmpNT
             | ELoadNT | ELoadByteNT | ELoad32NT
             | EXorNT | EOrNT | EAndNT
             | EShiftNT | EAddNT | EMulNT | ENotNT | EFieldNT | EBaseNT
             | RawStructNT | NmdStructNT | NmdFieldListNT | NmdFieldNT
             | ShapedIdentNT | ShapeNT | ShapeCombNT
             | EqOpsNT | CmpOpsNT | ShiftOpsNT | AddOpsNT | MulOpsNT
             | SharedLoadNT | SharedLoadByteNT | SharedLoad16NT
             | SharedLoad32NT
             | SharedStoreNT | SharedStoreByteNT | SharedStore16NT
             | SharedStore32NT
             | ExnDecNT";;

let mknt_def = cake_def
  `mknt (ntsym:pancakeNT) = peg_nt (INL ntsym) I:(A,pancakeNT,C,E)pegsym`;;

let mkleaf_def = cake_def
  `mkleaf (t:A#C) = [grammar_Lf (grammar_TOK (FST t),SND t):(A,B,C)parsetree]`;;

let mknode_def = cake_def
  `mknode (x:B) (ts:((A,B,locs)parsetree)list) =
     grammar_Nd (INL x,ptree_list_loc ts) ts`;;

(* Make a sub-parsetree with a single child *)

let mksubtree_def = cake_def
  `mksubtree (x:B) (ts:((A,B,locs)parsetree)list) = [mknode x ts]`;;

(* Accept a token without storing it. *)

let consume_tok_def = cake_def
  `consume_tok (t:A) = peg_tok ((=) t) (\t:A#locs. []):(A,B,(C)list,E)pegsym`;;

(* Accept and store a token in the parse tree. *)

let keep_tok_def = cake_def
  `keep_tok (t:A) =
     peg_tok ((=) t) mkleaf:(A,B,((A,D,locs)parsetree)list,E)pegsym`;;

(* Similar functions for keyword tokens *)

let consume_kw_def = cake_def
  `consume_kw k = consume_tok (KeywordT k):(panLexer_token,B,(C)list,E)pegsym`;;

let keep_kw_def = cake_def
  `keep_kw k =
     keep_tok (KeywordT k)
       :(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)pegsym`;;

let keep_ident_def = cake_def
  `keep_ident =
     peg_tok (\t. match t with IdentT _ -> T | _ -> F) mkleaf
       :(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)pegsym`;;

let keep_annot_def = cake_def
  `keep_annot =
     peg_tok (\t. match t with AnnotCommentT _ -> T | _ -> F) mkleaf
       :(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)pegsym`;;

let keep_ffi_ident_def = cake_def
  `keep_ffi_ident =
     peg_tok (\t. match t with ForeignIdent _ -> T | _ -> F) mkleaf
       :(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)pegsym`;;

let keep_int_def = cake_def
  `keep_int =
     peg_tok (\t. match t with panLexer_IntT _ -> T | _ -> F) mkleaf
       :(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)pegsym`;;

let keep_nat_def = cake_def
  `keep_nat =
     peg_tok (\t. match t with
                panLexer_IntT n -> if n >= &0 then T else F
              | _ -> F) mkleaf
       :(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)pegsym`;;

let extract_sum_def = cake_def
  `(extract_sum (INL (x:A)) = x) /\
   (extract_sum (INR (x:A)) = x)`;;

let panPEG_choicel_def = cake_def
  `(panPEG_choicel [] = peg_not (empty []) []:(A,B,(C)list,E)pegsym) /\
   (panPEG_choicel (CONS h t) = choice h (panPEG_choicel t) extract_sum)`;;

let panPEG_pegf_def = cake_def
  `panPEG_pegf (s:(A,B,(C)list,E)pegsym) (f:(C)list->(C)list) =
     peg_seq s (empty []) (\l1 l2. f l1)`;;

let panPEG_seql_def = cake_def
  `panPEG_seql (l:((A,B,(C)list,E)pegsym)list) f =
     panPEG_pegf (ITLIST (\p acc. peg_seq p acc APPEND) l (empty [])) f`;;

let panPEG_try_def = cake_def
  `panPEG_try (s:(A,B,(C)list,E)pegsym) = panPEG_choicel [s; empty []]`;;

(* like try, but stores the given token without consumption on failure *)

let try_default_def = cake_def
  `try_default (s:(A,B,((A,D,locs)parsetree)list,E)pegsym) (t:A) =
     panPEG_choicel [s; empty (mkleaf (t,unknown_loc))]`;;

(* add a single Skip in place of an empty Prog: generates unnecessary Skips *)
(* if used without caution                                                   *)

let try_ProgNT_def = cake_def
  `try_ProgNT =
     panPEG_choicel [
       panPEG_seql [consume_tok RCurT;
                    empty (mkleaf (KeywordT SkipK,unknown_loc))]
                   (mksubtree ProgNT);
       mknt ProgNT]
       :(panLexer_token,pancakeNT,
         ((panLexer_token,pancakeNT,locs)parsetree)list,E)pegsym`;;

let pancake_peg_def = cake_def
 `pancake_peg:(panLexer_token,pancakeNT,
               ((panLexer_token,pancakeNT,locs)parsetree)list,string)peg =
  peg_REC (mknt TopDecListNT)
    "Didn't expect an EOF"
    "Failed to see expected token"
    "Failed to see expected token; saw EOF instead"
    "Not combinator failed"
    (FEMPTY |++ [
      (INL TopDecListNT,
       panPEG_choicel
         [peg_not (peg_any (combin_K (mksubtree TopDecListNT []))) (mksubtree TopDecListNT []);
          panPEG_seql [mknt FunNT; mknt TopDecListNT] (mksubtree TopDecListNT);
          panPEG_seql [mknt GlobalDecNT; mknt TopDecListNT]
                      (mksubtree TopDecListNT);
          panPEG_seql [mknt ExnDecNT; mknt TopDecListNT]
                      (mksubtree TopDecListNT);
          panPEG_seql [mknt StructNameNT; mknt TopDecListNT]
                      (mksubtree TopDecListNT);
          panPEG_seql [keep_annot; mknt TopDecListNT]
                      (mksubtree TopDecListNT)]);
      (INL StructNameNT,
       panPEG_seql [consume_kw NamedK;
                    keep_ident;
                    consume_tok LCurT;
                    mknt FieldNameListNT;
                    consume_tok RCurT]
                   (mksubtree StructNameNT));
      (INL FieldNameListNT,
       panPEG_seql [mknt ShapedIdentNT;
                    peg_rpt (panPEG_seql [consume_tok panLexer_CommaT;
                                      mknt ShapedIdentNT] I)
                        FLAT]
                   (mksubtree FieldNameListNT));
      (INL FunNT,
       panPEG_seql [try_default (keep_kw InlineK) NoinlineT;
                    try_default (keep_kw ExportK) StaticT;
                    consume_kw FunK;
                    mknt ShapedIdentNT;
                    consume_tok LParT;
                    panPEG_choicel
                      [mknt ParamListNT;
                       empty (mksubtree ParamListNT [])];
                    consume_tok RParT;
                    consume_tok LCurT;
                    try_ProgNT]
                   (mksubtree FunNT));
      (INL ParamListNT,
       panPEG_seql [mknt ShapedIdentNT;
                    peg_rpt (panPEG_seql [consume_tok panLexer_CommaT;
                                      mknt ShapedIdentNT] I)
                        FLAT]
                   (mksubtree ParamListNT));
      (INL ProgNT,
       panPEG_choicel
         [panPEG_seql [mknt BlockNT; mknt ProgNT] (mksubtree ProgNT);
          panPEG_seql [mknt DecCallNT; try_ProgNT] (mksubtree DecCallNT);
          panPEG_seql [mknt DecNT; try_ProgNT] (mksubtree DecNT);
          panPEG_seql [keep_annot; mknt ProgNT] (mksubtree ProgNT);
          panPEG_seql [mknt StmtNT; consume_tok SemiT; mknt ProgNT]
                      (mksubtree ProgNT);
          consume_tok RCurT]);
      (INL BlockNT,
       panPEG_choicel [mknt HandleNT;
                       mknt IfNT;
                       mknt WhileNT]);
      (INL StmtNT,
       panPEG_choicel [keep_kw SkipK;
                       mknt CallNT;
                       mknt AssignNT; mknt StoreNT;
                       mknt StoreByteNT;
                       mknt Store32NT;
                       mknt SharedLoadByteNT;
                       mknt SharedLoad16NT;
                       mknt SharedLoad32NT;
                       mknt SharedLoadNT;
                       mknt SharedStoreByteNT;
                       mknt SharedStore16NT;
                       mknt SharedStore32NT;
                       mknt SharedStoreNT;
                       keep_kw BrK; keep_kw ContK;
                       mknt ExtCallNT;
                       mknt ThrowNT; mknt RetCallNT; mknt ReturnNT;
                       keep_kw TicK;
                       panPEG_seql [consume_tok LCurT; try_ProgNT] I]);
      (INL DecCallNT,
       panPEG_seql [consume_kw VarK; mknt ShapedIdentNT; consume_tok AssignT;
                    keep_ident;
                    consume_tok LParT; panPEG_try (mknt ArgListNT);
                    consume_tok RParT; consume_tok SemiT]
                   (mksubtree DecCallNT));
      (INL DecNT,
       panPEG_seql [consume_kw VarK; mknt ShapedIdentNT;
                    consume_tok AssignT; mknt ExpNT;
                    consume_tok SemiT]
                   (mksubtree DecNT));
      (INL GlobalDecNT,
       panPEG_seql [consume_kw VarK; mknt ShapedIdentNT;
                    consume_tok AssignT; mknt ExpNT;
                    consume_tok SemiT]
                   (mksubtree GlobalDecNT));
      (INL ExnDecNT,
       panPEG_seql [consume_kw ExceptionK;
                    keep_ident;
                    consume_tok panLexer_ColonT;
                    mknt ShapeNT;
                    consume_tok SemiT]
                   (mksubtree ExnDecNT));
      (INL AssignNT,
       panPEG_seql [keep_ident; consume_tok AssignT;
                    mknt ExpNT] (mksubtree AssignNT));
      (INL StoreNT,
       panPEG_seql [consume_kw StK; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree StoreNT));
      (INL StoreByteNT,
       panPEG_seql [consume_kw St8K; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree StoreByteNT));
      (INL Store32NT,
       panPEG_seql [consume_kw St32K; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree Store32NT));
      (INL IfNT,
       panPEG_seql [consume_kw IfK; mknt ExpNT; consume_tok LCurT;
                    try_ProgNT;
                    try_default (panPEG_seql [consume_kw ElseK;
                                              consume_tok LCurT;
                                              try_ProgNT] I)
                                (KeywordT SkipK)]
                   (mksubtree IfNT));
      (INL WhileNT,
       panPEG_seql [consume_kw WhileK; mknt ExpNT;
                    consume_tok LCurT; try_ProgNT] (mksubtree WhileNT));
      (INL CallNT,
       panPEG_seql [try_default (panPEG_choicel [keep_kw RetK; mknt RetNT])
                                NotT;
                    keep_ident;
                    consume_tok LParT; try_default (mknt ArgListNT) NotT;
                    consume_tok RParT]
                   (mksubtree CallNT));
      (INL RetNT,
       panPEG_seql [keep_ident; consume_tok AssignT]
                   (mksubtree RetNT));
      (INL HandleNT,
       panPEG_seql [consume_kw TryK;
                    try_default (mknt RetNT) NotT;
                    keep_ident;
                    consume_tok LParT; try_default (mknt ArgListNT) NotT;
                    consume_tok RParT;
                    consume_kw CatchK;
                    keep_ident;
                    consume_tok panLexer_ArrowT;
                    keep_ident;
                    consume_tok LCurT; try_ProgNT]
                   (mksubtree HandleNT));
      (INL ExtCallNT,
       panPEG_seql [keep_ffi_ident;
                    consume_tok LParT; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT;
                    consume_tok RParT]
                   (mksubtree ExtCallNT));
      (INL ThrowNT,
       panPEG_seql [consume_kw ThrowK; keep_ident; mknt ExpNT]
                   (mksubtree ThrowNT));
      (INL RetCallNT,
       panPEG_seql [consume_kw RetK;
                    keep_ident;
                    consume_tok LParT; panPEG_try (mknt ArgListNT);
                    consume_tok RParT]
                   (mksubtree RetCallNT));
      (INL ReturnNT,
       panPEG_seql [consume_kw RetK; mknt ExpNT]
                   (mksubtree ReturnNT));
      (INL ArgListNT,
       panPEG_seql [mknt ExpNT;
                    peg_rpt (panPEG_seql [consume_tok panLexer_CommaT;
                                      mknt ExpNT] I)
                        FLAT]
                   (mksubtree ArgListNT));
      (INL ExpNT,
       panPEG_seql [mknt EBoolAndNT;
                    peg_rpt (panPEG_seql [consume_tok BoolOrT; mknt EBoolAndNT] I)
                        FLAT]
                   (mksubtree ExpNT));
      (INL EBoolAndNT,
       panPEG_seql [mknt EEqNT;
                    peg_rpt (panPEG_seql [consume_tok BoolAndT; mknt EEqNT] I)
                        FLAT]
                   (mksubtree EBoolAndNT));
      (INL EEqNT,
       panPEG_seql [mknt ECmpNT;
                    panPEG_try (panPEG_seql [mknt EqOpsNT; mknt ECmpNT] I)]
                   (mksubtree EEqNT));
      (INL ECmpNT,
       panPEG_seql [mknt ELoadNT;
                    panPEG_try (panPEG_seql [mknt CmpOpsNT; mknt ELoadNT] I)]
                   (mksubtree ECmpNT));
      (INL ELoadNT,
       panPEG_choicel [panPEG_seql [consume_kw LdsK; mknt ShapeNT;
                                    mknt ELoadByteNT]
                                   (mksubtree ELoadNT);
                       mknt ELoadByteNT]);
      (INL ELoadByteNT,
       panPEG_choicel [panPEG_seql [consume_kw Ld8K; mknt ELoad32NT]
                                   (mksubtree ELoadByteNT);
                       mknt ELoad32NT]);
      (INL ELoad32NT,
       panPEG_choicel [panPEG_seql [consume_kw Ld32K; mknt EOrNT]
                                   (mksubtree ELoad32NT);
                       mknt EOrNT]);
      (INL EOrNT,
       panPEG_seql [mknt EXorNT;
                    peg_rpt (panPEG_seql [keep_tok OrT; mknt EXorNT] I)
                        FLAT]
                   (mksubtree EOrNT));
      (INL EXorNT,
       panPEG_seql [mknt EAndNT;
                    peg_rpt (panPEG_seql [keep_tok XorT; mknt EAndNT] I)
                        FLAT]
                   (mksubtree EXorNT));
      (INL EAndNT,
       panPEG_seql [mknt EShiftNT;
                    peg_rpt (panPEG_seql [keep_tok panLexer_AndT; mknt EShiftNT] I)
                        FLAT]
                   (mksubtree EAndNT));
      (INL EShiftNT,
       panPEG_seql [mknt EAddNT;
                    peg_rpt (panPEG_seql [mknt ShiftOpsNT; mknt EAddNT] I)
                        FLAT]
                   (mksubtree EShiftNT));
      (INL EAddNT,
       panPEG_seql [mknt EMulNT;
                    peg_rpt (panPEG_seql [mknt AddOpsNT; mknt EMulNT] I)
                        FLAT]
                   (mksubtree EAddNT));
      (INL EMulNT,
       panPEG_seql [mknt ENotNT;
                    peg_rpt (panPEG_seql [mknt MulOpsNT; mknt ENotNT] I) FLAT]
                   (mksubtree EMulNT));
      (INL ENotNT,
       panPEG_seql [panPEG_try (keep_tok NotT); mknt EFieldNT]
                   (mksubtree ENotNT));
      (INL EFieldNT,
       panPEG_seql [mknt EBaseNT;
                    peg_rpt (panPEG_seql [consume_tok DotT;
                                      panPEG_choicel [keep_nat; keep_ident]
                                     ] I)
                        FLAT]
                   (mksubtree EFieldNT));
      (INL EBaseNT,
       panPEG_choicel [panPEG_seql [consume_tok LParT;
                                    mknt ExpNT;
                                    consume_tok RParT] I;
                       keep_kw TrueK; keep_kw FalseK;
                       mknt RawStructNT; mknt NmdStructNT;
                       keep_kw BaseK; keep_kw BiwK; keep_kw TopK;
                       keep_int; keep_ident
                      ]);
      (INL RawStructNT,
       panPEG_seql [consume_tok LessT; mknt ArgListNT;
                    consume_tok GreaterT]
                   (mksubtree RawStructNT));
      (INL NmdStructNT,
       panPEG_seql [keep_ident; consume_tok LessT; mknt NmdFieldListNT;
                    consume_tok GreaterT]
                   (mksubtree NmdStructNT));
      (INL NmdFieldListNT,
       panPEG_seql [mknt NmdFieldNT;
                    peg_rpt (panPEG_seql [consume_tok panLexer_CommaT;
                                      mknt NmdFieldNT] I)
                        FLAT]
                   (mksubtree NmdFieldListNT));
      (INL NmdFieldNT,
       panPEG_seql [keep_ident;
                    consume_tok AssignT;
                    mknt ExpNT]
                   (mksubtree NmdFieldNT));
      (INL ShapedIdentNT,
       panPEG_choicel [panPEG_seql [mknt ShapeNT;
                                    keep_ident] I;
                       panPEG_seql [empty (mkleaf (DefaultShT,unknown_loc));
                                    keep_ident] I
                      ]);
      (INL ShapeNT,
       panPEG_choicel [keep_int;
                       panPEG_seql [consume_tok LCurT;
                                    mknt ShapeCombNT;
                                    consume_tok RCurT] I;
                       keep_ident
                      ]);
      (INL ShapeCombNT,
       panPEG_seql [mknt ShapeNT;
                    peg_rpt (peg_seq (consume_tok panLexer_CommaT)
                             (mknt ShapeNT) (flip combin_K)) FLAT]
                   (mksubtree ShapeCombNT));
      (INL EqOpsNT, panPEG_choicel [keep_tok EqT; keep_tok NeqT]);
      (INL CmpOpsNT,
       panPEG_choicel [keep_tok LessT; keep_tok GeqT; keep_tok GreaterT;
                       keep_tok LeqT;
                       keep_tok LowerT; keep_tok HigherT; keep_tok HigheqT;
                       keep_tok LoweqT]);
      (INL ShiftOpsNT,
       panPEG_choicel [keep_tok LslT; keep_tok LsrT;
                       keep_tok AsrT; keep_tok RorT]);
      (INL AddOpsNT, panPEG_choicel [keep_tok PlusT; keep_tok MinusT]);
      (INL MulOpsNT, keep_tok panLexer_StarT);
      (INL SharedLoadNT,
       panPEG_seql [consume_tok NotT; consume_kw LdwK; keep_ident;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedLoadNT));
      (INL SharedLoadByteNT,
       panPEG_seql [consume_tok NotT; consume_kw Ld8K; keep_ident;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedLoadByteNT));
      (INL SharedLoad16NT,
       panPEG_seql [consume_tok NotT; consume_kw Ld16K; keep_ident;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedLoad16NT));
      (INL SharedLoad32NT,
       panPEG_seql [consume_tok NotT; consume_kw Ld32K; keep_ident;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedLoad32NT));
      (INL SharedStoreNT,
       panPEG_seql [consume_tok NotT; consume_kw StwK; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedStoreNT));
      (INL SharedStoreByteNT,
       panPEG_seql [consume_tok NotT; consume_kw St8K; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedStoreByteNT));
      (INL SharedStore16NT,
       panPEG_seql [consume_tok NotT; consume_kw St16K; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedStore16NT));
      (INL SharedStore32NT,
       panPEG_seql [consume_tok NotT; consume_kw St32K; mknt ExpNT;
                    consume_tok panLexer_CommaT; mknt ExpNT]
                   (mksubtree SharedStore32NT))
      ])`;;

(* ------------------------------------------------------------------------- *)
(* The rules of pancake_peg, applied.  HOL4 computes FDOM_pancake_peg,       *)
(* pancake_peg_applied and pancake_peg_applied' with SIMP_CONV (srw_ss())    *)
(* and FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM; the port does the same with     *)
(* conversions (as cmlPEG does).  Equations between constructors of          *)
(* pancakeNT are decided by looking them up in a table of its distinctness  *)
(* theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

let PPARSEAUX_nt_eq_tbl =
  let tbl = Hashtbl.create 4000 in
  do_list (fun th ->
      let l,r = dest_eq(dest_neg(concl th)) in
      let a = fst(dest_const l) and b = fst(dest_const r) in
      Hashtbl.replace tbl (a,b) (EQF_INTRO th);
      Hashtbl.replace tbl (b,a) (EQF_INTRO (GSYM th)))
    (CONJUNCTS (distinctness "pancakeNT"));
  tbl;;

let PPARSEAUX_NT_EQ_CONV tm =
  let l,r = dest_eq tm in
  if l = r then EQT_INTRO(REFL l)
  else Hashtbl.find PPARSEAUX_nt_eq_tbl (fst(dest_const l),fst(dest_const r));;

let PPARSEAUX_INL_EQ_CONV =
  REWR_CONV(CONJUNCT1(injectivity "sum")) THENC PPARSEAUX_NT_EQ_CONV;;

let rec PPARSEAUX_FUPDATE_LIST_CONV tm =
  ((REWR_CONV FMAPAUX_FUL_CONS THENC PPARSEAUX_FUPDATE_LIST_CONV) ORELSEC
   REWR_CONV FMAPAUX_FUL_NIL) tm;;

(* peg_rules pancake_peg = FEMPTY |+ (INL TopDecListNT,..) |+ ... *)

let PPARSEAUX_rules =
  (RAND_CONV (REWR_CONV pancake_peg_def) THENC
   REWR_CONV (el 5 (CONJUNCTS (record_info "peg").ri_accessors)) THENC
   PPARSEAUX_FUPDATE_LIST_CONV)
  `peg_rules pancake_peg`;;

(* HOL4 pancake_peg with start := mknt FunNT, the grammar of the second set *)
(* of theorems; its rules are those of pancake_peg                          *)

let PPARSEAUX_G1 =
  `peg_start_fupd (combin_K (mknt FunNT)) pancake_peg
     :(panLexer_token,pancakeNT,
       ((panLexer_token,pancakeNT,locs)parsetree)list,string)peg`;;

let PPARSEAUX_rules1 =
  let th = (REWRITE_CONV[(record_info "peg").ri_accfupds])
             (mk_icomb(mk_const("peg_rules",[]),PPARSEAUX_G1)) in
  TRANS th PPARSEAUX_rules;;

let rec PPARSEAUX_FAPPLY_UPDATES_CONV tm =
  let th1 = REWR_CONV FAPPLY_FUPDATE_THM tm in
  let th2 = CONV_RULE (RAND_CONV
              (RATOR_CONV(RATOR_CONV(RAND_CONV PPARSEAUX_INL_EQ_CONV)) THENC
               GEN_REWRITE_CONV I [COND_CLAUSES])) th1 in
  let r = rhs(concl th2) in
  if is_comb r && is_comb(rator r) && is_const(rator(rator r)) &&
     fst(dest_const(rator(rator r))) = "FAPPLY" &&
     is_comb(rand(rator r))
  then TRANS th2 (PPARSEAUX_FAPPLY_UPDATES_CONV r) else th2;;

let PPARSEAUX_pancakeNT_constructors =
  map rhs (disjuncts(snd(dest_forall(concl(cases "pancakeNT")))));;

let PPARSEAUX_APPLIED (rth:thm) =
  let g = rand(lhs(concl rth)) in
  let app c =
    (RATOR_CONV(RAND_CONV(K rth)) THENC PPARSEAUX_FAPPLY_UPDATES_CONV)
    (mk_comb(mk_icomb(mk_const("FAPPLY",[]),mk_icomb(mk_const("peg_rules",[]),g)),
             mk_comb(`INL:pancakeNT->pancakeNT+num`,c))) in
  end_itlist CONJ (map app PPARSEAUX_pancakeNT_constructors);;

(* HOL4: Theorem FDOM_pancake_peg = SIMP_CONV .. ``FDOM pancake_peg.rules`` *)

let FDOM_pancake_peg =
  (RAND_CONV (K PPARSEAUX_rules) THENC
   PURE_REWRITE_CONV[FDOM_FUPDATE; FDOM_FEMPTY])
  `FDOM (peg_rules pancake_peg)`;;

let pancake_peg_applied = PPARSEAUX_APPLIED PPARSEAUX_rules;;

let pancake_peg_applied' = PPARSEAUX_APPLIED PPARSEAUX_rules1;;

let rec PPARSEAUX_ALLQ_CONV c tm =
  if is_forall tm then BINDER_CONV (PPARSEAUX_ALLQ_CONV c) tm else c tm;;

(* membership of INL c in the domain, decided (T or F) *)

let PPARSEAUX_IN_FDOM_CONV =
  let tor = TAUT `!p. (T \/ p) <=> T` and forr = TAUT `!p. (F \/ p) <=> p` in
  let in_empty = prove(`!x:pancakeNT+num. x IN {} <=> F`,
                       REWRITE_TAC[NOT_IN_EMPTY]) in
  let rec in_enum tm =
    (REWR_CONV in_empty ORELSEC
     (REWR_CONV IN_INSERT THENC LAND_CONV PPARSEAUX_INL_EQ_CONV THENC
      (REWR_CONV tor ORELSEC (REWR_CONV forr THENC in_enum)))) tm in
  RAND_CONV (REWR_CONV FDOM_pancake_peg) THENC in_enum;;

(* the rule of a non-terminal *)

let PPARSEAUX_rule (c:term) =
  find (fun r -> rand(rand(lhs(concl r))) = c)
       (CONJUNCTS pancake_peg_applied);;

(* HOL4: pancake_exec_thm[compute], peg_nt_thm for each non-terminal *)

let pancake_exec_thm =
  let spec0 = ISPEC `pancake_peg` peg_nt_thm in
  let inl = `INL:pancakeNT->pancakeNT+num` in
  let one c =
    let th = SPEC (mk_comb(inl,c)) spec0 in
    let th1 = CONV_RULE (PPARSEAUX_ALLQ_CONV (RAND_CONV
                (RATOR_CONV(RATOR_CONV(RAND_CONV PPARSEAUX_IN_FDOM_CONV)) THENC
                 GEN_REWRITE_CONV I [COND_CLAUSES]))) th in
    CONV_RULE (PPARSEAUX_ALLQ_CONV (RAND_CONV
                 (ONCE_DEPTH_CONV (REWR_CONV (PPARSEAUX_rule c))))) th1 in
  end_itlist CONJ (map one PPARSEAUX_pancakeNT_constructors);;

let parse_statement_def = cake_def
  `parse_statement s =
     match peg_exec pancake_peg (mknt ProgNT) s [] NONE [] pegexec_done failed with
       Result (peg_Success [] [e] _) -> SOME e
     | _ -> NONE`;;

let panPEG_parse_def = cake_def
  `panPEG_parse s =
     match peg_exec pancake_peg (mknt TopDecListNT) s [] NONE [] pegexec_done failed with
       Result (peg_Success [] [e] _) -> INL e
     | Result (peg_Success toks _ _) ->
         INR [(implode "Parser could not consume all tokens",unknown_loc)]
     | Result (Failure loc msg) -> INR [(implode msg,loc)]
     | Looped ->
         INR [(implode "PEG execution looped during parsing",unknown_loc)]
     | _ -> INR [(implode "Unknown error during parsing",unknown_loc)]`;;

(* Properties for proving well-formedness of the Pancake grammar. *)

(* HOL4: frange_image (local) *)

let panPEG_frange_image = prove
 (`!fm:(A,B)fmap. FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  REWRITE_TAC[FRANGE_DEF; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

(* HOL4's ML values peg0_rwts, wfpeg_rwts and pegnt_case_ths (the cases of   *)
(* peg0, peggt0, pegfail and wfpeg for each kind of expression) are the     *)
(* clause theorems LPARSEAUX_peg0_clauses, ... of hol4/peg.ml.              *)

(* ------------------------------------------------------------------------- *)
(* peg0 of the derived forms (HOL4 [simp]).                                  *)
(* ------------------------------------------------------------------------- *)

let panPEG_peg0_pegf = prove
 (`!(G:(A,B,(C)list,E)peg) s f. peg0 G (panPEG_pegf s f) <=> peg0 G s`,
  REWRITE_TAC[panPEG_pegf_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [panPEG_peg0_pegf];;

let panPEG_peg0_seql = prove
 (`!(G:(A,B,(C)list,E)peg) h t f.
     (peg0 G (panPEG_seql [] f) <=> T) /\
     (peg0 G (panPEG_seql (CONS h t) f) <=>
      peg0 G h /\ peg0 G (panPEG_seql t I))`,
  REWRITE_TAC[panPEG_seql_def; panPEG_pegf_def; ITLIST;
              LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [panPEG_peg0_seql];;

let peg0_keep_tok = prove
 (`!(G:(A,B,((A,D,locs)parsetree)list,E)peg) t. peg0 G (keep_tok t) <=> F`,
  REWRITE_TAC[keep_tok_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_keep_tok];;

let peg0_consume_tok = prove
 (`!(G:(A,B,(C)list,E)peg) t. peg0 G (consume_tok t) <=> F`,
  REWRITE_TAC[consume_tok_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_consume_tok];;

let peg0_keep_kw = prove
 (`!(G:(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)peg) k.
     peg0 G (keep_kw k) <=> F`,
  REWRITE_TAC[keep_kw_def; peg0_keep_tok]);;
let _ = cake_add_simps [peg0_keep_kw];;

let peg0_consume_kw = prove
 (`!(G:(panLexer_token,B,(C)list,E)peg) k. peg0 G (consume_kw k) <=> F`,
  REWRITE_TAC[consume_kw_def; peg0_consume_tok]);;
let _ = cake_add_simps [peg0_consume_kw];;

let peg0_keep_int = prove
 (`!(G:(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)peg).
     peg0 G keep_int <=> F`,
  REWRITE_TAC[keep_int_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_keep_int];;

(* HOL4 states peg0_keep_nat about keep_int (the same statement as          *)
(* peg0_keep_int; HOL4's proof, simp[keep_nat_def], closes it with the       *)
(* simp theorem peg0_keep_int); the statement is kept                        *)

let peg0_keep_nat = prove
 (`!(G:(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)peg).
     peg0 G keep_int <=> F`,
  REWRITE_TAC[peg0_keep_int]);;
let _ = cake_add_simps [peg0_keep_nat];;

let peg0_keep_ident = prove
 (`!(G:(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)peg).
     peg0 G keep_ident <=> F`,
  REWRITE_TAC[keep_ident_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_keep_ident];;

let peg0_keep_ffi_ident = prove
 (`!(G:(panLexer_token,B,((panLexer_token,D,locs)parsetree)list,E)peg).
     peg0 G keep_ffi_ident <=> F`,
  REWRITE_TAC[keep_ffi_ident_def; LPARSEAUX_peg0_clauses]);;
let _ = cake_add_simps [peg0_keep_ffi_ident];;

let panPEG_peg0_choicel = prove
 (`!(G:(A,B,(C)list,E)peg) h t.
     (peg0 G (panPEG_choicel []) <=> F) /\
     (peg0 G (panPEG_choicel (CONS h t)) <=>
      peg0 G h \/ pegfail G h /\ peg0 G (panPEG_choicel t))`,
  REWRITE_TAC[panPEG_choicel_def; LPARSEAUX_peg0_clauses;
              LPARSEAUX_pegfail_clauses]);;
let _ = cake_add_simps [panPEG_peg0_choicel];;

(* ------------------------------------------------------------------------- *)
(* Non-terminals that cannot consume nothing (HOL4: the ML function pegnt    *)
(* over topo_nts, for pancake_peg (peg0_X) and for pancake_peg with start := *)
(* mknt FunNT (peg1_X); each theorem is saved as ~peg0 G (nt (INL X) I) and  *)
(* exported as a rewrite).  As in HOL4, each proof unfolds the rule of the   *)
(* non-terminal once and uses the theorems proved before it for the         *)
(* non-terminals it mentions (kept as mknt Y).                               *)
(* ------------------------------------------------------------------------- *)

let PPARSEAUX_peg0_mknt = prove
 (`!(G:(A,pancakeNT,C,E)peg) n.
     peg0 G (mknt n) <=>
     INL n IN FDOM (peg_rules G) /\ peg0 G (FAPPLY (peg_rules G) (INL n))`,
  REWRITE_TAC[mknt_def; LPARSEAUX_peg0_nt_clauses]);;

let PPARSEAUX_wfpeg_mknt = prove
 (`!(G:(A,pancakeNT,C,E)peg) n.
     wfpeg G (mknt n) <=>
     INL n IN FDOM (peg_rules G) /\ wfpeg G (FAPPLY (peg_rules G) (INL n))`,
  REWRITE_TAC[mknt_def; LPARSEAUX_wfpeg_nt]);;

(* the derived forms and named expressions, unfolded (mknt is kept) *)

let PPARSEAUX_PEG_DEFS =
  [panPEG_seql_def; ITLIST; panPEG_choicel_def; panPEG_pegf_def;
   panPEG_try_def; try_default_def; try_ProgNT_def; keep_tok_def;
   consume_tok_def; keep_kw_def; consume_kw_def; keep_ident_def;
   keep_annot_def; keep_ffi_ident_def; keep_int_def; keep_nat_def];;

let PPARSEAUX_PEG0_RWTS =
  [LPARSEAUX_peg0_clauses; LPARSEAUX_peggt0_clauses;
   LPARSEAUX_pegfail_clauses];;

(* for the grammar G1 = pancake_peg with start := mknt FunNT: its rules are *)
(* those of pancake_peg                                                     *)

let PPARSEAUX_rules1_eq =
  REWRITE_CONV[(record_info "peg").ri_accfupds]
    (mk_icomb(mk_const("peg_rules",[]),PPARSEAUX_G1));;

let PPARSEAUX_IN_FDOM1_CONV =
  RAND_CONV (RAND_CONV (REWR_CONV PPARSEAUX_rules1_eq)) THENC
  PPARSEAUX_IN_FDOM_CONV;;

let PPARSEAUX_rule1 (c:term) =
  find (fun r -> rand(rand(lhs(concl r))) = c)
       (CONJUNCTS pancake_peg_applied');;

(* the grammar, the membership conversion, the rule lookup, the theorems     *)
(* proved so far                                                             *)

let PPARSEAUX_GRAMMARS =
  [`pancake_peg`, PPARSEAUX_IN_FDOM_CONV, PPARSEAUX_rule, ref ([]:thm list);
   PPARSEAUX_G1, PPARSEAUX_IN_FDOM1_CONV, PPARSEAUX_rule1, ref ([]:thm list)];;

let PPARSEAUX_PEGNT (k:int) (c:term) =
  let g,inconv,rule,acc = el k PPARSEAUX_GRAMMARS in
  let mk = mk_comb(`mknt:pancakeNT->(panLexer_token,pancakeNT,
                      ((panLexer_token,pancakeNT,locs)parsetree)list,string)pegsym`,
                   c) in
  let gl = mk_neg(list_mk_icomb "peg0" [g; mk]) in
  let th = prove(gl,
    GEN_REWRITE_TAC RAND_CONV [PPARSEAUX_peg0_mknt] THEN
    CONV_TAC(RAND_CONV(LAND_CONV inconv)) THEN
    REWRITE_TAC[rule c] THEN
    REWRITE_TAC(PPARSEAUX_PEG_DEFS @ PPARSEAUX_PEG0_RWTS @ !acc)) in
  acc := th :: !acc;
  REWRITE_RULE[mknt_def] th;;

let peg0_MulOpsNT = PPARSEAUX_PEGNT 0 `MulOpsNT`;;
let peg0_AddOpsNT = PPARSEAUX_PEGNT 0 `AddOpsNT`;;
let peg0_ShiftOpsNT = PPARSEAUX_PEGNT 0 `ShiftOpsNT`;;
let peg0_CmpOpsNT = PPARSEAUX_PEGNT 0 `CmpOpsNT`;;
let peg0_EqOpsNT = PPARSEAUX_PEGNT 0 `EqOpsNT`;;
let peg0_ShapeNT = PPARSEAUX_PEGNT 0 `ShapeNT`;;
let peg0_ShapeCombNT = PPARSEAUX_PEGNT 0 `ShapeCombNT`;;
let peg0_ShapedIdentNT = PPARSEAUX_PEGNT 0 `ShapedIdentNT`;;
let peg0_RawStructNT = PPARSEAUX_PEGNT 0 `RawStructNT`;;
let peg0_NmdFieldNT = PPARSEAUX_PEGNT 0 `NmdFieldNT`;;
let peg0_NmdFieldListNT = PPARSEAUX_PEGNT 0 `NmdFieldListNT`;;
let peg0_NmdStructNT = PPARSEAUX_PEGNT 0 `NmdStructNT`;;
let peg0_EBaseNT = PPARSEAUX_PEGNT 0 `EBaseNT`;;
let peg0_EFieldNT = PPARSEAUX_PEGNT 0 `EFieldNT`;;
let peg0_ENotNT = PPARSEAUX_PEGNT 0 `ENotNT`;;
let peg0_EMulNT = PPARSEAUX_PEGNT 0 `EMulNT`;;
let peg0_EAddNT = PPARSEAUX_PEGNT 0 `EAddNT`;;
let peg0_EShiftNT = PPARSEAUX_PEGNT 0 `EShiftNT`;;
let peg0_EAndNT = PPARSEAUX_PEGNT 0 `EAndNT`;;
let peg0_EXorNT = PPARSEAUX_PEGNT 0 `EXorNT`;;
let peg0_EOrNT = PPARSEAUX_PEGNT 0 `EOrNT`;;
let peg0_ELoad32NT = PPARSEAUX_PEGNT 0 `ELoad32NT`;;
let peg0_ELoadByteNT = PPARSEAUX_PEGNT 0 `ELoadByteNT`;;
let peg0_ELoadNT = PPARSEAUX_PEGNT 0 `ELoadNT`;;
let peg0_ECmpNT = PPARSEAUX_PEGNT 0 `ECmpNT`;;
let peg0_EEqNT = PPARSEAUX_PEGNT 0 `EEqNT`;;
let peg0_EBoolAndNT = PPARSEAUX_PEGNT 0 `EBoolAndNT`;;
let peg0_ExpNT = PPARSEAUX_PEGNT 0 `ExpNT`;;
let peg0_ArgListNT = PPARSEAUX_PEGNT 0 `ArgListNT`;;
let peg0_ReturnNT = PPARSEAUX_PEGNT 0 `ReturnNT`;;
let peg0_ThrowNT = PPARSEAUX_PEGNT 0 `ThrowNT`;;
let peg0_ExtCallNT = PPARSEAUX_PEGNT 0 `ExtCallNT`;;
let peg0_HandleNT = PPARSEAUX_PEGNT 0 `HandleNT`;;
let peg0_RetNT = PPARSEAUX_PEGNT 0 `RetNT`;;
let peg0_RetCallNT = PPARSEAUX_PEGNT 0 `RetCallNT`;;
let peg0_CallNT = PPARSEAUX_PEGNT 0 `CallNT`;;
let peg0_WhileNT = PPARSEAUX_PEGNT 0 `WhileNT`;;
let peg0_IfNT = PPARSEAUX_PEGNT 0 `IfNT`;;
let peg0_StoreByteNT = PPARSEAUX_PEGNT 0 `StoreByteNT`;;
let peg0_Store32NT = PPARSEAUX_PEGNT 0 `Store32NT`;;
let peg0_StoreNT = PPARSEAUX_PEGNT 0 `StoreNT`;;
let peg0_AssignNT = PPARSEAUX_PEGNT 0 `AssignNT`;;
let peg0_SharedLoadByteNT = PPARSEAUX_PEGNT 0 `SharedLoadByteNT`;;
let peg0_SharedLoad16NT = PPARSEAUX_PEGNT 0 `SharedLoad16NT`;;
let peg0_SharedLoad32NT = PPARSEAUX_PEGNT 0 `SharedLoad32NT`;;
let peg0_SharedLoadNT = PPARSEAUX_PEGNT 0 `SharedLoadNT`;;
let peg0_SharedStoreByteNT = PPARSEAUX_PEGNT 0 `SharedStoreByteNT`;;
let peg0_SharedStore16NT = PPARSEAUX_PEGNT 0 `SharedStore16NT`;;
let peg0_SharedStore32NT = PPARSEAUX_PEGNT 0 `SharedStore32NT`;;
let peg0_SharedStoreNT = PPARSEAUX_PEGNT 0 `SharedStoreNT`;;
let peg0_DecNT = PPARSEAUX_PEGNT 0 `DecNT`;;
let peg0_DecCallNT = PPARSEAUX_PEGNT 0 `DecCallNT`;;
let peg0_StmtNT = PPARSEAUX_PEGNT 0 `StmtNT`;;
let peg0_BlockNT = PPARSEAUX_PEGNT 0 `BlockNT`;;
let peg0_ParamListNT = PPARSEAUX_PEGNT 0 `ParamListNT`;;
let peg0_GlobalDecNT = PPARSEAUX_PEGNT 0 `GlobalDecNT`;;
let peg0_FunNT = PPARSEAUX_PEGNT 0 `FunNT`;;
let peg0_FieldNameListNT = PPARSEAUX_PEGNT 0 `FieldNameListNT`;;
let peg0_StructNameNT = PPARSEAUX_PEGNT 0 `StructNameNT`;;
let peg0_ExnDecNT = PPARSEAUX_PEGNT 0 `ExnDecNT`;;

let peg1_MulOpsNT = PPARSEAUX_PEGNT 1 `MulOpsNT`;;
let peg1_AddOpsNT = PPARSEAUX_PEGNT 1 `AddOpsNT`;;
let peg1_ShiftOpsNT = PPARSEAUX_PEGNT 1 `ShiftOpsNT`;;
let peg1_CmpOpsNT = PPARSEAUX_PEGNT 1 `CmpOpsNT`;;
let peg1_EqOpsNT = PPARSEAUX_PEGNT 1 `EqOpsNT`;;
let peg1_ShapeNT = PPARSEAUX_PEGNT 1 `ShapeNT`;;
let peg1_ShapeCombNT = PPARSEAUX_PEGNT 1 `ShapeCombNT`;;
let peg1_ShapedIdentNT = PPARSEAUX_PEGNT 1 `ShapedIdentNT`;;
let peg1_RawStructNT = PPARSEAUX_PEGNT 1 `RawStructNT`;;
let peg1_NmdFieldNT = PPARSEAUX_PEGNT 1 `NmdFieldNT`;;
let peg1_NmdFieldListNT = PPARSEAUX_PEGNT 1 `NmdFieldListNT`;;
let peg1_NmdStructNT = PPARSEAUX_PEGNT 1 `NmdStructNT`;;
let peg1_EBaseNT = PPARSEAUX_PEGNT 1 `EBaseNT`;;
let peg1_EFieldNT = PPARSEAUX_PEGNT 1 `EFieldNT`;;
let peg1_ENotNT = PPARSEAUX_PEGNT 1 `ENotNT`;;
let peg1_EMulNT = PPARSEAUX_PEGNT 1 `EMulNT`;;
let peg1_EAddNT = PPARSEAUX_PEGNT 1 `EAddNT`;;
let peg1_EShiftNT = PPARSEAUX_PEGNT 1 `EShiftNT`;;
let peg1_EAndNT = PPARSEAUX_PEGNT 1 `EAndNT`;;
let peg1_EXorNT = PPARSEAUX_PEGNT 1 `EXorNT`;;
let peg1_EOrNT = PPARSEAUX_PEGNT 1 `EOrNT`;;
let peg1_ELoad32NT = PPARSEAUX_PEGNT 1 `ELoad32NT`;;
let peg1_ELoadByteNT = PPARSEAUX_PEGNT 1 `ELoadByteNT`;;
let peg1_ELoadNT = PPARSEAUX_PEGNT 1 `ELoadNT`;;
let peg1_ECmpNT = PPARSEAUX_PEGNT 1 `ECmpNT`;;
let peg1_EEqNT = PPARSEAUX_PEGNT 1 `EEqNT`;;
let peg1_EBoolAndNT = PPARSEAUX_PEGNT 1 `EBoolAndNT`;;
let peg1_ExpNT = PPARSEAUX_PEGNT 1 `ExpNT`;;
let peg1_ArgListNT = PPARSEAUX_PEGNT 1 `ArgListNT`;;
let peg1_ReturnNT = PPARSEAUX_PEGNT 1 `ReturnNT`;;
let peg1_ThrowNT = PPARSEAUX_PEGNT 1 `ThrowNT`;;
let peg1_ExtCallNT = PPARSEAUX_PEGNT 1 `ExtCallNT`;;
let peg1_HandleNT = PPARSEAUX_PEGNT 1 `HandleNT`;;
let peg1_RetNT = PPARSEAUX_PEGNT 1 `RetNT`;;
let peg1_RetCallNT = PPARSEAUX_PEGNT 1 `RetCallNT`;;
let peg1_CallNT = PPARSEAUX_PEGNT 1 `CallNT`;;
let peg1_WhileNT = PPARSEAUX_PEGNT 1 `WhileNT`;;
let peg1_IfNT = PPARSEAUX_PEGNT 1 `IfNT`;;
let peg1_StoreByteNT = PPARSEAUX_PEGNT 1 `StoreByteNT`;;
let peg1_Store32NT = PPARSEAUX_PEGNT 1 `Store32NT`;;
let peg1_StoreNT = PPARSEAUX_PEGNT 1 `StoreNT`;;
let peg1_AssignNT = PPARSEAUX_PEGNT 1 `AssignNT`;;
let peg1_SharedLoadByteNT = PPARSEAUX_PEGNT 1 `SharedLoadByteNT`;;
let peg1_SharedLoad16NT = PPARSEAUX_PEGNT 1 `SharedLoad16NT`;;
let peg1_SharedLoad32NT = PPARSEAUX_PEGNT 1 `SharedLoad32NT`;;
let peg1_SharedLoadNT = PPARSEAUX_PEGNT 1 `SharedLoadNT`;;
let peg1_SharedStoreByteNT = PPARSEAUX_PEGNT 1 `SharedStoreByteNT`;;
let peg1_SharedStore16NT = PPARSEAUX_PEGNT 1 `SharedStore16NT`;;
let peg1_SharedStore32NT = PPARSEAUX_PEGNT 1 `SharedStore32NT`;;
let peg1_SharedStoreNT = PPARSEAUX_PEGNT 1 `SharedStoreNT`;;
let peg1_DecNT = PPARSEAUX_PEGNT 1 `DecNT`;;
let peg1_DecCallNT = PPARSEAUX_PEGNT 1 `DecCallNT`;;
let peg1_StmtNT = PPARSEAUX_PEGNT 1 `StmtNT`;;
let peg1_BlockNT = PPARSEAUX_PEGNT 1 `BlockNT`;;
let peg1_ParamListNT = PPARSEAUX_PEGNT 1 `ParamListNT`;;
let peg1_GlobalDecNT = PPARSEAUX_PEGNT 1 `GlobalDecNT`;;
let peg1_FunNT = PPARSEAUX_PEGNT 1 `FunNT`;;
let peg1_FieldNameListNT = PPARSEAUX_PEGNT 1 `FieldNameListNT`;;
let peg1_StructNameNT = PPARSEAUX_PEGNT 1 `StructNameNT`;;
let peg1_ExnDecNT = PPARSEAUX_PEGNT 1 `ExnDecNT`;;

(* HOL4: export_rewrites for each peg0_X and peg1_X *)

let _ = cake_add_simps
  [peg0_MulOpsNT; peg0_AddOpsNT; peg0_ShiftOpsNT; peg0_CmpOpsNT;
   peg0_EqOpsNT; peg0_ShapeNT; peg0_ShapeCombNT; peg0_ShapedIdentNT;
   peg0_RawStructNT; peg0_NmdFieldNT; peg0_NmdFieldListNT; peg0_NmdStructNT;
   peg0_EBaseNT; peg0_EFieldNT; peg0_ENotNT; peg0_EMulNT; peg0_EAddNT;
   peg0_EShiftNT; peg0_EAndNT; peg0_EXorNT; peg0_EOrNT; peg0_ELoad32NT;
   peg0_ELoadByteNT; peg0_ELoadNT; peg0_ECmpNT; peg0_EEqNT; peg0_EBoolAndNT;
   peg0_ExpNT; peg0_ArgListNT; peg0_ReturnNT; peg0_ThrowNT; peg0_ExtCallNT;
   peg0_HandleNT; peg0_RetNT; peg0_RetCallNT; peg0_CallNT; peg0_WhileNT;
   peg0_IfNT; peg0_StoreByteNT; peg0_Store32NT; peg0_StoreNT; peg0_AssignNT;
   peg0_SharedLoadByteNT; peg0_SharedLoad16NT; peg0_SharedLoad32NT;
   peg0_SharedLoadNT; peg0_SharedStoreByteNT; peg0_SharedStore16NT;
   peg0_SharedStore32NT; peg0_SharedStoreNT; peg0_DecNT; peg0_DecCallNT;
   peg0_StmtNT; peg0_BlockNT; peg0_ParamListNT; peg0_GlobalDecNT; peg0_FunNT;
   peg0_FieldNameListNT; peg0_StructNameNT; peg0_ExnDecNT; peg1_MulOpsNT;
   peg1_AddOpsNT; peg1_ShiftOpsNT; peg1_CmpOpsNT; peg1_EqOpsNT; peg1_ShapeNT;
   peg1_ShapeCombNT; peg1_ShapedIdentNT; peg1_RawStructNT; peg1_NmdFieldNT;
   peg1_NmdFieldListNT; peg1_NmdStructNT; peg1_EBaseNT; peg1_EFieldNT;
   peg1_ENotNT; peg1_EMulNT; peg1_EAddNT; peg1_EShiftNT; peg1_EAndNT;
   peg1_EXorNT; peg1_EOrNT; peg1_ELoad32NT; peg1_ELoadByteNT; peg1_ELoadNT;
   peg1_ECmpNT; peg1_EEqNT; peg1_EBoolAndNT; peg1_ExpNT; peg1_ArgListNT;
   peg1_ReturnNT; peg1_ThrowNT; peg1_ExtCallNT; peg1_HandleNT; peg1_RetNT;
   peg1_RetCallNT; peg1_CallNT; peg1_WhileNT; peg1_IfNT; peg1_StoreByteNT;
   peg1_Store32NT; peg1_StoreNT; peg1_AssignNT; peg1_SharedLoadByteNT;
   peg1_SharedLoad16NT; peg1_SharedLoad32NT; peg1_SharedLoadNT;
   peg1_SharedStoreByteNT; peg1_SharedStore16NT; peg1_SharedStore32NT;
   peg1_SharedStoreNT; peg1_DecNT; peg1_DecCallNT; peg1_StmtNT; peg1_BlockNT;
   peg1_ParamListNT; peg1_GlobalDecNT; peg1_FunNT; peg1_FieldNameListNT;
   peg1_StructNameNT; peg1_ExnDecNT];;

(* ------------------------------------------------------------------------- *)
(* Well-formedness of the non-terminals (HOL4: the ML function wfnt over     *)
(* topo_nts and ProgNT (and TopDecListNT for pancake_peg); each proof        *)
(* unfolds the rule once and uses the theorems proved before it).  As in     *)
(* HOL4 the conjunction lists the last one first.                            *)
(* ------------------------------------------------------------------------- *)

let PPARSEAUX_wfpeg_acc = [ref ([]:thm list); ref ([]:thm list)];;

let PPARSEAUX_WFNT (k:int) (c:term) =
  let g,inconv,rule,npeg0 = el k PPARSEAUX_GRAMMARS in
  let acc = el k PPARSEAUX_wfpeg_acc in
  let mk = mk_comb(`mknt:pancakeNT->(panLexer_token,pancakeNT,
                      ((panLexer_token,pancakeNT,locs)parsetree)list,string)pegsym`,
                   c) in
  let gl = list_mk_icomb "wfpeg" [g; mk] in
  let th = prove(gl,
    GEN_REWRITE_TAC I [PPARSEAUX_wfpeg_mknt] THEN
    CONV_TAC(LAND_CONV inconv) THEN
    REWRITE_TAC[rule c] THEN
    REWRITE_TAC(PPARSEAUX_PEG_DEFS @ [LPARSEAUX_wfpeg_clauses] @
                PPARSEAUX_PEG0_RWTS @ !npeg0 @ !acc)) in
  acc := th :: !acc; th;;

let PPARSEAUX_topo_nts =
  [`MulOpsNT`; `AddOpsNT`; `ShiftOpsNT`; `CmpOpsNT`;
   `EqOpsNT`; `ShapeNT`;
   `ShapeCombNT`; `ShapedIdentNT`; `RawStructNT`; `NmdFieldNT`;
   `NmdFieldListNT`; `NmdStructNT`;
   `EBaseNT`; `EFieldNT`; `ENotNT`; `EMulNT`; `EAddNT`; `EShiftNT`; `EAndNT`;
   `EXorNT`; `EOrNT`;
   `ELoad32NT`; `ELoadByteNT`; `ELoadNT`; `ECmpNT`; `EEqNT`; `EBoolAndNT`;
   `ExpNT`; `ArgListNT`; `ReturnNT`;
   `ThrowNT`; `ExtCallNT`;
   `HandleNT`; `RetNT`; `RetCallNT`; `CallNT`;
   `WhileNT`; `IfNT`; `StoreByteNT`; `Store32NT`;
   `StoreNT`; `AssignNT`;
   `SharedLoadByteNT`; `SharedLoad16NT`; `SharedLoad32NT`; `SharedLoadNT`;
   `SharedStoreByteNT`; `SharedStore16NT`; `SharedStore32NT`; `SharedStoreNT`;
   `DecNT`;
   `DecCallNT`; `StmtNT`; `BlockNT`; `ParamListNT`; `GlobalDecNT`; `FunNT`;
   `FieldNameListNT`; `StructNameNT`; `ExnDecNT`];;

(* This time include the top-level program non-terminal which is            *)
(* well-formed.                                                              *)

let pancake_wfpeg_thm =
  do_list (fun c -> ignore(PPARSEAUX_WFNT 0 c))
          (PPARSEAUX_topo_nts @ [`ProgNT`; `TopDecListNT`]);
  end_itlist CONJ (!(el 0 PPARSEAUX_wfpeg_acc));;

let pancake_wfpeg_FunNT_thm =
  do_list (fun c -> ignore(PPARSEAUX_WFNT 1 c))
          (PPARSEAUX_topo_nts @ [`ProgNT`]);
  end_itlist CONJ (!(el 1 PPARSEAUX_wfpeg_acc));;

(* HOL4: subexprs_mknt (local) *)

let subexprs_mknt = prove
 (`!n. subexprs (mknt n:(A,pancakeNT,C,E)pegsym) = {mknt n}`,
  REWRITE_TAC[subexprs_def; mknt_def]);;

(* HOL4: the ML value peg_start *)

let PPARSEAUX_peg_start = prove
 (`peg_start pancake_peg = mknt TopDecListNT`,
  REWRITE_TAC[pancake_peg_def; (record_info "peg").ri_accessors]);;

(* every subexpression of an expression is well-formed, by the form of the  *)
(* expression (for the proof of PEG_wellformed; HOL4 simplifies with        *)
(* subexprs_def, DISJ_IMP_THM and FORALL_AND_THM)                           *)

let PPARSEAUX_ALLWF_mknt = prove
 (`!(G:(A,pancakeNT,C,E)peg) n.
     (!x. x IN subexprs (mknt n) ==> wfpeg G x) <=> wfpeg G (mknt n)`,
  REWRITE_TAC[subexprs_mknt; IN_SING; FORALL_UNWIND_THM2]);;

let panPEG_PEG_wellformed = prove
 (`wfG pancake_peg`,
  REWRITE_TAC[wfG_def; LPARSEAUX_FORALL_GEXPRS; PPARSEAUX_peg_start;
              FDOM_pancake_peg; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[pancake_peg_applied] THEN
  REWRITE_TAC(PPARSEAUX_PEG_DEFS @ [LPARSEAUX_ALLWF; PPARSEAUX_ALLWF_mknt] @
              CONJUNCTS pancake_wfpeg_thm @ PPARSEAUX_PEG0_RWTS @
              !(let _,_,_,a = el 0 PPARSEAUX_GRAMMARS in a)));;
let _ = cake_add_simps [panPEG_PEG_wellformed];;
