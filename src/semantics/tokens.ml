(* ========================================================================= *)
(* tokens: port of HOL4 semantics/tokensScript.sml (CakeML v3479).           *)
(* The tokens CakeML concrete syntax.                                        *)
(* Some tokens are from Standard ML and not used in CakeML.                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The HOL4 type path of this theory is tokens_path: HOL Light already has *)
(*   a type path (HOL4's pathTheory, src/hol4/path.ml, loaded by misc).      *)
(* - Constructor names from doc/names.tsv: Mod, IntT, WordT and              *)
(*   CharT are tokens_Mod, tokens_IntT, tokens_WordT and tokens_CharT.       *)
(* ========================================================================= *)

needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* HOL4: Datatype path = Mod mlstring path | End *)

let tokens_path_INDUCT,tokens_path_RECURSION = cake_type
  "tokens_path = tokens_Mod mlstring tokens_path | End";;

let token_INDUCT,token_RECURSION = cake_type
  "token =
     WhitespaceT num | NewlineT | LexErrorT
   | HashT | LparT | RparT | StarT | CommaT | ArrowT | DotsT | ColonT | SealT
   | SemicolonT | EqualsT | DarrowT | LbrackT | RbrackT | UnderbarT | LbraceT
   | BarT | RbraceT | AndT | AndalsoT | AsT | CaseT | DatatypeT
   | ElseT | EndT | EqtypeT | ExceptionT | FnT | FunT | HandleT | IfT
   | InT | IncludeT | LetT | LocalT | OfT | OpT
   | OpenT | OrelseT | RaiseT | RecT | SharingT | SigT | SignatureT | StructT
   | StructureT | ThenT | TypeT | ValT | WhereT | WhileT | WithT | WithtypeT
   | tokens_IntT int
   | HexintT mlstring
   | tokens_WordT num
   | RealT mlstring
   | StringT mlstring
   | tokens_CharT char
   | TyvarT mlstring
   | AlphaT mlstring
   | SymbolT mlstring
   | LongidT tokens_path mlstring
   | FFIT mlstring
   | REPLIDT mlstring";;
