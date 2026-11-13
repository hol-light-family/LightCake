(* ========================================================================= *)
(* ast: port of HOL4 semantics/astScript.sml (CakeML v3479).                 *)
(* Definition of CakeML abstract syntax (AST).                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's type abbreviations modN varN conN typeN tvarN (all mlstring)     *)
(*   and type_def are HOL Light type abbreviations (new_type_abbrev).        *)
(* - word8 is byte and word64 is int64 (hol4/words4.ml).                     *)
(* - HOL4's paired lambdas (\(pat,e). t) are written                         *)
(*   (\pe. match pe with (pat,e) -> t), as in semantics/namespace.ml.        *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name (every_exp: Let xo, Tannot e ty, *)
(*   Lannot e lc for HOL4's Let x, Tannot e a, Lannot e a).                  *)
(* - Induction theorems of recursive definitions: NAME_ind = cake_ind "NAME" *)
(*   (HOL4's NAME_ind; ast_Seqs_ind etc. for the reserved names).            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/location.ml";;
needs "semantics/namespace.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* Literal constants *)

let lit_INDUCT,lit_RECURSION = cake_type
  "lit = IntLit int
       | Char char
       | StrLit mlstring
       | Word8 byte
       | Word64 int64
       | Float64 int64";;

let shift_INDUCT,shift_RECURSION = cake_type
  "shift = Lsl | Lsr | Asr | Ror";;

let arith_INDUCT,arith_RECURSION = cake_type
  "arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs
         | Sqrt | FMA";;

(* Module names *)
new_type_abbrev("modN",`:mlstring`);;

(* Variable names *)
new_type_abbrev("varN",`:mlstring`);;

(* Constructor names (from datatype definitions) *)
new_type_abbrev("conN",`:mlstring`);;

(* Type names *)
new_type_abbrev("typeN",`:mlstring`);;

(* Type variable names *)
new_type_abbrev("tvarN",`:mlstring`);;

let word_size_INDUCT,word_size_RECURSION = cake_type
  "word_size = W8 | W64";;

let thunk_mode_INDUCT,thunk_mode_RECURSION = cake_type
  "thunk_mode = Evaluated | NotEvaluated";;

let thunk_op_INDUCT,thunk_op_RECURSION = cake_type
  "thunk_op = AllocThunk thunk_mode
            | UpdateThunk thunk_mode
            | ForceThunk";;

let opb_INDUCT,opb_RECURSION = cake_type
  "opb = Lt | Gt | Leq | Geq";;

let test_INDUCT,test_RECURSION = cake_type
  "test = Equal | Compare opb | AltCompare opb";;

let prim_type_INDUCT,prim_type_RECURSION = cake_type
  "prim_type = BoolT
             | IntT
             | CharT
             | StrT
             | WordT word_size
             | Float64T";;

(* Arith: primitive operations for the primitive types (+, -, and, sqrt,  *)
(* ...); FromTo: conversions between primitive types (char<->int,         *)
(* word<->double, word<->int); Shift: operations on words; Opapp:         *)
(* function application; Opassign Opref Opderef: references; Aw8...:      *)
(* Word8Array operations; CopyStrStr ... XorAw8Str_unsafe: string and     *)
(* bytearray conversions; Implode ... Strcat: string operations;          *)
(* VfromList Vsub Vlength: vectors; Aalloc ... Aupdate: arrays; ..._unsafe *)
(* unsafe vector and array accesses; ThunkOp: thunk operations;           *)
(* ListAppend: list operations; ConfigGC: configure the GC; FFI: call a   *)
(* given foreign function; Eval: evaluate new code in a given env;        *)
(* Env_id: get the identifier of an env object.                           *)

let op_INDUCT,op_RECURSION = cake_type
  "op = Arith arith prim_type
      | FromTo prim_type prim_type
      | Shift word_size shift num
      | Equality
      | Test test prim_type
      | Opapp
      | Opassign
      | Opref
      | Opderef
      | Aw8alloc
      | Aw8sub
      | Aw8length
      | Aw8update
      | CopyStrStr
      | CopyStrAw8
      | CopyAw8Str
      | CopyAw8Aw8
      | XorAw8Str_unsafe
      | Implode
      | Explode
      | Strsub
      | Strlen
      | Strcat
      | VfromList
      | Vsub
      | Vlength
      | Aalloc
      | AallocEmpty
      | AallocFixed
      | Asub
      | Alength
      | Aupdate
      | Vsub_unsafe
      | Asub_unsafe
      | Aupdate_unsafe
      | Aw8sub_unsafe
      | Aw8update_unsafe
      | ThunkOp thunk_op
      | ListAppend
      | ConfigGC
      | FFI mlstring
      | Eval
      | Env_id";;

(* Define operator classes, that allow to group their behavior later:     *)
(* EvalOp the Eval primitive, FunApp function application, Force forcing  *)
(* a thunk, Simple arithmetic operations (no finite-precision/reals)       *)

let op_class_INDUCT,op_class_RECURSION = cake_type
  "op_class = EvalOp | FunApp | Force | Simple";;

let getOpClass_def = cake_def
  `getOpClass (op:op) =
     match op with
       Opapp -> FunApp
     | Eval -> EvalOp
     | ThunkOp t -> (if t = ForceThunk then Force else Simple)
     | _ -> Simple`;;
let _ = cake_add_simps [getOpClass_def];;

(* Types used in type annotations: Atvar type variables that the user      *)
(* writes down ('a, 'b, etc.), Atfun function types, Attup tuple types,   *)
(* Atapp type constructor applications (0-ary type applications represent *)
(* unparameterised types, e.g. num or string)                              *)

let ast_t_INDUCT,ast_t_RECURSION = cake_type
  "ast_t = Atvar tvarN
         | Atfun ast_t ast_t
         | Attup (ast_t list)
         | Atapp (ast_t list) ((modN,typeN)id)";;

(* Patterns; Pcon NONE is a tuple pattern; Pas is a pattern alias *)

let pat_INDUCT,pat_RECURSION = cake_type
  "pat = Pany
       | Pvar varN
       | Plit lit
       | Pcon (((modN,conN)id)option) (pat list)
       | Pref pat
       | Pas pat varN
       | Ptannot pat ast_t";;

(* Short circuiting logical operations *)

let lop_INDUCT,lop_RECURSION = cake_type
  "lop = Andalso | Orelse";;

(* Expressions.  Con NONE is a tuple; App applies a primitive operator     *)
(* (including function application); Log: logical operations (and, or);   *)
(* Mat: pattern matching; Let NONE is the sequencing expression (e1; e2);  *)
(* Letrec: local definition of (potentially) mutually recursive functions *)
(* (the first varN is the function's name, the second its parameter);     *)
(* Lannot: location annotated expressions, not expected in source         *)
(* programs.                                                               *)

let exp_INDUCT,exp_RECURSION = cake_type
  "exp = Raise exp
       | Handle exp ((pat # exp) list)
       | Lit lit
       | Con (((modN,conN)id)option) (exp list)
       | Var ((modN,varN)id)
       | Fun varN exp
       | App op (exp list)
       | Log lop exp exp
       | If exp exp exp
       | Mat exp ((pat # exp) list)
       | Let (varN option) exp exp
       | Letrec ((varN # varN # exp) list) exp
       | Tannot exp ast_t
       | Lannot exp locs";;

new_type_abbrev("type_def",
  `:(tvarN list # typeN # (conN # ast_t list) list) list`);;

(* Declarations.  Dlet: top-level bindings (the pattern allows several    *)
(* names to be bound at once); Dletrec: mutually recursive function        *)
(* definition; Dtype: type definition (several data types, each with      *)
(* several named variants, which can in turn have several arguments);     *)
(* Dtabbrev: type abbreviations; Dexn: new exceptions; Dmod: module;      *)
(* Dlocal: local part, visible part; Denv: store the current lexical env  *)
(* in an env value.                                                        *)

let dec_INDUCT,dec_RECURSION = cake_type
  "dec = Dlet locs pat exp
       | Dletrec locs ((varN # varN # exp) list)
       | Dtype locs type_def
       | Dtabbrev locs (tvarN list) typeN ast_t
       | Dexn locs conN (ast_t list)
       | Dmod modN (dec list)
       | Dlocal (dec list) (dec list)
       | Denv tvarN";;

(* Computes the bindings of a pattern *)

let pat_bindings_def = cake_def
  `(pat_bindings Pany = []:varN list) /\
   (pat_bindings (Pvar n) = [n]) /\
   (pat_bindings (Plit l) = []) /\
   (pat_bindings (Pcon v0 ps) = pats_bindings ps) /\
   (pat_bindings (Pref p) = pat_bindings p) /\
   (pat_bindings (Pas p i) = APPEND (pat_bindings p) [i]) /\
   (pat_bindings (Ptannot p v1) = pat_bindings p) /\
   (pats_bindings [] = []) /\
   (pats_bindings (CONS p ps) = APPEND (pats_bindings ps) (pat_bindings p))`;;

let pat_bindings_ind = cake_ind "pat_bindings";;

(* defined with sem1aux_def (TFL-style compilation of the 14 clauses: the   *)
(* kit's casewise package needs about 250 s for them)                      *)
let every_exp_def = sem1aux_def
  `(every_exp p (Raise e) <=>
      p (Raise e) /\ every_exp p e) /\
   (every_exp p (Handle e pes) <=>
      p (Handle e pes) /\ every_exp p e /\
      ALL (\pe. match pe with (pat,e) -> every_exp p e) pes) /\
   (every_exp p (Lit l) <=>
      p (Lit l)) /\
   (every_exp p (Con cn es) <=>
      p (Con cn es) /\ ALL (every_exp p) es) /\
   (every_exp p (Var v) <=>
      p (Var v)) /\
   (every_exp p (Fun x e) <=>
      p (Fun x e) /\ every_exp p e) /\
   (every_exp p (App op es) <=>
      p (App op es) /\ ALL (every_exp p) es) /\
   (every_exp p (Log lop e1 e2) <=>
      p (Log lop e1 e2) /\ every_exp p e1 /\ every_exp p e2) /\
   (every_exp p (If e1 e2 e3) <=>
      p (If e1 e2 e3) /\ every_exp p e1 /\ every_exp p e2 /\ every_exp p e3) /\
   (every_exp p (Mat e pes) <=>
      p (Mat e pes) /\ every_exp p e /\
      ALL (\pe. match pe with (pat,e) -> every_exp p e) pes) /\
   (every_exp p (Let xo e1 e2) <=>
      p (Let xo e1 e2) /\ every_exp p e1 /\ every_exp p e2) /\
   (every_exp p (Tannot e ty) <=>
      p (Tannot e ty) /\ every_exp p e) /\
   (every_exp p (Lannot e lc) <=>
      p (Lannot e lc) /\ every_exp p e) /\
   (every_exp p (Letrec funs e) <=>
      p (Letrec funs e) /\ every_exp p e /\
      ALL (\nve. match nve with (n,v,e) -> every_exp p e) funs)`;;
let _ = cake_add_simps [every_exp_def];;

let every_exp_ind = cake_ind "every_exp";;

(* HOL4: Seqs_def *)
let ast_Seqs_def = cake_def
  `(Seqs [] = Con NONE []) /\
   (Seqs (CONS x xs) = Let NONE x (Seqs xs))`;;

let ast_Seqs_ind = cake_ind "Seqs";;

(* HOL4: Apps_def *)
let ast_Apps_def = cake_def
  `(Apps f [] = f) /\
   (Apps f (CONS x xs) = Apps (App Opapp [f; x]) xs)`;;

let ast_Apps_ind = cake_ind "Apps";;

(* HOL4: Funs_def *)
let ast_Funs_def = cake_def
  `(Funs [] e = e) /\
   (Funs (CONS x xs) e = Fun x (Funs xs e))`;;

let ast_Funs_ind = cake_ind "Funs";;
