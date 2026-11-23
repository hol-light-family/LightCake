(* ========================================================================= *)
(* closLang: port of HOL4 compiler/backend/closLangScript.sml (CakeML v3479).*)
(* The closLang intermediate language. This language is the last            *)
(* intermediate language that has closure values. This language is          *)
(* designed for optimisation of function calls.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - word64 is int64; HOL4 EVERY is ALL.                                     *)
(* - HOL4's size functions of the nested types of exp (exp1_size, ...) are   *)
(*   written as their list_size / pair_size forms (HOL4's exp_size_eq):      *)
(*   exp1_size (on (num # exp) list) is                                      *)
(*   list_size (pair_size (\x. x) clos_exp_size).                            *)
(* - has_install and pure are defined with sem1aux_def_wf / sem1aux_def      *)
(*   (semantics/sem1aux_tfl.ml): the clauses and induction theorems of       *)
(*   cake_def, without the cost of the casewise recursion package.          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "compiler/backend/backend_common.ml";;
needs "basis/pure/mlstring.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* compilation from this language removes closures *)

let const_INDUCT,const_RECURSION = cake_type
  "const = ConstCons num (const list)
         | ConstInt int
         | ConstStr mlstring
         | ConstWord64 int64";;

let const_part_INDUCT,const_part_RECURSION = cake_type
  "const_part = clos_Con num (num list)
              | clos_Int int
              | clos_Str mlstring
              | clos_W64 int64";;

(* clos_Const: integer; clos_Add, clos_Sub, Mult, clos_Div, clos_Mod: plus, *)
(* minus, times, div, mod over the integers; clos_Less, LessEq, Greater,     *)
(* GreaterEq: < <= > >= over the integers; LessConstSmall: checks < const   *)
(* for small ints                                                            *)

let int_op_INDUCT,int_op_RECURSION = cake_type
  "int_op = clos_Const int
          | clos_Add
          | clos_Sub
          | Mult
          | clos_Div
          | clos_Mod
          | clos_Less
          | LessEq
          | Greater
          | GreaterEq
          | LessConstSmall num";;

let word_op_INDUCT,word_op_RECURSION = cake_type
  "word_op = WordOpw word_size opw
           | WordShift word_size shift num
           | WordTest word_size test
           | WordFromInt
           | WordToInt
           | WordFromWord bool
           | FP_cmp fp_cmp
           | FP_uop fp_uop
           | FP_bop fp_bop
           | FP_top fp_top";;

(* clos_Cons: construct a Block with given tag; ElemAt: same as El but for   *)
(* constant index; clos_TagLenEq: check Block's tag and length; clos_LenEq:  *)
(* check Block's length; TagEq: check Block's tag; LengthBlock: get length   *)
(* of Block; BoolTest: tests for bools; BoolNot: boolean not;                *)
(* BoundsCheckBlock: check that vector index is within bounds; ConsExtend:   *)
(* construct a Block with given tag (the first three arguments should be a   *)
(* block followed by two numbers indicating the first element, and how       *)
(* many, should be copied into the end of the new block; the fourth argument *)
(* is the total size of the new block); FromList: convert list to packed     *)
(* Block; clos_ListAppend: appends two lists; Constant: produces a constant  *)
(* value; clos_Equal: structural equality; EqualConst: equal to              *)
(* integer/string/word constant; Build: implementation of Constant above     *)

let block_op_INDUCT,block_op_RECURSION = cake_type
  "block_op = clos_Cons num
            | ElemAt num
            | clos_TagLenEq num num
            | clos_LenEq num
            | TagEq num
            | LengthBlock
            | BoolTest test
            | BoolNot
            | BoundsCheckBlock
            | ConsExtend num
            | FromList num
            | clos_ListAppend
            | Constant const
            | clos_Equal
            | EqualConst const_part
            | Build (const_part list)";;

(* clos_Global: load global var with index; SetGlobal: assign a value to a   *)
(* global; AllocGlobal: make space for a new global; GlobalsPtr: get pointer *)
(* to globals array; SetGlobalsPtr: set pointer to globals array             *)

let glob_op_INDUCT,glob_op_RECURSION = cake_type
  "glob_op = clos_Global num
           | SetGlobal num
           | AllocGlobal
           | GlobalsPtr
           | SetGlobalsPtr";;

(* clos_Ref: makes a reference/array; Update: updates a reference/array;     *)
(* clos_El: read index from block of reference/array; Length: get length of  *)
(* reference; LengthByte: get length of byte array; RefByte: makes a byte    *)
(* array, T = immutable/compare-by-contents; RefArray: makes an array by     *)
(* replicating a value; DerefByte: loads a byte from a byte array;           *)
(* UpdateByte: updates a byte array; ConcatByteVec: concatenate list of byte *)
(* vectors; CopyByte: copy a slice of a byte array, T means target should be *)
(* allocated; FromListByte: convert list of chars to ByteVector; ToListByte: *)
(* convert ByteVector to list of chars; LengthByteVec: get length of         *)
(* ByteVector; DerefByteVec: load a byte from a ByteVector; StringCmp:       *)
(* string comparisons; XorByte: xor a btye vector into a byte array;         *)
(* BoundsCheckByte: T = loose (<=) bound; MutCons: allocate a cons with a    *)
(* mutable hole, tag, index of hole; UpdateCons: mutate the hole in a        *)
(* MutCons; FinaliseCons: turns a stack of MutCons into Cons                 *)

let mem_op_INDUCT,mem_op_RECURSION = cake_type
  "mem_op = clos_Ref
          | Update
          | clos_El
          | Length
          | LengthByte
          | RefByte bool
          | RefArray
          | DerefByte
          | UpdateByte
          | ConcatByteVec
          | CopyByte bool
          | FromListByte
          | ToListByte
          | LengthByteVec
          | DerefByteVec
          | StringCmp bool opb
          | XorByte
          | BoundsCheckArray
          | BoundsCheckByte bool
          | MutCons num num
          | UpdateCons
          | FinaliseCons
          | clos_ConfigGC";;

(* clos_Label: constructs a CodePtr; clos_FFI: calls the FFI; clos_Install:  *)
(* installs new code at runtime                                              *)

let clos_op_INDUCT,clos_op_RECURSION = cake_type
  "clos_op = clos_Label num
           | clos_FFI mlstring
           | IntOp int_op
           | WordOp word_op
           | BlockOp block_op
           | GlobOp glob_op
           | MemOp mem_op
           | clos_Install
           | clos_ThunkOp thunk_op";;

(* clos_Call tra ticks loc args *)

let clos_exp_INDUCT,clos_exp_RECURSION = cake_type
  "clos_exp = clos_Var tra num
            | clos_If tra clos_exp clos_exp clos_exp
            | clos_Let tra (clos_exp list) clos_exp
            | clos_Raise tra clos_exp
            | clos_Handle tra clos_exp clos_exp
            | clos_Tick tra clos_exp
            | clos_Call tra num num (clos_exp list)
            | clos_App tra (num option) clos_exp (clos_exp list)
            | Fn mlstring (num option) ((num list) option) num clos_exp
            | clos_Letrec (mlstring list) (num option) ((num list) option)
                          ((num # clos_exp) list) clos_exp
            | clos_Op tra clos_op (clos_exp list)";;

(* HOL4: val exp_size_def = definition "exp_size_def": type_size_def          *)
(* "clos_exp" (with size_aux_eqs "clos_exp" for the nested types)            *)

(* the termination condition of Letrec needs the size of MAP SND fns, as  *)
(* in HOL4 (list_size_pair_size_MAP_FST_SND of misc)                       *)

let has_install_def = sem1aux_def_wf
  `MEASURE (\x:clos_exp + clos_exp list.
              sum_CASE x (\e. clos_exp_size e) (\es. list_size clos_exp_size es))`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN
    REWRITE_TAC(WF_REL_THMS @ [sum_CASE; type_size_def "clos_exp"] @
                size_aux_eqs "clos_exp") THEN
    REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC))
  `(has_install (clos_Var t n) <=> F) /\
   (has_install (clos_If t e1 e2 e3) <=>
      has_install e1 \/ has_install e2 \/ has_install e3) /\
   (has_install (clos_Let t es e) <=> has_install e \/ has_install_list es) /\
   (has_install (clos_Op t p es) <=> p = clos_Install \/ has_install_list es) /\
   (has_install (clos_Raise t e) <=> has_install e) /\
   (has_install (clos_Tick t e) <=> has_install e) /\
   (has_install (Fn _ _ _ _ e) <=> has_install e) /\
   (has_install (clos_Handle t e1 e2) <=> has_install e1 \/ has_install e2) /\
   (has_install (clos_Call _ _ _ es) <=> has_install_list es) /\
   (has_install (clos_App _ _ e es) <=> has_install e \/ has_install_list es) /\
   (has_install (clos_Letrec _ _ _ fns e) <=>
      has_install_list (MAP SND fns) \/ has_install e) /\
   (has_install_list [] <=> F) /\
   (has_install_list (CONS x xs) <=> has_install x \/ has_install_list xs)`;;

let has_install_ind = cake_ind "has_install";;

(* HOL4 exp1_size fns is list_size (pair_size (\x. x) clos_exp_size) fns *)

let exp1_size_lemma = prove
 (`!fns n x. MEM (n,x) fns ==>
             clos_exp_size x < list_size (pair_size (\i:num. i) clos_exp_size) fns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[pair_size_THM] THEN
    ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:clos_exp`]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* HOL4: pure_op *)

let clos_pure_op_def = cake_def
  `clos_pure_op op <=>
     match op with
       clos_FFI _ -> F
     | GlobOp (SetGlobal _) -> F
     | GlobOp AllocGlobal -> F
     | MemOp (RefByte _) -> F
     | MemOp RefArray -> F
     | MemOp UpdateByte -> F
     | MemOp (CopyByte F) -> F
     | MemOp XorByte -> F
     | MemOp clos_Ref -> F
     | MemOp Update -> F
     | clos_Install -> F
     | clos_ThunkOp _ -> F
     | _ -> T`;;

(* pure e means e can neither raise an exception nor side-effect the state *)

let pure_def = sem1aux_def
  `(pure (clos_Var _ _) <=> T) /\
   (pure (clos_If _ e1 e2 e3) <=> pure e1 /\ pure e2 /\ pure e3) /\
   (pure (clos_Let _ es e2) <=> ALL pure es /\ pure e2) /\
   (pure (clos_Raise _ _) <=> F) /\
   (pure (clos_Handle _ e1 e2) <=> pure e1) /\
   (pure (clos_Tick _ _) <=> F) /\
   (pure (clos_Call _ _ _ _) <=> F) /\
   (pure (clos_App _ _ _ _) <=> F) /\
   (pure (Fn _ _ _ _ _) <=> T) /\
   (pure (clos_Letrec _ _ _ _ x) <=> pure x) /\
   (pure (clos_Op _ opn es) <=> ALL pure es /\ clos_pure_op opn)`;;

let pure_ind = cake_ind "pure";;

(* used in proofs about closLang, BVL, BVI and dataLang *)

let assign_get_code_label_def = cake_def_clauses
  [`assign_get_code_label (clos_Label x) = {x:num}`;
   `assign_get_code_label (x:clos_op) = {}:num->bool`];;

(* HOL4's induction theorem of the completed clauses (a case split) *)

let assign_get_code_label_ind = prove
 (`!P. (!x. P (clos_Label x)) /\ (!v2. P (clos_FFI v2)) /\
       (!v3. P (IntOp v3)) /\ (!v4. P (WordOp v4)) /\ (!v5. P (BlockOp v5)) /\
       (!v6. P (GlobOp v6)) /\ (!v7. P (MemOp v7)) /\ P clos_Install /\
       (!v8. P (clos_ThunkOp v8))
       ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC clos_op_INDUCT THEN
  ASM_REWRITE_TAC[]);;

new_type_abbrev("clos_prog",`:clos_exp list # (num # num # clos_exp) list`);;

(* HOL4: Type clos_cc (with a type variable C): written out where used,  *)
(* as C -> clos_prog -> (byte list # int64 list # C) option               *)
