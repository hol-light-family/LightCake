(* ========================================================================= *)
(* dataLang: port of HOL4 compiler/backend/dataLangScript.sml (CakeML v3479).*)
(* The dataLang intermediate language is the last language with a           *)
(* functional-programming-style data abstraction.                            *)
(*                                                                           *)
(* dataLang is the next step from BVL/BVI: (1) dataLang is an imperative     *)
(* version of BVL/BVI, i.e. operations update state; (2) there is a new      *)
(* state component (called space) and an explicit MakeSpace operation that   *)
(* increases space. Space is consumed by Ref and Cons, and space is reset by *)
(* Add, Sub, etc.                                                            *)
(*                                                                           *)
(* The idea is that the MakeSpace calls can be moved around and lumped       *)
(* together. This optimisation reduces the number of calls to the allocator  *)
(* and, thus, simplifies the program.  The MakeSpace function can,           *)
(* unfortunately, not be moved across function calls or bignum operations,  *)
(* which can internally call the allocator.                                  *)
(*                                                                           *)
(* The MakeSpace command has an optional variable name list. If this list is *)
(* provided, i.e. SOME var_names, then only these variables can survive the  *)
(* execution of the MakeSpace command. The idea is that one generates        *)
(* MakeSpace X NONE when compiling into dataLang. Then optimisations move    *)
(* around and combine MakeSpace commands. Then liveness analysis annotates   *)
(* each MakeSpace command with a SOME. The translation from dataLang into    *)
(* more concete forms must implement a GC that only looks at the variables   *)
(* in the SOME annotations.                                                  *)
(*                                                                           *)
(* Notes on the rendering: FUNPOW f n x is ITER n f x; op_space_reset (a     *)
(* catch-all clause completed into one clause per constructor) is defined   *)
(* with sem1aux_def (semantics/sem1aux_tfl.ml).                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* Syntax of dataLang *)

let op_space_reset_def = sem1aux_def
  `(op_space_reset (IntOp clos_Add) <=> T) /\
   (op_space_reset (IntOp clos_Sub) <=> T) /\
   (op_space_reset (IntOp Mult) <=> T) /\
   (op_space_reset (IntOp clos_Div) <=> T) /\
   (op_space_reset (IntOp clos_Mod) <=> T) /\
   (op_space_reset (IntOp clos_Less) <=> T) /\
   (op_space_reset (IntOp LessEq) <=> T) /\
   (op_space_reset (IntOp Greater) <=> T) /\
   (op_space_reset (IntOp GreaterEq) <=> T) /\
   (op_space_reset (BlockOp clos_Equal) <=> T) /\
   (op_space_reset (BlockOp clos_ListAppend) <=> T) /\
   (op_space_reset (BlockOp (FromList _)) <=> T) /\
   (op_space_reset (MemOp RefArray) <=> T) /\
   (op_space_reset (MemOp (RefByte _)) <=> T) /\
   (op_space_reset (BlockOp (ConsExtend _)) <=> T) /\
   (op_space_reset (MemOp (CopyByte new_flag)) <=> new_flag) /\
   (op_space_reset (MemOp clos_ConfigGC) <=> T) /\
   (op_space_reset (clos_FFI _) <=> T) /\
   (op_space_reset _ <=> F)`;;

let op_requires_names_def = cake_def
  `op_requires_names op <=>
     op_space_reset op \/ (?n. op = clos_FFI n) \/
     (?new_flag. op = MemOp (CopyByte new_flag)) \/
     op = MemOp XorByte \/
     (?b cmp. op = MemOp (StringCmp b cmp)) \/
     op = clos_Install`;;

(* data_Call: return var and cut-set, target of call, arguments, handler    *)
(* (varname, handler code)                                                   *)

let data_prog_INDUCT,data_prog_RECURSION = cake_type
  "data_prog = data_Skip
             | data_Move num num
             | data_Call ((num list # num_set) option) (num option) (num list)
                         ((num # data_prog) option)
             | data_Assign num clos_op (num list) (num_set option)
             | data_Seq data_prog data_prog
             | data_If num data_prog data_prog
             | MakeSpace num num_set
             | data_Raise num
             | data_Return (num list)
             | data_Tick
             | data_Force ((num # num_set) option) num num";;

let mk_ticks_def = cake_def
  `mk_ticks n e = ITER n (data_Seq data_Tick) e`;;
