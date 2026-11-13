(* ========================================================================= *)
(* flat_to_clos: port of HOL4 compiler/backend/flat_to_closScript.sml        *)
(* (CakeML v3479).                                                           *)
(* Compilation from flatLang to closLang. This compiler phase converts      *)
(* explicit variable names of flatLang to de Bruijn indexing of closLang.   *)
(* It also makes all division-by-zero and out-of-bounds exceptions raised    *)
(* explicitly.                                                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so the NAME_pmatch theorems restate the definitions in match form.      *)
(* - HOL4 builds the bodies of CopyByteStr and CopyByteAw8 with the ML       *)
(*   functions check1 and var_fun; they are written out here.               *)
(* - HOL4 None (the trace) is backend_common_None; flatLang exp6_size is     *)
(*   list_size flat_exp_size; ZIP (l1,l2) is ZIP l1 l2; the mlstring         *)
(*   literals are implode "...".                                             *)
(* - Definitions with catch-all clauses are made with sem1aux_def(_wf)       *)
(*   (semantics/sem1aux_tfl.ml).                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let dest_pat_def = sem1aux_def
  `(dest_pat [(flat_Pvar v, h)] = SOME (v:mlstring,h:flat_exp)) /\
   (dest_pat _ = NONE)`;;

let dest_pat_pmatch = prove
 (CASE_TERM
  `!x. dest_pat x =
       match x with [(flat_Pvar v, h)] -> SOME (v:mlstring,h:flat_exp) | _ -> NONE`,
  GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[dest_pat_def]) THEN
  FS[dest_pat_def]);;

let dest_pat_thm = prove
 (`!pes p_1 p_2. dest_pat pes = SOME (p_1,p_2) <=> pes = [(flat_Pvar p_1, p_2)]`,
  GEN_TAC THEN CASES_ON `pes:(flat_pat # flat_exp) list` THEN FS[dest_pat_def] THEN
  CASES_ON `a1:(flat_pat # flat_exp) list` THEN FS[dest_pat_def] THEN
  CASES_ON `a0:flat_pat # flat_exp` THEN CASES_ON `x:flat_pat` THEN
  FS[dest_pat_def; PAIR_EQ] THEN MESON_TAC[]);;

let compile_lit_def = cake_def
  `compile_lit t l =
     clos_Op t
       (match l with
          IntLit i -> IntOp (clos_Const i)
        | Char c -> IntOp (clos_Const (&(ORD c)))
        | StrLit s -> BlockOp (Constant (ConstStr s))
        | Word8 b -> IntOp (clos_Const (&(val b)))
        | Word64 w -> BlockOp (Constant (ConstWord64 w))
        | Float64 w -> BlockOp (Constant (ConstWord64 w))) []`;;

(* HOL4: arg1, arg2 *)

let flat_to_clos_arg1_def = cake_def
  `flat_to_clos_arg1 xs (f:clos_exp->clos_exp) =
     match xs with
       [x] -> f x
     | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0)`;;

let arg1_pmatch = prove
 (CASE_TERM
  `!xs f. flat_to_clos_arg1 xs (f:clos_exp->clos_exp) =
          match xs with
            [x] -> f x
          | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0)`,
  REWRITE_TAC[flat_to_clos_arg1_def]);;

let flat_to_clos_arg2_def = cake_def
  `flat_to_clos_arg2 xs (f:clos_exp->clos_exp->clos_exp) =
     match xs with
       [x; y] -> f x y
     | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0)`;;

(* HOL4: arg2_pmatch *)

let flat_to_clos_arg2_pmatch = prove
 (CASE_TERM
  `!xs f. flat_to_clos_arg2 xs (f:clos_exp->clos_exp->clos_exp) =
          match xs with
            [x; y] -> f x y
          | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0)`,
  REWRITE_TAC[flat_to_clos_arg2_def]);;

(* HOL4's ML check1 (var_fun 2) and check1 (var_fun 4), written out: the     *)
(* bounds checks around the byte copies                                      *)

let CopyByteStr_def = cake_def
  `CopyByteStr t =
     clos_If t (clos_Op t (IntOp clos_Less)
                  [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 0])
       (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t (clos_Op t (IntOp clos_Less)
                  [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 1])
       (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t (clos_Op t (MemOp (BoundsCheckByte T))
                  [clos_Op t (IntOp clos_Add) [clos_Var t 0; clos_Var t 1];
                   clos_Var t 2])
       (clos_Op t (MemOp (CopyByte T)) [clos_Var t 0; clos_Var t 1; clos_Var t 2])
       (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))))`;;

let CopyByteAw8_def = cake_def
  `CopyByteAw8 t =
     clos_If t (clos_Op t (IntOp clos_Less)
                  [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 2])
       (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t (clos_Op t (IntOp clos_Less)
                  [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 3])
       (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t (clos_Op t (MemOp (BoundsCheckByte T))
                  [clos_Op t (IntOp clos_Add) [clos_Var t 2; clos_Var t 3];
                   clos_Var t 4])
       (clos_If t (clos_Op t (IntOp clos_Less)
                    [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 0])
          (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
          (clos_If t (clos_Op t (MemOp (BoundsCheckByte T))
                       [clos_Op t (IntOp clos_Add) [clos_Var t 2; clos_Var t 0];
                        clos_Var t 1])
             (clos_Op t (MemOp (CopyByte F))
                [clos_Var t 0; clos_Var t 1; clos_Var t 2; clos_Var t 3;
                 clos_Var t 4])
             (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))))
       (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))))`;;

let compile_arith_def = cake_def
  `compile_arith t (a:arith) ty xs =
     match ty with
       IntT ->
         (match a with
            Add -> clos_Op t (IntOp clos_Add) xs
          | Sub -> clos_Op t (IntOp clos_Sub) xs
          | Mul -> clos_Op t (IntOp Mult) xs
          | Div -> clos_Let t xs
                     (clos_If t (clos_Op t (BlockOp clos_Equal)
                                   [clos_Var t 0; clos_Op t (IntOp (clos_Const (&0))) []])
                        (clos_Raise t (clos_Op t (BlockOp (clos_Cons div_tag)) []))
                        (clos_Op t (IntOp clos_Div) [clos_Var t 0; clos_Var t 1]))
          | Mod -> clos_Let t xs
                     (clos_If t (clos_Op t (BlockOp clos_Equal)
                                   [clos_Var t 0; clos_Op t (IntOp (clos_Const (&0))) []])
                        (clos_Raise t (clos_Op t (BlockOp (clos_Cons div_tag)) []))
                        (clos_Op t (IntOp clos_Mod) [clos_Var t 0; clos_Var t 1]))
          | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0))
     | Float64T ->
         (match a with
            Abs -> clos_Op t (WordOp (FP_uop FP_Abs)) xs
          | Neg -> clos_Op t (WordOp (FP_uop FP_Neg)) xs
          | Sqrt -> clos_Op t (WordOp (FP_uop FP_Sqrt)) xs
          | Add -> clos_Op t (WordOp (FP_bop FP_Add)) xs
          | Sub -> clos_Op t (WordOp (FP_bop FP_Sub)) xs
          | Mul -> clos_Op t (WordOp (FP_bop FP_Mul)) xs
          | Div -> clos_Op t (WordOp (FP_bop FP_Div)) xs
          | FMA -> clos_Op t (WordOp (FP_top FP_Fma)) xs
          | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0))
     | WordT ws ->
         (match a with
            Add -> clos_Op t (WordOp (WordOpw ws backend_common_Add)) xs
          | Sub -> clos_Op t (WordOp (WordOpw ws backend_common_Sub)) xs
          | And -> clos_Op t (WordOp (WordOpw ws Andw)) xs
          | Or -> clos_Op t (WordOp (WordOpw ws Orw)) xs
          | Xor -> clos_Op t (WordOp (WordOpw ws backend_common_Xor)) xs
          | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0))
     | BoolT -> clos_Op t (BlockOp BoolNot) xs
     | _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0)`;;

(* HOL4: compile_op *)

let flat_to_clos_compile_op_def = cake_def
  `flat_to_clos_compile_op t op xs =
     match op with
       flat_TagLenEq tag n -> clos_Op t (BlockOp (clos_TagLenEq tag n)) xs
     | flat_LenEq n -> clos_Op t (BlockOp (clos_LenEq n)) xs
     | flat_El n ->
         flat_to_clos_arg1 xs
           (\x. clos_Op t (MemOp clos_El)
                  [clos_Op backend_common_None (IntOp (clos_Const (&n))) []; x])
     | GlobalVarAlloc n ->
         clos_Let t xs
           (clos_Op t (GlobOp AllocGlobal) [clos_Op t (IntOp (clos_Const (&n))) []])
     | GlobalVarInit n -> clos_Op t (GlobOp (SetGlobal (n + 1))) xs
     | GlobalVarLookup n -> clos_Op t (GlobOp (clos_Global (n + 1))) xs
     | Id -> flat_to_clos_arg1 xs (\x. x)
     | Src Opapp -> flat_to_clos_arg2 xs (\x f. clos_App t NONE f [x])
     | Src Opassign ->
         flat_to_clos_arg2 xs
           (\x y. clos_Op t (MemOp Update)
                    [x; clos_Op backend_common_None (IntOp (clos_Const (&0))) []; y])
     | Src Opref -> clos_Op t (MemOp clos_Ref) xs
     | Src ConfigGC -> clos_Op t (MemOp clos_ConfigGC) xs
     | Src Equality -> clos_Op t (BlockOp clos_Equal) xs
     | Src (FFI n) -> clos_Op t (clos_FFI n) xs
     | Src ListAppend -> clos_Op t (BlockOp clos_ListAppend) xs
     | Src Vlength -> clos_Op t (BlockOp LengthBlock) xs
     | Src Alength -> clos_Op t (MemOp Length) xs
     | Src Implode -> clos_Op t (MemOp FromListByte) xs
     | Src Explode -> clos_Op t (MemOp ToListByte) xs
     | Src Strlen -> clos_Op t (MemOp LengthByteVec) xs
     | Src Strcat -> clos_Op t (MemOp ConcatByteVec) xs
     | Src CopyStrStr -> clos_Let t xs (CopyByteStr t)
     | Src CopyStrAw8 -> clos_Let t xs (CopyByteAw8 t)
     | Src CopyAw8Str -> clos_Let t xs (CopyByteStr t)
     | Src CopyAw8Aw8 -> clos_Let t xs (CopyByteAw8 t)
     | Src XorAw8Str_unsafe -> clos_Op t (MemOp XorByte) xs
     | Src VfromList -> clos_Op t (BlockOp (FromList 0)) xs
     | Src (Test test test_ty) ->
         (match test_ty with
            BoolT -> clos_Op t (BlockOp (BoolTest test)) xs
          | CharT -> clos_Op t (WordOp (WordTest W8 test)) xs
          | WordT W8 -> clos_Op t (WordOp (WordTest W8 test)) xs
          | IntT ->
              (match test with
                 Compare Lt -> clos_Op t (IntOp clos_Less) xs
               | Compare Leq -> clos_Op t (IntOp LessEq) xs
               | Compare Gt -> clos_Op t (IntOp Greater) xs
               | Compare Geq -> clos_Op t (IntOp GreaterEq) xs
               | _ -> clos_Op t (BlockOp clos_Equal) xs)
          | Float64T ->
              (match test with
                 Compare Lt -> clos_Op t (WordOp (FP_cmp FP_Less)) xs
               | Compare Leq -> clos_Op t (WordOp (FP_cmp FP_LessEqual)) xs
               | Compare Gt -> clos_Op t (WordOp (FP_cmp FP_Greater)) xs
               | Compare Geq -> clos_Op t (WordOp (FP_cmp FP_GreaterEqual)) xs
               | _ -> clos_Op t (WordOp (FP_cmp FP_Equal)) xs)
          | StrT ->
              (match test with
                 Compare opb -> clos_Op t (MemOp (StringCmp F opb)) xs
               | AltCompare opb -> clos_Op t (MemOp (StringCmp T opb)) xs
               | _ -> clos_Op t (BlockOp clos_Equal) xs)
          | _ -> clos_Op t (BlockOp clos_Equal) xs)
     | Src Aw8length -> clos_Op t (MemOp LengthByte) xs
     | Src AallocFixed -> clos_Op t (MemOp clos_Ref) xs
     | Src Aalloc ->
         clos_Let t xs
           (clos_If t (clos_Op t (IntOp clos_Less)
                         [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 1])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
              (clos_Op t (MemOp RefArray) [clos_Var t 0; clos_Var t 1]))
     | Src Aw8alloc ->
         clos_Let t xs
           (clos_If t (clos_Op t (IntOp clos_Less)
                         [clos_Op t (IntOp (clos_Const (&0))) []; clos_Var t 1])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) []))
              (clos_Op t (MemOp (RefByte F)) [clos_Var t 0; clos_Var t 1]))
     | Src Vsub ->
         clos_Let t xs
           (clos_If t (clos_Op t (BlockOp BoundsCheckBlock) [clos_Var t 0; clos_Var t 1])
              (clos_Op t (MemOp clos_El) [clos_Var t 0; clos_Var t 1])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) [])))
     | Src Vsub_unsafe -> clos_Op t (MemOp clos_El) xs
     | Src Asub ->
         clos_Let t xs
           (clos_If t (clos_Op t (MemOp BoundsCheckArray) [clos_Var t 0; clos_Var t 1])
              (clos_Op t (MemOp clos_El) [clos_Var t 0; clos_Var t 1])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) [])))
     | Src Asub_unsafe -> clos_Op t (MemOp clos_El) xs
     | Src Aupdate ->
         clos_Let t xs
           (clos_If t (clos_Op t (MemOp BoundsCheckArray) [clos_Var t 1; clos_Var t 2])
              (clos_Op t (MemOp Update) [clos_Var t 0; clos_Var t 1; clos_Var t 2])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) [])))
     | Src Aupdate_unsafe -> clos_Op t (MemOp Update) xs
     | Src Aw8sub ->
         clos_Let t xs
           (clos_If t (clos_Op t (MemOp (BoundsCheckByte F)) [clos_Var t 0; clos_Var t 1])
              (clos_Op t (MemOp DerefByte) [clos_Var t 0; clos_Var t 1])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) [])))
     | Src Aw8sub_unsafe -> clos_Op t (MemOp DerefByte) xs
     | Src Aw8update ->
         clos_Let t xs
           (clos_If t (clos_Op t (MemOp (BoundsCheckByte F)) [clos_Var t 1; clos_Var t 2])
              (clos_Op t (MemOp UpdateByte) [clos_Var t 0; clos_Var t 1; clos_Var t 2])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) [])))
     | Src Aw8update_unsafe -> clos_Op t (MemOp UpdateByte) xs
     | Src Strsub ->
         clos_Let t xs
           (clos_If t (clos_Op t (MemOp (BoundsCheckByte F)) [clos_Var t 0; clos_Var t 1])
              (clos_Op t (MemOp DerefByteVec) [clos_Var t 0; clos_Var t 1])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons subscript_tag)) [])))
     | Src (Shift x1 x2 x3) -> clos_Op t (WordOp (WordShift x1 x2 x3)) xs
     | Src Eval -> clos_Op t clos_Install xs
     | Src (ThunkOp top) -> clos_Op t (clos_ThunkOp top) xs
     | Src (Arith a ty) -> compile_arith t a ty xs
     | Src (FromTo (WordT W8) IntT) -> flat_to_clos_arg1 xs (\x. x)
     | Src (FromTo (WordT W64) IntT) -> clos_Op t (WordOp WordToInt) xs
     | Src (FromTo IntT (WordT W8)) ->
         flat_to_clos_arg1 xs
           (\x. clos_Op t (IntOp clos_Mod) [clos_Op t (IntOp (clos_Const (&256))) []; x])
     | Src (FromTo IntT (WordT W64)) -> clos_Op t (WordOp WordFromInt) xs
     | Src (FromTo IntT CharT) ->
         clos_Let t xs
           (clos_If t (clos_Op t (IntOp clos_Less)
                         [clos_Op backend_common_None (IntOp (clos_Const (&0))) [];
                          clos_Var t 0])
              (clos_Raise t (clos_Op t (BlockOp (clos_Cons chr_tag)) []))
              (clos_If t (clos_Op t (IntOp clos_Less)
                            [clos_Var t 0;
                             clos_Op backend_common_None (IntOp (clos_Const (&255))) []])
                 (clos_Raise t (clos_Op t (BlockOp (clos_Cons chr_tag)) []))
                 (clos_Var t 0)))
     | Src (FromTo Float64T (WordT W64)) ->
         clos_Let backend_common_None xs (clos_Var backend_common_None 0)
     | Src (FromTo (WordT W64) Float64T) ->
         clos_Let backend_common_None xs (clos_Var backend_common_None 0)
     | Src _ -> clos_Let backend_common_None xs (clos_Var backend_common_None 0)`;;

let join_strings_def = cake_def
  `join_strings (x:mlstring) y =
     if strlen x = 0 then y else mlstring_concat [x; implode "_"; y]`;;

let dest_nop_def = cake_def
  `dest_nop op e =
     if op = Src (FromTo IntT (WordT W8)) then
       (match e with
          [flat_App _ op1 [x]] ->
            (if op1 = Src (FromTo CharT IntT) then SOME x else NONE)
        | _ -> NONE)
     else if op = Src (FromTo IntT CharT) then
       (match e with
          [flat_App _ op1 [x]] ->
            (if op1 = Src (FromTo (WordT W8) IntT) then SOME x else NONE)
        | _ -> NONE)
     else NONE`;;

let dest_nop_thm = prove
 (`!op es x.
     dest_nop op es = SOME x <=>
     (?t. op = Src (FromTo IntT (WordT W8)) /\
          es = [flat_App t (Src (FromTo CharT IntT)) [x]]) \/
     (?t. op = Src (FromTo IntT CharT) /\
          es = [flat_App t (Src (FromTo (WordT W8) IntT)) [x]])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_nop_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN
  FS[] THEN EVERY_CASE_TAC THEN FS[] THEN MESON_TAC[]);;

(* HOL4: dest_Constant *)

let flat_to_clos_dest_Constant_def = sem1aux_def
  `(flat_to_clos_dest_Constant (clos_Op t (BlockOp (Constant c)) []) = SOME c) /\
   (flat_to_clos_dest_Constant (clos_Op t (IntOp (clos_Const i)) []) =
      SOME (ConstInt i)) /\
   (flat_to_clos_dest_Constant (clos_Op t (BlockOp (clos_Cons n)) []) =
      SOME (ConstCons n [])) /\
   (flat_to_clos_dest_Constant _ = NONE)`;;

(* HOL4: dest_Constant_pmatch *)

let flat_to_clos_dest_Constant_pmatch = prove
 (CASE_TERM
  `!xs. flat_to_clos_dest_Constant xs =
        match xs with
          clos_Op t (BlockOp (Constant x)) [] -> SOME x
        | clos_Op t (IntOp (clos_Const i)) [] -> SOME (ConstInt i)
        | clos_Op t (BlockOp (clos_Cons n)) [] -> SOME (ConstCons n [])
        | _ -> NONE`,
  GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN
                       ASM_REWRITE_TAC[flat_to_clos_dest_Constant_def]) THEN
  FS[flat_to_clos_dest_Constant_def]);;

let dest_Constants_def = cake_def
  `(dest_Constants [] = SOME []) /\
   (dest_Constants (CONS c cs) =
      match flat_to_clos_dest_Constant c with
        NONE -> NONE
      | SOME x ->
          (match dest_Constants cs with
             NONE -> NONE
           | SOME xs -> SOME (CONS x xs)))`;;

let SmartCons_def = cake_def
  `SmartCons t tag xs =
     if NULL xs then clos_Op t (BlockOp (clos_Cons tag)) [] else
     match dest_Constants xs with
       NONE -> clos_Op t (BlockOp (clos_Cons tag)) xs
     | SOME cs -> clos_Op t (BlockOp (Constant (ConstCons tag (REVERSE cs)))) []`;;

(* termination of compile: as HOL4, with dest_nop_thm, dest_pat_thm and the *)
(* sizes of a reversed list                                                   *)

let IL1AUX_F2C_TC_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
     is_neg (concl th) && is_exists (dest_neg (concl th))))) THEN
   RULE_ASSUM_TAC (fun th ->
     let c = concl th in
     if is_eq c && is_comb (lhs c) &&
        (try fst(dest_const(rator(lhs c))) = "SOME" with Failure _ -> false)
     then SYM th else th) THEN
   RULE_ASSUM_TAC (REWRITE_RULE[dest_nop_thm; dest_pat_thm]) THEN
   REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN (X_CHOOSE_THEN `tt:tra` STRIP_ASSUME_TAC) o
                          check (is_disj o concl))) THEN
   RVEQ_TAC THEN REWRITE_TAC(WF_REL_THMS @ [FST; SND; exp6_size_REVERSE]) THEN
   TERM_TAC);;

(* HOL4: compile *)

let flat_to_clos_compile_def = sem1aux_def_wf
  `measure (\p:(mlstring option) list # flat_exp list.
              list_size flat_exp_size (SND p))`
  IL1AUX_F2C_TC_TAC
  `(flat_to_clos_compile m [] = []) /\
   (flat_to_clos_compile m (CONS x (CONS y xs)) =
      APPEND (flat_to_clos_compile m [x]) (flat_to_clos_compile m (CONS y xs))) /\
   (flat_to_clos_compile m [flat_Raise t e] =
      [clos_Raise t (HD (flat_to_clos_compile m [e]))]) /\
   (flat_to_clos_compile m [flat_Lit t l] = [compile_lit t l]) /\
   (flat_to_clos_compile m [Var_local t v] = [clos_Var t (findi (SOME v) m)]) /\
   (flat_to_clos_compile m [flat_Con t n es] =
      let tag = (match n with SOME (tg,_) -> tg | _ -> 0) in
        [SmartCons t tag (flat_to_clos_compile m (REVERSE es))]) /\
   (flat_to_clos_compile m [flat_App t op es] =
      match dest_nop op es with
        SOME e -> flat_to_clos_compile m [e]
      | NONE ->
          [flat_to_clos_compile_op t op (flat_to_clos_compile m (REVERSE es))]) /\
   (flat_to_clos_compile m [flat_Fun nm v e] =
      [Fn nm NONE NONE 1 (HD (flat_to_clos_compile (CONS (SOME v) m) [e]))]) /\
   (flat_to_clos_compile m [flat_If t x1 x2 x3] =
      [clos_If t (HD (flat_to_clos_compile m [x1]))
                 (HD (flat_to_clos_compile m [x2]))
                 (HD (flat_to_clos_compile m [x3]))]) /\
   (flat_to_clos_compile m [flat_Let t vo e1 e2] =
      [clos_Let t (flat_to_clos_compile m [e1])
         (HD (flat_to_clos_compile (CONS vo m) [e2]))]) /\
   (flat_to_clos_compile m [flat_Mat t e pes] =
      [clos_Op t (IntOp (clos_Const (&0))) []]) /\
   (flat_to_clos_compile m [flat_Handle t e pes] =
      match dest_pat pes with
        SOME (v,h) ->
          [clos_Handle t (HD (flat_to_clos_compile m [e]))
             (HD (flat_to_clos_compile (CONS (SOME v) m) [h]))]
      | _ -> flat_to_clos_compile m [e]) /\
   (flat_to_clos_compile m [flat_Letrec nm funs e] =
      let new_m = APPEND (MAP (\n. SOME (FST n)) funs) m in
        [clos_Letrec (MAP (\n. join_strings nm (FST n)) funs) NONE NONE
           (MAP (\p. match p with
                       (f,v,x) ->
                         (1, HD (flat_to_clos_compile (CONS (SOME v) new_m) [x])))
                funs)
           (HD (flat_to_clos_compile new_m [e]))])`;;

let flat_to_clos_compile_ind = cake_ind "flat_to_clos_compile";;

(* HOL4: compile_decs *)

let flat_to_clos_compile_decs_def = cake_def
  `(flat_to_clos_compile_decs [] = []) /\
   (flat_to_clos_compile_decs (CONS e xs) =
      APPEND (flat_to_clos_compile [] [e]) (flat_to_clos_compile_decs xs))`;;

(* HOL4: compile_prog *)

let flat_to_clos_compile_prog_def = cake_def
  `flat_to_clos_compile_prog xs =
     attach_interpreter (flat_to_clos_compile_decs xs)`;;

let inc_compile_decs_def = cake_def
  `inc_compile_decs decs =
     let xs = APPEND (flat_to_clos_compile_decs decs)
                     (flat_to_clos_compile_decs
                        [flat_Con backend_common_None NONE []]) in
       (insert_interp xs,[]:(num # num # clos_exp) list)`;;

let LENGTH_compile = prove
 (`!m xs. LENGTH (flat_to_clos_compile m xs) = LENGTH xs`,
  MATCH_MP_TAC flat_to_clos_compile_ind THEN
  REWRITE_TAC[flat_to_clos_compile_def; LENGTH; LENGTH_APPEND] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
  REPEAT STRIP_TAC THEN TRY (POP_ASSUM MP_TAC) THEN
  EVERY_CASE_TAC THEN ASM_SIMP_TAC[LENGTH] THEN ARITH_TAC);;

let compile_NOT_NIL = prove
 (`!m x xs. ~(flat_to_clos_compile m (CONS x xs) = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_compile; LENGTH; NOT_SUC]);;
let _ = cake_add_simps [compile_NOT_NIL];;

let HD_compile = prove
 (`!m x. [HD (flat_to_clos_compile m [x])] = flat_to_clos_compile m [x]`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`m:(mlstring option) list`; `[x:flat_exp]`] LENGTH_compile) THEN
  SPEC_TAC (`flat_to_clos_compile m [x]`,`l:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  SIMP_TAC[HD]);;
let _ = cake_add_simps [HD_compile];;
