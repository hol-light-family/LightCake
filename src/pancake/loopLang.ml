(* ========================================================================= *)
(* loopLang: port of HOL4 pancake/loopLangScript.sml (CakeML v3479).         *)
(* loopLang intermediate language.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: loop_exp, loop_prog and the                *)
(*   constructors that clash with other languages (loop_Const, loop_Var,     *)
(*   loop_Seq, ...); Mark, LocValue and the loop_arith constructors keep     *)
(*   their names.                                                            *)
(* - HOL4 Type shift = ast$shift is the type abbreviation loop_shift.        *)
(* - HOL4 exp_size l is loop_exp_size l; exp1_size l (the size of an exp     *)
(*   list) is list_size (loop_exp_size l).                                   *)
(* - num_set is 1 spt and () is one; ++ is APPEND.                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/panLang.ml";;

prioritize_num();;
type_invention_error := true;;

new_type_abbrev("loop_shift",`:shift`);;

let loop_exp_INDUCT,loop_exp_RECURSION = cake_type
  "loop_exp = loop_Const (A word)
            | loop_Var num
            | loop_Lookup (5 word)
            | loop_Load loop_exp
            | loop_Op binop (loop_exp list)
            | loop_Shift shift loop_exp loop_exp
            | loop_BaseAddr
            | loop_TopAddr";;

let loop_arith_INDUCT,loop_arith_RECURSION = cake_type
  "loop_arith = LLongMul num num num num
              | LLongDiv num num num num num
              | LDiv num num num";;

(* loop_Assign, loop_Store, loop_SetGlobal: dest, source.  loop_Loop: names *)
(* in, body, names out.  LocValue: assign v1 := Loc v2 0.  loop_Call:       *)
(* return var, target of call, arguments, and the handler: var to store the *)
(* exception, exception-handler code, normal-return handler code, live vars *)
(* after the call.  loop_FFI: FFI name, conf_ptr, conf_len, array_ptr,      *)
(* array_len, cut-set.                                                      *)

let loop_prog_INDUCT,loop_prog_RECURSION = cake_type
  "loop_prog = loop_Skip
             | loop_Assign num ((A)loop_exp)
             | loop_Primitive (num list) primop (num list)
             | loop_Arith loop_arith
             | loop_Store ((A)loop_exp) num
             | loop_SetGlobal (5 word) ((A)loop_exp)
             | loop_Load32 num num
             | loop_LoadByte num num
             | loop_Store32 num num
             | loop_StoreByte num num
             | loop_Seq loop_prog loop_prog
             | loop_If cmp num ((A)reg_imm) loop_prog loop_prog num_set
             | loop_Loop num_set loop_prog num_set
             | loop_Break num
             | loop_Continue num
             | loop_Raise num
             | loop_Return (num list)
             | loop_ShMem memop num ((A)loop_exp)
             | loop_Tick
             | Mark loop_prog
             | loop_Fail
             | LocValue num num
             | loop_Call ((num list # num_set) option) (num option) (num list)
                         ((num # loop_prog # loop_prog # num_set) option)
             | loop_FFI mlstring num num num num num_set";;

(* HOL4: MEM_IMP_exp_size *)

let loop_MEM_IMP_exp_size = prove
 (`!xs (a:(A)loop_exp).
     MEM a xs ==> loop_exp_size l a < list_size (loop_exp_size l) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)loop_exp`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

(* HOL4: nested_seq *)

let loop_nested_seq_def = cake_def
  `(loop_nested_seq [] = loop_Skip:(A)loop_prog) /\
   (loop_nested_seq (CONS e es) = loop_Seq e (loop_nested_seq es))`;;

let locals_touched_def = cake_def
  `(locals_touched (loop_Const (w:A word)) = []) /\
   (locals_touched (loop_Var v) = [v]) /\
   (locals_touched (loop_Lookup name) = []) /\
   (locals_touched (loop_Load addr) = locals_touched addr) /\
   (locals_touched (loop_Op op wexps) = FLAT (MAP locals_touched wexps)) /\
   (locals_touched (loop_Shift sh wexp1 wexp2) =
      APPEND (locals_touched wexp1) (locals_touched wexp2)) /\
   (locals_touched loop_BaseAddr = []) /\
   (locals_touched loop_TopAddr = [])`;;

let locals_touched_ind = cake_ind "locals_touched";;

(* HOL4: assigned_vars *)

(* the clauses are parsed one by one (HOL4 types each clause on its own:   *)
(* ns is a num_set in loop_If and a num list in loop_Call)                *)

let loop_assigned_vars_def = cake_def_clauses
 [`loop_assigned_vars (loop_Skip:(A)loop_prog) = []:num list`;
  `loop_assigned_vars (loop_Assign n e:(A)loop_prog) = [n]`;
  `loop_assigned_vars (loop_Primitive lhss pop rhss:(A)loop_prog) = lhss`;
  `loop_assigned_vars (loop_Arith arith:(A)loop_prog) =
     match arith with
       LLongMul v1 v2 v3 v4 -> [v1; v2]
     | LLongDiv v1 v2 v3 v4 v5 -> [v1; v2]
     | LDiv v1 v2 v3 -> [v1]`;
  `loop_assigned_vars (loop_Load32 n m:(A)loop_prog) = [m]`;
  `loop_assigned_vars (loop_LoadByte n m:(A)loop_prog) = [m]`;
  `loop_assigned_vars (loop_Seq p q:(A)loop_prog) =
     APPEND (loop_assigned_vars p) (loop_assigned_vars q):num list`;
  `loop_assigned_vars (loop_If cmp n r p q ns:(A)loop_prog) =
     APPEND (loop_assigned_vars p) (loop_assigned_vars q):num list`;
  `loop_assigned_vars (LocValue n m:(A)loop_prog) = [n]`;
  `loop_assigned_vars (loop_ShMem op n e:(A)loop_prog) = [n]`;
  `loop_assigned_vars (Mark p:(A)loop_prog) = loop_assigned_vars p:num list`;
  `loop_assigned_vars (loop_Loop _ p _:(A)loop_prog) = loop_assigned_vars p:num list`;
  `loop_assigned_vars (loop_Call NONE _ _ _:(A)loop_prog) = []:num list`;
  `loop_assigned_vars (loop_Call (SOME (ns,_)) _ _ NONE:(A)loop_prog) = ns`;
  `loop_assigned_vars (loop_Call (SOME (ns,_)) _ _ (SOME (m,p,q,_)):(A)loop_prog) =
     APPEND (APPEND ns (CONS m (loop_assigned_vars p))) (loop_assigned_vars q)`;
  `loop_assigned_vars (_:(A)loop_prog) = []:num list`];;

let acc_vars_def = cake_def
  `(acc_vars (loop_Seq p1 p2:(A)loop_prog) l = acc_vars p1 (acc_vars p2 l)) /\
   (acc_vars (loop_Break _) l = (l:num_set)) /\
   (acc_vars (loop_Continue _) l = l) /\
   (acc_vars (loop_Loop l1 body l2) l = acc_vars body l) /\
   (acc_vars (loop_If x1 x2 x3 p1 p2 l1) l = acc_vars p1 (acc_vars p2 l)) /\
   (acc_vars (loop_Arith arith) l =
      match arith with
        LLongMul v1 v2 v3 v4 -> insert v1 one (insert v2 one l)
      | LLongDiv v1 v2 v3 v4 v5 -> insert v1 one (insert v2 one l)
      | LDiv v1 v2 v3 -> insert v1 one l) /\
   (acc_vars (Mark p1) l = acc_vars p1 l) /\
   (acc_vars loop_Tick l = l) /\
   (acc_vars loop_Skip l = l) /\
   (acc_vars loop_Fail l = l) /\
   (acc_vars (loop_Raise v) l = l) /\
   (acc_vars (loop_Return vs) l = l) /\
   (acc_vars (loop_Call ret dest args handler) l =
      match ret with
        NONE -> l
      | SOME (vs,live) ->
          let l = list_insert vs l in
          match handler with
            NONE -> l
          | SOME (n,p1,p2,l1) -> acc_vars p1 (acc_vars p2 (insert n one l))) /\
   (acc_vars (LocValue n m) l = insert n one l) /\
   (acc_vars (loop_Assign n exp) l = insert n one l) /\
   (acc_vars (loop_Primitive lhss pop rhss) l = list_insert lhss l) /\
   (acc_vars (loop_ShMem op n exp) l = insert n one l) /\
   (acc_vars (loop_Store exp n) l = l) /\
   (acc_vars (loop_SetGlobal w exp) l = l) /\
   (acc_vars (loop_Load32 n m) l = insert m one l) /\
   (acc_vars (loop_LoadByte n m) l = insert m one l) /\
   (acc_vars (loop_Store32 n m) l = l) /\
   (acc_vars (loop_StoreByte n m) l = l) /\
   (acc_vars (loop_FFI name n1 n2 n3 n4 live) l = l)`;;

let acc_vars_ind = cake_ind "acc_vars";;
