(* ========================================================================= *)
(* stack_names: port of HOL4 compiler/backend/stack_namesScript.sml          *)
(* (CakeML v3479).                                                           *)
(* This compiler phase renames the registers to fit with the target         *)
(* architecture.                                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stackLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 Overload find_name = tlookup: tlookup (misc) is written out.       *)
(* - HOL4 GENLIST f n is list_of_seq f n, EVERY is ALL.                      *)

let ri_find_name_def = cake_def
  `(ri_find_name f (Reg r) = Reg (tlookup f r):(A)reg_imm) /\
   (ri_find_name f (Imm (w:A word)) = Imm w)`;;

let inst_find_name_def = cake_def
  `inst_find_name f (i:(A)inst) =
     match i with
       asm_Skip -> asm_Skip
     | asm_Const r w -> asm_Const (tlookup f r) w
     | asm_Arith (Binop bop d r ri) ->
         asm_Arith (Binop bop (tlookup f d) (tlookup f r) (ri_find_name f ri))
     | asm_Arith (asm_Shift sop d r ri) ->
         asm_Arith (asm_Shift sop (tlookup f d) (tlookup f r)
                      (ri_find_name f ri))
     | asm_Arith (asm_Div r1 r2 r3) ->
         asm_Arith (asm_Div (tlookup f r1) (tlookup f r2) (tlookup f r3))
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
         asm_Arith (asm_AddCarry (tlookup f r1) (tlookup f r2) (tlookup f r3)
                      (tlookup f r4))
     | asm_Arith (AddOverflow r1 r2 r3 r4) ->
         asm_Arith (AddOverflow (tlookup f r1) (tlookup f r2) (tlookup f r3)
                      (tlookup f r4))
     | asm_Arith (SubOverflow r1 r2 r3 r4) ->
         asm_Arith (SubOverflow (tlookup f r1) (tlookup f r2) (tlookup f r3)
                      (tlookup f r4))
     | asm_Arith (LongMul r1 r2 r3 r4) ->
         asm_Arith (LongMul (tlookup f r1) (tlookup f r2) (tlookup f r3)
                      (tlookup f r4))
     | asm_Arith (LongDiv r1 r2 r3 r4 r5) ->
         asm_Arith (LongDiv (tlookup f r1) (tlookup f r2) (tlookup f r3)
                      (tlookup f r4) (tlookup f r5))
     | Mem mop r (Addr a w) -> Mem mop (tlookup f r) (Addr (tlookup f a) w)
     | FP (FPLess r f1 f2) -> FP (FPLess (tlookup f r) f1 f2)
     | FP (FPLessEqual r f1 f2) -> FP (FPLessEqual (tlookup f r) f1 f2)
     | FP (FPEqual r f1 f2) -> FP (FPEqual (tlookup f r) f1 f2)
     | FP (FPMovToReg r1 r2 d) ->
         FP (FPMovToReg (tlookup f r1) (tlookup f r2) d)
     | FP (FPMovFromReg d r1 r2) ->
         FP (FPMovFromReg d (tlookup f r1) (tlookup f r2))
     | i -> i`;;

let dest_find_name_def = cake_def
  `(dest_find_name f (INR r) = INR (tlookup f r):A+num) /\
   (dest_find_name f x = x)`;;

(* HOL4: comp_def (HOL4 proves termination automatically, with the size of *)
(* the program)                                                              *)

let stack_names_comp_def = cake_def_wf
  `measure (\(f:num spt,p:(A)stack_prog). stack_prog_size (\x:A. 0) p)`
  TERM_TAC
  `stack_names_comp f (p:(A)stack_prog) =
     match p with
       stack_Halt r -> stack_Halt (tlookup f r)
     | stack_Raise r -> stack_Raise (tlookup f r)
     | stack_Break n -> stack_Break n
     | stack_Continue n -> stack_Continue n
     | stack_Return r -> stack_Return (tlookup f r)
     | stack_Inst i -> stack_Inst (inst_find_name f i)
     | stack_LocValue i l1 l2 -> stack_LocValue (tlookup f i) l1 l2
     | stack_Seq p1 p2 -> stack_Seq (stack_names_comp f p1) (stack_names_comp f p2)
     | stack_If c r ri p1 p2 ->
         stack_If c (tlookup f r) (ri_find_name f ri) (stack_names_comp f p1)
                  (stack_names_comp f p2)
     | stack_Loop p1 -> stack_Loop (stack_names_comp f p1)
     | stack_Call ret dest exc ->
         stack_Call
           (match ret with
              NONE -> NONE
            | SOME (p1,lr,l1,l2) -> SOME (stack_names_comp f p1,tlookup f lr,l1,l2))
           (dest_find_name f dest)
           (match exc with
              NONE -> NONE
            | SOME (p2,l1,l2) -> SOME (stack_names_comp f p2,l1,l2))
     | stack_Install r1 r2 r3 r4 r5 ->
         stack_Install (tlookup f r1) (tlookup f r2) (tlookup f r3)
                       (tlookup f r4) (tlookup f r5)
     | ShMemOp op r (Addr a w) -> ShMemOp op (tlookup f r) (Addr (tlookup f a) w)
     | stack_CodeBufferWrite r1 r2 ->
         stack_CodeBufferWrite (tlookup f r1) (tlookup f r2)
     | stack_FFI i r1 r2 r3 r4 r5 ->
         stack_FFI i (tlookup f r1) (tlookup f r2) (tlookup f r3) (tlookup f r4)
                   (tlookup f r5)
     | JumpLower r1 r2 dest -> JumpLower (tlookup f r1) (tlookup f r2) dest
     | p -> p`;;

let stack_names_comp_ind = cake_ind "stack_names_comp";;

(* HOL4: comp_pmatch, comp_def stated with pmatch for case.  Here both are  *)
(* written as match and compile to the same case constants, so the          *)
(* statement is that of stack_names_comp_def.                               *)

let stack_names_comp_pmatch = prove
 (concl stack_names_comp_def,
  ACCEPT_TAC stack_names_comp_def);;

(* HOL4: prog_comp_def *)

let stack_names_prog_comp_def = cake_def
  `stack_names_prog_comp f (n:num,p:(A)stack_prog) = (n,stack_names_comp f p)`;;

(* HOL4: compile_def *)

let stack_names_compile_def = cake_def
  `stack_names_compile f (prog:(num#(A)stack_prog)list) =
     MAP (stack_names_prog_comp f) prog`;;

(* some defaults *)

(* HOL4: names_ok_def *)

let stack_names_names_ok_def = cake_def
  `stack_names_names_ok names reg_count avoid_regs <=>
     let xs = list_of_seq (tlookup names) (reg_count - LENGTH avoid_regs) in
     ALL_DISTINCT xs /\
     ALL (\x. x < reg_count /\ ~(MEM x avoid_regs)) xs`;;
