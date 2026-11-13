(* ========================================================================= *)
(* stackLang: port of HOL4 compiler/backend/stackLangScript.sml              *)
(* (CakeML v3479).                                                           *)
(* The stackLang intermediate language is a structured programming language *)
(* with function calls, while loops, if statements, etc. All assignments are *)
(* assembly instructions and register allocation is assumed to have been    *)
(* done. This is the language within which stack operations get optimised   *)
(* and turned into normal memory accesses.                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The constructors of prog (stack_prog) that clash with other ILs carry   *)
(*   the prefix stack_ (stack_Skip, stack_Inst, stack_Call, ...), as         *)
(*   notes/naming/names.tsv says; the others keep their HOL4 names.          *)
(* - Words: n2w = word; 5 word is the HOL Light type 5 word.                 *)
(* - The HOL4 Overloads are abbreviations only; their expansions are         *)
(*   written out where used (see the comment after the datatypes).           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/backend_common.ml";;

prioritize_num();;
type_invention_error := true;;

let store_name_INDUCT,store_name_RECURSION = cake_type
  "store_name =
     NextFree | EndOfHeap | TriggerGC | HeapLength | ProgStart | BitmapBase |
     CurrHeap | OtherHeap | AllocSize | Globals | GlobReal | Handler |
     GenStart | CodeBuffer | CodeBufferEnd | BitmapBuffer | BitmapBufferEnd |
     Temp (5 word)";;

(* stack_Call: return-handler code, link reg, labels l1,l2; target of call;  *)
(* handler: exception-handler code, labels l1,l2.                           *)
(* JumpLower: reg, reg, target name.  StoreConsts: reg, reg, stub name to   *)
(* call.  FFI: FFI index, conf_ptr, conf_len, array_ptr, array_len,         *)
(* ret_addr.  LocValue: assign v1 := Loc v2 v3.  Install: code buffer       *)
(* start, length of new code, data buffer start, length of new data,        *)
(* ret_addr.  ShMemOp: share memory operation, register, addr to            *)
(* load/store.  CodeBufferWrite: code buffer address, byte to write.        *)
(* DataBufferWrite: data buffer address, word to write.                     *)
(* New in stackLang, compared to wordLang: RawCall (tail-call into body of  *)
(* function, past stack alloc), StackAlloc (allocate n slots on the stack), *)
(* StackFree (free n slots on the stack), StackStore (offset, fast),        *)
(* StackStoreAny (reg contains offset, slow, used by GC), StackLoad         *)
(* (offset, fast), StackLoadAny (reg contains offset, slow, used by GC),    *)
(* StackGetSize (used when installing exc handler), StackSetSize (used by   *)
(* implementation of raise), BitmapLoad (load word from read-only region),  *)
(* Halt.                                                                     *)

let stack_prog_INDUCT,stack_prog_RECURSION = cake_type
  "stack_prog = stack_Skip
              | stack_Inst ((A)inst)
              | stack_Get num store_name
              | stack_Set store_name num
              | stack_OpCurrHeap binop num num
              | stack_Call ((stack_prog#num#num#num) option) (num+num)
                           ((stack_prog#num#num) option)
              | stack_Seq stack_prog stack_prog
              | stack_If cmp num ((A)reg_imm) stack_prog stack_prog
              | stack_Loop stack_prog
              | JumpLower num num num
              | stack_Alloc num
              | stack_StoreConsts num num (num option)
              | stack_Raise num
              | stack_Return num
              | stack_Break num
              | stack_Continue num
              | stack_FFI mlstring num num num num num
              | stack_Tick
              | stack_LocValue num num num
              | stack_Install num num num num num
              | ShMemOp memop num ((A)addr)
              | stack_CodeBufferWrite num num
              | stack_DataBufferWrite num num
              | RawCall num
              | StackAlloc num
              | StackFree num
              | StackStore num num
              | StackStoreAny num num
              | StackLoad num num
              | StackLoadAny num num
              | StackGetSize num
              | StackSetSize num
              | BitmapLoad num num
              | stack_Halt num";;

(* HOL4 Overloads, written out where used:                                  *)
(*   While cmp r ri c = stack_Loop (stack_If cmp r ri c (stack_Break 0))    *)
(*   move dest src = stack_Inst (asm_Arith (Binop asm_Or dest src (Reg src)))*)
(*   sub_1_inst r1 =                                                         *)
(*     stack_Inst (asm_Arith (Binop asm_Sub r1 r1 (Imm (word 1))))           *)
(*   sub_inst r1 r2 = stack_Inst (asm_Arith (Binop asm_Sub r1 r1 (Reg r2)))  *)
(*   add_inst r1 r2 = stack_Inst (asm_Arith (Binop asm_Add r1 r1 (Reg r2)))  *)
(*   and_inst r1 r2 = stack_Inst (asm_Arith (Binop asm_And r1 r1 (Reg r2)))  *)
(*   xor_inst r1 r2 = stack_Inst (asm_Arith (Binop asm_Xor r1 r1 (Reg r2)))  *)
(*   add_1_inst r1 =                                                         *)
(*     stack_Inst (asm_Arith (Binop asm_Add r1 r1 (Imm (word 1))))           *)
(*   or_inst r1 r2 = stack_Inst (asm_Arith (Binop asm_Or r1 r1 (Reg r2)))    *)
(*   add_bytes_in_word_inst r1 =                                             *)
(*     stack_Inst (asm_Arith (Binop asm_Add r1 r1 (Imm bytes_in_word)))      *)
(*   div2_inst r = stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (word 1)))) *)
(*   left_shift_inst r v =                                                   *)
(*     stack_Inst (asm_Arith (asm_Shift Lsl r r (Imm (word v))))             *)
(*   right_shift_inst r v =                                                  *)
(*     stack_Inst (asm_Arith (asm_Shift Lsr r r (Imm (word v))))             *)
(*   const_inst r w = stack_Inst (asm_Const r w)                             *)
(*   load_inst r a = stack_Inst (Mem asm_Load r (Addr a (word 0)))           *)
(*   store_inst r a = stack_Inst (Mem asm_Store r (Addr a (word 0)))         *)

let stack_list_Seq_def = cake_def
  `(stack_list_Seq [] = stack_Skip:(A)stack_prog) /\
   (stack_list_Seq [x] = x) /\
   (stack_list_Seq (CONS x (CONS y xs)) =
      stack_Seq x (stack_list_Seq (CONS y xs)))`;;

let stack_list_Seq_ind = cake_ind "stack_list_Seq";;

let gc_stub_location_def = cake_def
  `gc_stub_location = stack_num_stubs - 1`;;

let stack_store_consts_stub_location_def = cake_def
  `stack_store_consts_stub_location = gc_stub_location - 1`;;

(* HOL4: gc_stub_location_def |> CONV_RULE(RAND_CONV EVAL) *)

let gc_stub_location_eq = prove
 (`gc_stub_location = 4`,
  REWRITE_TAC[gc_stub_location_def; stack_num_stubs_def] THEN ARITH_TAC);;

(* HOL4: store_consts_stub_location_def |> CONV_RULE(RAND_CONV EVAL) *)

let stack_store_consts_stub_location_eq = prove
 (`stack_store_consts_stub_location = 3`,
  REWRITE_TAC[stack_store_consts_stub_location_def; gc_stub_location_eq] THEN
  ARITH_TAC);;
