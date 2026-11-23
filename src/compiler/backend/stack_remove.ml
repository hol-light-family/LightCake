(* ========================================================================= *)
(* stack_remove: port of HOL4 compiler/backend/stack_removeScript.sml        *)
(* (CakeML v3479).                                                           *)
(* This compiler phase implements all stack operations as normal memory     *)
(* load/store operations.                                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/stackLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - The HOL4 stackLang Overloads (move, add_inst, sub_inst, const_inst,     *)
(*   load_inst, store_inst, add_bytes_in_word_inst, left_shift_inst,         *)
(*   right_shift_inst, While) are written out where used, as in             *)
(*   stackLang.ml: move d s = stack_Inst (asm_Arith (Binop asm_Or d s       *)
(*   (Reg s))), While c r ri p = stack_Loop (stack_If c r ri p              *)
(*   (stack_Break 0)), and so on.                                            *)
(* - HOL4 word_shift (:'a) is backend_common_word_shift (:A); n2w = word,    *)
(*   w2n = val, 0w - x = word_sub (word 0) x, x * y on words = word_mul.     *)
(* - HOL4 offset_ok is asm_offset_ok; () is one.                             *)
(* - The HOL4 variable gen_gc is gen_gc' (gen_gc is a constant of the        *)
(*   garbage collector theory gen_gc, which shares the session).             *)

(* -- compiler -- *)

let max_stack_alloc_def = cake_def
  `max_stack_alloc = 255`;;

let word_offset_def = cake_def
  `word_offset n = word (dimindex(:A) DIV 8 * n):A word`;;

(* HOL4: store_list_def *)

let stack_remove_store_list_def = cake_def
  `stack_remove_store_list =
     [NextFree; EndOfHeap; HeapLength; OtherHeap; TriggerGC;
      AllocSize; Handler; Globals; GlobReal; ProgStart; BitmapBase;
      GenStart; CodeBuffer; CodeBufferEnd; BitmapBuffer; BitmapBufferEnd;
      Temp (word 0); Temp (word 1); Temp (word 2); Temp (word 3);
      Temp (word 4); Temp (word 5); Temp (word 6); Temp (word 7);
      Temp (word 8); Temp (word 9); Temp (word 10); Temp (word 11);
      Temp (word 12); Temp (word 13); Temp (word 14); Temp (word 15);
      Temp (word 16); Temp (word 17); Temp (word 18); Temp (word 19);
      Temp (word 20); Temp (word 21); Temp (word 22); Temp (word 23);
      Temp (word 24); Temp (word 25); Temp (word 26); Temp (word 27);
      Temp (word 28); Temp (word 29); Temp (word 30); Temp (word 31)]`;;

let store_pos_def = cake_def
  `store_pos name =
     match INDEX_FIND 0 (\n. n = name) stack_remove_store_list with
       NONE -> 0
     | SOME (i,_) -> i + 1`;;

let store_length_def = cake_def
  `store_length =
     if EVEN (LENGTH stack_remove_store_list)
     then LENGTH stack_remove_store_list
     else LENGTH stack_remove_store_list + 1`;;

let store_offset_def = cake_def
  `store_offset name = word_sub (word 0) (word_offset (store_pos name)):A word`;;

let stack_err_lab_def = cake_def
  `stack_err_lab = 2`;;

let halt_inst_def = cake_def
  `halt_inst (w:A word) = stack_Seq (stack_Inst (asm_Const 1 w)) (stack_Halt 1)`;;

(* k is stack pointer register,                                              *)
(* k+1 is base of store array (and last stack address),                      *)
(* k+2 is CurrHeap (which is kept in a register for improved speed)          *)

let single_stack_alloc_def = cake_def
  `single_stack_alloc jump k n =
     if jump
     then
       stack_Seq
         (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))))
         (JumpLower k (k + 1) stack_err_lab)
     else
       stack_Seq
         (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))))
         (stack_If Lower k (Reg (k + 1)) (halt_inst (word 2)) stack_Skip)
       :(A)stack_prog`;;

let stack_alloc_def = cake_def_wf
  `MEASURE ((SND o SND):bool#num#num->num)`
  (REWRITE_TAC[measure_THM; o_THM; max_stack_alloc_def] THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `stack_alloc jump k n =
     if n = 0 then stack_Skip else
     if n <= max_stack_alloc then single_stack_alloc jump k n else
       stack_Seq (single_stack_alloc jump k max_stack_alloc)
                 (stack_alloc jump k (n - max_stack_alloc)):(A)stack_prog`;;

let stack_alloc_ind = cake_ind "stack_alloc";;

let single_stack_free_def = cake_def
  `single_stack_free k n =
     stack_Inst (asm_Arith (Binop asm_Add k k (Imm (word_offset n))))
       :(A)stack_prog`;;

(* HOL4: stack_free_def *)

let stack_remove_stack_free_def = cake_def_wf
  `MEASURE (SND:num#num->num)`
  (REWRITE_TAC[measure_THM; max_stack_alloc_def] THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `stack_remove_stack_free k n =
     if n = 0 then stack_Skip else
     if n <= max_stack_alloc then single_stack_free k n else
       stack_Seq (single_stack_free k max_stack_alloc)
                 (stack_remove_stack_free k (n - max_stack_alloc))
       :(A)stack_prog`;;

let stack_remove_stack_free_ind = cake_ind "stack_remove_stack_free";;

(* upshift the stack pointer *)

let upshift_def = cake_def_wf
  `MEASURE (SND:num#num->num)`
  (REWRITE_TAC[measure_THM; max_stack_alloc_def] THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `upshift r n =
     if n <= max_stack_alloc then
       stack_Inst (asm_Arith (Binop asm_Add r r (Imm (word_offset n))))
         :(A)stack_prog
     else
       stack_Seq
         (stack_Inst (asm_Arith (Binop asm_Add r r
            (Imm (word_offset max_stack_alloc)))))
         (upshift r (n - max_stack_alloc))`;;

let upshift_ind = cake_ind "upshift";;

let downshift_def = cake_def_wf
  `MEASURE (SND:num#num->num)`
  (REWRITE_TAC[measure_THM; max_stack_alloc_def] THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `downshift r n =
     if n <= max_stack_alloc then
       stack_Inst (asm_Arith (Binop asm_Sub r r (Imm (word_offset n))))
         :(A)stack_prog
     else
       stack_Seq
         (stack_Inst (asm_Arith (Binop asm_Sub r r
            (Imm (word_offset max_stack_alloc)))))
         (downshift r (n - max_stack_alloc))`;;

let downshift_ind = cake_ind "downshift";;

(* Shifts k up and down to store r into n *)

let stack_store_def = cake_def
  `stack_store k r n =
     stack_Seq (upshift k n)
       (stack_Seq (stack_Inst (Mem asm_Store r (Addr k (word 0))))
                  (downshift k n)):(A)stack_prog`;;

let stack_load_def = cake_def
  `stack_load r n =
     stack_Seq (upshift r n) (stack_Inst (Mem asm_Load r (Addr r (word 0))))
       :(A)stack_prog`;;

let copy_each_def = cake_def
  `copy_each t1 t2 =
     stack_Loop
       (stack_If NotEqual 1 (Imm (word 1))
          (stack_list_Seq
             [stack_Inst (Mem asm_Load t1 (Addr t2 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add t2 t2 (Imm bytes_in_word)));
              stack_If asm_Test 1 (Imm (word 1)) stack_Skip
                (stack_Inst (asm_Arith (Binop asm_Add t1 t1 (Reg 3))));
              stack_Inst (asm_Arith (asm_Shift Lsr 1 1 (Imm (word 1))));
              stack_Inst (Mem asm_Store t1 (Addr 2 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add 2 2 (Imm bytes_in_word)))])
          (stack_Break 0)):(A)stack_prog`;;

let copy_loop_def = cake_def
  `copy_loop t1 t2 =
     stack_list_Seq
       [stack_Inst (Mem asm_Load 1 (Addr t2 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add t2 t2 (Imm bytes_in_word)));
        stack_Loop
          (stack_If asm_Less 1 (Imm (word 0))
             (stack_list_Seq
                [copy_each t1 t2;
                 stack_Inst (Mem asm_Load 1 (Addr t2 (word 0)));
                 stack_Inst (asm_Arith (Binop asm_Add t2 t2
                                          (Imm bytes_in_word)))])
             (stack_Break 0));
        copy_each t1 t2]:(A)stack_prog`;;

(* HOL4: comp_def (HOL4 proves termination automatically, with the size of *)
(* the program)                                                              *)

let stack_remove_comp_def = cake_def_wf
  `MEASURE (\(jump:bool,off:A word#A word,k:num,p:(A)stack_prog).
              stack_prog_size (\x:A. 0) p)`
  TERM_TAC
  `stack_remove_comp jump (off:A word#A word) k (p:(A)stack_prog) =
     match p with
       stack_Get r name ->
         if name = CurrHeap
         then stack_Inst (asm_Arith (Binop asm_Or r (k + 2) (Reg (k + 2))))
         else stack_Inst (Mem asm_Load r (Addr (k + 1) (store_offset name)))
     | stack_Set name r ->
         if name = CurrHeap
         then stack_Inst (asm_Arith (Binop asm_Or (k + 2) r (Reg r)))
         else stack_Inst (Mem asm_Store r (Addr (k + 1) (store_offset name)))
     | stack_OpCurrHeap op r n ->
         stack_Inst (asm_Arith (Binop op r n (Reg (k + 2))))
     | StackFree n -> stack_remove_stack_free k n
     | StackAlloc n -> stack_alloc jump k n
     | StackStore r n ->
         let w = word_offset n in
         if asm_offset_ok 0 off w then stack_Inst (Mem asm_Store r (Addr k w))
         else stack_store k r n
     | StackLoad r n ->
         let w = word_offset n in
         if asm_offset_ok 0 off w then stack_Inst (Mem asm_Load r (Addr k w))
         else stack_Seq (stack_Inst (asm_Arith (Binop asm_Or r k (Reg k))))
                        (stack_load r n)
     | stack_DataBufferWrite r1 r2 ->
         stack_Inst (Mem asm_Store r2 (Addr r1 (word 0)))
     | StackLoadAny r i ->
         stack_Seq
           (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or r i (Reg i))))
                      (stack_Inst (asm_Arith (Binop asm_Add r r (Reg k)))))
           (stack_Inst (Mem asm_Load r (Addr r (word 0))))
     | StackStoreAny r i ->
         stack_Seq (stack_Inst (asm_Arith (Binop asm_Add k k (Reg i))))
           (stack_Seq (stack_Inst (Mem asm_Store r (Addr k (word 0))))
                      (stack_Inst (asm_Arith (Binop asm_Sub k k (Reg i)))))
     | StackGetSize r ->
         stack_Seq
           (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or r k (Reg k))))
                      (stack_Inst (asm_Arith (Binop asm_Sub r r (Reg (k + 1))))))
           (stack_Inst (asm_Arith (asm_Shift Lsr r r
              (Imm (word (backend_common_word_shift (:A)))))))
     | StackSetSize r ->
         stack_Seq
           (stack_Inst (asm_Arith (asm_Shift Lsl r r
              (Imm (word (backend_common_word_shift (:A)))))))
           (stack_Seq
              (stack_Inst (asm_Arith (Binop asm_Or k (k + 1) (Reg (k + 1)))))
              (stack_Inst (asm_Arith (Binop asm_Add k k (Reg r)))))
     | BitmapLoad r v ->
         stack_list_Seq
           [stack_Inst (Mem asm_Load r (Addr (k + 1) (store_offset BitmapBase)));
            stack_Inst (asm_Arith (Binop asm_Add r r (Reg v)));
            stack_Inst (asm_Arith (asm_Shift Lsl r r
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Inst (Mem asm_Load r (Addr r (word 0)))]
     | stack_StoreConsts t1 t2 _ ->
         stack_list_Seq
           [stack_Inst (Mem asm_Load t2 (Addr (k + 1) (store_offset BitmapBase)));
            stack_Inst (asm_Arith (Binop asm_Add t2 t2 (Reg 1)));
            stack_Inst (asm_Arith (asm_Shift Lsl t2 t2
              (Imm (word (backend_common_word_shift (:A))))));
            copy_loop t1 t2;
            stack_Inst (asm_Arith (Binop asm_Or t1 1 (Reg 1)));
            stack_Inst (asm_Arith (Binop asm_Or t2 1 (Reg 1)))]
     | stack_Seq p1 p2 ->
         stack_Seq (stack_remove_comp jump off k p1)
                   (stack_remove_comp jump off k p2)
     | stack_If c r ri p1 p2 ->
         stack_If c r ri (stack_remove_comp jump off k p1)
                         (stack_remove_comp jump off k p2)
     | stack_Loop p1 -> stack_Loop (stack_remove_comp jump off k p1)
     | stack_Call ret dest exc ->
         stack_Call
           (match ret with
              NONE -> NONE
            | SOME (p1,lr,l1,l2) -> SOME (stack_remove_comp jump off k p1,lr,l1,l2))
           dest
           (match exc with
              NONE -> NONE
            | SOME (p2,l1,l2) -> SOME (stack_remove_comp jump off k p2,l1,l2))
     | p -> p`;;

let stack_remove_comp_ind = cake_ind "stack_remove_comp";;

(* HOL4: prog_comp_def *)

let stack_remove_prog_comp_def = cake_def
  `stack_remove_prog_comp jump (off:A word#A word) k (n:num,p:(A)stack_prog) =
     (n,stack_remove_comp jump off k p)`;;

(* -- init code -- *)

let store_list_code_def = cake_def
  `(store_list_code a t [] = stack_Skip:(A)stack_prog) /\
   (store_list_code a t (CONS (INL w) xs) =
      stack_Seq
        (stack_list_Seq
           [stack_Inst (asm_Const t w);
            stack_Inst (Mem asm_Store t (Addr a (word 0)));
            stack_Inst (asm_Arith (Binop asm_Add a a (Imm bytes_in_word)))])
        (store_list_code a t xs)) /\
   (store_list_code a t (CONS (INR i) xs) =
      stack_Seq
        (stack_list_Seq
           [stack_Inst (Mem asm_Store i (Addr a (word 0)));
            stack_Inst (asm_Arith (Binop asm_Add a a (Imm bytes_in_word)))])
        (store_list_code a t xs))`;;

let store_list_code_ind = cake_ind "store_list_code";;

(* k+1 is base, k is stack pointer, discards 0 *)

let init_memory_def = cake_def
  `init_memory k (xs:(A word+num)list) =
     stack_list_Seq
       [stack_Inst (asm_Const 0 bytes_in_word);
        stack_Inst (asm_Arith (Binop asm_Sub k k (Reg 0)));
        stack_Inst (asm_Const 0 (word 0));
        stack_Inst (Mem asm_Store 0 (Addr k (word 0)));
        store_list_code (k + 1) 0 xs]`;;

let store_init_def = cake_def
  `store_init gen_gc' (k:num) =
     (K (INL (word 0:A word)) =++
        [(CurrHeap,INR (k + 2));
         (GlobReal,INR (k + 2));
         (NextFree,INR (k + 2));
         (TriggerGC,INR (if gen_gc' then k + 2 else 2));
         (EndOfHeap,INR 2);
         (HeapLength,INR 5);
         (OtherHeap,INR 2);
         (BitmapBase,INR 3);
         (BitmapBuffer,INR 4);
         (BitmapBufferEnd,INR 6);
         (CodeBuffer,INR 7);
         (CodeBufferEnd,INR 1)])`;;

(* init code assumes:                                                        *)
(*   reg 1: start of program                                                 *)
(*   reg 2: first address in heap                                            *)
(*   reg 3: first address in stack (and one past last address of heap)       *)
(*   reg 4: one past last address of stack                                   *)
(* The list below follows HOL4: compute the middle address, store it in      *)
(* reg 0; if reg 3 is not between start and end of memory, then put it in    *)
(* the middle (split heap and stack evenly); shrink the heap if it is too    *)
(* big; ensure the heap is an even number of words; split the heap into two, *)
(* store the heap length in reg 5; set up store and stack.                   *)
(* HOL4: init_code_def *)

let stack_remove_init_code_def = cake_def
  `stack_remove_init_code gen_gc' max_heap k =
     let max_heap = (if max_heap * val (bytes_in_word:A word) < dimword (:A)
                     then word_mul (word max_heap) bytes_in_word
                     else word_sub (word 0) (word 1):A word) in
     stack_list_Seq
       [stack_Inst (asm_Arith (Binop asm_Or 0 4 (Reg 4)));
        stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 0 0
          (Imm (word (1 + backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (asm_Shift Lsl 0 0
          (Imm (word (backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Reg 2)));
        stack_Inst (asm_Const 5 (word_mul (word max_stack_alloc) bytes_in_word));
        stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 5)));
        stack_Inst (asm_Arith (Binop asm_Sub 4 4 (Reg 5)));
        stack_If Lower 3 (Reg 2) (stack_Inst (asm_Arith (Binop asm_Or 3 0 (Reg 0))))
          (stack_If Lower 4 (Reg 3)
             (stack_Inst (asm_Arith (Binop asm_Or 3 0 (Reg 0)))) stack_Skip);
        stack_Inst (asm_Const 0 (word_mul (word max_stack_alloc) bytes_in_word));
        stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 0)));
        stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 0)));
        stack_Inst (asm_Arith (Binop asm_Or 0 3 (Reg 3)));
        stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
        stack_Inst (asm_Const 5 max_heap);
        stack_If Lower 5 (Reg 0)
          (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or 3 2 (Reg 2))))
                     (stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 5)))))
          stack_Skip;
        stack_Inst (asm_Arith (Binop asm_Sub 3 3 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 3 3
          (Imm (word (backend_common_word_shift (:A) + 1)))));
        stack_Inst (asm_Arith (asm_Shift Lsl 3 3
          (Imm (word (backend_common_word_shift (:A) + 1)))));
        stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 2)));
        stack_Inst (asm_Arith (Binop asm_Or 5 3 (Reg 3)));
        stack_Inst (asm_Arith (Binop asm_Sub 5 5 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 5 5 (Imm (word 1))));
        stack_Inst (asm_Arith (Binop asm_Or (k + 2) 2 (Reg 2)));
        stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 5)));
        stack_Inst (asm_Arith (Binop asm_Or k 4 (Reg 4)));
        stack_Inst (asm_Arith (Binop asm_Or (k + 1) 3 (Reg 3)));
        stack_Inst (Mem asm_Load 3 (Addr (k + 2) (word 0)));
        stack_Inst (asm_Arith (asm_Shift Lsr 3 3
          (Imm (word (backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (Binop asm_Or 0 (k + 2) (Reg (k + 2))));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 4 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 6 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 7 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 1 (Addr 0 (word 0)));
        init_memory k (MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list));
        stack_LocValue 0 1 0]`;;

let stack_remove_init_stubs_def = cake_def
  `stack_remove_init_stubs gen_gc' max_heap k start =
     [(0,stack_Seq (stack_remove_init_code gen_gc' max_heap k)
                   (stack_Call NONE (INL start) NONE));
      (1,halt_inst (word 0));
      (2,halt_inst (word 2))]:(num#(A)stack_prog)list`;;

(* HOL4: stub_names_def *)

let stack_remove_stub_names_def = cake_def
  `stack_remove_stub_names one =
     [(0,implode "_Init");
      (1,implode "_Halt0");
      (2,implode "_Halt2")]`;;

(* HOL4 proves it by EVAL_TAC; gc + dummy are the 2 *)

let check_init_stubs_length = prove
 (`LENGTH (stack_remove_init_stubs gen_gc' max_heap k start:(num#(A)stack_prog)list) + 2 =
   stack_num_stubs`,
  REWRITE_TAC[stack_remove_init_stubs_def; LENGTH; stack_num_stubs_def] THEN ARITH_TAC);;

(* -- full compiler -- *)

(* HOL4: compile_def *)

let stack_remove_compile_def = cake_def
  `stack_remove_compile jump (off:A word#A word) gen_gc' max_heap k start
                        (prog:(num#(A)stack_prog)list) =
     APPEND (stack_remove_init_stubs gen_gc' max_heap k start)
            (MAP (stack_remove_prog_comp jump off k) prog)`;;
