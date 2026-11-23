(* ========================================================================= *)
(* word_to_stack: port of HOL4 compiler/backend/word_to_stackScript.sml      *)
(* (CakeML v3479).                                                           *)
(* This compiler phase maps wordLang programs into stackLang programs. The  *)
(* most complicated part is the handling of spilled variables in            *)
(* conjunction with function calls. This compiler phase also introduces the *)
(* so called bitmaps that the garbage collector uses to known which         *)
(* variables it should treat as roots in a given stack frame.               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the prefix word_to_stack_ for the          *)
(*   names that clash with other theories (word_to_stack_config and its      *)
(*   fields, word_to_stack_word_list, word_to_stack_stack_free,              *)
(*   word_to_stack_comp, word_to_stack_compile_prog, word_to_stack_compile,  *)
(*   word_to_stack_stub_names).                                              *)
(* - wordLang constructors are wl_..., the clashing stackLang ones          *)
(*   stack_..., the clashing asm ones asm_... (see those files).            *)
(* - Words: n2w = word, 0w = word 0, -8w = word_neg (word 8), << = word_shl, *)
(*   || = word_or, + = word_add; GENLIST f n = list_of_seq f n; HOL4 () is   *)
(*   one; the mlstring literal of s is implode s; ZIP (l1,l2) = ZIP l1 l2.   *)
(* - The HOL4 Overload const_inst r w is written out:                        *)
(*   stack_Inst (asm_Const r w).                                             *)
(* - store_consts_stub_location is wordLang's (wl_store_consts_stub_location,*)
(*   = word_num_stubs - 1), as in HOL4 (wordLang's overload is the most      *)
(*   recent one: wordLang has stackLang as an ancestor).                     *)
(* - HOL4 lets (f-1 - (r - k)) left-associative: written ((f - 1) - (r - k)). *)
(* - Unused arguments get type variables as in HOL4 (the f and f' of        *)
(*   PushHandler, PopHandler, the dest of stack_arg_count, ...).            *)
(* - The local variable stack_arg_count of HOL4 compile_prog is             *)
(*   stack_arg_count' (the name is a constant).                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/reg_alloc/parmove.ml";;
needs "semantics/sem1aux_tfl.ml";;

prioritize_num();;
type_invention_error := true;;

(* bitmaps_length stores the current length of the bitmaps *)

let word_to_stack_config_INFO = cake_record "word_to_stack_config"
  ["bitmaps_length","num"; "stack_frame_size","num spt"];;

let word_to_stack_config_component_equality =
  word_to_stack_config_INFO.ri_component_equality;;

(* -- *)

(* Here k = number of registers
    and f = size of stack frame
    and f' = number of slots in stack frame (= f - bitmap_size)
    and kf = (k,f,f') *)

let wReg1_def = cake_def
  `wReg1 r (k,f,f':num) =
     let r = r DIV 2 in
     if r < k then ([],r) else ([(k,(f - 1) - (r - k))],k:num)`;;

let wReg2_def = cake_def
  `wReg2 r (k,f,f':num) =
     let r = r DIV 2 in
     if r < k then ([],r) else ([(k + 1,(f - 1) - (r - k))],k + 1:num)`;;

let wRegWrite1_def = cake_def
  `wRegWrite1 (g:num->(A)stack_prog) r (k,f,f':num) =
     let r = r DIV 2 in
     if r < k then g r else stack_Seq (g k) (StackStore k ((f - 1) - (r - k)))`;;

let wRegWrite2_def = cake_def
  `wRegWrite2 (g:num->(A)stack_prog) r (k,f,f':num) =
     let r = r DIV 2 in
     if r < k then g r
     else stack_Seq (g (k + 1)) (StackStore (k + 1) ((f - 1) - (r - k)))`;;

let wStackLoad_def = cake_def
  `(wStackLoad [] (x:(A)stack_prog) = x) /\
   (wStackLoad (CONS (r,i) ps) x = stack_Seq (StackLoad r i) (wStackLoad ps x))`;;

let wStackLoad_ind = cake_ind "wStackLoad";;

let wStackStore_def = cake_def
  `(wStackStore [] (x:(A)stack_prog) = x) /\
   (wStackStore (CONS (r,i) ps) x = stack_Seq (wStackStore ps x) (StackStore r i))`;;

let wMoveSingle_def = cake_def
  `wMoveSingle (x,y) (k,f,f':num) =
     match (x,y) with
       (INL r1,INL r2) -> stack_Inst (asm_Arith (Binop asm_Or r1 r2 (Reg r2)))
     | (INL r1,INR r2) -> StackLoad r1 ((f - 1) - (r2 - k))
     | (INR r1,INL r2) -> StackStore r2 ((f - 1) - (r1 - k))
     | (INR r1,INR r2) -> stack_Seq (StackLoad k ((f - 1) - (r2 - k)))
                                    (StackStore k ((f - 1) - (r1 - k))):(A)stack_prog`;;

let wMoveAux_def = cake_def
  `(wMoveAux [] (kf:num#num#num) = stack_Skip:(A)stack_prog) /\
   (wMoveAux [xy] kf = wMoveSingle xy kf) /\
   (wMoveAux (CONS xy xys) kf = stack_Seq (wMoveSingle xy kf) (wMoveAux xys kf))`;;

let wMoveAux_ind = cake_ind "wMoveAux";;

let format_var_def = cake_def
  `(format_var k NONE = INL (k + 1):num+num) /\
   (format_var k (SOME x) = if x < k then INL x else INR x)`;;

let wMove_def = cake_def
  `wMove xs (k,f:num,f':num) =
     wMoveAux (MAP (format_var k ## format_var k)
                 (parmove (MAP (DIV2 ## DIV2) xs))) (k,f,f'):(A)stack_prog`;;

let wInst_def = sem1aux_def
  `(wInst (asm_Const n c:(A)inst) (kf:num#num#num) =
      wRegWrite1 (\n. stack_Inst (asm_Const n c)) n kf) /\
   (wInst (asm_Arith (Binop bop n1 n2 (Imm imm))) kf =
      let (l,n2) = wReg1 n2 kf in
      wStackLoad l
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (Binop bop n1 n2 (Imm imm)))) n1 kf)) /\
   (wInst (asm_Arith (Binop bop n1 n2 (Reg n3))) kf =
      let (l,n2) = wReg1 n2 kf in
      let (l',n3) = wReg2 n3 kf in
      wStackLoad (APPEND l l')
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (Binop bop n1 n2 (Reg n3)))) n1 kf)) /\
   (wInst (asm_Arith (asm_Shift sh n1 n2 (Imm imm))) kf =
      let (l,n2) = wReg1 n2 kf in
      wStackLoad l
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (asm_Shift sh n1 n2 (Imm imm)))) n1 kf)) /\
   (wInst (asm_Arith (asm_Shift sh n1 n2 (Reg n3))) kf =
      let (l,n2) = wReg1 n2 kf in
      let (l',n3) = wReg2 n3 kf in
      wStackLoad (APPEND l l')
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (asm_Shift sh n1 n2 (Reg n3)))) n1 kf)) /\
   (wInst (asm_Arith (asm_Div n1 n2 n3)) kf =
      let (l,n2) = wReg1 n2 kf in
      let (l',n3) = wReg2 n3 kf in
      wStackLoad (APPEND l l')
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (asm_Div n1 n2 n3))) n1 kf)) /\
   (wInst (asm_Arith (asm_AddCarry n1 n2 n3 n4)) kf =
      let (l,n2) = wReg1 n2 kf in
      let (l',n3) = wReg2 n3 kf in
      wStackLoad (APPEND l l')
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (asm_AddCarry n1 n2 n3 n4))) n1 kf)) /\
   (wInst (asm_Arith (AddOverflow n1 n2 n3 n4)) kf =
      let (l,n2) = wReg1 n2 kf in
      let (l',n3) = wReg2 n3 kf in
      wStackLoad (APPEND l l')
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (AddOverflow n1 n2 n3 n4))) n1 kf)) /\
   (wInst (asm_Arith (SubOverflow n1 n2 n3 n4)) kf =
      let (l,n2) = wReg1 n2 kf in
      let (l',n3) = wReg2 n3 kf in
      wStackLoad (APPEND l l')
        (wRegWrite1 (\n1. stack_Inst (asm_Arith (SubOverflow n1 n2 n3 n4))) n1 kf)) /\
   (wInst (asm_Arith (LongMul n1 n2 n3 n4)) kf =
      stack_Inst (asm_Arith (LongMul 3 0 0 2))) /\
   (wInst (asm_Arith (LongDiv n1 n2 n3 n4 n5)) kf =
      let (l,n5) = wReg1 n5 kf in
      wStackLoad l (stack_Inst (asm_Arith (LongDiv 0 3 3 0 n5)))) /\
   (wInst (Mem asm_Load n1 (Addr n2 offset)) kf =
      let (l,n2) = wReg1 n2 kf in
      wStackLoad l
        (wRegWrite1 (\n1. stack_Inst (Mem asm_Load n1 (Addr n2 offset))) n1 kf)) /\
   (wInst (Mem asm_Store n1 (Addr n2 offset)) kf =
      let (l1,n2) = wReg1 n2 kf in
      let (l2,n1) = wReg2 n1 kf in
      wStackLoad (APPEND l1 l2) (stack_Inst (Mem asm_Store n1 (Addr n2 offset)))) /\
   (wInst (Mem Load8 n1 (Addr n2 offset)) kf =
      let (l,n2) = wReg1 n2 kf in
      wStackLoad l
        (wRegWrite1 (\n1. stack_Inst (Mem Load8 n1 (Addr n2 offset))) n1 kf)) /\
   (wInst (Mem Store8 n1 (Addr n2 offset)) kf =
      let (l1,n2) = wReg1 n2 kf in
      let (l2,n1) = wReg2 n1 kf in
      wStackLoad (APPEND l1 l2) (stack_Inst (Mem Store8 n1 (Addr n2 offset)))) /\
   (wInst (Mem asm_Load32 n1 (Addr n2 offset)) kf =
      let (l,n2) = wReg1 n2 kf in
      wStackLoad l
        (wRegWrite1 (\n1. stack_Inst (Mem asm_Load32 n1 (Addr n2 offset))) n1 kf)) /\
   (wInst (Mem asm_Store32 n1 (Addr n2 offset)) kf =
      let (l1,n2) = wReg1 n2 kf in
      let (l2,n1) = wReg2 n1 kf in
      wStackLoad (APPEND l1 l2) (stack_Inst (Mem asm_Store32 n1 (Addr n2 offset)))) /\
   (wInst (FP (FPLess r f1 f2)) kf =
      wRegWrite1 (\r. stack_Inst (FP (FPLess r f1 f2))) r kf) /\
   (wInst (FP (FPLessEqual r f1 f2)) kf =
      wRegWrite1 (\r. stack_Inst (FP (FPLessEqual r f1 f2))) r kf) /\
   (wInst (FP (FPEqual r f1 f2)) kf =
      wRegWrite1 (\r. stack_Inst (FP (FPEqual r f1 f2))) r kf) /\
   (wInst (FP (FPMovToReg r1 r2 d)) kf =
      if dimindex(:A) = 64 then
        wRegWrite1 (\r1. stack_Inst (FP (FPMovToReg r1 0 d))) r1 kf
      else
        wRegWrite2 (\r2. wRegWrite1 (\r1. stack_Inst (FP (FPMovToReg r1 r2 d))) r1 kf)
          r2 kf) /\
   (wInst (FP (FPMovFromReg d r1 r2)) kf =
      let (l,n1) = wReg1 r1 kf in
      let (l',n2) = if dimindex(:A) = 64 then ([],0) else wReg2 r2 kf in
      wStackLoad (APPEND l l') (stack_Inst (FP (FPMovFromReg d n1 n2)))) /\
   (wInst (FP f) kf = stack_Inst (FP f)) /\
   (wInst _ kf = stack_Inst asm_Skip)`;;

let wShareInst_def = cake_def
  `(wShareInst asm_Load v (Addr ad (offset:A word)) (kf:num#num#num) =
      let (l,n2) = wReg1 ad kf in
      wStackLoad l (wRegWrite1 (\r. ShMemOp asm_Load r (Addr n2 offset)) v kf)) /\
   (wShareInst Load8 v (Addr ad offset) kf =
      let (l,n2) = wReg1 ad kf in
      wStackLoad l (wRegWrite1 (\r. ShMemOp Load8 r (Addr n2 offset)) v kf)) /\
   (wShareInst Load16 v (Addr ad offset) kf =
      let (l,n2) = wReg1 ad kf in
      wStackLoad l (wRegWrite1 (\r. ShMemOp Load16 r (Addr n2 offset)) v kf)) /\
   (wShareInst asm_Load32 v (Addr ad offset) kf =
      let (l,n2) = wReg1 ad kf in
      wStackLoad l (wRegWrite1 (\r. ShMemOp asm_Load32 r (Addr n2 offset)) v kf)) /\
   (wShareInst asm_Store v (Addr ad offset) kf =
      let (l1,n2) = wReg1 ad kf in
      let (l2,n1) = wReg2 v kf in
      wStackLoad (APPEND l1 l2) (ShMemOp asm_Store n1 (Addr n2 offset))) /\
   (wShareInst Store8 v (Addr ad offset) kf =
      let (l1,n2) = wReg1 ad kf in
      let (l2,n1) = wReg2 v kf in
      wStackLoad (APPEND l1 l2) (ShMemOp Store8 n1 (Addr n2 offset))) /\
   (wShareInst Store16 v (Addr ad offset) kf =
      let (l1,n2) = wReg1 ad kf in
      let (l2,n1) = wReg2 v kf in
      wStackLoad (APPEND l1 l2) (ShMemOp Store16 n1 (Addr n2 offset))) /\
   (wShareInst asm_Store32 v (Addr ad offset) kf =
      let (l1,n2) = wReg1 ad kf in
      let (l2,n1) = wReg2 v kf in
      wStackLoad (APPEND l1 l2) (ShMemOp asm_Store32 n1 (Addr n2 offset)))`;;

let bits_to_word_def = cake_def
  `(bits_to_word [] = word 0:A word) /\
   (bits_to_word (CONS T xs) = word_or (word_shl (bits_to_word xs) 1) (word 1)) /\
   (bits_to_word (CONS F xs) = word_shl (bits_to_word xs) 1)`;;

(* HOL4: word_list_def, Termination WF_REL_TAC measure (LENGTH o FST) *)

let word_to_stack_word_list_def = cake_def_wf
  `MEASURE (LENGTH o (FST:bool list#num->bool list))`
  (REPEAT GEN_TAC THEN REWRITE_TAC(WF_REL_THMS @ [o_THM; FST; LENGTH_DROP]) THEN
   ARITH_TAC)
  `word_to_stack_word_list (xs:bool list) d =
     if LENGTH xs <= d \/ d = 0 then [bits_to_word xs:A word]
     else CONS (bits_to_word (APPEND (TAKE d xs) [T]))
               (word_to_stack_word_list (DROP d xs) d)`;;

let word_to_stack_word_list_ind = cake_ind "word_to_stack_word_list";;

let write_bitmap_def = cake_def
  `write_bitmap (live:B spt) k f' =
     let names = MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList live) in
     word_to_stack_word_list (APPEND (list_of_seq (\x. MEM x names) f') [T])
       (dimindex(:A) - 1):(A word)list`;;

let insert_bitmap_def = cake_def
  `insert_bitmap (ws:A list) (data,data_len) =
     let l = LENGTH ws in
     ((misc_Append data (misc_List ws),data_len + l),data_len)`;;

let wLive_def = cake_def
  `wLive (live:cutsets) (bitmaps:(A word)app_list#num) (k,f:num,f':num) =
     if f = 0 then (stack_Skip,bitmaps)
     else
       let (new_bitmaps,i) = insert_bitmap (write_bitmap (SND live) k f') bitmaps in
       (stack_Seq (stack_Inst (asm_Const k (word (i + 1)))) (StackStore k 0):(A)stack_prog,
        new_bitmaps)`;;

let SeqStackFree_def = cake_def
  `SeqStackFree n (p:(A)stack_prog) = if n = 0 then p else stack_Seq (StackFree n) p`;;

(* the NONE case with no arguments can never occur, raise_stub_location is *)
(* convenient                                                               *)

let call_dest_def = cake_def
  `(call_dest (SOME pos) (args:num list) (kf:num#num#num) =
      (stack_Skip:(A)stack_prog,INL pos:num+num)) /\
   (call_dest NONE args kf =
      if LENGTH args = 0
      then (stack_Skip,INL raise_stub_location)
      else
        let (x1,r) = wReg2 (LAST args) kf in
        (wStackLoad x1 stack_Skip,INR r))`;;

let stack_arg_count_def = cake_def
  `stack_arg_count (dest:B+C) arg_count k =
     match dest with
       INL _ -> arg_count - k:num
     | INR _ -> (arg_count - 1) - k:num`;;

let word_to_stack_stack_free_def = cake_def
  `word_to_stack_stack_free (dest:B+C) arg_count (k,f,f':num) =
     f - stack_arg_count dest arg_count k`;;

let stack_move_def = cake_def
  `(stack_move 0 start offset i (p:(A)stack_prog) = p) /\
   (stack_move (SUC n) start offset i p =
      stack_Seq (stack_move n (start + 1) offset i p)
        (stack_Seq (StackLoad i (start + offset)) (StackStore i start)))`;;

let StackArgs_def = cake_def
  `StackArgs (dest:B+C) arg_count (k,f,f':num) =
     let n = stack_arg_count dest arg_count k in
     stack_move n 0 f k (StackAlloc n):(A)stack_prog`;;

(* Unverified x64 perf-mode instrumentation.

   The idea is to simulate CakeML's call stack by pushing the return address
   and the frame pointer to the C stack, popping it when the call returns.
   This allows perf record --call-graph fp to walk CakeML stack traces.

   Due to the presence of exceptions, we need to additionally (re)store the
   base pointer and stack pointer (see PushHandler and raise_stub). *)

(* x64_config$x64_names: 14 -> 4 = RSP *)

let perf_rsp_def = cake_def
  `perf_rsp = 14`;;

(* x64_config$x64_names: 15 -> 5 = RBP (HOL's x64Script.sml) *)

let perf_rbp_def = cake_def
  `perf_rbp = 15`;;

(* k := return address; write the new frame's slots below perf_rsp first   *)
(* (perf_rsp is adjusted afterwards, so that perf's fp-walker still sees     *)
(* the old valid frame while the new one is being built; after the final    *)
(* Sub the layout is (perf_rsp) = old_rbp, 8(perf_rsp) = ret_addr); then    *)
(* commit the new frame atomically and sync perf_rbp := perf_rsp            *)

let perf_call_prefix_def = cake_def
  `perf_call_prefix l1 l2 k =
     stack_list_Seq
       [stack_LocValue k l1 l2;
        stack_Inst (Mem asm_Store k (Addr perf_rsp (word_neg (word 8))));
        stack_Inst (Mem asm_Store perf_rbp (Addr perf_rsp (word_neg (word 16))));
        stack_Inst (asm_Arith (Binop asm_Sub perf_rsp perf_rsp (Imm (word 16))));
        stack_Inst (asm_Arith (Binop asm_Or perf_rbp perf_rsp (Reg perf_rsp)))]
     :(A)stack_prog`;;

(* pop the saved %rbp, then discard both slots (saved-rbp + ret_addr) in one *)
(* atomic step                                                               *)

let perf_call_suffix_def = cake_def
  `perf_call_suffix =
     stack_list_Seq
       [stack_Inst (Mem asm_Load perf_rbp (Addr perf_rsp (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add perf_rsp perf_rsp (Imm (word 16))))]
     :(A)stack_prog`;;

let handler_slots_def = cake_def
  `handler_slots perf = if perf then 5 else 3`;;

let StackHandlerArgs_def = cake_def
  `StackHandlerArgs perf (dest:B+C) arg_count (k,f,f':num) =
     StackArgs dest arg_count (k,f + handler_slots perf,f' + handler_slots perf)
     :(A)stack_prog`;;

(* slot 3: saved %rsp, slot 4: saved %rbp *)

let PushHandler_def = cake_def
  `PushHandler perf l1 l2 (k,f:B,f':C) =
     stack_Seq (StackAlloc (handler_slots perf))
    (stack_Seq (stack_Inst (asm_Const k (word 1)))
    (stack_Seq (StackStore k 0)
    (stack_Seq (stack_LocValue k l1 l2)
    (stack_Seq (StackStore k 1)
    (stack_Seq (stack_Get k Handler)
    (stack_Seq (StackStore k 2)
    (stack_Seq (if perf then
                  stack_list_Seq
                    [stack_Inst (asm_Arith (Binop asm_Or k perf_rsp (Reg perf_rsp)));
                     StackStore k 3;
                     stack_Inst (asm_Arith (Binop asm_Or k perf_rbp (Reg perf_rbp)));
                     StackStore k 4]
                else stack_Skip)
    (stack_Seq (StackGetSize k)
               (stack_Set Handler k:(A)stack_prog)))))))))`;;

let PopHandler_def = cake_def
  `PopHandler perf (k,f:B,f':C) (prog:(A)stack_prog) =
     stack_Seq (StackLoad k 2)
    (stack_Seq (stack_Set Handler k)
    (stack_Seq (StackFree (handler_slots perf))
     prog))`;;

let chunk_to_bits_def = cake_def
  `(chunk_to_bits ([]:(bool#A word)list) = word 1:A word) /\
   (chunk_to_bits (CONS (b,w) ws) =
      let res = word_shl (chunk_to_bits ws) 1 in
      if b then word_add res (word 1) else res)`;;

let chunk_to_bitmap_def = cake_def
  `chunk_to_bitmap (ws:(bool#A word)list) = CONS (chunk_to_bits ws) (MAP SND ws)`;;

let const_words_to_bitmap_def = cake_def
  `const_words_to_bitmap (ws:(bool#A word)list) (ws_len:num) =
     if ws_len < dimindex(:A) - 1 \/ dimindex(:A) - 1 = 0
     then chunk_to_bitmap ws
     else
       let h = TAKE (dimindex(:A) - 1) ws in
       let t = DROP (dimindex(:A) - 1) ws in
       APPEND (chunk_to_bitmap h)
              (const_words_to_bitmap t (ws_len - (dimindex(:A) - 1)))`;;

let const_words_to_bitmap_ind = cake_ind "const_words_to_bitmap";;

(* Store a large constant in the second temporary *)

(*
0                f-1 0    ...   g-1
| ----------(---)|   |----------|----stack---|
            ^
      values returned on stack
*)

(* Stack slots used in multi-arg return *)

let num_stack_ret_def = cake_def
  `num_stack_ret k (vs:B list) = (LENGTH vs + 1) - k`;;

(* Number of slots to free by callee *)

let skip_free_def = cake_def
  `skip_free (k,f,f':C) (vs:B list) = f - num_stack_ret k vs`;;

(* Caller copying from the previous stack frame into its own *)

let copy_ret_aux_def = cake_def
  `copy_ret_aux k f n =
     if n = 0 then stack_Skip:(A)stack_prog
     else
       let n' = n - 1 in
       stack_list_Seq
         [StackLoad k n';
          StackStore k (n' + f);
          copy_ret_aux k f n']`;;

let copy_ret_aux_ind = cake_ind "copy_ret_aux";;

let copy_ret_def = cake_def
  `copy_ret perf is_handle (k,f,f':C) (vs:B list) (kont:(A)stack_prog) =
     let n = num_stack_ret k vs in
     if n = 0 then kont
     else stack_Seq
            (copy_ret_aux k (if is_handle then f + handler_slots perf else f) n)
            (SeqStackFree n kont)`;;

(* Return should be 2,4,6,...,2k,2k+1,...; the Set of BitmapBase, a Set of *)
(* another expression than a variable and the last clause are impossible   *)

(* HOL4 types each clause on its own (the b of OpCurrHeap is a binop, the b *)
(* of StoreConsts a num): the clauses are parsed one by one, with the type   *)
(* of the function given by a temporary type abbreviation.  Termination:     *)
(* the size of the program (HOL4 finds it by itself).                        *)

new_type_abbrev("backdefaux_comp_ty",
  `:(A)asm_config->bool->(A)wl_prog->(A word)app_list#num->num#num#num->
    (A)stack_prog#(A word)app_list#num`);;

let word_to_stack_comp_def = sem1aux_def_wf
  `MEASURE (\(conf:(A)asm_config,perf:bool,p:(A)wl_prog,bs:(A word)app_list#num,
              kf:num#num#num). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(word_to_stack_comp:backdefaux_comp_ty) conf perf wl_Skip bs kf = (stack_Skip,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Move _ xs) bs kf =
     (wMove xs kf,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Inst i) bs kf = (wInst i kf,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Return v1 vs) bs kf =
     let (xs,x) = wReg1 v1 kf in
     (wStackLoad xs (SeqStackFree (skip_free kf vs) (stack_Return x)),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Raise v) bs kf =
     (stack_Call NONE (INL raise_stub_location) NONE,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_OpCurrHeap b dst src) bs kf =
     let (xs,src_r) = wReg1 src kf in
     (wStackLoad xs (wRegWrite1 (\dst_r. stack_OpCurrHeap b dst_r src_r) dst kf),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf wl_Tick bs kf = (stack_Tick,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Break k) bs kf =
     (stack_Break k,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Continue k) bs kf =
     (stack_Continue k,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (MustTerminate p1) gs kf =
     word_to_stack_comp conf perf p1 gs kf`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Seq p1 p2) bs kf =
     let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
     let (q2,bs) = word_to_stack_comp conf perf p2 bs kf in
     (stack_Seq q1 q2,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_If cmp r ri p1 p2) bs kf =
     let (x1,r') = wReg1 r kf in
     let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
     let (q2,bs) = word_to_stack_comp conf perf p2 bs kf in
     match ri with
       Reg r ->
         let (x2,n) = wReg2 r kf in
         (wStackLoad (APPEND x1 x2) (stack_If cmp r' (Reg n) q1 q2),bs)
     | Imm i ->
         if asm_config_valid_imm conf (INR cmp) i then
           (wStackLoad x1 (stack_If cmp r' (Imm i) q1 q2),bs)
         else
           let r = FST kf + 1 in
           (stack_Seq (stack_Inst (asm_Const r i))
              (wStackLoad x1 (stack_If cmp r' (Reg r) q1 q2)),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Loop _ p1 _) bs kf =
     let (q1,bs) = word_to_stack_comp conf perf p1 bs kf in
     (stack_Loop q1,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Set name exp) bs kf =
     if name = BitmapBase then (stack_Skip,bs)
     else
       match exp with
         wl_Var n -> let (x1,r') = wReg1 n kf in (wStackLoad x1 (stack_Set name r'),bs)
       | _ -> (stack_Skip,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Get n name) bs kf =
     (wRegWrite1 (\r. stack_Get r name) n kf,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Call ret dest args handler) bs kf =
     let (q0,dest') = call_dest dest args kf in
     match ret with
       NONE ->
         (stack_Seq q0 (SeqStackFree (word_to_stack_stack_free dest' (LENGTH args) kf)
            (stack_Call NONE dest' NONE)),bs)
     | SOME (vs,live,ret_code,l1,l2) ->
         let (q1,bs) = wLive live bs kf in
         let (q2,bs) = word_to_stack_comp conf perf ret_code bs kf in
         let pre = if perf then perf_call_prefix l1 l2 (FST kf) else stack_Skip in
         let suf = if perf then perf_call_suffix else stack_Skip in
         (match handler with
            NONE ->
              let q3 = stack_Seq suf (copy_ret perf F kf vs q2) in
              (stack_Seq q0
                (stack_Seq q1
                  (stack_Seq (StackArgs dest' (LENGTH args + 1) kf)
                    (stack_Seq pre
                      (stack_Call (SOME (q3,0,l1,l2)) dest' NONE)))),bs)
          | SOME (handle_var,handle_code,h1,h2) ->
              let q3 = stack_Seq suf (copy_ret perf T kf vs (PopHandler perf kf q2)) in
              let (q4,bs) = word_to_stack_comp conf perf handle_code bs kf in
              (stack_Seq q0
                 (stack_Seq q1
                   (stack_Seq (PushHandler perf h1 h2 kf)
                     (stack_Seq (StackHandlerArgs perf dest' (LENGTH args + 1) kf)
                       (stack_Seq pre
                         (stack_Call (SOME (q3,0,l1,l2)) dest' (SOME (q4,h1,h2))))))),
               bs))`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Alloc r live) bs kf =
     let (q1,bs) = wLive live bs kf in
     (stack_Seq q1 (stack_Alloc 1),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_StoreConsts a b c d ws) bs kf =
     let (new_bs,i) = insert_bitmap (const_words_to_bitmap ws (LENGTH ws)) bs in
     (stack_Seq (stack_Inst (asm_Const 1 (word i)))
        (stack_StoreConsts (FST kf) (FST kf + 1) (SOME wl_store_consts_stub_location)),
      new_bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_LocValue r l1) bs kf =
     (wRegWrite1 (\r. stack_LocValue r l1 0) r kf,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_Install r1 r2 r3 r4 live) bs kf =
     let (l3,r3) = wReg1 r3 kf in
     let (l4,r4) = wReg2 r4 kf in
     (wStackLoad (APPEND l3 l4) (stack_Install (r1 DIV 2) (r2 DIV 2) r3 r4 0),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_CodeBufferWrite r1 r2) bs kf =
     let (l1,r1) = wReg1 r1 kf in
     let (l2,r2) = wReg2 r2 kf in
     (wStackLoad (APPEND l1 l2) (stack_CodeBufferWrite r1 r2),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_DataBufferWrite r1 r2) bs kf =
     let (l1,r1) = wReg1 r1 kf in
     let (l2,r2) = wReg2 r2 kf in
     (wStackLoad (APPEND l1 l2) (stack_DataBufferWrite r1 r2),bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (wl_FFI i r1 r2 r3 r4 live) bs kf =
     (stack_FFI i (r1 DIV 2) (r2 DIV 2) (r3 DIV 2) (r4 DIV 2) 0,bs)`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf (ShareInst op v exp) bs kf =
     (match exp_to_addr exp with
        NONE -> (stack_Skip,bs)
      | SOME addr -> (wShareInst op v addr kf,bs))`;
  `(word_to_stack_comp:backdefaux_comp_ty) conf perf _ bs kf =
     (stack_Skip,bs)`]);;

remove_type_abbrev "backdefaux_comp_ty";;

let word_to_stack_comp_ind = cake_ind "word_to_stack_comp";;

(* the perf code restores %rsp from slot 3 and %rbp from slot 4; slot 2 *)
(* holds the next handler, slot 1 the handler pc                         *)

let raise_stub_def = cake_def
  `raise_stub perf k =
     stack_Seq (stack_Get k Handler)
    (stack_Seq (StackSetSize k)
    (stack_Seq (if perf then
                  stack_list_Seq
                    [StackLoad k 3;
                     stack_Inst (asm_Arith (Binop asm_Or perf_rsp k (Reg k)));
                     StackLoad k 4;
                     stack_Inst (asm_Arith (Binop asm_Or perf_rbp k (Reg k)))]
                else stack_Skip)
    (stack_Seq (StackLoad k 2)
    (stack_Seq (stack_Set Handler k)
    (stack_Seq (StackLoad k 1)
    (stack_Seq (StackFree (handler_slots perf))
               (stack_Raise k:(A)stack_prog)))))))`;;

let store_consts_stub_def = cake_def
  `store_consts_stub k =
     stack_Seq (stack_StoreConsts k (k + 1) NONE) (stack_Return 0):(A)stack_prog`;;

(* stack args are in wordLang vars 0, 2, 4, ..., 2 k - 2, 2 k, ...; 2 k and *)
(* above are stack variables; we always allocate enough space for the       *)
(* maximum stack var                                                         *)

let word_to_stack_compile_prog_def = cake_def
  `word_to_stack_compile_prog (asm_conf:(A)asm_config) perf (prog:(A)wl_prog)
       arg_count reg_count bitmaps =
     let stack_arg_count' = arg_count - reg_count in
     let stack_var_count =
       MAX ((max_var prog DIV 2 + 1) - reg_count) stack_arg_count' in
     let f = if stack_var_count = 0 then 0 else stack_var_count + 1 in
     let (q1,bitmaps) =
       word_to_stack_comp asm_conf perf prog bitmaps (reg_count,f,stack_var_count) in
     (stack_Seq (StackAlloc (f - stack_arg_count')) q1,f,bitmaps)`;;

let compile_word_to_stack_def = cake_def
  `(compile_word_to_stack (asm_conf:(A)asm_config) perf k []
        (bitmaps:(A word)app_list#num) =
      ([]:(num#(A)stack_prog)list,[]:num list,bitmaps)) /\
   (compile_word_to_stack asm_conf perf k (CONS (i,n,p) progs) bitmaps =
      let (prog,f,bitmaps) = word_to_stack_compile_prog asm_conf perf p n k bitmaps in
      let (progs,fs,bitmaps) = compile_word_to_stack asm_conf perf k progs bitmaps in
      (CONS (i,prog) progs,CONS f fs,bitmaps))`;;

let compile_word_to_stack_ind = cake_ind "compile_word_to_stack";;

(* Since we increase the slots for the handler when perf=T, we need to      *)
(* update the bitmap to ensure that GC leaves the new entries alone.        *)

let word_to_stack_compile_def = cake_def
  `word_to_stack_compile (asm_conf:(A)asm_config) perf progs =
     let k = asm_config_reg_count asm_conf -
             (5 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let init_bitmaps =
       if perf then (misc_List [word 16:A word],1) else (misc_List [word 4],1) in
     let (progs,fs,bitmaps) =
       compile_word_to_stack asm_conf perf k progs init_bitmaps in
     let sfs = fromAList (MAP (\((i,p),n). (i,n)) (ZIP progs fs)) in
     (append (FST bitmaps),
      word_to_stack_config_REC (SND bitmaps) sfs,
      CONS 0 fs,
      CONS (raise_stub_location,raise_stub perf k)
        (CONS (wl_store_consts_stub_location,store_consts_stub k) progs))`;;

let word_to_stack_stub_names_def = cake_def
  `word_to_stack_stub_names one =
     [(raise_stub_location,implode "_Raise");
      (wl_store_consts_stub_location,implode "_StoreConsts")]`;;
