(* ========================================================================= *)
(* stack_alloc: port of HOL4 compiler/backend/stack_allocScript.sml          *)
(* (CakeML v3479).                                                           *)
(* This compiler phase introduces the implementation of the memory          *)
(* allocator and its garbage collector. It traverses the given code and     *)
(* replaces all calls to Alloc by calls to code that it inserts into the    *)
(* compiled program. The inserted code is a stackLang implementation of the *)
(* garbage collector.                                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/data_to_word.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - The HOL4 stackLang Overloads are written out where used, as in         *)
(*   stackLang.ml: While c r ri p = stack_Loop (stack_If c r ri p           *)
(*   (stack_Break 0)), move d s = stack_Inst (asm_Arith (Binop asm_Or d s   *)
(*   (Reg s))), sub_1_inst r = stack_Inst (asm_Arith (Binop asm_Sub r r     *)
(*   (Imm (word 1)))), left_shift_inst r v = stack_Inst (asm_Arith          *)
(*   (asm_Shift Lsl r r (Imm (word v)))), load_inst r a = stack_Inst (Mem   *)
(*   asm_Load r (Addr a (word 0))), and so on.                               *)
(* - HOL4 word_shift (:'a) and its wordLang Overload shift (:'a) are         *)
(*   backend_common_word_shift (:A); conf.f is data_to_word_config_f conf;  *)
(*   the gc_kind constructors None and Simple are data_to_word_None and     *)
(*   data_to_word_Simple; mlstring literals are implode "..."; () is one.   *)
(* - The HOL4 comments on the register use are kept before the definitions. *)

let memcpy_code_def = cake_def
  `memcpy_code =
     stack_Loop
       (stack_If NotEqual 0 (Imm (word 0))
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 1 (Addr 2 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add 2 2 (Imm bytes_in_word)));
              stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Imm (word 1))));
              stack_Inst (Mem asm_Store 1 (Addr 3 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add 3 3 (Imm bytes_in_word)))])
          (stack_Break 0)):(A)stack_prog`;;

let clear_top_inst_def = cake_def
  `clear_top_inst i n =
     stack_Seq
       (stack_Inst (asm_Arith (asm_Shift Lsl i i (Imm (word (dimindex(:A) - n - 1))))))
       (stack_Inst (asm_Arith (asm_Shift Lsr i i (Imm (word (dimindex(:A) - n - 1))))))
       :(A)stack_prog`;;

(* in the code below, register 0 is first ptr_to_addr conf old w, then      *)
(* register 1 is m (ptr_to_addr conf old w); the second branch gets len+1w, *)
(* stores it in 6 for later, does the memcpy, computes the original         *)
(* header_addr, stores i << 2 into header_addr, computes update_addr conf i *)
(* w (i in 4 and w in 5) and adds to i in 4                                  *)

let word_gc_move_code_def = cake_def
  `word_gc_move_code (conf:data_to_word_config) =
     stack_If asm_Test 5 (Imm (word 1:A word)) stack_Skip
       (stack_list_Seq
          [stack_Inst (asm_Arith (Binop asm_Or 0 5 (Reg 5)));
           stack_Get 1 CurrHeap;
           stack_Inst (asm_Arith (asm_Shift Lsr 0 0 (Imm (word (shift_length conf)))));
           stack_Inst (asm_Arith (asm_Shift Lsl 0 0
             (Imm (word (backend_common_word_shift (:A))))));
           stack_Inst (asm_Arith (Binop asm_Add 0 0 (Reg 1)));
           stack_Inst (Mem asm_Load 1 (Addr 0 (word 0)));
           stack_If asm_Test 1 (Imm (word 3))
             (stack_list_Seq
                [stack_Inst (asm_Arith (asm_Shift Lsr 1 1 (Imm (word 2))));
                 stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                   (Imm (word (shift_length conf)))));
                 clear_top_inst 5 (small_shift_length conf - 1);
                 stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)))])
             (stack_list_Seq
                [stack_Inst (asm_Arith (asm_Shift Lsr 1 1
                   (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                 stack_Inst (asm_Arith (Binop asm_Add 1 1 (Imm (word 1))));
                 stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
                 stack_Inst (asm_Arith (Binop asm_Or 2 0 (Reg 0)));
                 stack_Inst (asm_Arith (Binop asm_Or 0 1 (Reg 1)));
                 memcpy_code;
                 stack_Inst (asm_Arith (Binop asm_Or 0 6 (Reg 6)));
                 stack_Inst (asm_Arith (asm_Shift Lsl 0 0
                   (Imm (word (backend_common_word_shift (:A))))));
                 stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 0)));
                 stack_Inst (asm_Arith (Binop asm_Or 0 4 (Reg 4)));
                 stack_Inst (asm_Arith (asm_Shift Lsl 0 0 (Imm (word 2))));
                 stack_Inst (Mem asm_Store 0 (Addr 2 (word 0)));
                 stack_Inst (asm_Arith (Binop asm_Or 1 4 (Reg 4)));
                 clear_top_inst 5 (small_shift_length conf - 1);
                 stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                   (Imm (word (shift_length conf)))));
                 stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)));
                 stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 6)))])])`;;

let word_gc_move_list_code_def = cake_def
  `word_gc_move_list_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 7 (Imm (word 0:A word))
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 5 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Imm (word 1))));
              word_gc_move_code conf;
              stack_Inst (Mem asm_Store 5 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))])
          (stack_Break 0))`;;

let word_gc_move_loop_code_def = cake_def
  `word_gc_move_loop_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 3 (Reg 8)
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 7 (Addr 8 (word 0)));
              stack_If asm_Test 7 (Imm (word 4))
                (stack_list_Seq
                   [stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                      (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                    stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
                    word_gc_move_list_code conf])
                (stack_list_Seq
                   [stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                      (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                    stack_Inst (asm_Arith (Binop asm_Add 7 7 (Imm (word 1))));
                    stack_Inst (asm_Arith (asm_Shift Lsl 7 7
                      (Imm (word (backend_common_word_shift (:A))))));
                    stack_Inst (asm_Arith (Binop asm_Add 8 8 (Reg 7)))])])
          (stack_Break 0)):(A)stack_prog`;;

(* 7 is w, 8 is index into stack, 5 is input to word_gc_move_code *)

let word_gc_move_bitmap_code_def = cake_def
  `word_gc_move_bitmap_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotLower 7 (Imm (word 2))
          (stack_If asm_Test 7 (Imm (word 1))
             (stack_list_Seq
                [stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word 1))));
                 stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))])
             (stack_list_Seq
                [StackLoadAny 5 8;
                 stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word 1))));
                 word_gc_move_code conf;
                 StackStoreAny 5 8;
                 stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))]))
          (stack_Break 0)):(A)stack_prog`;;

(* 9 is w, 8 is index into stack *)

let word_gc_move_bitmaps_code_def = cake_def
  `word_gc_move_bitmaps_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 0 (Reg 0)
          (stack_list_Seq
             [BitmapLoad 7 9;
              word_gc_move_bitmap_code conf;
              BitmapLoad 0 9;
              stack_Inst (asm_Arith (Binop asm_Add 9 9 (Imm (word 1))));
              stack_Inst (asm_Arith (asm_Shift Lsr 0 0
                (Imm (word (dimindex (:A) - 1)))))])
          (stack_Break 0)):(A)stack_prog`;;

(* 9 is w, 8 is index into stack *)

let word_gc_move_roots_bitmaps_code_def = cake_def
  `word_gc_move_roots_bitmaps_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 9 (Reg 9)
          (stack_list_Seq
             [stack_Inst (asm_Arith (Binop asm_Or 0 9 (Reg 9)));
              stack_Inst (asm_Arith (Binop asm_Sub 9 9 (Imm (word 1))));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
              word_gc_move_bitmaps_code conf;
              StackLoadAny 9 8])
          (stack_Break 0)):(A)stack_prog`;;

(* as word_gc_move_code; the second branch puts the header in 6, gets      *)
(* len+1w, and tests for a ref header (is_ref_header): for a ref it        *)
(* updates ib (Temp 2w) and pb (Temp 3w) and copies to pb                  *)

let word_gen_gc_move_code_def = cake_def
  `word_gen_gc_move_code (conf:data_to_word_config) =
     stack_If asm_Test 5 (Imm (word 1:A word)) stack_Skip
       (stack_list_Seq
          [stack_Inst (asm_Arith (Binop asm_Or 0 5 (Reg 5)));
           stack_Get 1 CurrHeap;
           stack_Inst (asm_Arith (asm_Shift Lsr 0 0 (Imm (word (shift_length conf)))));
           stack_Inst (asm_Arith (asm_Shift Lsl 0 0
             (Imm (word (backend_common_word_shift (:A))))));
           stack_Inst (asm_Arith (Binop asm_Add 0 0 (Reg 1)));
           stack_Inst (Mem asm_Load 1 (Addr 0 (word 0)));
           stack_If asm_Test 1 (Imm (word 3))
             (stack_list_Seq
                [stack_Inst (asm_Arith (asm_Shift Lsr 1 1 (Imm (word 2))));
                 stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                   (Imm (word (shift_length conf)))));
                 clear_top_inst 5 (small_shift_length conf - 1);
                 stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)))])
             (stack_list_Seq
                [stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
                 stack_Inst (asm_Arith (asm_Shift Lsr 1 1
                   (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                 stack_Inst (asm_Arith (Binop asm_Add 1 1 (Imm (word 1))));
                 stack_Inst (asm_Const 2 (word 12));
                 stack_Inst (asm_Arith (Binop asm_And 6 6 (Reg 2)));
                 stack_If asm_Equal 6 (Imm (word 8))
                   (stack_list_Seq
                      [stack_Set (Temp (word 0)) 3;
                       stack_Set (Temp (word 1)) 4;
                       stack_Get 3 (Temp (word 2));
                       stack_Get 4 (Temp (word 3));
                       stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
                       stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                         (Imm (word (backend_common_word_shift (:A))))));
                       stack_Inst (asm_Arith (Binop asm_Sub 4 4 (Reg 6)));
                       stack_Inst (asm_Arith (Binop asm_Sub 3 3 (Reg 1)));
                       stack_Set (Temp (word 2)) 3;
                       stack_Set (Temp (word 3)) 4;
                       stack_Inst (asm_Arith (Binop asm_Or 2 0 (Reg 0)));
                       stack_Inst (asm_Arith (Binop asm_Or 4 0 (Reg 0)));
                       stack_Inst (asm_Arith (Binop asm_Or 0 6 (Reg 6)));
                       memcpy_code;
                       stack_Get 0 (Temp (word 3));
                       stack_Inst (asm_Arith (asm_Shift Lsl 0 0 (Imm (word 2))));
                       stack_Inst (Mem asm_Store 0 (Addr 4 (word 0)));
                       stack_Get 1 (Temp (word 3));
                       clear_top_inst 5 (small_shift_length conf - 1);
                       stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                         (Imm (word (shift_length conf)))));
                       stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)));
                       stack_Get 3 (Temp (word 0));
                       stack_Get 4 (Temp (word 1))])
                   (stack_list_Seq
                      [stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
                       stack_Inst (asm_Arith (Binop asm_Or 2 0 (Reg 0)));
                       stack_Inst (asm_Arith (Binop asm_Or 0 1 (Reg 1)));
                       memcpy_code;
                       stack_Inst (asm_Arith (Binop asm_Or 0 6 (Reg 6)));
                       stack_Inst (asm_Arith (asm_Shift Lsl 0 0
                         (Imm (word (backend_common_word_shift (:A))))));
                       stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 0)));
                       stack_Inst (asm_Arith (Binop asm_Or 0 4 (Reg 4)));
                       stack_Inst (asm_Arith (asm_Shift Lsl 0 0 (Imm (word 2))));
                       stack_Inst (Mem asm_Store 0 (Addr 2 (word 0)));
                       stack_Inst (asm_Arith (Binop asm_Or 1 4 (Reg 4)));
                       clear_top_inst 5 (small_shift_length conf - 1);
                       stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                         (Imm (word (shift_length conf)))));
                       stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)));
                       stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 6)))])])])
       :(A)stack_prog`;;

(* uses 0,1,2,6 as temps *)

let word_gen_gc_partial_move_code_def = cake_def
  `word_gen_gc_partial_move_code (conf:data_to_word_config) =
     stack_If asm_Test 5 (Imm (word 1:A word)) stack_Skip
       (stack_list_Seq
          [stack_Inst (asm_Arith (Binop asm_Or 0 5 (Reg 5)));
           stack_Get 6 (Temp (word 0));
           stack_Inst (asm_Arith (asm_Shift Lsr 0 0 (Imm (word (shift_length conf)))));
           stack_Inst (asm_Arith (asm_Shift Lsl 0 0
             (Imm (word (backend_common_word_shift (:A))))));
           stack_Get 1 (Temp (word 1));
           stack_If Lower 0 (Reg 6) stack_Skip
             (stack_Seq (stack_Get 6 (Temp (word 1)))
             (stack_If NotLower 0 (Reg 1) stack_Skip
               (stack_list_Seq
                  [stack_Get 1 CurrHeap;
                   stack_Inst (asm_Arith (Binop asm_Add 0 0 (Reg 1)));
                   stack_Inst (Mem asm_Load 1 (Addr 0 (word 0)));
                   stack_If asm_Test 1 (Imm (word 3))
                     (stack_list_Seq
                        [stack_Inst (asm_Arith (asm_Shift Lsr 1 1 (Imm (word 2))));
                         stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                           (Imm (word (shift_length conf)))));
                         clear_top_inst 5 (small_shift_length conf - 1);
                         stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)))])
                     (stack_list_Seq
                        [stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
                         stack_Inst (asm_Arith (asm_Shift Lsr 1 1
                           (Imm (word (dimindex (:A) -
                                       data_to_word_config_len_size conf)))));
                         stack_Inst (asm_Arith (Binop asm_Add 1 1 (Imm (word 1))));
                         stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
                         stack_Inst (asm_Arith (Binop asm_Or 2 0 (Reg 0)));
                         stack_Inst (asm_Arith (Binop asm_Or 0 1 (Reg 1)));
                         memcpy_code;
                         stack_Inst (asm_Arith (Binop asm_Or 0 6 (Reg 6)));
                         stack_Inst (asm_Arith (asm_Shift Lsl 0 0
                           (Imm (word (backend_common_word_shift (:A))))));
                         stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 0)));
                         stack_Inst (asm_Arith (Binop asm_Or 0 4 (Reg 4)));
                         stack_Inst (asm_Arith (asm_Shift Lsl 0 0 (Imm (word 2))));
                         stack_Inst (Mem asm_Store 0 (Addr 2 (word 0)));
                         stack_Inst (asm_Arith (Binop asm_Or 1 4 (Reg 4)));
                         clear_top_inst 5 (small_shift_length conf - 1);
                         stack_Inst (asm_Arith (asm_Shift Lsl 1 1
                           (Imm (word (shift_length conf)))));
                         stack_Inst (asm_Arith (Binop asm_Or 5 5 (Reg 1)));
                         stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 6)))])])))])
       :(A)stack_prog`;;

let word_gen_gc_move_bitmap_code_def = cake_def
  `word_gen_gc_move_bitmap_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotLower 7 (Imm (word 2))
          (stack_If asm_Test 7 (Imm (word 1))
             (stack_list_Seq
                [stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word 1))));
                 stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))])
             (stack_list_Seq
                [StackLoadAny 5 8;
                 stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word 1))));
                 word_gen_gc_move_code conf;
                 StackStoreAny 5 8;
                 stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))]))
          (stack_Break 0)):(A)stack_prog`;;

let word_gen_gc_partial_move_bitmap_code_def = cake_def
  `word_gen_gc_partial_move_bitmap_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotLower 7 (Imm (word 2))
          (stack_If asm_Test 7 (Imm (word 1))
             (stack_list_Seq
                [stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word 1))));
                 stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))])
             (stack_list_Seq
                [StackLoadAny 5 8;
                 stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word 1))));
                 word_gen_gc_partial_move_code conf;
                 StackStoreAny 5 8;
                 stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))]))
          (stack_Break 0)):(A)stack_prog`;;

(* 9 is w, 8 is index into stack *)

let word_gen_gc_move_bitmaps_code_def = cake_def
  `word_gen_gc_move_bitmaps_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 0 (Reg 0)
          (stack_list_Seq
             [BitmapLoad 7 9;
              word_gen_gc_move_bitmap_code conf;
              BitmapLoad 0 9;
              stack_Inst (asm_Arith (Binop asm_Add 9 9 (Imm (word 1))));
              stack_Inst (asm_Arith (asm_Shift Lsr 0 0
                (Imm (word (dimindex (:A) - 1)))))])
          (stack_Break 0)):(A)stack_prog`;;

(* 9 is w, 8 is index into stack *)

let word_gen_gc_partial_move_bitmaps_code_def = cake_def
  `word_gen_gc_partial_move_bitmaps_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 0 (Reg 0)
          (stack_list_Seq
             [BitmapLoad 7 9;
              word_gen_gc_partial_move_bitmap_code conf;
              BitmapLoad 0 9;
              stack_Inst (asm_Arith (Binop asm_Add 9 9 (Imm (word 1))));
              stack_Inst (asm_Arith (asm_Shift Lsr 0 0
                (Imm (word (dimindex (:A) - 1)))))])
          (stack_Break 0)):(A)stack_prog`;;

(* 9 is w, 8 is index into stack *)

let word_gen_gc_move_roots_bitmaps_code_def = cake_def
  `word_gen_gc_move_roots_bitmaps_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 9 (Reg 9)
          (stack_list_Seq
             [stack_Inst (asm_Arith (Binop asm_Or 0 9 (Reg 9)));
              stack_Inst (asm_Arith (Binop asm_Sub 9 9 (Imm (word 1))));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
              word_gen_gc_move_bitmaps_code conf;
              StackLoadAny 9 8])
          (stack_Break 0)):(A)stack_prog`;;

(* 9 is w, 8 is index into stack *)

let word_gen_gc_partial_move_roots_bitmaps_code_def = cake_def
  `word_gen_gc_partial_move_roots_bitmaps_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 9 (Reg 9)
          (stack_list_Seq
             [stack_Inst (asm_Arith (Binop asm_Or 0 9 (Reg 9)));
              stack_Inst (asm_Arith (Binop asm_Sub 9 9 (Imm (word 1))));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
              word_gen_gc_partial_move_bitmaps_code conf;
              StackLoadAny 9 8])
          (stack_Break 0)):(A)stack_prog`;;

let word_gen_gc_move_list_code_def = cake_def
  `word_gen_gc_move_list_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 7 (Imm (word 0:A word))
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 5 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Imm (word 1))));
              word_gen_gc_move_code conf;
              stack_Inst (Mem asm_Store 5 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))])
          (stack_Break 0))`;;

let word_gen_gc_partial_move_list_code_def = cake_def
  `word_gen_gc_partial_move_list_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 7 (Imm (word 0:A word))
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 5 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Imm (word 1))));
              word_gen_gc_partial_move_code conf;
              stack_Inst (Mem asm_Store 5 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)))])
          (stack_Break 0))`;;

let word_gen_gc_move_data_code_def = cake_def
  `word_gen_gc_move_data_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 3 (Reg 8)
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 7 (Addr 8 (word 0)));
              stack_If asm_Test 7 (Imm (word 4))
                (stack_list_Seq
                   [stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                      (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                    stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
                    word_gen_gc_move_list_code conf])
                (stack_list_Seq
                   [stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                      (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                    stack_Inst (asm_Arith (Binop asm_Add 7 7 (Imm (word 1))));
                    stack_Inst (asm_Arith (asm_Shift Lsl 7 7
                      (Imm (word (backend_common_word_shift (:A))))));
                    stack_Inst (asm_Arith (Binop asm_Add 8 8 (Reg 7)))])])
          (stack_Break 0)):(A)stack_prog`;;

let word_gen_gc_partial_move_ref_list_code_def = cake_def
  `word_gen_gc_partial_move_ref_list_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 9 (Reg 8)
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 7 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
              word_gen_gc_partial_move_list_code conf])
          (stack_Break 0)):(A)stack_prog`;;

let word_gen_gc_partial_move_data_code_def = cake_def
  `word_gen_gc_partial_move_data_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 3 (Reg 8)
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 7 (Addr 8 (word 0)));
              stack_If asm_Test 7 (Imm (word 4))
                (stack_list_Seq
                   [stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                      (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                    stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
                    word_gen_gc_partial_move_list_code conf])
                (stack_list_Seq
                   [stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                      (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
                    stack_Inst (asm_Arith (Binop asm_Add 7 7 (Imm (word 1))));
                    stack_Inst (asm_Arith (asm_Shift Lsl 7 7
                      (Imm (word (backend_common_word_shift (:A))))));
                    stack_Inst (asm_Arith (Binop asm_Add 8 8 (Reg 7)))])])
          (stack_Break 0)):(A)stack_prog`;;

(* r2a in 8, r1a in 0 and Temp 4w *)

let word_gen_gc_move_refs_code_def = cake_def
  `word_gen_gc_move_refs_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotEqual 0 (Reg 8)
          (stack_list_Seq
             [stack_Inst (Mem asm_Load 7 (Addr 8 (word 0)));
              stack_Inst (asm_Arith (asm_Shift Lsr 7 7
                (Imm (word (dimindex (:A) - data_to_word_config_len_size conf)))));
              stack_Inst (asm_Arith (Binop asm_Add 8 8 (Imm bytes_in_word)));
              word_gen_gc_move_list_code conf;
              stack_Get 0 (Temp (word 4))])
          (stack_Break 0)):(A)stack_prog`;;

(* 7 is 0w iff pbx = pb and pax = pa, 1 is pbx (Temp 4w), 2 is pb, 8 is    *)
(* pax, 3 is pa; the first case (pax <> pa) is move_data, the second       *)
(* (pbx <> pb) is move_refs, computing pbx', pb, pb', pa', i', pbx' - pa',  *)
(* pax and pax - pa'                                                       *)

let word_gen_gc_move_loop_code_def = cake_def
  `word_gen_gc_move_loop_code (conf:data_to_word_config) =
     stack_Loop
       (stack_If NotTest 7 (Reg 7)
          (stack_If asm_Equal 1 (Reg 2)
             (stack_list_Seq
                [word_gen_gc_move_data_code conf;
                 stack_Get 5 (Temp (word 2));
                 stack_Get 7 (Temp (word 4));
                 stack_Inst (asm_Arith (Binop asm_Or 1 7 (Reg 7)));
                 stack_Inst (asm_Arith (Binop asm_Or 2 5 (Reg 5)));
                 stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 5)))])
             (stack_list_Seq
                [stack_Inst (asm_Arith (Binop asm_Or 0 1 (Reg 1)));
                 stack_Set (Temp (word 6)) 8;
                 stack_Inst (asm_Arith (Binop asm_Or 8 2 (Reg 2)));
                 stack_Set (Temp (word 5)) 8;
                 word_gen_gc_move_refs_code conf;
                 stack_Inst (asm_Arith (Binop asm_Or 7 8 (Reg 8)));
                 stack_Get 1 (Temp (word 5));
                 stack_Get 2 (Temp (word 5));
                 stack_Set (Temp (word 4)) 2;
                 stack_Get 2 (Temp (word 2));
                 stack_Inst (asm_Arith (Binop asm_Or 3 3 (Reg 3)));
                 stack_Inst (asm_Arith (Binop asm_Or 4 4 (Reg 4)));
                 stack_Inst (asm_Arith (Binop asm_Or 7 1 (Reg 1)));
                 stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 2)));
                 stack_Get 8 (Temp (word 6));
                 stack_Inst (asm_Arith (Binop asm_Or 5 8 (Reg 8)));
                 stack_Inst (asm_Arith (Binop asm_Sub 5 5 (Reg 3)));
                 stack_Inst (asm_Arith (Binop asm_Or 7 7 (Reg 5)))]))
          (stack_Break 0)):(A)stack_prog`;;

let word_gc_partial_or_full_def = cake_def
  `word_gc_partial_or_full (gen_sizes:B list)
                           (partial_code:((A)stack_prog)list) full_code =
     match gen_sizes with
       [] -> stack_list_Seq
               (APPEND [stack_Get 8 TriggerGC; stack_Get 7 EndOfHeap;
                        stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 8)))]
                       full_code)
     | _ -> stack_list_Seq
              [stack_Get 8 TriggerGC;
               stack_Get 7 EndOfHeap;
               stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 8)));
               stack_If NotLower 7 (Reg 1)
                 (stack_list_Seq partial_code)
                 (stack_list_Seq full_code)]`;;

let SetNewTrigger_def = cake_def
  `SetNewTrigger (endh:num) (ib:num) gs =
     stack_list_Seq
       [stack_Inst (asm_Const 1 (get_gen_size gs:A word));
        stack_Get 7 AllocSize;
        stack_Inst (asm_Arith (Binop asm_Or 4 endh (Reg endh)));
        stack_Inst (asm_Arith (Binop asm_Sub 4 4 (Reg ib)));
        stack_If Lower 1 (Reg 7)
          (stack_If Lower 4 (Reg 7)
             (stack_Set TriggerGC endh)
             (stack_If asm_Test 7 (Imm (if dimindex (:A) = 32 then word 3 else word 7))
                (stack_Seq (stack_Inst (asm_Arith (Binop asm_Add 7 7 (Reg ib))))
                           (stack_Set TriggerGC 7))
                (stack_Set TriggerGC endh)))
          (stack_If Lower 4 (Reg 1)
             (stack_Set TriggerGC endh)
             (stack_Seq (stack_Inst (asm_Arith (Binop asm_Add 1 1 (Reg ib))))
                        (stack_Set TriggerGC 1)))]`;;

(* The partial collector (first list of the Generational case) needs no    *)
(* memory check at the end, because it is guaranteed to get to a state     *)
(* where there is enough memory for the allocation. In contrast, the full  *)
(* collector (second list) can hit a state where there is not enough       *)
(* memory, and so it can Halt execution.                                    *)

let word_gc_code_def = cake_def
  `word_gc_code (conf:data_to_word_config) =
     match data_to_word_config_gc_kind conf with
       data_to_word_None ->
         stack_list_Seq
           [stack_Set AllocSize 1;
            stack_Get 2 CurrHeap;
            stack_Set NextFree 2;
            stack_Set TriggerGC 2;
            stack_Set EndOfHeap 2;
            stack_If asm_Test 1 (Reg 1) stack_Skip
              (stack_Seq (stack_Inst (asm_Const 1 (word 1))) (stack_Halt 1))]
     | data_to_word_Simple ->
         stack_list_Seq
           [stack_Set AllocSize 1;
            stack_Set NextFree 0;
            stack_Inst (asm_Const 1 (word 0));
            stack_Inst (asm_Arith (Binop asm_Or 2 1 (Reg 1)));
            stack_Get 3 OtherHeap;
            stack_Inst (asm_Arith (Binop asm_Or 4 1 (Reg 1)));
            stack_Get 5 Globals;
            stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
            stack_Inst (asm_Arith (Binop asm_Or 8 1 (Reg 1)));
            word_gc_move_code conf;
            stack_Set Globals 5;
            stack_Inst (asm_Arith (Binop asm_Or 7 5 (Reg 5)));
            stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word (shift_length conf)))));
            stack_Inst (asm_Arith (asm_Shift Lsl 7 7
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Get 9 OtherHeap;
            stack_Inst (asm_Arith (Binop asm_Add 7 7 (Reg 9)));
            stack_Set GlobReal 7;
            stack_Inst (asm_Const 7 (word 0));
            StackLoadAny 9 8;
            stack_Inst (asm_Arith (Binop asm_Or 8 7 (Reg 7)));
            word_gc_move_roots_bitmaps_code conf;
            stack_Get 8 OtherHeap;
            word_gc_move_loop_code conf;
            stack_Get 0 CurrHeap;
            stack_Get 1 OtherHeap;
            stack_Get 2 HeapLength;
            stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 1)));
            stack_Set CurrHeap 1;
            stack_Set OtherHeap 0;
            stack_Get 0 NextFree;
            stack_Set NextFree 8;
            stack_Set EndOfHeap 2;
            stack_Set TriggerGC 2;
            stack_Get 1 AllocSize;
            stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 8)));
            stack_If Lower 2 (Reg 1)
              (stack_Seq (stack_Inst (asm_Const 1 (word 1))) (stack_Halt 1))
              stack_Skip]
     | Generational gen_sizes ->
         word_gc_partial_or_full gen_sizes
           [stack_Set AllocSize 1;
            stack_Set NextFree 0;
            stack_Get 4 GenStart;
            stack_Get 5 EndOfHeap;
            stack_Get 2 CurrHeap;
            stack_Set (Temp (word 0)) 4;
            stack_Inst (asm_Arith (Binop asm_Sub 5 5 (Reg 2)));
            stack_Set (Temp (word 1)) 5;
            stack_Get 7 HeapLength;
            stack_Get 5 Globals;
            stack_Get 3 OtherHeap;
            stack_Inst (asm_Arith (asm_Shift Lsr 4 4
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Inst (asm_Arith (Binop asm_Or 6 3 (Reg 3)));
            word_gen_gc_partial_move_code conf;
            stack_Set Globals 5;
            stack_Inst (asm_Arith (Binop asm_Or 8 5 (Reg 5)));
            stack_Inst (asm_Arith (asm_Shift Lsr 8 8 (Imm (word (shift_length conf)))));
            stack_Inst (asm_Arith (asm_Shift Lsl 8 8
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Get 9 CurrHeap;
            stack_Inst (asm_Arith (Binop asm_Add 8 8 (Reg 9)));
            stack_Set GlobReal 8;
            stack_Inst (asm_Const 8 (word 0));
            StackLoadAny 9 8;
            word_gen_gc_partial_move_roots_bitmaps_code conf;
            stack_Get 8 CurrHeap;
            stack_Get 9 HeapLength;
            stack_Inst (asm_Arith (Binop asm_Add 9 9 (Reg 8)));
            stack_Get 8 EndOfHeap;
            word_gen_gc_partial_move_ref_list_code conf;
            stack_Get 8 OtherHeap;
            word_gen_gc_partial_move_data_code conf;
            stack_Get 2 OtherHeap;
            stack_Inst (asm_Arith (Binop asm_Or 0 3 (Reg 3)));
            stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
            stack_Inst (asm_Arith (asm_Shift Lsr 0 0
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Get 3 GenStart;
            stack_Get 1 CurrHeap;
            stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 1)));
            memcpy_code;
            stack_Get 0 NextFree;
            stack_Set NextFree 3;
            stack_Get 8 EndOfHeap;
            stack_Get 2 TriggerGC;
            SetNewTrigger 8 3 gen_sizes;
            stack_Inst (asm_Const 1 (word 0));
            stack_Set (Temp (word 0)) 1;
            stack_Set (Temp (word 1)) 1;
            stack_Get 1 AllocSize;
            stack_Inst (asm_Arith (Binop asm_Sub 8 8 (Reg 3)));
            stack_Get 7 CurrHeap;
            stack_Inst (asm_Arith (Binop asm_Sub 3 3 (Reg 7)));
            stack_Set GenStart 3]
           [stack_Set AllocSize 1;
            stack_Set NextFree 0;
            stack_Inst (asm_Const 1 (word 0:A word));
            stack_Inst (asm_Arith (Binop asm_Or 2 1 (Reg 1)));
            stack_Get 3 OtherHeap;
            stack_Get 4 HeapLength;
            stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 3)));
            stack_Set (Temp (word 0)) 4;
            stack_Set (Temp (word 1)) 4;
            stack_Set (Temp (word 2)) 4;
            stack_Set (Temp (word 4)) 4;
            stack_Set (Temp (word 5)) 4;
            stack_Set (Temp (word 6)) 4;
            stack_Get 4 HeapLength;
            stack_Inst (asm_Arith (asm_Shift Lsr 4 4
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Set (Temp (word 3)) 4;
            stack_Inst (asm_Arith (Binop asm_Or 4 1 (Reg 1)));
            stack_Get 5 Globals;
            stack_Inst (asm_Arith (Binop asm_Or 6 1 (Reg 1)));
            stack_Inst (asm_Arith (Binop asm_Or 8 1 (Reg 1)));
            word_gen_gc_move_code conf;
            stack_Set Globals 5;
            stack_Inst (asm_Arith (Binop asm_Or 7 5 (Reg 5)));
            stack_Get 9 OtherHeap;
            stack_Inst (asm_Arith (asm_Shift Lsr 7 7 (Imm (word (shift_length conf)))));
            stack_Inst (asm_Arith (asm_Shift Lsl 7 7
              (Imm (word (backend_common_word_shift (:A))))));
            stack_Inst (asm_Arith (Binop asm_Add 7 7 (Reg 9)));
            stack_Set GlobReal 7;
            stack_Inst (asm_Const 7 (word 0));
            StackLoadAny 9 8;
            stack_Inst (asm_Arith (Binop asm_Or 8 7 (Reg 7)));
            word_gen_gc_move_roots_bitmaps_code conf;
            stack_Get 2 (Temp (word 2));
            stack_Get 8 OtherHeap;
            stack_Inst (asm_Arith (Binop asm_Or 7 3 (Reg 3)));
            stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 8)));
            stack_Get 1 (Temp (word 6));
            stack_Inst (asm_Arith (Binop asm_Or 6 2 (Reg 2)));
            stack_Inst (asm_Arith (Binop asm_Sub 6 6 (Reg 1)));
            stack_Inst (asm_Arith (Binop asm_Or 7 7 (Reg 6)));
            word_gen_gc_move_loop_code conf;
            stack_Get 0 CurrHeap;
            stack_Get 1 OtherHeap;
            stack_Get 2 (Temp (word 2));
            stack_Set CurrHeap 1;
            stack_Set OtherHeap 0;
            stack_Get 0 NextFree;
            stack_Set NextFree 3;
            stack_Set EndOfHeap 2;
            stack_Inst (asm_Arith (Binop asm_Or 8 3 (Reg 3)));
            stack_Inst (asm_Arith (Binop asm_Sub 8 8 (Reg 1)));
            stack_Set GenStart 8;
            SetNewTrigger 2 3 gen_sizes;
            stack_Inst (asm_Const 1 (word 0));
            stack_Set (Temp (word 0)) 1;
            stack_Set (Temp (word 1)) 1;
            stack_Set (Temp (word 2)) 1;
            stack_Set (Temp (word 3)) 1;
            stack_Set (Temp (word 4)) 1;
            stack_Set (Temp (word 5)) 1;
            stack_Set (Temp (word 6)) 1;
            stack_Get 1 AllocSize;
            stack_Get 2 TriggerGC;
            stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 3)));
            stack_If Lower 2 (Reg 1)
              (stack_Seq (stack_Inst (asm_Const 1 (word 1))) (stack_Halt 1))
              stack_Skip]
       :(A)stack_prog`;;

(* HOL4: stubs_def *)

let stack_alloc_stubs_def = cake_def
  `stack_alloc_stubs (conf:data_to_word_config) =
     [(gc_stub_location,stack_Seq (word_gc_code conf) (stack_Return 0))]
       :(num#(A)stack_prog)list`;;

(* HOL4: stub_names_def *)

let stack_alloc_stub_names_def = cake_def
  `stack_alloc_stub_names one = [(gc_stub_location,implode "_GC")]`;;

(* compiler *)

let next_lab_def = cake_def_wf
  `measure (\(p:(A)stack_prog,aux:num). stack_prog_size (\x:A. 0) p)`
  TERM_TAC
  `next_lab (p:(A)stack_prog) aux =
     match p with
       stack_Seq p1 p2 -> next_lab p1 (next_lab p2 aux)
     | stack_If _ _ _ p1 p2 -> next_lab p1 (next_lab p2 aux)
     | stack_Loop p -> next_lab p aux
     | stack_Call NONE _ NONE -> aux
     | stack_Call NONE _ (SOME (_,_,l2)) -> MAX aux (l2 + 2)
     | stack_Call (SOME (p,_,_,l2)) _ NONE -> next_lab p (MAX aux (l2 + 2))
     | stack_Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) ->
         next_lab p (next_lab p' (MAX (MAX l2 l3 + 2) aux))
     | _ -> aux`;;

let next_lab_ind = cake_ind "next_lab";;

(* HOL4 next_lab_pmatch and comp_pmatch state the definitions with pmatch  *)
(* for case; both are written as match here and compile to the same case   *)
(* constants, so they state the definitions again                           *)

let next_lab_pmatch = prove
 (concl next_lab_def,
  ACCEPT_TAC next_lab_def);;

(* HOL4: comp_def *)

let stack_alloc_comp_def = cake_def_wf
  `measure (\(n:num,m:num,p:(A)stack_prog). stack_prog_size (\x:A. 0) p)`
  TERM_TAC
  `stack_alloc_comp n m (p:(A)stack_prog) =
     match p with
       stack_Seq p1 p2 ->
         let (q1,m) = stack_alloc_comp n m p1 in
         let (q2,m) = stack_alloc_comp n m p2 in
         (stack_Seq q1 q2,m)
     | stack_If c r ri p1 p2 ->
         let (q1,m) = stack_alloc_comp n m p1 in
         let (q2,m) = stack_alloc_comp n m p2 in
         (stack_If c r ri q1 q2,m)
     | stack_Loop p1 ->
         let (q1,m) = stack_alloc_comp n m p1 in
         (stack_Loop q1,m)
     | stack_Call NONE dest exc -> (stack_Call NONE dest NONE,m)
     | stack_Call (SOME (p1,lr,l1,l2)) dest exc ->
         let (q1,m) = stack_alloc_comp n m p1 in
         (match exc with
            NONE -> (stack_Call (SOME (q1,lr,l1,l2)) dest NONE,m)
          | SOME (p2,k1,k2) ->
              let (q2,m) = stack_alloc_comp n m p2 in
              (stack_Call (SOME (q1,lr,l1,l2)) dest (SOME (q2,k1,k2)),m))
     | stack_Alloc k ->
         (stack_Call (SOME (stack_Skip,0,n,m)) (INL gc_stub_location) NONE,m + 1)
     | stack_StoreConsts k1 k2 (SOME loc) ->
         (stack_Call (SOME (stack_Skip,0,n,m)) (INL loc) NONE,m + 1)
     | _ -> (p,m)`;;

let stack_alloc_comp_ind = cake_ind "stack_alloc_comp";;

(* HOL4: comp_pmatch *)

let stack_alloc_comp_pmatch = prove
 (concl stack_alloc_comp_def,
  ACCEPT_TAC stack_alloc_comp_def);;

(* HOL4: prog_comp_def *)

let stack_alloc_prog_comp_def = cake_def
  `stack_alloc_prog_comp (n,p:(A)stack_prog) =
     (n,FST (stack_alloc_comp n (next_lab p 2) p))`;;

(* HOL4: compile_def *)

let stack_alloc_compile_def = cake_def
  `stack_alloc_compile (c:data_to_word_config) (prog:(num#(A)stack_prog)list) =
     APPEND (stack_alloc_stubs c) (MAP stack_alloc_prog_comp prog)`;;
