(* ========================================================================= *)
(* data_to_word: port of HOL4 compiler/backend/data_to_wordScript.sml       *)
(* (CakeML v3479).                                                           *)
(* This compiler phase removes the functional-programming-style data        *)
(* abstraction of dataLang and lands in wordLang where all values are       *)
(* machine words and memory is a flat finite mapping from machine           *)
(* addresses to machine words. This phase introduces the garbage            *)
(* collector and bignum library, among other things.                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: the prefix data_to_word_ for the  *)
(*   names that clash with other theories (data_to_word_config,              *)
(*   data_to_word_list_Seq, data_to_word_Unit, data_to_word_get_names,       *)
(*   data_to_word_arg1, data_to_word_arg2, data_to_word_assign,              *)
(*   data_to_word_comp, data_to_word_compile_part, data_to_word_stubs,       *)
(*   data_to_word_stub_names, data_to_word_compile; the gc_kind constructors *)
(*   data_to_word_None and data_to_word_Simple) and for the theorem names    *)
(*   that OCaml cannot bind (data_to_word_Add_location_def, ...).            *)
(* - Words (hol4/words4.ml): n2w = word, w2n = val, -1w = word_neg (word 1), *)
(*   ~0w = word_not (word 0), << = word_shl, || = word_or, (h '' l) =        *)
(*   word_slice h l, (h -- l) = word_bits h l, (h >< l) = word_extract h l;  *)
(*   2 ** n = 2 EXP n; HOL4 () is one; the mlstring literal of s is          *)
(*   implode s; GENLIST is list_of_seq.                                      *)
(* - The HOL4 overloads are written out where used:                          *)
(*     ShiftN sh e n = wl_Shift sh e (wl_Const (word n))                     *)
(*     shift (:A) = backend_common_word_shift (:A)                           *)
(*     TRUE_CONST = wl_Const (word 18), FALSE_CONST = wl_Const (word 2).     *)
(* - HOL4 definitions with a type argument (:'a) (conf_ok, max_heap_limit,  *)
(*   byte_len, small_int, stubs) take the universe (:A) as for dimword:      *)
(*   NAME_DEF is the definition (with a variable s:A->bool), NAME_def the    *)
(*   HOL4 statement.                                                         *)
(* - A HOL4 record update r with <| f1 := v1; f2 := v2 |> is                 *)
(*   f1_fupd (K v1) (f2_fupd (K v2) r), as HOL4 parses it.                   *)
(* - Unused arguments of a definition get type variables as in HOL4         *)
(*   (assign_ConfigGC, make_ptr, force_thunk).                               *)
(* - D2WAUX_ names are local helpers of this file.                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/multiword.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "semantics/sem1aux_tfl.ml";;

prioritize_num();;
type_invention_error := true;;

(* this configuration is used in data_to_wordProof and stack_alloc;        *)
(* Generational: sizes of generations, smallest first                       *)

let gc_kind_INDUCT,gc_kind_RECURSION = cake_type
  "gc_kind = data_to_word_None | data_to_word_Simple | Generational (num list)";;

(* tag_bits, len_bits, pad_bits: in each pointer; len_size: size of length *)
(* field in block header; has_div: Div available in target; has_longdiv:    *)
(* LongDiv available in target; has_fp_ops: can compile floating-point ops; *)
(* has_fp_tern: can compile FMA; be: bigendian; call_empty_ffi: emit (T) /  *)
(* omit (F) calls to FFI ""; gc_kind: GC settings                           *)

let data_to_word_config_INFO = cake_record "data_to_word_config"
  ["tag_bits","num"; "len_bits","num"; "pad_bits","num"; "len_size","num";
   "has_div","bool"; "has_longdiv","bool"; "has_fp_ops","bool";
   "has_fp_tern","bool"; "be","bool"; "call_empty_ffi","bool";
   "gc_kind","gc_kind"];;

let data_to_word_config_component_equality =
  (record_info "data_to_word_config").ri_component_equality;;

let adjust_var_def = cake_def
  `adjust_var n = 2 * n + 2`;;

let adjust_set_def = cake_def
  `adjust_set (names:A spt) =
     fromAList (MAP (\(n,k). (adjust_var n,one)) (toAList names)):num_set`;;

let adjust_sets_def = cake_def
  `adjust_sets (names:A spt) = (LS one,adjust_set names):num_set#num_set`;;

let data_to_word_Unit_def = cake_def
  `data_to_word_Unit = wl_Const (word 2):(A)wl_exp`;;

let GiveUp_def = cake_def
  `GiveUp = wl_Seq (wl_Assign 1 (wl_Const (word_neg (word 1))))
                   (wl_Alloc 1 (adjust_sets (LN:num_set))):(A)wl_prog`;;

let BignumHalt_def = cake_def
  `BignumHalt r = wl_If asm_Test r (Imm (word 1)) wl_Skip GiveUp:(A)wl_prog`;;

let make_header_def = cake_def
  `make_header (conf:data_to_word_config) (tag:A word) len =
     let l = dimindex(:A) - data_to_word_config_len_size conf in
     word_or (word_shl (word len) l) (word_or (word_shl tag 2) (word 3))`;;

let tag_mask_def = cake_def
  `tag_mask (conf:data_to_word_config) =
     let l = dimindex(:A) - data_to_word_config_len_size conf in
     word_slice (l - 1) 2 (word_not (word 0):A word)`;;

let encode_header_def = cake_def
  `encode_header (conf:data_to_word_config) tag len =
     if tag < 2 EXP ((dimindex(:A) - data_to_word_config_len_size conf) - 2) /\
        tag < dimword(:A) DIV 16 /\
        len < 2 EXP (dimindex(:A) - 4) /\
        len < 2 EXP data_to_word_config_len_size conf
     then SOME (make_header conf (word tag) len:A word)
     else NONE`;;

let data_to_word_list_Seq_def = cake_def
  `(data_to_word_list_Seq [] = wl_Skip:(A)wl_prog) /\
   (data_to_word_list_Seq [x] = x) /\
   (data_to_word_list_Seq (CONS x (CONS y xs)) =
      wl_Seq x (data_to_word_list_Seq (CONS y xs)))`;;

let data_to_word_list_Seq_ind = cake_ind "data_to_word_list_Seq";;

let StoreEach_def = cake_def
  `(StoreEach v [] (offset:A word) = wl_Skip) /\
   (StoreEach v (CONS x xs) offset =
      wl_Seq (wl_Store (wl_Op asm_Add [wl_Var v; wl_Const offset]) x)
             (StoreEach v xs (word_add offset bytes_in_word)))`;;

let small_shift_length_def = cake_def
  `small_shift_length (conf:data_to_word_config) =
     (data_to_word_config_len_bits conf + data_to_word_config_tag_bits conf) + 1`;;

let shift_length_def = cake_def
  `shift_length (conf:data_to_word_config) =
     (((1 + data_to_word_config_pad_bits conf) + data_to_word_config_len_bits conf) +
      data_to_word_config_tag_bits conf) + 1`;;

(* HOL4 conf_ok (:'a) c: the universe (:A) is the first argument (as for     *)
(* dimword); the definition is conf_ok_DEF, the HOL4 statement conf_ok_def. *)

let conf_ok_DEF = new_definition
  `conf_ok (s:A->bool) (c:data_to_word_config) <=>
     shift_length c < dimindex(:A) /\
     backend_common_word_shift(:A) <= shift_length c /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex(:A)`;;

let conf_ok_def = prove
 (`!c. conf_ok (:A) c <=>
     shift_length c < dimindex(:A) /\
     backend_common_word_shift(:A) <= shift_length c /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex(:A)`,
  REWRITE_TAC[conf_ok_DEF]);;

(* HOL4 max_heap_limit (:'a) c: as conf_ok *)

let max_heap_limit_DEF = new_definition
  `max_heap_limit (s:A->bool) (c:data_to_word_config) =
     MIN (dimword(:A) DIV (2 EXP shift_length c))
         (dimword(:A) DIV (2 EXP (backend_common_word_shift(:A) + 1)))`;;

let max_heap_limit_def = prove
 (`!c. max_heap_limit (:A) c =
     MIN (dimword(:A) DIV (2 EXP shift_length c))
         (dimword(:A) DIV (2 EXP (backend_common_word_shift(:A) + 1)))`,
  REWRITE_TAC[max_heap_limit_DEF]);;

let all_ones_def = cake_def
  `all_ones m n =
     if m <= n then word 0 else word_slice (m - 1) n (word_not (word 0)):A word`;;

let maxout_bits_def = cake_def
  `maxout_bits n rep_len k =
     if n < 2 EXP rep_len - 1 then word_shl (word n) k
     else all_ones (k + rep_len) k:A word`;;

let ptr_bits_def = cake_def
  `ptr_bits (conf:data_to_word_config) tag len =
     word_or (maxout_bits tag (data_to_word_config_tag_bits conf)
                (1 + data_to_word_config_len_bits conf))
             (maxout_bits len (data_to_word_config_len_bits conf) 1):A word`;;

(* HOL4 ShiftN sh e n = Shift sh e (Const (n2w n)) is written out *)

let real_addr_def = cake_def
  `real_addr (conf:data_to_word_config) r =
     let k = backend_common_word_shift(:A) in
     let l = shift_length conf in
     if k = l /\ data_to_word_config_len_bits conf = 0 /\
        data_to_word_config_tag_bits conf = 0 then
       wl_Op asm_Add [Lookup CurrHeap; wl_Op asm_Sub [wl_Var r; wl_Const (word 1)]]
     else if k <= data_to_word_config_pad_bits conf + 1 then
       wl_Op asm_Add [Lookup CurrHeap;
                      wl_Shift Lsr (wl_Var r) (wl_Const (word (l - k)))]
     else
       wl_Op asm_Add [Lookup CurrHeap;
                      wl_Shift Lsl (wl_Shift Lsr (wl_Var r) (wl_Const (word l)))
                                   (wl_Const (word k))]:(A)wl_exp`;;

let real_offset_def = cake_def
  `real_offset (conf:data_to_word_config) r =
     wl_Op asm_Add [wl_Const bytes_in_word;
                    if dimindex(:A) = 32 then wl_Var r
                    else wl_Shift Lsl (wl_Var r) (wl_Const (word 1))]:(A)wl_exp`;;

let real_byte_offset_def = cake_def
  `real_byte_offset r =
     wl_Op asm_Add [wl_Const bytes_in_word;
                    wl_Shift Lsr (wl_Var r) (wl_Const (word 2))]:(A)wl_exp`;;

let word_op_type_INDUCT,word_op_type_RECURSION = cake_type
  "word_op_type = Bitwise binop | Carried binop";;

let lookup_word_op_def = cake_def
  `(lookup_word_op Andw = Bitwise asm_And) /\
   (lookup_word_op Orw = Bitwise asm_Or) /\
   (lookup_word_op backend_common_Xor = Bitwise asm_Xor) /\
   (lookup_word_op backend_common_Add = Carried asm_Add) /\
   (lookup_word_op backend_common_Sub = Carried asm_Sub)`;;
let _ = cake_add_simps [lookup_word_op_def];;

let FromList_location_def = cake_def
  `FromList_location = word_num_stubs`;;
let FromList1_location_def = cake_def
  `FromList1_location = FromList_location + 1`;;
let RefByte_location_def = cake_def
  `RefByte_location = FromList1_location + 1`;;
let RefArray_location_def = cake_def
  `RefArray_location = RefByte_location + 1`;;
let data_to_word_Replicate_location_def = cake_def
  `Replicate_location = RefArray_location + 1`;;
let AnyArith_location_def = cake_def
  `AnyArith_location = Replicate_location + 1`;;
let data_to_word_Add_location_def = cake_def
  `Add_location = AnyArith_location + 1`;;
let data_to_word_Sub_location_def = cake_def
  `Sub_location = Add_location + 1`;;
let data_to_word_Mul_location_def = cake_def
  `Mul_location = Sub_location + 1`;;
let data_to_word_Div_location_def = cake_def
  `Div_location = Mul_location + 1`;;
let data_to_word_Mod_location_def = cake_def
  `Mod_location = Div_location + 1`;;
let data_to_word_Compare1_location_def = cake_def
  `Compare1_location = Mod_location + 1`;;
let data_to_word_Compare_location_def = cake_def
  `Compare_location = Compare1_location + 1`;;
let data_to_word_Equal1_location_def = cake_def
  `Equal1_location = Compare_location + 1`;;
let data_to_word_Equal_location_def = cake_def
  `Equal_location = Equal1_location + 1`;;
let LongDiv1_location_def = cake_def
  `LongDiv1_location = Equal_location + 1`;;
let LongDiv_location_def = cake_def
  `LongDiv_location = LongDiv1_location + 1`;;
let MemCopy_location_def = cake_def
  `MemCopy_location = LongDiv_location + 1`;;
let ByteCopy_location_def = cake_def
  `ByteCopy_location = MemCopy_location + 1`;;
let ByteCopyAdd_location_def = cake_def
  `ByteCopyAdd_location = ByteCopy_location + 1`;;
let ByteCopySub_location_def = cake_def
  `ByteCopySub_location = ByteCopyAdd_location + 1`;;
let ByteCopyNew_location_def = cake_def
  `ByteCopyNew_location = ByteCopySub_location + 1`;;
let data_to_word_Install_location_def = cake_def
  `Install_location = ByteCopyNew_location + 1`;;
let InstallCode_location_def = cake_def
  `InstallCode_location = Install_location + 1`;;
let InstallData_location_def = cake_def
  `InstallData_location = InstallCode_location + 1`;;
let data_to_word_Dummy_location_def = cake_def
  `Dummy_location = InstallData_location + 1`;;
let data_to_word_Append_location_def = cake_def
  `Append_location = Dummy_location + 1`;;
let AppendMainLoop_location_def = cake_def
  `AppendMainLoop_location = Append_location + 1`;;
let AppendLenLoop_location_def = cake_def
  `AppendLenLoop_location = AppendMainLoop_location + 1`;;
let XorLoop_location_def = cake_def
  `XorLoop_location = AppendLenLoop_location + 1`;;
let data_to_word_Unused_location_def = cake_def
  `Unused_location = XorLoop_location + 1`;;
let StringCmpLoop_location_def = cake_def
  `StringCmpLoop_location = Unused_location + 1`;;
let data_to_word_Bignum_location_def = cake_def
  `Bignum_location = StringCmpLoop_location + 1`;;

(* HOL4: Theorem X_location_eq = EVAL ``X_location`` *)

let D2WAUX_location_defs =
  [word_num_stubs_def; stack_num_stubs_def;
   FromList_location_def; FromList1_location_def; RefByte_location_def;
   RefArray_location_def; data_to_word_Replicate_location_def;
   AnyArith_location_def; data_to_word_Add_location_def;
   data_to_word_Sub_location_def; data_to_word_Mul_location_def;
   data_to_word_Div_location_def; data_to_word_Mod_location_def;
   data_to_word_Compare1_location_def; data_to_word_Compare_location_def;
   data_to_word_Equal1_location_def; data_to_word_Equal_location_def;
   LongDiv1_location_def; LongDiv_location_def; MemCopy_location_def;
   ByteCopy_location_def; ByteCopyAdd_location_def; ByteCopySub_location_def;
   ByteCopyNew_location_def; data_to_word_Install_location_def;
   InstallCode_location_def; InstallData_location_def;
   data_to_word_Dummy_location_def; data_to_word_Append_location_def;
   AppendMainLoop_location_def; AppendLenLoop_location_def;
   XorLoop_location_def; data_to_word_Unused_location_def;
   StringCmpLoop_location_def; data_to_word_Bignum_location_def];;

let D2WAUX_LOCATION_TAC =
  REWRITE_TAC D2WAUX_location_defs THEN CONV_TAC NUM_REDUCE_CONV;;

let FromList_location_eq = prove
 (`FromList_location = 7`, D2WAUX_LOCATION_TAC);;
let FromList1_location_eq = prove
 (`FromList1_location = 8`, D2WAUX_LOCATION_TAC);;
let RefByte_location_eq = prove
 (`RefByte_location = 9`, D2WAUX_LOCATION_TAC);;
let RefArray_location_eq = prove
 (`RefArray_location = 10`, D2WAUX_LOCATION_TAC);;
let data_to_word_Replicate_location_eq = prove
 (`Replicate_location = 11`, D2WAUX_LOCATION_TAC);;
let AnyArith_location_eq = prove
 (`AnyArith_location = 12`, D2WAUX_LOCATION_TAC);;
let data_to_word_Add_location_eq = prove
 (`Add_location = 13`, D2WAUX_LOCATION_TAC);;
let data_to_word_Sub_location_eq = prove
 (`Sub_location = 14`, D2WAUX_LOCATION_TAC);;
let data_to_word_Mul_location_eq = prove
 (`Mul_location = 15`, D2WAUX_LOCATION_TAC);;
let data_to_word_Div_location_eq = prove
 (`Div_location = 16`, D2WAUX_LOCATION_TAC);;
let data_to_word_Mod_location_eq = prove
 (`Mod_location = 17`, D2WAUX_LOCATION_TAC);;
let data_to_word_Compare1_location_eq = prove
 (`Compare1_location = 18`, D2WAUX_LOCATION_TAC);;
let data_to_word_Compare_location_eq = prove
 (`Compare_location = 19`, D2WAUX_LOCATION_TAC);;
let data_to_word_Equal1_location_eq = prove
 (`Equal1_location = 20`, D2WAUX_LOCATION_TAC);;
let data_to_word_Equal_location_eq = prove
 (`Equal_location = 21`, D2WAUX_LOCATION_TAC);;
let LongDiv1_location_eq = prove
 (`LongDiv1_location = 22`, D2WAUX_LOCATION_TAC);;
let LongDiv_location_eq = prove
 (`LongDiv_location = 23`, D2WAUX_LOCATION_TAC);;
let MemCopy_location_eq = prove
 (`MemCopy_location = 24`, D2WAUX_LOCATION_TAC);;
let data_to_word_Bignum_location_eq = prove
 (`Bignum_location = 39`, D2WAUX_LOCATION_TAC);;
let ByteCopy_location_eq = prove
 (`ByteCopy_location = 25`, D2WAUX_LOCATION_TAC);;
let ByteCopyAdd_location_eq = prove
 (`ByteCopyAdd_location = 26`, D2WAUX_LOCATION_TAC);;
let ByteCopySub_location_eq = prove
 (`ByteCopySub_location = 27`, D2WAUX_LOCATION_TAC);;
let ByteCopyNew_location_eq = prove
 (`ByteCopyNew_location = 28`, D2WAUX_LOCATION_TAC);;
let data_to_word_Install_location_eq = prove
 (`Install_location = 29`, D2WAUX_LOCATION_TAC);;
let InstallCode_location_eq = prove
 (`InstallCode_location = 30`, D2WAUX_LOCATION_TAC);;
let InstallData_location_eq = prove
 (`InstallData_location = 31`, D2WAUX_LOCATION_TAC);;
let data_to_word_Dummy_location_eq = prove
 (`Dummy_location = 32`, D2WAUX_LOCATION_TAC);;
let data_to_word_Append_location_eq = prove
 (`Append_location = 33`, D2WAUX_LOCATION_TAC);;
let AppendMainLoop_location_eq = prove
 (`AppendMainLoop_location = 34`, D2WAUX_LOCATION_TAC);;
let AppendLenLoop_location_eq = prove
 (`AppendLenLoop_location = 35`, D2WAUX_LOCATION_TAC);;
let XorLoop_location_eq = prove
 (`XorLoop_location = 36`, D2WAUX_LOCATION_TAC);;
let data_to_word_Unused_location_eq = prove
 (`Unused_location = 37`, D2WAUX_LOCATION_TAC);;
let StringCmpLoop_location_eq = prove
 (`StringCmpLoop_location = 38`, D2WAUX_LOCATION_TAC);;

let SilentFFI_def = cake_def
  `SilentFFI (c:data_to_word_config) n names =
     if data_to_word_config_call_empty_ffi c then
       data_to_word_list_Seq
         [wl_Assign n (wl_Const (word 0));
          wl_Assign 7 (wl_Op asm_Sub [Lookup NextFree; Lookup CurrHeap]);
          wl_Assign 9 (Lookup HeapLength);
          wl_FFI (implode "") 7 n 9 n names]
     else wl_Skip:(A)wl_prog`;;

let AllocVar_def = cake_def
  `AllocVar (c:data_to_word_config) (limit:num) (names:num_set) =
     data_to_word_list_Seq
       [wl_Assign 1 (wl_Shift Lsr (wl_Var 1) (wl_Const (word 2)));
        wl_If Lower 1 (Imm (word limit))
          (wl_Assign 1 (wl_Shift Lsl (wl_Op asm_Add [wl_Var 1; wl_Const (word 1)])
                          (wl_Const (word (backend_common_word_shift(:A))))))
          (wl_Assign 1 (wl_Const (word_neg (word 1):A word)));
        wl_Assign 3 (wl_Op asm_Sub [Lookup TriggerGC; Lookup NextFree]);
        wl_If Lower 3 (Reg 1)
          (data_to_word_list_Seq
             [SilentFFI c 3 (FST (adjust_sets names),
                             insert 1 one (SND (adjust_sets names)));
              wl_Alloc 1 (adjust_sets names);
              SilentFFI c 3 (adjust_sets names)]) wl_Skip]`;;

let MakeBytes_def = cake_def
  `MakeBytes n =
     data_to_word_list_Seq
       [wl_Assign n (wl_Shift Lsr (wl_Var n) (wl_Const (word 2)));
        wl_Assign n (wl_Op asm_Or [wl_Var n; wl_Shift Lsl (wl_Var n) (wl_Const (word 8))]);
        wl_Assign n (wl_Op asm_Or [wl_Var n; wl_Shift Lsl (wl_Var n) (wl_Const (word 16))]);
        if dimindex(:A) = 32 then wl_Skip else
          wl_Assign n (wl_Op asm_Or [wl_Var n;
                                     wl_Shift Lsl (wl_Var n) (wl_Const (word 32))])]
       :(A)wl_prog`;;

let SmallLsr_def = cake_def
  `SmallLsr (e:(A)wl_exp) n =
     if n = 0 then e else wl_Shift Lsr e (wl_Const (word n))`;;

let WriteLastByte_aux_def = cake_def
  `WriteLastByte_aux (offset:A word) a b n p =
     wl_If asm_Equal n (Imm offset) wl_Skip
       (wl_Seq (wl_Inst (Mem Store8 b (Addr a offset))) p)`;;

let WriteLastBytes_def = cake_def
  `WriteLastBytes a b n =
     WriteLastByte_aux (word 0:A word) a b n (
       WriteLastByte_aux (word 1) a b n (
         WriteLastByte_aux (word 2) a b n (
           WriteLastByte_aux (word 3) a b n (
             if dimindex(:A) = 32 then wl_Skip else
             WriteLastByte_aux (word 4) a b n (
               WriteLastByte_aux (word 5) a b n (
                 WriteLastByte_aux (word 6) a b n (
                   WriteLastByte_aux (word 7) a b n wl_Skip)))))))`;;

(* HOL4 comments: compute length; adjust end of heap; 3 := return value;    *)
(* compute header; compute repeated byte; store header; write last word of *)
(* byte array; write rest of byte array (Replicate: ret_loc, addr, v, n,    *)
(* ret_val)                                                                 *)

let RefByte_code_def = cake_def
  `RefByte_code (c:data_to_word_config) =
     let limit = MIN (2 EXP data_to_word_config_len_size c) (dimword(:A) DIV 16) in
     let h = wl_Op asm_Add [wl_Shift Lsr (wl_Var 2) (wl_Const (word 2));
                            wl_Const bytes_in_word] in
     let x = SmallLsr h (dimindex(:A) - 63) in
     let y = wl_Shift Lsl h
               (wl_Const (word ((dimindex(:A) - backend_common_word_shift(:A)) -
                                data_to_word_config_len_size c))) in
     data_to_word_list_Seq
       [BignumHalt 2;
        wl_Assign 1 x;
        AllocVar c limit (fromList [one;one;one]);
        wl_Assign 5 (wl_Shift Lsr h (wl_Const (word (backend_common_word_shift(:A)))));
        wl_Assign 7 (wl_Shift Lsl (wl_Var 5) (wl_Const (word 2)));
        wl_Assign 9 (Lookup NextFree);
        wl_Assign 1 (wl_Op asm_Add [wl_Var 9;
                       wl_Shift Lsl (wl_Var 5)
                         (wl_Const (word (backend_common_word_shift(:A))))]);
        wl_Set NextFree (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]);
        wl_Assign 3 (wl_Op asm_Or
          [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 9; Lookup CurrHeap])
             (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
           wl_Const (word 1:A word)]);
        wl_Assign 5 (wl_Op asm_Or [wl_Op asm_Or [y; wl_Const (word 7)]; wl_Var 6]);
        MakeBytes 4;
        wl_Store (wl_Var 9) 5;
        wl_Assign 11 (wl_Op asm_And [wl_Shift Lsr (wl_Var 2) (wl_Const (word 2));
                                     wl_Const (word_sub bytes_in_word (word 1))]);
        wl_Assign 13 (wl_Const (word 0));
        wl_Store (wl_Var 1) 13;
        WriteLastBytes 1 4 11;
        wl_Assign 7 (wl_Op asm_Sub [wl_Var 7; wl_Const (word 4)]);
        wl_Call NONE (SOME Replicate_location) [0;9;4;7;3] NONE]:(A)wl_prog`;;

let data_to_word_Maxout_bits_code_def = cake_def
  `Maxout_bits_code rep_len k dest n =
     wl_If Lower n (Imm (word (2 EXP rep_len - 1)))
       (wl_Assign dest (wl_Op asm_Or [wl_Var dest;
                                      wl_Shift Lsl (wl_Var n) (wl_Const (word k))]))
       (wl_Assign dest (wl_Op asm_Or [wl_Var dest; wl_Const (all_ones (k + rep_len) k)]))
       :(A)wl_prog`;;

let data_to_word_Make_ptr_bits_code_def = cake_def
  `Make_ptr_bits_code (c:data_to_word_config) tag len dest =
     data_to_word_list_Seq
       [wl_Assign dest (wl_Op asm_Or
          [wl_Const (word 1);
           wl_Shift Lsl (wl_Op asm_Sub [Lookup NextFree; Lookup CurrHeap])
             (wl_Const (word (shift_length c - backend_common_word_shift(:A))))]);
        Maxout_bits_code (data_to_word_config_tag_bits c)
          (1 + data_to_word_config_len_bits c) dest tag;
        Maxout_bits_code (data_to_word_config_len_bits c) 1 dest len]:(A)wl_prog`;;

let FromList_code_def = cake_def
  `FromList_code (c:data_to_word_config) =
     let limit = MIN (2 EXP data_to_word_config_len_size c) (dimword(:A) DIV 16) in
     let h = wl_Shift Lsl (wl_Var 2)
               (wl_Const (word ((dimindex(:A) - data_to_word_config_len_size c) - 2))) in
     wl_If asm_Equal 2 (Imm (word 0))
       (data_to_word_list_Seq
          [wl_Assign 6 (wl_Op asm_Add [wl_Var 6; wl_Const (word 2:A word)]);
           wl_Return 0 [6]])
       (data_to_word_list_Seq
          [BignumHalt 2;
           wl_Assign 1 (wl_Var 2); AllocVar c limit (fromList [one;one;one]);
           wl_Assign 1 (Lookup NextFree);
           wl_Assign 5 (wl_Op asm_Or [h; wl_Const (word 3); wl_Var 6]);
           wl_Assign 7 (wl_Shift Lsr (wl_Var 2) (wl_Const (word 2)));
           wl_Assign 9 (wl_Shift Lsr (wl_Var 6) (wl_Const (word 4)));
           Make_ptr_bits_code c 9 7 3;
           wl_Call NONE (SOME FromList1_location) [0;1;4;2;3;5] NONE]):(A)wl_prog`;;

(* 0 = return address, 2 = address to write to, 4 = where to lookup what to *)
(* write, 6 = how many left to write, 8 = value to be returned, 10 = first  *)
(* thing to write                                                           *)

let FromList1_code_def = cake_def
  `FromList1_code (c:data_to_word_config) =
     data_to_word_list_Seq
       [wl_Store (wl_Var 2) 10;
        wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Const bytes_in_word]);
        wl_If asm_Equal 6 (Imm (word 0))
          (data_to_word_list_Seq [wl_Set NextFree (wl_Var 2); wl_Return 0 [8]])
          (data_to_word_list_Seq
             [wl_Assign 4 (real_addr c 4);
              wl_Assign 10 (wl_Load (wl_Op asm_Add [wl_Var 4; wl_Const bytes_in_word]));
              wl_Assign 4 (wl_Load (wl_Op asm_Add
                             [wl_Var 4; wl_Const (word_mul (word 2) bytes_in_word)]));
              wl_Assign 6 (wl_Op asm_Sub [wl_Var 6; wl_Const (word 4)]);
              wl_Call NONE (SOME FromList1_location) [0;2;4;6;8;10] NONE])]
       :(A)wl_prog`;;

let RefArray_code_def = cake_def
  `RefArray_code (c:data_to_word_config) =
     data_to_word_list_Seq
       [wl_Assign 1 (wl_Shift Lsl
          (wl_Op asm_Add [wl_Shift Lsr (wl_Var 2) (wl_Const (word 2)); wl_Const (word 1)])
          (wl_Const (word (backend_common_word_shift(:A)))));
        wl_Set TriggerGC (wl_Op asm_Sub [Lookup TriggerGC; wl_Var 1]);
        wl_Assign 1 (wl_Op asm_Sub [Lookup EndOfHeap; wl_Var 1]);
        wl_Set EndOfHeap (wl_Var 1);
        wl_Assign 3 (wl_Op asm_Or
          [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
             (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
           wl_Const (word 1:A word)]);
        wl_Assign 5 (wl_Op asm_Or
          [wl_Shift Lsl (wl_Var 2)
             (wl_Const (word ((dimindex(:A) - data_to_word_config_len_size c) - 2)));
           wl_Const (make_header c (word 2) 0)]);
        wl_Store (wl_Var 1) 5;
        wl_Call NONE (SOME Replicate_location) [0;1;4;2;3] NONE]:(A)wl_prog`;;

(* 0 = return address, 2 = address to write to, 4 = what to write at each  *)
(* location, 6 = how many left to write, 8 = value to be returned           *)

let data_to_word_Replicate_code_def = cake_def
  `Replicate_code =
     wl_If asm_Equal 6 (Imm (word 0)) (wl_Return 0 [8])
       (data_to_word_list_Seq
          [wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Const bytes_in_word]);
           wl_Store (wl_Var 2) 4;
           wl_Assign 6 (wl_Op asm_Sub [wl_Var 6; wl_Const (word 4)]);
           wl_Call NONE (SOME Replicate_location) [0;2;4;6;8] NONE]):(A)wl_prog`;;

let AddNumSize_def = cake_def
  `AddNumSize (c:data_to_word_config) src =
     wl_If asm_Equal (adjust_var src) (Imm (word 0)) wl_Skip
       (wl_If asm_Test (adjust_var src) (Imm (word 1))
          (wl_Assign 1 (wl_Op asm_Add [wl_Var 1; wl_Const (word 4)]))
          (wl_Assign 1 (wl_Op asm_Add [wl_Var 1;
             wl_Shift Lsl
               (wl_Shift Lsr (wl_Load (real_addr c (adjust_var src)))
                  (wl_Const (word (dimindex(:A) - data_to_word_config_len_size c))))
               (wl_Const (word 2))]))):(A)wl_prog`;;

(* t1: header, t2: pointer, t3: payload *)

let AnyHeader_def = cake_def
  `AnyHeader (c:data_to_word_config) r a t1 t2 t3 =
     wl_If asm_Equal r (Imm (word 0:A word))
       (data_to_word_list_Seq
          [wl_Assign 7 (wl_Const (word 0));
           wl_Set (Temp t1) (wl_Var r);
           wl_Set (Temp t2) (wl_Var r);
           wl_Set (Temp t3) (wl_Var r)])
     (wl_If NotTest r (Imm (word 1))
       (data_to_word_list_Seq
          [wl_Assign 7 (real_addr c r);
           wl_Set (Temp t2) (wl_Op asm_Add [wl_Var 7; wl_Const bytes_in_word]);
           wl_Set (Temp t1) (wl_Op asm_Add
             [wl_Shift Lsl
                (wl_Shift Lsr (wl_Load (wl_Var 7))
                   (wl_Const (word (dimindex(:A) - data_to_word_config_len_size c))))
                (wl_Const (word 1));
              wl_Op asm_And [wl_Const (word 1);
                             wl_Shift Lsr (wl_Load (wl_Var 7)) (wl_Const (word 4))]]);
           wl_Set (Temp t3) (wl_Const (word 0))])
     (wl_If NotLess r (Imm (word 0))
       (data_to_word_list_Seq
          [wl_Set (Temp t1) (wl_Const (word 2));
           wl_Set (Temp t2) (Lookup (if a then OtherHeap else NextFree));
           wl_Set (Temp t3) (wl_Shift Lsr (wl_Var r) (wl_Const (word 2)));
           wl_Assign 7 (wl_Const (word 0))])
       (data_to_word_list_Seq
          [wl_Set (Temp t1) (wl_Const (word 3));
           wl_Set (Temp t2) (Lookup (if a then OtherHeap else NextFree));
           wl_Set (Temp t3) (wl_Op asm_Sub [wl_Const (word 0);
                                            wl_Shift Asr (wl_Var r) (wl_Const (word 2))]);
           wl_Assign 7 (wl_Const (word 0))])))`;;

let ShiftVar_def = cake_def
  `ShiftVar sh v n =
     if sh = Ror then
       (let m = if n < dimindex(:A) then n else n MOD dimindex(:A) in
        if m = 0 then wl_Var v else wl_Shift sh (wl_Var v) (wl_Const (word m)))
     else if n = 0 then wl_Var v
     else if dimindex(:A) <= n then
       (if sh = Asr then wl_Shift sh (wl_Var v) (wl_Const (word (dimindex(:A) - 1)))
        else wl_Const (word 0))
     else (wl_Shift sh (wl_Var v) (wl_Const (word n)):(A)wl_exp)`;;

(* HOL4 comments: perform allocation; convert smallnums to bignum if        *)
(* necessary; zero out result array; perform bignum calculation; convert    *)
(* bignum to smallnum if possible without loss of info; return the bignum  *)

let AnyArith_code_def = cake_def
  `AnyArith_code (c:data_to_word_config) = data_to_word_list_Seq [
     wl_Assign 1 (wl_Const (word 4));
     AddNumSize c 0;
     AddNumSize c 1;
     wl_Set (Temp (word 29)) (wl_Var 1);
     AllocVar c (2 EXP data_to_word_config_len_size c) (fromList [one;one;one]);
     AnyHeader c 2 F (word 0) (word 31) (word 12);
     AnyHeader c 4 T (word 1) (word 30) (word 11);
     wl_Get 1 (Temp (word 11));
     wl_Store (Lookup OtherHeap) 1;
     wl_Get 1 (Temp (word 12));
     wl_Store (Lookup NextFree) 1;
     wl_Get 1 (Temp (word 29));
     wl_Assign 2 (Lookup NextFree);
     wl_Set (Temp (word 29)) (wl_Var 2);
     wl_Set (Temp (word 3)) (wl_Shift Lsr (wl_Var 6) (wl_Const (word 2)));
     wl_Assign 3 (wl_Const (word 0));
     wl_Call (SOME ([0],(fromList [one],LN),wl_Skip,AnyArith_location,2))
       (SOME Replicate_location) [2;3;1;0] NONE;
     wl_Set (Temp (word 29)) (wl_Op asm_Add [Lookup (Temp (word 29)); wl_Const bytes_in_word]);
     wl_Call (SOME ([1],(fromList [one],LN),wl_Skip,AnyArith_location,3))
       (SOME Bignum_location) [] NONE;
     wl_Get 1 (Temp (word 10));
     wl_If asm_Test 1 (Reg 1) (wl_Return 0 [1]) wl_Skip;
     wl_Assign 3 (wl_Load (wl_Op asm_Add [Lookup NextFree; wl_Const bytes_in_word]));
     wl_If asm_Equal 1 (Imm (word 2))
       (wl_Seq (wl_Assign 5 (wl_Shift Lsr (wl_Var 3) (wl_Const (word (dimindex(:A) - 3)))))
               (wl_If asm_Test 5 (Reg 5)
                  (wl_Seq (wl_Assign 1 (wl_Shift Lsl (wl_Var 3) (wl_Const (word 2))))
                          (wl_Return 0 [1]))
                  wl_Skip))
       (wl_If asm_Equal 1 (Imm (word 3))
         (wl_Seq (wl_Assign 5 (wl_Shift Lsr (wl_Op asm_Sub [wl_Var 3; wl_Const (word 1)])
                                 (wl_Const (word (dimindex(:A) - 3)))))
                 (wl_If asm_Test 5 (Reg 5)
                    (wl_Seq (wl_Assign 1 (wl_Op asm_Sub
                               [wl_Const (word 0);
                                wl_Shift Lsl (wl_Var 3) (wl_Const (word 2))]))
                            (wl_Return 0 [1]))
                    wl_Skip))
         (wl_Assign 5 (wl_Const (word 0))));
     wl_Assign 5 (Lookup NextFree);
     wl_Assign 6 (ShiftVar Lsr 1 1);
     wl_Assign 8 (wl_Op asm_And [wl_Var 1; wl_Const (word 1)]);
     wl_Assign 7 (wl_Op asm_Or [wl_Const (word 15);
                                ShiftVar Lsl 6 (dimindex(:A) - data_to_word_config_len_size c);
                                ShiftVar Lsl 8 4]);
     wl_Store (wl_Var 5) 7;
     wl_Assign 1 (wl_Op asm_Sub [wl_Var 5; Lookup CurrHeap]);
     wl_Assign 1 (wl_Op asm_Or [ShiftVar Lsl 1 (shift_length c - backend_common_word_shift(:A));
                                wl_Const (word 1)]);
     wl_Set NextFree (wl_Op asm_Add [wl_Var 5; wl_Const bytes_in_word;
                                     ShiftVar Lsl 6 (backend_common_word_shift(:A))]);
     wl_Return 0 [1]]:(A)wl_prog`;;

let data_to_word_Add_code_def = cake_def
  `Add_code = wl_Seq (wl_Assign 6 (wl_Const (word (4 * 0))))
                     (wl_Call NONE (SOME AnyArith_location) [0;2;4;6] NONE):(A)wl_prog`;;

let data_to_word_Sub_code_def = cake_def
  `Sub_code = wl_Seq (wl_Assign 6 (wl_Const (word (4 * 1))))
                     (wl_Call NONE (SOME AnyArith_location) [0;2;4;6] NONE):(A)wl_prog`;;

let data_to_word_Mul_code_def = cake_def
  `Mul_code = wl_Seq (wl_Assign 6 (wl_Const (word (4 * 4))))
                     (wl_Call NONE (SOME AnyArith_location) [0;2;4;6] NONE):(A)wl_prog`;;

let data_to_word_Div_code_def = cake_def
  `Div_code = wl_Seq (wl_Assign 6 (wl_Const (word (4 * 5))))
                     (wl_Call NONE (SOME AnyArith_location) [0;2;4;6] NONE):(A)wl_prog`;;

let data_to_word_Mod_code_def = cake_def
  `Mod_code = wl_Seq (wl_Assign 6 (wl_Const (word (4 * 6))))
                     (wl_Call NONE (SOME AnyArith_location) [0;2;4;6] NONE):(A)wl_prog`;;

let data_to_word_Install_code_def = cake_def
  `Install_code (c:data_to_word_config) =
     data_to_word_list_Seq
       [wl_Assign 1 (Lookup BitmapBuffer);
        wl_Assign 3 (Lookup CodeBuffer);
        wl_Set BitmapBuffer (wl_Var 2);
        wl_Set CodeBuffer (wl_Var 4);
        wl_Install 3 4 1 2 (LS one,LN);
        wl_Return 0 [3]]:(A)wl_prog`;;

let InstallCode_code_def = cake_def
  `InstallCode_code (c:data_to_word_config) =
     wl_If asm_Test 2 (Imm (word 1))
       (wl_Seq (wl_Assign 2 (Lookup BitmapBuffer))
               (wl_Call NONE (SOME InstallData_location) [0;2;4;6] NONE))
       (data_to_word_list_Seq
          [wl_Assign 3 (real_addr c 2);
           wl_Assign 2 (wl_Load (wl_Op asm_Add [wl_Var 3; wl_Const bytes_in_word]));
           wl_Assign 2 (ShiftVar Lsr 2 2);
           wl_CodeBufferWrite 6 2;
           wl_Assign 6 (wl_Op asm_Add [wl_Var 6; wl_Const (word 1)]);
           wl_Assign 2 (wl_Load (wl_Op asm_Add
                          [wl_Var 3; wl_Const (word_mul (word 2) bytes_in_word)]));
           wl_Call NONE (SOME InstallCode_location) [0;2;4;6] NONE]):(A)wl_prog`;;

let InstallData_code_def = cake_def
  `InstallData_code (c:data_to_word_config) =
     wl_If asm_Test 4 (Imm (word 1))
       (data_to_word_list_Seq [wl_Call NONE (SOME Install_location) [0;2;6] NONE])
       (data_to_word_list_Seq
          [wl_Assign 3 (real_addr c 4);
           wl_Assign 4 (wl_Load (wl_Op asm_Add [wl_Var 3; wl_Const bytes_in_word]));
           wl_Assign 4 (real_addr c 4);
           wl_Assign 4 (wl_Load (wl_Op asm_Add [wl_Var 4; wl_Const bytes_in_word]));
           wl_DataBufferWrite 2 4;
           wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Const bytes_in_word]);
           wl_Assign 4 (wl_Load (wl_Op asm_Add
                          [wl_Var 3; wl_Const (word_mul (word 2) bytes_in_word)]));
           wl_Call NONE (SOME InstallData_location) [0;2;4;6] NONE]):(A)wl_prog`;;

(* l is 2, a1 is 4, a2 is 6 *)

let data_to_word_Compare1_code_def = cake_def
  `Compare1_code =
     wl_If asm_Equal 2 (Imm (word 0))
       (wl_Seq (wl_Assign 2 (wl_Const (word 1))) (wl_Return 0 [2]))
       (data_to_word_list_Seq
          [wl_Assign 8 (wl_Load (wl_Var 4));
           wl_Assign 9 (wl_Load (wl_Var 6));
           wl_If asm_Equal 8 (Reg 9)
             (data_to_word_list_Seq
                [wl_Assign 2 (wl_Op asm_Sub [wl_Var 2; wl_Const (word 1)]);
                 wl_Assign 4 (wl_Op asm_Sub [wl_Var 4; wl_Const bytes_in_word]);
                 wl_Assign 6 (wl_Op asm_Sub [wl_Var 6; wl_Const bytes_in_word]);
                 wl_Call NONE (SOME Compare1_location) [0;2;4;6] NONE])
             (wl_If Lower 8 (Reg 9)
                (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]))
                (wl_Seq (wl_Assign 2 (wl_Const (word 2))) (wl_Return 0 [2])))])
       :(A)wl_prog`;;

(* this code can assume that the arguments (2 and 4) are not both small     *)
(* numbers; 1st arg is small number, means that 2nd must be bignum (loads   *)
(* header of 2nd arg); 2nd arg is small number: 1st must be bignum (loads  *)
(* header of 1st arg); headers are the same / not the same                  *)

let data_to_word_Compare_code_def = cake_def
  `Compare_code (c:data_to_word_config) =
     wl_If asm_Test 2 (Imm (word 1))
       (data_to_word_list_Seq
          [wl_Assign 1 (wl_Load (real_addr c 4));
           wl_If asm_Test 1 (Imm (word 16))
             (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]))
             (wl_Seq (wl_Assign 2 (wl_Const (word 2))) (wl_Return 0 [2]))])
     (wl_If asm_Test 4 (Imm (word 1))
       (data_to_word_list_Seq
          [wl_Assign 1 (wl_Load (real_addr c 2));
           wl_If asm_Test 1 (Imm (word 16:A word))
             (wl_Seq (wl_Assign 2 (wl_Const (word 2))) (wl_Return 0 [2]))
             (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]))])
       (data_to_word_list_Seq
          [wl_Assign 11 (real_addr c 2);
           wl_Assign 1 (wl_Load (wl_Var 11));
           wl_Assign 13 (real_addr c 4);
           wl_Assign 3 (wl_Load (wl_Var 13));
           wl_Assign 6 (wl_Shift Lsr (wl_Var 1)
                          (wl_Const (word (dimindex(:A) - data_to_word_config_len_size c))));
           wl_Assign 8 (wl_Shift Lsr (wl_Var 3)
                          (wl_Const (word (dimindex(:A) - data_to_word_config_len_size c))));
           wl_If asm_Equal 1 (Reg 3)
             (data_to_word_list_Seq
                [wl_Assign 2 (wl_Op asm_Add [wl_Var 11;
                   wl_Shift Lsl (wl_Var 6) (wl_Const (word (backend_common_word_shift(:A))))]);
                 wl_Assign 4 (wl_Op asm_Add [wl_Var 13;
                   wl_Shift Lsl (wl_Var 6) (wl_Const (word (backend_common_word_shift(:A))))]);
                 wl_If asm_Test 1 (Imm (word 16))
                   (wl_Call NONE (SOME Compare1_location) [0;6;2;4] NONE)
                   (wl_Call NONE (SOME Compare1_location) [0;6;4;2] NONE)])
             (wl_If asm_Test 1 (Imm (word 16))
                (wl_If asm_Test 3 (Imm (word 16))
                   (wl_If Lower 6 (Reg 8)
                      (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]))
                      (wl_Seq (wl_Assign 2 (wl_Const (word 2))) (wl_Return 0 [2])))
                   (wl_Seq (wl_Assign 2 (wl_Const (word 2))) (wl_Return 0 [2])))
                (wl_If asm_Test 3 (Imm (word 16))
                   (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]))
                   (wl_If Lower 6 (Reg 8)
                      (wl_Seq (wl_Assign 2 (wl_Const (word 2))) (wl_Return 0 [2]))
                      (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2])))))]))`;;

let data_to_word_Equal1_code_def = cake_def
  `Equal1_code =
     data_to_word_list_Seq [
       wl_If asm_Equal 2 (Imm (word 0))
         (wl_Seq (wl_Assign 2 (wl_Const (word 1))) (wl_Return 0 [2])) wl_Skip;
       wl_Assign 1 (wl_Load (wl_Var 4));
       wl_Assign 3 (wl_Load (wl_Var 6));
       wl_Call (SOME ([5],(list_insert [0;2;4;6] LN,LN),wl_Skip,Equal1_location,2))
         (SOME Equal_location) [1;3] NONE;
       wl_If asm_Equal 5 (Imm (word 1)) wl_Skip (wl_Return 0 [5]);
       wl_Assign 2 (wl_Op asm_Sub [wl_Var 2; wl_Const (word 1)]);
       wl_Assign 4 (wl_Op asm_Add [wl_Var 4; wl_Const bytes_in_word]);
       wl_Assign 6 (wl_Op asm_Add [wl_Var 6; wl_Const bytes_in_word]);
       wl_Call NONE (SOME Equal1_location) [0;2;4;6] NONE]:(A)wl_prog`;;

let data_to_word_Equal_code_def = cake_def
  `Equal_code (c:data_to_word_config) =
     data_to_word_list_Seq [
       wl_If asm_Equal 2 (Reg 4)
         (wl_Seq (wl_Assign 2 (wl_Const (word 1:A word))) (wl_Return 0 [2])) wl_Skip;
       wl_Assign 1 (wl_Op asm_And [wl_Var 2; wl_Var 4]);
       wl_If asm_Test 1 (Imm (word 1))
         (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2])) wl_Skip;
       wl_Assign 20 (real_addr c 2);
       wl_Assign 40 (real_addr c 4);
       wl_Assign 21 (wl_Load (wl_Var 20));
       wl_Assign 41 (wl_Load (wl_Var 40));
       wl_If asm_Test 21 (Imm (word 12)) (data_to_word_list_Seq
           [wl_Assign 1 (wl_Op asm_And [wl_Var 21; wl_Const (word_or (tag_mask c) (word 2))]);
            wl_If asm_Equal 1 (Imm (word (16 * closure_tag + 2)))
              (wl_Seq (wl_Assign 2 (wl_Const (word 1))) (wl_Return 0 [2])) wl_Skip;
            wl_If asm_Equal 1 (Imm (word (16 * partial_app_tag + 2)))
              (wl_Seq (wl_Assign 2 (wl_Const (word 1))) (wl_Return 0 [2])) wl_Skip;
            wl_If asm_Equal 21 (Reg 41)
              wl_Skip (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]));
            wl_Assign 6 (ShiftVar Lsr 21 (dimindex(:A) - data_to_word_config_len_size c));
            wl_Assign 20 (wl_Op asm_Add [wl_Var 20; wl_Const bytes_in_word]);
            wl_Assign 40 (wl_Op asm_Add [wl_Var 40; wl_Const bytes_in_word]);
            wl_Call NONE (SOME Equal1_location) [0;6;20;40] NONE])
         wl_Skip;
       wl_If asm_Equal 21 (Reg 41) wl_Skip
         (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2]));
       wl_If asm_Test 21 (Imm (word 4))
         (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2])) wl_Skip;
       wl_Assign 1 (wl_Op asm_And [wl_Var 21; wl_Const (word 24)]);
       wl_If asm_Equal 1 (Imm (word 16))
         (wl_Seq (wl_Assign 2 (wl_Const (word 0))) (wl_Return 0 [2])) wl_Skip;
       wl_Assign 6 (ShiftVar Lsr 21 (dimindex(:A) - data_to_word_config_len_size c));
       wl_Assign 2 (wl_Op asm_Add [wl_Var 20; ShiftVar Lsl 6 (backend_common_word_shift(:A))]);
       wl_Assign 4 (wl_Op asm_Add [wl_Var 40; ShiftVar Lsl 6 (backend_common_word_shift(:A))]);
       wl_Call NONE (SOME Compare1_location) [0;6;2;4] NONE]`;;

let LongDiv_code_def = cake_def
  `LongDiv_code (c:data_to_word_config) =
     if data_to_word_config_has_longdiv c then
       data_to_word_list_Seq
         [wl_Inst (asm_Arith (LongDiv 1 3 2 4 6));
          wl_Set (Temp (word 28)) (wl_Var 3);
          wl_Return 0 [1]]
     else
       wl_Seq (wl_Assign 10 (wl_Const (word 0:A word)))
         (wl_Seq (wl_Assign 11 (wl_Const (word (dimindex(:A)))))
            (wl_Call NONE (SOME LongDiv1_location) [0;11;6;10;10;4;2] NONE))`;;

(* the following code is based on multiword single_div_loop_def *)

let LongDiv1_code_def = cake_def
  `LongDiv1_code (c:data_to_word_config) =
     if data_to_word_config_has_longdiv c then wl_Skip else
       wl_If asm_Test 2 (Reg 2)
         (wl_Seq (wl_Set (Temp (word 28)) (wl_Var 10):(A)wl_prog) (wl_Return 0 [8]))
         (data_to_word_list_Seq
            [wl_Assign 6 (wl_Op asm_Or [ShiftVar Lsr 6 1;
                                        ShiftVar Lsl 4 (dimindex(:A) - 1)]);
             wl_Assign 4 (ShiftVar Lsr 4 1);
             wl_Assign 8 (ShiftVar Lsl 8 1);
             wl_Assign 2 (wl_Op asm_Sub [wl_Var 2; wl_Const (word 1:A word)]);
             wl_If Lower 12 (Reg 4)
               (wl_Call NONE (SOME LongDiv1_location) [0;2;4;6;8;10;12] NONE) wl_Skip;
             wl_If asm_Equal 12 (Reg 4)
               (wl_If Lower 10 (Reg 6)
                  (wl_Call NONE (SOME LongDiv1_location) [0;2;4;6;8;10;12] NONE)
                  wl_Skip) wl_Skip;
             wl_Assign 8 (wl_Op asm_Add [wl_Var 8; wl_Const (word 1)]);
             wl_Assign 16 (wl_Op asm_Xor [wl_Var 6; wl_Const (word_neg (word 1))]);
             wl_Assign 14 (wl_Op asm_Xor [wl_Var 4; wl_Const (word_neg (word 1))]);
             wl_Assign 1 (wl_Const (word 1));
             wl_Inst (asm_Arith (asm_AddCarry 10 10 16 1));
             wl_Inst (asm_Arith (asm_AddCarry 12 12 14 1));
             wl_Call NONE (SOME LongDiv1_location) [0;2;4;6;8;10;12] NONE])`;;

let data_to_word_Append_code_def = cake_def
  `Append_code (c:data_to_word_config) =
     match encode_header c 0 2 with
       NONE -> (wl_Skip:(A)wl_prog)
     | SOME (header:A word) ->
         wl_If asm_Test 4 (Imm (word 1)) (wl_Return 0 [2])
           (data_to_word_list_Seq
              [wl_Set (Temp (word 0)) (wl_Var 2);
               wl_Set (Temp (word 1)) (wl_Var 4);
               wl_Assign 1 (Lookup NextFree);
               wl_Assign 3 (wl_Const header);
               wl_Assign 5 (wl_Op asm_Sub [Lookup TriggerGC; wl_Var 1]);
               wl_Assign 7 (wl_Op asm_Or
                 [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                    (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
                  wl_Const (word_or (word 1)
                              (word_bits (small_shift_length c - 1) 0 (ptr_bits c 0 2)))]);
               wl_Set (Temp (word 2)) (wl_Var 7);
               wl_Call NONE (SOME AppendMainLoop_location) [0; 1; 4; 3; 5; 7] NONE])`;;

(* unlucky case: GC is needed; cons case; nil case: arg 2 to append, ret    *)
(* value                                                                    *)

let AppendMainLoop_code_def = cake_def
  `AppendMainLoop_code (c:data_to_word_config) =
     data_to_word_list_Seq
       [wl_Assign 1 (real_addr c 4);
        wl_Assign 3 (wl_Load (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]));
        wl_Assign 5 (wl_Load (wl_Op asm_Add
                       [wl_Var 1; wl_Const (word_mul (word 2) bytes_in_word)]));
        wl_If Lower 8 (Imm (word_mul (word 3) bytes_in_word))
          (wl_Seq (wl_Assign 1 (wl_Const (word 0)))
                  (wl_Call NONE (SOME AppendLenLoop_location) [0; 4; 1] NONE)) wl_Skip;
        wl_Store (wl_Var 2) 6;
        wl_Store (wl_Op asm_Add [wl_Var 2; wl_Const bytes_in_word]) 3;
        wl_If asm_Test 5 (Imm (word 1)) wl_Skip
          (data_to_word_list_Seq
             [wl_Assign 10 (wl_Op asm_Add [wl_Var 10;
                wl_Const (word (3 * 2 EXP shift_length c))]);
              wl_Assign 8 (wl_Op asm_Sub [wl_Var 8; wl_Const (word_mul (word 3) bytes_in_word)]);
              wl_Store (wl_Op asm_Add [wl_Var 2; wl_Const (word_mul (word 2) bytes_in_word)]) 10;
              wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Const (word_mul (word 3) bytes_in_word)]);
              wl_Call NONE (SOME AppendMainLoop_location) [0; 2; 5; 6; 8; 10] NONE]);
        wl_Assign 1 (Lookup (Temp (word 0)));
        wl_Assign 3 (Lookup (Temp (word 2)));
        wl_Store (wl_Op asm_Add [wl_Var 2; wl_Const (word_mul (word 2) bytes_in_word)]) 1;
        wl_Set NextFree (wl_Op asm_Add [wl_Var 2; wl_Const (word_mul (word 3) bytes_in_word)]);
        wl_Return 0 [3]]:(A)wl_prog`;;

let AppendLenLoop_code_def = cake_def
  `AppendLenLoop_code (c:data_to_word_config) =
     wl_If asm_Test 2 (Imm (word 1))
       (data_to_word_list_Seq
          [wl_Assign 1 (wl_Op asm_Sub [Lookup TriggerGC; Lookup NextFree]);
           wl_Assign 1 (wl_Op asm_Add [wl_Var 4;
                          ShiftVar Lsr 1 (backend_common_word_shift(:A) - 2)]);
           wl_Assign 4 (Lookup (Temp (word 0)));
           wl_Assign 2 (Lookup (Temp (word 1)));
           AllocVar c ((dimword(:A) DIV 8) - 1) (fromList [one;one]);
           wl_Call NONE (SOME Append_location) [0; 4; 2] NONE])
       (data_to_word_list_Seq
          [wl_Assign 2 (wl_Load (wl_Op asm_Add
                          [real_addr c 2; wl_Const (word_mul (word 2) bytes_in_word)]));
           wl_Assign 4 (wl_Op asm_Add [wl_Var 4; wl_Const (word 12:A word)]);
           wl_Call NONE (SOME AppendLenLoop_location) [0; 2; 4] NONE])`;;

let XorLoop_code_def = cake_def
  `XorLoop_code =
     wl_If Lower 6 (Imm (word 2))
       (wl_If asm_Equal 6 (Imm (word 0))
          (data_to_word_list_Seq [wl_Assign 1 (wl_Const (word 2)); wl_Return 0 [1]])
          (data_to_word_list_Seq
             [wl_Assign 5 (wl_Load (wl_Var 4));
              wl_Assign 3 (wl_Load (wl_Var 2));
              wl_Assign 7 (wl_Op asm_Xor [wl_Var 5; wl_Var 3]);
              wl_Store (wl_Var 2) 7;
              wl_Assign 1 (wl_Const (word 2));
              wl_Return 0 [1]]))
       (data_to_word_list_Seq
          [wl_Assign 5 (wl_Load (wl_Var 4));
           wl_Assign 3 (wl_Load (wl_Var 2));
           wl_Assign 9 (wl_Load (wl_Op asm_Add [wl_Var 4; wl_Const bytes_in_word]));
           wl_Assign 7 (wl_Load (wl_Op asm_Add [wl_Var 2; wl_Const bytes_in_word]));
           wl_Assign 6 (wl_Op asm_Sub [wl_Var 6; wl_Const (word 2)]);
           wl_Assign 5 (wl_Op asm_Xor [wl_Var 5; wl_Var 3]);
           wl_Assign 9 (wl_Op asm_Xor [wl_Var 9; wl_Var 7]);
           wl_Store (wl_Var 2) 5;
           wl_Store (wl_Op asm_Add [wl_Var 2; wl_Const bytes_in_word]) 9;
           wl_Assign 4 (wl_Op asm_Add [wl_Var 4; wl_Const (word_mul (word 2) bytes_in_word)]);
           wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Const (word_mul (word 2) bytes_in_word)]);
           wl_Call NONE (SOME XorLoop_location) [0;2;4;6] NONE]):(A)wl_prog`;;

let StringCmpLoop_code_def = cake_def
  `StringCmpLoop_code =
     wl_If asm_Equal 6 (Imm bytes_in_word)
       (wl_Return 0 [8;10])
       (data_to_word_list_Seq
          [wl_Inst (Mem Load8 1 (Addr 2 (word 0)));
           wl_Inst (Mem Load8 3 (Addr 4 (word 0)));
           wl_If NotEqual 1 (Reg 3) (wl_Return 0 [1;3]) wl_Skip;
           wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Const (word 1)]);
           wl_Assign 4 (wl_Op asm_Add [wl_Var 4; wl_Const (word 1)]);
           wl_Assign 6 (wl_Op asm_Sub [wl_Var 6; wl_Const (word 1)]);
           wl_Call NONE (SOME StringCmpLoop_location) [0;2;4;6;8;10] NONE]):(A)wl_prog`;;

let data_to_word_get_names_def = cake_def
  `(data_to_word_get_names (NONE:(A spt)option) = LN) /\
   (data_to_word_get_names (SOME x) = x)`;;

let LoadWord64_def = cake_def
  `LoadWord64 (c:data_to_word_config) i j =
     wl_Assign i (wl_Load (wl_Op asm_Add [real_addr c j; wl_Const bytes_in_word]))
       :(A)wl_prog`;;

let LoadBignum_def = cake_def
  `LoadBignum (c:data_to_word_config) header word1 k = data_to_word_list_Seq [
     wl_Assign word1 (real_addr c k);
     wl_Assign header (wl_Load (wl_Var word1));
     wl_Assign word1 (wl_Load (wl_Op asm_Add [wl_Var word1; wl_Const bytes_in_word]))]
       :(A)wl_prog`;;

(* also works for storing bignums of length 1 *)

let WriteWord64_def = cake_def
  `WriteWord64 (c:data_to_word_config) (header:A word) dest i =
     data_to_word_list_Seq
       [wl_Assign 1 (Lookup NextFree);
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]) i;
        wl_Assign 3 (wl_Const header);
        wl_Store (wl_Var 1) 3;
        wl_Set NextFree (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 2) bytes_in_word)]);
        wl_Assign (adjust_var dest)
          (wl_Op asm_Or [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                           (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
                         wl_Const (word 1)])]`;;

let WriteWord64_on_32_def = cake_def
  `WriteWord64_on_32 (c:data_to_word_config) (header:A word) dest i1 i2 =
     data_to_word_list_Seq
       [wl_Assign 1 (Lookup NextFree);
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]) i2;
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 2) bytes_in_word)]) i1;
        wl_Assign 3 (wl_Const header);
        wl_Store (wl_Var 1) 3;
        wl_Set NextFree (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 3) bytes_in_word)]);
        wl_Assign (adjust_var dest)
          (wl_Op asm_Or [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                           (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
                         wl_Const (word 1)])]`;;

let WriteWord32_on_32_def = cake_def
  `WriteWord32_on_32 (c:data_to_word_config) header dest i1 =
     data_to_word_list_Seq
       [wl_Assign 1 (Lookup NextFree);
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]) i1;
        wl_Assign 3 (wl_Const header); wl_Store (wl_Var 1) 3;
        wl_Set NextFree (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 2) bytes_in_word)]);
        wl_Assign (adjust_var dest)
          (wl_Op asm_Or
             [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
              wl_Const (word 1:A word)])]`;;

let WordOp64_on_32_def = cake_def
  `WordOp64_on_32 (opw:opw) =
     match opw with
       Andw -> (data_to_word_list_Seq
                  [wl_Assign 29 (wl_Const (word 0));
                   wl_Assign 27 (wl_Const (word 0));
                   wl_Assign 33 (wl_Op asm_And [wl_Var 13; wl_Var 23]);
                   wl_Assign 31 (wl_Op asm_And [wl_Var 11; wl_Var 21])]:(A)wl_prog)
     | Orw -> data_to_word_list_Seq
                [wl_Assign 29 (wl_Const (word 0));
                 wl_Assign 27 (wl_Const (word 0));
                 wl_Assign 33 (wl_Op asm_Or [wl_Var 13; wl_Var 23]);
                 wl_Assign 31 (wl_Op asm_Or [wl_Var 11; wl_Var 21])]
     | backend_common_Xor -> data_to_word_list_Seq
                [wl_Assign 29 (wl_Const (word 0));
                 wl_Assign 27 (wl_Const (word 0));
                 wl_Assign 33 (wl_Op asm_Xor [wl_Var 13; wl_Var 23]);
                 wl_Assign 31 (wl_Op asm_Xor [wl_Var 11; wl_Var 21])]
     | backend_common_Add -> data_to_word_list_Seq
                [wl_Assign 29 (wl_Const (word 0));
                 wl_Assign 27 (wl_Const (word 0));
                 wl_Inst (asm_Arith (asm_AddCarry 33 13 23 29));
                 wl_Inst (asm_Arith (asm_AddCarry 31 11 21 29))]
     | backend_common_Sub -> data_to_word_list_Seq
                [wl_Assign 29 (wl_Const (word 1));
                 wl_Assign 27 (wl_Op asm_Xor [wl_Const (word_neg (word 1)); wl_Var 23]);
                 wl_Inst (asm_Arith (asm_AddCarry 33 13 27 29));
                 wl_Assign 27 (wl_Op asm_Xor [wl_Const (word_neg (word 1)); wl_Var 21]);
                 wl_Inst (asm_Arith (asm_AddCarry 31 11 27 29))]`;;

(* inputs in 11 and 13, writes results in 31 and 33 *)

let WordShift64_on_32_def = cake_def
  `WordShift64_on_32 sh n = data_to_word_list_Seq
     (if sh = Ror then
        (let n = n MOD 64 in
         (if n < 32 then
            [wl_Assign 33 (wl_Op asm_Or [ShiftVar Lsl 11 (32 - n); ShiftVar Lsr 13 n]);
             wl_Assign 31 (wl_Op asm_Or [ShiftVar Lsl 13 (32 - n); ShiftVar Lsr 11 n])]
          else
            [wl_Assign 33 (wl_Op asm_Or [ShiftVar Lsl 13 (64 - n);
                                         ShiftVar Lsr 11 (n - 32)]);
             wl_Assign 31 (wl_Op asm_Or [ShiftVar Lsl 11 (64 - n);
                                         ShiftVar Lsr 13 (n - 32)])]))
      else
        if n < 32 then
          (match sh with
             Lsl -> [wl_Assign 33 (ShiftVar sh 13 n);
                     wl_Assign 31 (wl_Op asm_Or [ShiftVar Lsr 13 (32 - n);
                                                 ShiftVar sh 11 n])]
           | Lsr -> [wl_Assign 33 (wl_Op asm_Or [ShiftVar Lsl 11 (32 - n);
                                                 ShiftVar sh 13 n]);
                     wl_Assign 31 (ShiftVar sh 11 n)]
           | Asr -> [wl_Assign 33 (wl_Op asm_Or [ShiftVar Lsl 11 (32 - n);
                                                 ShiftVar Lsr 13 n]);
                     wl_Assign 31 (ShiftVar sh 11 n)]
           | Ror -> [])
        else
          (match sh with
             Lsl -> [wl_Assign 33 (wl_Const (word 0));
                     wl_Assign 31 (ShiftVar sh 13 (n - 32))]
           | Lsr -> [wl_Assign 33 (ShiftVar sh 11 (n - 32));
                     wl_Assign 31 (wl_Const (word 0))]
           | Asr -> [wl_Assign 33 (ShiftVar sh 11 (n - 32));
                     wl_Assign 31 (ShiftVar sh 11 32)]
           | Ror -> ([]:((A)wl_prog)list)))`;;

let data_to_word_Smallnum_def = cake_def
  `Smallnum (i:int) =
     if i < &0 then word_sub (word 0) (word (num_of_int (&4 * (&0 - i))))
     else word (num_of_int (&4 * i)):A word`;;

(* HOL4: Overload FALSE_CONST = Const (n2w 2), TRUE_CONST = Const (n2w 18)  *)
(* (written out where used: wl_Const (word 2), wl_Const (word 18))          *)

let MemEqList_def = cake_def
  `(MemEqList (a:A word) [] = wl_Assign 1 (wl_Const (word 18))) /\
   (MemEqList a (CONS w ws) =
      wl_Seq (wl_Assign 5 (wl_Load (wl_Op asm_Add [wl_Var 3; wl_Const a])))
             (wl_If asm_Equal 5 (Imm w) (MemEqList (word_add a bytes_in_word) ws) wl_Skip))`;;

let get_gen_size_def = cake_def
  `(get_gen_size [] = word_mul bytes_in_word (word_neg (word 1)):A word) /\
   (get_gen_size (CONS x xs) =
      if val (bytes_in_word:A word) * x < dimword(:A)
      then word_mul bytes_in_word (word x)
      else word_mul bytes_in_word (word_neg (word 1)))`;;

let fp_cmp_inst_def = cake_def
  `(fp_cmp_inst FP_Less = FPLess 3 0 1) /\
   (fp_cmp_inst FP_LessEqual = FPLessEqual 3 0 1) /\
   (fp_cmp_inst FP_Greater = FPLess 3 1 0) /\
   (fp_cmp_inst FP_GreaterEqual = FPLessEqual 3 1 0) /\
   (fp_cmp_inst FP_Equal = FPEqual 3 0 1)`;;

let fp_top_inst_def = cake_def
  `fp_top_inst FP_Fma = FPFma 0 1 2`;;

let fp_bop_inst_def = cake_def
  `(fp_bop_inst FP_Add = FPAdd 0 0 1) /\
   (fp_bop_inst FP_Sub = FPSub 0 0 1) /\
   (fp_bop_inst FP_Mul = FPMul 0 0 1) /\
   (fp_bop_inst FP_Div = FPDiv 0 0 1)`;;

let fp_uop_inst_def = cake_def
  `(fp_uop_inst FP_Neg = FPNeg 1 0) /\
   (fp_uop_inst FP_Abs = FPAbs 1 0) /\
   (fp_uop_inst FP_Sqrt = FPSqrt 1 0)`;;

let data_to_word_arg1_def = cake_def
  `data_to_word_arg1 (vs:A list) (f:A->B) x =
     match vs with [v1] -> f v1 | _ -> x`;;

let data_to_word_arg2_def = cake_def
  `data_to_word_arg2 (vs:A list) (f:A->A->B) x =
     match vs with [v1;v2] -> f v1 v2 | _ -> x`;;

let arg3_def = cake_def
  `arg3 (vs:A list) (f:A->A->A->B) x =
     match vs with [v1;v2;v3] -> f v1 v2 v3 | _ -> x`;;

let arg4_def = cake_def
  `arg4 (vs:A list) (f:A->A->A->A->B) x =
     match vs with [v1;v2;v3;v4] -> f v1 v2 v3 v4 | _ -> x`;;

(* HOL4 arg2_pmatch, arg3_pmatch, arg4_pmatch: the definitions with pmatch *)
(* case expressions; both are written with match here (compiled into case  *)
(* constants), so the theorems restate the definitions                     *)

let data_to_word_arg2_pmatch = prove
 (CASE_TERM
  `!(vs:A list) (f:A->A->B) x.
     data_to_word_arg2 vs f x = match vs with [v1;v2] -> f v1 v2 | _ -> x`,
  REWRITE_TAC[data_to_word_arg2_def]);;

let arg3_pmatch = prove
 (CASE_TERM
  `!(vs:A list) (f:A->A->A->B) x.
     arg3 vs f x = match vs with [v1;v2;v3] -> f v1 v2 v3 | _ -> x`,
  REWRITE_TAC[arg3_def]);;

let arg4_pmatch = prove
 (CASE_TERM
  `!(vs:A list) (f:A->A->A->A->B) x.
     arg4 vs f x = match vs with [v1;v2;v3;v4] -> f v1 v2 v3 v4 | _ -> x`,
  REWRITE_TAC[arg4_def]);;

(* HOL4 collects the assign_NAME definitions below in the ML list           *)
(* assign_defs (all_assign_defs is their conjunction)                      *)

(* bvl_to_bvi compilation ensures that all literal constants fit into a    *)
(* machine word                                                             *)

let assign_Const_def = cake_def
  `assign_Const (i:int) (l:num) (dest:num) =
     if i < &0
     then (wl_Assign (adjust_var dest)
             (wl_Const (word_sub (word 0) (word (num_of_int (&4 * (&0 - i)))))),l)
     else ((wl_Assign (adjust_var dest) (wl_Const (word (num_of_int (&4 * i)))),l)
             :(A)wl_prog#num)`;;

let assign_SetGlobalsPtr_def = cake_def
  `assign_SetGlobalsPtr (c:data_to_word_config) (l:num) (dest:num) v1 =
     ((wl_Seq (wl_Set Globals (wl_Var (adjust_var v1)))
        (wl_Seq (wl_Set GlobReal (real_addr c (adjust_var v1)))
           (wl_Assign (adjust_var dest) data_to_word_Unit)),l):(A)wl_prog#num)`;;

let assign_Global_def = cake_def
  `assign_Global (c:data_to_word_config) n (l:num) (dest:num) =
     ((wl_Assign (adjust_var dest)
         (wl_Load (wl_Op asm_Add [Lookup GlobReal;
                                  wl_Const (word_mul bytes_in_word (word (n + 1)))])),l)
        :(A)wl_prog#num)`;;

let assign_SetGlobal_def = cake_def
  `assign_SetGlobal (c:data_to_word_config) n (l:num) (dest:num) v1 =
     ((wl_Seq (wl_Store (wl_Op asm_Add [Lookup GlobReal;
                                        wl_Const (word_mul bytes_in_word (word (n + 1)))])
                        (adjust_var v1))
              (wl_Assign (adjust_var dest) data_to_word_Unit),l):(A)wl_prog#num)`;;

let assign_El_def = cake_def
  `assign_El (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
     ((wl_Assign (adjust_var dest)
         (wl_Load (wl_Op asm_Add [real_addr c (adjust_var v1);
                                  real_offset c (adjust_var v2)])),l):(A)wl_prog#num)`;;

let assign_ElemAt_def = cake_def
  `assign_ElemAt (c:data_to_word_config) n (l:num) (dest:num) v1 =
     ((wl_Assign (adjust_var dest)
         (wl_Load (wl_Op asm_Add [real_addr c (adjust_var v1);
                                  wl_Const (word_add bytes_in_word
                                              (word_mul bytes_in_word (word n)))])),l)
        :(A)wl_prog#num)`;;

let assign_DerefByte_def = cake_def
  `assign_DerefByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
     ((data_to_word_list_Seq [
         wl_Assign 1 (wl_Op asm_Add [real_addr c (adjust_var v1);
                                     real_byte_offset (adjust_var v2)]);
         wl_Inst (Mem Load8 3 (Addr 1 (word 0)));
         wl_Assign (adjust_var dest) (wl_Shift Lsl (wl_Var 3) (wl_Const (word 2)))], l)
        :(A)wl_prog#num)`;;

let assign_Update_def = cake_def
  `assign_Update (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3 =
     ((wl_Seq (wl_Store (wl_Op asm_Add [real_addr c (adjust_var v1);
                                        real_offset c (adjust_var v2)])
                        (adjust_var v3))
              (wl_Assign (adjust_var dest) data_to_word_Unit),l):(A)wl_prog#num)`;;

let assign_UpdateThunk_def = cake_def
  `assign_UpdateThunk ev (c:data_to_word_config) (l:num) (dest:num) v1 v2 =
     (match ev with
        NotEvaluated ->
          (wl_Seq (wl_Store (wl_Op asm_Add [real_addr c (adjust_var v1);
                                            wl_Const bytes_in_word])
                            (adjust_var v2))
                  (wl_Assign (adjust_var dest) data_to_word_Unit),l)
      | Evaluated ->
          (match encode_header c (8 + 6) 1 with
             NONE -> (GiveUp,l)
           | SOME (header:A word) -> (data_to_word_list_Seq
               [wl_Assign 1 (real_addr c (adjust_var v1));
                wl_Assign 3 (wl_Const header);
                wl_Store (wl_Var 1) 3;
                wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]) (adjust_var v2);
                wl_Assign (adjust_var dest) data_to_word_Unit],l)):(A)wl_prog#num)`;;

let assign_UpdateByte_def = cake_def
  `assign_UpdateByte (c:data_to_word_config) (l:num) (dest:num) v1 v2 v3 =
     ((data_to_word_list_Seq [
         wl_Assign 1 (wl_Op asm_Add [real_addr c (adjust_var v1);
                                     real_byte_offset (adjust_var v2)]);
         wl_Assign 3 (wl_Shift Lsr (wl_Var (adjust_var v3)) (wl_Const (word 2)));
         wl_Inst (Mem Store8 3 (Addr 1 (word 0)));
         wl_Assign (adjust_var dest) data_to_word_Unit], l):(A)wl_prog#num)`;;

let assign_ListAppend_def = cake_def
  `assign_ListAppend (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                     (names:num_set option) v1 v2 =
     (match encode_header c 0 2 with
        NONE -> (GiveUp,l)
      | SOME (header:A word) ->
          ((MustTerminate
              (wl_Call (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                              wl_Skip,secn,l))
                 (SOME Append_location) [adjust_var v2; adjust_var v1] NONE):(A)wl_prog),
           l + 1):(A)wl_prog#num)`;;

(* tag is too big to be represented: GiveUp *)

let assign_Cons_def = cake_def
  `assign_Cons (c:data_to_word_config) (l:num) (dest:num) tag args =
     if LENGTH args = 0 then
       if tag < dimword(:A) DIV 16 then
         (wl_Assign (adjust_var dest) (wl_Const (word (16 * tag + 2))),l)
       else (GiveUp,l)
     else
       (match encode_header c (4 * tag) (LENGTH args) with
          NONE -> (GiveUp,l)
        | SOME (header:A word) -> (data_to_word_list_Seq
            [wl_Assign 1 (Lookup NextFree);
             wl_Assign 3 (wl_Const header);
             StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0);
             wl_Assign (adjust_var dest)
               (wl_Op asm_Or
                  [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                     (wl_Const (word (shift_length c - backend_common_word_shift(:A))));
                   wl_Const (word_or (word 1)
                               (word_bits (small_shift_length c - 1) 0
                                  (ptr_bits c tag (LENGTH args))))]);
             wl_Set NextFree (wl_Op asm_Add [wl_Var 1;
               wl_Const (word_mul bytes_in_word (word (LENGTH args + 1)))])],l)
          :(A)wl_prog#num)`;;

let assign_MutCons_def = cake_def
  `assign_MutCons (c:data_to_word_config) (l:num) (dest:num) tag args =
     match data_to_word_config_gc_kind c with
       Generational _ -> (GiveUp,l)
     | _ -> (assign_Cons c l dest tag args:(A)wl_prog#num)`;;

(* Alloc 1 ... runs the GC *)

let assign_ConfigGC_def = cake_def
  `assign_ConfigGC (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                   (names:num_set option) (v1:B) (v2:C) =
     ((data_to_word_list_Seq
         [SilentFFI c 3 (adjust_sets (data_to_word_get_names names));
          wl_Assign 1 (wl_Const (word 0));
          wl_Alloc 1 (adjust_sets (data_to_word_get_names names));
          SilentFFI c 3 (adjust_sets (data_to_word_get_names names));
          wl_Assign (adjust_var dest) (wl_Const (word 2))],l):(A)wl_prog#num)`;;
let getWords_def = cake_def
  `(getWords [] (aux:(bool#A word)list) = (REVERSE aux,[])) /\
   (getWords (CONS (c:bool#(A)word_loc) cs) aux =
      match c with
        (b,wl_Word w) -> getWords cs (CONS (b,w) aux)
      | _ -> (REVERSE aux,CONS c cs))`;;

(* HOL4 proves this inside the termination proof of StoreAnyConsts *)

let D2WAUX_getWords_LENGTH = prove
 (`!ws (aux:(bool#A word)list) ws1 vs1.
     getWords ws aux = (ws1,vs1) ==> LENGTH vs1 <= LENGTH ws`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[getWords_def; PAIR_EQ] THENL
   [MESON_TAC[LENGTH; LE_REFL]; ALL_TAC] THEN
  GEN_TAC THEN CASES_ON `h:bool#(A)word_loc` THEN
  CASES_ON `y:(A)word_loc` THEN SIMP[PAIR_EQ; LENGTH] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_ARITH_TAC);;

let StoreAnyConsts_def = cake_def_wf_clauses
  `measure (\(r1:num,r2:num,r3:num,vs:(bool#(A)word_loc)list,v:bool#(A)word_loc). LENGTH vs)`
  (REWRITE_TAC[measure_THM; FORALL_PAIR_THM] THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[SND] THEN STRIP_TAC THEN
   FS[getWords_def] THEN IMP_RES_TAC D2WAUX_getWords_LENGTH THEN
   REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC)
  [`StoreAnyConsts r1 r2 r3 ([]:(bool#(A)word_loc)list) (v:bool#(A)word_loc) =
      wl_Seq (wl_Set NextFree (wl_Var r2))
        (match SND v with
           wl_Loc n _ -> wl_LocValue r1 n
         | wl_Word w -> wl_Assign r1 (if FST v then wl_Op asm_Add [wl_Const w; wl_Var r3]
                                      else wl_Const w))`;
   `StoreAnyConsts r1 r2 r3 (CONS (v:bool#(A)word_loc) vs) (w:bool#(A)word_loc) =
      match (SND v:(A)word_loc) with
        wl_Loc n _ -> data_to_word_list_Seq
                        [wl_LocValue r1 n;
                         wl_Store (wl_Var r2) r1;
                         wl_Assign r2 (wl_Op asm_Add [wl_Var r2; wl_Const bytes_in_word]);
                         StoreAnyConsts r1 r2 r3 vs w]
      | _ -> let (ws,vs1) = getWords (CONS v vs) [] in
             wl_Seq (wl_StoreConsts r2 r3 r2 r3 ws)
                    (StoreAnyConsts r1 r2 r3 vs1 w:(A)wl_prog)`];;

let StoreAnyConsts_ind = cake_ind "StoreAnyConsts";;

let lookup_mem_def = cake_def
  `lookup_mem m a =
     match lookup a m with
       NONE -> (F,wl_Word (word 0:A word))
     | SOME x -> x`;;

(* HOL4 byte_len (:'a) num_bytes: as conf_ok *)

let byte_len_DEF = new_definition
  `byte_len (s:A->bool) num_bytes =
     if dimindex(:A) = 32 then num_bytes DIV 4 + 1
     else num_bytes DIV 8 + 1`;;

let byte_len_def = prove
 (`!num_bytes. byte_len (:A) num_bytes =
     if dimindex(:A) = 32 then num_bytes DIV 4 + 1
     else num_bytes DIV 8 + 1`,
  REWRITE_TAC[byte_len_DEF]);;

let make_byte_header_def = cake_def
  `make_byte_header (conf:data_to_word_config) cmp_by_contents len =
     let tag = if cmp_by_contents then word 7 else word 23 in
     (if dimindex(:A) = 32
      then word_or (word_shl (word (len + 4))
                      ((dimindex(:A) - 2) - data_to_word_config_len_size conf)) tag
      else word_or (word_shl (word (len + 8))
                      ((dimindex(:A) - 3) - data_to_word_config_len_size conf)) tag):A word`;;

let get_lowerbits_def = cake_def
  `(get_lowerbits (conf:data_to_word_config) (wl_Word w) =
      word_or (word_bits (small_shift_length conf - 1) 0 w) (word 1)) /\
   (get_lowerbits conf _ = word 1:A word)`;;

let make_cons_ptr_def = cake_def
  `make_cons_ptr (conf:data_to_word_config) nf tag len =
     wl_Word (word_or (word_shl nf (shift_length conf - backend_common_word_shift(:A)))
               (word_or (word 1:A word)
                  (get_lowerbits conf (wl_Word (ptr_bits conf tag len)))))`;;

let make_ptr_def = cake_def
  `make_ptr (conf:data_to_word_config) nf (tag:B) (len:C) =
     wl_Word (word_or (word_shl nf (shift_length conf - backend_common_word_shift(:A)))
                      (word 1:A word))`;;

let write_bytes_def = cake_def
  `(write_bytes bs [] be = []) /\
   (write_bytes bs (CONS (w:A word) ws) be =
      let k = dimindex(:A) DIV 8 in
      CONS (bytes_to_word k (word 0) bs w be) (write_bytes (DROP k bs) ws be))`;;

(* HOL4 small_int (:'a) i: as conf_ok *)

let small_int_DEF = new_definition
  `small_int (s:A->bool) (i:int) <=>
     --(&(dimword(:A) DIV 8)) <= i /\ i < &(dimword(:A) DIV 8)`;;

let small_int_def = prove
 (`!i. small_int (:A) i <=>
     --(&(dimword(:A) DIV 8)) <= i /\ i < &(dimword(:A) DIV 8)`,
  REWRITE_TAC[small_int_DEF]);;

let part_to_words_def = cake_def
  `(part_to_words (c:data_to_word_config) m (clos_Int i) (offset:A word) =
      (if small_int (:A) i then SOME ((F,wl_Word (Smallnum i)),[])
       else let (sign,ws) = i2mw i in
            match encode_header c (if sign then 7 else 3) (LENGTH ws) with
              NONE -> NONE
            | SOME hd -> SOME ((T,(make_ptr c offset (word 0:A word) (LENGTH ws))),
                               MAP (\w. (F,wl_Word w)) (CONS hd ws)))) /\
   (part_to_words c m (clos_Con t ns) offset =
      (if NULL ns then
         if t < dimword(:A) DIV 16
         then SOME ((F,wl_Word (word (16 * t + 2))),[]) else NONE
       else
         match encode_header c (4 * t) (LENGTH ns) with
           NONE -> NONE
         | SOME hd -> SOME ((T,wl_Word
                               (word_add
                                  (word_shl offset
                                     (shift_length c - backend_common_word_shift(:A)))
                                  (word_or (ptr_bits c t (LENGTH ns)) (word 1)))),
                            CONS (F,wl_Word hd) (MAP (lookup_mem m) ns)))) /\
   (part_to_words c m (clos_W64 w) offset =
      (let ws = (if dimindex(:A) < 64
                 then [word_extract 63 32 w; word_extract 31 0 w]
                 else [word_extract 63 0 w:A word]) in
       match encode_header c 3 (LENGTH ws) with
         NONE -> NONE
       | SOME hd -> SOME ((T,(make_ptr c offset (word 0:A word) (LENGTH ws))),
                          MAP (\w. (F,wl_Word w)) (CONS hd ws)))) /\
   (part_to_words c m (clos_Str s) offset =
      (let bytes = MAP (word o ORD) (explode s) in
       let n = LENGTH bytes in
       let hd = make_byte_header c T n in
       let k = byte_len (:A) n in
       let ws = write_bytes bytes (REPLICATE k (word 0)) (data_to_word_config_be c) in
       if k < 2 EXP (dimindex(:A) - 4) /\ k < 2 EXP data_to_word_config_len_size c
       then SOME ((T,(make_ptr c offset (word 0:A word) k)),
                  MAP (\w. (F,wl_Word w)) (CONS hd ws))
       else NONE))`;;

let parts_to_words_def = cake_def
  `(parts_to_words (c:data_to_word_config) m i [] (off:A word) =
      SOME (lookup_mem m (i - 1), [])) /\
   (parts_to_words c m i (CONS x parts) off =
      match part_to_words c m x off with
        NONE -> NONE
      | SOME (w,xs) ->
          match parts_to_words c (insert i w m) (i + 1) parts
                  (word_add off (word_mul bytes_in_word (word (LENGTH xs)))) with
            NONE -> NONE
          | SOME (r,ys) -> SOME (r,APPEND xs ys))`;;

let const_parts_to_words_def = cake_def
  `const_parts_to_words (c:data_to_word_config) parts =
     parts_to_words c LN 0 parts (word 0:A word)`;;

let get_Word_def = cake_def
  `(get_Word (wl_Word w) = w) /\
   (get_Word _ = word 0:A word)`;;
let _ = cake_add_simps [get_Word_def];;

let assign_Build_def = cake_def
  `assign_Build (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                (names:num_set option) ps =
     match const_parts_to_words c ps with
       NONE -> (GiveUp,l)
     | SOME (w,ws) ->
         ((data_to_word_list_Seq
             [wl_Assign 1 (Lookup NextFree);
              wl_Assign 3 (wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                             (wl_Const (word (shift_length c -
                                              backend_common_word_shift(:A)))));
              StoreAnyConsts (adjust_var dest) 1 3 ws w],l):(A)wl_prog#num)`;;

let assign_ConsExtend_def = cake_def
  `assign_ConsExtend (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                     (names:num_set option) tag args =
     (match args with
        CONS old (CONS start (CONS len (CONS tot rest))) ->
          (match encode_header c (4 * tag) 0 with
             NONE -> (GiveUp,l)
           | SOME header ->
               let limit = MIN (2 EXP data_to_word_config_len_size c)
                               (dimword(:A) DIV 16) in
               let h = wl_Shift Lsl (wl_Var (adjust_var tot))
                         (wl_Const (word ((dimindex(:A) -
                                           data_to_word_config_len_size c) - 2))) in
               (data_to_word_list_Seq
                  [BignumHalt (adjust_var tot);
                   wl_Assign 1 (wl_Var (adjust_var tot));
                   AllocVar c limit (list_insert args (data_to_word_get_names names));
                   wl_Assign 1 (Lookup NextFree);
                   wl_Assign 5 (wl_Op asm_Or [h; wl_Const header]);
                   wl_Assign 7 (wl_Shift Lsr (wl_Var (adjust_var tot)) (wl_Const (word 2)));
                   wl_Assign 9 (wl_Const (word tag));
                   StoreEach 1 (CONS 5 (MAP adjust_var rest)) (word 0);
                   Make_ptr_bits_code c 9 7 3;
                   wl_Set NextFree (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word;
                     wl_Shift Lsl (wl_Var 7)
                       (wl_Const (word (backend_common_word_shift(:A))))]);
                   wl_Assign 15 (wl_Var (adjust_var len));
                   wl_Assign 13 (wl_Op asm_Add [wl_Var 1;
                     wl_Const (word_mul bytes_in_word (word (LENGTH rest + 1)))]);
                   wl_Assign 11 (wl_Op asm_Add [real_addr c (adjust_var old);
                     wl_Const bytes_in_word;
                     ShiftVar Lsl (adjust_var start) (backend_common_word_shift(:A) - 2)]);
                   wl_If asm_Test 15 (Reg 15) (wl_Assign (adjust_var dest) (wl_Var 3))
                     (data_to_word_list_Seq [
                        MustTerminate
                          (wl_Call (SOME ([adjust_var dest],
                                          adjust_sets (data_to_word_get_names names),
                                          wl_Skip,secn,l))
                             (SOME MemCopy_location) [15;11;13;3] NONE)])],l + 1))
      | _ -> (wl_Skip,l)):(A)wl_prog#num`;;

let assign_Ref_def = cake_def
  `assign_Ref (c:data_to_word_config) (secn:num) (l:num) (dest:num)
              (names:num_set option) args =
     (match encode_header c 2 (LENGTH args) with
        NONE -> (GiveUp,l)
      | SOME (header:A word) -> (data_to_word_list_Seq
          [wl_Set TriggerGC (wl_Op asm_Sub [Lookup TriggerGC;
             wl_Const (word_mul bytes_in_word (word (LENGTH args + 1)))]);
           wl_Assign 1 (wl_Op asm_Sub [Lookup EndOfHeap;
             wl_Const (word_mul bytes_in_word (word (LENGTH args + 1)))]);
           wl_Set EndOfHeap (wl_Var 1);
           wl_Assign 3 (wl_Const header);
           StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0);
           wl_Assign (adjust_var dest)
             (wl_Op asm_Or [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                              (wl_Const (word (shift_length c -
                                               backend_common_word_shift(:A))));
                            wl_Const (word 1)])],l)):(A)wl_prog#num`;;

let assign_AllocThunk_def = cake_def
  `assign_AllocThunk (ev:thunk_mode) (c:data_to_word_config) (secn:num) (l:num)
                     (dest:num) (names:num_set option) arg =
     (let tag = (match ev with Evaluated -> 8 + 6 | NotEvaluated -> 0 + 6) in
      match encode_header c tag 1 with
        NONE -> (GiveUp,l)
      | SOME (header:A word) -> (data_to_word_list_Seq
          [wl_Set TriggerGC (wl_Op asm_Sub [Lookup TriggerGC;
             wl_Const (word_mul bytes_in_word (word 2))]);
           wl_Assign 1 (wl_Op asm_Sub [Lookup EndOfHeap;
             wl_Const (word_mul bytes_in_word (word 2))]);
           wl_Set EndOfHeap (wl_Var 1);
           wl_Assign 3 (wl_Const header);
           StoreEach 1 [3; adjust_var arg] (word 0);
           wl_Assign (adjust_var dest)
             (wl_Op asm_Or [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
                              (wl_Const (word (shift_length c -
                                               backend_common_word_shift(:A))));
                            wl_Const (word 1)])],l)):(A)wl_prog#num`;;

(* n.b. Assign 1 would have been better done with Set Temp *)

let assign_RefByte_def = cake_def
  `assign_RefByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                  (names:num_set option) immutable v1 v2 =
     ((wl_Seq
         (wl_Assign 1 (wl_Const (if immutable then word 0 else word 16)))
         (MustTerminate
            (wl_Call (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                            wl_Skip,secn,l))
               (SOME RefByte_location) [adjust_var v1; adjust_var v2; 1] NONE))
         :(A)wl_prog),l + 1)`;;

let assign_XorByte_def = cake_def
  `assign_XorByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                  (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq [
         wl_Assign 1 (real_addr c (adjust_var v1));
         wl_Assign 3 (real_addr c (adjust_var v2));
         wl_Assign 5 (SmallLsr (wl_Load (wl_Var 3))
                        (dimindex(:A) - data_to_word_config_len_size c));
         wl_Assign 1 (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]);
         wl_Assign 3 (wl_Op asm_Add [wl_Var 3; wl_Const (bytes_in_word:A word)]);
         MustTerminate
           (wl_Call
              (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                     wl_Skip,secn,l))
              (SOME XorLoop_location) [1;3;5] NONE)],l + 1):(A)wl_prog#num)`;;

(* HOL4 TRUE_CONST is wl_Const (word 18), FALSE_CONST is wl_Const (word 2) *)

let SetBool_def = cake_def
  `SetBool dest cmp r ri =
     wl_If cmp r ri
       (wl_Assign dest (wl_Const (word 18)))
       (wl_Assign dest (wl_Const (word 2))):(A)wl_prog`;;

let AssignCmp_def = cake_def
  `(AssignCmp dest Lt v1 v2 = SetBool dest Lower v1 (Reg v2):(A)wl_prog) /\
   (AssignCmp dest Gt v1 v2 = SetBool dest Lower v2 (Reg v1)) /\
   (AssignCmp dest Leq v1 v2 = SetBool dest NotLower v2 (Reg v1)) /\
   (AssignCmp dest Geq v1 v2 = SetBool dest NotLower v1 (Reg v2))`;;

(* the loads give len + bytes_in_word; real_addr gives the address of the   *)
(* header                                                                   *)

let assign_StringCmp_def = cake_def
  `assign_StringCmp (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                    (names:num_set option) (b:bool) (cmp:opb) v1 v2 =
     (((let k = (dimindex(:A) - data_to_word_config_len_size c) -
                backend_common_word_shift(:A) in
       data_to_word_list_Seq [
         wl_Assign 1 (real_addr c (adjust_var v1));
         wl_Assign 3 (real_addr c (adjust_var v2));
         wl_Assign 5 (wl_Shift Lsr (wl_Load (wl_Var 1)) (wl_Const (word k)));
         wl_Assign 7 (wl_Shift Lsr (wl_Load (wl_Var 3)) (wl_Const (word k)));
         (if b then
            wl_If asm_Equal 5 (Reg 7)
              (data_to_word_list_Seq
                 [wl_Assign 11 (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]);
                  wl_Assign 13 (wl_Op asm_Add [wl_Var 3; wl_Const bytes_in_word]);
                  MustTerminate
                    (wl_Call (SOME ([5;7],adjust_sets (data_to_word_get_names names),
                                    wl_Skip,secn,l))
                       (SOME StringCmpLoop_location) [11;13;7;7;7] NONE)])
              wl_Skip
          else
            data_to_word_list_Seq
              [wl_Assign 11 (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]);
               wl_Assign 13 (wl_Op asm_Add [wl_Var 3; wl_Const bytes_in_word]);
               wl_Assign 9 (wl_Var 5);
               wl_If Lower 7 (Reg 5) (wl_Assign 9 (wl_Var 7)) wl_Skip;
               MustTerminate
                 (wl_Call (SOME ([5;7],adjust_sets (data_to_word_get_names names),
                                 wl_Skip,secn,l))
                    (SOME StringCmpLoop_location) [11;13;9;5;7] NONE)]);
         AssignCmp (adjust_var dest) cmp 5 7]),l + 1):(A)wl_prog#num)`;;

(* [v1;v2;v3;v4;v5]: alloc_new is F; [v1;v2;v3]: alloc_new is T *)

let assign_CopyByte_def = cake_def
  `assign_CopyByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                   (names:num_set option) args =
     (match args with
        [v1;v2;v3;v4;v5] ->
          ((MustTerminate
              (wl_Call (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                              wl_Skip,secn,l))
                 (SOME ByteCopy_location)
                 [adjust_var v1; adjust_var v2; adjust_var v3;
                  adjust_var v4; adjust_var v5] NONE):(A)wl_prog),l + 1)
      | [v1;v2;v3] ->
          ((MustTerminate
              (wl_Call (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                              wl_Skip,secn,l))
                 (SOME ByteCopyNew_location)
                 [adjust_var v1; adjust_var v2; adjust_var v3] NONE):(A)wl_prog),l + 1)
      | _ -> (wl_Skip,l))`;;

let assign_RefArray_def = cake_def
  `assign_RefArray (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                   (names:num_set option) v1 v2 =
     let limit = MIN (2 EXP data_to_word_config_len_size c) (dimword(:A) DIV 16) in
     (data_to_word_list_Seq
        [BignumHalt (adjust_var v1);
         wl_Move 0 [(1,adjust_var v1)];
         AllocVar c limit (list_insert [v1; v2] (data_to_word_get_names names));
         (MustTerminate
            (wl_Call (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                            wl_Skip,secn,l))
               (SOME RefArray_location) [adjust_var v1; adjust_var v2] NONE)
            :(A)wl_prog)],l + 1)`;;

let assign_FromList_def = cake_def
  `assign_FromList (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                   (names:num_set option) tag v1 v2 =
     if encode_header c (4 * tag) 0 = (NONE:(A word)option) then (GiveUp,l) else
       (MustTerminate (data_to_word_list_Seq [
          wl_Assign 1 (wl_Const (word (16 * tag)));
          (wl_Call (SOME ([adjust_var dest],adjust_sets (data_to_word_get_names names),
                          wl_Skip,secn,l))
             (SOME FromList_location) [adjust_var v1; adjust_var v2; 1] NONE
             :(A)wl_prog)]),l + 1)`;;

let assign_LessConstSmall_def = cake_def
  `assign_LessConstSmall (l:num) (dest:num) i v1 =
     ((wl_If asm_Less (adjust_var v1) (Imm (word (4 * i)))
         (wl_Assign (adjust_var dest) (wl_Const (word 18)))
         (wl_Assign (adjust_var dest) (wl_Const (word 2))),l):(A)wl_prog#num)`;;

let assign_BoolTest_def = cake_def
  `assign_BoolTest (l:num) (dest:num) (test:test) v1 v2 =
     ((wl_If asm_Equal (adjust_var v1) (Reg (adjust_var v2))
         (wl_Assign (adjust_var dest) (wl_Const (word 18)))
         (wl_Assign (adjust_var dest) (wl_Const (word 2))),l):(A)wl_prog#num)`;;

let assign_BoolNot_def = cake_def
  `assign_BoolNot (l:num) (dest:num) v1 =
     ((wl_Assign (adjust_var dest)
         (wl_Op asm_Xor [wl_Var (adjust_var v1); wl_Const (word 16)]),l)
        :(A)wl_prog#num)`;;

let assign_WordTest_def = cake_def
  `assign_WordTest (l:num) (dest:num) (test:test) v1 v2 =
     (((match test with
         Equal -> wl_If asm_Equal (adjust_var v1) (Reg (adjust_var v2))
                    (wl_Assign (adjust_var dest) (wl_Const (word 18)))
                    (wl_Assign (adjust_var dest) (wl_Const (word 2)))
       | Compare Lt -> wl_If Lower (adjust_var v1) (Reg (adjust_var v2))
                         (wl_Assign (adjust_var dest) (wl_Const (word 18)))
                         (wl_Assign (adjust_var dest) (wl_Const (word 2)))
       | Compare Leq -> wl_If NotLower (adjust_var v2) (Reg (adjust_var v1))
                          (wl_Assign (adjust_var dest) (wl_Const (word 18)))
                          (wl_Assign (adjust_var dest) (wl_Const (word 2)))
       | _ -> wl_Skip),l):(A)wl_prog#num)`;;

let assign_BoundsCheckByte_def = cake_def
  `assign_BoundsCheckByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                          (names:num_set option) leq v1 v2 =
     ((data_to_word_list_Seq
         [wl_Assign 1
            (let addr = real_addr c (adjust_var v1) in
             let header = wl_Load addr in
             let extra = (if dimindex(:A) = 32 then 2 else 3) in
             let k = (dimindex(:A) - data_to_word_config_len_size c) - extra in
             wl_Op asm_Sub [wl_Shift Lsr header (wl_Const (word k)); wl_Const bytes_in_word]);
          wl_Assign 3 (ShiftVar Ror (adjust_var v2) 2);
          (if leq then wl_If NotLower 1 (Reg 3) else wl_If Lower 3 (Reg 1))
            (wl_Assign (adjust_var dest) (wl_Const (word 18)))
            (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l):(A)wl_prog#num)`;;

let assign_BoundsCheckArray_def = cake_def
  `assign_BoundsCheckArray (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                           (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Assign 1
            (let addr = real_addr c (adjust_var v1) in
             let header = wl_Load addr in
             let k = dimindex(:A) - data_to_word_config_len_size c in
             wl_Shift Lsr header (wl_Const (word k)));
          wl_Assign 3 (ShiftVar Ror (adjust_var v2) 2);
          wl_If Lower 3 (Reg 1)
            (wl_Assign (adjust_var dest) (wl_Const (word 18)))
            (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l):(A)wl_prog#num)`;;

let assign_BoundsCheckBlock_def = cake_def
  `assign_BoundsCheckBlock (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                           (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_If asm_Test (adjust_var v1) (Imm (word 1))
            (wl_Assign 1 (wl_Const (word 0)))
            (wl_Assign 1
               (let addr = real_addr c (adjust_var v1) in
                let header = wl_Load addr in
                let k = dimindex(:A) - data_to_word_config_len_size c in
                wl_Shift Lsr header (wl_Const (word k))));
          wl_Assign 3 (ShiftVar Ror (adjust_var v2) 2);
          wl_If Lower 3 (Reg 1)
            (wl_Assign (adjust_var dest) (wl_Const (word 18)))
            (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l):(A)wl_prog#num)`;;

let assign_Equal_def = cake_def
  `assign_Equal (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Assign 1 (wl_Var (adjust_var v1));
          wl_Assign 3 (wl_Var (adjust_var v2));
          wl_Assign 5 (wl_Op asm_And [wl_Var 1; wl_Var 3]);
          wl_If asm_Test 5 (Imm (word 1)) wl_Skip
            (wl_If asm_Equal 1 (Reg 3) wl_Skip
               (wl_Seq (MustTerminate
                          (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                          wl_Skip,secn,l))
                             (SOME Equal_location) [1;3] NONE))
                       (wl_Assign 3 (wl_Const (word 1)))));
          (wl_If asm_Equal 1 (Reg 3)
             (wl_Assign (adjust_var dest) (wl_Const (word 18)))
             (wl_Assign (adjust_var dest) (wl_Const (word 2))))],l + 1):(A)wl_prog#num)`;;

let assign_Less_def = cake_def
  `assign_Less (c:data_to_word_config) (secn:num) (l:num) (dest:num)
               (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Assign 1 (wl_Var (adjust_var v1));
          wl_Assign 3 (wl_Var (adjust_var v2));
          wl_Assign 5 (wl_Op asm_Or [wl_Var 1; wl_Var 3]);
          wl_If asm_Test 5 (Imm (word 1)) wl_Skip
            (wl_Seq (MustTerminate
                       (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                       wl_Skip,secn,l))
                          (SOME Compare_location) [1;3] NONE))
                    (wl_Assign 3 (wl_Const (word 1))));
          (wl_If asm_Less 1 (Reg 3)
             (wl_Assign (adjust_var dest) (wl_Const (word 18)))
             (wl_Assign (adjust_var dest) (wl_Const (word 2))))],l + 1):(A)wl_prog#num)`;;

let assign_LessEq_def = cake_def
  `assign_LessEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                 (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Assign 1 (wl_Var (adjust_var v1));
          wl_Assign 3 (wl_Var (adjust_var v2));
          wl_Assign 5 (wl_Op asm_Or [wl_Var 1; wl_Var 3]);
          wl_If asm_Test 5 (Imm (word 1)) wl_Skip
            (wl_Seq (MustTerminate
                       (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                       wl_Skip,secn,l))
                          (SOME Compare_location) [1;3] NONE))
                    (wl_Assign 3 (wl_Const (word 1))));
          (wl_If NotLess 3 (Reg 1)
             (wl_Assign (adjust_var dest) (wl_Const (word 18)))
             (wl_Assign (adjust_var dest) (wl_Const (word 2))))],l + 1):(A)wl_prog#num)`;;

let assign_LengthBlock_def = cake_def
  `assign_LengthBlock (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                      (names:num_set option) v1 =
     ((wl_If asm_Test (adjust_var v1) (Imm (word 1))
         (wl_Assign (adjust_var dest) (wl_Const (word 0)))
         (wl_Assign (adjust_var dest)
            (let addr = real_addr c (adjust_var v1) in
             let header = wl_Load addr in
             let k = dimindex(:A) - data_to_word_config_len_size c in
             let len = wl_Shift Lsr header (wl_Const (word k)) in
             wl_Shift Lsl len (wl_Const (word 2)))),l):(A)wl_prog#num)`;;

let assign_Length_def = cake_def
  `assign_Length (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                 (names:num_set option) v1 =
     ((wl_Assign (adjust_var dest)
         (let addr = real_addr c (adjust_var v1) in
          let header = wl_Load addr in
          let k = dimindex(:A) - data_to_word_config_len_size c in
          let len = wl_Shift Lsr header (wl_Const (word k)) in
          wl_Shift Lsl len (wl_Const (word 2))),l):(A)wl_prog#num)`;;

let assign_LengthByte_def = cake_def
  `assign_LengthByte (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                     (names:num_set option) v1 =
     ((wl_Assign (adjust_var dest)
         (let addr = real_addr c (adjust_var v1) in
          let header = wl_Load addr in
          let k = (dimindex(:A) - backend_common_word_shift(:A)) -
                  data_to_word_config_len_size c in
          let fakelen = wl_Shift Lsr header (wl_Const (word k)) in
          let len = wl_Op asm_Sub [fakelen; wl_Const bytes_in_word] in
          wl_Shift Lsl len (wl_Const (word 2))),l):(A)wl_prog#num)`;;

let assign_TagLenEq_def = cake_def
  `assign_TagLenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                   (names:num_set option) tag len v1 =
     (if len = 0 then
        if tag < dimword(:A) DIV 16 then
          (wl_If asm_Equal (adjust_var v1) (Imm (word (16 * tag + 2)))
             (wl_Assign (adjust_var dest) (wl_Const (word 18)))
             (wl_Assign (adjust_var dest) (wl_Const (word 2))),l)
        else (wl_Assign (adjust_var dest) (wl_Const (word 2)),l)
      else if tag < 2 EXP data_to_word_config_tag_bits c - 1 /\
              len < 2 EXP data_to_word_config_len_bits c - 1 then
        (wl_Seq
           (wl_Assign 1 (wl_Op asm_And
              [wl_Var (adjust_var v1);
               wl_Const (all_ones ((data_to_word_config_len_bits c +
                                    data_to_word_config_tag_bits c) + 1) 0)]))
           (wl_If asm_Equal 1 (Imm (word_or (ptr_bits c tag len) (word 1)))
              (wl_Assign (adjust_var dest) (wl_Const (word 18)))
              (wl_Assign (adjust_var dest) (wl_Const (word 2)))),l)
      else
        match encode_header c (4 * tag) len with
          NONE -> (wl_Assign (adjust_var dest) (wl_Const (word 2)),l)
        | SOME h ->
            (data_to_word_list_Seq
               [wl_Assign 1 (wl_Const (word 0));
                wl_If asm_Test (adjust_var v1) (Imm (word 1)) wl_Skip
                  (wl_Assign 1 (wl_Load (real_addr c (adjust_var v1))));
                wl_If asm_Equal 1 (Imm h)
                  (wl_Assign (adjust_var dest) (wl_Const (word 18)))
                  (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l)):(A)wl_prog#num`;;

let assign_LenEq_def = cake_def
  `assign_LenEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                (names:num_set option) len v1 =
     (if len = 0 then
        (wl_If asm_Test (adjust_var v1) (Imm (word 1))
           (wl_Assign (adjust_var dest) (wl_Const (word 18)))
           (wl_Assign (adjust_var dest) (wl_Const (word 2))),l)
      else if len < 2 EXP data_to_word_config_len_bits c - 1 then
        (wl_Seq
           (wl_Assign 1 (wl_Op asm_And
              [wl_Var (adjust_var v1);
               wl_Const (all_ones (data_to_word_config_len_bits c + 1) 0)]))
           (wl_If asm_Equal 1 (Imm (word_or (ptr_bits c 0 len) (word 1)))
              (wl_Assign (adjust_var dest) (wl_Const (word 18)))
              (wl_Assign (adjust_var dest) (wl_Const (word 2)))),l)
      else if len < dimword(:A) then
        (data_to_word_list_Seq
           [wl_Assign 1 (wl_Const (word 0));
            wl_If asm_Test (adjust_var v1) (Imm (word 1)) wl_Skip
              (wl_Assign 1
                 (let addr = real_addr c (adjust_var v1) in
                  let header = wl_Load addr in
                  let k = dimindex(:A) - data_to_word_config_len_size c in
                  let len = wl_Shift Lsr header (wl_Const (word k)) in
                  len));
            wl_If asm_Equal 1 (Imm (word len))
              (wl_Assign (adjust_var dest) (wl_Const (word 18)))
              (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l)
      else
        (wl_Assign (adjust_var dest) (wl_Const (word 2)),l)):(A)wl_prog#num`;;

let assign_TagEq_def = cake_def
  `assign_TagEq (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                (names:num_set option) tag v1 =
     (if tag < dimword(:A) DIV 16 then
        (data_to_word_list_Seq
           [wl_Assign 1 (wl_Var (adjust_var v1));
            wl_If asm_Test (adjust_var v1) (Imm (word 1)) wl_Skip
              (wl_Assign 1 (let v = adjust_var v1 in
                            let h = wl_Load (real_addr c v) in
                            wl_Op asm_And [h; wl_Const (word_or (tag_mask c) (word 2))]));
            wl_If asm_Equal 1 (Imm (word (16 * tag + 2)))
              (wl_Assign (adjust_var dest) (wl_Const (word 18)))
              (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l)
      else (wl_Assign (adjust_var dest) (wl_Const (word 2)),l)):(A)wl_prog#num`;;

(* perform addition; or together bits of overflow flag, and the two inputs; *)
(* if the least significant bit is set, then bignum is needed               *)

let assign_Add_def = cake_def
  `assign_Add (c:data_to_word_config) (secn:num) (l:num) (dest:num)
              (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Inst (asm_Arith (AddOverflow 1 (adjust_var v1) (adjust_var v2) 3));
          wl_Assign 3 (wl_Op asm_Or [wl_Var 3; wl_Var (adjust_var v1);
                                     wl_Var (adjust_var v2)]);
          wl_If asm_Test 3 (Imm (word 1)) wl_Skip
            (MustTerminate
               (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                               wl_Skip,secn,l))
                  (SOME Add_location) [adjust_var v1; adjust_var v2] NONE));
          wl_Move 2 [(adjust_var dest,1)]],l + 1):(A)wl_prog#num)`;;

(* perform subtraction; as for assign_Add *)

let assign_Sub_def = cake_def
  `assign_Sub (c:data_to_word_config) (secn:num) (l:num) (dest:num)
              (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Inst (asm_Arith (SubOverflow 1 (adjust_var v1) (adjust_var v2) 3));
          wl_Assign 3 (wl_Op asm_Or [wl_Var 3; wl_Var (adjust_var v1);
                                     wl_Var (adjust_var v2)]);
          wl_If asm_Test 3 (Imm (word 1)) wl_Skip
            (MustTerminate
               (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                               wl_Skip,secn,l))
                  (SOME Sub_location) [adjust_var v1; adjust_var v2] NONE));
          wl_Move 2 [(adjust_var dest,1)]],l + 1):(A)wl_prog#num)`;;

let assign_Mult_def = cake_def
  `assign_Mult (c:data_to_word_config) (secn:num) (l:num) (dest:num)
               (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq
         [wl_Assign 1 (ShiftVar Lsr (adjust_var v1) 1);
          wl_Inst (asm_Arith (LongMul 3 1 1 (adjust_var v2)));
          wl_Assign 3 (wl_Op asm_Or [wl_Var 3;
                         wl_Op asm_And [wl_Const (word 1);
                           wl_Op asm_Or [wl_Var (adjust_var v1); wl_Var (adjust_var v2)]]]);
          wl_Assign 1 (ShiftVar Lsr 1 1);
          wl_If asm_Equal 3 (Imm (word 0)) wl_Skip
            (MustTerminate
               (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                               wl_Skip,secn,l))
                  (SOME Mul_location) [adjust_var v1; adjust_var v2] NONE));
          wl_Move 2 [(adjust_var dest,1)]],l + 1):(A)wl_prog#num)`;;

let assign_Div_def = cake_def
  `assign_Div (c:data_to_word_config) (secn:num) (l:num) (dest:num)
              (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq [
         wl_Assign 1 (wl_Op asm_Or [wl_Var (adjust_var v1); wl_Var (adjust_var v2)]);
         wl_Assign 1 (wl_Op asm_Or [wl_Var 1; ShiftVar Lsr 1 (dimindex(:A) - 1)]);
         wl_If asm_Test 1 (Imm (word 1:A word))
           (if data_to_word_config_has_div c then
              data_to_word_list_Seq
                [wl_Inst (asm_Arith (asm_Div 1 (adjust_var v1) (adjust_var v2)));
                 wl_Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
            else if data_to_word_config_has_longdiv c then
              data_to_word_list_Seq
                [wl_Assign 1 (wl_Const (word 0));
                 wl_Inst (asm_Arith (LongDiv 1 3 1 (adjust_var v1) (adjust_var v2)));
                 wl_Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
            else
              data_to_word_list_Seq
                [wl_Assign 1 (wl_Const (word 0));
                 MustTerminate
                   (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                   wl_Skip,secn,l + 1))
                      (SOME LongDiv_location) [1; adjust_var v1; adjust_var v2] NONE);
                 wl_Assign (adjust_var dest) (ShiftVar Lsl 1 2)])
           (data_to_word_list_Seq
              [MustTerminate
                 (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                 wl_Skip,secn,l))
                    (SOME Div_location) [adjust_var v1; adjust_var v2] NONE);
               wl_Move 2 [(adjust_var dest,1)]])],l + 2):(A)wl_prog#num)`;;

let assign_Mod_def = cake_def
  `assign_Mod (c:data_to_word_config) (secn:num) (l:num) (dest:num)
              (names:num_set option) v1 v2 =
     ((data_to_word_list_Seq [
         wl_Assign 1 (wl_Op asm_Or [wl_Var (adjust_var v1); wl_Var (adjust_var v2)]);
         wl_Assign 1 (wl_Op asm_Or [wl_Var 1; ShiftVar Lsr 1 (dimindex(:A) - 1)]);
         wl_If asm_Test 1 (Imm (word 1:A word))
           (if data_to_word_config_has_div c then
              data_to_word_list_Seq
                [wl_Inst (asm_Arith (asm_Div 1 (adjust_var v1) (adjust_var v2)));
                 wl_Inst (asm_Arith (LongMul 3 1 1 (adjust_var v2)));
                 wl_Assign (adjust_var dest)
                   (wl_Op asm_Sub [wl_Var (adjust_var v1); wl_Var 1])]
            else if data_to_word_config_has_longdiv c then
              data_to_word_list_Seq
                [wl_Assign 1 (wl_Const (word 0));
                 wl_Inst (asm_Arith (LongDiv 1 3 1 (adjust_var v1) (adjust_var v2)));
                 wl_Move 2 [(adjust_var dest,3)]]
            else
              data_to_word_list_Seq
                [wl_Assign 1 (wl_Const (word 0));
                 MustTerminate
                   (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                   wl_Skip,secn,l + 1))
                      (SOME LongDiv_location) [1; adjust_var v1; adjust_var v2] NONE);
                 wl_Get (adjust_var dest) (Temp (word 28))])
           (data_to_word_list_Seq
              [MustTerminate
                 (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names),
                                 wl_Skip,secn,l))
                    (SOME Mod_location) [adjust_var v1; adjust_var v2] NONE);
               wl_Move 2 [(adjust_var dest,1)]])],l + 2):(A)wl_prog#num)`;;

let assign_WordOpW8_def = cake_def
  `assign_WordOpW8 opw (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                   (names:num_set option) v1 v2 =
     ((wl_Assign (adjust_var dest)
         (match lookup_word_op opw with
            Bitwise op -> wl_Op op [wl_Var (adjust_var v1); wl_Var (adjust_var v2)]
          | Carried op -> let k = dimindex(:A) - 10 in
              wl_Shift Lsr
                (wl_Shift Lsl (wl_Op op [wl_Var (adjust_var v1); wl_Var (adjust_var v2)])
                   (wl_Const (word k)))
                (wl_Const (word k))), l):(A)wl_prog#num)`;;

let assign_WordOpW64_def = cake_def
  `assign_WordOpW64 opw (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                    (names:num_set option) v1 v2 =
     (if dimindex(:A) = 64 then
        (match encode_header c 3 1 with
           NONE -> (GiveUp,l)
         | SOME (header:A word) ->
             (wl_Seq (wl_Assign 3
                (wl_Op (match opw with
                          Andw -> asm_And
                        | Orw -> asm_Or
                        | backend_common_Xor -> asm_Xor
                        | backend_common_Add -> asm_Add
                        | backend_common_Sub -> asm_Sub)
                   [wl_Load (wl_Op asm_Add [real_addr c (adjust_var v1);
                                            wl_Const bytes_in_word]);
                    wl_Load (wl_Op asm_Add [real_addr c (adjust_var v2);
                                            wl_Const bytes_in_word])]))
                (WriteWord64 c header dest 3),l))
      else
        (match encode_header c 3 2 with
           NONE -> (GiveUp,l)
         | SOME header ->
             (data_to_word_list_Seq [
                wl_Assign 15 (real_addr c (adjust_var v1));
                wl_Assign 17 (real_addr c (adjust_var v2));
                wl_Assign 11 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
                wl_Assign 13 (wl_Load (wl_Op asm_Add
                                [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Assign 21 (wl_Load (wl_Op asm_Add [wl_Var 17; wl_Const bytes_in_word]));
                wl_Assign 23 (wl_Load (wl_Op asm_Add
                                [wl_Var 17; wl_Const (word_mul (word 2) bytes_in_word)]));
                WordOp64_on_32 opw;
                WriteWord64_on_32 c header dest 33 31],l))):(A)wl_prog#num`;;

let assign_WordShiftW8_def = cake_def
  `assign_WordShiftW8 sh n (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                      (names:num_set option) v1 =
     ((wl_Assign (adjust_var dest)
         (match sh with
            Lsl ->
              wl_Shift Lsr
                (wl_Shift Lsl (wl_Var (adjust_var v1))
                   (wl_Const (word ((dimindex(:A) - 10) + MIN n 8))))
                (wl_Const (word (dimindex(:A) - 10)))
          | Lsr ->
              wl_Shift Lsl
                (wl_Shift Lsr (wl_Var (adjust_var v1)) (wl_Const (word (MIN n 8 + 2))))
                (wl_Const (word 2))
          | Asr ->
              wl_Shift Lsl
                (wl_Shift Lsr
                   (wl_Shift Asr
                      (wl_Shift Lsl (wl_Var (adjust_var v1))
                         (wl_Const (word (dimindex(:A) - 10))))
                      (wl_Const (word (MIN n 8))))
                   (wl_Const (word (dimindex(:A) - 8))))
                (wl_Const (word 2))
          | Ror ->
              (let n = n MOD 8 in
               wl_Op asm_Or
                 [wl_Shift Lsl (ShiftVar Lsr (adjust_var v1) (n + 2)) (wl_Const (word 2));
                  wl_Shift Lsr (ShiftVar Lsl (adjust_var v1) ((dimindex(:A) - 2) - n))
                    (wl_Const (word (dimindex(:A) - 10)))])),l):(A)wl_prog#num)`;;

let assign_WordShiftW64_def = cake_def
  `assign_WordShiftW64 sh n (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                       (names:num_set option) v1 =
     let len = if dimindex(:A) < 64 then 2 else 1 in
     (match encode_header c 3 len with
        NONE -> (GiveUp,l)
      | SOME (header:A word) ->
          ((if len = 1 then
              data_to_word_list_Seq
                [LoadWord64 c 3 (adjust_var v1);
                 wl_Assign 3 (ShiftVar sh 3 n);
                 WriteWord64 c header dest 3]
            else
              data_to_word_list_Seq [
                wl_Assign 15 (real_addr c (adjust_var v1));
                wl_Assign 11 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
                wl_Assign 13 (wl_Load (wl_Op asm_Add
                                [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
                WordShift64_on_32 sh n;
                WriteWord64_on_32 c header dest 33 31]),l)):(A)wl_prog#num`;;

let assign_WordFromWord_def = cake_def
  `assign_WordFromWord b (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                       (names:num_set option) v1 =
     (if b then
        (data_to_word_list_Seq
           [wl_Assign 1 (real_addr c (adjust_var v1));
            wl_Assign 1 (wl_Load (wl_Op asm_Add [wl_Var 1;
              wl_Const (if dimindex(:A) = 32
                        then word_mul (word 2) bytes_in_word else bytes_in_word)]));
            wl_Assign 1 (wl_Op asm_And [wl_Var 1; wl_Const (word 255)]);
            wl_Assign (adjust_var dest) (ShiftVar Lsl 1 2)],l)
      else
        (let len = if dimindex(:A) < 64 then 2 else 1 in
         match encode_header c 3 len with
           NONE -> (GiveUp,l)
         | SOME header ->
             (if len = 1 then
                (data_to_word_list_Seq
                   [wl_Assign 3 (wl_Shift Lsr (wl_Var (adjust_var v1)) (wl_Const (word 2)));
                    WriteWord64 c header dest 3],l)
              else
                (data_to_word_list_Seq
                   [wl_Assign 5 (wl_Shift Lsr (wl_Var (adjust_var v1)) (wl_Const (word 2)));
                    wl_Assign 3 (wl_Const (word 0));
                    WriteWord64_on_32 c header dest 5 3],l)))):(A)wl_prog#num`;;

(* put the word value into 3: smallnum case, bignum case; bignum of length *)
(* 1: positive case, negative case; longer bignum: positive case, negative  *)
(* case (messy)                                                             *)

let assign_WordFromInt_def = cake_def
  `assign_WordFromInt (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                      (names:num_set option) v1 =
     let len = if dimindex(:A) < 64 then 2 else 1 in
     (match encode_header c 3 len with
        NONE -> (GiveUp,l)
      | SOME (header:A word) ->
          ((if len = 1 then
              wl_Seq
                (wl_If asm_Test (adjust_var v1) (Imm (word 1))
                   (wl_Assign 3 (wl_Shift Asr (wl_Var (adjust_var v1)) (wl_Const (word 2))))
                   (wl_Seq
                      (LoadBignum c 1 3 (adjust_var v1))
                      (wl_If asm_Test 1 (Imm (word 16)) wl_Skip
                         (wl_Assign 3 (wl_Op asm_Sub [wl_Const (word 0); wl_Var 3])))))
                (WriteWord64 c header dest 3)
            else wl_If asm_Test (adjust_var v1) (Imm (word 1))
              (data_to_word_list_Seq [
                 wl_Assign 3 (wl_Shift Asr (wl_Var (adjust_var v1)) (wl_Const (word 2)));
                 wl_Assign 5 (wl_Shift Asr (wl_Var (adjust_var v1)) (wl_Const (word 31)));
                 WriteWord64_on_32 c header dest 3 5])
              (data_to_word_list_Seq [
                 wl_Assign 1 (real_addr c (adjust_var v1));
                 wl_Assign 3 (wl_Load (wl_Var 1));
                 wl_Assign 5 (wl_Load (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]));
                 wl_Assign 7 (ShiftVar Lsr 3 (dimindex(:A) - data_to_word_config_len_size c));
                 wl_If asm_Equal 7 (Imm (word 1))
                   (wl_If asm_Test 3 (Imm (word 16))
                      (wl_Seq (wl_Assign 9 (wl_Const (word 0)))
                              (WriteWord64_on_32 c header dest 5 9))
                      (wl_Seq (wl_Assign 9 (wl_Const (word_not (word 0))))
                         (wl_Seq (wl_Assign 5 (wl_Op asm_Sub [wl_Const (word 0); wl_Var 5]))
                                 (WriteWord64_on_32 c header dest 5 9))))
                   (wl_If asm_Test 3 (Imm (word 16))
                      (wl_Seq (wl_Assign 9 (wl_Load
                                 (wl_Op asm_Add [wl_Var 1;
                                                 wl_Const (word_mul (word 2) bytes_in_word)])))
                              (WriteWord64_on_32 c header dest 5 9))
                      (data_to_word_list_Seq
                         [wl_Assign 11 (wl_Const (word 0));
                          wl_Assign 13 (wl_Const (word 1));
                          wl_Assign 9 (wl_Load
                            (wl_Op asm_Add [wl_Var 1;
                                            wl_Const (word_mul (word 2) bytes_in_word)]));
                          wl_Assign 5 (wl_Op asm_Xor [wl_Const (word_not (word 0)); wl_Var 5]);
                          wl_Assign 9 (wl_Op asm_Xor [wl_Const (word_not (word 0)); wl_Var 9]);
                          wl_Inst (asm_Arith (asm_AddCarry 15 11 5 13));
                          wl_Inst (asm_Arith (asm_AddCarry 19 11 9 13));
                          WriteWord64_on_32 c header dest 15 19]))])), l)):(A)wl_prog#num`;;

let assign_WordToInt_def = cake_def
  `assign_WordToInt (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                    (names:num_set option) v =
     let len = if dimindex(:A) < 64 then 2 else 1 in
     (match encode_header c 3 len with
        NONE -> (GiveUp,l)
      | SOME header ->
          if len = 1 then
            (data_to_word_list_Seq
               [LoadWord64 c 3 (adjust_var v);
                wl_Assign 1 (wl_Shift Lsr (wl_Var 3) (wl_Const (word 61)));
                wl_If asm_Equal 1 (Imm (word 0))
                  (wl_Assign (adjust_var dest) (wl_Shift Lsl (wl_Var 3) (wl_Const (word 2))))
                  (WriteWord64 c header dest 3)], l)
          else
            (match encode_header c 3 1 with
               NONE -> (GiveUp,l)
             | SOME header1 ->
                 (data_to_word_list_Seq [
                    wl_Assign 15 (real_addr c (adjust_var v));
                    wl_Assign 13 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
                    wl_Assign 11 (wl_Load (wl_Op asm_Add
                                    [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
                    wl_If NotEqual 13 (Imm (word 0))
                      (WriteWord64_on_32 c header dest 13 11)
                      (data_to_word_list_Seq [
                         wl_Assign 1 (wl_Shift Lsr (wl_Var 11) (wl_Const (word 29)));
                         wl_If asm_Equal 1 (Imm (word 0))
                           (wl_Assign (adjust_var dest)
                              (wl_Shift Lsl (wl_Var 11) (wl_Const (word 2))))
                           (WriteWord32_on_32 c header1 dest 11)])],l))):(A)wl_prog#num`;;

let assign_FFI_def = cake_def
  `assign_FFI ffi_index (c:data_to_word_config) (secn:num) (l:num) (dest:num)
              (names:num_set option) v1 v2 =
     (if ~data_to_word_config_call_empty_ffi c /\ ffi_index = implode ""
      then (wl_Assign (adjust_var dest) data_to_word_Unit,l) else
      let addr1 = real_addr c (adjust_var v1) in
      let header1 = wl_Load addr1 in
      let k = (dimindex(:A) - backend_common_word_shift(:A)) -
              data_to_word_config_len_size c in
      let fakelen1 = wl_Shift Lsr header1 (wl_Const (word k)) in
      let addr2 = real_addr c (adjust_var v2) in
      let header2 = wl_Load addr2 in
      let fakelen2 = wl_Shift Lsr header2 (wl_Const (word k)) in
      (data_to_word_list_Seq [
         wl_Assign 1 (wl_Op asm_Add [addr1; wl_Const bytes_in_word]);
         wl_Assign 3 (wl_Op asm_Sub [fakelen1; wl_Const bytes_in_word]);
         wl_Assign 5 (if ffi_index = implode "" then wl_Const (word 0)
                      else wl_Op asm_Add [addr2; wl_Const bytes_in_word]);
         wl_Assign 7 (if ffi_index = implode "" then wl_Const (word 0)
                      else wl_Op asm_Sub [fakelen2; wl_Const bytes_in_word]);
         wl_FFI ffi_index 1 3 5 7
           (adjust_sets (match names with SOME names -> names | NONE -> LN));
         wl_Assign (adjust_var dest) data_to_word_Unit], l)):(A)wl_prog#num`;;

let assign_EqualConst_def = cake_def
  `assign_EqualConst p (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                     (names:num_set option) v =
     (match part_to_words c LN p (word 0) with
        SOME ((F,w),_) ->
          (wl_If asm_Equal (adjust_var v) (Imm (get_Word w))
             (wl_Assign (adjust_var dest) (wl_Const (word 18)))
             (wl_Assign (adjust_var dest) (wl_Const (word 2))),l)
      | SOME (_,words) ->
          ((match p with
              clos_Int _ ->
                wl_If asm_Test (adjust_var v) (Imm (word 1))
                  (wl_Assign (adjust_var dest) (wl_Const (word 2)))
                  (data_to_word_list_Seq
                     [wl_Assign 1 (wl_Const (word 2));
                      wl_Assign 3 (real_addr c (adjust_var v));
                      MemEqList (word 0) (MAP (get_Word o SND) words);
                      wl_Assign (adjust_var dest) (wl_Var 1)])
            | clos_W64 _ ->
                (data_to_word_list_Seq
                   [wl_Assign 1 (wl_Const (word 2));
                    wl_Assign 3 (wl_Op asm_Add [real_addr c (adjust_var v);
                                                wl_Const bytes_in_word]);
                    MemEqList (word 0) (MAP (get_Word o SND) (TL words));
                    wl_Assign (adjust_var dest) (wl_Var 1)])
            | clos_Str _ ->
                (data_to_word_list_Seq
                   [wl_Assign 1 (wl_Const (word 2));
                    wl_Assign 3 (real_addr c (adjust_var v));
                    MemEqList (word 0) (MAP (get_Word o SND) words);
                    wl_Assign (adjust_var dest) (wl_Var 1)])
            | _ -> wl_Skip),l)
      | _ -> (wl_Assign (adjust_var dest) (wl_Const (word 2)),l)):(A)wl_prog#num`;;

(* BignumHalt: the lengths must be smallints; GiveUp: too little data      *)
(* space, too little code space                                             *)

let assign_Install_def = cake_def
  `assign_Install (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                  (names:num_set option) v1 v2 v3 v4 =
     ((data_to_word_list_Seq
         [BignumHalt (adjust_var v3);
          BignumHalt (adjust_var v4);
          wl_Assign 1 (Lookup BitmapBuffer);
          wl_Assign 3 (wl_Op asm_Sub [Lookup BitmapBufferEnd; wl_Var 1]);
          wl_Assign 5 (ShiftVar Lsr (adjust_var v4) 2);
          wl_Assign 3 (ShiftVar Lsr 3 (backend_common_word_shift(:A)));
          wl_If Lower 3 (Reg 5) GiveUp wl_Skip;
          wl_Assign 1 (Lookup CodeBuffer);
          wl_Assign 3 (wl_Op asm_Sub [Lookup CodeBufferEnd; wl_Var 1]);
          wl_Assign 5 (ShiftVar Lsr (adjust_var v3) 2);
          wl_If Lower 3 (Reg 5) GiveUp wl_Skip;
          MustTerminate
            (wl_Call (SOME ([adjust_var dest],
                            adjust_sets (data_to_word_get_names names),wl_Skip,secn,l))
               (SOME InstallCode_location)
               [adjust_var v1; adjust_var v2; 1] NONE)],l + 1):(A)wl_prog#num)`;;

let assign_FP_cmp_def = cake_def
  `assign_FP_cmp fpc (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                 (names:num_set option) v1 v2 =
     (if ~data_to_word_config_has_fp_ops c then (GiveUp,l) else
      if dimindex(:A) = 64 then
        (data_to_word_list_Seq [
           wl_Assign 3 (wl_Load (wl_Op asm_Add
                          [real_addr c (adjust_var v1); wl_Const bytes_in_word]));
           wl_Assign 5 (wl_Load (wl_Op asm_Add
                          [real_addr c (adjust_var v2); wl_Const bytes_in_word]));
           wl_Inst (FP (FPMovFromReg 0 3 3));
           wl_Inst (FP (FPMovFromReg 1 5 5));
           wl_Inst (FP (fp_cmp_inst fpc));
           wl_Assign (adjust_var dest)
             (wl_Op asm_Add [ShiftVar Lsl 3 4; wl_Const (word 2)])],l)
      else
        (data_to_word_list_Seq [
           wl_Assign 15 (real_addr c (adjust_var v1));
           wl_Assign 17 (real_addr c (adjust_var v2));
           wl_Assign 11 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
           wl_Assign 13 (wl_Load (wl_Op asm_Add
                           [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
           wl_Assign 21 (wl_Load (wl_Op asm_Add [wl_Var 17; wl_Const bytes_in_word]));
           wl_Assign 23 (wl_Load (wl_Op asm_Add
                           [wl_Var 17; wl_Const (word_mul (word 2) bytes_in_word)]));
           wl_Inst (FP (FPMovFromReg 0 13 11));
           wl_Inst (FP (FPMovFromReg 1 23 21));
           wl_Inst (FP (fp_cmp_inst fpc));
           wl_Assign (adjust_var dest)
             (wl_Op asm_Add [ShiftVar Lsl 3 4; wl_Const (word 2)])],l)):(A)wl_prog#num`;;

let assign_FP_top_def = cake_def
  `assign_FP_top fpt (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                 (names:num_set option) v1 v2 v3 =
     (if ~data_to_word_config_has_fp_ops c \/ ~data_to_word_config_has_fp_tern c
      then (GiveUp,l) else
      if dimindex(:A) = 64 then
        (match encode_header c 3 1 with
           NONE -> (GiveUp,l)
         | SOME (header:A word) ->
             (data_to_word_list_Seq [
                wl_Assign 3 (wl_Load (wl_Op asm_Add
                               [real_addr c (adjust_var v1); wl_Const bytes_in_word]));
                wl_Assign 5 (wl_Load (wl_Op asm_Add
                               [real_addr c (adjust_var v2); wl_Const bytes_in_word]));
                wl_Assign 7 (wl_Load (wl_Op asm_Add
                               [real_addr c (adjust_var v3); wl_Const bytes_in_word]));
                wl_Inst (FP (FPMovFromReg 0 3 3));
                wl_Inst (FP (FPMovFromReg 1 5 5));
                wl_Inst (FP (FPMovFromReg 2 7 7));
                wl_Inst (FP (fp_top_inst fpt));
                wl_Inst (FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l))
      else
        (match encode_header c 3 2 with
           NONE -> (GiveUp,l)
         | SOME header ->
             (data_to_word_list_Seq [
                wl_Assign 15 (real_addr c (adjust_var v1));
                wl_Assign 17 (real_addr c (adjust_var v2));
                wl_Assign 19 (real_addr c (adjust_var v3));
                wl_Assign 11 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
                wl_Assign 13 (wl_Load (wl_Op asm_Add
                                [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Assign 21 (wl_Load (wl_Op asm_Add [wl_Var 17; wl_Const bytes_in_word]));
                wl_Assign 23 (wl_Load (wl_Op asm_Add
                                [wl_Var 17; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Assign 31 (wl_Load (wl_Op asm_Add [wl_Var 19; wl_Const bytes_in_word]));
                wl_Assign 33 (wl_Load (wl_Op asm_Add
                                [wl_Var 19; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Inst (FP (FPMovFromReg 0 13 11));
                wl_Inst (FP (FPMovFromReg 1 23 21));
                wl_Inst (FP (FPMovFromReg 2 33 31));
                wl_Inst (FP (fp_top_inst fpt));
                wl_Inst (FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):(A)wl_prog#num`;;

let assign_FP_bop_def = cake_def
  `assign_FP_bop fpb (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                 (names:num_set option) v1 v2 =
     (if ~data_to_word_config_has_fp_ops c then (GiveUp,l) else
      if dimindex(:A) = 64 then
        (match encode_header c 3 1 with
           NONE -> (GiveUp,l)
         | SOME (header:A word) ->
             (data_to_word_list_Seq [
                wl_Assign 3 (wl_Load (wl_Op asm_Add
                               [real_addr c (adjust_var v1); wl_Const bytes_in_word]));
                wl_Assign 5 (wl_Load (wl_Op asm_Add
                               [real_addr c (adjust_var v2); wl_Const bytes_in_word]));
                wl_Inst (FP (FPMovFromReg 0 3 3));
                wl_Inst (FP (FPMovFromReg 1 5 5));
                wl_Inst (FP (fp_bop_inst fpb));
                wl_Inst (FP (FPMovToReg 3 5 0));
                WriteWord64 c header dest 3],l))
      else
        (match encode_header c 3 2 with
           NONE -> (GiveUp,l)
         | SOME header ->
             (data_to_word_list_Seq [
                wl_Assign 15 (real_addr c (adjust_var v1));
                wl_Assign 17 (real_addr c (adjust_var v2));
                wl_Assign 11 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
                wl_Assign 13 (wl_Load (wl_Op asm_Add
                                [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Assign 21 (wl_Load (wl_Op asm_Add [wl_Var 17; wl_Const bytes_in_word]));
                wl_Assign 23 (wl_Load (wl_Op asm_Add
                                [wl_Var 17; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Inst (FP (FPMovFromReg 0 13 11));
                wl_Inst (FP (FPMovFromReg 1 23 21));
                wl_Inst (FP (fp_bop_inst fpb));
                wl_Inst (FP (FPMovToReg 5 3 0));
                WriteWord64_on_32 c header dest 5 3],l))):(A)wl_prog#num`;;

let assign_FP_uop_def = cake_def
  `assign_FP_uop fpu (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                 (names:num_set option) v1 =
     (if ~data_to_word_config_has_fp_ops c then (GiveUp,l) else
      if dimindex(:A) = 64 then
        (match encode_header c 3 1 with
           NONE -> (GiveUp,l)
         | SOME (header:A word) ->
             (data_to_word_list_Seq [
                wl_Assign 3 (wl_Load (wl_Op asm_Add
                               [real_addr c (adjust_var v1); wl_Const bytes_in_word]));
                wl_Inst (FP (FPMovFromReg 0 3 3));
                wl_Inst (FP (fp_uop_inst fpu));
                wl_Inst (FP (FPMovToReg 3 5 1));
                WriteWord64 c header dest 3],l))
      else
        (match encode_header c 3 2 with
           NONE -> (GiveUp,l)
         | SOME header ->
             (data_to_word_list_Seq [
                wl_Assign 15 (real_addr c (adjust_var v1));
                wl_Assign 11 (wl_Load (wl_Op asm_Add [wl_Var 15; wl_Const bytes_in_word]));
                wl_Assign 13 (wl_Load (wl_Op asm_Add
                                [wl_Var 15; wl_Const (word_mul (word 2) bytes_in_word)]));
                wl_Inst (FP (FPMovFromReg 0 13 11));
                wl_Inst (FP (fp_uop_inst fpu));
                wl_Inst (FP (FPMovToReg 5 3 1));
                WriteWord64_on_32 c header dest 5 3],l))):(A)wl_prog#num`;;

let assign_FinaliseCons_def = cake_def
  `assign_FinaliseCons (l:num) (dest:num) v1 =
     ((wl_Assign (adjust_var dest) (wl_Var (adjust_var v1)),l):(A)wl_prog#num)`;;

(* HOL4: Theorem all_assign_defs = LIST_CONJ (!assign_defs), the list being *)
(* built by consing, so the last definition comes first                     *)

let all_assign_defs = end_itlist CONJ
  [assign_FinaliseCons_def; assign_FP_uop_def; assign_FP_bop_def;
   assign_FP_top_def; assign_FP_cmp_def; assign_Install_def;
   assign_EqualConst_def; assign_FFI_def; assign_WordToInt_def;
   assign_WordFromInt_def; assign_WordFromWord_def; assign_WordShiftW64_def;
   assign_WordShiftW8_def; assign_WordOpW64_def; assign_WordOpW8_def;
   assign_Mod_def; assign_Div_def; assign_Mult_def; assign_Sub_def;
   assign_Add_def; assign_TagEq_def; assign_LenEq_def; assign_TagLenEq_def;
   assign_LengthByte_def; assign_Length_def; assign_LengthBlock_def;
   assign_LessEq_def; assign_Less_def; assign_Equal_def;
   assign_BoundsCheckBlock_def; assign_BoundsCheckArray_def;
   assign_BoundsCheckByte_def; assign_WordTest_def; assign_BoolNot_def;
   assign_BoolTest_def; assign_LessConstSmall_def; assign_FromList_def;
   assign_RefArray_def; assign_CopyByte_def; assign_StringCmp_def;
   assign_XorByte_def; assign_RefByte_def; assign_AllocThunk_def;
   assign_Ref_def; assign_ConsExtend_def; assign_Build_def;
   assign_ConfigGC_def; assign_MutCons_def; assign_Cons_def;
   assign_ListAppend_def; assign_UpdateByte_def; assign_UpdateThunk_def;
   assign_Update_def; assign_DerefByte_def; assign_ElemAt_def; assign_El_def;
   assign_SetGlobal_def; assign_Global_def; assign_SetGlobalsPtr_def;
   assign_Const_def];;

let data_to_word_assign_def = cake_def
  `data_to_word_assign (c:data_to_word_config) (secn:num) (l:num) (dest:num)
                       (op:clos_op) (args:num list) (names:num_set option) =
     match op with
       IntOp (clos_Const i) -> assign_Const i l dest
     | GlobOp GlobalsPtr -> (wl_Assign (adjust_var dest) (Lookup Globals),l)
     | GlobOp SetGlobalsPtr ->
         data_to_word_arg1 args (assign_SetGlobalsPtr c l dest) (wl_Skip,l)
     | GlobOp (SetGlobal n) ->
         data_to_word_arg1 args (assign_SetGlobal c n l dest) (wl_Skip,l)
     | GlobOp (clos_Global n) -> assign_Global c n l dest
     | MemOp clos_El -> data_to_word_arg2 args (assign_El c l dest) (wl_Skip,l)
     | BlockOp (ElemAt n) ->
         data_to_word_arg1 args (assign_ElemAt c n l dest) (wl_Skip,l)
     | MemOp DerefByte -> data_to_word_arg2 args (assign_DerefByte c l dest) (wl_Skip,l)
     | MemOp Update -> arg3 args (assign_Update c l dest) (wl_Skip,l)
     | MemOp UpdateCons -> arg3 args (assign_Update c l dest) (wl_Skip,l)
     | MemOp UpdateByte -> arg3 args (assign_UpdateByte c l dest) (wl_Skip,l)
     | MemOp FinaliseCons ->
         data_to_word_arg1 args (assign_FinaliseCons l dest) (wl_Skip,l)
     | BlockOp clos_ListAppend ->
         data_to_word_arg2 args (assign_ListAppend c secn l dest names) (wl_Skip,l)
     | BlockOp (clos_Cons tag) -> assign_Cons c l dest tag args
     | MemOp (MutCons tag _) -> assign_MutCons c l dest tag args
     | MemOp clos_ConfigGC ->
         data_to_word_arg2 args (assign_ConfigGC c secn l dest names) (wl_Skip,l)
     | BlockOp (Build parts) -> assign_Build c secn l dest names parts
     | BlockOp (ConsExtend tag) -> assign_ConsExtend c secn l dest names tag args
     | MemOp clos_Ref -> assign_Ref c secn l dest names args
     | clos_ThunkOp (AllocThunk ev) ->
         data_to_word_arg1 args (assign_AllocThunk ev c secn l dest names) (wl_Skip,l)
     | clos_ThunkOp (UpdateThunk ev) ->
         data_to_word_arg2 args (assign_UpdateThunk ev c l dest) (wl_Skip,l)
     | MemOp (RefByte imm) ->
         data_to_word_arg2 args (assign_RefByte c secn l dest names imm) (wl_Skip,l)
     | MemOp XorByte ->
         data_to_word_arg2 args (assign_XorByte c secn l dest names) (wl_Skip,l)
     | MemOp (StringCmp b cmp) ->
         data_to_word_arg2 args (assign_StringCmp c secn l dest names b cmp) (wl_Skip,l)
     | clos_Label n -> (wl_LocValue (adjust_var dest) n,l)
     | MemOp (CopyByte alloc_new) -> assign_CopyByte c secn l dest names args
     | MemOp RefArray ->
         data_to_word_arg2 args (assign_RefArray c secn l dest names) (wl_Skip,l)
     | BlockOp (BoolTest test) ->
         data_to_word_arg2 args (assign_BoolTest l dest test) (wl_Skip,l)
     | BlockOp BoolNot -> data_to_word_arg1 args (assign_BoolNot l dest) (wl_Skip,l)
     | WordOp (WordTest ws test) ->
         data_to_word_arg2 args (assign_WordTest l dest test) (wl_Skip,l)
     | BlockOp (FromList tag) ->
         data_to_word_arg2 args (assign_FromList c secn l dest names tag) (wl_Skip,l)
     | IntOp (LessConstSmall i) ->
         data_to_word_arg1 args (assign_LessConstSmall l dest i) (wl_Skip,l)
     | MemOp (BoundsCheckByte leq) ->
         data_to_word_arg2 args (assign_BoundsCheckByte c secn l dest names leq)
           (wl_Skip,l)
     | MemOp BoundsCheckArray ->
         data_to_word_arg2 args (assign_BoundsCheckArray c secn l dest names) (wl_Skip,l)
     | BlockOp BoundsCheckBlock ->
         data_to_word_arg2 args (assign_BoundsCheckBlock c secn l dest names) (wl_Skip,l)
     | BlockOp clos_Equal ->
         data_to_word_arg2 args (assign_Equal c secn l dest names) (wl_Skip,l)
     | IntOp clos_Less ->
         data_to_word_arg2 args (assign_Less c secn l dest names) (wl_Skip,l)
     | IntOp LessEq ->
         data_to_word_arg2 args (assign_LessEq c secn l dest names) (wl_Skip,l)
     | BlockOp LengthBlock ->
         data_to_word_arg1 args (assign_LengthBlock c secn l dest names) (wl_Skip,l)
     | MemOp Length ->
         data_to_word_arg1 args (assign_Length c secn l dest names) (wl_Skip,l)
     | MemOp LengthByte ->
         data_to_word_arg1 args (assign_LengthByte c secn l dest names) (wl_Skip,l)
     | BlockOp (clos_TagLenEq tag len) ->
         data_to_word_arg1 args (assign_TagLenEq c secn l dest names tag len) (wl_Skip,l)
     | BlockOp (clos_LenEq len) ->
         data_to_word_arg1 args (assign_LenEq c secn l dest names len) (wl_Skip,l)
     | BlockOp (TagEq tag) ->
         data_to_word_arg1 args (assign_TagEq c secn l dest names tag) (wl_Skip,l)
     | IntOp clos_Add ->
         data_to_word_arg2 args (assign_Add c secn l dest names) (wl_Skip,l)
     | IntOp clos_Sub ->
         data_to_word_arg2 args (assign_Sub c secn l dest names) (wl_Skip,l)
     | IntOp Mult ->
         data_to_word_arg2 args (assign_Mult c secn l dest names) (wl_Skip,l)
     | IntOp clos_Div ->
         data_to_word_arg2 args (assign_Div c secn l dest names) (wl_Skip,l)
     | IntOp clos_Mod ->
         data_to_word_arg2 args (assign_Mod c secn l dest names) (wl_Skip,l)
     | WordOp (WordOpw W8 opw) ->
         data_to_word_arg2 args (assign_WordOpW8 opw c secn l dest names) (wl_Skip,l)
     | WordOp (WordOpw W64 opw) ->
         data_to_word_arg2 args (assign_WordOpW64 opw c secn l dest names) (wl_Skip,l)
     | WordOp (WordShift W8 sh n) ->
         data_to_word_arg1 args (assign_WordShiftW8 sh n c secn l dest names) (wl_Skip,l)
     | WordOp (WordShift W64 sh n) ->
         data_to_word_arg1 args (assign_WordShiftW64 sh n c secn l dest names) (wl_Skip,l)
     | WordOp (WordFromWord b) ->
         data_to_word_arg1 args (assign_WordFromWord b c secn l dest names) (wl_Skip,l)
     | WordOp WordFromInt ->
         data_to_word_arg1 args (assign_WordFromInt c secn l dest names) (wl_Skip,l)
     | WordOp WordToInt ->
         data_to_word_arg1 args (assign_WordToInt c secn l dest names) (wl_Skip,l)
     | clos_FFI ffi_index ->
         data_to_word_arg2 args (assign_FFI ffi_index c secn l dest names) (wl_Skip,l)
     | BlockOp (EqualConst p) ->
         data_to_word_arg1 args (assign_EqualConst p c secn l dest names) (wl_Skip,l)
     | clos_Install -> arg4 args (assign_Install c secn l dest names) (wl_Skip,l)
     | WordOp (FP_cmp fpc) ->
         data_to_word_arg2 args (assign_FP_cmp fpc c secn l dest names) (wl_Skip,l)
     | WordOp (FP_top fpt) -> arg3 args (assign_FP_top fpt c secn l dest names) (wl_Skip,l)
     | WordOp (FP_bop fpb) ->
         data_to_word_arg2 args (assign_FP_bop fpb c secn l dest names) (wl_Skip,l)
     | WordOp (FP_uop fpu) ->
         data_to_word_arg1 args (assign_FP_uop fpu c secn l dest names) (wl_Skip,l)
     | _ -> ((wl_Skip,l):(A)wl_prog#num)`;;

let force_thunk_def = cake_def
  `force_thunk (c:data_to_word_config) secn (l:num) (ret:(num#B spt)option) loc v1 =
     (match encode_header c (8 + 6) 1 with
        NONE -> (GiveUp,l)
      | SOME (header:A word) ->
          (wl_If asm_Test (adjust_var v1) (Imm (word 1))
             (match ret with
                NONE -> wl_Return 0 [adjust_var v1]
              | SOME (dest,_) -> wl_Assign (adjust_var dest) (wl_Var (adjust_var v1)))
             (data_to_word_list_Seq
                [wl_Assign 1 (real_addr c (adjust_var v1));
                 wl_Assign 3 (wl_Op asm_And [wl_Load (wl_Var 1); wl_Const (word 60)]);
                 wl_If asm_Equal 3 (Imm (word ((8 + 6) * 4)))
                   (match ret with
                      NONE ->
                        data_to_word_list_Seq
                          [wl_Assign 1 (wl_Load (wl_Op asm_Add [wl_Var 1;
                                                                wl_Const bytes_in_word]));
                           wl_Return 0 [1]]
                    | SOME (dest,_) ->
                        wl_Assign (adjust_var dest)
                          (wl_Load (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word])))
                   (wl_If NotEqual 3 (Imm (word ((0 + 6) * 4)))
                      (match ret with
                         NONE -> wl_Return 0 [adjust_var v1]
                       | SOME (dest,_) ->
                           wl_Assign (adjust_var dest) (wl_Var (adjust_var v1)))
                      (data_to_word_list_Seq
                         [wl_Assign 5 (wl_Load (wl_Op asm_Add [wl_Var 1;
                                                               wl_Const bytes_in_word]));
                          (match ret with
                             NONE -> wl_Call NONE (SOME loc) [0; adjust_var v1; 5] NONE
                           | SOME (r,ns) ->
                               wl_Call (SOME ([adjust_var r],adjust_sets ns,wl_Skip,secn,l))
                                 (SOME loc) [adjust_var v1; 5] NONE)]))]),l + 1))
       :(A)wl_prog#num`;;

let data_to_word_comp_def = cake_def
  `data_to_word_comp (c:data_to_word_config) (secn:num) (l:num) (p:data_prog) =
     match p with
       data_Skip -> (wl_Skip:(A)wl_prog,l)
     | data_Tick -> (wl_Tick,l)
     | data_Raise n -> (wl_Raise (adjust_var n),l)
     | data_Return ns -> (wl_Return 0 (MAP adjust_var ns),l)
     | data_Move n1 n2 -> (wl_Move 0 [(adjust_var n1,adjust_var n2)],l)
     | data_Seq p1 p2 ->
         let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
         (wl_Seq q1 q2,l2)
     | data_If n p1 p2 ->
         let (q1,l1) = data_to_word_comp c secn l p1 in
         let (q2,l2) = data_to_word_comp c secn l1 p2 in
         (wl_If asm_Equal (adjust_var n) (Imm (word 18)) q1 q2,l2)
     | MakeSpace n names ->
         let k = dimindex(:A) DIV 8 in
         let w = word (n * k) in
         let w = if val w = n * k then w else word_not (word 0) in
         (wl_Seq (wl_Assign 1 (wl_Op asm_Sub [Lookup TriggerGC; Lookup NextFree]))
                 (wl_If Lower 1 (Imm w)
                    (data_to_word_list_Seq
                       [SilentFFI c 3 (adjust_sets names);
                        wl_Assign 1 (wl_Const w);
                        wl_Alloc 1 (adjust_sets names);
                        SilentFFI c 3 (adjust_sets names)])
                    wl_Skip),l)
     | data_Assign dest op args names -> data_to_word_assign c secn l dest op args names
     | data_Force ret loc v -> force_thunk c secn l ret loc v
     | data_Call ret target args handler ->
         match ret with
           NONE -> (wl_Call NONE target (CONS 0 (MAP adjust_var args)) NONE,l)
         | SOME (ns,names) ->
             let ret = SOME (MAP adjust_var ns, adjust_sets names, wl_Skip, secn, l) in
             match handler with
               NONE -> (wl_Call ret target (MAP adjust_var args) NONE, l + 1)
             | SOME (n,p) ->
                 let (q1,l1) = data_to_word_comp c secn (l + 2) p in
                 let handler = SOME (adjust_var n, q1, secn, l + 1) in
                 (wl_Call ret target (MAP adjust_var args) handler, l1)`;;

let data_to_word_comp_ind = cake_ind "data_to_word_comp";;

let data_to_word_compile_part_def = cake_def
  `data_to_word_compile_part (c:data_to_word_config) (n,arg_count,p) =
     (n,arg_count + 1,(FST (data_to_word_comp c n 2 p):(A)wl_prog))`;;

let MemCopy_code_def = cake_def
  `MemCopy_code =
     wl_If asm_Test 2 (Reg 2) (wl_Return 0 [8])
       (data_to_word_list_Seq
          [wl_Assign 1 (wl_Load (wl_Var 4));
           wl_Assign 2 (wl_Op asm_Sub [wl_Var 2; wl_Const (word 4)]);
           wl_Assign 4 (wl_Op asm_Add [wl_Var 4; wl_Const bytes_in_word]);
           wl_Store (wl_Var 6) 1;
           wl_Assign 6 (wl_Op asm_Add [wl_Var 6; wl_Const bytes_in_word]);
           wl_Call NONE (SOME MemCopy_location) [0;2;4;6;8] NONE]):(A)wl_prog`;;

let ByteCopy_code_def = cake_def
  `ByteCopy_code (c:data_to_word_config) = data_to_word_list_Seq
     [wl_Assign 4 (ShiftVar Lsr 4 2);
      wl_Assign 6 (ShiftVar Lsr 6 2);
      wl_Assign 10 (ShiftVar Lsr 10 2);
      wl_Assign 1 data_to_word_Unit;
      wl_Assign 2 (wl_Op asm_Add [real_addr c 2; wl_Const bytes_in_word; wl_Var 4]);
      wl_Assign 8 (wl_Op asm_Add [real_addr c 8; wl_Const bytes_in_word; wl_Var 10]);
      wl_If Lower 4 (Reg 10)
        (data_to_word_list_Seq
           [wl_Assign 3 (wl_Op asm_Sub [wl_Var 6; wl_Const (word 1)]);
            wl_Assign 2 (wl_Op asm_Add [wl_Var 2; wl_Var 3]);
            wl_Assign 8 (wl_Op asm_Add [wl_Var 8; wl_Var 3]);
            wl_Call NONE (SOME ByteCopySub_location) [0;6;2;8;1] NONE])
        (wl_Call NONE (SOME ByteCopyAdd_location) [0;6;2;8;1] NONE)]:(A)wl_prog`;;

(* the tests: n <+ 4w; n <+ 2w; n = 0w *)

let ByteCopyAdd_code_def = cake_def
  `ByteCopyAdd_code =
     wl_If Lower 2 (Imm (word 4))
       (wl_If Lower 2 (Imm (word 2))
          (wl_If asm_Equal 2 (Imm (word 0)) (wl_Return 0 [8])
             (data_to_word_list_Seq
                [wl_Inst (Mem Load8 1 (Addr 4 (word 0)));
                 wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
                 wl_Return 0 [8]]))
          (data_to_word_list_Seq
             [wl_Inst (Mem Load8 1 (Addr 4 (word 0)));
              wl_Inst (Mem Load8 3 (Addr 4 (word 1)));
              wl_If asm_Equal 2 (Imm (word 2))
                (data_to_word_list_Seq
                   [wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
                    wl_Inst (Mem Store8 3 (Addr 6 (word 1)));
                    wl_Return 0 [8]])
                (data_to_word_list_Seq
                   [wl_Inst (Mem Load8 5 (Addr 4 (word 2)));
                    wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
                    wl_Inst (Mem Store8 3 (Addr 6 (word 1)));
                    wl_Inst (Mem Store8 5 (Addr 6 (word 2)));
                    wl_Return 0 [8]])]))
       (data_to_word_list_Seq
          [wl_Inst (Mem Load8 1 (Addr 4 (word 0)));
           wl_Inst (Mem Load8 3 (Addr 4 (word 1)));
           wl_Inst (Mem Load8 5 (Addr 4 (word 2)));
           wl_Inst (Mem Load8 7 (Addr 4 (word 3)));
           wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
           wl_Inst (Mem Store8 3 (Addr 6 (word 1)));
           wl_Inst (Mem Store8 5 (Addr 6 (word 2)));
           wl_Inst (Mem Store8 7 (Addr 6 (word 3)));
           wl_Assign 9 (wl_Op asm_Sub [wl_Var 2; wl_Const (word 4)]);
           wl_Assign 11 (wl_Op asm_Add [wl_Var 4; wl_Const (word 4)]);
           wl_Assign 13 (wl_Op asm_Add [wl_Var 6; wl_Const (word 4)]);
           wl_Call NONE (SOME ByteCopyAdd_location) [0;9;11;13;8] NONE]):(A)wl_prog`;;

let ByteCopySub_code_def = cake_def
  `ByteCopySub_code =
     wl_If Lower 2 (Imm (word 4))
       (wl_If Lower 2 (Imm (word 2))
          (wl_If asm_Equal 2 (Imm (word 0)) (wl_Return 0 [8])
             (data_to_word_list_Seq
                [wl_Inst (Mem Load8 1 (Addr 4 (word 0)));
                 wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
                 wl_Return 0 [8]]))
          (data_to_word_list_Seq
             [wl_Inst (Mem Load8 1 (Addr 4 (word 0)));
              wl_Inst (Mem Load8 3 (Addr 4 (word_neg (word 1))));
              wl_If asm_Equal 2 (Imm (word 2))
                (data_to_word_list_Seq
                   [wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
                    wl_Inst (Mem Store8 3 (Addr 6 (word_neg (word 1))));
                    wl_Return 0 [8]])
                (data_to_word_list_Seq
                   [wl_Inst (Mem Load8 5 (Addr 4 (word_neg (word 2))));
                    wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
                    wl_Inst (Mem Store8 3 (Addr 6 (word_neg (word 1))));
                    wl_Inst (Mem Store8 5 (Addr 6 (word_neg (word 2))));
                    wl_Return 0 [8]])]))
       (data_to_word_list_Seq
          [wl_Inst (Mem Load8 1 (Addr 4 (word 0)));
           wl_Inst (Mem Load8 3 (Addr 4 (word_neg (word 1))));
           wl_Inst (Mem Load8 5 (Addr 4 (word_neg (word 2))));
           wl_Inst (Mem Load8 7 (Addr 4 (word_neg (word 3))));
           wl_Inst (Mem Store8 1 (Addr 6 (word 0)));
           wl_Inst (Mem Store8 3 (Addr 6 (word_neg (word 1))));
           wl_Inst (Mem Store8 5 (Addr 6 (word_neg (word 2))));
           wl_Inst (Mem Store8 7 (Addr 6 (word_neg (word 3))));
           wl_Assign 9 (wl_Op asm_Sub [wl_Var 2; wl_Const (word 4)]);
           wl_Assign 11 (wl_Op asm_Sub [wl_Var 4; wl_Const (word 4)]);
           wl_Assign 13 (wl_Op asm_Sub [wl_Var 6; wl_Const (word 4)]);
           wl_Call NONE (SOME ByteCopySub_location) [0;9;11;13;8] NONE]):(A)wl_prog`;;

let ByteCopyNew_code_def = cake_def
  `ByteCopyNew_code (c:data_to_word_config) = wl_Skip:(A)wl_prog`;;

(* HOL4 stubs (:'a) data_conf: as conf_ok *)

let data_to_word_stubs_DEF = new_definition
  `data_to_word_stubs (s:A->bool) (data_conf:data_to_word_config) =
     APPEND
       [(FromList_location,4,(FromList_code data_conf:(A)wl_prog));
        (FromList1_location,6,FromList1_code data_conf);
        (RefByte_location,4,RefByte_code data_conf);
        (RefArray_location,3,RefArray_code data_conf);
        (Replicate_location,5,Replicate_code);
        (AnyArith_location,4,AnyArith_code data_conf);
        (Add_location,3,Add_code);
        (Sub_location,3,Sub_code);
        (Mul_location,3,Mul_code);
        (Div_location,3,Div_code);
        (Mod_location,3,Mod_code);
        (Compare1_location,4,Compare1_code);
        (Compare_location,3,Compare_code data_conf);
        (Equal1_location,4,Equal1_code);
        (Equal_location,3,Equal_code data_conf);
        (LongDiv1_location,7,LongDiv1_code data_conf);
        (LongDiv_location,4,LongDiv_code data_conf);
        (Install_location,3,Install_code data_conf);
        (InstallCode_location,4,InstallCode_code data_conf);
        (InstallData_location,4,InstallData_code data_conf);
        (Append_location,3,Append_code data_conf);
        (AppendMainLoop_location,6,AppendMainLoop_code data_conf);
        (AppendLenLoop_location,3,AppendLenLoop_code data_conf);
        (XorLoop_location,4,XorLoop_code);
        (Unused_location,6,wl_Skip);
        (StringCmpLoop_location,6,StringCmpLoop_code);
        (MemCopy_location,5,MemCopy_code);
        (ByteCopy_location,6,ByteCopy_code data_conf);
        (ByteCopyAdd_location,5,ByteCopyAdd_code);
        (ByteCopySub_location,5,ByteCopySub_code);
        (ByteCopyNew_location,4,ByteCopyNew_code data_conf);
        (Dummy_location,0,wl_Skip)]
       (generated_bignum_stubs Bignum_location)`;;

let data_to_word_stubs_def = prove
 (`!data_conf. data_to_word_stubs (:A) data_conf =
     APPEND
       [(FromList_location,4,(FromList_code data_conf:(A)wl_prog));
        (FromList1_location,6,FromList1_code data_conf);
        (RefByte_location,4,RefByte_code data_conf);
        (RefArray_location,3,RefArray_code data_conf);
        (Replicate_location,5,Replicate_code);
        (AnyArith_location,4,AnyArith_code data_conf);
        (Add_location,3,Add_code);
        (Sub_location,3,Sub_code);
        (Mul_location,3,Mul_code);
        (Div_location,3,Div_code);
        (Mod_location,3,Mod_code);
        (Compare1_location,4,Compare1_code);
        (Compare_location,3,Compare_code data_conf);
        (Equal1_location,4,Equal1_code);
        (Equal_location,3,Equal_code data_conf);
        (LongDiv1_location,7,LongDiv1_code data_conf);
        (LongDiv_location,4,LongDiv_code data_conf);
        (Install_location,3,Install_code data_conf);
        (InstallCode_location,4,InstallCode_code data_conf);
        (InstallData_location,4,InstallData_code data_conf);
        (Append_location,3,Append_code data_conf);
        (AppendMainLoop_location,6,AppendMainLoop_code data_conf);
        (AppendLenLoop_location,3,AppendLenLoop_code data_conf);
        (XorLoop_location,4,XorLoop_code);
        (Unused_location,6,wl_Skip);
        (StringCmpLoop_location,6,StringCmpLoop_code);
        (MemCopy_location,5,MemCopy_code);
        (ByteCopy_location,6,ByteCopy_code data_conf);
        (ByteCopyAdd_location,5,ByteCopyAdd_code);
        (ByteCopySub_location,5,ByteCopySub_code);
        (ByteCopyNew_location,4,ByteCopyNew_code data_conf);
        (Dummy_location,0,wl_Skip)]
       (generated_bignum_stubs Bignum_location)`,
  REWRITE_TAC[data_to_word_stubs_DEF]);;

(* Unused_location: TODO in HOL4 (use next time new stub is needed) *)

let data_to_word_stub_names_def = cake_def
  `data_to_word_stub_names one =
     APPEND
       [(FromList_location,implode "_FromList");
        (FromList1_location,implode "_FromList1");
        (RefByte_location,implode "_RefByte");
        (RefArray_location,implode "_RefArray");
        (Replicate_location,implode "_Replicate");
        (AnyArith_location,implode "_AnyArith");
        (Add_location,implode "_Add");
        (Sub_location,implode "_Sub");
        (Mul_location,implode "_Mul");
        (Div_location,implode "_Div");
        (Mod_location,implode "_Mod");
        (Compare1_location,implode "_Compare1");
        (Compare_location,implode "_Compare");
        (Equal1_location,implode "_Equal1");
        (Equal_location,implode "_Equal");
        (LongDiv1_location,implode "_LongDiv1");
        (LongDiv_location,implode "_LongDiv");
        (Install_location,implode "_Install");
        (InstallCode_location,implode "_InstallCode");
        (InstallData_location,implode "_InstallData");
        (Append_location,implode "_Append");
        (AppendMainLoop_location,implode "_AppendMainLoop");
        (AppendLenLoop_location,implode "_AppendLenLoop");
        (XorLoop_location,implode "_XorLoop");
        (Unused_location,implode "_Unused");
        (StringCmpLoop_location,implode "_StringCmpLoop");
        (MemCopy_location,implode "_MemCopy");
        (ByteCopy_location,implode "_ByteCopy");
        (ByteCopyAdd_location,implode "_ByteCopyAdd");
        (ByteCopySub_location,implode "_ByteCopySub");
        (ByteCopyNew_location,implode "_ByteCopyNew");
        (Dummy_location,implode "_Dummy")]
       (list_of_seq (\i. (i + Bignum_location,implode "_Bignum"))
          (data_num_stubs - Bignum_location))`;;

let check_stubs_length = prove
 (`!c. word_num_stubs + LENGTH (data_to_word_stubs (:A) c) = data_num_stubs`,
  REWRITE_TAC[data_to_word_stubs_def; LENGTH_APPEND; LENGTH;
              generated_bignum_stubs_eq; LENGTH_MAP] THEN
  REWRITE_TAC[word_num_stubs_def; data_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let check_LongDiv_location = prove
 (`LongDiv_location = div_location`,
  REWRITE_TAC[LongDiv_location_eq; div_location_def]);;

let data_to_word_compile_def = cake_def
  `data_to_word_compile (data_conf:data_to_word_config) word_conf
                        (asm_conf:(A)asm_config) prog =
     let data_conf =
       data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_tern_fupd
            (K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
            data_conf) in
     let p = APPEND (data_to_word_stubs (:A) data_conf)
                    (MAP (data_to_word_compile_part data_conf) prog) in
     word_to_word_compile word_conf asm_conf p`;;

let compile_0_def = cake_def
  `compile_0 (data_conf:data_to_word_config) (asm_conf:(A)asm_config) prog =
     let data_conf =
       data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_tern_fupd
            (K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
            data_conf) in
     APPEND (data_to_word_stubs (:A) data_conf)
            (MAP (data_to_word_compile_part data_conf) prog)`;;

(* compute bignum call graph: HOL4 th_FF, th_FT, th_TF, th_TT are EVAL of  *)
(*   full_call_graph AnyArith_location                                     *)
(*     (fromAList (stubs (:'a) (data_conf with <| call_empty_ffi := b1;    *)
(*                                              has_longdiv := b2 |>)))     *)
(* for the four values of b1 and b2.  Here the evaluation is HOL Light's    *)
(* call-by-value Compute (HOL4's computeLib) with the definitions that the *)
(* call graph of the stubs reachable from AnyArith_location needs (the     *)
(* code of the other stubs stays unevaluated), numeral arithmetic, the      *)
(* record accessors of the updated configuration, and an equality test for *)
(* the ground terms of the datatypes (distinctness and injectivity, as     *)
(* HOL4's EVAL).                                                            *)

let D2WAUX_call_graph_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`,2,WORDP3AUX_EQ_CONV) cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  Compute.add_thms
    ([full_call_graph_def; call_graph_def; mk_Branch_def;
      data_to_word_stubs_def; generated_bignum_stubs_eq;
      fromAList_def; insert_def; lookup_def; delete_def; mk_BN_def; mk_BS_def;
      sptree_size_def; APPEND; MAP; MEM; LENGTH; K_THM; LET_END_DEF;
      case_def "option"; case_def "prod";
      (record_info "data_to_word_config").ri_accfupds;
      AnyArith_code_def; data_to_word_Replicate_code_def; LongDiv_code_def;
      LongDiv1_code_def; data_to_word_list_Seq_def; AddNumSize_def;
      AnyHeader_def; AllocVar_def; SilentFFI_def] @ D2WAUX_location_defs) cs;
  cs;;

let D2WAUX_call_graph_th b1 b2 =
  Compute.WEAK_CBV_CONV D2WAUX_call_graph_cs
   (vsubst [b1,`b1:bool`; b2,`b2:bool`]
     `full_call_graph AnyArith_location
        (fromAList (data_to_word_stubs (:A)
           (data_to_word_config_call_empty_ffi_fupd (K b1)
              (data_to_word_config_has_longdiv_fupd (K b2) data_conf))))`);;

let D2WAUX_th_FF = D2WAUX_call_graph_th `F` `F`;;
let D2WAUX_th_FT = D2WAUX_call_graph_th `F` `T`;;
let D2WAUX_th_TF = D2WAUX_call_graph_th `T` `F`;;
let D2WAUX_th_TT = D2WAUX_call_graph_th `T` `T`;;

let AnyArith_call_tree_def = new_definition
  (mk_eq(`AnyArith_call_tree:call_tree`, rand(concl D2WAUX_th_FF)));;


let structure_le_def = sem1aux_def
  `(structure_le word_depth_Leaf _ <=> T) /\
   (structure_le _ Unknown <=> T) /\
   (structure_le (word_depth_Const k1 t1) (word_depth_Const k2 t2) <=>
      k1 <= k2 /\ structure_le t1 t2) /\
   (structure_le (word_depth_Call n1 t2) (word_depth_Call m1 u2) <=>
      n1 = m1 /\ structure_le t2 u2) /\
   (structure_le (word_depth_Branch t1 t2) (word_depth_Branch u1 u2) <=>
      structure_le t1 u1 /\ structure_le t2 u2) /\
   (structure_le _ _ <=> F)`;;

let D2WAUX_structure_le_cs =
  let cs = Compute.bool_compset () in
  num_compute_add_convs cs;
  Compute.add_thms [structure_le_def; AnyArith_call_tree_def] cs;
  cs;;

(* HOL4 proves each case by rewriting data_conf to data_conf with          *)
(* <| call_empty_ffi := b1; has_longdiv := b2 |> (component equality) and *)
(* then with th_b1b2, AnyArith_call_tree_def and structure_le_def          *)

let D2WAUX_ANYARITH_CASE_TAC (b1,b2,th) : tactic =
  SUBGOAL_THEN
    (vsubst [b1,`b1:bool`; b2,`b2:bool`]
      `data_conf = data_to_word_config_call_empty_ffi_fupd (K b1)
                     (data_to_word_config_has_longdiv_fupd (K b2)
                        (data_conf:data_to_word_config))`)
    (fun eq -> ONCE_REWRITE_TAC[eq]) THENL
   [REWRITE_TAC[data_to_word_config_component_equality;
                (record_info "data_to_word_config").ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[th] THEN CONV_TAC(Compute.WEAK_CBV_CONV D2WAUX_structure_le_cs)];;

let AnyArith_call_tree_thm = prove
 (`!data_conf:data_to_word_config.
     structure_le
       (full_call_graph AnyArith_location
          (fromAList (data_to_word_stubs (:A) data_conf)))
       AnyArith_call_tree`,
  GEN_TAC THEN
  ASM_CASES_TAC `data_to_word_config_call_empty_ffi data_conf` THEN
  ASM_CASES_TAC `data_to_word_config_has_longdiv data_conf` THENL
   [D2WAUX_ANYARITH_CASE_TAC (`T`,`T`,D2WAUX_th_TT);
    D2WAUX_ANYARITH_CASE_TAC (`T`,`F`,D2WAUX_th_TF);
    D2WAUX_ANYARITH_CASE_TAC (`F`,`T`,D2WAUX_th_FT);
    D2WAUX_ANYARITH_CASE_TAC (`F`,`F`,D2WAUX_th_FF)]);;
