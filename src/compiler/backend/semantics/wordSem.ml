(* ========================================================================= *)
(* wordSem: port of HOL4 compiler/backend/semantics/wordSemScript.sml        *)
(* (CakeML v3479).                                                           *)
(* The formal semantics of wordLang.                                         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names: the prefix wl_ for the names that clash with other ILs           *)
(*   (wl_state, wl_result, wl_evaluate, wl_get_var, ...); the result         *)
(*   constructors Break and Continue are wordSem_Break and wordSem_Continue  *)
(*   (wl_Break and wl_Continue are the wordLang statements), as             *)
(*   doc/names.tsv says.                                                     *)
(* - The record state is wl_state with the fields wl_state_locals, ...;     *)
(*   HOL4 s.f is wl_state_f s and s with f := v is wl_state_f_fupd (K v) s;  *)
(*   s with <| f1 := x; f2 := y |> is wl_state_f1_fupd (K x)                 *)
(*   (wl_state_f2_fupd (K y) s).  Its type variables are A, C and FFI        *)
(*   (HOL4 'a, 'c and 'ffi); the type variable of result is W (HOL4 'w).    *)
(* - HOL4 Type gc_fun_type (a type abbreviation with a parameter) is        *)
(*   written out in the field gc_fun.                                        *)
(* - Words: n2w = word, w2n = val, w2w = word_zx, w2i = ival, i2w = iword,   *)
(*   && = word_and, signed < and <= = word_ilt and word_ile, <+ = word_ult,  *)
(*   / = word_jdiv, (h >< l) = word_extract h l, @@ = word_join,             *)
(*   bit_field_insert h l a w = word_insert w (l,(h + 1) - l) a; word32 =    *)
(*   int32, word64 = int64, word8 = byte; aligned = alignment_aligned.       *)
(* - HOL4 FOLDR f e l = ITLIST f l e, GENLIST = list_of_seq, FRONT = BUTLAST,*)
(*   ZIP (a,b) = ZIP a b, UNIV = (:num).                                     *)
(* - Many-clause definitions use sem1aux_def (HOL4's TFL completion).       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/wordLang.ml";;
needs "hol4/finite_map.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/ffi/ffi.ml";;
needs "hol4/lprefix_lub.ml";;
needs "hol4/machine_ieee.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

prioritize_num();;
type_invention_error := true;;

let buffer_INFO = cake_record "buffer"
  ["position","A word";
   "buffer","(B word) list";
   "space_left","num"];;

let buffer_flush_def = cake_def
  `buffer_flush (cb:(A,B)buffer) (w1:A word) w2 =
     if buffer_position cb = w1 /\
        word_add (buffer_position cb)
          (word_mul (word (dimindex(:B) DIV 8))
                    (word (LENGTH (buffer_buffer cb)))) = w2
     then SOME (buffer_buffer cb,
                buffer_position_fupd (combin_K w2) (buffer_buffer_fupd (combin_K []) cb))
     else NONE`;;

let buffer_write_def = cake_def
  `buffer_write (cb:(A,B)buffer) (w:A word) (b:B word) =
     if word_add (buffer_position cb)
          (word_mul (word (dimindex(:B) DIV 8))
                    (word (LENGTH (buffer_buffer cb)))) = w /\
        0 < buffer_space_left cb
     then SOME (buffer_buffer_fupd (combin_K (APPEND (buffer_buffer cb) [b]))
                  (buffer_space_left_fupd (combin_K (buffer_space_left cb - 1)) cb))
     else NONE`;;

let is_fwd_ptr_def = cake_def
  `(is_fwd_ptr (wl_Word (w:A word)) <=> word_and w (word 3) = word 0) /\
   (is_fwd_ptr (_:(A)word_loc) <=> F)`;;

let theWord_def = cake_def
  `theWord (wl_Word (w:A word)) = w`;;

let isWord_def = cake_def
  `(isWord (wl_Word (w:A word)) <=> T) /\
   (isWord (_:(A)word_loc) <=> F)`;;

let isWord_exists = prove
 (`isWord (x:(A)word_loc) <=> ?w. x = wl_Word w`,
  CASES_ON `x:(A)word_loc` THEN
  REWRITE_TAC[isWord_def; injectivity "word_loc"; distinctness "word_loc"] THEN
  MESON_TAC[]);;

let wl_word_cmp_def = sem1aux_def
  `(wl_word_cmp asm_Equal (wl_Word (w1:A word)) (wl_Word w2) = SOME (w1 = w2)) /\
   (wl_word_cmp asm_Less (wl_Word w1) (wl_Word w2) = SOME (word_ilt w1 w2)) /\
   (wl_word_cmp Lower (wl_Word w1) (wl_Word w2) = SOME (word_ult w1 w2)) /\
   (wl_word_cmp asm_Test (wl_Word w1) (wl_Word w2) =
      SOME (word_and w1 w2 = word 0)) /\
   (wl_word_cmp asm_Test (wl_Loc _ n) (wl_Word w2) =
      if ~(n = 0) then NONE else if w2 = word 1 then SOME T else NONE) /\
   (wl_word_cmp NotEqual (wl_Word w1) (wl_Word w2) = SOME (~(w1 = w2))) /\
   (wl_word_cmp NotLess (wl_Word w1) (wl_Word w2) = SOME (~(word_ilt w1 w2))) /\
   (wl_word_cmp NotLower (wl_Word w1) (wl_Word w2) =
      SOME (~(word_ult w1 w2))) /\
   (wl_word_cmp NotTest (wl_Word w1) (wl_Word w2) =
      SOME (~(word_and w1 w2 = word 0))) /\
   (wl_word_cmp NotTest (wl_Loc _ n) (wl_Word w2) =
      if ~(n = 0) then NONE else if w2 = word 1 then SOME F else NONE) /\
   (wl_word_cmp _ _ _ = NONE)`;;

let mem_load_32_def = cake_def
  `mem_load_32 (m:A word->(A)word_loc) dm be (w:A word) =
     if alignment_aligned 2 w
     then match m (byte_align w) with
            wl_Loc _ _ -> NONE
          | wl_Word v ->
              if byte_align w IN dm
              then SOME (word_of_bytes be (word 0:int32)
                           [get_byte w v be; get_byte (word_add w (word 1)) v be;
                            get_byte (word_add w (word 2)) v be;
                            get_byte (word_add w (word 3)) v be])
              else NONE
     else NONE`;;

let mem_store_32_def = cake_def
  `mem_store_32 (m:A word->(A)word_loc) dm be (w:A word) (hw:int32) =
     if alignment_aligned 2 w
     then match m (byte_align w) with
            wl_Word v ->
              if byte_align w IN dm
              then
                let v0 = set_byte w (get_byte (word 0:int32) hw be) v be in
                let v1 = set_byte (word_add w (word 1)) (get_byte (word 1) hw be)
                           v0 be in
                let v2 = set_byte (word_add w (word 2)) (get_byte (word 2) hw be)
                           v1 be in
                let v3 = set_byte (word_add w (word 3)) (get_byte (word 3) hw be)
                           v2 be in
                  SOME ((byte_align w =+ wl_Word v3) m)
              else NONE
          | _ -> NONE
     else NONE`;;

(* the bytes of a 32-bit word (for mem_load_32_alt) *)

let mem_load_32_alt = prove
 (CASE_TERM `mem_load_32 (m:A word->(A)word_loc) dm be (w:A word) =
   if alignment_aligned 2 w
   then match m (byte_align w) with
          wl_Loc _ _ -> NONE
        | wl_Word v ->
            if byte_align w IN dm
            then
              let b0 = get_byte w v be in
              let b1 = get_byte (word_add w (word 1)) v be in
              let b2 = get_byte (word_add w (word 2)) v be in
              let b3 = get_byte (word_add w (word 3)) v be in
              let v' =
                  (if be
                   then word_or (word_or (word_or (word_shl (word_zx b0) 24)
                                                  (word_shl (word_zx b1) 16))
                                         (word_shl (word_zx b2) 8))
                                (word_zx b3)
                   else word_or (word_or (word_or (word_zx b0)
                                                  (word_shl (word_zx b1) 8))
                                         (word_shl (word_zx b2) 16))
                                (word_shl (word_zx b3) 24)) in
              SOME (v':int32)
            else NONE
   else NONE`,
  REWRITE_TAC[mem_load_32_def; WORDSAUX_word_of_bytes_32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

(* the bytes of a 32-bit word (for mem_store_32_alt) *)

let mem_store_32_alt = prove
 (CASE_TERM `mem_store_32 (m:A word->(A)word_loc) dm be (w:A word) (hw:int32) =
   if alignment_aligned 2 w
   then match m (byte_align w) with
          wl_Word v ->
            if byte_align w IN dm
            then
              if be
              then
                let v0 = set_byte w (word_zx (word_ushr hw 24)) v be in
                let v1 = set_byte (word_add w (word 1)) (word_zx (word_ushr hw 16))
                           v0 be in
                let v2 = set_byte (word_add w (word 2)) (word_zx (word_ushr hw 8))
                           v1 be in
                let v3 = set_byte (word_add w (word 3)) (word_zx hw) v2 be in
                  SOME ((byte_align w =+ wl_Word v3) m)
              else
                let v0 = set_byte w (word_zx hw) v be in
                let v1 = set_byte (word_add w (word 1)) (word_zx (word_ushr hw 8))
                           v0 be in
                let v2 = set_byte (word_add w (word 2)) (word_zx (word_ushr hw 16))
                           v1 be in
                let v3 = set_byte (word_add w (word 3)) (word_zx (word_ushr hw 24))
                           v2 be in
                  SOME ((byte_align w =+ wl_Word v3) m)
            else NONE
        | _ -> NONE
   else NONE`,
  REWRITE_TAC[mem_store_32_def; WORDSAUX_get_byte_32] THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[]);;

let mem_load_byte_aux_def = cake_def
  `mem_load_byte_aux (m:A word->(A)word_loc) dm be (w:A word) =
     match m (byte_align w) with
       wl_Loc _ _ -> NONE
     | wl_Word v ->
         if byte_align w IN dm then SOME (get_byte w v be) else NONE`;;

let mem_store_byte_aux_def = cake_def
  `mem_store_byte_aux (m:A word->(A)word_loc) dm be (w:A word) (b:byte) =
     match m (byte_align w) with
       wl_Word v ->
         if byte_align w IN dm
         then SOME ((byte_align w =+ wl_Word (set_byte w b v be)) m)
         else NONE
     | _ -> NONE`;;

let write_bytearray_def = cake_def
  `(write_bytearray (a:A word) [] (m:A word->(A)word_loc) dm be = m) /\
   (write_bytearray a (CONS (b:byte) bs) m dm be =
      match mem_store_byte_aux (write_bytearray (word_add a (word 1)) bs m dm be)
              dm be a b with
        SOME m -> m
      | NONE -> m)`;;

(* StackFrame: the size of the locals, the non-GCed cutset, the GCed cutset *)
(* and the handler                                                           *)

let stack_frame_INDUCT,stack_frame_RECURSION = cake_type
  "stack_frame = StackFrame (num option) ((num#(A)word_loc) list)
                            ((num#(A)word_loc) list) ((num#num#num) option)";;

(* HOL4: Type gc_fun_type =                                                  *)
(*   ``: ('a word_loc list) # (('a word) -> ('a word_loc)) # ('a word) set # *)
(*       (store_name |-> 'a word_loc) ->                                     *)
(*       (('a word_loc list) # (('a word) -> ('a word_loc)) #                *)
(*       (store_name |-> 'a word_loc)) option``                              *)
(* (written out in the field gc_fun of wl_state)                            *)

let gc_bij_ok_def = cake_def
  `gc_bij_ok (seq':num->num->num) <=> !n. BIJ (seq' n) (:num) (:num)`;;

(* locals_size: size of locals when pushed to stack, NONE if unbounded;     *)
(* fp_regs: FP regs are treated globally; stack_limit: max stack size;      *)
(* stack_max: largest stack seen so far, NONE if unbounded; stack_size:     *)
(* stack frame size of function, unbounded if unmapped; permute: sequence   *)
(* of bijective mappings; handler: position of current handle frame on      *)
(* stack; termdep: count of how many MustTerminates we can still enter;     *)
(* be: is big-endian                                                         *)

let wl_state_INFO = cake_record "wl_state"
  ["locals","((A)word_loc)spt";
   "locals_size","num option";
   "fp_regs","(num,int64)fmap";
   "store","(store_name,(A)word_loc)fmap";
   "stack","((A)stack_frame)list";
   "stack_limit","num";
   "stack_max","num option";
   "stack_size","(num)spt";
   "memory","A word->(A)word_loc";
   "mdomain","A word->bool";
   "sh_mdomain","A word->bool";
   "permute","num->num->num";
   "compile","C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option";
   "compile_oracle","num->C#(num#num#(A)wl_prog)list";
   "code_buffer","(A,8)buffer";
   "data_buffer","(A,A)buffer";
   "gc_fun","(((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
              (store_name,(A)word_loc)fmap)->
             (((A)word_loc)list#(A word->(A)word_loc)#
              (store_name,(A)word_loc)fmap)option";
   "handler","num";
   "clock","num";
   "termdep","num";
   "code","(num#(A)wl_prog)spt";
   "be","bool";
   "ffi","(FFI)ffi_state"];;

let wl_state_component_equality = wl_state_INFO.ri_component_equality;;

let stack_size_frame_def = cake_def
  `(stack_size_frame (StackFrame n _ _ NONE:(A)stack_frame) = n) /\
   (stack_size_frame (StackFrame n _ _ (SOME _):(A)stack_frame) =
      OPTION_MAP ((+) 3) n)`;;

(* HOL4: stack_size = FOLDR (OPTION_MAP2 $+ o stack_size_frame) (SOME 1),    *)
(* here with the argument (ITLIST f l e = FOLDR f e l)                       *)

let wl_stack_size_def = cake_def
  `wl_stack_size (stack:((A)stack_frame)list) =
     ITLIST (OPTION_MAP2 (+) o stack_size_frame) stack (SOME 1)`;;

let wl_result_INDUCT,wl_result_RECURSION = cake_type
  "wl_result = wl_Result ((W)word_loc) (((W)word_loc) list)
             | wl_Exception ((W)word_loc) ((W)word_loc)
             | wordSem_Break num
             | wordSem_Continue num
             | wl_TimeOut
             | NotEnoughSpace
             | wl_FinalFFI final_event
             | wl_Error";;

let isResult_def = cake_def
  `(isResult (wl_Result (a:(W)word_loc) b) <=> T) /\
   (isResult (_:(W)wl_result) <=> F)`;;

let isException_def = cake_def
  `(isException (wl_Exception (a:(W)word_loc) b) <=> T) /\
   (isException (_:(W)wl_result) <=> F)`;;

let wl_dec_clock_def = cake_def
  `wl_dec_clock (s:(A,C,FFI)wl_state) =
     wl_state_clock_fupd (combin_K (wl_state_clock s - 1)) s`;;

(* HOL4 infers the most general type: old_s and new_s are states of        *)
(* independent types                                                         *)

let wl_fix_clock_def = cake_def
  `wl_fix_clock (old_s:(A,C,FFI)wl_state) (res:B,(new_s:(D,E,G)wl_state)) =
     (res,
      wl_state_clock_fupd
        (combin_K (if wl_state_clock old_s < wl_state_clock new_s
            then wl_state_clock old_s else wl_state_clock new_s))
        (wl_state_termdep_fupd (combin_K (wl_state_termdep old_s)) new_s))`;;

let is_word_def = cake_def
  `(is_word (wl_Word (w:A word)) <=> T) /\
   (is_word (_:(A)word_loc) <=> F)`;;

let _ = cake_add_simps [is_word_def];;

let get_word_def = cake_def
  `get_word (wl_Word (w:A word)) = w`;;

let _ = cake_add_simps [get_word_def];;

let wl_mem_store_def = cake_def
  `wl_mem_store (addr:A word) (w:(A)word_loc) (s:(A,C,FFI)wl_state) =
     if addr IN wl_state_mdomain s then
       SOME (wl_state_memory_fupd (combin_K ((addr =+ w) (wl_state_memory s))) s)
     else NONE`;;

let wl_mem_load_def = cake_def
  `wl_mem_load (addr:A word) (s:(A,C,FFI)wl_state) =
     if addr IN wl_state_mdomain s then SOME (wl_state_memory s addr)
     else NONE`;;

let the_words_def = cake_def
  `(the_words [] = SOME ([]:(A word) list)) /\
   (the_words (CONS (w:((A)word_loc)option) ws) =
      match (w,the_words ws) with
        (SOME (wl_Word x), SOME xs) -> SOME (CONS x xs)
      | _ -> NONE)`;;

let wl_get_var_def = cake_def
  `wl_get_var v (s:(A,C,FFI)wl_state) = lookup v (wl_state_locals s)`;;

let wl_get_vars_def = cake_def
  `(wl_get_vars [] (s:(A,C,FFI)wl_state) = SOME []) /\
   (wl_get_vars (CONS v vs) s =
      match wl_get_var v s with
        NONE -> NONE
      | SOME x -> (match wl_get_vars vs s with
                     NONE -> NONE
                   | SOME xs -> SOME (CONS x xs)))`;;

let wl_set_var_def = cake_def
  `wl_set_var v x (s:(A,C,FFI)wl_state) =
     wl_state_locals_fupd (combin_K (insert v x (wl_state_locals s))) s`;;

let wl_unset_var_def = cake_def
  `wl_unset_var v (s:(A,C,FFI)wl_state) =
     wl_state_locals_fupd (combin_K (delete v (wl_state_locals s))) s`;;

let wl_set_vars_def = cake_def
  `wl_set_vars vs xs (s:(A,C,FFI)wl_state) =
     wl_state_locals_fupd (combin_K (alist_insert vs xs (wl_state_locals s))) s`;;

let wl_get_store_def = cake_def
  `wl_get_store v (s:(A,C,FFI)wl_state) = FLOOKUP (wl_state_store s) v`;;

let wl_set_store_def = cake_def
  `wl_set_store v x (s:(A,C,FFI)wl_state) =
     wl_state_store_fupd (combin_K (wl_state_store s |+ (v,x))) s`;;

let wl_word_exp_def = cake_def_wf
  `MEASURE (\p:(A,C,FFI)wl_state#(A)wl_exp. wl_exp_size (\x:A. 0) (SND p))`
  TERM_TAC
  `(wl_word_exp (s:(A,C,FFI)wl_state) (wl_Const w) = SOME (wl_Word w)) /\
   (wl_word_exp s (wl_Var v) = wl_get_var v s) /\
   (wl_word_exp s (Lookup name) = wl_get_store name s) /\
   (wl_word_exp s (wl_Load addr) =
      match wl_word_exp s addr with
        SOME (wl_Word w) -> wl_mem_load w s
      | _ -> NONE) /\
   (wl_word_exp s (wl_Op op wexps) =
      match the_words (MAP (wl_word_exp s) wexps) with
        SOME ws -> OPTION_MAP wl_Word (word_op op ws)
      | _ -> NONE) /\
   (wl_word_exp s (wl_Shift sh wexp wexp1) =
      match (wl_word_exp s wexp, wl_word_exp s wexp1) with
        (SOME (wl_Word w), SOME (wl_Word w1)) ->
          OPTION_MAP wl_Word (word_sh sh w (val w1))
      | _ -> NONE)`;;

(* HOL4's word_exp_ind (the kit's cake_ind "wl_word_exp" has the weaker    *)
(* hypothesis wl_word_exp s wexp = SOME (wl_Word w) ==> P s wexp1 for Shift, *)
(* since the match on the pair is compiled into nested cases): structural   *)
(* induction                                                                 *)

let wl_word_exp_ind = prove
 (`!P:(A,C,FFI)wl_state->(A)wl_exp->bool.
       (!s w. P s (wl_Const w)) /\
       (!s v. P s (wl_Var v)) /\
       (!s name. P s (Lookup name)) /\
       (!s addr. P s addr ==> P s (wl_Load addr)) /\
       (!s op wexps. (!a. MEM a wexps ==> P s a) ==> P s (wl_Op op wexps)) /\
       (!s sh wexp wexp1. P s wexp /\ P s wexp1 ==> P s (wl_Shift sh wexp wexp1))
       ==> !v v1. P v v1`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:(A,C,FFI)wl_state` THEN
  MP_TAC(ISPECL [`\e:(A)wl_exp. P (v:(A,C,FFI)wl_state) e:bool`;
                 `\l:((A)wl_exp)list. !a. MEM a l ==> P (v:(A,C,FFI)wl_state) a`]
                wl_exp_INDUCT) THEN
  REWRITE_TAC[MEM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[]; SIMP_TAC[]]);;

(* Flushes the locals and (optionally) the store *)

let wl_flush_state_def = cake_def
  `(wl_flush_state T (s:(A,C,FFI)wl_state) =
      wl_state_locals_fupd (combin_K LN)
        (wl_state_stack_fupd (combin_K [])
           (wl_state_store_fupd (combin_K FEMPTY)
              (wl_state_locals_size_fupd (combin_K (SOME 0)) s)))) /\
   (wl_flush_state F s =
      wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0)) s))`;;

let wl_sh_mem_store_def = cake_def
  `wl_sh_mem_store (a:A word) (w:A word) (s:(A,C,FFI)wl_state) =
     if a IN wl_state_sh_mdomain s then
       match call_FFI (wl_state_ffi s) (SharedMem MappedWrite) [word 0:byte]
               (APPEND (word_to_bytes w F) (word_to_bytes a F)) with
         FFI_final outcome ->
           (SOME (wl_FinalFFI outcome:(W)wl_result), wl_flush_state T s)
       | FFI_return new_ffi new_bytes -> (NONE, wl_state_ffi_fupd (combin_K new_ffi) s)
     else (SOME wl_Error, s)`;;

let wl_sh_mem_load_def = cake_def
  `wl_sh_mem_load (a:A word) (s:(A,C,FFI)wl_state) =
     if a IN wl_state_sh_mdomain s then
       SOME (call_FFI (wl_state_ffi s) (SharedMem MappedRead) [word 0:byte]
               (word_to_bytes a F))
     else NONE`;;

let wl_sh_mem_store_byte_def = cake_def
  `wl_sh_mem_store_byte (a:A word) (w:A word) (s:(A,C,FFI)wl_state) =
     if byte_align a IN wl_state_sh_mdomain s then
       match call_FFI (wl_state_ffi s) (SharedMem MappedWrite) [word 1:byte]
               (APPEND [get_byte (word 0) w F] (word_to_bytes a F)) with
         FFI_final outcome ->
           (SOME (wl_FinalFFI outcome:(W)wl_result), wl_flush_state T s)
       | FFI_return new_ffi new_bytes -> (NONE, wl_state_ffi_fupd (combin_K new_ffi) s)
     else (SOME wl_Error, s)`;;

let wl_sh_mem_store16_def = cake_def
  `wl_sh_mem_store16 (a:A word) (w:A word) (s:(A,C,FFI)wl_state) =
     if byte_align a IN wl_state_sh_mdomain s then
       match call_FFI (wl_state_ffi s) (SharedMem MappedWrite) [word 2:byte]
               (APPEND (TAKE 2 (word_to_bytes w F)) (word_to_bytes a F)) with
         FFI_final outcome ->
           (SOME (wl_FinalFFI outcome:(W)wl_result), wl_flush_state T s)
       | FFI_return new_ffi new_bytes -> (NONE, wl_state_ffi_fupd (combin_K new_ffi) s)
     else (SOME wl_Error, s)`;;

let wl_sh_mem_store32_def = cake_def
  `wl_sh_mem_store32 (a:A word) (w:A word) (s:(A,C,FFI)wl_state) =
     if byte_align a IN wl_state_sh_mdomain s then
       match call_FFI (wl_state_ffi s) (SharedMem MappedWrite) [word 4:byte]
               (APPEND (TAKE 4 (word_to_bytes w F)) (word_to_bytes a F)) with
         FFI_final outcome ->
           (SOME (wl_FinalFFI outcome:(W)wl_result), wl_flush_state T s)
       | FFI_return new_ffi new_bytes -> (NONE, wl_state_ffi_fupd (combin_K new_ffi) s)
     else (SOME wl_Error, s)`;;

let wl_sh_mem_load_byte_def = cake_def
  `wl_sh_mem_load_byte (a:A word) (s:(A,C,FFI)wl_state) =
     if byte_align a IN wl_state_sh_mdomain s then
       SOME (call_FFI (wl_state_ffi s) (SharedMem MappedRead) [word 1:byte]
               (word_to_bytes a F))
     else NONE`;;

let wl_sh_mem_load16_def = cake_def
  `wl_sh_mem_load16 (a:A word) (s:(A,C,FFI)wl_state) =
     if byte_align a IN wl_state_sh_mdomain s then
       SOME (call_FFI (wl_state_ffi s) (SharedMem MappedRead) [word 2:byte]
               (word_to_bytes a F))
     else NONE`;;

let wl_sh_mem_load32_def = cake_def
  `wl_sh_mem_load32 (a:A word) (s:(A,C,FFI)wl_state) =
     if byte_align a IN wl_state_sh_mdomain s then
       SOME (call_FFI (wl_state_ffi s) (SharedMem MappedRead) [word 4:byte]
               (word_to_bytes a F))
     else NONE`;;

(* set variable given the output from ShareLoad(Byte) *)

let sh_mem_set_var_def = cake_def
  `(sh_mem_set_var (SOME (FFI_final outcome)) _ (s:(A,C,FFI)wl_state) =
      (SOME (wl_FinalFFI outcome:(W)wl_result), wl_flush_state T s)) /\
   (sh_mem_set_var (SOME (FFI_return new_ffi new_bytes)) v s =
      (NONE, wl_set_var v (wl_Word (word_of_bytes F (word 0) new_bytes))
               (wl_state_ffi_fupd (combin_K new_ffi) s))) /\
   (sh_mem_set_var _ _ s = (SOME wl_Error, s))`;;

let share_inst_def = cake_def
  `(share_inst asm_Load v (ad:A word) (s:(A,C,FFI)wl_state) =
      sh_mem_set_var (wl_sh_mem_load ad s) v s:((W)wl_result)option#(A,C,FFI)wl_state) /\
   (share_inst Load8 v ad s = sh_mem_set_var (wl_sh_mem_load_byte ad s) v s) /\
   (share_inst Load16 v ad s = sh_mem_set_var (wl_sh_mem_load16 ad s) v s) /\
   (share_inst asm_Load32 v ad s = sh_mem_set_var (wl_sh_mem_load32 ad s) v s) /\
   (share_inst asm_Store v ad s =
      match wl_get_var v s with
        SOME (wl_Word v) -> wl_sh_mem_store ad v s
      | _ -> (SOME wl_Error,s)) /\
   (share_inst Store8 v ad s =
      match wl_get_var v s with
        SOME (wl_Word v) -> wl_sh_mem_store_byte ad v s
      | _ -> (SOME wl_Error,s)) /\
   (share_inst Store16 v ad s =
      match wl_get_var v s with
        SOME (wl_Word v) -> wl_sh_mem_store16 ad v s
      | _ -> (SOME wl_Error,s)) /\
   (share_inst asm_Store32 v ad s =
      match wl_get_var v s with
        SOME (wl_Word v) -> wl_sh_mem_store32 ad v s
      | _ -> (SOME wl_Error,s))`;;

let wl_call_env_def = cake_def
  `wl_call_env args (size':num option) (s:(A,C,FFI)wl_state) =
     wl_state_locals_fupd (combin_K (fromList2 args))
       (wl_state_locals_size_fupd (combin_K size')
          (wl_state_stack_max_fupd
             (combin_K (OPTION_MAP2 MAX (wl_state_stack_max s)
                   (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) size')))
             s))`;;

(* if the mover function is actually a permutation, i.e. it bijects (or     *)
(* injects) the keys 0...n-1 to 0...n-1, use it; if it isn't well-formed,   *)
(* just pretend it is I                                                      *)

let list_rearrange_def = cake_def
  `list_rearrange mover (xs:A list) =
     if BIJ mover (pred_set_count (LENGTH xs)) (pred_set_count (LENGTH xs))
     then list_of_seq (\i. EL (mover i) xs) (LENGTH xs)
     else xs`;;

(* Compare on keys, if keys match (never), then compare on the word_loc     *)
(* vals. Treat Words as < Locs                                               *)

let key_val_compare_def = cake_def
  `key_val_compare (x:num#(A)word_loc) (y:num#(A)word_loc) <=>
     let (a,b) = x in
     let (a',b') = y in
       a > a' \/
       (a = a' /\
        match b with
          wl_Word x -> (match b' with wl_Word y -> word_ile x y | _ -> T)
        | wl_Loc a b ->
            (match b' with
               wl_Loc a' b' -> a > a' \/ (a = a' /\ b >= b')
             | _ -> F))`;;

let env_to_list_def = cake_def
  `env_to_list (env:((A)word_loc)spt) (bij_seq:num->num->num) =
     let mover = bij_seq 0 in
     let permute = (\n. bij_seq (n + 1)) in
     let l = toAList env in
     let l = sort key_val_compare l in
     let l = list_rearrange mover l in
       (l,permute)`;;

let wl_push_env_def = cake_def
  `(wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt) NONE
                (s:(A,C,FFI)wl_state) =
      let l0 = toAList (FST envs) in
      let (l,permute) = env_to_list (SND envs) (wl_state_permute s) in
      let stack = CONS (StackFrame (wl_state_locals_size s) l0 l NONE)
                       (wl_state_stack s) in
        wl_state_stack_fupd (combin_K stack)
          (wl_state_stack_max_fupd
             (combin_K (OPTION_MAP2 MAX (wl_state_stack_max s) (wl_stack_size stack)))
             (wl_state_permute_fupd (combin_K permute) s))) /\
   (wl_push_env envs (SOME (w:num,h:(A)wl_prog,l1,l2)) s =
      let l0 = toAList (FST envs) in
      let (l,permute) = env_to_list (SND envs) (wl_state_permute s) in
      let handler = SOME (wl_state_handler s,l1,l2) in
      let stack = CONS (StackFrame (wl_state_locals_size s) l0 l handler)
                       (wl_state_stack s) in
        wl_state_stack_fupd (combin_K stack)
          (wl_state_stack_max_fupd
             (combin_K (OPTION_MAP2 MAX (wl_state_stack_max s) (wl_stack_size stack)))
             (wl_state_permute_fupd (combin_K permute)
                (wl_state_handler_fupd (combin_K (LENGTH (wl_state_stack s))) s))))`;;

let wl_push_env_ind = IL2AUX_case_ind wl_push_env_def;;

let wl_pop_env_def = cake_def
  `wl_pop_env (s:(A,C,FFI)wl_state) =
     match wl_state_stack s with
       CONS (StackFrame m e0 e NONE) xs ->
         SOME (wl_state_locals_fupd (combin_K (sptree_union (fromAList e) (fromAList e0)))
                 (wl_state_stack_fupd (combin_K xs) (wl_state_locals_size_fupd (combin_K m) s)))
     | CONS (StackFrame m e0 e (SOME (n,_,_))) xs ->
         SOME (wl_state_locals_fupd (combin_K (sptree_union (fromAList e) (fromAList e0)))
                 (wl_state_stack_fupd (combin_K xs)
                    (wl_state_locals_size_fupd (combin_K m)
                       (wl_state_handler_fupd (combin_K n) s))))
     | _ -> NONE`;;

(* HOL4 [local] *)

let wl_push_env_clock = prove
 (`wl_state_clock (wl_push_env env b (s:(A,C,FFI)wl_state)) = wl_state_clock s`,
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN SIMP[]);;

(* HOL4 [local] *)

let wl_pop_env_clock = prove
 (`wl_pop_env (s:(A,C,FFI)wl_state) = SOME s1 ==> wl_state_clock s1 = wl_state_clock s`,
  REWRITE_TAC[wl_pop_env_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let wl_jump_exc_def = cake_def
  `wl_jump_exc (s:(A,C,FFI)wl_state) =
     if wl_state_handler s < LENGTH (wl_state_stack s) then
       match LASTN (wl_state_handler s + 1) (wl_state_stack s) with
         CONS (StackFrame m e0 e (SOME (n,l1,l2))) xs ->
           SOME (wl_state_handler_fupd (combin_K n)
                   (wl_state_locals_fupd (combin_K (sptree_union (fromAList e) (fromAList e0)))
                      (wl_state_stack_fupd (combin_K xs)
                         (wl_state_locals_size_fupd (combin_K m) s))),
                 l1,l2)
       | _ -> NONE
     else NONE`;;

let cut_names_def = cake_def
  `cut_names (name_set:(B)spt) (env:(A)spt) =
     if domain name_set SUBSET domain env then SOME (sptree_inter env name_set)
     else NONE`;;

let cut_envs_def = cake_def
  `cut_envs (name_sets:cutsets) (env:(A)spt) =
     match (cut_names (FST name_sets) env, cut_names (SND name_sets) env) with
       (SOME e1, SOME e2) -> SOME (e1, e2)
     | _ -> NONE`;;

let wl_cut_env_def = cake_def
  `wl_cut_env (name_sets:cutsets) (env:(A)spt) =
     match cut_envs name_sets env with
       SOME (e1, e2) -> SOME (sptree_union e2 e1)
     | _ -> NONE`;;

let wl_cut_state_def = cake_def
  `wl_cut_state (names:cutsets) (s:(A,C,FFI)wl_state) =
     match wl_cut_env names (wl_state_locals s) with
       NONE -> NONE
     | SOME env -> SOME (wl_state_locals_fupd (combin_K env) s)`;;

let wl_cut_state_opt_def = cake_def
  `wl_cut_state_opt (names:cutsets option) (s:(A,C,FFI)wl_state) =
     match names with
       NONE -> SOME s
     | SOME names -> wl_cut_state names s`;;

let wl_find_code_def = cake_def
  `(wl_find_code (SOME p) (args:((A)word_loc)list) (code:(num#B)spt)
                 (ssize:(C)spt) =
      match lookup p code with
        NONE -> NONE
      | SOME (arity,exp) ->
          if LENGTH args = arity then SOME (args,exp,lookup p ssize)
          else NONE) /\
   (wl_find_code NONE args code ssize =
      if args = [] then NONE else
      match LAST args with
        wl_Loc loc 0 ->
          (match lookup loc code with
             NONE -> NONE
           | SOME (arity,exp) ->
               if LENGTH args = arity + 1
               then SOME (BUTLAST args,exp,lookup loc ssize)
               else NONE)
      | other -> NONE)`;;

let wl_enc_stack_def = cake_def
  `(wl_enc_stack ([]:((A)stack_frame)list) = []) /\
   (wl_enc_stack (CONS (StackFrame n _ l handler) st) =
      APPEND (MAP SND l) (wl_enc_stack st))`;;

let wl_dec_stack_def = cake_def
  `(wl_dec_stack ([]:((A)word_loc)list) ([]:((A)stack_frame)list) = SOME []) /\
   (wl_dec_stack xs (CONS (StackFrame n l0 l handler) st) =
      if LENGTH xs < LENGTH l then NONE else
      match wl_dec_stack (DROP (LENGTH l) xs) st with
        NONE -> NONE
      | SOME s ->
          SOME (CONS (StackFrame n l0 (ZIP (MAP FST l) (TAKE (LENGTH l) xs))
                                 handler) s)) /\
   (wl_dec_stack _ _ = NONE)`;;

let wl_dec_stack_ind = cake_ind "wl_dec_stack";;

(* gc runs the garbage collector algorithm *)

let wl_gc_def = cake_def
  `wl_gc (s:(A,C,FFI)wl_state) =
     let wl_list = wl_enc_stack (wl_state_stack s) in
     match wl_state_gc_fun s (wl_list, wl_state_memory s, wl_state_mdomain s,
                              wl_state_store s) with
       NONE -> NONE
     | SOME (wl,m,st) ->
         (match wl_dec_stack wl (wl_state_stack s) with
            NONE -> NONE
          | SOME stack ->
              SOME (wl_state_stack_fupd (combin_K stack)
                      (wl_state_store_fupd (combin_K st)
                         (wl_state_memory_fupd (combin_K m) s))))`;;

let wl_has_space_def = cake_def
  `wl_has_space (wl:(A)word_loc) (s:(A,C,FFI)wl_state) =
     match (wl, wl_get_store NextFree s, wl_get_store TriggerGC s) with
       (wl_Word w, SOME (wl_Word n), SOME (wl_Word l)) ->
         SOME (val w <= val (word_sub l n))
     | _ -> NONE`;;

(* to_ask: should we not update stack size here?  The cases on a boolean   *)
(* (HOL4 SOME T => ... | SOME F => ...) are written as a conditional, which *)
(* is what HOL4's case on bool is.                                          *)

let wl_alloc_def = cake_def
  `wl_alloc (w:A word) (names:cutsets) (s:(A,C,FFI)wl_state) =
     match cut_envs names (wl_state_locals s) with
       NONE -> (SOME (wl_Error:(A)wl_result), wl_flush_state T s)
     | SOME envs ->
       (match wl_gc (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
                       (wl_set_store AllocSize (wl_Word w) s)) with
          NONE -> (SOME wl_Error, wl_flush_state T s)
        | SOME s ->
          (match wl_pop_env s with
             NONE -> (SOME wl_Error, wl_flush_state T s)
           | SOME s ->
             (match wl_get_store AllocSize s with
                NONE -> (SOME wl_Error, s)
              | SOME w ->
                (match wl_has_space w s with
                   NONE -> (SOME wl_Error, s)
                 | SOME b ->
                     if b then (NONE, s)
                     else (SOME NotEnoughSpace, wl_flush_state T s)))))`;;

let wl_assign_def = cake_def
  `wl_assign reg (exp:(A)wl_exp) (s:(A,C,FFI)wl_state) =
     match wl_word_exp s exp with
       NONE -> NONE
     | SOME w -> SOME (wl_set_var reg w s)`;;

let wl_get_fp_var_def = cake_def
  `wl_get_fp_var v (s:(A,C,FFI)wl_state) = FLOOKUP (wl_state_fp_regs s) v`;;

let wl_set_fp_var_def = cake_def
  `wl_set_fp_var v x (s:(A,C,FFI)wl_state) =
     wl_state_fp_regs_fupd (combin_K (wl_state_fp_regs s |+ (v,x))) s`;;

let wl_inst_def = cake_def
  `wl_inst (i:(A)inst) (s:(A,C,FFI)wl_state) =
     match i with
       asm_Skip -> SOME s
     | asm_Const reg w -> wl_assign reg (wl_Const w) s
     | asm_Arith (Binop bop r1 r2 ri) ->
         wl_assign r1
           (wl_Op bop [wl_Var r2; (match ri with Reg r3 -> wl_Var r3
                                               | Imm w -> wl_Const w)]) s
     | asm_Arith (asm_Shift sh r1 r2 ri) ->
         wl_assign r1
           (wl_Shift sh (wl_Var r2) (match ri with Reg r3 -> wl_Var r3
                                                 | Imm w -> wl_Const w)) s
     | asm_Arith (asm_Div r1 r2 r3) ->
         (let vs = wl_get_vars [r3;r2] s in
          match vs with
            SOME [wl_Word q; wl_Word w2] ->
              if ~(q = word 0) then
                SOME (wl_set_var r1 (wl_Word (word_jdiv w2 q)) s)
              else NONE
          | _ -> NONE)
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
         (let vs = wl_get_vars [r2;r3;r4] s in
          match vs with
            SOME [wl_Word l; wl_Word r; wl_Word c] ->
              let (res,co) = word_add_carry l r c in
                SOME (wl_set_var r4 (wl_Word co) (wl_set_var r1 (wl_Word res) s))
          | _ -> NONE)
     | asm_Arith (AddOverflow r1 r2 r3 r4) ->
         (let vs = wl_get_vars [r2;r3] s in
          match vs with
            SOME [wl_Word w2; wl_Word w3] ->
              SOME (wl_set_var r4
                      (wl_Word (if ~(ival (word_add w2 w3) = ival w2 + ival w3)
                                then word 1 else word 0))
                      (wl_set_var r1 (wl_Word (word_add w2 w3)) s))
          | _ -> NONE)
     | asm_Arith (SubOverflow r1 r2 r3 r4) ->
         (let vs = wl_get_vars [r2;r3] s in
          match vs with
            SOME [wl_Word w2; wl_Word w3] ->
              SOME (wl_set_var r4
                      (wl_Word (if ~(ival (word_sub w2 w3) = ival w2 - ival w3)
                                then word 1 else word 0))
                      (wl_set_var r1 (wl_Word (word_sub w2 w3)) s))
          | _ -> NONE)
     | asm_Arith (LongMul r1 r2 r3 r4) ->
         (let vs = wl_get_vars [r3;r4] s in
          match vs with
            SOME [wl_Word w3; wl_Word w4] ->
              let r = val w3 * val w4 in
                SOME (wl_set_var r2 (wl_Word (word r))
                        (wl_set_var r1 (wl_Word (word (r DIV dimword(:A)))) s))
          | _ -> NONE)
     | asm_Arith (LongDiv r1 r2 r3 r4 r5) ->
         (let vs = wl_get_vars [r3;r4;r5] s in
          match vs with
            SOME [wl_Word w3; wl_Word w4; wl_Word w5] ->
              let n = val w3 * dimword(:A) + val w4 in
              let d = val w5 in
              let q = n DIV d in
              if ~(d = 0) /\ q < dimword(:A) then
                SOME (wl_set_var r1 (wl_Word (word q))
                        (wl_set_var r2 (wl_Word (word (n MOD d))) s))
              else NONE
          | _ -> NONE)
     | Mem asm_Load r (Addr a w) ->
         (match wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
            SOME (wl_Word w) ->
              (match wl_mem_load w s with
                 NONE -> NONE
               | SOME w -> SOME (wl_set_var r w s))
          | _ -> NONE)
     | Mem Load8 r (Addr a w) ->
         (match wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
            SOME (wl_Word w) ->
              (match mem_load_byte_aux (wl_state_memory s) (wl_state_mdomain s)
                       (wl_state_be s) w with
                 NONE -> NONE
               | SOME w -> SOME (wl_set_var r (wl_Word (word_zx w)) s))
          | _ -> NONE)
     | Mem Load16 _ _ -> NONE
     | Mem asm_Load32 r (Addr a w) ->
         (match wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
            SOME (wl_Word w) ->
              (match mem_load_32 (wl_state_memory s) (wl_state_mdomain s)
                       (wl_state_be s) w with
                 NONE -> NONE
               | SOME w -> SOME (wl_set_var r (wl_Word (word_zx w)) s))
          | _ -> NONE)
     | Mem asm_Store r (Addr a w) ->
         (match (wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]),
                 wl_get_var r s) with
            (SOME (wl_Word a), SOME w) ->
              (match wl_mem_store a w s with
                 SOME s1 -> SOME s1
               | NONE -> NONE)
          | _ -> NONE)
     | Mem Store8 r (Addr a w) ->
         (match (wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]),
                 wl_get_var r s) with
            (SOME (wl_Word a), SOME (wl_Word w)) ->
              (match mem_store_byte_aux (wl_state_memory s) (wl_state_mdomain s)
                       (wl_state_be s) a (word_zx w) with
                 SOME new_m -> SOME (wl_state_memory_fupd (combin_K new_m) s)
               | NONE -> NONE)
          | _ -> NONE)
     | Mem Store16 _ _ -> NONE
     | Mem asm_Store32 r (Addr a w) ->
         (match (wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]),
                 wl_get_var r s) with
            (SOME (wl_Word a), SOME (wl_Word w)) ->
              (match mem_store_32 (wl_state_memory s) (wl_state_mdomain s)
                       (wl_state_be s) a (word_zx w) with
                 SOME new_m -> SOME (wl_state_memory_fupd (combin_K new_m) s)
               | NONE -> NONE)
          | _ -> NONE)
     | FP (FPLess r d1 d2) ->
         (match (wl_get_fp_var d1 s, wl_get_fp_var d2 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_var r
                      (wl_Word (if fp64_lessThan f1 f2 then word 1 else word 0)) s)
          | _ -> NONE)
     | FP (FPLessEqual r d1 d2) ->
         (match (wl_get_fp_var d1 s, wl_get_fp_var d2 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_var r
                      (wl_Word (if fp64_lessEqual f1 f2 then word 1 else word 0)) s)
          | _ -> NONE)
     | FP (FPEqual r d1 d2) ->
         (match (wl_get_fp_var d1 s, wl_get_fp_var d2 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_var r
                      (wl_Word (if fp64_equal f1 f2 then word 1 else word 0)) s)
          | _ -> NONE)
     | FP (FPMov d1 d2) ->
         (match wl_get_fp_var d2 s with
            SOME f -> SOME (wl_set_fp_var d1 f s)
          | _ -> NONE)
     | FP (FPAbs d1 d2) ->
         (match wl_get_fp_var d2 s with
            SOME f -> SOME (wl_set_fp_var d1 (fp64_abs f) s)
          | _ -> NONE)
     | FP (FPNeg d1 d2) ->
         (match wl_get_fp_var d2 s with
            SOME f -> SOME (wl_set_fp_var d1 (fp64_negate f) s)
          | _ -> NONE)
     | FP (FPSqrt d1 d2) ->
         (match wl_get_fp_var d2 s with
            SOME f -> SOME (wl_set_fp_var d1 (fp64_sqrt roundTiesToEven f) s)
          | _ -> NONE)
     | FP (FPAdd d1 d2 d3) ->
         (match (wl_get_fp_var d2 s, wl_get_fp_var d3 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPSub d1 d2 d3) ->
         (match (wl_get_fp_var d2 s, wl_get_fp_var d3 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPMul d1 d2 d3) ->
         (match (wl_get_fp_var d2 s, wl_get_fp_var d3 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPDiv d1 d2 d3) ->
         (match (wl_get_fp_var d2 s, wl_get_fp_var d3 s) with
            (SOME f1, SOME f2) ->
              SOME (wl_set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPFma d1 d2 d3) ->
         (match (wl_get_fp_var d1 s, wl_get_fp_var d2 s, wl_get_fp_var d3 s) with
            (SOME f1, SOME f2, SOME f3) ->
              SOME (wl_set_fp_var d1 (fpfma f1 f2 f3) s)
          | _ -> NONE)
     | FP (FPMovToReg r1 r2 d) ->
         (match wl_get_fp_var d s with
            SOME v ->
              if dimindex(:A) = 64 then
                SOME (wl_set_var r1 (wl_Word (word_zx v)) s)
              else
                SOME (wl_set_var r2 (wl_Word (word_extract 63 32 v))
                        (wl_set_var r1 (wl_Word (word_extract 31 0 v)) s))
          | _ -> NONE)
     | FP (FPMovFromReg d r1 r2) ->
         (if dimindex(:A) = 64 then
            match wl_get_var r1 s with
              SOME (wl_Word w1) -> SOME (wl_set_fp_var d (word_zx w1) s)
            | _ -> NONE
          else
            match (wl_get_var r1 s, wl_get_var r2 s) with
              (SOME (wl_Word w1), SOME (wl_Word w2)) ->
                SOME (wl_set_fp_var d (word_join w2 w1) s)
            | _ -> NONE)
     | FP (FPToInt d1 d2) ->
         (match wl_get_fp_var d2 s with
            NONE -> NONE
          | SOME f ->
            (match fp64_to_int roundTiesToEven f with
               NONE -> NONE
             | SOME i ->
               let w = iword i:int32 in
               if ival w = i then
                 (if dimindex(:A) = 64 then
                    SOME (wl_set_fp_var d1 (word_zx w) s)
                  else
                    match wl_get_fp_var (d1 DIV 2) s with
                      NONE -> NONE
                    | SOME f ->
                      let (h,l) = if ODD d1 then (63,32) else (31,0) in
                        SOME (wl_set_fp_var (d1 DIV 2)
                                (word_insert f (l,(h + 1) - l) w) s))
               else NONE))
     | FP (FPFromInt d1 d2) ->
         if dimindex(:A) = 64 then
           match wl_get_fp_var d2 s with
             SOME f ->
               let i = ival (word_extract 31 0 f:int32) in
                 SOME (wl_set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
           | NONE -> NONE
         else
           match wl_get_fp_var (d2 DIV 2) s with
             SOME v ->
               let i = ival (if ODD d2 then word_extract 63 32 v
                             else word_extract 31 0 v:A word) in
                 SOME (wl_set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
           | NONE -> NONE
     | _ -> NONE`;;

let wl_get_var_imm_def = cake_def
  `(wl_get_var_imm (Reg n:(A)reg_imm) (s:(A,C,FFI)wl_state) = wl_get_var n s) /\
   (wl_get_var_imm (Imm w) s = SOME (wl_Word w))`;;

let add_ret_loc_def = cake_def
  `(add_ret_loc (NONE:(B#C#D#num#num)option) (xs:((A)word_loc)list) = xs) /\
   (add_ret_loc (SOME (n,names,ret_handler,l1,l2)) xs = CONS (wl_Loc l1 l2) xs)`;;

(* Avoid case split *)

let bad_dest_args_def = cake_def
  `bad_dest_args (dest:A option) (args:B list) <=> dest = NONE /\ args = []`;;

(* HOL4 [local] *)

let termdep_rw = prove
 (`wl_state_termdep (wl_call_env p_1 ss (s:(A,C,FFI)wl_state)) =
     wl_state_termdep s /\
   wl_state_termdep (wl_dec_clock s) = wl_state_termdep s /\
   wl_state_termdep (wl_set_var n v s) = wl_state_termdep s`,
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_set_var_def] THEN SIMP[]);;

(* HOL4 [local] *)

let fix_clock_IMP_LESS_EQ = prove
 (`!x. wl_fix_clock (s:(A,C,FFI)wl_state) x = (res:B,(s1:(D,E,G)wl_state))
       ==> wl_state_clock s1 <= wl_state_clock s /\
           wl_state_termdep s1 = wl_state_termdep s`,
  REWRITE_TAC[FORALL_PAIR_THM; wl_fix_clock_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (SUBST1_TAC o SYM)) THEN SIMP[] THEN
  ARITH_TAC);;

(* This is just a number that's large enough for our purposes.  It stated  *)
(* in a way that makes proofs easy.  HOL4 MustTerminate_limit (:'a) takes  *)
(* the type as argument: here the universe (:A), as for dimword; the       *)
(* definition is MustTerminate_limit_DEF and the HOL4 statement            *)
(* MustTerminate_limit_def.  HOL4 ** is EXP (right associative).            *)

let MustTerminate_limit_DEF = new_definition
  `MustTerminate_limit (s:A->bool) =
     2 * dimword(:A) +
     dimword(:A) * dimword(:A) +
     dimword(:A) EXP dimword(:A) +
     dimword(:A) EXP (dimword(:A) EXP dimword(:A))`;;

let MustTerminate_limit_def = prove
 (`MustTerminate_limit (:A) =
     2 * dimword(:A) +
     dimword(:A) * dimword(:A) +
     dimword(:A) EXP dimword(:A) +
     dimword(:A) EXP (dimword(:A) EXP dimword(:A))`,
  REWRITE_TAC[MustTerminate_limit_DEF]);;

let const_addresses_def = cake_def
  `(const_addresses (a:A word) ([]:B list) d <=> T) /\
   (const_addresses a (CONS x xs) d <=>
      a IN d /\ const_addresses (word_add a bytes_in_word) xs d)`;;

let const_writes_def = cake_def
  `(const_writes (a:A word) off [] (m:A word->(A)word_loc) = m) /\
   (const_writes a off (CONS (b,x:A word) xs) m =
      const_writes (word_add a bytes_in_word) off xs
        ((a =+ wl_Word (if b then word_add x off else x)) m))`;;

let wl_STOP_def = cake_def
  `wl_STOP (x:A) = x`;;

let wl_bad_fun_return_def = cake_def
  `(wl_bad_fun_return (NONE:((W)wl_result)option) <=> T) /\
   (wl_bad_fun_return (SOME (wordSem_Break _)) <=> T) /\
   (wl_bad_fun_return (SOME (wordSem_Continue _)) <=> T) /\
   (wl_bad_fun_return _ <=> F)`;;

let _ = cake_add_simps [wl_bad_fun_return_def];;

let wl_cont_loop_def = cake_def
  `(wl_cont_loop (NONE:((W)wl_result)option) <=> T) /\
   (wl_cont_loop (SOME (wordSem_Continue n)) <=> n = 0) /\
   (wl_cont_loop _ <=> F)`;;

let _ = cake_add_simps [wl_cont_loop_def];;

let wl_exit_loop_def = cake_def
  `(wl_exit_loop (SOME (wordSem_Break n):((W)wl_result)option) =
      SOME (wordSem_Break (n - 1))) /\
   (wl_exit_loop (SOME (wordSem_Continue n)) = SOME (wordSem_Continue (n - 1))) /\
   (wl_exit_loop res = res)`;;

let _ = cake_add_simps [wl_exit_loop_def];;

(* ------------------------------------------------------------------------- *)
(* The semantics.  The termination tactic (HOL4: fix_clock_IMP_LESS_EQ,     *)
(* termdep_rw, push_env_clock, pop_env_clock, cut_state, then arithmetic)  *)
(* handles both kinds of termination conditions.                            *)
(* ------------------------------------------------------------------------- *)

let IL2AUX_push_env_termdep = prove
 (`wl_state_termdep (wl_push_env env b (s:(A,C,FFI)wl_state)) =
   wl_state_termdep s`,
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`,`b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN SIMP[]);;

let IL2AUX_pop_env_clock_termdep = prove
 (`wl_pop_env (s:(A,C,FFI)wl_state) = SOME s1
   ==> wl_state_clock s1 = wl_state_clock s /\
       wl_state_termdep s1 = wl_state_termdep s`,
  REWRITE_TAC[wl_pop_env_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let IL2AUX_cut_state_clock_termdep = prove
 (`wl_cut_state names (s:(A,C,FFI)wl_state) = SOME s1
   ==> wl_state_clock s1 = wl_state_clock s /\
       wl_state_termdep s1 = wl_state_termdep s`,
  REWRITE_TAC[wl_cut_state_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let IL2AUX_clock_rws =
  [wl_call_env_def; wl_dec_clock_def; wl_set_var_def; wl_set_vars_def;
   wl_STOP_def; wl_push_env_clock; IL2AUX_push_env_termdep;
   wl_state_INFO.ri_accfupds; K_THM; I_THM];;

let IL2AUX_is_num_fact tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let IL2AUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP fix_clock_IMP_LESS_EQ)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_pop_env_clock_termdep)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
                       MATCH_MP IL2AUX_cut_state_clock_termdep)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = WF_REL_THMS @ [FST; SND; type_size_def "wl_prog"] @
                      IL2AUX_clock_rws in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let IL2AUX_evaluate_rel =
  `inv_image (MEASURE I LEX MEASURE I LEX MEASURE (wl_prog_size (\x:A. 0)))
     (\p:(A)wl_prog#(A,C,FFI)wl_state.
        (wl_state_termdep (SND p), wl_state_clock (SND p), FST p))`;;

(* the clauses, parsed in five quotations (HOL4 types each clause on its    *)
(* own: v is a store_name in Set, names a num_set in Loop)                 *)

let IL2AUX_evaluate_clauses = list_mk_conj
 [`(wl_evaluate (wl_Skip:(A)wl_prog, s:(A,C,FFI)wl_state) =
      (NONE:((A)wl_result)option, s)) /\
   (wl_evaluate (wl_Alloc n names, s) =
      match wl_get_var n s with
        SOME (wl_Word w) -> wl_alloc w names s
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_StoreConsts t1 t2 addr offset words, s) =
      match (wl_get_var addr s, wl_get_var offset s) with
        (SOME (wl_Word a), SOME (wl_Word off)) ->
          (if ~const_addresses a words (wl_state_mdomain s) then
             (SOME wl_Error, s)
           else
             let s = wl_state_memory_fupd
                       (combin_K (const_writes a off words (wl_state_memory s))) s in
             let s = wl_set_var offset (wl_Word off)
                       (wl_unset_var t1 (wl_unset_var t2 s)) in
               (NONE, wl_set_var addr
                        (wl_Word (word_add a (word_mul bytes_in_word
                                                (word (LENGTH words))))) s))
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Move pri moves, s) =
      if ALL_DISTINCT (MAP FST moves) then
        match wl_get_vars (MAP SND moves) s with
          NONE -> (SOME wl_Error, s)
        | SOME vs -> (NONE, wl_set_vars (MAP FST moves) vs s)
      else (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Inst i, s) =
      match wl_inst i s with
        SOME s1 -> (NONE, s1)
      | NONE -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Assign v exp, s) =
      match wl_word_exp s exp with
        NONE -> (SOME wl_Error, s)
      | SOME w -> (NONE, wl_set_var v w s)) /\
   (wl_evaluate (wl_Get v name, s) =
      match wl_get_store name s with
        NONE -> (SOME wl_Error, s)
      | SOME x -> (NONE, wl_set_var v x s))`;
  `wl_evaluate (wl_Set v exp:(A)wl_prog, s:(A,C,FFI)wl_state) =
     if v = Handler \/ v = BitmapBase then (SOME (wl_Error:(A)wl_result), s)
     else
     match wl_word_exp s exp with
       NONE -> (SOME wl_Error, s)
     | SOME w -> (NONE, wl_set_store v w s)`;
  `(wl_evaluate (wl_OpCurrHeap b dst src:(A)wl_prog, s:(A,C,FFI)wl_state) =
      match wl_word_exp s (wl_Op b [wl_Var src; Lookup CurrHeap]) with
        NONE -> (SOME (wl_Error:(A)wl_result), s)
      | SOME w -> (NONE, wl_set_var dst w s)) /\
   (wl_evaluate (wl_Store exp v, s) =
      match (wl_word_exp s exp, wl_get_var v s) with
        (SOME (wl_Word a), SOME w) ->
          (match wl_mem_store a w s with
             SOME s1 -> (NONE, s1)
           | NONE -> (SOME wl_Error, s))
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Tick, s) =
      if wl_state_clock s = 0 then (SOME wl_TimeOut, wl_flush_state T s)
      else (NONE, wl_dec_clock s)) /\
   (wl_evaluate (MustTerminate p, s) =
      if wl_state_termdep s = 0 then (SOME wl_Error, s) else
        let (res,s1) = wl_evaluate (p, wl_state_clock_fupd
                                         (combin_K (MustTerminate_limit (:A)))
                                         (wl_state_termdep_fupd
                                            (combin_K (wl_state_termdep s - 1)) s)) in
          if res = SOME wl_TimeOut then (SOME wl_Error, s)
          else (res, wl_state_clock_fupd (combin_K (wl_state_clock s))
                       (wl_state_termdep_fupd (combin_K (wl_state_termdep s)) s1))) /\
   (wl_evaluate (wl_Seq c1 c2, s) =
      let (res,s1) = wl_fix_clock s (wl_evaluate (c1,s)) in
        if res = NONE then wl_evaluate (c2,s1) else (res,s1)) /\
   (wl_evaluate (wl_Return n ms, s) =
      match (wl_get_var n s, wl_get_vars ms s) with
        (SOME (wl_Loc l1 l2), SOME ys) ->
          (SOME (wl_Result (wl_Loc l1 l2) ys), wl_flush_state F s)
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Raise n, s) =
      match wl_get_var n s with
        NONE -> (SOME wl_Error, s)
      | SOME w ->
          (match wl_jump_exc s with
             NONE -> (SOME wl_Error, s)
           | SOME (s,l1,l2) -> (SOME (wl_Exception (wl_Loc l1 l2) w), s))) /\
   (wl_evaluate (wl_Break k, s) = (SOME (wordSem_Break k), s)) /\
   (wl_evaluate (wl_Continue k, s) = (SOME (wordSem_Continue k), s)) /\
   (wl_evaluate (wl_If cmp r1 ri c1 c2, s) =
      match (wl_get_var r1 s, wl_get_var_imm ri s) with
        (SOME x, SOME y) ->
          (match wl_word_cmp cmp x y with
             SOME b -> if b then wl_evaluate (c1,s) else wl_evaluate (c2,s)
           | NONE -> (SOME wl_Error, s))
      | _ -> (SOME wl_Error, s))`;
  `wl_evaluate (wl_Loop names c exit_names:(A)wl_prog, s:(A,C,FFI)wl_state) =
     match wl_cut_state (names,LN) s with
       NONE -> (SOME (wl_Error:(A)wl_result), s)
     | SOME s ->
         let (res,s1) = wl_fix_clock s (wl_evaluate (c,s)) in
           if wl_cont_loop res then
             (if wl_state_clock s1 = 0 then
                (SOME wl_TimeOut, wl_flush_state T s1)
              else
                wl_evaluate (wl_STOP (wl_Loop names c exit_names), wl_dec_clock s1))
           else if res = SOME (wordSem_Break 0) then
             (match wl_cut_state (exit_names,LN) s1 with
                NONE -> (SOME wl_Error, s1)
              | SOME s2 -> (NONE, s2))
           else (wl_exit_loop res, s1)`;
  `(wl_evaluate (wl_LocValue r l1:(A)wl_prog, s:(A,C,FFI)wl_state) =
      if l1 IN domain (wl_state_code s) then
        (NONE:((A)wl_result)option, wl_set_var r (wl_Loc l1 0) s)
      else (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Install ptr len dptr dlen names, s) =
      match wl_cut_env names (wl_state_locals s) with
        NONE -> (SOME wl_Error, s)
      | SOME env ->
      match (wl_get_var ptr s, wl_get_var len s, wl_get_var dptr s,
             wl_get_var dlen s) with
        (SOME (wl_Word w1), SOME (wl_Word w2), SOME (wl_Word w3),
         SOME (wl_Word w4)) ->
          let (cfg,progs) = wl_state_compile_oracle s 0 in
          (match (buffer_flush (wl_state_code_buffer s) w1 w2,
                  buffer_flush (wl_state_data_buffer s) w3 w4) with
             (SOME (bytes, cb), SOME (data, db)) ->
               let new_oracle = shift_seq 1 (wl_state_compile_oracle s) in
               (match (wl_state_compile s cfg progs, progs) with
                  (SOME (bytes',data',cfg'), CONS (k,prog) _) ->
                    if bytes = bytes' /\ data = data' /\ FST (new_oracle 0) = cfg'
                    then
                      let s' =
                        wl_state_code_buffer_fupd (combin_K cb)
                         (wl_state_data_buffer_fupd (combin_K db)
                          (wl_state_code_fupd
                             (combin_K (sptree_union (wl_state_code s) (fromAList progs)))
                           (wl_state_locals_fupd (combin_K (insert ptr (wl_Loc k 0) env))
                            (wl_state_fp_regs_fupd (combin_K FEMPTY)
                             (wl_state_compile_oracle_fupd (combin_K new_oracle)
                              (wl_state_stack_max_fupd (combin_K NONE)
                               (wl_state_stack_size_fupd (combin_K LN) s))))))) in
                        (NONE, s')
                    else (SOME wl_Error, s)
                | _ -> (SOME wl_Error, s))
           | _ -> (SOME wl_Error, s))
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_CodeBufferWrite r1 r2, s) =
      match (wl_get_var r1 s, wl_get_var r2 s) with
        (SOME (wl_Word w1), SOME (wl_Word w2)) ->
          (match buffer_write (wl_state_code_buffer s) w1 (word_zx w2) with
             SOME new_cb -> (NONE, wl_state_code_buffer_fupd (combin_K new_cb) s)
           | _ -> (SOME wl_Error, s))
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_DataBufferWrite r1 r2, s) =
      match (wl_get_var r1 s, wl_get_var r2 s) with
        (SOME (wl_Word w1), SOME (wl_Word w2)) ->
          (match buffer_write (wl_state_data_buffer s) w1 w2 with
             SOME new_db -> (NONE, wl_state_data_buffer_fupd (combin_K new_db) s)
           | _ -> (SOME wl_Error, s))
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_FFI ffi_index ptr1 len1 ptr2 len2 names, s) =
      match (wl_get_var len1 s, wl_get_var ptr1 s, wl_get_var len2 s,
             wl_get_var ptr2 s) with
        (SOME (wl_Word w), SOME (wl_Word w2), SOME (wl_Word w3),
         SOME (wl_Word w4)) ->
          (match wl_cut_env names (wl_state_locals s) with
             NONE -> (SOME wl_Error, s)
           | SOME env ->
               (match (read_bytearray w2 (val w)
                         (mem_load_byte_aux (wl_state_memory s) (wl_state_mdomain s)
                                            (wl_state_be s)),
                       read_bytearray w4 (val w3)
                         (mem_load_byte_aux (wl_state_memory s) (wl_state_mdomain s)
                                            (wl_state_be s))) with
                  (SOME bytes, SOME bytes2) ->
                    (match call_FFI (wl_state_ffi s) (ExtCall ffi_index) bytes bytes2 with
                       FFI_final outcome ->
                         (SOME (wl_FinalFFI outcome), wl_flush_state T s)
                     | FFI_return new_ffi new_bytes ->
                         let new_m = write_bytearray w4 new_bytes (wl_state_memory s)
                                       (wl_state_mdomain s) (wl_state_be s) in
                           (NONE, wl_state_memory_fupd (combin_K new_m)
                                    (wl_state_locals_fupd (combin_K env)
                                       (wl_state_fp_regs_fupd (combin_K FEMPTY)
                                          (wl_state_ffi_fupd (combin_K new_ffi) s)))))
                | _ -> (SOME wl_Error, s)))
      | res -> (SOME wl_Error, s)) /\
   (wl_evaluate (ShareInst op v exp, s) =
      match wl_word_exp s exp with
        SOME (wl_Word ad) -> share_inst op v ad s
      | _ -> (SOME wl_Error, s)) /\
   (wl_evaluate (wl_Call ret dest args handler, s) =
      match wl_get_vars args s with
        NONE -> (SOME wl_Error, s)
      | SOME xs ->
        if bad_dest_args dest args then (SOME wl_Error, s)
        else
        match wl_find_code dest (add_ret_loc ret xs) (wl_state_code s)
                (wl_state_stack_size s) with
          NONE -> (SOME wl_Error, s)
        | SOME (args1,prog,ss) ->
          match ret with
            NONE ->
              if handler = NONE then
                if wl_state_clock s = 0 then (SOME wl_TimeOut, wl_flush_state T s)
                else
                  (match wl_evaluate (prog, wl_call_env args1 ss (wl_dec_clock s)) with
                     (res,s) ->
                       if wl_bad_fun_return res then (SOME wl_Error, s)
                       else (res,s))
              else (SOME wl_Error, s)
          | SOME (n,names,ret_handler,l1,l2) ->
              if domain (FST names) = {} \/ ~ALL_DISTINCT n then (SOME wl_Error, s)
              else
                (match cut_envs names (wl_state_locals s) with
                   NONE -> (SOME wl_Error, s)
                 | SOME envs ->
                   if wl_state_clock s = 0 then
                     (SOME wl_TimeOut,
                      wl_flush_state T
                        (wl_state_stack_fupd (combin_K [])
                           (wl_state_stack_max_fupd
                              (combin_K (wl_state_stack_max
                                    (wl_call_env args1 ss (wl_push_env envs handler s))))
                              s)))
                   else
                     (match wl_fix_clock
                              (wl_call_env args1 ss
                                 (wl_push_env envs handler (wl_dec_clock s)))
                              (wl_evaluate (prog, wl_call_env args1 ss
                                 (wl_push_env envs handler (wl_dec_clock s)))) with
                        (SOME (wl_Result x ys), s2) ->
                          if ~(x = wl_Loc l1 l2) \/ ~(LENGTH ys = LENGTH n)
                          then (SOME wl_Error, s2)
                          else
                            (match wl_pop_env s2 with
                               NONE -> (SOME wl_Error, s2)
                             | SOME s1 ->
                                 (if domain (wl_state_locals s1) =
                                     domain (FST envs) UNION domain (SND envs)
                                  then wl_evaluate (ret_handler, wl_set_vars n ys s1)
                                  else (SOME wl_Error, s1)))
                      | (SOME (wl_Exception x y), s2) ->
                          (match handler with
                             NONE -> (SOME (wl_Exception x y), s2)
                           | SOME (n,h,l1,l2) ->
                               if ~(x = wl_Loc l1 l2) then (SOME wl_Error, s2)
                               else
                                 (if domain (wl_state_locals s2) =
                                     domain (FST envs) UNION domain (SND envs)
                                  then wl_evaluate (h, wl_set_var n y s2)
                                  else (SOME wl_Error, s2)))
                      | (NONE, s) -> (SOME wl_Error, s)
                      | (SOME (wordSem_Break _), s) -> (SOME wl_Error, s)
                      | (SOME (wordSem_Continue _), s) -> (SOME wl_Error, s)
                      | res -> res)))`];;

(* HOL4 evaluate_def (the first one, with fix_clock), made with             *)
(* sem1aux_def_wf (about 9 minutes)                                         *)

let IL2AUX_evaluate_fix_def =
  sem1aux_def_wf IL2AUX_evaluate_rel IL2AUX_TC_TAC IL2AUX_evaluate_clauses;;

(* HOL4 evaluate_ind (the first one, with fix_clock) *)

let IL2AUX_evaluate_fix_ind = cake_ind "wl_evaluate";;

(* We prove that the clock never increases and that termdep is constant. *)

let IL2AUX_flush_state_clock = prove
 (`!b (s:(A,C,FFI)wl_state).
     wl_state_clock (wl_flush_state b s) = wl_state_clock s /\
     wl_state_termdep (wl_flush_state b s) = wl_state_termdep s`,
  REWRITE_TAC[FORALL_BOOL_THM; wl_flush_state_def] THEN SIMP[]);;

let IL2AUX_set_store_clock = prove
 (`!v x (s:(A,C,FFI)wl_state).
     wl_state_clock (wl_set_store v x s) = wl_state_clock s /\
     wl_state_termdep (wl_set_store v x s) = wl_state_termdep s`,
  REWRITE_TAC[wl_set_store_def] THEN SIMP[]);;

let wl_gc_clock = prove
 (`!s1 s2. wl_gc (s1:(A,C,FFI)wl_state) = SOME s2
           ==> wl_state_clock s2 <= wl_state_clock s1 /\
               wl_state_termdep s2 = wl_state_termdep s1`,
  REWRITE_TAC[wl_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let wl_alloc_clock = prove
 (`!(xs:B) (s1:(A,C,FFI)wl_state) vs s2.
     wl_alloc x names s1 = (vs,s2)
     ==> wl_state_clock s2 <= wl_state_clock s1 /\
         wl_state_termdep s2 = wl_state_termdep s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP wl_gc_clock)) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP IL2AUX_pop_env_clock_termdep)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IL2AUX_flush_state_clock; IL2AUX_set_store_clock;
                              wl_push_env_clock; IL2AUX_push_env_termdep]) THEN
  ASM_REWRITE_TAC[IL2AUX_flush_state_clock; IL2AUX_set_store_clock;
                  wl_push_env_clock; IL2AUX_push_env_termdep; LE_REFL] THEN
  ASM_ARITH_TAC);;

let sh_mem_set_var_clock = prove
 (`!v (s1:(A,C,FFI)wl_state) (v2:((W)wl_result)option) s2 res.
     sh_mem_set_var res v s1 = (v2,s2)
     ==> wl_state_clock s2 <= wl_state_clock s1 /\
         wl_state_termdep s2 = wl_state_termdep s1`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `res:((FFI)ffi_result)option` (cases "option")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[wl_set_var_def; IL2AUX_flush_state_clock] THEN SIMP[]);;

(* HOL4 quantifies v1 and leaves v2 free *)

let share_inst_clock = prove
 (`!op v ad (s1:(A,C,FFI)wl_state) (v1:B) s2.
     share_inst op v ad s1 = (v2:((W)wl_result)option,s2)
     ==> wl_state_clock s2 <= wl_state_clock s1 /\
         wl_state_termdep s2 = wl_state_termdep s1`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def] THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(ACCEPT_TAC o MATCH_MP sh_mem_set_var_clock)) THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
              wl_sh_mem_store16_def; wl_sh_mem_store32_def; PAIR_EQ] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[IL2AUX_flush_state_clock] THEN SIMP[]);;

(* HOL4 [local] *)

let wl_inst_clock = prove
 (`wl_inst i (s:(A,C,FFI)wl_state) = SOME s2
   ==> wl_state_clock s2 <= wl_state_clock s /\
       wl_state_termdep s2 = wl_state_termdep s`,
  REWRITE_TAC[wl_inst_def; wl_assign_def; wl_mem_store_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  TRY(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[wl_set_var_def; wl_set_fp_var_def] THEN SIMP[]);;


(* the proof of evaluate_clock: the clock facts of the helpers, then the    *)
(* induction hypotheses instantiated at the evaluate assumptions            *)

let IL2AUX_mem_store_clock = prove
 (`wl_mem_store a w (s:(A,C,FFI)wl_state) = SOME s1
   ==> wl_state_clock s1 = wl_state_clock s /\
       wl_state_termdep s1 = wl_state_termdep s`,
  REWRITE_TAC[wl_mem_store_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let IL2AUX_jump_exc_clock = prove
 (`wl_jump_exc (s:(A,C,FFI)wl_state) = SOME (s1,l1,l2)
   ==> wl_state_clock s1 = wl_state_clock s /\
       wl_state_termdep s1 = wl_state_termdep s`,
  REWRITE_TAC[wl_jump_exc_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN SIMP[]);;

let IL2AUX_clock_case_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["word_loc"; "wl_result"; "ffi_result"];;

let IL2AUX_is_eval_eq tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "wl_evaluate"
   with Failure _ -> false);;

(* prove ?vs. A1 /\ ... /\ An from the assumptions: each existential      *)
(* variable is found by matching a conjunct with an assumption (or the two *)
(* sides of an equation), the instantiated conjunction is proved by        *)
(* rewriting with the assumptions                                          *)

let IL2AUX_EXISTS_ASM_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let facts = map (concl o snd) asl in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let fvs = filter (fun v -> mem v vs && not (can (rev_assoc v) theta))
                         (frees c') in
        if fvs = [] then go theta rest else
        let try_m p t =
          let (_,tmi,tyi) = term_match [] p t in
          if forall (fun (t,v) -> mem v fvs || t = v) tmi &&
             forall (fun (a,b) -> a = b) tyi
          then filter (fun (t,v) -> mem v fvs) tmi else failwith "" in
        let tmi = try tryfind (try_m c') facts
                  with Failure _ ->
                    try let l,r = dest_eq c' in
                        (try try_m r l with Failure _ -> try_m l r)
                    with Failure _ -> [] in
        go (tmi @ theta) rest in
  let theta = go [] (conjuncts body) in
  let wits = map (fun v -> try rev_assoc v theta with Failure _ -> v) vs in
  (MAP_EVERY EXISTS_TAC wits THEN ASM_REWRITE_TAC[]) g;;

(* for every assumption wl_evaluate p = (v,t) and every induction          *)
(* hypothesis !xs. ... /\ wl_evaluate p' = (vs,s2) /\ ... ==> C (after      *)
(* IMP_IMP) whose evaluate antecedent matches it, add the instance of C    *)
(* when its other antecedents follow from the assumptions                  *)

let IL2AUX_USE_IHS_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> IL2AUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists IL2AUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
  let inst_of ih0 e =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = GENL vs1 (SPECL vs1 ih0) in
    let vs,bod = strip_forall (concl ih) in
    let ant,_ = dest_imp bod in
    let cj = find IL2AUX_is_eval_eq (conjuncts ant) in
    let (_,tmi,tyi) = term_match [] cj (concl e) in
    if exists (fun (a,b) -> not (a = b)) tyi ||
       exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi then failwith "" else
    let ihi = INST tmi (SPEC_ALL ih) in
    let a,c = dest_imp (concl ihi) in
    let rest = filter (fun v -> mem v vs) (subtract (frees a) (frees c)) in
    c, GENL rest ihi in
  let insts = flat (map (fun e -> mapfilter (fun ih -> inst_of ih e) ihs) evs) in
  MAP_EVERY (fun (c,th) ->
      TRY (SUBGOAL_THEN c STRIP_ASSUME_TAC THENL
            [MATCH_MP_TAC th THEN IL2AUX_EXISTS_ASM_TAC THEN NO_TAC; ALL_TAC]))
    insts g;;

let IL2AUX_CLOCK_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[IL2AUX_evaluate_fix_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_USE_IHS_TAC THEN
  MAP_EVERY (fun th -> REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL o MATCH_MP th)))
    [fix_clock_IMP_LESS_EQ; IL2AUX_pop_env_clock_termdep;
     IL2AUX_cut_state_clock_termdep; IL2AUX_mem_store_clock;
     IL2AUX_jump_exc_clock; wl_inst_clock; wl_alloc_clock; share_inst_clock] THEN
  (fun g -> let ths = IL2AUX_clock_rws @
                      [IL2AUX_flush_state_clock; IL2AUX_set_store_clock;
                       wl_unset_var_def] in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* the If case (the boolean of the comparison is a context of the IHs) *)

let IL2AUX_CLOCK_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IL2AUX_evaluate_fix_def] THEN
  REWRITE_TAC[option_case_eq; COND_CASE_EQ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[];;

let IL2AUX_evaluate_clock = prove
 (`!p vs (s2:(A,C,FFI)wl_state).
     wl_evaluate p = (vs,s2)
     ==> wl_state_clock s2 <= wl_state_clock (SND p) /\
         wl_state_termdep s2 = wl_state_termdep (SND p)`,
  MATCH_MP_TAC IL2AUX_evaluate_fix_ind THEN REWRITE_TAC[SND] THEN
  REPEAT CONJ_TAC THEN FIRST [IL2AUX_CLOCK_TAC; IL2AUX_CLOCK_IF_TAC]);;

let wl_evaluate_clock = prove
 (`!xs (s1:(A,C,FFI)wl_state) vs s2.
     wl_evaluate (xs,s1) = (vs,s2)
     ==> wl_state_clock s2 <= wl_state_clock s1 /\
         wl_state_termdep s2 = wl_state_termdep s1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP IL2AUX_evaluate_clock) THEN
  REWRITE_TAC[SND]);;

let IL2AUX_fix_clock_id = prove
 (`!(s:(A,C,FFI)wl_state) (x:B#(A,C,FFI)wl_state).
     wl_state_clock (SND x) <= wl_state_clock s /\
     wl_state_termdep (SND x) = wl_state_termdep s
     ==> wl_fix_clock s x = x`,
  REWRITE_TAC[FORALL_PAIR_THM; wl_fix_clock_def; PAIR_EQ; SND] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN
  SIMP[] THEN ASM_ARITH_TAC);;

(* HOL4 [local] *)

let wl_fix_clock_evaluate = prove
 (`wl_fix_clock (s:(A,C,FFI)wl_state) (wl_evaluate (c1,s)) = wl_evaluate (c1,s)`,
  MATCH_MP_TAC IL2AUX_fix_clock_id THEN
  MP_TAC(ISPEC `wl_evaluate (c1:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND] THEN
  MATCH_MP_TAC wl_evaluate_clock THEN ASM_MESON_TAC[]);;

(* We store the theorems without fix_clock *)

(* HOL4: evaluate_ind[allow_rebind] = REWRITE_RULE [fix_clock_evaluate]     *)
(* evaluate_ind *)

let wl_evaluate_ind = REWRITE_RULE[wl_fix_clock_evaluate] IL2AUX_evaluate_fix_ind;;

(* HOL4: evaluate_def[allow_rebind] = REWRITE_RULE [fix_clock_evaluate]     *)
(* evaluate_def *)

let wl_evaluate_def = REWRITE_RULE[wl_fix_clock_evaluate] IL2AUX_evaluate_fix_def;;

let () = cake_ind_store := ("wl_evaluate",wl_evaluate_ind) :: !cake_ind_store;;

(* observational semantics *)

let wl_semantics_def = cake_def
  `wl_semantics (s:(A,C,FFI)wl_state) start =
     let prog = wl_Call NONE (SOME start) [0] NONE in
     if ?k. match FST (wl_evaluate (prog, wl_state_clock_fupd (combin_K k) s)) with
              SOME (wl_Exception _ _) -> T
            | SOME (wl_Result ret _) -> ~(ret = wl_Loc 1 0)
            | SOME wl_Error -> T
            | NONE -> T
            | _ -> F
     then Fail
     else
       match (some res.
                ?k t r outcome.
                  wl_evaluate (prog, wl_state_clock_fupd (combin_K k) s) = (r,t) /\
                  (match r with
                     SOME (wl_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (wl_Result _ _) -> outcome = Success
                   | SOME NotEnoughSpace -> outcome = Resource_limit_hit
                   | _ -> F) /\
                  res = Terminate outcome (ffi_state_io_events (wl_state_ffi t))) with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (wl_state_ffi
                                    (SND (wl_evaluate
                                            (prog, wl_state_clock_fupd (combin_K k) s))))))
                       (:num)))`;;

let word_lang_safe_for_space_def = cake_def
  `word_lang_safe_for_space (s:(A,C,FFI)wl_state) start <=>
     let prog = wl_Call NONE (SOME start) [0] NONE in
       !k res t.
         wl_evaluate (prog, wl_state_clock_fupd (combin_K k) s) = (res,t)
         ==> ?max'. wl_state_stack_max t = SOME max' /\
                    max' <= wl_state_stack_limit t`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let IL2AUX_evaluate_Seq_NONE = prove
 (`!c1 c2 (s:(A,C,FFI)wl_state) s1.
     wl_evaluate (c1,s) = (NONE,s1) ==> wl_evaluate (wl_Seq c1 c2,s) = wl_evaluate (c2,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]);;
