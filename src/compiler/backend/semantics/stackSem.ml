(* ========================================================================= *)
(* stackSem: port of HOL4 compiler/backend/semantics/stackSemScript.sml      *)
(* (CakeML v3479).                                                           *)
(* The formal semantics of stackLang.                                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/llist.ml";;
needs "hol4/lprefix_lub.ml";;
needs "hol4/machine_ieee.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - The record state is stack_state (type variables A, C and FFI, HOL4 'a, *)
(*   'c and 'ffi); HOL4 s.f is stack_state_f s, s with f := v is             *)
(*   stack_state_f_fupd (K v) s and s with <| f1 := x; f2 := y |> is         *)
(*   stack_state_f1_fupd (K x) (stack_state_f2_fupd (K y) s). The result    *)
(*   type is stack_result (type variable W, HOL4 'w).                        *)
(* - HOL4 Type gc_fun_type (wordSem) is written out in the field gc_fun.     *)
(* - wordSem$word_cmp is wl_word_cmp; the word_loc constructors are wl_Word *)
(*   and wl_Loc; HOL4 word_shift (:'a) is backend_common_word_shift (:A).   *)
(* - Words: n2w = word, w2n = val, w2w = word_zx, w2i = ival, i2w = iword,   *)
(*   >>> = word_ushr, << = word_shl, w ' i = bit i w, / = word_jdiv,         *)
(*   (h >< l) = word_extract h l, @@ = word_join, bit_field_insert h l a w = *)
(*   word_insert w (l,(h + 1) - l) a; word8 = byte, word32 = int32, word64 = *)
(*   int64.                                                                  *)
(* - Finite maps: |+ is FUPDATE (infix |+), \\ is DOMSUB, DRESTRICT,         *)
(*   FEMPTY and FLOOKUP as in hol4/finite_map.ml; num_map is spt.           *)
(* - HOL4 GENLIST is list_of_seq, EVERY is ALL, FOLDR f e l is ITLIST f l e. *)
(* - HOL4 a + b + c on numbers is (a + b) + c, written with parentheses      *)
(*   (HOL Light's + is right associative).                                   *)

let stack_result_INDUCT,stack_result_RECURSION = cake_type
  "stack_result = stack_Result ((W)word_loc)
                | stack_Exception ((W)word_loc)
                | stackSem_Break num
                | stackSem_Continue num
                | stackSem_Halt ((W)word_loc)
                | stack_TimeOut
                | stack_FinalFFI final_event
                | stack_Error";;

(* HOL4 proves termination automatically: val w decreases *)

let bit_length_def = cake_def_wf
  `measure (val:A word->num)`
  (REWRITE_TAC[measure_THM; VAL_WORD_USHR; EXP_1] THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~(val (w:A word) = 0)` MP_TAC THENL
    [ASM_REWRITE_TAC[VAL_EQ_0]; ARITH_TAC])
  `bit_length (w:A word) =
     if w = word 0 then 0 else bit_length (word_ushr w 1) + 1`;;

let bit_length_ind = cake_ind "bit_length";;

(* filter_bitmap and map_bitmap: HOL4 matches the booleans T and F in the  *)
(* clauses; the kit does not complete clauses with literal patterns, so the *)
(* functions are defined with a conditional (STACKPAUX_..._DEF) and the     *)
(* HOL4 clauses, completed as HOL4's TFL does, and induction theorems are   *)
(* proved from it                                                            *)

let STACKPAUX_filter_bitmap_DEF = cake_def
  `(filter_bitmap [] (rs:A list) = SOME ([]:A list,rs)) /\
   (filter_bitmap (CONS b bs) rs =
      match rs with
        [] -> NONE
      | CONS r rs ->
          if b then
            (match filter_bitmap bs rs with
               NONE -> NONE
             | SOME (ts,rs') -> SOME (CONS r ts,rs'))
          else filter_bitmap bs rs)`;;

let filter_bitmap_def = prove
 (CASE_TERM
  `(!rs:A list. filter_bitmap [] rs = SOME ([],rs)) /\
   (!bs (r:A) rs. filter_bitmap (CONS F bs) (CONS r rs) = filter_bitmap bs rs) /\
   (!bs (r:A) rs.
      filter_bitmap (CONS T bs) (CONS r rs) =
      match filter_bitmap bs rs with
        NONE -> NONE
      | SOME (ts,rs') -> SOME (CONS r ts,rs')) /\
   (!v6. filter_bitmap (CONS F v6) ([]:A list) = NONE) /\
   (!v6. filter_bitmap (CONS T v6) ([]:A list) = NONE)`,
  REWRITE_TAC[STACKPAUX_filter_bitmap_DEF; list_CASE]);;

let filter_bitmap_ind = prove
 (`!P:bool list->A list->bool.
     (!rs. P [] rs) /\
     (!bs r rs. P bs rs ==> P (CONS F bs) (CONS r rs)) /\
     (!bs r rs. P bs rs ==> P (CONS T bs) (CONS r rs)) /\
     (!v6. P (CONS F v6) []) /\
     (!v6. P (CONS T v6) [])
     ==> !v v1. P v v1`,
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  LIST_INDUCT_TAC THEN BOOL_CASES_TAC `h:bool` THEN ASM_MESON_TAC[]);;

let STACKPAUX_map_bitmap_DEF = cake_def
  `(map_bitmap [] (ts:A list) rs = SOME ([]:A list,ts,rs)) /\
   (map_bitmap (CONS b bs) ts rs =
      if b then
        (match ts with
           [] -> NONE
         | CONS t ts ->
             (match rs with
                [] -> NONE
              | CONS r rs ->
                  (match map_bitmap bs ts rs with
                     NONE -> NONE
                   | SOME (xs,ys,zs) -> SOME (CONS t xs,ys,zs))))
      else
        (match rs with
           [] -> NONE
         | CONS r rs ->
             (match map_bitmap bs ts rs with
                NONE -> NONE
              | SOME (xs,ys,zs) -> SOME (CONS r xs,ys,zs))))`;;

let map_bitmap_def = prove
 (CASE_TERM
  `(!ts rs:A list. map_bitmap [] ts rs = SOME ([],ts,rs)) /\
   (!bs ts (r:A) rs.
      map_bitmap (CONS F bs) ts (CONS r rs) =
      match map_bitmap bs ts rs with
        NONE -> NONE
      | SOME (xs,ys,zs) -> SOME (CONS r xs,ys,zs)) /\
   (!bs (t:A) ts r rs.
      map_bitmap (CONS T bs) (CONS t ts) (CONS r rs) =
      match map_bitmap bs ts rs with
        NONE -> NONE
      | SOME (xs,ys,zs) -> SOME (CONS t xs,ys,zs)) /\
   (!v8 v7:A list. map_bitmap (CONS F v8) v7 [] = NONE) /\
   (!v10 v9:A list. map_bitmap (CONS T v10) [] v9 = NONE) /\
   (!v10 (v13:A) v14. map_bitmap (CONS T v10) (CONS v13 v14) [] = NONE)`,
  REWRITE_TAC[STACKPAUX_map_bitmap_DEF; list_CASE]);;

let map_bitmap_ind = prove
 (`!P:bool list->A list->A list->bool.
     (!ts rs. P [] ts rs) /\
     (!bs ts r rs. P bs ts rs ==> P (CONS F bs) ts (CONS r rs)) /\
     (!bs t ts r rs. P bs ts rs ==> P (CONS T bs) (CONS t ts) (CONS r rs)) /\
     (!v8 v7. P (CONS F v8) v7 []) /\
     (!v10 v9. P (CONS T v10) [] v9) /\
     (!v10 v13 v14. P (CONS T v10) (CONS v13 v14) [])
     ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `h:bool` THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_MESON_TAC[]);;

let filter_bitmap_LENGTH = prove
 (`!bs (xs:A list) x y. filter_bitmap bs xs = SOME (x,y) ==> LENGTH y <= LENGTH xs`,
  MATCH_MP_TAC filter_bitmap_ind THEN REWRITE_TAC[filter_bitmap_def] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; LENGTH] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[LE_REFL];
    RES_TAC THEN ASM_ARITH_TAC;
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN RES_TAC THEN ASM_ARITH_TAC]);;

let map_bitmap_LENGTH = prove
 (`!t1 (t2:A list) t3 x y z.
     map_bitmap t1 t2 t3 = SOME (x,y,z) ==>
     LENGTH y <= LENGTH t2 /\ LENGTH z <= LENGTH t3`,
  MATCH_MP_TAC map_bitmap_ind THEN REWRITE_TAC[map_bitmap_def] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; LENGTH] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST [REWRITE_TAC[LE_REFL] THEN NO_TAC;
         POP_ASSUM MP_TAC THEN
         REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ;
                     PAIR_EQ] THEN
         STRIP_TAC THEN RVEQ_TAC THEN RES_TAC THEN ASM_ARITH_TAC]);;

(* if word_msb w, there is a continuation; else this is the last bitmap    *)
(* word                                                                       *)

let read_bitmap_def = cake_def
  `(read_bitmap [] = NONE:(bool list)option) /\
   (read_bitmap (CONS (w:A word) ws) =
      if word_msb w then
        (match read_bitmap ws with
           NONE -> NONE
         | SOME bs -> SOME (APPEND (list_of_seq (\i. bit i w) (dimindex(:A) - 1)) bs))
      else SOME (list_of_seq (\i. bit i w) (bit_length w - 1)))`;;

(* HOL4: state; be: is big-endian *)

let stack_state_INFO = cake_record "stack_state"
  ["regs","(num,(A)word_loc)fmap";
   "fp_regs","(num,int64)fmap";
   "store","(store_name,(A)word_loc)fmap";
   "stack","((A)word_loc)list";
   "stack_space","num";
   "memory","A word->(A)word_loc";
   "mdomain","A word->bool";
   "sh_mdomain","A word->bool";
   "bitmaps","(A word)list";
   "compile","C->(num#(A)stack_prog)list->(byte list#C)option";
   "compile_oracle","num->C#(num#(A)stack_prog)list#(A word)list";
   "code_buffer","(A,8)buffer";
   "data_buffer","(A,A)buffer";
   "gc_fun","(((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
              (store_name,(A)word_loc)fmap)->
             (((A)word_loc)list#(A word->(A)word_loc)#
              (store_name,(A)word_loc)fmap)option";
   "use_stack","bool";
   "use_store","bool";
   "use_alloc","bool";
   "clock","num";
   "code","((A)stack_prog)spt";
   "ffi","(FFI)ffi_state";
   "ffi_save_regs","num->bool";
   "be","bool"];;

let stack_state_component_equality = stack_state_INFO.ri_component_equality;;

(* HOL4: mem_store_def, mem_load_def, dec_clock_def *)

let stack_mem_store_def = cake_def
  `stack_mem_store (addr:A word) (w:(A)word_loc) (s:(A,C,FFI)stack_state) =
     if addr IN stack_state_mdomain s then
       SOME (stack_state_memory_fupd (K ((addr =+ w) (stack_state_memory s))) s)
     else NONE`;;

let stack_mem_load_def = cake_def
  `stack_mem_load (addr:A word) (s:(A,C,FFI)stack_state) =
     if addr IN stack_state_mdomain s then SOME (stack_state_memory s addr)
     else NONE`;;

let stack_dec_clock_def = cake_def
  `stack_dec_clock (s:(A,C,FFI)stack_state) =
     stack_state_clock_fupd (K (stack_state_clock s - 1)) s`;;

(* HOL4: word_exp_def; Termination WF_REL_TAC measure (exp_size ARB o SND) *)

let stack_word_exp_def = cake_def_wf
  `measure (\p:(A,C,FFI)stack_state#(A)wl_exp. wl_exp_size (\x:A. 0) (SND p))`
  TERM_TAC
  `(stack_word_exp (s:(A,C,FFI)stack_state) (wl_Const w) = SOME w) /\
   (stack_word_exp s (wl_Var v) =
      match FLOOKUP (stack_state_regs s) v with
        SOME (wl_Word w) -> SOME w
      | _ -> NONE) /\
   (stack_word_exp s (Lookup name) =
      match FLOOKUP (stack_state_store s) name with
        SOME (wl_Word w) -> SOME w
      | _ -> NONE) /\
   (stack_word_exp s (wl_Load addr) =
      match stack_word_exp s addr with
        SOME w -> (match stack_mem_load w s with
                     SOME (wl_Word w) -> SOME w
                   | _ -> NONE)
      | _ -> NONE) /\
   (stack_word_exp s (wl_Op op wexps) =
      let ws = MAP (stack_word_exp s) wexps in
      if ALL IS_SOME ws then word_op op (MAP THE ws) else NONE) /\
   (stack_word_exp s (wl_Shift sh wexp wexp1) =
      match (stack_word_exp s wexp,stack_word_exp s wexp1) with
        (SOME w,SOME w1) -> word_sh sh w (val w1)
      | _ -> NONE)`;;

(* HOL4's word_exp_ind (the kit's cake_ind "stack_word_exp" has the weaker *)
(* hypothesis stack_word_exp s wexp = SOME w ==> P s wexp1 for Shift, as the *)
(* match on the pair is compiled into nested cases): structural induction,  *)
(* as wl_word_exp_ind of wordSem.ml                                          *)

let stack_word_exp_ind = prove
 (`!P:(A,C,FFI)stack_state->(A)wl_exp->bool.
       (!s w. P s (wl_Const w)) /\
       (!s v. P s (wl_Var v)) /\
       (!s name. P s (Lookup name)) /\
       (!s addr. P s addr ==> P s (wl_Load addr)) /\
       (!s op wexps. (!a. MEM a wexps ==> P s a) ==> P s (wl_Op op wexps)) /\
       (!s sh wexp wexp1. P s wexp /\ P s wexp1 ==> P s (wl_Shift sh wexp wexp1))
       ==> !v v1. P v v1`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:(A,C,FFI)stack_state` THEN
  MP_TAC(ISPECL [`\e:(A)wl_exp. P (v:(A,C,FFI)stack_state) e:bool`;
                 `\l:((A)wl_exp)list. !a. MEM a l ==> P (v:(A,C,FFI)stack_state) a`]
                wl_exp_INDUCT) THEN
  REWRITE_TAC[MEM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[]; SIMP_TAC[]]);;

(* HOL4: get_var_def, get_vars_def, get_fp_var_def, set_var_def,          *)
(* set_fp_var_def, set_store_def, empty_env_def                             *)

let stack_get_var_def = cake_def
  `stack_get_var v (s:(A,C,FFI)stack_state) = FLOOKUP (stack_state_regs s) v`;;

let stack_get_vars_def = cake_def
  `(stack_get_vars [] (s:(A,C,FFI)stack_state) = SOME []) /\
   (stack_get_vars (CONS v vs) s =
      match stack_get_var v s with
        NONE -> NONE
      | SOME x -> (match stack_get_vars vs s with
                     NONE -> NONE
                   | SOME xs -> SOME (CONS x xs)))`;;

let stack_get_fp_var_def = cake_def
  `stack_get_fp_var v (s:(A,C,FFI)stack_state) = FLOOKUP (stack_state_fp_regs s) v`;;

let stack_set_var_def = cake_def
  `stack_set_var v x (s:(A,C,FFI)stack_state) =
     stack_state_regs_fupd (K (stack_state_regs s |+ (v,x))) s`;;

let stack_set_fp_var_def = cake_def
  `stack_set_fp_var v x (s:(A,C,FFI)stack_state) =
     stack_state_fp_regs_fupd (K (stack_state_fp_regs s |+ (v,x))) s`;;

let stack_set_store_def = cake_def
  `stack_set_store v x (s:(A,C,FFI)stack_state) =
     stack_state_store_fupd (K (stack_state_store s |+ (v,x))) s`;;

let stack_empty_env_def = cake_def
  `stack_empty_env (s:(A,C,FFI)stack_state) =
     stack_state_regs_fupd (K FEMPTY) (stack_state_stack_fupd (K []) s)`;;

(* HOL4: sh_mem_store_def ... sh_mem_load32_def *)

let stack_sh_mem_store_def = cake_def
  `stack_sh_mem_store r (a:A word) (s:(A,C,FFI)stack_state) =
     match stack_get_var r s with
       SOME (wl_Word w) ->
         if a IN stack_state_sh_mdomain s then
           (match call_FFI (stack_state_ffi s) (SharedMem MappedWrite) [word 0:byte]
                    (APPEND (word_to_bytes w F) (word_to_bytes a F)) with
              FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
            | FFI_return new_ffi new_bytes -> (NONE,stack_state_ffi_fupd (K new_ffi) s))
         else (SOME stack_Error,s)
     | _ -> (SOME stack_Error,s)`;;

let stack_sh_mem_load_def = cake_def
  `stack_sh_mem_load r (a:A word) (s:(A,C,FFI)stack_state) =
     if a IN stack_state_sh_mdomain s then
       (match call_FFI (stack_state_ffi s) (SharedMem MappedRead) [word 0:byte]
                (word_to_bytes a F) with
          FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
        | FFI_return new_ffi new_bytes ->
            (NONE,
             stack_state_regs_fupd
               (K (stack_state_regs s |+
                   (r,wl_Word (word_of_bytes F (word 0) new_bytes))))
               (stack_state_ffi_fupd (K new_ffi) s)))
     else (SOME stack_Error,s)`;;

let stack_sh_mem_store_byte_def = cake_def
  `stack_sh_mem_store_byte r (a:A word) (s:(A,C,FFI)stack_state) =
     match stack_get_var r s with
       SOME (wl_Word w) ->
         if byte_align a IN stack_state_sh_mdomain s then
           (match call_FFI (stack_state_ffi s) (SharedMem MappedWrite) [word 1:byte]
                    (APPEND [get_byte (word 0) w F] (word_to_bytes a F)) with
              FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
            | FFI_return new_ffi new_bytes -> (NONE,stack_state_ffi_fupd (K new_ffi) s))
         else (SOME stack_Error,s)
     | _ -> (SOME stack_Error,s)`;;

let stack_sh_mem_store16_def = cake_def
  `stack_sh_mem_store16 r (a:A word) (s:(A,C,FFI)stack_state) =
     match stack_get_var r s with
       SOME (wl_Word w) ->
         if byte_align a IN stack_state_sh_mdomain s then
           (match call_FFI (stack_state_ffi s) (SharedMem MappedWrite) [word 2:byte]
                    (APPEND (TAKE 2 (word_to_bytes w F)) (word_to_bytes a F)) with
              FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
            | FFI_return new_ffi new_bytes -> (NONE,stack_state_ffi_fupd (K new_ffi) s))
         else (SOME stack_Error,s)
     | _ -> (SOME stack_Error,s)`;;

let stack_sh_mem_store32_def = cake_def
  `stack_sh_mem_store32 r (a:A word) (s:(A,C,FFI)stack_state) =
     match stack_get_var r s with
       SOME (wl_Word w) ->
         if byte_align a IN stack_state_sh_mdomain s then
           (match call_FFI (stack_state_ffi s) (SharedMem MappedWrite) [word 4:byte]
                    (APPEND (TAKE 4 (word_to_bytes w F)) (word_to_bytes a F)) with
              FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
            | FFI_return new_ffi new_bytes -> (NONE,stack_state_ffi_fupd (K new_ffi) s))
         else (SOME stack_Error,s)
     | _ -> (SOME stack_Error,s)`;;

let stack_sh_mem_load_byte_def = cake_def
  `stack_sh_mem_load_byte r (a:A word) (s:(A,C,FFI)stack_state) =
     if byte_align a IN stack_state_sh_mdomain s then
       (match call_FFI (stack_state_ffi s) (SharedMem MappedRead) [word 1:byte]
                (word_to_bytes a F) with
          FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
        | FFI_return new_ffi new_bytes ->
            (NONE,
             stack_state_regs_fupd
               (K (stack_state_regs s |+
                   (r,wl_Word (word_of_bytes F (word 0) new_bytes))))
               (stack_state_ffi_fupd (K new_ffi) s)))
     else (SOME stack_Error,s)`;;

let stack_sh_mem_load16_def = cake_def
  `stack_sh_mem_load16 r (a:A word) (s:(A,C,FFI)stack_state) =
     if byte_align a IN stack_state_sh_mdomain s then
       (match call_FFI (stack_state_ffi s) (SharedMem MappedRead) [word 2:byte]
                (word_to_bytes a F) with
          FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
        | FFI_return new_ffi new_bytes ->
            (NONE,
             stack_state_regs_fupd
               (K (stack_state_regs s |+
                   (r,wl_Word (word_of_bytes F (word 0) new_bytes))))
               (stack_state_ffi_fupd (K new_ffi) s)))
     else (SOME stack_Error,s)`;;

let stack_sh_mem_load32_def = cake_def
  `stack_sh_mem_load32 r (a:A word) (s:(A,C,FFI)stack_state) =
     if byte_align a IN stack_state_sh_mdomain s then
       (match call_FFI (stack_state_ffi s) (SharedMem MappedRead) [word 4:byte]
                (word_to_bytes a F) with
          FFI_final outcome -> (SOME (stack_FinalFFI outcome:(A)stack_result),s)
        | FFI_return new_ffi new_bytes ->
            (NONE,
             stack_state_regs_fupd
               (K (stack_state_regs s |+
                   (r,wl_Word (word_of_bytes F (word 0) new_bytes))))
               (stack_state_ffi_fupd (K new_ffi) s)))
     else (SOME stack_Error,s)`;;

let sh_mem_op_def = cake_def
  `(sh_mem_op asm_Load r ad (s:(A,C,FFI)stack_state) = stack_sh_mem_load r ad s) /\
   (sh_mem_op asm_Store r ad s = stack_sh_mem_store r ad s) /\
   (sh_mem_op Load8 r ad s = stack_sh_mem_load_byte r ad s) /\
   (sh_mem_op Store8 r ad s = stack_sh_mem_store_byte r ad s) /\
   (sh_mem_op Load16 r ad s = stack_sh_mem_load16 r ad s) /\
   (sh_mem_op Store16 r ad s = stack_sh_mem_store16 r ad s) /\
   (sh_mem_op asm_Load32 r ad s = stack_sh_mem_load32 r ad s) /\
   (sh_mem_op asm_Store32 r ad s = stack_sh_mem_store32 r ad s)`;;

(* HOL4 infers the most general type: the word of the word_loc and the     *)
(* bitmaps may have different sizes                                         *)

let full_read_bitmap_def = cake_def
  `(full_read_bitmap (bitmaps:(A word)list) (wl_Word (w:B word)) =
      if w = word 0 then NONE
      else read_bitmap (DROP (val (word_sub w (word 1))) bitmaps)) /\
   (full_read_bitmap bitmaps _ = NONE)`;;

(* HOL4's TFL stores an induction theorem for this non-recursive definition *)
(* (with one case per completed clause); the kit stores none: it is proved *)

let full_read_bitmap_ind = prove
 (`!P:(A word)list->(B)word_loc->bool.
     (!bitmaps w. P bitmaps (wl_Word w)) /\
     (!bitmaps v1 v2. P bitmaps (wl_Loc v1 v2))
     ==> !v v1. P v v1`,
  REPEAT STRIP_TAC THEN CASES_ON `v1:(B)word_loc` THEN ASM_REWRITE_TAC[]);;

(* HOL4: enc_stack_def; Termination WF_REL_TAC measure (LENGTH o SND), with *)
(* filter_bitmap_LENGTH                                                      *)

let stack_enc_stack_def = cake_def_wf
  `measure (\p:(A word)list#((A)word_loc)list. LENGTH (SND p))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[LENGTH] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP filter_bitmap_LENGTH) THEN ARITH_TAC)
  `(stack_enc_stack (bitmaps:(A word)list) [] = NONE:(((A)word_loc)list)option) /\
   (stack_enc_stack bitmaps (CONS w ws) =
      if w = wl_Word (word 0) then (if ws = [] then SOME [] else NONE) else
        match full_read_bitmap bitmaps w with
          NONE -> NONE
        | SOME bs ->
            (match filter_bitmap bs ws with
               NONE -> NONE
             | SOME (ts,ws') ->
                 (match stack_enc_stack bitmaps ws' with
                    NONE -> NONE
                  | SOME rs -> SOME (APPEND ts rs))))`;;

let stack_enc_stack_ind = cake_ind "stack_enc_stack";;

(* HOL4: dec_stack_def; Termination WF_REL_TAC measure (LENGTH o SND o SND),*)
(* with map_bitmap_LENGTH                                                   *)

let stack_dec_stack_def = cake_def_wf
  `measure (\p:(A word)list#((A)word_loc)list#((A)word_loc)list. LENGTH (SND (SND p)))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[LENGTH] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP map_bitmap_LENGTH) THEN ARITH_TAC)
  `(stack_dec_stack (bitmaps:(A word)list) (_:((A)word_loc)list) [] =
      NONE:(((A)word_loc)list)option) /\
   (stack_dec_stack bitmaps ts (CONS w ws) =
      if w = wl_Word (word 0) then
        (if ts = [] /\ ws = [] then SOME [wl_Word (word 0)] else NONE)
      else
        match full_read_bitmap bitmaps w with
          NONE -> NONE
        | SOME bs ->
            (match map_bitmap bs ts ws with
               NONE -> NONE
             | SOME (hd,ts',ws') ->
                 (match stack_dec_stack bitmaps ts' ws' with
                    NONE -> NONE
                  | SOME rest -> SOME (APPEND (APPEND [w] hd) rest))))`;;

let stack_dec_stack_ind = cake_ind "stack_dec_stack";;

(* HOL4: gc_def *)

let stack_gc_def = cake_def
  `stack_gc (s:(A,C,FFI)stack_state) =
     if LENGTH (stack_state_stack s) < stack_state_stack_space s then NONE else
       let unused = TAKE (stack_state_stack_space s) (stack_state_stack s) in
       let stack = DROP (stack_state_stack_space s) (stack_state_stack s) in
       match stack_enc_stack (stack_state_bitmaps s)
               (DROP (stack_state_stack_space s) (stack_state_stack s)) with
         NONE -> NONE
       | SOME wl_list ->
           (match stack_state_gc_fun s
                    (wl_list,stack_state_memory s,stack_state_mdomain s,
                     stack_state_store s) with
              NONE -> NONE
            | SOME (wl,m,st) ->
                (match stack_dec_stack (stack_state_bitmaps s) wl stack with
                   NONE -> NONE
                 | SOME stack ->
                     SOME (stack_state_stack_fupd (K (APPEND unused stack))
                             (stack_state_store_fupd (K st)
                                (stack_state_regs_fupd (K FEMPTY)
                                   (stack_state_memory_fupd (K m) s))))))`;;

(* HOL4: has_space_def *)

let stack_has_space_def = cake_def
  `stack_has_space (wl:(A)word_loc) (store:(store_name,(A)word_loc)fmap) =
     match (wl,FLOOKUP store NextFree,FLOOKUP store TriggerGC) with
       (wl_Word w,SOME (wl_Word n),SOME (wl_Word l)) ->
         SOME (val w <= val (word_sub l n))
     | _ -> NONE`;;

(* HOL4: alloc_def: perform garbage collection, read how much space should *)
(* be allocated, check how much space there is: SOME T is success, there is *)
(* that much space; SOME F is failure, the GC did not free up enough space *)

let stackSem_alloc_def = cake_def
  `stackSem_alloc (w:A word) (s:(A,C,FFI)stack_state) =
     match stack_gc (stack_set_store AllocSize (wl_Word w) s) with
       NONE -> (SOME (stack_Error:(A)stack_result),s)
     | SOME s ->
         (match FLOOKUP (stack_state_store s) AllocSize with
            NONE -> (SOME stack_Error,s)
          | SOME w ->
              (match stack_has_space w (stack_state_store s) with
                 NONE -> (SOME stack_Error,s)
               | SOME b ->
                   if b then (NONE,s)
                   else (SOME (stackSem_Halt (wl_Word (word 1:A word))),
                         stack_empty_env s)))`;;

(* HOL4: assign_def *)

let stack_assign_def = cake_def
  `stack_assign reg (exp:(A)wl_exp) (s:(A,C,FFI)stack_state) =
     match stack_word_exp s exp with
       NONE -> NONE
     | SOME w -> SOME (stack_set_var reg (wl_Word w) s)`;;

(* HOL4: inst_def *)

let stack_inst_def = cake_def
  `stack_inst (i:(A)inst) (s:(A,C,FFI)stack_state) =
     match i with
       asm_Skip -> SOME s
     | asm_Const reg w -> stack_assign reg (wl_Const w) s
     | asm_Arith (Binop bop r1 r2 ri) ->
         if bop = asm_Or /\ ri = Reg r2 then
           (match FLOOKUP (stack_state_regs s) r2 with
              NONE -> NONE
            | SOME w -> SOME (stack_set_var r1 w s))
         else
           stack_assign r1
             (wl_Op bop [wl_Var r2; (match ri with Reg r3 -> wl_Var r3
                                                 | Imm w -> wl_Const w)]) s
     | asm_Arith (asm_Shift sh r1 r2 ri) ->
         stack_assign r1
           (wl_Shift sh (wl_Var r2) (match ri with Reg r3 -> wl_Var r3
                                                 | Imm w -> wl_Const w)) s
     | asm_Arith (asm_Div r1 r2 r3) ->
         (let vs = stack_get_vars [r3;r2] s in
          match vs with
            SOME [wl_Word q; wl_Word w2] ->
              if ~(q = word 0) then
                SOME (stack_set_var r1 (wl_Word (word_jdiv w2 q)) s)
              else NONE
          | _ -> NONE)
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
         (let vs = stack_get_vars [r2;r3;r4] s in
          match vs with
            SOME [wl_Word l; wl_Word r; wl_Word c] ->
              let res = (val l + val r) + (if c = word 0 then 0 else 1) in
              SOME (stack_set_var r4
                      (wl_Word (if dimword(:A) <= res then word 1 else word 0))
                      (stack_set_var r1 (wl_Word (word res)) s))
          | _ -> NONE)
     | asm_Arith (AddOverflow r1 r2 r3 r4) ->
         (let vs = stack_get_vars [r2;r3] s in
          match vs with
            SOME [wl_Word w2; wl_Word w3] ->
              SOME (stack_set_var r4
                      (wl_Word (if ~(ival (word_add w2 w3) = ival w2 + ival w3)
                                then word 1 else word 0))
                      (stack_set_var r1 (wl_Word (word_add w2 w3)) s))
          | _ -> NONE)
     | asm_Arith (SubOverflow r1 r2 r3 r4) ->
         (let vs = stack_get_vars [r2;r3] s in
          match vs with
            SOME [wl_Word w2; wl_Word w3] ->
              SOME (stack_set_var r4
                      (wl_Word (if ~(ival (word_sub w2 w3) = ival w2 - ival w3)
                                then word 1 else word 0))
                      (stack_set_var r1 (wl_Word (word_sub w2 w3)) s))
          | _ -> NONE)
     | asm_Arith (LongMul r1 r2 r3 r4) ->
         (let vs = stack_get_vars [r3;r4] s in
          match vs with
            SOME [wl_Word w3; wl_Word w4] ->
              let r = val w3 * val w4 in
              SOME (stack_set_var r2 (wl_Word (word r))
                      (stack_set_var r1 (wl_Word (word (r DIV dimword(:A)))) s))
          | _ -> NONE)
     | asm_Arith (LongDiv r1 r2 r3 r4 r5) ->
         (let vs = stack_get_vars [r3;r4;r5] s in
          match vs with
            SOME [wl_Word w3; wl_Word w4; wl_Word w5] ->
              let n = val w3 * dimword(:A) + val w4 in
              let d = val w5 in
              let q = n DIV d in
              if ~(d = 0) /\ q < dimword(:A) then
                SOME (stack_set_var r1 (wl_Word (word q))
                        (stack_set_var r2 (wl_Word (word (n MOD d))) s))
              else NONE
          | _ -> NONE)
     | Mem asm_Load r (Addr a w) ->
         (match stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
            NONE -> NONE
          | SOME w ->
              (match stack_mem_load w s with
                 NONE -> NONE
               | SOME w -> SOME (stack_set_var r w s)))
     | Mem Load8 r (Addr a w) ->
         (match stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
            SOME w ->
              (match mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                       (stack_state_be s) w with
                 NONE -> NONE
               | SOME w -> SOME (stack_set_var r (wl_Word (word_zx w)) s))
          | _ -> NONE)
     | Mem Load16 _ _ -> NONE
     | Mem asm_Load32 r (Addr a w) ->
         (match stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
            SOME w ->
              (match mem_load_32 (stack_state_memory s) (stack_state_mdomain s)
                       (stack_state_be s) w with
                 NONE -> NONE
               | SOME w -> SOME (stack_set_var r (wl_Word (word_zx w)) s))
          | _ -> NONE)
     | Mem asm_Store r (Addr a w) ->
         (match (stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]),
                 stack_get_var r s) with
            (SOME a,SOME w) ->
              (match stack_mem_store a w s with
                 SOME s1 -> SOME s1
               | NONE -> NONE)
          | _ -> NONE)
     | Mem Store8 r (Addr a w) ->
         (match (stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]),
                 stack_get_var r s) with
            (SOME a,SOME (wl_Word w)) ->
              (match mem_store_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                       (stack_state_be s) a (word_zx w) with
                 SOME new_m -> SOME (stack_state_memory_fupd (K new_m) s)
               | NONE -> NONE)
          | _ -> NONE)
     | Mem Store16 _ _ -> NONE
     | Mem asm_Store32 r (Addr a w) ->
         (match (stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]),
                 stack_get_var r s) with
            (SOME a,SOME (wl_Word w)) ->
              (match mem_store_32 (stack_state_memory s) (stack_state_mdomain s)
                       (stack_state_be s) a (word_zx w) with
                 SOME new_m -> SOME (stack_state_memory_fupd (K new_m) s)
               | NONE -> NONE)
          | _ -> NONE)
     | FP (FPLess r d1 d2) ->
         (match (stack_get_fp_var d1 s,stack_get_fp_var d2 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_var r
                      (wl_Word (if fp64_lessThan f1 f2 then word 1 else word 0)) s)
          | _ -> NONE)
     | FP (FPLessEqual r d1 d2) ->
         (match (stack_get_fp_var d1 s,stack_get_fp_var d2 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_var r
                      (wl_Word (if fp64_lessEqual f1 f2 then word 1 else word 0)) s)
          | _ -> NONE)
     | FP (FPEqual r d1 d2) ->
         (match (stack_get_fp_var d1 s,stack_get_fp_var d2 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_var r
                      (wl_Word (if fp64_equal f1 f2 then word 1 else word 0)) s)
          | _ -> NONE)
     | FP (FPMov d1 d2) ->
         (match stack_get_fp_var d2 s with
            SOME f -> SOME (stack_set_fp_var d1 f s)
          | _ -> NONE)
     | FP (FPAbs d1 d2) ->
         (match stack_get_fp_var d2 s with
            SOME f -> SOME (stack_set_fp_var d1 (fp64_abs f) s)
          | _ -> NONE)
     | FP (FPNeg d1 d2) ->
         (match stack_get_fp_var d2 s with
            SOME f -> SOME (stack_set_fp_var d1 (fp64_negate f) s)
          | _ -> NONE)
     | FP (FPSqrt d1 d2) ->
         (match stack_get_fp_var d2 s with
            SOME f -> SOME (stack_set_fp_var d1 (fp64_sqrt roundTiesToEven f) s)
          | _ -> NONE)
     | FP (FPAdd d1 d2 d3) ->
         (match (stack_get_fp_var d2 s,stack_get_fp_var d3 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPSub d1 d2 d3) ->
         (match (stack_get_fp_var d2 s,stack_get_fp_var d3 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPMul d1 d2 d3) ->
         (match (stack_get_fp_var d2 s,stack_get_fp_var d3 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPDiv d1 d2 d3) ->
         (match (stack_get_fp_var d2 s,stack_get_fp_var d3 s) with
            (SOME f1,SOME f2) ->
              SOME (stack_set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s)
          | _ -> NONE)
     | FP (FPFma d1 d2 d3) ->
         (match (stack_get_fp_var d1 s,stack_get_fp_var d2 s,stack_get_fp_var d3 s) with
            (SOME f1,SOME f2,SOME f3) -> SOME (stack_set_fp_var d1 (fpfma f1 f2 f3) s)
          | _ -> NONE)
     | FP (FPMovToReg r1 r2 d) ->
         (match stack_get_fp_var d s with
            SOME v ->
              if dimindex(:A) = 64 then
                SOME (stack_set_var r1 (wl_Word (word_zx v)) s)
              else
                SOME (stack_set_var r2 (wl_Word (word_extract 63 32 v))
                        (stack_set_var r1 (wl_Word (word_extract 31 0 v)) s))
          | _ -> NONE)
     | FP (FPMovFromReg d r1 r2) ->
         (if dimindex(:A) = 64 then
            match stack_get_var r1 s with
              SOME (wl_Word w1) -> SOME (stack_set_fp_var d (word_zx w1) s)
            | _ -> NONE
          else
            match (stack_get_var r1 s,stack_get_var r2 s) with
              (SOME (wl_Word w1),SOME (wl_Word w2)) ->
                SOME (stack_set_fp_var d (word_join w2 w1) s)
            | _ -> NONE)
     | FP (FPToInt d1 d2) ->
         (match stack_get_fp_var d2 s with
            NONE -> NONE
          | SOME f ->
              (match fp64_to_int roundTiesToEven f with
                 NONE -> NONE
               | SOME i ->
                   let w = iword i:int32 in
                   if ival w = i then
                     (if dimindex(:A) = 64 then
                        SOME (stack_set_fp_var d1 (word_zx w) s)
                      else
                        match stack_get_fp_var (d1 DIV 2) s with
                          NONE -> NONE
                        | SOME f ->
                            let (h,l) = if ODD d1 then (63,32) else (31,0) in
                            SOME (stack_set_fp_var (d1 DIV 2)
                                    (word_insert f (l,(h + 1) - l) w) s))
                   else NONE))
     | FP (FPFromInt d1 d2) ->
         if dimindex(:A) = 64 then
           match stack_get_fp_var d2 s with
             SOME f ->
               let i = ival (word_extract 31 0 f:int32) in
               SOME (stack_set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
           | NONE -> NONE
         else
           match stack_get_fp_var (d2 DIV 2) s with
             SOME v ->
               let i = ival (if ODD d2 then word_extract 63 32 v
                             else word_extract 31 0 v:A word) in
               SOME (stack_set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
           | NONE -> NONE
     | _ -> NONE`;;

(* HOL4: get_var_imm_def *)

let stack_get_var_imm_def = cake_def
  `(stack_get_var_imm (Reg n:(A)reg_imm) (s:(A,C,FFI)stack_state) =
      stack_get_var n s) /\
   (stack_get_var_imm (Imm w) s = SOME (wl_Word w))`;;

(* HOL4: find_code_def *)

let stack_find_code_def = cake_def
  `(stack_find_code (INL p) (regs:(num,(A)word_loc)fmap) (code:(B)spt) =
      lookup p code) /\
   (stack_find_code (INR r) regs code =
      match FLOOKUP regs r with
        SOME (wl_Loc loc 0) -> lookup loc code
      | other -> NONE)`;;

(* HOL4: fix_clock_def; HOL4 infers the most general type: the states are  *)
(* of independent types                                                      *)

let stack_fix_clock_def = cake_def
  `stack_fix_clock (s:(A,C,FFI)stack_state) (res:B,(s1:(D,E,G)stack_state)) =
     (res,stack_state_clock_fupd
            (K (MIN (stack_state_clock s) (stack_state_clock s1))) s1)`;;

(* HOL4: [local] fix_clock_IMP *)

let stack_fix_clock_IMP = prove
 (`stack_fix_clock (s:(A,C,FFI)stack_state) x = (res:B,(s1:(D,E,G)stack_state))
   ==> stack_state_clock s1 <= stack_state_clock s`,
  SPEC_TAC(`x:B#(D,E,G)stack_state`,`x:B#(D,E,G)stack_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; stack_fix_clock_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN ARITH_TAC);;

(* HOL4: STOP_def *)

let stack_STOP_def = cake_def
  `stack_STOP (x:A) = x`;;

(* HOL4: get_labels_def; the catch-all clause completes into one clause   *)
(* per constructor of stack_prog: sem1aux_def_wf (HOL4's TFL compilation).  *)
(* HOL4's UNION binds tighter than INSERT (HOL Light's the other way): the  *)
(* parentheses keep HOL4's term                                              *)

let stack_get_labels_def = sem1aux_def_wf
  `measure (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(stack_get_labels (stack_Seq p1 p2:(A)stack_prog) =
      stack_get_labels p1 UNION stack_get_labels p2) /\
   (stack_get_labels (stack_If _ _ _ p1 p2) =
      stack_get_labels p1 UNION stack_get_labels p2) /\
   (stack_get_labels (stack_Loop p) = stack_get_labels p) /\
   (stack_get_labels (stack_Call ret _ handler) =
      match ret with
        NONE -> {}
      | SOME (r,_,l1,l2) ->
          (l1,l2) INSERT
          (stack_get_labels r UNION
           (match handler with
              NONE -> {}
            | SOME (r,l1,l2) -> (l1,l2) INSERT stack_get_labels r))) /\
   (stack_get_labels (stack_Halt _) = {}) /\
   (stack_get_labels _ = {})`;;

let loc_check_def = cake_def
  `loc_check (code:((A)stack_prog)spt) (l1,l2) <=>
     (l2 = 0 /\ l1 IN domain code) \/
     ?n e. lookup n code = SOME e /\ (l1,l2) IN stack_get_labels e`;;

(* HOL4 proves termination automatically: val pattern decreases *)

let copy_words_for_pattern_def = cake_def_wf
  `measure (\x:A word#num#A word#A word#(A word)list#(A word->bool)#
               (A word->(A)word_loc). val (FST x))`
  (REWRITE_TAC[measure_THM; FST; VAL_WORD_USHR; EXP_1] THEN REPEAT STRIP_TAC THEN
   REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC)
  `copy_words_for_pattern (pattern:A word) (i:num) (a:A word) (off:A word) bs dm m =
     if pattern = word 0 then NONE else
     if pattern = word 1 then SOME (i,a,m) else
       if a IN dm /\ i < LENGTH bs then
         let b = bit 0 pattern in
         let w = EL i bs in
         let m = (a =+ wl_Word (if b then word_add w off else w)) m in
         copy_words_for_pattern (word_ushr pattern 1) (i + 1)
           (word_add a bytes_in_word) off bs dm m
       else NONE`;;

let copy_words_for_pattern_ind = cake_ind "copy_words_for_pattern";;

let copy_words_for_pattern_LESS_EQ = prove
 (`!p i (a:A word) f bs dm m j a1.
     copy_words_for_pattern p i a f bs dm m = SOME (j,a1) ==> i <= j`,
  MATCH_MP_TAC copy_words_for_pattern_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[copy_words_for_pattern_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `i + 1 <= j ==> i <= j`]);;

(* HOL4: copy_words_def; Termination WF_REL_TAC measure (LENGTH bs - i),   *)
(* with copy_words_for_pattern_LESS_EQ                                      *)

let copy_words_def = cake_def_wf
  `measure (\x:num#A word#A word#(A word)list#(A word->bool)#(A word->(A)word_loc).
              LENGTH (FST (SND (SND (SND x)))) - FST x)`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP copy_words_for_pattern_LESS_EQ) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC)
  `copy_words i (a:A word) off bs dm m =
     if LENGTH bs <= i then NONE else
       let pattern = EL i bs in
       match copy_words_for_pattern pattern (i + 1) a off bs dm m with
         NONE -> NONE
       | SOME (i1,a1,m1) ->
           if word_msb pattern then copy_words i1 a1 off bs dm m1
           else SOME (a1,m1)`;;

let copy_words_ind = cake_ind "copy_words";;

(* HOL4: unset_var_def *)

let stack_unset_var_def = cake_def
  `stack_unset_var v (s:(A,C,FFI)stack_state) =
     stack_state_regs_fupd (K (stack_state_regs s \\ v)) s`;;

let store_const_sem_def = cake_def
  `store_const_sem t1 t2 (s:(A,C,FFI)stack_state) =
     if ~ALL_DISTINCT [0;1;2;3;t1;t2] then (SOME (stack_Error:(A)stack_result),s)
     else
       match (stack_get_var 1 s,stack_get_var 2 s,stack_get_var 3 s) with
         (SOME (wl_Word i),SOME (wl_Word a),SOME (wl_Word off)) ->
           (match copy_words (val i) a off (stack_state_bitmaps s)
                    (stack_state_mdomain s) (stack_state_memory s) with
              NONE -> (SOME stack_Error,s)
            | SOME (a,m) ->
                (NONE,
                 (if stack_state_use_alloc s then stack_unset_var 0 else I)
                   (stack_set_var t1 (wl_Word (word 1))
                      (stack_set_var t2 (wl_Word (word 1))
                         (stack_set_var 1 (wl_Word (word 1))
                            (stack_set_var 2 (wl_Word a)
                               (stack_state_memory_fupd (K m) s)))))))
       | _ -> (SOME stack_Error,s)`;;

let check_store_consts_opt_def = cake_def
  `(check_store_consts_opt t1 t2 NONE (_:((A)stack_prog)spt) <=> T) /\
   (check_store_consts_opt t1 t2 (SOME n) c <=>
      lookup n c =
      SOME (stack_Seq (stack_StoreConsts t1 t2 NONE) (stack_Return 0)))`;;

(* HOL4: dest_Seq_def, bad_fun_return_def, cont_loop_def, exit_loop_def;  *)
(* catch-all clauses: sem1aux_def                                            *)

let stack_dest_Seq_def = sem1aux_def
  `(stack_dest_Seq (stack_Seq p1 p2) = SOME (p1,p2:(A)stack_prog)) /\
   (stack_dest_Seq _ = NONE)`;;

let stack_bad_fun_return_def = sem1aux_def
  `(stack_bad_fun_return (NONE:((W)stack_result)option) <=> T) /\
   (stack_bad_fun_return (SOME (stackSem_Break _)) <=> T) /\
   (stack_bad_fun_return (SOME (stackSem_Continue _)) <=> T) /\
   (stack_bad_fun_return _ <=> F)`;;

let _ = cake_add_simps [stack_bad_fun_return_def];;

let stack_cont_loop_def = sem1aux_def
  `(stack_cont_loop (NONE:((W)stack_result)option) <=> T) /\
   (stack_cont_loop (SOME (stackSem_Continue n)) <=> n = 0) /\
   (stack_cont_loop _ <=> F)`;;

let _ = cake_add_simps [stack_cont_loop_def];;

let stack_exit_loop_def = sem1aux_def
  `(stack_exit_loop (SOME (stackSem_Break n):((W)stack_result)option) =
      if n = 0 then NONE else SOME (stackSem_Break (n - 1))) /\
   (stack_exit_loop (SOME (stackSem_Continue n)) = SOME (stackSem_Continue (n - 1))) /\
   (stack_exit_loop res = res)`;;

let _ = cake_add_simps [stack_exit_loop_def];;

(* ------------------------------------------------------------------------- *)
(* The semantics.  HOL4: evaluate_def with Termination                       *)
(* WF_REL_TAC inv_image (measure I LEX measure (prog_size (K 0)))            *)
(* (\(xs,s). (s.clock,xs)), then fix_clock_IMP and arithmetic.  As for      *)
(* wordSem's wl_evaluate, the definition is made with sem1aux_def_wf (the    *)
(* kit's casewise package would need hours for the 34 clauses); the          *)
(* termination tactic handles both kinds of termination conditions.         *)
(* ------------------------------------------------------------------------- *)

let STACKPAUX_clock_rws = prove
 (`stack_state_clock (stack_dec_clock (s:(A,C,FFI)stack_state)) =
     stack_state_clock s - 1 /\
   stack_state_clock (stack_set_var n v s) = stack_state_clock s /\
   stack_state_clock (stack_STOP s) = stack_state_clock s`,
  REWRITE_TAC[stack_dec_clock_def; stack_set_var_def; stack_STOP_def] THEN SIMP[]);;

let STACKPAUX_is_num_fact tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let STACKPAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_fix_clock_IMP)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = WF_REL_THMS @ [FST; SND; type_size_def "stack_prog";
                                     STACKPAUX_clock_rws; stack_STOP_def; I_THM] in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (STACKPAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let STACKPAUX_evaluate_rel =
  `inv_image (measure I LEX measure (stack_prog_size (\x:A. 0)))
     (\p:(A)stack_prog#(A,C,FFI)stack_state. (stack_state_clock (SND p),FST p))`;;

(* the clauses, each parsed on its own (HOL4 types each clause on its own:  *)
(* ret is an option in Call and a register in Install and FFI, w a word or  *)
(* a word_loc, ...); the type of the function is given in each              *)

let STACKPAUX_evaluate_clauses = list_mk_conj
 [`stack_evaluate (stack_Skip:(A)stack_prog,s:(A,C,FFI)stack_state) =
     (NONE:((A)stack_result)option,s)`;
  `stack_evaluate (stack_Halt v:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match stack_get_var v s with
       SOME w -> (SOME (stackSem_Halt w:(A)stack_result),stack_empty_env s)
     | NONE -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Alloc n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_alloc s then (SOME (stack_Error:(A)stack_result),s) else
     match stack_get_var n s with
       SOME (wl_Word w) -> stackSem_alloc w s
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_StoreConsts t1 t2 stub_opt:(A)stack_prog,
                   s:(A,C,FFI)stack_state) =
     if ~stack_state_use_store s then (SOME (stack_Error:(A)stack_result),s) else
     if ~stack_state_use_alloc s /\ IS_SOME stub_opt then (SOME stack_Error,s) else
     if ~check_store_consts_opt t1 t2 stub_opt (stack_state_code s)
     then (SOME stack_Error,s)
     else store_const_sem t1 t2 s`;
  `stack_evaluate (stack_Inst i:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match stack_inst i s with
       SOME s1 -> (NONE:((A)stack_result)option,s1)
     | NONE -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Get v name:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_store s then (SOME (stack_Error:(A)stack_result),s) else
     match FLOOKUP (stack_state_store s) name with
       SOME x -> (NONE,stack_set_var v x s)
     | NONE -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Set name v:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_store s then (SOME (stack_Error:(A)stack_result),s) else
     match stack_get_var v s with
       SOME w -> (NONE,stack_set_store name w s)
     | NONE -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_OpCurrHeap binop v src:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_store s then (SOME (stack_Error:(A)stack_result),s) else
     match stack_word_exp s (wl_Op binop [wl_Var src; Lookup CurrHeap]) with
       SOME w -> (NONE,stack_set_var v (wl_Word w) s)
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Tick:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if stack_state_clock s = 0
     then (SOME (stack_TimeOut:(A)stack_result),stack_empty_env s)
     else (NONE,stack_dec_clock s)`;
  `stack_evaluate (stack_Seq c1 c2:(A)stack_prog,s:(A,C,FFI)stack_state) =
     let (res,s1) = stack_fix_clock s (stack_evaluate (c1,s)) in
     if res = NONE then stack_evaluate (c2,s1)
     else (res:((A)stack_result)option,s1)`;
  `stack_evaluate (stack_Return n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match stack_get_var n s with
       SOME (wl_Loc l1 l2) -> (SOME (stack_Result (wl_Loc l1 l2):(A)stack_result),s)
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Raise n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match stack_get_var n s with
       SOME (wl_Loc l1 l2) ->
         (SOME (stack_Exception (wl_Loc l1 l2):(A)stack_result),s)
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Break n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     (SOME (stackSem_Break n:(A)stack_result),s)`;
  `stack_evaluate (stack_Continue n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     (SOME (stackSem_Continue n:(A)stack_result),s)`;
  `stack_evaluate (stack_If cmp r1 ri c1 c2:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match (stack_get_var r1 s,stack_get_var_imm ri s) with
       (SOME x,SOME y) ->
         (match wl_word_cmp cmp x y with
            SOME b -> if b then stack_evaluate (c1,s) else stack_evaluate (c2,s)
          | NONE -> (SOME (stack_Error:(A)stack_result),s))
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Loop c1:(A)stack_prog,s:(A,C,FFI)stack_state) =
     let (res,s1) = stack_fix_clock s (stack_evaluate (c1,s)) in
     if stack_cont_loop res then
       (if stack_state_clock s1 = 0
        then (SOME (stack_TimeOut:(A)stack_result),stack_empty_env s1)
        else stack_evaluate (stack_STOP (stack_Loop c1),stack_dec_clock s1))
     else (stack_exit_loop res,s1)`;
  `stack_evaluate (JumpLower r1 r2 dest:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match (stack_get_var r1 s,stack_get_var r2 s) with
       (SOME (wl_Word x),SOME (wl_Word y)) ->
         if asm_word_cmp Lower x y then
           (match stack_find_code (INL dest) (stack_state_regs s) (stack_state_code s) with
              NONE -> (SOME (stack_Error:(A)stack_result),s)
            | SOME prog ->
                if stack_state_clock s = 0 then (SOME stack_TimeOut,stack_empty_env s)
                else
                  (match stack_evaluate (prog,stack_dec_clock s) with
                     (res,s) -> if stack_bad_fun_return res then (SOME stack_Error,s)
                                else (res,s)))
         else (NONE,s)
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (RawCall dest:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match lookup dest (stack_state_code s) with
       NONE -> (SOME (stack_Error:(A)stack_result),s)
     | SOME prog ->
         (match stack_dest_Seq prog with
            SOME (_,body) ->
              if stack_state_clock s = 0 then (SOME stack_TimeOut,stack_empty_env s)
              else
                (match stack_evaluate (body,stack_dec_clock s) with
                   (res,s) -> if stack_bad_fun_return res then (SOME stack_Error,s)
                              else (res,s))
          | _ -> (SOME stack_Error,s))
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_Call ret dest handler:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match ret with
       NONE ->
         (match stack_find_code dest (stack_state_regs s) (stack_state_code s) with
            NONE -> (SOME (stack_Error:(A)stack_result),s)
          | SOME prog ->
              if ~(handler = NONE) then (SOME stack_Error,s) else
              if stack_state_clock s = 0 then (SOME stack_TimeOut,stack_empty_env s)
              else
                (match stack_fix_clock (stack_dec_clock s)
                         (stack_evaluate (prog,stack_dec_clock s)) with
                   (res,s) -> if stack_bad_fun_return res then (SOME stack_Error,s)
                              else (res,s)))
     | SOME (ret_handler,link_reg,l1,l2) ->
         (match stack_find_code dest (stack_state_regs s \\ link_reg)
                  (stack_state_code s) with
            NONE -> (SOME stack_Error,s)
          | SOME prog ->
              if stack_state_clock s = 0 then (SOME stack_TimeOut,stack_empty_env s)
              else
                (match stack_fix_clock
                         (stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s))
                         (stack_evaluate
                            (prog,stack_dec_clock
                                    (stack_set_var link_reg (wl_Loc l1 l2) s))) with
                   (SOME (stack_Result x),s2) ->
                     if ~(x = wl_Loc l1 l2) then (SOME stack_Error,s2)
                     else stack_evaluate (ret_handler,s2)
                 | (SOME (stack_Exception x),s2) ->
                     (match handler with
                        NONE -> (SOME (stack_Exception x),s2)
                      | SOME (h,l1,l2) ->
                          if ~(x = wl_Loc l1 l2) then (SOME stack_Error,s2)
                          else stack_evaluate (h,s2))
                 | (NONE,s) -> (SOME stack_Error,s)
                 | (SOME (stackSem_Break _),s) -> (SOME stack_Error,s)
                 | (SOME (stackSem_Continue _),s) -> (SOME stack_Error,s)
                 | (res,s) -> (res,s)))`;
  `stack_evaluate (stack_Install ptr len dptr dlen ret:(A)stack_prog,
                   s:(A,C,FFI)stack_state) =
     match (stack_get_var ptr s,stack_get_var len s,stack_get_var dptr s,
            stack_get_var dlen s) with
       (SOME (wl_Word w1),SOME (wl_Word w2),SOME (wl_Word w3),SOME (wl_Word w4)) ->
         let (cfg,progs,bm) = stack_state_compile_oracle s 0 in
         (match (buffer_flush (stack_state_code_buffer s) w1 w2,
                 if stack_state_use_stack s
                 then buffer_flush (stack_state_data_buffer s) w3 w4
                 else SOME (bm,stack_state_data_buffer s)) with
            (SOME (bytes,cb),SOME (data,db)) ->
              let new_oracle = shift_seq 1 (stack_state_compile_oracle s) in
              (match (stack_state_compile s cfg progs,progs) with
                 (SOME (bytes',cfg'),CONS (k,prog) _) ->
                   if bytes = bytes' /\ data = bm /\ FST (new_oracle 0) = cfg' then
                     let s' =
                       stack_state_bitmaps_fupd (K (APPEND (stack_state_bitmaps s) bm))
                       (stack_state_code_buffer_fupd (K cb)
                       (stack_state_data_buffer_fupd (K db)
                       (stack_state_code_fupd
                          (K (union (stack_state_code s) (fromAList progs)))
                       (stack_state_regs_fupd
                          (K (DRESTRICT (stack_state_regs s) (stack_state_ffi_save_regs s)
                              |+ (ptr,wl_Loc k 0)))
                       (stack_state_fp_regs_fupd (K FEMPTY)
                       (stack_state_compile_oracle_fupd (K new_oracle) s)))))) in
                     (NONE,s')
                   else (SOME (stack_Error:(A)stack_result),s)
               | _ -> (SOME stack_Error,s))
          | _ -> (SOME stack_Error,s))
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (ShMemOp op r (Addr a w):(A)stack_prog,s:(A,C,FFI)stack_state) =
     match stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) with
       SOME a ->
         if stack_state_clock s = 0
         then (SOME (stack_TimeOut:(A)stack_result),stack_empty_env s)
         else sh_mem_op op r a (stack_dec_clock s)
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_CodeBufferWrite r1 r2:(A)stack_prog,s:(A,C,FFI)stack_state) =
     match (stack_get_var r1 s,stack_get_var r2 s) with
       (SOME (wl_Word w1),SOME (wl_Word w2)) ->
         (match buffer_write (stack_state_code_buffer s) w1 (word_zx w2) with
            SOME new_cb ->
              (NONE:((A)stack_result)option,stack_state_code_buffer_fupd (K new_cb) s)
          | _ -> (SOME stack_Error,s))
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_DataBufferWrite r1 r2:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     match (stack_get_var r1 s,stack_get_var r2 s) with
       (SOME (wl_Word w1),SOME (wl_Word w2)) ->
         (match buffer_write (stack_state_data_buffer s) w1 w2 with
            SOME new_db -> (NONE,stack_state_data_buffer_fupd (K new_db) s)
          | _ -> (SOME stack_Error,s))
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_FFI ffi_index ptr len ptr2 len2 ret:(A)stack_prog,
                   s:(A,C,FFI)stack_state) =
     match (stack_get_var len s,stack_get_var ptr s,stack_get_var len2 s,
            stack_get_var ptr2 s) with
       (SOME (wl_Word w),SOME (wl_Word w2),SOME (wl_Word w3),SOME (wl_Word w4)) ->
         (match (read_bytearray w2 (val w)
                   (mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                      (stack_state_be s)),
                 read_bytearray w4 (val w3)
                   (mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                      (stack_state_be s))) with
            (SOME bytes,SOME bytes2) ->
              (match call_FFI (stack_state_ffi s) (ExtCall ffi_index) bytes bytes2 with
                 FFI_final outcome ->
                   (SOME (stack_FinalFFI outcome:(A)stack_result),s)
               | FFI_return new_ffi new_bytes ->
                   let new_m = write_bytearray w4 new_bytes (stack_state_memory s)
                                 (stack_state_mdomain s) (stack_state_be s) in
                   (NONE,
                    stack_state_memory_fupd (K new_m)
                    (stack_state_regs_fupd
                       (K (DRESTRICT (stack_state_regs s) (stack_state_ffi_save_regs s)))
                    (stack_state_fp_regs_fupd (K FEMPTY)
                    (stack_state_ffi_fupd (K new_ffi) s)))))
          | _ -> (SOME stack_Error,s))
     | res -> (SOME stack_Error,s)`;
  `stack_evaluate (stack_LocValue r l1 l2:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if loc_check (stack_state_code s) (l1,l2) then
       (NONE:((A)stack_result)option,stack_set_var r (wl_Loc l1 l2) s)
     else (SOME stack_Error,s)`;
  `stack_evaluate (StackAlloc n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     if stack_state_stack_space s < n
     then (SOME (stackSem_Halt (wl_Word (word 2))),stack_empty_env s)
     else (NONE,stack_state_stack_space_fupd (K (stack_state_stack_space s - n)) s)`;
  `stack_evaluate (StackFree n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     if LENGTH (stack_state_stack s) < stack_state_stack_space s + n
     then (SOME stack_Error,stack_empty_env s)
     else (NONE,stack_state_stack_space_fupd (K (stack_state_stack_space s + n)) s)`;
  `stack_evaluate (StackLoad r n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     if stack_state_stack_space s + n < LENGTH (stack_state_stack s)
     then (NONE,stack_set_var r (EL (stack_state_stack_space s + n)
                                   (stack_state_stack s)) s)
     else (SOME stack_Error,stack_empty_env s)`;
  `stack_evaluate (StackLoadAny r rn:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     match stack_get_var rn s with
       SOME (wl_Word (w:A word)) ->
         let i = stack_state_stack_space s +
                 val (word_ushr w (backend_common_word_shift (:A))) in
         if i < LENGTH (stack_state_stack s) /\
            word_shl (word_ushr w (backend_common_word_shift (:A)))
              (backend_common_word_shift (:A)) = w
         then (NONE,stack_set_var r (EL i (stack_state_stack s)) s)
         else (SOME stack_Error,stack_empty_env s)
     | _ -> (SOME stack_Error,stack_empty_env s)`;
  `stack_evaluate (StackStore r n:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     if LENGTH (stack_state_stack s) <= stack_state_stack_space s + n
     then (SOME stack_Error,stack_empty_env s)
     else
       match stack_get_var r s with
         NONE -> (SOME stack_Error,stack_empty_env s)
       | SOME v ->
           (NONE,stack_state_stack_fupd
                   (K (LUPDATE v (stack_state_stack_space s + n) (stack_state_stack s)))
                   s)`;
  `stack_evaluate (StackStoreAny r rn:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     match (stack_get_var r s,stack_get_var rn s) with
       (SOME v,SOME (wl_Word (w:A word))) ->
         let i = stack_state_stack_space s +
                 val (word_ushr w (backend_common_word_shift (:A))) in
         if i < LENGTH (stack_state_stack s) /\
            word_shl (word_ushr w (backend_common_word_shift (:A)))
              (backend_common_word_shift (:A)) = w
         then (NONE,stack_state_stack_fupd (K (LUPDATE v i (stack_state_stack s))) s)
         else (SOME stack_Error,stack_empty_env s)
     | _ -> (SOME stack_Error,stack_empty_env s)`;
  `stack_evaluate (StackGetSize r:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     (NONE,stack_set_var r (wl_Word (word (stack_state_stack_space s))) s)`;
  `stack_evaluate (StackSetSize r:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s then (SOME (stack_Error:(A)stack_result),s) else
     match stack_get_var r s with
       SOME (wl_Word (w:A word)) ->
         if LENGTH (stack_state_stack s) <= val w then (SOME stack_Error,stack_empty_env s)
         else (NONE,stack_set_var r (wl_Word (word_shl w (backend_common_word_shift (:A))))
                      (stack_state_stack_space_fupd (K (val w)) s))
     | _ -> (SOME stack_Error,s)`;
  `stack_evaluate (BitmapLoad r v:(A)stack_prog,s:(A,C,FFI)stack_state) =
     if ~stack_state_use_stack s \/ r = v then (SOME (stack_Error:(A)stack_result),s)
     else
       match stack_get_var v s with
         SOME (wl_Word w) ->
           if LENGTH (stack_state_bitmaps s) <= val w then (SOME stack_Error,s)
           else (NONE,stack_set_var r (wl_Word (EL (val w) (stack_state_bitmaps s))) s)
       | _ -> (SOME stack_Error,s)`];;

let STACKPAUX_evaluate_fix_def =
  sem1aux_def_wf STACKPAUX_evaluate_rel STACKPAUX_TC_TAC STACKPAUX_evaluate_clauses;;

let STACKPAUX_evaluate_fix_ind = cake_ind "stack_evaluate";;

(* We prove that the clock never increases. *)

let STACKPAUX_mem_store_clock = prove
 (`stack_mem_store a w (s:(A,C,FFI)stack_state) = SOME s1
   ==> stack_state_clock s1 = stack_state_clock s`,
  REWRITE_TAC[stack_mem_store_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let stack_gc_clock = prove
 (`!(s1:(A,C,FFI)stack_state) s2.
     stack_gc s1 = SOME s2 ==> stack_state_clock s2 <= stack_state_clock s1`,
  REWRITE_TAC[stack_gc_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[LE_REFL]);;

(* HOL4 quantifies the unused variable xs (of an unconstrained type) *)

let stack_alloc_clock = prove
 (`!(xs:B) (s1:(A,C,FFI)stack_state) vs s2.
     stackSem_alloc x s1 = (vs,s2) ==> stack_state_clock s2 <= stack_state_clock s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stackSem_alloc_def] THEN
  MP_TAC(ISPEC `stack_set_store AllocSize (wl_Word x) (s1:(A,C,FFI)stack_state)`
           stack_gc_clock) THEN
  REWRITE_TAC[stack_set_store_def] THEN SIMP[] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[stack_empty_env_def] THEN SIMP[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC_ALL) THEN SIMP[]);;

let store_const_sem_clock = prove
 (`!(s1:(A,C,FFI)stack_state) v s2.
     store_const_sem t1 t2 s1 = (v,s2) ==> stack_state_clock s2 <= stack_state_clock s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[store_const_sem_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[stack_unset_var_def; stack_set_var_def; I_THM] THEN SIMP[LE_REFL]);;

(* HOL4 [local] *)

let stack_inst_clock = prove
 (`stack_inst i (s:(A,C,FFI)stack_state) = SOME s2
   ==> stack_state_clock s2 <= stack_state_clock s`,
  REWRITE_TAC[stack_inst_def; stack_assign_def; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[stack_set_var_def; stack_set_fp_var_def] THEN SIMP[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP STACKPAUX_mem_store_clock) THEN ARITH_TAC);;

(* HOL4 [local] *)

let sh_mem_op_clock = prove
 (`sh_mem_op op r a (s:(A,C,FFI)stack_state) = (res,s')
   ==> stack_state_clock s' <= stack_state_clock s`,
  CASES_ON `op:memop` THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_load_def;
              stack_sh_mem_store32_def; stack_sh_mem_load32_def;
              stack_sh_mem_load16_def; stack_sh_mem_store16_def;
              stack_sh_mem_store_byte_def; stack_sh_mem_load_byte_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[LE_REFL]);;

(* the proof of evaluate_clock (as for wl_evaluate_clock in wordSem.ml):    *)
(* the clock facts of the helpers, then the induction hypotheses             *)
(* instantiated at the evaluate assumptions                                  *)

let STACKPAUX_clock_case_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["word_loc"; "stack_result"; "ffi_result"];;

let STACKPAUX_is_eval_eq tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "stack_evaluate"
   with Failure _ -> false);;

(* prove ?vs. A1 /\ ... /\ An from the assumptions: each existential       *)
(* variable is found by matching a conjunct with an assumption (or the two  *)
(* sides of an equation), the instantiated conjunction is proved by         *)
(* rewriting with the assumptions                                           *)

let STACKPAUX_EXISTS_ASM_TAC : tactic = fun (asl,w as g) ->
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

(* for every assumption stack_evaluate p = (v,t) and every induction        *)
(* hypothesis whose evaluate antecedent matches it, add the instance of its  *)
(* conclusion when its other antecedents follow from the assumptions        *)

let STACKPAUX_USE_IHS_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> STACKPAUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists STACKPAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let inst_of ih0 e =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = GENL vs1 (SPECL vs1 ih0) in
    let vs,bod = strip_forall (concl ih) in
    let ant,_ = dest_imp bod in
    let cj = find STACKPAUX_is_eval_eq (conjuncts ant) in
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
            [MATCH_MP_TAC th THEN STACKPAUX_EXISTS_ASM_TAC THEN NO_TAC; ALL_TAC]))
    insts g;;

let STACKPAUX_CLOCK_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[STACKPAUX_evaluate_fix_def] THEN
  REWRITE_TAC(STACKPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  STACKPAUX_USE_IHS_TAC THEN
  MAP_EVERY (fun th -> REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL o MATCH_MP th)))
    [stack_fix_clock_IMP; STACKPAUX_mem_store_clock; stack_inst_clock;
     stack_alloc_clock; store_const_sem_clock; sh_mem_op_clock] THEN
  (fun g -> let ths = [STACKPAUX_clock_rws; stack_empty_env_def; stack_set_store_def;
                       stack_unset_var_def; stack_state_INFO.ri_accfupds; K_THM;
                       I_THM] in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (STACKPAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* the If case (the boolean of the comparison is a context of the IHs) *)

let STACKPAUX_CLOCK_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[STACKPAUX_evaluate_fix_def] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; COND_CASE_EQ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[];;

let STACKPAUX_evaluate_clock = prove
 (`!p vs (s2:(A,C,FFI)stack_state).
     stack_evaluate p = (vs,s2)
     ==> stack_state_clock s2 <= stack_state_clock (SND p)`,
  MATCH_MP_TAC STACKPAUX_evaluate_fix_ind THEN REWRITE_TAC[SND] THEN
  REPEAT CONJ_TAC THEN FIRST [STACKPAUX_CLOCK_TAC; STACKPAUX_CLOCK_IF_TAC]);;

let stack_evaluate_clock = prove
 (`!xs (s1:(A,C,FFI)stack_state) vs s2.
     stack_evaluate (xs,s1) = (vs,s2)
     ==> stack_state_clock s2 <= stack_state_clock s1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP STACKPAUX_evaluate_clock) THEN
  REWRITE_TAC[SND]);;

let STACKPAUX_fix_clock_id = prove
 (`!(s:(A,C,FFI)stack_state) (x:B#(A,C,FFI)stack_state).
     stack_state_clock (SND x) <= stack_state_clock s ==> stack_fix_clock s x = x`,
  REWRITE_TAC[FORALL_PAIR_THM; stack_fix_clock_def; PAIR_EQ; SND] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_state_component_equality] THEN
  SIMP[] THEN ASM_ARITH_TAC);;

let stack_fix_clock_evaluate = prove
 (`stack_fix_clock (s:(A,C,FFI)stack_state) (stack_evaluate (xs,s)) =
   stack_evaluate (xs,s)`,
  MATCH_MP_TAC STACKPAUX_fix_clock_id THEN
  MP_TAC(ISPEC `stack_evaluate (xs:(A)stack_prog,s:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND] THEN
  MATCH_MP_TAC stack_evaluate_clock THEN ASM_MESON_TAC[]);;

(* HOL4: evaluate_def[compute,allow_rebind] and evaluate_ind[allow_rebind]: *)
(* the theorems without fix_clock                                            *)

let stack_evaluate_def = REWRITE_RULE[stack_fix_clock_evaluate] STACKPAUX_evaluate_fix_def;;

let stack_evaluate_ind = REWRITE_RULE[stack_fix_clock_evaluate] STACKPAUX_evaluate_fix_ind;;

let () = cake_ind_store := ("stack_evaluate",stack_evaluate_ind) :: !cake_ind_store;;

(* observational semantics *)

let stack_semantics_def = cake_def
  `stack_semantics start (s:(A,C,FFI)stack_state) =
     let prog = stack_Call NONE (INL start) NONE:(A)stack_prog in
     if ?k. let res = FST (stack_evaluate (prog,stack_state_clock_fupd (K k) s)) in
            ~(res = SOME stack_TimeOut) /\ ~(res = SOME (stack_Result (wl_Loc 1 0))) /\
            (!w. ~(res = SOME (stackSem_Halt (wl_Word w)))) /\
            !f. ~(res = SOME (stack_FinalFFI f))
     then Fail
     else
       match some res.
               ?k t r outcome.
                 stack_evaluate (prog,stack_state_clock_fupd (K k) s) = (SOME r,t) /\
                 (match r with
                    stack_FinalFFI e -> outcome = FFI_outcome e
                  | stackSem_Halt w -> outcome = if w = wl_Word (word 0) then Success
                                                 else Resource_limit_hit
                  | stack_Result _ -> outcome = Success
                  | _ -> F) /\
                 res = Terminate outcome (ffi_state_io_events (stack_state_ffi t)) with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (stack_state_ffi
                                    (SND (stack_evaluate
                                            (prog,stack_state_clock_fupd (K k) s))))))
                       UNIV))`;;

(* record accessors *)

let read_stack_def = cake_def
  `read_stack (s:(A,B,C)stack_state) = stack_state_stack s`;;

let read_stack_space_def = cake_def
  `read_stack_space (s:(A,B,C)stack_state) = stack_state_stack_space s`;;
