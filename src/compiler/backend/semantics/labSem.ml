(* ========================================================================= *)
(* labSem: port of HOL4 compiler/backend/semantics/labSemScript.sml          *)
(* (CakeML v3479).                                                           *)
(* The formal semantics of labLang.                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/targetSem.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - The record state is lab_state (type variables A, C and FFI, HOL4 'a,   *)
(*   'c and 'ffi); HOL4 s.f is lab_state_f s, s with f := v is               *)
(*   lab_state_f_fupd (K v) s and s with <| f1 := x; f2 := y |> is           *)
(*   lab_state_f1_fupd (K x) (lab_state_f2_fupd (K y) s).                    *)
(* - HOL4 Overload read_reg r s = s.regs r is written out: lab_state_regs s r.*)
(* - The results Halt, Error and TimeOut are targetSem's (target_Halt, ...); *)
(*   word_cmp is wordSem's wl_word_cmp, word_shift is asmSem's               *)
(*   asm_word_shift; the word_loc constructors are wl_Word and wl_Loc.       *)
(* - Words: n2w = word, w2n = val, w2w = word_zx, w2i = ival, i2w = iword,   *)
(*   + = word_add, - = word_sub, / = word_jdiv, (h >< l) = word_extract h l, *)
(*   @@ = word_join, bit_field_insert h l a w = word_insert w (l,(h+1)-l) a;  *)
(*   word8 = byte, word32 = int32, word64 = int64.                           *)
(* - HOL4 a + b + c on numbers is (a + b) + c, written with parentheses      *)
(*   (HOL Light's + is right associative).                                   *)

let word8_loc_INDUCT,word8_loc_RECURSION = cake_type
  "word8_loc = Byte byte | LocByte num num num";;

(* ffi: oracle; io_regs: oracle, the sequence of havoc on registers at each *)
(* FFI call (seq number, ffi name, register); cc_regs: the same for calling *)
(* clear cache; io_fp_regs, cc_fp_regs: oracles, the sequence of havoc on FP *)
(* registers at each FFI call / clear-cache call (a SharedMem call consumes *)
(* an io_fp_regs position without using it: the machine-level counter is    *)
(* shared with ExtCall)                                                      *)

(* HOL4: state *)

let lab_state_INFO = cake_record "lab_state"
  ["regs","num->(A)word_loc";
   "fp_regs","num->int64";
   "mem","A word->(A)word_loc";
   "mem_domain","A word->bool";
   "shared_mem_domain","A word->bool";
   "pc","num";
   "be","bool";
   "ffi","(FFI)ffi_state";
   "io_regs","num->ffiname->num->(A word)option";
   "cc_regs","num->num->(A word)option";
   "io_fp_regs","num->num->int64";
   "cc_fp_regs","num->num->int64";
   "code","((A)sec)list";
   "compile","C->((A)sec)list->(byte list#C)option";
   "compile_oracle","num->C#((A)sec)list";
   "code_buffer","(A,8)buffer";
   "clock","num";
   "failed","bool";
   "ptr_reg","num";
   "len_reg","num";
   "ptr2_reg","num";
   "len2_reg","num";
   "link_reg","num"];;

let lab_state_component_equality = lab_state_INFO.ri_component_equality;;

let is_Label_def = cake_def
  `(is_Label (lab_Label _ _ _:(A)line) <=> T) /\
   (is_Label _ <=> F)`;;

let _ = cake_add_simps [is_Label_def];;

let asm_fetch_aux_def = cake_def
  `(asm_fetch_aux pos ([]:((A)sec)list) = NONE) /\
   (asm_fetch_aux pos (CONS (Section k []) xs) = asm_fetch_aux pos xs) /\
   (asm_fetch_aux pos (CONS (Section k (CONS y ys)) xs) =
      if is_Label y
      then asm_fetch_aux pos (CONS (Section k ys) xs)
      else if pos = 0
           then SOME y
           else asm_fetch_aux (pos - 1) (CONS (Section k ys) xs))`;;

let asm_fetch_aux_ind = cake_ind "asm_fetch_aux";;

let asm_fetch_def = cake_def
  `asm_fetch (s:(A,C,FFI)lab_state) =
     asm_fetch_aux (lab_state_pc s) (lab_state_code s)`;;

(* HOL4: upd_pc_def, upd_reg_def, upd_mem_def, assert_def *)

let lab_upd_pc_def = cake_def
  `lab_upd_pc pc (s:(A,C,FFI)lab_state) = lab_state_pc_fupd (K pc) s`;;

let lab_upd_reg_def = cake_def
  `lab_upd_reg r w (s:(A,C,FFI)lab_state) =
     lab_state_regs_fupd (K ((r =+ w) (lab_state_regs s))) s`;;

let lab_upd_mem_def = cake_def
  `lab_upd_mem a w (s:(A,C,FFI)lab_state) =
     lab_state_mem_fupd (K ((a =+ w) (lab_state_mem s))) s`;;

let lab_assert_def = cake_def
  `lab_assert b (s:(A,C,FFI)lab_state) =
     lab_state_failed_fupd (K (~b \/ lab_state_failed s)) s`;;

(* HOL4: reg_imm_def *)

let lab_reg_imm_def = cake_def
  `(lab_reg_imm (Reg r) (s:(A,C,FFI)lab_state) = lab_state_regs s r) /\
   (lab_reg_imm (Imm w) s = wl_Word w)`;;

let _ = cake_add_simps [lab_reg_imm_def];;

(* HOL4: binop_upd_def *)

let lab_binop_upd_def = cake_def
  `(lab_binop_upd r asm_Add (w1:A word) w2 =
      lab_upd_reg r (wl_Word (word_add w1 w2)):(A,C,FFI)lab_state->(A,C,FFI)lab_state) /\
   (lab_binop_upd r asm_Sub w1 w2 = lab_upd_reg r (wl_Word (word_sub w1 w2))) /\
   (lab_binop_upd r asm_And w1 w2 = lab_upd_reg r (wl_Word (word_and w1 w2))) /\
   (lab_binop_upd r asm_Or w1 w2 = lab_upd_reg r (wl_Word (word_or w1 w2))) /\
   (lab_binop_upd r asm_Xor w1 w2 = lab_upd_reg r (wl_Word (word_xor w1 w2)))`;;

(* HOL4: arith_upd_def *)

let lab_arith_upd_def = cake_def
  `(lab_arith_upd (Binop b r1 r2 (ri:(A)reg_imm)) (s:(A,C,FFI)lab_state) =
      match (lab_state_regs s r2,lab_reg_imm ri s) with
        (wl_Word w1,wl_Word w2) -> lab_binop_upd r1 b w1 w2 s
      | (x,_) -> if b = asm_Or /\ ri = Reg r2 then lab_upd_reg r1 x s
                 else lab_assert F s) /\
   (lab_arith_upd (asm_Shift l r1 r2 ri) s =
      match (lab_state_regs s r2,lab_reg_imm ri s) with
        (wl_Word w1,wl_Word w2) ->
          lab_assert (val w2 < dimindex(:A))
            (lab_upd_reg r1 (wl_Word (asm_word_shift l w1 (val w2))) s)
      | _ -> lab_assert F s) /\
   (lab_arith_upd (asm_Div r1 r2 r3) s =
      match (lab_state_regs s r3,lab_state_regs s r2) with
        (wl_Word q,wl_Word w2) ->
          lab_assert (~(q = word 0)) (lab_upd_reg r1 (wl_Word (word_jdiv w2 q)) s)
      | _ -> lab_assert F s) /\
   (lab_arith_upd (asm_AddCarry r1 r2 r3 r4) s =
      match (lab_state_regs s r2,lab_state_regs s r3,lab_state_regs s r4) with
        (wl_Word w2,wl_Word w3,wl_Word w4) ->
          let r = (val w2 + val w3) + (if w4 = word 0 then 0 else 1) in
          lab_upd_reg r4 (wl_Word (if dimword(:A) <= r then word 1 else word 0))
            (lab_upd_reg r1 (wl_Word (word r)) s)
      | _ -> lab_assert F s) /\
   (lab_arith_upd (LongMul r1 r2 r3 r4) s =
      match (lab_state_regs s r3,lab_state_regs s r4) with
        (wl_Word w3,wl_Word w4) ->
          let r = val w3 * val w4 in
          lab_upd_reg r2 (wl_Word (word r))
            (lab_upd_reg r1 (wl_Word (word (r DIV dimword(:A)))) s)
      | _ -> lab_assert F s) /\
   (lab_arith_upd (LongDiv r1 r2 r3 r4 r5) s =
      match (lab_state_regs s r3,lab_state_regs s r4,lab_state_regs s r5) with
        (wl_Word w3,wl_Word w4,wl_Word w5) ->
          let n = val w3 * dimword(:A) + val w4 in
          let d = val w5 in
          let q = n DIV d in
          lab_assert (~(d = 0) /\ q < dimword(:A))
            (lab_upd_reg r1 (wl_Word (word q))
               (lab_upd_reg r2 (wl_Word (word (n MOD d))) s))
      | _ -> lab_assert F s) /\
   (lab_arith_upd (AddOverflow r1 r2 r3 r4) s =
      match (lab_state_regs s r2,lab_state_regs s r3) with
        (wl_Word w2,wl_Word w3) ->
          lab_upd_reg r4
            (wl_Word (if ~(ival (word_add w2 w3) = ival w2 + ival w3)
                      then word 1 else word 0))
            (lab_upd_reg r1 (wl_Word (word_add w2 w3)) s)
      | _ -> lab_assert F s) /\
   (lab_arith_upd (SubOverflow r1 r2 r3 r4) s =
      match (lab_state_regs s r2,lab_state_regs s r3) with
        (wl_Word w2,wl_Word w3) ->
          lab_upd_reg r4
            (wl_Word (if ~(ival (word_sub w2 w3) = ival w2 - ival w3)
                      then word 1 else word 0))
            (lab_upd_reg r1 (wl_Word (word_sub w2 w3)) s)
      | _ -> lab_assert F s)`;;

let _ = cake_add_simps [lab_arith_upd_def];;

(* HOL4: upd_fp_reg_def, read_fp_reg_def *)

let lab_upd_fp_reg_def = cake_def
  `lab_upd_fp_reg r v (s:(A,C,FFI)lab_state) =
     lab_state_fp_regs_fupd (K ((r =+ v) (lab_state_fp_regs s))) s`;;

let lab_read_fp_reg_def = cake_def
  `lab_read_fp_reg r (s:(A,C,FFI)lab_state) = lab_state_fp_regs s r`;;

(* HOL4: fp_upd_def *)

let lab_fp_upd_def = cake_def
  `(lab_fp_upd (FPLess r d1 d2) (s:(A,C,FFI)lab_state) =
      lab_upd_reg r (wl_Word (if fp64_lessThan (lab_read_fp_reg d1 s)
                                   (lab_read_fp_reg d2 s)
                              then word 1 else word 0)) s) /\
   (lab_fp_upd (FPLessEqual r d1 d2) s =
      lab_upd_reg r (wl_Word (if fp64_lessEqual (lab_read_fp_reg d1 s)
                                   (lab_read_fp_reg d2 s)
                              then word 1 else word 0)) s) /\
   (lab_fp_upd (FPEqual r d1 d2) s =
      lab_upd_reg r (wl_Word (if fp64_equal (lab_read_fp_reg d1 s)
                                   (lab_read_fp_reg d2 s)
                              then word 1 else word 0)) s) /\
   (lab_fp_upd (FPMov d1 d2) s = lab_upd_fp_reg d1 (lab_read_fp_reg d2 s) s) /\
   (lab_fp_upd (FPAbs d1 d2) s =
      lab_upd_fp_reg d1 (fp64_abs (lab_read_fp_reg d2 s)) s) /\
   (lab_fp_upd (FPNeg d1 d2) s =
      lab_upd_fp_reg d1 (fp64_negate (lab_read_fp_reg d2 s)) s) /\
   (lab_fp_upd (FPSqrt d1 d2) s =
      lab_upd_fp_reg d1 (fp64_sqrt roundTiesToEven (lab_read_fp_reg d2 s)) s) /\
   (lab_fp_upd (FPAdd d1 d2 d3) s =
      lab_upd_fp_reg d1
        (fp64_add roundTiesToEven (lab_read_fp_reg d2 s) (lab_read_fp_reg d3 s)) s) /\
   (lab_fp_upd (FPSub d1 d2 d3) s =
      lab_upd_fp_reg d1
        (fp64_sub roundTiesToEven (lab_read_fp_reg d2 s) (lab_read_fp_reg d3 s)) s) /\
   (lab_fp_upd (FPMul d1 d2 d3) s =
      lab_upd_fp_reg d1
        (fp64_mul roundTiesToEven (lab_read_fp_reg d2 s) (lab_read_fp_reg d3 s)) s) /\
   (lab_fp_upd (FPDiv d1 d2 d3) s =
      lab_upd_fp_reg d1
        (fp64_div roundTiesToEven (lab_read_fp_reg d2 s) (lab_read_fp_reg d3 s)) s) /\
   (lab_fp_upd (FPFma d1 d2 d3) s =
      lab_upd_fp_reg d1
        (fpfma (lab_read_fp_reg d1 s) (lab_read_fp_reg d2 s) (lab_read_fp_reg d3 s))
        s) /\
   (lab_fp_upd (FPMovToReg r1 r2 d) s =
      if dimindex(:A) = 64 then
        lab_upd_reg r1 (wl_Word (word_zx (lab_read_fp_reg d s))) s
      else let v = lab_read_fp_reg d s in
        lab_upd_reg r2 (wl_Word (word_extract 63 32 v))
          (lab_upd_reg r1 (wl_Word (word_extract 31 0 v)) s)) /\
   (lab_fp_upd (FPMovFromReg d r1 r2) s =
      if dimindex(:A) = 64 then
        match lab_state_regs s r1 with
          wl_Word w1 -> lab_upd_fp_reg d (word_zx w1) s
        | _ -> lab_assert F s
      else
        match (lab_state_regs s r1,lab_state_regs s r2) with
          (wl_Word w1,wl_Word w2) -> lab_upd_fp_reg d (word_join w2 w1) s
        | _ -> lab_assert F s) /\
   (lab_fp_upd (FPToInt d1 d2) s =
      match fp64_to_int roundTiesToEven (lab_read_fp_reg d2 s) with
        SOME i ->
          let w = iword i:int32 in
          (if dimindex(:A) = 64 then
             lab_upd_fp_reg d1 (word_zx w)
           else let (h,l) = if ODD d1 then (63,32) else (31,0) in
             lab_upd_fp_reg (d1 DIV 2)
               (word_insert (lab_read_fp_reg (d1 DIV 2) s) (l,(h + 1) - l) w))
            (lab_assert (ival w = i) s)
      | _ -> lab_assert F s) /\
   (lab_fp_upd (FPFromInt d1 d2) s =
      let i = if dimindex(:A) = 64 then
                ival (word_extract 31 0 (lab_read_fp_reg d2 s):int32)
              else let v = lab_read_fp_reg (d2 DIV 2) s in
                ival (if ODD d2 then word_extract 63 32 v
                      else word_extract 31 0 v:A word) in
      lab_upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s)`;;

let _ = cake_add_simps [lab_fp_upd_def];;

(* HOL4: addr_def *)

let lab_addr_def = cake_def
  `lab_addr (Addr r offset) (s:(A,C,FFI)lab_state) =
     match lab_state_regs s r with
       wl_Word w -> SOME (word_add w offset)
     | _ -> NONE`;;

let is_Loc_def = cake_def
  `(is_Loc (wl_Loc _ _:(A)word_loc) <=> T) /\ (is_Loc _ <=> F)`;;

(* HOL4: mem_store_def, mem_load_def *)

let lab_mem_store_def = cake_def
  `lab_mem_store r a (s:(A,C,FFI)lab_state) =
     match lab_addr a s with
       NONE -> lab_assert F s
     | SOME w -> lab_assert (val w MOD (dimindex(:A) DIV 8) = 0 /\
                             w IN lab_state_mem_domain s)
                   (lab_upd_mem w (lab_state_regs s r) s)`;;

let lab_mem_load_def = cake_def
  `lab_mem_load r a (s:(A,C,FFI)lab_state) =
     match lab_addr a s with
       NONE -> lab_assert F s
     | SOME w -> lab_assert (val w MOD (dimindex(:A) DIV 8) = 0 /\
                             w IN lab_state_mem_domain s)
                   (lab_upd_reg r (lab_state_mem s w) s)`;;

let mem_load32_def = cake_def
  `mem_load32 r a (s:(A,C,FFI)lab_state) =
     match lab_addr a s with
       NONE -> lab_assert F s
     | SOME w ->
         match mem_load_32 (lab_state_mem s) (lab_state_mem_domain s)
                 (lab_state_be s) w with
           SOME v -> lab_upd_reg r (wl_Word (word_zx v)) s
         | NONE -> lab_assert F s`;;

let mem_store32_def = cake_def
  `mem_store32 r a (s:(A,C,FFI)lab_state) =
     match lab_addr a s with
       NONE -> lab_assert F s
     | SOME w ->
         match lab_state_regs s r with
           wl_Word b ->
             (match mem_store_32 (lab_state_mem s) (lab_state_mem_domain s)
                      (lab_state_be s) w (word_zx b) with
                SOME m -> lab_state_mem_fupd (K m) s
              | NONE -> lab_assert F s)
         | _ -> lab_assert F s`;;

let mem_load_byte_def = cake_def
  `mem_load_byte r a (s:(A,C,FFI)lab_state) =
     match lab_addr a s with
       NONE -> lab_assert F s
     | SOME w ->
         match mem_load_byte_aux (lab_state_mem s) (lab_state_mem_domain s)
                 (lab_state_be s) w with
           SOME v -> lab_upd_reg r (wl_Word (word_zx v)) s
         | NONE -> lab_assert F s`;;

let mem_store_byte_def = cake_def
  `mem_store_byte r a (s:(A,C,FFI)lab_state) =
     match lab_addr a s with
       NONE -> lab_assert F s
     | SOME w ->
         match lab_state_regs s r with
           wl_Word b ->
             (match mem_store_byte_aux (lab_state_mem s) (lab_state_mem_domain s)
                      (lab_state_be s) w (word_zx b) with
                SOME m -> lab_state_mem_fupd (K m) s
              | NONE -> lab_assert F s)
         | _ -> lab_assert F s`;;

(* HOL4: mem_op_def *)

let lab_mem_op_def = cake_def
  `(lab_mem_op asm_Load r a = lab_mem_load r a:(A,C,FFI)lab_state->(A,C,FFI)lab_state) /\
   (lab_mem_op asm_Store r a = lab_mem_store r a) /\
   (lab_mem_op asm_Load32 r a = mem_load32 r a) /\
   (lab_mem_op asm_Store32 r a = mem_store32 r a) /\
   (lab_mem_op Load8 r a = mem_load_byte r a) /\
   (lab_mem_op Store8 r a = mem_store_byte r a) /\
   (lab_mem_op Load16 r (a:(A)addr) = lab_assert F) /\
   (lab_mem_op Store16 r (a:(A)addr) = lab_assert F)`;;

let _ = cake_add_simps [lab_mem_op_def];;

let asm_inst_def = cake_def
  `(asm_inst asm_Skip s = (s:(A,C,FFI)lab_state)) /\
   (asm_inst (asm_Const r imm) s = lab_upd_reg r (wl_Word imm) s) /\
   (asm_inst (asm_Arith x) s = lab_arith_upd x s) /\
   (asm_inst (Mem m r a) s = lab_mem_op m r a s) /\
   (asm_inst (FP fp) s = lab_fp_upd fp s)`;;

let _ = cake_add_simps [asm_inst_def];;

(* HOL4: dec_clock_def *)

let lab_dec_clock_def = cake_def
  `lab_dec_clock (s:(A,C,FFI)lab_state) =
     lab_state_clock_fupd (K (lab_state_clock s - 1)) s`;;

let inc_pc_def = cake_def
  `inc_pc (s:(A,C,FFI)lab_state) = lab_state_pc_fupd (K (lab_state_pc s + 1)) s`;;

let asm_code_length_def = cake_def
  `(asm_code_length ([]:((A)sec)list) = 0) /\
   (asm_code_length (CONS (Section k []) xs) = asm_code_length xs) /\
   (asm_code_length (CONS (Section k (CONS y ys)) xs) =
      asm_code_length (CONS (Section k ys) xs) + (if is_Label y then 0 else 1))`;;

let asm_code_length_ind = cake_ind "asm_code_length";;

(* HOL4: [local] *)

let asm_fetch_IMP = prove
 (`asm_fetch (s:(A,C,FFI)lab_state) = SOME x ==>
   lab_state_pc s < asm_code_length (lab_state_code s)`,
  REWRITE_TAC[asm_fetch_def] THEN
  SPEC_TAC(`lab_state_pc (s:(A,C,FFI)lab_state)`,`pc:num`) THEN
  SPEC_TAC(`lab_state_code (s:(A,C,FFI)lab_state)`,`xs:((A)sec)list`) THEN
  MATCH_MP_TAC asm_code_length_ind THEN
  REWRITE_TAC[asm_fetch_aux_def; asm_code_length_def; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  TRY (DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_CASES_TAC `pc = 0` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRY ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pc - 1`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let lab_to_loc_def = cake_def
  `lab_to_loc (lab_Lab n1 n2) = wl_Loc n1 n2:(A)word_loc`;;

(* HOL4 proves termination automatically: the size of the code decreases *)

let loc_to_pc_def = cake_def_wf
  `MEASURE (\x:num#num#((A)sec)list. list_size (sec_size (\x:A. 0)) (SND (SND x)))`
  TERM_TAC
  `(loc_to_pc n1 n2 ([]:((A)sec)list) = NONE) /\
   (loc_to_pc n1 n2 (CONS (Section k xs) ys) =
      if k = n1 /\ n2 = 0 then SOME 0 else
        match xs with
          [] -> loc_to_pc n1 n2 ys
        | CONS z zs ->
            if (?k. z = lab_Label n1 n2 k) /\ ~(n2 = 0) then SOME 0 else
              if is_Label z then loc_to_pc n1 n2 (CONS (Section k zs) ys)
              else
                match loc_to_pc n1 n2 (CONS (Section k zs) ys) with
                  NONE -> NONE
                | SOME pos -> SOME (pos + 1))`;;

let loc_to_pc_ind = cake_ind "loc_to_pc";;

(* case split on every free variable of type ty of the goal (HOL4 names the *)
(* variables b, m, f after Cases_on; the kit's CASES_ON names them a0, ...) *)

let STACKPAUX_TYPE_CASES_TAC (ty:hol_type) : tactic =
  fun (asl,w as g) ->
    let vs = filter (fun v -> type_of v = ty) (frees w) in
    MAP_EVERY (fun v -> CASES_ON v) vs g;;

let asm_inst_consts = prove
 (`(lab_state_pc (asm_inst i s) = lab_state_pc (s:(A,C,FFI)lab_state)) /\
   (lab_state_code (asm_inst i s) = lab_state_code s) /\
   (lab_state_clock (asm_inst i s) = lab_state_clock s) /\
   (lab_state_ffi (asm_inst i s) = lab_state_ffi s) /\
   (lab_state_io_regs (asm_inst i s) = lab_state_io_regs s) /\
   (lab_state_io_fp_regs (asm_inst i s) = lab_state_io_fp_regs s) /\
   (lab_state_cc_regs (asm_inst i s) = lab_state_cc_regs s) /\
   (lab_state_cc_fp_regs (asm_inst i s) = lab_state_cc_fp_regs s) /\
   (lab_state_ptr_reg (asm_inst i s) = lab_state_ptr_reg s) /\
   (lab_state_len_reg (asm_inst i s) = lab_state_len_reg s) /\
   (lab_state_ptr2_reg (asm_inst i s) = lab_state_ptr2_reg s) /\
   (lab_state_len2_reg (asm_inst i s) = lab_state_len2_reg s) /\
   (lab_state_link_reg (asm_inst i s) = lab_state_link_reg s)`,
  CASES_ON `i:(A)inst` THEN SIMP[asm_inst_def; lab_upd_reg_def] THENL
   [STACKPAUX_TYPE_CASES_TAC `:(A)asm_arith` THEN SIMP[lab_arith_upd_def] THEN
    EVERY_CASE_TAC THEN STACKPAUX_TYPE_CASES_TAC `:binop` THEN
    SIMP[lab_binop_upd_def; lab_upd_reg_def; lab_assert_def];
    STACKPAUX_TYPE_CASES_TAC `:memop` THEN
    SIMP[lab_mem_op_def; lab_mem_load_def; lab_upd_mem_def;
         mem_load32_def; mem_store32_def; lab_assert_def; lab_upd_reg_def;
         lab_mem_store_def; mem_store_byte_def; mem_load_byte_def;
         mem_store_byte_aux_def; lab_addr_def] THEN
    EVERY_CASE_TAC THEN SIMP[];
    STACKPAUX_TYPE_CASES_TAC `:fp` THEN
    SIMP[lab_fp_upd_def; lab_upd_reg_def; lab_upd_fp_reg_def; lab_assert_def] THEN
    EVERY_CASE_TAC THEN SIMP[lab_upd_fp_reg_def]]);;

let get_pc_value_def = cake_def
  `get_pc_value lab (s:(A,C,FFI)lab_state) =
     match lab with lab_Lab n1 n2 -> loc_to_pc n1 n2 (lab_state_code s)`;;

let next_label_def = cake_def_wf
  `MEASURE (list_size (sec_size (\x:A. 0)))`
  TERM_TAC
  `(next_label ([]:((A)sec)list) = NONE:((A)word_loc)option) /\
   (next_label (CONS (Section k []) xs) = next_label xs) /\
   (next_label (CONS (Section k (CONS (lab_Label n1 n2 _) ys)) xs) =
      SOME (wl_Loc n1 n2)) /\
   (next_label (CONS (Section k (CONS y ys)) xs) =
      next_label (CONS (Section k ys) xs))`;;

let next_label_ind = cake_ind "next_label";;

let get_lab_after_def = cake_def_wf
  `MEASURE (\x:num#((A)sec)list. list_size (sec_size (\x:A. 0)) (SND x))`
  TERM_TAC
  `(get_lab_after pos ([]:((A)sec)list) = NONE:((A)word_loc)option) /\
   (get_lab_after pos (CONS (Section k []) xs) = get_lab_after pos xs) /\
   (get_lab_after pos (CONS (Section k (CONS y ys)) xs) =
      if is_Label y
      then get_lab_after pos (CONS (Section k ys) xs)
      else if pos = 0
           then next_label (CONS (Section k ys) xs)
           else get_lab_after (pos - 1) (CONS (Section k ys) xs))`;;

let get_lab_after_ind = cake_ind "get_lab_after";;

let get_ret_Loc_def = cake_def
  `get_ret_Loc (s:(A,C,FFI)lab_state) =
     get_lab_after (lab_state_pc s) (lab_state_code s)`;;

let share_mem_load_def = cake_def
  `share_mem_load r ad (s:(A,C,FFI)lab_state) n =
     match lab_addr ad s with
       NONE -> NONE
     | SOME v ->
         if (if n = 0
             then val v MOD (dimindex(:A) DIV 8) = 0 /\
                  v IN lab_state_shared_mem_domain s
             else byte_align v IN lab_state_shared_mem_domain s)
         then
           (match call_FFI (lab_state_ffi s) (SharedMem MappedRead) [word n]
                    (word_to_bytes v F) with
              FFI_final outcome -> SOME (FFI_final outcome,s)
            | FFI_return new_ffi new_bytes ->
                SOME (FFI_return new_ffi new_bytes,
                      lab_state_ffi_fupd (K new_ffi)
                        (lab_state_regs_fupd
                           (K ((r =+ wl_Word (word_of_bytes F (word 0) new_bytes))
                                 (lab_state_regs s)))
                        (lab_state_pc_fupd (K (lab_state_pc s + 1))
                        (lab_state_clock_fupd (K (lab_state_clock s - 1)) s)))))
         else NONE`;;

let share_mem_store_def = cake_def
  `share_mem_store r ad (s:(A,C,FFI)lab_state) n =
     match lab_state_regs s r with
       wl_Word w ->
         (match lab_addr ad s with
            NONE -> NONE
          | SOME v ->
              if (if n = 0
                  then val v MOD (dimindex(:A) DIV 8) = 0 /\
                       v IN lab_state_shared_mem_domain s
                  else byte_align v IN lab_state_shared_mem_domain s)
              then
                (match call_FFI (lab_state_ffi s) (SharedMem MappedWrite) [word n]
                         (APPEND (if n = 0 then word_to_bytes w F
                                  else TAKE n (word_to_bytes w F))
                                 (word_to_bytes v F)) with
                   FFI_final outcome -> SOME (FFI_final outcome,s)
                 | FFI_return new_ffi new_bytes ->
                     SOME (FFI_return new_ffi new_bytes,
                           inc_pc (lab_dec_clock (lab_state_ffi_fupd (K new_ffi) s))))
              else NONE)
     | _ -> NONE`;;

let share_mem_op_def = cake_def
  `(share_mem_op asm_Load r ad (s:(A,C,FFI)lab_state) = share_mem_load r ad s 0) /\
   (share_mem_op Load8 r ad s = share_mem_load r ad s 1) /\
   (share_mem_op Load16 r ad s = share_mem_load r ad s 2) /\
   (share_mem_op asm_Store r ad s = share_mem_store r ad s 0) /\
   (share_mem_op Store8 r ad s = share_mem_store r ad s 1) /\
   (share_mem_op Store16 r ad s = share_mem_store r ad s 2) /\
   (share_mem_op asm_Load32 r ad s = share_mem_load r ad s 4) /\
   (share_mem_op asm_Store32 r ad s = share_mem_store r ad s 4)`;;

(* the clock fact behind the termination of lab_evaluate in the ShareMem   *)
(* case (HOL4 derives it inside the termination proof)                      *)

let STACKPAUX_share_mem_op_clock = prove
 (`share_mem_op m r ad (s:(A,C,FFI)lab_state) = SOME (FFI_return x y,s') ==>
   lab_state_clock s' = lab_state_clock s - 1`,
  CASES_ON `m:memop` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def] THEN
  EVERY_CASE_TAC THEN
  SIMP[inc_pc_def; lab_dec_clock_def] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

(* HOL4: evaluate_def; Termination WF_REL_TAC measure (\s. s.clock), with  *)
(* asm_inst_consts and the definitions of the state updates                 *)

let lab_evaluate_def = cake_def_wf
  `MEASURE (lab_state_clock:(A,C,FFI)lab_state->num)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def;
                                lab_upd_reg_def]) THEN
   REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def] THEN
   SIMP[asm_inst_consts] THEN
   TRY (FIRST_X_ASSUM(MP_TAC o MATCH_MP STACKPAUX_share_mem_op_clock) THEN
        SIMP[]) THEN
   ASM_ARITH_TAC)
  `lab_evaluate (s:(A,C,FFI)lab_state) =
     if lab_state_clock s = 0 then (target_TimeOut,s) else
     match asm_fetch s with
       SOME (Asm (Asmi a) _ _) ->
         (match a with
            asm_Inst i ->
              (let s1 = asm_inst i s in
               if lab_state_failed s1 then (target_Error,s)
               else lab_evaluate (inc_pc (lab_dec_clock s1)))
          | JumpReg r ->
              (match lab_state_regs s r with
                 wl_Loc n1 n2 ->
                   (match loc_to_pc n1 n2 (lab_state_code s) with
                      NONE -> (target_Error,s)
                    | SOME p -> lab_evaluate (lab_upd_pc p (lab_dec_clock s)))
               | _ -> (target_Error,s))
          | _ -> (target_Error,s))
     | SOME (Asm (Cbw r1 r2) _ _) ->
         (match (lab_state_regs s r1,lab_state_regs s r2) with
            (wl_Word w1,wl_Word w2) ->
              (match buffer_write (lab_state_code_buffer s) w1 (word_zx w2) with
                 SOME new_cb ->
                   lab_evaluate
                     (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K new_cb) s)))
               | _ -> (target_Error,s))
          | _ -> (target_Error,s))
     | SOME (Asm (ShareMem m r ad) _ _) ->
         (match share_mem_op m r ad s with
            SOME (FFI_final outcome,s') -> (target_Halt (FFI_outcome outcome),s')
          | SOME (FFI_return new_ffi new_bytes,s') ->
              lab_evaluate
                (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                   (lab_state_io_fp_regs_fupd
                      (K (shift_seq 1 (lab_state_io_fp_regs s'))) s'))
          | NONE -> (target_Error,s))
     | SOME (LabAsm lab_Halt _ _ _) ->
         (match lab_state_regs s (lab_state_ptr_reg s) with
            wl_Word w -> if w = word 0 then (target_Halt Success,s)
                         else (target_Halt Resource_limit_hit,s)
          | _ -> (target_Error,s))
     | SOME (LabAsm (lab_LocValue r lab) _ _ _) ->
         (if get_pc_value lab s = NONE then (target_Error,s) else
            let s1 = lab_upd_reg r (lab_to_loc lab) s in
            lab_evaluate (inc_pc (lab_dec_clock s1)))
     | SOME (LabAsm (lab_Jump l) _ _ _) ->
         (match get_pc_value l s with
            NONE -> (target_Error,s)
          | SOME p -> lab_evaluate (lab_upd_pc p (lab_dec_clock s)))
     | SOME (LabAsm (lab_JumpCmp c r ri l) _ _ _) ->
         (match wl_word_cmp c (lab_state_regs s r) (lab_reg_imm ri s) with
            NONE -> (target_Error,s)
          | SOME b ->
              if b then
                (match get_pc_value l s with
                   NONE -> (target_Error,s)
                 | SOME p -> lab_evaluate (lab_upd_pc p (lab_dec_clock s)))
              else lab_evaluate (inc_pc (lab_dec_clock s)))
     | SOME (LabAsm (lab_Call l) _ _ _) ->
         (match get_pc_value l s with
            NONE -> (target_Error,s)
          | SOME p ->
              (match get_ret_Loc s with
                 NONE -> (target_Error,s)
               | SOME k ->
                   let s1 = lab_upd_reg (lab_state_link_reg s) k s in
                   lab_evaluate (lab_upd_pc p (lab_dec_clock s1))))
     | SOME (LabAsm lab_Install _ _ _) ->
         (match (lab_state_regs s (lab_state_ptr_reg s),
                 lab_state_regs s (lab_state_len_reg s),
                 lab_state_regs s (lab_state_link_reg s)) with
            (wl_Word w1,wl_Word w2,wl_Loc n1 n2) ->
              (match (buffer_flush (lab_state_code_buffer s) w1 w2,
                      loc_to_pc n1 n2 (lab_state_code s)) with
                 (SOME (bytes,cb),SOME new_pc) ->
                   let (cfg,prog) = lab_state_compile_oracle s 0 in
                   let new_oracle = shift_seq 1 (lab_state_compile_oracle s) in
                   (match (lab_state_compile s cfg prog,prog) with
                      (SOME (bytes',cfg'),CONS (Section k _) _) ->
                        if bytes = bytes' /\ FST (new_oracle 0) = cfg' then
                          lab_evaluate
                            (lab_state_pc_fupd (K new_pc)
                            (lab_state_code_buffer_fupd (K cb)
                            (lab_state_code_fupd (K (APPEND (lab_state_code s) prog))
                            (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s)))
                            (lab_state_cc_fp_regs_fupd
                               (K (shift_seq 1 (lab_state_cc_fp_regs s)))
                            (lab_state_regs_fupd
                               (K ((lab_state_ptr_reg s =+ wl_Loc k 0)
                                     (\a. get_reg_value (lab_state_cc_regs s 0 a)
                                            (lab_state_regs s a) wl_Word)))
                            (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s 0 n))
                            (lab_state_compile_oracle_fupd (K new_oracle)
                            (lab_state_clock_fupd (K (lab_state_clock s - 1)) s)))))))))
                        else (target_Error,s)
                    | _ -> (target_Error,s))
               | _ -> (target_Error,s))
          | _ -> (target_Error,s))
     | SOME (LabAsm (CallFFI ffi_index) _ _ _) ->
         (match (lab_state_regs s (lab_state_len_reg s),
                 lab_state_regs s (lab_state_ptr_reg s),
                 lab_state_regs s (lab_state_len2_reg s),
                 lab_state_regs s (lab_state_ptr2_reg s),
                 lab_state_regs s (lab_state_link_reg s)) with
            (wl_Word w,wl_Word w2,wl_Word w3,wl_Word w4,wl_Loc n1 n2) ->
              (match (read_bytearray w2 (val w)
                        (mem_load_byte_aux (lab_state_mem s) (lab_state_mem_domain s)
                           (lab_state_be s)),
                      read_bytearray w4 (val w3)
                        (mem_load_byte_aux (lab_state_mem s) (lab_state_mem_domain s)
                           (lab_state_be s)),
                      loc_to_pc n1 n2 (lab_state_code s)) with
                 (SOME bytes,SOME bytes2,SOME new_pc) ->
                   (match call_FFI (lab_state_ffi s) (ExtCall ffi_index) bytes bytes2 with
                      FFI_final outcome -> (target_Halt (FFI_outcome outcome),s)
                    | FFI_return new_ffi new_bytes ->
                        let new_io_regs = shift_seq 1 (lab_state_io_regs s) in
                        let new_io_fp_regs = shift_seq 1 (lab_state_io_fp_regs s) in
                        let new_m = write_bytearray w4 new_bytes (lab_state_mem s)
                                      (lab_state_mem_domain s) (lab_state_be s) in
                        lab_evaluate
                          (lab_state_mem_fupd (K new_m)
                          (lab_state_ffi_fupd (K new_ffi)
                          (lab_state_io_regs_fupd (K new_io_regs)
                          (lab_state_io_fp_regs_fupd (K new_io_fp_regs)
                          (lab_state_regs_fupd
                             (K (\a. get_reg_value
                                       (lab_state_io_regs s 0 (ExtCall ffi_index) a)
                                       (lab_state_regs s a) wl_Word))
                          (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s 0 n))
                          (lab_state_pc_fupd (K new_pc)
                          (lab_state_clock_fupd (K (lab_state_clock s - 1)) s)))))))))
               | _ -> (target_Error,s))
          | _ -> (target_Error,s))
     | _ -> (target_Error,s)`;;

let lab_evaluate_ind = cake_ind "lab_evaluate";;

(* HOL4: semantics_def *)

let lab_semantics_def = cake_def
  `lab_semantics (s:(A,C,FFI)lab_state) =
     if ?k. FST (lab_evaluate (lab_state_clock_fupd (K k) s)) = target_Error then Fail
     else
       match some res.
               ?k t outcome.
                 lab_evaluate (lab_state_clock_fupd (K k) s) = (target_Halt outcome,t) /\
                 res = Terminate outcome (ffi_state_io_events (lab_state_ffi t)) with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (lab_state_ffi
                                    (SND (lab_evaluate (lab_state_clock_fupd (K k) s))))))
                       UNIV))`;;
