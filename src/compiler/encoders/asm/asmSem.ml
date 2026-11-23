(* ========================================================================= *)
(* asmSem: port of HOL4 compiler/encoders/asm/asmSemScript.sml (CakeML       *)
(* v3479).  The semantics of the asm instruction description.                *)
(* HOL4 asm is asm_asm (a short or common word), and asm_def is asm_asm_def. *)
(* ========================================================================= *)

needs "compiler/encoders/asm/asm.ml";;
needs "hol4/machine_ieee.ml";;
needs "misc/misc.ml";;

type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - Record asm_state: HOL4 s.f is asm_state_f s; s with f := v is           *)
(*   asm_state_f_fupd (K v) s.  word64 is int64, word8 is byte, word32 is    *)
(*   int32.                                                                  *)
(* - Words (hol4/words4.ml): n2w = word, w2n = val, w2w = word_zx,          *)
(*   w2i = ival, i2w = iword, << = word_shl, >>> = word_ushr,               *)
(*   >> = word_ishr, / (word_quot) = word_jdiv, (h >< l) = word_extract h l, *)
(*   @@ = word_join, bit_field_insert h l a w = word_insert w (l,(h+1)-l) a, *)
(*   aligned = alignment_aligned.                                            *)
(* - Constants with names.tsv prefixes: asm_upd_pc, asm_upd_reg,             *)
(*   asm_upd_fp_reg, asm_upd_mem, asm_read_fp_reg, asm_read_mem,             *)
(*   asm_assert, asm_reg_imm, asm_binop_upd, asm_word_shift, asm_arith_upd,  *)
(*   asm_fp_upd, asm_addr, asm_mem_load, asm_mem_store, asm_mem_op and       *)
(*   asmSem_inst (HOL4 inst); read_reg, read_mem_word, write_mem_word,       *)
(*   is_test, jump_to_offset and asm_step keep their names; asm is asm_asm.  *)
(* - HOL4 + is left-associative: a + b + c is written (a + b) + c.           *)

(* -- semantics of ASM program -- *)
let asm_state_INFO = cake_record "asm_state"
  ["regs","num->A word";
   "fp_regs","num->int64";
   "mem","A word->byte";
   "mem_domain","A word->bool";
   "pc","A word";
   "lr","asm_reg";
   "align","num";
   "be","bool";
   "failed","bool"];;

let asm_state_component_equality = asm_state_INFO.ri_component_equality;;

let asm_upd_pc_def = cake_def
  `asm_upd_pc pc (s:(A)asm_state) = asm_state_pc_fupd (K pc) s`;;

let asm_upd_reg_def = cake_def
  `asm_upd_reg r v (s:(A)asm_state) =
     asm_state_regs_fupd (K ((r =+ v) (asm_state_regs s))) s`;;

let asm_upd_fp_reg_def = cake_def
  `asm_upd_fp_reg r v (s:(A)asm_state) =
     asm_state_fp_regs_fupd (K ((r =+ v) (asm_state_fp_regs s))) s`;;

let asm_upd_mem_def = cake_def
  `asm_upd_mem a b (s:(A)asm_state) =
     asm_state_mem_fupd (K ((a =+ b) (asm_state_mem s))) s`;;

let read_reg_def = cake_def
  `read_reg r (s:(A)asm_state) = asm_state_regs s r`;;

let asm_read_fp_reg_def = cake_def
  `asm_read_fp_reg r (s:(A)asm_state) = asm_state_fp_regs s r`;;

let asm_read_mem_def = cake_def
  `asm_read_mem a (s:(A)asm_state) = asm_state_mem s a`;;

let asm_assert_def = cake_def
  `asm_assert b (s:(A)asm_state) =
     asm_state_failed_fupd (K (~b \/ asm_state_failed s)) s`;;

let asm_reg_imm_def = cake_def
  `(asm_reg_imm (Reg r) (s:(A)asm_state) = read_reg r s) /\
   (asm_reg_imm (Imm w) s = w)`;;

let asm_binop_upd_def = cake_def
  `(asm_binop_upd r asm_Add (w1:A word) w2 = asm_upd_reg r (word_add w1 w2)) /\
   (asm_binop_upd r asm_Sub w1 w2 = asm_upd_reg r (word_sub w1 w2)) /\
   (asm_binop_upd r asm_And w1 w2 = asm_upd_reg r (word_and w1 w2)) /\
   (asm_binop_upd r asm_Or w1 w2 = asm_upd_reg r (word_or w1 w2)) /\
   (asm_binop_upd r asm_Xor w1 w2 = asm_upd_reg r (word_xor w1 w2))`;;

let is_test_def = cake_def
  `is_test c <=> c = asm_Test \/ c = NotTest`;;

let asm_word_shift_def = cake_def
  `(asm_word_shift Lsl (w:A word) n = word_shl w n) /\
   (asm_word_shift Lsr w n = word_ushr w n) /\
   (asm_word_shift Asr w n = word_ishr w n) /\
   (asm_word_shift Ror w n = word_ror w n)`;;

let asm_arith_upd_def = cake_def
  `(asm_arith_upd (Binop b r1 r2 (ri:(A)reg_imm)) (s:(A)asm_state) =
      asm_binop_upd r1 b (read_reg r2 s) (asm_reg_imm ri s) s) /\
   (asm_arith_upd (asm_Shift l r1 r2 ri) s =
      asm_assert (match ri with
                    Reg r -> val (read_reg r s) < dimindex(:A)
                  | _ -> T)
        (asm_upd_reg r1 (asm_word_shift l (read_reg r2 s) (val (asm_reg_imm ri s)))
           s)) /\
   (asm_arith_upd (asm_Div r1 r2 r3) s =
      let q = read_reg r3 s in
      asm_assert (~(q = word 0)) (asm_upd_reg r1 (word_jdiv (read_reg r2 s) q) s)) /\
   (asm_arith_upd (LongMul r1 r2 r3 r4) s =
      let r = val (read_reg r3 s) * val (read_reg r4 s) in
      asm_upd_reg r2 (word r) (asm_upd_reg r1 (word (r DIV dimword(:A))) s)) /\
   (asm_arith_upd (LongDiv r1 r2 r3 r4 r5) s =
      let n = val (read_reg r3 s) * dimword(:A) + val (read_reg r4 s) in
      let d = val (read_reg r5 s) in
      let q = n DIV d in
      asm_assert (~(d = 0) /\ q < dimword(:A))
        (asm_upd_reg r1 (word q) (asm_upd_reg r2 (word (n MOD d)) s))) /\
   (asm_arith_upd (asm_AddCarry r1 r2 r3 r4) s =
      let r = (val (read_reg r2 s) + val (read_reg r3 s)) +
              (if read_reg r4 s = word 0 then 0 else 1) in
      asm_upd_reg r4 (if dimword(:A) <= r then word 1 else word 0)
        (asm_upd_reg r1 (word r) s)) /\
   (asm_arith_upd (AddOverflow r1 r2 r3 r4) s =
      let w2 = read_reg r2 s in
      let w3 = read_reg r3 s in
      asm_upd_reg r4
        (if ~(ival (word_add w2 w3) = ival w2 + ival w3) then word 1 else word 0)
        (asm_upd_reg r1 (word_add w2 w3) s)) /\
   (asm_arith_upd (SubOverflow r1 r2 r3 r4) s =
      let w2 = read_reg r2 s in
      let w3 = read_reg r3 s in
      asm_upd_reg r4
        (if ~(ival (word_sub w2 w3) = ival w2 - ival w3) then word 1 else word 0)
        (asm_upd_reg r1 (word_sub w2 w3) s))`;;

let asm_fp_upd_def = cake_def
  `(asm_fp_upd (FPLess r d1 d2) (s:(A)asm_state) =
      asm_upd_reg r (if fp64_lessThan (asm_read_fp_reg d1 s) (asm_read_fp_reg d2 s)
                     then word 1 else word 0) s) /\
   (asm_fp_upd (FPLessEqual r d1 d2) s =
      asm_upd_reg r (if fp64_lessEqual (asm_read_fp_reg d1 s) (asm_read_fp_reg d2 s)
                     then word 1 else word 0) s) /\
   (asm_fp_upd (FPEqual r d1 d2) s =
      asm_upd_reg r (if fp64_equal (asm_read_fp_reg d1 s) (asm_read_fp_reg d2 s)
                     then word 1 else word 0) s) /\
   (asm_fp_upd (FPMov d1 d2) s = asm_upd_fp_reg d1 (asm_read_fp_reg d2 s) s) /\
   (asm_fp_upd (FPAbs d1 d2) s =
      asm_upd_fp_reg d1 (fp64_abs (asm_read_fp_reg d2 s)) s) /\
   (asm_fp_upd (FPNeg d1 d2) s =
      asm_upd_fp_reg d1 (fp64_negate (asm_read_fp_reg d2 s)) s) /\
   (asm_fp_upd (FPSqrt d1 d2) s =
      asm_upd_fp_reg d1 (fp64_sqrt roundTiesToEven (asm_read_fp_reg d2 s)) s) /\
   (asm_fp_upd (FPAdd d1 d2 d3) s =
      asm_upd_fp_reg d1
        (fp64_add roundTiesToEven (asm_read_fp_reg d2 s) (asm_read_fp_reg d3 s)) s) /\
   (asm_fp_upd (FPSub d1 d2 d3) s =
      asm_upd_fp_reg d1
        (fp64_sub roundTiesToEven (asm_read_fp_reg d2 s) (asm_read_fp_reg d3 s)) s) /\
   (asm_fp_upd (FPMul d1 d2 d3) s =
      asm_upd_fp_reg d1
        (fp64_mul roundTiesToEven (asm_read_fp_reg d2 s) (asm_read_fp_reg d3 s)) s) /\
   (asm_fp_upd (FPDiv d1 d2 d3) s =
      asm_upd_fp_reg d1
        (fp64_div roundTiesToEven (asm_read_fp_reg d2 s) (asm_read_fp_reg d3 s)) s) /\
   (asm_fp_upd (FPFma d1 d2 d3) s =
      asm_upd_fp_reg d1
        (fp64_mul_add roundTiesToEven (asm_read_fp_reg d2 s) (asm_read_fp_reg d3 s)
           (asm_read_fp_reg d1 s)) s) /\
   (asm_fp_upd (FPMovToReg r1 r2 d) s =
      if dimindex(:A) = 64 then
        asm_upd_reg r1 (word_zx (asm_read_fp_reg d s)) s
      else let v = asm_read_fp_reg d s in
        asm_upd_reg r2 (word_extract 63 32 v) (asm_upd_reg r1 (word_extract 31 0 v) s)) /\
   (asm_fp_upd (FPMovFromReg d r1 r2) s =
      asm_upd_fp_reg d
        (if dimindex(:A) = 64 then
           word_zx (read_reg r1 s)
         else
           word_join (read_reg r2 s) (read_reg r1 s)) s) /\
   (asm_fp_upd (FPToInt d1 d2) s =
      match fp64_to_int roundTiesToEven (asm_read_fp_reg d2 s) with
        SOME i ->
          let w = iword i:int32 in
          (if dimindex(:A) = 64 then
             asm_upd_fp_reg d1 (word_zx w)
           else let (h,l) = if ODD d1 then (63,32) else (31,0) in
             asm_upd_fp_reg (d1 DIV 2)
               (word_insert (asm_read_fp_reg (d1 DIV 2) s) (l,(h + 1) - l) w))
            (asm_assert (ival w = i) s)
      | _ -> asm_assert F s) /\
   (asm_fp_upd (FPFromInt d1 d2) s =
      let i = if dimindex(:A) = 64 then
                ival (word_extract 31 0 (asm_read_fp_reg d2 s):int32)
              else let v = asm_read_fp_reg (d2 DIV 2) s in
                ival (if ODD d2 then word_extract 63 32 v else word_extract 31 0 v:A word) in
      asm_upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s)`;;

let asm_addr_def = cake_def
  `asm_addr (Addr r offset) (s:(A)asm_state) = word_add (read_reg r s) offset`;;

let read_mem_word_def = cake_def
  `(read_mem_word (a:A word) 0 (s:(A)asm_state) = (word 0:A word,s)) /\
   (read_mem_word a (SUC n) s =
      let (w,s1) = read_mem_word (if asm_state_be s then word_sub a (word 1)
                                  else word_add a (word 1)) n s in
      (word_or (word_shl w 8) (word_zx (asm_read_mem a s1)),
       asm_assert (a IN asm_state_mem_domain s1) s1))`;;

let read_mem_word_ind = cake_ind "read_mem_word";;

let asm_mem_load_def = cake_def
  `asm_mem_load n r (a:(A)addr) (s:(A)asm_state) =
     let a = asm_addr a s in
     let (w,s) = read_mem_word (if asm_state_be s then word_add a (word (n - 1))
                                else a) n s in
     let s = asm_upd_reg r w s in
     asm_assert (alignment_aligned (LOG2 n) a) s`;;

let write_mem_word_def = cake_def
  `(write_mem_word (a:A word) 0 (w:A word) (s:(A)asm_state) = s) /\
   (write_mem_word a (SUC n) w s =
      let s1 = write_mem_word (if asm_state_be s then word_sub a (word 1)
                               else word_add a (word 1)) n (word_ushr w 8) s in
      asm_assert (a IN asm_state_mem_domain s1) (asm_upd_mem a (word_zx w) s1))`;;

let write_mem_word_ind = cake_ind "write_mem_word";;

let asm_mem_store_def = cake_def
  `asm_mem_store n r (a:(A)addr) (s:(A)asm_state) =
     let a = asm_addr a s in
     let w = read_reg r s in
     let s = write_mem_word (if asm_state_be s then word_add a (word (n - 1))
                             else a) n w s in
     asm_assert (alignment_aligned (LOG2 n) a) s`;;

let asm_mem_op_def = cake_def
  `(asm_mem_op asm_Load r (a:(A)addr) = asm_mem_load (dimindex(:A) DIV 8) r a) /\
   (asm_mem_op asm_Store r a = asm_mem_store (dimindex(:A) DIV 8) r a) /\
   (asm_mem_op Load8 r a = asm_mem_load 1 r a) /\
   (asm_mem_op Store8 r a = asm_mem_store 1 r a) /\
   (asm_mem_op Load16 r a = asm_mem_load 2 r a) /\
   (asm_mem_op Store16 r a = asm_mem_store 2 r a) /\
   (asm_mem_op asm_Load32 r a = asm_mem_load 4 r a) /\
   (asm_mem_op asm_Store32 r a = asm_mem_store 4 r a)`;;

let asmSem_inst_def = cake_def
  `(asmSem_inst (asm_Skip:(A)inst) (s:(A)asm_state) = s) /\
   (asmSem_inst (asm_Const r imm) s = asm_upd_reg r imm s) /\
   (asmSem_inst (asm_Arith x) s = asm_arith_upd x s) /\
   (asmSem_inst (Mem m r a) s = asm_mem_op m r a s) /\
   (asmSem_inst (FP fp) s = asm_fp_upd fp s)`;;

let jump_to_offset_def = cake_def
  `jump_to_offset w (s:(A)asm_state) = asm_upd_pc (word_add (asm_state_pc s) w) s`;;

let asm_asm_def = cake_def
  `(asm_asm (asm_Inst i) pc (s:(A)asm_state) = asm_upd_pc pc (asmSem_inst i s)) /\
   (asm_asm (asm_Jump l) pc s = jump_to_offset l s) /\
   (asm_asm (asm_JumpCmp cmp r ri l) pc s =
      if asm_word_cmp cmp (read_reg r s) (asm_reg_imm ri s)
      then jump_to_offset l s
      else asm_upd_pc pc s) /\
   (asm_asm (asm_Call l) pc s = jump_to_offset l (asm_upd_reg (asm_state_lr s) pc s)) /\
   (asm_asm (JumpReg r) pc s =
      let a = read_reg r s in
      asm_upd_pc a (asm_assert (alignment_aligned (asm_state_align s) a) s)) /\
   (asm_asm (asm_Loc r l) pc s =
      asm_upd_pc pc (asm_upd_reg r (word_add (asm_state_pc s) l) s))`;;

let asm_step_def = cake_def
  `asm_step (c:(A)asm_config) s1 i s2 <=>
     bytes_in_memory (asm_state_pc s1) (asm_config_encode c i) (asm_state_mem s1)
       (asm_state_mem_domain s1) /\
     (match asm_config_link_reg c with SOME r -> asm_state_lr s1 = r | NONE -> T) /\
     asm_state_be s1 = asm_config_big_endian c /\
     asm_state_align s1 = asm_config_code_alignment c /\
     asm_asm i (word_add (asm_state_pc s1) (word (LENGTH (asm_config_encode c i)))) s1 = s2 /\
     ~asm_state_failed s2 /\ asm_ok i c`;;
