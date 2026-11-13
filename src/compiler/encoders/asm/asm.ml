(* ========================================================================= *)
(* asm: port of HOL4 compiler/encoders/asm/asmScript.sml (CakeML v3479).     *)
(* The syntax of a small general-purpose machine instruction description     *)
(* (without labels) and its target-specific configuration.                   *)
(* ========================================================================= *)

needs "hol4/words4.ml";;
needs "semantics/ast.ml";;

type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 type abbreviations: reg and fp_reg (num) are the HOL Light type    *)
(*   abbreviations asm_reg and fp_reg; imm = A word is written out.          *)
(* - Constructors and the clashing constants have the names of names.tsv    *)
(*   (asm_Add, asm_Skip, asm_offset_ok, asm_word_cmp, ...).                 *)
(* - Words (hol4/words4.ml): n2w = word, w2n = val, -1w = word_neg (word 1), *)
(*   signed <= and < = word_ile and word_ilt, <+ = word_ult, && = word_and; *)
(*   aligned = alignment_aligned.                                            *)
(* - HOL4 set enumerations {a; b} are written {a, b}.                         *)
(* - The HOL4 Overloads addr_offset_ok, hw_offset_ok, byte_offset_ok,       *)
(*   jump_offset_ok, cjump_offset_ok and loc_offset_ok are abbreviations     *)
(*   only: their expansions (asm_offset_ok 0 (asm_config_addr_offset c),    *)
(*   asm_offset_ok (asm_config_code_alignment c) (asm_config_jump_offset c), *)
(*   ...) are written out where used.                                        *)

(* -- syntax of ASM instruction -- *)

new_type_abbrev("asm_reg",`:num`);;
new_type_abbrev("fp_reg",`:num`);;

(* HOL4: Type imm = ``:'a word``  (written out where used) *)

let reg_imm_INDUCT,reg_imm_RECURSION = cake_type
  "reg_imm = Reg asm_reg | Imm (A word)";;

let binop_INDUCT,binop_RECURSION = cake_type
  "binop = asm_Add | asm_Sub | asm_And | asm_Or | asm_Xor";;

let cmp_INDUCT,cmp_RECURSION = cake_type
  "cmp = asm_Equal | Lower | asm_Less | asm_Test
       | NotEqual | NotLower | NotLess | NotTest";;

let asm_arith_INDUCT,asm_arith_RECURSION = cake_type
  "asm_arith = Binop binop asm_reg asm_reg ((A)reg_imm)
             | asm_Shift shift asm_reg asm_reg ((A)reg_imm)
             | asm_Div asm_reg asm_reg asm_reg
             | LongMul asm_reg asm_reg asm_reg asm_reg
             | LongDiv asm_reg asm_reg asm_reg asm_reg asm_reg
             | asm_AddCarry asm_reg asm_reg asm_reg asm_reg
             | AddOverflow asm_reg asm_reg asm_reg asm_reg
             | SubOverflow asm_reg asm_reg asm_reg asm_reg";;

(* orderings: FPLess, FPLessEqual, FPEqual; unary ops: FPAbs, FPNeg          *)
(* (IEEE754:2008), FPSqrt; binary ops: FPAdd, FPSub, FPMul, FPDiv; ternary   *)
(* op: FPFma; moves and converts: FPMov, FPMovToReg, FPMovFromReg, FPToInt,  *)
(* FPFromInt                                                                 *)

let fp_INDUCT,fp_RECURSION = cake_type
  "fp = FPLess asm_reg fp_reg fp_reg
      | FPLessEqual asm_reg fp_reg fp_reg
      | FPEqual asm_reg fp_reg fp_reg
      | FPAbs fp_reg fp_reg
      | FPNeg fp_reg fp_reg
      | FPSqrt fp_reg fp_reg
      | FPAdd fp_reg fp_reg fp_reg
      | FPSub fp_reg fp_reg fp_reg
      | FPMul fp_reg fp_reg fp_reg
      | FPDiv fp_reg fp_reg fp_reg
      | FPFma fp_reg fp_reg fp_reg
      | FPMov fp_reg fp_reg
      | FPMovToReg asm_reg asm_reg fp_reg
      | FPMovFromReg fp_reg asm_reg asm_reg
      | FPToInt fp_reg fp_reg
      | FPFromInt fp_reg fp_reg";;

let addr_INDUCT,addr_RECURSION = cake_type
  "addr = Addr asm_reg (A word)";;

let memop_INDUCT,memop_RECURSION = cake_type
  "memop = asm_Load | Load8 | Load16 | asm_Load32
         | asm_Store | Store8 | Store16 | asm_Store32";;

let inst_INDUCT,inst_RECURSION = cake_type
  "inst = asm_Skip
        | asm_Const asm_reg (A word)
        | asm_Arith ((A)asm_arith)
        | Mem memop asm_reg ((A)addr)
        | FP fp";;

let asm_INDUCT,asm_RECURSION = cake_type
  "asm = asm_Inst ((A)inst)
       | asm_Jump (A word)
       | asm_JumpCmp cmp asm_reg ((A)reg_imm) (A word)
       | asm_Call (A word)
       | JumpReg asm_reg
       | asm_Loc asm_reg (A word)";;

(* -- ASM target-specific configuration -- *)

let architecture_INDUCT,architecture_RECURSION = cake_type
  "architecture = ARMv7 | ARMv8 | MIPS | RISC_V | Ag32 | x86_64";;

(* fp_reg_count: set to 0 if float not available *)

let asm_config_INFO = cake_record "asm_config"
  ["ISA","architecture";
   "encode","(A)asm->byte list";
   "big_endian","bool";
   "code_alignment","num";
   "link_reg","num option";
   "avoid_regs","num list";
   "reg_count","num";
   "fp_reg_count","num";
   "two_reg_arith","bool";
   "valid_imm","binop+cmp->A word->bool";
   "addr_offset","A word#A word";
   "hw_offset","A word#A word";
   "byte_offset","A word#A word";
   "jump_offset","A word#A word";
   "cjump_offset","A word#A word";
   "loc_offset","A word#A word"];;

let asm_config_component_equality = asm_config_INFO.ri_component_equality;;

let reg_ok_def = cake_def
  `reg_ok r (c:(A)asm_config) <=>
     r < asm_config_reg_count c /\ ~MEM r (asm_config_avoid_regs c)`;;

let fp_reg_ok_def = cake_def
  `fp_reg_ok d (c:(A)asm_config) <=> d < asm_config_fp_reg_count c`;;

(* Always permit Xor by -1 in order to provide 1's complement *)

let reg_imm_ok_def = cake_def
  `(reg_imm_ok (b:binop+cmp) (Reg r) (c:(A)asm_config) <=> reg_ok r c) /\
   (reg_imm_ok b (Imm w) c <=>
      b = INL asm_Xor /\ w = word_neg (word 1) \/ asm_config_valid_imm c b w)`;;

(* Requires register inequality for some architectures; register to       *)
(* register moves can be implemented with Or on two_reg_arith             *)
(* architectures                                                           *)

let arith_ok_def = cake_def
  `(arith_ok (Binop b r1 r2 ri) (c:(A)asm_config) <=>
      (asm_config_two_reg_arith c ==> r1 = r2 \/ b = asm_Or /\ ri = Reg r2) /\
      reg_ok r1 c /\ reg_ok r2 c /\ reg_imm_ok (INL b) ri c) /\
   (arith_ok (asm_Shift l r1 r2 ri) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\
      reg_ok r1 c /\ reg_ok r2 c /\
      (match ri with
         Imm i -> (i = word 0 ==> l = Lsl) /\ val i < dimindex(:A)
       | Reg r -> reg_ok r c /\ (asm_config_ISA c = x86_64 ==> r = 1))) /\
   (arith_ok (asm_Div r1 r2 r3) c <=>
      reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\
      asm_config_ISA c IN {ARMv8, MIPS, RISC_V}) /\
   (arith_ok (LongMul r1 r2 r3 r4) c <=>
      reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
      (asm_config_ISA c = x86_64 ==> r1 = 2 /\ r2 = 0 /\ r3 = 0) /\
      (asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
      (asm_config_ISA c IN {ARMv8, RISC_V, Ag32} ==> ~(r1 = r3) /\ ~(r1 = r4))) /\
   (arith_ok (LongDiv r1 r2 r3 r4 r5) c <=>
      asm_config_ISA c = x86_64 /\ r1 = 0 /\ r2 = 2 /\ r3 = 2 /\ r4 = 0 /\
      reg_ok r5 c) /\
   (arith_ok (asm_AddCarry r1 r2 r3 r4) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\
      reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
      (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V
       ==> ~(r1 = r3) /\ ~(r1 = r4))) /\
   (arith_ok (AddOverflow r1 r2 r3 r4) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\
      reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
      (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 = r3))) /\
   (arith_ok (SubOverflow r1 r2 r3 r4) c <=>
      (asm_config_two_reg_arith c ==> r1 = r2) /\
      reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
      (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 = r3)))`;;

let fp_ok_def = cake_def
  `(fp_ok (FPLess r d1 d2) (c:(A)asm_config) <=>
      reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPLessEqual r d1 d2) c <=>
      reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPEqual r d1 d2) c <=>
      reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPAbs d1 d2) c <=>
      (asm_config_two_reg_arith c ==> ~(d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPNeg d1 d2) c <=>
      (asm_config_two_reg_arith c ==> ~(d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPSqrt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPAdd d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_ok (FPSub d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_ok (FPMul d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_ok (FPDiv d1 d2 d3) c <=>
      (asm_config_two_reg_arith c ==> d1 = d2) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_ok (FPFma d1 d2 d3) c <=>
      asm_config_ISA c = ARMv7 /\
      2 < asm_config_fp_reg_count c /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_ok (FPMov d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_ok (FPMovToReg r1 r2 d) c <=>
      reg_ok r1 c /\ (dimindex(:A) = 32 ==> ~(r1 = r2) /\ reg_ok r2 c) /\
      fp_reg_ok d c) /\
   (fp_ok (FPMovFromReg d r1 r2) c <=>
      reg_ok r1 c /\ (dimindex(:A) = 32 ==> ~(r1 = r2) /\ reg_ok r2 c) /\
      fp_reg_ok d c) /\
   (fp_ok (FPToInt r d) c <=> fp_reg_ok r c /\ fp_reg_ok d c) /\
   (fp_ok (FPFromInt d r) c <=> fp_reg_ok r c /\ fp_reg_ok d c)`;;

let cmp_ok_def = cake_def
  `cmp_ok (cmp:cmp) r (ri:(A)reg_imm) (c:(A)asm_config) <=>
     reg_ok r c /\ reg_imm_ok (INR cmp) ri c`;;

(* HOL4: offset_ok (min and max are overloaded HOL Light constants: the     *)
(* bound names are lo and hi)                                              *)

let asm_offset_ok_def = cake_def
  `asm_offset_ok a (offset:A word#A word) (w:A word) <=>
     let (lo,hi) = offset in
     word_ile lo w /\ word_ile w hi /\ alignment_aligned a w`;;

(* HOL4 Overloads, written out where used:                                 *)
(*   addr_offset_ok c   = asm_offset_ok 0 (asm_config_addr_offset c)       *)
(*   hw_offset_ok c     = asm_offset_ok 0 (asm_config_hw_offset c)         *)
(*   byte_offset_ok c   = asm_offset_ok 0 (asm_config_byte_offset c)       *)
(*   jump_offset_ok c   = asm_offset_ok (asm_config_code_alignment c)      *)
(*                                      (asm_config_jump_offset c)         *)
(*   cjump_offset_ok c  = asm_offset_ok (asm_config_code_alignment c)      *)
(*                                      (asm_config_cjump_offset c)        *)
(*   loc_offset_ok c    = asm_offset_ok (asm_config_code_alignment c)      *)
(*                                      (asm_config_loc_offset c)          *)

let inst_ok_def = cake_def
  `(inst_ok (asm_Skip:(A)inst) (c:(A)asm_config) <=> T) /\
   (inst_ok (asm_Const r w) c <=> reg_ok r c) /\
   (inst_ok (asm_Arith x) c <=> arith_ok x c) /\
   (inst_ok (FP y) c <=> fp_ok y c) /\
   (inst_ok (Mem m r1 (Addr r2 w)) c <=>
      reg_ok r1 c /\ reg_ok r2 c /\
      (if m IN {asm_Load, asm_Store, asm_Load32, asm_Store32} then
         asm_offset_ok 0 (asm_config_addr_offset c) w
       else if m IN {Load16, Store16} then
         asm_offset_ok 0 (asm_config_hw_offset c) w /\ ~(asm_config_ISA c = Ag32)
       else
         asm_offset_ok 0 (asm_config_byte_offset c) w))`;;

let asm_ok_def = cake_def
  `(asm_ok (asm_Inst i) (c:(A)asm_config) <=> inst_ok i c) /\
   (asm_ok (asm_Jump w) c <=>
      asm_offset_ok (asm_config_code_alignment c) (asm_config_jump_offset c) w) /\
   (asm_ok (asm_JumpCmp cmp r ri w) c <=>
      asm_offset_ok (asm_config_code_alignment c) (asm_config_cjump_offset c) w /\
      cmp_ok cmp r ri c) /\
   (asm_ok (asm_Call w) c <=>
      (match asm_config_link_reg c with SOME r -> reg_ok r c | NONE -> F) /\
      asm_offset_ok (asm_config_code_alignment c) (asm_config_jump_offset c) w) /\
   (asm_ok (JumpReg r) c <=> reg_ok r c) /\
   (asm_ok (asm_Loc r w) c <=>
      reg_ok r c /\
      asm_offset_ok (asm_config_code_alignment c) (asm_config_loc_offset c) w)`;;

let asm_word_cmp_def = cake_def
  `(asm_word_cmp asm_Equal (w1:A word) w2 <=> w1 = w2) /\
   (asm_word_cmp asm_Less w1 w2 <=> word_ilt w1 w2) /\
   (asm_word_cmp Lower w1 w2 <=> word_ult w1 w2) /\
   (asm_word_cmp asm_Test w1 w2 <=> word_and w1 w2 = word 0) /\
   (asm_word_cmp NotEqual w1 w2 <=> ~(w1 = w2)) /\
   (asm_word_cmp NotLess w1 w2 <=> ~word_ilt w1 w2) /\
   (asm_word_cmp NotLower w1 w2 <=> ~word_ult w1 w2) /\
   (asm_word_cmp NotTest w1 w2 <=> ~(word_and w1 w2 = word 0))`;;

let is_load_def = cake_def
  `(is_load asm_Load <=> T) /\
   (is_load Load8 <=> T) /\
   (is_load Load16 <=> T) /\
   (is_load asm_Load32 <=> T) /\
   (is_load _ <=> F)`;;
let _ = cake_add_simps [is_load_def];;
