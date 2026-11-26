(* ========================================================================= *)
(* ag32_target: port of HOL4 compiler/encoders/ag32/ag32_targetScript.sml    *)
(* (CakeML v3479).  Define the target compiler configuration for ag32.       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The ag32 names are those of ag32.ml (ag32_Reg, ag32_Imm, ag32_Jump,     *)
(*   ag32_Shift, ag32_Encode, ag32_Next, ...); the asm names those of        *)
(*   asm.ml (asm_Inst, asm_Skip, Reg, Imm, asm_Add, ...; HOL4 asm$Imm is     *)
(*   Imm).  The local HOL4 Overloads enc = ag32_encode1 and temp_reg =       *)
(*   63w:word6 are written out.                                              *)
(* - Words: signed <= and < are word_ile and word_ilt, -n is word_neg; HOL4  *)
(*   0x7FFFFFw is word 8388607, 0x7FFFFFFFw is word 2147483647; aligned is   *)
(*   alignment_aligned; HOL4 combin$C is flip (hol4/vocab.ml); ++ is APPEND. *)
(* - The record literal of ag32_target leaves get_fp_reg out: as in HOL4 it  *)
(*   is an update chain on ARB; the literal of ag32_config gives every field *)
(*   and is written asm_config_REC (fields in record order).                 *)
(* - HOL4 ends with the theorems ag32_config and ag32_asm_ok, made by        *)
(*   asmLib.target_asm_rwts (EVAL of the 16 accessors of ag32_config, and    *)
(*   asm_ok of 41 instruction shapes simplified, as rewrites for the target  *)
(*   proof).  ag32_config is the conjunction of the accessor values, with    *)
(*   the word constants evaluated (as EVAL gives them); ag32_asm_ok is not   *)
(*   ported (its simplified forms are an artefact of HOL4's simplifier; the  *)
(*   target proof derives what it needs from asm_ok_def).                    *)
(* ========================================================================= *)

needs "hol4/set_sep.ml";;
needs "hol4/tailrec.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/encoders/ag32/ag32.ml";;

prioritize_num();;
type_invention_error := true;;

(* -- valid ag32 states -- *)

let ag32_ok_def = cake_def
  `ag32_ok ms <=> alignment_aligned 2 (ag32_state_PC ms)`;;

(* Possible initial states for Ag32, not placed in the L3 ISA because it was *)
(* difficult to express this concisely there                                *)

let is_ag32_init_state_def = cake_def
  `is_ag32_init_state mem s <=>
     ag32_state_PC s = word 0 /\
     ag32_state_MEM s = mem /\
     ag32_state_R s = combin_K (word 0) /\
     ag32_state_io_events s = []`;;

(* -- encode ASM instructions to Ag32 bytes -- *)

let ag32_encode1_def = cake_def
  `ag32_encode1 i =
     let w = ag32_Encode i in
     [word_extract 7 0 w; word_extract 15 8 w; word_extract 23 16 w;
      word_extract 31 24 w]:byte list`;;

let ag32_encode_def = new_definition
  `ag32_encode = flip LIST_BIND ag32_encode1`;;

let ag32_bop_def = cake_def
  `(ag32_bop asm_Add = fAdd) /\
   (ag32_bop asm_Sub = fSub) /\
   (ag32_bop asm_And = fAnd) /\
   (ag32_bop asm_Or = fOr) /\
   (ag32_bop asm_Xor = fXor)`;;

let ag32_sh_def = cake_def
  `(ag32_sh Lsl = shiftLL) /\
   (ag32_sh Lsr = shiftLR) /\
   (ag32_sh Asr = shiftAR) /\
   (ag32_sh Ror = shiftRor)`;;

let ag32_cmp_def = cake_def
  `(ag32_cmp asm_Equal = fEqual) /\
   (ag32_cmp asm_Less = fLess) /\
   (ag32_cmp Lower = fLower) /\
   (ag32_cmp asm_Test = fAnd) /\
   (ag32_cmp NotEqual = fEqual) /\
   (ag32_cmp NotLess = fLess) /\
   (ag32_cmp NotLower = fLower) /\
   (ag32_cmp NotTest = fAnd)`;;

let ag32_constant_def = cake_def
  `ag32_constant (r,v:int32) =
     if word_ile (word_neg (word 8388607)) v /\ word_ilt v (word 8388607) then
       let (b,n) = if word_ile (word 0) v then (F,v) else (T,word_neg v) in
       [LoadConstant (r,b,word_zx n)]
     else
       [LoadConstant (r,F,word_extract 22 0 v);
        LoadUpperConstant (r,word_extract 31 23 v)]`;;

(* Workaround that makes sure that all jump-related instructions are always *)
(* encoded to the same length.  Not using this workaround causes problems   *)
(* in lab_to_target.                                                        *)

let ag32_jump_constant_def = cake_def
  `ag32_jump_constant (r,v:int32,adjust_offset) =
     let v = if adjust_offset then word_sub v (word 8) else v in
     [LoadConstant (r,F,word_extract 22 0 v);
      LoadUpperConstant (r,word_extract 31 23 v)]`;;

let ag32_enc_def = cake_def
  `(ag32_enc (asm_Inst asm_Skip) =
      ag32_encode1 (Normal (fOr,word 0,ag32_Reg (word 0),ag32_Imm (word 0)))) /\
   (ag32_enc (asm_Inst (asm_Const r i)) =
      ag32_encode (ag32_constant (word r,i))) /\
   (ag32_enc (asm_Inst (asm_Arith (Binop bop r1 r2 (Reg r3)))) =
      ag32_encode1
        (Normal (ag32_bop bop,word r1,ag32_Reg (word r2),ag32_Reg (word r3)))) /\
   (ag32_enc (asm_Inst (asm_Arith (Binop bop r1 r2 (Imm i)))) =
      if word_ile (word_neg (word 32)) i /\ word_ilt i (word 32) then
        ag32_encode1
          (Normal (ag32_bop bop,word r1,ag32_Reg (word r2),ag32_Imm (word_zx i)))
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,i))
             [Normal (ag32_bop bop,word r1,ag32_Reg (word r2),ag32_Reg (word 63))])) /\
   (ag32_enc (asm_Inst (asm_Arith (asm_Shift sh r1 r2 (Imm i)))) =
      ag32_encode1
        (ag32_Shift (ag32_sh sh,word r1,ag32_Reg (word r2),ag32_Imm (word_zx i)))) /\
   (ag32_enc (asm_Inst (asm_Arith (asm_Shift sh r1 r2 (Reg r3)))) =
      ag32_encode1
        (ag32_Shift (ag32_sh sh,word r1,ag32_Reg (word r2),ag32_Reg (word r3)))) /\
   (ag32_enc (asm_Inst (asm_Arith (asm_Div _ _ _))) = ag32_encode1 ReservedInstr) /\
   (ag32_enc (asm_Inst (asm_Arith (LongMul r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fMulHU,word r1,ag32_Reg (word r3),ag32_Reg (word r4));
         Normal (fMul,word r2,ag32_Reg (word r3),ag32_Reg (word r4))]) /\
   (ag32_enc (asm_Inst (asm_Arith (LongDiv _ _ _ _ _))) =
      ag32_encode1 ReservedInstr) /\
   (ag32_enc (asm_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fAdd,word 63,ag32_Imm (word_neg (word 1)),ag32_Reg (word r4));
         Normal (fAddWithCarry,word r1,ag32_Reg (word r2),ag32_Reg (word r3));
         Normal (fCarry,word r4,ag32_Imm (word 0),ag32_Imm (word 0))]) /\
   (ag32_enc (asm_Inst (asm_Arith (AddOverflow r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Reg (word r3));
         Normal (fOverflow,word r4,ag32_Imm (word 0),ag32_Imm (word 0))]) /\
   (ag32_enc (asm_Inst (asm_Arith (SubOverflow r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fSub,word r1,ag32_Reg (word r2),ag32_Reg (word r3));
         Normal (fOverflow,word r4,ag32_Imm (word 0),ag32_Imm (word 0))]) /\
   (ag32_enc (asm_Inst (Mem asm_Load r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Imm (word_zx a));
           LoadMEM (word r1,ag32_Reg (word r1))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Reg (word 63));
              LoadMEM (word r1,ag32_Reg (word r1))])) /\
   (ag32_enc (asm_Inst (Mem asm_Load32 r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Imm (word_zx a));
           LoadMEM (word r1,ag32_Reg (word r1))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Reg (word 63));
              LoadMEM (word r1,ag32_Reg (word r1))])) /\
   (ag32_enc (asm_Inst (Mem Load16 r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Imm (word_zx a));
           LoadMEM (word r1,ag32_Reg (word r1))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Reg (word 63));
              LoadMEM (word r1,ag32_Reg (word r1))])) /\
   (ag32_enc (asm_Inst (Mem Load8 r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Imm (word_zx a));
           LoadMEMByte (word r1,ag32_Reg (word r1))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word r1,ag32_Reg (word r2),ag32_Reg (word 63));
              LoadMEMByte (word r1,ag32_Reg (word r1))])) /\
   (ag32_enc (asm_Inst (Mem asm_Store r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Imm (word_zx a));
           StoreMEM (ag32_Reg (word r1),ag32_Reg (word 63))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Reg (word 63));
              StoreMEM (ag32_Reg (word r1),ag32_Reg (word 63))])) /\
   (ag32_enc (asm_Inst (Mem asm_Store32 r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Imm (word_zx a));
           StoreMEM (ag32_Reg (word r1),ag32_Reg (word 63))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Reg (word 63));
              StoreMEM (ag32_Reg (word r1),ag32_Reg (word 63))])) /\
   (ag32_enc (asm_Inst (Mem Store16 r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Imm (word_zx a));
           StoreMEM (ag32_Reg (word r1),ag32_Reg (word 63))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Reg (word 63));
              StoreMEM (ag32_Reg (word r1),ag32_Reg (word 63))])) /\
   (ag32_enc (asm_Inst (Mem Store8 r1 (Addr r2 a))) =
      if word_ile (word_neg (word 32)) a /\ word_ilt a (word 32) then
        ag32_encode
          [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Imm (word_zx a));
           StoreMEMByte (ag32_Reg (word r1),ag32_Reg (word 63))]
      else
        ag32_encode
          (APPEND (ag32_constant (word 63,a))
             [Normal (fAdd,word 63,ag32_Reg (word r2),ag32_Reg (word 63));
              StoreMEMByte (ag32_Reg (word r1),ag32_Reg (word 63))])) /\
   (ag32_enc (asm_Inst (FP _)) = ag32_encode1 ReservedInstr) /\
   (ag32_enc (asm_Jump a) =
      ag32_encode
        (APPEND (ag32_jump_constant (word 63,a,T))
           [ag32_Jump (fAdd,word 63,ag32_Reg (word 63))])) /\
   (ag32_enc (asm_Call a) =
      ag32_encode
        (APPEND (ag32_jump_constant (word 63,a,T))
           [ag32_Jump (fAdd,word 0,ag32_Reg (word 63))])) /\
   (ag32_enc (JumpReg r) =
      ag32_encode1 (ag32_Jump (fSnd,word 63,ag32_Reg (word r)))) /\
   (ag32_enc (asm_Loc r i) =
      let j = word_sub i (word 4) in
      ag32_encode
        (CONS (ag32_Jump (fAdd,word r,ag32_Imm (word 4)))
           (APPEND (ag32_jump_constant (word 63,j,F))
              [Normal (fAdd,word r,ag32_Reg (word r),ag32_Reg (word 63))]))) /\
   (ag32_enc (asm_JumpCmp cmp r1 (Reg r2) a) =
      let arg = (ag32_cmp cmp,ag32_Reg (word 63),ag32_Reg (word r1),
                 ag32_Reg (word r2)) in
      ag32_encode
        (APPEND (ag32_jump_constant (word 63,a,T))
           [if cmp IN {asm_Test, NotEqual, NotLess, NotLower} then JumpIfZero arg
            else JumpIfNotZero arg])) /\
   (ag32_enc (asm_JumpCmp cmp r (Imm i) a) =
      let arg = (ag32_cmp cmp,ag32_Reg (word 63),ag32_Reg (word r),
                 ag32_Imm (word_zx i)) in
      ag32_encode
        (APPEND (ag32_jump_constant (word 63,a,T))
           [if cmp IN {asm_Test, NotEqual, NotLess, NotLower} then JumpIfZero arg
            else JumpIfNotZero arg]))`;;

(* -- configuration for Ag32 -- *)

(* Note that some bounds here might not be tight *)

let ag32_config_def = new_definition
  `ag32_config =
     asm_config_REC Ag32 ag32_enc F 2 (SOME 0) [63] 64 0 F
       (\i n. if ISL i then
                word_ile (word_neg (word 8388607)) n /\ word_ilt n (word 8388607)
              else word_ile (word_neg (word 32)) n /\ word_ilt n (word 32))
       (word_neg (word 8388607),word 8388607)
       (word_neg (word 8388607),word 8388607)
       (word_neg (word 32),word 31)
       (word_add (word_neg (word 2147483647)) (word 4),word 2147483647)
       (word_add (word_neg (word 2147483647)) (word 4),word 2147483647)
       (word_add (word_neg (word 2147483647)) (word 4),word 2147483647)`;;

let ag32_proj_def = cake_def
  `ag32_proj d s =
     (ag32_state_PC s,ag32_state_R s,fun2set (ag32_state_MEM s,d),
      ag32_state_CarryFlag s,ag32_state_OverflowFlag s)`;;

let ag32_target_def = new_definition
  `ag32_target =
     target_next_fupd (combin_K ag32_Next)
       (target_config_fupd (combin_K ag32_config)
          (target_get_pc_fupd (combin_K ag32_state_PC)
             (target_get_reg_fupd (combin_K (\s. ag32_state_R s o word))
                (target_get_byte_fupd (combin_K ag32_state_MEM)
                   (target_state_ok_fupd (combin_K ag32_ok)
                      (target_proj_fupd (combin_K ag32_proj)
                         (ARB:(32,ag32_state,
                               int32#((6)word->int32)#(int32#byte->bool)#bool#bool)
                              target)))))))`;;

(* HOL4: val (ag32_config, ag32_asm_ok) = asmLib.target_asm_rwts [] ag32_config *)

let ag32_config = prove
 (`asm_config_ISA ag32_config = Ag32 /\
   asm_config_encode ag32_config = ag32_enc /\
   asm_config_big_endian ag32_config = F /\
   asm_config_code_alignment ag32_config = 2 /\
   asm_config_link_reg ag32_config = SOME 0 /\
   asm_config_avoid_regs ag32_config = [63] /\
   asm_config_reg_count ag32_config = 64 /\
   asm_config_fp_reg_count ag32_config = 0 /\
   asm_config_two_reg_arith ag32_config = F /\
   asm_config_valid_imm ag32_config =
     (\i n. if ISL i then word_ile (word 4286578689) n /\ word_ilt n (word 8388607)
            else word_ile (word 4294967264) n /\ word_ilt n (word 32)) /\
   asm_config_addr_offset ag32_config = (word 4286578689,word 8388607) /\
   asm_config_hw_offset ag32_config = (word 4286578689,word 8388607) /\
   asm_config_byte_offset ag32_config = (word 4294967264,word 31) /\
   asm_config_jump_offset ag32_config = (word 2147483653,word 2147483647) /\
   asm_config_cjump_offset ag32_config = (word 2147483653,word 2147483647) /\
   asm_config_loc_offset ag32_config = (word 2147483653,word 2147483647)`,
  REWRITE_TAC[ag32_config_def; asm_config_INFO.ri_accessors] THEN
  CONV_TAC WORD_REDUCE_CONV);;
