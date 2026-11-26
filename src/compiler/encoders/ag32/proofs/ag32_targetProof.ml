(* ========================================================================= *)
(* ag32_targetProof: port of HOL4                                            *)
(* compiler/encoders/ag32/proofs/ag32_targetProofScript.sml (CakeML v3479).  *)
(* Prove encoder_correct for ag32, i.e. the Silver ISA.                      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Words: HOL4's blastLib (BBLAST_TAC, BBLAST_PROVE) is HOL Light's        *)
(*   BITBLAST_TAC (Library/words.ml), after HOL4 vocabulary is turned into   *)
(*   HOL Light's (word_extract h l w = word_subword w (l,(h+1)-l));          *)
(*   word identities of the ring are WORD_RULE.  The HOL4 ML values          *)
(*   jump_lem, jump_lem2, jump_lem3, load_lem, load_lem3, store_lem,         *)
(*   store_lem2, mem_lem and the unnamed ag32_encoding are helpers here      *)
(*   (AG32AUX_W1 .. AG32AUX_W4, AG32AUX_ADD_CANCEL, AG32AUX_ENC_LENGTH).     *)
(* - HOL4's proof of ag32_encoder_correct is automation (asmLib's            *)
(*   next_tac and state_tac): every asm instruction is unfolded into its     *)
(*   ag32 instructions, whose runs (interleaved with the interference env)   *)
(*   are computed and compared with the asm semantics.  The port does the   *)
(*   same with the tactic AG32AUX_AUTO_TAC below (set up, split the         *)
(*   conditionals of the encoding, step every ag32 instruction with         *)
(*   AG32AUX_FETCH, simplify, blast what is left), applied to every shape   *)
(*   of asm instruction (AG32AUX_ENC_ALL).                                   *)
(* - asmProps does not port asserts_eval and asserts2_eval (HOL4 EVAL       *)
(*   forms); AG32AUX_ASSERTS_CONV unfolds asserts and asserts2 at numerals.  *)
(* - HOL4 [local] theorems are global bindings here (port convention).       *)
(* - Helpers that are not HOL4 theorems have the prefix AG32AUX_.            *)
(* ========================================================================= *)

needs "compiler/encoders/ag32/ag32_target.ml";;

prioritize_num();;
type_invention_error := true;;

(* the fields of ag32_target (a record literal on ARB) *)

let AG32AUX_TARGET_FIELDS = prove
 (`target_next ag32_target = ag32_Next /\
   target_config ag32_target = ag32_config /\
   target_get_pc ag32_target = ag32_state_PC /\
   target_get_reg ag32_target = (\s. ag32_state_R s o word) /\
   target_get_byte ag32_target = ag32_state_MEM /\
   target_state_ok ag32_target = ag32_ok /\
   target_proj ag32_target = ag32_proj`,
  REWRITE_TAC[ag32_target_def; target_INFO.ri_accessors; target_INFO.ri_accfupds; K_THM] THEN
  SIMP[]);;

(* bit blasting of goals in HOL4 word vocabulary *)

let AG32AUX_BLAST_TAC =
  REWRITE_TAC[word_extract_subword; aligned_extract] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[word_extract_subword] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN BITBLAST_TAC;;

(* -- some lemmas -- *)

let bytes_in_memory_thm = prove
 (`!(w:A) s state a b c d.
     target_state_rel ag32_target s state /\
     bytes_in_memory (asm_state_pc s) [a; b; c; d] (asm_state_mem s)
       (asm_state_mem_domain s)
     ==> alignment_aligned 2 (ag32_state_PC state) /\
         ag32_state_MEM state (ag32_state_PC state) = a /\
         ag32_state_MEM state (word_add (ag32_state_PC state) (word 1)) = b /\
         ag32_state_MEM state (word_add (ag32_state_PC state) (word 2)) = c /\
         ag32_state_MEM state (word_add (ag32_state_PC state) (word 3)) = d /\
         word_add (ag32_state_PC state) (word 3) IN asm_state_mem_domain s /\
         word_add (ag32_state_PC state) (word 2) IN asm_state_mem_domain s /\
         word_add (ag32_state_PC state) (word 1) IN asm_state_mem_domain s /\
         ag32_state_PC state IN asm_state_mem_domain s`,
  REWRITE_TAC[target_state_rel_def; AG32AUX_TARGET_FIELDS; ag32_ok_def;
              bytes_in_memory_def; GSYM WORD_ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let bytes_in_memory_thm2 = prove
 (`!w s state a b c d.
     target_state_rel ag32_target s state /\
     bytes_in_memory (word_add (asm_state_pc s) w) [a; b; c; d] (asm_state_mem s)
       (asm_state_mem_domain s)
     ==> ag32_state_MEM state (word_add (ag32_state_PC state) w) = a /\
         ag32_state_MEM state (word_add (word_add (ag32_state_PC state) w) (word 1)) = b /\
         ag32_state_MEM state (word_add (word_add (ag32_state_PC state) w) (word 2)) = c /\
         ag32_state_MEM state (word_add (word_add (ag32_state_PC state) w) (word 3)) = d /\
         word_add (word_add (ag32_state_PC state) w) (word 3) IN asm_state_mem_domain s /\
         word_add (word_add (ag32_state_PC state) w) (word 2) IN asm_state_mem_domain s /\
         word_add (word_add (ag32_state_PC state) w) (word 1) IN asm_state_mem_domain s /\
         word_add (ag32_state_PC state) w IN asm_state_mem_domain s`,
  REWRITE_TAC[target_state_rel_def; AG32AUX_TARGET_FIELDS; ag32_ok_def;
              bytes_in_memory_def; GSYM WORD_ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let add_carry_lem = prove
 (`!w:int32. 4294967296 <= val w + 4294967295 <=> ~(w = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC);;

let add_carry_lem2 = prove
 (`!(a:N word) b. word (val a + val b + 1) = word_add (word_add a b) (word 1)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL; WORD_ADD_ASSOC]);;

let shift_lem = prove
 (`!n. n < 32 ==> val (word_sx (word n:(6)word):int32) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_VAL_CONV) THEN REWRITE_TAC[]);;

let long_mul_lem = prove
 (`!(a:int32) (b:int32).
     word ((val a * val b) DIV 4294967296) =
     (word_extract 63 32 (word_mul (word_zx a) (word_zx b):int64):int32)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_extract_subword] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN MP_TAC(ISPEC `b:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (a:int32) * val (b:int32) < 18446744073709551616` ASSUME_TAC THENL
   [SUBGOAL_THEN `18446744073709551616 = 4294967296 * 4294967296` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (a:int32) < 18446744073709551616 /\ val (b:int32) < 18446744073709551616`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* HOL4 jump_lem and load_lem (the same statement up to the bound 31w/32w),  *)
(* store_lem2 and load_lem3 (the two LoadConstant cases), mem_lem (the       *)
(* LoadConstant/LoadUpperConstant pair), as used by the proofs below         *)

let AG32AUX_W1 = BITBLAST_RULE
  `!c:int32. word_ile (word 0) c /\ word_ilt c (word 8388607)
             ==> word_zx (word_zx c:(23)word):int32 = c`;;

let AG32AUX_W2 = BITBLAST_RULE
  `!c:int32. word_ile (word 4286578689) c /\ ~word_ile (word 0) c
             ==> word_neg (word_zx (word_zx (word_neg c):(23)word):int32) = c`;;

let AG32AUX_W3 = prove
 (`!c:int32. word_insert (word_zx (word_extract 22 0 c:(23)word):int32) (23,9)
                         (word_extract 31 23 c:(9)word) = c`,
  AG32AUX_BLAST_TAC);;

let AG32AUX_W4 = BITBLAST_RULE
  `!c:int32. word_ile (word 4294967264) c /\ word_ilt c (word 32)
             ==> word_sx (word_zx c:(6)word):int32 = c`;;

let load_lem2 = prove
 (`!c:int32. alignment_aligned 2 c ==>
     word_join (word_extract 31 2 c:(30)word) (word 0:(2)word) = c`,
  REWRITE_TAC[aligned_extract; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  AG32AUX_BLAST_TAC);;

(* HOL4 store_lem: the addresses written by StoreMEM are distinct *)

let AG32AUX_ADD_CANCEL = prove
 (`(!x y z:int32. word_add x y = word_add x z <=> y = z) /\
   (!x y:int32. word_add x y = x <=> y = word 0) /\
   (!x y:int32. x = word_add x y <=> y = word 0)`,
  let th = WORD_RULE `!x y:int32. word_sub (word_add x y) x = y` in
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[WORD_ADD_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\v:int32. word_sub v x`) THEN
  REWRITE_TAC[th; WORD_SUB_REFL] THEN MESON_TAC[]);;

(* the other word facts of the simulation *)

let AG32AUX_SHIFT_IMM = prove
 (`!c:int32. val c < 32 ==> val (word_sx (word_zx c:(6)word):int32) = val c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx] THEN ASM_SIMP_TAC[shift_lem]);;

let AG32AUX_WORD_MUL_VAL = prove
 (`!a b:int32. word (val a * val b) = word_mul a b`,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

let AG32AUX_WORD_ADD_VAL = prove
 (`(!a b:int32. word (val a + val b) = word_add a b) /\
   (!a b:int32 n. word ((val a + val b) + n) = word_add a (word_add b (word n)))`,
  REWRITE_TAC[WORD_ADD; WORD_VAL; WORD_ADD_ASSOC]);;

let AG32AUX_CARRY = prove
 (`!w:int32. 4294967296 <= 4294967295 + val w <=> ~(w = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC);;

let AG32AUX_EXTRACT_ZX8 = prove
 (`!v:int32. (word_extract 7 0 v:byte) = word_zx v`,
  AG32AUX_BLAST_TAC);;

let AG32AUX_BYTES = prove
 (`(!v:int32. (word_extract 15 8 v:byte) = word_zx (word_ushr v 8)) /\
   (!v:int32. (word_extract 23 16 v:byte) = word_zx (word_ushr (word_ushr v 8) 8)) /\
   (!v:int32. (word_extract 31 24 v:byte) =
              word_zx (word_ushr (word_ushr (word_ushr v 8) 8) 8))`,
  REPEAT CONJ_TAC THEN AG32AUX_BLAST_TAC);;

let AG32AUX_LOAD_BYTES = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     (word_join b3 (word_join b2 (word_join b1 b0:int16):(24)word):int32) =
     word_or (word_shl (word_or (word_shl (word_or (word_shl (word_zx b3) 8) (word_zx b2)) 8)
                                (word_zx b1)) 8) (word_zx b0)`,
  BITBLAST_TAC);;

(* -- some rewrites -- *)

let AG32AUX_ENCODE_CLAUSES = prove
 (`ag32_encode [] = [] /\
   (!i l. ag32_encode (CONS i l) = APPEND (ag32_encode1 i) (ag32_encode l))`,
  REWRITE_TAC[ag32_encode_def; flip_DEF; LIST_BIND_THM]);;

let AG32AUX_ENCODE1_SING = prove
 (`!i. ag32_encode1 i = ag32_encode [i]`,
  REWRITE_TAC[AG32AUX_ENCODE_CLAUSES; APPEND_NIL]);;

(* HOL4 encode_rwts (with the ag32 instruction maps), asm_rwts, and the       *)
(* definitions of the instruction semantics                                  *)

let AG32AUX_ENC_RWTS = [ag32_enc_def; AG32AUX_ENCODE1_SING; ag32_constant_def;
  ag32_jump_constant_def; APPEND; LENGTH; ag32_bop_def; ag32_sh_def; ag32_cmp_def];;

let AG32AUX_ASM_RWTS = [asm_asm_def; asmSem_inst_def; asm_upd_pc_def; asm_upd_reg_def;
  asm_arith_upd_def; asm_binop_upd_def; read_reg_def; asm_reg_imm_def; asm_word_shift_def;
  asm_assert_def; jump_to_offset_def; asm_word_cmp_def; asm_addr_def; asm_mem_op_def;
  asm_mem_load_def; asm_mem_store_def; asm_read_mem_def; asm_upd_mem_def];;

let AG32AUX_RUN_RWTS = [ag32_Run_def; dfn'Normal_def; dfn'Shift_def; dfn'StoreMEM_def;
  dfn'StoreMEMByte_def; dfn'LoadMEM_def; dfn'LoadMEMByte_def; dfn'LoadConstant_def;
  dfn'LoadUpperConstant_def; dfn'Jump_def; dfn'JumpIfZero_def; dfn'JumpIfNotZero_def;
  ALU_def; ag32_norm_def; incPC_def; ri2word_def; ag32_shift_def; pair_CASE];;

(* -- ag32 target_ok -- *)

let length_ag32_encode = prove
 (`!i. LENGTH (ag32_encode1 i) = 4 /\ ~(ag32_encode1 i = [])`,
  REWRITE_TAC[ag32_encode1_def; LET_DEF; LET_END_DEF; LENGTH; NOT_CONS_NIL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AG32AUX_LENGTH_ENCODE = prove
 (`!l. LENGTH (ag32_encode l) = 4 * LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[AG32AUX_ENCODE_CLAUSES; LENGTH; LENGTH_APPEND; length_ag32_encode] THEN
  ARITH_TAC);;

(* (!x. P x) <=> P C1 /\ (!a. P (C2 a)) /\ ... from an induction theorem *)

let AG32AUX_FORALL_TY ind =
  let p,body = dest_forall(concl ind) in
  let ant,cons = dest_imp body in
  prove(mk_forall(p,mk_iff(cons,ant)),
        GEN_TAC THEN EQ_TAC THENL
         [DISCH_TAC THEN ASM_REWRITE_TAC[]; MATCH_ACCEPT_TAC(SPEC p ind)]);;

let AG32AUX_FORALL_ASM = map AG32AUX_FORALL_TY
  [asm_INDUCT; inst_INDUCT; asm_arith_INDUCT; binop_INDUCT; reg_imm_INDUCT; memop_INDUCT;
   addr_INDUCT; fp_INDUCT; cmp_INDUCT; shift_INDUCT];;

(* HOL4 ag32_encoding: every encoding is a non-empty list of instructions *)

let AG32AUX_ENC_LENGTH = prove
 (`!i. LENGTH (ag32_enc i) MOD 4 = 0 /\ ~(LENGTH (ag32_enc i) = 0)`,
  REWRITE_TAC AG32AUX_FORALL_ASM THEN REPEAT(CONJ_TAC ORELSE GEN_TAC) THEN
  CONV_TAC(CAKE_REWRITE_CONV[ag32_enc_def; AG32AUX_ENCODE1_SING; ag32_constant_def;
                             ag32_jump_constant_def]) THEN
  REPEAT COND_CASES_TAC THEN
  SIMP[AG32AUX_LENGTH_ENCODE; LENGTH; LENGTH_APPEND; AG32AUX_ENCODE_CLAUSES; APPEND_EQ_NIL;
       length_ag32_encode] THEN
  REPEAT COND_CASES_TAC THEN SIMP[LENGTH; LENGTH_APPEND] THEN CONV_TAC NUM_REDUCE_CONV);;

let ag32_target_ok = prove
 (`target_ok ag32_target`,
  REWRITE_TAC[target_ok_def; AG32AUX_TARGET_FIELDS] THEN CONJ_TAC THENL
   [REWRITE_TAC[enc_ok_def; offset_monotonic_def; ag32_config] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[AG32AUX_ENC_LENGTH] THEN
    REWRITE_TAC[AG32AUX_FORALL_TY reg_imm_INDUCT] THEN
    CONV_TAC(CAKE_REWRITE_CONV (AG32AUX_ENC_RWTS @ [LET_DEF; LET_END_DEF; LENGTH_APPEND;
                                                    AG32AUX_LENGTH_ENCODE]) THENC
             NUM_REDUCE_CONV) THEN
    REWRITE_TAC[LE_REFL];
    REWRITE_TAC[ag32_proj_def; PAIR_EQ; fun2set_eq] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[target_state_rel_def; AG32AUX_TARGET_FIELDS; ag32_ok_def; o_THM;
                 ag32_config; CONJUNCT1 LT]]);;

(* -- the encoder and decoder -- *)

let aligned_pc = prove
 (`!a:int32. alignment_aligned 2 a ==>
     word_join (word_extract 31 2 a:(30)word) (word 0:(2)word) = a`,
  REWRITE_TAC[load_lem2]);;

let concat_bytes = prove
 (`!w:int32.
     word_join (word_extract 31 24 w:byte)
       (word_join (word_extract 23 16 w:byte)
          (word_join (word_extract 15 8 w:byte) (word_extract 7 0 w:byte):int16)
        :(24)word) = w`,
  AG32AUX_BLAST_TAC);;

(* conversions: v2w of a list of literals; v2w [bit (n-1) x; ..; bit 0 x]   *)
(* = x for x:(n)word                                                        *)

let AG32AUX_V2W_LIT_CONV =
  let th = prove(`!l. v2w l:N word = word (v2n l)`, REWRITE_TAC[n2w_v2n])
  and t_tm = `T` and f_tm = `F` in
  fun tm -> match tm with
    Comb(Const("v2w",_),l) when
      (try forall (fun b -> b = t_tm || b = f_tm) (dest_list l) with _ -> false) ->
      (GEN_REWRITE_CONV I [th] THENC
       RAND_CONV (REWRITE_CONV[v2n; LENGTH] THENC NUM_REDUCE_CONV)) tm
  | _ -> failwith "AG32AUX_V2W_LIT_CONV";;

let AG32AUX_V2W_BITS_CONV tm =
  match tm with
    Comb(Const("v2w",ty),l) ->
      let els = dest_list l in
      let n = length els in
      let x = rand(hd els) in
      if type_of x <> snd(dest_fun_ty ty) then failwith "AG32AUX_V2W_BITS_CONV" else
      let ok i e = match e with
          Comb(Comb(Const("bit",_),k),y) -> y = x && dest_small_numeral k = i
        | _ -> false in
      if not (forall2 ok (rev(0--(n-1))) els)
      then failwith "AG32AUX_V2W_BITS_CONV" else
      prove(mk_eq(tm,x),
            REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
            CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
            CONV_TAC EXPAND_CASES_CONV THEN
            CONV_TAC(DEPTH_CONV AG32AUX_BIT_V2W_CONV) THEN REWRITE_TAC[])
  | _ -> failwith "AG32AUX_V2W_BITS_CONV";;

let funcT_thm = prove
 (`!func.
     num2funcT
       (val (v2w [numbit 3 (funcT2num func); numbit 2 (funcT2num func);
                  numbit 1 (funcT2num func); numbit 0 (funcT2num func)]:(4)word)) = func`,
  MATCH_MP_TAC funcT_INDUCT THEN REWRITE_TAC[funcT2num_def; numbit] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV AG32AUX_V2W_LIT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_VAL_CONV) THEN REWRITE_TAC[num2funcT_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let shiftT_thm = prove
 (`!shiftOp.
     num2shiftT
       (val (word_extract 1 0
               (v2w [numbit 3 (shiftT2num shiftOp); numbit 2 (shiftT2num shiftOp);
                     numbit 1 (shiftT2num shiftOp); numbit 0 (shiftT2num shiftOp)]:(4)word)
             :(2)word)) = shiftOp`,
  MATCH_MP_TAC shiftT_INDUCT THEN REWRITE_TAC[shiftT2num_def; numbit; word_extract_subword] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV AG32AUX_V2W_LIT_CONV) THEN
  CONV_TAC(DEPTH_CONV (WORD_RED_CONV ORELSEC WORD_VAL_CONV)) THEN REWRITE_TAC[num2shiftT_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* the variants of funcT_thm and shiftT_thm that Decode (Encode i) meets *)

let AG32AUX_NUM2FUNCT = prove
 (`!f. num2funcT (val (word (funcT2num f):(4)word)) = f`,
  MATCH_MP_TAC funcT_INDUCT THEN REWRITE_TAC[funcT2num_def] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[num2funcT_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AG32AUX_NUM2SHIFTT = prove
 (`!s. num2shiftT (val (word_extract 1 0 (word (shiftT2num s):(4)word):(2)word)) = s`,
  MATCH_MP_TAC shiftT_INDUCT THEN REWRITE_TAC[shiftT2num_def; word_extract_subword] THEN
  CONV_TAC(DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN REWRITE_TAC[num2shiftT_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AG32AUX_FORALL_REG_IMMT = AG32AUX_FORALL_TY reg_immT_INDUCT;;

let AG32AUX_V2W_1 = prove
 (`!b. (v2w [b] = word 0:(1)word) <=> ~b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  CONV_TAC(DEPTH_CONV AG32AUX_V2W_LIT_CONV) THEN CONV_TAC WORD_REDUCE_CONV);;

(* Decode (Encode i) for an instruction i with variable fields: the bits of *)
(* the encoding, then the decoder's tests                                   *)

let AG32AUX_DECODE_ENCODE_CONV =
  let bits_conv = DEPTH_CONV (AG32AUX_BIT_V2W_CONV ORELSEC
                              CHANGED_CONV (BIT_WORD_CONV THENC REWRITE_CONV[])) in
  fun tm ->
    let th1 = CAKE_REWRITE_CONV[ag32_Encode_def; ag32_enc'_def; encShift_def; ri2bits_def] tm in
    let th2 = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV[ag32_Decode_def])) th1 in
    let btm = find_term (fun t -> try fst(dest_const(rator t)) = "boolify32" with _ -> false)
                (rand(concl th2)) in
    let bth = (REWRITE_CONV[boolify32_def] THENC bits_conv) btm in
    let th3 = CONV_RULE (RAND_CONV (REWRITE_CONV[bth; pair_CASE])) th2 in
    CONV_RULE (RAND_CONV
      (REWRITE_CONV[] THENC
       TOP_DEPTH_CONV let_CONV THENC
       DEPTH_CONV (AG32AUX_V2W_LIT_CONV ORELSEC AG32AUX_V2W_BITS_CONV) THENC
       REWRITE_CONV[DecodeReg_imm_def; AG32AUX_NUM2FUNCT; AG32AUX_NUM2SHIFTT] THENC
       DEPTH_CONV WORD_RED_CONV THENC
       CAKE_REWRITE_CONV[])) th3;;

(* The encoder and decoder are well-behaved *)

let Decode_Encode = prove
 (`!i. ag32_Decode (ag32_Encode i) = i`,
  MATCH_MP_TAC instruction_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; AG32AUX_FORALL_REG_IMMT] THEN
  REPEAT(CONJ_TAC ORELSE GEN_TAC) THEN
  CONV_TAC(LAND_CONV AG32AUX_DECODE_ENCODE_CONV) THEN
  REWRITE_TAC[AG32AUX_V2W_1]);;

let ag32_run = prove
 (`!i ms.
     ag32_state_MEM ms (ag32_state_PC ms) = word_extract 7 0 (ag32_Encode i) /\
     ag32_state_MEM ms (word_add (ag32_state_PC ms) (word 1)) =
       word_extract 15 8 (ag32_Encode i) /\
     ag32_state_MEM ms (word_add (ag32_state_PC ms) (word 2)) =
       word_extract 23 16 (ag32_Encode i) /\
     ag32_state_MEM ms (word_add (ag32_state_PC ms) (word 3)) =
       word_extract 31 24 (ag32_Encode i) /\
     alignment_aligned 2 (ag32_state_PC ms)
     ==> ag32_Next ms = ag32_Run i ms`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ag32_Next_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[aligned_pc] THEN ASM_REWRITE_TAC[concat_bytes; Decode_Encode]);;

let bytes_in_memory_IMP_all_pcs_MEM = prove
 (`!(env:num->ag32_state->ag32_state) a xs m dm.
     bytes_in_memory a xs m dm /\
     (!(i:num) ms'. fun2set (ag32_state_MEM (env i ms'),dm) =
                    fun2set (ag32_state_MEM ms',dm))
     ==> (!i ms'. (!pc. pc IN all_pcs (LENGTH xs) a 0
                        ==> ag32_state_MEM (env i ms') pc = ag32_state_MEM ms' pc))`,
  REWRITE_TAC[fun2set_eq] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP bytes_in_memory_all_pcs) THEN
  REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]);;

(* -- the simulation of an asm instruction by its ag32 instructions -- *)

(* the j-th instruction of an encoding in memory is the next one at the     *)
(* j-th program counter (HOL4's next_state_tac with bytes_in_memory_thm2)   *)

let AG32AUX_EL_ENCODE = prove
 (`!l j k. j < LENGTH l /\ k < 4
           ==> EL (4 * j + k) (ag32_encode l) = EL k (ag32_encode1 (EL j l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_SUC; EL; HD; TL] THEN
  REWRITE_TAC[AG32AUX_ENCODE_CLAUSES; EL_APPEND; length_ag32_encode] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `4 * 0 + k = k`] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(4 * SUC j + k < 4)`;
               ARITH_RULE `(4 * SUC j + k) - 4 = 4 * j + k`]);;

let AG32AUX_ALIGNED_ADD4 = prove
 (`!pc:int32 j. alignment_aligned 2 pc ==> alignment_aligned 2 (word_add pc (word (4 * j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `alignment_aligned 2 (word (4 * j):int32)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_0_aligned THEN REWRITE_TAC[MOD_EQ_0] THEN
    EXISTS_TAC `j:num` THEN ARITH_TAC;
    ASM_SIMP_TAC[aligned_add_sub]]);;

let AG32AUX_FETCH = prove
 (`!l j pc m d x.
     bytes_in_memory pc (ag32_encode l) m d /\ alignment_aligned 2 pc /\
     j < LENGTH l /\ ag32_state_PC x = word_add pc (word (4 * j)) /\
     (!a. a IN d ==> ag32_state_MEM x a = m a)
     ==> ag32_Next x = ag32_Run (EL j l) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ag32_run THEN
  SUBGOAL_THEN
   `!k. k < 4 ==> ag32_state_MEM x (word_add (ag32_state_PC x) (word k)) =
                  EL k (ag32_encode1 (EL j l))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    SUBGOAL_THEN `4 * j + k < LENGTH (ag32_encode l)` ASSUME_TAC THENL
     [REWRITE_TAC[AG32AUX_LENGTH_ENCODE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[bytes_in_memory_in_domain; bytes_in_memory_EL; AG32AUX_EL_ENCODE];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[ag32_encode1_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[AG32AUX_ALIGNED_ADD4]]);;

(* asserts and asserts2 at numerals (HOL4 asserts_eval, asserts2_eval) *)

let AG32AUX_ASSERTS2_0 = prove
 (`!fi fc (ms:A) P. asserts2 0 fi fc ms P <=> T`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [asserts2_def] THEN REWRITE_TAC[]);;

let AG32AUX_ASSERTS2_SUC = prove
 (`!n fi fc (ms:A) P. asserts2 (SUC n) fi fc ms P <=>
       P ms (fc ms) /\ asserts2 n fi fc (fi (SUC n) (fc ms)) P`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [asserts2_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1]);;

let AG32AUX_ASSERTS_CONV =
  let a0 = CONJUNCT1 asserts_def and asuc = CONJUNCT2 asserts_def in
  let one tm =
    match strip_comb tm with
      Const("asserts",_),(n::_) when is_numeral n ->
        if dest_numeral n = num_0 then REWR_CONV a0 tm
        else (RATOR_CONV(RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV)))) THENC
              REWR_CONV asuc) tm
    | Const("asserts2",_),(n::_) when is_numeral n ->
        if dest_numeral n = num_0 then REWR_CONV AG32AUX_ASSERTS2_0 tm
        else (RATOR_CONV(RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV)))) THENC
              REWR_CONV AG32AUX_ASSERTS2_SUC) tm
    | _ -> failwith "AG32AUX_ASSERTS_CONV" in
  TOP_DEPTH_CONV (one ORELSEC BETA_CONV ORELSEC let_CONV ORELSEC NUM_RED_CONV);;

(* the interference of the environment, field by field *)

let AG32AUX_INTERFERENCE = prove
 (`!env d. interference_ok env (ag32_proj d) <=>
     (!i ms. ag32_state_PC (env i ms) = ag32_state_PC ms) /\
     (!i ms. ag32_state_R (env i ms) = ag32_state_R ms) /\
     (!i ms a. a IN d ==> ag32_state_MEM (env i ms) a = ag32_state_MEM ms a) /\
     (!i ms. ag32_state_CarryFlag (env i ms) = ag32_state_CarryFlag ms) /\
     (!i ms. ag32_state_OverflowFlag (env i ms) = ag32_state_OverflowFlag ms)`,
  REWRITE_TAC[interference_ok_def; ag32_proj_def; PAIR_EQ; fun2set_eq] THEN
  MESON_TAC[]);;

(* all_pcs n pc 2 at numerals, as a set enumeration *)

let AG32AUX_PCS_CONV =
  let c0 = CONJUNCT1 all_pcs_def and cs = CONJUNCT2 all_pcs_def and two_tm = `2` in
  let norm = REWRITE_CONV[GSYM WORD_ADD_ASSOC] THENC DEPTH_CONV WORD_RED_CONV in
  let rec conv tm =
    match strip_comb tm with
      Const("all_pcs",_),[n;a;k] when is_numeral n ->
        if dest_numeral n = num_0 then REWR_CONV c0 tm
        else (RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV)) THENC REWR_CONV cs THENC
              RAND_CONV (RATOR_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)) THENC
                         RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV) THENC norm)) THENC
                         conv)) tm
    | _ -> failwith "AG32AUX_PCS_CONV" in
  fun tm -> match strip_comb tm with
      Const("all_pcs",_),[_;_;k] when k = two_tm -> conv tm
    | _ -> failwith "AG32AUX_PCS_CONV";;

(* read_mem_word and write_mem_word of 1 and 4 bytes, little-endian *)

let AG32AUX_MEMWORD_TAC =
  let record_rwts = [asm_state_INFO.ri_accfupds; asm_state_INFO.ri_fupdfupds;
                     asm_state_INFO.ri_fupdcanon; K_THM; o_THM; K_o_THM] in
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  ASM (fun thl -> CONV_TAC(LAND_CONV
    (REWRITE_CONV[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`] THENC
     REWRITE_CONV[write_mem_word_def; read_mem_word_def; LET_DEF; LET_END_DEF;
                  asm_assert_def; asm_upd_mem_def; asm_read_mem_def; pair_CASE] THENC
     REWRITE_CONV (thl @ record_rwts) THENC
     REWRITE_CONV[GSYM WORD_ADD_ASSOC] THENC DEPTH_CONV WORD_RED_CONV THENC
     REWRITE_CONV[WORD_OR_0; WORD_ADD_0]))) [] THEN
  REFL_TAC;;

let AG32AUX_WRITE_MEM_WORD4 = prove
 (`!w (a:int32) (s:(32)asm_state).
     ~asm_state_be s
     ==> write_mem_word a 4 w s =
         asm_state_mem_fupd
           (combin_K ((a =+ word_zx w)
               ((word_add a (word 1) =+ word_zx (word_ushr w 8))
                ((word_add a (word 2) =+ word_zx (word_ushr (word_ushr w 8) 8))
                 ((word_add a (word 3) =+
                   word_zx (word_ushr (word_ushr (word_ushr w 8) 8) 8))
                  (asm_state_mem s))))))
           (asm_state_failed_fupd
              (combin_K (~(a IN asm_state_mem_domain s) \/
                  ~(word_add a (word 1) IN asm_state_mem_domain s) \/
                  ~(word_add a (word 2) IN asm_state_mem_domain s) \/
                  ~(word_add a (word 3) IN asm_state_mem_domain s) \/
                  asm_state_failed s))
              s)`,
  AG32AUX_MEMWORD_TAC);;

let AG32AUX_WRITE_MEM_WORD1 = prove
 (`!w (a:int32) (s:(32)asm_state).
     write_mem_word a 1 w s =
     asm_state_mem_fupd (combin_K ((a =+ word_zx w) (asm_state_mem s)))
       (asm_state_failed_fupd
          (combin_K (~(a IN asm_state_mem_domain s) \/ asm_state_failed s)) s)`,
  AG32AUX_MEMWORD_TAC);;

let AG32AUX_READ_MEM_WORD4 = prove
 (`!(a:int32) (s:(32)asm_state).
     ~asm_state_be s
     ==> read_mem_word a 4 s =
         (word_or
            (word_shl
               (word_or
                  (word_shl
                     (word_or
                        (word_shl (word_zx (asm_state_mem s (word_add a (word 3)))) 8)
                        (word_zx (asm_state_mem s (word_add a (word 2)))))
                     8)
                  (word_zx (asm_state_mem s (word_add a (word 1)))))
               8)
            (word_zx (asm_state_mem s a)),
          asm_state_failed_fupd
            (combin_K (~(a IN asm_state_mem_domain s) \/
                ~(word_add a (word 1) IN asm_state_mem_domain s) \/
                ~(word_add a (word 2) IN asm_state_mem_domain s) \/
                ~(word_add a (word 3) IN asm_state_mem_domain s) \/
                asm_state_failed s))
            s)`,
  AG32AUX_MEMWORD_TAC);;

let AG32AUX_READ_MEM_WORD1 = prove
 (`!(a:int32) (s:(32)asm_state).
     read_mem_word a 1 s =
     (word_zx (asm_state_mem s a),
      asm_state_failed_fupd
        (combin_K (~(a IN asm_state_mem_domain s) \/ asm_state_failed s)) s)`,
  AG32AUX_MEMWORD_TAC);;

let AG32AUX_MEMWORD_RWTS = [AG32AUX_WRITE_MEM_WORD4; AG32AUX_WRITE_MEM_WORD1;
  AG32AUX_READ_MEM_WORD4; AG32AUX_READ_MEM_WORD1];;

(* more rewrites for the final comparison of the states *)

let AG32AUX_WORD6_EQ = prove
 (`!a b. a < 64 /\ b < 64 ==> ((word a:(6)word) = word b <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_CONV `dimindex(:6)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let AG32AUX_REG_UPDATE = prove
 (`!r i (v:int32) R. r < 64 /\ i < 64
     ==> (word r =+ v) R (word i:(6)word) = if r = i then v else R (word i)`,
  SIMP_TAC[APPLY_UPDATE_THM; AG32AUX_WORD6_EQ]);;

let AG32AUX_MEM_UPDATE = prove
 (`!(a:int32) (b:byte) f c. (a =+ b) f c = if a = c then b else f c`,
  REWRITE_TAC[APPLY_UPDATE_THM]);;

let AG32AUX_NUM_UPDATE = prove
 (`!(r:num) (v:int32) f i. (r =+ v) f i = if r = i then v else f i`,
  REWRITE_TAC[APPLY_UPDATE_THM]);;

let AG32AUX_ALIGNED_ADDN = prove
 (`!a:int32. alignment_aligned 2 a ==>
     alignment_aligned 2 (word_add a (word 4)) /\ alignment_aligned 2 (word_add a (word 8)) /\
     alignment_aligned 2 (word_add a (word 12)) /\ alignment_aligned 2 (word_add a (word 16))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int32`] AG32AUX_ALIGNED_ADD4) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
     MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let AG32AUX_ALIGNED_NUMS = prove
 (`alignment_aligned 2 (word 4:int32) /\ alignment_aligned 2 (word 8:int32) /\
   alignment_aligned 2 (word 12:int32) /\ alignment_aligned 2 (word 16:int32)`,
  REWRITE_TAC[aligned_w2n] THEN CONV_TAC(DEPTH_CONV(WORD_VAL_CONV ORELSEC NUM_RED_CONV)));;

let AG32AUX_V2W_SING32 = prove
 (`!b. v2w [b]:int32 = if b then word 1 else word 0`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  CONV_TAC(DEPTH_CONV AG32AUX_V2W_LIT_CONV) THEN REWRITE_TAC[]);;

let AG32AUX_V2W_EQ0 = prove
 (`(!b. (v2w [b] = word 0:int32) <=> ~b) /\
   (!b. ((if b then word 1 else word 0) = word 0:int32) <=> ~b)`,
  CONJ_TAC THEN GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  CONV_TAC(DEPTH_CONV AG32AUX_V2W_LIT_CONV) THEN CONV_TAC WORD_REDUCE_CONV);;

let AG32AUX_WORD_LIST = [AG32AUX_W1; AG32AUX_W2; AG32AUX_W3; AG32AUX_W4; AG32AUX_SHIFT_IMM;
  long_mul_lem; AG32AUX_WORD_MUL_VAL; AG32AUX_WORD_ADD_VAL; AG32AUX_CARRY; WORD_ADD_0;
  AG32AUX_EXTRACT_ZX8];;

let AG32AUX_FINAL_LIST = [ag32_ok_def; AG32AUX_REG_UPDATE; AG32AUX_MEM_UPDATE;
  AG32AUX_NUM_UPDATE; AG32AUX_CARRY; long_mul_lem; AG32AUX_WORD_MUL_VAL; AG32AUX_WORD_ADD_VAL;
  WORD_ADD_0; COND_SWAP; AG32AUX_V2W_EQ0; AG32AUX_ALIGNED_NUMS; aligned_add_sub;
  AG32AUX_ALIGNED_ADDN; WORD_OR_0; ARITH; IN_INSERT; NOT_IN_EMPTY; AG32AUX_V2W_SING32;
  AG32AUX_EXTRACT_ZX8; aligned_pc; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; AG32AUX_ADD_CANCEL;
  AG32AUX_BYTES; AG32AUX_LOAD_BYTES];;

(* The tactics of the simulation (HOL4 next_tac and state_tac).  The goal: *)
(*   !s1 s2 ms. asm_step ag32_config s1 i s2 /\                             *)
(*              target_state_rel ag32_target s1 ms ==> ?n. !env. ...       *)
(* for an asm instruction i of a fixed shape.                               *)

let AG32AUX_bytes_assum asl =
  find (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "bytes_in_memory"
                  with Failure _ -> false) (map snd asl);;

(* a contradictory assumption: F, ~T, or both p and ~p *)

let AG32AUX_CONTR_TAC : tactic =
  let f_tm = `F` and nt_tm = `~T` in
  fun (asl,w as gl) ->
    let cs = map (concl o snd) asl in
    try let th = find (fun th -> let c = concl th in
                         c = f_tm || c = nt_tm || (is_neg c && mem (rand c) cs)) (map snd asl) in
        let c = concl th in
        if c = f_tm then CONTR_TAC th gl
        else if c = nt_tm then CONTR_TAC (EQ_MP (EQF_INTRO th) TRUTH) gl
        else let th' = snd(find (fun (_,t) -> concl t = rand c) asl) in
             CONTR_TAC (MP (NOT_ELIM th) th') gl
    with Failure _ -> ALL_TAC gl;;

(* unfold asm_step, target_state_rel and asm_ok *)

let AG32AUX_SETUP_TAC =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[asm_step_def; target_state_rel_def; AG32AUX_TARGET_FIELDS; ag32_config] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; MEM; CONJUNCT1 LT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `alignment_aligned 2 (asm_state_pc (s1:(32)asm_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ag32_ok_def]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[asm_ok_def; inst_ok_def; arith_ok_def; reg_ok_def;
     reg_imm_ok_def; fp_ok_def; fp_reg_ok_def; cmp_ok_def; asm_offset_ok_def; ag32_config;
     MEM; CONJUNCT1 LT; IN_INSERT; NOT_IN_EMPTY; ISL]) THEN
  RULE_ASSUM_TAC(CONV_RULE(CAKE_REWRITE_CONV[])) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th
                                 else failwith "")) THEN
  AG32AUX_CONTR_TAC;;

let AG32AUX_WRED_TAC =
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_RED_CONV)) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV);;

(* the encoding, as ag32_encode of a list of ag32 instructions *)

let AG32AUX_ENC_TAC =
  RULE_ASSUM_TAC(CONV_RULE(CAKE_REWRITE_CONV AG32AUX_ENC_RWTS THENC NUM_REDUCE_CONV)) THEN
  CONV_TAC(CAKE_REWRITE_CONV AG32AUX_ENC_RWTS THENC NUM_REDUCE_CONV) THEN
  AG32AUX_WRED_TAC;;

let AG32AUX_CLEAN_TAC =
  let rwts = [COND_CLAUSES; LET_DEF; LET_END_DEF; pair_CASE; APPEND; LENGTH;
              AG32AUX_LENGTH_ENCODE; IN_INSERT; NOT_IN_EMPTY] in
  RULE_ASSUM_TAC(CONV_RULE(CAKE_REWRITE_CONV rwts THENC NUM_REDUCE_CONV)) THEN
  CONV_TAC(CAKE_REWRITE_CONV rwts THENC NUM_REDUCE_CONV) THEN
  AG32AUX_WRED_TAC;;

(* a case split on the innermost conditional of the encoding *)

let AG32AUX_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let conds = find_terms is_cond (concl(AG32AUX_bytes_assum asl)) in
  let inner = filter (fun c -> not (exists (fun d -> not (d = c) && free_in d c) conds)) conds in
  match inner with
    [] -> failwith "AG32AUX_SPLIT_TAC"
  | c::_ -> (CASES_ON (lhand(rator c)) THEN AG32AUX_CLEAN_TAC THEN AG32AUX_CONTR_TAC) gl;;

(* the number of steps (the number of ag32 instructions less 1), asserts   *)
(* and asserts2 unfolded, and the facts of the code addresses              *)

let AG32AUX_BYTES_TAC : tactic = fun (asl,w as gl) ->
  let bth = AG32AUX_bytes_assum asl in
  let n = length(dest_list(rand(rand(rator(rator(concl bth)))))) in
  (MP_TAC(MATCH_MP bytes_in_memory_all_pcs bth) THEN
   REWRITE_TAC[AG32AUX_LENGTH_ENCODE; LENGTH; SUBSET] THEN CONV_TAC NUM_REDUCE_CONV THEN
   DISCH_THEN(ASSUME_TAC o SPEC `0`) THEN
   EXISTS_TAC (mk_small_numeral(n - 1)) THEN CONV_TAC AG32AUX_ASSERTS_CONV) gl;;

(* the asm side: s2 computed and substituted, its side conditions *)

let AG32AUX_SIMPLE_FACT th =
  let c = concl th in
  let c = if is_neg c then rand c else c in
  let h = if is_eq c then lhs c else c in
  try mem (fst(dest_const(rator h))) ["asm_state_be";"asm_state_lr";"asm_state_align"]
  with Failure _ -> false;;

let AG32AUX_ASM_TAC =
  let state_ty = `:(32)asm_state` in
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "asm_asm" with Failure _ -> false)
     then MP_TAC th else failwith "") THEN
  CONV_TAC(LAND_CONV(LAND_CONV(CAKE_REWRITE_CONV AG32AUX_ASM_RWTS THENC
    DEPTH_CONV (DIMINDEX_CONV ORELSEC NUM_RED_CONV ORELSEC LOG2_CONV)))) THEN
  ASSUM_LIST(fun thl -> CONV_TAC(LAND_CONV(LAND_CONV(CAKE_SIMP_CONV
    (GSYM WORD_ADD_ASSOC :: AG32AUX_MEMWORD_RWTS @ filter AG32AUX_SIMPLE_FACT thl))))) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(DEPTH_CONV WORD_RED_CONV))) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REPEAT(W(fun (asl,w) ->
    match find_terms (fun t -> is_cond t && type_of t = state_ty) w with
      [] -> NO_TAC
    | c::_ -> CASES_ON (lhand(rator c)))) THEN
  RULE_ASSUM_TAC(CONV_RULE(CAKE_SIMP_CONV[GSYM WORD_ADD_ASSOC; DE_MORGAN_THM] THENC
                           DEPTH_CONV WORD_RED_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th
                                 else failwith "")) THEN
  AG32AUX_CONTR_TAC;;

let AG32AUX_ENV_TAC =
  GEN_TAC THEN REWRITE_TAC[AG32AUX_INTERFERENCE] THEN STRIP_TAC;;

(* one step: the innermost ag32_Next t of the goal is the run of the next  *)
(* instruction of the encoding (HOL4 next_state_tac)                        *)

let AG32AUX_RUN_CONV =
  CAKE_REWRITE_CONV AG32AUX_RUN_RWTS THENC CAKE_SIMP_CONV[];;

let AG32AUX_NEXT_TAC : tactic =
  let next_tm = `ag32_Next` and run_tm = `ag32_Run`
  and el_tm = mk_const("EL",[`:instruction`,aty]) in
  let is_next t = is_comb t && rator t = next_tm in
  fun (asl,w as gl) ->
    let nexts = find_terms (fun t -> is_next t && not (can (find_term is_next) (rand t))) w in
    let t = rand(hd nexts) in
    let j = if is_var t then 0
            else Num.int_of_num(dest_numeral(rand(rator t))) + 1 in
    let bth = AG32AUX_bytes_assum asl in
    let pc,code,m,d = match snd(strip_comb(concl bth)) with
        [a;b;c;e] -> a,b,c,e | _ -> failwith "AG32AUX_NEXT_TAC" in
    let eqn = mk_eq(mk_comb(next_tm,t),
                    mk_comb(mk_comb(run_tm,mk_comb(mk_comb(el_tm,mk_small_numeral j),rand code)),
                            t)) in
    (SUBGOAL_THEN eqn SUBST1_TAC THENL
      [MATCH_MP_TAC AG32AUX_FETCH THEN MAP_EVERY EXISTS_TAC [pc;m;d] THEN
       REPEAT CONJ_TAC THENL
        [ACCEPT_TAC bth;
         ASM_MESON_TAC[ag32_ok_def];
         REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
         CONV_TAC NUM_REDUCE_CONV THEN SIMP[GSYM WORD_ADD_ASSOC; WORD_ADD_0] THEN
         CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN NO_TAC;
         REPEAT STRIP_TAC THEN SIMP[]];
       CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
       CONV_TAC(ONCE_DEPTH_CONV (fun tm ->
         if is_comb tm && is_comb(rator tm) && rator(rator tm) = run_tm
         then AG32AUX_RUN_CONV tm else failwith ""))]) gl;;

(* the final states compared (HOL4 state_tac): simplification, case splits *)
(* on the conditionals, word lemmas, and bit blasting of what is left       *)

let AG32AUX_WORD_FACT th =
  let c = concl th in
  not (can (find_term is_forall) c) && not (can (find_term is_exists) c) &&
  not (can (find_term (fun t -> is_const t && (let n = fst(dest_const t) in
          String.length n > 10 && (String.sub n 0 10 = "ag32_state" ||
                                   String.sub n 0 10 = "asm_state_")))) c) &&
  can (find_term (fun t -> is_const t && mem (fst(dest_const t))
          ["word_ile";"word_ilt";"word_ule";"word_ult";"alignment_aligned"])) c;;

let AG32AUX_STATE_FREE tm =
  not (can (find_term (fun t -> is_const t && (let n = fst(dest_const t) in
          String.length n > 10 && (String.sub n 0 10 = "ag32_state" ||
                                   String.sub n 0 10 = "asm_state_")))) tm);;

let AG32AUX_FULL_BLAST_TAC : tactic = fun (asl,w as gl) ->
  if not (AG32AUX_STATE_FREE w) then failwith "AG32AUX_FULL_BLAST_TAC" else
  (REPEAT(FIRST_X_ASSUM(fun th -> if AG32AUX_WORD_FACT th then MP_TAC th else failwith "")) THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN AG32AUX_BLAST_TAC) gl;;

let AG32AUX_FINAL_TAC =
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV AG32AUX_PCS_CONV) THEN
  CONV_TAC(CAKE_SIMP_CONV[GSYM WORD_ADD_ASSOC]) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REPEAT STRIP_TAC THEN AG32AUX_CONTR_TAC THEN
  TRY(SIMP AG32AUX_FINAL_LIST) THEN AG32AUX_CONTR_TAC THEN
  TRY(SIMP AG32AUX_WORD_LIST) THEN
  RW AG32AUX_FINAL_LIST THEN AG32AUX_CONTR_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[AG32AUX_ADD_CANCEL] THENC DEPTH_CONV WORD_RED_CONV THENC
                           REWRITE_CONV[])) THEN AG32AUX_CONTR_TAC THEN
  TRY(SIMP AG32AUX_WORD_LIST THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
      REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(W(fun (_,w) -> if is_eq w && can dest_word_ty (type_of(lhs w))
                     then ACCEPT_TAC(WORD_RULE w) else NO_TAC)) THEN
  TRY AG32AUX_FULL_BLAST_TAC;;

let AG32AUX_AUTO_TAC =
  AG32AUX_SETUP_TAC THEN AG32AUX_ENC_TAC THEN AG32AUX_CLEAN_TAC THEN AG32AUX_CONTR_TAC THEN
  REPEAT AG32AUX_SPLIT_TAC THEN AG32AUX_BYTES_TAC THEN
  AG32AUX_ASM_TAC THEN AG32AUX_ENV_TAC THEN
  REPEAT AG32AUX_NEXT_TAC THEN
  AG32AUX_FINAL_TAC;;

(* -- ag32 encoder_correct -- *)

(* encoder_correct ag32_target without target_ok, for each instruction *)

let AG32AUX_ENC_ALL =
  let tm = rand(rand(concl(REWRITE_CONV[encoder_correct_def; AG32AUX_TARGET_FIELDS;
                                         ag32_config] `encoder_correct ag32_target`))) in
  let s1,b = dest_forall tm in
  let i,b2 = dest_forall b in
  prove(mk_forall(i,mk_forall(s1,b2)),
        REWRITE_TAC AG32AUX_FORALL_ASM THEN REPEAT(CONJ_TAC ORELSE GEN_TAC) THEN
        AG32AUX_AUTO_TAC);;

let ag32_encoder_correct = prove
 (`encoder_correct ag32_target`,
  REWRITE_TAC[encoder_correct_def; ag32_target_ok; AG32AUX_TARGET_FIELDS; ag32_config] THEN
  MAP_EVERY X_GEN_TAC [`s1:(32)asm_state`; `i:(32)asm`] THEN
  MATCH_ACCEPT_TAC(SPEC `i:(32)asm` AG32AUX_ENC_ALL));;
