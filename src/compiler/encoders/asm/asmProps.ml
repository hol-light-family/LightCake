(* ========================================================================= *)
(* asmProps: port of HOL4 compiler/encoders/asm/asmPropsScript.sml (CakeML   *)
(* v3479).  Proofs of general properties of the asm language.                *)
(* ========================================================================= *)

needs "compiler/encoders/asm/asmSem.ml";;
needs "misc/misc.ml";;

type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - Records: HOL4 t.f is target_f t, s.f is asm_state_f s.                 *)
(* - Words: signed <= and < are word_ile and word_ilt; 0w = word 0;         *)
(*   n2w = word.                                                             *)
(* - Lists: FOLDR f e l is ITLIST f l e, GENLIST is list_of_seq, FUNPOW f n *)
(*   is ITER n f; HOL4 ($-) n is (-) n; HOL4 n + 1 - k is (n + 1) - k.       *)
(* - The free variables of a HOL4 statement are universally quantified,     *)
(*   after the quantified ones.                                              *)
(* - all_pcs_ind, asserts2_ind: HOL4's induction theorems of the two         *)
(*   recursive definitions (cake_ind).                                       *)

(* -- semantics is deterministic -- *)

let asm_deterministic = prove
 (`!(c:(A)asm_config) i s1 s2 s3.
     asm_step c s1 i s2 /\ asm_step c s1 i s3 ==> s2 = s3`,
  REWRITE_TAC[asm_step_def] THEN MESON_TAC[]);;

(* -- well-formedness of encoding -- *)

let offset_monotonic_def = cake_def
  `offset_monotonic (enc:(A)asm->byte list) (c:(A)asm_config) (a1:A word) a2 i1 i2 <=>
     asm_ok i1 c /\ asm_ok i2 c ==>
     (word_ile (word 0) a1 /\ word_ile (word 0) a2 /\ word_ile a1 a2
      ==> LENGTH (enc i1) <= LENGTH (enc i2)) /\
     (word_ilt a1 (word 0) /\ word_ilt a2 (word 0) /\ word_ile a2 a1
      ==> LENGTH (enc i1) <= LENGTH (enc i2))`;;

(* code alignment and length; label instantiation predictably affects the  *)
(* length of code                                                          *)

let enc_ok_def = cake_def
  `enc_ok (c:(A)asm_config) <=>
     2 EXP asm_config_code_alignment c =
       LENGTH (asm_config_encode c (asm_Inst asm_Skip)) /\
     (!w. LENGTH (asm_config_encode c w) MOD 2 EXP asm_config_code_alignment c = 0 /\
          ~(LENGTH (asm_config_encode c w) = 0)) /\
     (!w1 w2. offset_monotonic (asm_config_encode c) c w1 w2
                (asm_Jump w1) (asm_Jump w2)) /\
     (!cmp r ri w1 w2.
        offset_monotonic (asm_config_encode c) c w1 w2
          (asm_JumpCmp cmp r ri w1) (asm_JumpCmp cmp r ri w2)) /\
     (!w1 w2. offset_monotonic (asm_config_encode c) c w1 w2
                (asm_Call w1) (asm_Call w2)) /\
     (!w1 w2 r. offset_monotonic (asm_config_encode c) c w1 w2
                  (asm_Loc r w1) (asm_Loc r w2))`;;

(* -- correctness property to be proved for each backend -- *)

let target_INFO = cake_record "target"
  ["config","(A)asm_config";
   "next","B->B";
   "get_pc","B->A word";
   "get_reg","B->num->A word";
   "get_fp_reg","B->num->int64";
   "get_byte","B->A word->byte";
   "state_ok","B->bool";
   "proj","(A word->bool)->B->C"];;

let target_component_equality = target_INFO.ri_component_equality;;

let target_state_rel_def = cake_def
  `target_state_rel (t:(A,B,C)target) (s:(A)asm_state) (ms:B) <=>
     target_state_ok t ms /\ target_get_pc t ms = asm_state_pc s /\
     (!a. a IN asm_state_mem_domain s ==> target_get_byte t ms a = asm_state_mem s a) /\
     (!i. i < asm_config_reg_count (target_config t) /\
          ~MEM i (asm_config_avoid_regs (target_config t))
          ==> target_get_reg t ms i = asm_state_regs s i) /\
     (!i. i < asm_config_fp_reg_count (target_config t)
          ==> target_get_fp_reg t ms i = asm_state_fp_regs s i)`;;

let target_ok_def = cake_def
  `target_ok (t:(A,B,C)target) <=>
     enc_ok (target_config t) /\
     !ms1 ms2 (s:(A)asm_state).
       target_proj t (asm_state_mem_domain s) ms1 =
       target_proj t (asm_state_mem_domain s) ms2
       ==> (target_state_rel t s ms1 <=> target_state_rel t s ms2) /\
           (target_state_ok t ms1 <=> target_state_ok t ms2) /\
           target_get_pc t ms1 = target_get_pc t ms2 /\
           (!a. a IN asm_state_mem_domain s
                ==> target_get_byte t ms1 a = target_get_byte t ms2 a)`;;

let interference_ok_def = cake_def
  `interference_ok (env:num->A->A) (proj:A->B) <=>
     !i:num ms. proj (env i ms) = proj ms`;;

(* HOL4 exports arithmetic.ZERO_LT_EXP as a termination simp for all_pcs *)

let all_pcs_def = cake_def_wf
  `measure (\(n:num,a:A word,k:num). n)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`2`; `k:num`] EXP_EQ_0) THEN ARITH_TAC)
  `(all_pcs 0 (a:A word) k = {}) /\
   (all_pcs n a k = a INSERT all_pcs (n - 2 EXP k) (word_add a (word (2 EXP k))) k)`;;

let all_pcs_ind = cake_ind "all_pcs";;

let all_pcs_thm = prove
 (`!n (a:A word) k.
     all_pcs n a k = {word_add a (word (i * 2 EXP k)) | i | i * 2 EXP k < n}`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN DISCH_TAC THEN
  X_GEN_TAC `a:A word` THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[all_pcs_def; CONJUNCT1 LT; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:A word` THEN
  SUBGOAL_THEN `~(2 EXP k = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n' - 2 EXP k`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
      ARITH_TAC;
      EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD_AC]]];
    DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j:num` SUBST1_TAC)
      (SPEC `i:num` num_CASES) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `j:num` THEN REWRITE_TAC[WORD_ADD] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD_AC]]]);;

let asserts_def = cake_def
  `(asserts 0 (next:num->A->A) ms (_:A->bool) (Q:A->bool) <=> Q (next 0 ms)) /\
   (asserts (SUC n) next ms P Q <=>
      let ms' = next (SUC n) ms in P ms' /\ asserts n next ms' P Q)`;;

let asserts2_def = cake_def
  `asserts2 n (fi:num->A->A) (fc:A->A) ms (P:A->A->bool) <=>
     if n = 0 then T
     else P ms (fc ms) /\ asserts2 (n - 1) fi fc (fi n (fc ms)) P`;;

let asserts2_ind = cake_ind "asserts2";;

(* HOL4 n + 1 - k is (n + 1) - k *)

let encoder_correct_def = cake_def
  `encoder_correct (t:(A,B,C)target) <=>
     target_ok t /\
     !s1 i s2 ms.
       asm_step (target_config t) s1 i s2 /\ target_state_rel t s1 ms ==>
       ?n. !env.
             interference_ok (env:num->B->B) (target_proj t (asm_state_mem_domain s1))
             ==> let pcs = all_pcs (LENGTH (asm_config_encode (target_config t) i))
                                   (asm_state_pc s1) in
                 asserts n (\k s. env (n - k) (target_next t s)) ms
                   (\ms'. target_state_ok t ms' /\
                          (!pc. pc IN pcs 0
                                ==> target_get_byte t ms' pc = target_get_byte t ms pc) /\
                          target_get_pc t ms' IN pcs (asm_config_code_alignment (target_config t)))
                   (\ms'. target_state_rel t s2 ms') /\
                 asserts2 (n + 1) (\k. env ((n + 1) - k)) (target_next t) ms
                   (\ms1 ms2. !x. ~(x IN asm_state_mem_domain s1)
                                  ==> target_get_byte t ms1 x = target_get_byte t ms2 x)`;;

(* lemma for proofs *)

let bytes_in_memory_all_pcs = prove
 (`!xs (pc:A word) m d k.
     bytes_in_memory pc xs m d ==> all_pcs (LENGTH xs) pc k SUBSET d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[all_pcs_thm; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC bytes_in_memory_in_domain THEN
  MAP_EVERY EXISTS_TAC [`xs:byte list`; `m:A word->byte`] THEN
  ASM_REWRITE_TAC[]);;

let read_bytearray_IMP_bytes_in_memory = prove
 (`!p n m ba m' md.
     n = LENGTH ba /\
     (!k. k IN all_words p n ==> k IN md /\ m k = SOME (m' k)) /\
     read_bytearray (p:A word) n m = SOME ba
     ==> bytes_in_memory p ba m' md`,
  REPEAT GEN_TAC THEN SPEC_TAC(`p:A word`,`p:A word`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`ba:byte list`,`ba:byte list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[bytes_in_memory_def; LENGTH] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN SUBST1_TAC (CONJUNCT1 th)) THEN
  REWRITE_TAC[read_bytearray_def; all_words_def; IN_INSERT] THEN
  REWRITE_TAC[case_eq "option"; option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `p:A word`) THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `LENGTH (t:byte list)` THEN
  ASM_MESON_TAC[]);;

let sym_target_state_rel = prove
 (`!(t:(A,B,C)target) s ms.
     target_state_rel t s ms <=>
     target_state_ok t ms /\ asm_state_pc s = target_get_pc t ms /\
     (!a. a IN asm_state_mem_domain s ==> asm_state_mem s a = target_get_byte t ms a) /\
     (!i. i < asm_config_reg_count (target_config t) /\
          ~MEM i (asm_config_avoid_regs (target_config t))
          ==> asm_state_regs s i = target_get_reg t ms i) /\
     (!i. i < asm_config_fp_reg_count (target_config t)
          ==> asm_state_fp_regs s i = target_get_fp_reg t ms i)`,
  REWRITE_TAC[target_state_rel_def] THEN MESON_TAC[]);;

(* Not ported (evaluation forms for HOL4 automation, used only by the      *)
(* target proofs of the encoders): all_pcs (numLib.SUC_RULE all_pcs_def)  *)
(* and asserts_eval (asserts_def unfolded at SUC^n 0 for n < 20).          *)

let asserts_IMP_FOLDR_COUNT_LIST = prove
 (`!n (next:num->A->A) ms P Q.
     asserts n next ms P Q ==> Q (ITLIST next (COUNT_LIST n) (next n ms))`,
  INDUCT_TAC THEN
  REWRITE_TAC[asserts_def; COUNT_LIST_SNOC; FOLDR_SNOC; ITLIST; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* helper (ASMAUX_): one step of the unrolling of the state lists of the  *)
(* asserts lemmas                                                          *)

let ASMAUX_ITLIST_REVERSE_GENLIST_SUB = prove
 (`!n k (f:num->A->A) s.
     ITLIST f (REVERSE (list_of_seq ((-) (SUC n)) (SUC k))) s =
     ITLIST f (REVERSE (list_of_seq ((-) n) k)) (f (SUC n) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ; REVERSE; ITLIST_APPEND; ITLIST; SUB_0] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; SUB_SUC]);;

let asserts_IMP_FOLDR_COUNT_LIST_LESS = prove
 (`!k n (next:num->A->A) ms P Q.
     asserts n next ms P Q /\ k < n
     ==> P (ITLIST next (REVERSE (list_of_seq ((-) n) (SUC k))) ms)`,
  INDUCT_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
    REWRITE_TAC[ASMAUX_ITLIST_REVERSE_GENLIST_SUB; asserts_def; LET_DEF; LET_END_DEF;
                LIST_OF_SEQ; REVERSE; ITLIST] THEN MESON_TAC[];
    INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT; LT_SUC] THEN
    REWRITE_TAC[ASMAUX_ITLIST_REVERSE_GENLIST_SUB; asserts_def; LET_DEF; LET_END_DEF] THEN
    ASM_MESON_TAC[]]);;

let asserts_WEAKEN = prove
 (`!n (next:num->A->A) s P Q next' P'.
     (!k. k <= n
          ==> next k = next' k /\
              (P (ITLIST next (REVERSE (list_of_seq ((-) n) (SUC k))) s)
               ==> P' (ITLIST next (REVERSE (list_of_seq ((-) n) (SUC k))) s)))
     ==> asserts n next s P Q ==> asserts n next' s P' Q`,
  INDUCT_TAC THEN REWRITE_TAC[asserts_def; LET_DEF; LET_END_DEF] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LE_REFL] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(next':num->A->A) (SUC n) = next (SUC n)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LE_0; ASMAUX_ITLIST_REVERSE_GENLIST_SUB; LIST_OF_SEQ; REVERSE;
                ITLIST] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  EXISTS_TAC `next:num->A->A` THEN EXISTS_TAC `P:A->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN ASM_REWRITE_TAC[LE_SUC] THEN
    REWRITE_TAC[ASMAUX_ITLIST_REVERSE_GENLIST_SUB] THEN MESON_TAC[]]);;

(* Not ported (evaluation form for HOL4 automation): asserts2_eval         *)
(* (asserts2_def unfolded at the numerals 0 .. 20).                         *)

let asserts2_change_interfer = prove
 (`!n (fi:num->A->A) fc ms P fi2.
     asserts2 n fi fc ms P /\ (!k. k <= n ==> fi k = fi2 k)
     ==> asserts2 n fi2 fc ms P`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[asserts2_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(fi2:num->A->A) (SUC n) = fi (SUC n)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `fi:num->A->A` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let asserts2_first = prove
 (`!n (fi:num->A->A) fc ms P. 1 <= n /\ asserts2 n fi fc ms P ==> P ms (fc ms)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[asserts2_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL [ARITH_TAC; MESON_TAC[]]);;

let asserts2_every = prove
 (`!n ms j (f:A->A) g P.
     asserts2 n (\k. f) g ms P /\ j < n
     ==> P (ITER j (f o g) ms) (g (ITER j (f o g) ms))`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[asserts2_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `j:num` num_CASES) THEN
  REWRITE_TAC[LT_SUC; ITER_ALT; o_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let upd_pc_simps = prove
 (`!(x:A word) (s:(A)asm_state).
     asm_state_align (asm_upd_pc x s) = asm_state_align s /\
     asm_state_mem_domain (asm_upd_pc x s) = asm_state_mem_domain s /\
     (asm_state_failed (asm_upd_pc x s) <=> asm_state_failed s) /\
     (asm_state_be (asm_upd_pc x s) <=> asm_state_be s) /\
     asm_state_mem (asm_upd_pc x s) = asm_state_mem s /\
     asm_state_regs (asm_upd_pc x s) = asm_state_regs s /\
     asm_state_fp_regs (asm_upd_pc x s) = asm_state_fp_regs s /\
     asm_state_lr (asm_upd_pc x s) = asm_state_lr s /\
     asm_state_pc (asm_upd_pc x s) = x`,
  REWRITE_TAC[asm_upd_pc_def] THEN SIMP[]);;
let _ = cake_add_simps [upd_pc_simps];;

let asm_failed_ignore_new_pc = prove
 (`!i (v:A word) w s. asm_state_failed (asm i w s) <=> asm_state_failed (asm i v s)`,
  GEN_TAC THEN CASES_ON `i:(A)asm` THEN
  FS[asm_def; asm_upd_pc_def; jump_to_offset_def; asm_upd_reg_def] THEN
  RW[] THEN FS[]);;

let asm_mem_ignore_new_pc = prove
 (`!i (v:A word) w s. asm_state_mem (asm i w s) = asm_state_mem (asm i v s)`,
  GEN_TAC THEN CASES_ON `i:(A)asm` THEN
  FS[asm_def; asm_upd_pc_def; jump_to_offset_def; asm_upd_reg_def] THEN
  RW[] THEN FS[]);;

(* HOL4 [local] *)

let SND_read_mem_word_consts = prove
 (`!n (a:A word) s.
     (asm_state_be (SND (read_mem_word a n s)) <=> asm_state_be s) /\
     asm_state_lr (SND (read_mem_word a n s)) = asm_state_lr s /\
     asm_state_align (SND (read_mem_word a n s)) = asm_state_align s /\
     asm_state_mem_domain (SND (read_mem_word a n s)) = asm_state_mem_domain s`,
  INDUCT_TAC THEN REWRITE_TAC[read_mem_word_def; SND] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`if asm_state_be (s:(A)asm_state) then word_sub (a:A word) (word 1)
      else word_add a (word 1)`; `s:(A)asm_state`]) THEN
  ASM_REWRITE_TAC[SND] THEN SIMP[asm_assert_def]);;

(* HOL4 [local] *)

let write_mem_word_consts = prove
 (`!n (a:A word) w s.
     (asm_state_be (write_mem_word a n w s) <=> asm_state_be s) /\
     asm_state_lr (write_mem_word a n w s) = asm_state_lr s /\
     asm_state_align (write_mem_word a n w s) = asm_state_align s /\
     asm_state_mem_domain (write_mem_word a n w s) = asm_state_mem_domain s`,
  INDUCT_TAC THEN
  SIMP[write_mem_word_def; LET_DEF; LET_END_DEF; asm_assert_def; asm_upd_mem_def]);;

let asm_binop_upd_consts = prove
 (`!a b (c:A word) d (x:(A)asm_state).
     asm_state_mem_domain (asm_binop_upd a b c d x) = asm_state_mem_domain x /\
     asm_state_align (asm_binop_upd a b c d x) = asm_state_align x /\
     (asm_state_failed (asm_binop_upd a b c d x) <=> asm_state_failed x) /\
     asm_state_mem (asm_binop_upd a b c d x) = asm_state_mem x /\
     asm_state_lr (asm_binop_upd a b c d x) = asm_state_lr x /\
     (asm_state_be (asm_binop_upd a b c d x) <=> asm_state_be x)`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `b:binop` THEN
  SIMP[asm_binop_upd_def; asm_upd_reg_def]);;
let _ = cake_add_simps [asm_binop_upd_consts];;

let asm_arith_upd_consts = prove
 (`!a (x:(A)asm_state).
     asm_state_mem_domain (asm_arith_upd a x) = asm_state_mem_domain x /\
     asm_state_align (asm_arith_upd a x) = asm_state_align x /\
     asm_state_mem (asm_arith_upd a x) = asm_state_mem x /\
     asm_state_lr (asm_arith_upd a x) = asm_state_lr x /\
     (asm_state_be (asm_arith_upd a x) <=> asm_state_be x)`,
  GEN_TAC THEN CASES_ON `a:(A)asm_arith` THEN
  SIMP[asm_arith_upd_def; asm_upd_reg_def; asm_assert_def; LET_DEF; LET_END_DEF]);;
let _ = cake_add_simps [asm_arith_upd_consts];;

let asm_fp_upd_consts = prove
 (`!a (x:(A)asm_state).
     asm_state_mem_domain (asm_fp_upd a x) = asm_state_mem_domain x /\
     asm_state_align (asm_fp_upd a x) = asm_state_align x /\
     asm_state_mem (asm_fp_upd a x) = asm_state_mem x /\
     asm_state_lr (asm_fp_upd a x) = asm_state_lr x /\
     (asm_state_be (asm_fp_upd a x) <=> asm_state_be x)`,
  REPEAT GEN_TAC THEN CASES_ON `a:fp` THEN
  SIMP[asm_fp_upd_def; asm_upd_reg_def; asm_upd_fp_reg_def; asm_assert_def;
       LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN SIMP[asm_upd_fp_reg_def; asm_assert_def]);;
let _ = cake_add_simps [asm_fp_upd_consts];;

(* helpers (ASMAUX_) for asm_consts: the components that memory operations *)
(* and instructions keep                                                     *)

let ASMAUX_mem_load_consts = prove
 (`!n r a (s:(A)asm_state).
     (asm_state_be (asm_mem_load n r a s) <=> asm_state_be s) /\
     asm_state_lr (asm_mem_load n r a s) = asm_state_lr s /\
     asm_state_align (asm_mem_load n r a s) = asm_state_align s /\
     asm_state_mem_domain (asm_mem_load n r a s) = asm_state_mem_domain s`,
  SIMP[asm_mem_load_def; LET_DEF; LET_END_DEF; pair_CASE_def; asm_upd_reg_def;
       asm_assert_def; SND_read_mem_word_consts]);;

let ASMAUX_mem_store_consts = prove
 (`!n r a (s:(A)asm_state).
     (asm_state_be (asm_mem_store n r a s) <=> asm_state_be s) /\
     asm_state_lr (asm_mem_store n r a s) = asm_state_lr s /\
     asm_state_align (asm_mem_store n r a s) = asm_state_align s /\
     asm_state_mem_domain (asm_mem_store n r a s) = asm_state_mem_domain s`,
  SIMP[asm_mem_store_def; LET_DEF; LET_END_DEF; asm_assert_def;
       write_mem_word_consts]);;

let ASMAUX_mem_op_consts = prove
 (`!m r a (s:(A)asm_state).
     (asm_state_be (asm_mem_op m r a s) <=> asm_state_be s) /\
     asm_state_lr (asm_mem_op m r a s) = asm_state_lr s /\
     asm_state_align (asm_mem_op m r a s) = asm_state_align s /\
     asm_state_mem_domain (asm_mem_op m r a s) = asm_state_mem_domain s`,
  GEN_TAC THEN CASES_ON `m:memop` THEN
  SIMP[asm_mem_op_def; ASMAUX_mem_load_consts; ASMAUX_mem_store_consts]);;

let ASMAUX_inst_consts = prove
 (`!i (s:(A)asm_state).
     (asm_state_be (asmSem_inst i s) <=> asm_state_be s) /\
     asm_state_lr (asmSem_inst i s) = asm_state_lr s /\
     asm_state_align (asmSem_inst i s) = asm_state_align s /\
     asm_state_mem_domain (asmSem_inst i s) = asm_state_mem_domain s`,
  GEN_TAC THEN CASES_ON `i:(A)inst` THEN
  SIMP[asmSem_inst_def; asm_upd_reg_def; ASMAUX_mem_op_consts]);;

let asm_consts = prove
 (`!i (w:A word) s.
     (asm_state_be (asm i w s) <=> asm_state_be s) /\
     asm_state_lr (asm i w s) = asm_state_lr s /\
     asm_state_align (asm i w s) = asm_state_align s /\
     asm_state_mem_domain (asm i w s) = asm_state_mem_domain s`,
  REPEAT GEN_TAC THEN CASES_ON `i:(A)asm` THEN
  SIMP[asm_def; jump_to_offset_def; asm_upd_reg_def; asm_assert_def; LET_DEF;
       LET_END_DEF; ASMAUX_inst_consts] THEN
  RW[] THEN SIMP[]);;
let _ = cake_add_simps [asm_consts];;

let RTC_asm_step_consts = prove
 (`!(c:(A)asm_config) s1 s2.
     RTC (\s1 s2. ?i. asm_step c s1 i s2) s1 s2
     ==> asm_state_mem_domain s2 = asm_state_mem_domain s1 /\
         asm_state_lr s2 = asm_state_lr s1 /\
         asm_state_align s2 = asm_state_align s1 /\
         (asm_state_be s2 <=> asm_state_be s1)`,
  GEN_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[asm_step_def] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> is_eq(concl th) && is_var(rhs(concl th)))) THEN
    REWRITE_TAC[asm_consts];
    REWRITE_TAC[];
    MESON_TAC[]]);;

let read_mem_word_IMP_mem_eq = prove
 (`!(a:A word) k s w s'.
     read_mem_word a k s = (w,s') ==> asm_state_mem s' = asm_state_mem s`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[read_mem_word_def; pair_CASE_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[asm_assert_def] THEN SIMP[] THEN ASM_MESON_TAC[PAIR]);;

let write_mem_word_mem_domain = prove
 (`!k b (a:A word) s.
     asm_state_mem_domain (write_mem_word b k a s) = asm_state_mem_domain s`,
  INDUCT_TAC THEN
  SIMP[write_mem_word_def; LET_DEF; LET_END_DEF; asm_assert_def; asm_upd_mem_def]);;

let write_mem_word_mem_eq = prove
 (`!k b (a:A word) s x.
     ~asm_state_failed (write_mem_word b k a s) /\ ~(x IN asm_state_mem_domain s)
     ==> asm_state_mem (write_mem_word b k a s) x = asm_state_mem s x`,
  INDUCT_TAC THEN REWRITE_TAC[write_mem_word_def; LET_DEF; LET_END_DEF] THEN
  SIMP[asm_assert_def; asm_upd_mem_def; APPLY_UPDATE_THM; write_mem_word_mem_domain;
       DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let mem_op_outside_mem_domain = prove
 (`!m n a (s:(A)asm_state) x.
     ~(x IN asm_state_mem_domain s) /\ ~asm_state_failed (asm_mem_op m n a s)
     ==> asm_state_mem (asm_mem_op m n a s) x = asm_state_mem s x`,
  GEN_TAC THEN CASES_ON `m:memop` THEN
  REWRITE_TAC[asm_mem_op_def; asm_mem_load_def; asm_mem_store_def; LET_DEF;
              LET_END_DEF; pair_CASE_def] THEN
  SIMP[asm_assert_def; asm_upd_reg_def; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[read_mem_word_IMP_mem_eq; write_mem_word_mem_eq; PAIR]);;

let inst_outside_mem_domain = prove
 (`!i (x:A word) s.
     ~(x IN asm_state_mem_domain s) /\ ~asm_state_failed (asmSem_inst i s)
     ==> asm_state_mem (asmSem_inst i s) x = asm_state_mem s x`,
  GEN_TAC THEN CASES_ON `i:(A)inst` THEN
  SIMP[asmSem_inst_def; asm_upd_reg_def; mem_op_outside_mem_domain]);;

let asm_outside_mem_domain = prove
 (`!i p (s:(A)asm_state) x.
     ~(x IN asm_state_mem_domain s) /\ ~asm_state_failed (asm i p s)
     ==> asm_state_mem (asm i p s) x = asm_state_mem s x`,
  REPEAT GEN_TAC THEN CASES_ON `i:(A)asm` THEN
  SIMP[asm_def; jump_to_offset_def; asm_upd_reg_def; asm_assert_def; LET_DEF;
       LET_END_DEF; inst_outside_mem_domain] THEN
  RW[] THEN SIMP[]);;

let asm_step_outside_mem_domain = prove
 (`!(c:(A)asm_config) s1 i s2.
     asm_step c s1 i s2
     ==> !x. ~(x IN asm_state_mem_domain s1)
             ==> asm_state_mem s2 x = asm_state_mem s1 x`,
  REWRITE_TAC[asm_step_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && is_var(rhs(concl th)))) THEN
  MATCH_MP_TAC asm_outside_mem_domain THEN ASM_REWRITE_TAC[]);;

let RTC_asm_step_outside_mem_domain = prove
 (`!s1 s2 (c:(A)asm_config).
     RTC (\s1 s2. ?i. asm_step c s1 i s2) s1 s2
     ==> !a. ~(a IN asm_state_mem_domain s1)
             ==> asm_state_mem s2 a = asm_state_mem s1 a`,
  SUBGOAL_THEN
   `!(c:(A)asm_config) s1 s2.
      RTC (\s1 s2. ?i. asm_step c s1 i s2) s1 s2
      ==> !a. ~(a IN asm_state_mem_domain s1)
              ==> asm_state_mem s2 a = asm_state_mem s1 a`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN MATCH_MP_TAC relation_RTC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:(A)asm`) ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP asm_step_outside_mem_domain) THEN
    SUBGOAL_THEN
     `asm_state_mem_domain (s2:(A)asm_state) = asm_state_mem_domain s1`
     ASSUME_TAC THENL
     [UNDISCH_TAC `asm_step (c:(A)asm_config) s1 i s2` THEN
      REWRITE_TAC[asm_step_def] THEN MESON_TAC[asm_consts];
      ASM_MESON_TAC[]]]);;
