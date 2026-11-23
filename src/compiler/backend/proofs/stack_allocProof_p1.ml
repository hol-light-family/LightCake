(* ========================================================================= *)
(* stack_allocProof_p1: part 1 of 3 (HOL4 lines 1-1716) of the port of HOL4 *)
(* compiler/backend/proofs/stack_allocProofScript.sml (CakeML v3479).        *)
(* Correctness proof for stack_alloc.                                        *)
(* The parts stack_allocProof_p1.ml, stack_allocProof_p2.ml (HOL4 lines      *)
(* 1717-4591) and stack_allocProof.ml (HOL4 lines 4592-6361) are loaded one  *)
(* after the other (each needs the previous one).                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 stackSem state s: (A,C,FFI)stack_state; s.f is stack_state_f s;   *)
(*   s with f := v is stack_state_f_fupd (K v) s, and s with <| f1 := v1;   *)
(*   f2 := v2 |> nests the updates with the first field outermost.           *)
(* - Words: n2w = word, w2n = val, + = word_add, * = word_mul, - = word_sub, *)
(*   && = word_and, || = word_or, << = word_shl, >>> = word_ushr,            *)
(*   <+ = word_ult, <=+ = word_ule, w ' i = bit i w, (h -- l) w =            *)
(*   word_bits h l w; HOL4 word_shift (:'a) is backend_common_word_shift     *)
(*   (:A); GENLIST is list_of_seq; s ' k (finite maps) is FAPPLY s k.        *)
(* - The HOL4 proofs run the GC code with simp and the evaluation rules     *)
(*   (HOL4 tac, line 372).  Here a symbolic evaluator does that (the        *)
(*   STALLOCAUX block before memcpy_code_thm): it rewrites                   *)
(*   stack_evaluate (code,s) with one theorem per instruction and leaves the *)
(*   rest of the code where it cannot go on (a sub-program, a loop          *)
(*   iteration, a test that the assumptions do not decide).                  *)
(* - STALLOCAUX_ names are local helpers of this unit.                       *)

(* HOL4 line 28: the same theorem (up to the names of its variables) as    *)
(* lsl_lsr of src/hol4/words4.ml, bound again here under its HOL4 name     *)
let lsl_lsr = lsl_lsr;;

(* HOL4 line 51 *)
let stack_allocProof_bytes_in_word_word_shift = prove
 (`good_dimindex(:A) /\ val (bytes_in_word:A word) * val (n:A word) < dimword(:A)
   ==> word_ushr (word_mul bytes_in_word n) (backend_common_word_shift (:A)) = n`,
  STRIP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP bytes_in_word_mul_eq_shift th]) THEN
  MATCH_MP_TAC lsl_lsr THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `dimword(:A)`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def]) THEN
  REWRITE_TAC[bytes_in_word_def; backend_common_word_shift_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(* HOL4 line 66 *)
let get_var_imm_case = prove
 (CASE_TERM
  `!(ri:(A)reg_imm) (s:(A,C,FFI)stack_state).
     stack_get_var_imm ri s =
     match ri with Reg n -> stack_get_var n s | Imm w -> SOME (wl_Word w)`,
  GEN_TAC THEN CASES_ON `ri:(A)reg_imm` THEN REWRITE_TAC[stack_get_var_imm_def] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 75 *)
let prog_comp_lemma = prove
 (`stack_alloc_prog_comp =
   \(n,p:(A)stack_prog). (n,FST (stack_alloc_comp n (next_lab p 2) p))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; stack_alloc_prog_comp_def]);;

(* HOL4 line 81 *)
let stack_allocProof_FST_prog_comp = prove
 (`!pp:num#(A)stack_prog. FST (stack_alloc_prog_comp pp) = FST pp`,
  REWRITE_TAC[FORALL_PAIR_THM; stack_alloc_prog_comp_def]);;
let _ = cake_add_simps [stack_allocProof_FST_prog_comp];;

(* HOL4 line 87 *)
let lookup_IMP_lookup_compile = prove
 (`!dest (s:(A,C,FFI)stack_state) x (c:data_to_word_config).
     lookup dest (stack_state_code s) = SOME x /\ ~(dest = gc_stub_location)
     ==> ?m1 n1. lookup dest (fromAList (stack_alloc_compile c
                                           (toAList (stack_state_code s)))) =
                 SOME (FST (stack_alloc_comp m1 n1 x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lookup_fromAList; stack_alloc_compile_def; ALOOKUP_APPEND] THEN
  SUBGOAL_THEN `ALOOKUP (stack_alloc_stubs c:(num#(A)stack_prog)list) dest = NONE`
    SUBST1_TAC THENL
   [REWRITE_TAC[stack_alloc_stubs_def; ALOOKUP_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[prog_comp_lemma; ALOOKUP_MAP_2] THEN
  ASM_REWRITE_TAC[ALOOKUP_toAList; OPTION_MAP_DEF; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 100 *)
let map_bitmap_APPEND = prove
 (CASE_TERM
  `!x (q:A list) stack p0 p1 q'.
     filter_bitmap x stack = SOME (p0,p1) /\ LENGTH q = LENGTH p0
     ==> map_bitmap x (APPEND q q') stack =
         match map_bitmap x q stack with
           NONE -> NONE
         | SOME (hd,ts,ws) -> SOME (hd,APPEND ts q',ws)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[map_bitmap_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  BOOL_CASES_TAC `h:bool` THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `stack:A list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def; option_DISTINCT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[option_case_eq; pair_case_eq] THENL
   [CASES_ON `q:A list` THEN GVS[LENGTH; NOT_SUC; SUC_INJ] THEN
    REWRITE_TAC[APPEND; map_bitmap_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a1:A list`; `t':A list`; `x:A list`; `p1:A list`;
                                  `q':A list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC;
    REWRITE_TAC[map_bitmap_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:A list`; `t':A list`; `p0:A list`; `p1:A list`;
                                  `q':A list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  CASE_TAC THEN CASE_REWRITE_TAC[] THEN
  CASE_TAC THEN CASE_REWRITE_TAC[] THEN CASE_TAC THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 119 *)
let filter_bitmap_map_bitmap = prove
 (`!x (t:A list) q xs xs1 z ys ys1.
      filter_bitmap x t = SOME (xs,xs1) /\
      LENGTH q = LENGTH xs /\
      map_bitmap x q t = SOME (ys,z,ys1) ==>
      z = [] /\ ys1 = xs1`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_bitmap_def; map_bitmap_def; option_INJ; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LENGTH_EQ_NIL]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN BOOL_CASES_TAC `h:bool` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t':A list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def; option_DISTINCT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (fun ih -> GVS[map_bitmap_def; option_case_eq; pair_case_eq] THEN
                              ASSUME_TAC ih) THENL
   [POP_ASSUM(fun ih -> CASES_ON `q:A list` THEN
      GVS[LENGTH; NOT_SUC; SUC_INJ; map_bitmap_def; option_case_eq; pair_case_eq] THEN
      ASSUME_TAC ih) THEN
    POP_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    POP_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 150 *)
let get_bits_def = cake_def
  `get_bits (w:A word) = list_of_seq (\i. bit i w) (bit_length w - 1)`;;

(* HOL4 line 154 *)
let bit_length_thm = prove
 (`!w:A word. word_ushr w (bit_length w) = word 0 /\
              !n. n < bit_length w ==> ~(word_ushr w n = word 0)`,
  MATCH_MP_TAC (REWRITE_RULE[] bit_length_ind) THEN GEN_TAC THEN
  DISCH_TAC THEN GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [bit_length_def] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[WORD_USHR_ZERO; LT] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP (ASSUME `~(w:A word = word 0)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_USHR_COMPOSE]) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[WORD_USHR_ZERO] THEN
  REWRITE_TAC[ADD1; LT_ADD_RCANCEL] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 167 *)
let word_lsr_dimindex = prove
 (`!w:A word. word_ushr w (dimindex (:A)) = word 0`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_0] THEN
  MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[VAL_BOUND]);;

(* HOL4 line 173 *)
let bit_length_LESS_EQ_dimindex = prove
 (`!w:A word. bit_length w <= dimindex (:A)`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(CONJUNCT2(SPEC `w:A word` bit_length_thm)) THEN
  DISCH_THEN(MP_TAC o SPEC `dimindex(:A)`) THEN
  ASM_REWRITE_TAC[word_lsr_dimindex]);;

(* HOL4 line 181 *)
let shift_to_zero_word_msb = prove
 (`!(w:A word) n. word_ushr w n = word 0 /\ word_msb w ==> dimindex (:A) <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_msb_def] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `bit ((dimindex(:A) - 1) - n):A word->bool`) THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_0] THEN
  SUBGOAL_THEN `((dimindex(:A) - 1) - n) + n = dimindex(:A) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* HOL4 line 192 *)
let word_msb_IMP_bit_length = prove
 (`!h:A word. word_msb h ==> bit_length h = dimindex (:A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM; bit_length_LESS_EQ_dimindex] THEN
  MATCH_MP_TAC shift_to_zero_word_msb THEN EXISTS_TAC `h:A word` THEN
  ASM_REWRITE_TAC[bit_length_thm]);;

(* HOL4 line 202 *)
let get_bits_intro = prove
 (`!h:A word. word_msb h ==>
     list_of_seq (\i. bit i h) (dimindex (:A) - 1) = get_bits h`,
  SIMP_TAC[get_bits_def; word_msb_IMP_bit_length]);;

(* HOL4 line 209 *)
let filter_bitmap_APPEND = prove
 (CASE_TERM
  `!xs (stack:A list) ys.
     filter_bitmap (APPEND xs ys) stack =
     match filter_bitmap xs stack with
       NONE -> NONE
     | SOME (zs,rs) ->
         (match filter_bitmap ys rs with
            NONE -> NONE
          | SOME (zs2,rs) -> SOME (APPEND zs zs2,rs))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; filter_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN CASE_TAC THEN CASE_REWRITE_TAC[APPEND] THEN
    CASE_TAC THEN CASE_REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  BOOL_CASES_TAC `h:bool` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `stack:A list` list_CASES) THEN
  ASM_REWRITE_TAC[APPEND; filter_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  GEN_TAC THEN REPEAT (CASE_TAC THEN CASE_REWRITE_TAC[APPEND]));;

(* HOL4 line 226 *)
let bit_length_minus_1 = prove
 (`!w:A word. ~(w = word 0) ==> bit_length w - 1 = bit_length (word_ushr w 1)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bit_length_def] THEN
  ASM_REWRITE_TAC[ADD_SUB]);;

(* a helper for bit_length_eq_1 *)
let STALLOCAUX_bit_length_eq_0 = prove
 (`!w:A word. bit_length w = 0 <=> w = word 0`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bit_length_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ]);;

(* HOL4 line 232 *)
let bit_length_eq_1 = prove
 (`!w:A word. bit_length w = 1 <=> w = word 1`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bit_length_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n + 1 = 1 <=> n = 0`; STALLOCAUX_bit_length_eq_0] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_1; VAL_WORD_USHR; EXP_1] THEN
  ARITH_TAC);;

(* HOL4 line 246 *)
let stack_allocProof_word_and_one_eq_0_iff = prove
 (`!w:A word. word_and w (word 1) = word 0 <=> ~bit 0 w`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD_1] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[DIMINDEX_GT_0];
    MESON_TAC[]]);;

(* HOL4 line 252 *)
let split_num_forall_to_10 = prove
 (`!P. (!x:num. P x) <=>
       P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
       !x. 9 < x ==> P x`,
  GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `9 < x` THEN ASM_SIMP_TAC[] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`x:num`,`x:num`) THEN
  REWRITE_TAC[ARITH_RULE `~(9 < x) <=> x < 10`] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 268 *)
let word_shift_not_0 = prove
 (`~(backend_common_word_shift (:A) = 0)`,
  REWRITE_TAC[backend_common_word_shift_def] THEN COND_CASES_TAC THEN ARITH_TAC);;

(* HOL4 line 274 *)
let select_lower_lemma = prove
 (`!n (w:A word).
     word_bits n 0 w =
     word_ushr (word_shl w ((dimindex(:A) - n) - 1)) ((dimindex(:A) - n) - 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_USHR; BIT_WORD_SHL; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `bit i (w:A word)` THEN ASM_REWRITE_TAC[ADD_SUB] THEN ASM_ARITH_TAC);;

(* HOL4 line 282 *)
let select_eq_select_0 = prove
 (`!k n (w:A word). k <= n ==> word_bits n k w = word_bits (n - k) 0 (word_ushr w k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_USHR; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 288 *)
let is_fwd_ptr_iff = prove
 (`!w:(A)word_loc. is_fwd_ptr w <=> ?v. w = wl_Word v /\ word_and v (word 3) = word 0`,
  GEN_TAC THEN CASES_ON `w:(A)word_loc` THEN
  REWRITE_TAC[is_fwd_ptr_def; injectivity "word_loc"; distinctness "word_loc"] THEN
  MESON_TAC[]);;

(* HOL4 line 294 *)
let isWord_thm = prove
 (`!w:(A)word_loc. isWord w <=> ?v. w = wl_Word v`,
  GEN_TAC THEN CASES_ON `w:(A)word_loc` THEN
  REWRITE_TAC[isWord_def; injectivity "word_loc"; distinctness "word_loc"] THEN
  MESON_TAC[]);;

(* HOL4 line 300 *)
let lower_2w_eq = prove
 (`!w:A word. good_dimindex (:A) ==> (word_ult w (word 2) <=> w = word 0 \/ w = word 1)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_ULT; GSYM VAL_EQ; VAL_WORD; VAL_WORD_0] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* HOL4 line 307 (HOL4 binds a second EL_LENGTH_ADD_LEMMA at line 347;    *)
(* every use is after it)                                                  *)
let EL_LENGTH_ADD_LEMMA = prove
 (`!init old (x:A) st1.
     EL (LENGTH init + LENGTH old) (APPEND (APPEND (APPEND init old) [x]) st1) = x`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND; GSYM LENGTH_APPEND] THEN SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]);;

(* HOL4 line 314 *)
let LUPDATE_LENGTH_ADD_LEMMA = prove
 (`!init old (x:A) w st1.
     LUPDATE w (LENGTH init + LENGTH old) (APPEND (APPEND (APPEND init old) [x]) st1) =
     APPEND (APPEND (APPEND init old) [w]) st1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND; GSYM LENGTH_APPEND; LUPDATE_LENGTH]);;

(* HOL4 line 321 *)
let word_msb_IFF_lsr_EQ_0 = prove
 (`!h:A word. word_msb h <=> ~(word_ushr h (dimindex (:A) - 1) = word 0)`,
  GEN_TAC THEN REWRITE_TAC[word_msb_def; WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_0] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; DIMINDEX_GT_0];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[BIT_GUARD] THEN
    STRIP_TAC THEN SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[ADD_CLAUSES]]]);;

(* HOL4 line 327 *)
let map_bitmap_IMP_LENGTH = prove
 (`!x (wl:A list) stack xs ys.
      map_bitmap x wl stack = SOME (xs,ys) ==> LENGTH xs = LENGTH x`,
  MATCH_MP_TAC map_bitmap_ind THEN REWRITE_TAC[map_bitmap_def] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PAIR]);;

(* HOL4 line 337 *)
let filter_bitmap_IMP_LENGTH = prove
 (`!x (stack:A list) q r.
      filter_bitmap x stack = SOME (q,r) ==> LENGTH stack = LENGTH x + LENGTH r`,
  MATCH_MP_TAC filter_bitmap_ind THEN REWRITE_TAC[filter_bitmap_def] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; LENGTH; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 347 *)
let EL_LENGTH_ADD_LEMMA = prove
 (`!n xs (y:A) ys. LENGTH xs = n ==> EL n (APPEND xs (CONS y ys)) = y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]);;

(* HOL4 line 353 *)
let bytes_in_word_word_shift_n2w = prove
 (`!n. good_dimindex (:A) /\ (dimindex(:A) DIV 8) * n < dimword (:A)
       ==> word_ushr (word_mul bytes_in_word (word n)) (backend_common_word_shift (:A)) =
           word n:A word`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC stack_allocProof_bytes_in_word_word_shift THEN
  ASM_REWRITE_TAC[bytes_in_word_def; VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `(dimindex(:A) DIV 8) MOD dimword(:A) = dimindex(:A) DIV 8` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `dimword(:A)`] MOD_LE) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  MATCH_MP_TAC(ARITH_RULE `b * m <= b * n ==> b * n < d /\ m <= n ==> b * m < d`) THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL; MOD_LE]);;

(* HOL4 line 364 *)
let stack_allocProof_lt_dimindex_MOD_dimword = prove
 (`!n. n < dimindex (:A) ==> n MOD dimword (:A) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LT_TRANS `dimindex(:A)` THEN ASM_REWRITE_TAC[dimindex_lt_dimword]);;
let _ = cake_add_simps [stack_allocProof_lt_dimindex_MOD_dimword];;

(* ========================================================================= *)
(* HOL4 lines 372-389: the evaluation rules of HOL4 tac and tac1; here a     *)
(* symbolic evaluator for the code of the GC (STALLOCAUX_EV_TAC).           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* STALLOCAUX: symbolic evaluation of the stackLang code of the GC          *)
(* ------------------------------------------------------------------------- *)

(* the clause of stack_evaluate_def for a constructor *)

let STALLOCAUX_RW_TAC thl =
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC thl THEN CASE_REWRITE_TAC thl));;

let STALLOCAUX_ev_clause (name:string) : thm =
  find (fun th -> try let l = lhs(snd(strip_forall(concl th))) in
                      fst(dest_const(fst(strip_comb(fst(dest_pair(rand l)))))) = name
                  with Failure _ -> false)
       (CONJUNCTS stack_evaluate_def);;

let STALLOCAUX_seq_none = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state) s1.
     stack_evaluate (c1,s) = (NONE,s1)
     ==> stack_evaluate (stack_Seq c1 c2,s) = stack_evaluate (c2,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_seq_some = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state) s1 r.
     stack_evaluate (c1,s) = (SOME r,s1)
     ==> stack_evaluate (stack_Seq c1 c2,s) = (SOME r,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT]);;

let STALLOCAUX_seq_cong = prove
 (`!c1 c1' c2 (s:(A,C,FFI)stack_state) s'.
     stack_evaluate (c1,s) = stack_evaluate (c1',s')
     ==> stack_evaluate (stack_Seq c1 c2,s) = stack_evaluate (stack_Seq c1' c2,s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN
  ASM_REWRITE_TAC[]);;

let STALLOCAUX_seq_assoc = prove
 (`!a b c (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq (stack_Seq a b) c,s) =
     stack_evaluate (stack_Seq a (stack_Seq b c),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (a:(A)stack_prog,s:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let STALLOCAUX_if_lemma = prove
 (`!cmp r ri c1 c2 (s:(A,C,FFI)stack_state) x y b.
     stack_get_var r s = SOME x /\ stack_get_var_imm ri s = SOME y /\
     wl_word_cmp cmp x y = SOME b
     ==> stack_evaluate (stack_If cmp r ri c1 c2,s) =
         if b then stack_evaluate (c1,s) else stack_evaluate (c2,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_If"] THEN
  STALLOCAUX_RW_TAC[]);;

let STALLOCAUX_loop_break = prove
 (`!c (s:(A,C,FFI)stack_state) s1.
     stack_evaluate (c,s) = (SOME (stackSem_Break 0),s1)
     ==> stack_evaluate (stack_Loop c,s) = (NONE,s1)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [STALLOCAUX_ev_clause "stack_Loop"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def]);;

let STALLOCAUX_loop_cont = prove
 (`!c (s:(A,C,FFI)stack_state) s1.
     stack_evaluate (c,s) = (NONE,s1) /\ ~(stack_state_clock s1 = 0)
     ==> stack_evaluate (stack_Loop c,s) =
         stack_evaluate (stack_Loop c,stack_dec_clock s1)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [STALLOCAUX_ev_clause "stack_Loop"] THEN
  STALLOCAUX_RW_TAC[stack_cont_loop_def; stack_STOP_def]);;

let STALLOCAUX_ev_skip = prove
 (`!s:(A,C,FFI)stack_state. stack_evaluate (stack_Skip,s) = (NONE,s)`,
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_Skip"]);;

let STALLOCAUX_ev_break = prove
 (`!n (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Break n,s) = (SOME (stackSem_Break n),s)`,
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_Break"]);;

let STALLOCAUX_ev_halt = prove
 (`!v w (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) v = SOME w
     ==> stack_evaluate (stack_Halt v,s) = (SOME (stackSem_Halt w),stack_empty_env s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Halt"] THEN
  ASM_REWRITE_TAC[stack_get_var_def] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_ev_inst = prove
 (`!i (s:(A,C,FFI)stack_state) s1.
     stack_inst i s = SOME s1 ==> stack_evaluate (stack_Inst i,s) = (NONE,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Inst"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_ev_get = prove
 (`!v name x (s:(A,C,FFI)stack_state).
     stack_state_use_store s /\ FLOOKUP (stack_state_store s) name = SOME x
     ==> stack_evaluate (stack_Get v name,s) = (NONE,stack_set_var v x s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Get"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_ev_set = prove
 (`!v name w (s:(A,C,FFI)stack_state).
     stack_state_use_store s /\ FLOOKUP (stack_state_regs s) v = SOME w
     ==> stack_evaluate (stack_Set name v,s) = (NONE,stack_set_store name w s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "stack_Set"] THEN
  ASM_REWRITE_TAC[stack_get_var_def] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_ev_stackloadany = prove
 (`!r rn (w:A word) (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\ FLOOKUP (stack_state_regs s) rn = SOME (wl_Word w) /\
     stack_state_stack_space s + val (word_ushr w (backend_common_word_shift (:A))) <
       LENGTH (stack_state_stack s) /\
     word_shl (word_ushr w (backend_common_word_shift (:A)))
       (backend_common_word_shift (:A)) = w
     ==> stack_evaluate (StackLoadAny r rn,s) =
         (NONE,stack_set_var r
                 (EL (stack_state_stack_space s +
                      val (word_ushr w (backend_common_word_shift (:A))))
                     (stack_state_stack s)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "StackLoadAny"] THEN
  ASM_REWRITE_TAC[stack_get_var_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[]);;

let STALLOCAUX_ev_stackstoreany = prove
 (`!r rn v (w:A word) (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\ FLOOKUP (stack_state_regs s) r = SOME v /\
     FLOOKUP (stack_state_regs s) rn = SOME (wl_Word w) /\
     stack_state_stack_space s + val (word_ushr w (backend_common_word_shift (:A))) <
       LENGTH (stack_state_stack s) /\
     word_shl (word_ushr w (backend_common_word_shift (:A)))
       (backend_common_word_shift (:A)) = w
     ==> stack_evaluate (StackStoreAny r rn,s) =
         (NONE,stack_state_stack_fupd
                 (K (LUPDATE v (stack_state_stack_space s +
                                val (word_ushr w (backend_common_word_shift (:A))))
                       (stack_state_stack s))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "StackStoreAny"] THEN
  ASM_REWRITE_TAC[stack_get_var_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[]);;

let STALLOCAUX_ev_bitmapload = prove
 (`!r v (w:A word) (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\ ~(r = v) /\
     FLOOKUP (stack_state_regs s) v = SOME (wl_Word w) /\
     val w < LENGTH (stack_state_bitmaps s)
     ==> stack_evaluate (BitmapLoad r v,s) =
         (NONE,stack_set_var r (wl_Word (EL (val w) (stack_state_bitmaps s))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STALLOCAUX_ev_clause "BitmapLoad"] THEN
  STALLOCAUX_RW_TAC[stack_get_var_def; GSYM NOT_LT]);;

(* the instructions *)

let STALLOCAUX_inst_move = prove
 (`!r1 r2 v (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME v
     ==> stack_inst (asm_Arith (Binop asm_Or r1 r2 (Reg r2))) s =
         SOME (stack_set_var r1 v s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_inst_binop_reg = prove
 (`!b r1 r2 r3 (x:A word) y z (s:(A,C,FFI)stack_state).
     ~(b = asm_Or /\ r3 = r2) /\
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x) /\
     FLOOKUP (stack_state_regs s) r3 = SOME (wl_Word y) /\
     word_op b [x; y] = SOME z
     ==> stack_inst (asm_Arith (Binop b r1 r2 (Reg r3))) s =
         SOME (stack_set_var r1 (wl_Word z) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[injectivity "reg_imm"] THEN
  ASM_REWRITE_TAC[stack_assign_def; stack_word_exp_def; LET_DEF; LET_END_DEF; MAP] THEN
  CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let STALLOCAUX_inst_binop_imm = prove
 (`!b r1 r2 (w:A word) x z (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x) /\
     word_op b [x; w] = SOME z
     ==> stack_inst (asm_Arith (Binop b r1 r2 (Imm w))) s =
         SOME (stack_set_var r1 (wl_Word z) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[distinctness "reg_imm"] THEN
  ASM_REWRITE_TAC[stack_assign_def; stack_word_exp_def; LET_DEF; LET_END_DEF; MAP] THEN
  CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let STALLOCAUX_inst_shift = prove
 (CASE_TERM `!sh r1 r2 n (x:A word) (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x) /\ n < dimindex(:A)
     ==> stack_inst (asm_Arith (asm_Shift sh r1 r2 (Imm (word n)))) s =
         SOME (stack_set_var r1
                 (wl_Word (match sh with Lsl -> word_shl x n
                                       | Lsr -> word_ushr x n
                                       | Asr -> word_ishr x n
                                       | Ror -> word_ror x n)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word n:A word) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS `dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL]; ALL_TAC] THEN
  REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[stack_assign_def; stack_word_exp_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[word_sh_def; GE; GSYM NOT_LT] THEN
  CASES_ON `sh:shift` THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_inst_const = prove
 (`!r (w:A word) (s:(A,C,FFI)stack_state).
     stack_inst (asm_Const r w) s = SOME (stack_set_var r (wl_Word w) s)`,
  REWRITE_TAC[stack_inst_def; stack_assign_def; stack_word_exp_def] THEN
  CASE_REWRITE_TAC[]);;

let STALLOCAUX_inst_load = prove
 (`!r a (w:A word) x (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) a = SOME (wl_Word x) /\
     word_add x w IN stack_state_mdomain s
     ==> stack_inst (Mem asm_Load r (Addr a w)) s =
         SOME (stack_set_var r (stack_state_memory s (word_add x w)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[stack_word_exp_def; LET_DEF; LET_END_DEF; MAP] THEN
  CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF; word_op_def; ITLIST] THEN
  STALLOCAUX_RW_TAC[stack_mem_load_def; WORD_ADD_0]);;

let STALLOCAUX_inst_store = prove
 (`!r a (w:A word) x v (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) a = SOME (wl_Word x) /\
     FLOOKUP (stack_state_regs s) r = SOME v /\
     word_add x w IN stack_state_mdomain s
     ==> stack_inst (Mem asm_Store r (Addr a w)) s =
         SOME (stack_state_memory_fupd
                 (K ((word_add x w =+ v) (stack_state_memory s))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[stack_word_exp_def; stack_get_var_def; LET_DEF; LET_END_DEF; MAP] THEN
  CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF; word_op_def; ITLIST] THEN
  REWRITE_TAC[WORD_ADD_0] THEN STALLOCAUX_RW_TAC[stack_mem_store_def]);;

(* ------------------------------------------------------------------------- *)
(* the evaluator (OCaml): stallocaux_ev facts tm proves tm = rhs for a term     *)
(* tm = stack_evaluate (p,s) by running the code p as far as it can: the rhs *)
(* is a pair (res,s') or, when it stops (an unknown sub-program, a guard     *)
(* that the facts do not decide, a loop iteration), stack_evaluate (p',s').  *)
(* ------------------------------------------------------------------------- *)

let STALLOCAUX_record_rws =
  let ri = record_info "stack_state" in
  [ri.ri_accessors; ri.ri_accfupds; ri.ri_fupdfupds; ri.ri_fupdcanon];;

let STALLOCAUX_base_rws =
  STALLOCAUX_record_rws @
  [K_THM; K_o_THM; KLAM_o_THM; I_THM;
   stack_set_var_def; stack_set_store_def; stack_dec_clock_def;
   stack_get_var_def; stack_get_var_imm_def; FLOOKUP_UPDATE; ARITH_EQ;
   WORD_ADD_0; WORD_MUL_0; ADD_CLAUSES; SUC_SUB1; ADD_SUB; FST; SND; PAIR_EQ;
   wl_word_cmp_def; word_op_def; ITLIST];;

let STALLOCAUX_base_net =
  ref (itlist (net_of_thm true)
         (itlist (mk_rewrites false) STALLOCAUX_base_rws []) (!cake_case_net));;

(* more rewrites for the evaluator's normaliser *)
let stallocaux_add_rws (thl:thm list) =
  STALLOCAUX_base_net :=
    itlist (net_of_thm true) (itlist (mk_rewrites false) thl []) (!STALLOCAUX_base_net);;

let stallocaux_norm (facts:thm list) : conv =
  fun tm -> GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (!STALLOCAUX_base_net) facts tm;;

(* arithmetic facts: comparisons of numbers *)
let stallocaux_is_arith tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let stallocaux_debug = ref false;;
let stallocaux_say s tm =
  if !stallocaux_debug then (print_string s; print_term tm; print_newline()) else ();;

(* prove a fact: normalise it with the facts, else arithmetic with the      *)
(* arithmetic facts                                                          *)
let stallocaux_prove_fact (facts:thm list) (tm:term) : thm =
  let th = stallocaux_norm facts tm in
  let t = rhs(concl th) in
  if t = `T` then EQT_ELIM th else
  let ths = filter (fun th -> stallocaux_is_arith (concl th)) facts in
  let th2 =
    try let afs = DIMINDEX_GE_1 :: ths in
        let a = list_mk_conj (map concl afs) in
        let th3 = ARITH_RULE (mk_imp(a,t)) in
        MP th3 (end_itlist CONJ afs)
    with Failure _ ->
      (stallocaux_say "stallocaux_prove_fact: cannot prove " t;
       failwith "stallocaux_prove_fact") in
  EQ_MP (SYM th) th2;;

let stallocaux_is_genvar v =
  is_var v && let n = fst(dest_var v) in String.length n > 0 && n.[0] = '_';;

(* instantiate a conditional lemma |- !xs. a1 /\ .. /\ an ==> l = r at the   *)
(* term tm (matching l), computing the outputs of the antecedents in order:  *)
(* an equation whose right side has uninstantiated variables is computed by  *)
(* normalising its left side; any other antecedent is proved as a fact      *)
let stallocaux_apply_lemma (facts:thm list) (lemma:thm) (tm:term) : thm =
  let vs,_ = strip_forall (concl lemma) in
  let th0 = PURE_REWRITE_RULE[IMP_CONJ] (SPECL (map (genvar o type_of) vs) lemma) in
  let eqn = snd(splitlist dest_imp (concl th0)) in
  let i = term_match [] (lhs eqn) tm in
  let th1 = INSTANTIATE i th0 in
  let rec go th =
    if not (is_imp (concl th)) then th else
    let c,_ = dest_imp (concl th) in
    if is_eq c && exists stallocaux_is_genvar (frees (rhs c)) then
      let thl = stallocaux_norm facts (lhs c) in
      let i2 = term_match [] (rhs c) (rhs (concl thl)) in
      go (MP (INSTANTIATE i2 th) thl)
    else go (MP th (stallocaux_prove_fact facts c)) in
  let th2 = go th1 in
  if exists stallocaux_is_genvar (frees (concl th2))
  then failwith "stallocaux_apply_lemma: outputs left" else th2;;

(* the leaf evaluations (instructions, store access, stack access) *)

let STALLOCAUX_ev_inst_tac ilemma =
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC STALLOCAUX_ev_inst THEN
  MATCH_MP_TAC ilemma THEN ASM_MESON_TAC[];;

let STALLOCAUX_ev_move = prove
 (`!r1 r2 v (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME v
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop asm_Or r1 r2 (Reg r2))),s) =
         (NONE,stack_set_var r1 v s)`,
  STALLOCAUX_ev_inst_tac STALLOCAUX_inst_move);;

let STALLOCAUX_ev_binop_reg = prove
 (`!b r1 r2 r3 (x:A word) y z (s:(A,C,FFI)stack_state).
     ~(b = asm_Or /\ r3 = r2) /\
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x) /\
     FLOOKUP (stack_state_regs s) r3 = SOME (wl_Word y) /\
     word_op b [x; y] = SOME z
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop b r1 r2 (Reg r3))),s) =
         (NONE,stack_set_var r1 (wl_Word z) s)`,
  STALLOCAUX_ev_inst_tac STALLOCAUX_inst_binop_reg);;

let STALLOCAUX_ev_binop_imm = prove
 (`!b r1 r2 (w:A word) x z (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x) /\
     word_op b [x; w] = SOME z
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop b r1 r2 (Imm w))),s) =
         (NONE,stack_set_var r1 (wl_Word z) s)`,
  STALLOCAUX_ev_inst_tac STALLOCAUX_inst_binop_imm);;

let STALLOCAUX_ev_shift = prove
 (CASE_TERM `!sh r1 r2 n (x:A word) (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x) /\ n < dimindex(:A)
     ==> stack_evaluate (stack_Inst (asm_Arith (asm_Shift sh r1 r2 (Imm (word n)))),s) =
         (NONE,stack_set_var r1
                 (wl_Word (match sh with Lsl -> word_shl x n
                                       | Lsr -> word_ushr x n
                                       | Asr -> word_ishr x n
                                       | Ror -> word_ror x n)) s)`,
  STALLOCAUX_ev_inst_tac STALLOCAUX_inst_shift);;

let STALLOCAUX_ev_const = prove
 (`!r (w:A word) (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Inst (asm_Const r w),s) = (NONE,stack_set_var r (wl_Word w) s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC STALLOCAUX_ev_inst THEN
  REWRITE_TAC[STALLOCAUX_inst_const]);;

let STALLOCAUX_ev_load = prove
 (`!r a (w:A word) x (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) a = SOME (wl_Word x) /\
     word_add x w IN stack_state_mdomain s
     ==> stack_evaluate (stack_Inst (Mem asm_Load r (Addr a w)),s) =
         (NONE,stack_set_var r (stack_state_memory s (word_add x w)) s)`,
  STALLOCAUX_ev_inst_tac STALLOCAUX_inst_load);;

let STALLOCAUX_ev_store = prove
 (`!r a (w:A word) x v (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) a = SOME (wl_Word x) /\
     FLOOKUP (stack_state_regs s) r = SOME v /\
     word_add x w IN stack_state_mdomain s
     ==> stack_evaluate (stack_Inst (Mem asm_Store r (Addr a w)),s) =
         (NONE,stack_state_memory_fupd
                 (K ((word_add x w =+ v) (stack_state_memory s))) s)`,
  STALLOCAUX_ev_inst_tac STALLOCAUX_inst_store);;

let STALLOCAUX_leaf_lemmas = ref
  [STALLOCAUX_ev_skip; STALLOCAUX_ev_break; STALLOCAUX_ev_halt;
   STALLOCAUX_ev_get; STALLOCAUX_ev_set;
   STALLOCAUX_ev_move; STALLOCAUX_ev_binop_reg; STALLOCAUX_ev_binop_imm;
   STALLOCAUX_ev_shift; STALLOCAUX_ev_const; STALLOCAUX_ev_load; STALLOCAUX_ev_store;
   STALLOCAUX_ev_stackloadany; STALLOCAUX_ev_stackstoreany; STALLOCAUX_ev_bitmapload];;

(* ------------------------------------------------------------------------- *)
(* the evaluator                                                             *)
(* ------------------------------------------------------------------------- *)

let stallocaux_known = ref ([]:thm list);;

let stallocaux_dest_ev tm =
  let h,a = dest_comb tm in
  if is_const h && fst(dest_const h) = "stack_evaluate" then dest_pair a
  else failwith "stallocaux_dest_ev";;

let stallocaux_is_ev tm = can stallocaux_dest_ev tm;;

(* normalise the state of a result (res,s) or of a residual evaluation *)
let stallocaux_norm_rhs (th:thm) : thm =
  let r = rhs(concl th) in
  if is_pair r then CONV_RULE (RAND_CONV (RAND_CONV (stallocaux_norm []))) th
  else if stallocaux_is_ev r then
    CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (stallocaux_norm [])))) th
  else th;;

let stallocaux_is_none tm = is_const tm && fst(dest_const tm) = "NONE";;
let stallocaux_is_some tm = is_comb tm && is_const (rator tm) &&
                         fst(dest_const(rator tm)) = "SOME";;

let rec stallocaux_ev (facts:thm list) (tm:term) : thm =
  try find (fun th -> lhs(concl th) = tm) (!stallocaux_known) with Failure _ ->
  let p,s = stallocaux_dest_ev tm in
  let evc = rator tm in
  let h,args = strip_comb p in
  let name = try fst(dest_const h) with Failure _ -> "" in
  match name with
    "stack_list_Seq" ->
      let th = REWRITE_CONV[stack_list_Seq_def] tm in
      (try TRANS th (stallocaux_ev facts (rhs(concl th))) with Failure _ -> th)
  | "stack_Seq" -> stallocaux_ev_seq facts evc (hd args) (el 1 args) s
  | "stack_If" -> stallocaux_ev_if facts tm
  | "stack_Loop" -> stallocaux_ev_loop facts evc (hd args) s
  | _ ->
      let th = tryfind (fun lem -> stallocaux_apply_lemma facts lem tm)
                       (!STALLOCAUX_leaf_lemmas) in
      stallocaux_norm_rhs th

and stallocaux_ev_seq facts evc c1 c2 s =
  let th1 = stallocaux_ev facts (mk_comb(evc,mk_pair(c1,s))) in
  let r1 = rhs(concl th1) in
  if is_pair r1 then
    let res,s1 = dest_pair r1 in
    if stallocaux_is_none res then
      let th = MATCH_MP (ISPECL [c1;c2;s;s1] STALLOCAUX_seq_none) th1 in
      (try TRANS th (stallocaux_ev facts (rhs(concl th))) with Failure _ -> th)
    else if stallocaux_is_some res then
      MATCH_MP (ISPECL [c1;c2;s;s1] STALLOCAUX_seq_some) th1
    else failwith "stallocaux_ev_seq: result"
  else
    let c1',s1 = stallocaux_dest_ev r1 in
    let th = MATCH_MP (ISPECL [c1;c1';c2;s;s1] STALLOCAUX_seq_cong) th1 in
    CONV_RULE (RAND_CONV (REPEATC (REWR_CONV STALLOCAUX_seq_assoc))) th

and stallocaux_ev_if facts tm =
  let th = stallocaux_apply_lemma facts STALLOCAUX_if_lemma tm in
  let b,(e1,e2) = dest_cond (rhs(concl th)) in
  let thb = stallocaux_norm facts b in
  let b' = rhs(concl thb) in
  let thd =
    if b' = `T` || b' = `F` then thb else
    try EQT_INTRO (stallocaux_prove_fact facts b) with Failure _ ->
    try EQF_INTRO (stallocaux_prove_fact facts (mk_neg b)) with Failure _ ->
      (stallocaux_say "stallocaux_ev_if: undecided guard " b';
       failwith "stallocaux_ev_if: undecided") in
  let th2 = CONV_RULE (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (K thd))) THENC
                                  GEN_REWRITE_CONV I [COND_CLAUSES])) th in
  (try TRANS th2 (stallocaux_ev facts (rhs(concl th2))) with Failure _ -> th2)

and stallocaux_ev_loop facts evc c s =
  let th1 = stallocaux_ev facts (mk_comb(evc,mk_pair(c,s))) in
  let r1 = rhs(concl th1) in
  if not (is_pair r1) then failwith "stallocaux_ev_loop: body" else
  let res,s1 = dest_pair r1 in
  if stallocaux_is_none res then
    let clk = stallocaux_prove_fact facts
                (mk_neg(mk_eq(mk_icomb(`stack_state_clock:(A,C,FFI)stack_state->num`,s1),
                              `0`))) in
    stallocaux_norm_rhs (MATCH_MP (ISPECL [c;s;s1] STALLOCAUX_loop_cont) (CONJ th1 clk))
  else MATCH_MP (ISPECL [c;s;s1] STALLOCAUX_loop_break) th1;;

(* the conversion and the tactic: every evaluation in the goal, with the    *)
(* assumptions as facts                                                     *)
let STALLOCAUX_EV_CONV (facts:thm list) : conv =
  fun tm -> if stallocaux_is_ev tm then stallocaux_ev facts tm else failwith "STALLOCAUX_EV_CONV";;

(* the facts of the assumptions: normalised, and k IN FDOM f for each fact *)
(* FLOOKUP f k = SOME v                                                     *)
let stallocaux_facts (asl:(string*thm) list) : thm list =
  let fs = map (fun (_,th) -> CONV_RULE (stallocaux_norm []) th) asl in
  fs @ mapfilter (MATCH_MP FMAPAUX_FLOOKUP_SOME_FDOM) fs;;

let STALLOCAUX_EV_TAC : tactic = fun (asl,w as g) ->
  let facts = stallocaux_facts asl in
  CONV_TAC (ONCE_DEPTH_CONV (STALLOCAUX_EV_CONV facts)) g;;

(* ------------------------------------------------------------------------- *)
(* comparing the final states                                                *)
(* ------------------------------------------------------------------------- *)

let stallocaux_dest_fupd tm =
  let h,args = strip_comb tm in
  match args with
    [f;kv] when is_const h && fst(dest_const h) = "FUPDATE" -> f,dest_pair kv
  | _ -> failwith "stallocaux_dest_fupd";;

let stallocaux_is_fupd tm = can stallocaux_dest_fupd tm;;

(* the base and the updates (oldest first) of a chain f |+ (k1,v1) |+ ... *)
let rec stallocaux_fmap_parts tm =
  if stallocaux_is_fupd tm then
    let f,kv = stallocaux_dest_fupd tm in
    let b,l = stallocaux_fmap_parts f in b,l @ [kv]
  else tm,[];;

(* an equation of finite maps with explicit update chains: extensionality,  *)
(* a case split on the keys of the updates, and rewriting with the facts    *)
let STALLOCAUX_FMAP_EQ_TAC (facts:thm list) : tactic = fun (asl,w as g) ->
  let l,r = dest_eq w in
  let _,u1 = stallocaux_fmap_parts l and _,u2 = stallocaux_fmap_parts r in
  let keys = setify (map fst (u1 @ u2)) in
  let kty = fst(dest_fun_ty (type_of (mk_icomb(`FLOOKUP:(A,B)fmap->A->B option`,l))))
  in
  let k = variant (freesl (w :: map (concl o snd) asl)) (mk_var("k",kty)) in
  let rws = facts @ [FLOOKUP_UPDATE; FAPPLY_FUPDATE_THM] in
  let branch key =
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC rws THEN CONV_TAC (stallocaux_norm []) THEN
    REWRITE_TAC rws THEN TRY (REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC facts) THEN
    REWRITE_TAC[option_INJ; injectivity "word_loc"] in
  let rec split keys =
    match keys with
      [] -> ASM_REWRITE_TAC[FLOOKUP_UPDATE]
    | key::ks -> ASM_CASES_TAC (mk_eq(key,k)) THENL [branch key; split ks] in
  (REWRITE_TAC[fmap_eq_flookup] THEN X_GEN_TAC k THEN split keys) g;;

let () = stallocaux_add_rws [APPEND_NIL; GSYM APPEND_ASSOC; APPEND];;

(* witnesses for the existential variables of the goal ?vs. (r,S1) = (r,S2) *)
(* (or S1 = S2): a variable at key k of the registers (or the store) of S2 *)
(* gets the value of the last update of k in S1, else the value of a fact  *)
(* FLOOKUP base k = SOME x, else base ' k                                  *)
let STALLOCAUX_WITNESS_TAC : tactic = fun (asl,w as g) ->
  let vs,bod = strip_exists w in
  if vs = [] then ALL_TAC g else
  let facts = map (fun (_,th) -> concl(CONV_RULE (stallocaux_norm []) th)) asl in
  let l,r = dest_eq bod in
  let s1 = if is_pair l then snd(dest_pair l) else l
  and s2 = if is_pair r then snd(dest_pair r) else r in
  let comp acc t = rhs(concl(stallocaux_norm [FUPDATE_LIST_THM] (mk_icomb(acc,t)))) in
  let maps = map (fun acc -> comp acc s1,comp acc s2)
    [`stack_state_regs:(A,C,FFI)stack_state->(num,(A)word_loc)fmap`;
     `stack_state_store:(A,C,FFI)stack_state->(store_name,(A)word_loc)fmap`] in
  let from_fact b k =
    tryfind (fun f ->
      let lf,rf = dest_eq f in
      let h,args = strip_comb lf in
      if fst(dest_const h) = "FLOOKUP" && args = [b;k] then rand rf else failwith "") facts in
  let wit v =
    tryfind (fun (m1,m2) ->
        let b1,u1 = stallocaux_fmap_parts m1 and _,u2 = stallocaux_fmap_parts m2 in
        let k = fst(find (fun (_,x) -> x = v) u2) in
        (try assoc k (rev u1) with Failure _ ->
         try from_fact b1 k with Failure _ ->
           mk_icomb(mk_icomb(`FAPPLY:(A,B)fmap->A->B`,b1),k))) maps in
  MAP_EVERY (fun v -> EXISTS_TAC (try wit v with Failure _ ->
                                   failwith "STALLOCAUX_WITNESS_TAC")) vs g;;

(* the goal ?vs. (r,S1) = (r,S2): witnesses, component equality; the       *)
(* register and store maps by STALLOCAUX_FMAP_EQ_TAC; other components are *)
(* normalised with the assumptions and left as subgoals if not closed       *)
let STALLOCAUX_STATE_EQ_TAC : tactic = fun (asl,w as g) ->
  let facts = stallocaux_facts asl in
  (STALLOCAUX_WITNESS_TAC THEN
   REWRITE_TAC[PAIR_EQ; stack_state_component_equality] THEN
   CONV_TAC (stallocaux_norm [FUPDATE_LIST_THM]) THEN
   REPEAT CONJ_TAC THEN
   TRY (MATCH_ACCEPT_TAC EQ_REFL) THEN
   TRY (fun (asl,w as g) ->
          if is_eq w && (stallocaux_is_fupd (lhs w) || stallocaux_is_fupd (rhs w))
          then STALLOCAUX_FMAP_EQ_TAC facts g
          else (CONV_TAC (stallocaux_norm facts) THEN NO_TAC) g)) g;;

(* ------------------------------------------------------------------------- *)
(* using sub-results: the residual of an evaluation in the goal, its state   *)
(* without the clock update, and rewriting with a normalised evaluation      *)
(* ------------------------------------------------------------------------- *)

let () = stallocaux_add_rws [FDOM_FUPDATE; IN_INSERT];;

(* the first evaluation stack_evaluate (p,s) in the goal *)
let stallocaux_find_ev (w:term) =
  find_term stallocaux_is_ev w;;

(* a state without its clock update: stack_state_clock_fupd f s is s *)
let rec stallocaux_strip_clock (tm:term) =
  try let f,args = strip_comb tm in
      match args with
        [g;s] when is_const f && fst(dest_const f) = "stack_state_clock_fupd" -> s
      | [g;s] when is_const f &&
                   (let n = fst(dest_const f) in
                    String.length n > 17 && String.sub n 0 12 = "stack_state_" &&
                    String.sub n (String.length n - 5) 5 = "_fupd") ->
          mk_comb(mk_comb(f,g),stallocaux_strip_clock s)
      | _ -> tm
  with Failure _ -> tm;;

(* the state of the first evaluation of the goal, without its clock *)
let stallocaux_goal_state (w:term) =
  stallocaux_strip_clock (snd(stallocaux_dest_ev (stallocaux_find_ev w)));;

(* the antecedents of a sub-result: normalise with the assumptions, split,  *)
(* arithmetic                                                                *)
(* a goal that is an assumption up to normalisation with the other facts *)
let STALLOCAUX_BY_ASSUM_TAC : tactic = fun (asl,w as g) ->
  let facts = stallocaux_facts asl in
  let thw = stallocaux_norm facts w in
  let gn = rhs(concl thw) in
  let th = tryfind (fun f ->
      let others = filter (fun f' -> not (concl f' = concl f)) facts in
      let th' = CONV_RULE (stallocaux_norm others) f in
      if aconv (concl th') gn then EQ_MP (SYM thw) th' else failwith "") facts in
  ACCEPT_TAC th g;;

let STALLOCAUX_ANTS_TAC : tactic = fun (asl,w as g) ->
  let facts = stallocaux_facts asl in
  (CONV_TAC (stallocaux_norm facts) THEN REPEAT CONJ_TAC THEN
   TRY (MATCH_ACCEPT_TAC TRUTH) THEN
   TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
   TRY (ASM_ARITH_TAC THEN NO_TAC) THEN
   TRY STALLOCAUX_BY_ASSUM_TAC) g;;

(* rewrite the goal with an evaluation theorem |- stack_evaluate (p,s) = r *)
(* after normalising its state (and the programs with thl)                 *)
let STALLOCAUX_USE_EV_TAC (thl:thm list) (th:thm) : tactic =
  let th1 = CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (stallocaux_norm []) THENC
                                             LAND_CONV (REWRITE_CONV thl)))) th in
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th1];;

(* ------------------------------------------------------------------------- *)
(* clocks: sums are kept left-associated; a sub-result is given more clock   *)
(* with stack_evaluate_add_clock; the clock witness of a goal is chosen     *)
(* step by step                                                              *)
(* ------------------------------------------------------------------------- *)

let () = stallocaux_add_rws [ADD_ASSOC];;

(* |- stack_evaluate (p,s) = (NONE,s1) to the same with extra clock (states *)
(* normalised)                                                              *)
let STALLOCAUX_ADD_CLOCK (extra:term) (th:thm) : thm =
  let r = fst(dest_pair(rhs(concl th))) in
  let nt = EQF_ELIM (stallocaux_norm [] (mk_eq(r,`SOME (stack_TimeOut:(A)stack_result)`)
                                         |> inst (type_match `:((A)stack_result)option`
                                                    (type_of r) []))) in
  let th1 = MATCH_MP (INST [extra,`extra:num`] stack_evaluate_add_clock) (CONJ th nt) in
  CONV_RULE (BINOP_CONV (RAND_CONV (RAND_CONV (stallocaux_norm [])))) th1;;

(* the goal ?x. P x (x the clock): continue with ?v. P (k + v) *)
let STALLOCAUX_CLOCK_TAC (k:term) (v:term) : tactic = fun (asl,w as g) ->
  let x,body = dest_exists w in
  let th = ISPECL [mk_abs(x,body); k] BASICAUX_EX_ADD in
  (MATCH_MP_TAC th THEN CONV_TAC (GEN_ALPHA_CONV v) THEN
   CONV_TAC (BINDER_CONV BETA_CONV)) g;;

(* the evaluator with known evaluations (sub-results, normalised) *)
let STALLOCAUX_EV_KNOWN_TAC (thl:thm list) : tactic = fun g ->
  let old = !stallocaux_known in
  stallocaux_known := map (CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (stallocaux_norm []))))) thl;
  let r = try STALLOCAUX_EV_TAC g with e -> (stallocaux_known := old; raise e) in
  stallocaux_known := old; r;;

let STALLOCAUX_word_suc_facts = prove
 (`!n. SUC n < dimword(:A) ==>
       ~(word (SUC n):A word = word 0) /\ word_sub (word (SUC n)) (word 1):A word = word n`,
  GEN_TAC THEN REWRITE_TAC[dimword_def] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD] THEN ASM_SIMP_TAC[MOD_LT] THEN
    ARITH_TAC;
    REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 390 (the local memcpy_code_thm, for a counter word n) *)
let STALLOCAUX_memcpy_code_n = prove
 (`!n a b m dm b1 m1 (s:(A,C,FFI)stack_state).
      memcpy (word n:A word) a b m dm = (b1:A word,m1,T) /\
      n < dimword (:A) /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\
      stack_get_var 0 s = SOME (wl_Word (word n)) /\
      1 IN FDOM (stack_state_regs s) /\
      stack_get_var 2 s = SOME (wl_Word a) /\
      stack_get_var 3 s = SOME (wl_Word b) ==>
      ?r1.
        stack_evaluate (memcpy_code,
          stack_state_clock_fupd (K (stack_state_clock s + n)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,wl_Word (word 0)); (1,r1);
                          (2,wl_Word (word_add a (word_mul (word n) bytes_in_word)));
                          (3,wl_Word b1)])) s))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[memcpy_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    REWRITE_TAC[memcpy_code_def] THEN STALLOCAUX_EV_TAC THEN STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp(snd(strip_forall(concl th)))
                          then LABEL_TAC "ih" th else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STALLOCAUX_word_suc_facts) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "memcpy" with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[memcpy_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  REWRITE_TAC[memcpy_code_def] THEN STALLOCAUX_EV_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (USE_THEN "ih" (MP_TAC o SPECL
       [`word_add a bytes_in_word:A word`; `word_add b bytes_in_word:A word`;
        `(b =+ (stack_state_memory (s:(A,C,FFI)stack_state) a)) (stack_state_memory s)`;
        `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `b1:A word`;
        `m1:A word->(A)word_loc`; s0])) g) THEN
  ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1':(A)word_loc`
    (fun th -> STALLOCAUX_USE_EV_TAC [memcpy_code_def] th)) THEN
  STALLOCAUX_STATE_EQ_TAC THEN
  REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 444 *)
let memcpy_code_thm = prove
 (`!w a b m dm b1 m1 (s:(A,C,FFI)stack_state).
      memcpy (w:A word) a b m dm = (b1:A word,m1,T) /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\
      stack_get_var 0 s = SOME (wl_Word w) /\
      1 IN FDOM (stack_state_regs s) /\
      stack_get_var 2 s = SOME (wl_Word a) /\
      stack_get_var 3 s = SOME (wl_Word b) ==>
      ?r1.
        stack_evaluate (memcpy_code,
          stack_state_clock_fupd (K (stack_state_clock s + val w)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,wl_Word (word 0)); (1,r1);
                          (2,wl_Word (word_add a (word_mul w bytes_in_word)));
                          (3,wl_Word b1)])) s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`val (w:A word)`; `a:A word`; `b:A word`; `m:A word->(A)word_loc`;
                `dm:A word->bool`; `b1:A word`; `m1:A word->(A)word_loc`;
                `s:(A,C,FFI)stack_state`] STALLOCAUX_memcpy_code_n) THEN
  ASM_REWRITE_TAC[WORD_VAL; dimword_def; VAL_BOUND]);;
(* ------------------------------------------------------------------------- *)
(* splitting the tuple result of a function: STALLOCAUX_SPLIT_FN_TAC c names *)
(* finds the first application of the constant c in the goal (with no bound *)
(* variables), assumes it equal to a tuple of fresh variables (the names)    *)
(* and rewrites the goal with that                                           *)
(* ------------------------------------------------------------------------- *)

let STALLOCAUX_SPLIT_TAC (tm:term) (vs:term list) : tactic = fun (asl,w as g) ->
  let tup = end_itlist (curry mk_pair) vs in
  let ex = list_mk_exists(vs, mk_eq(tm,tup)) in
  let rec projs t n = if n = 1 then [t] else
      mk_icomb(`FST:A#B->A`,t) :: projs (mk_icomb(`SND:A#B->B`,t)) (n - 1) in
  let ps = projs tm (length vs) in
  (SUBGOAL_THEN ex MP_TAC THENL
   [MAP_EVERY EXISTS_TAC ps THEN REWRITE_TAC[PAIR];
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (fun th -> ASSUME_TAC th THEN
                      REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]))]) g;;

(* the first application of the constant c in the goal whose free variables *)
(* are free in the goal (not bound inside it)                               *)
let stallocaux_find_app (c:string) (asl,w) =
  let fv = freesl (w :: map (concl o snd) asl) in
  find_term (fun t -> is_comb t &&
                      (let h,_ = strip_comb t in is_const h && fst(dest_const h) = c) &&
                      subset (frees t) fv &&
                      is_type (type_of t) && fst(dest_type(type_of t)) = "prod") w;;

let STALLOCAUX_SPLIT_FN_TAC (c:string) (names:string list) : tactic = fun (asl,w as g) ->
  let t = stallocaux_find_app c (asl,w) in
  let rec tys ty n = if n = 1 then [ty] else
      let a,b = (match dest_type ty with (_,[a;b]) -> a,b | _ -> failwith "tys") in
      a :: tys b (n - 1) in
  let vs0 = map2 (fun n ty -> mk_var(n,ty)) names (tys (type_of t) (length names)) in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let vs = rev(snd(itlist (fun v (av,acc) -> let v' = variant av v in (v'::av, v'::acc))
                          (rev vs0) (avoid,[]))) in
  STALLOCAUX_SPLIT_TAC t vs g;;

(* ========================================================================= *)
(* gc_kind = Simple (HOL4 lines 467-1716)                                    *)
(* ========================================================================= *)

(* HOL4 line 481 (HOL4 word_gc_fun_lemma, line 469, is unfolded here)     *)
let word_gc_fun_thm = prove
 (CASE_TERM
  `!conf roots m dm (s:(store_name,(A)word_loc)fmap).
   data_to_word_config_gc_kind conf = data_to_word_Simple ==>
   word_gc_fun conf (roots,m,dm,s) =
      let (w1,i1:A word,pa1,m1,c1) =
            word_gc_move conf
              (FAPPLY s Globals,word 0,theWord (FAPPLY s OtherHeap),
               theWord (FAPPLY s CurrHeap),m,dm) in
      let (ws2,i2,pa2,m2,c2) =
            word_gc_move_roots conf
              (roots,i1,pa1,theWord (FAPPLY s CurrHeap),m1,dm) in
      let (i1,pa1,m1,c2) =
            word_gc_move_loop (dimword (:A)) conf
              (theWord (FAPPLY s OtherHeap),i2,pa2,
               theWord (FAPPLY s CurrHeap),m2,dm,(c1 /\ c2)) in
      let s1 =
            s |++
            [(CurrHeap,wl_Word (theWord (FAPPLY s OtherHeap)));
             (OtherHeap,wl_Word (theWord (FAPPLY s CurrHeap)));
             (NextFree,wl_Word pa1);
             (TriggerGC,
              wl_Word (word_add (theWord (FAPPLY s OtherHeap)) (theWord (FAPPLY s HeapLength))));
             (EndOfHeap,
              wl_Word (word_add (theWord (FAPPLY s OtherHeap)) (theWord (FAPPLY s HeapLength))));
             (Globals,w1);
             (GlobReal,glob_real conf (theWord (FAPPLY s OtherHeap)) w1)]
      in
        if word_gc_fun_assum conf s /\ c2 then SOME (ws2,m1,s1) else NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_gc_fun_def; word_full_gc_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF; word_gc_move_roots_def] THEN
  REPEAT (PAIRARG_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN REWRITE_TAC[HD; TL]);;

(* HOL4 line 526 *)
let word_gc_move_roots_bitmaps_def = cake_def
  `word_gc_move_roots_bitmaps (conf:data_to_word_config)
     (stack:((A)word_loc)list,bitmaps:(A word)list,i1:A word,pa1:A word,curr:A word,
      m:A word->(A)word_loc,dm:A word->bool) =
     match stack_enc_stack bitmaps stack with
       NONE -> (ARB,ARB,ARB,ARB,F)
     | SOME wl_list ->
         let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf (wl_list,i1,pa1,curr,m,dm) in
         (match stack_dec_stack bitmaps wl stack with
            NONE -> (ARB,ARB,ARB,ARB,F)
          | SOME stack -> (stack,i2,pa2,m2,c2))`;;

(* HOL4 line 538 *)
let word_gc_move_loop_F = prove
 (`!k conf pb i pa old m dm i1 pa1 m1 c1.
      word_gc_move_loop k conf (pb:A word,i,pa,old,m,dm,F) = (i1,pa1,m1,c1) ==> ~c1`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[word_gc_move_loop_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN TRY(MESON_TAC[]) THEN
  REPEAT PAIRARG_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 548 *)
let word_gc_move_loop_ok = prove
 (`!k conf pb i pa old m dm c i1 pa1 m1 c1.
     word_gc_move_loop k conf (pb:A word,i,pa,old,m,dm,c) = (i1,pa1,m1,c1) ==> c1 ==> c`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:bool` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[word_gc_move_loop_F]);;

(* HOL4 line 554 (the HOL4 val gc_lemma, line 519, is unfolded here) *)
let gc_thm = prove
 (CASE_TERM
  `!conf (s:(A,C,FFI)stack_state).
   stack_state_gc_fun s = word_gc_fun conf /\
   data_to_word_config_gc_kind conf = data_to_word_Simple ==>
   stack_gc s =
   if LENGTH (stack_state_stack s) < stack_state_stack_space s then NONE else
     let unused = TAKE (stack_state_stack_space s) (stack_state_stack s) in
     let stack = DROP (stack_state_stack_space s) (stack_state_stack s) in
     let (w1,i1,pa1,m1,c1) =
              word_gc_move conf
                (FAPPLY (stack_state_store s) Globals,word 0,
                 theWord (FAPPLY (stack_state_store s) OtherHeap),
                 theWord (FAPPLY (stack_state_store s) CurrHeap),
                 stack_state_memory s,stack_state_mdomain s) in
     let (stack,i2,pa2,m2,c2) =
           word_gc_move_roots_bitmaps conf
             (stack,stack_state_bitmaps s,i1,pa1,
              theWord (FAPPLY (stack_state_store s) CurrHeap),m1,stack_state_mdomain s) in
     let (i1,pa1,m1,c2) =
           word_gc_move_loop (dimword(:A)) conf
             (theWord (FAPPLY (stack_state_store s) OtherHeap),i2,pa2,
              theWord (FAPPLY (stack_state_store s) CurrHeap),m2,stack_state_mdomain s,
              (c1 /\ c2)) in
     let s1 =
           stack_state_store s |++
           [(CurrHeap,wl_Word (theWord (FAPPLY (stack_state_store s) OtherHeap)));
            (OtherHeap,wl_Word (theWord (FAPPLY (stack_state_store s) CurrHeap)));
            (NextFree,wl_Word pa1);
            (TriggerGC,
             wl_Word (word_add (theWord (FAPPLY (stack_state_store s) OtherHeap))
                               (theWord (FAPPLY (stack_state_store s) HeapLength))));
            (EndOfHeap,
             wl_Word (word_add (theWord (FAPPLY (stack_state_store s) OtherHeap))
                               (theWord (FAPPLY (stack_state_store s) HeapLength))));
            (Globals,w1);
            (GlobReal,glob_real conf (theWord (FAPPLY (stack_state_store s) OtherHeap)) w1)] in
       if word_gc_fun_assum conf (stack_state_store s) /\ c2 then
         SOME (stack_state_stack_fupd (K (APPEND unused stack))
                (stack_state_store_fupd (K s1)
                  (stack_state_regs_fupd (K FEMPTY)
                    (stack_state_memory_fupd (K m1) s))))
       else NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[stack_gc_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; word_gc_move_roots_bitmaps_def] THEN
  ASM_SIMP_TAC[word_gc_fun_thm] THEN
  CASES_ON `stack_enc_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state))
              (DROP (stack_state_stack_space s) (stack_state_stack s))` THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
   [REPEAT (PAIRARG_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_ASSUM(fun th -> try ASSUME_TAC (MATCH_MP word_gc_move_loop_F (REWRITE_RULE[] th))
                          with Failure _ -> failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws2";"i2";"pa2";"m2";"c2"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_loop" ["i3";"pa3";"m3";"c3"] THEN
  CASES_ON `stack_dec_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state)) ws2
              (DROP (stack_state_stack_space s) (stack_state_stack s))` THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [STALLOCAUX_SPLIT_FN_TAC "word_gc_move_loop" ["i4";"pa4";"m4";"c4"] THEN
    FIRST_ASSUM(fun th -> try ASSUME_TAC (MATCH_MP word_gc_move_loop_F th)
                          with Failure _ -> failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 613 *)
let word_gc_move_bitmaps_def = cake_def
  `word_gc_move_bitmaps (conf:data_to_word_config)
     (w:(A)word_loc,stack:((A)word_loc)list,bitmaps:(A word)list,i1:A word,pa1:A word,
      curr:A word,m:A word->(A)word_loc,dm:A word->bool) =
     match full_read_bitmap bitmaps w with
       NONE -> NONE
     | SOME bs ->
         (match filter_bitmap bs stack with
            NONE -> NONE
          | SOME (ts,ws) ->
              let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
              (match map_bitmap bs wl stack with
                 NONE -> NONE
               | SOME (hd,ts1,ws') -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 line 629 *)
let word_gc_move_roots_APPEND = prove
 (CASE_TERM
  `!conf xs ys i1 pa1 (curr:A word) m dm.
      word_gc_move_roots conf (APPEND xs ys,i1,pa1,curr,m,dm) =
        let (ws1,i1,pa1,m1,c1) = word_gc_move_roots conf (xs,i1,pa1,curr,m,dm) in
        let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ys,i1,pa1,curr,m1,dm) in
          (APPEND ws1 ws2,i2,pa2,m2,(c1 /\ c2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; word_gc_move_roots_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THENL
   [REPEAT GEN_TAC THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["w1";"i3";"pa3";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws1";"i4";"pa4";"m4";"c4"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws2";"i5";"pa5";"m5";"c5"] THEN
  REWRITE_TAC[APPEND; CONJ_ACI]);;

(* HOL4 line 646 *)
let word_gc_move_roots_IMP_LENGTH = prove
 (`!xs r0 r1 (curr:A word) r2 dm ys i2 pa2 m2 c conf.
      word_gc_move_roots conf (xs,r0,r1,curr,r2,dm) = (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_gc_move_roots_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws2";"i3";"pa3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 656 *)
let word_gc_move_roots_bitmaps = prove
 (CASE_TERM
  `!conf bitmaps (curr:A word) dm stack i1 pa1 m stack2 i2 pa2 m2.
      word_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm) =
        (stack2,i2,pa2,m2,T) ==>
      word_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm) =
      match stack with
        [] -> (ARB,ARB,ARB,ARB,F)
      | CONS w ws ->
          if w = wl_Word (word 0) then (stack,i1,pa1,m,(ws = [])) else
            (match word_gc_move_bitmaps conf (w,ws,bitmaps,i1,pa1,curr,m,dm) with
               NONE -> (ARB,ARB,ARB,ARB,F)
             | SOME (new,stack,i2,pa2,m2,c2) ->
                 let (stack,i,pa,m,c3) =
                   word_gc_move_roots_bitmaps conf (stack,bitmaps,i2,pa2,curr,m2,dm) in
                 (CONS w (APPEND new stack),i,pa,m,(c2 /\ c3)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th] THEN MP_TAC th) THEN
  STRUCT_CASES_TAC(ISPEC `stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[word_gc_move_roots_bitmaps_def; stack_enc_stack_def] THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[word_gc_move_roots_def] THEN CASE_REWRITE_TAC[stack_dec_stack_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[word_gc_move_bitmaps_def] THEN
  CASES_ON `full_read_bitmap (bitmaps:(A word)list) (h:(A)word_loc)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `filter_bitmap a (t:((A)word_loc)list)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  STALLOCAUX_SPLIT_TAC `a':((A)word_loc)list#((A)word_loc)list`
    [`ts:((A)word_loc)list`; `ws':((A)word_loc)list`] THEN
  CASES_ON `stack_enc_stack (bitmaps:(A word)list) (ws':((A)word_loc)list)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[word_gc_move_roots_APPEND; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws1";"i3";"pa3";"m3";"c3"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["ws2";"i4";"pa4";"m4";"c4"] THEN
  SUBGOAL_THEN `LENGTH (ws1:((A)word_loc)list) = LENGTH (ts:((A)word_loc)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[word_gc_move_roots_IMP_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `filter_bitmap a (t:((A)word_loc)list) = SOME (ts,ws')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:bool list`; `ws1:((A)word_loc)list`; `t:((A)word_loc)list`;
                 `ts:((A)word_loc)list`; `ws':((A)word_loc)list`; `ws2:((A)word_loc)list`]
         map_bitmap_APPEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[stack_dec_stack_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `map_bitmap a (ws1:((A)word_loc)list) t` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STALLOCAUX_SPLIT_TAC `a''':((A)word_loc)list#((A)word_loc)list#((A)word_loc)list`
    [`hd:((A)word_loc)list`; `tsx:((A)word_loc)list`; `wsx:((A)word_loc)list`] THEN
  MP_TAC(ISPECL [`a:bool list`; `t:((A)word_loc)list`; `ws1:((A)word_loc)list`;
                 `ts:((A)word_loc)list`; `ws':((A)word_loc)list`; `tsx:((A)word_loc)list`;
                 `hd:((A)word_loc)list`; `wsx:((A)word_loc)list`] filter_bitmap_map_bitmap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `stack_dec_stack (bitmaps:(A word)list) ws2 ws'` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[APPEND]);;

(* the content types of a tuple type, n components *)
let rec stallocaux_tuple_tys ty n =
  if n = 1 then [ty] else
  match dest_type ty with
    ("prod",[a;b]) -> a :: stallocaux_tuple_tys b (n - 1)
  | _ -> failwith "stallocaux_tuple_tys";;

(* fresh variables with the given names and the component types of ty *)
let stallocaux_fresh_vars (avoid:term list) (names:string list) (ty:hol_type) =
  let vs0 = map2 (fun n t -> mk_var(n,t)) names (stallocaux_tuple_tys ty (length names)) in
  rev(snd(itlist (fun v (av,acc) -> let v' = variant av v in (v'::av, v'::acc))
                 (rev vs0) (avoid,[])));;

(* a case split on an option term: tm = NONE, or tm = SOME (v1,...,vn) with *)
(* the names given; the equation is assumed and the goal rewritten         *)
let STALLOCAUX_OPT_CASES_TAC (tm:term) (names:string list) : tactic = fun (asl,w as g) ->
  let cty = hd(snd(dest_type(type_of tm))) in
  let vs = stallocaux_fresh_vars (freesl (w :: map (concl o snd) asl)) names cty in
  let tup = end_itlist (curry mk_pair) vs in
  let none = inst [cty,`:A`] `NONE:A option` in
  let some = mk_icomb(inst [cty,`:A`] `SOME:A->A option`, tup) in
  let disj = mk_disj(mk_eq(tm,none), list_mk_exists(vs, mk_eq(tm,some))) in
  let a = genvar cty in
  let rec projs t n = if n = 1 then [t] else
      mk_icomb(`FST:A#B->A`,t) :: projs (mk_icomb(`SND:A#B->B`,t)) (n - 1) in
  let use th = ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] in
  (SUBGOAL_THEN disj MP_TAC THENL
   [MP_TAC(ISPEC tm (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                 (X_CHOOSE_THEN a (fun th -> REWRITE_TAC[th; option_DISTINCT; option_INJ]))) THEN
    MAP_EVERY EXISTS_TAC (projs a (length vs)) THEN REWRITE_TAC[PAIR];
    DISCH_THEN(DISJ_CASES_THEN2 use (REPEAT_TCL CHOOSE_THEN use))]) g;;

(* HOL4 line 706 *)
let word_gc_move_bitmap_def = cake_def
  `word_gc_move_bitmap (conf:data_to_word_config)
     (w:A word,stack:((A)word_loc)list,i1:A word,pa1:A word,curr:A word,
      m:A word->(A)word_loc,dm:A word->bool) =
     let bs = get_bits w in
     match filter_bitmap bs stack with
       NONE -> NONE
     | SOME (ts,ws) ->
         let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
         (match map_bitmap bs wl stack with
            NONE -> NONE
          | SOME (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2))`;;

(* HOL4 line 718 (an ML value in HOL4) *)
let map_bitmap_APPEND_APPEND = prove
 (CASE_TERM
  `!vs1 (stack:A list) x0 x1 ws2 vs2 ws1.
      filter_bitmap vs1 stack = SOME (x0,x1) /\
      LENGTH x0 = LENGTH ws1 ==>
      map_bitmap (APPEND vs1 vs2) (APPEND ws1 ws2) stack =
      match map_bitmap vs1 ws1 stack with
        NONE -> NONE
      | SOME (ts1,ts2,ts3) ->
          (match map_bitmap vs2 ws2 ts3 with
             NONE -> NONE
           | SOME (us1,us2,us3) -> SOME (APPEND ts1 us1,APPEND ts2 us2,us3))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_bitmap_def; option_INJ; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ARITH_RULE `0 = n <=> n = 0`; LENGTH_EQ_NIL]) THEN
    RVEQ_TAC THEN REWRITE_TAC[APPEND; map_bitmap_def] THEN CASE_REWRITE_TAC[APPEND] THEN
    CASE_TAC THEN CASE_REWRITE_TAC[] THEN CASE_TAC THEN CASE_REWRITE_TAC[] THEN
    CASE_TAC THEN CASE_REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN BOOL_CASES_TAC `h:bool` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `stack:A list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def; option_DISTINCT] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN FIRST_ASSUM CONTR_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN
    CASES_ON `ws1:A list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; NOT_SUC; SUC_INJ]) THEN
    TRY (FIRST_ASSUM CONTR_TAC) THEN
    REWRITE_TAC[APPEND; map_bitmap_def] THEN
    USE_THEN "ih" (MP_TAC o SPECL [`t':A list`; `x:A list`; `x1:A list`; `ws2:A list`;
                                   `vs2:bool list`; `a1:A list`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap t (a1:A list) t'` ["p1";"p2";"p3"] THEN
    TRY (STALLOCAUX_OPT_CASES_TAC `map_bitmap vs2 (ws2:A list) p3` ["q1";"q2";"q3"]) THEN
    REWRITE_TAC[APPEND];
    REWRITE_TAC[APPEND; map_bitmap_def] THEN
    USE_THEN "ih" (MP_TAC o SPECL [`t':A list`; `x0:A list`; `x1:A list`; `ws2:A list`;
                                   `vs2:bool list`; `ws1:A list`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap t (ws1:A list) t'` ["p1";"p2";"p3"] THEN
    TRY (STALLOCAUX_OPT_CASES_TAC `map_bitmap vs2 (ws2:A list) p3` ["q1";"q2";"q3"]) THEN
    REWRITE_TAC[APPEND]]);;

(* HOL4 line 742 (an ML value in HOL4) *)
let word_gc_move_bitmaps_Loc = prove
 (`!conf l1 l2 stack bitmaps i1 pa1 (curr:A word) m dm.
     word_gc_move_bitmaps conf (wl_Loc l1 l2,stack,bitmaps,i1,pa1,curr,m,dm) = NONE`,
  REWRITE_TAC[word_gc_move_bitmaps_def; full_read_bitmap_def] THEN CASE_REWRITE_TAC[]);;

(* a case split on a list term: tm = [], or tm = CONS h t with the names *)
(* given; the equation is assumed and the goal rewritten                 *)
let STALLOCAUX_LIST_CASES_TAC (tm:term) (names:string list) : tactic = fun (asl,w as g) ->
  let ety = hd(snd(dest_type(type_of tm))) in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let h = variant avoid (mk_var(hd names,ety)) in
  let t = variant (h::avoid) (mk_var(el 1 names,type_of tm)) in
  let nil = inst [ety,`:A`] `[]:A list` in
  let disj = mk_disj(mk_eq(tm,nil), list_mk_exists([h;t], mk_eq(tm,mk_cons h t))) in
  let use th = ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] in
  (SUBGOAL_THEN disj MP_TAC THENL
   [MESON_TAC[list_CASES];
    DISCH_THEN(DISJ_CASES_THEN2 use (REPEAT_TCL CHOOSE_THEN use))]) g;;

(* helpers for word_gc_move_bitmaps_unroll *)

let STALLOCAUX_bitmaps_next = prove
 (`!(w:A word) (bitmaps:(A word)list) y ys.
     ~(w = word 0) /\ LENGTH bitmaps < dimword(:A) - 1 /\
     DROP (val (word_sub w (word 1))) bitmaps = CONS y ys
     ==> DROP (val w) bitmaps = ys /\ ~(word_add w (word 1) = word 0) /\
         word_sub (word_add w (word 1)) (word 1) = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_LESS_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_EQ_CONS_IMP_DROP_SUC) THEN
  SUBGOAL_THEN `1 <= val (w:A word)` ASSUME_TAC THENL
   [ASM_MESON_TAC[VAL_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub (w:A word) (word 1)) = val w - 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `DROP (SUC (val (word_sub (w:A word) (word 1)))) (bitmaps:(A word)list) =
                 ys` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> SUC (n - 1) = n`];
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_ADD; VAL_WORD_1] THEN
    SUBGOAL_THEN `val (w:A word) + 1 < 2 EXP dimindex(:A)` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC];
    CONV_TAC WORD_RULE]);;

let STALLOCAUX_option_tuple6_id = prove
 (CASE_TERM
  `!x:(A#B#C#D#E#G)option.
     (match x with NONE -> NONE | SOME (a,b,c,d,e,f) -> SOME (a,b,c,d,e,f)) = x`,
  GEN_TAC THEN STALLOCAUX_OPT_CASES_TAC `x:(A#B#C#D#E#G)option` ["a";"b";"c";"d";"e";"f"]);;

(* HOL4 line 746 *)
let word_gc_move_bitmaps_unroll = prove
 (CASE_TERM
  `!conf (w:A word) stack bitmaps i1 pa1 curr m dm x.
    word_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i1,pa1,curr,m,dm) = SOME x /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) ==>
    word_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i1,pa1,curr,m,dm) =
    match DROP (val (word_sub w (word 1))) bitmaps with
      [] -> NONE
    | CONS y ys ->
        (match word_gc_move_bitmap conf (y,stack,i1,pa1,curr,m,dm) with
           NONE -> NONE
         | SOME (hd,ws,i2,pa2,m2,c2) ->
             if ~(word_msb y) then SOME (hd,ws,i2,pa2,m2,c2) else
               (match word_gc_move_bitmaps conf
                        (wl_Word (word_add w (word 1)),ws,bitmaps,i2,pa2,curr,m2,dm) with
                  NONE -> NONE
                | SOME (hd3,ws3,i3,pa3,m3,c3) ->
                    SOME (APPEND hd hd3,ws3,i3,pa3,m3,(c2 /\ c3))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC th) THEN
  REWRITE_TAC[word_gc_move_bitmaps_def; full_read_bitmap_def] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  STALLOCAUX_LIST_CASES_TAC `DROP (val (word_sub (w:A word) (word 1))) (bitmaps:(A word)list)`
    ["y";"ys"] THEN
  REWRITE_TAC[read_bitmap_def] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPECL [`w:A word`; `bitmaps:(A word)list`; `y:A word`; `ys:(A word)list`]
           STALLOCAUX_bitmaps_next) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN
  ASM_REWRITE_TAC[read_bitmap_def; word_gc_move_bitmap_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP get_bits_intro th]) THEN
    STALLOCAUX_OPT_CASES_TAC `read_bitmap (ys:(A word)list)` ["bs"] THEN
    REWRITE_TAC[option_DISTINCT; filter_bitmap_APPEND] THEN
    STALLOCAUX_OPT_CASES_TAC `filter_bitmap (get_bits (y:A word)) (stack:((A)word_loc)list)`
      ["zs";"rs"] THEN
    STALLOCAUX_OPT_CASES_TAC `filter_bitmap bs (rs:((A)word_loc)list)` ["zs2";"rs2"] THEN
    REWRITE_TAC[word_gc_move_roots_APPEND; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["wl1";"i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["wl2";"i4";"pa4";"m4";"c4"] THEN
    SUBGOAL_THEN `LENGTH (zs:((A)word_loc)list) = LENGTH (wl1:((A)word_loc)list)`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[word_gc_move_roots_IMP_LENGTH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`get_bits (y:A word)`; `stack:((A)word_loc)list`; `zs:((A)word_loc)list`;
                   `rs:((A)word_loc)list`; `wl2:((A)word_loc)list`; `bs:bool list`;
                   `wl1:((A)word_loc)list`] map_bitmap_APPEND_APPEND) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap (get_bits (y:A word)) (wl1:((A)word_loc)list) stack`
      ["t1";"t2";"t3"] THEN
    MP_TAC(ISPECL [`get_bits (y:A word)`; `stack:((A)word_loc)list`; `wl1:((A)word_loc)list`;
                   `zs:((A)word_loc)list`; `rs:((A)word_loc)list`; `t2:((A)word_loc)list`;
                   `t1:((A)word_loc)list`; `t3:((A)word_loc)list`] filter_bitmap_map_bitmap) THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap bs (wl2:((A)word_loc)list) rs` ["u1";"u2";"u3"] THEN
    REWRITE_TAC[];
    REWRITE_TAC[GSYM get_bits_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[STALLOCAUX_option_tuple6_id] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[STALLOCAUX_option_tuple6_id; BASICAUX_pair_CASE_K]]);;

let STALLOCAUX_get_bits_cons = prove
 (`!w:A word. ~(w = word 0) /\ ~(w = word 1) ==>
              get_bits w = CONS (bit 0 w) (get_bits (word_ushr w 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[get_bits_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [bit_length_def] THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN
  SUBGOAL_THEN `~(bit_length (word_ushr (w:A word) 1) = 0)` MP_TAC THENL
   [REWRITE_TAC[STALLOCAUX_bit_length_eq_0] THEN
    UNDISCH_TAC `~(w:A word = word 0)` THEN UNDISCH_TAC `~(w:A word = word 1)` THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_1; VAL_WORD_USHR; EXP_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`bit_length (word_ushr (w:A word) 1)`,`k:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
  REWRITE_TAC[GENLIST_CONS; CONS_11] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; BIT_WORD_USHR; ADD1]);;

(* HOL4 line 823 *)
let word_gc_move_bitmap_unroll = prove
 (CASE_TERM
  `!conf (w:A word) stack i1 pa1 curr m dm.
   word_gc_move_bitmap conf (w,stack,i1,pa1,curr,m,dm) =
    if w = word 0 then SOME ([],stack,i1,pa1,m,T) else
    if w = word 1 then SOME ([],stack,i1,pa1,m,T) else
      match stack with
        [] -> NONE
      | CONS x xs ->
        if word_and w (word 1) = word 0 then
          (match word_gc_move_bitmap conf (word_ushr w 1,xs,i1,pa1,curr,m,dm) with
             NONE -> NONE
           | SOME (new,stack,i1,pa1,m,c) -> SOME (CONS x new,stack,i1,pa1,m,c))
        else
          let (x1,i1,pa1,m1,c1) = word_gc_move conf (x,i1,pa1,curr,m,dm) in
          (match word_gc_move_bitmap conf (word_ushr w 1,xs,i1,pa1,curr,m1,dm) with
             NONE -> NONE
           | SOME (new,stack,i1,pa1,m,c) -> SOME (CONS x1 new,stack,i1,pa1,m,(c1 /\ c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_allocProof_word_and_one_eq_0_iff] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gc_move_bitmap_def; get_bits_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[STALLOCAUX_bit_length_eq_0 |> SPEC `word 0:A word` |> REWRITE_RULE[]] THEN
    STALLOCAUX_RW_TAC[SUB_0; LIST_OF_SEQ; filter_bitmap_def; map_bitmap_def;
                      word_gc_move_roots_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `w:A word = word 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gc_move_bitmap_def; get_bits_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[bit_length_eq_1 |> SPEC `word 1:A word` |> REWRITE_RULE[]] THEN
    STALLOCAUX_RW_TAC[SUB_REFL; LIST_OF_SEQ; filter_bitmap_def; map_bitmap_def;
                      word_gc_move_roots_def];
    ALL_TAC] THEN
  ASM_SIMP_TAC[word_gc_move_bitmap_def; LET_DEF; LET_END_DEF; STALLOCAUX_get_bits_cons] THEN
  STRUCT_CASES_TAC(ISPEC `stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit 0 (w:A word)` THEN ASM_REWRITE_TAC[filter_bitmap_def] THEN
  CASE_REWRITE_TAC[] THEN
  STALLOCAUX_OPT_CASES_TAC
    `filter_bitmap (get_bits (word_ushr (w:A word) 1)) (t:((A)word_loc)list)` ["ts";"ws"] THEN
  REWRITE_TAC[word_gc_move_roots_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  TRY (STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["x1";"i3";"pa3";"m3";"c3"]) THEN
  TRY (STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["wl";"i4";"pa4";"m4";"c4"]) THEN
  REWRITE_TAC[map_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (STALLOCAUX_OPT_CASES_TAC
    `map_bitmap (get_bits (word_ushr (w:A word) 1)) (wl:((A)word_loc)list) t`
    ["hd";"p";"q"]) THEN
  REWRITE_TAC[]);;

(* more rewrites for the evaluator in the GC code proofs *)
let () = stallocaux_add_rws
  [WORD_ADD_SUB; WORD_OR_0; WORD_AND_NOT0; WORD_XOR_0; theWord_def; decode_length_def;
   FUPDATE_LIST_THM; isWord_def];;

(* HOL4 line 875 *)
let word_gc_move_code_thm = prove
 (`!conf w i pa old m dm w1 i1 pa1 m1 (s:(A,C,FFI)stack_state).
    word_gc_move conf (w,i,pa,old,m,dm) = (w1,i1,pa1,m1,T) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\
    0 IN FDOM (stack_state_regs s) /\
    1 IN FDOM (stack_state_regs s) /\
    2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\
    stack_get_var 4 s = SOME (wl_Word i) /\
    stack_get_var 5 s = SOME w /\
    6 IN FDOM (stack_state_regs s) ==>
    ?ck r0 r1 r2 r6.
      stack_evaluate (word_gc_move_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_regs_fupd
                   (K (stack_state_regs s |++
                       [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                        (5,w1); (6,r6)])) s))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[word_gc_move_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC] THEN
  ASM_CASES_TAC `word_and (a:A word) (word 1) = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_mul (word_ushr (a:A word) (shift_length conf)) bytes_in_word) old =
                ptr_to_addr conf old a` ASSUME_TAC THENL
   [REWRITE_TAC[ptr_to_addr_def] THEN MATCH_ACCEPT_TAC WORD_ADD_SYM; ALL_TAC] THEN
  ASM_CASES_TAC `is_fwd_ptr (m (ptr_to_addr conf old (a:A word)):(A)word_loc)` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `vv:A word` STRIP_ASSUME_TAC o REWRITE_RULE[is_fwd_ptr_iff]) THEN
    ASM_REWRITE_TAC[theWord_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_code_def; clear_top_inst_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC THEN
    REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM;
    ALL_TAC] THEN
  STALLOCAUX_SPLIT_FN_TAC "memcpy" ["pb";"mb";"cb"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `hdr:A word` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def; is_fwd_ptr_def]) THEN ASSUME_TAC th) o
    REWRITE_RULE[isWord_thm] o
    check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
  EXISTS_TAC `val (word_add (decode_length conf (hdr:A word)) (word 1))` THEN
  REWRITE_TAC[word_gc_move_code_def; clear_top_inst_def] THEN STALLOCAUX_EV_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (MP_TAC(ISPECL [`word_add (decode_length conf (hdr:A word)) (word 1)`;
                    `ptr_to_addr conf old (a:A word)`; `pa:A word`;
                    `stack_state_memory (s:(A,C,FFI)stack_state)`;
                    `stack_state_mdomain (s:(A,C,FFI)stack_state)`;
                    `pa1:A word`; `mb:A word->(A)word_loc`; s0] memcpy_code_thm)) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1':(A)word_loc` (fun th -> STALLOCAUX_EV_KNOWN_TAC [th])) THEN
  STALLOCAUX_STATE_EQ_TAC THENL
   [REWRITE_TAC[WORD_ADD_ASSOC];
    REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM]);;

(* the clock witness, a function of a new witness: ?x. P x from ?y. P (f y) *)
let STALLOCAUX_EX_FUN = prove
 (`!P (f:num->num). (?y. P (f y)) ==> (?x:num. P x)`,
  MESON_TAC[]);;

(* the goal ?x. P x (x the clock): continue with ?v. P (f v), f = \v. t *)
let STALLOCAUX_CLOCK_FN_TAC (f:term) : tactic = fun (asl,w as g) ->
  let x,body = dest_exists w in
  let th = CONV_RULE (RAND_CONV (BINDER_CONV BETA_CONV))
             (ISPECL [mk_abs(x,body); f] STALLOCAUX_EX_FUN) in
  let v = fst(dest_abs f) in
  (MATCH_MP_TAC th THEN CONV_TAC (GEN_ALPHA_CONV v) THEN
   CONV_TAC (BINDER_CONV (RAND_CONV BETA_CONV THENC BETA_CONV))) g;;

(* unfold the first loop of the goal once (HOL4: simp [Once evaluate_def]) *)
let STALLOCAUX_LOOP_UNFOLD_TAC : tactic =
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [STALLOCAUX_ev_clause "stack_Loop"];;

(* after the body of an unfolded loop has run: reduce the loop's case, the  *)
(* clock test, STOP; normalise the states                                   *)
let STALLOCAUX_LOOP_STEP_TAC : tactic =
  CASE_REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def; stack_STOP_def] THEN
  CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  CONV_TAC (stallocaux_norm []);;

(* HOL4 line 963: by induction on the counter (HOL4 Cases \\ Induct_on n) *)
let STALLOCAUX_word_gc_move_list_code_n = prove
 (`!n a (s:(A,C,FFI)stack_state) pa1 pa old m1 m i1 i dm conf a1.
      n < dimword(:A) /\ word_gc_move_list conf (a:A word,word n,i,pa,old,m,dm) = (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) ==>
      6 IN FDOM (stack_state_regs s) ==>
      stack_get_var 7 s = SOME (wl_Word (word n)) /\
      stack_get_var 8 s = SOME (wl_Word a) ==>
      ?ck r0 r1 r2 r5 r6.
        stack_evaluate (word_gc_move_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,r5); (6,r6); (7,wl_Word (word 0)); (8,wl_Word a1)])) s))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_gc_move_list_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[word_gc_move_list_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STALLOCAUX_word_suc_facts) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_list"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gc_move_list_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["w1";"i2";"pa2";"m2";"c2"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_list" ["a3";"i3";"pa3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[word_gc_move_list_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
  STALLOCAUX_EV_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (MP_TAC(ISPECL [`conf:data_to_word_config`;
                    `stack_state_memory (s:(A,C,FFI)stack_state) a`; `i:A word`; `pa:A word`;
                    `old:A word`; `stack_state_memory (s:(A,C,FFI)stack_state)`;
                    `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `w1:(A)word_loc`;
                    `i2:A word`; `pa2:A word`; `m2:A word->(A)word_loc`; s0]
            word_gc_move_code_thm)) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
    (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
    (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC))))) THEN
  STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
  FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
    (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
  STALLOCAUX_LOOP_STEP_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
       SPECL [`word_add a bytes_in_word:A word`; s0; `pa1:A word`; `pa2:A word`;
              `old:A word`; `m1:A word->(A)word_loc`;
              `(a =+ w1) (m2:A word->(A)word_loc)`; `i1:A word`; `i2:A word`;
              `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `conf:data_to_word_config`;
              `a1:A word`])) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
    (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
    (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
     (fun th -> EXISTS_TAC `ck3:num` THEN
                STALLOCAUX_USE_EV_TAC [word_gc_move_list_code_def] th))))))) THEN
  STALLOCAUX_STATE_EQ_TAC);;

let word_gc_move_list_code_thm = prove
 (`!l a (s:(A,C,FFI)stack_state) pa1 pa old m1 m i1 i dm conf a1.
      word_gc_move_list conf (a:A word,l,i,pa,old,m,dm) = (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) ==>
      6 IN FDOM (stack_state_regs s) ==>
      stack_get_var 7 s = SOME (wl_Word l) /\
      stack_get_var 8 s = SOME (wl_Word a) ==>
      ?ck r0 r1 r2 r5 r6.
        stack_evaluate (word_gc_move_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,r5); (6,r6); (7,wl_Word (word 0)); (8,wl_Word a1)])) s))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `l:A word` WORD_VAL) THEN DISCH_THEN(fun th ->
    ONCE_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`val (l:A word)`; `a:A word`; `s:(A,C,FFI)stack_state`; `pa1:A word`;
                `pa:A word`; `old:A word`; `m1:A word->(A)word_loc`;
                `m:A word->(A)word_loc`; `i1:A word`; `i:A word`; `dm:A word->bool`;
                `conf:data_to_word_config`; `a1:A word`]
         STALLOCAUX_word_gc_move_list_code_n) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[dimword_def; VAL_BOUND]);;

(* the components of the tuple argument of the first assumption f x (y) = r *)
(* with f the constant c, and the components of its right side             *)
let stallocaux_assum_args (c:string) (asl:(string*thm) list) =
  let th = snd(find (fun (_,th) ->
    try let l = lhs(concl th) in
        let h,_ = strip_comb l in fst(dest_const h) = c
    with Failure _ -> false) asl) in
  let l,r = dest_eq(concl th) in
  let rec comps t = if is_pair t then let a,b = dest_pair t in a :: comps b else [t] in
  comps (rand l), comps r;;

let STALLOCAUX_word_and_4 = prove
 (`!w:A word. 2 < dimindex(:A) ==> (word_and w (word 4) = word 0 <=> ~bit 2 w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `2`) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j = 2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~ODD (4 DIV 2 EXP j)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `j < 2` THENL
     [SUBGOAL_THEN `j = 0 \/ j = 1` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
      SUBGOAL_THEN `4 DIV 2 EXP j = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
      MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 3` THEN
      CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]]]);;

(* HOL4 line 1050 (HOL4 completeInduct_on k; the counter decreases by one) *)
let word_gc_move_loop_code_thm = prove
 (`!conf k pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:(A,C,FFI)stack_state).
  word_gc_move_loop k conf (pb1,i1,pa1,old1,m1,dm1,c1) = (i2,pa2,m2,T) /\
  shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
  2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
  data_to_word_config_len_size conf + 2 < dimindex (:A) /\
  (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
  FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old1) /\ stack_state_use_store s /\
  stack_state_memory s = m1 /\ stack_state_mdomain s = dm1 /\
  0 IN FDOM (stack_state_regs s) /\ 1 IN FDOM (stack_state_regs s) /\
  2 IN FDOM (stack_state_regs s) /\
  stack_get_var 3 s = SOME (wl_Word pa1) /\ stack_get_var 4 s = SOME (wl_Word i1) /\
  5 IN FDOM (stack_state_regs s) ==>
  6 IN FDOM (stack_state_regs s) ==>
  7 IN FDOM (stack_state_regs s) ==>
  stack_get_var 8 s = SOME (wl_Word pb1) /\ c1 ==>
  ?ck r0 r1 r2 r5 r6 r7.
    stack_evaluate (word_gc_move_loop_code conf,
                    stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
    (NONE,stack_state_memory_fupd (K m2)
            (stack_state_regs_fupd
               (K (stack_state_regs s |++
                   [(0,r0); (1,r1); (2,r2); (3,wl_Word pa2); (4,wl_Word i2); (5,r5); (6,r6);
                    (7,r7); (8,wl_Word pa2)])) s))`,
  GEN_TAC THEN INDUCT_TAC THENL [ALL_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_loop"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gc_move_loop_def] THEN
  ASM_CASES_TAC `pb1:A word = pa1` THEN ASM_REWRITE_TAC[PAIR_EQ; NOT_SUC; SUC_SUB1] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_loop_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_loop_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_CASES_TAC `bit 2 (theWord ((m1:A word->(A)word_loc) pb1))` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_move_loop_ok) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[isWord_thm] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th))) THEN
    SUBGOAL_THEN `~(word_and (v:A word) (word 4) = word 0) /\ ~(pa1 = pb1:A word)`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[STALLOCAUX_word_and_4] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck2 + 1` THEN
    REWRITE_TAC[word_gc_move_loop_code_def] THEN STALLOCAUX_EV_TAC;
    POP_ASSUM MP_TAC THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_list" ["pb2";"i3";"pa3";"m3";"c3"] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_move_loop_ok) THEN
    REWRITE_TAC[isWord_thm] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `v:A word` (fun th ->
         RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th))) ASSUME_TAC) THEN
    SUBGOAL_THEN `word_and (v:A word) (word 4) = word 0 /\ ~(pa1 = pb1:A word)`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[STALLOCAUX_word_and_4] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[word_gc_move_loop_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gc_move_list" asl in
      (match args, res with
         [a;l;i;pa;old;m;dm], [a1;i1;pa1;m1;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [l;a;s0;pa1;pa;old;m1;m;i1;i;dm;
                    `conf:data_to_word_config`;a1] word_gc_move_list_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC)))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC] THEN
  (fun (asl,w as g) ->
    let s0 = stallocaux_goal_state w in
    let args,res = stallocaux_assum_args "word_gc_move_loop" asl in
    (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
       SPECL (args @ butlast res @ [s0]))) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
    (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
    (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
    (X_CHOOSE_THEN `p7:(A)word_loc`
     (fun th -> EXISTS_TAC `ck3:num` THEN
                STALLOCAUX_USE_EV_TAC [word_gc_move_loop_code_def] th)))))))) THEN
  STALLOCAUX_STATE_EQ_TAC);;

(* the same for an assumption f x = SOME y: the components of x and of y *)
let stallocaux_assum_args_some (c:string) (asl:(string*thm) list) =
  let args,res = stallocaux_assum_args c asl in
  match res with
    [r] when is_comb r && is_const (rator r) && fst(dest_const(rator r)) = "SOME" ->
      let rec comps t = if is_pair t then let a,b = dest_pair t in a :: comps b else [t] in
      args, comps (rand r)
  | _ -> failwith "stallocaux_assum_args_some";;

(* StackLoadAny and StackStoreAny at a stack offset bytes_in_word * n *)

let STALLOCAUX_bytes_n_facts = prove
 (`!n. good_dimindex(:A) /\ (dimindex(:A) DIV 8) * n < dimword(:A)
       ==> word_ushr (word_mul bytes_in_word (word n)) (backend_common_word_shift (:A)) =
           word n:A word /\
           val (word n:A word) = n /\
           word_shl (word n:A word) (backend_common_word_shift (:A)) =
           word_mul bytes_in_word (word n)`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[bytes_in_word_word_shift_n2w] THEN
  SUBGOAL_THEN `n < dimword(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `(dimindex(:A) DIV 8) * n < dimword(:A)` THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[VAL_WORD; MOD_LT; GSYM dimword_def]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP bytes_in_word_mul_eq_shift th)]));;

let STALLOCAUX_ev_stackloadany_n = prove
 (`!r rn n (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\
     FLOOKUP (stack_state_regs s) rn = SOME (wl_Word (word_mul bytes_in_word (word n))) /\
     good_dimindex(:A) /\ (dimindex(:A) DIV 8) * n < dimword(:A) /\
     stack_state_stack_space s + n < LENGTH (stack_state_stack s)
     ==> stack_evaluate (StackLoadAny r rn,s) =
         (NONE,stack_set_var r (EL (stack_state_stack_space s + n) (stack_state_stack s)) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` STALLOCAUX_bytes_n_facts) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:num`; `rn:num`; `word_mul bytes_in_word (word n):A word`;
                 `s:(A,C,FFI)stack_state`] STALLOCAUX_ev_stackloadany) THEN
  ASM_REWRITE_TAC[]);;

let STALLOCAUX_ev_stackstoreany_n = prove
 (`!r rn v n (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\ FLOOKUP (stack_state_regs s) r = SOME v /\
     FLOOKUP (stack_state_regs s) rn = SOME (wl_Word (word_mul bytes_in_word (word n))) /\
     good_dimindex(:A) /\ (dimindex(:A) DIV 8) * n < dimword(:A) /\
     stack_state_stack_space s + n < LENGTH (stack_state_stack s)
     ==> stack_evaluate (StackStoreAny r rn,s) =
         (NONE,stack_state_stack_fupd
                 (K (LUPDATE v (stack_state_stack_space s + n) (stack_state_stack s))) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` STALLOCAUX_bytes_n_facts) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:num`; `rn:num`; `v:(A)word_loc`; `word_mul bytes_in_word (word n):A word`;
                 `s:(A,C,FFI)stack_state`] STALLOCAUX_ev_stackstoreany) THEN
  ASM_REWRITE_TAC[]);;

let () = STALLOCAUX_leaf_lemmas :=
  STALLOCAUX_ev_stackloadany_n :: STALLOCAUX_ev_stackstoreany_n :: !STALLOCAUX_leaf_lemmas;;

let () = stallocaux_add_rws [LENGTH_APPEND; LENGTH];;

let STALLOCAUX_mul_lt = prove
 (`!k a b d. k * a < d /\ b <= a ==> k * b < d`,
  REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS `k * a` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL]);;

let STALLOCAUX_bytes_suc = prove
 (`!n. word_mul bytes_in_word (word (SUC n)):A word =
       word_add (word_mul bytes_in_word (word n)) bytes_in_word`,
  REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE);;

let STALLOCAUX_EL_mid = prove
 (`!(a:A list) b x c. EL (LENGTH a + LENGTH b) (APPEND a (APPEND b (CONS x c))) = x`,
  REWRITE_TAC[APPEND_ASSOC; GSYM LENGTH_APPEND] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]);;

let STALLOCAUX_LUPDATE_mid = prove
 (`!(a:A list) b x c y. LUPDATE y (LENGTH a + LENGTH b) (APPEND a (APPEND b (CONS x c))) =
                        APPEND a (APPEND b (CONS y c))`,
  REWRITE_TAC[APPEND_ASSOC; GSYM LENGTH_APPEND; LUPDATE_LENGTH]);;

let () = stallocaux_add_rws [STALLOCAUX_bytes_suc; STALLOCAUX_EL_mid; STALLOCAUX_LUPDATE_mid];;

(* HOL4 line 1166 (HOL4 recInduct bit_length_ind) *)
let word_gc_move_bitmap_code_thm = prove
 (`!conf (init:((A)word_loc)list) w stack (s:(A,C,FFI)stack_state) i pa curr m dm new stack1
     (a1:A word) i1 pa1 m1 old.
      word_gc_move_bitmap conf (w,stack,i,pa,curr,m,dm) = SOME (new,stack1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_use_stack s /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) /\
      6 IN FDOM (stack_state_regs s) /\
      stack_get_var 7 s = SOME (wl_Word w) /\
      stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
      stack_state_stack s = APPEND (APPEND init old) stack /\
      stack_state_stack_space s = LENGTH init /\
      (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
      ?ck r0 r1 r2 r5 r6 r7.
        stack_evaluate (word_gc_move_bitmap_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_stack_fupd (K (APPEND (APPEND (APPEND init old) new) stack1))
                     (stack_state_regs_fupd
                        (K (stack_state_regs s |++
                            [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                             (5,r5); (6,r6); (7,r7);
                             (8,wl_Word (word_mul bytes_in_word
                                           (word (LENGTH (APPEND old new)))))])) s)))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE[] bit_length_ind) THEN
  X_GEN_TAC `w:A word` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
    then ASSUME_TAC (GEN `x:A word` (MP (ISPEC `x:A word` lower_2w_eq) th)) else NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_bitmap"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gc_move_bitmap_unroll] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `w:A word = word 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gc_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  STALLOCAUX_LIST_CASES_TAC `stack:((A)word_loc)list` ["x";"xs"] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `word_and (w:A word) (word 1) = word 0` THEN ASM_REWRITE_TAC[] THENL
   [STALLOCAUX_OPT_CASES_TAC
      `word_gc_move_bitmap conf (word_ushr w 1,xs:((A)word_loc)list,i,pa,curr,m,dm)`
      ["new2";"st2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck2 + 1` THEN
    REWRITE_TAC[word_gc_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gc_move_bitmap" asl in
      (match args, res with
         [w';stk;i;pa;curr;m;dm], [nw;st;i1;pa1;m1;_] ->
           USE_THEN "ih" (fun ih -> MP_TAC (REWRITE_RULE[IMP_IMP]
             (SPECL [stk;s0;i;pa;curr;m;dm;nw;st;i1;pa1;m1;
                     `APPEND old [x:(A)word_loc]`]
                (MP ih (ASSUME `~(w:A word = word 0)`)))))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gc_move_bitmap_code_def] th)))))))) THEN
    STALLOCAUX_STATE_EQ_TAC;
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["x1";"i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_OPT_CASES_TAC
      `word_gc_move_bitmap conf (word_ushr w 1,xs:((A)word_loc)list,i3,pa3,curr,m3,dm)`
      ["new2";"st2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * LENGTH (old:((A)word_loc)list) < dimword(:A)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC STALLOCAUX_mul_lt THEN
      EXISTS_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[word_gc_move_bitmap_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gc_move" asl in
      (match args, res with
         [x;i;pa;old;m;dm], [w1;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`;x;i;pa;old;m;dm;w1;i1;pa1;m1;s0]
                    word_gc_move_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gc_move_bitmap" asl in
      (match args, res with
         [w';stk;i;pa;curr;m;dm], [nw;st;i1;pa1;m1;_] ->
           USE_THEN "ih" (fun ih -> MP_TAC (REWRITE_RULE[IMP_IMP]
             (SPECL [stk;s0;i;pa;curr;m;dm;nw;st;i1;pa1;m1;
                     `APPEND old [x1:(A)word_loc]`]
                (MP ih (ASSUME `~(w:A word = word 0)`)))))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gc_move_bitmap_code_def] th)))))))) THEN
    STALLOCAUX_STATE_EQ_TAC]);;

(* rewrites and tactics for the bitmaps loop                              *)
let STALLOCAUX_word_sub_add_1 = prove
 (`!x:A word. word_add (word_sub x (word 1)) (word 1) = x`,
  CONV_TAC WORD_RULE);;

let () = stallocaux_add_rws [STALLOCAUX_word_sub_add_1; WORD_AND_REFL];;


(* eliminate the given variables with assumptions v = t or t = v (only    *)
(* these; HOL4 rveq can eliminate too much)                                *)
let STALLOCAUX_ELIM_TAC (vs:term list) : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let l,r = dest_eq (concl th) in
    if mem l vs && not (free_in l r) then SUBST_ALL_TAC th
    else if mem r vs && not (free_in r l) then SUBST_ALL_TAC (SYM th)
    else failwith "STALLOCAUX_ELIM_TAC"));;

(* complete induction on a measure m of the outer variables xs of the goal *)
(* !x1 .. xk. body: the goal becomes the step for n, with the assumption   *)
(* m = n and the induction hypothesis !xs. m < n ==> !rest. body (ih)      *)
let STALLOCAUX_MEASURE_INDUCT_TAC (xs:term list) (m:term) : tactic = fun (asl,w as g) ->
  let n = variant (freesl (w :: map (concl o snd) asl)) `n:num` in
  let ys,body = strip_forall w in
  let ys' = subtract ys xs in
  let body' = list_mk_forall(ys', body) in
  let gl = mk_forall(n, list_mk_forall(xs, mk_imp(mk_eq(m,n), body'))) in
  let simp_ih th =
    let ltn = mk_binop `(<):num->num->bool` m n in
    GENL xs (DISCH ltn (MP (SPECL xs (MP (SPEC m th) (ASSUME ltn))) (REFL m))) in
  (SUBGOAL_THEN gl (fun th ->
       MATCH_ACCEPT_TAC (GENL ys (SPECL ys' (MP (SPECL xs (SPEC m th)) (REFL m))))) THEN
   MATCH_MP_TAC num_WF THEN X_GEN_TAC n THEN
   DISCH_THEN(fun th -> LABEL_TAC "ih" (simp_ih th)) THEN
   REPEAT GEN_TAC THEN DISCH_TAC) g;;

(* HOL4 line 1311 *)
let word_gc_move_bitmaps_LENGTH = prove
 (`!conf (w:(A)word_loc) stack bitmaps i pa curr m dm xs stack1 i1 pa1 m1.
     word_gc_move_bitmaps conf (w,stack,bitmaps,i,pa,curr,m,dm) =
       SOME (xs,stack1,i1,pa1,m1,T) ==>
     LENGTH stack = LENGTH xs + LENGTH stack1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gc_move_bitmaps_def] THEN
  STALLOCAUX_OPT_CASES_TAC `full_read_bitmap (bitmaps:(A word)list) (w:(A)word_loc)` ["bs"] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  STALLOCAUX_OPT_CASES_TAC `filter_bitmap bs (stack:((A)word_loc)list)` ["ts";"ws"] THEN
  REWRITE_TAC[option_DISTINCT; LET_DEF; LET_END_DEF] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots" ["wl";"i2";"pa2";"m2";"c2"] THEN
  STALLOCAUX_OPT_CASES_TAC `map_bitmap bs (wl:((A)word_loc)list) stack` ["hd";"ts1";"ws1"] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`bs:bool list`; `wl:((A)word_loc)list`; `stack:((A)word_loc)list`;
                 `xs:((A)word_loc)list`; `(ts1:((A)word_loc)list,ws1:((A)word_loc)list)`]
         map_bitmap_IMP_LENGTH) THEN
  MP_TAC(ISPECL [`bs:bool list`; `stack:((A)word_loc)list`; `ts:((A)word_loc)list`;
                 `stack1:((A)word_loc)list`] filter_bitmap_IMP_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* a successful word_gc_move_bitmaps starts from a nonzero bitmap index  *)
let STALLOCAUX_bitmaps_nonzero = prove
 (`!conf (w:A word) stack (bitmaps:(A word)list) i pa curr m dm x.
     word_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i,pa,curr,m,dm) = SOME x
     ==> ~(w = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gc_move_bitmaps_def; full_read_bitmap_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 1323 *)
let word_gc_move_bitmaps_code_thm = prove
 (`!conf (init:((A)word_loc)list) w bitmaps (z:A word) stack (s:(A,C,FFI)stack_state)
     i pa curr m dm new stack1 (a1:A word) i1 pa1 m1 old.
    word_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i,pa,curr,m,dm) =
      SOME (new,stack1,i1,pa1,m1,T) /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_bitmaps s = bitmaps /\
    stack_state_use_stack s /\
    stack_get_var 0 s = SOME (wl_Word z) /\ ~(z = word 0) /\
    1 IN FDOM (stack_state_regs s) /\ 2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\ stack_get_var 4 s = SOME (wl_Word i) /\
    5 IN FDOM (stack_state_regs s) /\ 6 IN FDOM (stack_state_regs s) /\
    7 IN FDOM (stack_state_regs s) /\
    stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
    stack_get_var 9 s = SOME (wl_Word (word_sub w (word 1))) /\
    stack_state_stack s = APPEND (APPEND init old) stack /\
    stack_state_stack_space s = LENGTH init /\
    (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
    ?ck r0 r1 r2 r5 r6 r7 r9.
      stack_evaluate (word_gc_move_bitmaps_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_stack_fupd (K (APPEND (APPEND (APPEND init old) new) stack1))
                  (stack_state_clock_fupd (K (stack_state_clock s))
                    (stack_state_regs_fupd
                       (K (stack_state_regs s |++
                           [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                            (5,r5); (6,r6); (7,r7);
                            (8,wl_Word (word_mul bytes_in_word
                                          (word (LENGTH (APPEND old new)))));
                            (9,r9)])) s))))`,
  (GEN_TAC THEN GEN_TAC THEN
    STALLOCAUX_MEASURE_INDUCT_TAC [`w:A word`; `bitmaps:(A word)list`]
      `LENGTH (bitmaps:(A word)list) - val (word_sub (w:A word) (word 1))` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP STALLOCAUX_bitmaps_nonzero o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_bitmaps"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] word_gc_move_bitmaps_unroll) o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (POP_ASSUM MP_TAC THEN
    STALLOCAUX_LIST_CASES_TAC `DROP (val (word_sub (w:A word) (word 1))) (bitmaps:(A word)list)`
      ["y";"ys"] THEN
    REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_EL o check (fun th ->
      can (term_match [] `DROP n (l:(A word)list) = CONS h t`) (concl th))) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_LESS_LENGTH o check (fun th ->
      can (term_match [] `DROP n (l:(A word)list) = CONS h t`) (concl th))) THEN
    MP_TAC(ISPECL [`w:A word`; `bitmaps:(A word)list`; `y:A word`; `ys:(A word)list`]
             STALLOCAUX_bitmaps_next) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_gc_move_bitmap"
                               with Failure _ -> false)) (concl th))) THEN
    STALLOCAUX_OPT_CASES_TAC `word_gc_move_bitmap conf (y,stack:((A)word_loc)list,i,pa,curr,m,dm)`
      ["hd2";"ws2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    ASM_CASES_TAC `word_msb (y:A word)` THEN ASM_REWRITE_TAC[]) THENL
  [(STALLOCAUX_OPT_CASES_TAC `word_gc_move_bitmaps conf (wl_Word (word_add (w:A word) (word 1)),ws2:((A)word_loc)list,bitmaps,i2,pa2,curr,m2,dm)`
      ["hd3";"ws3";"i3";"pa3";"m3";"c3"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`new:((A)word_loc)list`; `stack1:((A)word_loc)list`; `i1:A word`;
                         `pa1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `~(word_ushr (y:A word) (dimindex(:A) - 1) = word 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM word_msb_IFF_lsr_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (word_sub (w:A word) (word 1)) + 1 = val w` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w:A word = word 0)` THEN
      REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
      ALL_TAC]) THEN
  (REWRITE_TAC[word_gc_move_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gc_move_bitmap" asl in
      (match args, res with
         [y;stk;i;pa;curr;m;dm], [nw;st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`;y;stk;s0;i;pa;curr;
                          m;dm;nw;st;`a1:A word`;i1;pa1;m1;`old:((A)word_loc)list`]
                    word_gc_move_bitmap_code_thm)
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (SUBGOAL_THEN `LENGTH (stack:((A)word_loc)list) =
                  LENGTH (hd2:((A)word_loc)list) + LENGTH (ws2:((A)word_loc)list)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`conf:data_to_word_config`; `wl_Word (w:A word)`; `stack:((A)word_loc)list`;
                     `bitmaps:(A word)list`; `i:A word`; `pa:A word`; `curr:A word`;
                     `m:A word->(A)word_loc`; `dm:A word->bool`;
                     `APPEND hd2 (hd3:((A)word_loc)list)`; `ws3:((A)word_loc)list`; `i3:A word`;
                     `pa3:A word`; `m3:A word->(A)word_loc`] word_gc_move_bitmaps_LENGTH) THEN
      MP_TAC(ISPECL [`conf:data_to_word_config`; `wl_Word (word_add (w:A word) (word 1))`;
                     `ws2:((A)word_loc)list`;
                     `bitmaps:(A word)list`; `i2:A word`; `pa2:A word`; `curr:A word`;
                     `m2:A word->(A)word_loc`; `dm:A word->bool`;
                     `hd3:((A)word_loc)list`; `ws3:((A)word_loc)list`; `i3:A word`;
                     `pa3:A word`; `m3:A word->(A)word_loc`] word_gc_move_bitmaps_LENGTH) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) *
                  (((LENGTH (init:((A)word_loc)list) + LENGTH (old:((A)word_loc)list)) +
                    LENGTH (hd2:((A)word_loc)list)) + LENGTH (ws2:((A)word_loc)list)) <
                  dimword(:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `(dimindex(:A) DIV 8) * LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                   dimword(:A)` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; ADD_ASSOC];
      ALL_TAC]) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gc_move_bitmaps" asl in
      (match args, res with
         [ww;stk;bms;i;pa;curr;m;dm], [nw;st;i1;pa1;m1;_] ->
           let w1 = rand ww in
           USE_THEN "ih" (fun ih -> MP_TAC (SPECL [w1;bms] ih)) THEN
           (ANTS_TAC THENL [CONV_TAC (stallocaux_norm (stallocaux_facts asl)) THEN ASM_ARITH_TAC;
                           ALL_TAC]) THEN
           DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL [`word_ushr (y:A word) (dimindex(:A) - 1)`;stk;s0;i;pa;curr;m;dm;nw;st;
                    i1;pa1;m1;`APPEND old (hd2:((A)word_loc)list)`])
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p9:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gc_move_bitmaps_code_def] th))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`new:((A)word_loc)list`; `stack1:((A)word_loc)list`; `i1:A word`;
                         `pa1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `word_ushr (y:A word) (dimindex(:A) - 1) = word 0` ASSUME_TAC THENL
     [MP_TAC(ISPEC `y:A word` word_msb_IFF_lsr_EQ_0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[word_gc_move_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gc_move_bitmap" asl in
      (match args, res with
         [y;stk;i;pa;curr;m;dm], [nw;st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`;y;stk;s0;i;pa;curr;
                          m;dm;nw;st;`a1:A word`;i1;pa1;m1;`old:((A)word_loc)list`]
                    word_gc_move_bitmap_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC THEN EXISTS_TAC `0` THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC)]);;

(* rewrites and a stack load at an offset bytes_in_word * n + bytes_in_word  *)
let () = stallocaux_add_rws [HD; TL];;

let STALLOCAUX_ev_stackloadany_suc = prove
 (`!r rn n (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\
     FLOOKUP (stack_state_regs s) rn =
       SOME (wl_Word (word_add (word_mul bytes_in_word (word n)) bytes_in_word)) /\
     good_dimindex(:A) /\ (dimindex(:A) DIV 8) * SUC n < dimword(:A) /\
     stack_state_stack_space s + SUC n < LENGTH (stack_state_stack s)
     ==> stack_evaluate (StackLoadAny r rn,s) =
         (NONE,stack_set_var r (EL (stack_state_stack_space s + SUC n)
                                   (stack_state_stack s)) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STALLOCAUX_ev_stackloadany_n THEN
  ASM_REWRITE_TAC[STALLOCAUX_bytes_suc]);;

let () = STALLOCAUX_leaf_lemmas :=
  STALLOCAUX_ev_stackloadany_suc :: !STALLOCAUX_leaf_lemmas;;

(* HOL4 line 1439 *)
let word_gc_move_roots_bitmaps_code_thm = prove
 (`!conf stack (init:((A)word_loc)list) bitmaps (s:(A,C,FFI)stack_state) i pa curr m dm
     (new:((A)word_loc)list) stack1 (a1:A word) i1 pa1 m1 old.
    word_gc_move_roots_bitmaps conf (stack,bitmaps,i,pa,curr,m,dm) =
      (stack1,i1,pa1,m1,T) /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_bitmaps s = bitmaps /\
    stack_state_use_stack s /\
    0 IN FDOM (stack_state_regs s) /\
    1 IN FDOM (stack_state_regs s) /\ 2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\ stack_get_var 4 s = SOME (wl_Word i) /\
    5 IN FDOM (stack_state_regs s) /\ 6 IN FDOM (stack_state_regs s) /\
    7 IN FDOM (stack_state_regs s) /\
    stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
    stack_get_var 9 s = SOME (HD stack) /\
    stack_state_stack s = APPEND (APPEND init old) stack /\
    stack_state_stack_space s = LENGTH init /\
    (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
    ?ck r0 r1 r2 r5 r6 r7 r8 (r9:(A)word_loc).
      stack_evaluate (word_gc_move_roots_bitmaps_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_stack_fupd (K (APPEND (APPEND init old) stack1))
                  (stack_state_clock_fupd (K (stack_state_clock s))
                    (stack_state_regs_fupd
                       (K (stack_state_regs s |++
                           [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                            (5,r5); (6,r6); (7,r7); (8,r8); (9,wl_Word (word 0))])) s))))`,
  (GEN_TAC THEN
    STALLOCAUX_MEASURE_INDUCT_TAC [`stack:((A)word_loc)list`] `LENGTH (stack:((A)word_loc)list)` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_move_roots_bitmaps o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_roots_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `stack:((A)word_loc)list` ["h";"t"] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    STALLOCAUX_ELIM_TAC [`stack:((A)word_loc)list`]) THEN
  (ASM_CASES_TAC `h = wl_Word (word 0):(A)word_loc` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      STALLOCAUX_ELIM_TAC [`stack1:((A)word_loc)list`; `i1:A word`; `pa1:A word`;
                           `m1:A word->(A)word_loc`; `t:((A)word_loc)list`; `h:(A)word_loc`] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[word_gc_move_roots_bitmaps_code_def] THEN
      STALLOCAUX_EV_TAC THEN STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC]) THEN
  (STALLOCAUX_OPT_CASES_TAC `word_gc_move_bitmaps conf (h,t:((A)word_loc)list,bitmaps,i,pa,curr,m,dm)`
      ["new2";"st2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots_bitmaps" ["st3";"i3";"pa3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`stack1:((A)word_loc)list`; `i1:A word`; `pa1:A word`;
                         `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `?c:A word. h = wl_Word c` (X_CHOOSE_THEN `c:A word` SUBST_ALL_TAC) THENL
     [MP_TAC(ISPEC `h:(A)word_loc` (cases "word_loc")) THEN STRIP_TAC THENL
       [POP_ASSUM(fun th -> EXISTS_TAC (rand(rhs(concl th))) THEN ACCEPT_TAC th);
        POP_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_bitmaps"
           with Failure _ -> false))) THEN
        REWRITE_TAC[word_gc_move_bitmaps_Loc; option_DISTINCT]];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP STALLOCAUX_bitmaps_nonzero o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_bitmaps"
      with Failure _ -> false))) THEN
  (REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_gc_move_bitmaps_LENGTH o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_bitmaps"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_move_roots_bitmaps o check (fun th ->
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_roots_bitmaps"
       with Failure _ -> false) && free_in `st2:((A)word_loc)list` (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `st2:((A)word_loc)list` ["h2";"t2"] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    STALLOCAUX_ELIM_TAC [`st2:((A)word_loc)list`]) THEN
  (REWRITE_TAC[word_gc_move_roots_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `n:num`)) THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * SUC (LENGTH (old:((A)word_loc)list) +
                  LENGTH (new2:((A)word_loc)list)) < dimword(:A)` ASSUME_TAC THENL
     [MATCH_MP_TAC STALLOCAUX_mul_lt THEN
      EXISTS_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `EL (SUC ((LENGTH (init:((A)word_loc)list) + LENGTH (old:((A)word_loc)list)) +
                           LENGTH (new2:((A)word_loc)list)))
                     (APPEND init (APPEND old (CONS (wl_Word c) (APPEND new2 (CONS h2 t2))))) =
                  h2:(A)word_loc` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`APPEND init (APPEND old [wl_Word c:(A)word_loc])`; `new2:((A)word_loc)list`;
                     `h2:(A)word_loc`; `t2:((A)word_loc)list`] STALLOCAUX_EL_mid) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH; GSYM APPEND_ASSOC; APPEND; ADD_CLAUSES; ADD_ASSOC];
      ALL_TAC]) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gc_move_bitmaps" asl in
      (match args, res with
         [ww;stk;bms;i;pa;curr;m;dm], [nw;st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`; rand ww; bms;
                          rand ww; stk; s0; i; pa; curr; m; dm; nw; st; `a1:A word`; i1; pa1; m1;
                          `APPEND old [wl_Word c:(A)word_loc]`] word_gc_move_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` (X_CHOOSE_THEN `q9:(A)word_loc` ASSUME_TAC)))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      (USE_THEN "ih" (fun ih -> MP_TAC (SPEC `CONS (h2:(A)word_loc) t2` ih)) THEN
       (ANTS_TAC THENL
         [UNDISCH_TAC `LENGTH (t:((A)word_loc)list) =
                       LENGTH (new2:((A)word_loc)list) + LENGTH (CONS (h2:(A)word_loc) t2)` THEN
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          ALL_TAC]) THEN
       DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL [`init:((A)word_loc)list`; `bitmaps:(A word)list`; s0; `i2:A word`; `pa2:A word`;
                `curr:A word`; `m2:A word->(A)word_loc`; `dm:A word->bool`;
                `st3:((A)word_loc)list`; `i3:A word`; `pa3:A word`; `m3:A word->(A)word_loc`;
                `APPEND (APPEND old [wl_Word c:(A)word_loc]) new2`])) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gc_move_roots_bitmaps_code_def] th))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC));;

(* store words, word_gc_move of a word, word_shift facts, offset-0 loads  *)
let () = stallocaux_add_rws [distinctness "store_name"];;

(* the result of word_gc_move on a word is a word *)
let STALLOCAUX_word_gc_move_Word = prove
 (`!conf (g:A word) i pa old m dm w1 i1 pa1 m1 c1.
     word_gc_move conf (wl_Word g,i,pa,old,m,dm) = (w1,i1,pa1,m1,c1) ==>
     ?g1. w1 = wl_Word g1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gc_move_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  STALLOCAUX_SPLIT_FN_TAC "memcpy" ["pa2";"m2";"c2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* for a store key k with isWord (FAPPLY store k): choose the word (named), *)
(* add FLOOKUP store k = SOME (wl_Word x) (k IN FDOM store is an assumption) *)
(* and replace FAPPLY store k everywhere                                     *)
let STALLOCAUX_STORE_WORD_TAC (st:term) (k:term) (name:string) : tactic = fun (asl,w as g) ->
  let vty = el 1 (snd(dest_type(type_of st))) in
  let wty = mk_type("word",[hd(snd(dest_type vty))]) in
  let x = variant (freesl (w :: map (concl o snd) asl)) (mk_var(name,wty)) in
  let fap = mk_icomb(mk_icomb(`FAPPLY:(B,C)fmap->B->C`,st),k) in
  let isw = mk_icomb(`isWord:(A)word_loc->bool`,fap) in
  let eq = mk_eq(fap, mk_icomb(`wl_Word:A word->(A)word_loc`,x)) in
  let fl = mk_eq(mk_icomb(mk_icomb(`FLOOKUP:(B,C)fmap->B->C option`,st),k),
                 mk_icomb(`SOME:C->C option`, rand eq)) in
  (FIRST_X_ASSUM(X_CHOOSE_TAC x o REWRITE_RULE[isWord_thm] o check (fun th -> concl th = isw)) THEN
   SUBGOAL_THEN fl ASSUME_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if concl th = eq then SUBST_ALL_TAC th else NO_TAC)) g;;

(* the word_shift facts of good_dimindex (HOL4 proves them inline)       *)
let STALLOCAUX_good_dimindex_shift = prove
 (`good_dimindex (:A) ==>
   backend_common_word_shift (:A) < dimindex (:A) /\ 2 < dimindex (:A) /\
   (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word)`,
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; bytes_in_word_def;
              WORD_MUL_LSL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_ACCEPT_TAC WORD_MUL_SYM);;

(* StackLoadAny at stack offset 0 *)
let STALLOCAUX_ev_stackloadany_0 = prove
 (`!r rn (s:(A,C,FFI)stack_state).
     stack_state_use_stack s /\
     FLOOKUP (stack_state_regs s) rn = SOME (wl_Word (word 0)) /\
     stack_state_stack_space s < LENGTH (stack_state_stack s)
     ==> stack_evaluate (StackLoadAny r rn,s) =
         (NONE,stack_set_var r (EL (stack_state_stack_space s) (stack_state_stack s)) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:num`; `rn:num`; `word 0:A word`; `s:(A,C,FFI)stack_state`]
           STALLOCAUX_ev_stackloadany) THEN
  ASM_REWRITE_TAC[WORD_USHR_0; WORD_SHL_0; VAL_WORD_0; ADD_CLAUSES]);;

let () = STALLOCAUX_leaf_lemmas :=
  STALLOCAUX_ev_stackloadany_0 :: !STALLOCAUX_leaf_lemmas;;

let () = stallocaux_add_rws [LBIGAUX_EL_LENGTH_CONS];;

(* HOL4 line 1577 *)
let alloc_correct_lemma_Simple = prove
 (`!w (s:(A,C,FFI)stack_state) r t conf l ret anything c.
   stackSem_alloc w s = (r,t) /\ ~(r = SOME stack_Error) /\
   stack_state_gc_fun s = word_gc_fun conf /\
   data_to_word_config_gc_kind conf = data_to_word_Simple /\
   LENGTH (stack_state_bitmaps s) < dimword (:A) - 1 /\
   LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
   FLOOKUP l 0 = SOME ret /\
   FLOOKUP l 1 = SOME (wl_Word w) ==>
   ?ck l2.
     stack_evaluate
       (word_gc_code conf,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_clock_fupd (K (stack_state_clock s + ck))
        (stack_state_regs_fupd (K l)
        (stack_state_gc_fun_fupd (K anything)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))) =
       (r,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
        (stack_state_regs_fupd (K l2)
        (stack_state_gc_fun_fupd (K anything) t)))))) /\
     (~(r = NONE) ==> r = SOME (stackSem_Halt (wl_Word (word 1)))) /\
     stack_state_regs t SUBMAP l2 /\
     (r = NONE ==> FLOOKUP l2 0 = SOME ret)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stackSem_alloc"
       with Failure _ -> false))) THEN
    REWRITE_TAC[stackSem_alloc_def] THEN
    MP_TAC(ISPECL [`conf:data_to_word_config`;
                   `stack_set_store AllocSize (wl_Word w) (s:(A,C,FFI)stack_state)`] gc_thm) THEN
    (ANTS_TAC THENL [CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[];
                     DISCH_THEN SUBST1_TAC]) THEN
    CONV_TAC (stallocaux_norm [])) THEN
  (COND_CASES_TAC THENL
     [CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_roots_bitmaps" ["stk2";"i2";"pa2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gc_move_loop" ["i3";"pa3";"m3";"c3"]) THEN
  (REWRITE_TAC[FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
    COND_CASES_TAC THENL
     [ALL_TAC; CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[word_gc_fun_assum_def; FDOM_FUPDATE; INSERT_SUBSET; IN_INSERT;
                FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
    STRIP_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[FAPPLY_FUPDATE_THM; distinctness "store_name"]) THEN
    MAP_EVERY (fun (k,n) ->
       STALLOCAUX_STORE_WORD_TAC `stack_state_store (s:(A,C,FFI)stack_state)` k n)
      [`OtherHeap`,"other"; `CurrHeap`,"curr"; `HeapLength`,"len"; `Globals`,"g"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[theWord_def]) THEN REWRITE_TAC[theWord_def] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_move_loop_ok o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_loop"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `g1:A word` SUBST_ALL_TAC o MATCH_MP STALLOCAUX_word_gc_move_Word o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move"
                       with Failure _ -> false)) THEN
    MP_TAC(ISPECL [`stack_state_stack (s:(A,C,FFI)stack_state)`; `stack_state_stack_space (s:(A,C,FFI)stack_state)`] LESS_EQ_LENGTH) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ys1:((A)word_loc)list` (X_CHOOSE_THEN `ys2:((A)word_loc)list`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                               lhs(concl th) = `stack_state_stack (s:(A,C,FFI)stack_state)`
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
      else NO_TAC)) THEN
  (REPEAT (FIRST_X_ASSUM(fun th -> if concl th = `T` then ALL_TAC else NO_TAC)) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs(concl th) = `LENGTH (ys1:((A)word_loc)list)`
      then REWRITE_TAC[GSYM th] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
           ASSUME_TAC (GSYM th)
      else NO_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAKE_LENGTH_APPEND; DROP_LENGTH_APPEND]) THEN
    REWRITE_TAC[TAKE_LENGTH_APPEND; DROP_LENGTH_APPEND] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[stack_has_space_def] THEN
    CONV_TAC (stallocaux_norm [])) THEN
  (DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
      then STRIP_ASSUME_TAC (MATCH_MP STALLOCAUX_good_dimindex_shift th) else NO_TAC) THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * LENGTH (APPEND ys1 (ys2:((A)word_loc)list)) <
                  dimword(:A)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_move_roots_bitmaps o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gc_move_roots_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `ys2:((A)word_loc)list` ["h";"t"] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    STALLOCAUX_ELIM_TAC [`ys2:((A)word_loc)list`]) THEN
  (REWRITE_TAC[word_gc_code_def;
                ASSUME `data_to_word_config_gc_kind conf = data_to_word_Simple`] THEN
    CASE_REWRITE_TAC[] THEN STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gc_move" asl in
      (match args, res with
         [x;i;pa;old;m;dm], [w1;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`;x;i;pa;old;m;dm;w1;i1;pa1;m1;s0]
                    word_gc_move_code_thm)
       | _ -> failwith "args") g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + ck2` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gc_move_roots_bitmaps" asl in
      (match args, res with
         [stk;bms;i;pa;curr;m;dm], [st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; stk; `ys1:((A)word_loc)list`; bms; s0;
                          i; pa; curr; m; dm; `[]:((A)word_loc)list`; st; `word 0:A word`;
                          i1; pa1; m1; `[]:((A)word_loc)list`]
                    word_gc_move_roots_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `u0:(A)word_loc`
      (X_CHOOSE_THEN `u1:(A)word_loc` (X_CHOOSE_THEN `u2:(A)word_loc`
      (X_CHOOSE_THEN `u5:(A)word_loc` (X_CHOOSE_THEN `u6:(A)word_loc`
      (X_CHOOSE_THEN `u7:(A)word_loc` (X_CHOOSE_THEN `u8:(A)word_loc`
      (X_CHOOSE_THEN `u9:(A)word_loc` ASSUME_TAC))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck4. ck3 + ck4` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck4:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gc_move_loop" asl in
      (match args, res with
         [pb;i;pa;old;m;dm;c1], [i1;pa1;m1;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP]
             (ISPECL [`conf:data_to_word_config`; `dimword(:A)`; pb; i; pa; old; m; dm; c1;
                      i1; pa1; m1; s0] word_gc_move_loop_code_thm))
       | _ -> failwith "args") g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck5:num` (X_CHOOSE_THEN `v0:(A)word_loc`
      (X_CHOOSE_THEN `v1:(A)word_loc` (X_CHOOSE_THEN `v2:(A)word_loc`
      (X_CHOOSE_THEN `v5:(A)word_loc` (X_CHOOSE_THEN `v6:(A)word_loc`
      (X_CHOOSE_THEN `v7:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck6. ck5 + ck6` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck6:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  (EXISTS_TAC `0` THEN
    ASM_CASES_TAC `val (w:A word) <= val (word_sub (word_add other len) (pa3:A word))` THENL
     [SUBGOAL_THEN `~(word_ult (word_sub (word_add len other) pa3) (w:A word))` ASSUME_TAC THENL
       [REWRITE_TAC[word_ult; relational2] THEN ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN ASM_ARITH_TAC; ALL_TAC];
      SUBGOAL_THEN `word_ult (word_sub (word_add len other) pa3) (w:A word)` ASSUME_TAC THENL
       [REWRITE_TAC[word_ult; relational2] THEN ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN ASM_ARITH_TAC; ALL_TAC]] THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_cond (lhs (concl th))
      then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    STALLOCAUX_EV_TAC) THENL
  [((fun (asl,w as g) ->
       let _,body = dest_exists w in
       let eq = hd (conjuncts body) in
       let s1 = snd (dest_pair (lhs eq)) in
       EXISTS_TAC (rand (rand (rator s1))) g) THEN
    SUBGOAL_THEN `word_add len other = word_add other (len:A word)` ASSUME_TAC THENL
     [MATCH_ACCEPT_TAC WORD_ADD_SYM; ALL_TAC] THEN
    SUBGOAL_THEN `glob_real conf other (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (other:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC);
   (EXISTS_TAC `FEMPTY:(num,(A)word_loc)fmap` THEN
    SUBGOAL_THEN `word_add len other = word_add other (len:A word)` ASSUME_TAC THENL
     [MATCH_ACCEPT_TAC WORD_ADD_SYM; ALL_TAC] THEN
    SUBGOAL_THEN `glob_real conf other (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (other:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN
    CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY; option_DISTINCT]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC)]);;
