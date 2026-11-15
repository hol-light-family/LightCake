(* ========================================================================= *)
(* stack_removeProof: port of HOL4 compiler/backend/proofs/                  *)
(* stack_removeProofScript.sml (CakeML v3479).                               *)
(* Correctness proof for stack_remove.                                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/set_sep.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/proofs/stack_rawcallProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 set_sep: one = set_sep_one, * = STAR, word_list = misc_word_list.  *)
(* - HOL4 words: n2w = word, w2n = val, + = word_add, * = word_mul,          *)
(*   - = word_sub, -1w * x = word_mul (word_neg (word 1)) x,                 *)
(*   << = word_shl, >>> = word_ushr, <+ = word_ult, <=+ = word_ule,          *)
(*   word_shift (:'a) = backend_common_word_shift (:A).                      *)
(* - HOL4 semanticsProps (an Ancestor) is not needed by any proof here.     *)
(* - STACKPROPSAUX_ names are local helpers (the unit's helper prefix).      *)
(* - stack_rawcallProof (same unit) is loaded for its generic stackSem      *)
(*   lemmas STACKPROPSAUX_semantics_sim and STACKPROPSAUX_dest_Seq_SOME.     *)

(* HOL4 line 21 *)
let stack_removeProof_word_list_exists_thm = prove
 (`(!a:A word. word_list_exists a 0 = (emp:(A word#B->bool)->bool)) /\
   (!(a:A word) n.
      word_list_exists a (SUC n) =
      SEP_EXISTS w:B. set_sep_one (a,w) STAR word_list_exists (word_add a bytes_in_word) n)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[word_list_exists_def; SEP_CLAUSES] THEN
  REWRITE_TAC[FUN_EQ_THM; SEP_EXISTS_THM; STAR_ASSOC; cond_STAR] THEN
  REWRITE_TAC[LENGTH_EQ_NIL; LENGTH_EQ_CONS] THENL
   [REWRITE_TAC[UNWIND_THM2; misc_word_list_def]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM2; misc_word_list_def] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`h:B`; `t:B list`] THEN
    UNDISCH_TAC `misc_word_list (a:A word) (xs:B list) x` THEN
    ASM_REWRITE_TAC[misc_word_list_def];
    MAP_EVERY EXISTS_TAC [`CONS (w:B) xs`; `w:B`; `xs:B list`] THEN
    ASM_REWRITE_TAC[misc_word_list_def]]);;

(* HOL4 line 38 *)
let stack_removeProof_word_list_exists_ADD = prove
 (`!m n (a:A word).
     (word_list_exists a (m + n):(A word#B->bool)->bool) =
     word_list_exists a m STAR
     word_list_exists (word_add a (word_mul bytes_in_word (word m))) n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; stack_removeProof_word_list_exists_thm; SEP_CLAUSES;
                WORD_RULE `word_add (a:A word) (word_mul b (word 0)) = a`];
    ASM_REWRITE_TAC[ADD_CLAUSES; stack_removeProof_word_list_exists_thm; SEP_CLAUSES] THEN
    REWRITE_TAC[STAR_ASSOC] THEN REPEAT GEN_TAC THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC ORELSE ABS_TAC) THEN
    REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 49 *)
let stack_removeProof_word_list_APPEND = prove
 (`!(xs:B list) ys (a:A word).
     misc_word_list a (APPEND xs ys) =
     misc_word_list a xs STAR
     misc_word_list (word_add a (word_mul bytes_in_word (word (LENGTH xs)))) ys`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; misc_word_list_def; LENGTH; SEP_CLAUSES] THENL
   [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 58 *)
let stack_removeProof_LESS_LENGTH_IMP_APPEND = prove
 (`!(xs:A list) n. n < LENGTH xs ==> ?ys zs. xs = APPEND ys zs /\ LENGTH ys = n`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE n (xs:A list)`; `DROP n (xs:A list)`] THEN
  ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE; LT_IMP_LE]);;

(* HOL4 line 67 *)
let stack_removeProof_call_FFI_LENGTH = prove
 (`!(s:(FFI)ffi_state) i conf xs n ys.
     call_FFI s i conf xs = FFI_return n ys ==> LENGTH ys = LENGTH xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[injectivity "ffi_result"; distinctness "ffi_result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 74 (simp) *)
let stack_removeProof_with_same_clock = prove
 (`!x:(A,C,FFI)stack_state. stack_state_clock_fupd (K (stack_state_clock x)) x = x`,
  REWRITE_TAC[stack_state_component_equality] THEN SIMP[]);;

(* HOL4 line 81 (simp) *)
let stack_removeProof_set_var_set_var = prove
 (`!x (y:(A)word_loc) z (w:(A,C,FFI)stack_state).
     stack_set_var x y (stack_set_var x z w) = stack_set_var x y w`,
  REWRITE_TAC[stack_set_var_def] THEN SIMP[FUPDATE_EQ]);;

(* HOL4 line 87 (simp) *)
let get_var_set_var_same = prove
 (`!x (y:(A)word_loc) (z:(A,C,FFI)stack_state).
     stack_get_var x (stack_set_var x y z) = SOME y`,
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE]);;

(* HOL4 line 93 *)
let stack_removeProof_get_var_set_var = prove
 (`!x x' (y:(A)word_loc) (z:(A,C,FFI)stack_state).
     stack_get_var x (stack_set_var x' y z) =
     if x = x' then SOME y else stack_get_var x z`,
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN
  MESON_TAC[]);;

(* local helper: under good_dimindex, bytes_in_word is 2 EXP word_shift *)

let STACKPROPSAUX_val_bytes_in_word = prove
 (`good_dimindex (:A)
   ==> val (bytes_in_word:A word) = 2 EXP backend_common_word_shift (:A) /\
       dimindex (:A) DIV 8 = 2 EXP backend_common_word_shift (:A)`,
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; bytes_in_word_def;
              VAL_WORD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 99 *)
let stack_removeProof_bytes_in_word_word_shift = prove
 (`!n:A word.
     good_dimindex(:A) /\ val (bytes_in_word:A word) * val n < dimword(:A)
     ==> word_ushr (word_mul (bytes_in_word:A word) n) (backend_common_word_shift (:A)) = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_val_bytes_in_word) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_MUL] THEN
  UNDISCH_TAC `val (bytes_in_word:A word) * val (n:A word) < dimword (:A)` THEN
  ASM_REWRITE_TAC[dimword_def] THEN DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

(* HOL4 line 112 *)
let word_offset_eq = prove
 (`!n. word_offset n = word_mul (bytes_in_word:A word) (word n)`,
  REWRITE_TAC[word_offset_def; bytes_in_word_def; WORD_MUL]);;

(* HOL4 line 118 *)
let memory_def = cake_def
  `memory (m:A->B) dm = \s. s = fun2set (m,dm)`;;

(* HOL4 line 122 *)
let word_list_rev_def = cake_def
  `(word_list_rev (a:A word) ([]:B list) = emp) /\
   (word_list_rev a (CONS x xs) =
      set_sep_one (word_sub a bytes_in_word,x) STAR
      word_list_rev (word_sub a bytes_in_word) xs)`;;

(* HOL4 line 128 *)
let word_store_def = cake_def
  `word_store (base:A word) (store:(store_name,(A)word_loc)fmap) =
     word_list_rev base
       (MAP (\name. match FLOOKUP store name with
                      NONE -> wl_Word (word 0)
                    | SOME x -> x) stack_remove_store_list)`;;

(* HOL4 line 135 *)
let stack_removeProof_code_rel_def = cake_def
  `stack_removeProof_code_rel jump off k (code1:((A)stack_prog)spt) code2 <=>
     (!n prog.
        lookup n code1 = SOME prog ==>
        reg_bound prog k /\
        lookup n code2 = SOME (stack_remove_comp jump off k prog)) /\
     domain code2 = domain code1 UNION {0,1,2}`;;

(* HOL4 line 144 *)
let is_SOME_Word_def = cake_def
  `(is_SOME_Word (SOME (wl_Word (w:A word))) <=> T) /\
   (is_SOME_Word _ <=> F)`;;

(* HOL4 line 149 *)
let the_SOME_Word_def = cake_def
  `the_SOME_Word (SOME (wl_Word (w:A word))) = w`;;

(* HOL4 line 153 *)
let stack_removeProof_state_rel_def = cake_def
  `stack_removeProof_state_rel jump off k (s1:(A,C,FFI)stack_state)
                               (s2:(A,C,FFI)stack_state) <=>
     stack_state_use_stack s1 /\ stack_state_use_store s1 /\
     ~stack_state_use_stack s2 /\ ~stack_state_use_store s2 /\
     ~stack_state_use_alloc s2 /\ ~stack_state_use_alloc s1 /\
     stack_state_be s2 = stack_state_be s1 /\
     stack_state_gc_fun s2 = stack_state_gc_fun s1 /\
     stack_state_clock s2 = stack_state_clock s1 /\
     stack_state_ffi s2 = stack_state_ffi s1 /\
     stack_state_ffi_save_regs s2 = stack_state_ffi_save_regs s1 /\
     stack_state_fp_regs s2 = stack_state_fp_regs s1 /\
     stack_state_code_buffer s2 = stack_state_code_buffer s1 /\
     stack_state_sh_mdomain s2 = stack_state_sh_mdomain s1 /\
     stack_state_compile s1 =
       (\c p. stack_state_compile s2 c (MAP (stack_remove_prog_comp jump off k) p)) /\
     stack_state_compile_oracle s2 =
       (\n. ((I ## MAP (stack_remove_prog_comp jump off k) ## I)
               (stack_state_compile_oracle s1 n))) /\
     (!n i p. MEM (i,p) (FST (SND (stack_state_compile_oracle s1 n)))
              ==> reg_bound p k /\ stack_num_stubs <= i + 1) /\
     good_dimindex (:A) /\
     (!n. n < k ==> FLOOKUP (stack_state_regs s2) n = FLOOKUP (stack_state_regs s1) n) /\
     stack_removeProof_code_rel jump off k (stack_state_code s1) (stack_state_code s2) /\
     lookup stack_err_lab (stack_state_code s2) = SOME (halt_inst (word 2)) /\
     FLOOKUP (stack_state_regs s2) (k + 2) = FLOOKUP (stack_state_store s1) CurrHeap /\
     {k, k + 1, k + 2} SUBSET stack_state_ffi_save_regs s2 /\
     is_SOME_Word (FLOOKUP (stack_state_store s1) BitmapBase) /\
     stack_state_stack_space s1 <= LENGTH (stack_state_stack s1) /\
     (let bp = word_shl (the_SOME_Word (FLOOKUP (stack_state_store s1) BitmapBase))
                        (backend_common_word_shift (:A)) in
      let all_bitmaps = APPEND (stack_state_bitmaps s1)
                               (buffer_buffer (stack_state_data_buffer s1)) in
        buffer_position (stack_state_data_buffer s1) =
          word_add bp (word_mul bytes_in_word (word (LENGTH (stack_state_bitmaps s1)))) /\
        (match FLOOKUP (stack_state_regs s2) (k + 1) with
           SOME (wl_Word base) ->
             dimindex (:A) DIV 8 * max_stack_alloc <= val base /\
             val base + val (bytes_in_word:A word) * LENGTH (stack_state_stack s1) <
               dimword (:A) /\
             FLOOKUP (stack_state_regs s2) k =
               SOME (wl_Word (word_add base (word_mul bytes_in_word
                                (word (stack_state_stack_space s1))))) /\
             (memory (stack_state_memory s1) (stack_state_mdomain s1) STAR
              misc_word_list bp (MAP wl_Word all_bitmaps) STAR
              word_list_exists
                (word_add bp (word_mul bytes_in_word (word (LENGTH all_bitmaps))))
                (buffer_space_left (stack_state_data_buffer s1)) STAR
              word_store base (stack_state_store s1) STAR
              misc_word_list base (stack_state_stack s1))
               (fun2set (stack_state_memory s2,stack_state_mdomain s2))
         | _ -> F))`;;

(* HOL4 line 198 (local) *)
let state_rel_get_var = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t n.
     stack_removeProof_state_rel jump off k s t /\ n < k
     ==> stack_get_var n s = stack_get_var n t`,
  REWRITE_TAC[stack_removeProof_state_rel_def; stack_get_var_def] THEN MESON_TAC[]);;

let STACKPROPSAUX_SR_ACC = CONJ stack_state_INFO.ri_accfupds K_THM;;

(* HOL4 line 204 (local) *)
let state_rel_IMP = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t1.
     stack_removeProof_state_rel jump off k s t1
     ==> stack_removeProof_state_rel jump off k (stack_dec_clock s) (stack_dec_clock t1)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; stack_dec_clock_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 212 (local) *)
let stack_removeProof_state_rel_with_clock = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t1 c.
     stack_removeProof_state_rel jump off k s t1
     ==> stack_removeProof_state_rel jump off k (stack_state_clock_fupd (K c) s)
                                     (stack_state_clock_fupd (K c) t1)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;
(* HOL4 line 220 *)
let stack_removeProof_state_rel_const = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> stack_state_code_buffer t = stack_state_code_buffer s /\
         stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
         ~stack_state_use_stack t /\ stack_state_use_stack s /\
         stack_state_ffi t = stack_state_ffi s /\
         stack_state_compile_oracle t =
           (\n. ((I ## MAP (stack_remove_prog_comp jump off k) ## I)
                   (stack_state_compile_oracle s n))) /\
         stack_state_compile s =
           (\c p. stack_state_compile t c (MAP (stack_remove_prog_comp jump off k) p))`,
  REWRITE_TAC[stack_removeProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* the facts of state_rel about code and registers *)

let STACKPROPSAUX_sr_code_regs = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> stack_removeProof_code_rel jump off k (stack_state_code s) (stack_state_code t) /\
         (!n. n < k ==> FLOOKUP (stack_state_regs t) n = FLOOKUP (stack_state_regs s) n)`,
  REWRITE_TAC[stack_removeProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 231 (local) *)
let stack_removeProof_find_code_lemma = prove
 (CASE_TERM
  `!jump off k (s:(A,C,FFI)stack_state) t1 dest x.
     stack_removeProof_state_rel jump off k s t1 /\
     (match dest with INL v2 -> T | INR i -> i < k) /\
     stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME x
     ==> stack_find_code dest (stack_state_regs t1) (stack_state_code t1) =
           SOME (stack_remove_comp jump off k x) /\
         reg_bound x k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> b ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP STACKPROPSAUX_sr_code_regs) THEN
  REWRITE_TAC[stack_removeProof_code_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "code") (K ALL_TAC))
                             (LABEL_TAC "regs")) THEN
  CASES_ON `dest:num+num` THEN REWRITE_TAC[stack_find_code_def] THEN CASE_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "regs" (fun th -> FIRST_ASSUM(fun lt -> REWRITE_TAC[MATCH_MP th lt])) THEN
  POP_ASSUM MP_TAC THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

(* HOL4 line 243 (local) *)
let find_code_lemma2 = prove
 (CASE_TERM
  `!jump off k (s:(A,C,FFI)stack_state) t1 dest x x1.
     stack_removeProof_state_rel jump off k s t1 /\
     (match dest with INL v2 -> T | INR i -> i < k) /\
     stack_find_code dest (fdomsub (stack_state_regs s) x1) (stack_state_code s) = SOME x
     ==> stack_find_code dest (fdomsub (stack_state_regs t1) x1) (stack_state_code t1) =
           SOME (stack_remove_comp jump off k x) /\
         reg_bound x k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> b ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP STACKPROPSAUX_sr_code_regs) THEN
  REWRITE_TAC[stack_removeProof_code_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "code") (K ALL_TAC))
                             (LABEL_TAC "regs")) THEN
  CASES_ON `dest:num+num` THEN REWRITE_TAC[stack_find_code_def; DOMSUB_FLOOKUP_THM] THEN
  CASE_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "regs" (fun th -> FIRST_ASSUM(fun lt -> REWRITE_TAC[MATCH_MP th lt])) THEN
  POP_ASSUM MP_TAC THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

(* HOL4 line 257 (simp) *)
let stack_removeProof_state_rel_set_var = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t1 v x.
     stack_removeProof_state_rel jump off k s t1 /\ v < k
     ==> stack_removeProof_state_rel jump off k (stack_set_var v x s) (stack_set_var v x t1)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; stack_set_var_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v = k) /\ ~(v = k + 1) /\ ~(v = k + 2)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 line 266 (local) *)
let word_store_CurrHeap = prove
 (`!(base:A word) (s:(A,C,FFI)stack_state) x.
     word_store base (stack_state_store s |+ (CurrHeap,x)) =
     word_store base (stack_state_store s)`,
  REWRITE_TAC[word_store_def; stack_remove_store_list_def; MAP; FLOOKUP_UPDATE;
              distinctness "store_name"]);;

(* HOL4 line 272 (local) *)
let memory_fun2set_IMP_read = prove
 (`!(m:A->B) d p m1 d1 a.
     (memory m d STAR p) (fun2set (m1,d1)) /\ a IN d ==> a IN d1 /\ m1 a = m a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STAR_def; SPLIT_EQ; memory_def] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(u:A#B->bool) SUBSET fun2set (m1,d1)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_fun2set] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:A`; `(m:A->B) a`]) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* the simple facts of state_rel *)

let STACKPROPSAUX_sr_facts = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> stack_state_use_stack s /\ stack_state_use_store s /\
         ~stack_state_use_stack t /\ ~stack_state_use_store t /\
         ~stack_state_use_alloc t /\ ~stack_state_use_alloc s /\
         stack_state_be t = stack_state_be s /\
         stack_state_gc_fun t = stack_state_gc_fun s /\
         stack_state_clock t = stack_state_clock s /\
         stack_state_ffi t = stack_state_ffi s /\
         stack_state_ffi_save_regs t = stack_state_ffi_save_regs s /\
         stack_state_fp_regs t = stack_state_fp_regs s /\
         stack_state_code_buffer t = stack_state_code_buffer s /\
         stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
         good_dimindex (:A)`,
  REWRITE_TAC[stack_removeProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* the memory part of state_rel *)

let STACKPROPSAUX_sr_memory = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> ?p. (memory (stack_state_memory s) (stack_state_mdomain s) STAR p)
               (fun2set (stack_state_memory t,stack_state_mdomain t))`,
  REWRITE_TAC[stack_removeProof_state_rel_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN MESON_TAC[]);;

(* HOL4 line 280 (local) *)
let state_rel_read = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t a.
     stack_removeProof_state_rel jump off k s t /\ a IN stack_state_mdomain s
     ==> a IN stack_state_mdomain t /\ stack_state_memory t a = stack_state_memory s a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:(A word#(A)word_loc->bool)->bool` o
    MATCH_MP STACKPROPSAUX_sr_memory) THEN
  ASM_MESON_TAC[memory_fun2set_IMP_read]);;

(* HOL4 line 288 (local) *)
let mem_load_32_IMP = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t a x.
     stack_removeProof_state_rel jump off k s t /\
     mem_load_32 (stack_state_memory s) (stack_state_mdomain s) (stack_state_be s) a = SOME x
     ==> mem_load_32 (stack_state_memory t) (stack_state_mdomain t) (stack_state_be t) a =
           SOME x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  ASM_CASES_TAC `byte_align (a:A word) IN stack_state_mdomain (s:(A,C,FFI)stack_state)` THENL
   [MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                   `t:(A,C,FFI)stack_state`; `byte_align (a:A word)`] state_rel_read) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `mem_load_32 (stack_state_memory s) (stack_state_mdomain s)
                   (stack_state_be (s:(A,C,FFI)stack_state)) (a:A word) = SOME x` THEN
    ASM_REWRITE_TAC[mem_load_32_def];
    UNDISCH_TAC `mem_load_32 (stack_state_memory s) (stack_state_mdomain s)
                   (stack_state_be (s:(A,C,FFI)stack_state)) (a:A word) = SOME x` THEN
    ASM_REWRITE_TAC[mem_load_32_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[option_DISTINCT]]);;

(* HOL4 line 301 (local) *)
let mem_load_byte_aux_IMP = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t a x.
     stack_removeProof_state_rel jump off k s t /\
     mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s) (stack_state_be s) a =
       SOME x
     ==> mem_load_byte_aux (stack_state_memory t) (stack_state_mdomain t) (stack_state_be t) a =
           SOME x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  ASM_CASES_TAC `byte_align (a:A word) IN stack_state_mdomain (s:(A,C,FFI)stack_state)` THENL
   [MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                   `t:(A,C,FFI)stack_state`; `byte_align (a:A word)`] state_rel_read) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                   (stack_state_be (s:(A,C,FFI)stack_state)) (a:A word) = SOME x` THEN
    ASM_REWRITE_TAC[mem_load_byte_aux_def];
    UNDISCH_TAC `mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                   (stack_state_be (s:(A,C,FFI)stack_state)) (a:A word) = SOME x` THEN
    ASM_REWRITE_TAC[mem_load_byte_aux_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[option_DISTINCT]]);;

(* HOL4 line 313 (local) *)
let read_bytearray_IMP_read_bytearray = prove
 (`!jump off n a k (s:(A,C,FFI)stack_state) t x.
     stack_removeProof_state_rel jump off k s t /\
     read_bytearray a n
       (mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s) (stack_state_be s)) =
       SOME x
     ==> read_bytearray a n
           (mem_load_byte_aux (stack_state_memory t) (stack_state_mdomain t)
                              (stack_state_be t)) = SOME x`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[read_bytearray_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  CASES_ON `mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
              (stack_state_be (s:(A,C,FFI)stack_state)) (a:A word)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP mem_load_byte_aux_IMP
    (CONJ (ASSUME `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t`) th)]) THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `read_bytearray (word_add (a:A word) (word 1)) n
              (mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                 (stack_state_be (s:(A,C,FFI)stack_state)))` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ih
    (CONJ (ASSUME `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t`) th)])) THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 324 (local) *)
let write_bytearray_IGNORE_non_aligned = prove
 (`!new_bytes (a:A word) m d be b.
     (!x. ~(b = byte_align x)) ==> write_bytearray a new_bytes m d be b = m b`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN
  SUBGOAL_THEN `~(byte_align (a:A word) = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN ASM_MESON_TAC[]);;

(* HOL4 line 334 (local) *)
let write_bytearray_IGNORE = prove
 (`!new_bytes (a:A word) x xx d1 d m1 m be.
     d1 SUBSET d /\
     read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x /\
     ~(xx IN d1)
     ==> write_bytearray a new_bytes m d be xx = m xx`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def; LENGTH; read_bytearray_def] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `mem_load_byte_aux (m1:A word->(A)word_loc) d1 be (a:A word)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `read_bytearray (word_add (a:A word) (word 1)) (LENGTH (t:byte list))
              (mem_load_byte_aux (m1:A word->(A)word_loc) d1 be)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `byte_align (a:A word) IN d1` ASSUME_TAC THENL
   [UNDISCH_TAC `mem_load_byte_aux (m1:A word->(A)word_loc) d1 be (a:A word) = SOME a'` THEN
    REWRITE_TAC[mem_load_byte_aux_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(byte_align (a:A word) = xx)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `write_bytearray (word_add (a:A word) (word 1)) t m d be xx = m xx`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM]);;

let STACKPROPSAUX_read_bytearray_SUC = prove
 (`!(a:A word) n (f:A word->B option) y.
     read_bytearray a (SUC n) f = SOME y
     ==> ?b bs. f a = SOME b /\ read_bytearray (word_add a (word 1)) n f = SOME bs /\
                y = CONS b bs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[read_bytearray_def] THEN
  CASES_ON `(f:A word->B option) a` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `read_bytearray (word_add (a:A word) (word 1)) n (f:A word->B option)` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 349 (local) *)
let write_bytearray_EQ = prove
 (`!new_bytes (a:A word) m1 m y x d1 d be.
     d1 SUBSET d /\ (!a. a IN d1 ==> m1 a = m a /\ a IN d) /\
     read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME y /\
     m1 x = m x
     ==> write_bytearray a new_bytes m1 d1 be x = write_bytearray a new_bytes m d be x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def; LENGTH] THENL
   [SIMP_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_read_bytearray_SUC) THEN
  SUBGOAL_THEN `byte_align (a:A word) IN d1` ASSUME_TAC THENL
   [UNDISCH_TAC `mem_load_byte_aux (m1:A word->(A)word_loc) d1 be (a:A word) = SOME b` THEN
    REWRITE_TAC[mem_load_byte_aux_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `byte_align (a:A word) IN d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. (m1:A word->(A)word_loc) z = m z
                    ==> write_bytearray (word_add (a:A word) (word 1)) t m1 d1 be z =
                        write_bytearray (word_add a (word 1)) t m d be z`
    (LABEL_TAC "ih") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `write_bytearray (word_add (a:A word) (word 1)) t m1 d1 be (byte_align a) =
                write_bytearray (word_add a (word 1)) t m d be (byte_align a)`
    ASSUME_TAC THENL
   [USE_THEN "ih" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `write_bytearray (word_add (a:A word) (word 1)) t m d be (byte_align a)` THEN
  CASE_REWRITE_TAC[APPLY_UPDATE_THM] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 372 (local) *)
let write_bytearray_lemma = prove
 (`!new_bytes (a:A word) m1 d1 be x p m d.
     (memory m1 d1 STAR p) (fun2set (m,d)) /\
     read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x
     ==> (memory (write_bytearray a new_bytes m1 d1 be) d1 STAR p)
           (fun2set (write_bytearray a new_bytes m d be,d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STAR_def; SPLIT_EQ; memory_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a:A word. a IN d1 ==> (m1:A word->(A)word_loc) a = m a /\ a IN d` (LABEL_TAC "f1") THENL
   [UNDISCH_TAC `(u:A word#(A)word_loc->bool) SUBSET fun2set (m,d)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_fun2set] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d1:A word->bool) SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:A word. z IN d1
                  ==> write_bytearray a new_bytes (m1:A word->(A)word_loc) d1 be z =
                      write_bytearray a new_bytes m d be z`
    (LABEL_TAC "f2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC write_bytearray_EQ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:A word. ~(z IN d1)
                  ==> write_bytearray a new_bytes (m:A word->(A)word_loc) d be z = m z`
    (LABEL_TAC "f3") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC write_bytearray_IGNORE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`fun2set (write_bytearray a new_bytes (m1:A word->(A)word_loc) d1 be,d1:A word->bool)`;
    `v:A word#(A)word_loc->bool`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_fun2set] THEN
    MAP_EVERY X_GEN_TAC [`z:A word`; `w:(A)word_loc`] THEN STRIP_TAC THEN
    USE_THEN "f2" (fun th -> ASM_SIMP_TAC[th]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_DIFF; IN_fun2set] THEN
  MAP_EVERY X_GEN_TAC [`z:A word`; `w:(A)word_loc`] THEN
  ASM_CASES_TAC `(z:A word) IN d1` THENL
   [USE_THEN "f1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(z:A word) IN d1`))) THEN
    USE_THEN "f2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:A word) IN d1`)]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    USE_THEN "f3" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((z:A word) IN d1)`)]) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 395 *)
let state_rel_get_var_k = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> ?c:A word.
           stack_get_var (k + 1) t = SOME (wl_Word c) /\
           dimindex (:A) DIV 8 * max_stack_alloc <= val c /\
           val c + val (bytes_in_word:A word) * LENGTH (stack_state_stack s) < dimword (:A) /\
           stack_get_var k t =
             SOME (wl_Word (word_add c (word_mul bytes_in_word
                                          (word (stack_state_stack_space s))))) /\
           (memory (stack_state_memory s) (stack_state_mdomain s) STAR
            misc_word_list
              (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                        (backend_common_word_shift (:A)))
              (APPEND (MAP wl_Word (stack_state_bitmaps s))
                      (MAP wl_Word (buffer_buffer (stack_state_data_buffer s)))) STAR
            word_list_exists
              (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                                  (backend_common_word_shift (:A)))
                        (word_mul bytes_in_word
                           (word (LENGTH (buffer_buffer (stack_state_data_buffer s)) +
                                  LENGTH (stack_state_bitmaps s)))))
              (buffer_space_left (stack_state_data_buffer s)) STAR
            word_store c (stack_state_store s) STAR
            misc_word_list c (stack_state_stack s))
             (fun2set (stack_state_memory t,stack_state_mdomain t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_removeProof_state_rel_def; LET_DEF; LET_END_DEF; stack_get_var_def] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  (fun (asl,w as g) ->
     let th = find (fun (_,th) -> try let l,r = dest_eq (concl th) in
                     l = `FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) (k + 1)`
                     with Failure _ -> false) asl in
     EXISTS_TAC (rand(rand(rhs(concl(snd th))))) g) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                             "STAR" with Failure _ -> false)) THEN
  REWRITE_TAC[MAP_APPEND; LENGTH_APPEND] THEN
  REWRITE_TAC[ISPECL [`LENGTH (stack_state_bitmaps (s:(A,C,FFI)stack_state))`;
                      `LENGTH (buffer_buffer (stack_state_data_buffer (s:(A,C,FFI)stack_state)))`]
                     ADD_SYM]);;

(* the word arithmetic of a stack allocation of n words: the new stack     *)
(* pointer c + bw * ss - word_offset n is below the base c exactly when    *)
(* ss < n, and is c + bw * (ss - n) otherwise                               *)

let STACKPROPSAUX_le_mul = prove
 (`!d m. ~(d = 0) ==> m <= d * m`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC);;

let STACKPROPSAUX_val_bw_mul = prove
 (`!m. good_dimindex(:A) /\ (dimindex(:A) DIV 8) * m < dimword(:A)
       ==> val (word_mul (bytes_in_word:A word) (word m)) = (dimindex(:A) DIV 8) * m`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_val_bytes_in_word) THEN
  UNDISCH_TAC `(dimindex(:A) DIV 8) * m < dimword(:A)` THEN
  ASM_REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; dimword_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `m MOD 2 EXP dimindex(:A) = m` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `2 EXP backend_common_word_shift (:A) * m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STACKPROPSAUX_le_mul THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ASM_SIMP_TAC[MOD_LT]]);;

let STACKPROPSAUX_alloc_arith = prove
 (`!(c:A word) ss n len.
     good_dimindex(:A) /\ dimindex(:A) DIV 8 * max_stack_alloc <= val c /\
     val c + val (bytes_in_word:A word) * len < dimword(:A) /\ ss <= len /\
     n <= max_stack_alloc
     ==> (word_ult (word_sub (word_add c (word_mul bytes_in_word (word ss)))
                             (word_offset n)) c <=> ss < n) /\
         (n <= ss
          ==> word_sub (word_add c (word_mul bytes_in_word (word ss))) (word_offset n) =
              word_add c (word_mul bytes_in_word (word (ss - n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_val_bytes_in_word) THEN
  SUBGOAL_THEN `val (bytes_in_word:A word) = dimindex(:A) DIV 8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. dimindex(:A) DIV 8 * m < dimword(:A)
                    ==> val (word_mul (bytes_in_word:A word) (word m)) = dimindex(:A) DIV 8 * m`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STACKPROPSAUX_val_bw_mul THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_offset n:A word) = dimindex(:A) DIV 8 * n` ASSUME_TAC THENL
   [REWRITE_TAC[word_offset_def; VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `c:A word` VAL_BOUND) THEN
    SUBGOAL_THEN `dimindex(:A) DIV 8 * n <= dimindex(:A) DIV 8 * max_stack_alloc` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
    UNDISCH_TAC `dimindex(:A) DIV 8 * max_stack_alloc <= val (c:A word)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = dimindex(:A) DIV 8` THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term ((=) `backend_common_word_shift (:A)`)) (concl th)))) THEN
  SUBGOAL_THEN `d * ss <= d * len /\ d * n <= val (c:A word)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `d * max_stack_alloc` THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (c:A word) + d * len < 2 EXP dimindex(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `val (c:A word) + val (bytes_in_word:A word) * len < dimword(:A)` THEN
    ASM_REWRITE_TAC[dimword_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_mul (bytes_in_word:A word) (word ss)) = d * ss` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall (concl th) then MATCH_MP_TAC th else failwith "") THEN
    REWRITE_TAC[dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_add c (word_mul (bytes_in_word:A word) (word ss))) = val c + d * ss`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_ADD_CASES] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub (word_add c (word_mul bytes_in_word (word ss)))
                              (word_offset n:A word)) = (val c + d * ss) - d * n`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[WORD_ULT] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `d * ss < d * n` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[LT_MULT_LCANCEL]];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d * (ss - n) <= d * ss /\ d * n <= d * ss` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_mul (bytes_in_word:A word) (word (ss - n))) = d * (ss - n)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall (concl th) then MATCH_MP_TAC th else failwith "") THEN
    REWRITE_TAC[dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD_CASES; LEFT_SUB_DISTRIB] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* clauses of stack_evaluate and evaluation steps for the straight-line     *)
(* code that stack_remove produces                                          *)

let STACKPROPSAUX_ev_clause (name:string) : thm =
  find (fun th -> try let l = lhs(snd(strip_forall(concl th))) in
                      fst(dest_const(fst(strip_comb(fst(dest_pair(rand l)))))) = name
                  with Failure _ -> false)
       (CONJUNCTS stack_evaluate_def);;

let STACKPROPSAUX_ev_seq_none = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state) s1.
     stack_evaluate (c1,s) = (NONE,s1)
     ==> stack_evaluate (stack_Seq c1 c2,s) = stack_evaluate (c2,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Seq"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_ev_seq_some = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state) s1 r.
     stack_evaluate (c1,s) = (SOME r,s1)
     ==> stack_evaluate (stack_Seq c1 c2,s) = (SOME r,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Seq"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT]);;

let STACKPROPSAUX_ev_inst = prove
 (`!i (s:(A,C,FFI)stack_state) s1.
     stack_inst i s = SOME s1 ==> stack_evaluate (stack_Inst i,s) = (NONE,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Inst"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_inst_binop_imm = prove
 (`!b r1 r2 (w:A word) x (s:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs s) r2 = SOME (wl_Word x)
     ==> stack_inst (asm_Arith (Binop b r1 r2 (Imm w))) s =
         OPTION_MAP (\y. stack_set_var r1 (wl_Word y) s) (word_op b [x; w])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_inst_def; stack_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "reg_imm"] THEN
  REWRITE_TAC[stack_word_exp_def; LET_DEF; LET_END_DEF; MAP] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF] THEN
  CASES_ON `word_op b [x; w:A word]` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF]);;

let STACKPROPSAUX_inst_const = prove
 (`!r (w:A word) (s:(A,C,FFI)stack_state).
     stack_inst (asm_Const r w) s = SOME (stack_set_var r (wl_Word w) s)`,
  REWRITE_TAC[stack_inst_def; stack_assign_def; stack_word_exp_def] THEN
  CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_ev_halt_inst = prove
 (`!(w:A word) (s:(A,C,FFI)stack_state).
     stack_evaluate (halt_inst w,s) =
     (SOME (stackSem_Halt (wl_Word w)),stack_empty_env (stack_set_var 1 (wl_Word w) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[halt_inst_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `stack_evaluate (stack_Halt 1:(A)stack_prog,
                              stack_set_var 1 (wl_Word (w:A word)) (s:(A,C,FFI)stack_state))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_seq_none THEN MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
    REWRITE_TAC[STACKPROPSAUX_inst_const];
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Halt"; get_var_set_var_same] THEN
    CASE_REWRITE_TAC[]]);;

(* more facts of state_rel *)

let STACKPROPSAUX_sr_facts2 = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> stack_state_stack_space s <= LENGTH (stack_state_stack s) /\
         lookup stack_err_lab (stack_state_code t) = SOME (halt_inst (word 2)) /\
         {k, k + 1, k + 2} SUBSET stack_state_ffi_save_regs t /\
         is_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase) /\
         FLOOKUP (stack_state_regs t) (k + 2) = FLOOKUP (stack_state_store s) CurrHeap`,
  REWRITE_TAC[stack_removeProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* changing the stack space: register k moves along *)

let STACKPROPSAUX_state_rel_stack_space = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t c m.
     stack_removeProof_state_rel jump off k s t /\
     FLOOKUP (stack_state_regs t) (k + 1) = SOME (wl_Word c) /\
     m <= LENGTH (stack_state_stack s)
     ==> stack_removeProof_state_rel jump off k (stack_state_stack_space_fupd (K m) s)
           (stack_state_regs_fupd
              (K (stack_state_regs t |+
                    (k,wl_Word (word_add c (word_mul bytes_in_word (word m)))))) t)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; ARITH_RULE `~(k = k + 1) /\ ~(k = k + 2)`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(k = n:num)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `the_SOME_Word:((A)word_loc)option->A word`)) (concl th))) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_clock_add_0 = prove
 (`!t:(A,C,FFI)stack_state. stack_state_clock_fupd (K (stack_state_clock t + 0)) t = t`,
  REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock]);;

let STACKPROPSAUX_word_op_sub = prove
 (`!(x:A word) y. word_op asm_Sub [x; y] = SOME (word_sub x y)`,
  REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_word_op_add = prove
 (`!(x:A word) y. word_op asm_Add [x; y] = SOME (word_add x y)`,
  REWRITE_TAC[word_op_def; ITLIST; WORD_ADD_0] THEN CASE_REWRITE_TAC[]);;

(* the goal ?t2. (r',st) = (r,t2) /\ P t2: the witness st *)

let STACKPROPSAUX_PAIR_WITNESS_TAC : tactic = fun (asl,w as g) ->
  if not (is_exists w) then ALL_TAC g else
  let v,bod = dest_exists w in
  let cs = conjuncts bod in
  let wit = tryfind (fun c ->
     let l,r = dest_eq c in
     if r = v then l else if l = v then r else
     let (_,l2) = dest_pair l and (_,r2) = dest_pair r in
     if r2 = v then l2 else failwith "PAIR_WITNESS_TAC") cs in
  (EXISTS_TAC wit THEN REWRITE_TAC[PAIR_EQ]) g;;

(* HOL4 line 420 *)
let evaluate_single_stack_alloc = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t1 r s2 n.
     stack_removeProof_state_rel jump off k s t1 /\
     ((r,s2) = if stack_state_stack_space s < n
               then (SOME (stackSem_Halt (wl_Word (word 2))),stack_empty_env s)
               else (NONE,stack_state_stack_space_fupd
                            (K (stack_state_stack_space s - n)) s)) /\
     ~(n = 0) /\ n <= max_stack_alloc
     ==> ?ck t2.
           stack_evaluate (single_stack_alloc jump k n,
                           stack_state_clock_fupd (K (stack_state_clock t1 + ck)) t1) =
             (r,t2) /\
           (if stack_state_stack_space s < n then stack_state_ffi t2 = stack_state_ffi s2
            else stack_removeProof_state_rel jump off k s2 t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_sr_facts2) THEN
  MP_TAC(ISPECL [`c:A word`; `stack_state_stack_space (s:(A,C,FFI)stack_state)`; `n:num`;
                 `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))`]
                STACKPROPSAUX_alloc_arith) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `cc = word_sub (word_add c (word_mul bytes_in_word
                     (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))))
                     (word_offset n):A word` THEN
  SUBGOAL_THEN
   `!t:(A,C,FFI)stack_state. stack_state_regs t = stack_state_regs (t1:(A,C,FFI)stack_state) ==>
      stack_evaluate (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))),t) =
      (NONE,stack_set_var k (wl_Word cc) t)`
    (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
    MP_TAC(ISPECL [`asm_Sub`; `k:num`; `k:num`; `word_offset n:A word`;
                   `word_add c (word_mul bytes_in_word
                      (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))):A word`;
                   `t:(A,C,FFI)stack_state`] STACKPROPSAUX_inst_binop_imm) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `stack_get_var k (t1:(A,C,FFI)stack_state) =
                   SOME (wl_Word (word_add c (word_mul bytes_in_word
                     (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))))` THEN
      REWRITE_TAC[stack_get_var_def];
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[STACKPROPSAUX_word_op_sub; OPTION_MAP_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:(A,C,FFI)stack_state. stack_state_regs t = stack_state_regs (t1:(A,C,FFI)stack_state) ==>
                  stack_get_var k (stack_set_var k (wl_Word cc) t) = SOME (wl_Word cc) /\
                  stack_get_var (k + 1) (stack_set_var k (wl_Word cc) t) = SOME (wl_Word c)`
    (LABEL_TAC "regs") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[get_var_set_var_same] THEN
    REWRITE_TAC[stack_removeProof_get_var_set_var; ARITH_RULE `~(k + 1 = k)`] THEN
    UNDISCH_TAC `stack_get_var (k + 1) (t1:(A,C,FFI)stack_state) = SOME (wl_Word c)` THEN
    ASM_REWRITE_TAC[stack_get_var_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state) < n` THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_pair (lhs (concl th))
                          then MP_TAC th else failwith "") THEN
  FIRST_ASSUM(fun th -> if is_neg(concl th) || is_comb(concl th) &&
                             (try fst(dest_const(fst(strip_comb(concl th)))) = "<"
                              with Failure _ -> false)
                          then REWRITE_TAC[th] else failwith "") THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  ASM_CASES_TAC `jump:bool` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `jump:bool` then SUBST_ALL_TAC(EQT_INTRO th)
                          else if concl th = `~jump` then SUBST_ALL_TAC(EQF_INTRO th)
                          else failwith "") THENL
   [(* halt, jump *)
    SUBGOAL_THEN `single_stack_alloc T k n:(A)stack_prog =
                  stack_Seq (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))))
                            (JumpLower k (k + 1) stack_err_lab)`
      SUBST1_TAC THENL [REWRITE_TAC[single_stack_alloc_def]; ALL_TAC] THEN
    EXISTS_TAC `1` THEN
    W(fun (asl,w) -> MP_TAC(ISPECL
      [`stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))):(A)stack_prog`;
       `JumpLower k (k + 1) stack_err_lab:(A)stack_prog`;
       `stack_state_clock_fupd (K (stack_state_clock t1 + 1)) (t1:(A,C,FFI)stack_state)`;
       `stack_set_var k (wl_Word cc)
          (stack_state_clock_fupd (K (stack_state_clock t1 + 1)) (t1:(A,C,FFI)stack_state))`]
      STACKPROPSAUX_ev_seq_none)) THEN
    ANTS_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN SIMP[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "regs" (MP_TAC o SPEC
      `stack_state_clock_fupd (K (stack_state_clock t1 + 1)) (t1:(A,C,FFI)stack_state)`) THEN
    ANTS_TAC THENL [SIMP[]; STRIP_TAC] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "JumpLower"] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[asm_word_cmp_def] THEN
    REWRITE_TAC[stack_find_code_def] THEN SIMP[stack_set_var_def] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_halt_inst] THEN CASE_REWRITE_TAC[stack_bad_fun_return_def] THEN
    STACKPROPSAUX_PAIR_WITNESS_TAC THEN
    REWRITE_TAC[stack_empty_env_def; stack_set_var_def; stack_dec_clock_def] THEN SIMP[] THEN
    ASM_REWRITE_TAC[];
    (* halt, no jump *)
    SUBGOAL_THEN `single_stack_alloc F k n:(A)stack_prog =
                  stack_Seq (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))))
                            (stack_If Lower k (Reg (k + 1)) (halt_inst (word 2)) stack_Skip)`
      SUBST1_TAC THENL [REWRITE_TAC[single_stack_alloc_def]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[STACKPROPSAUX_clock_add_0] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL
      [`stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))):(A)stack_prog`;
       `stack_If Lower k (Reg (k + 1)) (halt_inst (word 2)) stack_Skip:(A)stack_prog`;
       `t1:(A,C,FFI)stack_state`; `stack_set_var k (wl_Word cc) (t1:(A,C,FFI)stack_state)`]
      STACKPROPSAUX_ev_seq_none)) THEN
    ANTS_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN SIMP[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "regs" (MP_TAC o SPEC `t1:(A,C,FFI)stack_state`) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_If"; stack_get_var_imm_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_word_cmp_def] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_halt_inst] THEN
    STACKPROPSAUX_PAIR_WITNESS_TAC THEN
    REWRITE_TAC[stack_empty_env_def; stack_set_var_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    (* no halt, jump *)
    SUBGOAL_THEN `single_stack_alloc T k n:(A)stack_prog =
                  stack_Seq (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))))
                            (JumpLower k (k + 1) stack_err_lab)`
      SUBST1_TAC THENL [REWRITE_TAC[single_stack_alloc_def]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[STACKPROPSAUX_clock_add_0] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL
      [`stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))):(A)stack_prog`;
       `JumpLower k (k + 1) stack_err_lab:(A)stack_prog`;
       `t1:(A,C,FFI)stack_state`; `stack_set_var k (wl_Word cc) (t1:(A,C,FFI)stack_state)`]
      STACKPROPSAUX_ev_seq_none)) THEN
    ANTS_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN SIMP[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "regs" (MP_TAC o SPEC `t1:(A,C,FFI)stack_state`) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "JumpLower"] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[asm_word_cmp_def] THEN ASM_REWRITE_TAC[] THEN
    STACKPROPSAUX_PAIR_WITNESS_TAC THEN
    SUBGOAL_THEN `cc = word_add c (word_mul bytes_in_word
                     (word (stack_state_stack_space (s:(A,C,FFI)stack_state) - n))):A word`
      SUBST1_TAC THENL
     [FIRST [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
             EXPAND_TAC "cc" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[stack_set_var_def] THEN
    MATCH_MP_TAC STACKPROPSAUX_state_rel_stack_space THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `stack_get_var (k + 1) (t1:(A,C,FFI)stack_state) = SOME (wl_Word c)` THEN
      REWRITE_TAC[stack_get_var_def];
      ASM_ARITH_TAC];
    (* no halt, no jump *)
    SUBGOAL_THEN `single_stack_alloc F k n:(A)stack_prog =
                  stack_Seq (stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))))
                            (stack_If Lower k (Reg (k + 1)) (halt_inst (word 2)) stack_Skip)`
      SUBST1_TAC THENL [REWRITE_TAC[single_stack_alloc_def]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[STACKPROPSAUX_clock_add_0] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL
      [`stack_Inst (asm_Arith (Binop asm_Sub k k (Imm (word_offset n)))):(A)stack_prog`;
       `stack_If Lower k (Reg (k + 1)) (halt_inst (word 2)) stack_Skip:(A)stack_prog`;
       `t1:(A,C,FFI)stack_state`; `stack_set_var k (wl_Word cc) (t1:(A,C,FFI)stack_state)`]
      STACKPROPSAUX_ev_seq_none)) THEN
    ANTS_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN SIMP[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "regs" (MP_TAC o SPEC `t1:(A,C,FFI)stack_state`) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_If"; stack_get_var_imm_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_word_cmp_def] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Skip"] THEN
    STACKPROPSAUX_PAIR_WITNESS_TAC THEN
    SUBGOAL_THEN `cc = word_add c (word_mul bytes_in_word
                     (word (stack_state_stack_space (s:(A,C,FFI)stack_state) - n))):A word`
      SUBST1_TAC THENL
     [FIRST [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
             EXPAND_TAC "cc" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[stack_set_var_def] THEN
    MATCH_MP_TAC STACKPROPSAUX_state_rel_stack_space THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `stack_get_var (k + 1) (t1:(A,C,FFI)stack_state) = SOME (wl_Word c)` THEN
      REWRITE_TAC[stack_get_var_def];
      ASM_ARITH_TAC]]);;

(* sequencing with extra clock *)

let STACKPROPSAUX_seq_clock = prove
 (`!c1 c2 (t:(A,C,FFI)stack_state) ck1 t1 ck2 r t2.
     stack_evaluate (c1,stack_state_clock_fupd (K (stack_state_clock t + ck1)) t) = (NONE,t1) /\
     stack_evaluate (c2,stack_state_clock_fupd (K (stack_state_clock t1 + ck2)) t1) = (r,t2)
     ==> stack_evaluate (stack_Seq c1 c2,
                         stack_state_clock_fupd (K (stack_state_clock t + (ck1 + ck2))) t) =
         (r,t2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `stack_evaluate (c2:(A)stack_prog,
                stack_state_clock_fupd (K (stack_state_clock t1 + ck2)) (t1:(A,C,FFI)stack_state))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC STACKPROPSAUX_ev_seq_none THEN
  MP_TAC(ISPECL [`c1:(A)stack_prog`;
                 `stack_state_clock_fupd (K (stack_state_clock t + ck1)) (t:(A,C,FFI)stack_state)`;
                 `NONE:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`]
                (INST [`ck2:num`,`extra:num`] stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[distinctness "option"] THEN SIMP[ADD_ASSOC]);;

(* rewrite the other assumptions with the assumption tm *)

let STACKPROPSAUX_ASSUM_REWRITE_TAC (tm:term) : tactic =
  let th = ASSUME tm in
  RULE_ASSUM_TAC (fun a -> if concl a = tm then a else REWRITE_RULE[th] a);;

(* HOL4 line 550 *)
let evaluate_stack_alloc = prove
 (`!jump k n r (s:(A,C,FFI)stack_state) s2 t1 off.
     stack_evaluate (StackAlloc n,s) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_removeProof_state_rel jump off k s t1
     ==> ?ck t2.
           stack_evaluate (stack_alloc jump k n,
                           stack_state_clock_fupd (K (ck + stack_state_clock t1)) t1) =
             (r,t2) /\
           (if !w. ~(r = SOME (stackSem_Halt w))
            then stack_removeProof_state_rel jump off k s2 t2
            else stack_state_ffi t2 = stack_state_ffi s2)`,
  MATCH_MP_TAC stack_alloc_ind THEN
  MAP_EVERY X_GEN_TAC [`jump:bool`; `k:num`; `n:num`] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`r:((A)stack_result)option`; `s:(A,C,FFI)stack_state`;
                       `s2:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`;
                       `off:A word#A word`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SUBGOAL_THEN `(r:((A)stack_result)option,s2:(A,C,FFI)stack_state) =
                         (if stack_state_stack_space (s:(A,C,FFI)stack_state) < n
                          then (SOME (stackSem_Halt (wl_Word (word 2:A word))),stack_empty_env s)
                          else (NONE,stack_state_stack_space_fupd
                                       (K (stack_state_stack_space s - n)) s))`
    (LABEL_TAC "res") THENL
   [UNDISCH_TAC `stack_evaluate (StackAlloc n,s:(A,C,FFI)stack_state) = (r,s2)` THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "StackAlloc"] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[STACKPROPSAUX_clock_add_0; STACKPROPSAUX_ev_clause "stack_Skip"] THEN
    REMOVE_THEN "res" MP_TAC THEN
    ASM_REWRITE_TAC[LT; SUB_0; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    EXISTS_TAC `t1:(A,C,FFI)stack_state` THEN REWRITE_TAC[distinctness "option"] THEN
    SUBGOAL_THEN `stack_state_stack_space_fupd (K (stack_state_stack_space s)) s =
                  (s:(A,C,FFI)stack_state)` (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[stack_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n <= max_stack_alloc` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                   `t1:(A,C,FFI)stack_state`; `r:((A)stack_result)option`;
                   `s2:(A,C,FFI)stack_state`; `n:num`] evaluate_single_stack_alloc) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)stack_state`] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "res" MP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN
    ASM_REWRITE_TAC[option_INJ; distinctness "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* n > max_stack_alloc: first max_stack_alloc words, then the rest *)
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t1:(A,C,FFI)stack_state`;
                 `if stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc
                  then SOME (stackSem_Halt (wl_Word (word 2))):((A)stack_result)option
                  else NONE`;
                 `if stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc
                  then stack_empty_env s
                  else stack_state_stack_space_fupd
                         (K (stack_state_stack_space s - max_stack_alloc)) s`;
                 `max_stack_alloc`] evaluate_single_stack_alloc) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[max_stack_alloc_def] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc` THENL
   [(* the first allocation halts, and so does the whole *)
    SUBGOAL_THEN `stack_state_stack_space (s:(A,C,FFI)stack_state) < n` ASSUME_TAC THENL
     [UNDISCH_TAC `~(n <= max_stack_alloc)` THEN
      UNDISCH_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc` THEN
      ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "res" MP_TAC THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)stack_state`] THEN
    STACKPROPSAUX_ASSUM_REWRITE_TAC
      `stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_ev_seq_some THEN ASM_REWRITE_TAC[];
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `wl_Word (word 2):(A)word_loc`) THEN REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_state_ffi"
           with Failure _ -> false))) THEN
        REWRITE_TAC[stack_empty_env_def] THEN SIMP[]]];
    ALL_TAC] THEN
  (* the first allocation succeeds: the induction hypothesis for the rest *)
  STACKPROPSAUX_ASSUM_REWRITE_TAC
    `~(stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc)` THEN
  SUBGOAL_THEN `stack_state_stack_space (s:(A,C,FFI)stack_state) - max_stack_alloc <
                n - max_stack_alloc <=> stack_state_stack_space s < n` ASSUME_TAC THENL
   [UNDISCH_TAC `~(n <= max_stack_alloc)` THEN
    UNDISCH_TAC `~(stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc)` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(stack_state_stack_space (s:(A,C,FFI)stack_state) - max_stack_alloc) -
                (n - max_stack_alloc) = stack_state_stack_space s - n` ASSUME_TAC THENL
   [UNDISCH_TAC `~(n <= max_stack_alloc)` THEN
    UNDISCH_TAC `~(stack_state_stack_space (s:(A,C,FFI)stack_state) < max_stack_alloc)` THEN
    ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL
    [`r:((A)stack_result)option`;
     `stack_state_stack_space_fupd (K (stack_state_stack_space s - max_stack_alloc))
        (s:(A,C,FFI)stack_state)`;
     `if stack_state_stack_space (s:(A,C,FFI)stack_state) < n
      then stack_empty_env (stack_state_stack_space_fupd
             (K (stack_state_stack_space s - max_stack_alloc)) s)
      else (s2:(A,C,FFI)stack_state)`;
     `t2:(A,C,FFI)stack_state`; `off:A word#A word`] o
     REWRITE_RULE[ASSUME `~(n = 0)`; ASSUME `~(n <= max_stack_alloc)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "StackAlloc"] THEN
    REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "res" MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t3:(A,C,FFI)stack_state`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_seq_clock THEN EXISTS_TAC `t2:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "res" MP_TAC THEN
  ASM_CASES_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state) < n` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN
  ASM_REWRITE_TAC[option_INJ; distinctness "option"; injectivity "stack_result"] THEN
  TRY (COND_CASES_TAC THENL
        [FIRST_X_ASSUM(MP_TAC o SPEC `wl_Word (word 2):(A)word_loc`) THEN REWRITE_TAC[];
         REWRITE_TAC[stack_empty_env_def] THEN SIMP[]]) THEN
  TRY (SIMP[] THEN NO_TAC));;

(* HOL4 line 621 *)
let state_rel_mem_load_imp = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t x w.
     stack_removeProof_state_rel jump off k s t /\ stack_mem_load x s = SOME w
     ==> stack_mem_load x t = SOME w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_mem_load_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t:(A,C,FFI)stack_state`; `x:A word`] state_rel_read) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 674 *)
let memory_write = prove
 (`!(x:A) y sd sm p m dm.
     x IN sd /\ x IN dm /\ (memory (sm:A->B) sd STAR p) (fun2set (m,dm))
     ==> (memory ((x =+ y) sm) sd STAR p) (fun2set ((x =+ y) m,dm))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STAR_def; SPLIT_EQ; memory_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`fun2set ((x =+ y) (sm:A->B),sd)`; `v:A#B->bool`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!a:A. a IN sd ==> a IN dm /\ (m:A->B) a = sm a` (LABEL_TAC "f1") THENL
   [UNDISCH_TAC `(u:A#B->bool) SUBSET fun2set (m,dm)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_fun2set] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_fun2set; APPLY_UPDATE_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_DIFF; IN_fun2set; APPLY_UPDATE_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `w:B`] THEN
  ASM_CASES_TAC `(z:A) IN sd` THENL
   [USE_THEN "f1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(z:A) IN sd`))) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    SUBGOAL_THEN `~(x:A = z)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]]);;

(* memory updates at an address of the source memory domain *)

let STACKPROPSAUX_state_rel_memory_write = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t a v.
     stack_removeProof_state_rel jump off k s t /\ a IN stack_state_mdomain s
     ==> stack_removeProof_state_rel jump off k
           (stack_state_memory_fupd (K ((a =+ v) (stack_state_memory s))) s)
           (stack_state_memory_fupd (K ((a =+ v) (stack_state_memory t))) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t:(A,C,FFI)stack_state`; `a:A word`] state_rel_read) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t` THEN
  REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `the_SOME_Word:((A)word_loc)option->A word`)) (concl th))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN EVERY_CASE_TAC THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN
  ASM_MESON_TAC[memory_write]);;

(* HOL4 line 687 *)
let stack_removeProof_state_rel_mem_store = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t x y s' t'.
     stack_removeProof_state_rel jump off k s t /\
     stack_mem_store x y s = SOME s' /\ stack_mem_store x y t = SOME t'
     ==> stack_removeProof_state_rel jump off k s' t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_mem_store_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC STACKPROPSAUX_state_rel_memory_write THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 638 *)
let state_rel_word_exp = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t e w.
     stack_removeProof_state_rel jump off k s t /\ reg_bound_exp e k /\
     stack_word_exp s e = SOME w
     ==> stack_word_exp t e = SOME w`,
  REPEAT GEN_TAC THEN MAP_EVERY (fun v -> SPEC_TAC(v,v))
    [`w:A word`; `e:(A)wl_exp`; `s:(A,C,FFI)stack_state`] THEN
  MATCH_MP_TAC stack_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[stack_word_exp_def] THEN MESON_TAC[];
    REWRITE_TAC[stack_word_exp_def; reg_bound_exp_def] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 (MATCH_MP STACKPROPSAUX_sr_code_regs
      (ASSUME `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t`))) th]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[reg_bound_exp_def];
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[stack_word_exp_def; reg_bound_exp_def] THEN
    STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    CASES_ON `stack_word_exp (s:(A,C,FFI)stack_state) addr` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A word`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `stack_mem_load (a:A word) (s:(A,C,FFI)stack_state)` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel_mem_load_imp
      (CONJ (ASSUME `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t`) th)]) THEN
    CASE_REWRITE_TAC[];
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[stack_word_exp_def; reg_bound_exp_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `MAP (stack_word_exp (t:(A,C,FFI)stack_state)) wexps =
                  MAP (stack_word_exp (s:(A,C,FFI)stack_state)) wexps`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `x:(A)wl_exp` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?v:A word. stack_word_exp (s:(A,C,FFI)stack_state) x = SOME v`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ALL IS_SOME (MAP (stack_word_exp (s:(A,C,FFI)stack_state)) wexps)` THEN
      REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:(A)wl_exp`) THEN ASM_REWRITE_TAC[IS_SOME_EXISTS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:(A)wl_exp` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `MEM:(A)wl_exp->((A)wl_exp)list->bool`)) (concl th) &&
      can (find_term ((=) `stack_word_exp:(A,C,FFI)stack_state->(A)wl_exp->(A word)option`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:A word`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ALL (\e. reg_bound_exp e k) (wexps:((A)wl_exp)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `x:(A)wl_exp`) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[stack_word_exp_def; reg_bound_exp_def] THEN
    STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    CASES_ON `stack_word_exp (s:(A,C,FFI)stack_state) wexp` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `stack_word_exp (s:(A,C,FFI)stack_state) wexp1` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `stack_word_exp (t:(A,C,FFI)stack_state) wexp = SOME (a:A word) /\
                  stack_word_exp t wexp1 = SOME (a':A word)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 703 *)
let state_rel_mem_store_32 = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t a b z.
     stack_removeProof_state_rel jump off k s t /\
     mem_store_32 (stack_state_memory s) (stack_state_mdomain s) (stack_state_be s) a b =
       SOME z
     ==> ?y. mem_store_32 (stack_state_memory t) (stack_state_mdomain t) (stack_state_be t)
                          a b = SOME y /\
             stack_removeProof_state_rel jump off k (stack_state_memory_fupd (K z) s)
                                         (stack_state_memory_fupd (K y) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o el 6 o CONJUNCTS o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[mem_store_32_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `stack_state_memory (s:(A,C,FFI)stack_state) (byte_align (a:A word))` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t:(A,C,FFI)stack_state`; `byte_align (a:A word)`] state_rel_read) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  MATCH_MP_TAC STACKPROPSAUX_state_rel_memory_write THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 729 *)
let state_rel_mem_store_byte_aux = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t a b z.
     stack_removeProof_state_rel jump off k s t /\
     mem_store_byte_aux (stack_state_memory s) (stack_state_mdomain s) (stack_state_be s)
                        a b = SOME z
     ==> ?y. mem_store_byte_aux (stack_state_memory t) (stack_state_mdomain t)
                                (stack_state_be t) a b = SOME y /\
             stack_removeProof_state_rel jump off k (stack_state_memory_fupd (K z) s)
                                         (stack_state_memory_fupd (K y) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o el 6 o CONJUNCTS o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN
  CASES_ON `stack_state_memory (s:(A,C,FFI)stack_state) (byte_align (a:A word))` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t:(A,C,FFI)stack_state`; `byte_align (a:A word)`] state_rel_read) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  MATCH_MP_TAC STACKPROPSAUX_state_rel_memory_write THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 752 (local) *)
let stack_removeProof_state_rel_get_fp_var = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t n.
     stack_removeProof_state_rel jump off k s t
     ==> stack_get_fp_var n s = stack_get_fp_var n t`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  SIMP[stack_get_fp_var_def]);;

(* HOL4 line 759 (local) *)
let stack_removeProof_state_rel_set_fp_var = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t n v.
     stack_removeProof_state_rel jump off k s t
     ==> stack_removeProof_state_rel jump off k (stack_set_fp_var n v s)
                                     (stack_set_fp_var n v t)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; stack_set_fp_var_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_TYPE_CASES_TAC (ty:hol_type) : tactic =
  fun (asl,w as g) ->
    let vs = filter (fun v -> type_of v = ty) (frees w) in
    MAP_EVERY (fun v -> CASES_ON v) vs g;;

let STACKPROPSAUX_sr_get_var = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> !n. n < k ==> stack_get_var n t = stack_get_var n s /\
                       FLOOKUP (stack_state_regs t) n = FLOOKUP (stack_state_regs s) n`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP STACKPROPSAUX_sr_code_regs) THEN
  SIMP[stack_get_var_def]);;

let STACKPROPSAUX_INST_LEAF_TAC : tactic =
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)reg_imm` THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `SOME (s':(A,C,FFI)stack_state)`)) THEN
  USE_THEN "gv" (fun th -> ASM_SIMP_TAC[th; stack_get_vars_def; stack_assign_def;
                                         stack_word_exp_def; LET_DEF; LET_END_DEF; MAP;
                                         ALL; IS_SOME_DEF; THE_DEF]) THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) &&
        can (find_term ((=) `stack_get_fp_var:num->(A,C,FFI)stack_state->(int64)option`))
            (concl th) then REWRITE_TAC[GSYM th] else failwith "") THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  REPEAT(FIRST [MATCH_MP_TAC stack_removeProof_state_rel_set_var THEN ASM_REWRITE_TAC[] ;
                MATCH_MP_TAC stack_removeProof_state_rel_set_fp_var]) THEN
  ASM_REWRITE_TAC[];;

let STACKPROPSAUX_mem_store_IMP = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t x y s'.
     stack_removeProof_state_rel jump off k s t /\ stack_mem_store x y s = SOME s'
     ==> ?t'. stack_mem_store x y t = SOME t' /\ stack_removeProof_state_rel jump off k s' t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th))) THEN
  REWRITE_TAC[stack_mem_store_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t:(A,C,FFI)stack_state`; `x:A word`] state_rel_read) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  MATCH_MP_TAC stack_removeProof_state_rel_mem_store THEN
  MAP_EVERY EXISTS_TAC [`s:(A,C,FFI)stack_state`; `t:(A,C,FFI)stack_state`;
                        `x:A word`; `y:(A)word_loc`] THEN
  ASM_REWRITE_TAC[stack_mem_store_def]);;

let STACKPROPSAUX_MEM_FACTS_TAC : tactic = fun (asl,w as g) ->
  let srs = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                  "stack_removeProof_state_rel" with Failure _ -> false)
                   (map snd asl) in
  let ths = map snd asl in
  let lems1 = [state_rel_mem_load_imp; mem_load_byte_aux_IMP; mem_load_32_IMP] in
  let lems2 = [state_rel_mem_store_32; state_rel_mem_store_byte_aux; STACKPROPSAUX_mem_store_IMP] in
  let der1 = flat (map (fun sr -> mapfilter (fun th ->
                tryfind (fun lem -> MATCH_MP lem (CONJ sr th)) lems1) ths) srs) in
  let der2 = flat (map (fun sr -> mapfilter (fun th ->
                tryfind (fun lem -> MATCH_MP lem (CONJ sr th)) lems2) ths) srs) in
  (MAP_EVERY ASSUME_TAC der1 THEN MAP_EVERY STRIP_ASSUME_TAC der2) g;;

let STACKPROPSAUX_INST_MEM_TAC0 : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `SOME (s':(A,C,FFI)stack_state)`)) THEN
  USE_THEN "gv" (fun th -> ASM_SIMP_TAC[th; stack_assign_def;
                                         stack_word_exp_def; LET_DEF; LET_END_DEF; MAP;
                                         ALL; IS_SOME_DEF; THE_DEF]) THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STACKPROPSAUX_MEM_FACTS_TAC;;

(* two assumptions x = r1 and x = r2: contradiction if r1, r2 are distinct *)
(* option constructors, otherwise substitute the injected equation          *)

let STACKPROPSAUX_SAME_LHS_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun th -> is_eq (concl th) && not (is_var (lhs (concl th))))
                   (map snd asl) in
  tryfind (fun th1 -> tryfind (fun th2 ->
      let l1,r1 = dest_eq (concl th1) and l2,r2 = dest_eq (concl th2) in
      if l1 = l2 && not (r1 = r2) then
        let c = TRANS (SYM th1) th2 in
        let c' = REWRITE_RULE[option_DISTINCT; option_INJ] c in
        if concl c' = `F` then CONTR_TAC c' g
        else if is_eq (concl c') && is_var (rhs (concl c')) then SUBST_ALL_TAC c' g
        else if is_eq (concl c') && is_var (lhs (concl c')) then SUBST_ALL_TAC (SYM c') g
        else failwith "SAME_LHS_TAC"
      else failwith "SAME_LHS_TAC") eqs) eqs;;

let STACKPROPSAUX_INST_MEM_TAC : tactic =
  STACKPROPSAUX_INST_MEM_TAC0 THEN
  REPEAT (CHANGED_TAC STACKPROPSAUX_SAME_LHS_TAC) THEN
  REWRITE_TAC[option_INJ] THEN
  TRY (DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  TRY (MATCH_MP_TAC stack_removeProof_state_rel_set_var THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 767 *)
let state_rel_inst = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t i s'.
     stack_removeProof_state_rel jump off k s t /\ reg_bound_inst i k /\
     stack_inst i s = SOME s'
     ==> ?t'. stack_inst i t = SOME t' /\ stack_removeProof_state_rel jump off k s' t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "gv" o MATCH_MP STACKPROPSAUX_sr_get_var) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_removeProof_state_rel_get_fp_var) THEN
  UNDISCH_TAC `stack_inst i (s:(A,C,FFI)stack_state) = SOME s'` THEN
  UNDISCH_TAC `reg_bound_inst (i:(A)inst) k` THEN
  CASES_ON `i:(A)inst` THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)asm_arith` THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:memop` THEN STACKPROPSAUX_TYPE_CASES_TAC `:(A)addr` THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:fp` THEN
  REWRITE_TAC[stack_inst_def; reg_bound_inst_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST [REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
         ASM_MESON_TAC[] THEN NO_TAC;
         STACKPROPSAUX_INST_LEAF_TAC THEN NO_TAC;
         STACKPROPSAUX_INST_MEM_TAC THEN NO_TAC]);;

(* HOL4 line 871 *)
let stack_write = prove
 (`!(stack:B list) (base:A word) p m d a v.
     (misc_word_list base stack STAR p) (fun2set (m,d)) /\ a < LENGTH stack
     ==> (misc_word_list base (LUPDATE v a stack) STAR p)
           (fun2set ((word_add base (word_mul bytes_in_word (word a)) =+ v) m,d))`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; REWRITE_TAC[LENGTH]] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `a:num` num_CASES) THEN
  REWRITE_TAC[LUPDATE_DEF; NOT_SUC; SUC_SUB1; misc_word_list_def] THENL
   [REWRITE_TAC[WORD_RULE `word_add (b:A word) (word_mul c (word 0)) = b`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`v:B`; `base:A word`; `h:B`;
                   `misc_word_list (word_add (base:A word) bytes_in_word) (t:B list) STAR
                    (p:(A word#B->bool)->bool)`;
                   `m:A word->B`; `d:A word->bool`] write_fun2set) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(set_sep_one (base:A word,h:B) STAR misc_word_list (word_add base bytes_in_word) t
                    STAR p) (fun2set (m,d))` THEN REWRITE_TAC[STAR_ASSOC];
      MESON_TAC[STAR_COMM; STAR_ASSOC]];
    REWRITE_TAC[LT_SUC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`word_add (base:A word) bytes_in_word`;
       `set_sep_one (base:A word,h:B) STAR (p:(A word#B->bool)->bool)`;
       `m:A word->B`; `d:A word->bool`; `n:num`; `v:B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(set_sep_one (base:A word,h:B) STAR misc_word_list (word_add base bytes_in_word) t
                    STAR p) (fun2set (m,d))` THEN
      MESON_TAC[STAR_COMM; STAR_ASSOC];
      ALL_TAC] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (b:A word) c) (word_mul c (word n)) =
                           word_add b (word_mul c (word (SUC n)))`] THEN
    MESON_TAC[STAR_COMM; STAR_ASSOC]]);;

(* HOL4 line 885 *)
let state_rel_stack_store = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t st b n a x.
     stack_removeProof_state_rel jump off k s t /\ st = stack_state_stack s /\
     FLOOKUP (stack_state_regs t) k = SOME (wl_Word b) /\
     stack_state_stack_space s + n < LENGTH st /\
     word_add b (word_mul bytes_in_word (word n)) = a
     ==> stack_removeProof_state_rel jump off k
           (stack_state_stack_fupd (K (LUPDATE x (n + stack_state_stack_space s) st)) s)
           (stack_state_memory_fupd (K ((a =+ x) (stack_state_memory t))) t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC; LENGTH_LUPDATE] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `st:((A)word_loc)list`
                                                 with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `a:A word`
                                                       with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `the_SOME_Word:((A)word_loc)option->A word`)) (concl th))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN EVERY_CASE_TAC THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b = word_add a' (word_mul bytes_in_word
                     (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))):A word`
    SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) k = SOME (wl_Word b)` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(rator(concl th))))) = "STAR" with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`stack_state_stack (s:(A,C,FFI)stack_state)`; `a':A word`]
                stack_write) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`memory (stack_state_memory s) (stack_state_mdomain s) STAR
      misc_word_list
        (word_shl (the_SOME_Word (FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase))
                  (backend_common_word_shift (:A)))
        (MAP wl_Word (APPEND (stack_state_bitmaps s) (buffer_buffer (stack_state_data_buffer s)))) STAR
      word_list_exists
        (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                            (backend_common_word_shift (:A)))
                  (word_mul bytes_in_word
                     (word (LENGTH (APPEND (stack_state_bitmaps s)
                                           (buffer_buffer (stack_state_data_buffer s)))))))
        (buffer_space_left (stack_state_data_buffer s)) STAR
      word_store (a':A word) (stack_state_store s)`;
     `stack_state_memory (t:(A,C,FFI)stack_state)`; `stack_state_mdomain (t:(A,C,FFI)stack_state)`;
     `n + stack_state_stack_space (s:(A,C,FFI)stack_state)`; `x:(A)word_loc`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE
    `word_add (word_add (a:A word) (word_mul b (word s))) (word_mul b (word n)) =
     word_add a (word_mul b (word (n + s)))`] THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN REWRITE_TAC[]);;

(* HOL4 line 908 *)
let lsl_word_shift = prove
 (`!w:A word.
     good_dimindex (:A)
     ==> word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_val_bytes_in_word) THEN
  SUBGOAL_THEN `bytes_in_word:A word = word (2 EXP backend_common_word_shift (:A))`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_WORD; GSYM WORD_MUL] THEN CONV_TAC WORD_RULE);;

let STACKPROPSAUX_GL_TAC : tactic =
  REPEAT (CHANGED_TAC (REWRITE_TAC[stack_get_labels_def; UNION_EMPTY] THEN CASE_REWRITE_TAC[]));;

(* HOL4 line 916 (local) *)
let get_labels_stack_free = prove
 (`!k n. stack_get_labels (stack_remove_stack_free k n:(A)stack_prog) = {}`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[single_stack_free_def] THEN
  STACKPROPSAUX_GL_TAC THEN ASM_SIMP_TAC[]);;

let STACKPROPSAUX_get_labels_single_stack_alloc = prove
 (`!jump k n. stack_get_labels (single_stack_alloc jump k n:(A)stack_prog) = {}`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `jump:bool` THEN
  REWRITE_TAC[single_stack_alloc_def; halt_inst_def] THEN STACKPROPSAUX_GL_TAC);;

(* HOL4 line 924 (local) *)
let get_labels_stack_alloc = prove
 (`!jump k n. stack_get_labels (stack_alloc jump k n:(A)stack_prog) = {}`,
  MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[STACKPROPSAUX_get_labels_single_stack_alloc] THEN
  STACKPROPSAUX_GL_TAC THEN ASM_SIMP_TAC[STACKPROPSAUX_get_labels_single_stack_alloc;
                                        UNION_EMPTY]);;

(* HOL4 line 933 (local) *)
let get_labels_upshift = prove
 (`!n n0. stack_get_labels (upshift n n0:(A)stack_prog) = {}`,
  MATCH_MP_TAC upshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[upshift_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STACKPROPSAUX_GL_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 line 941 (local) *)
let get_labels_downshift = prove
 (`!n n0. stack_get_labels (downshift n n0:(A)stack_prog) = {}`,
  MATCH_MP_TAC downshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[downshift_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STACKPROPSAUX_GL_TAC THEN ASM_SIMP_TAC[]);;

let STACKPROPSAUX_GLC_TAC : tactic =
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[stack_get_labels_def; get_labels_stack_free; get_labels_stack_alloc;
              stack_store_def; stack_load_def; get_labels_upshift; get_labels_downshift;
              stack_list_Seq_def; copy_loop_def; copy_each_def; UNION_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_get_labels_def; get_labels_upshift; get_labels_downshift; UNION_EMPTY] THEN
  CASE_REWRITE_TAC[UNION_EMPTY];;
let STACKPROPSAUX_PAIRVAR_TAC : tactic = fun (asl,w as g) ->
  let tys = [`:(A)stack_prog#num#num#num`; `:num#num#num`; `:num#num`;
             `:(A)stack_prog#num#num`] in
  let v = find (fun v -> mem (type_of v) tys) (frees w) in
  CASES_ON v g;;
let STACKPROPSAUX_GLC_REC_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "stack_prog"; distinctness "stack_prog";
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[stack_get_labels_def] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (CHANGED_TAC (STACKPROPSAUX_PAIRVAR_TAC THEN CASE_REWRITE_TAC[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"; PAIR_EQ;
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  ASM_REWRITE_TAC[stack_get_labels_def] THEN CASE_REWRITE_TAC[];;
(* HOL4 line 949 *)
let stack_removeProof_get_labels_comp = prove
 (`!jump off k (e:(A)stack_prog).
     stack_get_labels (stack_remove_comp jump off k e) = stack_get_labels e`,
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  FIRST [STACKPROPSAUX_GLC_TAC THEN NO_TAC; STACKPROPSAUX_GLC_REC_TAC THEN NO_TAC]);;

(* HOL4 line 960 *)
let code_rel_loc_check = prove
 (`!jump off k (c1:((A)stack_prog)spt) c2 l1 l2.
     stack_removeProof_code_rel jump off k c1 c2 /\ loc_check c1 (l1,l2)
     ==> loc_check c2 (l1,l2)`,
  REWRITE_TAC[loc_check_def; stack_removeProof_code_rel_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`n:num`; `stack_remove_comp jump off k (e:(A)stack_prog)`] THEN
  ASM_MESON_TAC[stack_removeProof_get_labels_comp]);;

(* HOL4 line 968 *)
let evaluate_single_stack_free = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t1 r s2 n.
     stack_removeProof_state_rel jump off k s t1 /\
     ((r,s2) = (NONE,stack_state_stack_space_fupd (K (stack_state_stack_space s + n)) s)) /\
     ~(LENGTH (stack_state_stack s) < stack_state_stack_space s + n) /\
     ~(n = 0) /\ n <= max_stack_alloc
     ==> ?ck t2.
           stack_evaluate (single_stack_free k n,
                           stack_state_clock_fupd (K (stack_state_clock t1 + ck)) t1) =
             (r,t2) /\
           stack_removeProof_state_rel jump off k s2 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (lhs (concl th)))) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[STACKPROPSAUX_clock_add_0; single_stack_free_def] THEN
  EXISTS_TAC `stack_set_var k (wl_Word (word_add (word_add c (word_mul bytes_in_word
                (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))) (word_offset n)))
                (t1:(A,C,FFI)stack_state)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
    MP_TAC(ISPECL [`asm_Add`; `k:num`; `k:num`; `word_offset n:A word`;
                   `word_add c (word_mul bytes_in_word
                      (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))):A word`;
                   `t1:(A,C,FFI)stack_state`] STACKPROPSAUX_inst_binop_imm) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `stack_get_var k (t1:(A,C,FFI)stack_state) =
                   SOME (wl_Word (word_add c (word_mul bytes_in_word
                     (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))))` THEN
      REWRITE_TAC[stack_get_var_def];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[STACKPROPSAUX_word_op_add; OPTION_MAP_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add c (word_mul bytes_in_word
                  (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))) (word_offset n) =
                word_add c (word_mul bytes_in_word (word (stack_state_stack_space s + n))):A word`
    SUBST1_TAC THENL
   [REWRITE_TAC[word_offset_eq; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[stack_set_var_def] THEN
  MATCH_MP_TAC STACKPROPSAUX_state_rel_stack_space THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `stack_get_var (k + 1) (t1:(A,C,FFI)stack_state) = SOME (wl_Word c)` THEN
    REWRITE_TAC[stack_get_var_def];
    ASM_ARITH_TAC]);;

(* HOL4 line 992 *)
let evaluate_stack_free = prove
 (`!k n r (s:(A,C,FFI)stack_state) s2 t1 jump off.
     stack_evaluate (StackFree n,s) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_removeProof_state_rel jump off k s t1
     ==> ?ck t2.
           stack_evaluate (stack_remove_stack_free k n,
                           stack_state_clock_fupd (K (ck + stack_state_clock t1)) t1) =
             (r,t2) /\
           stack_removeProof_state_rel jump off k s2 t2`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `n:num`] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`r:((A)stack_result)option`; `s:(A,C,FFI)stack_state`;
                       `s2:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`;
                       `jump:bool`; `off:A word#A word`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP STACKPROPSAUX_sr_facts) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                  stack_state_stack_space s + n) /\
                r = (NONE:((A)stack_result)option) /\
                s2 = stack_state_stack_space_fupd (K (stack_state_stack_space s + n)) s`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `stack_evaluate (StackFree n,s:(A,C,FFI)stack_state) = (r,s2)` THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "StackFree"] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(r = SOME (stack_Error:(A)stack_result))` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[STACKPROPSAUX_clock_add_0; STACKPROPSAUX_ev_clause "stack_Skip"] THEN
    EXISTS_TAC `t1:(A,C,FFI)stack_state` THEN
    SUBGOAL_THEN `stack_state_stack_space_fupd (K (stack_state_stack_space s + 0)) s =
                  (s:(A,C,FFI)stack_state)` (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[stack_state_component_equality] THEN SIMP[ADD_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n <= max_stack_alloc` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC evaluate_single_stack_free THEN
    EXISTS_TAC `s:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t1:(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`;
                 `stack_state_stack_space_fupd
                    (K (stack_state_stack_space s + max_stack_alloc)) (s:(A,C,FFI)stack_state)`;
                 `max_stack_alloc`] evaluate_single_stack_free) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[max_stack_alloc_def; ARITH_EQ] THEN
    UNDISCH_TAC `~(LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                   stack_state_stack_space s + n)` THEN
    UNDISCH_TAC `~(n <= max_stack_alloc)` THEN REWRITE_TAC[max_stack_alloc_def] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "ih" (MP_TAC o SPECL
    [`NONE:((A)stack_result)option`;
     `stack_state_stack_space_fupd (K (stack_state_stack_space s + max_stack_alloc))
        (s:(A,C,FFI)stack_state)`;
     `stack_state_stack_space_fupd (K (stack_state_stack_space s + n))
        (s:(A,C,FFI)stack_state)`;
     `t2:(A,C,FFI)stack_state`; `jump:bool`; `off:A word#A word`] o
     REWRITE_RULE[ASSUME `~(n = 0)`; ASSUME `~(n <= max_stack_alloc)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[distinctness "option"] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "StackFree"; STACKPROPSAUX_SR_ACC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(stack_state_stack_space (s:(A,C,FFI)stack_state) + max_stack_alloc) +
                  (n - max_stack_alloc) = stack_state_stack_space s + n` SUBST1_TAC THENL
     [UNDISCH_TAC `~(n <= max_stack_alloc)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    REWRITE_TAC[stack_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t3:(A,C,FFI)stack_state`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC STACKPROPSAUX_seq_clock THEN EXISTS_TAC `t2:(A,C,FFI)stack_state` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_word_offset_add = prove
 (`!a b. word_offset (a + b):A word = word_add (word_offset a) (word_offset b)`,
  REWRITE_TAC[word_offset_def; LEFT_ADD_DISTRIB; WORD_ADD]);;

let STACKPROPSAUX_inst_binop_sub_add = prove
 (`!r (x:A word) (st:(A,C,FFI)stack_state) w.
     FLOOKUP (stack_state_regs st) r = SOME (wl_Word w)
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop asm_Add r r (Imm x))),st) =
           (NONE,stack_state_regs_fupd (K (stack_state_regs st |+ (r,wl_Word (word_add w x)))) st) /\
         stack_evaluate (stack_Inst (asm_Arith (Binop asm_Sub r r (Imm x))),st) =
           (NONE,stack_state_regs_fupd (K (stack_state_regs st |+ (r,wl_Word (word_sub w x)))) st)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_inst_binop_imm th]) THEN
  REWRITE_TAC[STACKPROPSAUX_word_op_add; STACKPROPSAUX_word_op_sub; OPTION_MAP_DEF;
              stack_set_var_def]);;

(* HOL4 line 1037 (local) *)
let evaluate_upshift = prove
 (`!r n (st:(A,C,FFI)stack_state) w.
     FLOOKUP (stack_state_regs st) r = SOME (wl_Word w)
     ==> stack_evaluate (upshift r n,st) =
           (NONE,stack_state_regs_fupd
                   (K (stack_state_regs st |+ (r,wl_Word (word_add w (word_offset n))))) st)`,
  MATCH_MP_TAC upshift_ind THEN MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[upshift_def] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[STACKPROPSAUX_inst_binop_sub_add] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `stack_evaluate (upshift r (n - max_stack_alloc):(A)stack_prog,
                stack_state_regs_fupd (K (stack_state_regs st |+
                   (r,wl_Word (word_add w (word_offset max_stack_alloc))))) (st:(A,C,FFI)stack_state))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_seq_none THEN ASM_SIMP_TAC[STACKPROPSAUX_inst_binop_sub_add];
    ALL_TAC] THEN
  USE_THEN "ih" (fun th -> MP_TAC(MATCH_MP th (ASSUME `~(n <= max_stack_alloc)`))) THEN
  DISCH_THEN(fun th -> W(fun (asl,w) -> MP_TAC(SPECL
    [`stack_state_regs_fupd (K (stack_state_regs st |+
        (r,wl_Word (word_add w (word_offset max_stack_alloc))))) (st:(A,C,FFI)stack_state)`;
     `word_add (w:A word) (word_offset max_stack_alloc)`] th))) THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC; FUPDATE_EQ] THEN
  SUBGOAL_THEN `n = max_stack_alloc + (n - max_stack_alloc)` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  REWRITE_TAC[STACKPROPSAUX_word_offset_add; WORD_ADD_ASSOC]);;

(* HOL4 line 1055 (local) *)
let evaluate_downshift = prove
 (`!r n (st:(A,C,FFI)stack_state) w.
     FLOOKUP (stack_state_regs st) r = SOME (wl_Word w)
     ==> stack_evaluate (downshift r n,st) =
           (NONE,stack_state_regs_fupd
                   (K (stack_state_regs st |+ (r,wl_Word (word_sub w (word_offset n))))) st)`,
  MATCH_MP_TAC downshift_ind THEN MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[downshift_def] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[STACKPROPSAUX_inst_binop_sub_add] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `stack_evaluate (downshift r (n - max_stack_alloc):(A)stack_prog,
                stack_state_regs_fupd (K (stack_state_regs st |+
                   (r,wl_Word (word_sub w (word_offset max_stack_alloc))))) (st:(A,C,FFI)stack_state))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_seq_none THEN ASM_SIMP_TAC[STACKPROPSAUX_inst_binop_sub_add];
    ALL_TAC] THEN
  USE_THEN "ih" (fun th -> MP_TAC(MATCH_MP th (ASSUME `~(n <= max_stack_alloc)`))) THEN
  DISCH_THEN(fun th -> W(fun (asl,w) -> MP_TAC(SPECL
    [`stack_state_regs_fupd (K (stack_state_regs st |+
        (r,wl_Word (word_sub w (word_offset max_stack_alloc))))) (st:(A,C,FFI)stack_state)`;
     `word_sub (w:A word) (word_offset max_stack_alloc)`] th))) THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC; FUPDATE_EQ] THEN
  SUBGOAL_THEN `n = max_stack_alloc + (n - max_stack_alloc)` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  REWRITE_TAC[STACKPROPSAUX_word_offset_add;
              WORD_RULE `word_sub (word_sub (w:A word) a) b = word_sub w (word_add a b)`]);;

(* HOL4 line 1076 (local) *)
let name_cases = prove
 (`!name. ~(name = CurrHeap) ==> MEM name stack_remove_store_list`,
  MATCH_MP_TAC store_name_INDUCT THEN
  REWRITE_TAC[stack_remove_store_list_def; MEM; distinctness "store_name";
              injectivity "store_name"] THEN
  X_GEN_TAC `w:5 word` THEN
  MP_TAC(ISPEC `w:5 word` VAL_BOUND) THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN SUBST1_TAC(SYM(ISPEC `w:5 word` WORD_VAL)) THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`val (w:5 word)`,`v:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* the store as a list of words below base: position and update of one     *)
(* name of the store list                                                    *)

let STACKPROPSAUX_INDEX_FIND_EQ = prove
 (`!l i n (x:A).
     ALL_DISTINCT l /\ n < LENGTH l /\ EL n l = x
     ==> INDEX_FIND i (\y. y = x) l = SOME (i + n,x)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; REWRITE_TAC[LENGTH]] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; INDEX_FIND_DEF; ALL_DISTINCT; ADD_CLAUSES; NOT_SUC; LT_SUC] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(h:A = x)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SUC i`; `n':num`; `x:A`]) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let STACKPROPSAUX_ALL_DISTINCT_store_list = prove
 (`ALL_DISTINCT stack_remove_store_list`,
  REWRITE_TAC[stack_remove_store_list_def; ALL_DISTINCT; MEM; distinctness "store_name";
              injectivity "store_name"] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let STACKPROPSAUX_store_offset_pos = prove
 (`!name n. n < LENGTH stack_remove_store_list /\ EL n stack_remove_store_list = name
            ==> store_offset name:A word =
                word_sub (word 0) (word_mul bytes_in_word (word (n + 1)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[store_offset_def; store_pos_def; word_offset_eq] THEN
  MP_TAC(ISPECL [`stack_remove_store_list`; `0`; `n:num`; `name:store_name`]
                STACKPROPSAUX_INDEX_FIND_EQ) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_ALL_DISTINCT_store_list; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_word_list_rev_split = prove
 (`!(xs:B list) (a:A word) i.
     i < LENGTH xs
     ==> ?rest. !v. word_list_rev a (LUPDATE v i xs) =
                    set_sep_one (word_sub a (word_mul bytes_in_word (word (i + 1))),v) STAR
                    rest`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; REWRITE_TAC[LENGTH]] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[LUPDATE_DEF; NOT_SUC; SUC_SUB1; word_list_rev_def; LT_SUC] THENL
   [DISCH_TAC THEN EXISTS_TAC `word_list_rev (word_sub (a:A word) bytes_in_word) (t:B list)` THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_RULE `word_mul (b:A word) (word 1) = b`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_sub (a:A word) bytes_in_word`; `n:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `rest:(A word#B->bool)->bool`) THEN
  EXISTS_TAC `set_sep_one (word_sub (a:A word) bytes_in_word,h:B) STAR rest` THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_sub (a:A word) b) (word_mul b (word (n + 1))) =
                         word_sub a (word_mul b (word (SUC n + 1)))`] THEN
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

let STACKPROPSAUX_MAP_update = prove
 (`!(l:A list) (f:A->B) g i y.
     ALL_DISTINCT l /\ i < LENGTH l /\
     (!x. MEM x l /\ ~(x = EL i l) ==> g x = f x) /\ g (EL i l) = y
     ==> MAP g l = LUPDATE y i (MAP f l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_LUPDATE] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; EL_LUPDATE; LENGTH_MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[MEM_EL] THEN
  ASM_MESON_TAC[EL_ALL_DISTINCT_EL_EQ; MEM_EL]);;

let STACKPROPSAUX_word_store_split = prove
 (CASE_TERM `!(base:A word) store name.
     MEM name stack_remove_store_list
     ==> ?rest. word_store base store =
                set_sep_one (word_add base (store_offset name),
                             match FLOOKUP store name with
                               NONE -> wl_Word (word 0) | SOME x -> x) STAR rest /\
                !v. word_store base (store |+ (name,v)) =
                    set_sep_one (word_add base (store_offset name),v) STAR rest`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `name:store_name`
                                                 with Failure _ -> false)) THEN
  MP_TAC(ISPECL [CASE_TERM `MAP (\name. match FLOOKUP (store:(store_name,(A)word_loc)fmap) name with
                                NONE -> wl_Word (word 0) | SOME x -> x)
                      stack_remove_store_list`; `base:A word`; `n:num`]
                STACKPROPSAUX_word_list_rev_split) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  DISCH_THEN(X_CHOOSE_TAC `rest:(A word#(A)word_loc->bool)->bool`) THEN
  EXISTS_TAC `rest:(A word#(A)word_loc->bool)->bool` THEN
  MP_TAC(ISPECL [`EL n stack_remove_store_list`; `n:num`] STACKPROPSAUX_store_offset_pos) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[WORD_RULE `word_add (b:A word) (word_sub (word 0) x) = word_sub b x`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[word_store_def] THEN
    FIRST_ASSUM(fun th -> if is_forall (concl th) then REWRITE_TAC[GSYM th] else failwith "") THEN
    AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`n:num`; CASE_TERM `MAP (\name. match FLOOKUP (store:(store_name,(A)word_loc)fmap) name with
                                NONE -> wl_Word (word 0) | SOME x -> x)
                      stack_remove_store_list`] LUPDATE_SAME) THEN
    ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[word_store_def] THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) then REWRITE_TAC[GSYM th] else failwith "") THEN
    AP_TERM_TAC THEN
  MATCH_MP_TAC STACKPROPSAUX_MAP_update THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_ALL_DISTINCT_store_list; FLOOKUP_UPDATE] THEN
  CASE_REWRITE_TAC[] THEN SIMP_TAC[]);;

let STACKPROPSAUX_STAR_pull = prove
 (`!(x:(A->bool)->bool) o1 r w. (x STAR (o1 STAR r)) STAR w = o1 STAR ((x STAR r) STAR w)`,
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

(* HOL4 line 1088 (local) *)
let mem_load_lemma = prove
 (`!name (s:(A,C,FFI)stack_state) (t1:(A,C,FFI)stack_state) x c.
     MEM name stack_remove_store_list /\
     FLOOKUP (stack_state_store s) name = SOME x /\
     (memory (stack_state_memory s) (stack_state_mdomain s) STAR
      misc_word_list
        (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                  (backend_common_word_shift (:A)))
        (APPEND (MAP wl_Word (stack_state_bitmaps s))
                (MAP wl_Word (buffer_buffer (stack_state_data_buffer s)))) STAR
      word_list_exists
        (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                            (backend_common_word_shift (:A)))
                  (word_mul bytes_in_word
                     (word (LENGTH (buffer_buffer (stack_state_data_buffer s)) +
                            LENGTH (stack_state_bitmaps s)))))
        (buffer_space_left (stack_state_data_buffer s)) STAR
      word_store c (stack_state_store s) STAR
      misc_word_list c (stack_state_stack s))
       (fun2set (stack_state_memory t1,stack_state_mdomain t1))
     ==> stack_mem_load (word_add c (store_offset name)) t1 = SOME x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:A word`; `stack_state_store (s:(A,C,FFI)stack_state)`; `name:store_name`]
                STACKPROPSAUX_word_store_split) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(rator(concl th))))) = "STAR" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_STAR_pull] THEN
  DISCH_THEN(MP_TAC o MATCH_MP read_fun2set) THEN
  SIMP_TAC[stack_mem_load_def]);;

(* HOL4 line 1131 (local) *)
let mem_load_lemma2 = prove
 (`!name (s:(A,C,FFI)stack_state) (t1:(A,C,FFI)stack_state) c.
     MEM name stack_remove_store_list /\
     (memory (stack_state_memory s) (stack_state_mdomain s) STAR
      misc_word_list
        (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                  (backend_common_word_shift (:A)))
        (APPEND (MAP wl_Word (stack_state_bitmaps s))
                (MAP wl_Word (buffer_buffer (stack_state_data_buffer s)))) STAR
      word_list_exists
        (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                            (backend_common_word_shift (:A)))
                  (word_mul bytes_in_word
                     (word (LENGTH (buffer_buffer (stack_state_data_buffer s)) +
                            LENGTH (stack_state_bitmaps s)))))
        (buffer_space_left (stack_state_data_buffer s)) STAR
      word_store c (stack_state_store s) STAR
      misc_word_list c (stack_state_stack s))
       (fun2set (stack_state_memory t1,stack_state_mdomain t1))
     ==> word_add c (store_offset name) IN stack_state_mdomain t1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:A word`; `stack_state_store (s:(A,C,FFI)stack_state)`; `name:store_name`]
                STACKPROPSAUX_word_store_split) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(rator(concl th))))) = "STAR" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_STAR_pull] THEN
  DISCH_THEN(MP_TAC o MATCH_MP read_fun2set) THEN SIMP_TAC[]);;

(* HOL4 line 1168 (local) *)
let assoc_lem = prove
 (`!(a:(A->bool)->bool) b c. (a STAR b) STAR c = (b STAR c) STAR a`,
  MESON_TAC[STAR_ASSOC; STAR_COMM]);;

(* HOL4 line 1177 (local) *)
let store_write_lemma = prove
 (`!name (s:(A,C,FFI)stack_state) c m d x.
     MEM name stack_remove_store_list /\
     (memory (stack_state_memory s) (stack_state_mdomain s) STAR
      misc_word_list
        (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                  (backend_common_word_shift (:A)))
        (APPEND (MAP wl_Word (stack_state_bitmaps s))
                (MAP wl_Word (buffer_buffer (stack_state_data_buffer s)))) STAR
      word_list_exists
        (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                            (backend_common_word_shift (:A)))
                  (word_mul bytes_in_word
                     (word (LENGTH (buffer_buffer (stack_state_data_buffer s)) +
                            LENGTH (stack_state_bitmaps s)))))
        (buffer_space_left (stack_state_data_buffer s)) STAR
      word_store c (stack_state_store s) STAR
      misc_word_list c (stack_state_stack s)) (fun2set (m,d))
     ==> (memory (stack_state_memory s) (stack_state_mdomain s) STAR
          misc_word_list
            (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                      (backend_common_word_shift (:A)))
            (APPEND (MAP wl_Word (stack_state_bitmaps s))
                    (MAP wl_Word (buffer_buffer (stack_state_data_buffer s)))) STAR
          word_list_exists
            (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                                (backend_common_word_shift (:A)))
                      (word_mul bytes_in_word
                         (word (LENGTH (buffer_buffer (stack_state_data_buffer s)) +
                                LENGTH (stack_state_bitmaps s)))))
            (buffer_space_left (stack_state_data_buffer s)) STAR
          word_store c (stack_state_store s |+ (name,x)) STAR
          misc_word_list c (stack_state_stack s))
           (fun2set ((word_add c (store_offset name) =+ x) m,d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:A word`; `stack_state_store (s:(A,C,FFI)stack_state)`; `name:store_name`]
                STACKPROPSAUX_word_store_split) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(rator(concl th))))) = "STAR" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_STAR_pull] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `x:(A)word_loc` write_fun2set)) THEN
  MESON_TAC[STAR_COMM]);;

(* HOL4 line 1244 *)
let stack_removeProof_prog_comp_eta = prove
 (`stack_remove_prog_comp =
     \jump off k (n,p:(A)stack_prog). (n,stack_remove_comp jump off k p)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[stack_remove_prog_comp_def]);;

(* HOL4 line 1473 *)
let memory_fun2set_SUBSET = prove
 (`!(m1:A->B) d1 rest m2 d2.
     (memory m1 d1 STAR rest) (fun2set (m2,d2)) ==> d1 SUBSET d2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1:A->B`; `d1:A->bool`; `rest:(A#B->bool)->bool`; `m2:A->B`;
                 `d2:A->bool`; `x:A`] memory_fun2set_IMP_read) THEN
  ASM_SIMP_TAC[]);;

(* the element i of a word list in memory *)

let STACKPROPSAUX_word_list_read = prove
 (`!(xs:B list) (a:A word) p m d i.
     (misc_word_list a xs STAR p) (fun2set (m,d)) /\ i < LENGTH xs
     ==> m (word_add a (word_mul bytes_in_word (word i))) = EL i xs /\
         word_add a (word_mul bytes_in_word (word i)) IN d`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; REWRITE_TAC[LENGTH]] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[misc_word_list_def; EL; HD; TL; LT_SUC] THENL
   [REWRITE_TAC[WORD_RULE `word_add (b:A word) (word_mul c (word 0)) = b`; GSYM STAR_ASSOC] THEN
    MESON_TAC[read_fun2set];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`word_add (a:A word) bytes_in_word`; `set_sep_one (a:A word,h:B) STAR p`;
     `m:A word->B`; `d:A word->bool`; `n:num`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(set_sep_one (a:A word,h:B) STAR misc_word_list (word_add a bytes_in_word) t
                  STAR p) (fun2set (m,d))` THEN
    MESON_TAC[STAR_COMM; STAR_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (b:A word) c) (word_mul c (word n)) =
                         word_add b (word_mul c (word (SUC n)))`]);;

(* copy_each_thm (HOL4 line 1250) and its helpers *)

let STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM = prove
 (`!(f:(A,B)fmap) k v. FLOOKUP f k = SOME v ==> f |+ (k,v) = f`,
  REWRITE_TAC[FLOOKUP_DEF] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC FUPDATE_ELIM THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_one_mod_dimword = prove
 (`1 MOD dimword (:A) = 1`,
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[dimword_def] THEN
  MATCH_MP_TAC(ARITH_RULE `2 EXP 1 <= n ==> 1 < n`) THEN
  REWRITE_TAC[LE_EXP; DIMINDEX_GE_1] THEN ARITH_TAC);;

let STACKPROPSAUX_dec_clock_regs_mem = prove
 (`!R M (t:(A,C,FFI)stack_state) n.
     stack_dec_clock (stack_state_regs_fupd (K R) (stack_state_memory_fupd (K M)
        (stack_state_clock_fupd (K (stack_state_clock t + n + 1)) t))) =
     stack_state_clock_fupd (K (stack_state_clock t + n))
       (stack_state_regs_fupd (K R) (stack_state_memory_fupd (K M) t))`,
  REWRITE_TAC[stack_dec_clock_def; stack_state_component_equality] THEN
  SIMP[ARITH_RULE `(a + n + 1) - 1 = a + n`]);;

(* rewrites that run straight-line stackLang code *)

let STACKPROPSAUX_EVAL_SIMPS =
  [STACKPROPSAUX_ev_clause "stack_Seq"; STACKPROPSAUX_ev_clause "stack_Inst";
   STACKPROPSAUX_ev_clause "stack_If"; STACKPROPSAUX_ev_clause "stack_Skip";
   STACKPROPSAUX_ev_clause "stack_Break";
   stack_get_var_imm_def; stack_get_var_def; wl_word_cmp_def; stack_inst_def;
   stack_assign_def; stack_word_exp_def; word_op_def; word_sh_def; stack_mem_load_def;
   stack_mem_store_def; stack_set_var_def; FLOOKUP_UPDATE; LET_DEF; LET_END_DEF; MAP; ALL;
   IS_SOME_DEF; THE_DEF; ITLIST; WORD_ADD_0];;

(* the step of copy_each_thm once the loop body has been run: the goal *)
(* contains stack_dec_clock (regs_fupd (K R) (memory_fupd (K M) ...)), *)
(* from which the state for the induction hypothesis "ih" is read off   *)

let STACKPROPSAUX_COPY_EACH_STEP_TAC : tactic = fun (asl,w) ->
  let dc = find_term (fun tm -> is_comb tm && is_const (rator tm) &&
                       fst(dest_const(rator tm)) = "stack_dec_clock") w in
  let arg = rand dc in
  let rfu = rator arg and marg = rand arg in
  let mfu = rator marg in
  let tt = rand (rand marg) in
  let t' = mk_comb(rfu, mk_comb(mfu, tt)) in
  let v = rand (rand (rator (rand (rand mfu)))) in
  let yg = mk_cond(`word_ushr (pattern:A word) 1 = word 1`, v, `y:A word`) in
  (SUBGOAL_THEN `~(t1 = 1) /\ ~(t1 = 2) /\ ~(t1 = 3) /\ ~(t2 = 1) /\ ~(t2 = 2) /\
                 ~(t2 = 3) /\ ~(t2 = t1)` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   USE_THEN "ih" MP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL
     [`stack_state_mdomain (t:(A,C,FFI)stack_state)`; `i1:num`; `a1:A word`;
      `m1:A word->A word_loc`; `x:A word`; t'; `t1:num`; `t2:num`;
      `rest:(A word#A word_loc->bool)->bool`]) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE; ARITH_EQ] THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
     FIRST [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[WORD_ADD] THEN
            CONV_TAC WORD_RULE;
            ONCE_REWRITE_TAC[STAR_COMM] THEN MATCH_MP_TAC memory_write THEN
            ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[STAR_COMM] THEN
            ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_SR_ACC; copy_each_def; stack_list_Seq_def] THEN
   DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `y:A word`
     (X_CHOOSE_THEN `m2:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`ck + 1`; yg; `m2:A word->A word_loc`] THEN
   ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; stack_STOP_def;
                   STACKPROPSAUX_dec_clock_regs_mem] THEN
   REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC] THEN
   ASM_CASES_TAC `word_ushr (pattern:A word) 1 = word 1` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN X_GEN_TAC `k:num` THEN
   MAP_EVERY (fun tm -> ASM_CASES_TAC tm THENL
     [POP_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC])
     [`t2:num = k`; `1 = k`; `2 = k`; `t1:num = k`] THEN
   ASM_REWRITE_TAC[]) (asl,w);;

(* HOL4 line 1250 *)
let copy_each_thm = prove
 (`!pattern i (a:A word) off bs d m dm i1 a1 m1 x (t:(A,C,FFI)stack_state) t1 t2 rest.
     copy_words_for_pattern pattern i a off bs d m = SOME (i1,a1,m1) /\
     ALL_DISTINCT [1;2;3;t1;t2] /\ dm = stack_state_mdomain t /\ good_dimindex (:A) /\
     stack_get_var 1 t = SOME (wl_Word pattern) /\ d SUBSET dm /\
     stack_get_var 2 t = SOME (wl_Word a) /\
     stack_get_var 3 t = SOME (wl_Word off) /\
     stack_get_var t2 t = SOME (wl_Word (word_add x (word_mul bytes_in_word (word i)))) /\
     (misc_word_list x (MAP wl_Word bs) STAR rest STAR memory m d)
       (fun2set (stack_state_memory t,dm))
     ==> ?ck y m2.
           stack_evaluate (copy_each t1 t2,
                           stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
             (NONE,stack_state_memory_fupd (K m2)
                     (stack_state_regs_fupd
                        (K ((if pattern = word 1 then stack_state_regs t
                             else stack_state_regs t |+ (t1,wl_Word y))
                            |+ (2,wl_Word a1) |+ (1,wl_Word (word 1))
                            |+ (t2,wl_Word (word_add x (word_mul bytes_in_word
                                                          (word i1)))))) t)) /\
           (misc_word_list x (MAP wl_Word bs) STAR rest STAR memory m1 d) (fun2set (m2,dm))`,
  MATCH_MP_TAC copy_words_for_pattern_ind THEN
  MAP_EVERY X_GEN_TAC [`pattern:A word`; `i:num`; `a:A word`; `off:A word`;
                       `bs:(A word)list`; `d:A word->bool`; `m:A word->(A)word_loc`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`dm:A word->bool`; `i1:num`; `a1:A word`; `m1:A word->(A)word_loc`;
                       `x:A word`; `t:(A,C,FFI)stack_state`; `t1:num`; `t2:num`;
                       `rest:(A word#(A)word_loc->bool)->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "copy_words_for_pattern"
     with Failure _ -> false))) THEN
  ONCE_REWRITE_TAC[copy_words_for_pattern_def] THEN
  ASM_CASES_TAC `pattern:A word = word 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `pattern:A word = word 1` THEN ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THENL
   [(* pattern = 1: the loop exits at once *)
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `0` THEN EXISTS_TAC `stack_state_memory (t:(A,C,FFI)stack_state)` THEN
    REWRITE_TAC[STACKPROPSAUX_clock_add_0] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[copy_each_def] THEN
    GEN_REWRITE_TAC LAND_CONV [STACKPROPSAUX_ev_clause "stack_Loop"] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_If"; stack_get_var_imm_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_word_cmp_def] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Break"] THEN
    CASE_REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def] THEN
    REWRITE_TAC[PAIR_EQ; stack_state_component_equality] THEN SIMP[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM];
    ALL_TAC] THEN
  (* one round of the loop, then the induction hypothesis *)
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    can (find_term ((=) `LENGTH:(A word)list->num`)) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `dm:A word->bool`
                                                 with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`MAP wl_Word (bs:(A word)list)`; `x:A word`;
                 `(rest:(A word#(A)word_loc->bool)->bool) STAR memory (m:A word->(A)word_loc) d`;
                 `stack_state_memory (t:(A,C,FFI)stack_state)`;
                 `stack_state_mdomain (t:(A,C,FFI)stack_state)`; `i:num`]
                STACKPROPSAUX_word_list_read) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP; STAR_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:A word) IN stack_state_mdomain (t:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL_DISTINCT"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[copy_each_def] THEN ONCE_REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Loop"] THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_If"; stack_get_var_imm_def; stack_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_word_cmp_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_list_Seq_def] THEN
  SIMP STACKPROPSAUX_EVAL_SIMPS THEN
  SUBGOAL_THEN `~(1 >= dimindex(:A))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `good_dimindex(:A)`)) THEN
    REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bit 0 (pattern:A word)` THEN
  ASM_REWRITE_TAC[WORD_AND_1; WORD_NE_10; STACKPROPSAUX_one_mod_dimword] THEN
  SIMP (STACKPROPSAUX_EVAL_SIMPS @ [WORD_AND_1; WORD_NE_10; STACKPROPSAUX_one_mod_dimword]) THEN
  STACKPROPSAUX_COPY_EACH_STEP_TAC);;

(* copy_loop_thm (HOL4 line 1334) and its helpers *)

let STACKPROPSAUX_seq_cong = prove
 (`!p q (s:(A,C,FFI)stack_state) s'.
     stack_evaluate (p,s) = stack_evaluate (p,s')
     ==> stack_evaluate (stack_Seq p q,s) = stack_evaluate (stack_Seq p q,s')`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Seq"] THEN
  ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_add_clock_NONE = prove
 (`!p (s:(A,C,FFI)stack_state) s' extra.
     stack_evaluate (p,s) = (NONE,s') ==>
     stack_evaluate (p,stack_state_clock_fupd (K (stack_state_clock s + extra)) s) =
     (NONE,stack_state_clock_fupd (K (stack_state_clock s' + extra)) s')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC stack_evaluate_add_clock THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

(* the first two instructions of copy_loop *)

let STACKPROPSAUX_copy_loop_start = prove
 (`!t1 t2 (s:(A,C,FFI)stack_state) w p.
     FLOOKUP (stack_state_regs s) t2 = SOME (wl_Word w) /\
     w IN stack_state_mdomain s /\ stack_state_memory s w = wl_Word p /\ ~(t2 = 1)
     ==> stack_evaluate (copy_loop t1 t2,s) =
         stack_evaluate
           (stack_Seq
              (stack_Loop
                (stack_If asm_Less 1 (Imm (word 0))
                   (stack_list_Seq
                      [copy_each t1 t2;
                       stack_Inst (Mem asm_Load 1 (Addr t2 (word 0)));
                       stack_Inst (asm_Arith (Binop asm_Add t2 t2 (Imm bytes_in_word)))])
                   (stack_Break 0)))
              (copy_each t1 t2),
            stack_state_regs_fupd
              (K (stack_state_regs s |+ (1,wl_Word p) |+
                  (t2,wl_Word (word_add w bytes_in_word)))) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(1 = t2)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[copy_loop_def; stack_list_Seq_def] THEN
  GEN_REWRITE_TAC LAND_CONV [STACKPROPSAUX_ev_clause "stack_Seq"] THEN
  SIMP STACKPROPSAUX_EVAL_SIMPS);;

(* normal form of stack states built with field updates *)

let STACKPROPSAUX_SR_NORM =
  [stack_state_INFO.ri_accfupds; stack_state_INFO.ri_fupdfupds;
   stack_state_INFO.ri_fupdcanon; K_o_THM; K_THM];;

(* equality of register maps that differ in the order of the updates of *)
(* the registers t1, t2, 1 and 2                                          *)

let STACKPROPSAUX_REGS_EQ_TAC : tactic =
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN X_GEN_TAC `k:num` THEN
  MAP_EVERY (fun tm -> ASM_CASES_TAC tm THENL
     [POP_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC])
     [`t2:num = k`; `1 = k`; `2 = k`; `t1:num = k`] THEN
  ASM_REWRITE_TAC[];;

(* is th an equation stack_evaluate (name ..., s) = ... ? *)

let STACKPROPSAUX_is_eval_of name th =
  try let l = lhs(concl th) in
      fst(dest_const(rator l)) = "stack_evaluate" &&
      fst(dest_const(fst(strip_comb(fst(dest_pair(rand l)))))) = name
  with Failure _ -> false;;

(* HOL4 line 1334 *)
let copy_loop_thm = prove
 (`!i (a:A word) off bs d m dm a1 m1 x (t:(A,C,FFI)stack_state) t1 t2 rest.
     copy_words i a off bs d m = SOME (a1,m1) /\
     ALL_DISTINCT [1;2;3;t1;t2] /\ dm = stack_state_mdomain t /\ good_dimindex (:A) /\
     d SUBSET dm /\
     stack_get_var 2 t = SOME (wl_Word a) /\
     stack_get_var 3 t = SOME (wl_Word off) /\
     stack_get_var t2 t = SOME (wl_Word (word_add x (word_mul bytes_in_word (word i)))) /\
     (misc_word_list x (MAP wl_Word bs) STAR rest STAR memory m d)
       (fun2set (stack_state_memory t,dm))
     ==> ?ck b y y2 m2.
           stack_evaluate (copy_loop t1 t2,
                           stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
             (NONE,stack_state_memory_fupd (K m2)
                     (stack_state_regs_fupd
                        (K ((if b then stack_state_regs t
                             else stack_state_regs t |+ (t1,wl_Word y))
                            |+ (2,wl_Word a1) |+ (1,wl_Word (word 1))
                            |+ (t2,wl_Word y2))) t)) /\
           (misc_word_list x (MAP wl_Word bs) STAR rest STAR memory m1 d) (fun2set (m2,dm))`,
  MATCH_MP_TAC copy_words_ind THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `a:A word`; `off:A word`;
                       `bs:(A word)list`; `d:A word->bool`; `m:A word->(A)word_loc`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`dm:A word->bool`; `a1:A word`; `m1:A word->(A)word_loc`;
                       `x:A word`; `t:(A,C,FFI)stack_state`; `t1:num`; `t2:num`;
                       `rest:(A word#(A)word_loc->bool)->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `dm:A word->bool`
                                                 with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "copy_words"
     with Failure _ -> false))) THEN
  ONCE_REWRITE_TAC[copy_words_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `copy_words_for_pattern (EL i bs) (i + 1) (a:A word) off bs d m = NONE \/
                ?i1 a2 mq. copy_words_for_pattern (EL i bs) (i + 1) a off bs d m =
                           SOME (i1,a2,mq)`
    (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `i1:num` (X_CHOOSE_THEN `a2:A word`
       (X_CHOOSE_THEN `mq:A word->(A)word_loc` ASSUME_TAC)))) THENL
   [MESON_TAC[cases "option"; PAIR_SURJECTIVE]; CASE_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  (* the first pattern word is read and copy_each runs on it *)
  SUBGOAL_THEN `i < LENGTH (bs:(A word)list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`MAP wl_Word (bs:(A word)list)`; `x:A word`;
                 `(rest:(A word#(A)word_loc->bool)->bool) STAR memory (m:A word->(A)word_loc) d`;
                 `stack_state_memory (t:(A,C,FFI)stack_state)`;
                 `stack_state_mdomain (t:(A,C,FFI)stack_state)`; `i:num`]
                STACKPROPSAUX_word_list_read) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP; STAR_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL_DISTINCT"
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `~(t1 = 1) /\ ~(t1 = 2) /\ ~(t1 = 3) /\ ~(t2 = 1) /\ ~(t2 = 2) /\
                ~(t2 = 3) /\ ~(t2 = t1)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`EL i bs:A word`; `i + 1`; `a:A word`; `off:A word`; `bs:(A word)list`;
                 `d:A word->bool`; `m:A word->(A)word_loc`;
                 `stack_state_mdomain (t:(A,C,FFI)stack_state)`; `i1:num`; `a2:A word`;
                 `mq:A word->(A)word_loc`; `x:A word`;
                 `stack_state_regs_fupd (K (stack_state_regs t |+ (1,wl_Word (EL i bs)) |+
                    (t2,wl_Word (word_add (word_add x (word_mul bytes_in_word (word i)))
                                          bytes_in_word)))) (t:(A,C,FFI)stack_state)`;
                 `t1:num`; `t2:num`; `rest:(A word#(A)word_loc->bool)->bool`]
                copy_each_thm) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE; ARITH_EQ] THEN
    ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cke:num` (X_CHOOSE_THEN `ye:A word`
    (X_CHOOSE_THEN `me:A word->(A)word_loc` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_SR_NORM) THEN
  ASM_CASES_TAC `word_msb (EL i (bs:(A word)list))` THEN ASM_REWRITE_TAC[] THENL
   [(* msb set: one round of the loop, then the induction hypothesis *)
    DISCH_TAC THEN
    SUBGOAL_THEN `~(EL i bs = word 1:A word)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `word_msb (EL i (bs:(A word)list))` THEN
      ASM_REWRITE_TAC[word_msb_def; BIT_WORD_1] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `good_dimindex(:A)`)) THEN
      REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i1 < LENGTH (bs:(A word)list)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "copy_words"
         with Failure _ -> false))) THEN
      ONCE_REWRITE_TAC[copy_words_def] THEN COND_CASES_TAC THEN
      REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`MAP wl_Word (bs:(A word)list)`; `x:A word`;
                   `(rest:(A word#(A)word_loc->bool)->bool) STAR memory (mq:A word->(A)word_loc) d`;
                   `me:A word->(A)word_loc`;
                   `stack_state_mdomain (t:(A,C,FFI)stack_state)`; `i1:num`]
                  STACKPROPSAUX_word_list_read) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP; STAR_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP] THEN STRIP_TAC THEN
    STACKPROPSAUX_ASSUM_REWRITE_TAC `~(EL i bs = word 1:A word)` THEN
    USE_THEN "ih" (MP_TAC o SPECL [`i1:num`; `a2:A word`; `mq:A word->(A)word_loc`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`stack_state_mdomain (t:(A,C,FFI)stack_state)`; `a1:A word`; `m1:A word->(A)word_loc`;
       `x:A word`;
       `stack_state_regs_fupd (K (stack_state_regs t |+ (1,wl_Word (EL i bs)) |+
          (t2,wl_Word (word_add (word_add x (word_mul bytes_in_word (word i))) bytes_in_word)) |+
          (t1,wl_Word ye) |+ (2,wl_Word a2) |+ (1,wl_Word (word 1)) |+
          (t2,wl_Word (word_add x (word_mul bytes_in_word (word i1))))))
          (stack_state_memory_fupd (K me) (t:(A,C,FFI)stack_state))`;
       `t1:num`; `t2:num`; `rest:(A word#(A)word_loc->bool)->bool`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE; ARITH_EQ] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `b2:bool` (X_CHOOSE_THEN `y3:A word`
      (X_CHOOSE_THEN `y4:A word` (X_CHOOSE_THEN `m4:A word->(A)word_loc`
         STRIP_ASSUME_TAC))))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_SR_NORM) THEN
    FIRST_X_ASSUM(fun th ->
      if STACKPROPSAUX_is_eval_of "copy_loop" th then
        let s = snd(dest_pair(rand(lhs(concl th)))) in
        MP_TAC th THEN
        MP_TAC(ISPECL [`t1:num`; `t2:num`; s;
                       `word_add x (word_mul bytes_in_word (word i1)):A word`;
                       `EL i1 bs:A word`] STACKPROPSAUX_copy_loop_start)
      else failwith "not copy_loop") THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC (FLOOKUP_UPDATE :: STACKPROPSAUX_SR_NORM); ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if STACKPROPSAUX_is_eval_of "copy_each" th then
        MP_TAC(SPEC `ck2 + 1` (MATCH_MP STACKPROPSAUX_add_clock_NONE th))
      else failwith "not copy_each") THEN
    REWRITE_TAC(GSYM ADD_ASSOC :: STACKPROPSAUX_SR_NORM) THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_SR_NORM) THEN
    MAP_EVERY EXISTS_TAC [`cke + ck2 + 1`; `F`; `if b2 then ye else y3:A word`; `y4:A word`;
                          `m4:A word->(A)word_loc`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t1:num`; `t2:num`;
                   `stack_state_clock_fupd (K (stack_state_clock t + cke + ck2 + 1))
                      (t:(A,C,FFI)stack_state)`;
                   `word_add x (word_mul bytes_in_word (word i)):A word`; `EL i bs:A word`]
                  STACKPROPSAUX_copy_loop_start) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[STACKPROPSAUX_SR_ACC]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
    FIRST_ASSUM(fun th ->
      if STACKPROPSAUX_is_eval_of "stack_Seq" th then
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (lhs(concl th))
      else failwith "no Seq") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_seq_cong THEN
      GEN_REWRITE_TAC LAND_CONV [STACKPROPSAUX_ev_clause "stack_Loop"] THEN
      REWRITE_TAC[stack_list_Seq_def] THEN
      SIMP (STACKPROPSAUX_EVAL_SIMPS @ [GSYM word_msb_neg; stack_cont_loop_def;
        stack_exit_loop_def; stack_dec_clock_def; stack_STOP_def;
        ARITH_RULE `(a + b + 1) - 1 = a + b`; ADD_EQ_0; ARITH_EQ]);
      FIRST_ASSUM(fun th ->
        if STACKPROPSAUX_is_eval_of "stack_Seq" th then REWRITE_TAC[th]
        else failwith "no Seq") THEN
      REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC] THEN
      ASM_CASES_TAC `b2:bool` THEN ASM_REWRITE_TAC[] THEN
      STACKPROPSAUX_REGS_EQ_TAC];
    (* msb clear: the loop exits at once and copy_each runs on the last word *)
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`cke:num`; `EL i bs = word 1:A word`; `ye:A word`;
                          `word_add x (word_mul bytes_in_word (word i1)):A word`;
                          `me:A word->(A)word_loc`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t1:num`; `t2:num`;
                   `stack_state_clock_fupd (K (stack_state_clock t + cke))
                      (t:(A,C,FFI)stack_state)`;
                   `word_add x (word_mul bytes_in_word (word i)):A word`; `EL i bs:A word`]
                  STACKPROPSAUX_copy_loop_start) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[STACKPROPSAUX_SR_ACC]; DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Seq"] THEN
    ONCE_REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Loop"] THEN
    SIMP (STACKPROPSAUX_EVAL_SIMPS @ [GSYM word_msb_neg; stack_cont_loop_def;
                                      stack_exit_loop_def]) THEN
    REWRITE_TAC[stack_state_component_equality; STACKPROPSAUX_SR_ACC] THEN
    ASM_CASES_TAC `EL i bs = word 1:A word` THEN ASM_REWRITE_TAC[] THEN
    STACKPROPSAUX_REGS_EQ_TAC]);;

(* comp_correct (HOL4 line 1481), case by case: STACKPROPSAUX_cc p s is  *)
(* its statement for one program and state                               *)

let STACKPROPSAUX_cc_def = new_definition (CASE_TERM
 `STACKPROPSAUX_cc (p:(A)stack_prog) (s1:(A,C,FFI)stack_state) <=>
    !r s2 t1 k off jump.
     stack_evaluate (p,s1) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_removeProof_state_rel jump off k s1 t1 /\ reg_bound p k
     ==> ?ck t2.
           stack_evaluate (stack_remove_comp jump off k p,
                           stack_state_clock_fupd (K (ck + stack_state_clock t1)) t1) =
             (r,t2) /\
           (match r with
              SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
            | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
            | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
            | _ -> stack_removeProof_state_rel jump off k s2 t2)`);;

(* the setup of a comp_correct case: unfold STACKPROPSAUX_cc and the       *)
(* compiler on the goal; the evaluation equation stays in the goal        *)

let STACKPROPSAUX_CC_SETUP_TAC : tactic =
  REWRITE_TAC[STACKPROPSAUX_cc_def] THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[reg_bound_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC);;

let STACKPROPSAUX_cc_Skip = prove
 (`!s:(A,C,FFI)stack_state. STACKPROPSAUX_cc stack_Skip s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Skip"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)stack_state`] THEN
  REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Skip"]);;

(* a leaf of a comp_correct case: the evaluation equation (R,S) = (r,s2) *)
(* is in the goal; error results are refuted, otherwise ck = 0          *)

let STACKPROPSAUX_CC_LEAF_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN CASE_REWRITE_TAC[];;

(* case split on an option-valued term, naming the SOME value and keeping *)
(* the equation as an assumption                                          *)

let STACKPROPSAUX_OPT_CASES_TAC (tm:term) (v:term) : tactic =
  MP_TAC(ISPEC tm (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)
     (X_CHOOSE_THEN v (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)));;

let STACKPROPSAUX_cc_Halt = prove
 (`!v (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Halt v) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Halt"] THEN
  SUBGOAL_THEN `stack_get_var v (s:(A,C,FFI)stack_state) =
                stack_get_var v (t1:(A,C,FFI)stack_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
  REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC] THEN
  CASES_ON `FLOOKUP (stack_state_regs (t1:(A,C,FFI)stack_state)) v` THEN
  CASE_REWRITE_TAC[] THEN STACKPROPSAUX_CC_LEAF_TAC THEN
  REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
  ASM_MESON_TAC[STACKPROPSAUX_sr_facts]);;

let STACKPROPSAUX_cc_Alloc = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Alloc n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  SUBGOAL_THEN `~stack_state_use_alloc (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Alloc"] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_MESON_TAC[]);;

let STACKPROPSAUX_cc_Inst = prove
 (`!i (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Inst i) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Inst"] THEN
  STACKPROPSAUX_OPT_CASES_TAC `stack_inst i (s:(A,C,FFI)stack_state)`
    `s3:(A,C,FFI)stack_state` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `?t3. stack_inst i (t1:(A,C,FFI)stack_state) = SOME t3 /\
                     stack_removeProof_state_rel jump off k (s3:(A,C,FFI)stack_state) t3`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_inst]; ALL_TAC] THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_cc_Tick = prove
 (`!s:(A,C,FFI)stack_state. STACKPROPSAUX_cc stack_Tick s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Tick"; STACKPROPSAUX_SR_ACC] THEN
  SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) =
                stack_state_clock (t1:(A,C,FFI)stack_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  COND_CASES_TAC THEN STACKPROPSAUX_CC_LEAF_TAC THENL
   [REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
    ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
    ASM_MESON_TAC[state_rel_IMP]]);;

let STACKPROPSAUX_cc_Return = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Return n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Return"] THEN
  SUBGOAL_THEN `stack_get_var n (s:(A,C,FFI)stack_state) =
                stack_get_var n (t1:(A,C,FFI)stack_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
  REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC] THEN
  CASES_ON `FLOOKUP (stack_state_regs (t1:(A,C,FFI)stack_state)) n` THEN
  CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_CC_LEAF_TAC);;

let STACKPROPSAUX_cc_Raise = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Raise n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Raise"] THEN
  SUBGOAL_THEN `stack_get_var n (s:(A,C,FFI)stack_state) =
                stack_get_var n (t1:(A,C,FFI)stack_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
  REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC] THEN
  CASES_ON `FLOOKUP (stack_state_regs (t1:(A,C,FFI)stack_state)) n` THEN
  CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_CC_LEAF_TAC);;

let STACKPROPSAUX_cc_Break = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Break n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Break"] THEN
  STACKPROPSAUX_CC_LEAF_TAC);;

let STACKPROPSAUX_cc_Continue = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Continue n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Continue"] THEN
  STACKPROPSAUX_CC_LEAF_TAC);;

let STACKPROPSAUX_add_clock_cc = prove
 (`!p (t:(A,C,FFI)stack_state) ck1 ck2 t2.
     stack_evaluate (p,stack_state_clock_fupd (K (ck1 + stack_state_clock t)) t) = (NONE,t2)
     ==> stack_evaluate (p,stack_state_clock_fupd (K ((ck1 + ck2) + stack_state_clock t)) t) =
         (NONE,stack_state_clock_fupd (K (ck2 + stack_state_clock t2)) t2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `ck2:num` o MATCH_MP STACKPROPSAUX_add_clock_NONE) THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  SUBGOAL_THEN `(ck1 + ck2) + stack_state_clock (t:(A,C,FFI)stack_state) =
                (ck1 + stack_state_clock t) + ck2 /\
                ck2 + stack_state_clock (t2:(A,C,FFI)stack_state) = stack_state_clock t2 + ck2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ARITH_TAC; REWRITE_TAC[]]);;

let STACKPROPSAUX_cc_Seq = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state).
     STACKPROPSAUX_cc c1 s /\
     (!s1. stack_evaluate (c1,s) = (NONE,s1) ==> STACKPROPSAUX_cc c2 s1)
     ==> STACKPROPSAUX_cc (stack_Seq c1 c2) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (c1,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res:((A)stack_result)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`NONE:((A)stack_result)option`;
      `s1:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`; `k:num`;
      `off:A word#A word`; `jump:bool`] o REWRITE_RULE[STACKPROPSAUX_cc_def]) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `STACKPROPSAUX_cc c2 (s1:(A,C,FFI)stack_state)` MP_TAC THENL
     [USE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[STACKPROPSAUX_cc_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`;
      `s2:(A,C,FFI)stack_state`; `t2:(A,C,FFI)stack_state`; `k:num`;
      `off:A word#A word`; `jump:bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `t3:(A,C,FFI)stack_state`] THEN
    FIRST_ASSUM(fun th -> if STACKPROPSAUX_is_eval_of "stack_remove_comp" th &&
                          rand(lhs(concl th)) <> `r:((A)stack_result)option`
                          then REWRITE_TAC[MATCH_MP STACKPROPSAUX_add_clock_cc th]
                          else failwith "no") THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o REWRITE_RULE[PAIR_EQ]) THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`res:((A)stack_result)option`;
      `s1:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`; `k:num`;
      `off:A word#A word`; `jump:bool`] o REWRITE_RULE[STACKPROPSAUX_cc_def]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1:num`; `t2:(A,C,FFI)stack_state`] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

let STACKPROPSAUX_get_var_clock = prove
 (`!r c (t:(A,C,FFI)stack_state).
     stack_get_var r (stack_state_clock_fupd (K c) t) = stack_get_var r t`,
  REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_get_var_imm_clock = prove
 (`!ri c (t:(A,C,FFI)stack_state).
     stack_get_var_imm ri (stack_state_clock_fupd (K c) t) = stack_get_var_imm ri t`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[stack_get_var_imm_def; stack_get_var_def; STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_get_var_imm_rel = prove
 (CASE_TERM `!jump off k (s:(A,C,FFI)stack_state) t ri.
     stack_removeProof_state_rel jump off k s t /\
     (match ri with Reg n -> n < k | _ -> T)
     ==> stack_get_var_imm ri s = stack_get_var_imm ri t`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  CASE_REWRITE_TAC[stack_get_var_imm_def] THEN MESON_TAC[state_rel_get_var]);;

let STACKPROPSAUX_cc_If = prove
 (`!cmp r1 ri c1 c2 (s:(A,C,FFI)stack_state).
    (!x y b. stack_get_var r1 s = SOME x /\ stack_get_var_imm ri s = SOME y /\
             wl_word_cmp cmp x y = SOME b /\ b ==> STACKPROPSAUX_cc c1 s) /\
    (!x y b. stack_get_var r1 s = SOME x /\ stack_get_var_imm ri s = SOME y /\
             wl_word_cmp cmp x y = SOME b /\ ~b ==> STACKPROPSAUX_cc c2 s)
    ==> STACKPROPSAUX_cc (stack_If cmp r1 ri c1 c2) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_If"; STACKPROPSAUX_get_var_clock;
              STACKPROPSAUX_get_var_imm_clock] THEN
  SUBGOAL_THEN `stack_get_var r1 (t1:(A,C,FFI)stack_state) = stack_get_var r1 (s:(A,C,FFI)stack_state) /\
                stack_get_var_imm ri t1 = stack_get_var_imm ri (s:(A,C,FFI)stack_state)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_MESON_TAC[state_rel_get_var; STACKPROPSAUX_get_var_imm_rel]; ALL_TAC] THEN
  STACKPROPSAUX_OPT_CASES_TAC `stack_get_var r1 (s:(A,C,FFI)stack_state)`
    `x:(A)word_loc` THEN CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  STACKPROPSAUX_OPT_CASES_TAC `stack_get_var_imm ri (s:(A,C,FFI)stack_state)`
    `y:(A)word_loc` THEN CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  STACKPROPSAUX_OPT_CASES_TAC `wl_word_cmp cmp (x:(A)word_loc) y` `b:bool` THEN
  CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [USE_THEN "ih1" (MP_TAC o SPECL [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`]);
    USE_THEN "ih2" (MP_TAC o SPECL [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`])] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[STACKPROPSAUX_cc_def]]) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`;
      `s2:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`; `k:num`;
      `off:A word#A word`; `jump:bool`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]));;

let STACKPROPSAUX_cc_case_exit_loop = prove
 (CASE_TERM `!(res:((A)stack_result)option) (s2:(A,C,FFI)stack_state) t2 jump off k.
    ~stack_cont_loop res /\
    (match res with
       SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
     | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
     | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
     | _ -> stack_removeProof_state_rel jump off k s2 t2)
    ==> (match stack_exit_loop res with
           SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
         | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
         | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
         | _ -> stack_removeProof_state_rel jump off k s2 t2)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)stack_result` THEN
  CASE_REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def] THEN
  REPEAT GEN_TAC THEN TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let STACKPROPSAUX_cc_case_cont_loop = prove
 (CASE_TERM `!(res:((A)stack_result)option) (s2:(A,C,FFI)stack_state) t2 jump off k.
    stack_cont_loop res /\
    (match res with
       SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
     | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
     | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
     | _ -> stack_removeProof_state_rel jump off k s2 t2)
    ==> stack_removeProof_state_rel jump off k s2 t2 /\ ~(res = SOME stack_TimeOut)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[stack_cont_loop_def; option_DISTINCT] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)stack_result` THEN
  CASE_REWRITE_TAC[stack_cont_loop_def; option_INJ; distinctness "stack_result"] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_add_clock_cc2 = prove
 (`!p (t:(A,C,FFI)stack_state) ck1 ck2 res t2.
     stack_evaluate (p,stack_state_clock_fupd (K (ck1 + stack_state_clock t)) t) = (res,t2) /\
     ~(res = SOME stack_TimeOut)
     ==> stack_evaluate (p,stack_state_clock_fupd (K ((ck1 + ck2) + stack_state_clock t)) t) =
         (res,stack_state_clock_fupd (K (ck2 + stack_state_clock t2)) t2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o INST [`ck2:num`,`extra:num`] o MATCH_MP stack_evaluate_add_clock) THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  SUBGOAL_THEN `(ck1 + ck2) + stack_state_clock (t:(A,C,FFI)stack_state) =
                (ck1 + stack_state_clock t) + ck2 /\
                ck2 + stack_state_clock (t2:(A,C,FFI)stack_state) = stack_state_clock t2 + ck2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ARITH_TAC; REWRITE_TAC[]]);;

let STACKPROPSAUX_comp_Loop = prove
 (`!jump off k (p:(A)stack_prog).
     stack_remove_comp jump off k (stack_Loop p) = stack_Loop (stack_remove_comp jump off k p)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [stack_remove_comp_def] THEN
  CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_cc_Loop = prove
 (`!c1 (s:(A,C,FFI)stack_state).
    STACKPROPSAUX_cc c1 s /\
    (!res s1. stack_evaluate (c1,s) = (res,s1) /\ stack_cont_loop res /\
              ~(stack_state_clock s1 = 0)
              ==> STACKPROPSAUX_cc (stack_STOP (stack_Loop c1)) (stack_dec_clock s1))
    ==> STACKPROPSAUX_cc (stack_Loop c1) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  STACKPROPSAUX_CC_SETUP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STACKPROPSAUX_ev_clause "stack_Loop"] THEN
  MP_TAC(ISPEC `stack_evaluate (c1,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_cont_loop (res:((A)stack_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(res = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_cont_loop_def]) THEN
      FIRST_ASSUM CONTR_TAC; ALL_TAC];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o REWRITE_RULE[PAIR_EQ]) THEN
    SUBGOAL_THEN `~(res = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_exit_loop_def]) THEN
      FIRST_ASSUM CONTR_TAC; ALL_TAC]] THEN
  USE_THEN "ih1" (MP_TAC o SPECL [`res:((A)stack_result)option`;
     `s1:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`; `k:num`;
     `off:A word#A word`; `jump:bool`] o REWRITE_RULE[STACKPROPSAUX_cc_def]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THENL
   [(* the body continues the loop *)
    MP_TAC(ISPECL [`res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`;
                   `t2:(A,C,FFI)stack_state`; `jump:bool`; `off:A word#A word`; `k:num`]
                  STACKPROPSAUX_cc_case_cont_loop) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `stack_state_clock (t2:(A,C,FFI)stack_state) =
                  stack_state_clock (s1:(A,C,FFI)stack_state)`
      ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
    ASM_CASES_TAC `stack_state_clock (s1:(A,C,FFI)stack_state) = 0` THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o REWRITE_RULE[PAIR_EQ]) THEN
      MAP_EVERY EXISTS_TAC [`ck1:num`; `stack_empty_env (t2:(A,C,FFI)stack_state)`] THEN
      REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Loop"] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
      ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
      DISCH_TAC THEN
      USE_THEN "ih2" (MP_TAC o SPECL [`res:((A)stack_result)option`;
                                      `s1:(A,C,FFI)stack_state`]) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[STACKPROPSAUX_cc_def]]) THEN
      DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`;
         `s2:(A,C,FFI)stack_state`; `stack_dec_clock (t2:(A,C,FFI)stack_state)`; `k:num`;
         `off:A word#A word`; `jump:bool`]) THEN
      (ANTS_TAC THENL
        [ASM_SIMP_TAC[state_rel_IMP] THEN REWRITE_TAC[stack_STOP_def; reg_bound_def] THEN
         ASM_REWRITE_TAC[];
         ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `t3:(A,C,FFI)stack_state`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Loop"] THEN
      FIRST_ASSUM(fun th ->
        if STACKPROPSAUX_is_eval_of "stack_remove_comp" th &&
           rand(fst(dest_pair(rand(lhs(concl th))))) = `c1:(A)stack_prog`
        then REWRITE_TAC[MATCH_MP STACKPROPSAUX_add_clock_cc2
               (CONJ th (ASSUME `~(res = SOME (stack_TimeOut:(A)stack_result))`))]
        else failwith "no") THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[STACKPROPSAUX_SR_ACC; ADD_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        STACKPROPSAUX_is_eval_of "stack_remove_comp" th &&
        rand(lhs(concl th)) <> `c1:(A)stack_prog` &&
        can (find_term ((=) `stack_STOP:(A)stack_prog->(A)stack_prog`)) (concl th))) THEN
      REWRITE_TAC[stack_STOP_def; STACKPROPSAUX_comp_Loop; stack_dec_clock_def] THEN
      REWRITE_TAC STACKPROPSAUX_SR_NORM THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(ck2 + stack_state_clock (s1:(A,C,FFI)stack_state)) - 1 =
                    ck2 + (stack_state_clock s1 - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[]]];
    (* the loop exits *)
    MAP_EVERY EXISTS_TAC [`ck1:num`; `t2:(A,C,FFI)stack_state`] THEN
    REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Loop"] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STACKPROPSAUX_cc_case_exit_loop THEN ASM_REWRITE_TAC[]]);;

let STACKPROPSAUX_state_rel_set_CurrHeap = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t w.
     stack_removeProof_state_rel jump off k s t
     ==> stack_removeProof_state_rel jump off k (stack_set_store CurrHeap w s)
                                     (stack_set_var (k + 2) w t)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; stack_set_store_def; stack_set_var_def;
              STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name";
                  ARITH_RULE `~(k + 2 = k + 1) /\ ~(k + 2 = k)`; word_store_CurrHeap] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k + 2 = n)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

let STACKPROPSAUX_state_rel_set_store = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t name w c.
     stack_removeProof_state_rel jump off k s t /\
     ~(name = CurrHeap) /\ ~(name = BitmapBase) /\
     FLOOKUP (stack_state_regs t) (k + 1) = SOME (wl_Word c)
     ==> word_add c (store_offset name) IN stack_state_mdomain t /\
         stack_removeProof_state_rel jump off k (stack_set_store name w s)
           (stack_state_memory_fupd
              (K ((word_add c (store_offset name) =+ w) (stack_state_memory t))) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c':A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  SUBGOAL_THEN `c':A word = c` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) (k + 1) =
                 SOME (wl_Word c')` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM name stack_remove_store_list` ASSUME_TAC THENL
   [ASM_MESON_TAC[name_cases]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC mem_load_lemma2 THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`name:store_name`; `s:(A,C,FFI)stack_state`; `c:A word`;
                 `stack_state_memory (t:(A,C,FFI)stack_state)`;
                 `stack_state_mdomain (t:(A,C,FFI)stack_state)`; `w:(A)word_loc`]
                store_write_lemma) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t` THEN
  REWRITE_TAC[stack_removeProof_state_rel_def; stack_set_store_def; STACKPROPSAUX_SR_ACC;
              LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP_APPEND; LENGTH_APPEND] THEN
  REWRITE_TAC[ISPECL [`LENGTH (stack_state_bitmaps (s:(A,C,FFI)stack_state))`;
                      `LENGTH (buffer_buffer (stack_state_data_buffer (s:(A,C,FFI)stack_state)))`]
                     ADD_SYM] THEN
  ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_cc_Get = prove
 (`!v name (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Get v name) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  SUBGOAL_THEN `stack_state_use_store (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Get"] THEN ASM_REWRITE_TAC[] THEN
  STACKPROPSAUX_OPT_CASES_TAC `FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) name`
    `x:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `stack_set_var v x (t1:(A,C,FFI)stack_state)` THEN
  ASM_SIMP_TAC[stack_removeProof_state_rel_set_var] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                MATCH_MP STACKPROPSAUX_sr_facts2) THEN
    SIMP STACKPROPSAUX_EVAL_SIMPS;
    FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
    SUBGOAL_THEN `stack_mem_load (word_add c (store_offset name)) (t1:(A,C,FFI)stack_state) =
                  SOME x` ASSUME_TAC THENL
     [MATCH_MP_TAC mem_load_lemma THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
      ASM_SIMP_TAC[name_cases];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
    SIMP (subtract STACKPROPSAUX_EVAL_SIMPS [stack_mem_load_def])]);;

let STACKPROPSAUX_cc_Set = prove
 (`!name v (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_Set name v) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  SUBGOAL_THEN `stack_state_use_store (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Set"] THEN ASM_REWRITE_TAC[] THEN
  STACKPROPSAUX_OPT_CASES_TAC `stack_get_var v (s:(A,C,FFI)stack_state)` `w:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `stack_get_var v (t1:(A,C,FFI)stack_state) = SOME w` ASSUME_TAC THENL
   [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `stack_set_var (k + 2) w (t1:(A,C,FFI)stack_state)` THEN
    ASM_SIMP_TAC[STACKPROPSAUX_state_rel_set_CurrHeap] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    SIMP STACKPROPSAUX_EVAL_SIMPS;
    FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                   `t1:(A,C,FFI)stack_state`; `name:store_name`; `w:(A)word_loc`; `c:A word`]
                  STACKPROPSAUX_state_rel_set_store) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `stack_state_memory_fupd
                  (K ((word_add c (store_offset name) =+ w) (stack_state_memory t1)))
                  (t1:(A,C,FFI)stack_state)` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP STACKPROPSAUX_EVAL_SIMPS]);;

let STACKPROPSAUX_cc_OpCurrHeap = prove
 (`!binop v src (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_OpCurrHeap binop v src) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_store (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
    [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_OpCurrHeap"] THEN ASM_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC
     `stack_word_exp (s:(A,C,FFI)stack_state) (wl_Op binop [wl_Var src; Lookup CurrHeap])`
     `w:A word` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `stack_set_var v (wl_Word w) (t1:(A,C,FFI)stack_state)` THEN
   ASM_SIMP_TAC[stack_removeProof_state_rel_set_var] THEN
   FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
               MATCH_MP STACKPROPSAUX_sr_facts2) THEN
   SUBGOAL_THEN `FLOOKUP (stack_state_regs (t1:(A,C,FFI)stack_state)) src =
                 FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) src` ASSUME_TAC THENL
    [ASM_MESON_TAC[STACKPROPSAUX_sr_code_regs]; ALL_TAC] THEN
   SUBGOAL_THEN `~(k + 2 = src)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `stack_word_exp (s:(A,C,FFI)stack_state)
                  (wl_Op binop [wl_Var src; Lookup CurrHeap]) = SOME w` THEN
   SIMP STACKPROPSAUX_EVAL_SIMPS);;

let STACKPROPSAUX_cc_StackAlloc = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackAlloc n) s`,
  REWRITE_TAC[STACKPROPSAUX_cc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `k:num`; `n:num`; `r:((A)stack_result)option`;
                 `s:(A,C,FFI)stack_state`; `s2:(A,C,FFI)stack_state`;
                 `t1:(A,C,FFI)stack_state`; `off:A word#A word`] evaluate_stack_alloc) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  UNDISCH_TAC `stack_evaluate (StackAlloc n,s:(A,C,FFI)stack_state) = r,s2` THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "StackAlloc"] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "stack_result";
                              injectivity "stack_result"]) THEN
  ASM_MESON_TAC[]);;

let STACKPROPSAUX_cc_StackFree = prove
 (`!n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackFree n) s`,
  REWRITE_TAC[STACKPROPSAUX_cc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `n:num`; `r:((A)stack_result)option`;
                 `s:(A,C,FFI)stack_state`; `s2:(A,C,FFI)stack_state`;
                 `t1:(A,C,FFI)stack_state`; `jump:bool`; `off:A word#A word`]
                evaluate_stack_free) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  UNDISCH_TAC `stack_evaluate (StackFree n,s:(A,C,FFI)stack_state) = r,s2` THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "StackFree"] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the stack of s sits at the base c in register k + 1 of t *)

let STACKPROPSAUX_sr_stack_load = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t i.
     stack_removeProof_state_rel jump off k s t /\ i < LENGTH (stack_state_stack s)
     ==> ?c. FLOOKUP (stack_state_regs t) (k + 1) = SOME (wl_Word c) /\
             FLOOKUP (stack_state_regs t) k =
               SOME (wl_Word (word_add c (word_mul bytes_in_word
                                            (word (stack_state_stack_space s))))) /\
             stack_mem_load (word_add c (word_mul bytes_in_word (word i))) t =
               SOME (EL i (stack_state_stack s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
  EXISTS_TAC `c:A word` THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                             "STAR" with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] STACKPROPSAUX_word_list_read)) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[stack_mem_load_def]);;

let STACKPROPSAUX_eval_stack_load = prove
 (`!r n (t:(A,C,FFI)stack_state) w v.
     FLOOKUP (stack_state_regs t) r = SOME (wl_Word w) /\
     stack_mem_load (word_add w (word_offset n)) t = SOME v
     ==> stack_evaluate (stack_load r n,t) = (NONE,stack_set_var r v t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_load_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_ev_seq_none
    (SPEC `n:num` (MATCH_MP evaluate_upshift th))]) THEN
  MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
  UNDISCH_TAC `stack_mem_load (word_add w (word_offset n)) (t:(A,C,FFI)stack_state) = SOME v` THEN
  REWRITE_TAC[stack_mem_load_def] THEN
  SIMP (subtract STACKPROPSAUX_EVAL_SIMPS [stack_mem_load_def] @
        [stack_mem_load_def; STACKPROPSAUX_SR_ACC]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[stack_set_var_def] THEN REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  REWRITE_TAC[FUPDATE_EQ]);;

let STACKPROPSAUX_mem_load_set_var = prove
 (`!a r v (t:(A,C,FFI)stack_state).
     stack_mem_load a (stack_set_var r v t) = stack_mem_load a t`,
  REWRITE_TAC[stack_mem_load_def; stack_set_var_def; STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_cc_StackLoad = prove
 (`!r n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackLoad r n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "StackLoad"] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t1:(A,C,FFI)stack_state`;
                 `stack_state_stack_space (s:(A,C,FFI)stack_state) + n`]
                STACKPROPSAUX_sr_stack_load) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `stack_set_var r (EL (stack_state_stack_space (s:(A,C,FFI)stack_state) + n)
                (stack_state_stack s)) (t1:(A,C,FFI)stack_state)` THEN
  ASM_SIMP_TAC[stack_removeProof_state_rel_set_var] THEN
  SUBGOAL_THEN `word_add (word_add (c:A word) (word_mul bytes_in_word
                  (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))))
                  (word_offset n) =
                word_add c (word_mul bytes_in_word (word (stack_state_stack_space s + n)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[word_offset_eq; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
    SIMP (subtract STACKPROPSAUX_EVAL_SIMPS [stack_mem_load_def]);
    MP_TAC(ISPECL [`stack_Inst (asm_Arith (Binop asm_Or r k (Reg k))):(A)stack_prog`;
                   `stack_load r n:(A)stack_prog`; `t1:(A,C,FFI)stack_state`;
                   `stack_set_var r (wl_Word (word_add c (word_mul bytes_in_word
                      (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))))
                      (t1:(A,C,FFI)stack_state)`]
                  STACKPROPSAUX_ev_seq_none) THEN
    (ANTS_TAC THENL [MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN SIMP STACKPROPSAUX_EVAL_SIMPS;
                     DISCH_THEN SUBST1_TAC]) THEN
    MP_TAC(ISPECL [`r:num`; `n:num`;
                   `stack_set_var r (wl_Word (word_add c (word_mul bytes_in_word
                      (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))))
                      (t1:(A,C,FFI)stack_state)`;
                   `word_add c (word_mul bytes_in_word
                      (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))):A word`;
                   `EL (stack_state_stack_space (s:(A,C,FFI)stack_state) + n)
                       (stack_state_stack s)`]
                  STACKPROPSAUX_eval_stack_load) THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[STACKPROPSAUX_mem_load_set_var; stack_set_var_def;
                       STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE];
       DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[stack_set_var_def] THEN REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
    REWRITE_TAC[FUPDATE_EQ]]);;

let STACKPROPSAUX_mem_load_IN = prove
 (`!a (t:(A,C,FFI)stack_state) v.
     stack_mem_load a t = SOME v ==> a IN stack_state_mdomain t`,
  REWRITE_TAC[stack_mem_load_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let STACKPROPSAUX_eval_stack_store = prove
 (`!k r n (t:(A,C,FFI)stack_state) b v.
     FLOOKUP (stack_state_regs t) k = SOME (wl_Word b) /\
     FLOOKUP (stack_state_regs t) r = SOME v /\ ~(r = k) /\
     word_add b (word_offset n) IN stack_state_mdomain t
     ==> stack_evaluate (stack_store k r n,t) =
         (NONE,stack_state_memory_fupd
                 (K ((word_add b (word_offset n) =+ v) (stack_state_memory t))) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_store_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_ev_seq_none
    (SPEC `n:num` (MATCH_MP evaluate_upshift th))]) THEN
  SUBGOAL_THEN `~(k = r:num)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `stack_evaluate (downshift k n,
                stack_state_memory_fupd
                  (K ((word_add b (word_offset n) =+ v) (stack_state_memory t)))
                  (stack_state_regs_fupd
                     (K (stack_state_regs t |+ (k,wl_Word (word_add b (word_offset n)))))
                     (t:(A,C,FFI)stack_state)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_seq_none THEN MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
    SIMP STACKPROPSAUX_EVAL_SIMPS;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `n:num`;
                 `stack_state_memory_fupd
                    (K ((word_add b (word_offset n) =+ v) (stack_state_memory t)))
                    (stack_state_regs_fupd
                       (K (stack_state_regs t |+ (k,wl_Word (word_add b (word_offset n)))))
                       (t:(A,C,FFI)stack_state))`;
                 `word_add (b:A word) (word_offset n)`] evaluate_downshift) THEN
  ANTS_TAC THENL [REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC; FUPDATE_EQ;
              WORD_RULE `word_sub (word_add (b:A word) x) x = b`] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM]);;

let STACKPROPSAUX_cc_StackStore = prove
 (`!r n (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackStore r n) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "StackStore"] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `stack_get_var r (t1:(A,C,FFI)stack_state) = stack_get_var r (s:(A,C,FFI)stack_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
  STACKPROPSAUX_OPT_CASES_TAC `stack_get_var r (s:(A,C,FFI)stack_state)` `v:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                 `t1:(A,C,FFI)stack_state`;
                 `stack_state_stack_space (s:(A,C,FFI)stack_state) + n`]
                STACKPROPSAUX_sr_stack_load) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_mem_load_IN) THEN
  SUBGOAL_THEN `word_add (word_add (c:A word) (word_mul bytes_in_word
                  (word (stack_state_stack_space (s:(A,C,FFI)stack_state)))))
                  (word_offset n) =
                word_add c (word_mul bytes_in_word (word (stack_state_stack_space s + n)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[word_offset_eq; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `stack_state_memory_fupd
                (K ((word_add c (word_mul bytes_in_word
                       (word (stack_state_stack_space (s:(A,C,FFI)stack_state) + n))) =+ v)
                    (stack_state_memory t1))) (t1:(A,C,FFI)stack_state)` THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN SIMP STACKPROPSAUX_EVAL_SIMPS;
      MP_TAC(ISPECL [`k:num`; `r:num`; `n:num`; `t1:(A,C,FFI)stack_state`;
                     `word_add (c:A word) (word_mul bytes_in_word
                        (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))`;
                     `v:(A)word_loc`] STACKPROPSAUX_eval_stack_store) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC state_rel_stack_store THEN
    EXISTS_TAC `word_add (c:A word) (word_mul bytes_in_word
                  (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let STACKPROPSAUX_word_shift_facts = prove
 (`good_dimindex (:A)
   ==> backend_common_word_shift (:A) MOD dimword (:A) = backend_common_word_shift (:A) /\
       ~(backend_common_word_shift (:A) >= dimindex (:A))`,
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;
let STACKPROPSAUX_cc_StackGetSize = prove
 (`!r (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackGetSize r) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state) /\ good_dimindex (:A)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "StackGetSize"] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_word_shift_facts) THEN
   SUBGOAL_THEN `word_ushr (word_mul bytes_in_word
                   (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))
                   (backend_common_word_shift (:A)) =
                 (word (stack_state_stack_space s):A word)` ASSUME_TAC THENL
    [MATCH_MP_TAC stack_removeProof_bytes_in_word_word_shift THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `stack_state_stack_space (s:(A,C,FFI)stack_state) <=
                   LENGTH (stack_state_stack s)` ASSUME_TAC THENL
      [ASM_MESON_TAC[STACKPROPSAUX_sr_facts2]; ALL_TAC] THEN
     MATCH_MP_TAC LET_TRANS THEN
     EXISTS_TAC `val (bytes_in_word:A word) * LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
     CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
     REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN REWRITE_TAC[VAL_WORD] THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state)` THEN
     ASM_REWRITE_TAC[MOD_LE];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(r = k) /\ ~(r = k + 1)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `stack_set_var r (wl_Word (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))
                 (t1:(A,C,FFI)stack_state)` THEN
   ASM_SIMP_TAC[stack_removeProof_state_rel_set_var] THEN
   SIMP (STACKPROPSAUX_EVAL_SIMPS @ [WORD_RULE `word_sub (word_add c x) c:A word = x`]));;

let STACKPROPSAUX_cc_StackSetSize = prove
 (`!r (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackSetSize r) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state) /\ good_dimindex (:A)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "StackSetSize"] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_get_var r (t1:(A,C,FFI)stack_state) = stack_get_var r (s:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var r (s:(A,C,FFI)stack_state)` `x:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_word_shift_facts) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP lsl_word_shift) THEN
   SUBGOAL_THEN `~(r = k) /\ ~(r = k + 1)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `stack_set_var r (wl_Word (word_shl a (backend_common_word_shift (:A))))
                 (stack_state_regs_fupd (K (stack_state_regs t1 |+
                    (k,wl_Word (word_add c (word_mul bytes_in_word (word (val (a:A word))))))))
                 (t1:(A,C,FFI)stack_state))` THEN
   CONJ_TAC THENL
    [SIMP (STACKPROPSAUX_EVAL_SIMPS @ [WORD_VAL]) THEN
     REWRITE_TAC[stack_state_component_equality; STACKPROPSAUX_SR_ACC; WORD_MUL_SYM] THEN
     MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC stack_removeProof_state_rel_set_var THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC STACKPROPSAUX_state_rel_stack_space THEN ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC]);;

let STACKPROPSAUX_STAR_second = prove
 (`!(a:(A->bool)->bool) b c d e.
     a STAR b STAR c STAR d STAR e = b STAR (a STAR c STAR d STAR e)`,
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

(* the bitmaps of s sit at the address in the store slot BitmapBase *)

let STACKPROPSAUX_sr_bitmap_load = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t i.
     stack_removeProof_state_rel jump off k s t /\ i < LENGTH (stack_state_bitmaps s)
     ==> ?ww. FLOOKUP (stack_state_store s) BitmapBase = SOME (wl_Word ww) /\
              stack_mem_load (word_add (word_shl ww (backend_common_word_shift (:A)))
                                       (word_mul bytes_in_word (word i))) t =
                SOME (wl_Word (EL i (stack_state_bitmaps s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ww:A word. FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase =
                            SOME (wl_Word ww)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts2) THEN
    STRIP_TAC THEN UNDISCH_TAC `is_SOME_Word (FLOOKUP (stack_state_store
                                  (s:(A,C,FFI)stack_state)) BitmapBase)` THEN
    STACKPROPSAUX_OPT_CASES_TAC `FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase`
      `x:(A)word_loc` THEN REWRITE_TAC[is_SOME_Word_def] THEN
    STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN
    REWRITE_TAC[is_SOME_Word_def; option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ww:A word` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                             "STAR" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[the_SOME_Word_def; STACKPROPSAUX_STAR_second] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] STACKPROPSAUX_word_list_read)) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_MAP; EL_APPEND; EL_MAP;
               ARITH_RULE `i < a ==> i < a + b:num`] THEN
  SIMP_TAC[stack_mem_load_def]);;

let STACKPROPSAUX_mem_load_regs_fupd = prove
 (`!a f (t:(A,C,FFI)stack_state).
     stack_mem_load a (stack_state_regs_fupd f t) = stack_mem_load a t`,
  REWRITE_TAC[stack_mem_load_def; STACKPROPSAUX_SR_ACC]);;
let STACKPROPSAUX_cc_BitmapLoad = prove
 (`!r v (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (BitmapLoad r v) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state) /\ good_dimindex (:A)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "BitmapLoad"] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `r:num = v` THEN ASM_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `stack_get_var v (t1:(A,C,FFI)stack_state) = stack_get_var v (s:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var v (s:(A,C,FFI)stack_state)` `x:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`; `val (a:A word)`] STACKPROPSAUX_sr_bitmap_load) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ww:A word` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   SUBGOAL_THEN `stack_mem_load (word_add c (store_offset BitmapBase)) (t1:(A,C,FFI)stack_state) =
                 SOME (wl_Word ww)` ASSUME_TAC THENL
    [MATCH_MP_TAC mem_load_lemma THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
     ASM_SIMP_TAC[name_cases; distinctness "store_name"];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_word_shift_facts) THEN
   SUBGOAL_THEN `word_mul (word_add ww (a:A word)) bytes_in_word =
                 word_add (word_mul ww bytes_in_word) (word_mul bytes_in_word a)`
     ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL; MATCH_MP lsl_word_shift
                                 (ASSUME `good_dimindex (:A)`)]) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP lsl_word_shift) THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `stack_set_var r (wl_Word (EL (val (a:A word)) (stack_state_bitmaps (s:(A,C,FFI)stack_state))))
                 (t1:(A,C,FFI)stack_state)` THEN
   ASM_SIMP_TAC[stack_removeProof_state_rel_set_var] THEN
   REWRITE_TAC[stack_list_Seq_def] THEN
   SIMP (subtract STACKPROPSAUX_EVAL_SIMPS [stack_mem_load_def] @
         [STACKPROPSAUX_mem_load_regs_fupd]) THEN
   REWRITE_TAC[stack_state_component_equality; STACKPROPSAUX_SR_ACC; FUPDATE_EQ]);;

let STACKPROPSAUX_any_addr = prove
 (`!(w:A word) c ss.
     good_dimindex (:A) /\
     word_shl (word_ushr w (backend_common_word_shift (:A)))
              (backend_common_word_shift (:A)) = w
     ==> word_add w (word_add c (word_mul bytes_in_word (word ss))) =
         word_add c (word_mul bytes_in_word
           (word (ss + val (word_ushr w (backend_common_word_shift (:A)))))) /\
         word_add (word_add c (word_mul bytes_in_word (word ss))) w =
         word_add c (word_mul bytes_in_word
           (word (ss + val (word_ushr w (backend_common_word_shift (:A))))))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`word_ushr (w:A word) (backend_common_word_shift (:A))`,`q:A word`) THEN
  GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[lsl_word_shift] THEN REWRITE_TAC[WORD_ADD; WORD_VAL] THEN CONV_TAC WORD_RULE);;
let STACKPROPSAUX_cc_StackLoadAny = prove
 (`!r rn (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackLoadAny r rn) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state) /\ good_dimindex (:A)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "StackLoadAny"] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_get_var rn (t1:(A,C,FFI)stack_state) = stack_get_var rn (s:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var rn (s:(A,C,FFI)stack_state)` `x:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   COND_CASES_TAC THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`;
                  `stack_state_stack_space (s:(A,C,FFI)stack_state) +
                   val (word_ushr (a:A word) (backend_common_word_shift (:A)))`]
                 STACKPROPSAUX_sr_stack_load) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`a:A word`; `c:A word`; `stack_state_stack_space (s:(A,C,FFI)stack_state)`]
                 STACKPROPSAUX_any_addr) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   SUBGOAL_THEN `~(r:num = k)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `stack_set_var r (EL (stack_state_stack_space (s:(A,C,FFI)stack_state) +
                   val (word_ushr (a:A word) (backend_common_word_shift (:A))))
                   (stack_state_stack s)) (t1:(A,C,FFI)stack_state)` THEN
   ASM_SIMP_TAC[stack_removeProof_state_rel_set_var] THEN
   SIMP (subtract STACKPROPSAUX_EVAL_SIMPS [stack_mem_load_def] @
         [STACKPROPSAUX_mem_load_regs_fupd]) THEN
   REWRITE_TAC[stack_state_component_equality; STACKPROPSAUX_SR_ACC; FUPDATE_EQ]);;

let STACKPROPSAUX_cc_StackStoreAny = prove
 (`!r rn (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (StackStoreAny r rn) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state) /\ good_dimindex (:A)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "StackStoreAny"] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_get_var r (t1:(A,C,FFI)stack_state) = stack_get_var r (s:(A,C,FFI)stack_state) /\
                 stack_get_var rn (t1:(A,C,FFI)stack_state) = stack_get_var rn s`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var r (s:(A,C,FFI)stack_state)` `v:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var rn (s:(A,C,FFI)stack_state)` `x:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   CASES_ON `x:(A)word_loc` THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   COND_CASES_TAC THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`;
                  `stack_state_stack_space (s:(A,C,FFI)stack_state) +
                   val (word_ushr (a:A word) (backend_common_word_shift (:A)))`]
                 STACKPROPSAUX_sr_stack_load) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_mem_load_IN) THEN
   MP_TAC(ISPECL [`a:A word`; `c:A word`; `stack_state_stack_space (s:(A,C,FFI)stack_state)`]
                 STACKPROPSAUX_any_addr) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   SUBGOAL_THEN `~(r:num = k) /\ ~(rn:num = k)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `word_sub (word_add c (word_mul bytes_in_word
                   (word (stack_state_stack_space (s:(A,C,FFI)stack_state) +
                          val (word_ushr (a:A word) (backend_common_word_shift (:A))))))) a =
                 word_add c (word_mul bytes_in_word (word (stack_state_stack_space s)))`
     ASSUME_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
       try rand(lhs(concl th)) = `a:A word` with Failure _ -> false)) THEN
     CONV_TAC WORD_RULE;
     ALL_TAC] THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `stack_state_memory_fupd
                 (K ((word_add c (word_mul bytes_in_word
                        (word (stack_state_stack_space (s:(A,C,FFI)stack_state) +
                               val (word_ushr (a:A word) (backend_common_word_shift (:A)))))) =+ v)
                     (stack_state_memory t1))) (t1:(A,C,FFI)stack_state)` THEN
   CONJ_TAC THENL
    [SIMP STACKPROPSAUX_EVAL_SIMPS THEN
     ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM] THEN
     REWRITE_TAC[stack_state_component_equality; STACKPROPSAUX_SR_ACC] THEN
     ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM];
     REWRITE_TAC[ISPECL [`stack_state_stack_space (s:(A,C,FFI)stack_state)`;
                         `val (word_ushr (a:A word) (backend_common_word_shift (:A)))`] ADD_SYM] THEN
     MATCH_MP_TAC state_rel_stack_store THEN
     EXISTS_TAC `word_add (c:A word) (word_mul bytes_in_word
                   (word (stack_state_stack_space (s:(A,C,FFI)stack_state))))` THEN
     ASM_REWRITE_TAC[] THEN

     REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let STACKPROPSAUX_cc_LocValue = prove
 (`!r l1 l2 (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_LocValue r l1 l2) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_LocValue"] THEN
  COND_CASES_TAC THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `loc_check (stack_state_code (t1:(A,C,FFI)stack_state)) (l1,l2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[code_rel_loc_check; STACKPROPSAUX_sr_code_regs]; ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  ASM_SIMP_TAC[stack_removeProof_state_rel_set_var]);;

let STACKPROPSAUX_state_rel_code_buffer = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t cb.
     stack_removeProof_state_rel jump off k s t
     ==> stack_removeProof_state_rel jump off k (stack_state_code_buffer_fupd (K cb) s)
                                     (stack_state_code_buffer_fupd (K cb) t)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_cc_CodeBufferWrite = prove
 (`!r1 r2 (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_CodeBufferWrite r1 r2) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_CodeBufferWrite"; STACKPROPSAUX_get_var_clock;
              STACKPROPSAUX_SR_ACC] THEN
  SUBGOAL_THEN `stack_get_var r1 (t1:(A,C,FFI)stack_state) =
                stack_get_var r1 (s:(A,C,FFI)stack_state) /\
                stack_get_var r2 t1 = stack_get_var r2 s /\
                stack_state_code_buffer t1 = stack_state_code_buffer s`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[state_rel_get_var; stack_removeProof_state_rel_const]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock; UNWIND_THM1] THEN
  CASE_REWRITE_TAC[] THEN MATCH_MP_TAC STACKPROPSAUX_state_rel_code_buffer THEN
  ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_STAR_AC = prove
 (`(!p q:(A->bool)->bool. p STAR q = q STAR p) /\
   (!p q r:(A->bool)->bool. (p STAR q) STAR r = p STAR (q STAR r)) /\
   (!p q r:(A->bool)->bool. p STAR (q STAR r) = q STAR (p STAR r))`,
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

(* writing the next word of the data buffer into its free space *)

let STACKPROPSAUX_buffer_write_mem = prove
 (`!bp (L:(A word)list) n (p:(A word#(A)word_loc->bool)->bool) v m d.
     (misc_word_list bp (MAP wl_Word L) STAR
      word_list_exists (word_add bp (word_mul bytes_in_word (word (LENGTH L)))) (SUC n) STAR p)
       (fun2set (m,d))
     ==> word_add bp (word_mul bytes_in_word (word (LENGTH L))) IN d /\
         (misc_word_list bp (MAP wl_Word (APPEND L [v])) STAR
          word_list_exists (word_add bp (word_mul bytes_in_word (word (LENGTH (APPEND L [v]))))) n
          STAR p)
           (fun2set ((word_add bp (word_mul bytes_in_word (word (LENGTH L))) =+ wl_Word v) m,d))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_removeProof_word_list_exists_thm; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:(A)word_loc`) THEN
  REWRITE_TAC[MAP_APPEND; stack_removeProof_word_list_APPEND; LENGTH_MAP; LENGTH_APPEND;
              MAP; misc_word_list_def; SEP_CLAUSES; LENGTH] THEN
  ABBREV_TAC `a = word_add (bp:A word) (word_mul bytes_in_word (word (LENGTH (L:(A word)list))))` THEN
  SUBGOAL_THEN `word_add (bp:A word) (word_mul bytes_in_word (word (LENGTH (L:(A word)list) + SUC 0))) =
                word_add a (bytes_in_word:A word)` SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[GSYM ONE; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_eq (concl th)))) THEN
  SUBGOAL_THEN `!w:(A)word_loc.
    misc_word_list (bp:A word) (MAP wl_Word (L:(A word)list)) STAR
    (set_sep_one (a,w) STAR word_list_exists (word_add a bytes_in_word) n) STAR
    (p:(A word#(A)word_loc->bool)->bool) =
    set_sep_one (a,w) STAR (misc_word_list bp (MAP wl_Word L) STAR
      word_list_exists (word_add a bytes_in_word) n STAR p)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC); ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[read_fun2set]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ISPEC `wl_Word v:(A)word_loc` write_fun2set)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

let STACKPROPSAUX_sr_buffer_position = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t.
     stack_removeProof_state_rel jump off k s t
     ==> buffer_position (stack_state_data_buffer s) =
         word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                            (backend_common_word_shift (:A)))
                  (word_mul bytes_in_word (word (LENGTH (stack_state_bitmaps s))))`,
  REWRITE_TAC[stack_removeProof_state_rel_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_state_rel_buffer_write = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t w1 w2 db.
     stack_removeProof_state_rel jump off k s t /\
     buffer_write (stack_state_data_buffer s) w1 w2 = SOME db
     ==> w1 IN stack_state_mdomain t /\
         stack_removeProof_state_rel jump off k (stack_state_data_buffer_fupd (K db) s)
           (stack_state_memory_fupd (K ((w1 =+ wl_Word w2) (stack_state_memory t))) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_sr_buffer_position) THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   UNDISCH_TAC `buffer_write (stack_state_data_buffer (s:(A,C,FFI)stack_state)) w1 w2 = SOME db` THEN
   REWRITE_TAC[buffer_write_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   ABBREV_TAC `bp = word_shl (the_SOME_Word (FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase))
                             (backend_common_word_shift (:A))` THEN
   ABBREV_TAC `BM = stack_state_bitmaps (s:(A,C,FFI)stack_state)` THEN
   ABBREV_TAC `BF = buffer_buffer (stack_state_data_buffer (s:(A,C,FFI)stack_state))` THEN
   SUBGOAL_THEN `w1 = word_add bp (word_mul bytes_in_word (word (LENGTH (APPEND BM (BF:(A word)list))))):A word`
     SUBST_ALL_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
       try rhs(concl th) = `w1:A word` with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[LENGTH_APPEND; WORD_ADD; GSYM bytes_in_word_def] THEN CONV_TAC WORD_RULE;
     ALL_TAC] THEN
   FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o MATCH_MP (MESON[num_CASES; LT_REFL] `0 < x ==> ?n. x = SUC n`)) THEN
   MP_TAC(ISPECL [`bp:A word`; `APPEND BM BF:(A word)list`; `n:num`;
                  `memory (stack_state_memory s) (stack_state_mdomain s) STAR
                   word_store c (stack_state_store s) STAR
                   misc_word_list c (stack_state_stack (s:(A,C,FFI)stack_state))`;
                  `w2:A word`; `stack_state_memory (t:(A,C,FFI)stack_state)`;
                  `stack_state_mdomain (t:(A,C,FFI)stack_state)`] STACKPROPSAUX_buffer_write_mem) THEN
   ANTS_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                              "STAR" with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[MAP_APPEND; LENGTH_APPEND] THEN
     MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN REWRITE_TAC[ADD_SYM] THEN
     CONV_TAC(AC STACKPROPSAUX_STAR_AC);
     ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t` THEN
   REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC; buffer_INFO.ri_accfupds;
               K_THM; LET_DEF; LET_END_DEF] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th ->
     try fst(dest_const(fst(strip_comb(rator(concl th))))) = "STAR" &&
         can (find_term ((=) `wl_Word (w2:A word)`)) (concl th)
     with Failure _ -> false)) THEN
   REWRITE_TAC[APPEND_ASSOC; ARITH_RULE `SUC n - 1 = n`] THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

let STACKPROPSAUX_cc_DataBufferWrite = prove
 (`!r1 r2 (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (stack_DataBufferWrite r1 r2) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
    [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_DataBufferWrite"] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_get_var r1 (t1:(A,C,FFI)stack_state) =
                 stack_get_var r1 (s:(A,C,FFI)stack_state) /\
                 stack_get_var r2 t1 = stack_get_var r2 s`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   EVERY_CASE_TAC THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   FIRST_X_ASSUM(fun th ->
     if can (find_term (fun t -> is_const t && fst(dest_const t) = "buffer_write")) (concl th)
     then MP_TAC(MATCH_MP STACKPROPSAUX_state_rel_buffer_write
            (CONJ (ASSUME `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t1`) th))
     else failwith "no") THEN
   STRIP_TAC THEN EXISTS_TAC `0` THEN
   REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   FIRST_ASSUM(fun th -> let c = concl th in
     if (try fst(dest_const(fst(strip_comb c))) = "stack_removeProof_state_rel"
         with Failure _ -> false) && not (rand c = `t1:(A,C,FFI)stack_state`)
     then EXISTS_TAC (rand c) else failwith "no") THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STACKPROPSAUX_ev_inst THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   SIMP STACKPROPSAUX_EVAL_SIMPS);;

let STACKPROPSAUX_state_rel_ffi_return = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t new_ffi new_bytes w4 n bytes2.
     stack_removeProof_state_rel jump off k s t /\
     read_bytearray w4 n (mem_load_byte_aux (stack_state_memory s) (stack_state_mdomain s)
                            (stack_state_be s)) = SOME bytes2 /\
     LENGTH new_bytes = n
     ==> stack_removeProof_state_rel jump off k
           (stack_state_memory_fupd
              (K (write_bytearray w4 new_bytes (stack_state_memory s) (stack_state_mdomain s)
                                  (stack_state_be s)))
              (stack_state_regs_fupd (K (DRESTRICT (stack_state_regs s) (stack_state_ffi_save_regs s)))
                 (stack_state_fp_regs_fupd (K FEMPTY) (stack_state_ffi_fupd (K new_ffi) s))))
           (stack_state_memory_fupd
              (K (write_bytearray w4 new_bytes (stack_state_memory t) (stack_state_mdomain t)
                                  (stack_state_be t)))
              (stack_state_regs_fupd (K (DRESTRICT (stack_state_regs t) (stack_state_ffi_save_regs t)))
                 (stack_state_fp_regs_fupd (K FEMPTY) (stack_state_ffi_fupd (K new_ffi) t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   SUBGOAL_THEN `k IN stack_state_ffi_save_regs (s:(A,C,FFI)stack_state) /\
                 k + 1 IN stack_state_ffi_save_regs s /\ k + 2 IN stack_state_ffi_save_regs s`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts2) THEN
     REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
     ALL_TAC] THEN
   UNDISCH_TAC `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t` THEN
   REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC; LET_DEF; LET_END_DEF;
               FLOOKUP_DRESTRICT] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[GSYM STAR_ASSOC] THEN MATCH_MP_TAC write_bytearray_lemma THEN
   EXISTS_TAC `bytes2:(byte)list` THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                             "STAR" with Failure _ -> false)) THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN REWRITE_TAC[MAP_APPEND; LENGTH_APPEND] THEN
   REWRITE_TAC[ADD_SYM] THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

(* case split on a word_loc value, naming the word *)

let STACKPROPSAUX_WL_CASES_TAC (x:term) (w:term) : tactic =
  DISJ_CASES_THEN2 (X_CHOOSE_THEN w SUBST_ALL_TAC) (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC x (cases "word_loc"));;
let STACKPROPSAUX_cc_FFI = prove
 (`!ffi_index ptr len ptr2 len2 ret (s:(A,C,FFI)stack_state).
     STACKPROPSAUX_cc (stack_FFI ffi_index ptr len ptr2 len2 ret) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_FFI"; STACKPROPSAUX_get_var_clock;
               STACKPROPSAUX_SR_ACC] THEN
   SUBGOAL_THEN `stack_get_var len (t1:(A,C,FFI)stack_state) = stack_get_var len (s:(A,C,FFI)stack_state) /\
                 stack_get_var ptr t1 = stack_get_var ptr s /\
                 stack_get_var len2 t1 = stack_get_var len2 s /\
                 stack_get_var ptr2 t1 = stack_get_var ptr2 s /\
                 stack_state_ffi t1 = stack_state_ffi s /\
                 stack_state_be t1 = stack_state_be s`
     (fun th -> REWRITE_TAC[th]) THENL
    [ASM_MESON_TAC[state_rel_get_var; STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var len (s:(A,C,FFI)stack_state)` `x1:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x1:(A)word_loc` `w:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var ptr (s:(A,C,FFI)stack_state)` `x2:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x2:(A)word_loc` `w2:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var len2 (s:(A,C,FFI)stack_state)` `x3:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x3:(A)word_loc` `w3:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var ptr2 (s:(A,C,FFI)stack_state)` `x4:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x4:(A)word_loc` `w4:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC
     `read_bytearray w2 (val (w:A word)) (mem_load_byte_aux (stack_state_memory s)
        (stack_state_mdomain (s:(A,C,FFI)stack_state)) (stack_state_be s))` `bytes:(byte)list` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC
     `read_bytearray w4 (val (w3:A word)) (mem_load_byte_aux (stack_state_memory s)
        (stack_state_mdomain (s:(A,C,FFI)stack_state)) (stack_state_be s))` `bytes2:(byte)list` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `read_bytearray w2 (val (w:A word)) (mem_load_byte_aux (stack_state_memory t1)
        (stack_state_mdomain (t1:(A,C,FFI)stack_state)) (stack_state_be (s:(A,C,FFI)stack_state))) =
        SOME bytes /\
      read_bytearray w4 (val (w3:A word)) (mem_load_byte_aux (stack_state_memory t1)
        (stack_state_mdomain t1) (stack_state_be s)) = SOME bytes2`
     (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
    [SUBGOAL_THEN `stack_state_be (t1:(A,C,FFI)stack_state) = stack_state_be (s:(A,C,FFI)stack_state)`
       (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
     CONJ_TAC THEN MATCH_MP_TAC read_bytearray_IMP_read_bytearray THEN
     MAP_EVERY EXISTS_TAC [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   CASE_REWRITE_TAC[] THEN
   MP_TAC(ISPEC `call_FFI (stack_state_ffi (s:(A,C,FFI)stack_state)) (ExtCall ffi_index) bytes bytes2`
                (cases "ffi_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   STACKPROPSAUX_CC_LEAF_TAC THENL
    [MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                    `t1:(A,C,FFI)stack_state`; `a0:(FFI)ffi_state`; `a1:(byte)list`;
                    `w4:A word`; `val (w3:A word)`; `bytes2:(byte)list`]
                   STACKPROPSAUX_state_rel_ffi_return) THEN
     SUBGOAL_THEN `stack_state_be (t1:(A,C,FFI)stack_state) = stack_state_be (s:(A,C,FFI)stack_state)`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_removeProof_call_FFI_LENGTH) THEN
     FIRST_ASSUM(fun th -> if can (find_term ((=) `bytes2:(byte)list`)) (concl th) &&
                             can (find_term (fun t -> is_const t && fst(dest_const t) = "read_bytearray")) (concl th)
                           then ASSUME_TAC (MATCH_MP read_bytearray_LENGTH th) else failwith "no") THEN
     ASM_REWRITE_TAC[];
     ASM_MESON_TAC[STACKPROPSAUX_sr_facts]]);;

let STACKPROPSAUX_state_rel_ffi = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t f.
     stack_removeProof_state_rel jump off k s t
     ==> stack_removeProof_state_rel jump off k (stack_state_ffi_fupd (K f) s)
                                     (stack_state_ffi_fupd (K f) t)`,
  REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_state_rel_ffi_set = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t f r v.
     stack_removeProof_state_rel jump off k s t /\ r < k
     ==> stack_removeProof_state_rel jump off k
           (stack_state_regs_fupd (K (stack_state_regs s |+ (r,v)))
              (stack_state_ffi_fupd (K f) s))
           (stack_state_regs_fupd (K (stack_state_regs t |+ (r,v)))
              (stack_state_ffi_fupd (K f) t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`;
                 `stack_state_ffi_fupd (K f) (s:(A,C,FFI)stack_state)`;
                 `stack_state_ffi_fupd (K f) (t:(A,C,FFI)stack_state)`; `r:num`; `v:(A)word_loc`]
                stack_removeProof_state_rel_set_var) THEN
  ASM_SIMP_TAC[STACKPROPSAUX_state_rel_ffi; stack_set_var_def; STACKPROPSAUX_SR_ACC]);;

(* the shared memory operations run alike in related states *)

let STACKPROPSAUX_sh_mem_op_rel = prove
 (CASE_TERM `!jump off k op r (a:A word) (s:(A,C,FFI)stack_state) t res s'.
     stack_removeProof_state_rel jump off k s t /\ r < k /\
     sh_mem_op op r a s = (res,s') /\ ~(res = SOME stack_Error)
     ==> ?t'. sh_mem_op op r a t = (res,t') /\
              (match res with
                 SOME (stackSem_Halt _) -> stack_state_ffi t' = stack_state_ffi s'
               | SOME stack_TimeOut -> stack_state_ffi t' = stack_state_ffi s'
               | SOME (stack_FinalFFI _) -> stack_state_ffi t' = stack_state_ffi s'
               | _ -> stack_removeProof_state_rel jump off k s' t')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stack_get_var r (t:(A,C,FFI)stack_state) = stack_get_var r (s:(A,C,FFI)stack_state) /\
                stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
                stack_state_ffi t = stack_state_ffi s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[state_rel_get_var; STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  UNDISCH_TAC `sh_mem_op op r (a:A word) (s:(A,C,FFI)stack_state) = res,s'` THEN
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_load_def; stack_sh_mem_store_def;
              stack_sh_mem_load_byte_def; stack_sh_mem_store_byte_def;
              stack_sh_mem_load16_def; stack_sh_mem_store16_def;
              stack_sh_mem_load32_def; stack_sh_mem_store32_def] THEN
  ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq (concl th) && is_var (rhs (concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[UNWIND_THM1] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_SR_ACC; STACKPROPSAUX_state_rel_ffi_set;
               STACKPROPSAUX_state_rel_ffi]);;

let STACKPROPSAUX_cc_ShMemOp = prove
 (`!op rg a w (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc (ShMemOp op rg (Addr a w)) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "ShMemOp"] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_word_exp (s:(A,C,FFI)stack_state)
      (wl_Op asm_Add [wl_Var a; wl_Const w])` `a':A word` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `stack_word_exp (t1:(A,C,FFI)stack_state) (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME a'`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                    `t1:(A,C,FFI)stack_state`; `wl_Op asm_Add [wl_Var a; wl_Const (w:A word)]`;
                    `a':A word`] state_rel_word_exp) THEN
     ASM_REWRITE_TAC[reg_bound_exp_def; ALL; MAP];
     ALL_TAC] THEN
   SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) = stack_state_clock (t1:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
     REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
     ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
     DISCH_TAC THEN
     MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `op:memop`; `rg:num`; `a':A word`;
                    `stack_dec_clock (s:(A,C,FFI)stack_state)`;
                    `stack_dec_clock (t1:(A,C,FFI)stack_state)`;
                    `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`]
                   STACKPROPSAUX_sh_mem_op_rel) THEN
     ASM_SIMP_TAC[state_rel_IMP] THEN
     DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
     MAP_EVERY EXISTS_TAC [`0`; `t2:(A,C,FFI)stack_state`] THEN
     REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

(* an induction hypothesis for a call: the callee runs from dec_clock *)

let STACKPROPSAUX_cc_dec_clock = prove
 (CASE_TERM `!p (s:(A,C,FFI)stack_state) t1 r s2 jump off k.
     STACKPROPSAUX_cc p (stack_dec_clock s) /\
     stack_evaluate (p,stack_dec_clock s) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_removeProof_state_rel jump off k s t1 /\ reg_bound p k /\
     ~(stack_state_clock s = 0)
     ==> ?ck t2.
           stack_evaluate (stack_remove_comp jump off k p,
             stack_dec_clock (stack_state_clock_fupd (K (ck + stack_state_clock t1)) t1)) =
             (r,t2) /\
           (match r with
              SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
            | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
            | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
            | _ -> stack_removeProof_state_rel jump off k s2 t2)`,
  REWRITE_TAC[STACKPROPSAUX_cc_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `stack_dec_clock (t1:(A,C,FFI)stack_state)`; `k:num`; `off:A word#A word`; `jump:bool`]) THEN
  ASM_SIMP_TAC[state_rel_IMP] THEN
  SUBGOAL_THEN `stack_state_clock (t1:(A,C,FFI)stack_state) = stack_state_clock (s:(A,C,FFI)stack_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ck:num` THEN
  REWRITE_TAC[stack_dec_clock_def] THEN REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(ck + stack_state_clock (s:(A,C,FFI)stack_state)) - 1 =
                ck + (stack_state_clock s - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let STACKPROPSAUX_cc_JumpLower = prove
 (`!r1 r2 dest (s:(A,C,FFI)stack_state).
  (!x y prog. stack_get_var r1 s = SOME (wl_Word x) /\ stack_get_var r2 s = SOME (wl_Word y) /\
              asm_word_cmp Lower x y /\
              stack_find_code (INL dest) (stack_state_regs s) (stack_state_code s) = SOME prog /\
              ~(stack_state_clock s = 0)
              ==> STACKPROPSAUX_cc prog (stack_dec_clock s))
  ==> STACKPROPSAUX_cc (JumpLower r1 r2 dest) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
   STACKPROPSAUX_CC_SETUP_TAC THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "JumpLower"; STACKPROPSAUX_get_var_clock;
               STACKPROPSAUX_SR_ACC] THEN
   SUBGOAL_THEN `stack_get_var r1 (t1:(A,C,FFI)stack_state) = stack_get_var r1 (s:(A,C,FFI)stack_state) /\
                 stack_get_var r2 t1 = stack_get_var r2 s`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var r1 (s:(A,C,FFI)stack_state)` `x1:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x1:(A)word_loc` `x:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var r2 (s:(A,C,FFI)stack_state)` `x2:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x2:(A)word_loc` `y:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   COND_CASES_TAC THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_find_code (INL dest) (stack_state_regs (s:(A,C,FFI)stack_state))
                                  (stack_state_code s)` `prog:(A)stack_prog` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`; `INL dest:num+num`; `prog:(A)stack_prog`]
                 stack_removeProof_find_code_lemma) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) = stack_state_clock (t1:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; UNWIND_THM1] THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
     ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
     ALL_TAC] THEN
   MP_TAC(ISPEC `stack_evaluate (prog,stack_dec_clock (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
     (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MP_TAC(ISPECL [`prog:(A)stack_prog`; `s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`;
                  `res:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
                  `jump:bool`; `off:A word#A word`; `k:num`] STACKPROPSAUX_cc_dec_clock) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN
     MAP_EVERY EXISTS_TAC [`x:A word`; `y:A word`] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ck:num` THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t2:(A,C,FFI)stack_state` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* STACKPROPSAUX_dest_Seq_SOME: from stack_rawcallProof *)

let STACKPROPSAUX_comp_Seq = prove
 (`!jump off k (p1:(A)stack_prog) p2.
     stack_remove_comp jump off k (stack_Seq p1 p2) =
     stack_Seq (stack_remove_comp jump off k p1) (stack_remove_comp jump off k p2)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [stack_remove_comp_def] THEN
  CASE_REWRITE_TAC[]);;
let STACKPROPSAUX_cc_RawCall = prove
 (`!dest (s:(A,C,FFI)stack_state).
    (!prog x body. lookup dest (stack_state_code s) = SOME prog /\
                   stack_dest_Seq prog = SOME (x,body) /\ ~(stack_state_clock s = 0)
                   ==> STACKPROPSAUX_cc body (stack_dec_clock s))
    ==> STACKPROPSAUX_cc (RawCall dest) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
   STACKPROPSAUX_CC_SETUP_TAC THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "RawCall"; STACKPROPSAUX_SR_ACC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `lookup dest (stack_state_code (s:(A,C,FFI)stack_state))`
     `prog:(A)stack_prog` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `lookup dest (stack_state_code (t1:(A,C,FFI)stack_state)) =
                   SOME (stack_remove_comp jump off k prog) /\ reg_bound prog k`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP STACKPROPSAUX_sr_code_regs) THEN
     REWRITE_TAC[stack_removeProof_code_rel_def] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_dest_Seq (prog:(A)stack_prog)` `xb:(A)stack_prog#(A)stack_prog` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPEC `xb:(A)stack_prog#(A)stack_prog` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `x:(A)stack_prog` (X_CHOOSE_THEN `body:(A)stack_prog` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[STACKPROPSAUX_dest_Seq_SOME] o check (fun th ->
     try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_dest_Seq" with Failure _ -> false)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[reg_bound_def]) THEN
   REWRITE_TAC[STACKPROPSAUX_comp_Seq; stack_dest_Seq_def] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) = stack_state_clock (t1:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; UNWIND_THM1] THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
     ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
     ALL_TAC] THEN
   MP_TAC(ISPEC `stack_evaluate (body,stack_dec_clock (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
     (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MP_TAC(ISPECL [`body:(A)stack_prog`; `s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`;
                  `res:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
                  `jump:bool`; `off:A word#A word`; `k:num`] STACKPROPSAUX_cc_dec_clock) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN
     MAP_EVERY EXISTS_TAC [`stack_Seq x body:(A)stack_prog`; `x:(A)stack_prog`] THEN
     ASM_REWRITE_TAC[stack_dest_Seq_def];
     ALL_TAC] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ck:num` THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t2:(A,C,FFI)stack_state` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_code_rel_union = prove
 (`!jump off k (c1:((A)stack_prog)spt) c2 progs.
     stack_removeProof_code_rel jump off k c1 c2 /\
     (!i p. MEM (i,p) progs ==> reg_bound p k /\ stack_num_stubs <= i + 1)
     ==> stack_removeProof_code_rel jump off k (union c1 (fromAList progs))
           (union c2 (fromAList (MAP (stack_remove_prog_comp jump off k) progs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_removeProof_code_rel_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "old") (LABEL_TAC "dom"))
                              (LABEL_TAC "mem")) THEN
   CONJ_TAC THENL
    [MAP_EVERY X_GEN_TAC [`n:num`; `p:(A)stack_prog`] THEN
     REWRITE_TAC[lookup_union; lookup_fromAList] THEN
     STACKPROPSAUX_OPT_CASES_TAC `lookup n (c1:((A)stack_prog)spt)` `q:(A)stack_prog` THEN
     CASE_REWRITE_TAC[option_INJ] THENL
      [DISCH_TAC THEN
       FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
       USE_THEN "mem" (MP_TAC o SPECL [`n:num`; `p:(A)stack_prog`]) THEN
       (ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[stack_num_stubs_def]]) THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `~(n IN domain (c2:((A)stack_prog)spt))` MP_TAC THENL
        [USE_THEN "dom" SUBST1_TAC THEN
         ASM_REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; domain_lookup; option_DISTINCT] THEN
         ASM_ARITH_TAC;
         ALL_TAC] THEN
       REWRITE_TAC[domain_lookup; NOT_EXISTS_THM] THEN
       STACKPROPSAUX_OPT_CASES_TAC `lookup n (c2:((A)stack_prog)spt)` `v:(A)stack_prog` THENL
        [DISCH_TAC THEN CASE_REWRITE_TAC[] THEN
         REWRITE_TAC[stack_removeProof_prog_comp_eta; ALOOKUP_MAP_2] THEN
         ASM_REWRITE_TAC[OPTION_MAP_DEF];
         REWRITE_TAC[option_INJ] THEN DISCH_THEN(MP_TAC o SPEC `v:(A)stack_prog`) THEN
         REWRITE_TAC[]];
       DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
       USE_THEN "old" (MP_TAC o SPECL [`n:num`; `q:(A)stack_prog`]) THEN
       (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]];
     USE_THEN "dom" (fun th -> REWRITE_TAC[domain_union; domain_fromAList; MAP_MAP_o; th]) THEN
     SUBGOAL_THEN `(FST o stack_remove_prog_comp jump off k):num#(A)stack_prog->num = FST`
       SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; stack_removeProof_prog_comp_eta];
       ALL_TAC] THEN
     SET_TAC[]]);;

let STACKPROPSAUX_state_rel_install = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t cfg progs bm w3 w4 db cb ptr l.
     stack_removeProof_state_rel jump off k s t /\
     stack_state_compile_oracle s 0 = (cfg,progs,bm) /\
     buffer_flush (stack_state_data_buffer s) w3 w4 = SOME (bm,db) /\ ptr < k
     ==> stack_removeProof_state_rel jump off k
           (stack_state_bitmaps_fupd (K (APPEND (stack_state_bitmaps s) bm))
           (stack_state_code_buffer_fupd (K cb)
           (stack_state_data_buffer_fupd (K db)
           (stack_state_code_fupd (K (union (stack_state_code s) (fromAList progs)))
           (stack_state_regs_fupd
              (K (DRESTRICT (stack_state_regs s) (stack_state_ffi_save_regs s) |+
                  (ptr,wl_Loc l 0)))
           (stack_state_fp_regs_fupd (K FEMPTY)
           (stack_state_compile_oracle_fupd
              (K (\i. stack_state_compile_oracle s (i + 1))) s)))))))
           (stack_state_bitmaps_fupd (K (APPEND (stack_state_bitmaps t) bm))
           (stack_state_code_buffer_fupd (K cb)
           (stack_state_data_buffer_fupd (K (stack_state_data_buffer t))
           (stack_state_code_fupd
              (K (union (stack_state_code t)
                    (fromAList (MAP (stack_remove_prog_comp jump off k) progs))))
           (stack_state_regs_fupd
              (K (DRESTRICT (stack_state_regs t) (stack_state_ffi_save_regs t) |+
                  (ptr,wl_Loc l 0)))
           (stack_state_fp_regs_fupd (K FEMPTY)
           (stack_state_compile_oracle_fupd
              (K (\i. FST (stack_state_compile_oracle s (i + 1)),
                      MAP (stack_remove_prog_comp jump off k)
                          (FST (SND (stack_state_compile_oracle s (i + 1)))),
                      SND (SND (stack_state_compile_oracle s (i + 1))))) t)))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_sr_buffer_position) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   SUBGOAL_THEN `k IN stack_state_ffi_save_regs (s:(A,C,FFI)stack_state) /\
                 k + 1 IN stack_state_ffi_save_regs s /\ k + 2 IN stack_state_ffi_save_regs s`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts2) THEN
     REWRITE_TAC[INSERT_SUBSET] THEN MESON_TAC[];
     ALL_TAC] THEN
   UNDISCH_TAC `buffer_flush (stack_state_data_buffer (s:(A,C,FFI)stack_state)) w3 w4 = SOME (bm,db)` THEN
   REWRITE_TAC[buffer_flush_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  UNDISCH_TAC `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t` THEN
   REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC; buffer_INFO.ri_accfupds;
               K_THM; LET_DEF; LET_END_DEF; FLOOKUP_UPDATE; FLOOKUP_DRESTRICT] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~(ptr = k + 1) /\ ~(ptr = k) /\ ~(ptr = k + 2)` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; PAIR_MAP_DEF; I_THM];
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
     MATCH_MP_TAC STACKPROPSAUX_code_rel_union THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
       can (find_term ((=) `stack_num_stubs`)) (concl th))) THEN
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[lookup_union] THEN CASE_REWRITE_TAC[];
     FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
       try rhs(concl th) = `w4:A word` with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[LENGTH_APPEND; WORD_ADD; GSYM bytes_in_word_def] THEN CONV_TAC WORD_RULE;
     REWRITE_TAC[APPEND_NIL] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                              "STAR" with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN REWRITE_TAC[MAP_APPEND; LENGTH_APPEND] THEN
     REWRITE_TAC[ADD_SYM]]);;

let STACKPROPSAUX_cc_Install = prove
 (`!ptr len dptr dlen ret (s:(A,C,FFI)stack_state).
     STACKPROPSAUX_cc (stack_Install ptr len dptr dlen ret) s`,
  STACKPROPSAUX_CC_SETUP_TAC THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Install"; STACKPROPSAUX_get_var_clock;
               STACKPROPSAUX_SR_ACC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_removeProof_state_rel_const) THEN
   SUBGOAL_THEN `stack_get_var ptr (t1:(A,C,FFI)stack_state) = stack_get_var ptr (s:(A,C,FFI)stack_state) /\
                 stack_get_var len t1 = stack_get_var len s /\
                 stack_get_var dptr t1 = stack_get_var dptr s /\
                 stack_get_var dlen t1 = stack_get_var dlen s`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[state_rel_get_var]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var ptr (s:(A,C,FFI)stack_state)` `x1:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x1:(A)word_loc` `w1:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var len (s:(A,C,FFI)stack_state)` `x2:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x2:(A)word_loc` `w2:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var dptr (s:(A,C,FFI)stack_state)` `x3:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x3:(A)word_loc` `w3:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var dlen (s:(A,C,FFI)stack_state)` `x4:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x4:(A)word_loc` `w4:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   MP_TAC(ISPEC `stack_state_compile_oracle (s:(A,C,FFI)stack_state) 0` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `cfg:C` (X_CHOOSE_THEN `pb:(num#(A)stack_prog)list#(A word)list`
     ASSUME_TAC)) THEN
   MP_TAC(ISPEC `pb:(num#(A)stack_prog)list#(A word)list` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `progs:(num#(A)stack_prog)list` (X_CHOOSE_THEN `bm:(A word)list`
     SUBST_ALL_TAC)) THEN
   ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `buffer_flush (stack_state_code_buffer (s:(A,C,FFI)stack_state)) w1 w2`
     `bc:(byte)list#(A,8)buffer` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPEC `bc:(byte)list#(A,8)buffer` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `bytes:(byte)list` (X_CHOOSE_THEN `cb:(A,8)buffer` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `buffer_flush (stack_state_data_buffer (s:(A,C,FFI)stack_state)) w3 w4`
     `dd:(A word)list#(A,A)buffer` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPEC `dd:(A word)list#(A,A)buffer` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `data:(A word)list` (X_CHOOSE_THEN `db:(A,A)buffer` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_state_compile (t1:(A,C,FFI)stack_state) cfg
       (MAP (stack_remove_prog_comp jump off k) (progs:(num#(A)stack_prog)list))`
     `bf:(byte)list#C` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPEC `bf:(byte)list#C` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `bytes':(byte)list` (X_CHOOSE_THEN `cfg':C` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `h:num#(A)stack_prog`
     (X_CHOOSE_THEN `t:(num#(A)stack_prog)list` SUBST_ALL_TAC))
     (ISPEC `progs:(num#(A)stack_prog)list` list_CASES) THEN
   REWRITE_TAC[MAP] THEN CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPEC `h:num#(A)stack_prog` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `prog:(A)stack_prog` SUBST_ALL_TAC)) THEN
   REWRITE_TAC[stack_remove_prog_comp_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[shift_seq_def; PAIR_MAP_DEF; I_THM] THEN
   COND_CASES_TAC THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; stack_removeProof_with_same_clock] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN CASE_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try rhs(concl th) = `bm:(A word)list` with Failure _ -> false)) THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`; `cfg:C`; `CONS (n0,prog) t:(num#(A)stack_prog)list`;
                  `bm:(A word)list`; `w3:A word`; `w4:A word`; `db:(A,A)buffer`; `cb:(A,8)buffer`;
                  `ptr:num`; `n0:num`] STACKPROPSAUX_state_rel_install) THEN
   ASM_REWRITE_TAC[MAP; stack_remove_prog_comp_def]);;

let STACKPROPSAUX_cc_Call_NONE = prove
 (`!dest handler (s:(A,C,FFI)stack_state).
     (!prog. stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME prog /\
             handler = NONE /\ ~(stack_state_clock s = 0)
             ==> STACKPROPSAUX_cc prog (stack_dec_clock s))
     ==> STACKPROPSAUX_cc (stack_Call NONE dest handler) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
   STACKPROPSAUX_CC_SETUP_TAC THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Call"; STACKPROPSAUX_SR_ACC] THEN
   CASE_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state))
                                  (stack_state_code s)` `prog:(A)stack_prog` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`; `dest:num+num`; `prog:(A)stack_prog`]
                 stack_removeProof_find_code_lemma) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `handler:((A)stack_prog#num#num)option`
     `hh:(A)stack_prog#num#num` THEN
   REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) = stack_state_clock (t1:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; UNWIND_THM1] THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
     ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
     ALL_TAC] THEN
   MP_TAC(ISPEC `stack_evaluate (prog,stack_dec_clock (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
     (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MP_TAC(ISPECL [`prog:(A)stack_prog`; `s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`;
                  `res:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
                  `jump:bool`; `off:A word#A word`; `k:num`] STACKPROPSAUX_cc_dec_clock) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ck:num` THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t2:(A,C,FFI)stack_state` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_dec_set_clock = prove
 (`!r v ck (t:(A,C,FFI)stack_state).
     ~(stack_state_clock t = 0)
     ==> stack_dec_clock (stack_set_var r v
           (stack_state_clock_fupd (K (ck + stack_state_clock t)) t)) =
         stack_state_clock_fupd
           (K (ck + stack_state_clock (stack_dec_clock (stack_set_var r v t))))
           (stack_dec_clock (stack_set_var r v t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_dec_clock_def; stack_set_var_def] THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  SUBGOAL_THEN `(ck + stack_state_clock (t:(A,C,FFI)stack_state)) - 1 =
                ck + (stack_state_clock t - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let STACKPROPSAUX_state_rel_dec_set = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t r v.
     stack_removeProof_state_rel jump off k s t /\ r < k
     ==> stack_removeProof_state_rel jump off k (stack_dec_clock (stack_set_var r v s))
                                     (stack_dec_clock (stack_set_var r v t))`,
  MESON_TAC[state_rel_IMP; stack_removeProof_state_rel_set_var]);;

let STACKPROPSAUX_SR_CALL_ERR_TAC : tactic =
  USE_THEN "ev" MP_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_MESON_TAC[];;
let STACKPROPSAUX_SR_CALL_SIMPLE_TAC : tactic =
  USE_THEN "ev" MP_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`ck1:num`; `t3:(A,C,FFI)stack_state`] THEN
  USE_THEN "ev1" (fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "case1" MP_TAC THEN CASE_REWRITE_TAC[];;
let STACKPROPSAUX_CALL_SEQ_TAC (ih:string) (spec:term list) : tactic =
  DISCH_TAC THEN
  USE_THEN "case1" (ASSUME_TAC o CASE_REWRITE_RULE[]) THEN
  USE_THEN ih (MP_TAC o SPECL spec) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[STACKPROPSAUX_cc_def]]) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `t3:(A,C,FFI)stack_state`; `k:num`; `off:A word#A word`; `jump:bool`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t4:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `t4:(A,C,FFI)stack_state`] THEN
  USE_THEN "ev1" (fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_add_clock_cc2
    (CONJ th (prove(mk_neg(mk_eq(lhand(rhs(concl th)),
                                  `SOME (stack_TimeOut:(A)stack_result)`)),
                    REWRITE_TAC[option_INJ; distinctness "stack_result"])))]) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;
let STACKPROPSAUX_cc_Call_SOME = prove
 (`!rh lr l1 l2 dest handler (s:(A,C,FFI)stack_state).
  (!prog. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog /\
          ~(stack_state_clock s = 0)
          ==> STACKPROPSAUX_cc prog (stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s))) /\
  (!prog x s2. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog /\
               ~(stack_state_clock s = 0) /\
               stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
                 (SOME (stack_Result x),s2) /\ x = wl_Loc l1 l2
               ==> STACKPROPSAUX_cc rh s2) /\
  (!prog x l1' l2' h s2.
               stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog /\
               ~(stack_state_clock s = 0) /\
               stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
                 (SOME (stack_Exception x),s2) /\
               handler = SOME (h,l1',l2') /\ x = wl_Loc l1' l2'
               ==> STACKPROPSAUX_cc h s2)
  ==> STACKPROPSAUX_cc (stack_Call (SOME (rh,lr,l1,l2)) dest handler) s`,
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih3"))) THEN
   STACKPROPSAUX_CC_SETUP_TAC THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Call"; STACKPROPSAUX_SR_ACC] THEN
   CASE_REWRITE_TAC[] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state) \\ lr)
                                  (stack_state_code s)` `prog:(A)stack_prog` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `k:num`; `s:(A,C,FFI)stack_state`;
                  `t1:(A,C,FFI)stack_state`; `dest:num+num`; `prog:(A)stack_prog`; `lr:num`]
                 find_code_lemma2) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) = stack_state_clock (t1:(A,C,FFI)stack_state)`
     ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
    [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; UNWIND_THM1] THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC] THEN
     ASM_MESON_TAC[STACKPROPSAUX_sr_facts];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th ->
     is_conj (concl th) && can (find_term ((=) `reg_bound (rh:(A)stack_prog) k`)) (concl th)))) THEN
   MP_TAC(ISPEC `stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2)
                   (s:(A,C,FFI)stack_state)))` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `x:((A)stack_result)option`
     (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(LABEL_TAC "ev") THEN
   SUBGOAL_THEN `~(x = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(r = SOME (stack_Error:(A)stack_result))` THEN
     USE_THEN "ev" MP_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC] THEN
   USE_THEN "ih1" (MP_TAC o SPEC `prog:(A)stack_prog`) THEN
   (ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[STACKPROPSAUX_cc_def]]) THEN
   DISCH_THEN(MP_TAC o SPECL [`x:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
     `stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) (t1:(A,C,FFI)stack_state))`;
     `k:num`; `off:A word#A word`; `jump:bool`]) THEN
   (ANTS_TAC THENL [ASM_SIMP_TAC[STACKPROPSAUX_state_rel_dec_set]; ALL_TAC]) THEN
   DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
     (CONJUNCTS_THEN2 (LABEL_TAC "ev1") (LABEL_TAC "case1")))) THEN
   ASM_SIMP_TAC[STACKPROPSAUX_dec_set_clock; ADD_EQ_0] THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `xr:(A)stack_result` SUBST_ALL_TAC)
     (ISPEC `x:((A)stack_result)option` (cases "option")) THENL
    [STACKPROPSAUX_SR_CALL_ERR_TAC; ALL_TAC] THEN
   (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) (ISPEC `xr:(A)stack_result` (cases "stack_result")) THENL
    [USE_THEN "ev" MP_TAC THEN CASE_REWRITE_TAC[] THEN
     ASM_CASES_TAC `a = wl_Loc l1 l2:(A)word_loc` THEN ASM_REWRITE_TAC[] THENL
      [FIRST_X_ASSUM SUBST_ALL_TAC THEN
       STACKPROPSAUX_CALL_SEQ_TAC "ih2" [`prog:(A)stack_prog`; `wl_Loc l1 l2:(A)word_loc`;
                                         `s3:(A,C,FFI)stack_state`];
       REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]];
     USE_THEN "ev" MP_TAC THEN CASE_REWRITE_TAC[] THEN
     DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `hh:(A)stack_prog#num#num` SUBST_ALL_TAC)
       (ISPEC `handler:((A)stack_prog#num#num)option` (cases "option")) THEN
     CASE_REWRITE_TAC[] THENL
      [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
       MAP_EVERY EXISTS_TAC [`ck1:num`; `t3:(A,C,FFI)stack_state`] THEN
       USE_THEN "ev1" (fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
       USE_THEN "case1" MP_TAC THEN CASE_REWRITE_TAC[];
       MP_TAC(ISPEC `hh:(A)stack_prog#num#num` PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN `h:(A)stack_prog` (X_CHOOSE_THEN `ll:num#num` SUBST_ALL_TAC)) THEN
       MP_TAC(ISPEC `ll:num#num` PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN `l1q:num` (X_CHOOSE_THEN `l2q:num` SUBST_ALL_TAC)) THEN
       CASE_REWRITE_TAC[] THEN
       ASM_CASES_TAC `a = wl_Loc l1q l2q:(A)word_loc` THEN ASM_REWRITE_TAC[] THENL
        [FIRST_X_ASSUM SUBST_ALL_TAC THEN
         RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
         REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
           can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "reg_bound"
                                    with Failure _ -> false)) (concl th)))) THEN
         STACKPROPSAUX_CALL_SEQ_TAC "ih3" [`prog:(A)stack_prog`; `wl_Loc l1q l2q:(A)word_loc`;
            `l1q:num`; `l2q:num`; `h:(A)stack_prog`; `s3:(A,C,FFI)stack_state`];
         REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]]];
     STACKPROPSAUX_SR_CALL_ERR_TAC; STACKPROPSAUX_SR_CALL_ERR_TAC;
     STACKPROPSAUX_SR_CALL_SIMPLE_TAC; STACKPROPSAUX_SR_CALL_SIMPLE_TAC; STACKPROPSAUX_SR_CALL_SIMPLE_TAC;
     STACKPROPSAUX_SR_CALL_ERR_TAC]);;

let STACKPROPSAUX_cc_Call = prove
 (`!ret dest handler (s:(A,C,FFI)stack_state).
    (!ret_handler prog link_reg l1 l2.
         ret = SOME (ret_handler,link_reg,l1,l2) /\
         stack_find_code dest (stack_state_regs s \\ link_reg) (stack_state_code s) = SOME prog /\
         ~(stack_state_clock s = 0)
         ==> STACKPROPSAUX_cc prog
               (stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s))) /\
    (!prog link_reg x l1 l2 ret_handler s2.
         ret = SOME (ret_handler,link_reg,l1,l2) /\
         stack_find_code dest (stack_state_regs s \\ link_reg) (stack_state_code s) = SOME prog /\
         ~(stack_state_clock s = 0) /\
         stack_evaluate (prog,stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s)) =
           (SOME (stack_Result x),s2) /\
         x = wl_Loc l1 l2
         ==> STACKPROPSAUX_cc ret_handler s2) /\
    (!ret_handler prog link_reg l1 l2 x l1' l2' h s2.
         ret = SOME (ret_handler,link_reg,l1,l2) /\
         stack_find_code dest (stack_state_regs s \\ link_reg) (stack_state_code s) = SOME prog /\
         ~(stack_state_clock s = 0) /\
         stack_evaluate (prog,stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s)) =
           (SOME (stack_Exception x),s2) /\
         handler = SOME (h,l1',l2') /\ x = wl_Loc l1' l2'
         ==> STACKPROPSAUX_cc h s2) /\
    (!prog. ret = NONE /\
            stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME prog /\
            handler = NONE /\ ~(stack_state_clock s = 0)
            ==> STACKPROPSAUX_cc prog (stack_dec_clock s))
    ==> STACKPROPSAUX_cc (stack_Call ret dest handler) s`,
  REPEAT GEN_TAC THEN
   DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `rr:(A)stack_prog#num#num#num` SUBST1_TAC)
     (ISPEC `ret:((A)stack_prog#num#num#num)option` (cases "option")) THEN
   REWRITE_TAC[option_DISTINCT; option_INJ] THENL
    [STRIP_TAC THEN MATCH_MP_TAC STACKPROPSAUX_cc_Call_NONE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPEC `rr:(A)stack_prog#num#num#num` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `rh:(A)stack_prog` (X_CHOOSE_THEN `r3:num#num#num` SUBST1_TAC)) THEN
   MP_TAC(ISPEC `r3:num#num#num` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `lr:num` (X_CHOOSE_THEN `r2:num#num` SUBST1_TAC)) THEN
   MP_TAC(ISPEC `r2:num#num` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST1_TAC)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i1") (CONJUNCTS_THEN2 (LABEL_TAC "i2")
     (LABEL_TAC "i3"))) THEN
   MATCH_MP_TAC STACKPROPSAUX_cc_Call_SOME THEN REPEAT CONJ_TAC THENL
    [X_GEN_TAC `prog:(A)stack_prog` THEN STRIP_TAC THEN
     USE_THEN "i1" (MATCH_MP_TAC o SPECL [`rh:(A)stack_prog`; `prog:(A)stack_prog`;
       `lr:num`; `l1:num`; `l2:num`]) THEN ASM_REWRITE_TAC[];
     MAP_EVERY X_GEN_TAC [`prog:(A)stack_prog`; `x:(A)word_loc`; `s2:(A,C,FFI)stack_state`] THEN
     STRIP_TAC THEN
     USE_THEN "i2" (MATCH_MP_TAC o SPECL [`prog:(A)stack_prog`; `lr:num`; `x:(A)word_loc`;
       `l1:num`; `l2:num`; `rh:(A)stack_prog`; `s2:(A,C,FFI)stack_state`]) THEN
     ASM_REWRITE_TAC[];
     MAP_EVERY X_GEN_TAC [`prog:(A)stack_prog`; `x:(A)word_loc`; `l1':num`; `l2':num`;
                          `h:(A)stack_prog`; `s2:(A,C,FFI)stack_state`] THEN
     STRIP_TAC THEN
     USE_THEN "i3" (MATCH_MP_TAC o SPECL [`rh:(A)stack_prog`; `prog:(A)stack_prog`; `lr:num`;
       `l1:num`; `l2:num`; `x:(A)word_loc`; `l1':num`; `l2':num`; `h:(A)stack_prog`;
       `s2:(A,C,FFI)stack_state`]) THEN
     ASM_REWRITE_TAC[]]);;

let STACKPROPSAUX_state_rel_regs_mem = prove
 (`!jump off k (s:(A,C,FFI)stack_state) t R1 R2 m1 m2 c.
     stack_removeProof_state_rel jump off k s t /\
     FLOOKUP (stack_state_regs t) (k + 1) = SOME (wl_Word c) /\
     (!n. n < k ==> FLOOKUP R2 n = FLOOKUP R1 n) /\
     FLOOKUP R2 k = FLOOKUP (stack_state_regs t) k /\
     FLOOKUP R2 (k + 1) = FLOOKUP (stack_state_regs t) (k + 1) /\
     FLOOKUP R2 (k + 2) = FLOOKUP (stack_state_regs t) (k + 2) /\
     (memory m1 (stack_state_mdomain s) STAR
      misc_word_list
        (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                  (backend_common_word_shift (:A)))
        (MAP wl_Word (APPEND (stack_state_bitmaps s) (buffer_buffer (stack_state_data_buffer s)))) STAR
      word_list_exists
        (word_add (word_shl (the_SOME_Word (FLOOKUP (stack_state_store s) BitmapBase))
                            (backend_common_word_shift (:A)))
           (word_mul bytes_in_word
              (word (LENGTH (APPEND (stack_state_bitmaps s)
                                    (buffer_buffer (stack_state_data_buffer s)))))))
        (buffer_space_left (stack_state_data_buffer s)) STAR
      word_store c (stack_state_store s) STAR
      misc_word_list c (stack_state_stack s))
       (fun2set (m2,stack_state_mdomain t))
     ==> stack_removeProof_state_rel jump off k
           (stack_state_regs_fupd (K R1) (stack_state_memory_fupd (K m1) s))
           (stack_state_regs_fupd (K R2) (stack_state_memory_fupd (K m2) t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c':A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
   SUBGOAL_THEN `c':A word = c` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) (k + 1) =
                  SOME (wl_Word c')` THEN
     ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
     ALL_TAC] THEN
   UNDISCH_TAC `stack_removeProof_state_rel jump off k (s:(A,C,FFI)stack_state) t` THEN
   REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC; LET_DEF; LET_END_DEF] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_sc_prefix = prove
 (`!tb k c ww (i:A word) rest (t:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs t) (k + 1) = SOME (wl_Word c) /\
     stack_mem_load (word_add c (store_offset BitmapBase)) t = SOME (wl_Word ww) /\
     FLOOKUP (stack_state_regs t) 1 = SOME (wl_Word i) /\ ~(tb = 1) /\ good_dimindex (:A)
     ==> stack_evaluate
           (stack_Seq (stack_Inst (Mem asm_Load tb (Addr (k + 1) (store_offset BitmapBase))))
           (stack_Seq (stack_Inst (asm_Arith (Binop asm_Add tb tb (Reg 1))))
           (stack_Seq (stack_Inst (asm_Arith (asm_Shift Lsl tb tb
                         (Imm (word (backend_common_word_shift (:A))))))) rest)),t) =
         stack_evaluate (rest,stack_set_var tb
                                (wl_Word (word_mul (word_add ww i) bytes_in_word)) t)`,
  REPEAT STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_word_shift_facts) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP lsl_word_shift) THEN
   SUBGOAL_THEN `~(1 = tb)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   SIMP (subtract STACKPROPSAUX_EVAL_SIMPS [stack_mem_load_def; FLOOKUP_UPDATE] @
         [STACKPROPSAUX_mem_load_regs_fupd; FLOOKUP_UPDATE]));;

let STACKPROPSAUX_sc_suffix = prove
 (`!ta tb (t:(A,C,FFI)stack_state) w.
     FLOOKUP (stack_state_regs t) 1 = SOME w /\ ~(ta = 1)
     ==> stack_evaluate
           (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or ta 1 (Reg 1))))
                      (stack_Inst (asm_Arith (Binop asm_Or tb 1 (Reg 1)))),t) =
         (NONE,stack_set_var tb w (stack_set_var ta w t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ta = 1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP STACKPROPSAUX_EVAL_SIMPS THEN
  REWRITE_TAC[stack_set_var_def] THEN REWRITE_TAC STACKPROPSAUX_SR_NORM);;

let STACKPROPSAUX_mem_load_clock = prove
 (`!a f (t:(A,C,FFI)stack_state).
     stack_mem_load a (stack_state_clock_fupd f t) = stack_mem_load a t`,
  REWRITE_TAC[stack_mem_load_def; STACKPROPSAUX_SR_ACC]);;
let STACKPROPSAUX_SC_REGS_TAC : tactic =
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
  MAP_EVERY (fun tm -> ASM_CASES_TAC tm THENL
     [POP_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC])
     [`tb:num = n`; `ta:num = n`; `1 = n`; `2 = n`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[STACKPROPSAUX_sr_code_regs];;
let STACKPROPSAUX_SC_MEM_TAC : tactic =
  USE_THEN "mem2" MP_TAC THEN
  EXPAND_TAC "rst" THEN EXPAND_TAC "T3" THEN EXPAND_TAC "bp" THEN
  FIRST_ASSUM(fun th -> if (try lhs(concl th) =
      `FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase` with Failure _ -> false)
    then REWRITE_TAC[th] else failwith "no") THEN
  REWRITE_TAC[the_SOME_Word_def; stack_set_var_def; STACKPROPSAUX_SR_ACC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  REWRITE_TAC[MAP_APPEND; stack_removeProof_word_list_APPEND; LENGTH_APPEND; LENGTH_MAP] THEN
  REWRITE_TAC[ADD_SYM] THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);;

let STACKPROPSAUX_cc_StoreConsts = prove
 (`!t1 t2 stub_opt (s:(A,C,FFI)stack_state).
     STACKPROPSAUX_cc (stack_StoreConsts t1 t2 stub_opt) s`,
  REWRITE_TAC[STACKPROPSAUX_cc_def] THEN
   MAP_EVERY X_GEN_TAC [`ta:num`; `tb:num`; `stub_opt:(num)option`; `s:(A,C,FFI)stack_state`;
     `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`; `t1:(A,C,FFI)stack_state`;
     `k:num`; `off:A word#A word`; `jump:bool`] THEN
   ONCE_REWRITE_TAC[stack_remove_comp_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[reg_bound_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `stack_state_use_store (s:(A,C,FFI)stack_state) /\ ~stack_state_use_alloc s /\
                 good_dimindex (:A)` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
   REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_StoreConsts"] THEN ASM_REWRITE_TAC[] THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nn:num` SUBST_ALL_TAC)
     (ISPEC `stub_opt:(num)option` (cases "option")) THEN
   REWRITE_TAC[IS_SOME_DEF; check_store_consts_opt_def] THENL
    [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   REWRITE_TAC[store_const_sem_def] THEN
   COND_CASES_TAC THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM] o
     REWRITE_RULE[]) THEN
  SUBGOAL_THEN `stack_get_var 1 (t1:(A,C,FFI)stack_state) = stack_get_var 1 (s:(A,C,FFI)stack_state) /\
                 stack_get_var 2 t1 = stack_get_var 2 s /\ stack_get_var 3 t1 = stack_get_var 3 s`
     STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC state_rel_get_var THEN
     MAP_EVERY EXISTS_TAC [`jump:bool`; `off:A word#A word`; `k:num`] THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var 1 (s:(A,C,FFI)stack_state)` `x1:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x1:(A)word_loc` `i:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var 2 (s:(A,C,FFI)stack_state)` `x2:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x2:(A)word_loc` `aw:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `stack_get_var 3 (s:(A,C,FFI)stack_state)` `x3:(A)word_loc` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   STACKPROPSAUX_WL_CASES_TAC `x3:(A)word_loc` `ofs:A word` THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; STACKPROPSAUX_CC_LEAF_TAC] THEN
   STACKPROPSAUX_OPT_CASES_TAC `copy_words (val (i:A word)) aw ofs
      (stack_state_bitmaps (s:(A,C,FFI)stack_state)) (stack_state_mdomain s) (stack_state_memory s)`
     `cw:A word#(A word->(A)word_loc)` THEN
   CASE_REWRITE_TAC[] THENL [STACKPROPSAUX_CC_LEAF_TAC; ALL_TAC] THEN
   MP_TAC(ISPEC `cw:A word#(A word->(A)word_loc)` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `m1:A word->(A)word_loc` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[I_THM] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(X_CHOOSE_THEN `c:A word` STRIP_ASSUME_TAC o MATCH_MP state_rel_get_var_k) THEN
   SUBGOAL_THEN `?ww:A word. FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase =
                             SOME (wl_Word ww)` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_sr_facts2) THEN
     STRIP_TAC THEN UNDISCH_TAC `is_SOME_Word (FLOOKUP (stack_state_store
                                   (s:(A,C,FFI)stack_state)) BitmapBase)` THEN
     STACKPROPSAUX_OPT_CASES_TAC `FLOOKUP (stack_state_store (s:(A,C,FFI)stack_state)) BitmapBase`
       `x:(A)word_loc` THEN REWRITE_TAC[is_SOME_Word_def] THEN
     STACKPROPSAUX_TYPE_CASES_TAC `:(A)word_loc` THEN
     REWRITE_TAC[is_SOME_Word_def; option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `stack_mem_load (word_add c (store_offset BitmapBase)) (t1:(A,C,FFI)stack_state) =
                 SOME (wl_Word ww)` ASSUME_TAC THENL
    [MATCH_MP_TAC mem_load_lemma THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
     ASM_SIMP_TAC[name_cases; distinctness "store_name"];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  ABBREV_TAC `bp = word_shl (ww:A word) (backend_common_word_shift (:A))` THEN
   ABBREV_TAC `T3 = stack_set_var tb (wl_Word (word_mul (word_add ww i) bytes_in_word))
                      (t1:(A,C,FFI)stack_state)` THEN
   ABBREV_TAC `rst = misc_word_list (word_add bp (word_mul bytes_in_word
                        (word (LENGTH (MAP wl_Word (stack_state_bitmaps (s:(A,C,FFI)stack_state)))))))
                        (MAP wl_Word (buffer_buffer (stack_state_data_buffer s))) STAR
                      word_list_exists
                        (word_add bp (word_mul bytes_in_word
                           (word (LENGTH (buffer_buffer (stack_state_data_buffer s)) +
                                  LENGTH (stack_state_bitmaps s)))))
                        (buffer_space_left (stack_state_data_buffer s)) STAR
                      word_store c (stack_state_store s) STAR
                      misc_word_list c (stack_state_stack s)` THEN
   SUBGOAL_THEN `(misc_word_list bp (MAP wl_Word (stack_state_bitmaps (s:(A,C,FFI)stack_state))) STAR
                  rst STAR memory (stack_state_memory s) (stack_state_mdomain s))
                   (fun2set (stack_state_memory t1,stack_state_mdomain (t1:(A,C,FFI)stack_state)))`
     ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(rator(concl th))))) =
                                              "STAR" with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[the_SOME_Word_def; stack_removeProof_word_list_APPEND] THEN
     EXPAND_TAC "rst" THEN
     MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
     ALL_TAC] THEN
  SUBGOAL_THEN `~(tb = 1) /\ ~(tb = 2) /\ ~(tb = 3) /\ ~(ta = 1) /\ ~(ta = 2) /\ ~(ta = 3) /\
                 ~(tb = ta)` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP lsl_word_shift) THEN
   MP_TAC(ISPECL [`val (i:A word)`; `aw:A word`; `ofs:A word`;
                  `stack_state_bitmaps (s:(A,C,FFI)stack_state)`; `stack_state_mdomain (s:(A,C,FFI)stack_state)`;
                  `stack_state_memory (s:(A,C,FFI)stack_state)`;
                  `stack_state_mdomain (T3:(A,C,FFI)stack_state)`; `a1:A word`;
                  `m1:A word->(A)word_loc`; `bp:A word`; `T3:(A,C,FFI)stack_state`;
                  `ta:num`; `tb:num`; `rst:(A word#(A)word_loc->bool)->bool`] copy_loop_thm) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "T3" THEN
     REWRITE_TAC[stack_set_var_def; stack_get_var_def; STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE;
                 ALL_DISTINCT; MEM; DE_MORGAN_THM] THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_fun2set_SUBSET o ONCE_REWRITE_RULE[STAR_COMM] o
         check (fun th -> can (find_term ((=) `rst:(A word#(A)word_loc->bool)->bool`)) (concl th) &&
                          not (is_eq (concl th)))) THEN REWRITE_TAC[];
       EXPAND_TAC "bp" THEN
       REWRITE_TAC[WORD_VAL; MATCH_MP lsl_word_shift (ASSUME `good_dimindex (:A)`)] THEN
       AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE];
     ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `y:A word`
     (X_CHOOSE_THEN `y2:A word` (X_CHOOSE_THEN `m2:A word->(A)word_loc`
       (CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "mem2"))))))) THEN
   EXISTS_TAC `ck:num` THEN REWRITE_TAC[stack_list_Seq_def] THEN
   MP_TAC(ISPECL [`tb:num`; `k:num`; `c:A word`; `ww:A word`; `i:A word`;
     `stack_Seq (copy_loop ta tb)
        (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or ta 1 (Reg 1))))
                   (stack_Inst (asm_Arith (Binop asm_Or tb 1 (Reg 1))))):(A)stack_prog`;
     `stack_state_clock_fupd (K (ck + stack_state_clock t1)) (t1:(A,C,FFI)stack_state)`]
     STACKPROPSAUX_sc_prefix) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[STACKPROPSAUX_SR_ACC; STACKPROPSAUX_mem_load_clock]; DISCH_THEN SUBST1_TAC] THEN
   SUBGOAL_THEN `stack_set_var tb (wl_Word (word_mul (word_add ww i) bytes_in_word))
                   (stack_state_clock_fupd (K (ck + stack_state_clock t1)) (t1:(A,C,FFI)stack_state)) =
                 stack_state_clock_fupd (K (stack_state_clock (T3:(A,C,FFI)stack_state) + ck)) T3`
     SUBST1_TAC THENL
    [EXPAND_TAC "T3" THEN REWRITE_TAC[stack_set_var_def] THEN REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
     REWRITE_TAC[ADD_SYM];
     ALL_TAC] THEN
   USE_THEN "cl" (fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_ev_seq_none th]) THEN
  W(fun (asl,w) ->
     let ev = find_term (fun t -> try fst(dest_const(rator t)) = "stack_evaluate"
                                  with Failure _ -> false) w in
     let ms = snd(dest_pair(rand ev)) in
     MP_TAC(ISPECL [`ta:num`; `tb:num`; ms; `wl_Word (word 1):(A)word_loc`]
                   STACKPROPSAUX_sc_suffix)) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
   EXPAND_TAC "T3" THEN REWRITE_TAC[stack_set_var_def] THEN REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  MATCH_MP_TAC STACKPROPSAUX_state_rel_regs_mem THEN EXISTS_TAC `c:A word` THEN
   SUBGOAL_THEN `~(tb = k) /\ ~(ta = k) /\ ~(1 = k) /\ ~(2 = k) /\
                 ~(tb = k + 1) /\ ~(ta = k + 1) /\ ~(1 = k + 1) /\ ~(2 = k + 1) /\
                 ~(tb = k + 2) /\ ~(ta = k + 2) /\ ~(1 = k + 2) /\ ~(2 = k + 2)`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(CONJ (ASSUME `tb < k`) (CONJ (ASSUME `ta < k`) (ASSUME `3 < k`))) THEN ARITH_TAC;
     ALL_TAC] THEN
  REMOVE_THEN "cl" (K ALL_TAC) THEN
   BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   TRY(REWRITE_TAC[FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [STACKPROPSAUX_SC_REGS_TAC; STACKPROPSAUX_SC_MEM_TAC;
    STACKPROPSAUX_SC_REGS_TAC; STACKPROPSAUX_SC_MEM_TAC]);;

(* all cases together: the induction of stack_evaluate *)

let STACKPROPSAUX_cc_all = prove
 (`!p (s:(A,C,FFI)stack_state). STACKPROPSAUX_cc p s`,
  STACKPROPSAUX_EVAL_IND_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
   [STACKPROPSAUX_cc_Skip; STACKPROPSAUX_cc_Halt; STACKPROPSAUX_cc_Alloc;
    STACKPROPSAUX_cc_StoreConsts; STACKPROPSAUX_cc_Inst; STACKPROPSAUX_cc_Get;
    STACKPROPSAUX_cc_Set; STACKPROPSAUX_cc_OpCurrHeap; STACKPROPSAUX_cc_Tick;
    STACKPROPSAUX_cc_Seq; STACKPROPSAUX_cc_Return; STACKPROPSAUX_cc_Raise;
    STACKPROPSAUX_cc_Break; STACKPROPSAUX_cc_Continue; STACKPROPSAUX_cc_If;
    STACKPROPSAUX_cc_Loop; STACKPROPSAUX_cc_JumpLower; STACKPROPSAUX_cc_RawCall;
    STACKPROPSAUX_cc_Call; STACKPROPSAUX_cc_Install; STACKPROPSAUX_cc_ShMemOp;
    STACKPROPSAUX_cc_CodeBufferWrite; STACKPROPSAUX_cc_DataBufferWrite;
    STACKPROPSAUX_cc_FFI; STACKPROPSAUX_cc_LocValue; STACKPROPSAUX_cc_StackAlloc;
    STACKPROPSAUX_cc_StackFree; STACKPROPSAUX_cc_StackLoad; STACKPROPSAUX_cc_StackLoadAny;
    STACKPROPSAUX_cc_StackStore; STACKPROPSAUX_cc_StackStoreAny;
    STACKPROPSAUX_cc_StackGetSize; STACKPROPSAUX_cc_StackSetSize;
    STACKPROPSAUX_cc_BitmapLoad]));;

(* HOL4 line 1481 (local) *)
let stack_removeProof_comp_correct = prove
 (CASE_TERM
  `!(p:(A)stack_prog) (s1:(A,C,FFI)stack_state) r s2 t1 k off jump.
     stack_evaluate (p,s1) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_removeProof_state_rel jump off k s1 t1 /\ reg_bound p k
     ==> ?ck t2.
           stack_evaluate (stack_remove_comp jump off k p,
                           stack_state_clock_fupd (K (ck + stack_state_clock t1)) t1) =
             (r,t2) /\
           (match r with
              SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
            | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
            | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
            | _ -> stack_removeProof_state_rel jump off k s2 t2)`,
  REWRITE_TAC[REWRITE_RULE[STACKPROPSAUX_cc_def] STACKPROPSAUX_cc_all]);;

(* the relation of the results of comp_correct gives equal ffi states *)

let STACKPROPSAUX_cc_case_ffi = prove
 (CASE_TERM `!(r:((A)stack_result)option) (s2:(A,C,FFI)stack_state) t2 jump off k.
    (match r with
       SOME (stackSem_Halt _) -> stack_state_ffi t2 = stack_state_ffi s2
     | SOME stack_TimeOut -> stack_state_ffi t2 = stack_state_ffi s2
     | SOME (stack_FinalFFI _) -> stack_state_ffi t2 = stack_state_ffi s2
     | _ -> stack_removeProof_state_rel jump off k s2 t2)
    ==> stack_state_ffi t2 = stack_state_ffi s2`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THENL [MESON_TAC[STACKPROPSAUX_sr_facts]; ALL_TAC] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:(A)stack_result` THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[STACKPROPSAUX_sr_facts]);;

(* HOL4 line 2418 *)
let stack_removeProof_compile_semantics = prove
 (`!jump off k (s1:(A,C,FFI)stack_state) s2 start.
     stack_removeProof_state_rel jump off k s1 s2 /\ ~(stack_semantics start s1 = Fail)
     ==> stack_semantics start s2 = stack_semantics start s1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STACKPROPSAUX_semantics_sim THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`kk:num`; `r:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                 `stack_state_clock_fupd (K kk) (s1:(A,C,FFI)stack_state)`;
                 `r:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
                 `stack_state_clock_fupd (K kk) (s2:(A,C,FFI)stack_state)`;
                 `k:num`; `off:A word#A word`; `jump:bool`] stack_removeProof_comp_correct) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[stack_removeProof_state_rel_with_clock] THEN
    REWRITE_TAC[reg_bound_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)stack_state`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC STACKPROPSAUX_cc_case_ffi THEN
  MAP_EVERY EXISTS_TAC [`r:((A)stack_result)option`; `jump:bool`; `off:A word#A word`; `k:num`] THEN
  ASM_REWRITE_TAC[]);;

(* the init part (HOL4 line 2631 on): store_list_code_thm, addresses *)

(* HOL4 line 2631 *)
let mem_val_def = cake_def
  `(mem_val (regs:(num,(A)word_loc)fmap) (INL (w:A word)) = wl_Word w) /\
   (mem_val regs (INR n) = FAPPLY regs n)`;;

let STACKPROPSAUX_slc_INL = prove
 (`!(s:(A,C,FFI)stack_state) a t c w.
     ~(a = t) /\ stack_get_var a s = SOME (wl_Word w) /\ w IN stack_state_mdomain s
     ==> stack_evaluate
           (stack_list_Seq [stack_Inst (asm_Const t c);
                            stack_Inst (Mem asm_Store t (Addr a (word 0)));
                            stack_Inst (asm_Arith (Binop asm_Add a a (Imm bytes_in_word)))],s) =
         (NONE,stack_state_memory_fupd (K ((w =+ wl_Word c) (stack_state_memory s)))
                 (stack_state_regs_fupd
                    (K (stack_state_regs s |+ (t,wl_Word c) |+
                        (a,wl_Word (word_add w bytes_in_word)))) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(t:num = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  REWRITE_TAC[stack_list_Seq_def] THEN
  REPEAT(CHANGED_TAC
    (ASM_REWRITE_TAC(STACKPROPSAUX_SR_ACC::FLOOKUP_UPDATE::STACKPROPSAUX_EVAL_SIMPS) THEN
     CASE_REWRITE_TAC STACKPROPSAUX_EVAL_SIMPS)) THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_slc_INR = prove
 (`!(s:(A,C,FFI)stack_state) a i v w.
     stack_get_var a s = SOME (wl_Word w) /\ FLOOKUP (stack_state_regs s) i = SOME v /\
     w IN stack_state_mdomain s
     ==> stack_evaluate
           (stack_list_Seq [stack_Inst (Mem asm_Store i (Addr a (word 0)));
                            stack_Inst (asm_Arith (Binop asm_Add a a (Imm bytes_in_word)))],s) =
         (NONE,stack_state_memory_fupd (K ((w =+ v) (stack_state_memory s)))
                 (stack_state_regs_fupd
                    (K (stack_state_regs s |+ (a,wl_Word (word_add w bytes_in_word)))) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  REWRITE_TAC[stack_list_Seq_def] THEN
  REPEAT(CHANGED_TAC
    (ASM_REWRITE_TAC(STACKPROPSAUX_SR_ACC::FLOOKUP_UPDATE::STACKPROPSAUX_EVAL_SIMPS) THEN
     CASE_REWRITE_TAC STACKPROPSAUX_EVAL_SIMPS)) THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_slc_regs = prove
 (`!(f:(num,(A)word_loc)fmap) a t x y z r1.
     ~(a = t) ==> f |+ (t,x) |+ (a,y) |++ [(a,z); (t,r1)] = f |++ [(a,z); (t,r1)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN X_GEN_TAC `k:num` THEN
  MAP_EVERY ASM_CASES_TAC [`t:num = k`; `a:num = k`] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let STACKPROPSAUX_slc_regs2 = prove
 (`!(f:(num,(A)word_loc)fmap) a t y z r1.
     f |+ (a,y) |++ [(a,z); (t,r1)] = f |++ [(a,z); (t,r1)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; FUPDATE_EQ]);;

let STACKPROPSAUX_slc_word = prove
 (`!(w:A word) n.
     word_add (word_add w bytes_in_word) (word_mul bytes_in_word (word n)) =
     word_add w (word_mul bytes_in_word (word (SUC n)))`,
  REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 2636 *)
let store_list_code_thm = prove
 (`!xs (s:(A,C,FFI)stack_state) w frame ys m dm a t.
     (misc_word_list w ys STAR frame) (fun2set (m,dm)) /\
     m = stack_state_memory s /\ dm = stack_state_mdomain s /\
     LENGTH ys = LENGTH xs /\ ~(a = t) /\
     stack_get_var a s = SOME (wl_Word w) /\ t IN FDOM (stack_state_regs s) /\
     ALL (\x. !n. INR n = x ==> ~(n = a) /\ ~(n = t) /\ n IN FDOM (stack_state_regs s)) xs
     ==> ?r1 m1.
           (misc_word_list w (MAP (mem_val (stack_state_regs s)) xs) STAR frame)
             (fun2set (m1,stack_state_mdomain s)) /\
           stack_evaluate (store_list_code a t xs,s) =
             (NONE,stack_state_memory_fupd (K m1)
                     (stack_state_regs_fupd
                        (K (stack_state_regs s |++
                              [(a,wl_Word (word_add w (word_mul bytes_in_word
                                                        (word (LENGTH xs)))));
                               (t,r1)])) s))`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    MAP_EVERY EXISTS_TAC [`FAPPLY (stack_state_regs (s:(A,C,FFI)stack_state)) t`;
                          `stack_state_memory (s:(A,C,FFI)stack_state)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def; SEP_CLAUSES]) THEN
    ASM_REWRITE_TAC[MAP; misc_word_list_def; SEP_CLAUSES; store_list_code_def;
                    STACKPROPSAUX_ev_clause "stack_Skip"; WORD_MUL_0; WORD_ADD_0;
                    FUPDATE_LIST_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM; FUPDATE_ELIM] THEN
    REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x0:A word + num`; `xs:(A word + num)list`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)stack_state`; `w:A word`;
    `frame:(A word#(A)word_loc->bool)->bool`; `ys:((A)word_loc)list`;
    `m:A word->(A)word_loc`; `dm:A word->bool`; `a:num`; `t:num`] THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)word_loc` (X_CHOOSE_THEN `ys1:((A)word_loc)list` SUBST1_TAC))
    (ISPEC `ys:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  REWRITE_TAC[misc_word_list_def; GSYM STAR_ASSOC; ALL] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP read_fun2set) THEN
  SUBGOAL_THEN `~(t:num = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (\x. !n. INR n = x ==> ~(n = a) /\ ~(n = t) /\
                 n IN a INSERT FDOM (stack_state_regs (s:(A,C,FFI)stack_state))) xs /\
    ALL (\x. !n. INR n = x ==> ~(n = a) /\ ~(n = t) /\
                 n IN a INSERT t INSERT FDOM (stack_state_regs (s:(A,C,FFI)stack_state))) xs /\
    MAP (mem_val (stack_state_regs s |+ (a,wl_Word (word_add w bytes_in_word)))) xs =
    MAP (mem_val (stack_state_regs s)) xs /\
    !c. MAP (mem_val (stack_state_regs s |+ (t,wl_Word c) |+
                      (a,wl_Word (word_add w bytes_in_word)))) xs =
        MAP (mem_val (stack_state_regs s)) xs`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term
      ((=) `ALL:((A word + num)->bool)->(A word + num)list->bool`)) (concl th))) THEN
    DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN TRY GEN_TAC THEN
      TRY (MATCH_MP_TAC MAP_EQ) THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_ALL THENL
     [REWRITE_TAC[IN_INSERT] THEN MESON_TAC[];
      REWRITE_TAC[IN_INSERT] THEN MESON_TAC[];
      ALL_TAC; ALL_TAC] THEN
    MATCH_MP_TAC sum_INDUCT THEN
    REWRITE_TAC[mem_val_def; distinctness "sum"; injectivity "sum"; FAPPLY_FUPDATE_THM;
                FORALL_UNWIND_THM2] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `c:A word` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) (ISPEC `x0:A word + num` (cases "sum")) THENL
   [MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `a:num`; `t:num`; `c:A word`; `w:A word`]
      STACKPROPSAUX_slc_INL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[store_list_code_def; MATCH_MP STACKPROPSAUX_ev_seq_none th]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ISPEC `wl_Word (c:A word)` write_fun2set) o
      check (fun th -> can (find_term ((=) `set_sep_one (w:A word,y:(A)word_loc)`)) (concl th))) THEN
    DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPECL
      [`stack_state_memory_fupd (K ((w =+ wl_Word c) (stack_state_memory s)))
          (stack_state_regs_fupd
            (K (stack_state_regs s |+ (t,wl_Word c) |+
                (a,wl_Word (word_add w bytes_in_word)))) (s:(A,C,FFI)stack_state))`;
       `word_add (w:A word) bytes_in_word`;
       `set_sep_one (w:A word,wl_Word (c:A word)) STAR frame`; `ys1:((A)word_loc)list`;
       `(w =+ wl_Word c) (stack_state_memory (s:(A,C,FFI)stack_state))`;
       `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `a:num`; `t:num`]) THEN
    REWRITE_TAC[STACKPROPSAUX_SR_ACC; stack_get_var_def; FLOOKUP_UPDATE; FDOM_FUPDATE] THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term
        ((=) `set_sep_one (w:A word,wl_Word (c:A word))`)) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(A)word_loc`
      (X_CHOOSE_THEN `m1:A word->(A)word_loc` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r1:(A)word_loc`; `m1:A word->(A)word_loc`] THEN
    ASM_REWRITE_TAC[MAP; mem_val_def; misc_word_list_def] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term
        ((=) `fun2set (m1:A word->(A)word_loc,
                       stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
      REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC] THEN
      ASM_SIMP_TAC[STACKPROPSAUX_slc_regs; STACKPROPSAUX_slc_word]];
    SUBGOAL_THEN `~(i:num = a) /\ ~(i = t) /\
                  i IN FDOM (stack_state_regs (s:(A,C,FFI)stack_state))` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> can (find_term
        ((=) `INR (i:num):A word + num`)) (concl th))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `a:num`; `i:num`;
                   `FAPPLY (stack_state_regs (s:(A,C,FFI)stack_state)) i`; `w:A word`]
      STACKPROPSAUX_slc_INR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[store_list_code_def; MATCH_MP STACKPROPSAUX_ev_seq_none th]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ISPEC `FAPPLY (stack_state_regs (s:(A,C,FFI)stack_state)) i`
        write_fun2set) o
      check (fun th -> can (find_term ((=) `set_sep_one (w:A word,y:(A)word_loc)`)) (concl th))) THEN
    DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPECL
      [`stack_state_memory_fupd
          (K ((w =+ FAPPLY (stack_state_regs s) i) (stack_state_memory s)))
          (stack_state_regs_fupd
            (K (stack_state_regs s |+ (a,wl_Word (word_add w bytes_in_word))))
            (s:(A,C,FFI)stack_state))`;
       `word_add (w:A word) bytes_in_word`;
       `set_sep_one (w:A word,FAPPLY (stack_state_regs (s:(A,C,FFI)stack_state)) i) STAR frame`;
       `ys1:((A)word_loc)list`;
       `(w =+ FAPPLY (stack_state_regs s) i) (stack_state_memory (s:(A,C,FFI)stack_state))`;
       `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `a:num`; `t:num`]) THEN
    REWRITE_TAC[STACKPROPSAUX_SR_ACC; stack_get_var_def; FLOOKUP_UPDATE; FDOM_FUPDATE] THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term
        ((=) `set_sep_one (w:A word,FAPPLY (stack_state_regs (s:(A,C,FFI)stack_state)) i)`))
        (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(A)word_loc`
      (X_CHOOSE_THEN `m1:A word->(A)word_loc` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r1:(A)word_loc`; `m1:A word->(A)word_loc`] THEN
    ASM_REWRITE_TAC[MAP; mem_val_def; misc_word_list_def] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term
        ((=) `fun2set (m1:A word->(A)word_loc,
                       stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
      REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC] THEN
      REWRITE_TAC[STACKPROPSAUX_slc_regs2; STACKPROPSAUX_slc_word]]]);;

(* HOL4 line 2727 (local) *)
let MOD_EQ_IMP_MULT = prove
 (`!n d. n MOD d = 0 /\ ~(d = 0) ==> ?k. n = d * k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `n DIV d` THEN
  MP_TAC(SPECL [`n:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MESON_TAC[MULT_SYM]);;

(* HOL4 line 2733 (local) *)
let star_move_lemma = prove
 (`!(p0:(A->bool)->bool) p1 p1' p2 p3 p4.
     p0 STAR p1 STAR p1' STAR p2 STAR p3 STAR p4 =
     p2 STAR (p1 STAR p1' STAR (p3 STAR (p4 STAR p0)))`,
  REPEAT GEN_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

(* HOL4 line 2739 *)
let stack_removeProof_read_mem_def = cake_def
  `(stack_removeProof_read_mem (a:A word) (m:A word->B) 0 = []) /\
   (stack_removeProof_read_mem a m (SUC n) =
      CONS (m a) (stack_removeProof_read_mem (word_add a bytes_in_word) m n))`;;

(* HOL4 line 2745 *)
let addresses_def = cake_def
  `(addresses (a:A word) 0 = {}) /\
   (addresses a (SUC n) = a INSERT addresses (word_add a bytes_in_word) n)`;;
(* HOL4 line 2750 *)
let LENGTH_read_mem = prove
 (`!n (a:A word) (m:A word->B). LENGTH (stack_removeProof_read_mem a m n) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[stack_removeProof_read_mem_def; LENGTH]);;

(* HOL4 line 2756 (local) *)
let IN_addresses = prove
 (`!n (a:A word) x.
     x IN addresses a n <=> ?i. i < n /\ x = word_add a (word_mul (word i) bytes_in_word)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[addresses_def; NOT_IN_EMPTY; IN_INSERT; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LT_0] THEN CONV_TAC WORD_RULE;
      EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[LT_SUC; ADD1; WORD_ADD] THEN
      CONV_TAC WORD_RULE];
    DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
    REWRITE_TAC[NOT_SUC; SUC_INJ] THENL
     [DISCH_TAC THEN DISJ1_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[LT_SUC] THEN DISCH_TAC THEN DISJ2_TAC THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (lhand(concl th))) THEN
    ASM_REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 2770 *)
let addresses_thm = prove
 (`!n (a:A word).
     addresses a n = {word_add a (word_mul (word i) bytes_in_word) | i < n}`,
  REWRITE_TAC[EXTENSION; IN_addresses; IN_ELIM_THM] THEN MESON_TAC[]);;

let STACKPROPSAUX_memory_INSERT = prove
 (`!(m:A->B) a X. ~(a IN X)
     ==> memory m (a INSERT X) = set_sep_one (a,m a) STAR memory m X`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[memory_def; one_STAR] THEN X_GEN_TAC `s:A#B->bool` THEN
  SUBGOAL_THEN `fun2set (m:A->B,a INSERT X) = (a,m a) INSERT fun2set (m,X) /\
                ~((a,m a) IN fun2set (m,X))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_fun2set; FORALL_PAIR_THM; PAIR_EQ] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`p1:A`; `p2:B`] THEN
    ASM_CASES_TAC `p1:A = a` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  SPEC_TAC(`fun2set (m:A->B,X)`,`u:A#B->bool`) THEN
  SPEC_TAC(`(a:A,(m:A->B) a)`,`x:A#B`) THEN SET_TAC[]);;

let STACKPROPSAUX_addr_no_wrap = prove
 (`!(a:A word) k.
     good_dimindex (:A) /\ ~(k = 0) /\ k * (dimindex (:A) DIV 8) < dimword (:A)
     ==> ~(word_add a (word_mul (word k) bytes_in_word) = a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (a:A word) x = a <=> x = word 0`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
  REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL; VAL_WORD; VAL_WORD_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[MULT_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_not_in_addresses = prove
 (`!(a:A word) n.
     good_dimindex (:A) /\ n * (dimindex (:A) DIV 8) < dimword (:A)
     ==> ~(a IN addresses (word_add a bytes_in_word) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_addresses] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (a:A word) b) (word_mul (word i) b) =
                         word_add a (word_add b (word_mul (word i) b))`] THEN
  REWRITE_TAC[WORD_RULE `word_add (b:A word) (word_mul (word i) b) =
                         word_mul (word_add (word i) (word 1)) b`; GSYM WORD_ADD] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[IMP_CLAUSES] THEN
  MATCH_MP_TAC STACKPROPSAUX_addr_no_wrap THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n * dimindex (:A) DIV 8` THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let STACKPROPSAUX_memory_addresses_gen = prove
 (`!n (a:A word) (m:A word->B).
     n * (dimindex (:A) DIV 8) < dimword (:A) /\ good_dimindex (:A)
     ==> memory m (addresses a n) = misc_word_list a (stack_removeProof_read_mem a m n)`,
  INDUCT_TAC THEN
  REWRITE_TAC[addresses_def; stack_removeProof_read_mem_def; misc_word_list_def] THENL
   [REWRITE_TAC[FUN_EQ_THM; memory_def; emp_def; EXTENSION; FORALL_PAIR_THM;
                IN_fun2set; NOT_IN_EMPTY];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n * dimindex (:A) DIV 8 < dimword (:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `SUC n * dimindex (:A) DIV 8` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) bytes_in_word`;
                                `m:A word->B`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC STACKPROPSAUX_memory_INSERT THEN
  MATCH_MP_TAC STACKPROPSAUX_not_in_addresses THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2776 (local) *)
let memory_addresses = prove
 (`!n (a:A word) (m:A word->(A)word_loc).
     n * (dimindex (:A) DIV 8) < dimword (:A) /\ good_dimindex (:A)
     ==> memory m (addresses a n) = misc_word_list a (stack_removeProof_read_mem a m n)`,
  MATCH_ACCEPT_TAC STACKPROPSAUX_memory_addresses_gen);;

(* HOL4 line 2805 (local) *)
let MOD_LESS_EQ_MOD_IMP = prove
 (`!m k n. m MOD k <= n /\ m < k ==> m <= n`,
  MESON_TAC[MOD_LT]);;

(* HOL4 line 2811 (local) *)
let MAP_mem_val_MAP_INL = prove
 (`!(ws:(A word)list) (f:(num,(A)word_loc)fmap).
     MAP (mem_val f) (MAP (INL:A word->A word+num) ws) = MAP wl_Word ws`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; mem_val_def]);;

(* HOL4 line 2817 *)
let word_list_EQ_rev = prove
 (`!(xs:B list) (a:A word).
     misc_word_list a xs =
     word_list_rev (word_add a (word_mul (word (LENGTH xs)) bytes_in_word)) (REVERSE xs)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; REVERSE; misc_word_list_def; word_list_rev_def]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REVERSE_SNOC; SNOC_APPEND; stack_removeProof_word_list_APPEND;
                  word_list_rev_def; misc_word_list_def; SEP_CLAUSES; LENGTH_APPEND;
                  LENGTH] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) (word_mul (word (n + SUC 0)) b)) b =
                         word_add a (word_mul (word n) b)`] THEN
  REWRITE_TAC[WORD_RULE `word_add (a:A word) (word_mul b (word n)) =
                         word_add a (word_mul (word n) b)`] THEN
  CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

(* HOL4 line 2827 (local) *)
let word_list_and_rev_join_lemma = prove
 (`!b (a:A word) (xs:B list) ys p q ss b1.
     (b = word_add a (word_mul (word (LENGTH xs + LENGTH ys)) bytes_in_word)) /\
     (p STAR misc_word_list a (APPEND xs (REVERSE ys)) STAR q) ss /\ b1
     ==> (p STAR misc_word_list a xs STAR word_list_rev b ys STAR q) ss /\ b1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[stack_removeProof_word_list_APPEND] THEN
  MP_TAC(ISPECL [`REVERSE ys:B list`;
                 `word_add (a:A word) (word_mul bytes_in_word (word (LENGTH (xs:B list))))`]
         word_list_EQ_rev) THEN
  REWRITE_TAC[REVERSE_REVERSE; LENGTH_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_ADD; WORD_RULE
   `word_add (word_add (a:A word) (word_mul b (word m))) (word_mul (word n) b) =
    word_add a (word_mul (word_add (word m) (word n)) b)`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

(* HOL4 line 2837 (local) *)
let word_list_IMP_read_mem = prove
 (`!(xs:B list) (a:A word) p m dm.
     (p STAR misc_word_list a xs) (fun2set (m,dm))
     ==> stack_removeProof_read_mem a m (LENGTH xs) = xs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; stack_removeProof_read_mem_def; misc_word_list_def; CONS_11] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:A word`; `h:B`; `p STAR misc_word_list (word_add (a:A word) bytes_in_word) (t:B list)`;
                   `m:A word->B`; `dm:A word->bool`] read_fun2set) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    CONV_TAC(AC STACKPROPSAUX_STAR_AC);
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p STAR set_sep_one (a:A word,h:B)`; `dm:A word->bool`] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    CONV_TAC(AC STACKPROPSAUX_STAR_AC)]);;

(* HOL4 line 2846 (local) *)
let INSERT_DELETE_EQ_DELETE = prove
 (`!(x:A) s. (x INSERT s) DELETE x = s DELETE x`,
  SET_TAC[]);;

(* HOL4 line 2852 *)
let word_list_exists_addresses = prove
 (`!n (a:A word) (m1:A word->B).
     (dimindex (:A) DIV 8) * n < dimword (:A) /\ good_dimindex (:A)
     ==> word_list_exists a n (fun2set (m1,addresses a n))`,
  INDUCT_TAC THEN
  REWRITE_TAC[stack_removeProof_word_list_exists_thm; addresses_def] THENL
   [REWRITE_TAC[emp_def; fun2set_EMPTY]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SEP_EXISTS_THM] THEN EXISTS_TAC `(m1:A word->B) a` THEN
  REWRITE_TAC[one_fun2set; IN_INSERT; INSERT_DELETE_EQ_DELETE] THEN
  SUBGOAL_THEN `n * dimindex (:A) DIV 8 < dimword (:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `SUC n * dimindex (:A) DIV 8` THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `addresses (word_add (a:A word) bytes_in_word) n DELETE a =
                addresses (word_add a bytes_in_word) n` SUBST1_TAC THENL
   [REWRITE_TAC[SET_RULE `(s:A word->bool) DELETE x = s <=> ~(x IN s)`] THEN
    MATCH_MP_TAC STACKPROPSAUX_not_in_addresses THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]);;

(* the init part: init_reduce, init_prop, init_code_pre and word_list lemmas *)

(* HOL4 line 2873 *)
let init_reduce_def = cake_def
  `init_reduce gen_gc' jump off k code bitmaps data_sp coracle
               (s:(A,C,FFI)stack_state) =
     let heap_ptr = theWord (FAPPLY (stack_state_regs s) (k + 2)) in
     let bitmap_ptr = word_shl (theWord (FAPPLY (stack_state_regs s) 3))
                               (backend_common_word_shift (:A)) in
     let stack_ptr = theWord (FAPPLY (stack_state_regs s) k) in
     let base_ptr = theWord (FAPPLY (stack_state_regs s) (k + 1)) in
     let heap_sp = val (word_sub base_ptr heap_ptr) DIV (dimindex (:A) DIV 8) -
                   LENGTH stack_remove_store_list in
     let stack_sp = val (word_sub stack_ptr base_ptr) DIV (dimindex (:A) DIV 8) in
       stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_mdomain_fupd (K (addresses heap_ptr heap_sp))
       (stack_state_bitmaps_fupd (K bitmaps)
       (stack_state_code_fupd (K code)
       (stack_state_compile_fupd
          (K (\c p. stack_state_compile s c (MAP (stack_remove_prog_comp jump off k) p)))
       (stack_state_compile_oracle_fupd (K coracle)
       (stack_state_data_buffer_fupd
          (K (buffer_REC (word_add bitmap_ptr (word_mul bytes_in_word
                                                  (word (LENGTH bitmaps)))) [] data_sp))
       (stack_state_stack_space_fupd (K stack_sp)
       (stack_state_stack_fupd
          (K (stack_removeProof_read_mem base_ptr (stack_state_memory s) (stack_sp + 1)))
       (stack_state_store_fupd
          (K (FEMPTY |++
                MAP (\n. match store_init gen_gc' k n with
                           INL w -> (n,wl_Word w)
                         | INR i -> (n,FAPPLY (stack_state_regs s) i))
                    (CONS CurrHeap stack_remove_store_list))) s)))))))))))`;;

(* HOL4 line 2899 (local) *)
let init_reduce_stack_space = prove
 (`!gen_gc' jump off k code bitmaps data_sp coracle (s8:(A,C,FFI)stack_state).
     stack_state_stack_space
       (init_reduce gen_gc' jump off k code bitmaps data_sp coracle s8) <=
     LENGTH (stack_state_stack
       (init_reduce gen_gc' jump off k code bitmaps data_sp coracle s8))`,
  REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF; STACKPROPSAUX_SR_ACC;
              LENGTH_read_mem] THEN ARITH_TAC);;

(* HOL4 line 2906 *)
let stack_heap_limit_ok_def = cake_def
  `stack_heap_limit_ok (t:(A,C,FFI)stack_state) (stack_lim,heap_lim) <=>
     FLOOKUP (stack_state_store t) HeapLength =
       SOME (wl_Word (word_mul (word heap_lim) bytes_in_word:A word)) /\
     heap_lim * (dimindex (:A) DIV 8) < dimword (:A) /\
     stack_lim = LENGTH (stack_state_stack t)`;;

(* HOL4 line 2913 *)
let init_prop_def = cake_def
  `init_prop gen_gc' max_heap data_sp stack_heap_lim (s:(A,C,FFI)stack_state) <=>
     ?curr other bitmap_base len.
       FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\
       FLOOKUP (stack_state_store s) NextFree = SOME (wl_Word curr) /\
       FLOOKUP (stack_state_store s) TriggerGC =
         SOME (wl_Word (if gen_gc' then curr else other)) /\
       FLOOKUP (stack_state_store s) EndOfHeap = SOME (wl_Word other) /\
       FLOOKUP (stack_state_store s) OtherHeap = SOME (wl_Word other) /\
       FLOOKUP (stack_state_store s) BitmapBase = SOME (wl_Word bitmap_base) /\
       FLOOKUP (stack_state_store s) HeapLength =
         SOME (wl_Word (word_mul (word len) bytes_in_word)) /\
       FLOOKUP (stack_state_store s) ProgStart = SOME (wl_Word (word 0)) /\
       FLOOKUP (stack_state_store s) AllocSize = SOME (wl_Word (word 0)) /\
       FLOOKUP (stack_state_store s) Globals = SOME (wl_Word (word 0)) /\
       FLOOKUP (stack_state_store s) GlobReal = SOME (wl_Word curr) /\
       FLOOKUP (stack_state_store s) Handler = SOME (wl_Word (word 0)) /\
       FLOOKUP (stack_state_store s) GenStart = SOME (wl_Word (word 0)) /\
       FLOOKUP (stack_state_store s) CodeBuffer =
         SOME (wl_Word (buffer_position (stack_state_code_buffer s))) /\
       FLOOKUP (stack_state_store s) CodeBufferEnd =
         SOME (wl_Word (word_add (buffer_position (stack_state_code_buffer s))
                                 (word (buffer_space_left (stack_state_code_buffer s))))) /\
       FLOOKUP (stack_state_store s) BitmapBuffer =
         SOME (wl_Word (buffer_position (stack_state_data_buffer s))) /\
       FLOOKUP (stack_state_store s) BitmapBufferEnd =
         SOME (wl_Word (word_add (buffer_position (stack_state_data_buffer s))
                          (word_mul bytes_in_word
                             (word (buffer_space_left (stack_state_data_buffer s)))))) /\
       stack_heap_limit_ok s stack_heap_lim /\
       buffer_buffer (stack_state_code_buffer s) = [] /\
       buffer_buffer (stack_state_data_buffer s) = [] /\
       stack_state_use_stack s /\ stack_state_use_store s /\
       FLOOKUP (stack_state_regs s) 0 = SOME (wl_Loc 1 0) /\
       LENGTH (stack_state_bitmaps s) + data_sp + 1 < dimword (:A) /\
       LENGTH (stack_state_stack s) < dimword (:A) /\
       (other = word_add curr (word_mul bytes_in_word (word len))) /\
       byte_aligned curr /\
       LAST (stack_state_stack s) = wl_Word (word 0) /\
       LENGTH (stack_state_stack s) = SUC (stack_state_stack_space s) /\
       LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
       len + len <= max_heap /\
       (word_list_exists curr len STAR word_list_exists other len)
         (fun2set (stack_state_memory s,stack_state_mdomain s))`;;

(* HOL4 line 2953 *)
let init_code_pre_def = cake_def
  `init_code_pre k (bitmaps:(A word)list) data_sp (s:(A,C,FFI)stack_state) <=>
     ?ptr2 ptr3 ptr4 bitmap_ptr.
       good_dimindex (:A) /\ 8 <= k /\ 1 IN domain (stack_state_code s) /\
       {k, k + 1, k + 2} SUBSET stack_state_ffi_save_regs s /\
       ~stack_state_use_stack s /\ ~stack_state_use_store s /\ ~stack_state_use_alloc s /\
       FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word (ptr2:A word)) /\
       FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word ptr3) /\
       FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word ptr4) /\
       stack_state_memory s ptr2 = wl_Word bitmap_ptr /\
       stack_state_memory s (word_add ptr2 bytes_in_word) =
         wl_Word (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       stack_state_memory s (word_add ptr2 (word_mul (word 2) bytes_in_word)) =
         wl_Word (word_add (word_add bitmap_ptr
                              (word_mul bytes_in_word (word (LENGTH bitmaps))))
                           (word_mul bytes_in_word (word data_sp))) /\
       stack_state_memory s (word_add ptr2 (word_mul (word 3) bytes_in_word)) =
         wl_Word (buffer_position (stack_state_code_buffer s)) /\
       stack_state_memory s (word_add ptr2 (word_mul (word 4) bytes_in_word)) =
         wl_Word (word_add (buffer_position (stack_state_code_buffer s))
                           (word (buffer_space_left (stack_state_code_buffer s)))) /\
       word_ule ptr2 ptr4 /\ word_ule (word_mul (word 1024) bytes_in_word) (word_sub ptr4 ptr2) /\
       byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       buffer_buffer (stack_state_code_buffer s) = [] /\
       (misc_word_list bitmap_ptr (MAP wl_Word bitmaps) STAR
        word_list_exists (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps))))
                         data_sp STAR
        word_list_exists ptr2 (val (word_sub ptr4 ptr2) DIV val (bytes_in_word:A word)))
         (fun2set (stack_state_memory s,stack_state_mdomain s))`;;

(* HOL4 line 2983 (local) *)
let byte_aligned_bytes_in_word_MULT = prove
 (`!w:A word. good_dimindex (:A) ==> byte_aligned (word_mul bytes_in_word w)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; byte_aligned_def; bytes_in_word_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THENL
   [MP_TAC(ISPECL [`2`; `w:A word`] aligned_mul_shift_1);
    MP_TAC(ISPECL [`3`; `w:A word`] aligned_mul_shift_1)] THEN
  REWRITE_TAC[word_1_lsl] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* HOL4 line 2995 *)
let word_list_wrap = prove
 (`!(a:A word) (ls:B list).
     good_dimindex (:A) /\ dimword (:A) DIV (dimindex (:A) DIV 8) < LENGTH ls
     ==> ?x xs y ys b.
           misc_word_list a ls = misc_word_list a (CONS x xs) STAR misc_word_list b (CONS y ys) /\
           b = a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP stack_removeProof_LESS_LENGTH_IMP_APPEND) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:B list` (X_CHOOSE_THEN `l2:B list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(dimword (:A) DIV (dimindex (:A) DIV 8) = 0) /\
                word_mul bytes_in_word (word (dimword (:A) DIV (dimindex (:A) DIV 8))) =
                word 0:A word`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def; dimword_def; bytes_in_word_def; GSYM WORD_MUL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(l1:B list = []) /\ ~(l2:B list = [])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    UNDISCH_TAC `dimword (:A) DIV (dimindex (:A) DIV 8) < LENGTH (ls:B list)` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    UNDISCH_TAC `~(dimword (:A) DIV (dimindex (:A) DIV 8) = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`HD (l1:B list)`; `TL (l1:B list)`; `HD (l2:B list)`;
                        `TL (l2:B list)`; `a:A word`] THEN
  ASM_SIMP_TAC[GSYM CONS_HD_TL] THEN
  ASM_REWRITE_TAC[stack_removeProof_word_list_APPEND; WORD_ADD_0]);;

(* HOL4 line 3017 (local) *)
let sub_rewrite = prove
 (`!ptr ptr'.
     ptr <= ptr'
     ==> word_add (word_mul (word_neg (word 1)) (word ptr)) (word ptr') =
         word (ptr' - ptr):A word`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 3025 (local) *)
let div_rewrite = prove
 (`!n x. n <= x /\ 1 < n ==> ~(x DIV n = 0)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`x:num`; `n:num`] DIV_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 3034 *)
let stack_removeProof_push_if = prove
 (`!b (f:A->B) g x y.
     ((if b then f x else f y) = f (if b then x else y)) /\
     ((if b then f x else g x) = (if b then f else g) x)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 3041 (local) *)
let fmap_simp_lemma1 = prove
 (`!(g:(num,B)fmap) x y z. g |+ (0,x) |+ (5,y) |+ (0,z) = g |+ (0,z) |+ (5,y)`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`0 = k`; `5 = k`] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 3048 *)
let get_stack_heap_limit''_def = cake_def
  `get_stack_heap_limit'' (h2:num) (h3:num) (h4:num) =
     (h4 - h3 - LENGTH stack_remove_store_list,(h3 - h2) DIV 2)`;;

(* HOL4 line 3053 *)
let get_stack_heap_limit'_def = cake_def
  `get_stack_heap_limit' max_heap (p2:A word) (p3:A word) (p4:A word) =
     let ptr2 = val p2 in
     let ptr3 = val p3 in
     let ptr4 = val p4 in
     let d = dimindex (:A) DIV 8 in
     let max_heap_w = if max_heap * val (bytes_in_word:A word) < dimword (:A)
                      then word_mul bytes_in_word (word max_heap)
                      else word_neg (word 1):A word in
     let reg3 = word_add (word ptr2)
                  (word_shl
                     (word_ushr
                        (word_add (word_mul (word_neg (word 1)) (word ptr2))
                           (if word_ult max_heap_w
                                 (word_add (word_mul (word_neg (word 1)) (word ptr2))
                                           (word ptr3))
                            then word_add max_heap_w (word ptr2):A word
                            else word ptr3))
                        (backend_common_word_shift (:A) + 1))
                     (backend_common_word_shift (:A) + 1)) in
       get_stack_heap_limit'' (ptr2 DIV d) (val reg3 DIV d) (ptr4 DIV d)`;;

(* HOL4 line 3070 *)
let get_stack_heap_limit_def = cake_def
  `get_stack_heap_limit max_heap (ptr2,ptr3,ptr4:A word) =
     let middle = word_add ptr2
                    (word_shl (word_ushr (word_add (word_mul (word_neg (word 1)) ptr2) ptr4)
                                         (backend_common_word_shift (:A) + 1))
                              (backend_common_word_shift (:A))) in
     let adj_ptr2 = word_add ptr2 (word_mul bytes_in_word (word max_stack_alloc)) in
     let adj_ptr4 = word_sub ptr4 (word_mul bytes_in_word (word max_stack_alloc)) in
     let adj_ptr3 = (if word_ule adj_ptr2 ptr3 /\ word_ule ptr3 adj_ptr4 then ptr3
                     else middle) in
       get_stack_heap_limit' max_heap ptr2 adj_ptr3 ptr4`;;

(* HOL4 line 3079 *)
let read_pointers_def = cake_def
  `read_pointers (s:(A,C,FFI)stack_state) =
     (theWord (THE (FLOOKUP (stack_state_regs s) 2)),
      theWord (THE (FLOOKUP (stack_state_regs s) 3)),
      theWord (THE (FLOOKUP (stack_state_regs s) 4)))`;;

(* HOL4 line 3089 *)
let word_list_inj = prove
 (`!(xs:B list) (a:A word) u u'. misc_word_list a xs u /\ misc_word_list a xs u' ==> u = u'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[misc_word_list_def; emp_def; one_STAR] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) bytes_in_word`;
    `(u:A word#B->bool) DELETE (a,h)`; `(u':A word#B->bool) DELETE (a,h)`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `((a:A word),(h:B)) IN u` THEN UNDISCH_TAC `((a:A word),(h:B)) IN u'` THEN
  SET_TAC[]);;

let STACKPROPSAUX_word_list_set_aux = prove
 (`!(xs:B list) (a:A word) s.
     good_dimindex (:A) /\
     val a + LENGTH xs * val (bytes_in_word:A word) < dimword (:A)
     ==> (misc_word_list a xs s <=>
          s = {(word_add a (word_mul (word i) bytes_in_word),EL i xs) | i | i < LENGTH xs})`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[misc_word_list_def; emp_def; LENGTH; LT] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (bytes_in_word:A word) = dimindex (:A) DIV 8`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH]) THEN ASSUME_TAC th) THENL
   [ASM_MESON_TAC[STACKPROPSAUX_val_bytes_in_word]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_add (a:A word) bytes_in_word) + LENGTH (t:B list) * dimindex (:A) DIV 8
                < dimword (:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_ADD; GSYM dimword_def] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `val (a:A word) + SUC (LENGTH (t:B list)) * dimindex (:A) DIV 8` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val (a:A word) + dimindex (:A) DIV 8`; `dimword (:A)`] MOD_LE) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[misc_word_list_def; one_STAR] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `good_dimindex (:A)`)
    (ASSUME `val (word_add (a:A word) bytes_in_word) + LENGTH (t:B list) * dimindex (:A) DIV 8
             < dimword (:A)`))]) THEN
  SUBGOAL_THEN
   `{(word_add a (word_mul (word i) bytes_in_word),EL i (CONS h t)) | i | i < LENGTH (CONS h t)} =
    ((a:A word),(h:B)) INSERT
    {(word_add (word_add a bytes_in_word) (word_mul (word i) bytes_in_word),EL i t) | i |
     i < LENGTH t} /\
    ~(((a:A word),(h:B)) IN
      {(word_add (word_add a bytes_in_word) (word_mul (word i) bytes_in_word),EL i t) | i |
       i < LENGTH (t:B list)})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LENGTH; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`p1:A word`; `p2:B`] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `i:num` MP_TAC) THEN
        DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j:num` SUBST1_TAC)
          (SPEC `i:num` num_CASES) THEN
        REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0; WORD_MUL_0; WORD_ADD_0; PAIR_EQ] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN EXISTS_TAC `j:num` THEN
        ASM_REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
         [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; LT_0; WORD_MUL_0; WORD_ADD_0];
          EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[EL; TL; LT_SUC; PAIR_EQ; ADD1; WORD_ADD] THEN
          CONV_TAC WORD_RULE]];
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; NOT_EXISTS_THM] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`a:A word`; `SUC i`] STACKPROPSAUX_addr_no_wrap) THEN
      ASM_REWRITE_TAC[NOT_SUC] THEN MATCH_MP_TAC(TAUT `p /\ q ==> ~(p ==> ~q)`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC `val (a:A word) + SUC (LENGTH (t:B list)) * dimindex (:A) DIV 8` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(ARITH_RULE `x <= y ==> x <= a + y`) THEN
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
        REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`{(word_add (word_add (a:A word) bytes_in_word) (word_mul (word i) bytes_in_word),
              EL i t) | i | i < LENGTH (t:B list)}`, `u:A word#B->bool`) THEN
  SPEC_TAC(`((a:A word),(h:B))`,`x:A word#B`) THEN SET_TAC[]);;

let STACKPROPSAUX_set_of_list_seq = prove
 (`!(a:A word) (xs:B list).
     set_of_list (list_of_seq (\i. (word_add a (word_mul (word i) bytes_in_word),EL i xs))
                              (LENGTH xs)) =
     {(word_add a (word_mul (word i) bytes_in_word),EL i xs) | i | i < LENGTH xs}`,
  REWRITE_TAC[LIST_TO_SET_GENLIST; EXTENSION; IN_IMAGE; count_DEF; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* HOL4 line 3101 *)
let word_list_set = prove
 (`!(xs:B list) (a:A word).
     good_dimindex (:A) /\
     val a + LENGTH xs * val (bytes_in_word:A word) < dimword (:A)
     ==> misc_word_list a xs
           (set_of_list (list_of_seq (\i. (word_add a (word_mul (word i) bytes_in_word):A word,
                                           EL i xs)) (LENGTH xs)))`,
  SIMP_TAC[STACKPROPSAUX_word_list_set_aux; STACKPROPSAUX_set_of_list_seq]);;

(* HOL4 line 3166 *)
let word_list_seteq = prove
 (`!(xs:B list) (a:A word).
     good_dimindex (:A) /\
     val a + LENGTH xs * val (bytes_in_word:A word) < dimword (:A)
     ==> misc_word_list a xs =
         (\s. s = set_of_list (list_of_seq (\i. (word_add a (word_mul (word i)
                                                 bytes_in_word):A word, EL i xs))
                                           (LENGTH xs)))`,
  SIMP_TAC[FUN_EQ_THM; STACKPROPSAUX_word_list_set_aux; STACKPROPSAUX_set_of_list_seq]);;

(* HOL4 line 3180 *)
let word_list_EL_in_memory = prove
 (`!(a:A word) (xs:B list) r1 r2 m dm i.
     good_dimindex (:A) /\
     val a + LENGTH xs * val (bytes_in_word:A word) < dimword (:A) /\
     (r1 STAR misc_word_list a xs STAR r2) (fun2set (m,dm)) /\
     i < LENGTH xs
     ==> m (word_add a (word_mul (word i) bytes_in_word):A word) = EL i xs`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN
  MP_TAC(ISPECL [`xs:B list`; `a:A word`; `r1 STAR r2:(A word#B->bool)->bool`;
                 `m:A word->B`; `dm:A word->bool`; `i:num`] STACKPROPSAUX_word_list_read) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "fun2set")) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

(* HOL4 line 3201 *)
let word_list_in_memory = prove
 (`!(a:A word) (xs:B list) r1 r2 m dm.
     (r1 STAR misc_word_list a xs STAR r2) (fun2set (m,dm)) /\
     good_dimindex (:A) /\
     val a + LENGTH xs * val (bytes_in_word:A word) < dimword (:A)
     ==> memory m (addresses a (LENGTH xs)) = misc_word_list a xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`LENGTH (xs:B list)`; `a:A word`; `m:A word->B`]
    STACKPROPSAUX_memory_addresses_gen) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (bytes_in_word:A word) = dimindex (:A) DIV 8` (SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[STACKPROPSAUX_val_bytes_in_word]; ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC word_list_IMP_read_mem THEN
  MAP_EVERY EXISTS_TAC [`r1 STAR r2:(A word#B->bool)->bool`; `dm:A word->bool`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "fun2set")) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

(* init_code_thm (HOL4 line 3225): evaluation of the init code, segment by segment *)

let STACKPROPSAUX_ev_seq_NONE_inv = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state) s1.
     stack_evaluate (stack_Seq c1 c2,s) = (NONE,s1)
     ==> ?s2. stack_evaluate (c1,s) = (NONE,s2) /\ stack_evaluate (c2,s2) = (NONE,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (c1:(A)stack_prog,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s2:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res:((A)stack_result)option = NONE` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_list_Seq_APPEND = prove
 (`!l1 l2 (s:(A,C,FFI)stack_state) s1.
     ~(l1 = []) /\ ~(l2 = []) /\ stack_evaluate (stack_list_Seq l1,s) = (NONE,s1)
     ==> stack_evaluate (stack_list_Seq (APPEND l1 l2),s) =
         stack_evaluate (stack_list_Seq l2,s1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `l2:((A)stack_prog)list` THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)stack_prog` (X_CHOOSE_THEN `l3:((A)stack_prog)list` SUBST1_TAC))
    (ISPEC `l2:((A)stack_prog)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x:(A)stack_prog` (X_CHOOSE_THEN `t2:((A)stack_prog)list` SUBST_ALL_TAC))
    (ISPEC `t:((A)stack_prog)list` list_CASES) THEN
  REWRITE_TAC[APPEND; stack_list_Seq_def] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_ev_seq_none THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `s2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC o
                  MATCH_MP STACKPROPSAUX_ev_seq_NONE_inv) THEN
    MP_TAC(ISPECL [`h:(A)stack_prog`;
                   `stack_list_Seq (APPEND (CONS x t2) (CONS y l3)):(A)stack_prog`;
                   `s:(A,C,FFI)stack_state`; `s2:(A,C,FFI)stack_state`]
           STACKPROPSAUX_ev_seq_none) THEN
    ASM_REWRITE_TAC[APPEND] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (y:(A)stack_prog) l3`; `s2:(A,C,FFI)stack_state`;
                                  `s1:(A,C,FFI)stack_state`]) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; APPEND]]);;

let STACKPROPSAUX_init_shift_facts = prove
 (`good_dimindex (:A)
   ==> val (word (1 + backend_common_word_shift (:A)):A word) =
         1 + backend_common_word_shift (:A) /\
       val (word (backend_common_word_shift (:A) + 1):A word) =
         backend_common_word_shift (:A) + 1 /\
       val (word (backend_common_word_shift (:A)):A word) = backend_common_word_shift (:A) /\
       val (word 1:A word) = 1 /\
       (1 + backend_common_word_shift (:A) >= dimindex (:A) <=> F) /\
       (backend_common_word_shift (:A) + 1 >= dimindex (:A) <=> F) /\
       (backend_common_word_shift (:A) >= dimindex (:A) <=> F) /\
       (1 >= dimindex (:A) <=> F)`,
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; VAL_WORD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_init_code_split = prove
 (`!gen_gc' max_heap k.
     stack_remove_init_code gen_gc' max_heap k:(A)stack_prog =
     stack_list_Seq
      (APPEND
       [stack_Inst (asm_Arith (Binop asm_Or 0 4 (Reg 4)));
        stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 0 0
          (Imm (word (1 + backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (asm_Shift Lsl 0 0
          (Imm (word (backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Reg 2)));
        stack_Inst (asm_Const 5 (word_mul (word max_stack_alloc) bytes_in_word));
        stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 5)));
        stack_Inst (asm_Arith (Binop asm_Sub 4 4 (Reg 5)))]
      (APPEND
       [stack_If Lower 3 (Reg 2) (stack_Inst (asm_Arith (Binop asm_Or 3 0 (Reg 0))))
          (stack_If Lower 4 (Reg 3)
             (stack_Inst (asm_Arith (Binop asm_Or 3 0 (Reg 0)))) stack_Skip)]
      (APPEND
       [stack_Inst (asm_Const 0 (word_mul (word max_stack_alloc) bytes_in_word));
        stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 0)));
        stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 0)));
        stack_Inst (asm_Arith (Binop asm_Or 0 3 (Reg 3)));
        stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
        stack_Inst (asm_Const 5
          (if max_heap * val (bytes_in_word:A word) < dimword (:A)
           then word_mul (word max_heap) bytes_in_word
           else word_sub (word 0) (word 1)))]
      (APPEND
       [stack_If Lower 5 (Reg 0)
          (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or 3 2 (Reg 2))))
                     (stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 5)))))
          stack_Skip]
      (APPEND
       [stack_Inst (asm_Arith (Binop asm_Sub 3 3 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 3 3
          (Imm (word (backend_common_word_shift (:A) + 1)))));
        stack_Inst (asm_Arith (asm_Shift Lsl 3 3
          (Imm (word (backend_common_word_shift (:A) + 1)))));
        stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 2)));
        stack_Inst (asm_Arith (Binop asm_Or 5 3 (Reg 3)));
        stack_Inst (asm_Arith (Binop asm_Sub 5 5 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 5 5 (Imm (word 1))));
        stack_Inst (asm_Arith (Binop asm_Or (k + 2) 2 (Reg 2)));
        stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 5)));
        stack_Inst (asm_Arith (Binop asm_Or k 4 (Reg 4)));
        stack_Inst (asm_Arith (Binop asm_Or (k + 1) 3 (Reg 3)))]
      (APPEND
       [stack_Inst (Mem asm_Load 3 (Addr (k + 2) (word 0)));
        stack_Inst (asm_Arith (asm_Shift Lsr 3 3
          (Imm (word (backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (Binop asm_Or 0 (k + 2) (Reg (k + 2))));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 4 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 6 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 7 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 1 (Addr 0 (word 0)))]
       [init_memory k (MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list));
        stack_LocValue 0 1 0]))))))`,
  REWRITE_TAC[stack_remove_init_code_def; LET_DEF; LET_END_DEF; APPEND]);;

let STACKPROPSAUX_RUN_TAC (extra:thm list) : tactic =
  REWRITE_TAC[stack_list_Seq_def] THEN
  REPEAT(CHANGED_TAC
    (ASM_REWRITE_TAC(STACKPROPSAUX_SR_ACC::FLOOKUP_UPDATE::ARITH_EQ::WORD_OR_0::WORD_OR_REFL::
                     extra @ STACKPROPSAUX_EVAL_SIMPS) THEN
     CASE_REWRITE_TAC STACKPROPSAUX_EVAL_SIMPS)) THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC; FUPDATE_EQ];;

let STACKPROPSAUX_init_segA = prove
 (`!(s:(A,C,FFI)stack_state) p2 p4.
     good_dimindex (:A) /\
     FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word p2) /\
     FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word p4)
     ==> stack_evaluate (stack_list_Seq
       [stack_Inst (asm_Arith (Binop asm_Or 0 4 (Reg 4)));
        stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 0 0
          (Imm (word (1 + backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (asm_Shift Lsl 0 0
          (Imm (word (backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Reg 2)));
        stack_Inst (asm_Const 5 (word_mul (word max_stack_alloc) bytes_in_word));
        stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 5)));
        stack_Inst (asm_Arith (Binop asm_Sub 4 4 (Reg 5)))],s) =
       (NONE,stack_state_regs_fupd (K (stack_state_regs s |+
          (0,wl_Word (word_add (word_shl (word_ushr (word_sub p4 p2)
                                  (1 + backend_common_word_shift (:A)))
                                  (backend_common_word_shift (:A))) p2)) |+
          (5,wl_Word (word_mul (word max_stack_alloc) bytes_in_word)) |+
          (2,wl_Word (word_add p2 (word_mul (word max_stack_alloc) bytes_in_word))) |+
          (4,wl_Word (word_sub p4 (word_mul (word max_stack_alloc) bytes_in_word))))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_init_shift_facts) THEN
  STACKPROPSAUX_RUN_TAC []);;

let STACKPROPSAUX_init_segB = prove
 (`!(s:(A,C,FFI)stack_state) m a2 p3 a4.
     FLOOKUP (stack_state_regs s) 0 = SOME (wl_Word m) /\
     FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word a2) /\
     FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word p3) /\
     FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word a4)
     ==> stack_evaluate (stack_list_Seq
       [stack_If Lower 3 (Reg 2) (stack_Inst (asm_Arith (Binop asm_Or 3 0 (Reg 0))))
          (stack_If Lower 4 (Reg 3)
             (stack_Inst (asm_Arith (Binop asm_Or 3 0 (Reg 0)))) stack_Skip)],s) =
       (NONE,stack_state_regs_fupd (K (stack_state_regs s |+
          (3,wl_Word (if word_ule a2 p3 /\ word_ule p3 a4 then p3 else m)))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_NOT_LOWER] THEN
  ASM_CASES_TAC `word_ult (p3:A word) a2` THEN ASM_CASES_TAC `word_ult (a4:A word) p3` THEN
  STACKPROPSAUX_RUN_TAC [] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM]);;

let STACKPROPSAUX_init_segC = prove
 (`!(s:(A,C,FFI)stack_state) a2 a3 a4 mhw.
     FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word a2) /\
     FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word a3) /\
     FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word a4)
     ==> stack_evaluate (stack_list_Seq
       [stack_Inst (asm_Const 0 (word_mul (word max_stack_alloc) bytes_in_word));
        stack_Inst (asm_Arith (Binop asm_Sub 2 2 (Reg 0)));
        stack_Inst (asm_Arith (Binop asm_Add 4 4 (Reg 0)));
        stack_Inst (asm_Arith (Binop asm_Or 0 3 (Reg 3)));
        stack_Inst (asm_Arith (Binop asm_Sub 0 0 (Reg 2)));
        stack_Inst (asm_Const 5 mhw)],s) =
       (NONE,stack_state_regs_fupd (K (stack_state_regs s |+
          (2,wl_Word (word_sub a2 (word_mul (word max_stack_alloc) bytes_in_word))) |+
          (4,wl_Word (word_add a4 (word_mul (word max_stack_alloc) bytes_in_word))) |+
          (0,wl_Word (word_sub a3 (word_sub a2 (word_mul (word max_stack_alloc)
                                                         bytes_in_word)))) |+
          (5,wl_Word mhw))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STACKPROPSAUX_RUN_TAC [] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN X_GEN_TAC `n:num` THEN
  MAP_EVERY ASM_CASES_TAC [`n = 0`; `n = 2`; `n = 4`; `n = 5`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_K_FACTS_TAC : tactic =
  let es = ["k"; "k + 1"; "k + 2"] and ns = List.map string_of_int (0--7) in
  let fs = List.concat (List.map (fun e -> List.concat (List.map (fun n ->
             ["~(" ^ e ^ " = " ^ n ^ ")"; "~(" ^ n ^ " = " ^ e ^ ")"]) ns)) es) @
           ["~(k + 1 = k)"; "~(k + 2 = k)"; "~(k + 2 = k + 1)"; "~(k = k + 1)";
            "~(k = k + 2)"; "~(k + 1 = k + 2)"] in
  let tm = parse_term (String.concat " /\\ " fs) in
  SUBGOAL_THEN tm STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC];;

let STACKPROPSAUX_init_segD = prove
 (`!(s:(A,C,FFI)stack_state) mh r0 p2 r3.
     FLOOKUP (stack_state_regs s) 0 = SOME (wl_Word r0) /\
     FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word p2) /\
     FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word r3) /\
     FLOOKUP (stack_state_regs s) 5 = SOME (wl_Word mh)
     ==> stack_evaluate (stack_list_Seq
       [stack_If Lower 5 (Reg 0)
          (stack_Seq (stack_Inst (asm_Arith (Binop asm_Or 3 2 (Reg 2))))
                     (stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 5)))))
          stack_Skip],s) =
       (NONE,stack_state_regs_fupd (K (stack_state_regs s |+
          (3,wl_Word (if word_ult mh r0 then word_add p2 mh else r3)))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `word_ult (mh:A word) r0` THEN
  STACKPROPSAUX_RUN_TAC [] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_FUPDATE_FLOOKUP_ELIM]);;

let STACKPROPSAUX_init_segE = prove
 (`!(s:(A,C,FFI)stack_state) k p2 r3 r4.
     good_dimindex (:A) /\ 8 <= k /\
     FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word p2) /\
     FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word r3) /\
     FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word r4)
     ==> stack_evaluate (stack_list_Seq
       [stack_Inst (asm_Arith (Binop asm_Sub 3 3 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 3 3
          (Imm (word (backend_common_word_shift (:A) + 1)))));
        stack_Inst (asm_Arith (asm_Shift Lsl 3 3
          (Imm (word (backend_common_word_shift (:A) + 1)))));
        stack_Inst (asm_Arith (Binop asm_Add 3 3 (Reg 2)));
        stack_Inst (asm_Arith (Binop asm_Or 5 3 (Reg 3)));
        stack_Inst (asm_Arith (Binop asm_Sub 5 5 (Reg 2)));
        stack_Inst (asm_Arith (asm_Shift Lsr 5 5 (Imm (word 1))));
        stack_Inst (asm_Arith (Binop asm_Or (k + 2) 2 (Reg 2)));
        stack_Inst (asm_Arith (Binop asm_Add 2 2 (Reg 5)));
        stack_Inst (asm_Arith (Binop asm_Or k 4 (Reg 4)));
        stack_Inst (asm_Arith (Binop asm_Or (k + 1) 3 (Reg 3)))],s) =
       (NONE,stack_state_regs_fupd (K (stack_state_regs s |+
          (3,wl_Word (word_add (word_shl (word_ushr (word_sub r3 p2)
                        (backend_common_word_shift (:A) + 1))
                        (backend_common_word_shift (:A) + 1)) p2)) |+
          (5,wl_Word (word_ushr (word_sub (word_add (word_shl (word_ushr (word_sub r3 p2)
                        (backend_common_word_shift (:A) + 1))
                        (backend_common_word_shift (:A) + 1)) p2) p2) 1)) |+
          (k + 2,wl_Word p2) |+
          (2,wl_Word (word_add p2 (word_ushr (word_sub (word_add (word_shl (word_ushr
                        (word_sub r3 p2) (backend_common_word_shift (:A) + 1))
                        (backend_common_word_shift (:A) + 1)) p2) p2) 1))) |+
          (k,wl_Word r4) |+
          (k + 1,wl_Word (word_add (word_shl (word_ushr (word_sub r3 p2)
                        (backend_common_word_shift (:A) + 1))
                        (backend_common_word_shift (:A) + 1)) p2)))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_init_shift_facts) THEN
  STACKPROPSAUX_K_FACTS_TAC THEN
  STACKPROPSAUX_RUN_TAC []);;

let STACKPROPSAUX_init_segF = prove
 (`!(s:(A,C,FFI)stack_state) k p2 x0 v1 v2 v3 v4.
     good_dimindex (:A) /\ 8 <= k /\
     FLOOKUP (stack_state_regs s) (k + 2) = SOME (wl_Word p2) /\
     p2 IN stack_state_mdomain s /\
     word_add p2 bytes_in_word IN stack_state_mdomain s /\
     word_add p2 (word_mul (word 2) bytes_in_word) IN stack_state_mdomain s /\
     word_add p2 (word_mul (word 3) bytes_in_word) IN stack_state_mdomain s /\
     word_add p2 (word_mul (word 4) bytes_in_word) IN stack_state_mdomain s /\
     stack_state_memory s p2 = wl_Word x0 /\
     stack_state_memory s (word_add p2 bytes_in_word) = v1 /\
     stack_state_memory s (word_add p2 (word_mul (word 2) bytes_in_word)) = v2 /\
     stack_state_memory s (word_add p2 (word_mul (word 3) bytes_in_word)) = v3 /\
     stack_state_memory s (word_add p2 (word_mul (word 4) bytes_in_word)) = v4
     ==> stack_evaluate (stack_list_Seq
       [stack_Inst (Mem asm_Load 3 (Addr (k + 2) (word 0)));
        stack_Inst (asm_Arith (asm_Shift Lsr 3 3
          (Imm (word (backend_common_word_shift (:A))))));
        stack_Inst (asm_Arith (Binop asm_Or 0 (k + 2) (Reg (k + 2))));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 4 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 6 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 7 (Addr 0 (word 0)));
        stack_Inst (asm_Arith (Binop asm_Add 0 0 (Imm bytes_in_word)));
        stack_Inst (Mem asm_Load 1 (Addr 0 (word 0)))],s) =
       (NONE,stack_state_regs_fupd (K (stack_state_regs s |+
          (3,wl_Word (word_ushr x0 (backend_common_word_shift (:A)))) |+
          (4,v1) |+ (6,v2) |+ (7,v3) |+
          (0,wl_Word (word_add p2 (word_mul (word 4) bytes_in_word))) |+
          (1,v4))) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_init_shift_facts) THEN
  STACKPROPSAUX_K_FACTS_TAC THEN
  STACKPROPSAUX_RUN_TAC
    [WORD_RULE `word_add (word_add (p2:A word) b) b = word_add p2 (word_mul (word 2) b)`;
     WORD_RULE `word_add (word_add (p2:A word) (word_mul (word 2) b)) b =
                word_add p2 (word_mul (word 3) b)`;
     WORD_RULE `word_add (word_add (p2:A word) (word_mul (word 3) b)) b =
                word_add p2 (word_mul (word 4) b)`] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN X_GEN_TAC `n:num` THEN
  MAP_EVERY ASM_CASES_TAC [`n = 0`; `n = 1`; `n = 3`; `n = 4`; `n = 6`; `n = 7`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_init_LocValue = prove
 (`!(s:(A,C,FFI)stack_state).
     1 IN domain (stack_state_code s)
     ==> stack_evaluate (stack_LocValue 0 1 0,s) =
         (NONE,stack_state_regs_fupd (K (stack_state_regs s |+ (0,wl_Loc 1 0))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_LocValue"] THEN
  ASM_REWRITE_TAC[loc_check_def; stack_set_var_def]);;

let STACKPROPSAUX_list5_split = prove
 (`!a1 a2 a3 a4 a5:(A)stack_prog. [a1;a2;a3;a4;a5] = APPEND [a1;a2;a3;a4] [a5]`,
  REWRITE_TAC[APPEND]);;

let STACKPROPSAUX_init_memory_thm = prove
 (`!(s:(A,C,FFI)stack_state) k p4 w frame ys xs.
     8 <= k /\
     FLOOKUP (stack_state_regs s) k = SOME (wl_Word p4) /\
     FLOOKUP (stack_state_regs s) (k + 1) = SOME (wl_Word w) /\
     word_sub p4 bytes_in_word IN stack_state_mdomain s /\
     (misc_word_list w ys STAR frame)
       (fun2set ((word_sub p4 bytes_in_word =+ wl_Word (word 0)) (stack_state_memory s),
                 stack_state_mdomain s)) /\
     LENGTH ys = LENGTH xs /\
     ALL (\x. !n. INR n = x ==> ~(n = k + 1) /\ ~(n = 0) /\
                               n IN FDOM (stack_state_regs s)) xs
     ==> ?r1 m1.
           (misc_word_list w (MAP (mem_val (stack_state_regs s |+ (0,wl_Word bytes_in_word) |+
                                     (k,wl_Word (word_sub p4 bytes_in_word)) |+
                                     (0,wl_Word (word 0)))) xs) STAR frame)
             (fun2set (m1,stack_state_mdomain s)) /\
           stack_evaluate (init_memory k xs,s) =
             (NONE,stack_state_memory_fupd (K m1)
                     (stack_state_regs_fupd
                        (K (stack_state_regs s |+ (0,wl_Word bytes_in_word) |+
                              (k,wl_Word (word_sub p4 bytes_in_word)) |+
                              (0,wl_Word (word 0)) |++
                              [(k + 1,wl_Word (word_add w (word_mul bytes_in_word
                                                        (word (LENGTH xs)))));
                               (0,r1)])) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STACKPROPSAUX_K_FACTS_TAC THEN
  SUBGOAL_THEN
   `stack_evaluate (stack_list_Seq
      [stack_Inst (asm_Const 0 bytes_in_word);
       stack_Inst (asm_Arith (Binop asm_Sub k k (Reg 0)));
       stack_Inst (asm_Const 0 (word 0));
       stack_Inst (Mem asm_Store 0 (Addr k (word 0)))],s) =
    (NONE,stack_state_memory_fupd
            (K ((word_sub p4 bytes_in_word =+ wl_Word (word 0)) (stack_state_memory s)))
            (stack_state_regs_fupd (K (stack_state_regs (s:(A,C,FFI)stack_state) |+ (0,wl_Word bytes_in_word) |+
                  (k,wl_Word (word_sub p4 bytes_in_word)) |+ (0,wl_Word (word 0)))) s))`
  ASSUME_TAC THENL
   [STACKPROPSAUX_RUN_TAC []; ALL_TAC] THEN
  REWRITE_TAC[init_memory_def; STACKPROPSAUX_list5_split] THEN
  MP_TAC(ISPECL
   [`[stack_Inst (asm_Const 0 bytes_in_word);
      stack_Inst (asm_Arith (Binop asm_Sub k k (Reg 0)));
      stack_Inst (asm_Const 0 (word 0));
      stack_Inst (Mem asm_Store 0 (Addr k (word 0)))]:((A)stack_prog)list`;
    `[store_list_code (k + 1) 0 (xs:(A word+num)list)]:((A)stack_prog)list`;
    `s:(A,C,FFI)stack_state`;
    `stack_state_memory_fupd
       (K ((word_sub p4 bytes_in_word =+ wl_Word (word 0)) (stack_state_memory s)))
       (stack_state_regs_fupd (K (stack_state_regs (s:(A,C,FFI)stack_state) |+ (0,wl_Word bytes_in_word) |+
                  (k,wl_Word (word_sub p4 bytes_in_word)) |+ (0,wl_Word (word 0)))) s)`]
   STACKPROPSAUX_list_Seq_APPEND) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[stack_list_Seq_def] THEN
  MP_TAC(ISPECL [`xs:(A word+num)list`;
    `stack_state_memory_fupd
       (K ((word_sub p4 bytes_in_word =+ wl_Word (word 0)) (stack_state_memory s)))
       (stack_state_regs_fupd (K (stack_state_regs (s:(A,C,FFI)stack_state) |+ (0,wl_Word bytes_in_word) |+
                  (k,wl_Word (word_sub p4 bytes_in_word)) |+ (0,wl_Word (word 0)))) s)`;
    `w:A word`; `frame:(A word#(A)word_loc->bool)->bool`; `ys:((A)word_loc)list`;
    `(word_sub p4 bytes_in_word =+ wl_Word (word 0))
       (stack_state_memory (s:(A,C,FFI)stack_state))`;
    `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `k + 1`; `0`] store_list_code_thm) THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[stack_get_var_def; STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE; FDOM_FUPDATE;
                    IN_INSERT] THEN
    UNDISCH_TAC `ALL (\x. !n. INR n = x ==> ~(n = k + 1) /\ ~(n = 0) /\
                              n IN FDOM (stack_state_regs (s:(A,C,FFI)stack_state)))
                     (xs:(A word+num)list)` THEN
    MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(A)word_loc`
    (X_CHOOSE_THEN `m1:A word->(A)word_loc` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r1:(A)word_loc`; `m1:A word->(A)word_loc`] THEN
  ASM_REWRITE_TAC[PAIR_EQ; stack_state_component_equality; STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_list_Seq_APPEND_alt = prove
 (`!h t (s:(A,C,FFI)stack_state) s1.
     stack_evaluate (stack_list_Seq (CONS h t),s) = (NONE,s1)
     ==> !l2. ~(l2 = [])
              ==> stack_evaluate (stack_list_Seq (APPEND (CONS h t) l2),s) =
                  stack_evaluate (stack_list_Seq l2,s1)`,
  MESON_TAC[STACKPROPSAUX_list_Seq_APPEND; NOT_CONS_NIL]);;

let STACKPROPSAUX_store_init_INR = prove
 (`!gen_gc' k n i. store_init gen_gc' k n = (INR i:A word+num)
     ==> i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = k + 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[store_init_def; UPDATE_LIST_THM; APPLY_UPDATE_THM; K_THM; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "sum"; injectivity "sum"] THEN ARITH_TAC);;

let STACKPROPSAUX_mem_val_store_init = prove
 (`!(R:(num,(A)word_loc)fmap) R' gen_gc' k l.
     (!i. i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = k + 2
          ==> FAPPLY R i = FAPPLY R' i)
     ==> MAP (mem_val R) (MAP (store_init gen_gc' k) l) =
         MAP (mem_val R') (MAP (store_init gen_gc' k) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN X_GEN_TAC `nm:store_name` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPEC `store_init gen_gc' k nm:A word+num` (cases "sum")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[mem_val_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_store_init_INR) THEN
  ASM_MESON_TAC[]);;

let STACKPROPSAUX_cur_state (w:term) : term =
  rand(rand(lhs(find_term (fun t -> is_eq t &&
     (try fst(dest_const(fst(strip_comb(lhs t)))) = "stack_evaluate"
      with Failure _ -> false)) w)));;

let STACKPROPSAUX_SEG_TAC : tactic =
  ANTS_TAC THENL
   [REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> SIMP_TAC[MATCH_MP STACKPROPSAUX_list_Seq_APPEND_alt th;
                               APPEND_EQ_NIL; NOT_CONS_NIL]) THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM;;

let STACKPROPSAUX_FOLD_TAC (v:term) : tactic =
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhs(concl th) = v));;

let STACKPROPSAUX_init_eval = prove
 (`!(s:(A,C,FFI)stack_state) gen_gc' max_heap k ptr2 ptr3 ptr4 bitmap_ptr v1 v2 v3 v4
    mid adj3 mhw q reg3 half frame ys.
     good_dimindex (:A) /\ 8 <= k /\ 1 IN domain (stack_state_code s) /\
     FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word ptr2) /\
     FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word ptr3) /\
     FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word ptr4) /\
     ptr2 IN stack_state_mdomain s /\
     word_add ptr2 bytes_in_word IN stack_state_mdomain s /\
     word_add ptr2 (word_mul (word 2) bytes_in_word) IN stack_state_mdomain s /\
     word_add ptr2 (word_mul (word 3) bytes_in_word) IN stack_state_mdomain s /\
     word_add ptr2 (word_mul (word 4) bytes_in_word) IN stack_state_mdomain s /\
     word_sub ptr4 bytes_in_word IN stack_state_mdomain s /\
     stack_state_memory s ptr2 = wl_Word bitmap_ptr /\
     stack_state_memory s (word_add ptr2 bytes_in_word) = v1 /\
     stack_state_memory s (word_add ptr2 (word_mul (word 2) bytes_in_word)) = v2 /\
     stack_state_memory s (word_add ptr2 (word_mul (word 3) bytes_in_word)) = v3 /\
     stack_state_memory s (word_add ptr2 (word_mul (word 4) bytes_in_word)) = v4 /\
     mid = word_add (word_shl (word_ushr (word_sub ptr4 ptr2)
                                 (1 + backend_common_word_shift (:A)))
                              (backend_common_word_shift (:A))) ptr2 /\
     adj3 = (if word_ule (word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word)) ptr3 /\
                word_ule ptr3 (word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word))
             then ptr3 else mid) /\
     mhw = (if max_heap * val (bytes_in_word:A word) < dimword (:A)
            then word_mul (word max_heap) bytes_in_word else word_sub (word 0) (word 1)) /\
     q = (if word_ult mhw (word_sub adj3 ptr2) then word_add ptr2 mhw else adj3) /\
     reg3 = word_add (word_shl (word_ushr (word_sub q ptr2)
                                  (backend_common_word_shift (:A) + 1))
                               (backend_common_word_shift (:A) + 1)) ptr2 /\
     half = word_ushr (word_sub reg3 ptr2) 1 /\
     (misc_word_list reg3 ys STAR frame)
       (fun2set ((word_sub ptr4 bytes_in_word =+ wl_Word (word 0)) (stack_state_memory s),
                 stack_state_mdomain s)) /\
     LENGTH ys = LENGTH stack_remove_store_list
     ==> ?m1 RF.
           (misc_word_list reg3 (MAP (mem_val RF)
               (MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list))) STAR frame)
             (fun2set (m1,stack_state_mdomain s)) /\
           stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) =
             (NONE,stack_state_memory_fupd (K m1) (stack_state_regs_fupd (K RF) s)) /\
           FLOOKUP RF 0 = SOME (wl_Loc 1 0) /\
           FLOOKUP RF 1 = SOME v4 /\
           FLOOKUP RF 2 = SOME (wl_Word (word_add ptr2 half)) /\
           FLOOKUP RF 3 = SOME (wl_Word (word_ushr bitmap_ptr (backend_common_word_shift (:A)))) /\
           FLOOKUP RF 4 = SOME v1 /\
           FLOOKUP RF 5 = SOME (wl_Word half) /\
           FLOOKUP RF 6 = SOME v2 /\
           FLOOKUP RF 7 = SOME v3 /\
           FLOOKUP RF k = SOME (wl_Word (word_sub ptr4 bytes_in_word)) /\
           FLOOKUP RF (k + 1) = SOME (wl_Word (word_add reg3 (word_mul bytes_in_word
                                        (word (LENGTH stack_remove_store_list))))) /\
           FLOOKUP RF (k + 2) = SOME (wl_Word ptr2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STACKPROPSAUX_K_FACTS_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_init_code_split] THEN
  (* segment A *)
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `ptr2:A word`; `ptr4:A word`]
    STACKPROPSAUX_init_segA) THEN
  STACKPROPSAUX_SEG_TAC THEN STACKPROPSAUX_FOLD_TAC `mid:A word` THEN
  (* segment B *)
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPECL [st; `mid:A word`;
                   `word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word):A word`;
                   `ptr3:A word`;
                   `word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word):A word`]
      STACKPROPSAUX_init_segB)) THEN
  STACKPROPSAUX_SEG_TAC THEN STACKPROPSAUX_FOLD_TAC `adj3:A word` THEN
  (* segment C *)
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPECL [st;
                   `word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word):A word`;
                   `adj3:A word`;
                   `word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word):A word`;
                   `if max_heap * val (bytes_in_word:A word) < dimword (:A)
                    then word_mul (word max_heap) bytes_in_word
                    else word_sub (word 0) (word 1):A word`]
      STACKPROPSAUX_init_segC)) THEN
  STACKPROPSAUX_SEG_TAC THEN STACKPROPSAUX_FOLD_TAC `mhw:A word` THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) x) x = a`;
              WORD_RULE `word_add (word_sub (a:A word) x) x = a`] THEN
  (* segment D *)
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPECL [st; `mhw:A word`; `word_sub adj3 ptr2:A word`; `ptr2:A word`;
                   `adj3:A word`] STACKPROPSAUX_init_segD)) THEN
  STACKPROPSAUX_SEG_TAC THEN STACKPROPSAUX_FOLD_TAC `q:A word` THEN
  (* segment E *)
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPECL [st; `k:num`; `ptr2:A word`; `q:A word`; `ptr4:A word`]
      STACKPROPSAUX_init_segE)) THEN
  STACKPROPSAUX_SEG_TAC THEN STACKPROPSAUX_FOLD_TAC `reg3:A word` THEN
  STACKPROPSAUX_FOLD_TAC `half:A word` THEN
  (* segment F *)
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPECL [st; `k:num`; `ptr2:A word`; `bitmap_ptr:A word`;
                   `v1:(A)word_loc`; `v2:(A)word_loc`; `v3:(A)word_loc`; `v4:(A)word_loc`]
      STACKPROPSAUX_init_segF)) THEN
  STACKPROPSAUX_SEG_TAC THEN
  (* init_memory and LocValue *)
  REWRITE_TAC[stack_list_Seq_def] THEN
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPECL [st; `k:num`; `ptr4:A word`; `reg3:A word`;
                   `frame:(A word#(A)word_loc->bool)->bool`; `ys:((A)word_loc)list`;
                   `MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list):(A word+num)list`]
      STACKPROPSAUX_init_memory_thm)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[STACKPROPSAUX_SR_ACC; FLOOKUP_UPDATE; ARITH_EQ; LENGTH_MAP; LENGTH_REVERSE;
                FDOM_FUPDATE; IN_INSERT] THEN
    ASM_REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    X_GEN_TAC `nm:store_name` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(MP_TAC o MATCH_MP STACKPROPSAUX_store_init_INR o SYM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(A)word_loc`
    (X_CHOOSE_THEN `m1:A word->(A)word_loc` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_ev_seq_none th]) THEN
  W(fun (asl,w) -> let st = STACKPROPSAUX_cur_state w in
    MP_TAC(ISPEC st STACKPROPSAUX_init_LocValue)) THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN
  W(fun (asl,w) ->
    let tm = find_term (fun t -> is_comb t && is_comb (rator t) &&
               (try fst(dest_const(rator(rator t))) = "stack_state_regs_fupd" with Failure _ -> false) &&
               (try fst(dest_const(fst(strip_comb(rand t)))) = "stack_state_memory_fupd" &&
                    rand(rand(rator(rand t))) = `m1:A word->(A)word_loc`
                with Failure _ -> false)) w in
    MAP_EVERY EXISTS_TAC [`m1:A word->(A)word_loc`; rand(rand(rator tm))]) THEN
  REWRITE_TAC[FLOOKUP_UPDATE; FUPDATE_LIST_THM; ARITH_EQ; LENGTH_MAP; LENGTH_REVERSE] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `frame:(A word#(A)word_loc->bool)->bool`)) (concl th) &&
                                          can (find_term ((=) `m1:A word->(A)word_loc`)) (concl th))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC STACKPROPSAUX_mem_val_store_init THEN
  REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;

(* init_code_thm (HOL4 line 3225): the arithmetic of the init code *)

let STACKPROPSAUX_byte_aligned_val = prove
 (`!w:A word. good_dimindex (:A)
     ==> (byte_aligned w <=> val w MOD (dimindex (:A) DIV 8) = 0)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; byte_aligned_def; aligned_w2n] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_init_env = prove
 (`good_dimindex (:A)
   ==> val (bytes_in_word:A word) = dimindex (:A) DIV 8 /\
       2 EXP backend_common_word_shift (:A) = dimindex (:A) DIV 8 /\
       2 EXP (1 + backend_common_word_shift (:A)) = 2 * (dimindex (:A) DIV 8) /\
       2 EXP (backend_common_word_shift (:A) + 1) = 2 * (dimindex (:A) DIV 8) /\
       dimword (:A) = 2 EXP dimindex (:A) /\
       ((dimindex (:A) = 32 /\ dimindex (:A) DIV 8 = 4 /\ 2 EXP dimindex (:A) = 4294967296) \/
        (dimindex (:A) = 64 /\ dimindex (:A) DIV 8 = 8 /\
         2 EXP dimindex (:A) = 18446744073709551616))`,
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def; VAL_WORD; dimword_def;
              backend_common_word_shift_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_val_add_lt = prove
 (`!x y:A word. val x + val y < 2 EXP dimindex (:A) ==> val (word_add x y) = val x + val y`,
  SIMP_TAC[VAL_WORD_ADD; MOD_LT]);;

let STACKPROPSAUX_val_sub_le = prove
 (`!x y:A word. val y <= val x ==> val (word_sub x y) = val x - val y`,
  SIMP_TAC[VAL_WORD_SUB_CASES]);;

let STACKPROPSAUX_val_shl_lt = prove
 (`!(x:A word) n. 2 EXP n * val x < 2 EXP dimindex (:A)
     ==> val (word_shl x n) = 2 EXP n * val x`,
  SIMP_TAC[VAL_WORD_SHL; MOD_LT]);;

let STACKPROPSAUX_val_mul_bw = prove
 (`!n. good_dimindex (:A) /\ n * (dimindex (:A) DIV 8) < 2 EXP dimindex (:A)
       ==> val (word_mul (word n) (bytes_in_word:A word)) = n * (dimindex (:A) DIV 8) /\
           val (word_mul (bytes_in_word:A word) (word n)) = n * (dimindex (:A) DIV 8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL; VAL_WORD] THEN
  SUBGOAL_THEN `(dimindex (:A) DIV 8 * n) = n * dimindex (:A) DIV 8` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_SYM]; ASM_SIMP_TAC[MOD_LT]]);;

let STACKPROPSAUX_DIVFACTS_TAC : tactic = fun (asl,w) ->
  let isdiv t = is_comb t && is_comb (rator t) &&
                (try fst(dest_const(rator(rator t))) = "DIV" with Failure _ -> false) &&
                is_numeral (rand t) in
  let tms = setify (List.concat (map (fun t -> find_terms isdiv t) (w :: map (concl o snd) asl))) in
  MAP_EVERY (fun t -> MP_TAC(SPECL [lhand t; rand t] DIVISION) THEN
                      CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC) tms (asl,w);;

let STACKPROPSAUX_val_shl_ushr_add = prove
 (`!(x:A word) (y:A word) m n.
     2 EXP n * (val x DIV 2 EXP m) + val y < 2 EXP dimindex (:A)
     ==> val (word_add (word_shl (word_ushr x m) n) y) = 2 EXP n * (val x DIV 2 EXP m) + val y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP n * (val (x:A word) DIV 2 EXP m) < 2 EXP dimindex (:A)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let STACKPROPSAUX_DIMCASES_TAC : tactic =
  USE_THEN "dimcases" (DISJ_CASES_THEN (fun th ->
     let ths = CONJUNCTS th in
     RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths THEN MAP_EVERY ASSUME_TAC ths)) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV;;

let STACKPROPSAUX_DIMCASES_GOAL_TAC : tactic =
  REWRITE_TAC[backend_common_word_shift_def] THEN
  USE_THEN "dimcases" (DISJ_CASES_THEN (fun th -> REWRITE_TAC (dimword_def :: CONJUNCTS th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let STACKPROPSAUX_DIVFACTS_GOAL_TAC : tactic = fun (asl,w) ->
  let isdiv t = is_comb t && is_comb (rator t) &&
                (try fst(dest_const(rator(rator t))) = "DIV" with Failure _ -> false) &&
                is_numeral (rand t) in
  let tms = setify (find_terms isdiv w) in
  MAP_EVERY (fun t -> MP_TAC(SPECL [lhand t; rand t] DIVISION) THEN
                      CONV_TAC NUM_REDUCE_CONV) tms (asl,w);;

let STACKPROPSAUX_DROP_DEF_TAC (v:term) : tactic =
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) && lhs(concl th) = v));;

let STACKPROPSAUX_init_vals = prove
 (`!(ptr2:A word) ptr3 ptr4 max_heap mid adj3 mhw q reg3 half.
     good_dimindex (:A) /\ max_stack_alloc <= max_heap /\
     word_ule ptr2 ptr4 /\
     word_ule (word_mul (word 1024) bytes_in_word) (word_sub ptr4 ptr2) /\
     byte_aligned ptr2 /\ byte_aligned ptr4 /\
     mid = word_add (word_shl (word_ushr (word_sub ptr4 ptr2)
                                 (1 + backend_common_word_shift (:A)))
                              (backend_common_word_shift (:A))) ptr2 /\
     adj3 = (if word_ule (word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word)) ptr3 /\
                word_ule ptr3 (word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word))
             then ptr3 else mid) /\
     mhw = (if max_heap * val (bytes_in_word:A word) < dimword (:A)
            then word_mul (word max_heap) bytes_in_word else word_sub (word 0) (word 1)) /\
     q = (if word_ult mhw (word_sub adj3 ptr2) then word_add ptr2 mhw else adj3) /\
     reg3 = word_add (word_shl (word_ushr (word_sub q ptr2)
                                  (backend_common_word_shift (:A) + 1))
                               (backend_common_word_shift (:A) + 1)) ptr2 /\
     half = word_ushr (word_sub reg3 ptr2) 1
     ==> ?Nw hh.
           val (word_sub ptr4 ptr2) = (dimindex (:A) DIV 8) * Nw /\
           val ptr2 + (dimindex (:A) DIV 8) * Nw < dimword (:A) /\
           val ptr2 MOD (dimindex (:A) DIV 8) = 0 /\
           1024 <= Nw /\ 2 * hh + 255 <= Nw /\ 127 <= hh /\
           val reg3 = val ptr2 + (dimindex (:A) DIV 8) * (2 * hh) /\
           val half = (dimindex (:A) DIV 8) * hh /\
           2 * hh <= max_heap /\
           (word_ule (word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word)) ptr3 /\
            word_ule ptr3 (word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word)) /\
            val (word_add (word_mul (word_neg (word 1)) ptr2) ptr3) <=
              max_heap * val (bytes_in_word:A word) /\
            val (bytes_in_word:A word) * max_heap < dimword (:A)
            ==> q = ptr3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (ptr2:A word) MOD (dimindex (:A) DIV 8) = 0 /\
                val (ptr4:A word) MOD (dimindex (:A) DIV 8) = 0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[STACKPROPSAUX_byte_aligned_val]; ALL_TAC] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(ISPEC t VAL_BOUND))
    [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ULE]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_init_env) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dimcases")))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[max_stack_alloc_def]) THEN
  REWRITE_TAC[max_stack_alloc_def] THEN
  (* basic values *)
  SUBGOAL_THEN `val (word_sub (ptr4:A word) ptr2) = val ptr4 - val ptr2` ASSUME_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_val_sub_le THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n * (dimindex (:A) DIV 8) < 2 EXP dimindex (:A)
                    ==> val (word_mul (word n) (bytes_in_word:A word)) = n * (dimindex (:A) DIV 8)`
    ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_val_mul_bw]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_mul (word 1024) (bytes_in_word:A word)) = 1024 * (dimindex (:A) DIV 8) /\
                val (word_mul (word 255) (bytes_in_word:A word)) = 255 * (dimindex (:A) DIV 8)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN STACKPROPSAUX_DIMCASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE
    [ASSUME `val (word_mul (word 1024) (bytes_in_word:A word)) = 1024 * (dimindex (:A) DIV 8)`;
     ASSUME `val (word_sub (ptr4:A word) ptr2) = val ptr4 - val ptr2`] o
    check (fun th -> is_binary "<=" (concl th) &&
                     can (find_term ((=) `word 1024:A word`)) (concl th))) THEN
  SUBGOAL_THEN `val (word_add (ptr2:A word) (word_mul (word 255) bytes_in_word)) =
                val ptr2 + 255 * (dimindex (:A) DIV 8) /\
                val (word_sub (ptr4:A word) (word_mul (word 255) bytes_in_word)) =
                val ptr4 - 255 * (dimindex (:A) DIV 8)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`ptr2:A word`; `word_mul (word 255) (bytes_in_word:A word)`]
        STACKPROPSAUX_val_add_lt);
      MP_TAC(ISPECL [`ptr4:A word`; `word_mul (word 255) (bytes_in_word:A word)`]
        STACKPROPSAUX_val_sub_le)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    STACKPROPSAUX_DIMCASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the middle *)
  SUBGOAL_THEN `val (mid:A word) = (dimindex (:A) DIV 8) *
                  ((val (ptr4:A word) - val (ptr2:A word)) DIV (2 * (dimindex (:A) DIV 8))) + val ptr2`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `mid:A word`)) THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) STACKPROPSAUX_val_shl_ushr_add (lhs w))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    STACKPROPSAUX_DIMCASES_TAC THEN STACKPROPSAUX_DIVFACTS_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STACKPROPSAUX_DROP_DEF_TAC `mid:A word` THEN
  (* adj3 *)
  SUBGOAL_THEN `val (ptr2:A word) + 255 * (dimindex (:A) DIV 8) <= val (adj3:A word) /\
                val adj3 <= val (ptr4:A word) - 255 * (dimindex (:A) DIV 8) /\
                (val ptr2 + 255 * (dimindex (:A) DIV 8) <= val (ptr3:A word) /\
                 val ptr3 <= val ptr4 - 255 * (dimindex (:A) DIV 8) ==> adj3 = ptr3)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `adj3:A word`)) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    STACKPROPSAUX_DIMCASES_TAC THEN STACKPROPSAUX_DIVFACTS_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STACKPROPSAUX_DROP_DEF_TAC `adj3:A word` THEN
  (* mhw *)
  SUBGOAL_THEN `255 * (dimindex (:A) DIV 8) <= val (mhw:A word) /\
                (max_heap * (dimindex (:A) DIV 8) < 2 EXP dimindex (:A)
                 ==> val mhw = max_heap * (dimindex (:A) DIV 8)) /\
                (~(max_heap * (dimindex (:A) DIV 8) < 2 EXP dimindex (:A))
                 ==> val mhw = 2 EXP dimindex (:A) - 1)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `mhw:A word`)) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[WORD_RULE `word_sub (word 0) (word 1):A word = word_neg (word 1)`;
                  VAL_WORD_NEG_1] THEN
      STACKPROPSAUX_DIMCASES_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  STACKPROPSAUX_DROP_DEF_TAC `mhw:A word` THEN
  (* q *)
  SUBGOAL_THEN `val (q:A word) = (if val (mhw:A word) < val (adj3:A word) - val (ptr2:A word)
                                  then val ptr2 + val mhw else val adj3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `q:A word`)) THEN
    REWRITE_TAC[WORD_ULT] THEN
    SUBGOAL_THEN `val (word_sub (adj3:A word) ptr2) = val adj3 - val ptr2` SUBST1_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_val_sub_le THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STACKPROPSAUX_val_add_lt THEN
    MP_TAC(ISPEC `adj3:A word` VAL_BOUND) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STACKPROPSAUX_DROP_DEF_TAC `q:A word` THEN
  (* reg3 and half *)
  SUBGOAL_THEN `val (reg3:A word) = (2 * (dimindex (:A) DIV 8)) *
                  ((val (q:A word) - val (ptr2:A word)) DIV (2 * (dimindex (:A) DIV 8))) + val ptr2`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `reg3:A word`)) THEN
    SUBGOAL_THEN `val (word_sub (q:A word) ptr2) = val q - val ptr2` ASSUME_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_val_sub_le THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) STACKPROPSAUX_val_shl_ushr_add (lhs w))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `q:A word` VAL_BOUND) THEN
    STACKPROPSAUX_DIMCASES_TAC THEN STACKPROPSAUX_DIVFACTS_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STACKPROPSAUX_DROP_DEF_TAC `reg3:A word` THEN
  SUBGOAL_THEN `val (half:A word) = (dimindex (:A) DIV 8) *
                  ((val (q:A word) - val (ptr2:A word)) DIV (2 * (dimindex (:A) DIV 8)))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `half:A word`)) THEN
    REWRITE_TAC[VAL_WORD_USHR; EXP_1] THEN
    SUBGOAL_THEN `val (word_sub (reg3:A word) ptr2) = val reg3 - val ptr2` SUBST1_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_val_sub_le THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_SUB; GSYM MULT_ASSOC] THEN MATCH_MP_TAC DIV_MULT THEN ARITH_TAC;
    ALL_TAC] THEN
  STACKPROPSAUX_DROP_DEF_TAC `half:A word` THEN
  (* the conditional conjunct *)
  SUBGOAL_THEN
   `word_ule (word_add ptr2 (word_mul (word 255) bytes_in_word)) (ptr3:A word) /\
    word_ule ptr3 (word_sub ptr4 (word_mul (word 255) bytes_in_word)) /\
    val (word_add (word_mul (word_neg (word 1)) ptr2) ptr3) <=
      max_heap * val (bytes_in_word:A word) /\
    val (bytes_in_word:A word) * max_heap < dimword (:A)
    ==> q = ptr3`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ULE; WORD_RULE `word_add (word_mul (word_neg (word 1)) (x:A word)) y =
                                     word_sub y x`] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "hm") (LABEL_TAC "hd")))) THEN
    SUBGOAL_THEN `val (word_sub (ptr3:A word) ptr2) = val ptr3 - val ptr2` ASSUME_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_val_sub_le THEN
      UNDISCH_TAC `val (ptr2:A word) + 255 * dimindex (:A) DIV 8 <= val (ptr3:A word)` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `max_heap * (dimindex (:A) DIV 8) < 2 EXP dimindex (:A)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN USE_THEN "hd" ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(adj3:A word) = ptr3` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl) o
        check (fun th -> can (find_term ((=) `adj3:A word`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `val (mhw:A word) = max_heap * dimindex (:A) DIV 8` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
        not (is_neg (lhand (concl th))) &&
        can (find_term ((=) `mhw:A word`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "hm" MP_TAC THEN
    REWRITE_TAC[ASSUME `val (word_sub (ptr3:A word) ptr2) = val ptr3 - val ptr2`] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* bounds on q, then forget its value *)
  SUBGOAL_THEN `val (ptr2:A word) + 255 * (dimindex (:A) DIV 8) <= val (q:A word) /\
                val q <= val (adj3:A word) /\ val q - val ptr2 <= val (mhw:A word)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
                                                lhs(concl th) = `val (q:A word)`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`val (ptr2:A word) + 255 * dimindex (:A) DIV 8 <= val (adj3:A word)`;
      `255 * dimindex (:A) DIV 8 <= val (mhw:A word)`] THEN
    COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
                                             lhs(concl th) = `val (q:A word)`)) THEN
  SUBGOAL_THEN `(val (ptr4:A word) - val (ptr2:A word)) MOD (dimindex (:A) DIV 8) = 0`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`val (ptr2:A word) MOD (dimindex (:A) DIV 8) = 0`;
                           `val (ptr4:A word) MOD (dimindex (:A) DIV 8) = 0`] THEN
    REWRITE_TAC[MOD_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST1_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
    EXISTS_TAC `b - a:num` THEN REWRITE_TAC[RIGHT_SUB_DISTRIB];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (ptr4:A word) - val (ptr2:A word) =
                (dimindex (:A) DIV 8) * ((val ptr4 - val ptr2) DIV (dimindex (:A) DIV 8))`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (ptr4:A word) - val (ptr2:A word)`; `dimindex (:A) DIV 8`] DIVISION) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN ANTS_TAC THENL
     [STACKPROPSAUX_DIMCASES_GOAL_TAC; DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th])] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`255 * (dimindex (:A) DIV 8)`; `val (q:A word) - val (ptr2:A word)`;
                `2 * (dimindex (:A) DIV 8)`] DIV_MONO) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `val (ptr2:A word) + 255 * dimindex (:A) DIV 8 <= val (q:A word)` THEN ARITH_TAC;
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(val (ptr4:A word) - val (ptr2:A word)) DIV (dimindex (:A) DIV 8)`;
    `(val (q:A word) - val (ptr2:A word)) DIV (2 * (dimindex (:A) DIV 8))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `val (ptr4:A word) - val (ptr2:A word) =
       dimindex (:A) DIV 8 * (val ptr4 - val ptr2) DIV (dimindex (:A) DIV 8)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`val (ptr2:A word) <= val (ptr4:A word)`;
                           `val (ptr4:A word) < 2 EXP dimindex (:A)`] THEN
    REWRITE_TAC[dimword_def] THEN ARITH_TAC;
    ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`1024 * dimindex (:A) DIV 8 <= val (ptr4:A word) - val (ptr2:A word)`;
      `val (ptr4:A word) - val (ptr2:A word) =
       dimindex (:A) DIV 8 * (val ptr4 - val ptr2) DIV (dimindex (:A) DIV 8)`] THEN
    STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
    MAP_EVERY UNDISCH_TAC
     [`val (q:A word) <= val (adj3:A word)`;
      `val (adj3:A word) <= val (ptr4:A word) - 255 * dimindex (:A) DIV 8`;
      `val (ptr4:A word) - val (ptr2:A word) =
       dimindex (:A) DIV 8 * (val ptr4 - val ptr2) DIV (dimindex (:A) DIV 8)`;
      `val (ptr2:A word) + 255 * dimindex (:A) DIV 8 <= val (q:A word)`] THEN
    STACKPROPSAUX_DIMCASES_GOAL_TAC THEN STACKPROPSAUX_DIVFACTS_GOAL_TAC THEN ARITH_TAC;
    UNDISCH_TAC `(255 * dimindex (:A) DIV 8) DIV (2 * dimindex (:A) DIV 8) <=
                 (val (q:A word) - val (ptr2:A word)) DIV (2 * dimindex (:A) DIV 8)` THEN
    STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
    UNDISCH_TAC `val (reg3:A word) =
      (2 * dimindex (:A) DIV 8) * (val (q:A word) - val (ptr2:A word)) DIV
      (2 * dimindex (:A) DIV 8) + val ptr2` THEN ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_CASES_TAC `max_heap * dimindex (:A) DIV 8 < 2 EXP dimindex (:A)` THENL
     [UNDISCH_TAC `max_heap * dimindex (:A) DIV 8 < 2 EXP dimindex (:A)
                   ==> val (mhw:A word) = max_heap * dimindex (:A) DIV 8` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`val (q:A word) - val (ptr2:A word) <= val (mhw:A word)`;
        `val (mhw:A word) = max_heap * dimindex (:A) DIV 8`];
      UNDISCH_TAC `~(max_heap * dimindex (:A) DIV 8 < 2 EXP dimindex (:A))
                   ==> val (mhw:A word) = 2 EXP dimindex (:A) - 1` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`~(max_heap * dimindex (:A) DIV 8 < 2 EXP dimindex (:A))`;
        `val (q:A word) - val (ptr2:A word) <= val (mhw:A word)`;
        `val (mhw:A word) = 2 EXP dimindex (:A) - 1`]] THEN
    STACKPROPSAUX_DIMCASES_GOAL_TAC THEN STACKPROPSAUX_DIVFACTS_GOAL_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* init_code_thm (HOL4 line 3225): memory and store helpers *)

let STACKPROPSAUX_FAPPLY_OF_FLOOKUP = prove
 (`!(f:(A,B)fmap) k v. FLOOKUP f k = SOME v ==> FAPPLY f k = v`,
  SIMP_TAC[FAPPLY_FLOOKUP; THE_DEF]);;

let STACKPROPSAUX_LENGTH_store_list = prove
 (`LENGTH stack_remove_store_list = 48`,
  REWRITE_TAC[stack_remove_store_list_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_word_list_split4 = prove
 (`!(ys:B list) (a:A word) n1 n2.
     n1 + n2 < LENGTH ys
     ==> ?l1 l2 l3 x.
           LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ LENGTH l3 = LENGTH ys - n1 - n2 - 1 /\
           misc_word_list a ys =
           misc_word_list a l1 STAR
           misc_word_list (word_add a (word_mul bytes_in_word (word n1))) l2 STAR
           misc_word_list (word_add a (word_mul bytes_in_word (word (n1 + n2)))) l3 STAR
           set_sep_one (word_add a (word_mul bytes_in_word (word (LENGTH ys - 1))),x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ys:B list`; `n1:num`] stack_removeProof_LESS_LENGTH_IMP_APPEND) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:B list` (X_CHOOSE_THEN `r1:B list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `ys:B list`)) THEN
  MP_TAC(ISPECL [`r1:B list`; `n2:num`] stack_removeProof_LESS_LENGTH_IMP_APPEND) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n1 + n2 < LENGTH (APPEND (l1:B list) r1)` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:B list` (X_CHOOSE_THEN `r2:B list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `r1:B list`)) THEN
  MP_TAC(ISPECL [`r2:B list`; `LENGTH (r2:B list) - 1`]
    stack_removeProof_LESS_LENGTH_IMP_APPEND) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n1 + n2 < LENGTH (APPEND (l1:B list) (APPEND l2 r2))` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:B list` (X_CHOOSE_THEN `r3:B list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `r2:B list`)) THEN
  SUBGOAL_THEN `LENGTH (r3:B list) = 1` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> lhs(concl th) = `LENGTH (l3:B list)`)) THEN
    UNDISCH_TAC `n1 + n2 < LENGTH (APPEND (l1:B list) (APPEND l2 (APPEND l3 r3)))` THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> lhs(concl th) = `LENGTH (l3:B list)`)) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x:B` (X_CHOOSE_THEN `r4:B list` SUBST_ALL_TAC))
    (ISPEC `r3:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 1)`; ARITH_RULE `SUC n = 1 <=> n = 0`;
              LENGTH_EQ_NIL] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`l1:B list`; `l2:B list`; `l3:B list`; `x:B`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[stack_removeProof_word_list_APPEND; misc_word_list_def; SEP_CLAUSES;
              STAR_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(n1 + n2 + l + SUC 0) - 1 = n1 + n2 + l`] THEN
  REWRITE_TAC[WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (a:A word) (word_mul b x)) (word_mul b y) =
                         word_add a (word_mul b (word_add x y))`]);;

let STACKPROPSAUX_FLOOKUP_FUPDATE_LIST_MAP = prove
 (`!(g:A->B) l (f:(A,B)fmap) x.
     FLOOKUP (f |++ MAP (\n. (n,g n)) l) x = if MEM x l then SOME (g x) else FLOOKUP f x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; MEM; FUPDATE_LIST_THM] THEN
  REWRITE_TAC[FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:A = h` THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let STACKPROPSAUX_store_map = prove
 (CASE_TERM
  `!gen_gc' k (RF:(num,(A)word_loc)fmap).
     (\n. match store_init gen_gc' k n with
            INL w -> (n,wl_Word w)
          | INR i -> (n,FAPPLY RF i)) =
     (\n. (n,mem_val RF (store_init gen_gc' k n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:store_name` THEN
  MP_TAC(ISPEC `store_init gen_gc' k n:A word+num` (cases "sum")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[mem_val_def] THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_one_one_F = prove
 (`!(a:A) (x:B) y p m d.
     (set_sep_one (a,x) STAR set_sep_one (a,y) STAR p) (fun2set (m,d)) ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM STAR_ASSOC; one_STAR; IN_DELETE; IN_fun2set; PAIR_EQ] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_word_list_no_wrap = prove
 (`!(a:A word) (ls:B list) p m d.
     good_dimindex (:A) /\ (misc_word_list a ls STAR p) (fun2set (m,d))
     ==> LENGTH ls <= dimword (:A) DIV (dimindex (:A) DIV 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:A word`; `ls:B list`] word_list_wrap) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fun2set (m:A word->B,d)`))
                                         (concl th))) THEN
  ASM_REWRITE_TAC[misc_word_list_def] THEN
  REWRITE_TAC[GSYM STAR_ASSOC] THEN DISCH_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:A word`,`:A`] STACKPROPSAUX_one_one_F) THEN
  MAP_EVERY EXISTS_TAC [`a:A word`; `x:B`; `y:B`] THEN
  MAP_EVERY EXISTS_TAC
   [`misc_word_list (word_add (a:A word) bytes_in_word) (xs:B list) STAR
     misc_word_list (word_add a bytes_in_word) ys STAR (p:(A word#B->bool)->bool)`;
    `m:A word->B`; `d:A word->bool`] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  CONV_TAC(AC STACKPROPSAUX_STAR_AC));;

let STACKPROPSAUX_DIV_MULT_R = prove
 (`!m n. ~(m = 0) ==> (n * m) DIV m = n`,
  MESON_TAC[DIV_MULT; MULT_SYM]);;

let STACKPROPSAUX_init_limits = prove
 (`!(ptr2:A word) ptr3 ptr4 max_heap mid adj3 mhw q reg3 Nw hh.
     good_dimindex (:A) /\
     mid = word_add (word_shl (word_ushr (word_sub ptr4 ptr2)
                                 (1 + backend_common_word_shift (:A)))
                              (backend_common_word_shift (:A))) ptr2 /\
     adj3 = (if word_ule (word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word)) ptr3 /\
                word_ule ptr3 (word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word))
             then ptr3 else mid) /\
     mhw = (if max_heap * val (bytes_in_word:A word) < dimword (:A)
            then word_mul (word max_heap) bytes_in_word else word_sub (word 0) (word 1)) /\
     q = (if word_ult mhw (word_sub adj3 ptr2) then word_add ptr2 mhw else adj3) /\
     reg3 = word_add (word_shl (word_ushr (word_sub q ptr2)
                                  (backend_common_word_shift (:A) + 1))
                               (backend_common_word_shift (:A) + 1)) ptr2 /\
     val ptr4 = val ptr2 + (dimindex (:A) DIV 8) * Nw /\
     val ptr2 MOD (dimindex (:A) DIV 8) = 0 /\
     val reg3 = val ptr2 + dimindex (:A) DIV 8 * 2 * hh /\
     2 * hh + 255 <= Nw
     ==> get_stack_heap_limit max_heap (ptr2,ptr3,ptr4) = (Nw - 2 * hh - 48,hh)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[get_stack_heap_limit_def; get_stack_heap_limit'_def; get_stack_heap_limit''_def;
              LET_DEF; LET_END_DEF; WORD_VAL] THEN
  MAP_EVERY (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
   [WORD_RULE `word_add (word_mul (word_neg (word 1)) (x:A word)) y = word_sub y x`;
    WORD_RULE `word_mul (bytes_in_word:A word) (word n) = word_mul (word n) bytes_in_word`;
    WORD_RULE `word_neg (word 1):A word = word_sub (word 0) (word 1)`;
    ARITH_RULE `backend_common_word_shift (:A) + 1 = 1 + backend_common_word_shift (:A)`] THEN
  SUBGOAL_THEN `word_add (ptr2:A word) (word_shl (word_ushr (word_sub ptr4 ptr2)
                  (1 + backend_common_word_shift (:A))) (backend_common_word_shift (:A))) = mid`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MAP_EVERY (fun v -> FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
                                                             lhs(concl th) = v)))
    [`adj3:A word`; `mhw:A word`] THEN
  SUBST1_TAC(WORD_RULE `word_add (mhw:A word) ptr2 = word_add ptr2 mhw`) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) && lhs(concl th) = `q:A word`)) THEN
  SUBGOAL_THEN `word_add (ptr2:A word) (word_shl (word_ushr (word_sub q ptr2)
                  (1 + backend_common_word_shift (:A))) (1 + backend_common_word_shift (:A))) = reg3`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                          lhs(concl th) = `val (ptr2:A word) MOD (dimindex (:A) DIV 8)`)) THEN
  REWRITE_TAC[MOD_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_LENGTH_store_list; PAIR_EQ] THEN
  REWRITE_TAC[ARITH_RULE `a * d + d * n = d * (a + n:num)`; ARITH_RULE `a * d = d * a:num`;
              ARITH_RULE `d * a + d * 2 * h = d * (a + 2 * h:num)`] THEN
  SUBGOAL_THEN `~(dimindex (:A) DIV 8 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_DIV_MULT_R] THEN
  REWRITE_TAC[ARITH_RULE `(a + h * 2) - a = h * 2`] THEN
  SIMP_TAC[STACKPROPSAUX_DIV_MULT_R; ARITH_EQ] THEN ARITH_TAC);;

let STACKPROPSAUX_word_list_read' = prove
 (`!(xs:B list) (a:A word) p m d.
     (p STAR misc_word_list a xs) (fun2set (m,d))
     ==> !i. i < LENGTH xs
             ==> m (word_add a (word_mul bytes_in_word (word i))) = EL i xs /\
                 word_add a (word_mul bytes_in_word (word i)) IN d`,
  MESON_TAC[STACKPROPSAUX_word_list_read; STAR_COMM]);;

let STACKPROPSAUX_WB = "misc_word_list (bitmap_ptr:A word) (MAP wl_Word (bitmaps:(A word)list))";;
let STACKPROPSAUX_WD = "word_list_exists (word_add (bitmap_ptr:A word) (word_mul bytes_in_word (word (LENGTH (bitmaps:(A word)list))))) data_sp";;
let STACKPROPSAUX_WH = "misc_word_list (ptr2:A word) (heap:((A)word_loc)list)";;
let STACKPROPSAUX_WS = "misc_word_list (reg3:A word) (bitst:((A)word_loc)list)";;
let STACKPROPSAUX_WR = "misc_word_list (word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48)))) (rest1:((A)word_loc)list)";;

let STACKPROPSAUX_INTRO_TAC (v:term) (e:term) : tactic =
  X_CHOOSE_TAC v (ISPEC e EXISTS_REFL);;

let STACKPROPSAUX_store_lookup = prove
 (`!(g:store_name->B) x.
     MEM x (CONS CurrHeap stack_remove_store_list)
     ==> FLOOKUP (FEMPTY |++ MAP (\n. (n,g n)) (CONS CurrHeap stack_remove_store_list)) x =
         SOME (g x)`,
  SIMP_TAC[STACKPROPSAUX_FLOOKUP_FUPDATE_LIST_MAP]);;

let STACKPROPSAUX_word_store_map = prove
 (CASE_TERM
  `!(g:store_name->(A)word_loc) (base:A word).
     word_store base (FEMPTY |++ MAP (\n. (n,g n)) (CONS CurrHeap stack_remove_store_list)) =
     word_list_rev base (MAP g stack_remove_store_list)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_store_def] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`g:store_name->(A)word_loc`; `x:store_name`]
                                 STACKPROPSAUX_store_lookup)) THEN
  ASM_REWRITE_TAC[MEM] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_init_store_lookups = prove
 (`!gen_gc' k (RF:(num,(A)word_loc)fmap).
     let st = FEMPTY |++ MAP (\n. (n,mem_val RF (store_init gen_gc' k n)))
                             (CONS CurrHeap stack_remove_store_list) in
     FLOOKUP st CurrHeap = SOME (FAPPLY RF (k + 2)) /\
     FLOOKUP st NextFree = SOME (FAPPLY RF (k + 2)) /\
     FLOOKUP st GlobReal = SOME (FAPPLY RF (k + 2)) /\
     FLOOKUP st TriggerGC = SOME (FAPPLY RF (if gen_gc' then k + 2 else 2)) /\
     FLOOKUP st EndOfHeap = SOME (FAPPLY RF 2) /\
     FLOOKUP st OtherHeap = SOME (FAPPLY RF 2) /\
     FLOOKUP st HeapLength = SOME (FAPPLY RF 5) /\
     FLOOKUP st BitmapBase = SOME (FAPPLY RF 3) /\
     FLOOKUP st BitmapBuffer = SOME (FAPPLY RF 4) /\
     FLOOKUP st BitmapBufferEnd = SOME (FAPPLY RF 6) /\
     FLOOKUP st CodeBuffer = SOME (FAPPLY RF 7) /\
     FLOOKUP st CodeBufferEnd = SOME (FAPPLY RF 1) /\
     FLOOKUP st ProgStart = SOME (wl_Word (word 0)) /\
     FLOOKUP st AllocSize = SOME (wl_Word (word 0)) /\
     FLOOKUP st Globals = SOME (wl_Word (word 0)) /\
     FLOOKUP st Handler = SOME (wl_Word (word 0)) /\
     FLOOKUP st GenStart = SOME (wl_Word (word 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SIMP_TAC[STACKPROPSAUX_store_lookup; MEM; stack_remove_store_list_def;
           distinctness "store_name"] THEN
  REWRITE_TAC[store_init_def; UPDATE_LIST_THM; APPLY_UPDATE_THM; K_THM; FST; SND;
              distinctness "store_name"] THEN
  REWRITE_TAC[mem_val_def] THEN COND_CASES_TAC THEN REWRITE_TAC[mem_val_def]);;

let STACKPROPSAUX_bitmaps_bound = prove
 (`!(bp:A word) (bms:(A word)list) data_sp p m dm.
     good_dimindex (:A) /\
     (misc_word_list bp (MAP wl_Word bms) STAR
      word_list_exists (word_add bp (word_mul bytes_in_word (word (LENGTH bms)))) data_sp STAR
      p) (fun2set (m,dm))
     ==> LENGTH bms + data_sp + 1 < dimword (:A)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPECL [`word_add (bp:A word) (word_mul bytes_in_word (word (LENGTH (bms:(A word)list))))`;
                     `data_sp:num`]
    (INST_TYPE [`:(A)word_loc`,`:B`] word_list_exists_def)) THEN
  REWRITE_TAC[SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xs:((A)word_loc)list` MP_TAC)) THEN
  DISCH_THEN(MP_TAC o EQ_MP
    ((prove(parse_term ("(misc_word_list (bp:A word) (MAP wl_Word (bms:(A word)list)) STAR " ^
       "(misc_word_list (word_add bp (word_mul bytes_in_word (word (LENGTH bms)))) xs STAR " ^
       "cond (LENGTH (xs:((A)word_loc)list) = data_sp)) STAR p) (fun2set (m,dm)) <=> " ^
       "((misc_word_list bp (MAP wl_Word bms) STAR " ^
       "misc_word_list (word_add bp (word_mul bytes_in_word (word (LENGTH bms)))) xs STAR p) STAR " ^
       "cond (LENGTH xs = data_sp)) (fun2set (m,dm))"),
      AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC))))) THEN
  REWRITE_TAC[cond_STAR] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bp:A word`; `APPEND (MAP wl_Word (bms:(A word)list)) (xs:((A)word_loc)list)`;
                 `p:(A word#(A)word_loc->bool)->bool`; `m:A word->(A)word_loc`;
                 `dm:A word->bool`] STACKPROPSAUX_word_list_no_wrap) THEN
  ASM_REWRITE_TAC[stack_removeProof_word_list_APPEND; LENGTH_MAP; LENGTH_APPEND] THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let STACKPROPSAUX_stack_last_addr = prove
 (`!(ptr2:A word) hh Nw. 2 * hh + 255 <= Nw ==>
     word_add (word_add ptr2 (word_mul bytes_in_word (word (2 * hh + 48))))
       (word_mul bytes_in_word (word (Nw - 2 * hh - 49))) =
     word_add ptr2 (word_mul bytes_in_word (word (Nw - 1)))`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `Nw - 1 = (2 * hh + 48) + (Nw - 2 * hh - 49)` SUBST1_TAC THENL
    [UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC;
     REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]));;

(* HOL4 line 3225 *)
let init_code_thm = prove
 (CASE_TERM
  `!k bitmaps data_sp (s:(A,C,FFI)stack_state) jump off code coracle gen_gc' max_heap.
     init_code_pre k bitmaps data_sp s /\
     stack_removeProof_code_rel jump off k code (stack_state_code s) /\
     stack_state_compile_oracle s =
       (I ## MAP (stack_remove_prog_comp jump off k) ## I) o coracle /\
     (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k /\ stack_num_stubs <= i + 1) /\
     lookup stack_err_lab (stack_state_code s) = SOME (halt_inst (word 2)) /\
     max_stack_alloc <= max_heap
     ==> (match stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) with
            (SOME res,t) -> F
          | (NONE,t) ->
             (?w2 w3 (w4:A word).
                FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word w2) /\ byte_aligned w2 /\
                FLOOKUP (stack_state_regs t) (k + 2) = SOME (wl_Word w2) /\
                FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word w4) /\ byte_aligned w4 /\
                word_ult w2 w4 /\
                FLOOKUP (stack_state_regs t) k = SOME (wl_Word (word_sub w4 bytes_in_word)) /\
                (word_ule (word_add w2 (word_mul (word max_stack_alloc) bytes_in_word)) w3 /\
                 word_ule w3 (word_sub w4 (word_mul (word max_stack_alloc) bytes_in_word)) /\
                 val (word_add (word_mul (word_neg (word 1)) w2) w3) <=
                   max_heap * val (bytes_in_word:A word) /\
                 val (bytes_in_word:A word) * max_heap < dimword (:A)
                 ==> FLOOKUP (stack_state_regs t) (k + 1) =
                       SOME (wl_Word
                         (word_add
                            (word_add
                               (word_shl
                                  (word_ushr (word_add w3 (word_mul (word_neg (word 1)) w2))
                                             (backend_common_word_shift (:A) + 1))
                                  (backend_common_word_shift (:A) + 1))
                               w2)
                            (word_mul (bytes_in_word:A word)
                                      (word (LENGTH stack_remove_store_list)))))) /\
                FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word w3)) /\
             stack_removeProof_state_rel jump off k
               (init_reduce gen_gc' jump off k code bitmaps data_sp coracle t) t /\
             stack_state_ffi t = stack_state_ffi s /\
             init_prop gen_gc' max_heap data_sp
               (get_stack_heap_limit max_heap (read_pointers s))
               (init_reduce gen_gc' jump off k code bitmaps data_sp coracle t) /\
             stack_state_mdomain s = stack_state_mdomain t /\
             stack_state_sh_mdomain s = stack_state_sh_mdomain t /\
             (let t0 = init_reduce gen_gc' jump off k code bitmaps data_sp coracle t in
                fun2set (stack_state_memory s,stack_state_mdomain t0) =
                fun2set (stack_state_memory t,stack_state_mdomain t0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[init_code_pre_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ptr2:A word` (X_CHOOSE_THEN `ptr3:A word` (X_CHOOSE_THEN `ptr4:A word`
      (X_CHOOSE_THEN `bitmap_ptr:A word` STRIP_ASSUME_TAC)))) STRIP_ASSUME_TAC) THEN
  (* abbreviations *)
  STACKPROPSAUX_INTRO_TAC `mid:A word`
    `word_add (word_shl (word_ushr (word_sub ptr4 ptr2) (1 + backend_common_word_shift (:A)))
                        (backend_common_word_shift (:A))) (ptr2:A word)` THEN
  STACKPROPSAUX_INTRO_TAC `adj3:A word`
    `if word_ule (word_add ptr2 (word_mul (word max_stack_alloc) bytes_in_word)) ptr3 /\
        word_ule ptr3 (word_sub ptr4 (word_mul (word max_stack_alloc) bytes_in_word))
     then ptr3 else (mid:A word)` THEN
  STACKPROPSAUX_INTRO_TAC `mhw:A word`
    `if max_heap * val (bytes_in_word:A word) < dimword (:A)
     then word_mul (word max_heap) bytes_in_word else word_sub (word 0) (word 1):A word` THEN
  STACKPROPSAUX_INTRO_TAC `q:A word`
    `if word_ult (mhw:A word) (word_sub adj3 ptr2) then word_add ptr2 mhw else adj3` THEN
  STACKPROPSAUX_INTRO_TAC `reg3:A word`
    `word_add (word_shl (word_ushr (word_sub (q:A word) ptr2)
                                   (backend_common_word_shift (:A) + 1))
                        (backend_common_word_shift (:A) + 1)) ptr2` THEN
  STACKPROPSAUX_INTRO_TAC `half:A word` `word_ushr (word_sub (reg3:A word) ptr2) 1` THEN
  MP_TAC(ISPECL [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`; `max_heap:num`; `mid:A word`;
                 `adj3:A word`; `mhw:A word`; `q:A word`; `reg3:A word`; `half:A word`]
    STACKPROPSAUX_init_vals) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nw:num` (X_CHOOSE_THEN `hh:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_init_env) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dimcases")))))) THEN
  SUBGOAL_THEN `~(dimindex (:A) DIV 8 = 0)` ASSUME_TAC THENL
   [STACKPROPSAUX_DIMCASES_GOAL_TAC; ALL_TAC] THEN
  (* the memory: the region at ptr2 *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
    `word_list_exists (ptr2:A word) (val (word_sub ptr4 ptr2) DIV val (bytes_in_word:A word))
       :(A word#(A)word_loc->bool)->bool`)) (concl th))) THEN
  REWRITE_TAC[ASSUME `val (word_sub (ptr4:A word) ptr2) = dimindex (:A) DIV 8 * Nw`;
              ASSUME `val (bytes_in_word:A word) = dimindex (:A) DIV 8`] THEN
  REWRITE_TAC[MATCH_MP DIV_MULT (ASSUME `~(dimindex (:A) DIV 8 = 0)`)] THEN
  SUBST1_TAC(ISPECL [`ptr2:A word`; `Nw:num`]
    (INST_TYPE [`:(A)word_loc`,`:B`] word_list_exists_def)) THEN
  REWRITE_TAC[SEP_CLAUSES; SEP_EXISTS_THM; STAR_ASSOC; cond_STAR] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
  (* addresses *)
  SUBGOAL_THEN `val (ptr4:A word) = val (ptr2:A word) + dimindex (:A) DIV 8 * Nw`
    ASSUME_TAC THENL
   [UNDISCH_TAC `val (word_sub (ptr4:A word) ptr2) = dimindex (:A) DIV 8 * Nw` THEN
    UNDISCH_TAC `word_ule (ptr2:A word) ptr4` THEN
    REWRITE_TAC[WORD_ULE; VAL_WORD_SUB_CASES] THEN SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`; `max_heap:num`; `mid:A word`;
                 `adj3:A word`; `mhw:A word`; `q:A word`; `reg3:A word`; `Nw:num`; `hh:num`]
    STACKPROPSAUX_init_limits) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `read_pointers (s:(A,C,FFI)stack_state) = (ptr2,ptr3,ptr4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[read_pointers_def; THE_DEF; theWord_def]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= Nw ==> val (word_add (ptr2:A word) (word_mul bytes_in_word (word n))) =
                                val ptr2 + n * dimindex (:A) DIV 8` (LABEL_TAC "vaddr") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `n * dimindex (:A) DIV 8 <= Nw * dimindex (:A) DIV 8` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ptr2:A word`; `word_mul (bytes_in_word:A word) (word n)`]
      STACKPROPSAUX_val_add_lt) THEN
    MP_TAC(SPEC `n:num` STACKPROPSAUX_val_mul_bw) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `ptr4:A word` VAL_BOUND) THEN
    UNDISCH_TAC `val (ptr4:A word) = val (ptr2:A word) + dimindex (:A) DIV 8 * Nw` THEN
    REWRITE_TAC[ARITH_RULE `d * Nw = Nw * d:num`] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `reg3 = word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN USE_THEN "vaddr" (MP_TAC o SPEC `2 * hh`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_sub ptr4 bytes_in_word =
                word_add (ptr2:A word) (word_mul bytes_in_word (word (Nw - 1)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN USE_THEN "vaddr" (MP_TAC o SPEC `Nw - 1`) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `val (word_sub (ptr4:A word) bytes_in_word) = val ptr4 - val (bytes_in_word:A word)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_val_sub_le THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `1024 <= Nw` THEN STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1024 <= Nw` THEN
    STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the domain contains the words read by the init code *)
  FIRST_ASSUM(LABEL_TAC "rd" o MATCH_MP STACKPROPSAUX_word_list_read' o
    check (fun th -> can (find_term ((=) `misc_word_list (ptr2:A word) (ys:((A)word_loc)list)`))
                       (concl th))) THEN
  SUBGOAL_THEN
   `ptr2 IN stack_state_mdomain (s:(A,C,FFI)stack_state) /\
    word_add ptr2 bytes_in_word IN stack_state_mdomain s /\
    word_add ptr2 (word_mul (word 2) bytes_in_word) IN stack_state_mdomain s /\
    word_add ptr2 (word_mul (word 3) bytes_in_word) IN stack_state_mdomain s /\
    word_add ptr2 (word_mul (word 4) bytes_in_word) IN stack_state_mdomain s /\
    word_sub ptr4 bytes_in_word IN stack_state_mdomain s`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun (i,rw) ->
      USE_THEN "rd" (MP_TAC o SPEC i) THEN REWRITE_TAC rw THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `1024 <= Nw` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC])
     [`0`,[WORD_MUL_0; WORD_ADD_0];
      `1`,[WORD_RULE `word_mul (x:A word) (word 1) = x`];
      `2`,[WORD_RULE `word_mul (x:A word) (word 2) = word_mul (word 2) x`];
      `3`,[WORD_RULE `word_mul (x:A word) (word 3) = word_mul (word 3) x`];
      `4`,[WORD_RULE `word_mul (x:A word) (word 4) = word_mul (word 4) x`];
      `Nw - 1`,[]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* split the region: heap, store, stack, last word *)
  MP_TAC(ISPECL [`ys:((A)word_loc)list`; `ptr2:A word`; `2 * hh`; `48`]
    STACKPROPSAUX_word_list_split4) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap:((A)word_loc)list` (X_CHOOSE_THEN `bitst:((A)word_loc)list`
    (X_CHOOSE_THEN `rest1:((A)word_loc)list` (X_CHOOSE_THEN `lastw:(A)word_loc`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `misc_word_list (ptr2:A word) (ys:((A)word_loc)list)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
    `misc_word_list (ptr2:A word) (heap:((A)word_loc)list)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(ASSUME `reg3 = word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh)))`);
              GSYM(ASSUME `word_sub ptr4 bytes_in_word =
                           word_add (ptr2:A word) (word_mul bytes_in_word (word (Nw - 1)))`)] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN (parse_term ("(" ^ STACKPROPSAUX_WS ^ " STAR (" ^ STACKPROPSAUX_WB ^ " STAR " ^
      STACKPROPSAUX_WD ^ " STAR " ^ STACKPROPSAUX_WH ^ " STAR " ^ STACKPROPSAUX_WR ^
      " STAR set_sep_one (word_sub ptr4 bytes_in_word,wl_Word (word 0)))) " ^
      "(fun2set ((word_sub ptr4 bytes_in_word =+ wl_Word (word 0)) " ^
      "(stack_state_memory (s:(A,C,FFI)stack_state)),stack_state_mdomain s))"))
    ASSUME_TAC THENL
   [SUBGOAL_THEN (parse_term ("(set_sep_one (word_sub ptr4 bytes_in_word,lastw:(A)word_loc) STAR (" ^
       STACKPROPSAUX_WB ^ " STAR " ^ STACKPROPSAUX_WD ^ " STAR " ^ STACKPROPSAUX_WH ^ " STAR " ^
       STACKPROPSAUX_WS ^ " STAR " ^ STACKPROPSAUX_WR ^ ")) " ^
       "(fun2set (stack_state_memory (s:(A,C,FFI)stack_state),stack_state_mdomain s))"))
     (MP_TAC o MATCH_MP (ISPEC `wl_Word (word 0):(A)word_loc` write_fun2set)) THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
        `set_sep_one (word_sub (ptr4:A word) bytes_in_word,lastw:(A)word_loc)`)) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC)];
    ALL_TAC] THEN
  (* run the init code *)
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `gen_gc':bool`; `max_heap:num`; `k:num`;
     `ptr2:A word`; `ptr3:A word`; `ptr4:A word`; `bitmap_ptr:A word`;
     `wl_Word (word_add bitmap_ptr (word_mul bytes_in_word
        (word (LENGTH (bitmaps:(A word)list))))):(A)word_loc`;
     `wl_Word (word_add (word_add bitmap_ptr (word_mul bytes_in_word
        (word (LENGTH (bitmaps:(A word)list))))) (word_mul bytes_in_word (word data_sp))):(A)word_loc`;
     `wl_Word (buffer_position (stack_state_code_buffer (s:(A,C,FFI)stack_state)))`;
     `wl_Word (word_add (buffer_position (stack_state_code_buffer (s:(A,C,FFI)stack_state)))
        (word (buffer_space_left (stack_state_code_buffer s))))`;
     `mid:A word`; `adj3:A word`; `mhw:A word`; `q:A word`; `reg3:A word`; `half:A word`;
     parse_term (STACKPROPSAUX_WB ^ " STAR " ^ STACKPROPSAUX_WD ^ " STAR " ^ STACKPROPSAUX_WH ^
       " STAR " ^ STACKPROPSAUX_WR ^
       " STAR set_sep_one (word_sub (ptr4:A word) bytes_in_word,wl_Word (word 0))");
     `bitst:((A)word_loc)list`] STACKPROPSAUX_init_eval) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[STACKPROPSAUX_LENGTH_store_list]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word->(A)word_loc` (X_CHOOSE_THEN `RF:(num,(A)word_loc)fmap`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_evaluate" with Failure _ -> false)
     then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY STACKPROPSAUX_DROP_DEF_TAC
    [`mid:A word`; `adj3:A word`; `mhw:A word`; `q:A word`; `half:A word`] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs(concl th) = `reg3:A word` && can (find_term ((=) `q:A word`)) (concl th))) THEN
  (* values read by init_reduce *)
  MAP_EVERY (fun n -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_FAPPLY_OF_FLOOKUP o
     check (fun th -> try lhand(lhs(concl th)) = `RF:(num,(A)word_loc)fmap` &&
                          rand(lhs(concl th)) = n with Failure _ -> false)))
    [`1`; `2`; `3`; `4`; `5`; `6`; `7`; `k:num`; `k + 1`; `k + 2`] THEN
  SUBGOAL_THEN `word_add reg3 (word_mul bytes_in_word (word (LENGTH stack_remove_store_list))) =
                word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48)))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[STACKPROPSAUX_LENGTH_store_list; WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub (word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48))))
                               ptr2) DIV (dimindex (:A) DIV 8) - LENGTH stack_remove_store_list =
                2 * hh /\
                val (word_sub (word_add ptr2 (word_mul bytes_in_word (word (Nw - 1))))
                              (word_add ptr2 (word_mul bytes_in_word (word (2 * hh + 48)))))
                  DIV (dimindex (:A) DIV 8) = Nw - 2 * hh - 49`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "vaddr" (MP_TAC o SPEC `Nw - 1`) THEN
    REWRITE_TAC[ARITH_RULE `Nw - 1 <= Nw`] THEN DISCH_TAC THEN
    USE_THEN "vaddr" (MP_TAC o SPEC `2 * hh + 48`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC; DISCH_TAC] THEN
    REWRITE_TAC[STACKPROPSAUX_LENGTH_store_list] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48)))`;
                     `ptr2:A word`] STACKPROPSAUX_val_sub_le);
      MP_TAC(ISPECL [`word_add (ptr2:A word) (word_mul bytes_in_word (word (Nw - 1)))`;
                     `word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48)))`]
        STACKPROPSAUX_val_sub_le)] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [REWRITE_TAC[LE_ADD_LCANCEL; LE_ADD; LE_MULT_RCANCEL] THEN
       UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC;
       DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[ARITH_RULE `(p + a) - p = a:num`;
                ARITH_RULE `(p + a) - (p + b) = a - b:num`; GSYM RIGHT_SUB_DISTRIB] THEN
    ASM_SIMP_TAC[DIV_MULT; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_shl (word_ushr bitmap_ptr (backend_common_word_shift (:A)))
                         (backend_common_word_shift (:A)) = bitmap_ptr:A word` ASSUME_TAC THENL
   [UNDISCH_TAC `byte_aligned (bitmap_ptr:A word)` THEN
    REWRITE_TAC[byte_aligned_def; aligned_def; align_shift] THEN
    SUBGOAL_THEN `LOG2 (dimindex (:A) DIV 8) = backend_common_word_shift (:A)` SUBST1_TAC THENL
     [STACKPROPSAUX_DIMCASES_GOAL_TAC THEN CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THEN REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the stack after the init code *)
  SUBGOAL_THEN `stack_removeProof_read_mem
                  (word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48))))
                  (m1:A word->(A)word_loc) (Nw - 2 * hh - 49 + 1) =
                APPEND (rest1:((A)word_loc)list) [wl_Word (word 0)]`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `Nw - 2 * hh - 49 + 1 = LENGTH (APPEND rest1 [wl_Word (word 0):(A)word_loc])`
      SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC word_list_IMP_read_mem THEN
    REWRITE_TAC[stack_removeProof_word_list_APPEND; misc_word_list_def; SEP_CLAUSES] THEN
    SUBGOAL_THEN `word_add (word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48))))
                    (word_mul bytes_in_word (word (LENGTH (rest1:((A)word_loc)list)))) =
                  word_sub ptr4 bytes_in_word` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `n - a - 48 - 1 = n - a - 49`] THEN
      (SUBGOAL_THEN `Nw - 1 = (2 * hh + 48) + (Nw - 2 * hh - 49)` SUBST1_TAC THENL
        [UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC;
         REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [parse_term ("misc_word_list (reg3:A word) (MAP (mem_val (RF:(num,(A)word_loc)fmap)) " ^
        "(MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list))) STAR " ^
        STACKPROPSAUX_WB ^ " STAR " ^ STACKPROPSAUX_WD ^ " STAR " ^ STACKPROPSAUX_WH);
      `stack_state_mdomain (s:(A,C,FFI)stack_state)`] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fun2set (m1:A word->(A)word_loc,
       stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
    ALL_TAC] THEN
  MP_TAC(CONV_RULE (DEPTH_CONV let_CONV) (ISPECL [`gen_gc':bool`; `k:num`; `RF:(num,(A)word_loc)fmap`]
    STACKPROPSAUX_init_store_lookups)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF; STACKPROPSAUX_SR_ACC] THEN
  ASM_REWRITE_TAC[theWord_def] THEN
  CONJ_TAC THENL
   [(* the pointers *)
    MAP_EVERY EXISTS_TAC [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`] THEN
    ASM_REWRITE_TAC[WORD_ULT] THEN CONJ_TAC THENL
     [UNDISCH_TAC `val (ptr4:A word) = val (ptr2:A word) + dimindex (:A) DIV 8 * Nw` THEN
      UNDISCH_TAC `1024 <= Nw` THEN STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `q:A word = ptr3` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
        rand(concl th) = `q:A word = ptr3`)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `q:A word = ptr3`);
                WORD_RULE `word_add (x:A word) (word_mul (word_neg (word 1)) y) = word_sub x y`] THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && rhs(concl th) = `reg3:A word`
                          then REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                          lhs(concl th) = `word_add reg3 (word_mul bytes_in_word
                                             (word (LENGTH stack_remove_store_list))):A word`
                          then REWRITE_TAC[th] else NO_TAC);
    ALL_TAC] THEN
  REWRITE_TAC[STACKPROPSAUX_store_map] THEN
  CONJ_TAC THENL
   [(* state_rel *)
    REWRITE_TAC[stack_removeProof_state_rel_def; STACKPROPSAUX_SR_ACC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; is_SOME_Word_def; the_SOME_Word_def; LET_DEF; LET_END_DEF;
                buffer_INFO.ri_accessors; APPEND_NIL; LENGTH_APPEND; LENGTH] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    USE_THEN "vaddr" (MP_TAC o SPEC `2 * hh + 48`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[max_stack_alloc_def] THEN UNDISCH_TAC `127 <= hh` THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                             `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC STACKPROPSAUX_stack_last_addr THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_word_store_map] THEN
    SUBGOAL_THEN `memory (m1:A word->(A)word_loc) (addresses ptr2 (2 * hh)) =
                  misc_word_list ptr2 (heap:((A)word_loc)list)` SUBST1_TAC THENL
     [SUBGOAL_THEN `2 * hh = LENGTH (heap:((A)word_loc)list)`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC word_list_in_memory THEN
      MAP_EVERY EXISTS_TAC
       [parse_term ("misc_word_list (reg3:A word) (MAP (mem_val (RF:(num,(A)word_loc)fmap)) " ^
          "(MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list))) STAR " ^
          STACKPROPSAUX_WB ^ " STAR " ^ STACKPROPSAUX_WD);
        parse_term (STACKPROPSAUX_WR ^
          " STAR set_sep_one (word_sub (ptr4:A word) bytes_in_word,wl_Word (word 0))");
        `stack_state_mdomain (s:(A,C,FFI)stack_state)`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fun2set (m1:A word->(A)word_loc,
          stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                               `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
        STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `misc_word_list (reg3:A word) (MAP (mem_val (RF:(num,(A)word_loc)fmap))
        (MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list))) =
      word_list_rev (word_add ptr2 (word_mul bytes_in_word (word (2 * hh + 48))))
        (MAP (\n. mem_val RF (store_init gen_gc' k n)) stack_remove_store_list)`
      SUBST_ALL_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [word_list_EQ_rev] THEN
      REWRITE_TAC[LENGTH_MAP; LENGTH_REVERSE; STACKPROPSAUX_LENGTH_store_list; MAP_REVERSE;
                  REVERSE_REVERSE; MAP_MAP_o; o_DEF] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[ASSUME `reg3 = word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh)))`;
                  WORD_ADD] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `misc_word_list (word_add (ptr2:A word) (word_mul bytes_in_word (word (2 * hh + 48))))
        (APPEND (rest1:((A)word_loc)list) [wl_Word (word 0)]) =
      misc_word_list (word_add ptr2 (word_mul bytes_in_word (word (2 * hh + 48)))) rest1 STAR
      set_sep_one (word_sub ptr4 bytes_in_word,wl_Word (word 0))` SUBST1_TAC THENL
     [REWRITE_TAC[stack_removeProof_word_list_APPEND; misc_word_list_def; SEP_CLAUSES] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - a - 48 - 1 = n - a - 49`] THEN
      MATCH_MP_TAC STACKPROPSAUX_stack_last_addr THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fun2set (m1:A word->(A)word_loc,
       stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* init_prop *)
    REWRITE_TAC[init_prop_def; stack_heap_limit_ok_def; STACKPROPSAUX_SR_ACC;
                buffer_INFO.ri_accessors] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`ptr2:A word`; `word_add ptr2 half:A word`;
      `word_ushr bitmap_ptr (backend_common_word_shift (:A)):A word`; `hh:num`] THEN
    SUBGOAL_THEN `half = word_mul (word hh) (bytes_in_word:A word)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN
      MP_TAC(SPEC `hh:num` STACKPROPSAUX_val_mul_bw) THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                               `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
        STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
        SIMP_TAC[] THEN DISCH_TAC THEN ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bitmap_ptr:A word`; `bitmaps:(A word)list`; `data_sp:num`;
      parse_term ("misc_word_list (reg3:A word) (MAP (mem_val (RF:(num,(A)word_loc)fmap)) " ^
        "(MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list))) STAR " ^
        STACKPROPSAUX_WH ^ " STAR " ^ STACKPROPSAUX_WR ^
        " STAR set_sep_one (word_sub (ptr4:A word) bytes_in_word,wl_Word (word 0))");
      `m1:A word->(A)word_loc`; `stack_state_mdomain (s:(A,C,FFI)stack_state)`]
      STACKPROPSAUX_bitmaps_bound) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fun2set (m1:A word->(A)word_loc,
         stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
      DISCH_TAC] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; LAST_APPEND; LAST; NOT_CONS_NIL] THEN
    REWRITE_TAC[WORD_RULE `word_mul (word n) (bytes_in_word:A word) =
                           word_mul bytes_in_word (word n)`] THEN
    REPEAT CONJ_TAC THENL
     [BOOL_CASES_TAC `gen_gc':bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_RULE `word_mul (word n) (bytes_in_word:A word) =
                             word_mul bytes_in_word (word n)`];
      MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                             `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC;
      UNDISCH_TAC `LENGTH (bitmaps:(A word)list) + data_sp + 1 < dimword (:A)` THEN
      REWRITE_TAC[dimword_def];
      MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                             `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      UNDISCH_TAC `2 * hh + 255 <= Nw` THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                             `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      UNDISCH_TAC `2 * hh <= max_heap` THEN ARITH_TAC;
      REWRITE_TAC[GSYM stack_removeProof_word_list_exists_ADD; ARITH_RULE `hh + hh = 2 * hh`] THEN
      MATCH_MP_TAC word_list_exists_addresses THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                             `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC];
    (* the heap is not touched *)
    SUBGOAL_THEN `2 * hh = LENGTH (heap:((A)word_loc)list)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `memory (stack_state_memory (s:(A,C,FFI)stack_state))
                    (addresses ptr2 (LENGTH (heap:((A)word_loc)list))) =
                  memory (m1:A word->(A)word_loc) (addresses ptr2 (LENGTH heap))` MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `misc_word_list (ptr2:A word) (heap:((A)word_loc)list)` THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
      MATCH_MP_TAC word_list_in_memory THENL
       [MAP_EVERY EXISTS_TAC
         [parse_term (STACKPROPSAUX_WB ^ " STAR " ^ STACKPROPSAUX_WD);
          parse_term (STACKPROPSAUX_WS ^ " STAR " ^ STACKPROPSAUX_WR ^
            " STAR set_sep_one (word_sub (ptr4:A word) bytes_in_word,lastw:(A)word_loc)");
          `stack_state_mdomain (s:(A,C,FFI)stack_state)`] THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
            `set_sep_one (word_sub (ptr4:A word) bytes_in_word,lastw:(A)word_loc)`)) (concl th))) THEN
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
          ASM_REWRITE_TAC[];
          ALL_TAC];
        MAP_EVERY EXISTS_TAC
         [parse_term ("misc_word_list (reg3:A word) (MAP (mem_val (RF:(num,(A)word_loc)fmap)) " ^
            "(MAP (store_init gen_gc' k) (REVERSE stack_remove_store_list))) STAR " ^
            STACKPROPSAUX_WB ^ " STAR " ^ STACKPROPSAUX_WD);
          parse_term (STACKPROPSAUX_WR ^
            " STAR set_sep_one (word_sub (ptr4:A word) bytes_in_word,wl_Word (word 0))");
          `stack_state_mdomain (s:(A,C,FFI)stack_state)`] THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `fun2set (m1:A word->(A)word_loc,
            stack_state_mdomain (s:(A,C,FFI)stack_state))`)) (concl th))) THEN
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN CONV_TAC(AC STACKPROPSAUX_STAR_AC);
          ASM_REWRITE_TAC[];
          ALL_TAC]] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`2 * hh + 255 <= Nw`;
                             `val (ptr2:A word) + dimindex (:A) DIV 8 * Nw < dimword (:A)`] THEN
      STACKPROPSAUX_DIMCASES_GOAL_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[memory_def; FUN_EQ_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `fun2set (stack_state_memory (s:(A,C,FFI)stack_state),
                                       addresses ptr2 (LENGTH (heap:((A)word_loc)list)))`) THEN
    REWRITE_TAC[]]);;

(* the init part: make_init_opt, init_pre, clock and ffi neutrality, IMP_code_rel, make_init_any *)

(* HOL4 line 3839 *)
let make_init_opt_def = cake_def
  `make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code
                 (s:(A,C,FFI)stack_state) =
     match stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) with
       (SOME _,t) -> NONE
     | (NONE,t) ->
         if init_prop gen_gc' max_heap data_sp
              (get_stack_heap_limit max_heap (read_pointers s))
              (init_reduce gen_gc' jump off k code bitmaps data_sp coracle t)
         then SOME (init_reduce gen_gc' jump off k code bitmaps data_sp coracle t)
         else NONE`;;

(* HOL4 line 3849 *)
let init_pre_def = cake_def
  `init_pre gen_gc' max_heap (bitmaps:(A word)list) data_sp k start
            (s:(A,C,FFI)stack_state) <=>
     lookup 0 (stack_state_code s) =
       SOME (stack_Seq (stack_remove_init_code gen_gc' max_heap k)
                       (stack_Call NONE (INL start) NONE)) /\
     init_code_pre k bitmaps data_sp s /\ max_stack_alloc <= max_heap`;;

(* HOL4 line 3856 *)
let evaluate_init_code = prove
 (CASE_TERM
  `!gen_gc' max_heap bitmaps data_sp k start (s:(A,C,FFI)stack_state) jump off coracle code.
     init_pre gen_gc' max_heap bitmaps data_sp k start s /\
     stack_state_compile_oracle s =
       (I ## MAP (stack_remove_prog_comp jump off k) ## I) o coracle /\
     (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k /\ stack_num_stubs <= i + 1) /\
     lookup stack_err_lab (stack_state_code s) = SOME (halt_inst (word 2)) /\
     stack_removeProof_code_rel jump off k code (stack_state_code s)
     ==> (match stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) with
            (NONE,t) ->
              ?r. make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code s =
                    SOME r /\
                  stack_removeProof_state_rel jump off k r t /\
                  stack_state_ffi t = stack_state_ffi s
          | _ -> F)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[init_pre_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `bitmaps:(A word)list`; `data_sp:num`; `s:(A,C,FFI)stack_state`;
                 `jump:bool`; `off:A word#A word`; `code:((A)stack_prog)spt`;
                 `coracle:num->C#(num#(A)stack_prog)list#(A word)list`; `gen_gc':bool`;
                 `max_heap:num`] init_code_thm) THEN
  ASM_REWRITE_TAC[make_init_opt_def] THEN
  MP_TAC(ISPEC `stack_evaluate (stack_remove_init_code gen_gc' max_heap k,
                                (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  STRUCT_CASES_TAC(ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3875 *)
let clock_neutral_store_list_code = prove
 (`!xs n k. clock_neutral (store_list_code n k xs:(A)stack_prog)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[store_list_code_def; clock_neutral_def] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:A word+num`,`h:A word+num`) THEN
  MATCH_MP_TAC sum_INDUCT THEN
  SIMP_TAC[store_list_code_def; clock_neutral_def; stack_list_Seq_def]);;

let STACKPROPSAUX_clock_neutral_init_code = prove
 (`!gen_gc' max_heap k. clock_neutral (stack_remove_init_code gen_gc' max_heap k:(A)stack_prog)`,
  REWRITE_TAC[stack_remove_init_code_def; LET_DEF; LET_END_DEF; stack_list_Seq_def;
              init_memory_def; clock_neutral_def; clock_neutral_store_list_code]);;

(* HOL4 line 3882 (local) *)
let evaluate_init_code_clock = prove
 (`!gen_gc' max_heap k (s:(A,C,FFI)stack_state) res t c.
     stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) = (res,t)
     ==> stack_evaluate (stack_remove_init_code gen_gc' max_heap k,
                         stack_state_clock_fupd (K c) s) =
           (res,stack_state_clock_fupd (K c) t)`,
  MESON_TAC[evaluate_clock_neutral; STACKPROPSAUX_clock_neutral_init_code]);;

(* HOL4 line 3893 *)
let evaluate_init_code_ffi = prove
 (`!gen_gc' max_heap k (s:(A,C,FFI)stack_state) res t c.
     stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) = (res,t)
     ==> stack_evaluate (stack_remove_init_code gen_gc' max_heap k,
                         stack_state_ffi_fupd (K c) s) =
           (res,stack_state_ffi_fupd (K c) t)`,
  MESON_TAC[evaluate_ffi_neutral; STACKPROPSAUX_clock_neutral_init_code]);;

(* init_semantics: the init program shifts the clock by one *)

let STACKPROPSAUX_EVAL_EQ_REWRITE_TAC : tactic =
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_evaluate" with Failure _ -> false)
     then REWRITE_TAC[th] else NO_TAC);;

let STACKPROPSAUX_semantics_shift = prove
 (`!st0 st1 (s:(A,C,FFI)stack_state) (t:(A,C,FFI)stack_state).
     (!k. FST (stack_evaluate (stack_Call NONE (INL st0) NONE,stack_state_clock_fupd (K (k + 1)) s)) =
          FST (stack_evaluate (stack_Call NONE (INL st1) NONE,stack_state_clock_fupd (K k) t)) /\
          stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL st0) NONE,
                                                stack_state_clock_fupd (K (k + 1)) s))) =
          stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL st1) NONE,
                                                stack_state_clock_fupd (K k) t)))) /\
     FST (stack_evaluate (stack_Call NONE (INL st0) NONE,stack_state_clock_fupd (K 0) s)) =
       SOME stack_TimeOut /\
     stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL st0) NONE,
                                           stack_state_clock_fupd (K 0) s))) =
     stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL st1) NONE,
                                           stack_state_clock_fupd (K 0) t)))
     ==> stack_semantics st0 s = stack_semantics st1 t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "shift") (CONJUNCTS_THEN2 (LABEL_TAC "to0")
    (LABEL_TAC "ffi0"))) THEN
  REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  (* the fail condition *)
  W(fun (asl,w) ->
    let c0 = rand(rator(rator(lhs w))) and c1 = rand(rator(rator(rhs w))) in
    SUBGOAL_THEN (mk_eq(c0,c1)) SUBST1_TAC) THENL
   [EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THENL
     [STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN USE_THEN "to0" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "stack_result"] THEN
      REWRITE_TAC[ADD1] THEN USE_THEN "shift" (fun th -> REWRITE_TAC[th]) THEN
      MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `n + 1` THEN USE_THEN "shift" (fun th -> ASM_REWRITE_TAC[th])];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  (* the diverging behaviours *)
  W(fun (asl,w) ->
    let isimg t = is_comb t && is_comb (rator t) &&
                  (try fst(dest_const(rator(rator t))) = "IMAGE" with Failure _ -> false) in
    let i0 = find_term isimg (lhs w) and i1 = find_term isimg (rhs w) in
    SUBGOAL_THEN (mk_eq(i0,i1)) SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `x:(io_event)llist` THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
     [STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
       [EXISTS_TAC `0` THEN USE_THEN "ffi0" (fun th -> REWRITE_TAC[th]);
        EXISTS_TAC `n':num` THEN REWRITE_TAC[ADD1] THEN
        USE_THEN "shift" (fun th -> REWRITE_TAC[th])];
      EXISTS_TAC `n + 1` THEN USE_THEN "shift" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  (* the terminating behaviours *)
  W(fun (asl,w) ->
    let issome t = is_comb t && (try fst(dest_const(rator t)) = "some" with Failure _ -> false) in
    let p0 = rand(find_term issome (lhs w)) and p1 = rand(find_term issome (rhs w)) in
    SUBGOAL_THEN (mk_eq(p0,p1)) SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `res:behaviour` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
        (X_CHOOSE_THEN `r:(A)stack_result` (X_CHOOSE_THEN `out:outcome` STRIP_ASSUME_TAC)))) THEN
      DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)
        (SPEC `n:num` num_CASES) THENL
       [USE_THEN "to0" MP_TAC THEN STACKPROPSAUX_EVAL_EQ_REWRITE_TAC THEN
        REWRITE_TAC[injectivity "option"] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `out:outcome`)) (concl th) &&
                                                not (is_eq (concl th)))) THEN
        CASE_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "shift" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[GSYM ADD1] THEN
      STACKPROPSAUX_EVAL_EQ_REWRITE_TAC THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`m:num`;
        `SND (stack_evaluate (stack_Call NONE (INL st1) NONE,
                              stack_state_clock_fupd (K m) (t:(A,C,FFI)stack_state)))`;
        `r:(A)stack_result`; `out:outcome`] THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ];
      DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
        (X_CHOOSE_THEN `r:(A)stack_result` (X_CHOOSE_THEN `out:outcome` STRIP_ASSUME_TAC)))) THEN
      USE_THEN "shift" (MP_TAC o SPEC `n:num`) THEN STACKPROPSAUX_EVAL_EQ_REWRITE_TAC THEN
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`n + 1`;
        `SND (stack_evaluate (stack_Call NONE (INL st0) NONE,
                              stack_state_clock_fupd (K (n + 1)) (s:(A,C,FFI)stack_state)))`;
        `r:(A)stack_result`; `out:outcome`] THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ]];
    ALL_TAC] THEN
  REWRITE_TAC[]);;

let STACKPROPSAUX_tail_call_not_bad = prove
 (`!dest (s:(A,C,FFI)stack_state).
     ~stack_bad_fun_return (FST (stack_evaluate (stack_Call NONE dest NONE,s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_OPT_CASES_TAC
    `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state)) (stack_state_code s)`
    `prog:(A)stack_prog` THEN
  CASE_REWRITE_TAC[stack_bad_fun_return_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[stack_bad_fun_return_def] THEN
  MP_TAC(ISPEC `stack_evaluate (prog:(A)stack_prog,stack_dec_clock (s:(A,C,FFI)stack_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)stack_result)option`
    (X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  REWRITE_TAC[stack_fix_clock_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[stack_bad_fun_return_def]);;

let STACKPROPSAUX_call_seq = prove
 (`!(s:(A,C,FFI)stack_state) p1 dest k t1.
     lookup 0 (stack_state_code s) = SOME (stack_Seq p1 (stack_Call NONE dest NONE)) /\
     stack_evaluate (p1,stack_state_clock_fupd (K k) s) = (NONE,t1)
     ==> FST (stack_evaluate (stack_Call NONE (INL 0) NONE,
                              stack_state_clock_fupd (K (k + 1)) s)) =
         FST (stack_evaluate (stack_Call NONE dest NONE,t1)) /\
         stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL 0) NONE,
                                               stack_state_clock_fupd (K (k + 1)) s))) =
         stack_state_ffi (SND (stack_evaluate (stack_Call NONE dest NONE,t1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dest:num+num`; `t1:(A,C,FFI)stack_state`] STACKPROPSAUX_tail_call_not_bad) THEN
  ABBREV_TAC `R = stack_evaluate (stack_Call NONE dest NONE:(A)stack_prog,t1:(A,C,FFI)stack_state)` THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[stack_find_code_def] THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_SR_ACC; ARITH_RULE `~(k + 1 = 0)`] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_dec_clock_def; STACKPROPSAUX_SR_ACC] THEN
  REWRITE_TAC STACKPROPSAUX_SR_NORM THEN REWRITE_TAC[ARITH_RULE `(k + 1) - 1 = k`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STACKPROPSAUX_ev_seq_none th]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `R:((A)stack_result)option#(A,C,FFI)stack_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)stack_result)option`
    (X_CHOOSE_THEN `s2:(A,C,FFI)stack_state` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[stack_fix_clock_def] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN ASM_REWRITE_TAC[STACKPROPSAUX_SR_ACC]);;

let STACKPROPSAUX_tail_call_clock0 = prove
 (`!dest (s:(A,C,FFI)stack_state).
     stack_state_ffi (SND (stack_evaluate (stack_Call NONE dest NONE,
                                           stack_state_clock_fupd (K 0) s))) =
     stack_state_ffi s /\
     (!p. stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME p
          ==> FST (stack_evaluate (stack_Call NONE dest NONE,stack_state_clock_fupd (K 0) s)) =
              SOME stack_TimeOut)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STACKPROPSAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN
  STACKPROPSAUX_OPT_CASES_TAC
    `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state)) (stack_state_code s)`
    `prog:(A)stack_prog` THEN
  CASE_REWRITE_TAC[stack_empty_env_def; STACKPROPSAUX_SR_ACC; injectivity "option";
                   distinctness "option"]);;

(* HOL4 line 3904 *)
let init_semantics = prove
 (CASE_TERM
  `!(s:(A,C,FFI)stack_state) jump off k code gen_gc' max_heap bitmaps data_sp start coracle.
     lookup stack_err_lab (stack_state_code s) = SOME (halt_inst (word 2)) /\
     stack_removeProof_code_rel jump off k code (stack_state_code s) /\
     init_pre gen_gc' max_heap bitmaps data_sp k start s /\
     stack_state_compile_oracle s =
       (I ## MAP (stack_remove_prog_comp jump off k) ## I) o coracle /\
     (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k /\ stack_num_stubs <= i + 1)
     ==> (match stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) with
            (NONE,t) ->
              stack_semantics 0 s = stack_semantics start t /\
              (?r. make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code s =
                     SOME r /\
                   stack_removeProof_state_rel jump off k r t)
          | _ -> F)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`gen_gc':bool`; `max_heap:num`; `bitmaps:(A word)list`; `data_sp:num`; `k:num`;
                 `start:num`; `s:(A,C,FFI)stack_state`; `jump:bool`; `off:A word#A word`;
                 `coracle:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `code:((A)stack_prog)spt`] evaluate_init_code) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `stack_evaluate (stack_remove_init_code gen_gc' max_heap k,
                                (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:(A)stack_result` SUBST_ALL_TAC)
    (ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `r:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[init_pre_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "init_pre"
                     with Failure _ -> false)) THEN
  MATCH_MP_TAC STACKPROPSAUX_semantics_shift THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:num` THEN MATCH_MP_TAC STACKPROPSAUX_call_seq THEN
    EXISTS_TAC `stack_remove_init_code gen_gc' max_heap k:(A)stack_prog` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_init_code_clock th]);
    MP_TAC(ISPECL [`INL 0:num+num`; `s:(A,C,FFI)stack_state`] STACKPROPSAUX_tail_call_clock0) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[stack_find_code_def] THEN
    MESON_TAC[];
    REWRITE_TAC[STACKPROPSAUX_tail_call_clock0] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 3971 *)
let make_init_opt_SOME_semantics = prove
 (`!gen_gc' max_heap bitmaps data_sp k start (s2:(A,C,FFI)stack_state) jump off coracle code.
     init_pre gen_gc' max_heap bitmaps data_sp k start s2 /\
     stack_state_compile_oracle s2 =
       (I ## MAP (stack_remove_prog_comp jump off k) ## I) o coracle /\
     (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k /\ stack_num_stubs <= i + 1) /\
     stack_removeProof_code_rel jump off k code (stack_state_code s2) /\
     lookup stack_err_lab (stack_state_code s2) = SOME (halt_inst (word 2))
     ==> ?s1. make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code s2 =
                SOME s1 /\
              (~(stack_semantics start s1 = Fail)
               ==> stack_semantics 0 s2 = stack_semantics start s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s2:(A,C,FFI)stack_state`; `jump:bool`; `off:A word#A word`; `k:num`;
                 `code:((A)stack_prog)spt`; `gen_gc':bool`; `max_heap:num`;
                 `bitmaps:(A word)list`; `data_sp:num`; `start:num`;
                 `coracle:num->C#(num#(A)stack_prog)list#(A word)list`] init_semantics) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `stack_evaluate (stack_remove_init_code gen_gc' max_heap k,
                                (s2:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `rr:(A)stack_result` SUBST1_TAC)
    (ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `r:(A,C,FFI)stack_state` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `r:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[stack_removeProof_compile_semantics]);;

(* HOL4 line 3988 (local) *)
let IMP_code_rel = prove
 (`!k (code1:(num#(A)stack_prog)list) code2 jump off gen_gc' max_heap start.
     ALL (\(n,p). reg_bound p k /\ stack_num_stubs <= n + 1) code1 /\
     code2 = fromAList (stack_remove_compile jump off gen_gc' max_heap k start code1)
     ==> stack_removeProof_code_rel jump off k (fromAList code1) code2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[stack_removeProof_code_rel_def; lookup_fromAList; domain_fromAList;
              stack_remove_compile_def; stack_remove_init_stubs_def;
              stack_removeProof_prog_comp_eta] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `prog:(A)stack_prog`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (\(n,p). reg_bound p k /\ stack_num_stubs <= n + 1)
                     (code1:(num#(A)stack_prog)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[stack_num_stubs_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND; ALOOKUP_THM] THEN
    SUBGOAL_THEN `~(0 = n) /\ ~(1 = n) /\ ~(2 = n)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ALOOKUP_MAP_2] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF];
    REWRITE_TAC[APPEND; MAP; set_of_list; MAP_MAP_o; o_DEF] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM] THEN
    SUBGOAL_THEN `(\(x:num,y:(A)stack_prog). x) = FST` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]; SET_TAC[]]]);;

(* HOL4 line 4007 *)
let make_init_any_def = cake_def
  `make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code
                 (s:(A,C,FFI)stack_state) =
     match make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code s with
       SOME t -> t
     | NONE ->
         stack_state_regs_fupd (K (FEMPTY |+ (0,wl_Loc 1 0)))
         (stack_state_fp_regs_fupd (K FEMPTY)
         (stack_state_mdomain_fupd (K EMPTY)
         (stack_state_bitmaps_fupd (K [word 4])
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_store_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_stack_fupd (K [wl_Word (word 0)])
         (stack_state_stack_space_fupd (K 0)
         (stack_state_compile_fupd
            (K (\c p. stack_state_compile s c (MAP (stack_remove_prog_comp jump off k) p)))
         (stack_state_compile_oracle_fupd (K coracle)
         (stack_state_data_buffer_fupd (K (buffer_REC (word 0) [] 0))
         (stack_state_code_buffer_fupd (K (buffer_REC (word 0) [] 0))
         (stack_state_code_fupd (K code)
         (stack_state_store_fupd
            (K (FEMPTY |++ MAP (\x. (x,wl_Word (word 0)))
                               (CONS CurrHeap stack_remove_store_list))) s))))))))))))))`;;

(* HOL4 line 4029 *)
let discharge_these_def = cake_def
  `discharge_these jump off gen_gc' max_heap k start coracle
                   (code:(num#(A)stack_prog)list) (s2:(A,C,FFI)stack_state) <=>
     ALL (\(n,p). reg_bound p k /\ stack_num_stubs <= n + 1) code /\
     (!n i p. MEM (i,p) (FST (SND (coracle n))) ==> reg_bound p k /\ stack_num_stubs <= i + 1) /\
     stack_state_compile_oracle s2 =
       (I ## MAP (stack_remove_prog_comp jump off k) ## I) o coracle /\
     stack_state_code s2 =
       fromAList (stack_remove_compile jump off gen_gc' max_heap k start code) /\
     8 <= k /\ 1 IN domain (stack_state_code s2) /\
     {k, k + 1, k + 2} SUBSET stack_state_ffi_save_regs s2 /\ ~stack_state_use_stack s2 /\
     ~stack_state_use_store s2 /\ ~stack_state_use_alloc s2 /\ max_stack_alloc <= max_heap`;;

(* HOL4 line 4041 *)
let propagate_these_def = cake_def
  `propagate_these (s:(A,C,FFI)stack_state) (bitmaps:(A word)list) data_sp <=>
     good_dimindex (:A) /\
     ?ptr2 ptr3 ptr4 bitmap_ptr.
       FLOOKUP (stack_state_regs s) 2 = SOME (wl_Word ptr2) /\
       FLOOKUP (stack_state_regs s) 3 = SOME (wl_Word ptr3) /\
       FLOOKUP (stack_state_regs s) 4 = SOME (wl_Word ptr4) /\
       stack_state_memory s ptr2 = wl_Word bitmap_ptr /\
       stack_state_memory s (word_add ptr2 bytes_in_word) =
         wl_Word (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       stack_state_memory s (word_add ptr2 (word_mul (word 2) bytes_in_word)) =
         wl_Word (word_add (word_add bitmap_ptr
                              (word_mul bytes_in_word (word (LENGTH bitmaps))))
                           (word_mul bytes_in_word (word data_sp))) /\
       stack_state_memory s (word_add ptr2 (word_mul (word 3) bytes_in_word)) =
         wl_Word (buffer_position (stack_state_code_buffer s)) /\
       stack_state_memory s (word_add ptr2 (word_mul (word 4) bytes_in_word)) =
         wl_Word (word_add (buffer_position (stack_state_code_buffer s))
                           (word (buffer_space_left (stack_state_code_buffer s)))) /\
       buffer_buffer (stack_state_code_buffer s) = [] /\
       word_ule ptr2 ptr4 /\
       byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       word_ule (word_mul (word 1024) bytes_in_word) (word_sub ptr4 ptr2) /\
       (misc_word_list bitmap_ptr (MAP wl_Word bitmaps) STAR
        word_list_exists (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps))))
                         data_sp STAR
        word_list_exists ptr2
          (val (word_add (word_mul (word_neg (word 1)) ptr2) ptr4) DIV
           val (bytes_in_word:A word)))
         (fun2set (stack_state_memory s,stack_state_mdomain s))`;;

(* HOL4 line 4069 *)
let stack_removeProof_make_init_semantics = prove
 (`!jump off gen_gc' max_heap k start coracle code (s2:(A,C,FFI)stack_state)
    (bitmaps:(A word)list) data_sp.
     discharge_these jump off gen_gc' max_heap k start coracle code s2 /\
     propagate_these s2 bitmaps data_sp
     ==> ?s1. make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k
                (fromAList code) s2 = SOME s1 /\
              (~(stack_semantics start s1 = Fail)
               ==> stack_semantics 0 s2 = stack_semantics start s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[discharge_these_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC make_init_opt_SOME_semantics THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[init_pre_def; init_code_pre_def] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[lookup_fromAList; stack_remove_compile_def; stack_remove_init_stubs_def;
                  APPEND; ALOOKUP_THM];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[propagate_these_def] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "propagate_these"
                         with Failure _ -> false)) THEN
      REWRITE_TAC[WORD_RULE `word_add (word_mul (word_neg (word 1)) (x:A word)) y =
                             word_sub y x`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`; `bitmap_ptr:A word`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC IMP_code_rel THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ASM_REWRITE_TAC[lookup_fromAList; stack_remove_compile_def; stack_remove_init_stubs_def;
                    APPEND; ALOOKUP_THM; stack_err_lab_def] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let STACKPROPSAUX_init_code_ffi_same = prove
 (`!gen_gc' max_heap k (s:(A,C,FFI)stack_state) res t.
     stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) = (res,t)
     ==> stack_state_ffi t = stack_state_ffi s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `stack_state_ffi (s:(A,C,FFI)stack_state)` o
              MATCH_MP evaluate_init_code_ffi) THEN
  SUBGOAL_THEN `stack_state_ffi_fupd (K (stack_state_ffi s)) s = (s:(A,C,FFI)stack_state)`
  SUBST1_TAC THENL
   [REWRITE_TAC[stack_state_component_equality; STACKPROPSAUX_SR_ACC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `stack_state_ffi:(A,C,FFI)stack_state->(FFI)ffi_state`) THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC] THEN MESON_TAC[]);;

let STACKPROPSAUX_MIA_TAC : tactic =
  REWRITE_TAC[make_init_any_def; make_init_opt_def] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF; STACKPROPSAUX_SR_ACC];;

(* HOL4 line 4088 *)
let make_init_any_ffi = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_ffi (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
                                    code s) = stack_state_ffi s`,
  STACKPROPSAUX_MIA_TAC THEN ASM_MESON_TAC[STACKPROPSAUX_init_code_ffi_same]);;

(* HOL4 line 4100 *)
let make_init_any_bitmaps = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_bitmaps (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
                                        code s) =
     if IS_SOME (make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code s)
     then bitmaps else [word 4]`,
  REWRITE_TAC[make_init_any_def; make_init_opt_def] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF; STACKPROPSAUX_SR_ACC; IS_SOME_DEF]);;

(* HOL4 line 4109 *)
let make_init_any_use_stack = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_use_stack (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
                                          code s)`,
  STACKPROPSAUX_MIA_TAC);;

(* HOL4 line 4116 *)
let make_init_any_use_store = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_use_store (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
                                          code s)`,
  STACKPROPSAUX_MIA_TAC);;

(* HOL4 line 4123 *)
let make_init_any_use_alloc = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     ~stack_state_use_alloc (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off
                                           k code s)`,
  STACKPROPSAUX_MIA_TAC);;

(* HOL4 line 4130 *)
let make_init_any_code = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_code (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
                                     code s) = code`,
  STACKPROPSAUX_MIA_TAC);;

(* HOL4 line 4137 *)
let make_init_any_stack_limit = prove
 (`!gen_gc' max_heap (bitmaps:(A word)list) data_sp coracle jump off k code
    (s:(A,C,FFI)stack_state).
     LENGTH (stack_state_stack (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump
                                              off k code s)) *
     (dimindex (:A) DIV 8) < dimword (:A)`,
  REWRITE_TAC[make_init_any_def; make_init_opt_def] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[init_prop_def]) THEN
                          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[STACKPROPSAUX_SR_ACC; LENGTH; MULT_CLAUSES; dimword_def] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dimindex (:A)` THEN
  REWRITE_TAC[DIV_LE; LT_POW2_REFL] THEN ARITH_TAC);;

(* HOL4 line 4151 *)
let make_init_any_compile_oracle = prove
 (`!ggc max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_compile_oracle (make_init_any ggc max_heap bitmaps data_sp coracle jump off k
                                               code s) = coracle`,
  STACKPROPSAUX_MIA_TAC);;

(* the labels of the code that the compiler adds *)

let STACKPROPSAUX_EL_TAC : tactic =
  REPEAT (CHANGED_TAC (REWRITE_TAC[stack_extract_labels_def; APPEND; APPEND_NIL] THEN
                       CASE_REWRITE_TAC[]));;

let STACKPROPSAUX_extract_labels_stack_free = prove
 (`!k n. stack_extract_labels (stack_remove_stack_free k n:(A)stack_prog) = []`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[single_stack_free_def] THEN
  STACKPROPSAUX_EL_TAC THEN ASM_SIMP_TAC[]);;

let STACKPROPSAUX_extract_labels_single_stack_alloc = prove
 (`!jump k n. stack_extract_labels (single_stack_alloc jump k n:(A)stack_prog) = []`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `jump:bool` THEN
  REWRITE_TAC[single_stack_alloc_def; halt_inst_def] THEN STACKPROPSAUX_EL_TAC);;

let STACKPROPSAUX_extract_labels_stack_alloc = prove
 (`!jump k n. stack_extract_labels (stack_alloc jump k n:(A)stack_prog) = []`,
  MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[STACKPROPSAUX_extract_labels_single_stack_alloc] THEN
  STACKPROPSAUX_EL_TAC THEN
  ASM_SIMP_TAC[STACKPROPSAUX_extract_labels_single_stack_alloc; APPEND]);;

let STACKPROPSAUX_extract_labels_upshift = prove
 (`!n n0. stack_extract_labels (upshift n n0:(A)stack_prog) = []`,
  MATCH_MP_TAC upshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[upshift_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STACKPROPSAUX_EL_TAC THEN ASM_SIMP_TAC[]);;

let STACKPROPSAUX_extract_labels_downshift = prove
 (`!n n0. stack_extract_labels (downshift n n0:(A)stack_prog) = []`,
  MATCH_MP_TAC downshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[downshift_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STACKPROPSAUX_EL_TAC THEN ASM_SIMP_TAC[]);;

let STACKPROPSAUX_ELC_TAC : tactic =
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[stack_extract_labels_def; STACKPROPSAUX_extract_labels_stack_free;
              STACKPROPSAUX_extract_labels_stack_alloc;
              stack_store_def; stack_load_def; STACKPROPSAUX_extract_labels_upshift;
              STACKPROPSAUX_extract_labels_downshift;
              stack_list_Seq_def; copy_loop_def; copy_each_def; APPEND; APPEND_NIL] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_extract_labels_def; STACKPROPSAUX_extract_labels_upshift;
              STACKPROPSAUX_extract_labels_downshift; APPEND; APPEND_NIL] THEN
  CASE_REWRITE_TAC[APPEND; APPEND_NIL];;

let STACKPROPSAUX_ELC_REC_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "stack_prog"; distinctness "stack_prog";
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[stack_extract_labels_def] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (CHANGED_TAC (STACKPROPSAUX_PAIRVAR_TAC THEN CASE_REWRITE_TAC[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"; PAIR_EQ;
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  ASM_REWRITE_TAC[stack_extract_labels_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[];;

(* HOL4 line 4176 *)
let stack_remove_lab_pres = prove
 (`!jump off k (p:(A)stack_prog).
     stack_extract_labels p = stack_extract_labels (stack_remove_comp jump off k p)`,
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  FIRST [STACKPROPSAUX_ELC_TAC THEN NO_TAC; STACKPROPSAUX_ELC_REC_TAC THEN NO_TAC]);;

(* HOL4 line 4170 (simp) *)
let stack_removeProof_FST_prog_comp = prove
 (`!jump (off:A word#A word) k (pp:num#(A)stack_prog).
     FST (stack_remove_prog_comp jump off k pp) = FST pp`,
  REWRITE_TAC[FORALL_PAIR_THM; stack_remove_prog_comp_def]);;

(* call_args of the code that the compiler produces *)

let STACKPROPSAUX_CA_TAC : tactic =
  REPEAT (CHANGED_TAC (REWRITE_TAC[call_args_def] THEN CASE_REWRITE_TAC[]));;

(* HOL4 line 4308 *)
let upshift_downshift_call_args = prove
 (`!n n0. call_args (upshift n n0:(A)stack_prog) 1 2 3 4 0 /\
          call_args (downshift n n0:(A)stack_prog) 1 2 3 4 0`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[upshift_def; downshift_def] THEN
  COND_CASES_TAC THEN STACKPROPSAUX_CA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[max_stack_alloc_def] THEN ARITH_TAC);;

let STACKPROPSAUX_call_args_store_list_code = prove
 (`!a t xs. call_args (store_list_code a t xs:(A)stack_prog) 1 2 3 4 0`,
  MATCH_MP_TAC store_list_code_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[store_list_code_def; stack_list_Seq_def] THEN STACKPROPSAUX_CA_TAC THEN
  ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_call_args_stack_free = prove
 (`!k n. call_args (stack_remove_stack_free k n:(A)stack_prog) 1 2 3 4 0`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[single_stack_free_def] THEN
  STACKPROPSAUX_CA_TAC THEN ASM_SIMP_TAC[]);;

let STACKPROPSAUX_call_args_single_stack_alloc = prove
 (`!jump k n. call_args (single_stack_alloc jump k n:(A)stack_prog) 1 2 3 4 0`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `jump:bool` THEN
  REWRITE_TAC[single_stack_alloc_def; halt_inst_def] THEN STACKPROPSAUX_CA_TAC);;

let STACKPROPSAUX_call_args_stack_alloc = prove
 (`!jump k n. call_args (stack_alloc jump k n:(A)stack_prog) 1 2 3 4 0`,
  MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[STACKPROPSAUX_call_args_single_stack_alloc] THEN
  STACKPROPSAUX_CA_TAC THEN
  ASM_SIMP_TAC[STACKPROPSAUX_call_args_single_stack_alloc]);;

let STACKPROPSAUX_call_args_init_stubs = prove
 (`!gen_gc' max_heap k start.
     ALL (\p. call_args p 1 2 3 4 0)
         (MAP SND (stack_remove_init_stubs gen_gc' max_heap k start:(num#(A)stack_prog)list))`,
  REWRITE_TAC[stack_remove_init_stubs_def; MAP; ALL; halt_inst_def;
              stack_remove_init_code_def; init_memory_def; LET_DEF; LET_END_DEF;
              stack_list_Seq_def] THEN
  STACKPROPSAUX_CA_TAC THEN REWRITE_TAC[STACKPROPSAUX_call_args_store_list_code]);;

let STACKPROPSAUX_CAC_TAC : tactic =
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[call_args_def; STACKPROPSAUX_call_args_stack_free;
              STACKPROPSAUX_call_args_stack_alloc;
              stack_store_def; stack_load_def; upshift_downshift_call_args;
              stack_list_Seq_def; copy_loop_def; copy_each_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[call_args_def; upshift_downshift_call_args] THEN
  CASE_REWRITE_TAC[];;

let STACKPROPSAUX_CAC_REC_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "stack_prog"; distinctness "stack_prog";
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  REWRITE_TAC[call_args_def] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (CHANGED_TAC (STACKPROPSAUX_PAIRVAR_TAC THEN CASE_REWRITE_TAC[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"; PAIR_EQ;
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  ASM_SIMP_TAC[call_args_def] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let STACKPROPSAUX_sr_call_args_comp = prove
 (`!jump off k (p:(A)stack_prog).
     call_args p 1 2 3 4 0 ==> call_args (stack_remove_comp jump off k p) 1 2 3 4 0`,
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  FIRST [STACKPROPSAUX_CAC_TAC THEN NO_TAC; STACKPROPSAUX_CAC_REC_TAC THEN NO_TAC]);;

(* HOL4 line 4320 *)
let stack_remove_call_args = prove
 (`!jump (off:A word#A word) gen_gc' n k pos (p:(num#(A)stack_prog)list) p'.
     stack_remove_compile jump off gen_gc' n k pos p = p' /\
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND p)
     ==> ALL (\p. call_args p 1 2 3 4 0) (MAP SND p')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[stack_remove_compile_def; MAP_APPEND; ALL_APPEND;
              STACKPROPSAUX_call_args_init_stubs] THEN
  SPEC_TAC(`p:(num#(A)stack_prog)list`,`p:(num#(A)stack_prog)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; stack_remove_prog_comp_def] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_sr_call_args_comp]);;

(* the conditions of stack_asm_name for the code that the compiler adds *)

let STACKPROPSAUX_reg_name_le = prove
 (`!r s (c:(A)asm_config). reg_name s c /\ r <= s ==> reg_name r c`,
  REWRITE_TAC[reg_name_def] THEN ARITH_TAC);;

let STACKPROPSAUX_word_offset_imm = prove
 (`!n. word_offset n:A word = word (n * (dimindex (:A) DIV 8))`,
  GEN_TAC THEN REWRITE_TAC[word_offset_def] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_SYM]);;

let STACKPROPSAUX_ASM_NAME_TAC : tactic =
  REWRITE_TAC[stack_asm_name_def; inst_name_def; arith_name_def; reg_imm_name_def;
              addr_name_def; STACKPROPSAUX_word_offset_imm] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[];;

let STACKPROPSAUX_asm_name_shift = prove
 (`!(c:(A)asm_config) n n0.
     reg_name n c /\
     (!m. m <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (m * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (m * (dimindex (:A) DIV 8))))
     ==> stack_asm_name c (upshift n n0:(A)stack_prog) /\
         stack_asm_name c (downshift n n0:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n0:num` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[upshift_def; downshift_def] THEN
  COND_CASES_TAC THEN STACKPROPSAUX_ASM_NAME_TAC THEN
  REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n0 - max_stack_alloc` o check (fun th ->
    can (find_term ((=) `upshift:num->num->(A)stack_prog`)) (concl th))) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[max_stack_alloc_def] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LE_REFL]);;

let STACKPROPSAUX_asm_name_stack_free = prove
 (`!k n (c:(A)asm_config).
     reg_name k c /\
     (!m. m <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (m * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (m * (dimindex (:A) DIV 8))))
     ==> stack_asm_name c (stack_remove_stack_free k n:(A)stack_prog)`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[single_stack_free_def] THEN
  STACKPROPSAUX_ASM_NAME_TAC THEN ASM_SIMP_TAC[LE_REFL]);;

let STACKPROPSAUX_asm_name_single_stack_alloc = prove
 (`!jump k n (c:(A)asm_config).
     reg_name k c /\ ~(k = 0) /\ n <= max_stack_alloc /\
     (!m. m <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (m * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (m * (dimindex (:A) DIV 8))))
     ==> stack_asm_name c (single_stack_alloc jump k n:(A)stack_prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `reg_name 1 (c:(A)asm_config)` ASSUME_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_reg_name_le THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  BOOL_CASES_TAC `jump:bool` THEN REWRITE_TAC[single_stack_alloc_def; halt_inst_def] THEN
  STACKPROPSAUX_ASM_NAME_TAC);;

let STACKPROPSAUX_asm_name_stack_alloc = prove
 (`!jump k n (c:(A)asm_config).
     reg_name k c /\ ~(k = 0) /\
     (!m. m <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (m * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (m * (dimindex (:A) DIV 8))))
     ==> stack_asm_name c (stack_alloc jump k n:(A)stack_prog)`,
  MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[stack_asm_name_def] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_asm_name_single_stack_alloc; LE_REFL]);;

let STACKPROPSAUX_word_shift_imm = prove
 (`good_dimindex (:A)
   ==> val (word (backend_common_word_shift (:A)):A word) < dimindex (:A) /\
       ~(word (backend_common_word_shift (:A)) = word 0:A word) /\
       val (word 1:A word) < dimindex (:A)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[backend_common_word_shift_def; GSYM VAL_EQ_0; VAL_WORD; dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let STACKPROPSAUX_AN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[stack_asm_name_def; stack_asm_remove_def;
                              STACKPROPSAUX_word_offset_imm]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_word_offset_imm]) THEN
  REWRITE_TAC[stack_asm_name_def; inst_name_def; arith_name_def; reg_imm_name_def;
              addr_name_def; stack_store_def; stack_load_def; stack_list_Seq_def;
              copy_loop_def; copy_each_def; halt_inst_def; STACKPROPSAUX_word_offset_imm] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; distinctness "memop"] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_asm_name_shift; STACKPROPSAUX_asm_name_stack_free;
               STACKPROPSAUX_asm_name_stack_alloc; LE_REFL; WORD_NE_10];;

let STACKPROPSAUX_AN_REC_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "stack_prog"; distinctness "stack_prog";
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_asm_name_def; stack_asm_remove_def]) THEN
  REWRITE_TAC[stack_asm_name_def] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_TYPE_CASES_TAC `:((A)stack_prog#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (CHANGED_TAC (STACKPROPSAUX_PAIRVAR_TAC THEN CASE_REWRITE_TAC[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; distinctness "option"; PAIR_EQ;
                              IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];;

(* HOL4 line 4209 *)
let stack_remove_comp_stack_asm_name = prove
 (`!jump off k (p:(A)stack_prog) (c:(A)asm_config).
     stack_asm_name c p /\ stack_asm_remove c p /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     good_dimindex (:A) /\
     (!n. n <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (n * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (n * (dimindex (:A) DIV 8)))) /\
     (!s. asm_offset_ok 0 (asm_config_addr_offset c) (store_offset s)) /\
     reg_name (k + 2) c /\ reg_name (k + 1) c /\ reg_name k c /\ ~(k = 0) /\
     off = asm_config_addr_offset c
     ==> stack_asm_name c (stack_remove_comp jump off k p)`,
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_word_shift_imm) THEN
  SUBGOAL_THEN `reg_name 1 (c:(A)asm_config) /\ reg_name 2 c /\ reg_name 3 c`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC STACKPROPSAUX_reg_name_le THEN
    EXISTS_TAC `k + 2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `asm_config_valid_imm (c:(A)asm_config) (INL asm_Add) bytes_in_word`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `max_stack_alloc`)) (concl th))) THEN
    REWRITE_TAC[max_stack_alloc_def; bytes_in_word_def; MULT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_remove_comp_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  FIRST [STACKPROPSAUX_AN_TAC THEN NO_TAC; STACKPROPSAUX_AN_REC_TAC THEN NO_TAC]);;

let STACKPROPSAUX_store_init_regs = prove
 (`!gen_gc' k n.
     (?w. store_init gen_gc' k n = INL (w:A word)) \/
     (?i. store_init gen_gc' k n = (INR i:A word+num) /\ (i = k + 2 \/ i <= 7))`,
  REWRITE_TAC[store_init_def; UPDATE_LIST_THM; APPLY_UPDATE_THM; FST; SND; K_THM] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "sum"; distinctness "sum"; UNWIND_THM1; UNWIND_THM2;
              EXISTS_REFL] THEN
  TRY ARITH_TAC THEN MESON_TAC[]);;

let STACKPROPSAUX_asm_name_store_list_code = prove
 (`!a t (xs:(A word+num)list) (c:(A)asm_config).
     reg_name a c /\ reg_name t c /\ asm_config_valid_imm c (INL asm_Add) bytes_in_word /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     ALL (\x. !i. x = INR i ==> reg_name i c) xs
     ==> stack_asm_name c (store_list_code a t xs:(A)stack_prog)`,
  MATCH_MP_TAC store_list_code_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; injectivity "sum"; distinctness "sum"; FORALL_UNWIND_THM1;
                              FORALL_UNWIND_THM2]) THEN
  REWRITE_TAC[store_list_code_def; stack_list_Seq_def] THEN
  REWRITE_TAC[stack_asm_name_def; inst_name_def; arith_name_def; reg_imm_name_def;
              addr_name_def; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 4280 *)
let stack_remove_stack_asm_name = prove
 (`!(c:(A)asm_config) (prog:(num#(A)stack_prog)list) jump gen_gc' max_heap k start.
     ALL (\(n,p). stack_asm_name c p) prog /\
     ALL (\(n,p). stack_asm_remove c p) prog /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     good_dimindex (:A) /\
     (!n. n <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (n * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (n * (dimindex (:A) DIV 8)))) /\
     asm_config_valid_imm c (INL asm_Add) (word 4) /\
     asm_config_valid_imm c (INL asm_Add) (word 8) /\
     (!s. asm_offset_ok 0 (asm_config_addr_offset c) (store_offset s)) /\
     reg_name 7 c /\ reg_name (k + 2) c /\ reg_name (k + 1) c /\ reg_name k c /\ ~(k = 0)
     ==> ALL (\(n,p). stack_asm_name c p)
             (stack_remove_compile jump (asm_config_addr_offset c) gen_gc' max_heap k start prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[stack_remove_compile_def; ALL_APPEND] THEN CONJ_TAC THENL
    [ALL_TAC;
     UNDISCH_TAC `ALL (\(n,p). stack_asm_remove (c:(A)asm_config) p) (prog:(num#(A)stack_prog)list)` THEN
     UNDISCH_TAC `ALL (\(n,p). stack_asm_name (c:(A)asm_config) p) (prog:(num#(A)stack_prog)list)` THEN
     SPEC_TAC(`prog:(num#(A)stack_prog)list`,`prog:(num#(A)stack_prog)list`) THEN
     LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
     SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
     REWRITE_TAC[FORALL_PAIR_THM; stack_remove_prog_comp_def] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC stack_remove_comp_stack_asm_name THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!r. r <= 7 ==> reg_name r (c:(A)asm_config)` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC STACKPROPSAUX_reg_name_le THEN
     EXISTS_TAC `7` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `asm_config_valid_imm (c:(A)asm_config) (INL asm_Add) bytes_in_word /\
                 val (word (1 + backend_common_word_shift (:A)):A word) < dimindex (:A) /\
                 ~(word (1 + backend_common_word_shift (:A)) = word 0:A word) /\
                 val (word (backend_common_word_shift (:A) + 1):A word) < dimindex (:A) /\
                 ~(word (backend_common_word_shift (:A) + 1) = word 0:A word) /\
                 val (word (backend_common_word_shift (:A)):A word) < dimindex (:A) /\
                 ~(word (backend_common_word_shift (:A)) = word 0:A word) /\
                 val (word 1:A word) < dimindex (:A)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `good_dimindex(:A)` THEN
     REWRITE_TAC[good_dimindex_def; bytes_in_word_def; backend_common_word_shift_def;
                 GSYM VAL_EQ_0; VAL_WORD; dimword_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[stack_remove_init_stubs_def; ALL; halt_inst_def; stack_remove_init_code_def;
               init_memory_def; LET_DEF; LET_END_DEF; stack_list_Seq_def] THEN
   CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[stack_asm_name_def; inst_name_def; arith_name_def; reg_imm_name_def;
               addr_name_def; IN_INSERT; NOT_IN_EMPTY; distinctness "memop"] THEN
   CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[ARITH; LE_REFL; WORD_NE_10] THEN
  MATCH_MP_TAC STACKPROPSAUX_asm_name_store_list_code THEN ASM_SIMP_TAC[LE_0] THEN
   REWRITE_TAC[ALL_MAP; o_DEF; GSYM ALL_MEM] THEN
   X_GEN_TAC `nm:store_name` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
   MP_TAC(ISPECL [`gen_gc':bool`; `k:num`; `nm:store_name`]
     (INST_TYPE [`:A`,`:A`] STACKPROPSAUX_store_init_regs)) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "sum"; distinctness "sum"] THEN
   DISCH_THEN SUBST_ALL_TAC THEN ASM_SIMP_TAC[]);;

