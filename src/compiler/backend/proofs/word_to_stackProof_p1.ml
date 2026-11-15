(* ========================================================================= *)
(* word_to_stackProof_p1: part 1 of 4 (HOL4 lines 1-3105) of the port of    *)
(* HOL4 compiler/backend/proofs/word_to_stackProofScript.sml (CakeML v3479). *)
(* Correctness proof for word_to_stack.                                      *)
(* The parts _p1 ... _p4 are loaded one after the other (each needs the     *)
(* previous one).                                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 Type state = wordSem$state is written out: (A,num#C,FFI)wl_state  *)
(*   (HOL4 val s), (A,C,FFI)stack_state (HOL4 val t); HOL4 val nn is         *)
(*   (NONE:(num#(A)wl_prog#num#num)option).                                  *)
(* - wordSem constants are wl_ ones, stackSem's stack_ ones (decided by the  *)
(*   types, or by the HOL4 proof where both type-check).                     *)
(*   store_consts_stub_location is wordLang's (wl_store_consts_stub_location *)
(*   = 6), as in word_to_stack.ml.                                           *)
(* - HOL4 r with f := v is RECTYPE_f_fupd (K v) r; t.store \\ Handler is     *)
(*   fdomsub (stack_state_store t) Handler; fm ' k is FAPPLY fm k; <<= is    *)
(*   isPREFIX; ZIP (l1,l2) is ZIP l1 l2 (length of l1: docs/CONVENTIONS.md   *)
(*   8; all uses here have equal lengths); GENLIST is list_of_seq; (<>) a is *)
(*   (\x. ~(a = x)); HOL4 LLOOKUP l n is oEL n l; const_inst r w is          *)
(*   stack_Inst (asm_Const r w).                                             *)
(* - Words: hol4/words4.ml (n2w = word, w2n = val, << = word_shl, >>> =      *)
(*   word_ushr, w ' i = bit i w, ...).                                       *)
(* - Free variables of HOL4 statements are universally quantified, after    *)
(*   HOL4's explicit binders; unused bound variables of HOL4 statements are  *)
(*   left out.  HOL4 variables named like constants of the session are       *)
(*   renamed: fv (closProps' fv) is fvl.                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/reg_alloc/parmove.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-3105 ===== *)

(* HOL4 lines 22-29: temp_delsimps, diminish_srw_ss, temp_prefer_num        *)
(* (simpset settings of the script; prioritize_num above).                   *)
(* HOL4 lines 31-32: val get_labels_def = stackSemTheory.get_labels_def,     *)
(* val extract_labels_def = stackPropsTheory.extract_labels_def: aliases;    *)
(* use stack_get_labels_def and stack_extract_labels_def.                    *)
(* HOL4 line 33: Type state = (A,B,C) wordSem$state: written out as wl_state *)
(* (HOL Light type abbreviations take no parameters).                        *)
(* HOL4 line 34: Overload word_cmp[local] = wordSem$word_cmp: wl_word_cmp.   *)
(* HOL4 lines 37-40: val nn = NONE:(num # 'a wordLang$prog # num # num)      *)
(* option, val s = s:('a,num # 'c,'ffi) wordSem$state, val t = t:('a,'c,'ffi)*)
(* stackSem$state: written out where used, as                                *)
(* (NONE:(num#(A)wl_prog#num#num)option), (s:(A,num#C,FFI)wl_state) and      *)
(* (t:(A,C,FFI)stack_state).                                                 *)

(* HOL4 line 42 *)
let StackHandlerArgs_F = prove
 (`!(dest:B+C) arg_count k f f'.
     StackHandlerArgs F dest arg_count (k,f,f') =
     StackArgs dest arg_count (k,f + 3,f' + 3):(A)stack_prog`,
  REWRITE_TAC[StackHandlerArgs_def; handler_slots_def]);;

(* HOL4 line 49 *)
let PushHandler_F = prove
 (`!l1 l2 k (f:B) (f':C).
     PushHandler F l1 l2 (k,f,f') =
     stack_Seq (StackAlloc 3)
    (stack_Seq (stack_Inst (asm_Const k (word 1)))
    (stack_Seq (StackStore k 0)
    (stack_Seq (stack_LocValue k l1 l2)
    (stack_Seq (StackStore k 1)
    (stack_Seq (stack_Get k Handler)
    (stack_Seq (StackStore k 2)
    (stack_Seq stack_Skip
    (stack_Seq (StackGetSize k)
               (stack_Set Handler k:(A)stack_prog)))))))))`,
  REWRITE_TAC[PushHandler_def; handler_slots_def]);;

(* HOL4 line 65 *)
let PopHandler_F = prove
 (`!k (f:B) (f':C) (prog:(A)stack_prog).
     PopHandler F (k,f,f') prog =
     stack_Seq (StackLoad k 2)
    (stack_Seq (stack_Set Handler k)
    (stack_Seq (StackFree 3) prog))`,
  REWRITE_TAC[PopHandler_def; handler_slots_def]);;

(* HOL4 line 74 *)
let raise_stub_F = prove
 (`!k. raise_stub F k =
     stack_Seq (stack_Get k Handler)
    (stack_Seq (StackSetSize k)
    (stack_Seq stack_Skip
    (stack_Seq (StackLoad k 2)
    (stack_Seq (stack_Set Handler k)
    (stack_Seq (StackLoad k 1)
    (stack_Seq (StackFree 3)
               (stack_Raise k:(A)stack_prog)))))))`,
  REWRITE_TAC[raise_stub_def; handler_slots_def]);;

(* HOL4 line 88 *)
let copy_ret_F = prove
 (`!is_handle k f (f':C) (vs:B list) (kont:(A)stack_prog).
     copy_ret F is_handle (k,f,f') vs kont =
     let n = num_stack_ret k vs in
     if n = 0 then kont
     else stack_Seq (copy_ret_aux k (if is_handle then f + 3 else f) n)
                    (SeqStackFree n kont)`,
  REWRITE_TAC[copy_ret_def; handler_slots_def]);;

(* HOL4 line 99 *)
let set_var_swap = prove
 (`!a a' b b' (c:(A,C,FFI)stack_state).
     ~(a = a')
     ==> stack_set_var a b (stack_set_var a' b' c) =
         stack_set_var a' b' (stack_set_var a b c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_set_var_def] THEN
  SIMP[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 106 *)
let set_var_swap_word = prove
 (`!a a' b b' (c:(A,C,FFI)wl_state).
     ~(a = a')
     ==> wl_set_var a b (wl_set_var a' b' c) = wl_set_var a' b' (wl_set_var a b c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_set_var_def] THEN
  SIMP[] THEN MATCH_MP_TAC insert_swap THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 112 *)
let set_var_cancel = prove
 (`!a b b' (t:(A,C,FFI)stack_state).
     stack_set_var a b (stack_set_var a b' t) = stack_set_var a b t`,
  REWRITE_TAC[stack_set_var_def] THEN SIMP[FUPDATE_EQ]);;

(* HOL4 line 118 *)
let set_var_cancel_word = prove
 (`!a b b' (s:(A,C,FFI)wl_state).
     wl_set_var a b (wl_set_var a b' s) = wl_set_var a b s`,
  REWRITE_TAC[wl_set_var_def] THEN SIMP[insert_shadow]);;

(* HOL4 line 124 *)
let word_to_stackProof_get_var_set_var = prove
 (`!k v (st:(A,C,FFI)stack_state). stack_get_var k (stack_set_var k v st) = SOME v`,
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE]);;

let _ = cake_add_simps [word_to_stackProof_get_var_set_var];;

(* HOL4 line 131 *)
let state_with_const = prove
 (`!(t:(A,C,FFI)stack_state). stack_state_clock_fupd (K (stack_state_clock t)) t = t`,
  SIMP[stack_state_component_equality]);;

let _ = cake_add_simps [state_with_const];;

(* HOL4 line 137 *)
let set_store_set_var = prove
 (`!a b c d (e:(A,C,FFI)stack_state).
     stack_set_store a b (stack_set_var c d e) =
     stack_set_var c d (stack_set_store a b e)`,
  REWRITE_TAC[stack_set_store_def; stack_set_var_def] THEN SIMP[]);;

(* HOL4 line 146 *)
let DROP_DROP_EQ = prove
 (`!n m (xs:A list). DROP m (DROP n xs) = DROP (m + n) xs`,
  MATCH_ACCEPT_TAC DROP_DROP_T);;

(* HOL4 line 152 *)
let TAKE_TAKE_MIN = prove
 (`!(xs:A list) m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_TAKE_CLAUSES] THEN
  INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_TAKE_CLAUSES; MIN; ARITH_RULE `SUC m <= SUC n <=> m <= n`;
                  ARITH_RULE `0 <= n /\ (SUC n <= 0 <=> F)`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[RICHAUX_TAKE_CLAUSES]);;

(* HOL4 line 159 *)
let TAKE_DROP_EQ = prove
 (`!(xs:A list) n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC TAKE_DROP_SWAP);;

(* HOL4 line 166 *)
let DROP_TAKE_NIL = prove
 (`!n (xs:A list). DROP n (TAKE n xs) = []`,
  REWRITE_TAC[DROP_TAKE_EQ_NIL]);;

(* HOL4 line 174 *)
let MAX_LIST_GENLIST_evens = prove
 (`!n. MAX_LIST (list_of_seq (\x. 2 * x) n) = 2 * (n - 1)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[GENLIST; MAX_LIST; MAX_LIST_SNOC] THEN
  ARITH_TAC);;

(* HOL4 line 181 *)
let MAX_LIST_GENLIST_evens2 = prove
 (`!n. MAX_LIST (list_of_seq (\x. 2 * (x + 1)) n) = 2 * n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[GENLIST; MAX_LIST; MAX_LIST_SNOC] THEN
  ARITH_TAC);;

(* HOL4 line 190 *)
let word_to_stackProof_word_or_eq_0 = prove
 (`!(w:A word) v. word_or w v = word 0 <=> w = word 0 /\ v = word 0`,
  REWRITE_TAC[WORD_OR_EQ_0]);;

(* HOL4 line 197 *)
let word_to_stackProof_shift_shift_lemma = prove
 (`!(w:A word). ~(word_msb w) ==> word_ushr (word_shl w 1) 1 = w`,
  GEN_TAC THEN REWRITE_TAC[word_msb_def; WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_SHL] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= i + 1`; ADD_SUB] THEN
  ASM_CASES_TAC `i + 1 < dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i = dimindex(:A) - 1` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* HOL4 line 207 *)
let word_shift_or_1 = prove
 (`!(n:A word). word_or (word_shl n 1) (word 1) = word_add (word_shl n 1) (word 1)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_1; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(1 <= 0)`]);;

(* HOL4 line 231 *)
let push_env_set_store = prove
 (`!env (c:A word) (s:(A,C,FFI)wl_state).
     wl_push_env env (NONE:(num#(A)wl_prog#num#num)option)
       (wl_set_store AllocSize (wl_Word c) s) =
     wl_set_store AllocSize (wl_Word c)
       (wl_push_env env (NONE:(num#(A)wl_prog#num#num)option) s)`,
  REWRITE_TAC[wl_push_env_def; wl_set_store_def] THEN SIMP[] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `env_to_list (SND (env:((A)word_loc)spt#((A)word_loc)spt))
              (wl_state_permute (s:(A,C,FFI)wl_state))` THEN
  SIMP[]);;

(* HOL4 line 238 *)
let LASTN_LENGTH_ID2 = prove
 (`!(stack:A list) x.
     x + 1 = LENGTH stack
     ==> LASTN (x + 1) stack = CONS (HD stack) (LASTN x stack)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; HD] THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `x + 1 = SUC n <=> x = n`] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[LASTN_CONS; LE_REFL; LASTN_LENGTH_ID] THEN
  MATCH_MP_TAC LASTN_LENGTH_cond THEN REWRITE_TAC[LENGTH; ADD1]);;

(* HOL4 line 249 *)
let LASTN_MORE = prove
 (`!(ls:A list) n. ~(n < LENGTH ls) ==> LASTN n ls = ls`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LASTN_LENGTH_LESS_EQ THEN ASM_ARITH_TAC);;

(* HOL4 line 257 *)
let LASTN_LENGTH_BOUNDS = prove
 (`!n (ls:A list).
     let xs = LASTN n ls in
     LENGTH xs <= n /\ LENGTH xs <= LENGTH ls`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LASTN_DEF; LENGTH_REVERSE; LENGTH_TAKE_EQ_MIN] THEN ARITH_TAC);;

(* HOL4 line 266 *)
let LASTN_CONS_ID = prove
 (`!n (ls:A list) frame.
     n = LENGTH ls ==> LASTN (SUC n) (CONS frame ls) = CONS frame ls`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LASTN_LENGTH_cond THEN ASM_REWRITE_TAC[LENGTH]);;

(* HOL4 line 274 *)
let LASTN_DROP2 = prove
 (`!(l:A list) n. LASTN n l = DROP (LENGTH l - n) l`,
  REWRITE_TAC[LASTN_DROP_UNCOND]);;

(* HOL4 line 285 *)
let EVERY_IMP_EVERY_LASTN = prove
 (`!(xs:A list) ys P n. ALL P xs /\ LASTN n xs = ys ==> ALL P ys`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[MEM_LASTN; ALL_MEM]);;

let W2SP1AUX_HD_DROP_LE = prove
 (`!(l:A list) n. n <= LENGTH l ==> HD (DROP n l) = EL n l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `n <= 0 <=> n = 0`] THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP; EL]; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[DROP; EL; HD; TL; LE_SUC] THEN ASM_SIMP_TAC[]);;

(* HOL4 line 291 *)
let LASTN_HD = prove
 (`!(ls:A list) x. x <= LENGTH ls ==> HD (LASTN x ls) = EL (LENGTH ls - x) ls`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LASTN_DROP_UNCOND] THEN
  MATCH_MP_TAC W2SP1AUX_HD_DROP_LE THEN ARITH_TAC);;

(* HOL4 line 308 *)
let LLOOKUP_TAKE = prove
 (`!n f (xs:A list). n < f ==> oEL n (TAKE f xs) = oEL n xs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[oEL_THM; LENGTH_TAKE_EQ_MIN] THEN
  SUBGOAL_THEN `n < MIN f (LENGTH (xs:A list)) <=> n < LENGTH xs` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_TAKE]]);;

(* HOL4 line 317: val the_eqn = backendPropsTheory.the_eqn (alias).          *)

(* HOL4 line 319 *)
let index_list_def = cake_def
  `(index_list ([]:A list) n = []) /\
   (index_list (CONS x xs) n = CONS (n + LENGTH xs,x) (index_list xs n))`;;

let index_list_ind = cake_ind "index_list";;

(* HOL4 line 324 *)
let LENGTH_index_list = prove
 (`!(l:A list) n. LENGTH (index_list l n) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[index_list_def; LENGTH]);;

(* HOL4 line 330 *)
let EL_index_list = prove
 (`!(xs:A list) i k.
     i < LENGTH xs
     ==> EL i (index_list xs k) = (((k + LENGTH xs) - i) - 1,EL i xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[index_list_def; EL; HD; TL; LT_SUC] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC;
    ASM_SIMP_TAC[PAIR_EQ] THEN ASM_ARITH_TAC]);;

(* HOL4 line 338 *)
let EL_index_list2 = prove
 (`!(xs:A list) i k.
     i < LENGTH xs
     ==> EL i (index_list xs k) = ((k + LENGTH xs) - (i + 1),EL i xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[index_list_def; EL; HD; TL; LT_SUC] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC;
    ASM_SIMP_TAC[PAIR_EQ] THEN ASM_ARITH_TAC]);;

(* HOL4 line 346 *)
let MAP_SND_index_list = prove
 (`!(xs:A list) k. MAP SND (index_list xs k) = xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[index_list_def; MAP]);;

(* HOL4 line 353 *)
let MAP_FST_index_list = prove
 (`!(xs:A list) k.
     MAP FST (index_list xs k) = REVERSE (MAP ((+) k) (COUNT_LIST (LENGTH xs)))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[index_list_def; MAP; LENGTH; COUNT_LIST_SNOC; REVERSE; MAP_SNOC;
                  REVERSE_SNOC]);;

(* HOL4 line 379 *)
let index_list_eq_ZIP = prove
 (`!(xs:A list) k.
     index_list xs k = ZIP (REVERSE (MAP ((+) k) (COUNT_LIST (LENGTH xs)))) xs`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ZIP_MAP_FST_SND_EQ] THEN
  REWRITE_TAC[MAP_FST_index_list; MAP_SND_index_list]);;

(* HOL4 line 386 *)
let MEM_index_list_LIM = prove
 (`!(ls:A list) n v k. MEM (n,v) (index_list ls k) ==> n - k < LENGTH ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[index_list_def; MEM; LENGTH; PAIR_EQ] THEN
  REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:A`; `k:num`]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* HOL4 line 399 *)
let MEM_index_list_EL = prove
 (`!(ls:A list) n v k.
     MEM (n,v) (index_list ls k) ==> EL (LENGTH ls - ((n - k) + 1)) ls = v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[index_list_def; MEM; LENGTH; PAIR_EQ] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `SUC (LENGTH (t:A list)) - ((n - k) + 1) = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[EL; HD]];
    SUBGOAL_THEN `(n:num) - k < LENGTH (t:A list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM_index_list_LIM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `SUC (LENGTH (t:A list)) - ((n - k) + 1) = SUC (LENGTH t - ((n - k) + 1))`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 414 *)
let ALOOKUP_index_list = prove
 (`!(ls:A list) n k.
     n < LENGTH ls + k
     ==> ALOOKUP (index_list ls k) n = oEL ((LENGTH ls + k) - (n + 1)) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[index_list_def; ALOOKUP_def; oEL_def; LENGTH] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `(SUC (LENGTH (t:A list)) + k) - (n + 1) = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    SUBGOAL_THEN
     `~((SUC (LENGTH (t:A list)) + k) - (n + 1) = 0) /\
      ((SUC (LENGTH t) + k) - (n + 1)) - 1 = (LENGTH t + k) - (n + 1) /\
      n < LENGTH t + k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]]]);;

(* HOL4 line 424 *)
let IMP_filter_bitmap_EQ_SOME_NIL = prove
 (`!xs (ys:A list) zs.
     LENGTH xs = LENGTH ys /\ zs = MAP FST (FILTER SND (ZIP ys xs))
     ==> filter_bitmap xs ys = SOME (zs,[])`,
  MATCH_MP_TAC filter_bitmap_ind THEN
  REWRITE_TAC[filter_bitmap_def; LENGTH; ZIP; HD; TL; FILTER; MAP; SUC_INJ; NOT_SUC] THEN
  REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `0 = LENGTH (rs:A list)` THEN
    REWRITE_TAC[ARITH_RULE `0 = n <=> n = 0`; LENGTH_EQ_NIL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[ZIP; FILTER; MAP];
    FIRST_X_ASSUM(MP_TAC o SPEC `MAP FST (FILTER SND (ZIP (rs:A list) bs))`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[]]);;

(* HOL4 line 434 *)
let filter_bitmap_length = prove
 (`!bs (ls:A list) xs ys.
     filter_bitmap bs ls = SOME (xs,ys) ==> LENGTH xs <= LENGTH bs`,
  MATCH_MP_TAC filter_bitmap_ind THEN
  REWRITE_TAC[filter_bitmap_def] THEN REPEAT STRIP_TAC THEN
  GVS(all_case_eqs()) THEN ASM_ARITH_TAC);;

(* HOL4 line 444 *)
let filter_bitmap_length_input = prove
 (`!xs (ys:A list) ls. filter_bitmap xs ys = SOME ls ==> LENGTH xs <= LENGTH ys`,
  MATCH_MP_TAC filter_bitmap_ind THEN
  REWRITE_TAC[filter_bitmap_def; LENGTH; LE_0] THEN REPEAT STRIP_TAC THEN
  GVS(all_case_eqs()) THEN RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 453 *)
let filter_bitmap_MAP_IMP = prove
 (`!ys (xs:(A#B)list) l.
     filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[]) /\
     filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])
     ==> filter_bitmap ys xs = SOME (l,[])`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_bitmap_def] THEN GVS[MAP_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `xs:(A#B)list` THEN BOOL_CASES_TAC `h:bool` THEN
  STRUCT_CASES_TAC(ISPEC `xs:(A#B)list` list_CASES) THEN
  REWRITE_TAC[MAP; filter_bitmap_def; NOT_SOME_NONE; GSYM NOT_SOME_NONE] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `y:A#B` (X_CHOOSE_THEN `ys:(A#B)list` SUBST_ALL_TAC))
    (ISPEC `l:(A#B)list` list_CASES) THEN
  FS[MAP] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':(A#B)list`; `ys:(A#B)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[PAIR_FST_SND_EQ]);;

(* HOL4 line 472 *)
let filter_bitmap_IMP_MAP_SND = prove
 (`!ys (xs:(A#B)list) l.
     filter_bitmap ys xs = SOME (l,[])
     ==> filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[])`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_bitmap_def] THEN GVS[MAP_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `xs:(A#B)list` THEN BOOL_CASES_TAC `h:bool` THEN
  STRUCT_CASES_TAC(ISPEC `xs:(A#B)list` list_CASES) THEN
  REWRITE_TAC[MAP; filter_bitmap_def; NOT_SOME_NONE; GSYM NOT_SOME_NONE] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SIMP[]);;

(* HOL4 line 483 *)
let filter_bitmap_IMP_MAP_FST = prove
 (`!ys (xs:(A#B)list) l.
     filter_bitmap ys xs = SOME (l,[])
     ==> filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_bitmap_def] THEN GVS[MAP_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `xs:(A#B)list` THEN BOOL_CASES_TAC `h:bool` THEN
  STRUCT_CASES_TAC(ISPEC `xs:(A#B)list` list_CASES) THEN
  REWRITE_TAC[MAP; filter_bitmap_def; NOT_SOME_NONE; GSYM NOT_SOME_NONE] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SIMP[]);;

(* HOL4 line 494 *)
let filter_bitmap_TAKE_LENGTH_IMP = prove
 (`!h5 (x4:A list) (l:(B#A)list).
     filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l,[])
     ==> filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; RICHAUX_TAKE_CLAUSES; filter_bitmap_def; RICHAUX_DROP_CLAUSES] THEN
    GVS[MAP_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `x4:A list` THEN BOOL_CASES_TAC `h:bool` THEN
  STRUCT_CASES_TAC(ISPEC `x4:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; RICHAUX_TAKE_CLAUSES; RICHAUX_DROP_CLAUSES; filter_bitmap_def;
              NOT_SOME_NONE; GSYM NOT_SOME_NONE] THEN
  REPEAT STRIP_TAC THENL
   [GVS(all_case_eqs()) THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `y:B#A` (X_CHOOSE_THEN `ys:(B#A)list` SUBST_ALL_TAC))
      (ISPEC `l:(B#A)list` list_CASES) THEN
    FS[MAP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':A list`; `ys:(B#A)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 505 *)
let filter_bitmap_lemma = prove
 (`!h5 (x4:A list) k l.
     filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l,[])
     ==> filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP filter_bitmap_IMP_MAP_SND) THEN
  REWRITE_TAC[MAP_SND_index_list] THEN MATCH_ACCEPT_TAC filter_bitmap_TAKE_LENGTH_IMP);;

(* HOL4 line 513 *)
let filter_bitmap_MEM = prove
 (`!b (ls:A list) ls' x.
     filter_bitmap b ls = SOME (ls',[]) /\ MEM x ls' ==> MEM x ls`,
  MATCH_MP_TAC filter_bitmap_ind THEN REWRITE_TAC[filter_bitmap_def] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN FS[MEM] THEN ASM_MESON_TAC[]);;

(* HOL4 line 524 *)
let TAKE_LUPDATE = prove
 (`!(xs:A list) n x i. TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_def; RICHAUX_TAKE_CLAUSES] THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `x:A` THEN X_GEN_TAC `i:num` THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[LUPDATE_def; RICHAUX_TAKE_CLAUSES]);;

let _ = cake_add_simps [TAKE_LUPDATE];;

(* HOL4 line 534 *)
let DROP_LUPDATE_lemma1 = prove
 (`!(xs:A list) n m h.
     n <= m ==> DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_def; RICHAUX_DROP_CLAUSES] THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `m:num` THEN X_GEN_TAC `x:A` THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  ASM_SIMP_TAC[LUPDATE_def; RICHAUX_DROP_CLAUSES; SUB_0; LE_SUC; SUB_SUC;
               ARITH_RULE `~(SUC n <= 0)`]);;

(* HOL4 line 541 *)
let DROP_LUPDATE_lemma2 = prove
 (`!(xs:A list) n m h. m < n ==> DROP n (LUPDATE h m xs) = DROP n xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_def; RICHAUX_DROP_CLAUSES] THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `m:num` THEN X_GEN_TAC `x:A` THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  ASM_SIMP_TAC[LUPDATE_def; RICHAUX_DROP_CLAUSES; LT_SUC; CONJUNCT1 LT]);;

(* HOL4 line 548 *)
let word_to_stackProof_DROP_LUPDATE = prove
 (`!n (h:A) m xs.
     DROP n (LUPDATE h m xs) =
     if m < n then DROP n xs else LUPDATE h (m - n) (DROP n xs)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[DROP_LUPDATE_lemma2] THEN
  MATCH_MP_TAC DROP_LUPDATE_lemma1 THEN ASM_ARITH_TAC);;

(* HOL4 line 558 *)
let word_to_stackProof_MIN_ADD = prove
 (`!m1 m2 n. MIN m1 m2 + n = MIN (m1 + n) (m2 + n)`,
  ARITH_TAC);;

(* HOL4 line 564 *)
let list_LUPDATE_def = cake_def
  `(list_LUPDATE ([]:A list) n ys = ys) /\
   (list_LUPDATE (CONS x xs) n ys = list_LUPDATE xs (n + 1) (LUPDATE x n ys))`;;

let list_LUPDATE_ind = cake_ind "list_LUPDATE";;

(* HOL4 line 569 *)
let LENGTH_list_LUPDATE = prove
 (`!(xs:A list) n ys. LENGTH (list_LUPDATE xs n ys) = LENGTH ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_LUPDATE_def; LENGTH_LUPDATE]);;

let _ = cake_add_simps [LENGTH_list_LUPDATE];;

(* HOL4 line 575 *)
let TAKE_list_LUPDATE = prove
 (`!(ys:A list) xs n i. TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE n xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_LUPDATE_def; TAKE_LUPDATE]);;

let _ = cake_add_simps [TAKE_list_LUPDATE];;

(* HOL4 line 581 *)
let LLOOKUP_list_LUPDATE_IGNORE = prove
 (`!(xs:A list) i n ys.
     i + LENGTH xs <= n ==> oEL n (list_LUPDATE xs i ys) = oEL n ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_LUPDATE_def; LENGTH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(i + 1) + LENGTH (t:A list) <= n /\ ~(i = n)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[oEL_LUPDATE]]);;

(* HOL4 line 591 *)
let DROP_list_LUPDATE = prove
 (`!(ys:A list) n m xs.
     n <= m
     ==> DROP n (list_LUPDATE ys m xs) = list_LUPDATE ys (m - n) (DROP n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_LUPDATE_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= m + 1 /\ (m + 1) - n = (m - n) + 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[DROP_LUPDATE_lemma1]]);;

(* HOL4 line 604 *)
let DROP_list_LUPDATE_IGNORE = prove
 (`!(xs:A list) i ys n.
     LENGTH xs + i <= n ==> DROP n (list_LUPDATE xs i ys) = DROP n ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_LUPDATE_def; LENGTH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (t:A list) + (i + 1) <= n /\ i < n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[DROP_LUPDATE_lemma2]]);;

(* HOL4 line 614 *)
let list_LUPDATE_NIL = prove
 (`!(xs:A list) i. list_LUPDATE xs i [] = []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_LUPDATE_def; LUPDATE_def]);;

let _ = cake_add_simps [list_LUPDATE_NIL];;

(* HOL4 line 620 *)
let LUPDATE_TAKE_LEMMA = prove
 (`!(xs:A list) n w. LUPDATE w n xs = APPEND (TAKE n xs) (LUPDATE w 0 (DROP n xs))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LUPDATE_def; RICHAUX_TAKE_CLAUSES; RICHAUX_DROP_CLAUSES; APPEND] THEN
  X_GEN_TAC `n:num` THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  ASM_REWRITE_TAC[LUPDATE_def; RICHAUX_TAKE_CLAUSES; RICHAUX_DROP_CLAUSES; APPEND]);;

(* HOL4 line 626 *)
let list_LUPDATE_TAKE_DROP = prove
 (`!xs (ys:A list) n.
     list_LUPDATE xs n ys = APPEND (TAKE n ys) (list_LUPDATE xs 0 (DROP n ys))`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[list_LUPDATE_def; RICHAUX_TAKE_DROP]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[list_LUPDATE_def] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SIMP_TAC[DROP_LUPDATE_lemma2; ARITH_RULE `n < n + 1 /\ 0 < 1`; DROP_DROP_T] THEN
  REWRITE_TAC[APPEND_ASSOC; ARITH_RULE `1 + n = n + 1`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUPDATE_TAKE_LEMMA] THEN
  REWRITE_TAC[TAKE_APPEND; TAKE_TAKE_MIN; ARITH_RULE `MIN n (n + 1) = n`;
              LENGTH_TAKE_EQ_MIN] THEN
  AP_TERM_TAC THEN ASM_CASES_TAC `n <= LENGTH (ys:A list)` THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `DROP n (ys:A list) = []` SUBST1_TAC THENL
     [REWRITE_TAC[DROP_NIL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[LUPDATE_def; RICHAUX_TAKE_NIL]]]);;

(* HOL4 line 639 *)
let list_LUPDATE_0_CONS = prove
 (`!(xs:A list) x ys y.
     list_LUPDATE (CONS x xs) 0 (CONS y ys) = CONS x (list_LUPDATE xs 0 ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_LUPDATE_def; LUPDATE_def; ADD_CLAUSES] THEN
  GEN_REWRITE_TAC LAND_CONV [list_LUPDATE_TAKE_DROP] THEN
  REWRITE_TAC[num_CONV `1`; RICHAUX_TAKE_CLAUSES; RICHAUX_DROP_CLAUSES; APPEND]);;

let _ = cake_add_simps [list_LUPDATE_0_CONS];;

(* HOL4 line 646 *)
let list_LUPDATE_APPEND = prove
 (`!(xs:A list) ys zs.
     LENGTH xs = LENGTH ys ==> list_LUPDATE xs 0 (APPEND ys zs) = APPEND xs zs`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:A list` THEN
  STRUCT_CASES_TAC(ISPEC `ys:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; GSYM NOT_SUC; SUC_INJ; list_LUPDATE_0_CONS] THEN
  ASM_SIMP_TAC[list_LUPDATE_def]);;

(* HOL4 line 655 *)
let DIV_ADD_1 = prove
 (`!d m. 0 < d ==> m DIV d + 1 = (m + d) DIV d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `m:num`; `d:num`] (el 2 (CONJUNCTS DIV_MULT_ADD))) THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ARITH_RULE `0 < d ==> ~(d = 0)`]);;

(* HOL4 line 663 *)
let LENGTH_word_list_lemma = prove
 (`!xs d.
     0 < d
     ==> LENGTH (word_to_stack_word_list xs d:(A word)list) = (LENGTH xs - 1) DIV d + 1`,
  MATCH_MP_TAC word_to_stack_word_list_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[word_to_stack_word_list_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = x + 1 <=> x = 0`] THEN
    MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[LENGTH; LENGTH_DROP] THEN
  ASM_SIMP_TAC[DIV_ADD_1; ARITH_RULE `SUC (x + 1) = y + 1 <=> y = x + 1`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 679 *)
let LENGTH_word_list = prove
 (`!xs d.
     LENGTH (word_to_stack_word_list xs d:(A word)list) =
     if d = 0 then 1 else (LENGTH xs - 1) DIV d + 1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ONCE_REWRITE_TAC[word_to_stack_word_list_def] THEN ASM_REWRITE_TAC[LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC LENGTH_word_list_lemma THEN ASM_ARITH_TAC]);;

(* HOL4 line 689 *)
let list_rearrange_I = prove
 (`list_rearrange I = (I:A list->A list)`,
  REWRITE_TAC[FUN_EQ_THM; list_rearrange_def; I_PERMUTES; I_THM; GENLIST_ID]);;

(* HOL4 line 700 (the frames are of any type (B)stack_frame, as in HOL4;    *)
(* HOL4's catch-all clause abs_stack bitmaps _ _ _ = NONE is written as its  *)
(* three completed clauses, as HOL4's TFL stores them: the kit's completion  *)
(* takes 20 min; the termination measure is the length of the frames)      *)
let abs_stack_def = cake_def_wf
  `measure (\x:(A word)list#((B)stack_frame)list#((A)word_loc)list#num list.
              LENGTH (FST (SND x)))`
  (REPEAT STRIP_TAC THEN REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN ARITH_TAC)
  `(abs_stack (bitmaps:(A word)list) [] stack [] =
      if stack = [wl_Word (word 0:A word)] then SOME [] else NONE) /\
   (abs_stack bitmaps (CONS (StackFrame n l0 l NONE:(B)stack_frame) xs) (CONS w stack)
              (CONS len lens) =
      match full_read_bitmap bitmaps w with
        NONE -> NONE
      | SOME bits ->
          if ~(LENGTH bits = len) then NONE else
          if LENGTH stack < len then NONE else
            let frame = TAKE len stack in
            let rest = DROP len stack in
              match abs_stack bitmaps xs rest lens with
                NONE -> NONE
              | SOME ys -> SOME (CONS (NONE,bits,frame) ys)) /\
   (abs_stack bitmaps (CONS (StackFrame n l0 l (SOME h)) xs) (CONS w stack)
              (CONS len lens) =
      if ~(w = wl_Word (word 1)) then NONE
      else
        (match stack with
           CONS loc (CONS hv (CONS w stack)) ->
             (match full_read_bitmap bitmaps w with
                NONE -> NONE
              | SOME bits ->
                  if ~(LENGTH bits = len) then NONE else
                  if LENGTH stack < len then NONE else
                    let frame = TAKE len stack in
                    let rest = DROP len stack in
                      match abs_stack bitmaps xs rest lens with
                        NONE -> NONE
                      | SOME ys -> SOME (CONS (SOME (loc,hv),bits,frame) ys))
         | _ -> NONE)) /\
   (abs_stack bitmaps [] stack (CONS len lens) = NONE) /\
   (abs_stack bitmaps (CONS x xs) [] lens = NONE) /\
   (abs_stack bitmaps (CONS x xs) (CONS w stack) [] = NONE)`;;

(* HOL4 line 742: val abs_stack_ind = theorem "abs_stack_ind" *)
let abs_stack_ind = cake_ind "abs_stack";;

(* HOL4 line 744 *)
let read_bitmap_append_extra = prove
 (`!(l1:(A word)list) l2 bits.
     read_bitmap l1 = SOME bits ==> read_bitmap (APPEND l1 l2) = SOME bits`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[read_bitmap_def; APPEND] THEN SIMP[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 757 *)
let full_read_bitmap_append = prove
 (`!(bitmaps:(A word)list) (w:(B)word_loc) bits more_bitmaps.
     full_read_bitmap bitmaps w = SOME bits
     ==> full_read_bitmap (APPEND bitmaps more_bitmaps) w = SOME bits`,
  REPEAT GEN_TAC THEN CASES_ON `w:(B)word_loc` THEN
  REWRITE_TAC[full_read_bitmap_def; GSYM NOT_SOME_NONE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_APPEND; GSYM NOT_SOME_NONE] THEN
  MESON_TAC[read_bitmap_append_extra]);;

(* HOL4 line 768 *)
let abs_stack_bitmaps_prefix = prove
 (`!(bitmaps:(A word)list) (frames:((B)stack_frame)list) stack lens more_bitmaps result.
     abs_stack bitmaps frames stack lens = SOME result
     ==> abs_stack (APPEND bitmaps more_bitmaps) frames stack lens = SOME result`,
  MATCH_MP_TAC abs_stack_ind THEN REWRITE_TAC[abs_stack_def] THEN REPEAT STRIP_TAC THEN
  GVS(all_case_eqs()) THEN IMP_RES_TAC full_read_bitmap_append THEN RES_TAC THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 782 *)
let MAP_FST_def = cake_def
  `MAP_FST (f:A->B) (xs:(A#C)list) = MAP (\(x,y). (f x,y)) xs`;;

(* HOL4 line 786 *)
let MAP_SND_MAP_FST = prove
 (`!(xs:(A#C)list) (f:A->B). MAP SND (MAP_FST f xs) = MAP SND xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP_FST_def; MAP] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[MAP_FST_def]) THEN
  SPEC_TAC(`h:A#C`,`h:A#C`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]);;

(* HOL4 line 792 *)
let adjust_names_def = cake_def
  `adjust_names n = n DIV 2`;;

(* HOL4 line 797 *)
let handler_val_def = cake_def
  `(handler_val ([]:(A option#B#C list)list) = 1) /\
   (handler_val (CONS (NONE,_,frame) stack) = 1 + LENGTH frame + handler_val stack) /\
   (handler_val (CONS (SOME _,_,frame) stack) = 4 + LENGTH frame + handler_val stack)`;;

let handler_val_ind = cake_ind "handler_val";;

(* HOL4 line 809 *)
let is_handler_frame_def = cake_def
  `(is_handler_frame (StackFrame n l0 l NONE:(A)stack_frame) <=> F) /\
   (is_handler_frame (_:(A)stack_frame) <=> T)`;;

(* HOL4 line 815 (HOL4's catch-all clause stack_rel_aux k len _ _ = F is   *)
(* written as its four completed clauses, as HOL4's TFL stores them: the    *)
(* kit's completion of a catch-all over two list arguments takes too long) *)
let stack_rel_aux_def = cake_def
  `(stack_rel_aux k len ([]:((A)stack_frame)list)
      ([]:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list) <=> T) /\
   (stack_rel_aux k len (CONS (StackFrame n l0 l NONE) xs)
      (CONS (NONE,bits,frame) stack) <=>
      (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE
         ==> adjust_names n < k + LENGTH bits /\
             oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F /\
             ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) /\
      the (LENGTH frame + 1) n = LENGTH frame + 1 /\
      stack_rel_aux k len xs stack) /\
   (stack_rel_aux k len (CONS (StackFrame n l0 l (SOME (h1,l1,l2))) xs)
      (CONS (SOME (loc,hv),bits,frame) stack) <=>
      (h1 < LENGTH stack /\
       is_handler_frame (EL (LENGTH stack - (h1 + 1)) xs)
       ==> hv = wl_Word (word (len - handler_val (LASTN (h1 + 1) stack)))) /\
      loc = wl_Loc l1 l2 /\
      (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE
         ==> adjust_names n < k + LENGTH bits /\
             oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F /\
             ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) /\
      the (LENGTH frame + 1) n = LENGTH frame + 1 /\
      stack_rel_aux k len xs stack) /\
   (stack_rel_aux k len [] (CONS sf stack) <=> F) /\
   (stack_rel_aux k len (CONS x xs) [] <=> F) /\
   (stack_rel_aux k len (CONS (StackFrame n l0 l NONE) xs) (CONS (SOME p,bits,frame) stack) <=>
      F) /\
   (stack_rel_aux k len (CONS (StackFrame n l0 l (SOME h)) xs) (CONS (NONE,bits,frame) stack) <=>
      F)`;;

let stack_rel_aux_ind = cake_ind "stack_rel_aux";;

(* HOL4 line 842 *)
let sorted_env_def = cake_def
  `sorted_env (StackFrame n l0 l _:(A)stack_frame) <=> SORTED (\x y. FST x > FST y) l`;;

(* HOL4 line 846 (the word type of t_handler is free, as in HOL4) *)
let word_to_stackProof_stack_rel_def = cake_def
  `word_to_stackProof_stack_rel k s_handler (s_stack:((A)stack_frame)list)
     (t_handler:((B)word_loc)option)
     t_rest_of_stack t_stack_length (t_bitmaps:(A word)list) lens <=>
     ALL sorted_env s_stack /\
     ?stack.
       abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack /\
       (s_handler < LENGTH s_stack /\
        is_handler_frame (EL (LENGTH s_stack - (s_handler + 1)) s_stack)
        ==> t_handler =
            SOME (wl_Word (word (t_stack_length -
                                 handler_val (LASTN (s_handler + 1) stack))))) /\
       stack_rel_aux k t_stack_length s_stack stack`;;

(* HOL4 line 866 *)
let stack_size_rel_def = cake_def
  `stack_size_rel f s_locals_size s_stack_limit s_stack_max
     (s_stack:((A)stack_frame)list) (t_stack:B list) t_stack_space (extra:num) <=>
     (~(f = 0) ==> the f s_locals_size = f) /\
     s_stack_limit = LENGTH t_stack /\
     !sm. s_stack_max = SOME sm
          ==> ((LENGTH t_stack - t_stack_space) - f) - extra <= sm /\
              IS_SOME s_locals_size /\
              (?ss. wl_stack_size s_stack = SOME ss /\
                    ss = ((LENGTH t_stack - t_stack_space) - f) - extra)`;;

(* HOL4 line 878 *)
let stack_size_rel_iff = prove
 (`!f s_locals_size s_stack_limit s_stack_max (s_stack:((A)stack_frame)list)
     (t_stack:B list) t_stack_space extra.
     stack_size_rel f s_locals_size s_stack_limit s_stack_max s_stack
       t_stack t_stack_space extra <=>
     (~(f = 0) ==> the f s_locals_size = f) /\
     s_stack_limit = LENGTH t_stack /\
     ((LENGTH t_stack - t_stack_space) - f) - extra <=
       the (((LENGTH t_stack - t_stack_space) - f) - extra) s_stack_max /\
     (IS_SOME s_stack_max ==> IS_SOME (wl_stack_size s_stack)) /\
     (IS_SOME s_stack_max ==> IS_SOME s_locals_size) /\
     (IS_SOME s_stack_max
      ==> the (((LENGTH t_stack - t_stack_space) - f) - extra) (wl_stack_size s_stack) =
          ((LENGTH t_stack - t_stack_space) - f) - extra)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_size_rel_def] THEN
  STRUCT_CASES_TAC(ISPEC `s_stack_max:num option` (cases "option")) THEN
  REWRITE_TAC[the_def; IS_SOME_DEF; NOT_SOME_NONE; GSYM NOT_SOME_NONE; option_INJ; LE_REFL;
              FORALL_UNWIND_THM1] THEN
  STRUCT_CASES_TAC(ISPEC `wl_stack_size (s_stack:((A)stack_frame)list)` (cases "option")) THEN
  REWRITE_TAC[the_def; IS_SOME_DEF; NOT_SOME_NONE; GSYM NOT_SOME_NONE; option_INJ;
              UNWIND_THM1] THEN
  MESON_TAC[]);;

(* HOL4 line 895.  HOL4 t.store \\ Handler is fdomsub (stack_state_store t)  *)
(* Handler; (<>) a is \x. ~(a = x); store_consts_stub_location is wordLang's *)
(* (wl_store_consts_stub_location, as in word_to_stack.ml).                  *)
let word_to_stackProof_state_rel_def = cake_def
  `word_to_stackProof_state_rel (ac:(A)asm_config) k f f' (s:(A,num#C,FFI)wl_state)
     (t:(A,C,FFI)stack_state) lens extra <=>
     wl_state_clock s = stack_state_clock t /\
     wl_state_gc_fun s = stack_state_gc_fun t /\
     wl_state_permute s = K I /\
     stack_state_ffi t = wl_state_ffi s /\ stack_state_use_stack t /\
     stack_state_use_store t /\ stack_state_use_alloc t /\
     stack_state_memory t = wl_state_memory s /\
     stack_state_mdomain t = wl_state_mdomain s /\ 4 < k /\
     stack_state_sh_mdomain t = wl_state_sh_mdomain s /\
     wl_state_store s = fdomsub (stack_state_store t) Handler /\
     gc_fun_ok (stack_state_gc_fun t) /\ wl_state_termdep s = 0 /\
     stack_state_be t = wl_state_be s /\ stack_state_ffi t = wl_state_ffi s /\
     Handler IN FDOM (stack_state_store t) /\
     stack_state_fp_regs t = wl_state_fp_regs s /\
     stack_state_data_buffer t = wl_state_data_buffer s /\
     stack_state_code_buffer t = wl_state_code_buffer s /\
     wl_state_compile s =
       (\(bm0,cfg) progs.
          let (progs,fs,bm) = compile_word_to_stack ac F k progs (Nil,bm0) in
          OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND bm,cfg)))
            (stack_state_compile t cfg progs)) /\
     stack_state_compile_oracle t =
       (\n. let ((bm0,cfg),progs) = wl_state_compile_oracle s n in
            let (progs,fs,bm) = compile_word_to_stack ac F k progs (Nil,bm0) in
            (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = wl_state_compile_oracle s n in
          ALL (post_alloc_conventions k o SND o SND) progs /\
          ALL (flat_exp_conventions o SND o SND) progs /\
          ALL ((\x. ~(raise_stub_location = x)) o FST) progs /\
          ALL ((\x. ~(wl_store_consts_stub_location = x)) o FST) progs /\
          (n = 0 ==> bm0 = LENGTH (stack_state_bitmaps t))) /\
     domain (stack_state_code t) =
       raise_stub_location INSERT wl_store_consts_stub_location INSERT
       domain (wl_state_code s) /\
     (!n word_prog arg_count.
        lookup n (wl_state_code s) = SOME (arg_count,word_prog)
        ==> post_alloc_conventions k word_prog /\
            flat_exp_conventions word_prog /\
            ?bs i bs2 i2 f stack_prog.
              word_to_stack_compile_prog ac F word_prog arg_count k (bs,i) =
                (stack_prog,f,(bs2,i2)) /\
              LENGTH (append bs) <= i /\
              i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
              isPREFIX (append bs2)
                (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
              lookup n (stack_state_code t) = SOME stack_prog /\
              the f (lookup n (wl_state_stack_size s)) = f) /\
     lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
     lookup wl_store_consts_stub_location (stack_state_code t) =
       SOME (store_consts_stub k) /\
     good_dimindex (:A) /\ 8 <= dimindex (:A) /\
     LENGTH (stack_state_bitmaps t) +
       LENGTH (buffer_buffer (wl_state_data_buffer s)) +
       buffer_space_left (wl_state_data_buffer s) + 1 < dimword (:A) /\
     1 <= LENGTH (stack_state_bitmaps t) /\ HD (stack_state_bitmaps t) = word 4 /\
     stack_state_stack_space t + f <= LENGTH (stack_state_stack t) /\
     LENGTH (stack_state_stack t) < dimword (:A) /\
     (if f' = 0 then f = 0 else f = f' + 1) /\
     wf (wl_state_locals s) /\
     stack_size_rel f (wl_state_locals_size s) (wl_state_stack_limit s)
       (wl_state_stack_max s) (wl_state_stack s)
       (stack_state_stack t) (stack_state_stack_space t) extra /\
     let stack = DROP (stack_state_stack_space t + extra) (stack_state_stack t) in
     let current_frame = TAKE f stack in
     let rest_of_stack = DROP f stack in
       word_to_stackProof_stack_rel k (wl_state_handler s) (wl_state_stack s)
         (FLOOKUP (stack_state_store t) Handler)
         rest_of_stack (LENGTH (stack_state_stack t)) (stack_state_bitmaps t) lens /\
       (!n v.
          lookup n (wl_state_locals s) = SOME v
          ==> EVEN n /\
              if n DIV 2 < k then FLOOKUP (stack_state_regs t) (n DIV 2) = SOME v
              else oEL ((f - 1) - (n DIV 2 - k)) current_frame = SOME v /\
                   n DIV 2 < k + f')`;;

(* HOL4 line 960 (rebound at HOL4 line 3286) *)
let evaluate_SeqStackFree = prove
 (`!(t:(A,C,FFI)stack_state) f p.
     stack_state_use_stack t /\ stack_state_stack_space t <= LENGTH (stack_state_stack t)
     ==> stack_evaluate (SeqStackFree f p,t) =
         stack_evaluate (stack_Seq (StackFree f) p,t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SeqStackFree_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [stack_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
  ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `a <= b ==> ~(b < a)`] THEN
  SUBGOAL_THEN
   `stack_state_stack_space_fupd (K (stack_state_stack_space t)) t =
    (t:(A,C,FFI)stack_state)` SUBST1_TAC THENL
   [SIMP[stack_state_component_equality]; SIMP[]]);;

(* HOL4 line 974: val convs_def = LIST_CONJ [post_alloc_conventions_def,     *)
(* call_arg_convention_def, flat_exp_conventions_def, every_var_def,         *)
(* every_var_imm_def, every_stack_var_def, every_name_def] (a derived        *)
(* theorem, made here with the wordConvs/wordLang names)                     *)
let word_to_stackProof_convs_def = end_itlist CONJ
  [post_alloc_conventions_def; call_arg_convention_def; flat_exp_conventions_def;
   wl_every_var_def; every_var_imm_def; every_stack_var_def; every_name_def];;

(* HOL4 line 995: MATCH_MP DROP_list_LUPDATE (SPEC_ALL LESS_EQ_REFL)         *)
(* |> SIMP_RULE std_ss []                                                    *)
let DROP_list_LUPDATE_lemma = prove
 (`!(ys:A list) n xs. DROP n (list_LUPDATE ys n xs) = list_LUPDATE ys 0 (DROP n xs)`,
  SIMP_TAC[DROP_list_LUPDATE; LE_REFL; SUB_REFL]);;

(* HOL4 line 998 *)
let bits_to_word_bit = prove
 (`!bs i.
     i < dimindex (:A) /\ i < LENGTH bs ==> (bit i (bits_to_word bs:A word) <=> EL i bs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  BOOL_CASES_TAC `h:bool` THEN
  REWRITE_TAC[bits_to_word_def; EL; HD; TL; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_1;
              LT_SUC; NOT_SUC; ARITH_RULE `~(1 <= 0) /\ 1 <= SUC j /\ SUC j - 1 = j`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 1008 *)
let bits_to_word_miss = prove
 (`!bs i. i < dimindex (:A) /\ LENGTH bs <= i ==> ~(bit i (bits_to_word bs:A word))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; bits_to_word_def; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
  BOOL_CASES_TAC `h:bool` THEN
  REWRITE_TAC[bits_to_word_def; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_1; NOT_SUC;
              ARITH_RULE `1 <= SUC j /\ SUC j - 1 = j`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 1020 *)
let bits_to_word_SNOC = prove
 (`!bs b.
     bits_to_word (SNOC b bs):A word =
     word_or (word_shl (if b then word 1 else word 0) (LENGTH bs)) (bits_to_word bs)`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
    REWRITE_TAC[SNOC; bits_to_word_def; LENGTH; WORD_SHL_0; WORD_OR_0; WORD_SHL_ZERO];
    GEN_TAC THEN BOOL_CASES_TAC `h:bool` THEN
    ASM_REWRITE_TAC[SNOC; bits_to_word_def; LENGTH; WORD_SHL_OR; WORD_SHL_COMPOSE; ADD1;
                    WORD_OR_ASSOC]]);;

let W2SP1AUX_bits_to_word_T_NZ = prove
 (`!bs. LENGTH bs < dimindex(:A) ==> ~(bits_to_word (APPEND bs [T]):A word = word 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`APPEND bs [T]`; `LENGTH (bs:bool list)`] bits_to_word_bit) THEN
  ASM_SIMP_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD; BIT_WORD_0;
               ARITH_RULE `n < n + SUC 0`]);;

(* HOL4 line 1032 *)
let list_LUPDATE_write_bitmap_NOT_NIL = prove
 (`!(names:1 spt) k f' xs.
     8 <= dimindex (:A)
     ==> ~(list_LUPDATE (MAP wl_Word (write_bitmap names k f')) 0 xs =
           [wl_Word (word 0:A word)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[list_LUPDATE_NIL; NOT_CONS_NIL] THEN
  REWRITE_TAC[write_bitmap_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[word_to_stack_word_list_def] THEN
  SUBGOAL_THEN `~(dimindex(:A) - 1 = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[MAP; list_LUPDATE_0_CONS; CONS_11; injectivity "word_loc"; DE_MORGAN_THM] THEN
  DISJ1_TAC THEN MATCH_MP_TAC W2SP1AUX_bits_to_word_T_NZ THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_LIST_OF_SEQ; LENGTH_TAKE_EQ_MIN] THEN
  ASM_ARITH_TAC);;

let W2SP1AUX_ushr_or_shl = prove
 (`!(x:A word). ~(word_msb x)
     ==> word_ushr (word_or (word_shl x 1) (word 1)) 1 = x /\
         word_ushr (word_shl x 1) 1 = x`,
  REWRITE_TAC[word_msb_def; WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OR; BIT_WORD_SHL;
              BIT_WORD_1] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= i + 1 /\ (i + 1) - 1 = i /\ ~(i + 1 = 0)`] THEN
  ASM_CASES_TAC `i + 1 < dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `i = dimindex(:A) - 1` SUBST_ALL_TAC THENL
    [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]));;

(* HOL4 line 1047 *)
let bit_length_bits_to_word = prove
 (`!qs. LENGTH qs + 1 < dimindex (:A)
        ==> bit_length (bits_to_word (APPEND qs [T]):A word) = LENGTH qs + 1`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; bits_to_word_def; WORD_SHL_0; WORD_OR_0; LENGTH] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[bit_length_def] THEN REWRITE_TAC[WORD_NE_10] THEN
    SUBGOAL_THEN `word_ushr (word 1) 1 = (word 0:A word)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_1; BIT_WORD_0] THEN ARITH_TAC;
      ONCE_REWRITE_TAC[bit_length_def] THEN REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(bits_to_word (APPEND (CONS h t) [T]) = (word 0:A word))` MP_TAC THENL
   [MATCH_MP_TAC W2SP1AUX_bits_to_word_T_NZ THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word_msb (bits_to_word (APPEND t [T]):A word))` ASSUME_TAC THENL
   [REWRITE_TAC[word_msb_def] THEN MATCH_MP_TAC bits_to_word_miss THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[APPEND] THEN DISCH_TAC THEN ONCE_REWRITE_TAC[bit_length_def] THEN
  ASM_REWRITE_TAC[] THEN BOOL_CASES_TAC `h:bool` THEN
  ASM_SIMP_TAC[bits_to_word_def; W2SP1AUX_ushr_or_shl] THEN ARITH_TAC);;

(* HOL4 line 1074 *)
let bits_to_word_bitstring_reverse = prove
 (`!xs. bits_to_word xs:A word = v2w (REVERSE xs)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; testbit; LENGTH_REVERSE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < LENGTH (xs:bool list)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[bits_to_word_bit; EL_REVERSE; ARITH_RULE
     `i < n ==> (n - 1) - i < n /\ PRE (n - ((n - 1) - i)) = i`];
    MATCH_MP_TAC bits_to_word_miss THEN ASM_ARITH_TAC]);;

(* HOL4 line 1088 *)
let GENLIST_bits_to_word_alt = prove
 (`!xs ys.
     LENGTH (APPEND xs ys) <= dimindex (:A)
     ==> list_of_seq (\i. bit i (bits_to_word (APPEND xs ys):A word)) (LENGTH xs) = xs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH_APPEND] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < dimindex(:A) /\ i < LENGTH (APPEND xs ys:bool list)` MP_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP bits_to_word_bit th]) THEN
  ASM_SIMP_TAC[EL_APPEND1]);;

(* HOL4 line 1096 *)
let GENLIST_bits_to_word = prove
 (`!qs'.
     LENGTH qs' + 1 < dimindex (:A)
     ==> list_of_seq (\i. bit i (bits_to_word (APPEND qs' [T]):A word)) (LENGTH qs') = qs'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GENLIST_bits_to_word_alt THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC);;

(* HOL4 line 1103 *)
let read_bitmap_word_list = prove
 (`!qs (xs:(A word)list).
     8 <= dimindex (:A)
     ==> read_bitmap
           (APPEND (word_to_stack_word_list (APPEND qs [T]) (dimindex (:A) - 1)) xs) =
         SOME qs`,
  SUBGOAL_THEN
   `!n qs (xs:(A word)list).
      LENGTH qs = n /\ 8 <= dimindex (:A)
      ==> read_bitmap
            (APPEND (word_to_stack_word_list (APPEND qs [T]) (dimindex (:A) - 1)) xs) =
          SOME qs`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[word_to_stack_word_list_def] THEN
  SUBGOAL_THEN `~(dimindex(:A) - 1 = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[APPEND; read_bitmap_def] THEN
    SUBGOAL_THEN `~word_msb (bits_to_word (APPEND qs [T]):A word)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[word_msb_def] THEN MATCH_MP_TAC bits_to_word_miss THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (qs:bool list) + 1 < dimindex(:A)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP bit_length_bits_to_word th; ADD_SUB;
                                      MATCH_MP GENLIST_bits_to_word th]);
    ALL_TAC] THEN
  ABBREV_TAC `d = dimindex(:A) - 1` THEN
  SUBGOAL_THEN `d <= LENGTH (qs:bool list) /\ 0 < d /\ d + 1 = dimindex(:A)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[TAKE_APPEND1; DROP_APPEND1; APPEND] THEN
  REWRITE_TAC[read_bitmap_def] THEN
  SUBGOAL_THEN `LENGTH (TAKE d (qs:bool list)) = d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LENGTH_TAKE]; ALL_TAC] THEN
  SUBGOAL_THEN `word_msb (bits_to_word (APPEND (TAKE d qs) [T]):A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[word_msb_def] THEN
    SUBGOAL_THEN `dimindex(:A) - 1 < dimindex(:A) /\
                  dimindex(:A) - 1 < LENGTH (APPEND (TAKE d qs) [T])` MP_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP bits_to_word_bit th]) THEN
    ASM_REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
    SUBGOAL_THEN `dimindex(:A) - 1 = d` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT_REFL; SUB_REFL; EL; HD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (DROP d (qs:bool list))`) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`DROP d (qs:bool list)`; `xs:(A word)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[] THEN
  MP_TAC(ISPECL [`TAKE d (qs:bool list)`; `[T]`] GENLIST_bits_to_word_alt) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TAKE_DROP]);;

(* HOL4 line 1150 *)
let APPEND_LEMMA = prove
 (`!n1 n2 n3 (xs:A list).
     n1 + n2 + n3 <= LENGTH xs
     ==> ?xs2 xs3. DROP n1 xs = APPEND xs2 xs3 /\ n2 = LENGTH xs2`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE n2 (DROP n1 (xs:A list))`; `DROP n2 (DROP n1 (xs:A list))`] THEN
  REWRITE_TAC[TAKE_DROP] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LENGTH_TAKE THEN
  REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC);;

(* HOL4 line 1165 *)
let read_bitmap_write_bitmap = prove
 (`!(names:1 spt) k f'.
     8 <= dimindex (:A)
     ==> read_bitmap (write_bitmap names k f':(A word)list) =
         SOME (list_of_seq
                 (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList names)))
                 f')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[write_bitmap_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM APPEND_NIL] THEN
  MATCH_MP_TAC read_bitmap_word_list THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1176 *)
let read_bitmap_insert_bitmap = prove
 (`!bs n bs' n' i (cur:(A word)list) bm.
     i < dimword (:A) /\
     IS_SOME (read_bitmap bm) /\
     n = LENGTH cur + LENGTH (append bs) /\
     insert_bitmap bm (bs,n) = ((bs',n'),i)
     ==> read_bitmap (DROP (i MOD dimword (:A)) (APPEND cur (append bs'))) =
         read_bitmap bm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[insert_bitmap_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  ASM_SIMP_TAC[MOD_LT; append_thm; APPEND_ASSOC] THEN
  REWRITE_TAC[GSYM LENGTH_APPEND; DROP_LENGTH_APPEND]);;

(* HOL4 line 1188 (the frames are of any type, as in HOL4) *)
let abs_stack_IMP_LENGTH = prove
 (`!(bs:(A word)list) (wstack:((B)stack_frame)list) sstack lens stack.
     abs_stack bs wstack sstack lens = SOME stack
     ==> LENGTH stack = LENGTH wstack /\ LENGTH lens = LENGTH wstack`,
  MATCH_MP_TAC abs_stack_ind THEN REWRITE_TAC[abs_stack_def] THEN REPEAT STRIP_TAC THEN
  GVS(all_case_eqs()) THEN RES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let W2SP1AUX_transitive_FST_GT = prove
 (`transitive (\(x:num#A) (y:num#A). FST x > FST y)`,
  REWRITE_TAC[transitive_def] THEN ARITH_TAC);;

(* HOL4 line 1197 *)
let SORTED_FST_LESS_IMP = prove
 (`!(xs:(num#A)list) x.
     SORTED (\x y. FST x > FST y) (CONS x xs)
     ==> SORTED (\x y. FST x > FST y) xs /\ ~(MEM x xs) /\
         (!y. MEM y xs ==> FST x > FST y)`,
  REPEAT GEN_TAC THEN SIMP_TAC[SORTED_EQ; W2SP1AUX_transitive_FST_GT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num#A`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 1208 *)
let SORTED_IMP_EQ_LISTS = prove
 (`!(xs:(num#A)list) ys.
     SORTED (\x y. FST x > FST y) ys /\
     SORTED (\x y. FST x > FST y) xs /\
     (!x. MEM x ys <=> MEM x xs)
     ==> xs = ys`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(num#A)list` THEN
  STRUCT_CASES_TAC(ISPEC `ys:(num#A)list` list_CASES) THEN
  REWRITE_TAC[MEM; NOT_CONS_NIL] THENL [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(num#A)list`; `h:num#A`] SORTED_FST_LESS_IMP) THEN
  MP_TAC(ISPECL [`t':(num#A)list`; `h':num#A`] SORTED_FST_LESS_IMP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h:num#A = h'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `~(a > b /\ b > a:num)`]; ALL_TAC] THEN
  REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 1234 *)
let transitive_key_val_compare = prove
 (`transitive (key_val_compare:num#(A)word_loc->num#(A)word_loc->bool)`,
  REWRITE_TAC[transitive_def; FORALL_PAIR_THM; key_val_compare_def] THEN
  MAP_EVERY X_GEN_TAC [`a1:num`; `b1:(A)word_loc`; `a2:num`; `b2:(A)word_loc`;
                       `a3:num`; `b3:(A)word_loc`] THEN
  CASES_ON `b1:(A)word_loc` THEN CASES_ON `b2:(A)word_loc` THEN
  CASES_ON `b3:(A)word_loc` THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC THEN
  ASM_MESON_TAC[WORD_LESS_EQ_TRANS]);;

(* HOL4 line 1242 *)
let total_key_val_compare = prove
 (`total (key_val_compare:num#(A)word_loc->num#(A)word_loc->bool)`,
  REWRITE_TAC[total_def; FORALL_PAIR_THM; key_val_compare_def] THEN
  MAP_EVERY X_GEN_TAC [`a1:num`; `b1:(A)word_loc`; `a2:num`; `b2:(A)word_loc`] THEN
  CASES_ON `b1:(A)word_loc` THEN CASES_ON `b2:(A)word_loc` THEN SIMP[] THEN
  TRY ARITH_TAC THEN
  ASM_CASES_TAC `a1:num = a2` THEN ASM_REWRITE_TAC[ARITH_RULE `~(n > n:num)`] THENL
   [REWRITE_TAC[WORD_ILE] THEN INT_ARITH_TAC; ASM_ARITH_TAC]);;

(* HOL4 line 1252 *)
let SORTS_SORT_key_val_compare = prove
 (`SORTS sort (key_val_compare:num#(A)word_loc->num#(A)word_loc->bool)`,
  MATCH_MP_TAC sort_SORTS THEN
  REWRITE_TAC[transitive_key_val_compare; total_key_val_compare]);;

(* HOL4 line 1259: val MEM_SORT = SORTS_SORT_key_val_compare |> SIMP_RULE    *)
(* std_ss [SORTS_DEF] |> SPEC_ALL |> CONJUNCT1 |> MATCH_MP MEM_PERM |> GSYM  *)
(* |> GEN_ALL (a derived theorem)                                            *)
let MEM_SORT = prove
 (`!(l:(num#(A)word_loc)list) x. MEM x (sort key_val_compare l) <=> MEM x l`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `l:(num#(A)word_loc)list`
    (REWRITE_RULE[SORTS_DEF] SORTS_SORT_key_val_compare)) THEN
  MESON_TAC[MEM_PERM]);;

(* HOL4 line 1264 *)
let SORTED_weaken2 = prove
 (`!(ls:A list) R R'.
     SORTED R ls /\ ALL_DISTINCT ls /\
     (!x y. MEM x ls /\ MEM y ls /\ ~(x = y) /\ R x y ==> R' x y)
     ==> SORTED R' ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SORTED_DEF] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h2:A` (X_CHOOSE_THEN `t2:A list` SUBST_ALL_TAC))
    (ISPEC `t:A list` list_CASES) THEN
  REWRITE_TAC[SORTED_DEF; ALL_DISTINCT; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`R:A->A->bool`; `R':A->A->bool`]) THEN
    ASM_REWRITE_TAC[ALL_DISTINCT; MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEM]]);;

(* HOL4 line 1274 *)
let EVEN_GT = prove
 (`!a b. EVEN a /\ EVEN b /\ a > b ==> a DIV 2 > b DIV 2`,
  REWRITE_TAC[EVEN_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* HOL4 line 1285 *)
let transitive_GT = prove
 (`transitive ((>):num->num->bool)`,
  REWRITE_TAC[transitive_def] THEN ARITH_TAC);;

(* HOL4 line 1291 *)
let env_to_list_K_I_IMP = prove
 (`!(env:((A)word_loc)spt) l oracle.
     env_to_list env (K I) = (l,oracle)
     ==> SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[K_THM; list_rearrange_I; I_THM; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[FUN_EQ_THM; K_THM] THEN
  MP_TAC(SPEC `toAList (env:((A)word_loc)spt)`
    (REWRITE_RULE[SORTS_DEF] SORTS_SORT_key_val_compare)) THEN
  SPEC_TAC(`sort key_val_compare (toAList (env:((A)word_loc)spt))`,
           `l:(num#(A)word_loc)list`) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (l:(num#(A)word_loc)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERM_ALL_DISTINCT_MAP; ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  MATCH_MP_TAC SORTED_weaken2 THEN
  EXISTS_TAC `key_val_compare:num#(A)word_loc->num#(A)word_loc->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ALL_DISTINCT_MAP]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; key_val_compare_def] THEN
  MAP_EVERY X_GEN_TAC [`a1:num`; `b1:(A)word_loc`; `a2:num`; `b2:(A)word_loc`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `a1:num = a2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `ALL_DISTINCT (MAP FST (l:(num#(A)word_loc)list))` THEN
    UNDISCH_TAC `MEM (a2:num,b1:(A)word_loc) l` THEN
    UNDISCH_TAC `MEM (a2:num,b2:(A)word_loc) l` THEN
    UNDISCH_TAC `~((a2:num,b1:(A)word_loc) = (a2,b2))` THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM; option_INJ];
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SIMP[] THEN ARITH_TAC]);;

(* HOL4 line 1312 *)
let isPREFIX_DROP = prove
 (`!(s:A list) t i. isPREFIX s t ==> isPREFIX (DROP i s) (DROP i t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_DROP_NIL; isPREFIX_THM] THEN
  X_GEN_TAC `u:A list` THEN X_GEN_TAC `i:num` THEN
  STRUCT_CASES_TAC(ISPEC `u:A list` list_CASES) THEN REWRITE_TAC[isPREFIX_THM] THEN
  STRIP_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_SIMP_TAC[RICHAUX_DROP_CLAUSES; isPREFIX_THM]);;

(* HOL4 line 1322 *)
let LLOOKUP_cons_SUC = prove
 (`!m n (h:A) xs. m < n ==> oEL (n - m) (CONS h xs) = oEL (n - (m + 1)) xs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n - m = SUC (n - (m + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[oEL_def; NOT_SUC; SUC_SUB1]]);;

(* HOL4 line 1332 *)
let EVEN_DIV2_INJ = prove
 (`!x y. EVEN x /\ EVEN y /\ DIV2 x = DIV2 y ==> x = y`,
  REWRITE_TAC[EVEN_EXISTS; DIV2_def] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let W2SP1AUX_SORTED_index_list = prove
 (`!(fr:A list) k. SORTED (\x y. FST x > FST y) (index_list fr k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[index_list_def; SORTED_DEF] THEN GEN_TAC THEN
  SIMP_TAC[SORTED_EQ; W2SP1AUX_transitive_FST_GT] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEM_index_list_LIM) THEN ARITH_TAC);;

let W2SP1AUX_SORTED_FILTER_ZIP = prove
 (`!(il:(num#A)list) (bits:bool list).
     SORTED (\x y. FST x > FST y) il /\ LENGTH il = LENGTH bits
     ==> SORTED (\x y. FST x > FST y) (MAP FST (FILTER SND (ZIP il bits)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sorted_map] THEN
  MATCH_MP_TAC SORTED_FILTER THEN CONJ_TAC THENL
   [MATCH_MP_TAC transitive_inv_image THEN REWRITE_TAC[W2SP1AUX_transitive_FST_GT];
    ONCE_REWRITE_TAC[GSYM sorted_map] THEN ASM_SIMP_TAC[MAP_FST_ZIP]]);;

let W2SP1AUX_MAP_FST_MAP_FST = prove
 (`!(f:A->B) (xs:(A#C)list). MAP FST (MAP_FST f xs) = MAP f (MAP FST xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP_FST_def; MAP] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[MAP_FST_def]) THEN
  SPEC_TAC(`h:A#C`,`h:A#C`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]);;

let W2SP1AUX_SORTED_FST = prove
 (`!l:(num#A)list. SORTED (\x y. FST x > FST y) l <=> SORTED (>) (MAP FST l)`,
  GEN_TAC THEN REWRITE_TAC[sorted_map] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; inv_image]);;

let W2SP1AUX_SORTED_MAP_FST_adjust = prove
 (`!(l:(num#A)list).
     SORTED (\x y. FST x > FST y) l /\ (!p. MEM p l ==> EVEN (FST p))
     ==> SORTED (\x y. FST x > FST y) (MAP_FST adjust_names l)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [W2SP1AUX_SORTED_FST] THEN REWRITE_TAC[W2SP1AUX_MAP_FST_MAP_FST] THEN
  GEN_REWRITE_TAC I [sorted_map] THEN
  MATCH_MP_TAC SORTED_weaken THEN EXISTS_TAC `(>):num->num->bool` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[W2SP1AUX_SORTED_FST]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[inv_image; adjust_names_def; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EVEN_GT THEN ASM_MESON_TAC[]);;

let W2SP1AUX_SORTED_sort_toAList = prove
 (`!(env:((A)word_loc)spt).
     SORTED (\x y. FST x > FST y) (sort key_val_compare (toAList env))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`env:((A)word_loc)spt`; `FST (env_to_list (env:((A)word_loc)spt) (K I))`;
                 `SND (env_to_list (env:((A)word_loc)spt) (K I))`] env_to_list_K_I_IMP) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `SORTED (\x y. FST x > FST y) (FST (env_to_list (env:((A)word_loc)spt) (K I)))` THEN
  REWRITE_TAC[env_to_list_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[K_THM; list_rearrange_I; I_THM; FST]);;

let W2SP1AUX_HAS_CONST c th = can (find_term (fun t -> is_const t && fst(dest_const t) = c)) (concl th);;

let W2SP1AUX_filter_bits_eq = prove
 (`!f' k (fr:((A)word_loc)list) (names1:1 spt) (locals:((A)word_loc)spt).
     LENGTH fr = f' /\
     domain names1 SUBSET domain locals /\
     (!x. x IN domain names1 ==> EVEN x /\ k <= x DIV 2) /\
     (!r v. lookup r locals = SOME v /\ r IN domain names1
            ==> r DIV 2 < k + f' /\ oEL ((f' + k) - (r DIV 2 + 1)) fr = SOME v)
     ==> filter_bitmap
           (list_of_seq (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList names1))) f')
           (index_list fr k) =
         SOME (MAP_FST adjust_names (sort key_val_compare (toAList (inter locals names1))),[])`,
  (REPEAT STRIP_TAC THEN MATCH_MP_TAC IMP_filter_bitmap_EQ_SOME_NIL THEN
   ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_index_list] THEN
   MATCH_MP_TAC SORTED_IMP_EQ_LISTS THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC W2SP1AUX_SORTED_FILTER_ZIP THEN
     ASM_REWRITE_TAC[W2SP1AUX_SORTED_index_list; LENGTH_index_list; LENGTH_LIST_OF_SEQ];
     MATCH_MP_TAC W2SP1AUX_SORTED_MAP_FST_adjust THEN
     REWRITE_TAC[W2SP1AUX_SORTED_sort_toAList; FORALL_PAIR_THM; MEM_SORT; MEM_toAList;
                 FST; lookup_inter_alt] THEN
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[GSYM NOT_SOME_NONE] THEN
     ASM_MESON_TAC[];
     ALL_TAC]) THEN
  (REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`m:num`; `v:(A)word_loc`] THEN
   SUBGOAL_THEN `LENGTH (index_list fr k:(num#(A)word_loc)list) =
     LENGTH (list_of_seq (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList (names1:1 spt)))) f')`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH_index_list; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
   ASM_SIMP_TAC[MAP_FST_def; MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ; MEM_FILTER; MEM_ZIP;
                MEM_SORT; MEM_toAList; lookup_inter_alt; LENGTH_index_list] THEN
   SIMP[]) THEN
  (REWRITE_TAC[adjust_names_def] THEN EQ_TAC) THENL
  [(DISCH_THEN(X_CHOOSE_THEN `b:bool` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC))) THEN
     UNDISCH_TAC `(b:bool) <=> EL j (list_of_seq (\x. ?p1 p2. lookup p1 (names1:1 spt) = SOME p2 /\
                    x = (f' - 1) - (p1 DIV 2 - k)) f')` THEN
     ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
     DISCH_THEN(X_CHOOSE_THEN `r:num` (X_CHOOSE_THEN `u:1` STRIP_ASSUME_TAC)) THEN
     SUBGOAL_THEN `(r:num) IN domain (names1:1 spt)` ASSUME_TAC THENL
      [REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `?v'. lookup r (locals:((A)word_loc)spt) = SOME v'` STRIP_ASSUME_TAC THENL
      [REWRITE_TAC[GSYM domain_lookup] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `v':(A)word_loc`] o check (W2SP1AUX_HAS_CONST "oEL")) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall (concl th) &&
       W2SP1AUX_HAS_CONST "EVEN" th)) THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `j < LENGTH (fr:((A)word_loc)list) /\ j = (f' + k) - (r DIV 2 + 1)`
       STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     UNDISCH_TAC `(m:num,v:(A)word_loc) = EL j (index_list fr k)` THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP EL_index_list2 th]) THEN
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [UNDISCH_TAC `oEL ((f' + k) - (r DIV 2 + 1)) (fr:((A)word_loc)list) = SOME v'` THEN
       FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) && lhs (concl th) = `j:num` &&
         W2SP1AUX_HAS_CONST "DIV" th)) THEN
       ASM_REWRITE_TAC[oEL_THM; option_INJ] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
       ASM_ARITH_TAC]);
   (DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `v:(A)word_loc`] o check (W2SP1AUX_HAS_CONST "oEL")) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall (concl th) &&
     W2SP1AUX_HAS_CONST "EVEN" th)) THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   EXISTS_TAC `T` THEN REWRITE_TAC[] THEN
   EXISTS_TAC `(f' + k) - (r DIV 2 + 1)` THEN
   SUBGOAL_THEN `(f' + k) - (r DIV 2 + 1) < f' /\ (f' + k) - (r DIV 2 + 1) < LENGTH (fr:((A)word_loc)list)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[MATCH_MP EL_index_list2 (ASSUME `(f' + k) - (r DIV 2 + 1) < LENGTH (fr:((A)word_loc)list)`);
               MATCH_MP EL_LIST_OF_SEQ (ASSUME `(f' + k) - (r DIV 2 + 1) < f'`)] THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THENL
    [ASM_ARITH_TAC;
     UNDISCH_TAC `oEL ((f' + k) - (r DIV 2 + 1)) (fr:((A)word_loc)list) = SOME v` THEN
     ASM_REWRITE_TAC[oEL_THM; option_INJ] THEN SIMP_TAC[];
     UNDISCH_TAC `(r:num) IN domain (names1:1 spt)` THEN REWRITE_TAC[domain_lookup] THEN
     DISCH_THEN(X_CHOOSE_TAC `u:1`) THEN MAP_EVERY EXISTS_TAC [`r:num`; `u:1`] THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC])]);;

let W2SP1AUX_stack_evaluate_clause c =
  find (fun th -> let l = lhs(snd(strip_forall(concl th))) in
                  let p = rand l in
                  try fst(dest_const(fst(strip_comb(fst(dest_pair p))))) = c
                  with Failure _ -> false)
       (CONJUNCTS stack_evaluate_def);;

let W2SP1AUX_wLive_eval = prove
 (`!k w (t:(A,C,FFI)stack_state).
     stack_state_use_stack t /\ stack_state_stack_space t < LENGTH (stack_state_stack t)
     ==> stack_evaluate (stack_Seq (stack_Inst (asm_Const k w)) (StackStore k 0),t) =
         (NONE,stack_state_stack_fupd
                 (K (LUPDATE (wl_Word w) (stack_state_stack_space t) (stack_state_stack t)))
                 (stack_set_var k (wl_Word w) t))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "stack_Seq";
              W2SP1AUX_stack_evaluate_clause "stack_Inst"] THEN
  REWRITE_TAC[stack_inst_def; stack_assign_def] THEN SIMP[stack_word_exp_def] THEN
  REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "StackStore"] THEN
  REWRITE_TAC[word_to_stackProof_get_var_set_var] THEN
  REWRITE_TAC[stack_set_var_def] THEN SIMP[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `a < b ==> ~(b <= a)`]);;

let W2SP1AUX_DROP_LUPDATE_CONS = prove
 (`!(l:A list) sp w. sp < LENGTH l ==> DROP sp (LUPDATE w sp l) = CONS w (DROP (sp + 1) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[LUPDATE_def; RICHAUX_DROP_CLAUSES; ADD_CLAUSES; LT_SUC] THENL
   [REWRITE_TAC[num_CONV `1`; RICHAUX_DROP_CLAUSES]; ASM_MESON_TAC[]]);;

let W2SP1AUX_push_env_K_I = prove
 (`!envs (s:(A,C,FFI)wl_state).
     wl_state_permute s = K I
     ==> wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s =
         wl_state_stack_fupd
           (K (CONS (StackFrame (wl_state_locals_size s) (toAList (FST envs))
                       (sort key_val_compare (toAList (SND envs))) NONE) (wl_state_stack s)))
           (wl_state_stack_max_fupd
              (K (OPTION_MAP2 MAX (wl_state_stack_max s)
                    (wl_stack_size (CONS (StackFrame (wl_state_locals_size s) (toAList (FST envs))
                       (sort key_val_compare (toAList (SND envs))) NONE) (wl_state_stack s))))) s)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[K_THM; list_rearrange_I; I_THM] THEN
  SIMP[wl_state_component_equality] THEN REWRITE_TAC[FUN_EQ_THM; K_THM]);;

let W2SP1AUX_state_rel_LUPDATE_sp = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens w.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\ 1 <= f
     ==> word_to_stackProof_state_rel ac k f f' s
           (stack_state_stack_fupd
              (K (LUPDATE w (stack_state_stack_space t) (stack_state_stack t))) t)
           lens 0`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[LENGTH_LUPDATE; ADD_CLAUSES] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[]) THEN
  (SIMP_TAC[DROP_LUPDATE_lemma1; LE_REFL; SUB_REFL] THEN
   ASM_SIMP_TAC[DROP_LUPDATE_lemma2; ARITH_RULE `1 <= f ==> 0 < f`; TAKE_LUPDATE] THEN
   REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[];
     UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
        (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
        (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
     REWRITE_TAC[stack_size_rel_def; LENGTH_LUPDATE];
     MAP_EVERY X_GEN_TAC [`x:num`; `v:(A)word_loc`] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `v:(A)word_loc`] o check (fun th ->
       is_forall (concl th) && W2SP1AUX_HAS_CONST "oEL" th)) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[oEL_LUPDATE] THEN
     SUBGOAL_THEN `~(0 = (f - 1) - (x DIV 2 - k))` (fun th -> ASM_REWRITE_TAC[th]) THEN
     FIRST_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN ASM_ARITH_TAC]));;

let W2SP1AUX_cut_envs_SOME = prove
 (`!names (locals:((A)word_loc)spt) envs.
     cut_envs names locals = SOME envs
     ==> domain (FST names) SUBSET domain locals /\
         domain (SND names) SUBSET domain locals /\
         envs = (inter locals (FST names), inter locals (SND names))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN SIMP[] THEN MESON_TAC[]);;

let W2SP1AUX_stack_size_cons_NONE = prove
 (`!n l0 l (stack:((A)stack_frame)list).
     wl_stack_size (CONS (StackFrame n l0 l NONE) stack) =
     OPTION_MAP2 (+) n (wl_stack_size stack)`,
  REWRITE_TAC[wl_stack_size_def; ITLIST; o_THM; stack_size_frame_def]);;

let W2SP1AUX_wLive_size_rel = prove
 (`!f' ls lim mx (stack:((A)stack_frame)list) (tstack:B list) sp l0 l w.
     stack_size_rel (f' + 1) ls lim mx stack tstack sp 0 /\ sp + f' + 1 <= LENGTH tstack
     ==> stack_size_rel 0 (SOME 0) lim
           (OPTION_MAP2 MAX mx (wl_stack_size (CONS (StackFrame ls l0 l NONE) stack)))
           (CONS (StackFrame ls l0 l NONE) stack) (LUPDATE w sp tstack) sp 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_size_rel_def; LENGTH_LUPDATE; W2SP1AUX_stack_size_cons_NONE] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; SUB_0; IS_SOME_DEF] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `a:num` SUBST_ALL_TAC)
    (ISPEC `mx:num option` option_nchotomy) THENL
   [REWRITE_TAC[OPTION_MAP2_SOME; option_DISTINCT] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)
    (ISPEC `ls:num option` option_nchotomy) THEN
  REWRITE_TAC[IS_SOME_DEF] THEN
  UNDISCH_TAC `the (f' + 1) (SOME m) = f' + 1` THEN REWRITE_TAC[the_def] THEN
  DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;

let W2SP1AUX_word_eq_small = prove
 (`!m n. m < dimword(:A) /\ n < dimword(:A) ==> (word m = (word n:A word) <=> m = n)`,
  REWRITE_TAC[dimword_def; GSYM VAL_EQ; VAL_WORD] THEN SIMP_TAC[MOD_LT]);;

let W2SP1AUX_wLive_read_bitmap = prove
 (`!(bitmaps:(A word)list) (bs:(A word)list) n (names:1 spt) k f'.
     8 <= dimindex (:A) /\ LENGTH bitmaps < dimword (:A) /\
     LENGTH bs <= n /\ n - LENGTH bs <= LENGTH bitmaps /\
     isPREFIX (APPEND bs (write_bitmap names k f')) (DROP (n - LENGTH bs) bitmaps)
     ==> full_read_bitmap bitmaps (wl_Word (word (n + 1):A word)) =
         SOME (list_of_seq
                 (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList names))) f')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_PREFIX_APPEND; GSYM APPEND_ASSOC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `DROP n (bitmaps:(A word)list) = APPEND (write_bitmap (names:1 spt) k f') l`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `n = LENGTH (bs:(A word)list) + (n - LENGTH bs)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM DROP_DROP_T; DROP_LENGTH_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `n + 1 < dimword(:A)` ASSUME_TAC THENL
   [MP_TAC(AP_TERM `LENGTH:(A word)list->num` (ASSUME
      `DROP n (bitmaps:(A word)list) = APPEND (write_bitmap (names:1 spt) k f') l`)) THEN
    REWRITE_TAC[LENGTH_DROP; LENGTH_APPEND; write_bitmap_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH_word_list] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word (n + 1) = (word 0:A word))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n + 1`; `0`] W2SP1AUX_word_eq_small) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[full_read_bitmap_def; WORD_RULE `word_sub (word (n + 1)) (word 1):A word = word n`] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; GSYM dimword_def; ARITH_RULE `n + 1 < d ==> n < d`] THEN
  MATCH_MP_TAC read_bitmap_append_extra THEN ASM_SIMP_TAC[read_bitmap_write_bitmap]);;

let W2SP1AUX_MEM_sort_toAList = prove
 (`!(env:((A)word_loc)spt) x.
     MEM x (MAP FST (sort key_val_compare (toAList env))) <=> x IN domain env`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `toAList (env:((A)word_loc)spt)`
    (REWRITE_RULE[SORTS_DEF] SORTS_SORT_key_val_compare)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEM_PERM o CONJUNCT1) THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[MEM_toAList; domain_lookup] THEN MESON_TAC[]);;

let W2SP1AUX_bits_F = prove
 (`!f' k (names1:1 spt) (locals:((A)word_loc)spt) n.
     domain names1 SUBSET domain locals /\
     (!x. x IN domain names1 ==> EVEN x /\ k <= x DIV 2) /\
     (!r v. lookup r locals = SOME v /\ k <= r DIV 2 ==> r DIV 2 < k + f') /\
     EVEN n /\ k <= n DIV 2 /\ n DIV 2 < k + f' /\ ~(n IN domain names1)
     ==> oEL ((k + f') - (n DIV 2 + 1))
           (list_of_seq (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList names1)))
              f') = SOME F`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[oEL_THM; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n /\ n < k + f' ==> (k + f') - (n + 1) < f'`; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[option_INJ; MEM_MAP; EXISTS_PAIR_THM; MEM_toAList] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `y:1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r IN domain (names1:1 spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  SUBGOAL_THEN `?v:(A)word_loc. lookup r locals = SOME v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `EVEN r /\ k <= r DIV 2` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r DIV 2 < k + f'` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r DIV 2 = n DIV 2` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r = n:num` SUBST_ALL_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[EVEN_MOD]) THEN
    MP_TAC(SPECL [`r:num`; `2`] DIVISION) THEN MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ASM_MESON_TAC[]]);;

let W2SP1AUX_wLive_stack_rel = prove
 (`!k handler (stack:((A)stack_frame)list) (th:((A)word_loc)option)
     (tstack:((A)word_loc)list) sp (bitmaps:(A word)list) lens f' ls
     (locals:((A)word_loc)spt) (regs:(num,(A)word_loc)fmap) (names:cutsets) w.
     word_to_stackProof_stack_rel k handler stack th (DROP (f' + 1) (DROP sp tstack))
       (LENGTH tstack) bitmaps lens /\
     sp + f' + 1 <= LENGTH tstack /\
     the (f' + 1) ls = f' + 1 /\
     (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
     (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
     domain (FST names) SUBSET domain locals /\
     domain (SND names) SUBSET domain locals /\
     (!n v. lookup n locals = SOME v
            ==> EVEN n /\
                (if n DIV 2 < k then FLOOKUP regs (n DIV 2) = SOME v
                 else oEL ((f' + 1) - 1 - (n DIV 2 - k)) (TAKE (f' + 1) (DROP sp tstack)) =
                      SOME v /\ n DIV 2 < k + f')) /\
     full_read_bitmap bitmaps w =
       SOME (list_of_seq (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k))
                                    (toAList (SND names)))) f')
     ==> word_to_stackProof_stack_rel k handler
           (CONS (StackFrame ls (toAList (inter locals (FST names)))
                    (sort key_val_compare (toAList (inter locals (SND names)))) NONE) stack)
           th (DROP sp (LUPDATE w sp tstack)) (LENGTH tstack) bitmaps (CONS f' lens)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `bits = list_of_seq (\x. MEM x (MAP (\(r,y). (f' - 1) - (r DIV 2 - k))
                                    (toAList (SND (names:cutsets))))) f'` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (bits:bool list) = f'` ASSUME_TAC THENL
   [EXPAND_TAC "bits" THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  ABBREV_TAC `fr = TAKE f' (DROP (sp + 1) (tstack:((A)word_loc)list))` THEN
  SUBGOAL_THEN `LENGTH (fr:((A)word_loc)list) = f'` ASSUME_TAC THENL
   [EXPAND_TAC "fr" THEN MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!j. oEL (j + 1) (TAKE (f' + 1) (DROP sp (tstack:((A)word_loc)list))) = oEL j fr`
    (LABEL_TAC "shift") THENL
   [EXPAND_TAC "fr" THEN
    SUBGOAL_THEN `DROP sp (tstack:((A)word_loc)list) = CONS (EL sp tstack) (DROP (sp + 1) tstack)`
      SUBST1_TAC THENL [MATCH_MP_TAC DROP_EL_CONS THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD1; RICHAUX_TAKE_CLAUSES; oEL_DEF; NOT_SUC; SUC_SUB1];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r v. lookup r locals = SOME v /\ k <= r DIV 2
                      ==> r DIV 2 < k + f' /\
                          oEL ((f' + k) - (r DIV 2 + 1)) fr = SOME (v:(A)word_loc)`
    (LABEL_TAC "inv") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `lookup r locals = SOME (v:(A)word_loc)`) o
                check (W2SP1AUX_HAS_CONST "FLOOKUP")) THEN
    SUBGOAL_THEN `~(r DIV 2 < k)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "shift" (fun th -> REWRITE_TAC[GSYM(SPEC `(f' + k) - (r DIV 2 + 1)` th)]) THEN
    SUBGOAL_THEN `(f' + k) - (r DIV 2 + 1) + 1 = (f' + 1) - 1 - (r DIV 2 - k)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DROP sp (LUPDATE (w:(A)word_loc) sp tstack) = CONS w (DROP (sp + 1) tstack)`
    SUBST1_TAC THENL [MATCH_MP_TAC W2SP1AUX_DROP_LUPDATE_CONS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (W2SP1AUX_HAS_CONST "word_to_stackProof_stack_rel")) THEN
  REWRITE_TAC[word_to_stackProof_stack_rel_def; ALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
      STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[sorted_env_def; W2SP1AUX_SORTED_sort_toAList] THEN
  EXISTS_TAC `CONS (NONE:((A)word_loc#(A)word_loc)option,(bits:bool list),
                     (fr:((A)word_loc)list))
                    (stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[abs_stack_def] THEN
    SUBGOAL_THEN
      `DROP f' (DROP (sp + 1) tstack) = DROP (f' + 1) (DROP sp (tstack:((A)word_loc)list))`
      SUBST1_TAC THENL
     [REWRITE_TAC[DROP_DROP_T] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_DROP; ARITH_RULE `sp + f' + 1 <= l ==> ~(l - (sp + 1) < f')`] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN SIMP[];
    REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
    SUBGOAL_THEN `handler < LENGTH (stack:((A)stack_frame)list)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (W2SP1AUX_HAS_CONST "is_handler_frame")) THEN
      SUBGOAL_THEN `SUC (LENGTH (stack:((A)stack_frame)list)) - (handler + 1) = 0`
        SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[EL; HD; is_handler_frame_def]];
      ALL_TAC] THEN
    SUBGOAL_THEN `SUC (LENGTH (stack:((A)stack_frame)list)) - (handler + 1) =
                  SUC (LENGTH stack - (handler + 1))` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EL; TL]) THEN
    SUBGOAL_THEN `handler + 1 <= LENGTH (stk:(((A)word_loc#(A)word_loc)option#bool list#
                                         ((A)word_loc)list)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LASTN_CONS] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[stack_rel_aux_def; adjust_names_def] THEN CONJ_TAC THENL
     [REWRITE_TAC[ALOOKUP_toAList; lookup_inter_alt; ALOOKUP_NONE; W2SP1AUX_MEM_sort_toAList;
                  domain_inter; IN_INTER] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
      SUBGOAL_THEN `EVEN n /\ k <= n DIV 2` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "inv" (MP_TAC o SPECL [`n:num`; `v:(A)word_loc`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "bits" THEN MATCH_MP_TAC W2SP1AUX_bits_F THEN
        EXISTS_TAC `locals:((A)word_loc)spt` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[domain_lookup]];
        ASM_SIMP_TAC[ALOOKUP_index_list; ARITH_RULE `n < k + f' ==> n < f' + k`]];
      EXPAND_TAC "bits" THEN MATCH_MP_TAC W2SP1AUX_filter_bits_eq THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]]]);;

let W2SP1AUX_state_rel_basic = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> stack_state_use_stack t /\
         stack_state_stack_space t + f <= LENGTH (stack_state_stack t) /\
         (if f' = 0 then f = 0 else f = f' + 1)`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[]);;

let W2SP1AUX_EXPAND_STATE_REL_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if (try fst(dest_const(fst(strip_comb c))) = "word_to_stackProof_state_rel"
        with Failure _ -> false)
    then STRIP_ASSUME_TAC
           (CONV_RULE(TOP_DEPTH_CONV let_CONV)
              (REWRITE_RULE[word_to_stackProof_state_rel_def] th))
    else NO_TAC);;

let W2SP1AUX_wLive_push_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens names envs
     (bs:(A word)app_list) n.
     (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
     (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\ 1 <= f /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
     isPREFIX (APPEND (append bs) (write_bitmap (SND names) k f':(A word)list))
       (DROP (n - LENGTH (append bs)) (stack_state_bitmaps t))
     ==> word_to_stackProof_state_rel ac k 0 0
           (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
              (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s)))
           (stack_state_stack_fupd
              (K (LUPDATE (wl_Word (word (n + 1))) (stack_state_stack_space t)
                    (stack_state_stack t)))
              (stack_set_var k (wl_Word (word (n + 1))) t))
           (CONS f' lens) 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_state_rel_basic o check (fun th ->
    W2SP1AUX_HAS_CONST "word_to_stackProof_state_rel" th)) THEN
  SUBGOAL_THEN `f = f' + 1` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W2SP1AUX_EXPAND_STATE_REL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
      lhs (concl th) = `wl_state_permute (s:(A,num#C,FFI)wl_state)`
    then REWRITE_TAC[MATCH_MP W2SP1AUX_push_env_K_I th] else NO_TAC) THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; stack_set_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[LENGTH_LUPDATE; ADD_CLAUSES; RICHAUX_DROP_CLAUSES; RICHAUX_TAKE_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_cut_envs_SOME) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "envs")) THEN
  REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `the (f' + 1) (wl_state_locals_size (s:(A,num#C,FFI)wl_state)) = f' + 1`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (W2SP1AUX_HAS_CONST "stack_size_rel")) THEN
    REWRITE_TAC[stack_size_rel_def; ADD_EQ_0; ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_ARITH_TAC;
    MATCH_MP_TAC W2SP1AUX_wLive_size_rel THEN EXISTS_TAC `f':num` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state)) < dimword(:A)`
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`stack_state_bitmaps (t:(A,C,FFI)stack_state)`; `append (bs:(A word)app_list)`;
                   `n:num`; `SND (names:cutsets)`; `k:num`; `f':num`]
                  W2SP1AUX_wLive_read_bitmap) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC W2SP1AUX_wLive_stack_rel THEN
    EXISTS_TAC `stack_state_regs (t:(A,C,FFI)stack_state)` THEN ASM_REWRITE_TAC[]]);;

let W2SP1AUX_state_rel_regs = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra r.
     (!x. x < k ==> FLOOKUP r x = FLOOKUP (stack_state_regs t) x)
     ==> (word_to_stackProof_state_rel ac k f f' s (stack_state_regs_fupd (K r) t)
            lens extra <=>
          word_to_stackProof_state_rel ac k f f' s t lens extra)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[]);;

(* HOL4 line 1339 (HOL4's unused binder bs5 is left out) *)
let evaluate_wLive = prove
 (`!names bs n k f f' wlive_prog bs' n' ac (s:(A,num#C,FFI)wl_state)
     (t:(A,C,FFI)stack_state) lens envs.
     wLive names (bs,n) (k,f,f') = (wlive_prog,(bs',n')) /\
     (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
     (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     1 <= f /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) (stack_state_bitmaps t))
     ==> ?(t5:(A,C,FFI)stack_state).
           stack_evaluate (wlive_prog,t) = (NONE,t5) /\
           word_to_stackProof_state_rel ac k 0 0
             (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
                (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s)))
             t5 (CONS f' lens) 0 /\
           word_to_stackProof_state_rel ac k f f' s t5 lens 0 /\
           LENGTH (stack_state_stack t5) = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t5 = stack_state_stack_space t /\
           !i. ~(i = k) ==> stack_get_var i t5 = stack_get_var i t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `wLive names (bs,n) (k,f,f') = (wlive_prog:(A)stack_prog,(bs',n'))` THEN
  ASM_REWRITE_TAC[wLive_def; insert_bitmap_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN SIMP[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[append_thm]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_state_rel_basic o check (fun th ->
    W2SP1AUX_HAS_CONST "word_to_stackProof_state_rel" th)) THEN
  EXISTS_TAC `stack_state_stack_fupd
      (K (LUPDATE (wl_Word (word (n + 1))) (stack_state_stack_space t) (stack_state_stack t)))
      (stack_set_var k (wl_Word (word (n + 1):A word)) (t:(A,C,FFI)stack_state))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC W2SP1AUX_wLive_eval THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC W2SP1AUX_wLive_push_rel THEN
    MAP_EVERY EXISTS_TAC [`f:num`; `names:cutsets`; `bs:(A word)app_list`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `word_to_stackProof_state_rel ac k f f' s
                    (stack_set_var k (wl_Word (word (n + 1):A word)) (t:(A,C,FFI)stack_state))
                    lens 0` MP_TAC THENL
     [REWRITE_TAC[stack_set_var_def] THEN
      SUBGOAL_THEN
        `!x. x < k
             ==> FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state) |+
                            (k,wl_Word (word (n + 1):A word))) x =
                 FLOOKUP (stack_state_regs t) x`
        (fun th -> ASM_REWRITE_TAC[MATCH_MP W2SP1AUX_state_rel_regs th]) THEN
      REWRITE_TAC[FLOOKUP_UPDATE] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP W2SP1AUX_state_rel_LUPDATE_sp o C CONJ (ASSUME `1 <= f`)) THEN
    REWRITE_TAC[stack_set_var_def] THEN SIMP[];
    REWRITE_TAC[stack_set_var_def] THEN SIMP[LENGTH_LUPDATE];
    REWRITE_TAC[stack_set_var_def] THEN SIMP[];
    REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 1600 *)
let state_rel_set_store_0 = prove
 (`!ac k (s5:(A,num#C,FFI)wl_state) (t5:(A,C,FFI)stack_state) len extra w.
     word_to_stackProof_state_rel ac k 0 0 s5 t5 len extra
     ==> word_to_stackProof_state_rel ac k 0 0 (wl_set_store AllocSize w s5)
           (stack_set_store AllocSize w t5) len extra`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_set_store_def; stack_set_store_def] THEN
  SIMP[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(GSYM DOMSUB_FUPDATE_NEQ) THEN REWRITE_TAC[distinctness "store_name"];
    ASM_MESON_TAC[]]);;

(* HOL4 line 1614 *)
let read_bitmap_not_empty = prove
 (`!(stack:(A word)list) a. read_bitmap stack = SOME a ==> ~(stack = [])`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `stack:(A word)list = []` THEN
  ASM_REWRITE_TAC[read_bitmap_def; GSYM NOT_SOME_NONE]);;

(* HOL4 line 1623 *)
let n2w_lsr_1 = prove
 (`!n. n < dimword (:A) ==> word_ushr (word n) 1 = (word (n DIV 2)):A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; EXP_1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < m ==> n DIV 2 < m`] THEN
  MATCH_MP_TAC(GSYM MOD_LT) THEN
  TRANS_TAC LET_TRANS `n:num` THEN ASM_REWRITE_TAC[DIV_LE] THEN ARITH_TAC);;

let W2SP1AUX_good_dimword = prove
 (`good_dimindex(:A) ==> 2 EXP 32 <= dimword(:A)`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1630 *)
let handler_bitmap_props = prove
 (`!(stack:(A word)list).
     good_dimindex (:A) ==> read_bitmap (CONS (word 4:A word) stack) = SOME [F; F]`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP1AUX_good_dimword) THEN
  SUBGOAL_THEN `32 <= dimindex(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[read_bitmap_def] THEN
  SUBGOAL_THEN `~word_msb (word 4:A word)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[word_msb_def; BIT_WORD] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `4 DIV 2 EXP (dimindex(:A) - 1) = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP 31` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `bit_length (word 4:A word) = 3` SUBST1_TAC THENL
   [SUBGOAL_THEN `4 < dimword(:A) /\ 2 < dimword(:A) /\ 1 < dimword(:A) /\ 0 < dimword(:A)`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[bit_length_def] THEN
    ASM_SIMP_TAC[W2SP1AUX_word_eq_small; n2w_lsr_1; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[bit_length_def] THEN
    ASM_SIMP_TAC[W2SP1AUX_word_eq_small; n2w_lsr_1; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[bit_length_def] THEN
    ASM_SIMP_TAC[W2SP1AUX_word_eq_small; n2w_lsr_1; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[bit_length_def] THEN REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[num_CONV `2`; num_CONV `1`; list_of_seq] THEN
  REWRITE_TAC[APPEND; BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `32 <= n ==> 0 < n /\ SUC 0 < n`]);;

let W2SP1AUX_full_read_bitmap_NZ = prove
 (`!(bs:(A word)list) (w:(B)word_loc) bits.
     full_read_bitmap bs w = SOME bits ==> ~(w = wl_Word (word 0))`,
  REPEAT GEN_TAC THEN CASES_ON `w:(B)word_loc` THEN
  REWRITE_TAC[full_read_bitmap_def; distinctness "word_loc"; injectivity "word_loc"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_SOME_NONE]);;

let W2SP1AUX_enc_stack_cons = prove
 (`!(bs:(A word)list) w ws bits ts ws' rs.
     full_read_bitmap bs w = SOME bits /\
     filter_bitmap bits ws = SOME (ts,ws') /\
     stack_enc_stack bs ws' = SOME rs
     ==> stack_enc_stack bs (CONS w ws) = SOME (APPEND ts rs)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP1AUX_full_read_bitmap_NZ) THEN
  ONCE_REWRITE_TAC[stack_enc_stack_def] THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let W2SP1AUX_full_read_bitmap_1 = prove
 (`!(bs:(A word)list).
     good_dimindex(:A) /\ 1 <= LENGTH bs /\ HD bs = word 4
     ==> full_read_bitmap bs (wl_Word (word 1:A word)) = SOME [F; F]`,
  GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `b0:A word` (X_CHOOSE_THEN `bt:(A word)list` SUBST_ALL_TAC))
    (ISPEC `bs:(A word)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(1 <= 0)`; HD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[full_read_bitmap_def; WORD_NE_10; WORD_SUB_REFL; VAL_WORD_0;
                  RICHAUX_DROP_CLAUSES] THEN
  ASM_SIMP_TAC[handler_bitmap_props]);;

(* HOL4 line 1642 (HOL4's unused binder bs' is left out) *)
let enc_stack_lemma = prove
 (`!(bs:(A word)list) (wstack:((A)stack_frame)list) sstack lens astack k len.
     good_dimindex (:A) /\
     LENGTH bs + 1 < dimword (:A) /\
     abs_stack bs wstack sstack lens = SOME astack /\
     1 <= LENGTH bs /\
     HD bs = word 4 /\
     stack_rel_aux k len wstack astack
     ==> stack_enc_stack bs sstack = SOME (wl_enc_stack wstack)`,
  MATCH_MP_TAC abs_stack_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[abs_stack_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM NOT_SOME_NONE; stack_enc_stack_def; wl_enc_stack_def];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[abs_stack_def] THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_rel_aux_def]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RES_TAC THEN IMP_RES_TAC filter_bitmap_lemma THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP_SND_MAP_FST]) THEN
    REWRITE_TAC[wl_enc_stack_def] THEN MATCH_MP_TAC W2SP1AUX_enc_stack_cons THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[abs_stack_def] THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_rel_aux_def]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RES_TAC THEN IMP_RES_TAC filter_bitmap_lemma THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP_SND_MAP_FST]) THEN
    SUBGOAL_THEN `stack_enc_stack bitmaps (CONS (a0'':(A)word_loc) a1'') =
                  SOME (APPEND (MAP SND (l:(num#(A)word_loc)list)) (wl_enc_stack xs))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC W2SP1AUX_enc_stack_cons THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[wl_enc_stack_def] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM (CONJUNCT1 APPEND)] THEN
    MATCH_MP_TAC W2SP1AUX_enc_stack_cons THEN
    MAP_EVERY EXISTS_TAC [`[F;F]`; `CONS (a0'':(A)word_loc) a1''`] THEN
    ASM_SIMP_TAC[W2SP1AUX_full_read_bitmap_1] THEN REWRITE_TAC[filter_bitmap_def];
    REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE];
    REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE];
    REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE]]);;

(* HOL4 line 1696 *)
let IMP_enc_stack = prove
 (`!ac k (s1:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state) lens.
     word_to_stackProof_state_rel ac k 0 0 s1 t1 lens 0
     ==> stack_enc_stack (stack_state_bitmaps t1)
           (DROP (stack_state_stack_space t1) (stack_state_stack t1)) =
         SOME (wl_enc_stack (wl_state_stack s1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[word_to_stackProof_stack_rel_def; ADD_CLAUSES; RICHAUX_DROP_CLAUSES] THEN
  STRIP_TAC THEN MATCH_MP_TAC enc_stack_lemma THEN
  MAP_EVERY EXISTS_TAC
   [`lens:num list`;
    `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
    `k:num`; `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `LENGTH (stack_state_bitmaps (t1:(A,C,FFI)stack_state)) +
    LENGTH (buffer_buffer (wl_state_data_buffer (s1:(A,num#C,FFI)wl_state))) +
    buffer_space_left (wl_state_data_buffer s1) + 1 < dimword(:A)` THEN
  ARITH_TAC);;

(* HOL4 line 1707 (HOL4's unused binder z is left out) *)
let map_bitmap_success = prove
 (`!bs (stack:A list) a b (ls:A list).
     filter_bitmap bs stack = SOME (a,b) /\ LENGTH ls = LENGTH a
     ==> ?x. map_bitmap bs ls stack = SOME (x,[],DROP (LENGTH bs) stack) /\
               filter_bitmap bs x = SOME (ls,[])`,
  MATCH_MP_TAC filter_bitmap_ind THEN REWRITE_TAC[filter_bitmap_def; GSYM NOT_SOME_NONE] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `[]:A list` THEN
    UNDISCH_TAC `LENGTH (ls:A list) = LENGTH (a:A list)` THEN
    UNDISCH_TAC `[]:A list = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[map_bitmap_def; LENGTH; RICHAUX_DROP_CLAUSES];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:A list`; `b:A list`; `ls:A list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `CONS (r:A) x` THEN
    ASM_REWRITE_TAC[map_bitmap_def; filter_bitmap_def; LENGTH; RICHAUX_DROP_CLAUSES] THEN
    SIMP[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    GVS(all_case_eqs()) THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `l0:A` (X_CHOOSE_THEN `ls':A list` SUBST_ALL_TAC))
      (ISPEC `ls:A list` list_CASES) THEN
    FS[LENGTH] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ls':A list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (l0:A) y` THEN
    ASM_REWRITE_TAC[map_bitmap_def; filter_bitmap_def; SUC_SUB1] THEN SIMP[]]);;

(* HOL4 line 1726 (n is an unused binder of HOL4, left out) *)
let map_bitmap_more = prove
 (`!bs (ls:A list) stack a c ls'.
     map_bitmap bs ls stack = SOME (a,[],c)
     ==> map_bitmap bs (APPEND ls ls') stack = SOME (a,ls',c)`,
  MATCH_MP_TAC map_bitmap_ind THEN
  REWRITE_TAC[map_bitmap_def; GSYM NOT_SOME_NONE; APPEND] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP[]);;

(* HOL4 line 1735 *)
let map_bitmap_more_simp = prove
 (`!bs (l:B list) (ls:A list) stack a c.
     map_bitmap bs (TAKE (LENGTH l) ls) stack = SOME (a,[],c)
     ==> map_bitmap bs ls stack = SOME (a,DROP (LENGTH l) ls,c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`bs:bool list`; `TAKE (LENGTH (l:B list)) (ls:A list)`; `stack:A list`;
                 `a:A list`; `c:A list`; `DROP (LENGTH (l:B list)) (ls:A list)`]
         map_bitmap_more) THEN
  ASM_REWRITE_TAC[TAKE_DROP]);;

(* HOL4 line 1742 *)
let map_bitmap_LLOOKUP_F = prove
 (`!bm (ls:A list) stack n res ls1 stack1.
     oEL n bm = SOME F /\
     map_bitmap bm ls stack = SOME (res,ls1,stack1)
     ==> ?v. oEL n res = SOME v /\ oEL n stack = SOME v`,
  MATCH_MP_TAC map_bitmap_ind THEN
  REWRITE_TAC[map_bitmap_def; GSYM NOT_SOME_NONE; oEL_def] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN
  REWRITE_TAC[oEL_def] THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(n = 0)`]) THEN
  RES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 1755 *)
let word_stack_dec_stack_shape = prove
 (`!(ls:((A)word_loc)list) (wstack:((A)stack_frame)list) res n.
     wl_dec_stack ls wstack = SOME res /\ n < LENGTH wstack
     ==> (is_handler_frame (EL n wstack) <=> is_handler_frame (EL n res))`,
  MATCH_MP_TAC wl_dec_stack_ind THEN
  REWRITE_TAC[wl_dec_stack_def; GSYM NOT_SOME_NONE; LENGTH; CONJUNCT1 LT] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)
    (SPEC `n':num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL] THEN
  TRY(CASES_ON `handler:(num#num#num)option` THEN REWRITE_TAC[is_handler_frame_def] THEN
      NO_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 1771.  DEVIATION (docs/CONVENTIONS.md 8): HOL4 ZIP (MAP FST l,  *)
(* ls) with LENGTH ls = LENGTH l is ZIP (MAP FST l) ls (equal lengths).      *)
let sorted_env_zip = prove
 (`!(l:(num#(A)word_loc)list) (ls:((A)word_loc)list) x n l0.
     sorted_env (StackFrame n l0 l x) /\ LENGTH ls = LENGTH l
     ==> sorted_env (StackFrame n l0 (ZIP (MAP FST l) ls) x)`,
  REWRITE_TAC[sorted_env_def; W2SP1AUX_SORTED_FST] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; LENGTH_MAP]);;

(* HOL4 line 1789 *)
let word_stack_dec_stack_sorted = prove
 (`!(ls:((A)word_loc)list) (wstack:((A)stack_frame)list) res.
     wl_dec_stack ls wstack = SOME res /\ ALL sorted_env wstack
     ==> ALL sorted_env res`,
  MATCH_MP_TAC wl_dec_stack_ind THEN
  REWRITE_TAC[wl_dec_stack_def; GSYM NOT_SOME_NONE; ALL] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC sorted_env_zip THEN ASM_REWRITE_TAC[LENGTH_TAKE_EQ_MIN; LENGTH] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 1802 *)
let abs_stack_empty = prove
 (`!(bs:(A word)list) ls stack lens.
     abs_stack bs ([]:((B)stack_frame)list) ls lens = SOME stack
     ==> ls = [wl_Word (word 0)] /\ lens = []`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `lens:num list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_SOME_NONE]);;

(* HOL4 line 1809 *)
let abs_frame_eq_def = cake_def
  `abs_frame_eq (p:A#B#C list) (q:A#B#D list) <=>
     FST p = FST q /\
     FST (SND p) = FST (SND q) /\
     LENGTH (SND (SND p)) = LENGTH (SND (SND q))`;;

(* HOL4 line 1816 *)
let LIST_REL_abs_frame_eq_handler_val = prove
 (`!(xs:(A option#B#C list)list) (ys:(A option#B#D list)list).
     ALL2 abs_frame_eq xs ys ==> handler_val xs = handler_val ys`,
  MATCH_MP_TAC LIST_REL_ind THEN REWRITE_TAC[FORALL_PAIR_THM; abs_frame_eq_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN GVS[] THEN REWRITE_TAC[handler_val_def] THEN
  W(fun (asl,w) -> CASES_ON (find_term (fun t -> is_var t && type_of t = `:A option`) w)) THEN
  ASM_REWRITE_TAC[handler_val_def]);;

let W2SP1AUX_dec_frame = prove
 (`!bits (stack:((A)word_loc)list) (l:(num#(A)word_loc)list) (l0:(num#(A)word_loc)list)
     ls k.
     filter_bitmap bits (index_list (TAKE (LENGTH bits) stack) k) =
       SOME (MAP_FST adjust_names l,[]) /\
     ~(LENGTH stack < LENGTH bits) /\ ~(LENGTH ls < LENGTH l) /\
     (!n v. ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE
            ==> adjust_names n < k + LENGTH bits /\
                oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F /\
                ALOOKUP (index_list (TAKE (LENGTH bits) stack) k) (n DIV 2) = SOME v)
     ==> ?x. map_bitmap bits ls stack =
               SOME (x,DROP (LENGTH l) ls,DROP (LENGTH bits) stack) /\
             LENGTH x = LENGTH bits /\
             filter_bitmap bits (index_list x k) =
               SOME (MAP_FST adjust_names (ZIP (MAP FST l) (TAKE (LENGTH l) ls)),[]) /\
             (!n v. ALOOKUP l0 n = SOME v /\
                    ALOOKUP (ZIP (MAP FST l) (TAKE (LENGTH l) ls)) n = NONE
                    ==> adjust_names n < k + LENGTH bits /\
                        oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F /\
                        ALOOKUP (index_list x k) (n DIV 2) = SOME v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[MAP_SND_MAP_FST] o MATCH_MP filter_bitmap_lemma) THEN
  SUBGOAL_THEN `LENGTH (TAKE (LENGTH (l:(num#(A)word_loc)list)) (ls:((A)word_loc)list)) =
                LENGTH l` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`bits:bool list`; `stack:((A)word_loc)list`;
                 `MAP SND (l:(num#(A)word_loc)list)`;
                 `DROP (LENGTH (bits:bool list)) (stack:((A)word_loc)list)`;
                 `TAKE (LENGTH (l:(num#(A)word_loc)list)) (ls:((A)word_loc)list)`]
         map_bitmap_success) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:((A)word_loc)list` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP map_bitmap_more_simp) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP map_bitmap_length) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC filter_bitmap_MAP_IMP THEN
    ASM_SIMP_TAC[MAP_SND_index_list; MAP_SND_MAP_FST; MAP_ZIP; LENGTH_MAP] THEN
    REWRITE_TAC[W2SP1AUX_MAP_FST_MAP_FST] THEN ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP filter_bitmap_IMP_MAP_FST o
      check (fun th -> can (find_term (fun t -> t = `MAP_FST adjust_names (l:(num#(A)word_loc)list)`)) (concl th))) THEN
    REWRITE_TAC[W2SP1AUX_MAP_FST_MAP_FST; MAP_FST_index_list] THEN
    ASM_SIMP_TAC[LENGTH_TAKE; ARITH_RULE `~(a < b) ==> b <= a`];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_NONE] THEN ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[GSYM ALOOKUP_NONE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALOOKUP (index_list (TAKE (LENGTH (bits:bool list)) (stack:((A)word_loc)list)) k)
                 (n DIV 2) = SOME v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[adjust_names_def]) THEN
  ASM_SIMP_TAC[ALOOKUP_index_list; LENGTH_TAKE; ARITH_RULE `~(a < b) ==> b <= a`;
               ARITH_RULE `n < k + b ==> n < b + k`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(k + LENGTH (bits:bool list)) - (n DIV 2 + 1) =
                (LENGTH bits + k) - (n DIV 2 + 1)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP oEL_TAKE_E) THEN
  MP_TAC(ISPECL [`bits:bool list`; `ls:((A)word_loc)list`; `stack:((A)word_loc)list`;
                 `(LENGTH (bits:bool list) + k) - (n DIV 2 + 1)`; `x:((A)word_loc)list`;
                 `DROP (LENGTH (l:(num#(A)word_loc)list)) (ls:((A)word_loc)list)`;
                 `DROP (LENGTH (bits:bool list)) (stack:((A)word_loc)list)`]
         map_bitmap_LLOOKUP_F) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:(A)word_loc` STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[option_INJ]);;

let W2SP1AUX_dec_stack_cons = prove
 (CASE_TERM `!(ls:((A)word_loc)list) n l0 l h st.
     wl_dec_stack ls (CONS (StackFrame n l0 l h) st) =
     if LENGTH ls < LENGTH l then NONE
     else (match wl_dec_stack (DROP (LENGTH l) ls) st with
             NONE -> NONE
           | SOME s -> SOME (CONS (StackFrame n l0 (ZIP (MAP FST l) (TAKE (LENGTH l) ls)) h) s))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[wl_dec_stack_def]);;

let W2SP1AUX_stack_dec_stack_cons = prove
 (`!(bs:(A word)list) w ts ws bits hd ts' ws' rest.
     full_read_bitmap bs w = SOME bits /\
     map_bitmap bits ts ws = SOME (hd,ts',ws') /\
     stack_dec_stack bs ts' ws' = SOME rest
     ==> stack_dec_stack bs ts (CONS w ws) = SOME (CONS w (APPEND hd rest))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP1AUX_full_read_bitmap_NZ) THEN
  ONCE_REWRITE_TAC[stack_dec_stack_def] THEN ASM_REWRITE_TAC[] THEN SIMP[APPEND]);;

(* HOL4 line 1827 *)
let dec_stack_lemma1 = prove
 (`!(bs:(A word)list) (wstack:((A)stack_frame)list) sstack lens astack wdec ls k len.
     good_dimindex (:A) /\
     1 <= LENGTH bs /\
     HD bs = word 4 /\
     abs_stack bs wstack sstack lens = SOME astack /\
     stack_rel_aux k len wstack astack /\
     wl_dec_stack ls wstack = SOME wdec
     ==> ?sdec bstack.
           stack_dec_stack bs ls sstack = SOME sdec /\
           abs_stack bs wdec sdec lens = SOME bstack /\
           stack_rel_aux k len wdec bstack /\
           ALL2 abs_frame_eq astack bstack`,
  (MATCH_MP_TAC abs_stack_ind THEN REPEAT CONJ_TAC) THENL
  [(REWRITE_TAC[abs_stack_def] THEN REPEAT GEN_TAC THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `l1:(A)word_loc` (X_CHOOSE_THEN `l2:((A)word_loc)list` SUBST_ALL_TAC))
     (ISPEC `ls:((A)word_loc)list` list_CASES) THEN
   REWRITE_TAC[wl_dec_stack_def; GSYM NOT_SOME_NONE] THEN
   COND_CASES_TAC THEN REWRITE_TAC[GSYM NOT_SOME_NONE; option_INJ] THEN STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
   MAP_EVERY EXISTS_TAC [`[wl_Word (word 0:A word)]`;
     `[]:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`] THEN
   ASM_REWRITE_TAC[stack_dec_stack_def; abs_stack_def; stack_rel_aux_def; ALL2]);
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[abs_stack_def; W2SP1AUX_dec_stack_cons] THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_rel_aux_def]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)))) THEN
  (MP_TAC(ISPECL [`a:bool list`; `stack:((A)word_loc)list`; `l:(num#(A)word_loc)list`;
                 `l0:(num#(A)word_loc)list`; `ls:((A)word_loc)list`; `k:num`]
         W2SP1AUX_dec_frame) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:((A)stack_frame)list`;
     `DROP (LENGTH (l:(num#(A)word_loc)list)) (ls:((A)word_loc)list)`; `k:num`; `len':num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sdec':((A)word_loc)list`
    (X_CHOOSE_THEN `bstack':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
      STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`CONS (w:(A)word_loc) (APPEND x sdec')`;
    `CONS (NONE:((A)word_loc#(A)word_loc)option,a:bool list,x:((A)word_loc)list) bstack'`] THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `sdec':((A)word_loc)list`] TAKE_LENGTH_APPEND) THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `sdec':((A)word_loc)list`] DROP_LENGTH_APPEND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (TAKE (LENGTH (a:bool list)) (stack:((A)word_loc)list)) =
                LENGTH (x:((A)word_loc)list)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LENGTH_TAKE; ARITH_RULE `~(a < b) ==> b <= a`]; ALL_TAC] THEN
  REPEAT CONJ_TAC) THENL
  [(MATCH_MP_TAC W2SP1AUX_stack_dec_stack_cons THEN ASM_MESON_TAC[]);
   (REWRITE_TAC[APPEND; abs_stack_def] THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]) THEN
  (SIMP[ARITH_RULE `~(a + b < a:num)`]);
   (REWRITE_TAC[stack_rel_aux_def] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);
   (MAP_EVERY EXISTS_TAC
     [`(NONE:((A)word_loc#(A)word_loc)option,a:bool list,x:((A)word_loc)list)`;
      `bstack':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`] THEN
    ASM_REWRITE_TAC[abs_frame_eq_def; FST; SND])];
   (REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[abs_stack_def; W2SP1AUX_dec_stack_cons] THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[stack_rel_aux_def]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)))) THEN
  (MP_TAC(ISPECL [`a:bool list`; `a1'':((A)word_loc)list`; `l:(num#(A)word_loc)list`;
                 `l0:(num#(A)word_loc)list`; `ls:((A)word_loc)list`; `k:num`]
         W2SP1AUX_dec_frame) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:((A)stack_frame)list`;
     `DROP (LENGTH (l:(num#(A)word_loc)list)) (ls:((A)word_loc)list)`; `k:num`; `len':num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sdec':((A)word_loc)list`
    (X_CHOOSE_THEN `bstack':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
      STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`CONS (wl_Word (word 1:A word)) (APPEND [a0:(A)word_loc; a0'] (CONS (a0'':(A)word_loc) (APPEND x sdec')))`;
    `CONS (SOME (a0:(A)word_loc,a0':(A)word_loc),a:bool list,x:((A)word_loc)list) bstack'`] THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `sdec':((A)word_loc)list`] TAKE_LENGTH_APPEND) THEN
  MP_TAC(ISPECL [`x:((A)word_loc)list`; `sdec':((A)word_loc)list`] DROP_LENGTH_APPEND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (TAKE (LENGTH (a:bool list)) (a1'':((A)word_loc)list)) =
                LENGTH (x:((A)word_loc)list)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LENGTH_TAKE; ARITH_RULE `~(a < b) ==> b <= a`]; ALL_TAC] THEN
  REPEAT CONJ_TAC) THENL
  [(MATCH_MP_TAC W2SP1AUX_stack_dec_stack_cons THEN
   MAP_EVERY EXISTS_TAC [`[F;F]`; `ls:((A)word_loc)list`; `CONS (a0'':(A)word_loc) a1''`] THEN
   ASM_SIMP_TAC[W2SP1AUX_full_read_bitmap_1] THEN REWRITE_TAC[map_bitmap_def] THEN SIMP[] THEN
   MATCH_MP_TAC W2SP1AUX_stack_dec_stack_cons THEN ASM_MESON_TAC[]);
   (REWRITE_TAC[APPEND; abs_stack_def] THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    SIMP[ARITH_RULE `~(a + b < a:num)`]);
   (REWRITE_TAC[stack_rel_aux_def] THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
   STRIP_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
   MP_TAC(ISPECL [`bitmaps:(A word)list`; `a:((A)stack_frame)list`; `sdec':((A)word_loc)list`;
                  `lens:num list`; `bstack':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`]
          abs_stack_IMP_LENGTH) THEN
   MP_TAC(ISPECL [`bitmaps:(A word)list`; `xs:((A)stack_frame)list`;
                  `DROP (LENGTH (a:bool list)) (a1'':((A)word_loc)list)`;
                  `lens:num list`; `a:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`]
          abs_stack_IMP_LENGTH) THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`DROP (LENGTH (l:(num#(A)word_loc)list)) (ls:((A)word_loc)list)`;
                  `xs:((A)stack_frame)list`; `a:((A)stack_frame)list`;
                  `LENGTH (xs:((A)stack_frame)list) - (p1 + 1)`] word_stack_dec_stack_shape) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(ISPECL [`abs_frame_eq:((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list->((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list->bool`;
                  `a:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                  `bstack':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                  `p1 + 1`] list_rel_lastn) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(ASSUME_TAC o MATCH_MP LIST_REL_abs_frame_eq_handler_val) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
     can (find_term (fun t -> t = `a0':(A)word_loc`)) (concl th))) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[]);
   (MAP_EVERY EXISTS_TAC
     [`(SOME (wl_Loc p1' p2,a0'):((A)word_loc#(A)word_loc)option,a:bool list,x:((A)word_loc)list)`;
      `bstack':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`] THEN
    ASM_REWRITE_TAC[abs_frame_eq_def; FST; SND])];
   (REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE]);
   (REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE]);
   (REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE])]);;

(* HOL4 line 1992 *)
let dec_stack_lemma = prove
 (`!(t1:(A,C,FFI)stack_state) (s1:(A,num#C,FFI)wl_state) x0 x k lens.
     good_dimindex (:A) /\
     1 <= LENGTH (stack_state_bitmaps t1) /\
     HD (stack_state_bitmaps t1) = word 4 /\
     stack_state_stack_space t1 <= LENGTH (stack_state_stack t1) /\
     stack_enc_stack (stack_state_bitmaps t1)
       (DROP (stack_state_stack_space t1) (stack_state_stack t1)) =
       SOME (wl_enc_stack (wl_state_stack s1)) /\
     wl_dec_stack x0 (wl_state_stack s1) = SOME x /\
     word_to_stackProof_stack_rel k (wl_state_handler s1) (wl_state_stack s1)
       (SOME (FAPPLY (stack_state_store t1) Handler))
       (DROP (stack_state_stack_space t1) (stack_state_stack t1))
       (LENGTH (stack_state_stack t1)) (stack_state_bitmaps t1) lens /\
     LENGTH (wl_enc_stack (wl_state_stack s1)) = LENGTH x0
     ==> ?yy:((A)word_loc)list.
           stack_dec_stack (stack_state_bitmaps t1) x0
             (DROP (stack_state_stack_space t1) (stack_state_stack t1)) = SOME yy /\
           stack_state_stack_space t1 + LENGTH yy = LENGTH (stack_state_stack t1) /\
           word_to_stackProof_stack_rel k (wl_state_handler s1) x
             (SOME (FAPPLY (stack_state_store t1) Handler)) yy
             (LENGTH (stack_state_stack t1)) (stack_state_bitmaps t1) lens`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stack_state_bitmaps (t1:(A,C,FFI)stack_state)`;
                 `wl_state_stack (s1:(A,num#C,FFI)wl_state)`;
                 `DROP (stack_state_stack_space t1) (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                 `lens:num list`;
                 `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                 `x:((A)stack_frame)list`; `x0:((A)word_loc)list`; `k:num`;
                 `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`] dec_stack_lemma1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sdec:((A)word_loc)list`
    (X_CHOOSE_THEN `bstack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
      STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `sdec:((A)word_loc)list` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP dec_stack_length) THEN REWRITE_TAC[LENGTH_DROP] THEN
    ASM_ARITH_TAC;
    ASM_MESON_TAC[word_stack_dec_stack_sorted];
    EXISTS_TAC
     `bstack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
    MP_TAC(ISPECL [`stack_state_bitmaps (t1:(A,C,FFI)stack_state)`;
                   `x:((A)stack_frame)list`; `sdec:((A)word_loc)list`; `lens:num list`;
                   `bstack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`]
           abs_stack_IMP_LENGTH) THEN
    MP_TAC(ISPECL [`stack_state_bitmaps (t1:(A,C,FFI)stack_state)`;
                   `wl_state_stack (s1:(A,num#C,FFI)wl_state)`;
                   `DROP (stack_state_stack_space t1) (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                   `lens:num list`;
                   `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`]
           abs_stack_IMP_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`x0:((A)word_loc)list`; `wl_state_stack (s1:(A,num#C,FFI)wl_state)`;
                   `x:((A)stack_frame)list`;
                   `LENGTH (wl_state_stack (s1:(A,num#C,FFI)wl_state)) -
                    (wl_state_handler s1 + 1)`] word_stack_dec_stack_shape) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`abs_frame_eq:((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list->((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list->bool`;
                   `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                   `bstack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                   `wl_state_handler (s1:(A,num#C,FFI)wl_state) + 1`] list_rel_lastn) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP LIST_REL_abs_frame_eq_handler_val) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      can (find_term (fun t -> t = `Handler`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2033 *)
let dec_stack_stack_size = prove
 (`!(xs:((A)word_loc)list) st st'.
     wl_dec_stack xs st = SOME st' ==> wl_stack_size st = wl_stack_size st'`,
  MATCH_MP_TAC wl_dec_stack_ind THEN
  REWRITE_TAC[wl_dec_stack_def; GSYM NOT_SOME_NONE] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN
  REWRITE_TAC[stack_size_eq2] THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `handler:(num#num#num)option` THEN REWRITE_TAC[stack_size_frame_def]);;

let W2SP1AUX_wl_gc_SOME = prove
 (`!(s:(A,C,FFI)wl_state) s2.
     wl_gc s = SOME s2 <=>
     ?wl m st stk.
       wl_state_gc_fun s (wl_enc_stack (wl_state_stack s),wl_state_memory s,
                          wl_state_mdomain s,wl_state_store s) = SOME (wl,m,st) /\
       wl_dec_stack wl (wl_state_stack s) = SOME stk /\
       s2 = wl_state_stack_fupd (K stk) (wl_state_store_fupd (K st)
              (wl_state_memory_fupd (K m) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EQ_TAC THENL
   [STRIP_TAC THEN GVS(all_case_eqs()) THEN MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]]);;

(* HOL4 line 2045 *)
let gc_state_rel = prove
 (`!(s1:(A,num#C,FFI)wl_state) s2 ac k (t1:(A,C,FFI)stack_state) lens.
     wl_gc s1 = SOME s2 /\
     word_to_stackProof_state_rel ac k 0 0 s1 t1 lens 0
     ==> ?(t2:(A,C,FFI)stack_state).
           stack_gc t1 = SOME t2 /\
           word_to_stackProof_state_rel ac k 0 0 (wl_state_locals_fupd (K LN) s2) t2 lens 0 /\
           LENGTH (stack_state_stack t2) = LENGTH (stack_state_stack t1) /\
           stack_state_stack_space t2 = stack_state_stack_space t1`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[W2SP1AUX_wl_gc_SOME] THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `wl:((A)word_loc)list` (X_CHOOSE_THEN `m:A word->(A)word_loc`
       (X_CHOOSE_THEN `st:(store_name,(A)word_loc)fmap`
         (X_CHOOSE_THEN `stk:((A)stack_frame)list` STRIP_ASSUME_TAC))))
     ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP IMP_enc_stack) THEN
   W2SP1AUX_EXPAND_STATE_REL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; RICHAUX_DROP_CLAUSES; RICHAUX_TAKE_CLAUSES]) THEN
   SUBGOAL_THEN
    `stack_state_gc_fun (t1:(A,C,FFI)stack_state)
       (wl_enc_stack (wl_state_stack (s1:(A,num#C,FFI)wl_state)),wl_state_memory s1,
        wl_state_mdomain s1,fdomsub (stack_state_store t1) Handler) =
     SOME (wl,m,st)` ASSUME_TAC THENL
    [UNDISCH_TAC
      `wl_state_gc_fun (s1:(A,num#C,FFI)wl_state)
         (wl_enc_stack (wl_state_stack s1),wl_state_memory s1,wl_state_mdomain s1,
          wl_state_store s1) = SOME (wl,m,st)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(SPECL [`wl_enc_stack (wl_state_stack (s1:(A,num#C,FFI)wl_state))`;
     `wl_state_memory (s1:(A,num#C,FFI)wl_state)`; `wl_state_mdomain (s1:(A,num#C,FFI)wl_state)`;
     `stack_state_store (t1:(A,C,FFI)stack_state)`; `wl:((A)word_loc)list`;
     `m:A word->(A)word_loc`; `st:(store_name,(A)word_loc)fmap`]
     (REWRITE_RULE[gc_fun_ok_def]
        (ASSUME `gc_fun_ok (stack_state_gc_fun (t1:(A,C,FFI)stack_state))`))) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC(SPECL [`t1:(A,C,FFI)stack_state`; `s1:(A,num#C,FFI)wl_state`; `wl:((A)word_loc)list`;
                 `stk:((A)stack_frame)list`; `k:num`; `lens:num list`] dec_stack_lemma) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `word_to_stackProof_stack_rel k (wl_state_handler (s1:(A,num#C,FFI)wl_state))
        (wl_state_stack s1) (FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler)
        (DROP (stack_state_stack_space t1) (stack_state_stack t1))
        (LENGTH (stack_state_stack t1)) (stack_state_bitmaps t1) lens` THEN
     ASM_REWRITE_TAC[FLOOKUP_DEF];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `yy:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC
    `stack_state_stack_fupd
       (K (APPEND (TAKE (stack_state_stack_space t1) (stack_state_stack t1)) yy))
       (stack_state_store_fupd
          (K (st |+ (Handler,FAPPLY (stack_state_store t1) Handler)))
          (stack_state_regs_fupd (K FEMPTY)
             (stack_state_memory_fupd (K m) (t1:(A,C,FFI)stack_state))))` THEN
   SUBGOAL_THEN `LENGTH (TAKE (stack_state_stack_space t1)
                   (stack_state_stack (t1:(A,C,FFI)stack_state))) = stack_state_stack_space t1`
     ASSUME_TAC THENL [ASM_SIMP_TAC[LENGTH_TAKE]; ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [REWRITE_TAC[stack_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC[GSYM NOT_LE] THEN SIMP[];
     ALL_TAC;
     SIMP[LENGTH_APPEND] THEN ASM_ARITH_TAC;
     SIMP[]]) THEN
  (REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SIMP[LENGTH_APPEND; ADD_CLAUSES; RICHAUX_DROP_CLAUSES; FDOM_FUPDATE; IN_INSERT; FLOOKUP_UPDATE] THEN
   ASM_REWRITE_TAC[]) THEN
  (REPEAT CONJ_TAC THENL
    [ASM_SIMP_TAC[DOMSUB_NOT_IN_DOM];
     ASM_MESON_TAC[];
     UNDISCH_TAC `stack_size_rel 0 (wl_state_locals_size (s1:(A,num#C,FFI)wl_state))
        (wl_state_stack_limit s1) (wl_state_stack_max s1) (wl_state_stack s1)
        (stack_state_stack (t1:(A,C,FFI)stack_state)) (stack_state_stack_space t1) 0` THEN
     REWRITE_TAC[stack_size_rel_def; LENGTH_APPEND] THEN
     FIRST_ASSUM(SUBST1_TAC o MATCH_MP dec_stack_stack_size) THEN ASM_REWRITE_TAC[];
     FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THEN
     ASM_REWRITE_TAC[DROP_LENGTH_APPEND]]));;

(* HOL4 line 2075 (the HOL4 case on bool SOME T / SOME F is a conditional, *)
(* as in wl_alloc_def; HOL4's local name alloc_alt gets the theory prefix: *)
(* data_to_word_gcProof binds alloc_alt to a different theorem)            *)
let word_to_stackProof_alloc_alt = prove
 (CASE_TERM `!c names (s:(A,num#C,FFI)wl_state).
     ~(FST (wl_alloc c names s) = SOME (wl_Error:(A)wl_result))
     ==> wl_alloc c names s =
         match cut_envs names (wl_state_locals s) with
           NONE -> (SOME wl_Error,s)
         | SOME env ->
           (match wl_gc (wl_set_store AllocSize (wl_Word c)
                    (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
                       (wl_push_env env (NONE:(num#(A)wl_prog#num#num)option) s)))) with
              NONE -> (SOME wl_Error,s)
            | SOME s' ->
              (match wl_pop_env s' with
                 NONE -> (SOME wl_Error,s')
               | SOME s' ->
                 (match wl_get_store AllocSize s' with
                    NONE -> (SOME wl_Error,s')
                  | SOME w ->
                    (match wl_has_space w s' with
                       NONE -> (SOME wl_Error,s')
                     | SOME b ->
                         if b then (NONE,s')
                         else (SOME NotEnoughSpace,wl_flush_state T s')))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  CASES_ON `cut_envs names (wl_state_locals (s:(A,num#C,FFI)wl_state))` THEN SIMP[] THEN
  REWRITE_TAC[push_env_set_store; wl_set_store_def] THEN SIMP[] THEN
  EVERY_CASE_TAC THEN FS[]);;

(* HOL4 line 2105: Type result = :'a wordSem$result: written out as          *)
(* (A)wl_result.                                                              *)

let W2SP1AUX_CASES_VARS_TAC ty =
  W(fun (asl,w) ->
     let vs = setify (find_terms (fun t -> is_var t && type_of t = ty) w) in
     MAP_EVERY CASES_ON vs);;

(* HOL4 line 2107 *)
let word_to_stackProof_s_key_eq_stack_size = prove
 (`!(stack:((A)stack_frame)list) stack'.
     s_key_eq stack stack' ==> wl_stack_size stack = wl_stack_size stack'`,
  MATCH_MP_TAC s_key_eq_ind THEN REWRITE_TAC[s_key_eq_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[stack_size_eq2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  CASES_ON `x:(A)stack_frame` THEN CASES_ON `y:(A)stack_frame` THEN
  W2SP1AUX_CASES_VARS_TAC `:(num#num#num)option` THEN
  SIMP[s_frame_key_eq_def; stack_size_frame_def]);;

(* HOL4 line 2119 *)
let s_key_eq_push_env_locals_size = prove
 (`!env (opt1:(num#(A)wl_prog#num#num)option) (s:(A,C,FFI)wl_state) n l0 l opt2 stack'.
     s_key_eq (wl_state_stack (wl_push_env env opt1 s))
       (CONS (StackFrame n l0 l opt2) stack')
     ==> n = wl_state_locals_size s /\
         wl_stack_size (wl_state_stack s) = wl_stack_size stack'`,
  MATCH_MP_TAC wl_push_env_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_push_env_def] THEN
  W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                                   "env_to_list" with Failure _ -> false) w)) THEN
  SIMP[s_key_eq_def] THEN
  CASES_ON `opt2:(num#num#num)option` THEN REWRITE_TAC[s_frame_key_eq_def] THEN
  MESON_TAC[word_to_stackProof_s_key_eq_stack_size]);;

let W2SP1AUX_stack_rel_top_frame = prove
 (`!k h n l0 l (tail:((A)stack_frame)list) (th:((A)word_loc)option) rest_t len (bitmaps:(A word)list) f' lens.
     word_to_stackProof_stack_rel k h (CONS (StackFrame n l0 l NONE) tail) th rest_t len
       bitmaps (CONS f' lens)
     ==> ?w rest bits.
           rest_t = CONS w rest /\ full_read_bitmap bitmaps w = SOME bits /\
           LENGTH bits = f' /\ f' <= LENGTH rest /\
           word_to_stackProof_stack_rel k h tail th (DROP f' rest) len bitmaps lens /\
           (!n v. ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE
                  ==> adjust_names n < k + LENGTH bits /\
                      oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F /\
                      ALOOKUP (index_list (TAKE f' rest) k) (n DIV 2) = SOME v) /\
           filter_bitmap bits (index_list (TAKE f' rest) k) =
             SOME (MAP_FST adjust_names l,[]) /\
           the (f' + 1) n = f' + 1`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def; ALL] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `w:(A)word_loc` (X_CHOOSE_THEN `rest:((A)word_loc)list` SUBST_ALL_TAC))
    (ISPEC `rest_t:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE] THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_rel_aux_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)))) THEN
  (REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    SUBGOAL_THEN `SUC (LENGTH (tail:((A)stack_frame)list)) - (h + 1) =
                  SUC (LENGTH tail - (h + 1))` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[EL; TL] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h + 1 <= LENGTH (a:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)`
      (fun th -> SIMP_TAC[MATCH_MP LASTN_CONS th]) THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `the (LENGTH (TAKE (LENGTH (a:bool list)) (rest:((A)word_loc)list)) + 1) n =
                 LENGTH (TAKE (LENGTH a) rest) + 1` THEN
    ASM_SIMP_TAC[LENGTH_TAKE; ARITH_RULE `~(a < b) ==> b <= a`]]));;

let W2SP1AUX_cut_envs_domain = prove
 (`!names (locals:((A)word_loc)spt) envs.
     cut_envs names locals = SOME envs
     ==> domain (FST envs) SUBSET domain (FST names) /\
         domain (SND envs) SUBSET domain (SND names)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN SIMP[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[domain_inter] THEN SET_TAC[]);;

let W2SP1AUX_push_key_mem = prove
 (`!envs (s:(A,C,FFI)wl_state) n l0 l opt ls x.
     s_key_eq (wl_state_stack (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s))
       (CONS (StackFrame n l0 l opt) ls) /\
     wl_state_permute s = K I /\ MEM x (MAP FST l)
     ==> x IN domain (SND envs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def] THEN
  CASES_ON `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
              (wl_state_permute (s:(A,C,FFI)wl_state))` THEN
  SIMP[s_key_eq_def] THEN CASES_ON `opt:(num#num#num)option` THEN
  REWRITE_TAC[s_frame_key_eq_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    is_const t && fst(dest_const t) = "env_to_list")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP env_to_list_K_I_IMP) THEN
  FIRST_ASSUM(fun th -> if (try fst(dest_const(fst(strip_comb(concl th)))) = "PERM"
                            with Failure _ -> false)
                        then ASSUME_TAC (MATCH_MP MEM_PERM th) else NO_TAC) THEN
  UNDISCH_TAC `MEM (x:num) (MAP FST (l:(num#(A)word_loc)list))` THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      rhs(concl th) = `MAP FST (l:(num#(A)word_loc)list)`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `p2:(A)word_loc` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `p2:(A)word_loc` THEN
  ASM_MESON_TAC[MEM_toAList]);;

let W2SP1AUX_pop_state_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t5:(A,C,FFI)stack_state) envs names s2 s3
     (t2:(A,C,FFI)stack_state) lens.
     (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
     (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
     1 <= f /\
     word_to_stackProof_state_rel ac k f f' s t5 lens 0 /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     s_key_eq (wl_state_stack (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s))
       (wl_state_stack s2) /\
     word_to_stackProof_state_rel ac k 0 0 (wl_state_locals_fupd (K LN) s2) t2
       (CONS f' lens) 0 /\
     wl_pop_env s2 = SOME s3
     ==> word_to_stackProof_state_rel ac k f f' s3 t2 lens 0`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP push_env_pop_env_s_key_eq) THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num option` (X_CHOOSE_THEN `l:(num#(A)word_loc)list`
     (X_CHOOSE_THEN `ls:((A)stack_frame)list` (X_CHOOSE_THEN `opt:(num#num#num)option`
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:(A,num#C,FFI)wl_state` STRIP_ASSUME_TAC)))))) THEN
   SUBGOAL_THEN `y:(A,num#C,FFI)wl_state = s3` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `wl_pop_env (s2:(A,num#C,FFI)wl_state) = SOME s3` THEN
     ASM_REWRITE_TAC[option_INJ]; ALL_TAC] THEN
   SUBGOAL_THEN `opt:(num#num#num)option = NONE` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `s_key_eq (wl_state_stack (wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt)
         (NONE:(num#(A)wl_prog#num#num)option) (s:(A,num#C,FFI)wl_state)))
       (wl_state_stack (s2:(A,num#C,FFI)wl_state))` THEN
     ASM_REWRITE_TAC[wl_push_env_def] THEN
     W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                                   "env_to_list" with Failure _ -> false) w)) THEN
     SIMP[s_key_eq_def] THEN CASES_ON `opt:(num#num#num)option` THEN
     REWRITE_TAC[s_frame_key_eq_def];
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_state_rel_basic o check (fun th -> can (find_term (fun t -> t = `t5:(A,C,FFI)stack_state`)) (concl th))) THEN
   SUBGOAL_THEN `f = f' + 1` SUBST_ALL_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (MP_TAC(ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`; `NONE:(num#(A)wl_prog#num#num)option`;
                  `s:(A,num#C,FFI)wl_state`; `n:num option`; `toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))`;
                  `l:(num#(A)word_loc)list`; `NONE:(num#num#num)option`; `ls:((A)stack_frame)list`]
          s_key_eq_push_env_locals_size) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
   SUBGOAL_THEN
    `wl_pop_env (s2:(A,num#C,FFI)wl_state) =
     SOME (wl_state_locals_fupd
             (K (union (fromAList l)
                   (fromAList (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))))))
             (wl_state_stack_fupd (K ls) (wl_state_locals_size_fupd (K n) s2)))` MP_TAC THENL
    [REWRITE_TAC[wl_pop_env_def] THEN
     FIRST_ASSUM(fun th -> if is_eq (concl th) &&
         lhs (concl th) = `wl_state_stack (s2:(A,num#C,FFI)wl_state)`
       then REWRITE_TAC[th] else NO_TAC) THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th -> if (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_pop_env"
                            with Failure _ -> false) then REWRITE_TAC[th] else NO_TAC) THEN
   REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
   UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0 (wl_state_locals_fupd (K LN) (s2:(A,num#C,FFI)wl_state))
       (t2:(A,C,FFI)stack_state) (CONS f' lens) 0` THEN
   REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SIMP[ADD_CLAUSES; RICHAUX_DROP_CLAUSES; RICHAUX_TAKE_CLAUSES] THEN STRIP_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP1AUX_stack_rel_top_frame o check (fun th ->
     (try fst(dest_const(fst(strip_comb(concl th)))) = "word_to_stackProof_stack_rel"
      with Failure _ -> false))) THEN
   DISCH_THEN(X_CHOOSE_THEN `w:(A)word_loc` (X_CHOOSE_THEN `rest:((A)word_loc)list`
     (X_CHOOSE_THEN `bits:bool list` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~(f' = 0)` ASSUME_TAC THENL
    [DISCH_TAC THEN UNDISCH_TAC `if f' = 0 then f' + 1 = 0 else f' + 1 = f' + 1` THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `wl_state_permute (s:(A,num#C,FFI)wl_state) = K I` ASSUME_TAC THENL
    [UNDISCH_TAC `word_to_stackProof_state_rel ac k (f' + 1) f' (s:(A,num#C,FFI)wl_state)
       (t5:(A,C,FFI)stack_state) lens 0` THEN
     REWRITE_TAC[word_to_stackProof_state_rel_def] THEN SIMP_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_cut_envs_domain) THEN
   REPEAT CONJ_TAC) THENL
  [(ASM_MESON_TAC[]);
   (UNDISCH_TAC `DROP (stack_state_stack_space t2) (stack_state_stack (t2:(A,C,FFI)stack_state)) =
                CONS w rest` THEN
   DISCH_THEN(MP_TAC o AP_TERM `LENGTH:((A)word_loc)list->num`) THEN
   REWRITE_TAC[LENGTH_DROP; LENGTH] THEN ASM_ARITH_TAC);
   (SIMP_TAC[wf_union; wf_fromAList]);
   (UNDISCH_TAC `stack_size_rel 0 (wl_state_locals_size (s2:(A,num#C,FFI)wl_state))
     (wl_state_stack_limit s2) (wl_state_stack_max s2)
     (CONS (StackFrame (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
       (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))) l NONE) ls)
     (stack_state_stack (t2:(A,C,FFI)stack_state)) (stack_state_stack_space t2) 0` THEN
   UNDISCH_TAC `the (f' + 1) (wl_state_locals_size (s:(A,num#C,FFI)wl_state)) = f' + 1` THEN
   REWRITE_TAC[stack_size_rel_def; stack_size_eq; SUB_0; ARITH_RULE `~(f' + 1 = 0)`] THEN
   CASES_ON `wl_state_locals_size (s:(A,num#C,FFI)wl_state)` THEN
   CASES_ON `wl_stack_size (ls:((A)stack_frame)list)` THEN SIMP[the_def] THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);
   (REWRITE_TAC[GSYM ADD1; RICHAUX_DROP_CLAUSES] THEN ASM_REWRITE_TAC[]);
   (SUBGOAL_THEN `LENGTH (TAKE f' (rest:((A)word_loc)list)) = f'` ASSUME_TAC THENL
    [ASM_SIMP_TAC[LENGTH_TAKE]; ALL_TAC] THEN
   REWRITE_TAC[lookup_union; lookup_fromAList; lookup_fromAList_toAList] THEN
   REWRITE_TAC[GSYM ADD1; RICHAUX_TAKE_CLAUSES] THEN
   X_GEN_TAC `m:num` THEN X_GEN_TAC `v:(A)word_loc` THEN
   CASES_ON `ALOOKUP (l:(num#(A)word_loc)list) m` THEN SIMP[] THEN STRIP_TAC) THENL
  [(SUBGOAL_THEN `EVEN m /\ k <= m DIV 2` STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t -> t = `FST (names:cutsets)`)) (concl th) && is_forall (concl th))) THEN
     UNDISCH_TAC `domain (FST (envs:((A)word_loc)spt#((A)word_loc)spt)) SUBSET domain (FST (names:cutsets))` THEN
     REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
     REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `v:(A)word_loc`] o check (fun th -> can (find_term (fun t -> t = `adjust_names`)) (concl th) && is_forall (concl th))) THEN
   ASM_REWRITE_TAC[ALOOKUP_toAList; adjust_names_def] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[NOT_LT] THEN
   UNDISCH_TAC `ALOOKUP (index_list (TAKE f' (rest:((A)word_loc)list)) k) (m DIV 2) = SOME v` THEN
   ASM_SIMP_TAC[ALOOKUP_index_list; ARITH_RULE `m < k + f ==> m < f + k`] THEN
   SUBGOAL_THEN `f' - (m DIV 2 - k) = SUC ((f' + k) - (m DIV 2 + 1))` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[oEL_def; NOT_SUC; SUC_SUB1] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_ARITH_TAC);
   (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) && rhs (concl th) = `v:(A)word_loc`)) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM o check (fun th -> can (find_term (fun t -> t = `ALOOKUP (l:(num#(A)word_loc)list) m`)) (concl th))) THEN
   SUBGOAL_THEN `EVEN m /\ k <= m DIV 2` STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t -> t = `SND (names:cutsets)`)) (concl th) && is_forall (concl th))) THEN
     UNDISCH_TAC `domain (SND (envs:((A)word_loc)spt#((A)word_loc)spt)) SUBSET domain (SND (names:cutsets))` THEN
     REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC (INST_TYPE [`:num#C`,`:C`] W2SP1AUX_push_key_mem) THEN
     MAP_EVERY EXISTS_TAC [`s:(A,num#C,FFI)wl_state`; `wl_state_locals_size (s:(A,num#C,FFI)wl_state)`;
       `toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))`; `l:(num#(A)word_loc)list`;
       `NONE:(num#num#num)option`; `ls:((A)stack_frame)list`] THEN
     ASM_REWRITE_TAC[MEM_MAP] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[]; EXISTS_TAC `(m:num,v:(A)word_loc)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   SUBGOAL_THEN `MEM (m DIV 2,v:(A)word_loc) (index_list (TAKE f' (rest:((A)word_loc)list)) k)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC filter_bitmap_MEM THEN
     MAP_EVERY EXISTS_TAC [`bits:bool list`; `MAP_FST adjust_names (l:(num#(A)word_loc)list)`] THEN
     ASM_REWRITE_TAC[MAP_FST_def; MEM_MAP; EXISTS_PAIR_THM] THEN
     MAP_EVERY EXISTS_TAC [`m:num`; `v:(A)word_loc`] THEN ASM_REWRITE_TAC[adjust_names_def];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP MEM_index_list_EL) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP MEM_index_list_LIM) THEN
   ASM_REWRITE_TAC[NOT_LT] THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN `f' - (m DIV 2 - k) = SUC (f' - ((m DIV 2 - k) + 1))` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[oEL_def; NOT_SUC; SUC_SUB1; oEL_THM] THEN
   ASM_REWRITE_TAC[ARITH_RULE `f - (a + 1) < f <=> ~(f = 0)`] THEN ASM_ARITH_TAC)]]);;

let W2SP1AUX_state_rel_store = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> wl_state_store s = fdomsub (stack_state_store t) Handler /\
         wl_state_clock s = stack_state_clock t /\ stack_state_ffi t = wl_state_ffi s`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[]);;

let W2SP1AUX_has_space_store = prove
 (`!(s:(A,C,FFI)wl_state) st w.
     wl_state_store s = fdomsub st Handler
     ==> wl_get_store AllocSize s = FLOOKUP st AllocSize /\
         wl_has_space w s = stack_has_space w st`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[wl_get_store_def; wl_has_space_def; stack_has_space_def] THEN
  SIMP_TAC[DOMSUB_FLOOKUP_NEQ; distinctness "store_name"]);;

(* HOL4 line 2131 *)
let alloc_IMP_alloc = prove
 (`!c names (s:(A,num#C,FFI)wl_state) (res:((A)wl_result)option) s1 k f ac f'
     (t5:(A,C,FFI)stack_state) lens envs.
     wl_alloc c names s = (res,s1) /\
     (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
     (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
     1 <= f /\
     word_to_stackProof_state_rel ac k f f' s t5 lens 0 /\
     word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s)))
       t5 (CONS f' lens) 0 /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     ~(res = SOME wl_Error)
     ==> ?(t1:(A,C,FFI)stack_state) res1.
           stackSem_alloc c t5 = (res1:((A)stack_result)option,t1) /\
           if res = NONE then
             res1 = NONE /\
             word_to_stackProof_state_rel ac k f f' s1 t1 lens 0 /\
             LENGTH (stack_state_stack t1) = LENGTH (stack_state_stack t5) /\
             stack_state_stack_space t1 = stack_state_stack_space t5
           else
             res = SOME NotEnoughSpace /\ res1 = SOME (stackSem_Halt (wl_Word (word 1))) /\
             wl_state_clock s1 = stack_state_clock t1 /\
             wl_state_ffi s1 = stack_state_ffi t1`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`c:A word`; `names:cutsets`; `s:(A,num#C,FFI)wl_state`]
            word_to_stackProof_alloc_alt) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) =
       `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` then REWRITE_TAC[th] else NO_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `wl_Word (c:A word)` o MATCH_MP state_rel_set_store_0 o
     check (fun th -> can (find_term (fun t -> t = `wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt)
        (NONE:(num#(A)wl_prog#num#num)option) (s:(A,num#C,FFI)wl_state)`)) (concl th))) THEN
   REPEAT DISCH_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) =
        `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "wl_gc"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_TAC) THEN
  (FIRST_ASSUM(fun th8 ->
     if is_eq (concl th8) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th8))))) = "wl_gc" with Failure _ -> false)
     then FIRST_ASSUM(fun th7 -> MP_TAC (MATCH_MP gc_state_rel (CONJ th8 th7))) THEN
          ASSUME_TAC (CAKE_SIMP_RULE [wl_set_store_def] (MATCH_MP gc_s_key_eq th8))
     else NO_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) =
        `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "wl_pop_env"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_TAC) THEN
  (MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                  `t5:(A,C,FFI)stack_state`; `envs:((A)word_loc)spt#((A)word_loc)spt`;
                  `names:cutsets`; `a:(A,num#C,FFI)wl_state`; `a':(A,num#C,FFI)wl_state`;
                  `t2:(A,C,FFI)stack_state`; `lens:num list`] W2SP1AUX_pop_state_rel) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_state_rel_store o
     check (fun th -> can (find_term (fun t -> t = `a':(A,num#C,FFI)wl_state`)) (concl th))) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP1AUX_has_space_store o
     check (fun th -> is_eq (concl th) && lhs (concl th) = `wl_state_store (a':(A,num#C,FFI)wl_state)`)) THEN
   REWRITE_TAC[stackSem_alloc_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) =
        `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
   ASM_REWRITE_TAC[] THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "FLOOKUP"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "stack_has_space"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH (stack_state_stack (t2:(A,C,FFI)stack_state)) =
      LENGTH (stack_state_stack (stack_set_store AllocSize (wl_Word c) (t5:(A,C,FFI)stack_state)))` THEN
    UNDISCH_TAC `stack_state_stack_space (t2:(A,C,FFI)stack_state) =
      stack_state_stack_space (stack_set_store AllocSize (wl_Word c) (t5:(A,C,FFI)stack_state))` THEN
    REWRITE_TAC[stack_set_store_def] THEN SIMP[];
    MAP_EVERY EXISTS_TAC [`stack_empty_env (t2:(A,C,FFI)stack_state)`;
                          `SOME (stackSem_Halt (wl_Word (word 1:A word)))`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
    REWRITE_TAC[wl_flush_state_def; stack_empty_env_def] THEN SIMP[] THEN ASM_REWRITE_TAC[]]));;

let W2SP1AUX_dec_stack_empty_frame = prove
 (`!(xs:((A)word_loc)list) n st.
     wl_dec_stack xs (CONS (StackFrame n [] [] NONE) st) =
     OPTION_MAP (CONS (StackFrame n [] [] NONE)) (wl_dec_stack xs st)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[wl_dec_stack_def; LENGTH; CONJUNCT1 LT; RICHAUX_DROP_CLAUSES; MAP;
              RICHAUX_TAKE_CLAUSES; ZIP] THEN
  REPEAT GEN_TAC THEN
  W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                                   "wl_dec_stack" with Failure _ -> false) w)) THEN
  SIMP[OPTION_MAP_DEF]);;

(* HOL4 line 2314 *)
let word_gc_empty_frame = prove
 (`!(s:(A,C,FFI)wl_state) n x y.
     wl_gc (wl_state_stack_fupd (K (CONS (StackFrame n [] [] NONE) (wl_state_stack s))) s) =
       SOME x /\
     wl_pop_env x = SOME y
     ==> wl_state_locals y = LN /\
         wl_gc s = SOME (wl_state_locals_fupd (K (wl_state_locals s))
                           (wl_state_locals_size_fupd (K (wl_state_locals_size s)) y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[wl_enc_stack_def; MAP; APPEND; W2SP1AUX_dec_stack_empty_frame] THEN
  STRIP_TAC THEN GVS(wl_pop_env_def :: all_case_eqs()) THEN
  REWRITE_TAC[fromAList_def; union_def] THEN
  SIMP[wl_state_component_equality]);;

(* HOL4 line 2327 *)
let inter_eq_empty_2 = prove
 (`!(t:B spt) (s:A spt). domain t = {} ==> inter s t = LN`,
  SIMP_TAC[inter_eq_LN; DISJOINT_EMPTY]);;

let W2SP1AUX_cut_envs_empty = prove
 (`!names (locals:((A)word_loc)spt).
     domain (FST names) = {} /\ domain (SND names) = {}
     ==> cut_envs names locals = SOME (LN,LN)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN ASM_SIMP_TAC[inter_eq_empty_2] THEN SIMP[]);;

let W2SP1AUX_push_env_empty = prove
 (`!(s:(A,C,FFI)wl_state).
     wl_state_permute s = K I
     ==> wl_push_env (LN,LN) (NONE:(num#(A)wl_prog#num#num)option) s =
         wl_state_stack_fupd
           (K (CONS (StackFrame (wl_state_locals_size s) [] [] NONE) (wl_state_stack s)))
           (wl_state_stack_max_fupd
              (K (OPTION_MAP2 MAX (wl_state_stack_max s)
                    (wl_stack_size (CONS (StackFrame (wl_state_locals_size s) [] [] NONE)
                                     (wl_state_stack s))))) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `[]:(num#(A)word_loc)list`
    (REWRITE_RULE[SORTS_DEF] SORTS_SORT_key_val_compare)) THEN
  REWRITE_TAC[PERM_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_push_env_def; env_to_list_def; IL2AUX_toAList_LN; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[K_THM; list_rearrange_I; I_THM] THEN
  SIMP[wl_state_component_equality] THEN REWRITE_TAC[FUN_EQ_THM; K_THM]);;

let W2SP1AUX_state_rel_reset_locals = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens.
     word_to_stackProof_state_rel ac k 0 0 s t lens 0
     ==> word_to_stackProof_state_rel ac k 0 0
           (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
              (wl_state_stack_max_fupd (K (OPTION_MAP2 MAX (wl_state_stack_max s)
                 (wl_stack_size (CONS (StackFrame (wl_state_locals_size s) [] [] NONE)
                                  (wl_state_stack s))))) s)))
           t lens 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `stack_size_rel 0 (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
     (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
     (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
  REWRITE_TAC[stack_size_rel_def; stack_size_eq] THEN
  CASES_ON `wl_state_stack_max (s:(A,num#C,FFI)wl_state)` THEN
  CASES_ON `wl_state_locals_size (s:(A,num#C,FFI)wl_state)` THEN
  CASES_ON `wl_stack_size (wl_state_stack (s:(A,num#C,FFI)wl_state))` THEN
  REWRITE_TAC[OPTION_MAP2_THM; IS_SOME_DEF; option_INJ; GSYM NOT_SOME_NONE; NOT_SOME_NONE] THEN
  SIMP[] THEN ARITH_TAC);;

let W2SP1AUX_state_rel_locals_size = prove
 (`!ac k (y:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens.
     word_to_stackProof_state_rel ac k 0 0 (wl_state_locals_size_fupd (K (SOME 0)) y) t lens 0 /\
     (IS_SOME (wl_state_stack_max y) ==> IS_SOME (wl_state_locals_size y))
     ==> word_to_stackProof_state_rel ac k 0 0 y t lens 0`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   UNDISCH_TAC `stack_size_rel 0 (SOME 0) (wl_state_stack_limit (y:(A,num#C,FFI)wl_state))
      (wl_state_stack_max y) (wl_state_stack y)
      (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
   UNDISCH_TAC `IS_SOME (wl_state_stack_max (y:(A,num#C,FFI)wl_state)) ==>
                IS_SOME (wl_state_locals_size y)` THEN
   REWRITE_TAC[stack_size_rel_def] THEN
   CASES_ON `wl_state_stack_max (y:(A,num#C,FFI)wl_state)` THEN
   REWRITE_TAC[IS_SOME_DEF; option_INJ; GSYM NOT_SOME_NONE; NOT_SOME_NONE] THEN
   MESON_TAC[]));;

let W2SP1AUX_SPLIT_PAIR_VAR_TAC =
  W(fun (asl,w) ->
     match filter (fun t -> is_type (type_of t) &&
                            fst(dest_type(type_of t)) = "prod") (frees w) with
       [] -> NO_TAC
     | v::_ -> STRUCT_CASES_TAC (ISPEC v PAIR_SURJECTIVE));;

let W2SP1AUX_pop_locals_size = prove
 (`!(x:(A,C,FFI)wl_state) y n l0 l opt ls.
     wl_state_stack x = CONS (StackFrame n l0 l opt) ls /\ wl_pop_env x = SOME y
     ==> wl_state_locals_size y = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_pop_env (x:(A,C,FFI)wl_state) = SOME y` THEN
  REWRITE_TAC[wl_pop_env_def] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `opt:(num#num#num)option` THEN TRY(REPEAT W2SP1AUX_SPLIT_PAIR_VAR_TAC) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let W2SP1AUX_s_key_eq_cons_frame = prove
 (`!n l0 l opt (xs:((A)stack_frame)list) ys.
     s_key_eq (CONS (StackFrame n l0 l opt) xs) ys
     ==> ?l' ys'. ys = CONS (StackFrame n l0 l' opt) ys'`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  REWRITE_TAC[s_key_eq_def; CONS_11] THEN
  W(fun (asl,w) -> CASES_ON (find_term (fun t -> is_var t && type_of t = `:(A)stack_frame`) w)) THEN
  CASES_ON `opt:(num#num#num)option` THEN
  W2SP1AUX_CASES_VARS_TAC `:(num#num#num)option` THEN
  REWRITE_TAC[s_frame_key_eq_def; injectivity "stack_frame"] THEN MESON_TAC[]);;

(* HOL4 line 2334 *)
let alloc_IMP_alloc2 = prove
 (`!c names (s:(A,num#C,FFI)wl_state) (res:((A)wl_result)option) s1 ac k
     (t:(A,C,FFI)stack_state) lens.
     wl_alloc c names s = (res,s1) /\
     word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\
     domain (FST names) = {} /\
     domain (SND names) = {} /\
     ~(res = SOME wl_Error)
     ==> ?(t1:(A,C,FFI)stack_state) res1.
           stackSem_alloc c t = (res1:((A)stack_result)option,t1) /\
           if res = NONE then
             res1 = NONE /\
             word_to_stackProof_state_rel ac k 0 0 s1 t1 lens 0 /\
             LENGTH (stack_state_stack t1) = LENGTH (stack_state_stack t) /\
             stack_state_stack_space t1 = stack_state_stack_space t
           else
             res = SOME NotEnoughSpace /\ res1 = SOME (stackSem_Halt (wl_Word (word 1))) /\
             wl_state_clock s1 = stack_state_clock t1 /\
             wl_state_ffi s1 = stack_state_ffi t1`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `wl_state_permute (s:(A,num#C,FFI)wl_state) = K I` ASSUME_TAC THENL
    [UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0 (s:(A,num#C,FFI)wl_state)
       (t:(A,C,FFI)stack_state) lens 0` THEN
     REWRITE_TAC[word_to_stackProof_state_rel_def] THEN SIMP_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:A word`; `names:cutsets`; `s:(A,num#C,FFI)wl_state`]
            word_to_stackProof_alloc_alt) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) =
       `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` then REWRITE_TAC[th] else NO_TAC) THEN
   ASM_SIMP_TAC[W2SP1AUX_cut_envs_empty] THEN CASE_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[W2SP1AUX_push_env_empty] THEN
   ABBREV_TAC `M = OPTION_MAP2 MAX (wl_state_stack_max (s:(A,num#C,FFI)wl_state))
      (wl_stack_size (CONS (StackFrame (wl_state_locals_size s) [] [] NONE) (wl_state_stack s)))` THEN
   ABBREV_TAC `B = wl_set_store AllocSize (wl_Word c) (wl_state_locals_fupd (K LN)
      (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_stack_max_fupd (K M)
         (s:(A,num#C,FFI)wl_state))))` THEN
   SUBGOAL_THEN
    `wl_set_store AllocSize (wl_Word c) (wl_state_locals_fupd (K LN)
       (wl_state_locals_size_fupd (K (SOME 0))
         (wl_state_stack_fupd
           (K (CONS (StackFrame (wl_state_locals_size s) [] [] NONE) (wl_state_stack s)))
           (wl_state_stack_max_fupd (K M) (s:(A,num#C,FFI)wl_state))))) =
     wl_state_stack_fupd
       (K (CONS (StackFrame (wl_state_locals_size s) [] [] NONE) (wl_state_stack B))) B`
    SUBST1_TAC THENL
    [EXPAND_TAC "B" THEN REWRITE_TAC[wl_set_store_def] THEN SIMP[wl_state_component_equality];
     ALL_TAC] THEN
   DISCH_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) =
        `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "wl_gc"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "wl_pop_env"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_TAC) THEN
  (FIRST_ASSUM(fun th8 ->
     if is_eq (concl th8) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th8))))) = "wl_gc" with Failure _ -> false)
     then FIRST_ASSUM(fun th9 -> STRIP_ASSUME_TAC (MATCH_MP word_gc_empty_frame (CONJ th8 th9))) THEN
          ASSUME_TAC (CAKE_SIMP_RULE [] (MATCH_MP gc_s_key_eq th8))
     else NO_TAC) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `l':(num#(A)word_loc)list` (X_CHOOSE_THEN `ys':((A)stack_frame)list`
     ASSUME_TAC) o MATCH_MP W2SP1AUX_s_key_eq_cons_frame o check (fun th ->
       (try fst(dest_const(fst(strip_comb(concl th)))) = "s_key_eq" with Failure _ -> false))) THEN
   SUBGOAL_THEN `wl_state_locals_size (a':(A,num#C,FFI)wl_state) =
                 wl_state_locals_size (s:(A,num#C,FFI)wl_state)` ASSUME_TAC THENL
    [MATCH_MP_TAC W2SP1AUX_pop_locals_size THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `word_to_stackProof_state_rel ac k 0 0 B
     (stack_set_store AllocSize (wl_Word c) (t:(A,C,FFI)stack_state)) lens 0` ASSUME_TAC THENL
    [EXPAND_TAC "B" THEN MATCH_MP_TAC state_rel_set_store_0 THEN EXPAND_TAC "M" THEN
     MATCH_MP_TAC W2SP1AUX_state_rel_reset_locals THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th12 ->
     if is_eq (concl th12) && lhs (concl th12) = `wl_gc (B:(A,num#C,FFI)wl_state)`
     then FIRST_ASSUM(fun th -> MP_TAC (MATCH_MP gc_state_rel (CONJ th12 th))) else NO_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN
    `wl_state_locals_fupd (K LN)
       (wl_state_locals_fupd (K (wl_state_locals (B:(A,num#C,FFI)wl_state)))
          (wl_state_locals_size_fupd (K (wl_state_locals_size B)) a')) =
     wl_state_locals_size_fupd (K (SOME 0)) (a':(A,num#C,FFI)wl_state)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [EXPAND_TAC "B" THEN REWRITE_TAC[wl_set_store_def] THEN
     SIMP[wl_state_component_equality]; ALL_TAC] THEN
   SUBGOAL_THEN `word_to_stackProof_state_rel ac k 0 0 a' (t2:(A,C,FFI)stack_state) lens 0`
     ASSUME_TAC THENL
    [MATCH_MP_TAC W2SP1AUX_state_rel_locals_size THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun th -> if is_eq (concl th) &&
         (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_pop_env" with Failure _ -> false)
       then STRIP_ASSUME_TAC (MATCH_MP wl_pop_env_const th) else NO_TAC) THEN
     FIRST_ASSUM(fun th -> if is_eq (concl th) &&
         (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_gc" with Failure _ -> false) &&
         not (lhs (concl th) = `wl_gc (B:(A,num#C,FFI)wl_state)`)
       then STRIP_ASSUME_TAC (MATCH_MP gc_const th) else NO_TAC) THEN
     ASM_REWRITE_TAC[] THEN SIMP[] THEN EXPAND_TAC "B" THEN REWRITE_TAC[wl_set_store_def] THEN
     SIMP[] THEN EXPAND_TAC "M" THEN
     REWRITE_TAC[stack_size_eq] THEN
     CASES_ON `wl_state_stack_max (s:(A,num#C,FFI)wl_state)` THEN
     CASES_ON `wl_state_locals_size (s:(A,num#C,FFI)wl_state)` THEN
     CASES_ON `wl_stack_size (wl_state_stack (s:(A,num#C,FFI)wl_state))` THEN
     REWRITE_TAC[OPTION_MAP2_THM; IS_SOME_DEF];
     ALL_TAC]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP1AUX_state_rel_store o
     check (fun th -> concl th = `word_to_stackProof_state_rel ac k 0 0 (a':(A,num#C,FFI)wl_state)
                                    (t2:(A,C,FFI)stack_state) lens 0`)) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP1AUX_has_space_store o
     check (fun th -> is_eq (concl th) && lhs (concl th) = `wl_state_store (a':(A,num#C,FFI)wl_state)`)) THEN
   REWRITE_TAC[stackSem_alloc_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) =
        `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
   ASM_REWRITE_TAC[] THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "FLOOKUP"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "stack_has_space"
                                         with Failure _ -> false) w)) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH (stack_state_stack (t2:(A,C,FFI)stack_state)) =
      LENGTH (stack_state_stack (stack_set_store AllocSize (wl_Word c) (t:(A,C,FFI)stack_state)))` THEN
    UNDISCH_TAC `stack_state_stack_space (t2:(A,C,FFI)stack_state) =
      stack_state_stack_space (stack_set_store AllocSize (wl_Word c) (t:(A,C,FFI)stack_state))` THEN
    REWRITE_TAC[stack_set_store_def] THEN SIMP[];
    MAP_EVERY EXISTS_TAC [`stack_empty_env (t2:(A,C,FFI)stack_state)`;
                          `SOME (stackSem_Halt (wl_Word (word 1:A word)))`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
    REWRITE_TAC[wl_flush_state_def; stack_empty_env_def] THEN SIMP[] THEN ASM_REWRITE_TAC[]]));;

(* HOL4 line 2411 (the second value of Exception is w3: one quotation      *)
(* types a variable once) *)
let compile_result_def = cake_def
  `(compile_result (wl_Result (w1:(A)word_loc) w2) = stack_Result w1) /\
   (compile_result (wl_Exception w1 w3) = stack_Exception w1) /\
   (compile_result wl_TimeOut = stack_TimeOut) /\
   (compile_result NotEnoughSpace = stackSem_Halt (wl_Word (word 1))) /\
   (compile_result (wl_FinalFFI f) = stack_FinalFFI f) /\
   (compile_result (wordSem_Break k) = stackSem_Break k) /\
   (compile_result (wordSem_Continue k) = stackSem_Continue k) /\
   (compile_result wl_Error = stack_Error)`;;

let _ = cake_add_simps [compile_result_def];;

(* HOL4 line 2422 *)
let Halt_EQ_compile_result = prove
 (`!(z:(A)wl_result).
     (stackSem_Halt (wl_Word (word 1)) = compile_result z <=> z = NotEnoughSpace) /\
     (good_dimindex (:A) ==> ~(stackSem_Halt (wl_Word (word 2:A word)) = compile_result z))`,
  GEN_TAC THEN CASES_ON `z:(A)wl_result` THEN REWRITE_TAC[compile_result_def] THEN SIMP[] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP W2SP1AUX_good_dimword) THEN
  SUBGOAL_THEN `2 < dimword(:A) /\ 1 < dimword(:A)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT; ARITH_EQ]]);;

(* HOL4 line 2429: val stack_evaluate_add_clock_NONE =                       *)
(* stackPropsTheory.evaluate_add_clock |> Q.SPECL [p,s,NONE] |>        *)
(* SIMP_RULE (srw_ss()) [] |> GEN_ALL (a derived theorem)                     *)
let stack_evaluate_add_clock_NONE = prove
 (`!p (s:(A,C,FFI)stack_state) s1 ck.
     stack_evaluate (p,s) = (NONE,s1)
     ==> stack_evaluate (p,stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
         (NONE,stack_state_clock_fupd (K (stack_state_clock s1 + ck)) s1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`ck:num`,`extra:num`]
    (ISPECL [`p:(A)stack_prog`; `s:(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`;
             `s1:(A,C,FFI)stack_state`] stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[GSYM NOT_SOME_NONE]);;

(* HOL4 line 2433 *)
let push_locals_def = cake_def
  `push_locals l0 l (s:(A,C,FFI)wl_state) =
     wl_state_locals_fupd (K LN)
       (wl_state_locals_size_fupd (K (SOME 0))
          (wl_state_stack_fupd
             (K (CONS (StackFrame (wl_state_locals_size s) l0 l NONE) (wl_state_stack s)))
             s))`;;

(* HOL4 line 2438 *)
let stack_rel_aux_LENGTH = prove
 (`!k len (xs:((A)stack_frame)list) ys.
     stack_rel_aux k len xs ys ==> LENGTH xs = LENGTH ys`,
  MATCH_MP_TAC stack_rel_aux_ind THEN REWRITE_TAC[stack_rel_aux_def; LENGTH] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let W2SP1AUX_stack_rel_aux_TL = prove
 (`!k len (x:(A)stack_frame) xs y ys.
     stack_rel_aux k len (CONS x xs) (CONS y ys) ==> stack_rel_aux k len xs ys`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)stack_frame` THEN
  MP_TAC(ISPEC `y:((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list`
    PAIR_SURJECTIVE) THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  W2SP1AUX_CASES_VARS_TAC `:(num#num#num)option` THEN
  W2SP1AUX_CASES_VARS_TAC `:((A)word_loc#(A)word_loc)option` THEN
  REPEAT W2SP1AUX_SPLIT_PAIR_VAR_TAC THEN
  REWRITE_TAC[stack_rel_aux_def] THEN SIMP_TAC[]);;

(* HOL4 line 2447 *)
let stack_rel_aux_LASTN = prove
 (`!k len (xs:((A)stack_frame)list) ys n.
     stack_rel_aux k len xs ys ==> stack_rel_aux k len (LASTN n xs) (LASTN n ys)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
  STRUCT_CASES_TAC(ISPEC `ys:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` list_CASES) THEN
  REWRITE_TAC[stack_rel_aux_def; LASTN_ALT] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_rel_aux_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP1AUX_stack_rel_aux_TL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SUC_INJ]) THEN
  ASM_REWRITE_TAC[LENGTH] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2464 *)
let abs_stack_to_stack_LENGTH = prove
 (`!(bs:(A word)list) (wstack:((B)stack_frame)list) sstack lens stack.
     abs_stack bs wstack sstack lens = SOME stack ==> handler_val stack = LENGTH sstack`,
  MATCH_MP_TAC abs_stack_ind THEN REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN
  ASM_REWRITE_TAC[handler_val_def; LENGTH; LENGTH_TAKE_EQ_MIN; LENGTH_DROP] THEN
  ASM_ARITH_TAC);;

let W2SP1AUX_LASTN_APPEND_DROP = prove
 (`!m (pre:A list) l j. m + j <= LENGTH l ==> LASTN m (APPEND pre l) = LASTN m (DROP j l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LASTN_DROP_UNCOND; LENGTH_APPEND; LENGTH_DROP] THEN
  REWRITE_TAC[DROP_APPEND; DROP_DROP_T] THEN
  SUBGOAL_THEN `DROP ((LENGTH (pre:A list) + LENGTH (l:A list)) - m) pre = []` SUBST1_TAC THENL
   [REWRITE_TAC[DROP_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[APPEND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let W2SP1AUX_abs_stack_LASTN_full = prove
 (`!(bs:(A word)list) (wstack:((B)stack_frame)list) sstack lens stack h.
     abs_stack bs wstack sstack lens = SOME stack /\ h = LENGTH wstack
     ==> abs_stack bs (LASTN h wstack) (LASTN (handler_val (LASTN h stack)) sstack)
           (LASTN h lens) = SOME (LASTN h stack)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP abs_stack_to_stack_LENGTH) THEN
  ASM_SIMP_TAC[LASTN_LENGTH_cond]);;

let W2SP1AUX_LASTN_CONS_DROP = prove
 (`!m (x:A) l j. m + j <= LENGTH l ==> LASTN m (CONS x l) = LASTN m (DROP j l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `[x:A]`; `l:A list`; `j:num`] W2SP1AUX_LASTN_APPEND_DROP) THEN
  ASM_REWRITE_TAC[APPEND]);;

let W2SP1AUX_LASTN_CONS_DROP2 = prove
 (`!m (x:A) l j. m <= LENGTH l - j /\ j <= LENGTH l
                 ==> LASTN m (CONS x l) = LASTN m (DROP j l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP1AUX_LASTN_CONS_DROP THEN ASM_ARITH_TAC);;

let W2SP1AUX_LASTN_CONS4_DROP2 = prove
 (`!m (a:A) b c d l j. m <= LENGTH l - j /\ j <= LENGTH l
     ==> LASTN m (CONS a (CONS b (CONS c (CONS d l)))) = LASTN m (DROP j l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `[a:A; b; c; d]`; `l:A list`; `j:num`] W2SP1AUX_LASTN_APPEND_DROP) THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let W2SP1AUX_handler_val_LASTN_LE = prove
 (`!(l:(A option#B#C list)list) h. handler_val (LASTN h l) <= handler_val l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LASTN_ALT; LE_REFL] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[LE_REFL] THEN
  TRANS_TAC LE_TRANS `handler_val (t:(A option#B#C list)list)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT W2SP1AUX_SPLIT_PAIR_VAR_TAC THEN
  W2SP1AUX_CASES_VARS_TAC `:A option` THEN REWRITE_TAC[handler_val_def] THEN ARITH_TAC);;

let W2SP1AUX_abs_stack_LASTN = prove
 (`!(bs:(A word)list) (wstack:((B)stack_frame)list) sstack lens stack.
     abs_stack bs wstack sstack lens = SOME stack
     ==> !h. h <= LENGTH wstack
             ==> abs_stack bs (LASTN h wstack) (LASTN (handler_val (LASTN h stack)) sstack)
                   (LASTN h lens) = SOME (LASTN h stack)`,
  (MATCH_MP_TAC abs_stack_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[abs_stack_def; LENGTH; LE; LASTN] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[GSYM NOT_SOME_NONE; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[LASTN; handler_val_def] THEN
    REWRITE_TAC[num_CONV `1`; abs_stack_def] THEN SIMP_TAC[LASTN_LENGTH_cond; LENGTH];
    ALL_TAC; ALL_TAC;
    REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE];
    REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE];
    REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE]]) THENL
  [(REPEAT GEN_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
   DISCH_TAC THEN X_GEN_TAC `h:num` THEN DISCH_TAC THEN
   ASM_CASES_TAC `h = LENGTH (CONS (StackFrame n l0 l NONE) (xs:((B)stack_frame)list))` THENL
    [MATCH_MP_TAC W2SP1AUX_abs_stack_LASTN_full THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `h <= LENGTH (xs:((B)stack_frame)list)` ASSUME_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
     ALL_TAC] THEN
   UNDISCH_TAC `abs_stack bitmaps (CONS (StackFrame n l0 l NONE) (xs:((B)stack_frame)list))
     (CONS (w:(A)word_loc) stack) (CONS len lens) = SOME stk` THEN
   REWRITE_TAC[abs_stack_def] THEN DISCH_TAC THEN GVS(all_case_eqs())) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP abs_stack_to_stack_LENGTH) THEN
   SUBGOAL_THEN `h <= LENGTH (lens:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[LASTN_CONS] THEN
   W(fun (asl,w) ->
     let hvt = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "handler_val"
                                   with Failure _ -> false) w in
     MP_TAC (ISPECL [rand(rand hvt); `h:num`] W2SP1AUX_handler_val_LASTN_LE)) THEN
   ASM_REWRITE_TAC[LENGTH_DROP] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
   FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP W2SP1AUX_LASTN_CONS_DROP2 (CONJ th1 th2)])) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
   DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_CASES_TAC `i = LENGTH (CONS (StackFrame n l0 l (SOME h)) (xs:((B)stack_frame)list))` THENL
    [MATCH_MP_TAC W2SP1AUX_abs_stack_LASTN_full THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `i <= LENGTH (xs:((B)stack_frame)list)` ASSUME_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
     ALL_TAC] THEN
   UNDISCH_TAC `abs_stack bitmaps (CONS (StackFrame n l0 l (SOME h)) (xs:((B)stack_frame)list))
     (CONS (w:(A)word_loc) stack) (CONS len lens) = SOME stk` THEN
   REWRITE_TAC[abs_stack_def] THEN DISCH_TAC THEN GVS(all_case_eqs()) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP abs_stack_to_stack_LENGTH) THEN
   SUBGOAL_THEN `i <= LENGTH (lens:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[LASTN_CONS] THEN
   W(fun (asl,w) ->
     let hvt = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "handler_val"
                                   with Failure _ -> false) w in
     MP_TAC (ISPECL [rand(rand hvt); `i:num`] W2SP1AUX_handler_val_LASTN_LE)) THEN
   ASM_REWRITE_TAC[LENGTH_DROP] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
   FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP W2SP1AUX_LASTN_CONS4_DROP2 (CONJ th1 th2)])) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[])]);;

(* HOL4 line 2488 *)
let abs_stack_prefix_drop = prove
 (`!(bs:(A word)list) wstack sstack lens stack h wrest k len.
     h <= LENGTH wstack /\
     LASTN h wstack = wrest /\
     abs_stack bs wstack sstack lens = SOME stack /\
     stack_rel_aux k len wstack stack
     ==> let rest = LASTN h stack in
         let lrest = LASTN h lens in
         let srest = LASTN (handler_val rest) sstack in
         abs_stack bs wrest srest lrest = SOME rest /\
         stack_rel_aux k len wrest rest`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) && is_var (rhs (concl th)))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] W2SP1AUX_abs_stack_LASTN) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC stack_rel_aux_LASTN THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2575 *)
let abs_stack_len = prove
 (`!(bs:(A word)list) (wstack:((B)stack_frame)list) sstack lens stack handler.
     abs_stack bs wstack sstack lens = SOME stack
     ==> handler_val (LASTN handler stack) <= LENGTH sstack`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP abs_stack_to_stack_LENGTH) THEN
  REWRITE_TAC[W2SP1AUX_handler_val_LASTN_LE]);;

(* HOL4 line 2601 *)
let EL_REVERSE_REWRITE = prove
 (`!(l:A list) n k.
     n < LENGTH l /\ k < n
     ==> EL ((LENGTH l - n) + k) l = EL ((n - k) - 1) (REVERSE l)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_REVERSE; ARITH_RULE `n < l /\ k < n ==> (n - k) - 1 < l`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 2608 *)
let LASTN_LESS = prove
 (`!(ls:A list) n x xs.
     n + 1 <= LENGTH ls /\ LASTN (n + 1) ls = CONS x xs ==> LASTN n ls = xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LASTN_DROP_UNCOND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (ls:A list) - n = 1 + (LENGTH ls - (n + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM DROP_DROP_T; num_CONV `1`; RICHAUX_DROP_CLAUSES]);;

(* HOL4 line 2628 *)
let ALOOKUP_IFF_MEM = prove
 (`!(l:(A#B)list) q r. ALL_DISTINCT (MAP FST l) ==> (ALOOKUP l q = SOME r <=> MEM (q,r) l)`,
  MESON_TAC[MEM_ALOOKUP]);;

(* HOL4 line 2635 *)
let SORTED_CONS_IMP = prove
 (`!(h:num#A) t.
     SORTED (\x y. FST x > FST y) (CONS h t)
     ==> ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
         !x. MEM x t ==> FST h > FST x`,
  MESON_TAC[SORTED_FST_LESS_IMP]);;

(* HOL4 line 2646 *)
let SORTED_IMP_ALL_DISTINCT_LEMMA = prove
 (`!(l:(num#A)list). SORTED (\x y. FST x > FST y) l ==> ALL_DISTINCT (MAP FST l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SORTED_CONS_IMP) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[ARITH_RULE `~(n > n:num)`]);;

(* HOL4 line 2653 *)
let MEM_toAList_fromAList = prove
 (`!(l:(num#A)list) a.
     SORTED (\x y. FST x > FST y) l ==> (MEM a (toAList (fromAList l)) <=> MEM a l)`,
  REPEAT STRIP_TAC THEN
  SPEC_TAC(`a:num#A`,`a:num#A`) THEN REWRITE_TAC[FORALL_PAIR_THM; MEM_toAList; lookup_fromAList] THEN
  ASM_MESON_TAC[ALOOKUP_IFF_MEM; SORTED_IMP_ALL_DISTINCT_LEMMA]);;

(* HOL4 line 2661 *)
let SORTED_FST_PERM_IMP_ALIST_EQ = prove
 (`!(l:(num#A)list) q.
     SORTED (\x y. FST x > FST y) l /\
     SORTED (\x y. FST x > FST y) q /\
     PERM (toAList (fromAList l)) q
     ==> q = l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SORTED_IMP_EQ_LISTS THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEM_PERM; MEM_toAList_fromAList]);;

(* HOL4 line 2678 *)
let inter_union_left = prove
 (`!(s:A spt) t. wf s ==> inter (union s t) s = s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`inter (union s t) (s:A spt)`; `s:A spt`] spt_eq_thm) THEN
  ASM_REWRITE_TAC[wf_inter] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_inter; lookup_union] THEN GEN_TAC THEN
  CASES_ON `lookup n (s:A spt)` THEN SIMP[] THEN
  CASES_ON `lookup n (t:A spt)` THEN SIMP[]);;

let W2SP1AUX_SPLIT_PAIR_VAR_ALL_TAC =
  W(fun (asl,w) ->
     match filter (fun t -> is_type (type_of t) &&
                            fst(dest_type(type_of t)) = "prod") (frees w) with
       [] -> NO_TAC
     | v::_ -> CASES_ON v);;

let W2SP1AUX_abs_stack_SOME_frame = prove
 (`!(bs:(A word)list) n l0 l h (xs:((B)stack_frame)list) ss lns res.
     abs_stack bs (CONS (StackFrame n l0 l (SOME h)) xs) ss lns = SOME res
     ==> ?loc hv w st len lr bits ys.
           ss = CONS (wl_Word (word 1)) (CONS loc (CONS hv (CONS w st))) /\
           lns = CONS len lr /\
           full_read_bitmap bs w = SOME bits /\ LENGTH bits = len /\ len <= LENGTH st /\
           abs_stack bs xs (DROP len st) lr = SOME ys /\
           res = CONS (SOME (loc,hv),bits,TAKE len st) ys`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `lns:num list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `ss:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; GSYM NOT_SOME_NONE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
  ASM_MESON_TAC[NOT_LT]);;

let W2SP1AUX_EL_CONS_123 = prove
 (`!(a:A) b c l. EL 1 (CONS a (CONS b l)) = b /\ EL 2 (CONS a (CONS b (CONS c l))) = c`,
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; EL; HD; TL]);;

let W2SP1AUX_DROP_3_CONS = prove
 (`!(a:A) b c l. DROP 3 (CONS a (CONS b (CONS c l))) = l`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; RICHAUX_DROP_CLAUSES]);;

(* HOL4 line 2687 *)
let stack_rel_raise = prove
 (`!n (sstack:((A)word_loc)list) handler (wstack:((A)stack_frame)list) l m l0 h1 l3 l4 rest
     (bs:(A word)list) lens stack k.
     n <= LENGTH sstack /\
     handler + 1 <= LENGTH wstack /\ SORTED (\x y. FST x > FST y) l /\
     LASTN (handler + 1) wstack = CONS (StackFrame m l0 l (SOME (h1,l3,l4))) rest /\
     abs_stack bs wstack (DROP n sstack) lens = SOME stack /\
     stack_rel_aux k (LENGTH sstack) wstack stack
     ==> ?ex payload.
           LASTN (handler + 1) stack = CONS (SOME ex,payload) (LASTN handler stack) /\
           3 <= LENGTH sstack /\ 3 <= handler_val (LASTN (handler + 1) stack) /\
           EL ((LENGTH sstack - handler_val (LASTN (handler + 1) stack)) + 1) sstack =
             wl_Loc l3 l4 /\
           (h1 < LENGTH rest /\ is_handler_frame (EL (LENGTH rest - (h1 + 1)) rest)
            ==> EL ((LENGTH sstack - handler_val (LASTN (handler + 1) stack)) + 2) sstack =
                wl_Word (word (LENGTH sstack -
                               handler_val (LASTN (h1 + 1) (LASTN (handler + 1) stack))))) /\
           stack_rel_aux k (LENGTH sstack)
             (CONS (StackFrame m l0 (FST (env_to_list (fromAList l) (K I))) NONE) rest)
             (CONS (NONE,payload) (LASTN handler stack)) /\
           abs_stack bs
             (CONS (StackFrame m l0 (FST (env_to_list (fromAList l) (K I))) NONE) rest)
             (DROP ((LENGTH sstack - handler_val (LASTN (handler + 1) stack)) + 3) sstack)
             (LASTN (handler + 1) lens) =
             SOME (CONS (NONE,payload) (LASTN handler stack))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `FST (env_to_list (fromAList (l:(num#(A)word_loc)list)) (K I)) = l` SUBST1_TAC THENL
    [MP_TAC(ISPECL [`fromAList (l:(num#(A)word_loc)list)`;
                    `FST (env_to_list (fromAList (l:(num#(A)word_loc)list)) (K I))`;
                    `SND (env_to_list (fromAList (l:(num#(A)word_loc)list)) (K I))`]
                   env_to_list_K_I_IMP) THEN
     REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC SORTED_FST_PERM_IMP_ALIST_EQ THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH o check (fun th ->
     can (find_term (fun t -> t = `DROP n (sstack:((A)word_loc)list)`)) (concl th))) THEN
   MP_TAC(ISPECL [`bs:(A word)list`; `wstack:((A)stack_frame)list`;
                  `DROP n (sstack:((A)word_loc)list)`; `lens:num list`;
                  `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                  `handler + 1`] abs_stack_len) THEN
   ASM_REWRITE_TAC[LENGTH_DROP] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`bs:(A word)list`; `wstack:((A)stack_frame)list`;
                  `DROP n (sstack:((A)word_loc)list)`; `lens:num list`;
                  `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                  `handler + 1`; `LASTN (handler + 1) (wstack:((A)stack_frame)list)`; `k:num`;
                  `LENGTH (sstack:((A)word_loc)list)`] abs_stack_prefix_drop) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
   SUBGOAL_THEN
    `LASTN (handler_val (LASTN (handler + 1)
       (stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)))
       (DROP n (sstack:((A)word_loc)list)) =
     DROP (LENGTH sstack - handler_val (LASTN (handler + 1) stack)) sstack`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [GEN_REWRITE_TAC LAND_CONV [LASTN_DROP_UNCOND] THEN
     REWRITE_TAC[LENGTH_DROP; DROP_DROP_T] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP1AUX_abs_stack_SOME_frame o check (fun th ->
     can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "abs_stack" with Failure _ -> false)) (concl th) &&
     can (find_term (fun t -> t = `rest:((A)stack_frame)list`)) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `loc:(A)word_loc` (X_CHOOSE_THEN `hvv:(A)word_loc`
     (X_CHOOSE_THEN `w:(A)word_loc` (X_CHOOSE_THEN `st:((A)word_loc)list`
     (X_CHOOSE_THEN `len0:num` (X_CHOOSE_THEN `lr:num list`
     (X_CHOOSE_THEN `bits:bool list`
     (X_CHOOSE_THEN `ys:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
       STRIP_ASSUME_TAC))))))))) THEN
  (UNDISCH_TAC `stack_rel_aux k (LENGTH (sstack:((A)word_loc)list))
      (CONS (StackFrame m l0 l (SOME (h1,l3,l4))) (rest:((A)stack_frame)list))
      (LASTN (handler + 1)
         (stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list))` THEN
   ASM_REWRITE_TAC[stack_rel_aux_def] THEN STRIP_TAC THEN
   SUBGOAL_THEN `LASTN handler (stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list) = ys`
     SUBST1_TAC THENL
    [MATCH_MP_TAC LASTN_LESS THEN
     EXISTS_TAC `(SOME (loc:(A)word_loc,hvv:(A)word_loc),bits:bool list,
                  TAKE len0 (st:((A)word_loc)list))` THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH o check (fun th ->
     can (find_term (fun t -> t = `DROP len0 (st:((A)word_loc)list)`)) (concl th))) THEN
   SUBGOAL_THEN `LENGTH (DROP (LENGTH sstack - handler_val (LASTN (handler + 1)
       (stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)))
       (sstack:((A)word_loc)list)) = handler_val (LASTN (handler + 1) stack)` ASSUME_TAC THENL
    [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`(loc:(A)word_loc,hvv:(A)word_loc)`;
                         `(bits:bool list,TAKE len0 (st:((A)word_loc)list))`] THEN
   ALL_TAC) THEN
  (FIRST_ASSUM(fun th ->
     if is_eq (concl th) && lhs (concl th) =
        `LASTN (handler + 1) (stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)`
     then RULE_ASSUM_TAC(fun th' -> if th' == th then th' else REWRITE_RULE[th] th')
     else NO_TAC) THEN
   ABBREV_TAC `hv = handler_val (CONS (SOME (loc:(A)word_loc,hvv:(A)word_loc),bits:bool list,
                       TAKE len0 (st:((A)word_loc)list)) ys)` THEN
   SUBGOAL_THEN `4 <= hv /\ hv <= LENGTH (sstack:((A)word_loc)list)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `LENGTH (DROP (LENGTH sstack - hv) (sstack:((A)word_loc)list)) = hv` THEN
     FIRST_ASSUM(fun th -> if is_eq (concl th) && can (find_term (fun t -> t = `wl_Word (word 1:A word)`)) (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
     REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `!j. j < 4 ==> EL ((LENGTH sstack - hv) + j) (sstack:((A)word_loc)list) =
                   EL j (DROP (LENGTH sstack - hv) sstack)` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC EL_DROP THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[ARITH_RULE `1 < 4 /\ 2 < 4`] THEN
   FIRST_ASSUM(fun th -> if is_eq (concl th) && can (find_term (fun t -> t = `wl_Word (word 1:A word)`)) (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
   REWRITE_TAC[W2SP1AUX_EL_CONS_123] THEN
   REPEAT CONJ_TAC THENL
    [ASM_ARITH_TAC;
     ASM_ARITH_TAC;
     STRIP_TAC THEN
     SUBGOAL_THEN `h1 + 1 <= LENGTH (ys:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)`
       (fun th -> REWRITE_TAC[MATCH_MP LASTN_CONS th]) THEN ASM_ARITH_TAC;
     REWRITE_TAC[stack_rel_aux_def] THEN ASM_REWRITE_TAC[];
     ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM DROP_DROP_T] THEN
     FIRST_ASSUM(fun th -> if is_eq (concl th) && can (find_term (fun t -> t = `wl_Word (word 1:A word)`)) (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
     REWRITE_TAC[W2SP1AUX_DROP_3_CONS; abs_stack_def] THEN ASM_REWRITE_TAC[NOT_LT] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_ARITH_TAC]));;

(* HOL4 line 2797 *)
let insert_bitmap_isPREFIX = prove
 (`!(bs:(A)app_list#num) bs' i (bm:A list).
     insert_bitmap bm bs = (bs',i) ==> isPREFIX (append (FST bs)) (append (FST bs'))`,
  REWRITE_TAC[FORALL_PAIR_THM; insert_bitmap_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN GVS[] THEN REWRITE_TAC[FST; append_thm; IS_PREFIX_APPEND3]);;

(* HOL4 line 2805 *)
let wLive_isPREFIX = prove
 (`!a (bs:(A word)app_list#num) c q bs'.
     wLive a bs c = (q:(A)stack_prog,bs')
     ==> isPREFIX (append (FST bs)) (append (FST bs'))`,
  REWRITE_TAC[FORALL_PAIR_THM; wLive_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN GVS[] THEN REWRITE_TAC[IS_PREFIX_REFL]; ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP insert_bitmap_isPREFIX) THEN REWRITE_TAC[FST]);;

(* HOL4 line 2818 *)
let comp_IMP_isPREFIX = prove
 (`!(ac:(A)asm_config) perf c1 bs r q1 bs'.
     word_to_stack_comp ac perf c1 bs r = (q1,bs')
     ==> isPREFIX (append (FST bs)) (append (FST bs'))`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `perf:bool` BOOL_CASES_AX) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  TRY(STRIP_TAC THEN GVS[] THEN REWRITE_TAC[IS_PREFIX_REFL] THEN NO_TAC) THEN
  EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN GVS[] THEN
  TRY(ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL; wLive_isPREFIX; insert_bitmap_isPREFIX]));;

(* HOL4 line 2830 *)
let compile_prog_isPREFIX = prove
 (`!(ac:(A)asm_config) perf x y k bs prog fs bs1.
     word_to_stack_compile_prog ac perf x y k bs = (prog,fs,bs1)
     ==> isPREFIX (append (FST bs)) (append (FST bs1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN GVS[] THEN ASM_MESON_TAC[comp_IMP_isPREFIX]);;

(* HOL4 line 2840 *)
let compile_word_to_stack_isPREFIX = prove
 (`!code k bs progs1 fs1 bs1 (ac:(A)asm_config) perf.
     compile_word_to_stack ac perf k code bs = (progs1,fs1,bs1)
     ==> isPREFIX (append (FST bs)) (append (FST bs1))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN GVS[] THEN
    REWRITE_TAC[IS_PREFIX_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT W2SP1AUX_SPLIT_PAIR_VAR_TAC THEN
  REWRITE_TAC[compile_word_to_stack_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN GVS[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP compile_prog_isPREFIX) THEN
  FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[FST] THEN MESON_TAC[isPREFIX_TRANS]);;

(* HOL4 line 2856 *)
let wMoveAux_thm = prove
 (`!kf (s:(A,C,FFI)stack_state) x xs.
     stack_evaluate (wMoveAux [] kf,s) = (NONE,s) /\
     stack_evaluate (wMoveAux (CONS x xs) kf,s) =
     stack_evaluate (stack_Seq (wMoveSingle x kf) (wMoveAux xs kf),s)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[wMoveAux_def; W2SP1AUX_stack_evaluate_clause "stack_Skip"];
    STRUCT_CASES_TAC(ISPEC `xs:((num+num)#(num+num))list` list_CASES) THEN
    REWRITE_TAC[wMoveAux_def] THEN
    REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "stack_Seq";
                W2SP1AUX_stack_evaluate_clause "stack_Skip"] THEN
    CASES_ON `stack_evaluate (wMoveSingle x kf:(A)stack_prog,s:(A,C,FFI)stack_state)` THEN
    SIMP[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2868 *)
let state_rel_get_var_imp = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra x v.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     wl_get_var (2 * x) s = SOME v /\
     x < k
     ==> FLOOKUP (stack_state_regs t) x = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def; wl_get_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`2 * x`; `v:(A)word_loc`]) THEN
  ASM_SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* HOL4 line 2884 *)
let state_rel_get_var_imp' = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra n v.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     wl_get_var n s = SOME v /\
     EVEN n /\
     n DIV 2 < k
     ==> stack_get_var (n DIV 2) t = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(SIMP_RULE[DIV_MULT; ARITH_EQ]) THEN
  ASM_SIMP_TAC[stack_get_var_def; DIV_MULT; ARITH_EQ] THEN
  ASM_MESON_TAC[state_rel_get_var_imp]);;

let W2SP1AUX_EL_TAKE_DROP = prove
 (`!i f sp (l:A list).
     i < LENGTH (TAKE f (DROP sp l)) ==> EL i (TAKE f (DROP sp l)) = EL (sp + i) l`,
  REWRITE_TAC[LENGTH_TAKE_EQ_MIN; LENGTH_DROP] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < f /\ i + sp < LENGTH (l:A list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_TAKE; EL_DROP]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* HOL4 line 2895 *)
let state_rel_get_var_imp2 = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens x v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_get_var (2 * x) s = SOME v /\
     ~(x < k)
     ==> EL (stack_state_stack_space t + ((f + k) - (x + 1))) (stack_state_stack t) = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def; wl_get_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`2 * x`; `v:(A)word_loc`]) THEN
  ASM_SIMP_TAC[DIV_MULT; ARITH_EQ; ADD_CLAUSES; oEL_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[GSYM NOT_SOME_NONE; option_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[W2SP1AUX_EL_TAKE_DROP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(f' = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `if f' = 0 then f = 0 else f = f' + 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 2917 *)
let state_rel_set_var_k = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra v.
     (word_to_stackProof_state_rel ac k f f' s (stack_set_var (k + 1) v t) lens extra <=>
      word_to_stackProof_state_rel ac k f f' s t lens extra) /\
     (word_to_stackProof_state_rel ac k f f' s (stack_set_var k v t) lens extra <=>
      word_to_stackProof_state_rel ac k f f' s t lens extra)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_set_var_def] THEN CONJ_TAC THEN
  MATCH_MP_TAC W2SP1AUX_state_rel_regs THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let _ = cake_add_simps [state_rel_set_var_k];;

let W2SP1AUX_EVEN_DIV2_NEQ = prove
 (`!n x. EVEN n /\ ~(n = 2 * x) ==> ~(x = n DIV 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* HOL4 line 2930 *)
let word_to_stackProof_state_rel_set_var = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra x v.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     x < k
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_var (2 * x) v s)
           (stack_set_var x v t) lens extra`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_set_var_def; stack_set_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_SIMP_TAC[wf_insert];
    REWRITE_TAC[lookup_insert] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_INJ] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[DIV_MULT; ARITH_EQ; EVEN_DOUBLE; FLOOKUP_UPDATE];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v':(A)word_loc`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
      SUBGOAL_THEN `~(x = n DIV 2)` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC W2SP1AUX_EVEN_DIV2_NEQ THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 2953 *)
let state_rel_set_var' = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra x y v.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     x < k /\ y = x * 2
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_var y v s)
           (stack_set_var x v t) lens extra`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC word_to_stackProof_state_rel_set_var THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2962 *)
let state_rel_set_var2 = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens x st sp v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     ~(x < k) /\ x < f' + k /\ st = stack_state_stack t /\ sp = stack_state_stack_space t
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_var (2 * x) v s)
           (stack_state_stack_fupd (K (LUPDATE v (sp + ((f + k) - (x + 1))) st)) t)
           lens 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_set_var_def; ADD_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[LENGTH_LUPDATE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(f' = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `f = f' + 1` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `if f' = 0 then f = 0 else f = f' + 1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `i = ((f' + 1) + k) - (x + 1)` THEN
  SUBGOAL_THEN `i < f' + 1 /\ ((f' + 1) - 1) - (x - k) = i` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `DROP (stack_state_stack_space t) (LUPDATE v (stack_state_stack_space t + i)
      (stack_state_stack t)) =
    LUPDATE v i (DROP (stack_state_stack_space t) (stack_state_stack (t:(A,C,FFI)stack_state)))`
    SUBST1_TAC THENL [SIMP_TAC[DROP_LUPDATE_lemma1; LE_ADD; ADD_SUB2]; ALL_TAC] THEN
  ASM_SIMP_TAC[DROP_LUPDATE_lemma2; TAKE_LUPDATE] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_SIMP_TAC[wf_insert];
    UNDISCH_TAC
     `stack_size_rel (f' + 1) (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
        (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
        (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
    REWRITE_TAC[stack_size_rel_def; LENGTH_LUPDATE];
    REWRITE_TAC[lookup_insert] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_INJ] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[DIV_MULT; ARITH_EQ; EVEN_DOUBLE; oEL_LUPDATE; LENGTH_TAKE_EQ_MIN;
                   LENGTH_DROP] THEN
      SUBGOAL_THEN
       `i < MIN (f' + 1) (LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                          stack_state_stack_space t)`
       (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v':(A)word_loc`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      (SUBGOAL_THEN `~(x = n DIV 2)` ASSUME_TAC THENL
        [MATCH_MP_TAC W2SP1AUX_EVEN_DIV2_NEQ THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      (SUBGOAL_THEN `~(i = ((f' + 1) - 1) - (n DIV 2 - k))` ASSUME_TAC THENL
        [ASM_ARITH_TAC; ASM_REWRITE_TAC[oEL_LUPDATE]])]]);;

let W2SP1AUX_state_rel_stack_var = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens x v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_get_var (2 * x) s = SOME v /\ ~(x < k)
     ==> f = f' + 1 /\ x < k + f' /\
         EL (stack_state_stack_space t + ((f - 1) - (x - k))) (stack_state_stack t) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                `t:(A,C,FFI)stack_state`; `lens:num list`; `x:num`; `v:(A)word_loc`]
         state_rel_get_var_imp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x < k + f'` ASSUME_TAC THENL
   [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                   (t:(A,C,FFI)stack_state) lens 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2 * x`; `v:(A)word_loc`]) THEN
    UNDISCH_TAC `wl_get_var (2 * x) (s:(A,num#C,FFI)wl_state) = SOME v` THEN
    REWRITE_TAC[wl_get_var_def] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[DIV_MULT; ARITH_EQ];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP W2SP1AUX_state_rel_basic) THEN
  SUBGOAL_THEN `~(f' = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let W2SP1AUX_eval_or_move = prove
 (`!r1 r2 w (t:(A,C,FFI)stack_state).
     FLOOKUP (stack_state_regs t) r2 = SOME w
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop asm_Or r1 r2 (Reg r2))),t) =
         (NONE,stack_set_var r1 w t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "stack_Inst"] THEN
  REWRITE_TAC[stack_inst_def] THEN SIMP[]);;

let W2SP1AUX_eval_load = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens x v r.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_get_var (2 * x) s = SOME v /\ ~(x < k)
     ==> stack_evaluate (StackLoad r ((f - 1) - (x - k)),t) = (NONE,stack_set_var r v t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                `t:(A,C,FFI)stack_state`; `lens:num list`; `x:num`; `v:(A)word_loc`]
         W2SP1AUX_state_rel_stack_var) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP W2SP1AUX_state_rel_basic) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "StackLoad"] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let W2SP1AUX_eval_store = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens y r v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     ~(y < k) /\ y < f' + k /\ stack_get_var r t = SOME v
     ==> stack_evaluate (StackStore r ((f - 1) - (y - k)),t) =
         (NONE,stack_state_stack_fupd
                 (K (LUPDATE v (stack_state_stack_space t + ((f + k) - (y + 1)))
                       (stack_state_stack t))) t)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP W2SP1AUX_state_rel_basic) THEN
  SUBGOAL_THEN `~(f' = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "StackStore"] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
      stack_state_stack_space t + (f' + 1) - 1 - (y - k))`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN SIMP[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let W2SP1AUX_GETVAR_FLOOKUP_TAC =
  FIRST_ASSUM(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "stack_get_var")) (concl th)
    then ASSUME_TAC (REWRITE_RULE[stack_get_var_def] th) else NO_TAC);;

let W2SP1AUX_FIN_SETVAR_TAC =
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_set_var' THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[stack_set_var_def] THEN SIMP[];
    REWRITE_TAC[stack_set_var_def] THEN SIMP[]];;

let W2SP1AUX_FIN_STORE_TAC =
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC state_rel_set_var2 THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    ASM_REWRITE_TAC[stack_get_var_def] THEN SIMP[LENGTH_LUPDATE]];;

(* HOL4 line 2995 *)
let wMoveSingle_thm = prove
 (CASE_TERM `!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens x v y.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     (match x with
        NONE -> stack_get_var (k + 1) t = SOME v
      | SOME x -> wl_get_var (x * 2) s = SOME v) /\
     (match y with SOME x -> x < f' + k | _ -> T)
     ==> ?t'.
           stack_evaluate (wMoveSingle (format_var k y,format_var k x) (k,f,f'),t) =
             (NONE,t') /\
           word_to_stackProof_state_rel ac k f f'
             (match y with NONE -> s | SOME y -> wl_set_var (y * 2) v s) t' lens 0 /\
           (y = NONE ==> stack_get_var (k + 1) t' = SOME v) /\
           (~(y = NONE) ==> stack_get_var (k + 1) t' = stack_get_var (k + 1) t) /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `y0:num` SUBST_ALL_TAC)
    (ISPEC `y:num option` (cases "option")) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x0:num` SUBST_ALL_TAC)
    (ISPEC `x:num option` (cases "option")) THEN
  REWRITE_TAC[format_var_def; option_CASE; NOT_SOME_NONE] THEN STRIP_TAC THENL
   [(* NONE NONE *)
    REWRITE_TAC[wMoveSingle_def] THEN SIMP[] THEN
    EXISTS_TAC `stack_set_var (k + 1) v (t:(A,C,FFI)stack_state)` THEN
    W2SP1AUX_GETVAR_FLOOKUP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP W2SP1AUX_eval_or_move th]) THEN
    ASM_SIMP_TAC[state_rel_set_var_k; word_to_stackProof_get_var_set_var] THEN
    REWRITE_TAC[stack_set_var_def] THEN SIMP[];
    (* NONE SOME *)
    ASM_CASES_TAC `x0 < k` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wMoveSingle_def] THEN SIMP[] THEN
    EXISTS_TAC `stack_set_var (k + 1) v (t:(A,C,FFI)stack_state)` THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THENL
     [FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_get_var_imp o
                  CONJ (ASSUME `word_to_stackProof_state_rel ac k f f'
                     (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens 0`) o
                  CONJ (ASSUME `wl_get_var (2 * x0) (s:(A,num#C,FFI)wl_state) = SOME v`) o
                  ASSUME o concl) THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP W2SP1AUX_eval_or_move th]);
      MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                    `t:(A,C,FFI)stack_state`; `lens:num list`; `x0:num`; `v:(A)word_loc`;
                    `k + 1`] W2SP1AUX_eval_load) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[state_rel_set_var_k; word_to_stackProof_get_var_set_var] THEN
    REWRITE_TAC[stack_set_var_def] THEN SIMP[];
    (* SOME NONE *)
    ASM_CASES_TAC `y0 < k` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[wMoveSingle_def] THEN
    SIMP[] THENL
     [EXISTS_TAC `stack_set_var y0 v (t:(A,C,FFI)stack_state)` THEN
      W2SP1AUX_GETVAR_FLOOKUP_TAC THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP W2SP1AUX_eval_or_move th]) THEN
      W2SP1AUX_FIN_SETVAR_TAC;
      EXISTS_TAC `stack_state_stack_fupd (K (LUPDATE v (stack_state_stack_space t +
                    ((f + k) - (y0 + 1))) (stack_state_stack t))) (t:(A,C,FFI)stack_state)` THEN
      MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                    `t:(A,C,FFI)stack_state`; `lens:num list`; `y0:num`; `k + 1`;
                    `v:(A)word_loc`] W2SP1AUX_eval_store) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN W2SP1AUX_FIN_STORE_TAC];
    (* SOME SOME *)
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_CASES_TAC `y0 < k` THEN ASM_CASES_TAC `x0 < k` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wMoveSingle_def] THEN SIMP[] THENL
     [EXISTS_TAC `stack_set_var y0 v (t:(A,C,FFI)stack_state)` THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_get_var_imp o
                  CONJ (ASSUME `word_to_stackProof_state_rel ac k f f'
                     (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens 0`) o
                  CONJ (ASSUME `wl_get_var (2 * x0) (s:(A,num#C,FFI)wl_state) = SOME v`) o
                  ASSUME o concl) THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP W2SP1AUX_eval_or_move th]) THEN
      W2SP1AUX_FIN_SETVAR_TAC;
      EXISTS_TAC `stack_set_var y0 v (t:(A,C,FFI)stack_state)` THEN
      MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                    `t:(A,C,FFI)stack_state`; `lens:num list`; `x0:num`; `v:(A)word_loc`;
                    `y0:num`] W2SP1AUX_eval_load) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN W2SP1AUX_FIN_SETVAR_TAC;
      EXISTS_TAC `stack_state_stack_fupd (K (LUPDATE v (stack_state_stack_space t +
                    ((f + k) - (y0 + 1))) (stack_state_stack t))) (t:(A,C,FFI)stack_state)` THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_get_var_imp o
                  CONJ (ASSUME `word_to_stackProof_state_rel ac k f f'
                     (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens 0`) o
                  CONJ (ASSUME `wl_get_var (2 * x0) (s:(A,num#C,FFI)wl_state) = SOME v`) o
                  ASSUME o concl) THEN
      MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                    `t:(A,C,FFI)stack_state`; `lens:num list`; `y0:num`; `x0:num`;
                    `v:(A)word_loc`] W2SP1AUX_eval_store) THEN
      ASM_REWRITE_TAC[stack_get_var_def] THEN DISCH_THEN SUBST1_TAC THEN
      W2SP1AUX_FIN_STORE_TAC;
      EXISTS_TAC
       `stack_state_stack_fupd
          (K (LUPDATE v (stack_state_stack_space (stack_set_var k v t) +
                          ((f + k) - (y0 + 1)))
                (stack_state_stack (stack_set_var k v t))))
          (stack_set_var k v (t:(A,C,FFI)stack_state))` THEN
      REWRITE_TAC[W2SP1AUX_stack_evaluate_clause "stack_Seq"] THEN
      MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                    `t:(A,C,FFI)stack_state`; `lens:num list`; `x0:num`; `v:(A)word_loc`;
                    `k:num`] W2SP1AUX_eval_load) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `word_to_stackProof_state_rel ac k f f' s
                      (stack_set_var k v (t:(A,C,FFI)stack_state)) lens 0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[state_rel_set_var_k]; ALL_TAC] THEN
      MP_TAC(SPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                    `stack_set_var k v (t:(A,C,FFI)stack_state)`; `lens:num list`; `y0:num`;
                    `k:num`; `v:(A)word_loc`] W2SP1AUX_eval_store) THEN
      ASM_REWRITE_TAC[word_to_stackProof_get_var_set_var] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC state_rel_set_var2 THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN
        SIMP[LENGTH_LUPDATE; FLOOKUP_UPDATE; ARITH_RULE `~(k = k + 1)`]]]]);;

