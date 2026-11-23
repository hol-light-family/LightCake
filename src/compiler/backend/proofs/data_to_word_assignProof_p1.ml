(* ========================================================================= *)
(* data_to_word_assignProof_p1: part 1 of 6 (HOL4 lines 1-2889) of the port  *)
(* of HOL4 compiler/backend/proofs/data_to_word_assignProofScript.sml        *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p6 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_assignProof.ml needs the last.                *)
(* ASP1AUX_ names are local helpers of this part.                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/sptree.ml";;
needs "hol4/int_bitwise.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/multiword.ml";;
needs "hol4/mc_multiword.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
(* HOL4 ancestors not needed by part 1: semanticsProps, While, alignment    *)
(* (in hol4/words4.ml)                                                      *)

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2889 ===== *)

(* HOL4 lines 40-55: ML values (assign_def, clean_tac, state_rel_def,      *)
(* code_rel_def, do_app, eval_tac): proof tools, not stated                *)

(* HOL4 line 63 (HOL4: LIST_CONJ of definitions) *)
let assign_def_extras = end_itlist CONJ
  [LoadWord64_def; WriteWord64_def; BignumHalt_def; LoadBignum_def;
   AnyArith_code_def; data_to_word_Add_code_def; data_to_word_Sub_code_def;
   data_to_word_Mul_code_def; data_to_word_Div_code_def; data_to_word_Mod_code_def;
   data_to_word_Compare1_code_def; data_to_word_Compare_code_def;
   data_to_word_Equal1_code_def; data_to_word_Equal_code_def; LongDiv1_code_def;
   LongDiv_code_def; ShiftVar_def; generated_bignum_stubs_eq; DivCode_def;
   AddNumSize_def; AnyHeader_def; WriteWord64_on_32_def; WriteWord32_on_32_def;
   AllocVar_def; SilentFFI_def; WordOp64_on_32_def; WordShift64_on_32_def;
   data_to_word_Make_ptr_bits_code_def];;

(* HOL4 line 74 *)
let get_vars_SING = prove
 (`!args (s:A spt) w. data_get_vars args s = SOME [w] ==> ?y. args = [y]`,
  GEN_TAC THEN CASES_ON `args:num list` THEN FS[data_get_vars_def] THEN
  CASES_ON `a1:num list` THEN FS[data_get_vars_def] THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN FS[]);;

(* HOL4 line 83 *)
let state_rel_IMP_tstamps = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) p locs.
     data_to_word_gcProof_state_rel c l1 l2 x t p locs ==>
     ?next_stamp. data_state_tstamps x = SOME next_stamp`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  MESON_TAC[IS_SOME_EXISTS]);;

(* HOL4 line 90 *)
let INT_EQ_NUM_LEMMA = prove
 (`!i:int. &0 <= i <=> ?index. i = &index`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `num_of_int i` THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POS]]);;

(* HOL4 line 96 (local) *)
let data_to_word_assignProof_push_if = prove
 (`(!(f:A->B) x y b. (if b then f x else f y) = f (if b then x else y)) /\
   (!(f:A->B) h x b. (if b then f x else h x) = (if b then f else h) x)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 103 (local) *)
let split_if = prove
 (`!b (f:A->B) h x y. (if b then f x else h y) = (if b then f else h) (if b then x else y)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 109 *)
let cut_env_IMP_domain = prove
 (`!(x:B spt) (y:A spt) t. cut_names x y = SOME t ==> domain t = domain x`,
  REWRITE_TAC[cut_names_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[domain_inter] THEN ASM SET_TAC[]);;

(* HOL4 line 116 *)
let cut_envs_wf = prove
 (`!kept_names (t:A spt) y1 y2.
     cut_envs kept_names t = SOME (y1,y2) ==> sptree_wf y1 /\ sptree_wf y2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[wf_inter]);;

(* HOL4 line 123 *)
let domain_list_insert_thm = prove
 (`!l names:num_set. domain (list_insert l names) = set_of_list l UNION domain names`,
  REWRITE_TAC[EXTENSION; domain_list_insert; IN_UNION; IN_SET_OF_LIST]);;

(* HOL4 line 130 *)
let cut_env_lookup = prove
 (`!names (t:A spt) y n a.
     wl_cut_env names t = SOME y /\ lookup n y = SOME a ==> lookup n t = SOME a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN VAR_EQ_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[lookup_union; lookup_inter_alt] THEN
  REPEAT COND_CASES_TAC THEN CASES_ON `lookup n (t:A spt)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 141 *)
let cut_env_get_vars_get_vars = prove
 (`!vs ws ws' kept_names (t:(A,C,FFI)wl_state) y.
     wl_cut_env kept_names (wl_state_locals t) = SOME y /\
     wl_get_vars vs (wl_state_locals_fupd (K y) t) = SOME ws /\
     wl_get_vars vs t = SOME ws' ==>
     ws = ws'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_var_def] THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
  REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[cut_env_lookup; option_INJ];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 153 *)
let memory_rel_lookup_var_IMP = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm ll (t:(A,C,FFI)wl_state) envs n x w.
     memory_rel c be ts refs sp st m dm
       (APPEND (join_env ll (toAList (sptree_inter (wl_state_locals t) (adjust_set ll)))) envs) /\
     data_get_vars n ll = SOME x /\
     wl_get_vars (MAP adjust_var n) t = SOME w ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (APPEND (ZIP x w)
          (join_env ll (toAList (sptree_inter (wl_state_locals t) (adjust_set ll))))) envs)`,
  REWRITE_TAC[memory_rel_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC word_ml_inv_get_vars_IMP_lemma THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 168 *)
let get_real_offset_lemma = prove
 (`!v (t:(A,C,FFI)wl_state) i_w y c.
     wl_get_var v t = SOME (wl_Word i_w) /\
     good_dimindex (:A) /\
     get_real_offset i_w = SOME y ==>
     wl_word_exp t (real_offset c v) = SOME (wl_Word (y:A word))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_real_offset_def; real_offset_def; good_dimindex_def] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[word_exp_rw; MAP; the_words_def; VAL_WORD_1] THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ITLIST; OPTION_MAP_DEF; WORD_ADD_0; VAL_WORD_1] THEN
    CONV_TAC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN REWRITE_TAC[WORD_ADD_SYM]);;

(* HOL4 line 180 *)
let state_rel_push_env_loc = prove
 (`!c n l (s:(C,FFI)data_state) args b y1 y2 (t:(A,C,FFI)wl_state) ys l1 l2 locs.
     data_to_word_gcProof_state_rel c n l s
       (wl_call_env args b (wl_push_env (y1,y2) NONE t)) ys (CONS (l1,l2) locs) ==>
     lookup 0 y1 = SOME (wl_Loc l1 l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[wl_push_env_def; wl_call_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  SIMP[ALL2; contains_loc_def; ALOOKUP_toAList]);;

(* HOL4 line 190 *)
let evaluate_IMP_domain_union = prove
 (`!p args b y1 y2 (t:(A,C,FFI)wl_state) ck tp ret1 ret2 t1 t2 l1 l2 (kept_names:B spt).
     wl_evaluate (p,wl_state_clock_fupd (K ck) (wl_state_termdep_fupd (K tp)
                    (wl_call_env args b (wl_push_env (y1,y2) NONE t)))) =
       (SOME (wl_Result ret1 ret2),t1) /\
     wl_pop_env t1 = SOME t2 /\
     lookup 0 y1 = SOME (wl_Loc l1 l2) /\
     cut_envs (adjust_sets kept_names) (wl_state_locals t) = SOME (y1,y2) ==>
     domain (wl_state_locals t2) = domain y1 UNION domain y2 /\
     lookup 0 (wl_state_locals t2) = SOME (wl_Loc l1 l2)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`p:(A)wl_prog`; `wl_state_clock_fupd (K ck) (wl_state_termdep_fupd (K tp)
                    (wl_call_env args b (wl_push_env (y1,y2) NONE (t:(A,C,FFI)wl_state))))`]
     wl_evaluate_stack_swap) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[wl_call_env_def; wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   PAIRARG_TAC THEN SIMP[] THEN
   UNDISCH_TAC `wl_pop_env t1 = SOME (t2:(A,C,FFI)wl_state)` THEN
   REWRITE_TAC[wl_pop_env_def] THEN
   CASES_ON `wl_state_stack (t1:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[s_key_eq_def] THEN
   CASE_REWRITE_TAC[]) THEN
  (CASES_ON `a0:(A)stack_frame` THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `a3:(num#num#num)option` THEN
   REWRITE_TAC[s_frame_key_eq_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_INJ] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[s_frame_key_eq_def] THEN SIMP[] THEN STRIP_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv) THEN STRIP_TAC THEN
   SUBGOAL_THEN `lookup 0 (y2:(A word_loc)spt) = NONE` ASSUME_TAC THENL
    [UNDISCH_TAC `cut_envs (adjust_sets (kept_names:B spt)) (wl_state_locals (t:(A,C,FFI)wl_state)) =
                  SOME (y1,y2)` THEN
     REWRITE_TAC[cut_envs_def; cut_names_def; adjust_sets_def] THEN
     REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[lookup_inter_alt; NOT_0_domain];
     ALL_TAC] THEN
   SUBGOAL_THEN `!n. MEM n (MAP FST (a2:(num#(A)word_loc)list)) <=>
                     n IN domain (y2:(A word_loc)spt)` ASSUME_TAC THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `MAP FST (a2:(num#(A)word_loc)list) = MAP FST (l:(num#(A)word_loc)list)`
       SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
     REWRITE_TAC[GSYM ALOOKUP_NONE; GSYM lookup_NONE_domain] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALOOKUP (a2:(num#(A)word_loc)list) 0 = NONE` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[ALOOKUP_NONE; GSYM lookup_NONE_domain]; ALL_TAC] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
     is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "a1'")) THEN
   ASM_REWRITE_TAC[domain_fromAList_toAList; domain_fromAList; lookup_union;
               lookup_fromAList; lookup_fromAList_toAList] THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[EXTENSION; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[]));;

(* HOL4 line 241 *)
let get_real_byte_offset_lemma = prove
 (`!v (t:(A,C,FFI)wl_state) (w:A word).
     wl_get_var v t = SOME (wl_Word w) /\ good_dimindex (:A) ==>
     wl_word_exp t (real_byte_offset v) =
       SOME (wl_Word (word_add bytes_in_word (word_ushr w 2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_byte_offset_def; good_dimindex_def] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[word_exp_rw; MAP; the_words_def; VAL_WORD] THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ITLIST; OPTION_MAP_DEF; WORD_ADD_0; VAL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV)));;

(* HOL4 line 249 *)
let reorder_lemma = prove
 (`!c be ts (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) x1 x2 x3 xs.
     memory_rel c be ts (data_state_refs x) (data_state_space x) (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS x1 (CONS x2 (CONS x3 xs))) ==>
     memory_rel c be ts (data_state_refs x) (data_state_space x) (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS x3 (CONS x1 (CONS x2 xs)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 256 *)
let reorder_2_lemma = prove
 (`!c be ts (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) x1 x2 xs.
     memory_rel c be ts (data_state_refs x) (data_state_space x) (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS x1 (CONS x2 xs)) ==>
     memory_rel c be ts (data_state_refs x) (data_state_space x) (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS x2 (CONS x1 xs))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 263 (HOL4: Q.prove ... |> Q.SPECL [xs,ys,t,0w] |>             *)
(* SIMP_RULE (srw_ss()) [] |> GEN_ALL: the offset is 0w)                     *)
let evaluate_StoreEach = prove
 (`!xs ys (t:(A,C,FFI)wl_state) m1 a i.
     data_to_word_memoryProof_store_list a ys (wl_state_memory t) (wl_state_mdomain t) =
       SOME m1 /\
     wl_get_vars xs t = SOME ys /\
     wl_get_var i t = SOME (wl_Word a) ==>
     wl_evaluate (StoreEach i xs (word 0),t) = (NONE,wl_state_memory_fupd (K m1) t)`,
  SUBGOAL_THEN
   `!xs ys (s:(A,C,FFI)wl_state) offset m1 a i.
     data_to_word_memoryProof_store_list (word_add a offset) ys (wl_state_memory s)
       (wl_state_mdomain s) = SOME m1 /\
     wl_get_vars xs s = SOME ys /\
     wl_get_var i s = SOME (wl_Word a) ==>
     wl_evaluate (StoreEach i xs offset,s) = (NONE,wl_state_memory_fupd (K m1) s)`
   (fun th -> MESON_TAC[th; WORD_ADD_0]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[wl_get_vars_def; option_INJ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    VAR_EQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_store_list_def; option_INJ]) THEN
    VAR_EQ_TAC THEN
    REWRITE_TAC[StoreEach_def; wl_evaluate_def; PAIR_EQ; wl_state_component_equality] THEN
    SIMP[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASES_ON `wl_get_var h (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_get_vars t (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN VAR_EQ_TAC THEN
  UNDISCH_TAC `data_to_word_memoryProof_store_list (word_add a offset) (CONS a' a'')
      (wl_state_memory (s:(A,C,FFI)wl_state)) (wl_state_mdomain s) = SOME m1` THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  REWRITE_TAC[StoreEach_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[wl_evaluate_def; word_exp_rw; wl_mem_store_def; MAP; the_words_def; ITLIST;
       WORD_ADD_0] THEN
  SUBGOAL_THEN `!qs f. wl_get_vars qs (wl_state_memory_fupd f (s:(A,C,FFI)wl_state)) =
                       wl_get_vars qs s` ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN SIMP[wl_get_vars_def; wl_get_var_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`a'':(A word_loc)list`;
     `wl_state_memory_fupd (K ((word_add a offset =+ a') (wl_state_memory s)))
        (s:(A,C,FFI)wl_state)`;
     `word_add offset bytes_in_word:A word`; `m1:A word->A word_loc`; `a:A word`;
     `i:num`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[wl_get_var_def] THEN ANTS_TAC THENL
   [UNDISCH_TAC `data_to_word_memoryProof_store_list
                   (word_add (word_add a offset) bytes_in_word) a''
                   ((word_add a offset =+ a') (wl_state_memory (s:(A,C,FFI)wl_state)))
                   (wl_state_mdomain s) = SOME m1` THEN
    REWRITE_TAC[WORD_ADD_ASSOC];
    SIMP[]]);;

(* HOL4 line 291 *)
let get_vars_adjust_var = prove
 (`!k args (t:(A,C,FFI)wl_state) w s.
     ODD k ==>
     wl_get_vars (MAP adjust_var args) (wl_state_locals_fupd (K (insert k w s)) t) =
     wl_get_vars (MAP adjust_var args) (wl_state_locals_fupd (K s) t)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  SIMP[MAP; wl_get_vars_def; wl_get_var_def; lookup_insert] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(adjust_var h = k)` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[adjust_var_def] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]);;

(* HOL4 line 301 *)
let get_vars_with_store = prove
 (`!args (t:(A,C,FFI)wl_state) s.
     wl_get_vars args (wl_state_locals_fupd (K (wl_state_locals t))
                         (wl_state_store_fupd (K s) t)) =
     wl_get_vars args t`,
  LIST_INDUCT_TAC THEN SIMP[wl_get_vars_def; wl_get_var_def]);;

(* HOL4 line 308 *)
let word_less_lemma1 = prove
 (`!v2 v1:A word. word_ilt v2 v1 <=> ~(word_ile v1 v2)`,
  MESON_TAC[WORD_NOT_LESS]);;

(* HOL4 line 314 *)
let get_vars_2_imp = prove
 (`!x1 x2 (s:(A,C,FFI)wl_state) y1 y2.
     wl_get_vars [x1;x2] s = SOME [y1;y2] ==>
     wl_get_var x1 s = SOME y1 /\ wl_get_var x2 s = SOME y2`,
  REWRITE_TAC[wl_get_vars_def] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  SIMP[]);;

(* HOL4 line 322 *)
let get_vars_1_imp = prove
 (`!x1 (s:(A,C,FFI)wl_state) y1.
     wl_get_vars [x1] s = SOME [y1] ==> wl_get_var x1 s = SOME y1`,
  REWRITE_TAC[wl_get_vars_def] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  SIMP[]);;

(* HOL4 line 329 *)
let data_to_word_assignProof_LESS_DIV_16_IMP = prove
 (`!n k. n < k DIV 16 ==> 16 * n + 2 < k:num`,
  REPEAT GEN_TAC THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC);;

(* HOL4 line 335 *)
let lookup_loc_lemma = prove
 (`!(y2:(A word_loc)spt) permute l' permute' (keep_names:B spt) (locals:(A word_loc)spt) y1
    l1 l2.
     env_to_list y2 permute = (l',permute') /\
     cut_envs (adjust_sets keep_names) locals = SOME (y1,y2) /\
     lookup 0 (sptree_union y2 y1) = SOME (wl_Loc l1 l2) ==>
     ALOOKUP l' 0 = NONE /\ lookup 0 y1 = SOME (wl_Loc l1 l2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  SUBGOAL_THEN `lookup 0 (y2:(A word_loc)spt) = NONE` ASSUME_TAC THENL
   [UNDISCH_TAC `cut_envs (adjust_sets (keep_names:B spt)) (locals:(A word_loc)spt) =
                 SOME (y1,y2)` THEN
    REWRITE_TAC[cut_envs_def; cut_names_def; adjust_sets_def] THEN
    REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[lookup_inter_alt; NOT_0_domain];
    UNDISCH_TAC `lookup 0 (sptree_union (y2:(A word_loc)spt) y1) = SOME (wl_Loc l1 l2)` THEN
    ASM_REWRITE_TAC[lookup_union] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 351 *)
let word_exp_real_addr = prove
 (`!c (t:(A,C,FFI)wl_state) ptr_w a a1.
     get_real_addr c (wl_state_store t) ptr_w = SOME a /\
     shift_length c < dimindex (:A) /\ good_dimindex (:A) /\
     lookup (adjust_var a1) (wl_state_locals t) = SOME (wl_Word ptr_w) ==>
     !w. wl_word_exp (wl_state_locals_fupd
                        (K (insert 1 (wl_Word (w:A word)) (wl_state_locals t))) t)
           (real_addr c (adjust_var a1)) = SOME (wl_Word a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN
  EXISTS_TAC `ptr_w:A word` THEN
  SIMP[wl_get_var_def; lookup_insert; adjust_var_NEQ]);;

(* HOL4 line 362 *)
let word_exp_real_addr_2 = prove
 (`!c (t:(A,C,FFI)wl_state) ptr_w a a1.
     get_real_addr c (wl_state_store t) ptr_w = SOME a /\
     shift_length c < dimindex (:A) /\ good_dimindex (:A) /\
     lookup (adjust_var a1) (wl_state_locals t) = SOME (wl_Word ptr_w) ==>
     !w1 w2.
       wl_word_exp
         (wl_state_locals_fupd
            (K (insert 3 (wl_Word (w1:A word)) (insert 1 (wl_Word w2) (wl_state_locals t))))
            t)
         (real_addr c (adjust_var a1)) = SOME (wl_Word a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN
  EXISTS_TAC `ptr_w:A word` THEN
  SIMP[wl_get_var_def; lookup_insert; adjust_var_NEQ]);;

(* HOL4 line 375 *)
let encode_header_IMP_BIT0 = prove
 (`!c tag l (w:A word). encode_header c tag l = SOME w ==> bit 0 w`,
  REWRITE_TAC[encode_header_def; make_header_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_LSB_WORD; DIMINDEX_GT_0] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 382 *)
let get_addr_inj = prove
 (`!p1 p2 c.
     p1 * 2 EXP shift_length c < dimword (:A) /\
     p2 * 2 EXP shift_length c < dimword (:A) /\
     get_addr c p1 (wl_Word (word 0:A word)) = get_addr c p2 (wl_Word (word 0)) ==>
     p1 = p2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_addr_def; get_lowerbits_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `1 <= shift_length c` ASSUME_TAC THENL
   [REWRITE_TAC[shift_length_def] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_shl (word p1) (shift_length c):A word =
                word_shl (word p2) (shift_length c)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_1;
                BIT_WORD_BITS; BIT_WORD_0] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
     [SUBGOAL_THEN `~(shift_length c <= 0)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_SHL; VAL_WORD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  SUBGOAL_THEN `!p k. ~(k = 0) ==> p <= p * k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `p = p * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p1 < 2 EXP dimindex(:A) /\ p2 < 2 EXP dimindex(:A)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LET_TRANS THENL
     [EXISTS_TAC `p1 * 2 EXP shift_length c`; EXISTS_TAC `p2 * 2 EXP shift_length c`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[EQ_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]);;

(* HOL4 line 415 *)
let Word64Rep_inj = prove
 (`!w1 w2. good_dimindex(:A) ==>
           (Word64Rep (:A) w1 = Word64Rep (:A) w2 <=> w1 = w2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def; Word64Rep_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[injectivity "heap_element"; PAIR_EQ; CONS_11; injectivity "word_loc"] THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < 32` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i <= 31` (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(K ALL_TAC o SPEC `i:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i - 32`) THEN
      SUBGOAL_THEN `i - 32 < 32 /\ (i - 32) + 32 <= 63 /\ (i - 32) + 32 = i`
        (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `i <= 63` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

(* HOL4 line 423 *)
let IMP_read_bytearray_GENLIST = prove
 (`!(ls:B list) len (a:A word) g.
     len = LENGTH ls /\
     (!i. i < len ==> g (word_add a (word i)) = SOME (EL i ls)) ==>
     read_bytearray a len g = SOME ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[read_bytearray_def];
    STRIP_TAC THEN VAR_EQ_TAC THEN
    REWRITE_TAC[read_bytearray_def] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; EL; HD; WORD_ADD_0] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`LENGTH (t:B list)`; `word_add a (word 1):A word`;
                                  `g:A word->B option`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[LT_SUC; EL; TL] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE;
      DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]]);;

(* HOL4 line 441 *)
let lookup_IMP_insert_EQ = prove
 (`!t x (y:A). lookup x t = SOME y ==> insert x y t = t`,
  MESON_TAC[insert_unchanged]);;

(* HOL4 line 447 *)
let data_to_word_assignProof_set_vars_sing = prove
 (`!n (w:A word_loc) (t:(A,C,FFI)wl_state). wl_set_vars [n] [w] t = wl_set_var n w t`,
  REWRITE_TAC[wl_set_vars_def; wl_set_var_def; alist_insert_def]);;

(* HOL4 line 453 *)
let NONNEG_INT = prove
 (`!i:int. &0 <= i ==> ?j. i = &j`,
  MESON_TAC[INT_EQ_NUM_LEMMA]);;

(* HOL4 line 459 *)
let BIT_X_1 = prove
 (`!i. numbit i 1 = (i = 0)`,
  GEN_TAC THEN REWRITE_TAC[numbit] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EXP; DIV_1; ARITH] THEN
  SUBGOAL_THEN `1 DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ARITH]) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE `2 EXP 1 <= x ==> 1 < x`) THEN
  REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

(* HOL4 line 465 *)
let minus_2_word_and_id = prove
 (`!w:A word. ~(bit 0 w) ==> word_and (word_neg (word 2)) w = w`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_neg (word 2):A word = word_not (word 1)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_1] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i = 0` THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 475 *)
let FOUR_MUL_LSL = prove
 (`!i k. word_shl (word (4 * i):A word) k = word_shl (word i) (k + 2)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_AC]);;

(* HOL4 line 481 *)
let evaluate_BignumHalt = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs reg w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     wl_get_var reg t = SOME (wl_Word w) ==>
     ?r. (wl_evaluate (BignumHalt reg,t) =
            if bit 0 w then (SOME NotEnoughSpace,r) else (NONE,t)) /\
         wl_state_ffi r = data_state_ffi s /\ wl_state_ffi t = data_state_ffi s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[BignumHalt_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_get_var_imm_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff] THEN
  ASM_CASES_TAC `bit 0 (w:A word)` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_GiveUp) THEN MESON_TAC[];
    REWRITE_TAC[wl_evaluate_def] THEN EXISTS_TAC `t:(A,C,FFI)wl_state` THEN
    ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]]);;

(* HOL4 line 497 *)
let evaluate_GiveUp2 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     ?r. wl_evaluate (GiveUp,t) = (SOME NotEnoughSpace,r) /\
         wl_state_ffi r = data_state_ffi s /\ wl_state_ffi t = data_state_ffi s /\
         option_le (wl_state_stack_max r) (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_GiveUp) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `wl_evaluate (GiveUp,t:(A,C,FFI)wl_state) = (SOME NotEnoughSpace,r)` THEN
  REWRITE_TAC[GiveUp_def] THEN SIMP[wl_evaluate_def; word_exp_rw; wl_set_var_def] THEN
  REWRITE_TAC[wl_alloc_def] THEN
  CASES_ON `cut_envs (adjust_sets (LN:num_set))
              (insert 1 (wl_Word (word_neg (word 1):A word))
                 (wl_state_locals (t:(A,C,FFI)wl_state)))` THEN SIMP[] THEN
  EVERY_CASE_TAC THEN SIMP[PAIR_EQ; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP wl_pop_env_const) THEN SIMP[] THEN DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_const) THEN SIMP[] THEN DISCH_THEN(K ALL_TAC) THEN
  CASES_ON `a:(A word_loc)spt#(A word_loc)spt` THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIRARG_TAC THEN SIMP[wl_set_store_def] THEN
  REWRITE_TAC[option_le_OPTION_MAP2_MAX; wl_stack_size_def; ITLIST; o_THM;
              stack_size_frame_def] THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                 (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; wl_stack_size_def] THEN
  MESON_TAC[option_add_comm]);;

(* HOL4 line 522 *)
let evaluate_BignumHalt2 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs reg w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     wl_get_var reg t = SOME (wl_Word w) ==>
     ?r. (wl_evaluate (BignumHalt reg,t) =
            if bit 0 w then (SOME NotEnoughSpace,r) else (NONE,t)) /\
         wl_state_ffi r = data_state_ffi s /\ wl_state_ffi t = data_state_ffi s /\
         option_le (wl_state_stack_max r) (wl_state_stack_max t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[BignumHalt_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_get_var_imm_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff] THEN
  ASM_CASES_TAC `bit 0 (w:A word)` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_GiveUp2) THEN MESON_TAC[];
    REWRITE_TAC[wl_evaluate_def] THEN EXISTS_TAC `t:(A,C,FFI)wl_state` THEN
    REWRITE_TAC[option_le_refl] THEN
    ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]]);;

(* the memory_rel conjunct of state_rel with v1 = NONE, the stack part      *)
(* reassociated (HOL4: fs [state_rel_thm] then GSYM APPEND_ASSOC)          *)
let ASP1AUX_state_rel_memory_rel = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

(* HOL4 line 537 *)
let state_rel_get_var_Number_IMP_alt = prove
 (`!k i c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var k (data_state_locals s) = SOME (data_Number i) /\
     wl_get_var (2 * k + 2) t = SOME a1 ==>
     ?w:A word. a1 = wl_Word w /\ (bit 0 w <=> ~small_int (:A) i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_var (adjust_var k) (t:(A,C,FFI)wl_state) = SOME a1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[adjust_var_def]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  DRULE_ALL memory_rel_get_var_IMP THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME `good_dimindex(:A)`)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP memory_rel_any_Number_IMP));;

(* HOL4 line 551 (local) *)
let EXISTS_NOT_IN_spt_DOMAIN = prove
 (`!refs:A spt. ?x. ~(x IN domain refs)`,
  MESON_TAC[num_FINITE_AVOID; FINITE_domain]);;

(* HOL4 line 562 *)
let LEAST_NOTIN_spt_DOMAIN = prove
 (`!refs:A spt. ~((minimal x. ~(x IN domain refs)) IN domain refs)`,
  GEN_TAC THEN MP_TAC(ISPEC `refs:A spt` EXISTS_NOT_IN_spt_DOMAIN) THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN SIMP_TAC[]);;

(* HOL4 line 571 *)
let option_le_add_indv = prove
 (`!n m r. option_le (OPTION_MAP2 (+) n m) r ==> option_le n r /\ option_le m r`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; option_le_def] THEN
  ARITH_TAC);;

(* HOL4 line 578 *)
let option_le_add_drop_right = prove
 (`!x y z. option_le x y ==> option_le x (OPTION_MAP2 (+) z y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC option_le_trans THEN
  EXISTS_TAC `y:num option` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[option_add_comm] THEN REWRITE_TAC[option_le_add]);;

(* HOL4 line 587 *)
let word_exp_SmallLsr = prove
 (CASE_TERM
  `!n (s:(A,C,FFI)wl_state) e.
     n < dimindex(:A) ==>
     wl_word_exp s (SmallLsr e n) =
     match wl_word_exp s e with
       SOME (wl_Word w) -> SOME (wl_Word (word_ushr (w:A word) n))
     | res -> (if n = 0 then res else NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SmallLsr_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_USHR_ZERO; word_exp_rw] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) e` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[] THEN NO_TAC) THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[WORD_USHR_ZERO; VAL_WORD; word_sh_def] THEN
  SUBGOAL_THEN `n MOD 2 EXP dimindex(:A) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `dimindex(:A)` THEN ASM_REWRITE_TAC[GSYM dimword_def; dimindex_lt_dimword];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n >= dimindex(:A))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[OPTION_MAP_DEF]);;

(* HOL4 line 604 *)
let evaluate_MakeBytes = prove
 (CASE_TERM
  `!n (s:(A,C,FFI)wl_state).
     good_dimindex (:A) ==>
     wl_evaluate (MakeBytes n,s) =
     match wl_get_var n s with
       SOME (wl_Word w) ->
         (NONE,wl_set_var n (wl_Word (word_of_byte (word_ushr (w:A word) 2))) s)
     | _ -> (SOME wl_Error,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  REWRITE_TAC[MakeBytes_def; data_to_word_list_Seq_def] THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  CASES_ON `wl_get_var n (s:(A,C,FFI)wl_state)` THEN
  TRY(CASES_ON `a:(A)word_loc`) THEN
  SIMP[wl_evaluate_def; word_exp_rw; wl_set_var_def; VAL_WORD; MOD_LT; word_of_byte_def;
       insert_shadow; WORD_OR_0] THEN
  REWRITE_TAC[WORD_OR_SYM]);;

(* HOL4 line 621 *)
let w2w_shift_shift = prove
 (`!w:byte. good_dimindex (:A) ==>
            (word_ushr (word_shl (word_zx w) 2) 2:A word) = word_zx w`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_ZX; ADD_SUB] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `bit i (w:byte)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[BIT_GUARD]) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

(* HOL4 line 629: fun sort_tac (a tactic) *)

(* ASP1AUX: a NotEnoughSpace result of the first part of a Seq *)
let ASP1AUX_Seq_halt = prove
 (`!c1 c2 (s:(A,C,FFI)wl_state) r.
     wl_evaluate (c1,s) = (SOME NotEnoughSpace,r) ==>
     wl_evaluate (wl_Seq c1 c2,s) = (SOME NotEnoughSpace,r)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT]);;

(* ASP1AUX: last_bytes peeled from its last byte *)
let ASP1AUX_last_bytes_snoc = prove
 (`!k m b (w:A word) be.
     good_dimindex(:A) /\ m + SUC k <= dimindex(:A) DIV 8 ==>
     last_bytes (SUC k) b (word m:A word) w be =
     set_byte (word (m + k)) b (last_bytes k b (word m) w be) be`,
  INDUCT_TAC THENL
   [REWRITE_TAC[last_bytes_simp; ADD_CLAUSES]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 last_bytes_simp] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`m + 1`; `b:byte`; `w:A word`; `be:bool`] th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m + SUC (SUC k) <= dimindex(:A) DIV 8` THEN
                  ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[set_byte_sort] THEN
  SUBGOAL_THEN `~(m = (m + 1) + k) /\ m < dimindex(:A) DIV 8 /\
                (m + 1) + k < dimindex(:A) DIV 8 /\ ~((m + 1) + k = m)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `m + SUC (SUC k) <= dimindex(:A) DIV 8` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[last_bytes_simp; GSYM WORD_ADD; ARITH_RULE `m + SUC k = (m + 1) + k`]);;

let ASP1AUX_last_bytes_snoc_num = prove
 (`!k m b (w:A word) be.
     good_dimindex(:A) /\ ~(k = 0) /\ m + k <= dimindex(:A) DIV 8 ==>
     last_bytes k b (word m:A word) w be =
     set_byte (word (m + (k - 1))) b (last_bytes (k - 1) b (word m) w be) be`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k - 1`; `m:num`; `b:byte`; `w:A word`; `be:bool`] ASP1AUX_last_bytes_snoc) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> SUC (k - 1) = k`]);;

(* ASP1AUX: byte addresses inside an aligned word *)
let ASP1AUX_byte_align_add_aligned = prove
 (`!(a:A word) i. good_dimindex(:A) /\ byte_aligned a /\ i < dimindex(:A) DIV 8 ==>
                  byte_align (word_add a (word i)) = a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_align_def; byte_aligned_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC align_add_aligned THEN ASM_REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN UNDISCH_TAC `i < dimindex(:A) DIV 8` THEN
  ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 4 ==> i < 4294967296`;
               ARITH_RULE `i < 8 ==> i < 18446744073709551616`]);;

let ASP1AUX_set_byte_add_aligned = prove
 (`!(a:A word) i b v be. good_dimindex(:A) /\ byte_aligned a /\ i < dimindex(:A) DIV 8 ==>
                         set_byte (word_add a (word i)) b v be = set_byte (word i) b v be`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC set_byte_change_a THEN
  SUBGOAL_THEN `byte_align (a:A word) = a` (fun th -> GEN_REWRITE_TAC
    (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THENL
   [MP_TAC(SPECL [`a:A word`; `0`] ASP1AUX_byte_align_add_aligned) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN ASM_SIMP_TAC[w2n_add_byte_align_lemma]);;

let ASP1AUX_word_small_eq = prove
 (`!i j. good_dimindex(:A) /\ i < 8 /\ j < 8 ==> (word i:A word = word j <=> i = j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 8 ==> i < 4294967296`;
               ARITH_RULE `i < 8 ==> i < 18446744073709551616`]);;

(* ASP1AUX: the steps of WriteLastBytes and a tactic that performs them *)
let ASP1AUX_WLB_If = prove
 (`!nv (s:(A,C,FFI)wl_state) k i P.
     good_dimindex(:A) /\ k < 8 /\ i < 8 /\
     lookup nv (wl_state_locals s) = SOME (wl_Word (word k)) ==>
     wl_evaluate (wl_If asm_Equal nv (Imm (word i)) wl_Skip P, s) =
     if k = i then (NONE, s) else wl_evaluate (P, s)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ASP1AUX_word_small_eq] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN REWRITE_TAC[]);;

let ASP1AUX_WLB_Store = prove
 (`!av bv (s:(A,C,FFI)wl_state) (a:A word) b i v P.
     good_dimindex(:A) /\ byte_aligned a /\ i < dimindex(:A) DIV 8 /\
     lookup av (wl_state_locals s) = SOME (wl_Word a) /\
     lookup bv (wl_state_locals s) = SOME (wl_Word b) /\
     a IN wl_state_mdomain s /\ wl_state_memory s a = wl_Word v ==>
     wl_evaluate (wl_Seq (wl_Inst (Mem Store8 bv (Addr av (word i)))) P, s) =
     wl_evaluate (P, wl_state_memory_fupd
        (K ((a =+ wl_Word (set_byte (word i) (word_zx b) v (wl_state_be s)))
              (wl_state_memory s))) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN
  REWRITE_TAC[wl_evaluate_def; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[word_exp_rw; MAP; ITLIST; WORD_ADD_0] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ITLIST; WORD_ADD_0; OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN
  ASM_SIMP_TAC[ASP1AUX_byte_align_add_aligned; ASP1AUX_set_byte_add_aligned] THEN
  CASE_REWRITE_TAC[]);;

let ASP1AUX_WLB_STEP_TAC : tactic = fun (asl,w as g) ->
  let l = lhs w in
  let prog, st = dest_pair (rand l) in
  let f, args = strip_comb prog in
  let lookup_val v =
    let c = find (fun c -> try let ll = lhs c in
                     let f2,a2 = strip_comb ll in
                     fst(dest_const f2) = "lookup" && hd a2 = v
                   with Failure _ -> false) (map concl (List.concat (map (CONJUNCTS o snd) asl))) in
    rand(rand(rhs c)) in
  match fst(dest_const f) with
    "wl_If" ->
      let nv = el 1 args and ii = rand(rand(el 2 args)) and pP = el 4 args in
      let k = rand(lookup_val nv) in
      (MP_TAC(ISPECL [nv; st; k; ii; pP] ASP1AUX_WLB_If) THEN
       ANTS_TAC THENL [SIMP[ARITH]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH_EQ]]) g
  | "wl_Seq" ->
      let inst = el 0 args and pP = el 1 args in
      let mem = rand inst in
      let margs = snd(strip_comb mem) in
      let bv = el 1 margs and addr = el 2 margs in
      let av = rand(rator addr) and ii = rand(rand addr) in
      let a = lookup_val av and b = lookup_val bv in
      let memtm = mk_comb(mk_comb(`wl_state_memory:(A,C,FFI)wl_state->A word->(A)word_loc`,
                                  st), a) in
      let memth = CAKE_SIMP_CONV ([UPDATE_APPLY1] @ map snd asl) memtm in
      let v = rand(rhs(concl memth)) in
      (MP_TAC(ISPECL [av; bv; st; a; b; ii; v; pP] ASP1AUX_WLB_Store) THEN
       ANTS_TAC THENL [SIMP[ARITH; UPDATE_APPLY1]; DISCH_THEN SUBST1_TAC]) g
  | _ -> failwith "ASP1AUX_WLB_STEP_TAC";;

(* HOL4 line 633 *)
let evaluate_WriteLastBytes = prove
 (`!av bv nv (s:(A,C,FFI)wl_state) (a:A word) b n w.
     good_dimindex(:A) /\ val n < dimindex(:A) DIV 8 /\
     wl_get_vars [av;bv;nv] s = SOME [wl_Word a; wl_Word b; wl_Word n] /\
     byte_aligned a /\ a IN wl_state_mdomain s /\ wl_state_memory s a = wl_Word w ==>
     wl_evaluate (WriteLastBytes av bv nv,s) =
       (NONE,wl_state_memory_fupd
          (K ((a =+ wl_Word (last_bytes (val n) (word_zx b) (word 0) w (wl_state_be s)))
                (wl_state_memory s))) s)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[get_vars_SOME_IFF; wl_get_var_def]) THEN
   ABBREV_TAC `k = val (n:A word)` THEN
   SUBGOAL_THEN `n:A word = word k` SUBST_ALL_TAC THENL
    [EXPAND_TAC "k" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
   SUBGOAL_THEN `byte_align (a:A word) = a /\
                 (!b v be. set_byte (a:A word) b v be = set_byte (word 0) b v be)`
     STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
      [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
       ALL_TAC] THEN
     MP_TAC(SPECL [`a:A word`; `0`] ASP1AUX_byte_align_add_aligned) THEN
     MP_TAC(SPECL [`a:A word`; `0`] ASP1AUX_set_byte_add_aligned) THEN
     ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_state_memory_fupd (K ((a =+ wl_Word w) (wl_state_memory s))) s =
                 (s:(A,C,FFI)wl_state)` ASSUME_TAC THENL
    [REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
       `wl_state_memory (s:(A,C,FFI)wl_state) a = wl_Word w`)) THEN
     REWRITE_TAC[APPLY_UPDATE_ID];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `dimindex(:A) = 32 \/ dimindex(:A) = 64` MP_TAC THENL
    [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `dimindex(:A) DIV 8`))
                                              (concl th) && is_binary "<" (concl th))) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[ARITH_RULE `k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`;
               ARITH_RULE `k < 8 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
                                     k = 6 \/ k = 7`] THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   REWRITE_TAC[WriteLastBytes_def; WriteLastByte_aux_def] THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
   REPEAT ASP1AUX_WLB_STEP_TAC THEN
   SIMP[UPDATE_EQ; ASP1AUX_last_bytes_snoc_num; last_bytes_simp; ARITH]));;

(* HOL4 line 681 *)
let data_to_word_assignProof_byte_aligned_bytes_in_word = prove
 (`!w:A word. good_dimindex (:A) ==>
              byte_aligned (word_mul w bytes_in_word) /\
              byte_aligned (word_mul bytes_in_word w:A word)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; byte_aligned_def; bytes_in_word_def] THEN
  SUBGOAL_THEN `!k. word_mul (w:A word) (word (2 EXP k)) = word_shl w k /\
                    word_mul (word (2 EXP k)) w = word_shl w k`
    (fun th -> STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
               REWRITE_TAC[ARITH_RULE `4 = 2 EXP 2 /\ 8 = 2 EXP 3`; th] THEN
               CONV_TAC(DEPTH_CONV LOG2_CONV) THEN
               REWRITE_TAC[LOG2_TWOEXP] THEN SIMP_TAC[aligned_lsl_leq; LE_REFL]) THEN
  REWRITE_TAC[WORD_MUL_LSL] THEN REWRITE_TAC[WORD_MUL_SYM]);;

(* HOL4 line 694 *)
let is_env_def = cake_def
  `is_env st <=> (?n vs. st = data_Env n vs)`;;

(* HOL4 line 699 (the unused bound variable b is left out) *)
let size_of_Number_head = prove
 (`!vs lims refs seen n.
     small_num (limits_arch_64_bit lims) n ==>
     (size_of lims (CONS (data_Number n) vs) refs seen = size_of lims vs refs seen)`,
  LIST_INDUCT_TAC THEN SIMP[size_of_def] THEN REPEAT STRIP_TAC THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN SIMP[]);;

(* HOL4 line 707 (local; HOL4: ADD_DIV_ADD_DIV |> Q.SPEC 4 |> SIMP_RULE ...  *)
(* |> Q.SPEC 1 |> ... |> Q.SPEC i |> PURE_ONCE_REWRITE_RULE [ADD_SYM])      *)
let ADD4DIV4 = prove
 (`!i. (i + 4) DIV 4 = i DIV 4 + 1`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i MOD 4` THEN
  MP_TAC(SPECL [`i:num`; `4`] DIVISION) THEN ARITH_TAC);;

(* HOL4 line 712 (local; as ADD4DIV4 with 8) *)
let ADD8DIV8 = prove
 (`!i. (i + 8) DIV 8 = i DIV 8 + 1`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i MOD 8` THEN
  MP_TAC(SPECL [`i:num`; `8`] DIVISION) THEN ARITH_TAC);;


(* one step of symbolic evaluation: for the first subterm                   *)
(* wl_evaluate (wl_Seq c1 c2,s) of the goal, evaluate c1 with the kit's      *)
(* simplifier (thl and the assumptions); when that gives (NONE,s1), replace  *)
(* the subterm by wl_evaluate (c2,s1)                                        *)
let ASP1AUX_STEP_TAC thl : tactic = fun (asl,w as g) ->
  let is_seq_eval t =
    try let f,p = dest_comb t in
        fst(dest_const f) = "wl_evaluate" &&
        (let prog,_ = dest_pair p in
         fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
    with Failure _ -> false in
  let t = find_term is_seq_eval w in
  let f,p = dest_comb t in
  let prog,s = dest_pair p in
  let c1 = rand(rator prog) and c2 = rand prog in
  let tm = mk_comb(f,mk_pair(c1,s)) in
  let th = CAKE_SIMP_CONV (thl @ map snd asl) tm in
  let th2 = SPEC c2 (MATCH_MP IL2AUX_evaluate_Seq_NONE th) in
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th2] g;;

let ASP1AUX_EVAL_TAC thl = REPEAT (ASP1AUX_STEP_TAC thl);;

(* the memory_rel conjunct of state_rel without its v1 part (HOL4:          *)
(* fs [state_rel_thm] then memory_rel_drop)                                 *)
let ASP1AUX_state_rel_memory_rel_drop = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) vs locs.
     data_to_word_gcProof_state_rel c l1 l2 s t vs locs ==>
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP memory_rel_drop));;

(* ASP1AUX: state_rel_get_var_Number_IMP (HOL4 line 1311), proved here     *)
(* because RefByte_thm uses it                                              *)
let ASP1AUX_state_rel_get_var_Number = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) vs locs i n.
     data_to_word_gcProof_state_rel c l1 l2 s t vs locs /\
     data_get_var i (data_state_locals s) = SOME (data_Number (&n)) /\
     small_int (:A) (&n) ==>
     wl_get_var (adjust_var i) t = SOME (wl_Word (Smallnum (&n):A word))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `data_get_var i (data_state_locals (s:(C,FFI)data_state)) =
             SOME (data_Number (&n))`) o MATCH_MP state_rel_get_var_IMP) THEN
  DISCH_THEN(X_CHOOSE_TAC `w1:A word_loc`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel_drop) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def; wl_get_var_def]) THEN
  DRULE_ALL memory_rel_lookup THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP IMP_memory_rel_Number o
    CONJ (ASSUME `good_dimindex(:A)`) o CONJ (ASSUME `small_int (:A) (&n)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_Number_EQ o
    C CONJ (CONJ (DISJ1 (ASSUME `small_int (:A) (&n)`) `small_int (:A) (&n)`)
                 (ASSUME `good_dimindex(:A)`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[wl_get_var_def] THEN
  UNDISCH_TAC `wl_Word (Smallnum (&n)) = wl_Word (v1:A word)` THEN
  REWRITE_TAC[injectivity "word_loc"] THEN ASM_MESON_TAC[]);;

(* ASP1AUX: helpers for RefByte_thm: the data side of RefByte *)
let ASP1AUX_RefByte_data = prove
 (`!fl vals (s1:(C,FFI)data_state) v s2.
     data_do_app (MemOp (RefByte fl)) vals s1 = Rval (v,s2) ==>
     ?i (b:byte).
       vals = [data_Number (&i); data_Number (&(val b))] /\
       v = data_RefPtr T (minimal ptr. ~(ptr IN domain (data_state_refs s1))) /\
       data_state_refs s2 =
         insert (minimal ptr. ~(ptr IN domain (data_state_refs s1)))
           (bvl_ByteArray fl (REPLICATE i b)) (data_state_refs s1) /\
       data_state_space s2 = 0 /\
       data_state_stack_max s2 =
         OPTION_MAP2 MAX (data_state_stack_max s1)
           (OPTION_MAP2 (+)
              (stack_consumed (data_state_stack_frame_sizes s1) (data_state_limits s1)
                 (MemOp (RefByte fl)) vals)
              (OPTION_MAP2 (+) (size_of_stack (data_state_stack s1))
                 (data_state_locals_size s1))) /\
       data_state_locals s2 = data_state_locals s1 /\
       data_state_locals_size s2 = data_state_locals_size s1 /\
       data_state_stack s2 = data_state_stack s1 /\
       data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s1 /\
       data_state_code s2 = data_state_code s1 /\
       data_state_compile s2 = data_state_compile s1 /\
       data_state_compile_oracle s2 = data_state_compile_oracle s1 /\
       data_state_clock s2 = data_state_clock s1 /\
       data_state_ffi s2 = data_state_ffi s1 /\
       data_state_handler s2 = data_state_handler s1 /\
       data_state_global s2 = data_state_global s1 /\
       data_state_tstamps s2 = data_state_tstamps s1 /\
       data_state_limits s2 = data_state_limits s1`,
  (REPEAT GEN_TAC THEN
   REWRITE_TAC[data_do_app_def; distinctness "clos_op"; MEM; injectivity "clos_op";
     distinctness "mem_op"; do_space_def; op_space_reset_def] THEN
   REWRITE_TAC[data_do_app_aux_def] THEN
   CASE_REWRITE_TAC[distinctness "clos_op"; injectivity "clos_op"; distinctness "mem_op";
                    injectivity "mem_op"]) THEN
  (EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ]) THEN
  (FIRST_X_ASSUM(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC o MATCH_MP NONNEG_INT)
     (X_CHOOSE_THEN `w:byte` SUBST_ALL_TAC)) THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; injectivity "result"; PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
   MAP_EVERY EXISTS_TAC [`n:num`; `w:byte`] THEN
   SIMP[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF; NUM_OF_INT_OF_NUM;
        GSYM WORD_IWORD; WORD_VAL]));;

let ASP1AUX_small_num_small_int = prove
 (`!arch i. good_dimindex(:A) /\ (arch <=> dimindex(:A) = 64) ==>
            (small_num arch i <=> small_int (:A) i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[small_num_def; small_int_def; dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let ASP1AUX_size_of_small_Numbers = prove
 (`!l vs lims refs seen.
     ALL (\v. ?n. v = data_Number n /\ small_num (limits_arch_64_bit lims) n) l ==>
     size_of lims (APPEND l vs) refs seen = size_of lims vs refs seen`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ALL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:int` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) ASSUME_TAC) THEN
  ASM_SIMP_TAC[size_of_Number_head]);;

let ASP1AUX_cut3_env = prove
 (`!(env:(data_v)spt).
     IS_SOME (lookup 0 env) /\ IS_SOME (lookup 1 env) /\ IS_SOME (lookup 2 env) ==>
     data_cut_env (fromList [one;one;one]) env =
       SOME (mk_wf (sptree_inter env (fromList [one;one;one]))) /\
     (!k v. lookup k (mk_wf (sptree_inter env (fromList [one;one;one]))) = SOME v <=>
            (k = 0 \/ k = 1 \/ k = 2) /\ lookup k env = SOME v)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[data_cut_env_def; lookup_mk_wf; lookup_inter_alt; domain_fromList; LENGTH] THEN
  REWRITE_TAC[pred_set_count_DEF; IN_ELIM_THM; SUBSET; domain_lookup] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `x < 3 <=> x = 0 \/ x = 1 \/ x = 2`] THEN
  SUBGOAL_THEN `!x. x = 0 \/ x = 1 \/ x = 2 ==> ?v. lookup x (env:(data_v)spt) = SOME v`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_MESON_TAC[IS_SOME_EXISTS];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]]);;

let ASP1AUX_size_of_heap_cut3 = prove
 (`!(s:(C,FFI)data_state) ss e xs a0 a1 a2.
     data_state_stack s = CONS (data_Env ss e) xs /\
     lookup 0 (data_state_locals s) = SOME (data_Number a0) /\
     lookup 1 (data_state_locals s) = SOME (data_Number a1) /\
     lookup 2 (data_state_locals s) = SOME (data_Number a2) /\
     small_num (limits_arch_64_bit (data_state_limits s)) a0 /\
     small_num (limits_arch_64_bit (data_state_limits s)) a1 /\
     small_num (limits_arch_64_bit (data_state_limits s)) a2 ==>
     size_of_heap (cut_locals (fromList [one;one;one]) s) =
     size_of_heap (data_state_locals_fupd (K e) (data_state_stack_fupd (K xs)
                     (data_state_locals_size_fupd (K ss) s)))`,
  (REPEAT STRIP_TAC THEN
   MP_TAC(ISPEC `data_state_locals (s:(C,FFI)data_state)` ASP1AUX_cut3_env) THEN
   ASM_REWRITE_TAC[IS_SOME_DEF] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[cut_locals_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[size_of_heap_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[MAP; FLAT; extract_stack_def; GSYM APPEND_ASSOC] THEN
   SUBGOAL_THEN `ALL (\v. ?n. v = data_Number n /\
                       small_num (limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state))) n)
                   (toList (mk_wf (sptree_inter (data_state_locals s) (fromList [one;one;one]))))`
     ASSUME_TAC THENL
    [REWRITE_TAC[GSYM ALL_MEM; MEM_toList] THEN GEN_TAC THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
     FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
     ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[injectivity "data_v"; UNWIND_THM1] THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[ASP1AUX_size_of_small_Numbers]]));;

(* ASP1AUX: word arithmetic for RefByte_code *)
let ASP1AUX_val_wA = prove
 (`!i. good_dimindex(:A) /\ 4 * i < dimword(:A) ==>
       val (word_ushr (word_add (word i) bytes_in_word) (dimindex(:A) - 63):A word) DIV 4 =
       byte_len (:A) i`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[byte_len_def; bytes_in_word_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  REWRITE_TAC[WORD_USHR_ZERO; GSYM WORD_ADD; VAL_WORD_USHR; VAL_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THENL
   [SUBGOAL_THEN `(i + 4) MOD 4294967296 = i + 4` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; REWRITE_TAC[ADD4DIV4]];
    SUBGOAL_THEN `(i + 8) MOD 18446744073709551616 = i + 8` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      REWRITE_TAC[DIV_DIV; ARITH_RULE `2 * 4 = 8`; ADD8DIV8]]]);;

let ASP1AUX_byte_len_limit = prove
 (`!i len. good_dimindex(:A) /\
           i DIV (dimindex(:A) DIV 8) < dimword(:A) DIV dimindex(:A) /\
           i DIV (dimindex(:A) DIV 8) + 1 < 2 EXP len ==>
           byte_len (:A) i < MIN (2 EXP len) (dimword(:A) DIV 16)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[MP4AUX_byte_len] THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let ASP1AUX_memory_rel_NextFree_aligned = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars free.
     memory_rel c be ts refs sp st m dm vars /\
     FLOOKUP st NextFree = SOME (wl_Word free) /\ good_dimindex(:A) ==>
     byte_aligned free`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `FLOOKUP st NextFree = SOME (wl_Word (free:A word))` THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC byte_aligned_add THEN
  ASM_SIMP_TAC[data_to_word_assignProof_byte_aligned_bytes_in_word]);;

let ASP1AUX_shl_shift_mul = prove
 (`!n. good_dimindex(:A) ==>
       word_shl (word n:A word) (backend_common_word_shift(:A)) =
       word_mul (word n) bytes_in_word`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_MUL_LSL; bytes_in_word_def; backend_common_word_shift_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_MUL_SYM]);;

let ASP1AUX_ushr_byte_len = prove
 (`!i. good_dimindex(:A) /\ 4 * i < dimword(:A) ==>
       word_ushr (word_add (word i) bytes_in_word) (backend_common_word_shift(:A)) =
       (word (byte_len (:A) i):A word)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[byte_len_def; bytes_in_word_def; backend_common_word_shift_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_USHR; GSYM WORD_ADD; VAL_WORD] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THENL
   [SUBGOAL_THEN `(i + 4) MOD 4294967296 = i + 4 /\ (i DIV 4 + 1) MOD 4294967296 = i DIV 4 + 1`
      (fun th -> REWRITE_TAC[th; ADD4DIV4]) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`i:num`; `4`] DIVISION) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(i + 8) MOD 18446744073709551616 = i + 8 /\
                  (i DIV 8 + 1) MOD 18446744073709551616 = i DIV 8 + 1`
      (fun th -> REWRITE_TAC[th; ADD8DIV8]) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`i:num`; `8`] DIVISION) THEN ASM_ARITH_TAC]);;

let ASP1AUX_and_bytes_mask = prove
 (`!i. good_dimindex(:A) ==>
       word_and (word i) (word_sub bytes_in_word (word 1)) =
       (word (i MOD (dimindex(:A) DIV 8)):A word)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes_in_word_def] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [MP_TAC(ISPECL [`2`; `i:num`] (INST_TYPE [`:A`,`:N`] WORD_AND_EXP_SUB1));
    MP_TAC(ISPECL [`3`; `i:num`] (INST_TYPE [`:A`,`:N`] WORD_AND_EXP_SUB1))] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ASP1AUX_word_or_7_16 = prove
 (`word_or (word 7) (word 16) = (word 23:A word)`,
  SUBGOAL_THEN `word_and (word 7) (word 16) = (word 0:A word)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
    MP_TAC(ISPECL [`3`; `16`] (INST_TYPE [`:A`,`:N`] WORD_AND_EXP_SUB1)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP WORD_ADD_OR) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP1AUX_RefByte_header = prove
 (`!c fl i. good_dimindex(:A) ==>
     word_or (word_or (word_shl (word_add (word i) bytes_in_word)
                         ((dimindex(:A) - backend_common_word_shift(:A)) -
                          data_to_word_config_len_size c)) (word 7))
             (word (4 * (if fl then 0 else 4))) =
     (make_byte_header c fl i:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[make_byte_header_def; LET_DEF; LET_END_DEF; bytes_in_word_def;
                  backend_common_word_shift_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_OR_0; GSYM WORD_OR_ASSOC; ASP1AUX_word_or_7_16]);;

let ASP1AUX_RefByte_shift_facts = prove
 (`!c (b:byte). good_dimindex(:A) /\ shift_length c < dimindex(:A) ==>
     val (word (backend_common_word_shift(:A)):A word) = backend_common_word_shift(:A) /\
     ~(backend_common_word_shift(:A) = 0) /\
     ~(backend_common_word_shift(:A) >= dimindex(:A)) /\
     val (word (shift_length c - backend_common_word_shift(:A)):A word) =
       shift_length c - backend_common_word_shift(:A) /\
     ~(shift_length c - backend_common_word_shift(:A) >= dimindex(:A)) /\
     val (word ((dimindex(:A) - backend_common_word_shift(:A)) -
                data_to_word_config_len_size c):A word) =
       (dimindex(:A) - backend_common_word_shift(:A)) - data_to_word_config_len_size c /\
     ~((dimindex(:A) - backend_common_word_shift(:A)) - data_to_word_config_len_size c >=
       dimindex(:A)) /\
     word_ushr (word (4 * val b)) 2 = (word (val b):A word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; VAL_WORD; dimword_def] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOD_LT) THEN TRY(ASM_ARITH_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_USHR; VAL_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (SUBGOAL_THEN `(4 * val (b:byte)) MOD 4294967296 = 4 * val b /\
                val b MOD 4294967296 = val b /\
                (4 * val (b:byte)) MOD 18446744073709551616 = 4 * val b /\
                val b MOD 18446744073709551616 = val b`
    (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    SIMP_TAC[DIV_MULT; ARITH_EQ]]));;

let ASP1AUX_val_mod_bytes = prove
 (`!i. good_dimindex(:A) ==>
       val (word (i MOD (dimindex(:A) DIV 8)):A word) = i MOD (dimindex(:A) DIV 8) /\
       i MOD (dimindex(:A) DIV 8) < dimindex(:A) DIV 8`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; VAL_WORD; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THENL
   [EXISTS_TAC `4`; EXISTS_TAC `8`] THEN
  REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ASP1AUX: the memory written by RefByte_code *)
let ASP1AUX_LUPDATE_REPLICATE_last = prove
 (`!k (lw:A) rw. LUPDATE lw k (REPLICATE (SUC k) rw) = APPEND (REPLICATE k rw) [lw]`,
  INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; LUPDATE_def; APPEND];
    POP_ASSUM(MP_TAC o REWRITE_RULE[REPLICATE]) THEN
    REWRITE_TAC[REPLICATE; LUPDATE_def; APPEND] THEN SIMP_TAC[]]);;

let ASP1AUX_RefByte_store_list = prove
 (`!(free:A word) n hd rw lw m dm m1.
     data_to_word_memoryProof_store_list free
       (CONS hd (LUPDATE lw (n - 1) (REPLICATE n rw))) m dm = SOME m1 /\
     0 < n /\ n * (dimindex(:A) DIV 8) < dimword(:A) /\ good_dimindex(:A) ==>
     data_to_word_memoryProof_store_list (word_add free bytes_in_word) (REPLICATE (n - 1) rw)
       ((word_add free (word_mul (word n) bytes_in_word) =+ lw) ((free =+ hd) m)) dm =
     SOME m1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `data_to_word_memoryProof_store_list (free:A word)
       (CONS hd (LUPDATE lw (n - 1) (REPLICATE n rw))) m dm = SOME m1` THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  SUBGOAL_THEN `n = SUC (n - 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; ASP1AUX_LUPDATE_REPLICATE_last] THEN
  DISCH_THEN(MP_TAC o MATCH_MP store_list_append_imp) THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:A word->A word_loc` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `data_to_word_memoryProof_store_list
       (word_add (word_add (free:A word) bytes_in_word)
          (word_mul (word (LENGTH (REPLICATE (n - 1) (rw:A word_loc)))) bytes_in_word))
       [lw:A word_loc] (m2:A word->A word_loc) (dm:A word->bool) =
       SOME (m1:A word->A word_loc)` THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def; LENGTH_REPLICATE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `word_add (word_add free bytes_in_word)
                  (word_mul (word (n - 1)) bytes_in_word) =
                word_add free (word_mul (word (SUC (n - 1))) bytes_in_word):A word`
    SUBST1_TAC THENL
   [REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MATCH_MP_TAC store_list_update_m_outside THEN ASM_REWRITE_TAC[LENGTH_REPLICATE] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_add (word_add free bytes_in_word) (word_mul (word j) bytes_in_word) =
                word_add free (word_mul (word (j + 1)) bytes_in_word):A word` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_ADD_LCANCEL; bytes_in_word_def; GSYM WORD_MUL] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `(j + 1) * dimindex(:A) DIV 8 < dimword(:A) /\
                SUC (n - 1) * dimindex(:A) DIV 8 < dimword(:A) /\ 0 < dimindex(:A) DIV 8`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n * dimindex(:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> is_binary "<" (concl th) && lhand(concl th) = `j:num`)) THEN ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `0 < n ==> SUC (n - 1) = n`];
      UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; EQ_MULT_RCANCEL; ARITH_RULE `0 < d ==> ~(d = 0)`] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_binary "<" (concl th) && lhand(concl th) = `j:num`)) THEN ARITH_TAC);;

let ASP1AUX_shl2_sub4 = prove
 (`!n. good_dimindex(:A) /\ 0 < n /\ 4 * n < dimword(:A) ==>
       word_sub (word_shl (word n) 2) (word 4) = (word (4 * (n - 1)):A word)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(dimindex(:A) - 1 < 2)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[word_lsl_n2w] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `4 * (n - 1) = n * 4 - 4 /\ 4 <= n * 4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[WORD_SUB]);;

(* ASP1AUX: the state relation after RefByte_code *)
let ASP1AUX_option_le_add_0 = prove
 (`!a b. option_le (OPTION_MAP2 (+) a (SOME 0)) (OPTION_MAP2 (+) a b)`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; option_le_def] THEN
  ARITH_TAC);;

let ASP1AUX_option_le_stack = prove
 (`!x f r. option_le (OPTION_MAP2 (+) x r) (OPTION_MAP2 (+) (OPTION_MAP2 MAX f r) x)`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; option_le_def] THEN
  ARITH_TAC);;

let ASP1AUX_RefByte_state_rel = prove
 (`!c l1 l2 r1 r2 (s9:(C,FFI)data_state) (ra:(A,C,FFI)wl_state) (rf:(A,C,FFI)wl_state)
      (sx:(C,FFI)data_state) locs new fl i b (free:A word) curr m1 mx ss e xs.
     data_to_word_gcProof_state_rel c l1 l2 s9 ra NONE locs /\
     data_state_stack s9 = CONS (data_Env ss e) xs /\
     data_state_space s9 = byte_len (:A) i + 1 /\
     memory_rel c (wl_state_be ra) (THE (data_state_tstamps s9))
       (insert new (bvl_ByteArray fl (REPLICATE i b)) (data_state_refs s9))
       (data_state_space s9 - (byte_len (:A) i + 1))
       (wl_state_store ra |+
          (NextFree,wl_Word (word_add free (word_mul bytes_in_word (word (byte_len (:A) i + 1))))))
       m1 (wl_state_mdomain ra)
       (CONS (data_RefPtr T new,make_ptr c (word_sub free curr) (word 0:A word) (byte_len (:A) i))
          (APPEND (join_env (data_state_locals s9)
                    (toAList (sptree_inter (wl_state_locals ra) (adjust_set (data_state_locals s9)))))
             (APPEND [(the_global (data_state_global s9),FAPPLY (wl_state_store ra) Globals)]
                (data_to_word_gcProof_flat (data_state_stack s9) (wl_state_stack ra))))) /\
     data_state_refs sx = insert new (bvl_ByteArray fl (REPLICATE i b)) (data_state_refs s9) /\
     data_state_space sx = 0 /\
     data_state_stack_max sx =
       OPTION_MAP2 MAX (data_state_stack_max s9)
         (OPTION_MAP2 (+)
            (OPTION_MAP2 MAX (lookup RefByte_location (data_state_stack_frame_sizes s9))
                             (lookup Replicate_location (data_state_stack_frame_sizes s9)))
            (OPTION_MAP2 (+) (size_of_stack xs) ss)) /\
     data_state_stack sx = data_state_stack s9 /\
     data_state_stack_frame_sizes sx = data_state_stack_frame_sizes s9 /\
     data_state_code sx = data_state_code s9 /\
     data_state_compile sx = data_state_compile s9 /\
     data_state_compile_oracle sx = data_state_compile_oracle s9 /\
     data_state_ffi sx = data_state_ffi s9 /\
     data_state_handler sx = data_state_handler s9 /\
     data_state_global sx = data_state_global s9 /\
     data_state_tstamps sx = data_state_tstamps s9 /\
     data_state_limits sx = data_state_limits s9 /\
     data_state_locals sx = LN /\ data_state_locals_size sx = SOME 0 /\
     data_state_clock sx = wl_state_clock rf /\
     wl_state_memory rf = m1 /\
     wl_state_store rf =
       wl_state_store ra |+
         (NextFree,wl_Word (word_add (word_add free
            (word_mul (word (byte_len (:A) i)) bytes_in_word)) bytes_in_word)) /\
     wl_state_locals rf = LN /\ wl_state_locals_size rf = SOME 0 /\
     wl_state_stack_max rf = mx /\
     option_le (wl_state_stack_max ra) mx /\
     option_le mx (OPTION_MAP2 MAX (wl_state_stack_max ra)
       (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack ra))
          (lookup Replicate_location (wl_state_stack_size ra)))) /\
     wl_state_stack rf = wl_state_stack ra /\
     wl_state_stack_size rf = wl_state_stack_size ra /\
     wl_state_handler rf = wl_state_handler ra /\
     wl_state_code rf = wl_state_code ra /\
     wl_state_compile rf = wl_state_compile ra /\
     wl_state_compile_oracle rf = wl_state_compile_oracle ra /\
     wl_state_code_buffer rf = wl_state_code_buffer ra /\
     wl_state_data_buffer rf = wl_state_data_buffer ra /\
     wl_state_be rf = wl_state_be ra /\
     wl_state_mdomain rf = wl_state_mdomain ra /\
     wl_state_ffi rf = wl_state_ffi ra /\
     wl_state_gc_fun rf = wl_state_gc_fun ra /\
     wl_state_stack_limit rf = wl_state_stack_limit ra ==>
     data_to_word_gcProof_state_rel c r1 r2 sx rf
       (SOME [(data_RefPtr T new,
               wl_Word (word_or (word_shl (word_sub free curr)
                  (shift_length c - backend_common_word_shift (:A))) (word 1)))]) locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s9:(C,FFI)data_state)
                  (ra:(A,C,FFI)wl_state) NONE locs` THEN
   REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `word_add (word_add free (word_mul (word (byte_len (:A) i)) bytes_in_word))
                   bytes_in_word =
                 word_add free (word_mul bytes_in_word (word (byte_len (:A) i + 1))):A word`
     SUBST1_TAC THENL [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [UNDISCH_TAC `code_oracle_rel c (data_state_compile (s9:(C,FFI)data_state))
       (data_state_compile_oracle s9) (wl_state_store (ra:(A,C,FFI)wl_state))
       (wl_state_compile ra) (wl_state_compile_oracle ra) (wl_state_code_buffer ra)
       (wl_state_data_buffer ra)` THEN
     REWRITE_TAC[code_oracle_rel_def; FLOOKUP_UPDATE; distinctness "store_name"];
     UNDISCH_TAC `ALL (\n. n IN FDOM (wl_state_store (ra:(A,C,FFI)wl_state))) [Globals]` THEN
     REWRITE_TAC[ALL; FDOM_FUPDATE; IN_INSERT] THEN SIMP[];
     REWRITE_TAC[option_DISTINCT];
     REWRITE_TAC[lookup_def; IS_SOME_DEF];
     MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (ra:(A,C,FFI)wl_state)))
                   (wl_state_locals_size ra)` THEN
     REWRITE_TAC[ASP1AUX_option_le_add_0] THEN
     MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `wl_state_stack_max (ra:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `OPTION_MAP2 MAX (wl_state_stack_max (ra:(A,C,FFI)wl_state))
       (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack ra))
          (lookup Replicate_location (wl_state_stack_size ra)))` THEN
     ASM_REWRITE_TAC[option_le_max] THEN CONJ_TAC THENL
      [REWRITE_TAC[option_le_max_right] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[option_le_max_right] THEN DISJ2_TAC THEN
       FIRST_ASSUM(SUBST1_TAC o MATCH_MP stack_rel_IMP_size_of_stack o
         check (fun th -> can (find_term (fun t -> is_const t &&
           fst(dest_const t) = "data_to_word_gcProof_stack_rel")) (concl th))) THEN
       ASM_REWRITE_TAC[size_of_stack_def; ITLIST; o_THM; size_of_stack_frame_def] THEN
       REWRITE_TAC[GSYM size_of_stack_def] THEN
       MP_TAC(ISPECL [`OPTION_MAP2 (+) ss (size_of_stack xs)`;
         `lookup RefByte_location (data_state_stack_frame_sizes (s9:(C,FFI)data_state))`;
         `lookup Replicate_location (data_state_stack_frame_sizes (s9:(C,FFI)data_state))`]
         ASP1AUX_option_le_stack) THEN
       REWRITE_TAC[option_add_comm]];
     UNDISCH_TAC `limits_inv (data_state_limits (s9:(C,FFI)data_state))
       (FLOOKUP (wl_state_store (ra:(A,C,FFI)wl_state)) HeapLength) (wl_state_stack_limit ra)
       (data_to_word_config_len_size c) (data_to_word_config_has_fp_ops c)
       (data_to_word_config_has_fp_tern c)` THEN
     REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name"];
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
     fst(dest_const t) = "data_RefPtr")) (concl th) &&
     (try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" with Failure _ -> false))) THEN
   ASM_REWRITE_TAC[SUB_REFL; make_ptr_def; FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
   MATCH_MP_TAC memory_rel_rearrange THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[inter_LN; toAList_def; foldi_def; join_env_def; FILTER; MAP; APPEND] THEN
   REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]));;

(* HOL4 line 717 *)
let RefByte_thm = prove
 (CASE_TERM
  `!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs vals fl s1 v s2 r1 r2.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars [0;1;2] (data_state_locals s) =
       SOME (APPEND vals [data_Number (&(if fl then 0 else 4))]) /\
     wl_state_clock t = MustTerminate_limit (:A) - 1 /\
     data_pop_env s = SOME s1 /\ is_env (HD (data_state_stack s)) /\
     data_state_locals_size s = lookup RefByte_location (data_state_stack_frame_sizes s) /\
     data_do_app (MemOp (RefByte fl)) vals s1 = Rval (v,s2) ==>
     ?q r new_c.
       wl_evaluate (RefByte_code c,t) = (q,r) /\
       if q = SOME NotEnoughSpace then
         wl_state_ffi r = wl_state_ffi t /\
         option_le (wl_state_stack_max r) (data_state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = data_to_word_None) /\
          no_thunks_in_refs (data_state_refs s) ==>
          match vals with
            CONS (data_Number i) _ ->
              (i < &0 \/
               ~small_num (limits_arch_64_bit (data_state_limits s)) i \/
               ~(num_of_int i DIV (arch_size (data_state_limits s) DIV 8) <
                 dimword (:A) DIV arch_size (data_state_limits s)) \/
               ~(num_of_int i DIV (arch_size (data_state_limits s) DIV 8) + 1 <
                 (2 EXP data_to_word_config_len_size c)) \/
               limits_heap_limit (data_state_limits s1) <
               size_of_heap s1 + num_of_int i DIV (arch_size (data_state_limits s) DIV 8) +
               2))
       else
         ?rv. q = SOME (wl_Result (wl_Loc l1 l2) [rv]) /\
              data_to_word_gcProof_state_rel c r1 r2
                (data_state_locals_fupd (K LN)
                   (data_state_locals_size_fupd (K (SOME 0))
                      (data_state_clock_fupd (K new_c)
                         (data_state_stack_fupd (K (data_state_stack s)) s2))))
                r (SOME [(v,rv)]) locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP1AUX_RefByte_data) THEN
   DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `b:byte` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> fst(dest_var(lhs(concl th))) = "vals")) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> fst(dest_var(lhs(concl th))) = "v")) THEN
   SUBGOAL_THEN `?ss e xs. data_state_stack (s:(C,FFI)data_state) = CONS (data_Env ss e) xs`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `is_env (HD (data_state_stack (s:(C,FFI)data_state)))` THEN
     UNDISCH_TAC `data_pop_env (s:(C,FFI)data_state) = SOME s1` THEN
     REWRITE_TAC[data_pop_env_def; is_env_def] THEN
     SPEC_TAC(`data_state_stack (s:(C,FFI)data_state)`,`st:(stack)list`) THEN
     LIST_INDUCT_TAC THEN REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
     DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n0:num option`
       (X_CHOOSE_THEN `vs0:(data_v)spt` SUBST_ALL_TAC)) THEN
     MAP_EVERY EXISTS_TAC [`n0:num option`; `vs0:(data_v)spt`; `t':stack list`] THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
   UNDISCH_TAC `data_pop_env (s:(C,FFI)data_state) = SOME s1` THEN
   ASM_REWRITE_TAC[data_pop_env_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM; APPEND;
     get_vars_SOME_IFF_data])) THEN
  (REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN CASE_REWRITE_TAC[] THEN
   ABBREV_TAC `tag = if fl then 0 else 4` THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "data_get_var")) (concl th))) THEN
   FIRST_ASSUM((fun th -> MP_TAC(MATCH_MP (MATCH_MP state_rel_get_var_IMP th)
     (ASSUME `data_get_var 0 (data_state_locals (s:(C,FFI)data_state)) =
              SOME (data_Number (&i))`))) o
     check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                                    (t:(A,C,FFI)wl_state) NONE locs`)) THEN
   DISCH_THEN(X_CHOOSE_TAC `tw2:A word_loc`) THEN
   MP_TAC(ISPECL [`0`; `&i:int`; `c:data_to_word_config`; `l1:num`; `l2:num`;
     `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `tw2:A word_loc`]
     state_rel_get_var_Number_IMP_alt) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[adjust_var_def]) THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `w2:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
     check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                                    (t:(A,C,FFI)wl_state) NONE locs`)) THEN
   DISCH_THEN(fun th ->
     let cs = CONJUNCTS th in
     let pick name = find (fun c -> try fst(dest_const(fst(strip_comb(concl c)))) = name
                                    with Failure _ -> false) cs in
     let sl = find (fun c -> concl c = `shift_length c < dimindex(:A)`) cs in
     ASSUME_TAC (pick "good_dimindex") THEN ASSUME_TAC sl THEN
     ASSUME_TAC (REWRITE_RULE[limits_inv_def] (pick "limits_inv"))) THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "limits_stack_limit"))
       (concl th)))) THEN
  (SUBGOAL_THEN `option_le (wl_state_stack_max (t:(A,C,FFI)wl_state))
                   (data_state_stack_max (s:(C,FFI)data_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
   REWRITE_TAC[RefByte_code_def; LET_DEF; LET_END_DEF] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `2`; `w2:A word`] evaluate_BignumHalt2) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
   ASM_CASES_TAC `small_int (:A) (&i)` THENL
    [ALL_TAC;
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r0:(A,C,FFI)wl_state` THEN EXISTS_TAC `0` THEN
     CONJ_TAC THENL [MATCH_MP_TAC ASP1AUX_Seq_halt THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       REWRITE_TAC[option_le_max_right] THEN DISJ1_TAC THEN
       MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
       ASM_REWRITE_TAC[];
       DISCH_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
       MP_TAC(ISPECL [`limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state))`;
                      `&i:int`] ASP1AUX_small_num_small_int) THEN
       ASM_REWRITE_TAC[]]] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
     fst(dest_const t) = "BignumHalt")) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th])) THEN
  (SUBGOAL_THEN `!n. Smallnum (&n) = word (4 * n):A word` ASSUME_TAC THENL
    [REWRITE_TAC[data_to_word_Smallnum_def; INT_OF_NUM_LT; LT; INT_OF_NUM_MUL;
                 NUM_OF_INT_OF_NUM];
     ALL_TAC] THEN
   SUBGOAL_THEN `(w2:A word) = word (4 * i)` SUBST_ALL_TAC THENL
    [MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
       `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`;
       `0`; `i:num`] ASP1AUX_state_rel_get_var_Number) THEN
     ASM_REWRITE_TAC[adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"];
     ALL_TAC] THEN
   SUBGOAL_THEN `4 * i < dimword(:A) /\ i < dimword(:A)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `small_int (:A) (&i)` THEN REWRITE_TAC[small_int_def; INT_OF_NUM_LT] THEN
     MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN
     REWRITE_TAC[ARITH_EQ] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `word_ushr (word (4 * i)) 2 = (word i:A word)` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_USHR; VAL_WORD] THEN
     REWRITE_TAC[GSYM dimword_def] THEN ASM_SIMP_TAC[MOD_LT] THEN
     CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DIV_MULT; ARITH_EQ];
     ALL_TAC] THEN
   SUBGOAL_THEN `dimindex(:A) - 63 < dimindex(:A) /\ ~(2 >= dimindex(:A)) /\
                 val (word 2:A word) = 2` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; VAL_WORD] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_STEP_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     word_exp_SmallLsr; MAP; ITLIST; WORD_ADD_0]) THEN
  (ABBREV_TAC `wA = word_ushr (word_add (word i) bytes_in_word) (dimindex (:A) - 63):A word` THEN
   ABBREV_TAC `limit = MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)` THEN
   (fun (asl,w as g) ->
      let tm = find_term (fun t -> try let f,p = dest_comb t in
                 fst(dest_const f) = "wl_evaluate" &&
                 (let prog,_ = dest_pair p in
                  fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
               with Failure _ -> false) w in
      let t1 = snd(dest_pair(rand tm)) in
      ABBREV_TAC (mk_eq(`t1:(A,C,FFI)wl_state`, t1)) g) THEN
   MP_TAC(ISPEC `wl_evaluate (AllocVar c limit (fromList [one;one;one]),
                              t1:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `qa:((A)wl_result)option`
     (X_CHOOSE_THEN `ra:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
   MP_TAC(ISPEC `data_state_locals (s:(C,FFI)data_state)` ASP1AUX_cut3_env) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN ASM_REWRITE_TAC[IS_SOME_DEF];
     ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `t1:(A,C,FFI)wl_state`; `locs:(num#num)list`; `fromList [one;one;one]`;
     `mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (fromList [one;one;one]))`;
     `wA:A word`; `limit:num`; `qa:((A)wl_result)option`; `ra:(A,C,FFI)wl_state`]
     AllocVar_thm) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t1" THEN
     REWRITE_TAC[state_rel_insert_1; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM;
                 lookup_insert] THEN ASM_REWRITE_TAC[] THEN
     EXPAND_TAC "limit" THEN
     UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
     MATCH_MP_TAC(ARITH_RULE `b < c ==> MIN a b < c`) THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   STRIP_TAC) THEN
  (SUBGOAL_THEN `val (wA:A word) DIV 4 = byte_len (:A) i` ASSUME_TAC THENL
    [EXPAND_TAC "wA" THEN MATCH_MP_TAC ASP1AUX_val_wA THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `arch_size (data_state_limits (s:(C,FFI)data_state)) = dimindex(:A)`
     ASSUME_TAC THENL
    [REWRITE_TAC[arch_size_def] THEN
     REWRITE_TAC[ASSUME `limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state)) <=>
                         dimindex (:A) = 64`] THEN
     UNDISCH_TAC `good_dimindex(:A)` THEN
     REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `val (b:byte) < 256 /\ tag <= 4` STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
     CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     EXPAND_TAC "tag" THEN COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `small_int (:A) (&i) /\ small_int (:A) (&(val (b:byte))) /\
                 small_int (:A) (&tag)` STRIP_ASSUME_TAC THENL
    [MAP_EVERY UNDISCH_TAC [`small_int (:A) (&i)`; `val (b:byte) < 256`; `tag <= 4`] THEN
     UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[small_int_def; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_LE; INT_ARITH `!a b. --(&a:int) <= &b`] THEN
     ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `!j. small_num (limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state))) j
                     <=> small_int (:A) j` ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC ASP1AUX_small_num_small_int THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `size_of_heap (cut_locals (fromList [one;one;one]) (s:(C,FFI)data_state)) =
                 size_of_heap (data_state_locals_fupd (K e) (data_state_stack_fupd (K xs)
                   (data_state_locals_size_fupd (K ss) s)))` ASSUME_TAC THENL
    [MATCH_MP_TAC ASP1AUX_size_of_heap_cut3 THEN
     MAP_EVERY EXISTS_TAC [`&i:int`; `&(val (b:byte)):int`; `&tag:int`] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `qa = SOME NotEnoughSpace:((A)wl_result)option` THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
       lhand (concl th) = `qa = SOME NotEnoughSpace:((A)wl_result)option`)) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `ra:(A,C,FFI)wl_state` THEN EXISTS_TAC `0` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC ASP1AUX_Seq_halt THEN
       UNDISCH_TAC `wl_evaluate (AllocVar c limit (fromList [one; one; one]),t1) =
                    (qa:((A)wl_result)option),(ra:(A,C,FFI)wl_state)` THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       REWRITE_TAC[option_le_max_right] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     STRIP_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_LT; LT] THEN
     REWRITE_TAC[ASSUME `arch_size (data_state_limits (s:(C,FFI)data_state)) = dimindex(:A)`;
       ASSUME `!j. small_num (limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state))) j
                   <=> small_int (:A) j`;
       ASSUME `small_int (:A) (&i)`] THEN
     SUBGOAL_THEN `small_num (dimindex(:A) = 64) (&i)` (fun th -> REWRITE_TAC[th]) THENL
      [MP_TAC(ISPECL [`dimindex(:A) = 64`; `&i:int`] ASP1AUX_small_num_small_int) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[TAUT `~a \/ ~b \/ c <=> a /\ b ==> c`] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "limits_heap_limit"))
         (concl th))) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN EXPAND_TAC "limit" THEN MATCH_MP_TAC ASP1AUX_byte_len_limit THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_SIMP_TAC[MP4AUX_byte_len] THEN ARITH_TAC;
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
     lhand (concl th) = `~(qa = SOME NotEnoughSpace:((A)wl_result)option)`)) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `qa = NONE:((A)wl_result)option`)) THEN
   FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th])) THEN
  (ABBREV_TAC `s9 = data_state_locals_fupd
       (K (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (fromList [one; one; one]))))
       (data_state_space_fupd (K (byte_len (:A) i + 1)) s)` THEN
   SUBGOAL_THEN `data_get_var 0 (data_state_locals (s9:(C,FFI)data_state)) = SOME (data_Number (&i)) /\
                 data_get_var 1 (data_state_locals s9) = SOME (data_Number (&(val (b:byte)))) /\
                 data_get_var 2 (data_state_locals s9) = SOME (data_Number (&tag))`
     STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "s9" THEN REWRITE_TAC[data_get_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_get_var 2 (ra:(A,C,FFI)wl_state) = SOME (wl_Word (word (4 * i))) /\
                 wl_get_var 4 ra = SOME (wl_Word (word (4 * val (b:byte)))) /\
                 wl_get_var 6 ra = SOME (wl_Word (word (4 * tag)))` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s9:(C,FFI)data_state`;
         `ra:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`;
         `0`; `i:num`] ASP1AUX_state_rel_get_var_Number);
       MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s9:(C,FFI)data_state`;
         `ra:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`;
         `1`; `val (b:byte)`] ASP1AUX_state_rel_get_var_Number);
       MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s9:(C,FFI)data_state`;
         `ra:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`;
         `2`; `tag:num`] ASP1AUX_state_rel_get_var_Number)] THEN
     ASM_REWRITE_TAC[adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
     ALL_TAC]) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel o
     check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (s9:(C,FFI)data_state)
                                    (ra:(A,C,FFI)wl_state) NONE locs`)) THEN
   (fun (asl,w as g) ->
      let tm = lhand w in
      let args = snd(strip_comb tm) in
      (DISCH_TAC THEN
       MP_TAC(ISPECL ([`c:data_to_word_config`] @ (tl(butlast args)) @ [last args;
        `minimal ptr. ~(ptr IN domain (data_state_refs (s:(C,FFI)data_state)))`;
        `i:num`; `b:byte`; `fl:bool`]) memory_rel_RefByte_alt)) g) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s9" THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; LEAST_NOTIN_spt_DOMAIN;
                 ARITH_RULE `n < n + 1`] THEN
     UNDISCH_TAC `byte_len (:A) i < limit` THEN EXPAND_TAC "limit" THEN
     UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
     ALL_TAC] THEN
   STRIP_TAC) THEN
  (FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV let_CONV) o
     check (is_let o concl)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP store_list_domain o
     check (fun th -> can (find_term (fun t -> is_const t &&
       fst(dest_const t) = "data_to_word_memoryProof_store_list")) (concl th))) THEN
   REWRITE_TAC[LENGTH; LENGTH_LUPDATE; LENGTH_REPLICATE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(free:A word) IN wl_state_mdomain (ra:(A,C,FFI)wl_state) /\
                 word_add free (word_mul (word (byte_len (:A) i)) bytes_in_word) IN
                   wl_state_mdomain ra` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl) o
         check (fun th -> can (find_term (fun t -> is_const t &&
           fst(dest_const t) = "bytes_in_word")) (concl th))) THEN
       REWRITE_TAC[WORD_MUL_0; WORD_ADD_0; LT_0];
       FIRST_X_ASSUM(MP_TAC o SPEC `byte_len (:A) i` o check (is_forall o concl) o
         check (fun th -> can (find_term (fun t -> is_const t &&
           fst(dest_const t) = "bytes_in_word")) (concl th))) THEN
       REWRITE_TAC[LT]];
     ALL_TAC] THEN
   SUBGOAL_THEN `byte_aligned (free:A word)` ASSUME_TAC THENL
    [MATCH_MP_TAC ASP1AUX_memory_rel_NextFree_aligned THEN
     FIRST_ASSUM((fun th -> MAP_EVERY EXISTS_TAC (let args = snd(strip_comb(concl th)) in
        [hd args; el 1 args; el 2 args; el 3 args; el 4 args; el 5 args; el 6 args;
         el 7 args; el 8 args])) o
       check (fun th -> (try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel"
                         with Failure _ -> false) &&
                        not (can (find_term (fun t -> is_const t &&
                          fst(dest_const t) = "data_RefPtr")) (concl th)))) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `b:byte`] ASP1AUX_RefByte_shift_facts) THEN
   ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; MAP; ITLIST; WORD_ADD_0; wl_set_store_def; wl_mem_store_def;
     evaluate_MakeBytes; ASP1AUX_ushr_byte_len; ASP1AUX_shl_shift_mul; ASP1AUX_and_bytes_mask;
     ASP1AUX_RefByte_header; FLOOKUP_UPDATE; distinctness "store_name"; wl_get_store_def]) THEN
  (SUBGOAL_THEN `word_or (word_or (word_shl (word_add (word i) bytes_in_word)
                   ((dimindex(:A) - backend_common_word_shift(:A)) -
                    data_to_word_config_len_size c)) (word 7)) (word (4 * tag)) =
                 (make_byte_header c fl i:A word)` ASSUME_TAC THENL
    [EXPAND_TAC "tag" THEN MATCH_MP_TAC ASP1AUX_RefByte_header THEN FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `word_and (word i) (word_sub bytes_in_word (word 1)) =
                 (word (i MOD (dimindex(:A) DIV 8)):A word)` ASSUME_TAC THENL
    [MATCH_MP_TAC ASP1AUX_and_bytes_mask THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   REWRITE_TAC[WORD_OR_0; WORD_AND_NOT0] THEN ASM_REWRITE_TAC[]) THEN
  (MP_TAC(ISPEC `i:num` ASP1AUX_val_mod_bytes) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
   SUBGOAL_THEN `byte_aligned (word_add free (word_mul (word (byte_len (:A) i)) bytes_in_word):A word)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC byte_aligned_add THEN ASM_SIMP_TAC[data_to_word_assignProof_byte_aligned_bytes_in_word];
     ALL_TAC] THEN
   (fun (asl,w as g) ->
     let tm = find_term (fun t -> try let f,p = dest_comb t in
                fst(dest_const f) = "wl_evaluate" &&
                (let prog,_ = dest_pair p in
                 fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
              with Failure _ -> false) w in
     let s14 = snd(dest_pair(rand tm)) in
     MP_TAC(ISPECL [`1`; `4`; `11`; s14;
       `word_add free (word_mul (word (byte_len (:A) i)) bytes_in_word):A word`;
       `word_of_byte (word (val (b:byte))):A word`;
       `word (i MOD (dimindex(:A) DIV 8)):A word`; `word 0:A word`] evaluate_WriteLastBytes) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ; UPDATE_APPLY1];
     DISCH_TAC] THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th])) THEN
  (SUBGOAL_THEN `word_zx (word_of_byte (word (val (b:byte)):A word)) = b` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM word_zx] THEN MATCH_MP_TAC w2w_word_of_byte_w2w THEN
     FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_THM; UPDATE_EQ; o_THM] THEN
   REWRITE_TAC[ASSUME `val (word (i MOD (dimindex(:A) DIV 8)):A word) = i MOD (dimindex(:A) DIV 8)`;
               ASSUME `word_zx (word_of_byte (word (val (b:byte)):A word)) = b`] THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; MAP; ITLIST; WORD_ADD_0]) THEN
  (SUBGOAL_THEN `0 < byte_len (:A) i /\ 4 * byte_len (:A) i < dimword(:A) /\
                 byte_len (:A) i * (dimindex(:A) DIV 8) < dimword(:A) /\
                 byte_len (:A) i - 1 < dimword(:A)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `byte_len (:A) i < limit` THEN EXPAND_TAC "limit" THEN
     MP_TAC(ISPEC `i:num` MP4AUX_byte_len) THEN
     UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `word_sub (word_shl (word (byte_len (:A) i)) 2) (word 4) =
                 (word (4 * (byte_len (:A) i - 1)):A word)` (fun th -> REWRITE_TAC[th]) THENL
    [MATCH_MP_TAC ASP1AUX_shl2_sub4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[word_zx] o check (fun th ->
     can (find_term (fun t -> is_const t &&
       fst(dest_const t) = "data_to_word_memoryProof_store_list")) (concl th) &&
     not (is_forall (concl th)))) THEN
   DISCH_THEN(fun th -> MP_TAC(MATCH_MP ASP1AUX_RefByte_store_list
     (CONJ th (CONJ (ASSUME `0 < byte_len (:A) i`)
       (CONJ (ASSUME `byte_len (:A) i * (dimindex(:A) DIV 8) < dimword(:A)`)
             (ASSUME `good_dimindex(:A)`)))))) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `lookup 0 (wl_state_locals (ra:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2) /\
                 wl_state_clock ra = MustTerminate_limit (:A) - 1 /\
                 lookup Replicate_location (wl_state_code ra) = SOME (5,Replicate_code)`
     STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s9:(C,FFI)data_state)
                      (ra:(A,C,FFI)wl_state) NONE locs` THEN
       REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
       UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s9:(C,FFI)data_state)
                      (ra:(A,C,FFI)wl_state) NONE locs` THEN
       UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                      (t:(A,C,FFI)wl_state) NONE locs` THEN
       UNDISCH_TAC `wl_state_clock (t:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 1` THEN
       EXPAND_TAC "s9" THEN
       REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds; K_THM] THEN
       MESON_TAC[];
       FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP lookup_RefByte_location th]) o
         check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2
                  (s9:(C,FFI)data_state) (ra:(A,C,FFI)wl_state) NONE locs`))];
     ALL_TAC]) THEN
  ((fun (asl,w as g) ->
     let tm = find_term (fun t -> try let f,p = dest_comb t in
                fst(dest_const f) = "wl_evaluate" &&
                (let prog,_ = dest_pair p in
                 fst(dest_const(fst(strip_comb prog))) = "wl_Call")
              with Failure _ -> false) w in
     let s15 = snd(dest_pair(rand tm)) in
     MP_TAC(ISPECL [`byte_len (:A) i - 1`; `free:A word`; s15; `m1:A word->A word_loc`;
       `0`; `9`; `4`; `7`; `3`; `wl_Word (word_of_byte (word (val (b:byte)))):A word_loc`;
       `l1:num`; `l2:num`;
       `wl_Word (word_or (word_shl (word_sub free curr)
          (shift_length c - backend_common_word_shift(:A))) (word 1)):A word_loc`]
       data_to_word_bignumProof_Replicate_code_thm) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_get_var_def; lookup_insert; ARITH_EQ] THEN CONJ_TAC THENL
      [UNDISCH_TAC `lookup Replicate_location (wl_state_code (ra:(A,C,FFI)wl_state)) =
                    SOME (5,Replicate_code)` THEN
       ASM_REWRITE_TAC[];
       UNDISCH_TAC `4 * byte_len (:A) i < dimword(:A)` THEN ARITH_TAC];
     ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `mx:num option` STRIP_ASSUME_TAC) THEN
   (fun (asl,w as g) ->
     let th = find (fun th -> try let l = lhs(concl th) in
                 fst(dest_const(fst(strip_comb l))) = "wl_evaluate" &&
                 (let prog,_ = dest_pair (rand l) in
                  fst(dest_const(fst(strip_comb prog))) = "wl_Call")
               with Failure _ -> false) (map snd asl) in
     let q, rf = dest_pair (rhs (concl th)) in
     let rv = hd(dest_list(rand(rand q))) in
     (EXISTS_TAC q THEN EXISTS_TAC rf THEN
      EXISTS_TAC (mk_comb(`wl_state_clock:(A,C,FFI)wl_state->num`, rf)) THEN
      REWRITE_TAC[th; option_INJ; distinctness "wl_result"] THEN
      EXISTS_TAC rv THEN REWRITE_TAC[]) g)) THEN
  ((fun (asl,w as g) ->
     let args = snd(strip_comb w) in
     let sx = el 3 args and rf = el 4 args in
     MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `r1:num`; `r2:num`;
       `s9:(C,FFI)data_state`; `ra:(A,C,FFI)wl_state`; rf; sx; `locs:(num#num)list`;
       `minimal ptr. ~(ptr IN domain (data_state_refs (s:(C,FFI)data_state)))`;
       `fl:bool`; `i:num`; `b:byte`; `free:A word`; `curr:A word`;
       `m1:A word->A word_loc`; `mx:num option`; `ss:num option`; `e:(data_v)spt`;
       `xs:(stack)list`] ASP1AUX_RefByte_state_rel) g) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
      [EXPAND_TAC "s9" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
       FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     CONJ_TAC THENL
      [EXPAND_TAC "s9" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
     CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_stack_max_le o
       check (fun th -> try let l = lhs(concl th) in
                 fst(dest_const(fst(strip_comb l))) = "wl_evaluate" &&
                 (let prog,_ = dest_pair (rand l) in
                  fst(dest_const(fst(strip_comb prog))) = "wl_Call")
               with Failure _ -> false)) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM]) THEN
     EXPAND_TAC "s9" THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[stack_consumed_def];
     REWRITE_TAC[]]));;

(* HOL4 line 1236 *)
let size_of_seen_SUBSET = prove
 (`!lims vs refs seen n1 seen1 refs1.
     (size_of lims vs refs seen = (n1,refs1,seen1)) ==> domain seen SUBSET domain seen1`,
  MATCH_MP_TAC size_of_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[size_of_def; PAIR_EQ] THEN MESON_TAC[SUBSET_REFL];
    STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_def] THEN
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    REWRITE_TAC[size_of_def; PAIR_EQ] THEN MESON_TAC[SUBSET_REFL];
    REWRITE_TAC[size_of_def; PAIR_EQ] THEN MESON_TAC[SUBSET_REFL];
    REWRITE_TAC[size_of_def; PAIR_EQ] THEN MESON_TAC[SUBSET_REFL];
    STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN ASM_MESON_TAC[SUBSET_REFL];
    REWRITE_TAC[size_of_def; PAIR_EQ] THEN MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[size_of_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `seen':(1)spt`; `refs':((data_v)bvl_ref)spt`]) THEN
    ASM_REWRITE_TAC[domain_insert] THEN SET_TAC[]]);;

(* HOL4 line 1250 *)
let size_of_seen_Block = prove
 (`!lims vs refs seen n1 refs1 seen1 ts tag l.
     size_of lims vs refs seen = (n1,refs1,seen1) ==>
     (MEM (data_Block ts tag l) vs /\ ~(l = []) ==> lookup ts seen1 = SOME one)`,
  SUBGOAL_THEN `!seen1 ts. ts IN domain (seen1:1 spt) ==> lookup ts seen1 = SOME one`
    ASSUME_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN MESON_TAC[one]; ALL_TAC] THEN
  MATCH_MP_TAC size_of_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[MEM];
    STRIP_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_def] THEN
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[] THEN
    SUBGOAL_THEN `domain (seen1':1 spt) SUBSET domain (seen1:1 spt)` MP_TAC THENL
     [ASM_MESON_TAC[size_of_seen_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`ts:num`; `tag:num`; `l:data_v list`])) THEN
    DISCH_THEN(LABEL_TAC "ih1") THEN DISCH_THEN(LABEL_TAC "ih2") THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
     [USE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!seen1 ts. ts IN domain (seen1:1 spt) ==>
                                      lookup ts seen1 = SOME one`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[domain_lookup] THEN
      EXISTS_TAC `one` THEN USE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!seen1 ts. ts IN domain (seen1:1 spt) ==>
                                      lookup ts seen1 = SOME one`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[domain_lookup] THEN
      EXISTS_TAC `one` THEN USE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[MEM; distinctness "data_v"];
    REWRITE_TAC[MEM; distinctness "data_v"];
    REWRITE_TAC[MEM; distinctness "data_v"];
    REWRITE_TAC[MEM; distinctness "data_v"];
    REWRITE_TAC[MEM; injectivity "data_v"] THEN MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[MEM; injectivity "data_v"] THEN DISCH_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
    REPEAT VAR_EQ_TAC THEN
    UNDISCH_TAC `size_of lims [data_Block ts tag (CONS v16 v17)] refs seen =
                 n1,refs1,seen1` THEN
    REWRITE_TAC[size_of_def] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN VAR_EQ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[domain_lookup] THEN
      ASM_MESON_TAC[IS_SOME_EXISTS];
      ALL_TAC] THEN
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT VAR_EQ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPECL [`lims:limits`; `CONS (v16:data_v) v17`; `refs:((data_v)bvl_ref)spt`;
                  `insert ts one (seen:1 spt)`; `n:num`; `seen1:1 spt`;
                  `refs1:((data_v)bvl_ref)spt`] size_of_seen_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET; domain_insert; IN_INSERT] THEN MESON_TAC[]]);;

(* HOL4 line 1272 *)
let size_of_cons_seen_Block = prove
 (`!lims vs refs seen ts tag l.
     MEM (data_Block ts tag l) vs ==>
     size_of lims (CONS (data_Block ts tag l) vs) refs seen = size_of lims vs refs seen`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `size_of lims (CONS (h:data_v) t) refs seen` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `rs:((data_v)bvl_ref)spt#(1)spt`
    MP_TAC)) THEN
  MP_TAC(ISPEC `rs:((data_v)bvl_ref)spt#(1)spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `seen1:1 spt`
    SUBST1_TAC)) THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[size_of_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `a:data_v` (X_CHOOSE_THEN `b:data_v list` SUBST_ALL_TAC))
    (ISPEC `l:data_v list` list_CASES) THENL
   [REWRITE_TAC[size_of_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[size_of_def] THEN
  SUBGOAL_THEN `lookup ts (seen1:1 spt) = SOME one` (fun th -> REWRITE_TAC[th; IS_SOME_DEF]) THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] size_of_seen_Block) THEN
    MAP_EVERY EXISTS_TAC [`lims:limits`; `CONS (h:data_v) t`; `refs:((data_v)bvl_ref)spt`;
      `seen:1 spt`; `n1:num`; `refs1:((data_v)bvl_ref)spt`; `tag:num`;
      `CONS (a:data_v) b`] THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; MEM];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES]]);;

(* HOL4 line 1286 *)
let state_rel_IMP_test_zero = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) vs locs i n.
     data_to_word_gcProof_state_rel c l1 l2 s t vs locs /\
     data_get_var i (data_state_locals s) = SOME (data_Number n) ==>
     ?w. wl_get_var (adjust_var i) t = SOME (wl_Word w) /\ (w = word 0 <=> (n = &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `data_get_var i (data_state_locals (s:(C,FFI)data_state)) =
             SOME (data_Number n)`) o MATCH_MP state_rel_get_var_IMP) THEN
  DISCH_THEN(X_CHOOSE_TAC `w1:A word_loc`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel_drop) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def; wl_get_var_def]) THEN
  DRULE_ALL memory_rel_lookup THEN DISCH_TAC THEN
  SUBGOAL_THEN `small_int (:A) (&0)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[small_int_def; good_dimindex_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP IMP_memory_rel_Number o
    CONJ (ASSUME `good_dimindex(:A)`) o CONJ (ASSUME `small_int (:A) (&0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_Number_EQ o
    C CONJ (CONJ (DISJ1 (ASSUME `small_int (:A) (&0)`) `small_int (:A) n`)
                 (ASSUME `good_dimindex(:A)`))) THEN
  STRIP_TAC THEN
  EXISTS_TAC `v2:A word` THEN ASM_REWRITE_TAC[wl_get_var_def] THEN
  UNDISCH_TAC `wl_Word (Smallnum (&0)) = wl_Word (v1:A word)` THEN
  REWRITE_TAC[injectivity "word_loc"; data_to_word_Smallnum_def] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[]);;

(* HOL4 line 1311 (the vacuous existential w is left out) *)
let state_rel_get_var_Number_IMP = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) vs locs i n.
     data_to_word_gcProof_state_rel c l1 l2 s t vs locs /\
     data_get_var i (data_state_locals s) = SOME (data_Number (&n)) /\
     small_int (:A) (&n) ==>
     wl_get_var (adjust_var i) t = SOME (wl_Word (Smallnum (&n):A word))`,
  MATCH_ACCEPT_TAC ASP1AUX_state_rel_get_var_Number);;

(* HOL4 line 1335 *)
let EXP_LEMMA1 = prove
 (`!n k. 4 * n * (2 EXP k) = n * 2 EXP (k + 2)`,
  REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_AC]);;

(* HOL4 line 1341 *)
let evaluate_Maxout_bits_code = prove
 (`!n_reg dest n rep_len k (t:(A,C,FFI)wl_state) w.
     ~(n_reg = dest) /\ n < dimword (:A) /\ rep_len < dimindex (:A) /\
     k < dimindex (:A) /\
     lookup n_reg (wl_state_locals t) = SOME (wl_Word (word n:A word)) ==>
     wl_evaluate (Maxout_bits_code rep_len k dest n_reg,wl_set_var dest (wl_Word w) t) =
       (NONE,wl_set_var dest (wl_Word (word_or w (maxout_bits n rep_len k))) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k < dimword(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_TRANS; dimindex_lt_dimword]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP rep_len < dimword(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[dimword_def; LT_EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_ult (word n:A word) (word (2 EXP rep_len - 1)) <=>
                n < 2 EXP rep_len - 1` ASSUME_TAC THENL
   [REWRITE_TAC[word_ult; relational2; VAL_WORD] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
    BINOP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k >= dimindex(:A))` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_Maxout_bits_code_def; maxout_bits_def] THEN
  SIMP[wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_imm_def;
       wl_word_cmp_def; lookup_insert; MAP; the_words_def; ITLIST; WORD_OR_0] THEN
  COND_CASES_TAC THEN SIMP[insert_shadow]);;

(* HOL4 line 1358 (the unused existential t1 is left out) *)
let data_to_word_assignProof_Make_ptr_bits_thm = prove
 (`!tag_reg dest tag1 c len_reg len1 (t:(A,C,FFI)wl_state) f d.
     ~(tag_reg = dest) /\ tag1 < dimword (:A) /\
     data_to_word_config_tag_bits c < dimindex (:A) /\
     ~(len_reg = dest) /\ len1 < dimword (:A) /\
     data_to_word_config_len_bits c < dimindex (:A) /\
     data_to_word_config_len_bits c + 1 < dimindex (:A) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word f) /\
     FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word d) /\
     lookup tag_reg (wl_state_locals t) = SOME (wl_Word (word tag1)) /\
     lookup len_reg (wl_state_locals t) = SOME (wl_Word (word len1)) /\
     shift_length c < dimindex (:A) + backend_common_word_shift (:A) ==>
     wl_evaluate (Make_ptr_bits_code c tag_reg len_reg dest,t) =
       (NONE,wl_set_var dest (make_cons_ptr c (word_sub f d) tag1 len1:A word_loc) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sh = shift_length c - backend_common_word_shift (:A)` THEN
  SUBGOAL_THEN `sh < dimindex(:A)` ASSUME_TAC THENL
   [EXPAND_TAC "sh" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sh < dimword(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_TRANS; dimindex_lt_dimword]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sh >= dimindex(:A))` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_Make_ptr_bits_code_def; data_to_word_list_Seq_def] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[wl_evaluate_def; word_exp_rw; MAP; the_words_def; ITLIST; WORD_OR_0;
       wl_get_store_def] THEN
  MP_TAC(ISPECL [`tag_reg:num`; `dest:num`; `tag1:num`;
                 `data_to_word_config_tag_bits c`; `1 + data_to_word_config_len_bits c`;
                 `t:(A,C,FFI)wl_state`;
                 `word_or (word 1) (word_shl (word_sub f d) sh):A word`]
                evaluate_Maxout_bits_code) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`len_reg:num`; `dest:num`; `len1:num`;
                 `data_to_word_config_len_bits c`; `1`; `t:(A,C,FFI)wl_state`;
                 `word_or (word_or (word 1) (word_shl (word_sub f d) sh))
                    (maxout_bits tag1 (data_to_word_config_tag_bits c)
                       (1 + data_to_word_config_len_bits c)):A word`]
                evaluate_Maxout_bits_code) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[make_cons_ptr_thm; ptr_bits_def; PAIR_EQ] THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR] THEN MESON_TAC[]);;

(* HOL4 line 1387: val get_var_get_real_addr_lemma (get_real_addr_lemma of  *)
(* bignumProof with its get_var conjunct moved to the front, GEN_ALL)       *)
let get_var_get_real_addr_lemma = prove
 (`!c v (t:(A,C,FFI)wl_state) ptr_w x.
     wl_get_var v t = SOME (wl_Word ptr_w) /\
     shift_length c < dimindex (:A) /\
     good_dimindex (:A) /\
     get_real_addr c (wl_state_store t) ptr_w = SOME x ==>
     wl_word_exp t (real_addr c v) = SOME (wl_Word (x:A word))`,
  MESON_TAC[get_real_addr_lemma]);;

(* HOL4 line 1393 *)
let evaluate_LoadWord64 = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) w v vars src dest.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (data_Word64 w,v) vars) /\
     shift_length c < dimindex(:A) /\ dimindex(:A) = 64 /\
     wl_get_var src t = SOME v ==>
     wl_evaluate (LoadWord64 c dest src,t) =
       (NONE,wl_set_var dest (wl_Word (word_zx w)) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_Word64_IMP o
    C CONJ (ASSUME `good_dimindex(:A)`)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(64 < 64)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `x:A word`
    (X_CHOOSE_THEN `hw:A word` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c src) = SOME (wl_Word x)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC get_var_get_real_addr_lemma THEN
    EXISTS_TAC `get_addr c ptr (wl_Word (word 0:A word))` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_extract 63 0 (w:int64) = (word_zx w:A word)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_ZX] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `i <= 63` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LoadWord64_def] THEN
  SIMP[wl_evaluate_def; word_exp_rw; wl_mem_load_def; MAP; the_words_def; ITLIST;
       WORD_ADD_0]);;

let ASP1AUX_store_list_2 = prove
 (`!(a:A word) x y m dm m1.
     data_to_word_memoryProof_store_list a [x; y] m dm = SOME m1 <=>
     a IN dm /\ word_add a bytes_in_word IN dm /\
     m1 = ((word_add a bytes_in_word =+ y) ((a =+ x) m))`,
  REWRITE_TAC[data_to_word_memoryProof_store_list_def] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let ASP1AUX_store_list_3 = prove
 (`!(a:A word) x y z m dm m1.
     data_to_word_memoryProof_store_list a [x; y; z] m dm = SOME m1 <=>
     a IN dm /\ word_add a bytes_in_word IN dm /\
     word_add a (word_mul (word 2) bytes_in_word) IN dm /\
     m1 = ((word_add a (word_mul (word 2) bytes_in_word) =+ z)
             ((word_add a bytes_in_word =+ y) ((a =+ x) m)))`,
  REWRITE_TAC[data_to_word_memoryProof_store_list_def;
              WORD_RULE `word_add (word_add (a:A word) b) b = word_add a (word_mul (word 2) b)`] THEN
  REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let ASP1AUX_bytes_in_word_NOT_0 = prove
 (`!ne:A word. good_dimindex (:A) ==>
     ~(word_add ne bytes_in_word = ne) /\
     ~(word_add ne (word_mul (word 2) bytes_in_word) = ne) /\
     ~(word_add ne (word_mul (word 2) bytes_in_word) = word_add ne bytes_in_word)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (a:A word) b = a <=> b = word 0`;
              WORD_RULE `word_add (a:A word) b = word_add a c <=> b = c`] THEN
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM WORD_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASP1AUX_eval_write1 = prove
 (`!c header dest i (t:(A,C,FFI)wl_state) ne curr w m1.
     good_dimindex (:A) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word ne) /\
     FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word curr) /\
     wl_get_var i t = SOME (wl_Word w) /\ ~(i = 1) /\
     shift_length c - backend_common_word_shift(:A) < dimindex(:A) /\
     data_to_word_memoryProof_store_list ne [wl_Word header; wl_Word w]
       (wl_state_memory t) (wl_state_mdomain t) = SOME m1 ==>
     wl_evaluate (data_to_word_list_Seq
       [wl_Assign 1 (Lookup NextFree);
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]) i;
        wl_Assign 3 (wl_Const header); wl_Store (wl_Var 1) 3;
        wl_Set NextFree
          (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 2) bytes_in_word)]);
        wl_Assign (adjust_var dest)
          (wl_Op asm_Or
            [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
               (wl_Const (word (shift_length c - backend_common_word_shift (:A))));
             wl_Const (word 1)])], t) =
     (NONE, wl_state_store_fupd (K (wl_state_store t |+
               (NextFree, wl_Word (word_add ne (word_mul (word 2) bytes_in_word)))))
              (wl_state_memory_fupd (K m1)
                (wl_state_locals_fupd
                  (K (insert (adjust_var dest)
                        (make_ptr c (word_sub ne curr) (word 0:A word) 1)
                       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
                          (wl_state_locals t))))) t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP1AUX_store_list_2] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `ne:A word` o MATCH_MP
    (MESON[ASP1AUX_bytes_in_word_NOT_0]
      `good_dimindex(:A) ==> !ne:A word. ~(word_add ne bytes_in_word = ne)`)) THEN
  SUBGOAL_THEN `shift_length c - backend_common_word_shift(:A) < dimword(:A)` ASSUME_TAC
  THENL [ASM_MESON_TAC[LT_TRANS; dimindex_lt_dimword]; ALL_TAC] THEN
  SUBGOAL_THEN `~(shift_length c - backend_common_word_shift(:A) >= dimindex(:A))`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_mem_store_def; MAP; the_words_def;
    ITLIST; WORD_ADD_0; WORD_OR_0; wl_set_var_def; wl_get_var_def; lookup_insert;
    wl_set_store_def; FLOOKUP_UPDATE] THEN
  SIMP[wl_evaluate_def; word_exp_rw; MAP; the_words_def; ITLIST;
       WORD_ADD_0; WORD_OR_0; wl_set_var_def; wl_get_var_def; lookup_insert;
       wl_get_store_def; FLOOKUP_UPDATE; make_ptr_def] THEN
  ASM_SIMP_TAC[UPDATE_COMMUTES]);;

let ASP1AUX_eval_write2 = prove
 (`!c header dest i1 i2 (t:(A,C,FFI)wl_state) ne curr w1 w2 m1.
     good_dimindex (:A) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word ne) /\
     FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word curr) /\
     wl_get_var i1 t = SOME (wl_Word w1) /\ ~(i1 = 1) /\
     wl_get_var i2 t = SOME (wl_Word w2) /\ ~(i2 = 1) /\
     shift_length c - backend_common_word_shift(:A) < dimindex(:A) /\
     data_to_word_memoryProof_store_list ne [wl_Word header; wl_Word w2; wl_Word w1]
       (wl_state_memory t) (wl_state_mdomain t) = SOME m1 ==>
     wl_evaluate (data_to_word_list_Seq
       [wl_Assign 1 (Lookup NextFree);
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word]) i2;
        wl_Store (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 2) bytes_in_word)]) i1;
        wl_Assign 3 (wl_Const header); wl_Store (wl_Var 1) 3;
        wl_Set NextFree
          (wl_Op asm_Add [wl_Var 1; wl_Const (word_mul (word 3) bytes_in_word)]);
        wl_Assign (adjust_var dest)
          (wl_Op asm_Or
            [wl_Shift Lsl (wl_Op asm_Sub [wl_Var 1; Lookup CurrHeap])
               (wl_Const (word (shift_length c - backend_common_word_shift (:A))));
             wl_Const (word 1)])], t) =
     (NONE, wl_state_store_fupd (K (wl_state_store t |+
               (NextFree, wl_Word (word_add ne (word_mul (word 3) bytes_in_word)))))
              (wl_state_memory_fupd (K m1)
                (wl_state_locals_fupd
                  (K (insert (adjust_var dest)
                        (make_ptr c (word_sub ne curr) (word 0:A word) 2)
                       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
                          (wl_state_locals t))))) t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP1AUX_store_list_3] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `ne:A word` o MATCH_MP
    (MESON[ASP1AUX_bytes_in_word_NOT_0]
      `good_dimindex(:A) ==> !ne:A word.
         ~(word_add ne bytes_in_word = ne) /\
         ~(word_add ne (word_mul (word 2) bytes_in_word) = ne) /\
         ~(word_add ne (word_mul (word 2) bytes_in_word) = word_add ne bytes_in_word)`)) THEN
  SUBGOAL_THEN `shift_length c - backend_common_word_shift(:A) < dimword(:A)` ASSUME_TAC
  THENL [ASM_MESON_TAC[LT_TRANS; dimindex_lt_dimword]; ALL_TAC] THEN
  SUBGOAL_THEN `~(shift_length c - backend_common_word_shift(:A) >= dimindex(:A))`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_mem_store_def; MAP; the_words_def;
    ITLIST; WORD_ADD_0; WORD_OR_0; wl_set_var_def; wl_get_var_def; lookup_insert;
    wl_set_store_def; FLOOKUP_UPDATE] THEN
  SIMP[wl_evaluate_def; word_exp_rw; MAP; the_words_def; ITLIST;
       WORD_ADD_0; WORD_OR_0; wl_set_var_def; wl_get_var_def; lookup_insert;
       wl_get_store_def; FLOOKUP_UPDATE; make_ptr_def]  THEN
  ASM_SIMP_TAC[UPDATE_COMMUTES]);;

let ASP1AUX_write_post = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm x ptr sl (locals:(A word_loc)spt)
    vars dest v3 v1.
     memory_rel c be ts refs sp st m dm
       (CONS (x,ptr) (APPEND (join_env_locals sl locals) vars)) /\
     (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) locals)) ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (join_env_locals (insert dest x sl)
                  (insert (adjust_var dest) ptr (insert 3 v3 (insert 1 v1 locals)))) vars) /\
     (!n. IS_SOME (lookup n sl) ==>
          IS_SOME (lookup (adjust_var n)
            (insert (adjust_var dest) ptr (insert 3 v3 (insert 1 v1 locals))))) /\
     IS_SOME (lookup (adjust_var dest)
       (insert (adjust_var dest) ptr (insert 3 v3 (insert 1 v1 locals)))) /\
     lookup 0 (insert (adjust_var dest) ptr (insert 3 v3 (insert 1 v1 locals))) =
       lookup 0 locals`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. ~(0 = adjust_var n) /\ ~(1 = adjust_var n) /\ ~(3 = adjust_var n)`
    ASSUME_TAC THENL [MESON_TAC[adjust_var_NEQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ; IS_SOME_DEF; ARITH_EQ] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
    ASM_MESON_TAC[]] THEN
  REWRITE_TAC[join_env_locals_def] THEN
  SIMP_TAC[inter_insert_ODD_adjust_set; ARITH] THEN
  MATCH_MP_TAC memory_rel_insert THEN
  UNDISCH_TAC `memory_rel c be ts refs sp st (m:A word->A word_loc) dm
       (CONS (x,ptr) (APPEND (join_env_locals sl locals) vars))` THEN
  REWRITE_TAC[join_env_locals_def; APPEND]);;
let ASP1AUX_Bignum_val = prove
 (`!w:A word. good_dimindex (:A) /\ ~small_int (:A) (&(val w)) ==>
              Bignum (&(val w)) = DataElement [] 1 (NumTag F, MAP wl_Word [w])`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val (w:A word) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~small_int (:A) (&(val (w:A word)))` THEN
    ASM_REWRITE_TAC[small_int_def] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_memoryProof_Bignum_def; i2mw_def] THEN
  REWRITE_TAC[INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_LT; GSYM INT_OF_NUM_LT; LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[INT_POS] THEN
  SUBGOAL_THEN `n2mw (val (w:A word)) = [w]` SUBST1_TAC THENL
   [SUBGOAL_THEN `val (w:A word) < dimword(:A)` ASSUME_TAC THENL
     [REWRITE_TAC[dimword_def; VAL_BOUND]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[n2mw_def] THEN ASM_SIMP_TAC[MOD_LT; DIV_LT] THEN
    ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[WORD_VAL];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* HOL4 line 1413 (the unused existential v is left out) *)
let evaluate_WriteWord64 = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) sl vars src w header dest.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (APPEND (join_env_locals sl (wl_state_locals t)) vars) /\
     wl_get_var src t = SOME (wl_Word w) /\
     shift_length c < dimindex(:A) /\
     ~(src = 1) /\ 1 < sp /\
     dimindex(:A) = 64 /\
     encode_header c 3 1 = SOME header /\
     (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) (wl_state_locals t))) ==>
     ?nf m' locals'.
       wl_evaluate (WriteWord64 c header dest src,t) =
         (NONE,wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
                 (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) /\
       memory_rel c be ts refs (sp - 2) (wl_state_store t |+ (NextFree,nf)) m'
         (wl_state_mdomain t)
         (APPEND (join_env_locals (insert dest (data_Word64 (word_zx w)) sl) locals') vars) /\
       (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) locals')) /\
       IS_SOME (lookup (adjust_var dest) locals') /\
       lookup 0 locals' = lookup 0 (wl_state_locals t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:((data_v)bvl_ref)spt`;
    `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `[]:(data_v#(A)word_loc)list`;
    `APPEND (join_env_locals (sl:data_v spt) (wl_state_locals (t:(A,C,FFI)wl_state)))
       (vars:(data_v#(A)word_loc)list)`;
    `word_zx (w:A word):int64`; `[wl_Word (w:A word)]`; `header:A word`]
    memory_rel_Word64_alt) THEN
  ASM_REWRITE_TAC[APPEND; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[Word64Rep_def; ARITH_RULE `~(64 < 64)`] THEN
    REWRITE_TAC[injectivity "heap_element"; CONS_11; PAIR_EQ; injectivity "word_loc"] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_ZX; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `i <= 63` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `header:A word`; `dest:num`; `src:num`;
    `t:(A,C,FFI)wl_state`; `ne:A word`; `curr:A word`; `w:A word`;
    `m1:A word->A word_loc`] ASP1AUX_eval_write1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WriteWord64_def] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`wl_Word (word_add ne (word_mul (word 2) bytes_in_word)):A word_loc`;
    `m1:A word->A word_loc`;
    `insert (adjust_var dest) (make_ptr c (word_sub ne curr) (word 0:A word) 1)
       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
          (wl_state_locals (t:(A,C,FFI)wl_state))))`] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC ASP1AUX_write_post THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     can (find_term ((=) `data_Word64`)) (concl th))) THEN
  REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[]);;

(* HOL4 line 1469 (the unused existential v is left out) *)
let evaluate_WriteWord64_on_32 = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) sl vars src1 src2 (w:int64) header dest.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (APPEND (join_env_locals sl (wl_state_locals t)) vars) /\
     wl_get_var src1 t = SOME (wl_Word (word_extract 31 0 w)) /\
     wl_get_var src2 t = SOME (wl_Word (word_extract 63 32 w)) /\
     shift_length c < dimindex(:A) /\
     ~(src1 = 1) /\ ~(src2 = 1) /\ 2 < sp /\
     dimindex(:A) = 32 /\
     encode_header c 3 2 = SOME header /\
     (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) (wl_state_locals t))) ==>
     ?nf m' locals'.
       wl_evaluate (WriteWord64_on_32 c header dest src1 src2,t) =
         (NONE,wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
                 (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) /\
       memory_rel c be ts refs (sp - 3) (wl_state_store t |+ (NextFree,nf)) m'
         (wl_state_mdomain t)
         (APPEND (join_env_locals (insert dest (data_Word64 w) sl) locals') vars) /\
       (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) locals')) /\
       IS_SOME (lookup (adjust_var dest) locals') /\
       lookup 0 locals' = lookup 0 (wl_state_locals t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:((data_v)bvl_ref)spt`;
    `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `[]:(data_v#(A)word_loc)list`;
    `APPEND (join_env_locals (sl:data_v spt) (wl_state_locals (t:(A,C,FFI)wl_state)))
       (vars:(data_v#(A)word_loc)list)`;
    `w:int64`;
    `[wl_Word (word_extract 63 32 (w:int64):A word); wl_Word (word_extract 31 0 w)]`;
    `header:A word`]
    memory_rel_Word64_alt) THEN
  ASM_REWRITE_TAC[APPEND; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[Word64Rep_def] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `header:A word`; `dest:num`; `src1:num`;
    `src2:num`; `t:(A,C,FFI)wl_state`; `ne:A word`; `curr:A word`;
    `word_extract 31 0 (w:int64):A word`; `word_extract 63 32 (w:int64):A word`;
    `m1:A word->A word_loc`] ASP1AUX_eval_write2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WriteWord64_on_32_def] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`wl_Word (word_add ne (word_mul (word 3) bytes_in_word)):A word_loc`;
    `m1:A word->A word_loc`;
    `insert (adjust_var dest) (make_ptr c (word_sub ne curr) (word 0:A word) 2)
       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
          (wl_state_locals (t:(A,C,FFI)wl_state))))`] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC ASP1AUX_write_post THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     can (find_term ((=) `data_Word64`)) (concl th))) THEN
  REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[]);;

(* HOL4 line 1532 (local) *)
let Num_ABS_AND = prove
 (`!n. num_of_int (abs (&n)) = n /\ num_of_int (abs (-- &n)) = n`,
  REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM]);;

(* HOL4 line 1538 (the unused existential v is left out) *)
let evaluate_WriteWord64_on_32_num = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) sl vars src1 src2 (w1:A word) w2 header dest.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (APPEND (join_env_locals sl (wl_state_locals t)) vars) /\
     wl_get_var src1 t = SOME (wl_Word w1) /\
     wl_get_var src2 t = SOME (wl_Word w2) /\
     shift_length c < dimindex(:A) /\ ~(w2 = word 0) /\
     ~(src1 = 1) /\ ~(src2 = 1) /\ 2 < sp /\
     dimindex(:A) = 32 /\
     encode_header c 3 2 = SOME header /\
     (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) (wl_state_locals t))) ==>
     ?nf m' locals'.
       wl_evaluate (WriteWord64_on_32 c header dest src2 src1,t) =
         (NONE,wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
                 (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) /\
       memory_rel c be ts refs (sp - 3) (wl_state_store t |+ (NextFree,nf)) m'
         (wl_state_mdomain t)
         (APPEND (join_env_locals
                    (insert dest (data_Number (&(val w2 * dimword (:A) + val w1))) sl)
                    locals') vars) /\
       (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) locals')) /\
       IS_SOME (lookup (adjust_var dest) locals') /\
       lookup 0 locals' = lookup 0 (wl_state_locals t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < val (w2:A word)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; VAL_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `val (w1:A word) < dimword(:A) /\ val (w2:A word) < dimword(:A)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[dimword_def; VAL_BOUND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:((data_v)bvl_ref)spt`;
    `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `APPEND (join_env_locals (sl:data_v spt) (wl_state_locals (t:(A,C,FFI)wl_state)))
       (vars:(data_v#(A)word_loc)list)`;
    `&(val (w2:A word) * dimword (:A) + val (w1:A word)):int`;
    `[w1:A word; w2]`; `F`; `header:A word`]
    IMP_memory_rel_bignum_alt) THEN
  ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[small_int_def; DE_MORGAN_THM; INT_NOT_LT] THEN DISJ2_TAC THEN
      REWRITE_TAC[INT_OF_NUM_LE] THEN
      MATCH_MP_TAC(ARITH_RULE `d DIV 8 <= d /\ d <= a * d ==> d DIV 8 <= a * d + b`) THEN
      CONJ_TAC THENL [MESON_TAC[DIV_LE; ARITH_RULE `~(8 = 0)`]; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `d = 1 * d`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[data_to_word_memoryProof_Bignum_def; i2mw_def] THEN
      REWRITE_TAC[INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_LT; GSYM INT_OF_NUM_LT; LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[INT_POS] THEN
      SUBGOAL_THEN `n2mw (val (w2:A word) * dimword (:A) + val (w1:A word)) = [w1; w2]`
        SUBST1_TAC THENL
       [SUBGOAL_THEN `~(dimword(:A) = 0)` ASSUME_TAC THENL
         [REWRITE_TAC[dimword_def; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
        ONCE_REWRITE_TAC[n2mw_def] THEN
        ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES] THEN
        SUBGOAL_THEN `~(val (w2:A word) * dimword (:A) + val (w1:A word) = 0)`
          (fun th -> REWRITE_TAC[th]) THENL
         [REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[n2mw_def] THEN ASM_SIMP_TAC[MOD_LT; DIV_LT] THEN
        ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
        ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[WORD_VAL];
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV];
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[b2w_def; WORD_SHL_0; WORD_OR_0; VAL_WORD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `header:A word`; `dest:num`; `src2:num`;
    `src1:num`; `t:(A,C,FFI)wl_state`; `ne:A word`; `curr:A word`;
    `w2:A word`; `w1:A word`; `m1:A word->A word_loc`] ASP1AUX_eval_write2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WriteWord64_on_32_def] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`wl_Word (word_add ne (word_mul (word 3) bytes_in_word)):A word_loc`;
    `m1:A word->A word_loc`;
    `insert (adjust_var dest) (make_ptr c (word_sub ne curr) (word 0:A word) 2)
       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
          (wl_state_locals (t:(A,C,FFI)wl_state))))`] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC ASP1AUX_write_post THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     can (find_term ((=) `data_Number`)) (concl th))) THEN
  REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[]);;

(* HOL4 line 1614 (the unused existential v is left out) *)
let evaluate_WriteWord32_bignum = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) sl vars src (w:A word) header dest.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (APPEND (join_env_locals sl (wl_state_locals t)) vars) /\
     wl_get_var src t = SOME (wl_Word w) /\
     shift_length c < dimindex(:A) /\
     ~(src = 1) /\ 1 < sp /\
     dimindex(:A) = 32 /\
     encode_header c 3 1 = SOME header /\
     ~small_int (:A) (&(val w)) /\
     (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) (wl_state_locals t))) ==>
     ?nf m' locals'.
       wl_evaluate (WriteWord32_on_32 c header dest src,t) =
         (NONE,wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
                 (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) /\
       memory_rel c be ts refs (sp - 2) (wl_state_store t |+ (NextFree,nf)) m'
         (wl_state_mdomain t)
         (APPEND (join_env_locals (insert dest (data_Number (&(val w))) sl) locals') vars) /\
       (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) locals')) /\
       IS_SOME (lookup (adjust_var dest) locals') /\
       lookup 0 locals' = lookup 0 (wl_state_locals t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:((data_v)bvl_ref)spt`;
    `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `APPEND (join_env_locals (sl:data_v spt) (wl_state_locals (t:(A,C,FFI)wl_state)))
       (vars:(data_v#(A)word_loc)list)`;
    `&(val (w:A word)):int`; `[w:A word]`; `F`; `header:A word`]
    IMP_memory_rel_bignum_alt) THEN
  ASM_SIMP_TAC[LENGTH; ASP1AUX_Bignum_val] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[b2w_def; WORD_SHL_0; WORD_OR_0; VAL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `header:A word`; `dest:num`; `src:num`;
    `t:(A,C,FFI)wl_state`; `ne:A word`; `curr:A word`; `w:A word`;
    `m1:A word->A word_loc`] ASP1AUX_eval_write1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WriteWord32_on_32_def] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`wl_Word (word_add ne (word_mul (word 2) bytes_in_word)):A word_loc`;
    `m1:A word->A word_loc`;
    `insert (adjust_var dest) (make_ptr c (word_sub ne curr) (word 0:A word) 1)
       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
          (wl_state_locals (t:(A,C,FFI)wl_state))))`] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC ASP1AUX_write_post THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     can (find_term ((=) `data_Number`)) (concl th))) THEN
  REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[]);;

(* HOL4 line 1679 (the unused existential v is left out) *)
let evaluate_WriteWord64_bignum = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) sl vars src (w:A word) header dest.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (APPEND (join_env_locals sl (wl_state_locals t)) vars) /\
     wl_get_var src t = SOME (wl_Word w) /\
     shift_length c < dimindex(:A) /\
     ~(src = 1) /\ 1 < sp /\
     dimindex(:A) = 64 /\
     encode_header c 3 1 = SOME header /\
     ~small_int (:A) (&(val w)) /\
     (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) (wl_state_locals t))) ==>
     ?nf m' locals'.
       wl_evaluate (WriteWord64 c header dest src,t) =
         (NONE,wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
                 (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) /\
       memory_rel c be ts refs (sp - 2) (wl_state_store t |+ (NextFree,nf)) m'
         (wl_state_mdomain t)
         (APPEND (join_env_locals (insert dest (data_Number (&(val w))) sl) locals') vars) /\
       (!n. IS_SOME (lookup n sl) ==> IS_SOME (lookup (adjust_var n) locals')) /\
       IS_SOME (lookup (adjust_var dest) locals') /\
       lookup 0 locals' = lookup 0 (wl_state_locals t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:((data_v)bvl_ref)spt`;
    `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `APPEND (join_env_locals (sl:data_v spt) (wl_state_locals (t:(A,C,FFI)wl_state)))
       (vars:(data_v#(A)word_loc)list)`;
    `&(val (w:A word)):int`; `[w:A word]`; `F`; `header:A word`]
    IMP_memory_rel_bignum_alt) THEN
  ASM_SIMP_TAC[LENGTH; ASP1AUX_Bignum_val] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[b2w_def; WORD_SHL_0; WORD_OR_0; VAL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `header:A word`; `dest:num`; `src:num`;
    `t:(A,C,FFI)wl_state`; `ne:A word`; `curr:A word`; `w:A word`;
    `m1:A word->A word_loc`] ASP1AUX_eval_write1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WriteWord64_def] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`wl_Word (word_add ne (word_mul (word 2) bytes_in_word)):A word_loc`;
    `m1:A word->A word_loc`;
    `insert (adjust_var dest) (make_ptr c (word_sub ne curr) (word 0:A word) 1)
       (insert 3 (wl_Word header) (insert 1 (wl_Word ne)
          (wl_state_locals (t:(A,C,FFI)wl_state))))`] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC ASP1AUX_write_post THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     can (find_term ((=) `data_Number`)) (concl th))) THEN
  REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[]);;

(* HOL4 line 1744 *)
let evaluate_LoadBignum = prove
 (`!c be ts refs sp (t:(A,C,FFI)wl_state) i v vars src header w1.
     memory_rel c be ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (data_Number i,v) vars) /\
     ~small_int (:A) i /\ good_dimindex (:A) /\ shift_length c < dimindex (:A) /\
     wl_get_var src t = SOME v /\ ~(header = w1) ==>
     ?h junk.
       wl_evaluate (LoadBignum c header w1 src,t) =
         (NONE,wl_set_vars [w1;header;w1]
                 [wl_Word (word (num_of_int (abs i))); (wl_Word h); junk] t) /\
       (word_and (word 16) h = word 0 <=> &0 <= i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_bignum_IMP o
    C CONJ (CONJ (ASSUME `~small_int (:A) i`) (ASSUME `good_dimindex(:A)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `x:A word`
    (X_CHOOSE_THEN `a:A word` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c src) = SOME (wl_Word a)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC get_var_get_real_addr_lemma THEN
    EXISTS_TAC `w:A word` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:A word`; `wl_Word (a:A word)`] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[WORD_AND_SYM]] THEN
  REWRITE_TAC[LoadBignum_def; data_to_word_list_Seq_def] THEN
  SIMP[wl_evaluate_def; word_exp_rw; wl_mem_load_def; MAP; the_words_def; ITLIST;
       WORD_ADD_0; wl_set_var_def; wl_get_var_def; lookup_insert] THEN
  ASM_REWRITE_TAC[wl_set_vars_def; alist_insert_def]);;

(* HOL4 line 1765: val assign_thm_goal *)
let assign_thm_goal =
  `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state)
     NONE locs /\
   ~(op_requires_names op <=> (names_opt = NONE)) /\
   data_cut_state_opt names_opt s = SOME x /\
   data_get_vars args (data_state_locals s) = SOME vals /\
   wl_state_termdep t > 1 /\
   data_do_app op vals x = Rval (v,s2) ==>
   ?q r.
     wl_evaluate (FST (data_to_word_assign c n l dest op args names_opt),t) = (q,r) /\
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = wl_state_ffi t /\
      option_le (wl_state_stack_max r) (data_state_stack_max s2) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
       ~data_state_safe_for_space s2)) /\
     (~(q = SOME NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2) r NONE locs /\
      q = NONE)`;;

(* the statement of HOL4's Theorem assign_X: P ==> ^assign_thm_goal         *)
let assign_thm_stmt hyp =
  let tm = mk_imp(hyp,assign_thm_goal) in list_mk_forall(frees tm,tm);;

(* HOL4 line 1780: val evaluate_Assign (SIMP_CONV of evaluate_def on        *)
(* evaluate (Assign _ _,_)): a proof tool, not stated                        *)

(* HOL4 line 1783 *)
let data_to_word_assignProof_cut_names_adjust_set_insert_1 = prove
 (`!(x:B spt) (w:A) l.
     cut_names (adjust_set x) (insert 1 w l) = cut_names (adjust_set x) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; domain_insert] THEN
  SUBGOAL_THEN `domain (adjust_set (x:B spt)) SUBSET 1 INSERT domain (l:A spt) <=>
                domain (adjust_set x) SUBSET domain l` SUBST1_TAC THENL
   [MP_TAC(ISPEC `x:B spt` NOT_1_domain) THEN SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[inter_insert_ODD_adjust_set_alt; ODD; ARITH]);;

(* HOL4 line 1793 *)
let data_to_word_assignProof_cut_names_adjust_set_insert_3 = prove
 (`!(x:B spt) (w:A) l.
     cut_names (adjust_set x) (insert 3 w l) = cut_names (adjust_set x) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; domain_insert] THEN
  SUBGOAL_THEN `domain (adjust_set (x:B spt)) SUBSET 3 INSERT domain (l:A spt) <=>
                domain (adjust_set x) SUBSET domain l` SUBST1_TAC THENL
   [MP_TAC(ISPEC `x:B spt` NOT_3_domain) THEN SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[inter_insert_ODD_adjust_set_alt; ARITH]);;

(* HOL4 line 1803 *)
let cut_names_adjust_set_insert_5 = prove
 (`!(x:B spt) (w:A) l.
     cut_names (adjust_set x) (insert 5 w l) = cut_names (adjust_set x) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; domain_insert] THEN
  SUBGOAL_THEN `domain (adjust_set (x:B spt)) SUBSET 5 INSERT domain (l:A spt) <=>
                domain (adjust_set x) SUBSET domain l` SUBST1_TAC THENL
   [MP_TAC(ISPEC `x:B spt` NOT_5_domain) THEN SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[inter_insert_ODD_adjust_set_alt; ARITH]);;

(* HOL4 line 1813 *)
let word_bit_test_0 = prove
 (`!w:A word. word_and (word 1) w = word 0 <=> ~bit 0 w`,
  REWRITE_TAC[WORD_AND_1] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_1; BIT_WORD_0] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[DIMINDEX_GT_0]);;

(* HOL4 line 1819 (local) *)
let MAP_Number_11_w2n_word8 = prove
 (`!ns ns':byte list.
     MAP (data_Number o (&) o val) ns = MAP (data_Number o (&) o val) ns' <=> ns = ns'`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; o_THM; injectivity "data_v";
                  INT_OF_NUM_EQ; VAL_EQ]);;

(* HOL4 line 1827 (local) *)
let MAP_Word64_11 = prove
 (`!ns ns'. MAP data_Word64 ns = MAP data_Word64 ns' <=> ns = ns'`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; injectivity "data_v"]);;

(* HOL4 line 1835 *)
let v_to_list_EQ_SOME_NIL = prove
 (`!hv1. data_v_to_list hv1 = SOME [] <=> ?ts. hv1 = data_Block ts 0 []`,
  GEN_TAC THEN CASES_ON `hv1:data_v` THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT; distinctness "data_v";
              injectivity "data_v"] THEN
  STRUCT_CASES_TAC(ISPEC `a2:data_v list` list_CASES) THEN
  REWRITE_TAC[data_v_to_list_def; NOT_CONS_NIL; nil_tag_def] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:data_v list` list_CASES) THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t':data_v list` list_CASES) THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `data_v_to_list h'` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL]);;

let ASP1AUX_v_to_bytes = prove
 (`!hv (q:byte list). data_v_to_bytes hv = SOME q <=>
          data_v_to_list hv = SOME (MAP (data_Number o (&) o val) q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_v_to_bytes_def; some_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
    SPEC_TAC(`@ns:byte list. data_v_to_list hv = SOME (MAP (data_Number o (&) o val) ns)`,
             `ns:byte list`) THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[option_INJ; MAP_Number_11_w2n_word8] THEN MESON_TAC[];
    ASM_MESON_TAC[]]);;

let ASP1AUX_v_to_list_CONS = prove
 (`!hv x xs. data_v_to_list hv = SOME (CONS x xs) <=>
             ?ts bt. hv = data_Block ts cons_tag [x; bt] /\ data_v_to_list bt = SOME xs`,
  GEN_TAC THEN CASES_ON `hv:data_v` THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT; distinctness "data_v";
              injectivity "data_v"] THEN
  STRUCT_CASES_TAC(ISPEC `a2:data_v list` list_CASES) THEN
  REWRITE_TAC[data_v_to_list_def; NOT_CONS_NIL; CONS_11] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:data_v list` list_CASES) THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT; NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t':data_v list` list_CASES) THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT; NOT_CONS_NIL; CONS_11] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `data_v_to_list h'` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11] THEN
  SIMP[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let ASP1AUX_bad_fun_filter = prove
 (CASE_TERM `!(x:((A)wl_result)option # (A,C,FFI)wl_state).
     (match (match x with (r,s) -> if wl_bad_fun_return r then (SOME wl_Error,s) else (r,s)) with
        (r,s) -> if wl_bad_fun_return r then (SOME wl_Error,s) else (r,s)) =
     (match x with (r,s) -> if wl_bad_fun_return r then (SOME wl_Error,s) else (r,s))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[wl_bad_fun_return_def]);;

let ASP1AUX_InstallCode = prove
 (CASE_TERM
  `!q1 (t:(A,C,FFI)wl_state) c hv1 a1 a2 ret_val bptr vars sp refs ts.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (hv1,a1) vars) /\
     lookup InstallCode_location (wl_state_code t) = SOME (4,InstallCode_code c) /\
     lookup InstallData_location (wl_state_code t) = SOME (4,InstallData_code c) /\
     FLOOKUP (wl_state_store t) BitmapBuffer = SOME bptr /\
     data_v_to_bytes hv1 = SOME q1 /\
     LENGTH q1 <= buffer_space_left (wl_state_code_buffer t) /\
     LENGTH q1 < wl_state_clock t /\
     wl_get_var 0 t = SOME ret_val /\
     wl_get_var 2 t = SOME a1 /\
     wl_get_var 4 t = SOME a2 /\
     wl_get_var 6 t = SOME (wl_Word (word_add (buffer_position (wl_state_code_buffer t))
                              (word (LENGTH (buffer_buffer (wl_state_code_buffer t)))))) /\
     good_dimindex (:A) ==>
     ?lsz smx.
       wl_evaluate (InstallCode_code c,t) =
       match
         wl_evaluate (InstallData_code c,
           wl_state_locals_fupd
             (K (fromList2 [ret_val; bptr; a2;
                  wl_Word (word_add (buffer_position (wl_state_code_buffer t))
                    (word (LENGTH (buffer_buffer (wl_state_code_buffer t)) +
                           LENGTH q1)))]))
             (wl_state_locals_size_fupd (K lsz)
                (wl_state_clock_fupd (K ((wl_state_clock t - LENGTH q1) - 1))
                   (wl_state_code_buffer_fupd
                      (K (buffer_buffer_fupd
                            (K (APPEND (buffer_buffer (wl_state_code_buffer t)) q1))
                            (buffer_space_left_fupd
                               (K (buffer_space_left (wl_state_code_buffer t) -
                                   LENGTH q1))
                               (wl_state_code_buffer t))))
                      (wl_state_stack_max_fupd (K smx) t))))) with
         (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)`,
  (MATCH_MP_TAC list_INDUCT THEN CONJ_TAC) THENL
  [(REPEAT GEN_TAC THEN REWRITE_TAC[ASP1AUX_v_to_bytes; MAP; v_to_list_EQ_SOME_NIL] THEN
   STRIP_TAC THEN VAR_EQ_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
     C CONJ (ASSUME `good_dimindex(:A)`) o
     check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel"))
                          (concl th))) THEN
   REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:A word` STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[InstallCode_code_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
   REWRITE_TAC[ASSUME `wl_get_var 2 (t:(A,C,FFI)wl_state) = SOME a1`;
               ASSUME `a1:A word_loc = wl_Word w`; wl_get_var_imm_def] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff; ASSUME `~bit 0 (w:A word)`]) THEN
   (RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_STEP_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_store_def] THEN
   REWRITE_TAC[wl_evaluate_def] THEN
   SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ; bad_dest_args_def;
        wl_find_code_def; add_ret_loc_def; LENGTH; option_DISTINCT; NOT_CONS_NIL] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
   (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `LENGTH ([]:byte list) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `lookup InstallData_location (wl_state_stack_size (t:(A,C,FFI)wl_state))` THEN
   EXISTS_TAC `OPTION_MAP2 MAX (wl_state_stack_max (t:(A,C,FFI)wl_state))
      (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
         (lookup InstallData_location (wl_state_stack_size t)))` THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_component_equality] THEN SIMP[] THEN
   REWRITE_TAC[buffer_INFO.ri_component_equality] THEN SIMP[]);
   (X_GEN_TAC `b:byte` THEN X_GEN_TAC `bs:byte list` THEN DISCH_THEN(LABEL_TAC "IH") THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[ASP1AUX_v_to_bytes; MAP; ASP1AUX_v_to_list_CONS] THEN
   STRIP_TAC THEN VAR_EQ_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
     C CONJ (ASSUME `good_dimindex(:A)`) o
     check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel"))
                          (concl th))) THEN
   REWRITE_TAC[NOT_CONS_NIL] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `pa:A word` (X_CHOOSE_THEN `hx:A word` STRIP_ASSUME_TAC))))) THEN
   (SUBGOAL_THEN `shift_length c < dimindex(:A)` ASSUME_TAC THENL
    [UNDISCH_TAC `memory_rel c (wl_state_be (t:(A,C,FFI)wl_state)) ts refs sp
       (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (data_Block ts' cons_tag [(data_Number o (&) o val) (b:byte); bt],wl_Word w) vars)` THEN
     REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[];
     ALL_TAC]) THEN
   (MP_TAC(SPEC `0` (ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
     `refs:((data_v)bvl_ref)spt`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`;
     `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
     `ts':num`; `cons_tag`; `[(data_Number o (&) o val) (b:byte); bt]`; `wl_Word (w:A word)`;
     `vars:(data_v#(A)word_loc)list`] memory_rel_El_any)) THEN
   ASM_REWRITE_TAC[LENGTH; EL; HD; TL; injectivity "word_loc"; ARITH] THEN
   CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `x0:A word` STRIP_ASSUME_TAC))) THEN
   (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = pw`))) THEN
   (SUBGOAL_THEN `x0:A word = pa` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) w = SOME (x0:A word)` THEN
     ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
     ALL_TAC]) THEN
   (MP_TAC(SPEC `1` (ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
     `refs:((data_v)bvl_ref)spt`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`;
     `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
     `ts':num`; `cons_tag`; `[(data_Number o (&) o val) (b:byte); bt]`; `wl_Word (w:A word)`;
     `vars:(data_v#(A)word_loc)list`] memory_rel_El_any)) THEN
   ASM_REWRITE_TAC[LENGTH; EL; HD; TL; injectivity "word_loc"; ARITH;
     prove(`!x y (l:data_v list). EL 1 (CONS x (CONS y l)) = y`, REWRITE_TAC[ONE; EL; HD; TL])] THEN
   CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `pw1:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = pw1`)) THEN
   SUBGOAL_THEN `x1:A word = pa` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) w = SOME (x1:A word)` THEN
     ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[o_THM; WORD_MUL_0; WORD_ADD_0;
     WORD_RULE `word_mul (x:A word) (word 1) = x`])) THEN
   (SUBGOAL_THEN `val (b:byte) < 256` ASSUME_TAC THENL
    [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_state_memory (t:(A,C,FFI)wl_state) (word_add pa bytes_in_word) =
                 wl_Word (word (4 * val (b:byte)))` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
       `refs:((data_v)bvl_ref)spt`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`;
       `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
       `&(val (b:byte)):int`; `wl_state_memory (t:(A,C,FFI)wl_state) (word_add pa bytes_in_word)`;
       `CONS (data_Block ts' cons_tag [data_Number (&(val (b:byte))); bt],wl_Word (w:A word))
          (vars:(data_v#(A)word_loc)list)`] memory_rel_Number_IMP) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; small_int_def] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; INT_ARITH `-- &a <= &b:int`] THEN
       ASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `~(&n:int < &0)`] THEN
       REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM]];
     ALL_TAC]) THEN
   (SUBGOAL_THEN `2 EXP 32 <= 2 EXP dimindex(:A)` ASSUME_TAC THENL
    [REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `good_dimindex(:A)` THEN
     REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC; ALL_TAC]) THEN
   (SUBGOAL_THEN `4 * val (b:byte) < 2 EXP dimindex(:A) /\ val b < 2 EXP dimindex(:A)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 32` THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC]) THEN
   (SUBGOAL_THEN `word_ushr (word (4 * val (b:byte))) 2 = (word (val b):A word)` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_USHR; VAL_WORD] THEN
     ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
     SIMP_TAC[DIV_MULT; ARITH_EQ]; ALL_TAC]) THEN
   (SUBGOAL_THEN `word_zx (word (val (b:byte)):A word) = b` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD] THEN
     ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND];
     ALL_TAC]) THEN
   (SUBGOAL_THEN `word_add pa (word_mul (word 2) bytes_in_word) =
                 word_add (word_add pa bytes_in_word) (bytes_in_word:A word)` ASSUME_TAC THENL
    [CONV_TAC WORD_RULE; ALL_TAC]) THEN
   (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 2) = SOME (wl_Word pa)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
   (REWRITE_TAC[InstallCode_code_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
   REWRITE_TAC[ASSUME `wl_get_var 2 (t:(A,C,FFI)wl_state) = SOME (wl_Word w)`;
               wl_get_var_imm_def] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff; ASSUME `bit 0 (w:A word)`] THEN
   REWRITE_TAC[data_to_word_list_Seq_def]) THEN
   (SUBGOAL_THEN `0 < buffer_space_left (wl_state_code_buffer (t:(A,C,FFI)wl_state))` ASSUME_TAC
   THENL [UNDISCH_TAC `LENGTH (CONS (b:byte) bs) <=
                       buffer_space_left (wl_state_code_buffer (t:(A,C,FFI)wl_state))` THEN
          REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `ShiftVar Lsr 2 2 = wl_Shift Lsr (wl_Var 2) (wl_Const (word 2)):(A)wl_exp`
     SUBST1_TAC THENL
    [REWRITE_TAC[ShiftVar_def; distinctness "shift"; ARITH_EQ] THEN
     UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   SUBGOAL_THEN `~(2 >= dimindex(:A)) /\ 2 < dimword(:A)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; MAP; the_words_def; ITLIST; WORD_ADD_0; wl_mem_load_def;
     MOD_LT; VAL_WORD; buffer_write_def; DIMINDEX_8;
     WORD_RULE `word_mul (word 1) (x:B word) = x`]) THEN
   (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `LENGTH (CONS (b:byte) bs) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   ABBREV_TAC `tw = wl_state_memory (t:(A,C,FFI)wl_state)
                      (word_add (word_add pa bytes_in_word) bytes_in_word)` THEN
   REWRITE_TAC[wl_evaluate_def] THEN
   SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ; bad_dest_args_def;
        wl_find_code_def; add_ret_loc_def; LENGTH; option_DISTINCT; NOT_CONS_NIL] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
   ((fun (asl,w as g) ->
     let t88 = find_term (fun t -> is_comb t && is_const (fst(strip_comb t)) &&
                fst(dest_const(fst(strip_comb t))) = "wl_call_env") w in
     USE_THEN "IH" (MP_TAC o SPECL [t88; `c:data_to_word_config`; `bt:data_v`;
       `tw:A word_loc`; `a2:A word_loc`; `ret_val:A word_loc`; `bptr:A word_loc`;
       `CONS (data_Block ts' cons_tag [data_Number (&(val (b:byte))); bt], wl_Word (w:A word))
          (vars:(data_v#(A)word_loc)list)`; `sp:num`; `refs:((data_v)bvl_ref)spt`; `ts:num`]) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_call_env_def; wl_dec_clock_def; wl_get_var_def; fromList2_def; ASP1AUX_v_to_bytes;
          lookup_insert; ARITH_EQ; LENGTH; LENGTH_APPEND; WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
     MAP_EVERY (fun tm -> UNDISCH_TAC tm)
      [`LENGTH (CONS (b:byte) bs) < wl_state_clock (t:(A,C,FFI)wl_state)`;
       `LENGTH (CONS (b:byte) bs) <= buffer_space_left (wl_state_code_buffer (t:(A,C,FFI)wl_state))`] THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC;
     ALL_TAC]) THEN
   (DISCH_THEN(X_CHOOSE_THEN `lsz:num option` (X_CHOOSE_THEN `smx:num option` SUBST1_TAC))) THEN
   (REWRITE_TAC[ASP1AUX_bad_fun_filter]) THEN
   (MAP_EVERY EXISTS_TAC [`lsz:num option`; `smx:num option`] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
   (REWRITE_TAC[wl_call_env_def; wl_dec_clock_def]) THEN
   (REWRITE_TAC[wl_state_component_equality]) THEN
   (SIMP[]) THEN
   (REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; ARITH_RULE `(a - 1) - b = a - SUC b`;
               ARITH_RULE `(l + 1) + b = SUC (l + b)`])]);;

(* HOL4 line 1845 (the unused bound variables v1 s1 are left out) *)
let InstallCode_code_thm = prove
 (CASE_TERM
  `!(t:(A,C,FFI)wl_state) c hv1 q1 a1 a2 ret_val bptr vars sp refs ts.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (hv1,a1) vars) /\
     lookup InstallCode_location (wl_state_code t) = SOME (4,InstallCode_code c) /\
     lookup InstallData_location (wl_state_code t) = SOME (4,InstallData_code c) /\
     FLOOKUP (wl_state_store t) BitmapBuffer = SOME bptr /\
     data_v_to_bytes hv1 = SOME q1 /\
     LENGTH q1 <= buffer_space_left (wl_state_code_buffer t) /\
     LENGTH q1 < wl_state_clock t /\
     wl_get_var 0 t = SOME ret_val /\
     wl_get_var 2 t = SOME a1 /\
     wl_get_var 4 t = SOME a2 /\
     wl_get_var 6 t = SOME (wl_Word (word_add (buffer_position (wl_state_code_buffer t))
                              (word (LENGTH (buffer_buffer (wl_state_code_buffer t)))))) /\
     good_dimindex (:A) ==>
     ?lsz smx.
       wl_evaluate (InstallCode_code c,t) =
       match
         wl_evaluate (InstallData_code c,
           wl_state_locals_fupd
             (K (fromList2 [ret_val; bptr; a2;
                  wl_Word (word_add (buffer_position (wl_state_code_buffer t))
                    (word (LENGTH (buffer_buffer (wl_state_code_buffer t)) +
                           LENGTH q1)))]))
             (wl_state_locals_size_fupd (K lsz)
                (wl_state_clock_fupd (K ((wl_state_clock t - LENGTH q1) - 1))
                   (wl_state_code_buffer_fupd
                      (K (buffer_buffer_fupd
                            (K (APPEND (buffer_buffer (wl_state_code_buffer t)) q1))
                            (buffer_space_left_fupd
                               (K (buffer_space_left (wl_state_code_buffer t) -
                                   LENGTH q1))
                               (wl_state_code_buffer t))))
                      (wl_state_stack_max_fupd (K smx) t))))) with
         (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`q1:byte list`; `t:(A,C,FFI)wl_state`; `c:data_to_word_config`;
    `hv1:data_v`; `a1:A word_loc`; `a2:A word_loc`; `ret_val:A word_loc`;
    `bptr:A word_loc`; `vars:(data_v#(A)word_loc)list`; `sp:num`;
    `refs:((data_v)bvl_ref)spt`; `ts:num`] ASP1AUX_InstallCode) THEN
  REWRITE_TAC[]);;

(* HOL4 line 1964 *)
let w2w_upper_def = cake_def
  `w2w_upper (w:int64) =
     if dimindex (:A) = 32 then (word_extract 63 32 w):A word else word_zx w`;;

let ASP1AUX_v_to_words = prove
 (`!hv (q:int64 list). data_v_to_words hv = SOME q <=>
          data_v_to_list hv = SOME (MAP data_Word64 q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_v_to_words_def; some_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
    SPEC_TAC(`@ns:int64 list. data_v_to_list hv = SOME (MAP data_Word64 ns)`,
             `ns:int64 list`) THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[option_INJ; MAP_Word64_11] THEN MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* InstallData_code_thm with q2 quantified first, by induction on q2 *)
let ASP1AUX_InstallData = prove
 (CASE_TERM
  `!q2 (t:(A,C,FFI)wl_state) c hv2 a1 a2 ret_val vars sp refs ts.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (hv2,a2) vars) /\
     lookup InstallData_location (wl_state_code t) = SOME (4,InstallData_code c) /\
     lookup Install_location (wl_state_code t) = SOME (3,Install_code c) /\
     data_v_to_words hv2 = SOME q2 /\
     LENGTH q2 <= buffer_space_left (wl_state_data_buffer t) /\
     LENGTH q2 < wl_state_clock t /\
     wl_get_var 0 t = SOME ret_val /\
     wl_get_var 2 t = SOME (wl_Word (word_add (buffer_position (wl_state_data_buffer t))
                              (word_mul bytes_in_word
                                 (word (LENGTH (buffer_buffer (wl_state_data_buffer t))))))) /\
     wl_get_var 4 t = SOME a2 /\
     wl_get_var 6 t = SOME a1 /\
     good_dimindex (:A) ==>
     ?smx lsz.
       wl_evaluate (InstallData_code c,t) =
       match
         wl_evaluate (Install_code c,
           wl_state_locals_fupd
             (K (fromList2 [ret_val;
                  wl_Word (word_add (word_add (buffer_position (wl_state_data_buffer t))
                    (word_mul bytes_in_word
                       (word (LENGTH (buffer_buffer (wl_state_data_buffer t))))))
                    (word_mul bytes_in_word (word (LENGTH q2)))); a1]))
             (wl_state_clock_fupd (K ((wl_state_clock t - LENGTH q2) - 1))
                (wl_state_data_buffer_fupd
                   (K (buffer_buffer_fupd
                         (K (APPEND (buffer_buffer (wl_state_data_buffer t))
                                    (MAP w2w_upper q2)))
                         (buffer_space_left_fupd
                            (K (buffer_space_left (wl_state_data_buffer t) - LENGTH q2))
                            (wl_state_data_buffer t))))
                   (wl_state_locals_size_fupd (K lsz)
                      (wl_state_stack_max_fupd (K smx) t))))) with
         (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)`,
  (MATCH_MP_TAC list_INDUCT THEN CONJ_TAC) THENL
  [(REPEAT GEN_TAC THEN REWRITE_TAC[ASP1AUX_v_to_words; MAP; v_to_list_EQ_SOME_NIL] THEN
   STRIP_TAC THEN VAR_EQ_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
     C CONJ (ASSUME `good_dimindex(:A)`) o
     check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel"))
                          (concl th))) THEN
   REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:A word` STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[InstallData_code_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
   REWRITE_TAC[ASSUME `wl_get_var 4 (t:(A,C,FFI)wl_state) = SOME a2`;
               ASSUME `a2:A word_loc = wl_Word w`; wl_get_var_imm_def] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff; ASSUME `~bit 0 (w:A word)`] THEN
   REWRITE_TAC[data_to_word_list_Seq_def]) THEN
   (RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   REWRITE_TAC[wl_evaluate_def] THEN
   SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ; bad_dest_args_def;
        wl_find_code_def; add_ret_loc_def; LENGTH; option_DISTINCT; NOT_CONS_NIL] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
   (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `LENGTH ([]:int64 list) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   EXISTS_TAC `OPTION_MAP2 MAX (wl_state_stack_max (t:(A,C,FFI)wl_state))
      (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
         (lookup Install_location (wl_state_stack_size t)))` THEN
   EXISTS_TAC `lookup Install_location (wl_state_stack_size (t:(A,C,FFI)wl_state))` THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_component_equality] THEN SIMP[] THEN
   REWRITE_TAC[buffer_INFO.ri_component_equality; WORD_MUL_0; WORD_ADD_0] THEN SIMP[]);
   (X_GEN_TAC `h:int64` THEN X_GEN_TAC `hs:int64 list` THEN DISCH_THEN(LABEL_TAC "IH") THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[ASP1AUX_v_to_words; MAP; ASP1AUX_v_to_list_CONS] THEN
   STRIP_TAC THEN VAR_EQ_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
     C CONJ (ASSUME `good_dimindex(:A)`) o
     check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel"))
                          (concl th))) THEN
   REWRITE_TAC[NOT_CONS_NIL] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `pa:A word` (X_CHOOSE_THEN `hx:A word` STRIP_ASSUME_TAC))))) THEN
   (SUBGOAL_THEN `shift_length c < dimindex(:A)` ASSUME_TAC THENL
    [UNDISCH_TAC `memory_rel c (wl_state_be (t:(A,C,FFI)wl_state)) ts refs sp
       (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (data_Block ts' cons_tag [data_Word64 h; bt],wl_Word w) vars)` THEN
     REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[];
     ALL_TAC]) THEN
   (MP_TAC(SPEC `0` (ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
     `refs:((data_v)bvl_ref)spt`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`;
     `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
     `ts':num`; `cons_tag`; `[data_Word64 h; bt]`; `wl_Word (w:A word)`;
     `vars:(data_v#(A)word_loc)list`] memory_rel_El_any)) THEN
   ASM_REWRITE_TAC[LENGTH; EL; HD; TL; injectivity "word_loc"; ARITH] THEN
   CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `x0:A word` STRIP_ASSUME_TAC))) THEN
   (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = pw`))) THEN
   (SUBGOAL_THEN `x0:A word = pa` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) w = SOME (x0:A word)` THEN
     ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
     ALL_TAC]) THEN
   (MP_TAC(SPEC `1` (ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
     `refs:((data_v)bvl_ref)spt`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`;
     `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
     `ts':num`; `cons_tag`; `[data_Word64 h; bt]`; `wl_Word (w:A word)`;
     `vars:(data_v#(A)word_loc)list`] memory_rel_El_any)) THEN
   ASM_REWRITE_TAC[LENGTH; EL; HD; TL; injectivity "word_loc"; ARITH;
     prove(`!x y (l:data_v list). EL 1 (CONS x (CONS y l)) = y`, REWRITE_TAC[ONE; EL; HD; TL])] THEN
   CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `pw1:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = pw1`)) THEN
   SUBGOAL_THEN `x1:A word = pa` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) w = SOME (x1:A word)` THEN
     ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[o_THM; WORD_MUL_0; WORD_ADD_0;
     WORD_RULE `word_mul (x:A word) (word 1) = x`])) THEN
   (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Word64_IMP o C CONJ (ASSUME `good_dimindex(:A)`) o
     check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "data_Word64"))
                      (concl th) &&
                      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "data_Block"))
                      (rand(rator(concl th)))))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `xw:A word` (X_CHOOSE_THEN `hw:A word`
     STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `wl_state_memory (t:(A,C,FFI)wl_state) (word_add xw bytes_in_word) =
                 wl_Word (w2w_upper h)` ASSUME_TAC THENL
    [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
     ASM_REWRITE_TAC[w2w_upper_def] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[injectivity "word_loc"] THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_ZX; DIMINDEX_64] THEN
     ASM_REWRITE_TAC[ADD_CLAUSES] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `i <= 63` (fun th -> REWRITE_TAC[th]) THEN
     ASM_ARITH_TAC;
     ALL_TAC]) THEN
   (SUBGOAL_THEN `word_add pa (word_mul (word 2) bytes_in_word) =
                 word_add (word_add pa bytes_in_word) (bytes_in_word:A word)` ASSUME_TAC THENL
    [CONV_TAC WORD_RULE; ALL_TAC] THEN
   SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 4) = SOME (wl_Word pa)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `0 < buffer_space_left (wl_state_data_buffer (t:(A,C,FFI)wl_state))` ASSUME_TAC
   THENL [UNDISCH_TAC `LENGTH (CONS (h:int64) hs) <=
                       buffer_space_left (wl_state_data_buffer (t:(A,C,FFI)wl_state))` THEN
          REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC]) THEN
   (REWRITE_TAC[InstallData_code_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
   REWRITE_TAC[ASSUME `wl_get_var 4 (t:(A,C,FFI)wl_state) = SOME (wl_Word w)`;
               wl_get_var_imm_def] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[wl_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff; ASSUME `bit 0 (w:A word)`] THEN
   REWRITE_TAC[data_to_word_list_Seq_def]) THEN
   (RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; MAP; the_words_def; ITLIST; WORD_ADD_0; wl_mem_load_def;
     buffer_write_def; GSYM bytes_in_word_def]) THEN
   ((fun (asl,w as g) ->
     let is_seq_eval t =
       try let f,p = dest_comb t in
           fst(dest_const f) = "wl_evaluate" &&
           (let prog,_ = dest_pair p in
            fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
       with Failure _ -> false in
     let s2 = snd(dest_pair(rand(find_term is_seq_eval w))) in
     SUBGOAL_THEN (vsubst [s2, `s0:(A,C,FFI)wl_state`]
        `wl_word_exp (s0:(A,C,FFI)wl_state) (real_addr c 4) = SOME (wl_Word (xw:A word))`)
       ASSUME_TAC g) THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN
     EXISTS_TAC `get_addr c ptr (wl_Word (word 0)):A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def] THEN SIMP[lookup_insert];
     ALL_TAC]) THEN
   (ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; MAP; the_words_def; ITLIST; WORD_ADD_0; wl_mem_load_def;
     buffer_write_def; GSYM bytes_in_word_def]) THEN
   (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `LENGTH (CONS (h:int64) hs) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   ABBREV_TAC `tw = wl_state_memory (t:(A,C,FFI)wl_state)
                      (word_add (word_add pa bytes_in_word) bytes_in_word)` THEN
   REWRITE_TAC[wl_evaluate_def] THEN
   SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ; bad_dest_args_def;
        wl_find_code_def; add_ret_loc_def; LENGTH; option_DISTINCT; NOT_CONS_NIL] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
   ((fun (asl,w as g) ->
     let t88 = find_term (fun t -> is_comb t && is_const (fst(strip_comb t)) &&
                fst(dest_const(fst(strip_comb t))) = "wl_call_env") w in
     USE_THEN "IH" (MP_TAC o SPECL [t88; `c:data_to_word_config`; `bt:data_v`;
       `a1:A word_loc`; `tw:A word_loc`; `ret_val:A word_loc`;
       `CONS (data_Block ts' cons_tag [data_Word64 h; bt], wl_Word (w:A word))
          (vars:(data_v#(A)word_loc)list)`; `sp:num`; `refs:((data_v)bvl_ref)spt`; `ts:num`]) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_call_env_def; wl_dec_clock_def; wl_get_var_def; fromList2_def; ASP1AUX_v_to_words;
          lookup_insert; ARITH_EQ; LENGTH; LENGTH_APPEND] THEN
     REPEAT CONJ_TAC THENL
      [UNDISCH_TAC `LENGTH (CONS (h:int64) hs) <=
                    buffer_space_left (wl_state_data_buffer (t:(A,C,FFI)wl_state))` THEN
       REWRITE_TAC[LENGTH] THEN ARITH_TAC;
       UNDISCH_TAC `LENGTH (CONS (h:int64) hs) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN
       REWRITE_TAC[LENGTH] THEN ARITH_TAC;
       REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
     ALL_TAC]) THEN
   (DISCH_THEN(X_CHOOSE_THEN `smx:num option` (X_CHOOSE_THEN `lsz:num option` SUBST1_TAC))) THEN
   (REWRITE_TAC[ASP1AUX_bad_fun_filter]) THEN
   (MAP_EVERY EXISTS_TAC [`smx:num option`; `lsz:num option`] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
   (REWRITE_TAC[wl_call_env_def; wl_dec_clock_def]) THEN
   (REWRITE_TAC[wl_state_component_equality]) THEN
   (SIMP[]) THEN
   (REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; ARITH_RULE `(a - 1) - b = a - SUC b`] THEN
   AP_TERM_TAC THEN REWRITE_TAC[CONS_11; injectivity "word_loc"] THEN
   REWRITE_TAC[WORD_ADD; ADD1] THEN CONV_TAC WORD_RULE)]);;

(* HOL4 line 1969 (the unused bound variables v1 s1 are left out) *)
let InstallData_code_thm = prove
 (CASE_TERM
  `!(t:(A,C,FFI)wl_state) c hv2 q2 a1 a2 ret_val vars sp refs ts.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (hv2,a2) vars) /\
     lookup InstallData_location (wl_state_code t) = SOME (4,InstallData_code c) /\
     lookup Install_location (wl_state_code t) = SOME (3,Install_code c) /\
     data_v_to_words hv2 = SOME q2 /\
     LENGTH q2 <= buffer_space_left (wl_state_data_buffer t) /\
     LENGTH q2 < wl_state_clock t /\
     wl_get_var 0 t = SOME ret_val /\
     wl_get_var 2 t = SOME (wl_Word (word_add (buffer_position (wl_state_data_buffer t))
                              (word_mul bytes_in_word
                                 (word (LENGTH (buffer_buffer (wl_state_data_buffer t))))))) /\
     wl_get_var 4 t = SOME a2 /\
     wl_get_var 6 t = SOME a1 /\
     good_dimindex (:A) ==>
     ?smx lsz.
       wl_evaluate (InstallData_code c,t) =
       match
         wl_evaluate (Install_code c,
           wl_state_locals_fupd
             (K (fromList2 [ret_val;
                  wl_Word (word_add (word_add (buffer_position (wl_state_data_buffer t))
                    (word_mul bytes_in_word
                       (word (LENGTH (buffer_buffer (wl_state_data_buffer t))))))
                    (word_mul bytes_in_word (word (LENGTH q2)))); a1]))
             (wl_state_clock_fupd (K ((wl_state_clock t - LENGTH q2) - 1))
                (wl_state_data_buffer_fupd
                   (K (buffer_buffer_fupd
                         (K (APPEND (buffer_buffer (wl_state_data_buffer t))
                                    (MAP w2w_upper q2)))
                         (buffer_space_left_fupd
                            (K (buffer_space_left (wl_state_data_buffer t) - LENGTH q2))
                            (wl_state_data_buffer t))))
                   (wl_state_locals_size_fupd (K lsz)
                      (wl_state_stack_max_fupd (K smx) t))))) with
         (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`q2:int64 list`; `t:(A,C,FFI)wl_state`; `c:data_to_word_config`;
    `hv2:data_v`; `a1:A word_loc`; `a2:A word_loc`; `ret_val:A word_loc`;
    `vars:(data_v#(A)word_loc)list`; `sp:num`;
    `refs:((data_v)bvl_ref)spt`; `ts:num`] ASP1AUX_InstallData) THEN
  REWRITE_TAC[]);;

(* HOL4 line 2098 *)
let LENGTH_EQ_4 = prove
 (`!xs:A list.
     (LENGTH xs = 4 <=> ?a1 a2 a3 a4. xs = [a1;a2;a3;a4]) /\
     (4 = LENGTH xs <=> ?a1 a2 a3 a4. xs = [a1;a2;a3;a4])`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a <=> c) /\ (b <=> a) ==> (a <=> c) /\ (b <=> c)`) THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

(* HOL4 line 2106 *)
let w2w_upper_upper_w2w = prove
 (`!z1. good_dimindex (:A) ==> MAP w2w_upper (MAP upper_w2w z1) = z1:(A word)list`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; CONS_11] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[w2w_upper_def; upper_w2w_def; ARITH_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_SHL; BIT_WORD_ZX;
              DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `bit i (h:A word)` THEN ASM_REWRITE_TAC[ADD_SUB] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[BIT_GUARD]) THEN ASM_ARITH_TAC);;

(* HOL4 line 2118 (local) *)
let MAP_FST_MAP_compile_part = prove
 (`!c full_list.
     MAP FST (MAP (data_to_word_compile_part c) full_list:(num#num#(A)wl_prog)list) =
     MAP FST full_list`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN
  SPEC_TAC(`h:num#num#data_prog`,`h:num#num#data_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; data_to_word_compile_part_def]);;

(* HOL4 line 2124 (local) *)
let memory_rel_ignore_buffers = prove
 (`!c be ts refs sp st x (m:A word->A word_loc) dm vars.
     memory_rel c be ts refs sp (st |+ (BitmapBuffer,x)) m dm vars =
     memory_rel c be ts refs sp st m dm vars /\
     memory_rel c be ts refs sp (st |+ (CodeBuffer,x)) m dm vars =
     memory_rel c be ts refs sp st m dm vars`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def; FLOOKUP_UPDATE;
              FDOM_FUPDATE; IN_INSERT; distinctness "store_name"]);;

(* HOL4 line 2133 (local) *)
let compile_part_loc_IMP = prove
 (`!c a1 a2 n (x:num#(A)wl_prog).
     data_to_word_compile_part c (a1,a2) = (n,x) ==> n = a1`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`a2:num#data_prog`,`a2:num#data_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; data_to_word_compile_part_def; PAIR_EQ] THEN
  MESON_TAC[]);;

(* HOL4 line 2139 *)
let consume_space_stack_max = prove
 (`!a (x:(C,FFI)data_state) s.
     consume_space a x = SOME s ==> data_state_stack_max x = data_state_stack_max s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[consume_space_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

(* HOL4 line 2146: fun cases_on_op (a tactic) *)

(* HOL4 line 2149 *)
let do_app_aux_safe_for_space_mono = prove
 (`!op xs (s:(C,FFI)data_state) r s1.
     (data_do_app_aux op xs s = Rval (r,s1)) /\ data_state_safe_for_space s1 ==>
     data_state_safe_for_space s`,
  X_GEN_TAC `op:clos_op` THEN DSEMAUX_OP_CASES_TAC `op:clos_op` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_aux_def; with_fresh_ts_def; check_lim_def; consume_space_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          CASE_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2164 *)
let do_app_safe_for_space_allowed_op = prove
 (`!op xs (s:(C,FFI)data_state) r s1.
     data_do_app op xs s = Rval(r,s1) /\ data_state_safe_for_space s1 ==>
     allowed_op op (LENGTH xs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `data_state_locals (s:(C,FFI)data_state)` o
    MATCH_MP do_app_locals) THEN
  SUBGOAL_THEN `data_state_locals_fupd (K (data_state_locals s)) (s:(C,FFI)data_state) = s`
    SUBST1_TAC THENL
   [REWRITE_TAC[data_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `data_state_safe_for_space:(C,FFI)data_state->bool`) THEN
  SIMP[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2177 *)
let state_rel_cut_state_opt_SOME = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs args vals kept_names x.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME vals /\
     data_cut_state_opt (SOME kept_names) s = SOME x ==>
     ?y ws.
       wl_cut_env (adjust_sets kept_names) (wl_state_locals t) = SOME y /\
       wl_get_vars (MAP adjust_var args) t = SOME ws /\
       LENGTH args = LENGTH vals /\ LENGTH args = LENGTH ws /\
       data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\
       data_to_word_gcProof_state_rel c l1 l2 x (wl_state_locals_fupd (K y) t) NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 x (t:(A,C,FFI)wl_state) NONE locs`
    ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_cut_IMP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`args:num list`; `vals:data_v list`; `c:data_to_word_config`;
    `l1:num`; `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
    `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?kenv. data_cut_env kept_names (data_state_locals (s:(C,FFI)data_state)) =
                       SOME kenv /\ x = data_state_locals_fupd (K kenv) s`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_state_opt (SOME kept_names) (s:(C,FFI)data_state) = SOME x` THEN
    REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `data_cut_env kept_names (data_state_locals (s:(C,FFI)data_state))` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `kept_names:num_set`; `kenv:data_v spt`]
    cut_env_IMP_cut_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:(A word_loc)spt`) THEN
  MAP_EVERY EXISTS_TAC [`y:(A word_loc)spt`; `ws:(A word_loc)list`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH];
    ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH];
    UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 x (t:(A,C,FFI)wl_state) NONE locs` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_MESON_TAC[state_rel_cut_env_cut_env]]);;

(* HOL4 line 2202 *)
let cut_state_opt_SOME_eq = prove
 (`!names (s:(C,FFI)data_state) x.
     data_cut_state_opt (SOME names) s = SOME x ==>
     x = data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) names))) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_cut_env_def] THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 2210: val mk_wf_inter = MATCH_MP wf_mk_id (SPEC_ALL wf_inter)   *)
(* |> GEN_ALL *)
let mk_wf_inter = prove
 (`!(m1:A spt) (m2:B spt). mk_wf (sptree_inter m1 m2) = sptree_inter m1 m2`,
  MESON_TAC[wf_mk_id; wf_inter]);;

(* HOL4 line 2211: val state_rel_cut_env' = state_rel_cut_env |>            *)
(* REWRITE_RULE [GSYM AND_IMP_INTRO] (the curried form)                     *)
let state_rel_cut_env' = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     data_cut_env names (data_state_locals s) = SOME x ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (K x) s) t NONE locs`,
  MESON_TAC[state_rel_cut_env]);;

(* HOL4 line 2214 *)
let state_rel_cut_state_opt_set_var = prove
 (`!c l1 l2 dest v (s2:(C,FFI)data_state) (r:(A,C,FFI)wl_state) locs names s2_cut.
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2) r NONE locs /\
     data_cut_state_opt (SOME names) s2 = SOME s2_cut ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2_cut) r NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `domain (names:num_set) SUBSET domain (data_state_locals (s2:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_state_opt (SOME names) (s2:(C,FFI)data_state) = SOME s2_cut` THEN
    REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_cut_env_def] THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  SUBGOAL_THEN
   `data_cut_env (insert dest one names) (insert dest v (data_state_locals s2)) =
    SOME (insert dest v (sptree_inter (data_state_locals (s2:(C,FFI)data_state)) (names:num_set)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[data_cut_env_def; domain_insert] THEN
    SUBGOAL_THEN `dest INSERT domain (names:num_set) SUBSET
                  dest INSERT domain (data_state_locals (s2:(C,FFI)data_state))`
      (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[spt_eq_thm; wf_mk_wf; wf_insert; wf_inter] THEN GEN_TAC THEN
    REWRITE_TAC[lookup_mk_wf; lookup_insert; lookup_inter_alt; domain_insert; IN_INSERT] THEN
    ASM_CASES_TAC `n:num = dest` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_set_var dest v (s2:(C,FFI)data_state)`; `r:(A,C,FFI)wl_state`;
    `locs:(num#num)list`; `insert dest one (names:num_set)`;
    `insert dest v (sptree_inter (data_state_locals (s2:(C,FFI)data_state)) (names:num_set))`]
    state_rel_cut_env') THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[data_set_var_def] THEN SIMP[mk_wf_inter] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP[]]);;

(* HOL4 line 2240 *)
let cut_env_idempotent = prove
 (`!ns (s_locals:A spt) env.
     data_cut_env ns s_locals = SOME env ==> data_cut_env ns env = SOME env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def; mk_wf_inter] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[domain_inter; mk_wf_inter] THEN
  SUBGOAL_THEN `domain (ns:num_set) SUBSET domain (s_locals:A spt) INTER domain ns`
    (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[option_INJ] THEN
  SIMP_TAC[spt_eq_thm; wf_inter] THEN GEN_TAC THEN
  REWRITE_TAC[lookup_inter_alt] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 2254 *)
let cut_env_cut_env_list_insert = prove
 (`!vs ns (env:A spt) env_wide env_narrow.
     data_cut_env (list_insert vs ns) env = SOME env_wide /\
     data_cut_env ns env = SOME env_narrow ==>
     data_cut_env ns env_wide = SOME env_narrow`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def; mk_wf_inter] THEN
  ASM_CASES_TAC `domain (list_insert vs ns) SUBSET domain (env:A spt)` THEN
  ASM_CASES_TAC `domain (ns:num_set) SUBSET domain (env:A spt)` THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[domain_inter] THEN
  SUBGOAL_THEN `domain (ns:num_set) SUBSET domain (list_insert vs ns)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; domain_list_insert] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `domain (ns:num_set) SUBSET domain (env:A spt) INTER domain (list_insert vs ns)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[option_INJ] THEN
  SIMP_TAC[spt_eq_thm; wf_inter] THEN GEN_TAC THEN
  REWRITE_TAC[lookup_inter_alt] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* HOL4 line 2272 *)
let join_env_submap_MEM = prove
 (`!(l1:A spt) l1' (l2:B spt) l2' p.
     (!k v. lookup k l1 = SOME v ==> lookup k l1' = SOME v) /\
     (!k v. lookup k l2 = SOME v ==> lookup k l2' = SOME v) /\
     MEM p (join_env l1 (toAList (sptree_inter l2 (adjust_set l1)))) ==>
     MEM p (join_env l1' (toAList (sptree_inter l2' (adjust_set l1'))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM; MEM_toAList] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num` (X_CHOOSE_THEN `vv:B` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`nn:num`; `vv:B`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!l:A spt. nn IN domain (adjust_set l) <=> (nn - 2) DIV 2 IN domain l`
    ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [domain_lookup] THEN
    REWRITE_TAC[lookup_adjust_set] THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `lookup nn (sptree_inter (l2:B spt) (adjust_set (l1:A spt))) = SOME vv` THEN
  ASM_REWRITE_TAC[lookup_inter_alt] THEN
  ASM_CASES_TAC `(nn - 2) DIV 2 IN domain (l1:A spt)` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [domain_lookup] o
    check (fun th -> concl th = `(nn - 2) DIV 2 IN domain (l1:A spt)`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `u:A`) THEN
  SUBGOAL_THEN `lookup ((nn - 2) DIV 2) (l1':A spt) = SOME u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(nn - 2) DIV 2 IN domain (l1':A spt)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2286 *)
let state_rel_FLOOKUP_heap = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     ?nf cu hl.
       FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word nf) /\
       FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word cu) /\
       FLOOKUP (wl_state_store t) HeapLength = SOME (wl_Word hl)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[]);;

(* HOL4 line 2303 *)
let evaluate_SilentFFI_3 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs (ns:B spt) env.
     data_to_word_config_call_empty_ffi c /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     wl_cut_env (adjust_sets ns) (wl_state_locals t) = SOME env ==>
     wl_evaluate (SilentFFI c 3 (adjust_sets ns),t) =
       (NONE,wl_state_locals_fupd (K env) (wl_state_fp_regs_fupd (K FEMPTY)
               (wl_state_memory_fupd (K (wl_state_memory t))
                  (wl_state_ffi_fupd (K (wl_state_ffi t)) t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP state_rel_FLOOKUP_heap) THEN
  ASM_REWRITE_TAC[SilentFFI_def; data_to_word_list_Seq_def] THEN
  ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; MAP; the_words_def; ITLIST;
    WORD_ADD_0; wl_set_var_def; wl_get_var_def; lookup_insert; wl_get_store_def] THEN
  SIMP[wl_evaluate_def; wl_get_var_def; lookup_insert; ARITH_EQ;
       cut_env_adjust_sets_insert_ODD; ARITH_ODD; VAL_WORD_0; read_bytearray_def;
       call_FFI_def; write_bytearray_def] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* HOL4 line 2327 *)
let size_of_app_Number = prove
 (CASE_TERM
  `!xs ys lims i refs seen.
     size_of lims (APPEND xs (CONS (data_Number i) ys)) refs seen =
     let (n,refs',seen') = size_of lims (APPEND xs ys) refs seen in
     let k = if small_num (limits_arch_64_bit lims) i then 0
             else bignum_size (limits_arch_64_bit lims) i in
     (n + k,refs',seen')`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
   [REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ys:data_v list` list_CASES) THEN
    REWRITE_TAC[size_of_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES] THEN
    MP_TAC(ISPEC `size_of lims (CONS (h:data_v) t) refs seen` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `rs:((data_v)bvl_ref)spt#(1)spt`
      MP_TAC)) THEN
    MP_TAC(ISPEC `rs:((data_v)bvl_ref)spt#(1)spt` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `s1:1 spt`
      SUBST1_TAC)) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[size_of_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_cons] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `size_of lims (APPEND (t:data_v list) ys) refs seen` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `rs:((data_v)bvl_ref)spt#(1)spt`
    MP_TAC)) THEN
  MP_TAC(ISPEC `rs:((data_v)bvl_ref)spt#(1)spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `s1:1 spt`
    SUBST1_TAC)) THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `size_of lims [h:data_v] r1 s1` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `rs2:((data_v)bvl_ref)spt#(1)spt`
    MP_TAC)) THEN
  MP_TAC(ISPEC `rs2:((data_v)bvl_ref)spt#(1)spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `s2:1 spt`
    SUBST1_TAC)) THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC);;

(* HOL4 line 2348 *)
let toList_delete_split = prove
 (`!k (spt:A spt) vv.
     lookup k spt = SOME vv ==>
     ?pre post.
       toList spt = APPEND (APPEND pre [vv]) post /\
       toList (delete k spt) = APPEND pre post`,
  SUBGOAL_THEN
   `(!(t1:A spt) t2. toList (BN t1 t2) = APPEND (toList t1) (toList t2)) /\
    (!(t1:A spt) a t2. toList (BS t1 a t2) = APPEND (toList t1) (CONS a (toList t2))) /\
    (!(t1:A spt) t2. toList (mk_BN t1 t2) = toList (BN t1 t2)) /\
    (!(t1:A spt) a t2. toList (mk_BS t1 a t2) = toList (BS t1 a t2)) /\
    (!a:A. toList (LS a) = [a]) /\ toList (LN:A spt) = []`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[toList_def; toListA_mk] THEN REWRITE_TAC[toListA_def] THEN
    ONCE_REWRITE_TAC[toListA_append] THEN REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC spt_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_def; option_DISTINCT];
    REPEAT GEN_TAC THEN REWRITE_TAC[lookup_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[delete_def] THEN
    MAP_EVERY EXISTS_TAC [`[]:A list`; `[]:A list`] THEN REWRITE_TAC[APPEND];
    MAP_EVERY X_GEN_TAC [`t1:A spt`; `t2:A spt`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `vv:A`] THEN REWRITE_TAC[lookup_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    ASM_REWRITE_TAC[delete_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`(k - 1) DIV 2`; `vv:A`] o
        check (fun th -> can (find_term ((=) `t1:A spt`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `pre:A list` (X_CHOOSE_THEN `post:A list`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`pre:A list`; `APPEND post (toList (t2:A spt))`] THEN
      ASM_REWRITE_TAC[APPEND_ASSOC];
      FIRST_X_ASSUM(MP_TAC o SPECL [`(k - 1) DIV 2`; `vv:A`] o
        check (fun th -> can (find_term ((=) `t2:A spt`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `pre:A list` (X_CHOOSE_THEN `post:A list`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`APPEND (toList (t1:A spt)) pre`; `post:A list`] THEN
      ASM_REWRITE_TAC[APPEND_ASSOC]];
    MAP_EVERY X_GEN_TAC [`t1:A spt`; `a:A`; `t2:A spt`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `vv:A`] THEN REWRITE_TAC[lookup_def] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[delete_def] THEN
      MAP_EVERY EXISTS_TAC [`toList (t1:A spt)`; `toList (t2:A spt)`] THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[delete_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`(k - 1) DIV 2`; `vv:A`] o
        check (fun th -> can (find_term ((=) `t1:A spt`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `pre:A list` (X_CHOOSE_THEN `post:A list`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`pre:A list`; `APPEND post (CONS (a:A) (toList (t2:A spt)))`] THEN
      ASM_REWRITE_TAC[APPEND_ASSOC];
      FIRST_X_ASSUM(MP_TAC o SPECL [`(k - 1) DIV 2`; `vv:A`] o
        check (fun th -> can (find_term ((=) `t2:A spt`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `pre:A list` (X_CHOOSE_THEN `post:A list`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`APPEND (toList (t1:A spt)) (CONS (a:A) pre)`; `post:A list`] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]]);;

(* HOL4 line 2382 *)
let size_of_heap_delete_Number_LE = prove
 (`!k (s:(C,FFI)data_state) i.
     lookup k (data_state_locals s) = SOME (data_Number i) ==>
     size_of_heap (data_state_locals_fupd (K (delete k (data_state_locals s))) s) <=
     size_of_heap s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `pre:data_v list` (X_CHOOSE_THEN `post:data_v list`
    STRIP_ASSUME_TAC) o MATCH_MP toList_delete_split) THEN
  REWRITE_TAC[size_of_heap_def; stack_to_vs_def] THEN SIMP[] THEN
  ABBREV_TAC `rest = APPEND (FLAT (MAP extract_stack (data_state_stack (s:(C,FFI)data_state))))
                       (global_to_vs (data_state_global s))` THEN
  SUBGOAL_THEN
   `APPEND (APPEND (APPEND (APPEND pre [data_Number i]) post)
       (FLAT (MAP extract_stack (data_state_stack (s:(C,FFI)data_state)))))
       (global_to_vs (data_state_global s)) =
    APPEND pre (CONS (data_Number i) (APPEND post rest)) /\
    APPEND (APPEND (APPEND pre post)
       (FLAT (MAP extract_stack (data_state_stack (s:(C,FFI)data_state)))))
       (global_to_vs (data_state_global s)) =
    APPEND pre (APPEND post rest)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "rest" THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  REWRITE_TAC[size_of_app_Number; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `size_of (data_state_limits (s:(C,FFI)data_state))
                  (APPEND pre (APPEND post rest)) (data_state_refs s) LN` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `rs:((data_v)bvl_ref)spt#(1)spt`
    MP_TAC)) THEN
  MP_TAC(ISPEC `rs:((data_v)bvl_ref)spt#(1)spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `s1:1 spt`
    SUBST1_TAC)) THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 2402 *)
let wf_FOLDR_delete = prove
 (`!ks (L:A spt). sptree_wf L ==> sptree_wf (ITLIST delete ks L)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ITLIST; wf_delete]);;

(* HOL4 line 2408 *)
let data_to_word_assignProof_lookup_FOLDR_delete = prove
 (`!ks (L:A spt) h.
     lookup h (ITLIST delete ks L) = if MEM h ks then NONE else lookup h L`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MEM; lookup_delete] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `h' = (h:num)` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* HOL4 line 2416 *)
let size_of_heap_FOLDR_delete_Number_LE = prove
 (`!ks L (state:(A,B)data_state).
     sptree_wf L /\
     (!k. MEM k ks ==> lookup k L = NONE \/ ?i. lookup k L = SOME (data_Number i)) ==>
     size_of_heap (data_state_locals_fupd (K (ITLIST delete ks L)) state) <=
     size_of_heap (data_state_locals_fupd (K L) state)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; LE_REFL; MEM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `M = ITLIST delete (t:num list) (L:data_v spt)` THEN
  SUBGOAL_THEN `size_of_heap (data_state_locals_fupd (K (M:data_v spt)) (state:(A,B)data_state)) <=
                size_of_heap (data_state_locals_fupd (K L) state)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `lookup h (M:data_v spt) = NONE` THENL
   [SUBGOAL_THEN `delete h (M:data_v spt) = M` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`h:num`; `M:data_v spt`] delete_fail) THEN
    ANTS_TAC THENL [EXPAND_TAC "M" THEN ASM_SIMP_TAC[wf_FOLDR_delete]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i. lookup h (M:data_v spt) = SOME (data_Number i)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(lookup h (M:data_v spt) = NONE)` THEN EXPAND_TAC "M" THEN
    REWRITE_TAC[data_to_word_assignProof_lookup_FOLDR_delete] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `size_of_heap (data_state_locals_fupd (K (M:data_v spt)) (state:(A,B)data_state))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:num`; `data_state_locals_fupd (K (M:data_v spt)) (state:(A,B)data_state)`;
                 `i:int`] size_of_heap_delete_Number_LE) THEN
  SIMP[]);;

(* the end of most assign proofs (HOL4: fs [state_rel_thm] ... then         *)
(* match_mp_tac memory_rel_insert): dest := v in the data state and         *)
(* adjust_var dest := w in the word state, the data state changed only in   *)
(* refs, tstamps, stack_max and the safety flags                            *)
let ASP1AUX_state_rel_set_var = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w
    (s2:(C,FFI)data_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     data_state_space s2 = data_state_space s /\
     data_state_global s2 = data_state_global s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_set_var (adjust_var dest) w t) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; wl_set_var_def] THEN SIMP[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_insert; adjust_var_NEQ; adjust_var_11] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[option_le_trans];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

(* as ASP1AUX_state_rel_set_var, the word state's memory also replaced     *)
let ASP1AUX_state_rel_set_var_mem = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w m'
    (s2:(C,FFI)data_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     data_state_space s2 = data_state_space s /\
     data_state_global s2 = data_state_global s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s) (wl_state_store t) m' (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_set_var (adjust_var dest) w (wl_state_memory_fupd (K m') t)) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; wl_set_var_def] THEN SIMP[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_insert; adjust_var_NEQ; adjust_var_11] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[option_le_trans];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

let ASP1AUX_LENGTH_EQ_3 = prove
 (`!xs:A list. LENGTH xs = 3 <=> ?a1 a2 a3. xs = [a1;a2;a3]`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

(* as ASP1AUX_state_rel_set_var, for code that also wrote the temporaries   *)
(* 1 and 3, the memory and NextFree, and consumed space                      *)
let ASP1AUX_state_rel_set_var_alloc = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w m' nf v1 v3
    (s2:(C,FFI)data_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     data_state_global s2 = data_state_global s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s2) (wl_state_store t |+ (NextFree,nf)) m' (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
         (wl_state_memory_fupd (K m')
           (wl_state_locals_fupd
             (K (insert (adjust_var dest) w (insert 3 v3 (insert 1 v1 (wl_state_locals t)))))
             t))) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def] THEN SIMP[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. ~(0 = adjust_var n) /\ ~(1 = adjust_var n) /\ ~(3 = adjust_var n)`
    ASSUME_TAC THENL [MESON_TAC[adjust_var_NEQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ; adjust_var_11; ARITH_EQ;
                  FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM;
                  distinctness "store_name"; code_oracle_rel_NextFree] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[option_le_trans];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    SIMP_TAC[inter_insert_ODD_adjust_set; ARITH] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

(* ASP1AUX: the shape of a successful data_do_install *)
let ASP1AUX_do_install_IMP = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_install vs s = (Rval (v,s2):(data_v#(C,FFI)data_state,data_v)result) ==>
     ?hv1 hv2 q1 q2 cfg progs k prog rest cfg'.
       vs = [hv1; hv2; data_Number (&(LENGTH q1)); data_Number (&(LENGTH q2))] /\
       data_v_to_bytes hv1 = SOME q1 /\ data_v_to_words hv2 = SOME q2 /\
       data_state_compile_oracle s 0 = (cfg,progs) /\
       progs = CONS (k,prog) rest /\
       data_state_compile s cfg progs = SOME (q1,q2,cfg') /\
       FST (shift_seq 1 (data_state_compile_oracle s) 0) = cfg' /\
       v = data_CodePtr k /\
       s2 = data_state_safe_for_space_fupd (K F)
              (data_state_code_fupd (K (sptree_union (data_state_code s) (fromAList progs)))
                 (data_state_compile_oracle_fupd
                    (K (shift_seq 1 (data_state_compile_oracle s))) s))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[data_do_install_def; LET_DEF; LET_END_DEF] THEN
   REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
   REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ]) THEN
  (STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
   MAP_EVERY EXISTS_TAC [`a0:data_v`; `a0':data_v`; `x':byte list`; `x'':int64 list`; `x:C`;
     `CONS (x''':num,y''':num#data_prog) a1`; `x''':num`; `y''':num#data_prog`;
     `a1:(num#num#data_prog)list`; `y'':C`] THEN
   ASM_REWRITE_TAC[]));;

(* ASP1AUX: the stub locations are below data_num_stubs *)
let ASP1AUX_MEM_stubs_lt = prove
 (`!c n. MEM n (MAP FST (data_to_word_stubs (:A) c)) ==> n < data_num_stubs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_stubs_def; generated_bignum_stubs_eq; MAP; APPEND; MEM] THEN
  REWRITE_TAC[FromList_location_eq; FromList1_location_eq; RefByte_location_eq;
    RefArray_location_eq; data_to_word_Replicate_location_eq; AnyArith_location_eq;
    data_to_word_Add_location_eq; data_to_word_Sub_location_eq; data_to_word_Mul_location_eq;
    data_to_word_Div_location_eq; data_to_word_Mod_location_eq;
    data_to_word_Compare1_location_eq; data_to_word_Compare_location_eq;
    data_to_word_Equal1_location_eq; data_to_word_Equal_location_eq; LongDiv1_location_eq;
    LongDiv_location_eq; MemCopy_location_eq; data_to_word_Bignum_location_eq;
    ByteCopy_location_eq; ByteCopyAdd_location_eq; ByteCopySub_location_eq;
    ByteCopyNew_location_eq; data_to_word_Install_location_eq; InstallCode_location_eq;
    InstallData_location_eq; data_to_word_Dummy_location_eq; data_to_word_Append_location_eq;
    AppendMainLoop_location_eq; AppendLenLoop_location_eq; XorLoop_location_eq;
    data_to_word_Unused_location_eq; StringCmpLoop_location_eq;
    data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV);;

(* ASP1AUX: ALOOKUP through MAP compile_part *)
let ASP1AUX_ALOOKUP_MAP_compile_part = prove
 (`!c (progs:(num#num#data_prog)list) n a p.
     ALOOKUP progs n = SOME (a,p) ==>
     ALOOKUP (MAP (data_to_word_compile_part c) progs) n =
       SOME (a + 1,FST (data_to_word_comp c n 2 p):(A)wl_prog)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; MAP; option_DISTINCT] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN
  SPEC_TAC(`h:num#num#data_prog`,`h:num#num#data_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `a':num`; `p':data_prog`] THEN
  REWRITE_TAC[data_to_word_compile_part_def; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ASP1AUX: code_rel is kept by installing new code above the stubs *)
let ASP1AUX_code_rel_union = prove
 (`!c (s_code:(num#data_prog)spt) (t_code:(num#(A)wl_prog)spt) progs.
     data_to_word_gcProof_code_rel c s_code t_code /\
     ALL (\(n,_). data_num_stubs <= n) progs ==>
     data_to_word_gcProof_code_rel c (sptree_union s_code (fromAList progs))
       (sptree_union t_code (fromAList (MAP (data_to_word_compile_part c) progs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_code_rel_def] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[domain_union; domain_fromAList; MAP_FST_MAP_compile_part] THEN SET_TAC[];
    UNDISCH_TAC `ALL (\(n,x). lookup n t_code = SOME x)
                   (data_to_word_stubs (:A) c:(num#num#(A)wl_prog)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP[lookup_union];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `ac:num`; `p:data_prog`] THEN
  REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  CASES_ON `lookup n (s_code:(num#data_prog)spt)` THEN CASE_REWRITE_TAC[option_INJ] THENL
   [DISCH_TAC THEN
    CASES_ON `lookup n (t_code:(num#(A)wl_prog)spt)` THEN CASE_REWRITE_TAC[option_INJ] THENL
     [MATCH_MP_TAC ASP1AUX_ALOOKUP_MAP_compile_part THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `n IN domain (t_code:(num#(A)wl_prog)spt)` MP_TAC THENL
     [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION; IN_SET_OF_LIST] THEN
    SUBGOAL_THEN `~(n IN domain (s_code:(num#data_prog)spt))` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[domain_lookup; option_DISTINCT]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ASP1AUX_MEM_stubs_lt) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM o check (is_eq o concl) o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "ALOOKUP"))
                       (concl th))) THEN
    UNDISCH_TAC `ALL (\(n,_). data_num_stubs <= n) (progs:(num#num#data_prog)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    SIMP[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `ac:num`; `p:data_prog`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

(* ASP1AUX: code_oracle_rel after flushing the code and data buffers *)
let ASP1AUX_code_oracle_rel_shift = prove
 (`!c (s_compile:C -> (num#num#data_prog)list -> (byte list#int64 list#C)option)
      s_co st (t_compile:C -> (num#num#(A)wl_prog)list -> (byte list#(A word)list#C)option)
      t_co (cb:(A,8)buffer) (db:(A,A)buffer) cb' db' n1 n2.
     code_oracle_rel c s_compile s_co st t_compile t_co cb db /\
     n1 <= buffer_space_left cb /\ n2 <= buffer_space_left db /\
     buffer_buffer cb' = [] /\
     buffer_position cb' = word_add (buffer_position cb) (word n1) /\
     buffer_space_left cb' = buffer_space_left cb - n1 /\
     buffer_buffer db' = [] /\
     buffer_position db' = word_add (buffer_position db) (word_mul bytes_in_word (word n2)) /\
     buffer_space_left db' = buffer_space_left db - n2 ==>
     code_oracle_rel c s_compile (shift_seq 1 s_co)
       (st |+ (BitmapBuffer,wl_Word (buffer_position db')) |+
              (CodeBuffer,wl_Word (buffer_position cb')))
       t_compile (shift_seq 1 t_co) cb' db'`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[code_oracle_rel_def] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name"; option_INJ;
                   injectivity "word_loc"] THEN
   ASM_SIMP_TAC[WORD_SUB] THEN REPEAT CONJ_TAC THENL
    [CONV_TAC WORD_RULE;
     CONV_TAC WORD_RULE;
     REWRITE_TAC[FUN_EQ_THM; shift_seq_def; o_THM];
     REWRITE_TAC[shift_seq_def] THEN ASM_REWRITE_TAC[]]));;

(* ASP1AUX: the call of InstallCode_code in assign_Install, up to its Return *)
let ASP1AUX_Install_callee = prove
 (`!c (t:(A,C,FFI)wl_state) hv1 hv2 q1 q2 w1 w2 l1 l2 vars sp refs ts cfg wk wprog wrest cfg'.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (hv1,w1) (CONS (hv2,w2) vars)) /\
     lookup InstallCode_location (wl_state_code t) = SOME (4,InstallCode_code c) /\
     lookup InstallData_location (wl_state_code t) = SOME (4,InstallData_code c) /\
     lookup Install_location (wl_state_code t) = SOME (3,Install_code c) /\
     FLOOKUP (wl_state_store t) BitmapBuffer =
       SOME (wl_Word (buffer_position (wl_state_data_buffer t))) /\
     FLOOKUP (wl_state_store t) CodeBuffer =
       SOME (wl_Word (buffer_position (wl_state_code_buffer t))) /\
     buffer_buffer (wl_state_code_buffer t) = [] /\
     buffer_buffer (wl_state_data_buffer t) = [] /\
     data_v_to_bytes hv1 = SOME q1 /\ data_v_to_words hv2 = SOME q2 /\
     LENGTH q1 <= buffer_space_left (wl_state_code_buffer t) /\
     LENGTH q2 <= buffer_space_left (wl_state_data_buffer t) /\
     LENGTH q1 + LENGTH q2 + 1 < wl_state_clock t /\
     wl_get_var 0 t = SOME (wl_Loc l1 l2) /\ wl_get_var 2 t = SOME w1 /\
     wl_get_var 4 t = SOME w2 /\
     wl_get_var 6 t = SOME (wl_Word (buffer_position (wl_state_code_buffer t))) /\
     wl_state_compile_oracle t 0 = (cfg,CONS (wk,wprog) wrest) /\
     wl_state_compile t cfg (CONS (wk,wprog) wrest) = SOME (q1,MAP w2w_upper q2,cfg') /\
     FST (shift_seq 1 (wl_state_compile_oracle t) 0) = cfg' /\
     good_dimindex (:A) ==>
     ?t'. wl_evaluate (InstallCode_code c,t) =
            (SOME (wl_Result (wl_Loc l1 l2) [wl_Loc wk 0]),t') /\
          wl_state_stack t' = wl_state_stack t /\
          wl_state_store t' =
            wl_state_store t |+
              (BitmapBuffer,wl_Word (word_add (buffer_position (wl_state_data_buffer t))
                                       (word_mul bytes_in_word (word (LENGTH q2))))) |+
              (CodeBuffer,wl_Word (word_add (buffer_position (wl_state_code_buffer t))
                                     (word (LENGTH q1)))) /\
          wl_state_code t' = sptree_union (wl_state_code t) (fromAList (CONS (wk,wprog) wrest)) /\
          buffer_position (wl_state_code_buffer t') =
            word_add (buffer_position (wl_state_code_buffer t)) (word (LENGTH q1)) /\
          buffer_buffer (wl_state_code_buffer t') = [] /\
          buffer_space_left (wl_state_code_buffer t') =
            buffer_space_left (wl_state_code_buffer t) - LENGTH q1 /\
          buffer_position (wl_state_data_buffer t') =
            word_add (buffer_position (wl_state_data_buffer t))
              (word_mul bytes_in_word (word (LENGTH q2))) /\
          buffer_buffer (wl_state_data_buffer t') = [] /\
          buffer_space_left (wl_state_data_buffer t') =
            buffer_space_left (wl_state_data_buffer t) - LENGTH q2 /\
          wl_state_compile_oracle t' = shift_seq 1 (wl_state_compile_oracle t) /\
          wl_state_stack_max t' = NONE /\ wl_state_stack_size t' = LN /\
          wl_state_memory t' = wl_state_memory t /\
          wl_state_mdomain t' = wl_state_mdomain t /\
          wl_state_be t' = wl_state_be t /\ wl_state_ffi t' = wl_state_ffi t /\
          wl_state_handler t' = wl_state_handler t /\
          wl_state_gc_fun t' = wl_state_gc_fun t /\
          wl_state_compile t' = wl_state_compile t /\
          wl_state_stack_limit t' = wl_state_stack_limit t`,
  (REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (MP_TAC(ISPECL [`t:(A,C,FFI)wl_state`; `c:data_to_word_config`; `hv1:data_v`; `q1:byte list`;
     `w1:A word_loc`; `w2:A word_loc`; `wl_Loc l1 l2:A word_loc`;
     `wl_Word (buffer_position (wl_state_data_buffer (t:(A,C,FFI)wl_state)))`;
     `CONS (hv2:data_v,w2:A word_loc) vars`; `sp:num`; `refs:((data_v)bvl_ref)spt`;
     `ts:num`] InstallCode_code_thm) THEN
   ASM_REWRITE_TAC[LENGTH; WORD_ADD_0] THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `lsz:num option` (X_CHOOSE_THEN `smx:num option` SUBST1_TAC))) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_swap) THEN
   (fun (asl,w as g) ->
     let tm = find_term (fun t -> try let f,p = dest_comb t in
                fst(dest_const f) = "wl_evaluate" &&
                (let prog,_ = dest_pair p in
                 fst(dest_const(fst(strip_comb prog))) = "InstallData_code")
              with Failure _ -> false) w in
     let tA = snd(dest_pair(rand tm)) in
     MP_TAC(ISPECL [tA; `c:data_to_word_config`; `hv2:data_v`; `q2:int64 list`;
       `wl_Word (word_add (buffer_position (wl_state_code_buffer (t:(A,C,FFI)wl_state)))
          (word (0 + LENGTH (q1:byte list))))`;
       `w2:A word_loc`; `wl_Loc l1 l2:A word_loc`; `CONS (hv1:data_v,w1:A word_loc) vars`;
       `sp:num`; `refs:((data_v)bvl_ref)spt`; `ts:num`] InstallData_code_thm) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_get_var_def; fromList2_def; lookup_insert; ARITH_EQ; LENGTH; WORD_MUL_0;
          WORD_ADD_0] THEN
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `smx2:num option` (X_CHOOSE_THEN `lsz2:num option` SUBST1_TAC))) THEN
  (REWRITE_TAC[data_to_word_Install_code_def; data_to_word_list_Seq_def]) THEN
  (REWRITE_TAC[wl_state_INFO.ri_accfupds; buffer_INFO.ri_accfupds; K_THM; APPEND; ADD_CLAUSES;
     LENGTH; WORD_MUL_0; WORD_ADD_0;
     ASSUME `buffer_buffer (wl_state_data_buffer (t:(A,C,FFI)wl_state)) = []`]) THEN
  (ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; wl_set_store_def; fromList2_def; distinctness "store_name"]) THEN
  (ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_get_var_def; lookup_insert; ARITH_EQ;
     wl_cut_env_def; cut_envs_def; cut_names_def; domain_def; domain_insert; INSERT_SUBSET;
     IN_INSERT; EMPTY_SUBSET; inter_LN; buffer_flush_def; DIMINDEX_8;
     ARITH_RULE `8 DIV 8 = 1`; WORD_RULE `word_mul (word 1) (x:B word) = x`;
     GSYM bytes_in_word_def; LENGTH_MAP; LET_DEF; LET_END_DEF]) THEN
  ((fun (asl,w as g) ->
     let tm = find_term (fun t -> try let f,p = dest_comb t in
                fst(dest_const f) = "wl_evaluate" &&
                (let prog,_ = dest_pair p in
                 fst(dest_const(fst(strip_comb prog))) = "wl_Return")
              with Failure _ -> false) w in
     let st = snd(dest_pair(rand tm)) in
     EXISTS_TAC (mk_comb(`wl_flush_state F:(A,C,FFI)wl_state->(A,C,FFI)wl_state`, st)) g) THEN
   SIMP[wl_evaluate_def; wl_get_var_def; wl_get_vars_def; lookup_insert; ARITH_EQ;
        lookup_inter_alt; domain_def; IN_SING; wl_flush_state_def]));;

(* ASP1AUX: the state relation after assign_Install, from the components *)
let ASP1AUX_Install_state_rel = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) (r:(A,C,FFI)wl_state) locs y dest k
      cfg progs (q1:byte list) (q2:int64 list).
     data_to_word_gcProof_state_rel c l1 l2 x (wl_state_locals_fupd (K y) t) NONE locs /\
     data_state_compile_oracle x 0 = (cfg,progs) /\
     LENGTH q1 <= buffer_space_left (wl_state_code_buffer t) /\
     LENGTH q2 <= buffer_space_left (wl_state_data_buffer t) /\
     wl_state_locals r = insert (adjust_var dest) (wl_Loc k 0) y /\
     wl_state_store r = wl_state_store t |+
       (BitmapBuffer,wl_Word (word_add (buffer_position (wl_state_data_buffer t))
                                (word_mul bytes_in_word (word (LENGTH q2))))) |+
       (CodeBuffer,wl_Word (word_add (buffer_position (wl_state_code_buffer t))
                              (word (LENGTH q1)))) /\
     wl_state_code r =
       sptree_union (wl_state_code t) (fromAList (MAP (data_to_word_compile_part c) progs)) /\
     buffer_position (wl_state_code_buffer r) =
       word_add (buffer_position (wl_state_code_buffer t)) (word (LENGTH q1)) /\
     buffer_buffer (wl_state_code_buffer r) = [] /\
     buffer_space_left (wl_state_code_buffer r) =
       buffer_space_left (wl_state_code_buffer t) - LENGTH q1 /\
     buffer_position (wl_state_data_buffer r) =
       word_add (buffer_position (wl_state_data_buffer t))
         (word_mul bytes_in_word (word (LENGTH q2))) /\
     buffer_buffer (wl_state_data_buffer r) = [] /\
     buffer_space_left (wl_state_data_buffer r) =
       buffer_space_left (wl_state_data_buffer t) - LENGTH q2 /\
     wl_state_compile_oracle r = shift_seq 1 (wl_state_compile_oracle t) /\
     wl_state_stack_max r = NONE /\ wl_state_stack_size r = LN /\
     wl_state_stack r = wl_state_stack t /\
     wl_state_locals_size r = wl_state_locals_size t /\
     wl_state_clock r = wl_state_clock t /\
     wl_state_memory r = wl_state_memory t /\ wl_state_mdomain r = wl_state_mdomain t /\
     wl_state_be r = wl_state_be t /\ wl_state_ffi r = wl_state_ffi t /\
     wl_state_handler r = wl_state_handler t /\ wl_state_gc_fun r = wl_state_gc_fun t /\
     wl_state_compile r = wl_state_compile t /\
     wl_state_stack_limit r = wl_state_stack_limit t ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest (data_CodePtr k)
          (data_state_safe_for_space_fupd (K F)
             (data_state_code_fupd (K (sptree_union (data_state_code x) (fromAList progs)))
                (data_state_compile_oracle_fupd
                   (K (shift_seq 1 (data_state_compile_oracle x)))
                   (data_state_stack_max_fupd (K NONE)
                      (data_state_stack_frame_sizes_fupd (K LN) x))))))
       r NONE locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                  (wl_state_locals_fupd (K y) (t:(A,C,FFI)wl_state)) NONE locs` THEN
   REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def] THEN
   ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `ALL (\(n,_). data_num_stubs <= n) (progs:(num#num#data_prog)list)` ASSUME_TAC
   THENL
    [UNDISCH_TAC `code_oracle_rel c (data_state_compile (x:(C,FFI)data_state))
       (data_state_compile_oracle x) (wl_state_store (t:(A,C,FFI)wl_state))
       (wl_state_compile t) (wl_state_compile_oracle t) (wl_state_code_buffer t)
       (wl_state_data_buffer t)` THEN
     REWRITE_TAC[code_oracle_rel_def] THEN
     DISCH_THEN(MP_TAC o SPEC `0` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC ASP1AUX_code_rel_union THEN ASM_REWRITE_TAC[];
     MP_TAC(ISPECL [`c:data_to_word_config`; `data_state_compile (x:(C,FFI)data_state)`;
       `data_state_compile_oracle (x:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
       `wl_state_compile (t:(A,C,FFI)wl_state)`; `wl_state_compile_oracle (t:(A,C,FFI)wl_state)`;
       `wl_state_code_buffer (t:(A,C,FFI)wl_state)`; `wl_state_data_buffer (t:(A,C,FFI)wl_state)`;
       `wl_state_code_buffer (r:(A,C,FFI)wl_state)`; `wl_state_data_buffer (r:(A,C,FFI)wl_state)`;
       `LENGTH (q1:byte list)`; `LENGTH (q2:int64 list)`] ASP1AUX_code_oracle_rel_shift) THEN
     ASM_REWRITE_TAC[];
     UNDISCH_TAC `ALL (\n. n IN FDOM (wl_state_store (t:(A,C,FFI)wl_state))) [Globals]` THEN
     REWRITE_TAC[ALL; FDOM_FUPDATE; IN_INSERT] THEN SIMP[];
     ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ_0];
     GEN_TAC THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
     REWRITE_TAC[option_le_def];
     REWRITE_TAC[option_le_def];
     ASM_REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name"];
     ALL_TAC]) THEN
  (REWRITE_TAC[memory_rel_ignore_buffers; FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
   MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
   MATCH_MP_TAC memory_rel_CodePtr THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
     fst(dest_const t) = "memory_rel")) (concl th))) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]));;

(* ASP1AUX: state_rel with the locals set to themselves *)
let ASP1AUX_state_rel_locals_id = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s
       (wl_state_locals_fupd (K (wl_state_locals t)) t) v locs <=>
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `wl_state_locals_fupd (K (wl_state_locals t)) t = (t:(A,C,FFI)wl_state)`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

(* ASP1AUX: odd word variables do not matter for state_rel *)
let ASP1AUX_state_rel_insert_odd = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs k (w:A word_loc) l.
     ODD k ==>
     (data_to_word_gcProof_state_rel c l1 l2 s
        (wl_state_locals_fupd (K (insert k w l)) t) v locs <=>
      data_to_word_gcProof_state_rel c l1 l2 s (wl_state_locals_fupd (K l) t) v locs)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(0 = k) /\ (!n. ~(adjust_var n = k))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EVEN_adjust_var; NOT_EVEN; ODD]; ALL_TAC] THEN
  SIMP[data_to_word_gcProof_state_rel_thm; lookup_insert;
           inter_insert_ODD_adjust_set_alt]);;

(* ASP1AUX: case split on the condition of the first step of a Seq chain *)
let ASP1AUX_COND_CASES_TAC thl : tactic = fun (asl,w as g) ->
  let is_seq_eval t =
    try let f,p = dest_comb t in
        fst(dest_const f) = "wl_evaluate" &&
        (let prog,_ = dest_pair p in
         fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
    with Failure _ -> false in
  let t = find_term is_seq_eval w in
  let f,p = dest_comb t in
  let prog,s = dest_pair p in
  let c1 = rand(rator prog) in
  let tm = mk_comb(f,mk_pair(c1,s)) in
  let th = CAKE_SIMP_CONV (thl @ map snd asl) tm in
  let r = rhs(concl th) in
  if is_cond r then ASM_CASES_TAC (fst(dest_cond r)) g
  else failwith "ASP1AUX_COND_CASES_TAC: not a conditional";;

(* ASP1AUX: the word level compile result from the data level one *)
let ASP1AUX_compile_SOME = prove
 (`!c (t_compile:C -> (num#num#(A)wl_prog)list -> (byte list#(A word)list#C)option)
      cfg progs q1 q2 cfg'.
     good_dimindex(:A) /\
     OPTION_MAP (I ## MAP upper_w2w ## I)
       (t_compile cfg (MAP (data_to_word_compile_part c) progs)) = SOME (q1,q2,cfg') ==>
     t_compile cfg (MAP (data_to_word_compile_part c) progs) =
       SOME (q1,MAP w2w_upper q2,cfg')`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`(t_compile:C -> (num#num#(A)wl_prog)list -> (byte list#(A word)list#C)option)
              cfg (MAP (data_to_word_compile_part c) progs)`,
           `r:(byte list#(A word)list#C)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; OPTION_MAP_DEF; option_DISTINCT;
              option_INJ; PAIR_MAP_THM; PAIR_EQ; I_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "upper_w2w")) (concl th))) THEN
  ASM_SIMP_TAC[w2w_upper_upper_w2w]);;

(* ASP1AUX: arithmetic for the buffer space checks of assign_Install *)
let ASP1AUX_MUL_MOD_DIV_LE = prove
 (`!a m N. ~(a = 0) ==> ((a * (m MOD N)) MOD N) DIV a <= m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(a * (m MOD N)) DIV a` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN REWRITE_TAC[MOD_LE];
    ASM_SIMP_TAC[DIV_MULT; MOD_LE]]);;

let ASP1AUX_word_ult_le = prove
 (`!n L. L < dimword(:A) /\ ~(word_ult (word n) (word L:A word)) ==> L <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ULT; VAL_WORD; GSYM dimword_def] THEN
  STRIP_TAC THEN UNDISCH_TAC `~(n MOD dimword(:A) < L MOD dimword(:A))` THEN
  ASM_SIMP_TAC[MOD_LT] THEN MP_TAC(SPECL [`n:num`; `dimword(:A)`] MOD_LE) THEN ARITH_TAC);;

let ASP1AUX_ushr_bytes_le = prove
 (`!n L. good_dimindex(:A) /\ L < dimword(:A) /\
         ~(word_ult (word_ushr (word_mul bytes_in_word (word n))
                       (backend_common_word_shift(:A))) (word L:A word)) ==> L <= n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_ULT; VAL_WORD_USHR; VAL_WORD_MUL; bytes_in_word_def; VAL_WORD;
              backend_common_word_shift_def; GSYM dimword_def] THEN
  STRIP_TAC THEN UNDISCH_TAC `~(((dimindex (:A) DIV 8) MOD dimword (:A) *
                                 n MOD dimword (:A)) MOD dimword (:A) DIV
                                2 EXP (if dimindex (:A) = 32 then 2 else 3) <
                                L MOD dimword (:A))` THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(ARITH_RULE `x <= n ==> ~(x < L) ==> L <= n`) THEN
  MATCH_MP_TAC ASP1AUX_MUL_MOD_DIV_LE THEN CONV_TAC NUM_REDUCE_CONV);;

(* ASP1AUX: the locals restored by pop_env after a call with cut_envs *)
let ASP1AUX_union_fromAList_env = prove
 (`!(y1:(A word_loc)spt) y2 p q r.
     sptree_wf y1 /\ sptree_wf y2 /\ env_to_list y2 p = (q,r) ==>
     sptree_union (fromAList q) (fromAList (toAList y1)) = sptree_union y2 y1`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  MP_TAC(ISPECL [`sptree_union (fromAList q) (fromAList (toAList (y1:(A word_loc)spt)))`;
                 `sptree_union (y2:(A word_loc)spt) y1`] spt_eq_thm) THEN
  ASM_SIMP_TAC[wf_union; wf_fromAList] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[lookup_union; lookup_fromAList; ALOOKUP_toAList]);;

(* HOL4 line 2451 *)
let assign_Install = prove
 (assign_thm_stmt `(op = clos_Install)`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `?kept_names. names_opt = SOME (kept_names:num_set)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `~(op_requires_names clos_Install <=> names_opt = (NONE:num_set option))` THEN
     REWRITE_TAC[op_requires_names_def] THEN MESON_TAC[cases "option"];
     ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`;
     `kept_names:num_set`; `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
     STRIP_ASSUME_TAC))) THEN
  (UNDISCH_TAC `data_do_app clos_Install vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
   REWRITE_TAC[data_do_app_def] THEN
   DISCH_THEN(MP_TAC o MATCH_MP ASP1AUX_do_install_IMP) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `?v1 v2 v3 v4:num. args = [v1;v2;v3;v4]` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[GSYM(CONJUNCT1(SPEC_ALL LENGTH_EQ_4))] THEN
     ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   SUBGOAL_THEN `?w1 w2 tw3 tw4:A word_loc. ws = [w1;w2;tw3;tw4]` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `LENGTH [v1;v2;v3;v4:num] = LENGTH (ws:(A word_loc)list)` THEN
     REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[LENGTH_EQ_4]; ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> fst(dest_var(lhs(concl th))) = "vals"))) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel o
     check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                                    (t:(A,C,FFI)wl_state) NONE locs`)) THEN
   DISCH_THEN(MP_TAC o MATCH_MP memory_rel_lookup_var_IMP o
     C CONJ (CONJ (ASSUME `data_get_vars [v1;v2;v3;v4] (data_state_locals (s:(C,FFI)data_state)) =
                     SOME [hv1; hv2; data_Number (&(LENGTH (q1:byte list)));
                           data_Number (&(LENGTH (q2:int64 list)))]`)
                  (ASSUME `wl_get_vars (MAP adjust_var [v1;v2;v3;v4]) (t:(A,C,FFI)wl_state) =
                     SOME [w1;w2;tw3;tw4]`))) THEN
   REWRITE_TAC[ZIP; APPEND] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[get_vars_SOME_IFF_data; get_vars_SOME_IFF; MAP]) THEN
   MP_TAC(ISPECL [`v3:num`; `&(LENGTH (q1:byte list)):int`; `c:data_to_word_config`; `l1:num`;
     `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`;
     `tw3:A word_loc`] state_rel_get_var_Number_IMP_alt) THEN
   ASM_REWRITE_TAC[GSYM adjust_var_def] THEN
   DISCH_THEN(X_CHOOSE_THEN `w3:A word` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`v4:num`; `&(LENGTH (q2:int64 list)):int`; `c:data_to_word_config`; `l1:num`;
     `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`;
     `tw4:A word_loc`] state_rel_get_var_Number_IMP_alt) THEN
   ASM_REWRITE_TAC[GSYM adjust_var_def] THEN
   DISCH_THEN(X_CHOOSE_THEN `w4:A word` STRIP_ASSUME_TAC) THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> let l = lhs(concl th) in
     is_var l && (fst(dest_var l) = "tw3" || fst(dest_var l) = "tw4"))))) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> fst(dest_var(lhs(concl th))) = "s2")) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> fst(dest_var(lhs(concl th))) = "v")) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; option_le_def]) THEN
  (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[arg4_def; assign_Install_def; data_to_word_list_Seq_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST]) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `adjust_var v3`; `w3:A word`]
     evaluate_BignumHalt) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r3:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
   ASM_CASES_TAC `small_int (:A) (&(LENGTH (q1:byte list)))` THENL
    [ALL_TAC;
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r3:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC ASP1AUX_Seq_halt THEN ASM_REWRITE_TAC[]] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
     fst(dest_const t) = "BignumHalt")) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th])) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `adjust_var v4`; `w4:A word`]
     evaluate_BignumHalt) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r4:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
   ASM_CASES_TAC `small_int (:A) (&(LENGTH (q2:int64 list)))` THENL
    [ALL_TAC;
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r4:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC ASP1AUX_Seq_halt THEN ASM_REWRITE_TAC[]] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
     fst(dest_const t) = "BignumHalt")) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th])) THEN
  (SUBGOAL_THEN `!n. Smallnum (&n) = word (4 * n):A word` ASSUME_TAC THENL
    [REWRITE_TAC[data_to_word_Smallnum_def; INT_OF_NUM_LT; LT; INT_OF_NUM_MUL;
                 NUM_OF_INT_OF_NUM];
     ALL_TAC] THEN
   SUBGOAL_THEN `(w3:A word) = word (4 * LENGTH (q1:byte list)) /\
                 (w4:A word) = word (4 * LENGTH (q2:int64 list))` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
         `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`;
         `v3:num`; `LENGTH (q1:byte list)`] state_rel_get_var_Number_IMP);
       MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
         `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`;
         `v4:num`; `LENGTH (q2:int64 list)`] state_rel_get_var_Number_IMP)] THEN
     ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"];
     ALL_TAC] THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> let l = lhs(concl th) in
     is_var l && (fst(dest_var l) = "w3" || fst(dest_var l) = "w4"))))) THEN
  (SUBGOAL_THEN `4 * LENGTH (q1:byte list) < dimword(:A) /\
                 4 * LENGTH (q2:int64 list) < dimword(:A)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `small_int (:A) (&(LENGTH (q1:byte list)))` THEN
     UNDISCH_TAC `small_int (:A) (&(LENGTH (q2:int64 list)))` THEN
     REWRITE_TAC[small_int_def; INT_OF_NUM_LT] THEN
     MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN
     REWRITE_TAC[ARITH_EQ] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `word_ushr (word (4 * LENGTH (q1:byte list))) 2 = (word (LENGTH q1):A word) /\
                 word_ushr (word (4 * LENGTH (q2:int64 list))) 2 = (word (LENGTH q2):A word)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_USHR; VAL_WORD] THEN
     REWRITE_TAC[GSYM dimword_def] THEN
     ASM_SIMP_TAC[MOD_LT; ARITH_RULE `4 * n < d ==> n < d`] THEN
     CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DIV_MULT; ARITH_EQ];
     ALL_TAC]) THEN
  (FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
     check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                                    (t:(A,C,FFI)wl_state) NONE locs`)) THEN
   DISCH_THEN(fun th ->
     let cs = CONJUNCTS th in
     let pick name = find (fun c -> try fst(dest_const(fst(strip_comb(concl c)))) = name
                                    with Failure _ -> false) cs in
     let sl = find (fun c -> concl c = `shift_length c < dimindex(:A)`) cs in
     MP_TAC (pick "code_oracle_rel") THEN
     ASSUME_TAC (pick "data_to_word_gcProof_code_rel") THEN
     ASSUME_TAC (pick "good_dimindex") THEN ASSUME_TAC sl) THEN
   REWRITE_TAC[code_oracle_rel_def] THEN STRIP_TAC) THEN
  (MP_TAC(ISPEC `prog:num#data_prog` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `pa:num` (X_CHOOSE_THEN `pp:data_prog` SUBST_ALL_TAC)) THEN
   SUBGOAL_THEN `wl_state_compile_oracle (t:(A,C,FFI)wl_state) 0 =
                   (cfg,MAP (data_to_word_compile_part c) progs) /\
                 FST (shift_seq 1 (wl_state_compile_oracle (t:(A,C,FFI)wl_state)) 0) = cfg'`
     STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC[o_THM; PAIR_MAP_THM; I_THM] THEN
     UNDISCH_TAC `FST (shift_seq 1 (data_state_compile_oracle (x:(C,FFI)data_state)) 0) = cfg'` THEN
     REWRITE_TAC[shift_seq_def; o_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
     MP_TAC(ISPEC `data_state_compile_oracle (x:(C,FFI)data_state) 1` PAIR_SURJECTIVE) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_MAP_THM; FST; I_THM];
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_state_compile (t:(A,C,FFI)wl_state) cfg
                   (MAP (data_to_word_compile_part c) progs) =
                 SOME (q1,MAP w2w_upper q2,cfg')` ASSUME_TAC THENL
    [MATCH_MP_TAC ASP1AUX_compile_SOME THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `data_state_compile (x:(C,FFI)data_state) cfg progs = SOME (q1,q2,cfg')` THEN
     ASM_REWRITE_TAC[o_THM];
     ALL_TAC] THEN
   REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> let tm = concl th in
     is_eq tm && (let l = lhs tm in
       l = `data_state_compile (x:(C,FFI)data_state)` ||
       l = `wl_state_compile_oracle (t:(A,C,FFI)wl_state)`)))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> fst(dest_var(lhs(concl th))) = "progs")) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MAP; data_to_word_compile_part_def])) THEN
  (SUBGOAL_THEN `~(backend_common_word_shift(:A) = 0) /\
                 ~(backend_common_word_shift(:A) >= dimindex(:A)) /\
                 ~(2 >= dimindex(:A)) /\ val(word 2:A word) = 2 /\
                 val(word (backend_common_word_shift(:A)):A word) =
                   backend_common_word_shift(:A) /\
                 ~(dimindex(:A) <= 2) /\ ~(dimindex(:A) <= backend_common_word_shift(:A))`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `good_dimindex(:A)` THEN
     REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; VAL_WORD; dimword_def] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   SUBGOAL_THEN `!v. ShiftVar Lsr v 2 = wl_Shift Lsr (wl_Var v) (wl_Const (word 2)):(A)wl_exp`
     (fun th -> REWRITE_TAC[th]) THENL
    [ASM_REWRITE_TAC[ShiftVar_def; distinctness "shift"; ARITH_EQ]; ALL_TAC] THEN
   SUBGOAL_THEN `ShiftVar Lsr 3 (backend_common_word_shift(:A)) =
                 wl_Shift Lsr (wl_Var 3) (wl_Const (word (backend_common_word_shift(:A)))):(A)wl_exp`
     SUBST1_TAC THENL
    [ASM_REWRITE_TAC[ShiftVar_def; distinctness "shift"]; ALL_TAC]) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; adjust_var_NEQ; WORD_RULE `word_sub (word_add (a:A word) b) a = b`]) THEN
  (SUBGOAL_THEN `data_state_ffi (x:(C,FFI)data_state) = data_state_ffi (s:(C,FFI)data_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
       check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                                      (t:(A,C,FFI)wl_state) NONE locs`)) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[];
     ALL_TAC]) THEN
  (ASP1AUX_COND_CASES_TAC [wl_evaluate_def; word_exp_rw; wl_get_var_def; lookup_insert;
     ARITH_EQ; wl_word_cmp_def] THENL
    [(fun (asl,w as g) ->
       let tm = find_term (fun t -> try let f,p = dest_comb t in
                  fst(dest_const f) = "wl_evaluate" &&
                  (let prog,_ = dest_pair p in
                   fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
                with Failure _ -> false) w in
       let s5 = snd(dest_pair(rand tm)) in
       MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `x:(C,FFI)data_state`; s5;
                      `locs:(num#num)list`] evaluate_GiveUp) g) THEN
     ANTS_TAC THENL
      [SIMP[ASP1AUX_state_rel_insert_odd; ARITH; ASP1AUX_state_rel_locals_id]; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `r5:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r5:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC ASP1AUX_Seq_halt THEN
     SIMP[wl_evaluate_def; word_exp_rw; wl_get_var_def; lookup_insert; ARITH_EQ; wl_word_cmp_def];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (q2:int64 list) <= buffer_space_left (wl_state_data_buffer (t:(A,C,FFI)wl_state))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC ASP1AUX_ushr_bytes_le THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `4 * LENGTH (q2:int64 list) < dimword(:A)` THEN ARITH_TAC;
     ALL_TAC] THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; adjust_var_NEQ; wl_word_cmp_def;
     WORD_RULE `word_sub (word_add (a:A word) b) a = b`]) THEN
  (ASP1AUX_COND_CASES_TAC [wl_evaluate_def; word_exp_rw; wl_get_var_def; lookup_insert;
     ARITH_EQ; wl_word_cmp_def] THENL
    [(fun (asl,w as g) ->
       let tm = find_term (fun t -> try let f,p = dest_comb t in
                  fst(dest_const f) = "wl_evaluate" &&
                  (let prog,_ = dest_pair p in
                   fst(dest_const(fst(strip_comb prog))) = "wl_Seq")
                with Failure _ -> false) w in
       let s5 = snd(dest_pair(rand tm)) in
       MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `x:(C,FFI)data_state`; s5;
                      `locs:(num#num)list`] evaluate_GiveUp) g) THEN
     ANTS_TAC THENL
      [SIMP[ASP1AUX_state_rel_insert_odd; ARITH; ASP1AUX_state_rel_locals_id]; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `r5:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r5:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC ASP1AUX_Seq_halt THEN
     SIMP[wl_evaluate_def; word_exp_rw; wl_get_var_def; lookup_insert; ARITH_EQ; wl_word_cmp_def];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (q1:byte list) <= buffer_space_left (wl_state_code_buffer (t:(A,C,FFI)wl_state))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC ASP1AUX_word_ult_le THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `4 * LENGTH (q1:byte list) < dimword(:A)` THEN ARITH_TAC;
     ALL_TAC] THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def; wl_get_var_def;
     lookup_insert; ARITH_EQ; adjust_var_NEQ; wl_word_cmp_def]) THEN
  (SUBGOAL_THEN `lookup InstallCode_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                   SOME (4,InstallCode_code c) /\
                 lookup InstallData_location (wl_state_code t) = SOME (4,InstallData_code c) /\
                 lookup Install_location (wl_state_code t) = SOME (3,Install_code c)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `data_to_word_gcProof_code_rel c (data_state_code (x:(C,FFI)data_state))
                    (wl_state_code (t:(A,C,FFI)wl_state))` THEN
     REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def; ALL_APPEND; ALL] THEN
     CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
     STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs o
     check (fun th -> concl th = `wl_cut_env (adjust_sets (kept_names:num_set))
                                    (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME y`)) THEN
   SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0) /\
                 ~(MustTerminate_limit (:A) = 0)` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC;
       REWRITE_TAC[MustTerminate_limit_def] THEN
       MP_TAC(INST_TYPE [`:A`,`:N`] ZERO_LT_dimword) THEN ARITH_TAC];
     ALL_TAC]) THEN
  ((fun (asl,w as g) ->
     let tm = find_term (fun t -> is_comb t && (try fst(dest_const(fst(strip_comb t))) =
                "data_set_var" with Failure _ -> false)) w in
     ABBREV_TAC (mk_eq(`s3:(C,FFI)data_state`, tm)) g) THEN
   MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `eq:(num#(A)word_loc)list` (X_CHOOSE_THEN `ep:num->num->num`
     ASSUME_TAC)) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_envs_wf o
     check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "cut_envs"))
                      (concl th))) THEN
   MP_TAC(ISPECL [`y1:(A word_loc)spt`; `y2:(A word_loc)spt`;
     `wl_state_permute (t:(A,C,FFI)wl_state)`; `eq:(num#(A)word_loc)list`;
     `ep:num->num->num`] ASP1AUX_union_fromAList_env) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `FST (adjust_sets (kept_names:num_set)) = LS one` ASSUME_TAC THENL
    [REWRITE_TAC[adjust_sets_def]; ALL_TAC]) THEN
  (SIMP[wl_evaluate_def; wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ; adjust_var_NEQ;
        bad_dest_args_def; wl_find_code_def; add_ret_loc_def; LENGTH; option_DISTINCT;
        data_to_word_get_names_def; domain_def; NOT_INSERT_EMPTY;
        ALL_DISTINCT; MEM; cut_envs_adjust_sets_ODD; ARITH]) THEN
  ((fun (asl,w as g) ->
     let t88 = find_term (fun t -> is_comb t && (try fst(dest_const(fst(strip_comb t))) =
                 "wl_call_env" with Failure _ -> false)) w in
     let mr = find (fun th -> let tm = concl th in
                 (try fst(dest_const(fst(strip_comb tm))) = "memory_rel" with Failure _ -> false) &&
                 can (find_term ((=) `hv1:data_v`)) tm) (map snd asl) in
     let args = snd(strip_comb(concl mr)) in
     let lst = last args in
     let rest = rand(rand lst) in
     MP_TAC(ISPECL [`c:data_to_word_config`; t88; `hv1:data_v`; `hv2:data_v`; `q1:byte list`;
       `q2:int64 list`; `w1:A word_loc`; `w2:A word_loc`; `n:num`; `l:num`; rest;
       el 4 args; el 3 args; el 2 args; `cfg:C`; `k:num`;
       `(pa + 1,FST (data_to_word_comp c k 2 pp)):num#(A)wl_prog`;
       `MAP (data_to_word_compile_part c) (rest:(num#num#data_prog)list):(num#num#(A)wl_prog)list`;
       `cfg':C`] ASP1AUX_Install_callee) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_call_env_def; wl_push_env_def; wl_dec_clock_def; wl_get_var_def; fromList2_def;
          lookup_insert; ARITH_EQ; MAP; data_to_word_compile_part_def] THEN
     SUBGOAL_THEN `2 * dimword(:A) <= MustTerminate_limit(:A)` MP_TAC THENL
      [REWRITE_TAC[MustTerminate_limit_def] THEN ARITH_TAC; ALL_TAC] THEN
     MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN
     MAP_EVERY UNDISCH_TAC [`4 * LENGTH (q1:byte list) < dimword(:A)`;
                            `4 * LENGTH (q2:int64 list) < dimword(:A)`] THEN
     ARITH_TAC;
     ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t9:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> can (find_term (fun t ->
     is_const t && fst(dest_const t) = "InstallCode_code")) (lhs(concl th)))) THEN
   SUBGOAL_THEN `domain (sptree_union (y2:(A word_loc)spt) y1) = domain y1 UNION domain y2`
     ASSUME_TAC THENL [REWRITE_TAC[domain_union] THEN SET_TAC[]; ALL_TAC] THEN
   SIMP[injectivity "wl_result"; LENGTH; wl_pop_env_def; wl_push_env_def; wl_call_env_def;
        wl_dec_clock_def; LET_DEF; LET_END_DEF; wl_set_vars_def; alist_insert_def;
        option_DISTINCT; distinctness "option"]) THEN
  (FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `s3:(C,FFI)data_state`)) THEN
   (fun (asl,w as g) ->
      let rr = el 4 (snd(strip_comb w)) in
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `x:(C,FFI)data_state`;
        `t:(A,C,FFI)wl_state`; rr; `locs:(num#num)list`; `y:(A word_loc)spt`; `dest:num`;
        `k:num`; `cfg:C`; `CONS (k,pa,pp) (rest:(num#num#data_prog)list)`; `q1:byte list`;
        `q2:int64 list`] ASP1AUX_Install_state_rel) g) THEN
   ANTS_TAC THENL
    [SIMP[wl_call_env_def; wl_push_env_def; wl_dec_clock_def; LET_DEF; LET_END_DEF; MAP;
          data_to_word_compile_part_def];
     REWRITE_TAC[]]));;

(* HOL4 line 2747 *)
let assign_MutCons = prove
 (assign_thm_stmt `(?t k. op = MemOp (MutCons t k))`,
  (REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `k:num` SUBST1_TAC)) THEN
   STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[distinctness "clos_op"; injectivity "clos_op";
     distinctness "mem_op"]) THEN
   VAR_EQ_TAC THEN
   UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
   REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_GiveUp2) THEN
   SUBGOAL_THEN `~data_state_safe_for_space (s2:(C,FFI)data_state)` ASSUME_TAC THENL
    [DISCH_TAC THEN
     MP_TAC(ISPECL [`MemOp (MutCons tag k)`; `vals:data_v list`; `s:(C,FFI)data_state`;
                    `v:data_v`; `s2:(C,FFI)data_state`] do_app_safe_for_space_allowed_op) THEN
     ASM_REWRITE_TAC[allowed_op_def; injectivity "clos_op"; injectivity "mem_op"] THEN
     MESON_TAC[];
     ALL_TAC]) THEN
  (UNDISCH_TAC `data_do_app (MemOp (MutCons tag k)) vals (s:(C,FFI)data_state) = Rval (v,s2)` THEN
   REWRITE_TAC[data_do_app_def; distinctness "clos_op"; MEM; injectivity "clos_op"; do_space_def;
     op_space_reset_def; op_space_req_def; distinctness "mem_op"] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
  (REWRITE_TAC[ARITH_RULE `~(n + 1 = 0)`; consume_space_def] THEN
   COND_CASES_TAC THEN CASE_REWRITE_TAC[distinctness "result"] THEN
   REWRITE_TAC[data_do_app_aux_def] THEN
   CASE_REWRITE_TAC[distinctness "clos_op"; injectivity "clos_op"; distinctness "mem_op";
                    injectivity "mem_op"] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)) THEN
  (SUBGOAL_THEN `option_le (data_state_stack_max (s:(C,FFI)data_state))
                   (data_state_stack_max (s2:(C,FFI)data_state)) /\
                 data_state_refs s2 =
                   insert (minimal ptr. ~(ptr IN domain (data_state_refs s)))
                     (MutBlock tag F (TAKE k vals) (EL k vals) (DROP (k + 1) vals))
                     (data_state_refs s) /\
                 data_state_space s2 = data_state_space s - (LENGTH vals + 1) /\
                 data_state_ffi s2 = data_state_ffi s /\
                 data_state_clock s2 = data_state_clock s /\
                 data_state_handler s2 = data_state_handler s /\
                 data_state_code s2 = data_state_code s /\
                 data_state_compile s2 = data_state_compile s /\
                 data_state_compile_oracle s2 = data_state_compile_oracle s /\
                 data_state_locals s2 = data_state_locals s /\
                 data_state_stack s2 = data_state_stack s /\
                 data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
                 data_state_locals_size s2 = data_state_locals_size s /\
                 data_state_limits s2 = data_state_limits s /\
                 data_state_global s2 = data_state_global s /\
                 data_state_tstamps s2 = data_state_tstamps s`
     STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     SIMP[do_stack_def; LET_DEF; LET_END_DEF; option_le_max_right; option_le_refl];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `option_le (wl_state_stack_max (r:(A,C,FFI)wl_state))
                   (data_state_stack_max (s2:(C,FFI)data_state))` ASSUME_TAC THENL
    [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm];
     ALL_TAC] THEN
   REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_MutCons_def] THEN
   CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC; ALL_TAC;
     EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]]) THEN
  (REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds;
               K_THM] THEN
   ABBREV_TAC `new = minimal ptr. ~(ptr IN domain (data_state_refs (s:(C,FFI)data_state)))` THEN
   SUBGOAL_THEN `~(new IN domain (data_state_refs (s:(C,FFI)data_state)))` ASSUME_TAC THENL
    [EXPAND_TAC "new" THEN REWRITE_TAC[LEAST_NOTIN_spt_DOMAIN]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (args:num list) = LENGTH (vals:data_v list)` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH]; ALL_TAC] THEN
   REWRITE_TAC[assign_Cons_def] THEN
   SUBGOAL_THEN `~(LENGTH (args:num list) = 0)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   CASES_ON `encode_header c (4 * tag) (LENGTH (args:num list)):(A word)option` THEN
   CASE_REWRITE_TAC[] THENL
    [EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
     EXISTS_TAC `r:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm];
     ALL_TAC]) THEN
  (FIRST_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) = SOME vals`) o
     MATCH_MP state_rel_get_vars_IMP) THEN
   DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
   DRULE_ALL memory_rel_get_vars_IMP THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_TAC THEN
   SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
   SUBGOAL_THEN `shift_length c < dimindex(:A)` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
   DRULE memory_rel_MutCons) THEN
  (DISCH_THEN(MP_TAC o SPECL [`tag:num`; `a:A word`; `k:num`; `new:num`]) THEN
   SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = LENGTH (args:num list)` (fun th -> REWRITE_TAC[th])
   THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[ASSUME `LENGTH (args:num list) = LENGTH (vals:data_v list)`;
     ASSUME `good_dimindex(:A)`; ASSUME `~(new IN domain (data_state_refs (s:(C,FFI)data_state)))`;
     distinctness "gc_kind"] THEN
   SUBGOAL_THEN `!gs. ~(data_to_word_config_gc_kind c = Generational gs)`
     (fun th -> REWRITE_TAC[th]) THENL
    [ASM_REWRITE_TAC[distinctness "gc_kind"]; ALL_TAC] THEN
   REWRITE_TAC[GSYM(ASSUME `LENGTH (args:num list) = LENGTH (vals:data_v list)`);
     ASSUME `encode_header c (4 * tag) (LENGTH (args:num list)) = SOME (a:A word)`] THEN
   SUBGOAL_THEN `~(vals:data_v list = []) /\ LENGTH (args:num list) < data_state_space (s:(C,FFI)data_state) /\
                 k < LENGTH args`
     (fun th -> REWRITE_TAC[th]) THENL
    [REPEAT CONJ_TAC THENL [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC;
                            ASM_ARITH_TAC; ASM_ARITH_TAC];
     ALL_TAC] THEN
   CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
   DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr:A word`
     (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC)))) THEN
  (REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP1AUX_STEP_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def] THEN
   ASP1AUX_STEP_TAC [wl_evaluate_def; word_exp_rw; wl_set_var_def]) THEN
  (ABBREV_TAC `t2 = wl_state_locals_fupd
      (K (insert 3 (wl_Word a) (insert 1 (wl_Word free) (wl_state_locals t))))
      (t:(A,C,FFI)wl_state)` THEN
   SUBGOAL_THEN `wl_evaluate (StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0),
                   (t2:(A,C,FFI)wl_state)) = (NONE, wl_state_memory_fupd (K m1) t2)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC evaluate_StoreEach THEN EXISTS_TAC `CONS (wl_Word (a:A word)) ws` THEN
     EXISTS_TAC `free:A word` THEN EXPAND_TAC "t2" THEN
     SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert; ARITH_EQ] THEN
     MP_TAC(ISPECL [`3`; `args:num list`; `wl_state_locals_fupd (K (insert 1 (wl_Word free)
       (wl_state_locals t))) (t:(A,C,FFI)wl_state)`; `wl_Word (a:A word)`;
       `insert 1 (wl_Word (free:A word)) (wl_state_locals (t:(A,C,FFI)wl_state))`]
       get_vars_adjust_var) THEN
     MP_TAC(ISPECL [`1`; `args:num list`; `t:(A,C,FFI)wl_state`; `wl_Word (free:A word)`;
       `wl_state_locals (t:(A,C,FFI)wl_state)`] get_vars_adjust_var) THEN
     SIMP[ARITH_ODD] THEN
     SUBGOAL_THEN `wl_state_locals_fupd (K (wl_state_locals t)) (t:(A,C,FFI)wl_state) = t`
       (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[wl_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (ONCE_DEPTH_CONV)
     [MATCH_MP IL2AUX_evaluate_Seq_NONE th])) THEN
  (EXPAND_TAC "t2" THEN
   SUBGOAL_THEN `shift_length c - backend_common_word_shift(:A) < dimword(:A) /\
                 ~(shift_length c - backend_common_word_shift(:A) >= dimindex(:A))`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL [ASM_MESON_TAC[LET_TRANS; dimindex_lt_dimword; ARITH_RULE `a - b <= a`;
                                   LT_TRANS];
                     ASM_ARITH_TAC];
     ALL_TAC]) THEN
  (SIMP[wl_evaluate_def; word_exp_rw; wl_set_var_def; MAP; the_words_def;
     ITLIST; WORD_OR_0; WORD_ADD_0; wl_get_var_def; lookup_insert; ARITH_EQ;
     wl_get_store_def; wl_set_store_def; option_DISTINCT; distinctness "store_name"; MOD_LT]) THEN
  (SUBGOAL_THEN
    `wl_Word (word_or (word_shl (word_sub free curr)
               (shift_length c - backend_common_word_shift (:A)))
            (word_or (word 1) (word_bits (small_shift_length c - 1) 0
               (ptr_bits c tag (LENGTH (ws:(A word_loc)list)))))) =
     make_cons_ptr c (word_sub free curr) tag (LENGTH (args:num list)):A word_loc`
     SUBST1_TAC THENL
    [REWRITE_TAC[make_cons_ptr_def; get_lowerbits_def; injectivity "word_loc"] THEN
     SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = LENGTH (args:num list)` SUBST1_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!L S M (t:(A,C,FFI)wl_state).
      wl_state_locals_fupd (K L) (wl_state_store_fupd (K S) (wl_state_memory_fupd (K M) t)) =
      wl_state_store_fupd (K S) (wl_state_memory_fupd (K M) (wl_state_locals_fupd (K L) t))`
     (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[wl_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = LENGTH (args:num list)` SUBST1_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC ASP1AUX_state_rel_set_var_alloc THEN EXISTS_TAC `s:(C,FFI)data_state` THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term (fun t -> is_const t && fst(dest_const t) = "MutBlock")) (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "make_cons_ptr")) (concl th))) THEN
   ASM_REWRITE_TAC[]));;

(* HOL4 line 2817 *)
let assign_UpdateCons = prove
 (assign_thm_stmt `op = MemOp UpdateCons`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[distinctness "clos_op"; injectivity "clos_op";
     distinctness "mem_op"])) THEN
  (VAR_EQ_TAC THEN
   UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
   REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   UNDISCH_TAC `data_do_app (MemOp UpdateCons) vals (s:(C,FFI)data_state) = Rval (v,s2)` THEN
   REWRITE_TAC[data_do_app_def; distinctness "clos_op"; MEM; injectivity "clos_op"; do_space_def;
     op_space_reset_def; op_space_req_def; distinctness "mem_op"] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
  (CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_do_app_aux_def] THEN
   CASE_REWRITE_TAC[distinctness "clos_op"; injectivity "clos_op"; distinctness "mem_op"]) THEN
  (EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
   STRIP_TAC THEN REPEAT VAR_EQ_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
     data_state_INFO.ri_accfupds; K_THM; DE_MORGAN_THM]) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
   REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[ASP1AUX_LENGTH_EQ_3] THEN
   DISCH_THEN(X_CHOOSE_THEN `b1:num` (X_CHOOSE_THEN `b2:num` (X_CHOOSE_THEN `b3:num`
     SUBST_ALL_TAC))) THEN
   REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[arg3_def; assign_Update_def] THEN CASE_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
   FIRST_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `data_get_vars [b1; b2; b3] (data_state_locals (s:(C,FFI)data_state)) =
              SOME [data_RefPtr a0''' a1'''; data_Number (&(LENGTH (a2:data_v list))); a0'']`) o
     MATCH_MP state_rel_get_vars_IMP) THEN
   REWRITE_TAC[LENGTH; MAP] THEN CONV_TAC NUM_REDUCE_CONV THEN
   DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SYM))) THEN
   REWRITE_TAC[ASP1AUX_LENGTH_EQ_3] THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
       (X_CHOOSE_THEN `w3:A word_loc` SUBST_ALL_TAC)))) THEN
  (SUBGOAL_THEN `wl_get_vars (MAP adjust_var [b1;b2;b3]) (t:(A,C,FFI)wl_state) = SOME [w1; w2; w3]`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[MAP]; ALL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
   DRULE_ALL memory_rel_get_vars_IMP THEN REWRITE_TAC[ZIP; APPEND] THEN DISCH_TAC THEN
   SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP reorder_lemma) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(a1'''':bool)`]) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_UpdateCons o
     C CONJ (CONJ (ASSUME `lookup a1''' (data_state_refs (s:(C,FFI)data_state)) =
                           SOME (MutBlock a0'''' F a2 a3 a4)`)
                  (CONJ (ASSUME `good_dimindex(:A)`) (REFL `LENGTH (a2:data_v list)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `i_w:A word`
     (X_CHOOSE_THEN `xa:A word` (X_CHOOSE_THEN `ya:A word` STRIP_ASSUME_TAC))))) THEN
  (REPEAT VAR_EQ_TAC THEN
   SUBGOAL_THEN `shift_length c < dimindex(:A)` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_vars_3_IMP) THEN
   SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var b1)) =
                 SOME (wl_Word xa)` ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_offset c (adjust_var b2)) =
                 SOME (wl_Word ya)` ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_offset_lemma THEN EXISTS_TAC `i_w:A word` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP1AUX_EVAL_TAC [wl_evaluate_def; word_exp_rw; wl_mem_store_def; MAP; the_words_def;
     ITLIST; WORD_ADD_0; wl_set_var_def; wl_get_var_def] THEN
   SIMP[wl_evaluate_def; word_exp_rw; data_to_word_Unit_def; option_DISTINCT]) THEN
  (SUBGOAL_THEN `!m v w (t:(A,C,FFI)wl_state).
     wl_state_memory_fupd (K m) (wl_set_var v w t) =
     wl_set_var v w (wl_state_memory_fupd (K m) t)` (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[wl_set_var_def] THEN SIMP[]; ALL_TAC] THEN
   MATCH_MP_TAC ASP1AUX_state_rel_set_var_mem THEN EXISTS_TAC `s:(C,FFI)data_state` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP[do_stack_def; LET_DEF; LET_END_DEF; option_le_max_right; option_le_refl] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
   MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term ((=) `insert a1''' (MutBlock a0'''' F a2 a0'' a4)
                            (data_state_refs (s:(C,FFI)data_state))`)) (concl th))) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]));;

(* HOL4 line 2860 *)
let assign_FinaliseCons = prove
 (assign_thm_stmt `op = MemOp FinaliseCons`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[distinctness "clos_op"; injectivity "clos_op";
     distinctness "mem_op"])) THEN
  (VAR_EQ_TAC THEN
   UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
   REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   UNDISCH_TAC `data_do_app (MemOp FinaliseCons) vals (s:(C,FFI)data_state) = Rval (v,s2)` THEN
   REWRITE_TAC[data_do_app_def; distinctness "clos_op"; MEM; injectivity "clos_op"; do_space_def;
     op_space_reset_def; op_space_req_def; distinctness "mem_op"] THEN
   CONV_TAC NUM_REDUCE_CONV) THEN
  (CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_do_app_aux_def] THEN
   CASE_REWRITE_TAC[distinctness "clos_op"; injectivity "clos_op"; distinctness "mem_op"]) THEN
  (EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
   STRIP_TAC THEN REPEAT VAR_EQ_TAC) THEN
  (FIRST_ASSUM(X_CHOOSE_THEN `a1:num` SUBST_ALL_TAC o MATCH_MP get_vars_SING) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
     data_state_INFO.ri_accfupds; K_THM]) THEN
   REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg1_def; assign_FinaliseCons_def]) THEN
  (CASE_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[get_vars_SOME_IFF_data]) THEN
   FIRST_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `data_get_var a1 (data_state_locals (s:(C,FFI)data_state)) = SOME a0`) o
     MATCH_MP state_rel_get_var_IMP) THEN
   DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
   SIMP[wl_evaluate_def; word_exp_rw; option_DISTINCT] THEN
   FIRST_ASSUM(X_CHOOSE_TAC `ts:num` o MATCH_MP state_rel_IMP_tstamps)) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel)) THEN
  (DRULE_ALL memory_rel_get_var_IMP THEN DISCH_TAC) THEN
  (UNDISCH_TAC `data_finalise_cons a0 (data_state_refs (s:(C,FFI)data_state))
                  (data_state_tstamps s) = SOME (v,x',y')` THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts`;
                               THE_DEF]) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_FinaliseCons o
     C CONJ (ASSUME `data_finalise_cons a0 (data_state_refs (s:(C,FFI)data_state)) (SOME ts) =
                     SOME (v,x',y')`) o
     check (fun th -> can (find_term ((=) `CONS ((a0:data_v),(w:A word_loc))`)) (concl th))) THEN
   STRIP_TAC) THEN
  (MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN EXISTS_TAC `s:(C,FFI)data_state` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP[do_stack_def; LET_DEF; LET_END_DEF; option_le_max_right; option_le_refl]) THEN
  (REWRITE_TAC[GSYM APPEND_ASSOC] THEN ASM_REWRITE_TAC[]));;
