(* ========================================================================= *)
(* data_to_wordProof: port of HOL4                                           *)
(* compiler/backend/proofs/data_to_wordProofScript.sml (CakeML v3479),       *)
(* HOL4 lines 1-2811 (the whole script).                                     *)
(* Correctness proof for data_to_word.                                       *)
(*                                                                           *)
(* Rendering (as in data_to_word_gcProof): HOL4 Type state (wordSem state)   *)
(* is (A,C,FFI)wl_state; wordSem, dataLang and backend are qualified         *)
(* ancestors in HOL4.  HOL4 overloads word_get_code_labels,                  *)
(* word_good_handlers, word_good_code_labels (wordConvs) are                 *)
(* wordConvs_get_code_labels, good_handlers, wordConvs_good_code_labels;     *)
(* data_get_code_labels and data_good_code_labels (dataProps) keep their     *)
(* names.  HOL4 isPREFIX (the infix of io_events) is <<= (hol4/vocab.ml).    *)
(* D2WPAUX_ names are local helpers of this file.                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/sptree.ml";;
needs "hol4/int_bitwise.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/multiword.ml";;
needs "hol4/machine_ieee.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_assignProof.ml";;
needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_to_wordProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2811 ===== *)

(* HOL4 lines 23-29: ML values (clean_tac, state_rel_def, code_rel_def,     *)
(* assign_def): proof tools, not stated                                      *)

(* HOL4 line 37 *)
let state_rel_with_locals_sfs = prove
 (`!c l1 l2 (x:(C,FFI)data_state) l m (r:(A,C,FFI)wl_state) t locs.
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (combin_K l) (data_state_safe_for_space_fupd (combin_K m) x)) r t locs <=>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (combin_K l) x) r t locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM]);;

let _ = cake_add_simps [state_rel_with_locals_sfs];;

(* HOL4 line 45 *)
let do_space_code_const = prove
 (`!op vs (s:(A,B)data_state) s1.
     do_space op vs s = SOME s1 ==>
     data_state_code s1 = data_state_code s /\
     data_state_compile_oracle s1 = data_state_compile_oracle s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_space_def; consume_space_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 53 (local; 0b111100w is word 60) *)
let word_test_lemma1 = prove
 (`!x:A word.
     good_dimindex (:A) ==>
     (word_and (word 60) x = word ((8 + 6) * 4) <=>
      ~bit 2 x /\ bit 3 x /\ bit 4 x /\ bit 5 x)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND_ALT; BIT_WORD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* HOL4 line 64 (local) *)
let word_test_lemma2 = prove
 (`!x:A word.
     good_dimindex (:A) ==>
     (word_and (word 60) x = word ((0 + 6) * 4) <=>
      ~bit 2 x /\ bit 3 x /\ bit 4 x /\ ~bit 5 x)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND_ALT; BIT_WORD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* HOL4 line 81 *)
let memory_rel_Thunk_bits = prove
 (CASE_TERM
  `!c be ts refs sp st m dm bl p (w:A word) vars ev z a x.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,wl_Word w) vars) /\
     lookup p refs = SOME (bvl_Thunk ev z) /\
     good_dimindex (:A) /\
     get_real_addr c st w = SOME a /\
     m a = wl_Word x /\
     bit 0 w ==>
     (~bl /\ ev = Evaluated /\
      ~(word_and (word 60) x = word ((0 + 6) * 4)) /\
      ~(word_and (word 60) x = word ((8 + 6) * 4))) \/
     (match ev with
        NotEvaluated -> word_and (word 60) x = word ((0 + 6) * 4)
      | Evaluated -> word_and (word 60) x = word ((8 + 6) * 4))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `bl:bool`; `p:num`; `wl_Word w:A word_loc`;
                 `vars:(data_v#A word_loc)list`; `ev:thunk_mode`; `z:data_v`]
         memory_rel_Thunk_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:A word`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':A word` (X_CHOOSE_THEN `x':A word` STRIP_ASSUME_TAC) o
               CONJUNCT2) THEN
    SUBGOAL_THEN `a':A word = a` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
    SUBGOAL_THEN `x':A word = x` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
    DISJ1_TAC THEN ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w':A word = w` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  SUBGOAL_THEN `a':A word = a` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `x':A word = x` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  DISJ2_TAC THEN ASM_SIMP_TAC[word_test_lemma1; word_test_lemma2] THEN
  CASES_ON `ev:thunk_mode` THEN CAKE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "thunk_mode"]) THEN ASM_REWRITE_TAC[]);;

(* the domain of adjust_set depends only on the domain *)
let D2WPAUX_domain_adjust_set_mk_wf = prove
 (`!t:A spt. domain (adjust_set (mk_wf t)) = domain (adjust_set t)`,
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_adjust_set; lookup_mk_wf]);;

(* HOL4 line 102 *)
let MEM_join_env_cut_env = prove
 (`!(a:data_v#A word_loc) (t:(A word_loc)spt) r s x.
     MEM a (join_env x (toAList (sptree_inter t (adjust_set x)))) /\
     data_cut_env r s = SOME x ==>
     MEM a (join_env s (toAList (sptree_inter t (adjust_set s))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM; MEM_toAList;
              lookup_inter_alt; data_cut_env_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[D2WPAUX_domain_adjust_set_mk_wf; IN_domain_adjust_set_inter; lookup_mk_wf] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `p2:A word_loc` MP_TAC)) THEN
  ASM_CASES_TAC
    `p1 IN domain (adjust_set (s:data_v spt)) /\ p1 IN domain (adjust_set (r:num_set))` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p1:num`; `p2:A word_loc`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_adjust_set_IN o CONJUNCT2) THEN
  ASM_REWRITE_TAC[lookup_inter_alt]);;

(* HOL4 line 117 *)
let jump_exc_locals = prove
 (`!(t:(A,C,FFI)wl_state) l.
     wl_jump_exc (wl_state_locals_fupd (combin_K l) t) = wl_jump_exc t`,
  SIMP[wl_jump_exc_def]);;

(* HOL4 line 123 (HOL4: state_rel_cut_state_opt_SOME |> Q.GEN args |>      *)
(* Q.SPEC [] |> GEN_ALL |> SRULE [get_vars_def, cut_state_opt_def,           *)
(* cut_state_def, CaseEq "option", PULL_EXISTS, wordSem get_vars_def])       *)
let state_rel_cut_env_IMP_cut_env = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs kept_names env.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env kept_names (data_state_locals s) = SOME env ==>
     ?y. wl_cut_env (adjust_sets kept_names) (wl_state_locals t) = SOME y /\
         data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (combin_K env) s) t
           NONE locs /\
         data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (combin_K env) s)
           (wl_state_locals_fupd (combin_K y) t) NONE locs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `[]:num list`;
                 `[]:data_v list`; `kept_names:num_set`;
                 `data_state_locals_fupd (combin_K env) (s:(C,FFI)data_state)`]
         state_rel_cut_state_opt_SOME) THEN
  SIMP[data_get_vars_def; data_cut_state_opt_def; data_cut_state_def; MAP; LENGTH;
       wl_get_vars_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:(A word_loc)spt` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 128 (local) *)
let v_inv_Loc = prove
 (`!c v1 (s:(C,FFI)data_state) v2 f tf (heap:((A word_loc,data_to_word_memoryProof_tag#
     (A word_loc)list)heap_element)list) n1 n2.
     v_inv c v1 (data_state_refs s) (v2,f,tf,heap) /\
     word_addr c v2 = wl_Loc n1 n2 ==>
     n2 = 0`,
  REWRITE_TAC[word_addr_eq_Loc] THEN MESON_TAC[]);;

(* the right-hand version of LIST_REL_MEM_IMP (hol4/list.ml) *)
let D2WPAUX_ALL2_MEM_R = prove
 (`!(P:A->B->bool) xs ys y. ALL2 P xs ys /\ MEM y ys ==> ?x. P x y`,
  REWRITE_TAC[LIST_REL_EL_EQN; MEM_EXISTS_EL] THEN MESON_TAC[]);;

(* HOL4 line 136 (local) *)
let state_rel_get_var_RefPtr_Loc = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v1 locs n b p n1 n2.
     data_to_word_gcProof_state_rel c l1 l2 s t v1 locs /\
     data_get_var n (data_state_locals s) = SOME (data_RefPtr b p) /\
     wl_get_var (adjust_var n) t = SOME (wl_Loc n1 n2) ==>
     n2 = 0`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_get_var_def; wl_get_var_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[GSYM APPEND_ASSOC] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "word_ml_inv"
                     with Failure _ -> false)) THEN
  DRULE_ALL word_ml_inv_lookup THEN REWRITE_TAC[word_ml_inv_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `hs:(((A)word_loc)heap_address)list` (MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPEC `wl_Loc n1 n2:A word_loc` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] D2WPAUX_ALL2_MEM_R)) THEN
  REWRITE_TAC[MAP_APPEND; MAP; MEM_APPEND; MEM] THEN
  REWRITE_TAC[word_addr_eq_Loc] THEN MESON_TAC[]);;

(* HOL4 line 171 (local) *)
let cut_state_opt_ffi = prove
 (`!names_opt (r:(C,FFI)data_state) v1.
     data_cut_state_opt names_opt r = SOME v1 ==> data_state_ffi v1 = data_state_ffi r`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* HOL4 line 179: val psv_tail (a tactic) *)

let D2WPAUX_ALOOKUP_ZIP_EL = prove
 (`!(ks:K list) (vs:A list) i.
     LENGTH ks = LENGTH vs /\ ALL_DISTINCT ks /\ i < LENGTH ks ==>
     ALOOKUP (ZIP ks vs) (EL i ks) = SOME (EL i vs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ZIP (ks:K list) (vs:A list)`; `i:num`] ALOOKUP_ALL_DISTINCT_EL) THEN
  ASM_SIMP_TAC[LENGTH_ZIP; MAP_FST_ZIP; EL_ZIP] THEN ASM_MESON_TAC[]);;

let D2WPAUX_lookup_alist_insert_EL = prove
 (`!ks (vs:A list) t i.
     LENGTH ks = LENGTH vs /\ ALL_DISTINCT ks /\ i < LENGTH ks ==>
     lookup (EL i ks) (alist_insert ks vs t) = SOME (EL i vs)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_alist_insert; D2WPAUX_ALOOKUP_ZIP_EL] THEN
  CAKE_REWRITE_TAC[]);;

let D2WPAUX_lookup_union_ZIP_NOT_MEM = prove
 (`!ks (vs:A list) s k.
     LENGTH ks = LENGTH vs /\ ~MEM k ks ==>
     lookup k (sptree_union (fromAList (ZIP ks vs)) s) = lookup k s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  SUBGOAL_THEN `ALOOKUP (ZIP (ks:num list) (vs:A list)) k = NONE` SUBST1_TAC THENL
   [ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL]; CAKE_REWRITE_TAC[]]);;

let D2WPAUX_lookup_union_ZIP_EL = prove
 (`!ks (vs:A list) s i.
     LENGTH ks = LENGTH vs /\ ALL_DISTINCT ks /\ i < LENGTH ks ==>
     lookup (EL i ks) (sptree_union (fromAList (ZIP ks vs)) s) = SOME (EL i vs)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[lookup_union; lookup_fromAList; D2WPAUX_ALOOKUP_ZIP_EL] THEN
  CAKE_REWRITE_TAC[]);;

(* the variables of the frame after set_vars, from before or from the     *)
(* set values (the memory part of state_rel_pop_env_set_vars_IMP)        *)
let D2WPAUX_MEM_join_env_set_vars = prove
 (`!(s:data_v spt) (t:(A word_loc)spt) ns as ws x.
     LENGTH as = LENGTH ws /\ LENGTH ns = LENGTH as /\ ALL_DISTINCT ns /\
     MEM x (join_env (sptree_union (fromAList (ZIP ns as)) s)
             (toAList (sptree_inter (alist_insert (MAP adjust_var ns) ws t)
                             (adjust_set (sptree_union (fromAList (ZIP ns as)) s))))) ==>
     MEM x (ZIP as ws) \/ MEM x (join_env s (toAList (sptree_inter t (adjust_set s))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM; MEM_toAList;
              lookup_inter_alt] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `j = (k - 2) DIV 2` THEN
  SUBGOAL_THEN `k = adjust_var j` SUBST_ALL_TAC THENL
   [EXPAND_TAC "j" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMP_adjust_var THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (MAP adjust_var ns) = LENGTH (ws:(A word_loc)list)` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP adjust_var ns)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[adjust_var_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `MEM (j:num) ns` THENL
   [UNDISCH_TAC `MEM (j:num) ns` THEN REWRITE_TAC[MEM_EXISTS_EL] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `adjust_var j = EL i (MAP adjust_var ns)` SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC[EL_MAP]; ALL_TAC] THEN
    UNDISCH_TAC `(if EL i (MAP adjust_var ns) IN
                     domain (adjust_set (sptree_union (fromAList (ZIP ns as)) (s:data_v spt)))
                  then lookup (EL i (MAP adjust_var ns))
                         (alist_insert (MAP adjust_var ns) ws (t:(A word_loc)spt))
                  else NONE) = SOME v` THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `i < LENGTH (MAP adjust_var ns)` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`MAP adjust_var ns`; `ws:(A word_loc)list`; `t:(A word_loc)spt`;
                   `i:num`] D2WPAUX_lookup_alist_insert_EL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `lookup (EL i ns) (sptree_union (fromAList (ZIP ns as)) (s:data_v spt)) =
                  SOME (EL i as)` ASSUME_TAC THENL
     [MATCH_MP_TAC D2WPAUX_lookup_union_ZIP_EL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `j:num = EL i (ns:num list)` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[THE_DEF] THEN DISJ1_TAC THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `i:num` THEN
    SUBGOAL_THEN `i < LENGTH (as:data_v list) /\ i < LENGTH (ws:(A word_loc)list)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i < LENGTH (ns:num list)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `LENGTH (as:data_v list) = LENGTH (ws:(A word_loc)list)` THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_ZIP; EL_ZIP];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `~MEM (adjust_var j) (MAP adjust_var ns)` ASSUME_TAC THENL
   [REWRITE_TAC[MEM_MAP; adjust_var_11] THEN UNDISCH_TAC `~MEM (j:num) ns` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup j (sptree_union (fromAList (ZIP ns as)) (s:data_v spt)) = lookup j s`
    ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_lookup_union_ZIP_NOT_MEM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lookup (adjust_var j) (alist_insert (MAP adjust_var ns) ws t) =
                lookup (adjust_var j) (t:(A word_loc)spt)` ASSUME_TAC THENL
   [MATCH_MP_TAC WALLOCPAUX_lookup_alist_insert_notin THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`adjust_var j`; `v:A word_loc`] THEN
  UNDISCH_TAC `(if adjust_var j IN
                   domain (adjust_set (sptree_union (fromAList (ZIP ns as)) (s:data_v spt)))
                then lookup (adjust_var j)
                       (alist_insert (MAP adjust_var ns) ws (t:(A word_loc)spt))
                else NONE) = SOME v` THEN
  ASM_REWRITE_TAC[GCP1AUX_adjust_var_IN_adjust_set; domain_lookup] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

(* state_rel after setting the returned values of a call with set_vars    *)
let D2WPAUX_state_rel_set_vars = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) as ws locs ns.
     data_to_word_gcProof_state_rel c l1 l2 s t (SOME (ZIP as ws)) locs /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     LENGTH as = LENGTH ws /\ LENGTH ns = LENGTH as /\ ALL_DISTINCT ns ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_vars ns as s)
       (wl_set_vars (MAP adjust_var ns) ws t) NONE locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_vars_def; wl_set_vars_def;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `LENGTH (MAP adjust_var ns) = LENGTH (ws:(A word_loc)list)` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP adjust_var ns)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[adjust_var_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `~MEM 0 (MAP adjust_var ns)` ASSUME_TAC THENL
     [REWRITE_TAC[MEM_MAP; adjust_var_def] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin];
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `MEM (n:num) ns` THENL
     [UNDISCH_TAC `MEM (n:num) ns` THEN REWRITE_TAC[MEM_EXISTS_EL] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `adjust_var n = EL i (MAP adjust_var ns)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[EL_MAP]; ALL_TAC] THEN
      SUBGOAL_THEN `i < LENGTH (MAP adjust_var ns)` ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[D2WPAUX_lookup_alist_insert_EL; IS_SOME_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN `~MEM (adjust_var n) (MAP adjust_var ns)` ASSUME_TAC THENL
     [REWRITE_TAC[MEM_MAP; adjust_var_11] THEN UNDISCH_TAC `~MEM (n:num) ns` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin; D2WPAUX_lookup_union_ZIP_NOT_MEM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel"
    with Failure _ -> false)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  X_GEN_TAC `x:data_v#A word_loc` THEN REWRITE_TAC[MEM_APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`data_state_locals (s:(C,FFI)data_state)`;
                 `wl_state_locals (t:(A,C,FFI)wl_state)`;
                 `ns:num list`; `as:data_v list`; `ws:(A word_loc)list`;
                 `x:data_v#A word_loc`] D2WPAUX_MEM_join_env_set_vars) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* an option of a triple is NONE or SOME of a triple *)
let D2WPAUX_option_triple_cases = prove
 (`!h:(A#B#C)option. h = NONE \/ ?x1 x2 x3. h = SOME (x1,x2,x3)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `h:(A#B#C)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MAP_EVERY EXISTS_TAC [`FST (a:A#B#C)`; `FST (SND (a:A#B#C))`; `SND (SND (a:A#B#C))`] THEN
  REWRITE_TAC[PAIR]);;

(* the return location of a frame is in its variable 0 after pop_env *)
let D2WPAUX_frame_lookup_0 = prove
 (`!sf m (e0:(num#A word_loc)list) e h l8 l9.
     data_to_word_gcProof_stack_rel sf (StackFrame m e0 e h) /\
     contains_loc (StackFrame m e0 e h) (l8,l9) ==>
     lookup 0 (sptree_union (fromAList e) (fromAList e0)) = SOME (wl_Loc l8 l9)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `data_to_word_gcProof_stack_rel sf (StackFrame m (e0:(num#A word_loc)list) e h)
                ==> ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) e` MP_TAC THENL
   [MP_TAC(ISPEC `sf:stack` (cases "stack")) THEN
    DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    DISJ_CASES_THEN2 SUBST1_TAC (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
      (ISPEC `h:(num#num#num)option` D2WPAUX_option_triple_cases) THEN
    REWRITE_TAC[data_to_word_gcProof_stack_rel_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[contains_loc_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[lookup_union; lookup_fromAList; GCP2AUX_ALOOKUP_0_NONE] THEN
  CAKE_REWRITE_TAC[]);;

(* after pop_env of related states, variable 0 holds the return location *)
let D2WPAUX_pop_env_lookup_0 = prove
 (`!c q l (s1:(C,FFI)data_state) (t1:(A,C,FFI)wl_state) xs locs t2 l8 l9 ll.
     data_to_word_gcProof_state_rel c q l s1 t1 xs locs /\
     wl_pop_env t1 = SOME t2 /\ locs = CONS (l8,l9) ll ==>
     lookup 0 (wl_state_locals t2) = SOME (wl_Loc l8 l9)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_pop_env (t1:(A,C,FFI)wl_state) = SOME t2` THEN
  REWRITE_TAC[wl_pop_env_def] THEN
  UNDISCH_TAC `ALL2 contains_loc (wl_state_stack (t1:(A,C,FFI)wl_state)) locs` THEN
  UNDISCH_TAC `ALL2 data_to_word_gcProof_stack_rel (data_state_stack (s1:(C,FFI)data_state))
                 (wl_state_stack (t1:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`wl_state_stack (t1:(A,C,FFI)wl_state)`,`st:((A)stack_frame)list`) THEN
  SPEC_TAC(`data_state_stack (s1:(C,FFI)data_state)`,`ds:stack list`) THEN
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ds:stack list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `st:((A)stack_frame)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN
  MP_TAC(ISPEC `h':(A)stack_frame` (cases "stack_frame")) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `e0:(num#A word_loc)list`
    (X_CHOOSE_THEN `e:(num#A word_loc)list` (X_CHOOSE_THEN `hh:(num#num#num)option`
       SUBST1_TAC)))) THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_locals (t2:(A,C,FFI)wl_state) = sptree_union (fromAList e) (fromAList e0)`
    SUBST1_TAC THENL
   [POP_ASSUM MP_TAC THEN
    DISJ_CASES_THEN2 SUBST1_TAC (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
      (ISPEC `hh:(num#num#num)option` D2WPAUX_option_triple_cases) THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    MATCH_MP_TAC D2WPAUX_frame_lookup_0 THEN ASM_MESON_TAC[]]);;

(* HOL4 line 256 (local) *)
let state_rel_pop_env_set_vars_IMP = prove
 (`!c q l (s1:(C,FFI)data_state) (t1:(A,C,FFI)wl_state) as ws locs ns s2.
     data_to_word_gcProof_state_rel c q l s1 t1 (SOME (ZIP as ws)) locs /\
     LENGTH as = LENGTH ws /\ LENGTH ns = LENGTH as /\ ALL_DISTINCT ns /\
     data_pop_env s1 = SOME s2 ==>
     ?t2 l8 l9 ll.
       wl_pop_env t1 = SOME t2 /\ locs = CONS (l8,l9) ll /\
       data_to_word_gcProof_state_rel c l8 l9 (data_set_vars ns as s2)
         (wl_set_vars (MAP adjust_var ns) ws t2) NONE ll`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `q:num`; `l:num`; `s1:(C,FFI)data_state`;
                 `t1:(A,C,FFI)wl_state`; `SOME (ZIP (as:data_v list) (ws:(A word_loc)list))`;
                 `locs:(num#num)list`; `s2:(C,FFI)data_state`] state_rel_pop_env_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num`
    (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)wl_state`; `l8:num`; `l9:num`; `ll:(num#num)list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC D2WPAUX_state_rel_set_vars THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC D2WPAUX_pop_env_lookup_0 THEN
  MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `q:num`; `l:num`; `s1:(C,FFI)data_state`;
                 `t1:(A,C,FFI)wl_state`; `SOME (ZIP (as:data_v list) (ws:(A word_loc)list))`;
                 `locs:(num#num)list`; `ll:(num#num)list`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helpers of data_compile_correct (HOL4 line 293): the clauses of the       *)
(* evaluation functions and of comp for one constructor each, and the       *)
(* statement of data_compile_correct for one program and state             *)
(* (D2WPAUX_correct), proved case by case (HOL4 suspend/Resume blocks).     *)
(* ------------------------------------------------------------------------- *)

(* the clause of an evaluation function (or of comp) for the constructor   *)
(* named cname                                                               *)
let d2wpaux_clause defth cname =
  let cl = CONJUNCTS defth in
  let ok th =
    let l = lhs (concl (SPEC_ALL th)) in
    let arg = rand l in
    let p = if is_pair arg then fst (dest_pair arg) else arg in
    let h,_ = strip_comb p in
    is_const h && fst (dest_const h) = cname in
  try find ok cl with Failure _ -> failwith ("d2wpaux_clause: " ^ cname);;

(* comp unfolded for each constructor of dataLang programs *)
let D2WPAUX_comp_eqs =
  let conv = ONCE_REWRITE_CONV[data_to_word_comp_def] THENC CAKE_REWRITE_CONV[] in
  end_itlist CONJ (map (fun tm -> GEN_ALL (conv tm))
   [`data_to_word_comp c n l data_Skip:(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Move dest src):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Assign dest op args names_opt):(A)wl_prog#num`;
    `data_to_word_comp c n l data_Tick:(A)wl_prog#num`;
    `data_to_word_comp c n l (MakeSpace k names):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Raise v):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Return ns):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Seq c1 c2):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_If v c1 c2):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Force ret loc src):(A)wl_prog#num`;
    `data_to_word_comp c n l (data_Call ret dest args handler):(A)wl_prog#num`]);;

let D2WPAUX_correct_def = new_definition (CASE_TERM
  `D2WPAUX_correct (a:A->bool) (prog:data_prog) (s:(C,FFI)data_state) <=>
   !c n l l1 l2 res s1 (t:(A,C,FFI)wl_state) locs.
     (data_evaluate (prog,s) = (res,s1)) /\
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     wl_state_termdep t > 1 ==>
     ?t1 res1.
       (wl_evaluate (FST (data_to_word_comp c n l prog),t) = (res1,t1)) /\
       option_le (wl_state_stack_max t1) (data_state_stack_max s1) /\
       (res1 = SOME NotEnoughSpace ==>
        ffi_state_io_events (wl_state_ffi t1) <<= ffi_state_io_events (data_state_ffi s1) /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~data_state_safe_for_space s1)) /\
       (~(res1 = SOME NotEnoughSpace) ==>
        match res with
          NONE -> data_to_word_gcProof_state_rel c l1 l2 s1 t1 NONE locs /\ (res1 = NONE)
        | SOME (Rval v) ->
            ?ws. LENGTH ws = LENGTH v /\
                 data_to_word_gcProof_state_rel c l1 l2 s1 t1 (SOME (ZIP v ws)) locs /\
                 (res1 = SOME (wl_Result (wl_Loc l1 l2) ws))
        | SOME (Rerr (Rraise v)) ->
            (wl_state_ffi t1 = data_state_ffi s1) /\
            ?w l5 l6 ll.
              (res1 = SOME (wl_Exception (mk_loc (wl_jump_exc t)) w)) /\
              (~(wl_jump_exc t = NONE) ==>
               LASTN (LENGTH (data_state_stack s1) + 1) locs = CONS (l5,l6) ll /\
               !i. data_to_word_gcProof_state_rel c l5 l6 (data_set_var i v s1)
                     (wl_set_var (adjust_var i) w t1) NONE ll)
        | SOME (Rerr (Rabort (Rffi_error f))) ->
            (res1 = SOME (wl_FinalFFI f) /\ wl_state_ffi t1 = data_state_ffi s1)
        | SOME (Rerr (Rabort e)) ->
            (res1 = SOME wl_TimeOut) /\ wl_state_ffi t1 = data_state_ffi s1)`);;

(* the start of each case: the definition unfolded, the data evaluation    *)
(* clause and the comp clause rewritten                                     *)
let d2wpaux_open_tac dcl : tactic =
  REWRITE_TAC[D2WPAUX_correct_def; D2WPAUX_comp_eqs; FST] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[dcl] THEN STRIP_TAC;;

let D2WPAUX_Skip = prove
 (`!s:(C,FFI)data_state. D2WPAUX_correct (:A) data_Skip s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Skip") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Skip"; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`t:(A,C,FFI)wl_state`; `NONE:((A)wl_result)option`] THEN
  CAKE_REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                 (t:(A,C,FFI)wl_state) NONE locs` THEN
  SIMP_TAC[data_to_word_gcProof_state_rel_thm]);;

(* the parts of state_rel that the cases use most *)
let D2WPAUX_state_rel_IMP = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v1 locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v1 locs ==>
     wl_state_ffi t = data_state_ffi s /\
     wl_state_clock t = data_state_clock s /\
     wl_state_handler t = data_state_handler s /\
     option_le (wl_state_stack_max t) (data_state_stack_max s) /\
     wl_state_stack_size t = data_state_stack_frame_sizes s /\
     wl_state_locals_size t = data_state_locals_size s /\
     LENGTH (wl_state_stack t) = LENGTH (data_state_stack s) /\
     LENGTH locs = LENGTH (data_state_stack s)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL2"
                     with Failure _ -> false))) THEN
  ARITH_TAC);;

(* the record facts of the cases *)
let D2WPAUX_REC_RWS =
  [data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM;
   data_flush_state_def; wl_flush_state_def; data_dec_clock_def; wl_dec_clock_def;
   data_set_var_def; wl_set_var_def];;

let D2WPAUX_Tick = prove
 (`!s:(C,FFI)data_state. D2WPAUX_correct (:A) data_Tick s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Tick") THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Tick"] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = 0` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "COND" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
   [MAP_EVERY EXISTS_TAC [`wl_flush_state T (t:(A,C,FFI)wl_state)`;
                          `SOME wl_TimeOut:((A)wl_result)option`] THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC D2WPAUX_REC_RWS;
    MAP_EVERY EXISTS_TAC [`wl_dec_clock (t:(A,C,FFI)wl_state)`;
                          `NONE:((A)wl_result)option`] THEN
    CAKE_REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC D2WPAUX_REC_RWS THEN
    REWRITE_TAC[GSYM data_dec_clock_def; GSYM wl_dec_clock_def] THEN
    REWRITE_TAC[data_dec_clock_def; wl_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC data_to_word_gcProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]]);;

(* the evaluation assumption data_evaluate ... = (res,s1) of a case *)
let d2wpaux_is_eval_asm tm =
  is_eq tm &&
  (let r = rhs tm in
   is_pair r && is_var (fst (dest_pair r)) && is_var (snd (dest_pair r)) &&
   fst (dest_var (fst (dest_pair r))) = "res" &&
   fst (dest_var (snd (dest_pair r))) = "s1")
  && not (is_const (fst (strip_comb (lhs tm))) &&
          fst (dest_const (fst (strip_comb (lhs tm)))) = "wl_evaluate");;

(* a goal with the assumptions res = type error and res <> type error is   *)
(* solved                                                                     *)
let d2wpaux_tyerr = `SOME (Rerr (Rabort Rtype_error)):((data_v list,data_v)result)option`;;

let d2wpaux_type_error_tac : tactic =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = d2wpaux_tyerr && is_var (rhs c)
    then SUBST_ALL_TAC (SYM th) THEN
         FIRST_X_ASSUM(fun th -> if is_neg (concl th) then CONTR_TAC (REWRITE_RULE[] th)
                                 else NO_TAC)
    else NO_TAC);;

(* split the option term tm (with its equation) in the evaluation assumption *)
let d2wpaux_split_tac (tm:term) : tactic =
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  CASES_ON tm THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ]) THEN
  TRY(d2wpaux_type_error_tac THEN NO_TAC);;

let D2WPAUX_Raise = prove
 (`!n (s:(C,FFI)data_state). D2WPAUX_correct (:A) (data_Raise n) s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Raise") THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Raise"] THEN
  d2wpaux_split_tac `data_get_var n (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_split_tac `data_jump_exc (s:(C,FFI)data_state)` THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th))) o
    check (fun th -> is_eq (concl th) && not (is_var (lhs (concl th)))))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                 `locs:(num#num)list`; `n:num`; `a:data_v`] state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `n:num`; `a:data_v`;
                 `w:A word_loc`; `a':(C,FFI)data_state`] state_rel_jump_exc) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN `d1:num`
    (X_CHOOSE_THEN `d2:num` (X_CHOOSE_THEN `l5:num` (X_CHOOSE_THEN `l6:num`
      (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE D2WPAUX_REC_RWS o
              MATCH_MP D2WPAUX_state_rel_IMP o SPEC `0`) THEN
  MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`;
                        `SOME (wl_Exception (wl_Loc d1 d2) w):((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[distinctness "wl_result"; option_INJ; option_DISTINCT] THEN
  MAP_EVERY EXISTS_TAC [`w:A word_loc`; `l5:num`; `l6:num`; `ll:(num#num)list`] THEN
  ASM_REWRITE_TAC[mk_loc_def; option_DISTINCT]);;

(* word_ml_inv_get_vars_IMP (gcProof) for memory_rel *)
let D2WPAUX_memory_rel_get_vars_IMP = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) n x w envs.
     memory_rel c be ts refs sp st m dm
       (APPEND (join_env (data_state_locals s)
          (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          envs) /\
     data_get_vars n (data_state_locals s) = SOME x /\
     wl_get_vars (MAP adjust_var n) t = SOME w ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (APPEND (ZIP x w)
          (join_env (data_state_locals s)
             (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s))))))
          envs)`,
  REWRITE_TAC[memory_rel_def] THEN MESON_TAC[word_ml_inv_get_vars_IMP]);;

(* option_le of the stack with no locals *)
let D2WPAUX_option_le_locals_0 = prove
 (`!ss (lsz:num option) mx.
     option_le (OPTION_MAP2 (+) ss lsz) mx ==>
     option_le (OPTION_MAP2 (+) ss (SOME 0)) mx`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `mx:num option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `ss:num option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `lsz:num option` (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

(* state_rel after a Return: the returned values in the list of roots *)
let D2WPAUX_state_rel_flush_F = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs ns xs ws.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars ns (data_state_locals s) = SOME xs /\
     wl_get_vars (MAP adjust_var ns) t = SOME ws ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_flush_state F s) (wl_flush_state F t)
       (SOME (ZIP xs ws)) locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_flush_state_def; wl_flush_state_def;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_def; IS_SOME_DEF] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP D2WPAUX_option_le_locals_0 o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "option_le" &&
                           can (find_term (fun t -> is_const t && fst(dest_const t) = "wl_stack_size"))
                             (concl th)
                       with Failure _ -> false));
    ALL_TAC] THEN
  REWRITE_TAC[toAList_def] THEN REWRITE_TAC[GSYM toAList_def] THEN
  SUBGOAL_THEN `toAList (sptree_inter (LN:(A word_loc)spt) (adjust_set (LN:data_v spt))) = []`
    SUBST1_TAC THENL
   [REWRITE_TAC[sptree_inter_def; toAList_def; foldi_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[foldi_def];
    ALL_TAC] THEN
  REWRITE_TAC[join_env_def; FILTER; MAP; APPEND_NIL] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel"
    with Failure _ -> false)) THEN
  REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN DISCH_TAC THEN
  DRULE_ALL D2WPAUX_memory_rel_get_vars_IMP THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

(* substitute the assumptions e = res and e = s1 (the result of the data    *)
(* evaluation) into the goal                                                *)
let d2wpaux_res_tac : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (rhs c) && mem (fst (dest_var (rhs c))) ["res"; "s1"] &&
       not (lhs c = rhs c)
    then SUBST_ALL_TAC (SYM th)
    else if is_eq c && is_var (lhs c) && mem (fst (dest_var (lhs c))) ["res"; "s1"] &&
            not (vfree_in (lhs c) (rhs c))
    then SUBST_ALL_TAC th else NO_TAC));;

let D2WPAUX_Return = prove
 (`!ns (s:(C,FFI)data_state). D2WPAUX_correct (:A) (data_Return ns) s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Return") THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Return"] THEN
  d2wpaux_split_tac `data_get_vars ns (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_res_tac THEN
  MP_TAC(ISPECL [`ns:num list`; `a:data_v list`; `c:data_to_word_config`; `l1:num`;
                 `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
                 `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wl_get_var 0 (t:(A,C,FFI)wl_state) = SOME (wl_Loc l1 l2)` ASSUME_TAC THENL
   [REWRITE_TAC[wl_get_var_def] THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`wl_flush_state F (t:(A,C,FFI)wl_state)`;
                        `SOME (wl_Result (wl_Loc l1 l2) ws):((A)wl_result)option`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  REWRITE_TAC[distinctness "wl_result"; option_INJ] THEN CAKE_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC D2WPAUX_REC_RWS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `ws:(A word_loc)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC D2WPAUX_state_rel_flush_F THEN EXISTS_TAC `ns:num list` THEN
  ASM_REWRITE_TAC[]);;

(* state_rel after a Move: the moved value in the new variable *)
let D2WPAUX_state_rel_Move = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs src dest v w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var src (data_state_locals s) = SOME v /\
     wl_get_var (adjust_var src) t = SOME w ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s)
       (wl_set_var (adjust_var dest) w t) NONE locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def; wl_set_var_def;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[lookup_insert; adjust_var_def; ARITH_RULE `~(0 = 2 * n + 2)`];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC (REWRITE_RULE[APPEND] memory_rel_insert) THEN
  MATCH_MP_TAC memory_rel_get_var_IMP THEN EXISTS_TAC `src:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel"
    with Failure _ -> false)) THEN
  REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]);;

let D2WPAUX_Move = prove
 (`!dest src (s:(C,FFI)data_state). D2WPAUX_correct (:A) (data_Move dest src) s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Move") THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Move"] THEN
  d2wpaux_split_tac `data_get_var src (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_res_tac THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                 `locs:(num#num)list`; `src:num`; `a:data_v`] state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
  REWRITE_TAC[MAP; FST; SND; ALL_DISTINCT; MEM; wl_get_vars_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM wl_set_var_def; wl_set_vars_def; alist_insert_def] THEN
  REWRITE_TAC[GSYM wl_set_var_def] THEN
  MAP_EVERY EXISTS_TAC [`wl_set_var (adjust_var dest) w (t:(A,C,FFI)wl_state)`;
                        `NONE:((A)wl_result)option`] THEN
  REWRITE_TAC[option_DISTINCT] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest a s)
                  (wl_set_var (adjust_var dest) w (t:(A,C,FFI)wl_state)) NONE locs`
    ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_state_rel_Move THEN EXISTS_TAC `src:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN SIMP_TAC[]);;

(* the case statement for one program and state, unfolded *)
let d2wpaux_unfold_ih = REWRITE_RULE[D2WPAUX_correct_def];;

let D2WPAUX_If = prove
 (`!v c1 c2 (s:(C,FFI)data_state).
     (!x. data_get_var v (data_state_locals s) = SOME x /\ isBool T x ==>
          D2WPAUX_correct (:A) c1 s) /\
     (!x. data_get_var v (data_state_locals s) = SOME x /\ ~isBool T x /\ isBool F x ==>
          D2WPAUX_correct (:A) c2 s)
     ==> D2WPAUX_correct (:A) (data_If v c1 c2) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_If") THEN
  REWRITE_TAC[pair_CASE_def; FST] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_If"] THEN
  d2wpaux_split_tac `data_get_var v (data_state_locals (s:(C,FFI)data_state))` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                 `locs:(num#num)list`; `v:num`; `a:data_v`] state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `v:num`; `a:data_v`;
                 `w:A word_loc`] get_var_isT_OR_isF) THEN
  ASM_REWRITE_TAC[wl_get_var_imm_def] THEN STRIP_TAC THEN
  ASM_CASES_TAC `isBool T a` THENL
   [UNDISCH_TAC `isBool T a ==> (w:A word_loc) = wl_Word (word 18)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[wl_word_cmp_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o SPEC `a:data_v` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `c1:data_prog`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n:num`; `l:num`; `l1:num`;
      `l2:num`; `res:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `isBool F a` THENL
   [UNDISCH_TAC `isBool F a ==> (w:A word_loc) = wl_Word (word 2)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[wl_word_cmp_def] THEN
    SUBGOAL_THEN `~(word 2 = word 18:A word)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[WORD_EQ; CONG] THEN
      UNDISCH_TAC `~(18 MOD dimword (:A) = 2 MOD dimword (:A))` THEN
      REWRITE_TAC[dimword_def] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o SPEC `a:data_v` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `c2:data_prog`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n:num`;
      `SND (data_to_word_comp c n l c1:(A)wl_prog#num)`; `l1:num`;
      `l2:num`; `res:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac);;

(* the NotEnoughSpace part of the statement survives a later data evaluation *)
let D2WPAUX_NES_mono = prove
 (`!c (prog:data_prog) (s0:(C,FFI)data_state) res s1 (t0:(A,C,FFI)wl_state).
     data_evaluate (prog,s0) = (res,s1) /\
     option_le (wl_state_stack_max t0) (data_state_stack_max s0) /\
     ffi_state_io_events (wl_state_ffi t0) <<= ffi_state_io_events (data_state_ffi s0) /\
     (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
      ~data_state_safe_for_space s0) ==>
     option_le (wl_state_stack_max t0) (data_state_stack_max s1) /\
     ffi_state_io_events (wl_state_ffi t0) <<= ffi_state_io_events (data_state_ffi s1) /\
     (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
      ~data_state_safe_for_space s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (s0:(C,FFI)data_state)` THEN
    ASM_MESON_TAC[evaluate_option_le_stack_max];
    MATCH_MP_TAC IS_PREFIX_TRANS THEN
    EXISTS_TAC `ffi_state_io_events (data_state_ffi (s0:(C,FFI)data_state))` THEN
    ASM_MESON_TAC[data_evaluate_io_events_mono];
    ASM_MESON_TAC[evaluate_safe_for_space_mono]]);;

(* the shapes of the result of a data evaluation *)
let D2WPAUX_result_option_cases = prove
 (`!r:((A list,A)result)option.
     r = NONE \/ (?v. r = SOME (Rval v)) \/ (?v. r = SOME (Rerr (Rraise v))) \/
     r = SOME (Rerr (Rabort Rtype_error)) \/ r = SOME (Rerr (Rabort Rtimeout_error)) \/
     (?f. r = SOME (Rerr (Rabort (Rffi_error f))))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:((A list,A)result)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; UNWIND_THM1; EXISTS_REFL] THEN
  STRUCT_CASES_TAC(ISPEC `a:(A list,A)result` (cases "result")) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; EXISTS_REFL] THEN
  STRUCT_CASES_TAC(ISPEC `a':(A)error_result` (cases "error_result")) THEN
  REWRITE_TAC[distinctness "error_result"; injectivity "error_result"; EXISTS_REFL] THEN
  STRUCT_CASES_TAC(ISPEC `a:abort` (cases "abort")) THEN
  REWRITE_TAC[distinctness "abort"; injectivity "abort"; EXISTS_REFL] THEN
  MESON_TAC[]);;

(* split the result r of a data evaluation into its shapes, reducing the  *)
(* case expressions on it in the goal and the assumptions                   *)
let d2wpaux_result_cases_tac (r:term) : tactic =
  REPEAT_TCL DISJ_CASES_THEN (fun th -> REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC th)
    (ISPEC r D2WPAUX_result_option_cases) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[];;

let D2WPAUX_Seq = prove
 (`!c1 c2 (s:(C,FFI)data_state).
     D2WPAUX_correct (:A) c1 s /\
     (!s1. data_evaluate (c1,s) = (NONE,s1) ==> D2WPAUX_correct (:A) c2 s1)
     ==> D2WPAUX_correct (:A) (data_Seq c1 c2) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Seq") THEN
  REWRITE_TAC[pair_CASE_def; FST] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Seq"] THEN
  MP_TAC(ISPEC `data_evaluate (c1,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s0:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r0 = SOME (Rerr (Rabort Rtype_error)):((data_v list,data_v)result)option)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    REWRITE_TAC[option_DISTINCT; PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:data_to_word_config`; `n:num`; `l:num`; `l1:num`;
      `l2:num`; `r0:((data_v list,data_v)result)option`; `s0:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] o d2wpaux_unfold_ih o
    check (fun th -> not (is_forall (concl th)) &&
                     can (find_term (fun t -> t = `c1:data_prog`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res0:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r0:((data_v list,data_v)result)option = NONE` THENL
   [ALL_TAC;
    (* the first program did not finish normally *)
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    SUBGOAL_THEN `~(res0:((A)wl_result)option = NONE)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(r0:((data_v list,data_v)result)option = NONE)` THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        is_neg (fst (dest_imp (concl th))))) THEN
      REWRITE_TAC[option_DISTINCT] THEN
      d2wpaux_result_cases_tac `r0:((data_v list,data_v)result)option` THEN
      REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t0:(A,C,FFI)wl_state`; `res0:((A)wl_result)option`] THEN
    ASM_REWRITE_TAC[]] THEN
  (* the first program finished normally *)
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `res0 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`t0:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    MATCH_MP_TAC D2WPAUX_NES_mono THEN
    MAP_EVERY EXISTS_TAC [`c2:data_prog`; `s0:(C,FFI)data_state`;
                          `res:((data_v list,data_v)result)option`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:(C,FFI)data_state` o
    check (fun th -> is_forall (concl th) &&
                     can (find_term (fun t -> t = `c2:data_prog`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n:num`;
      `SND (data_to_word_comp c n l c1:(A)wl_prog#num)`; `l1:num`;
      `l2:num`; `res:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`;
      `t0:(A,C,FFI)wl_state`; `locs:(num#num)list`] o d2wpaux_unfold_ih) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_clock o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
                     with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_mk_loc_EQ o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
                     with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP eval_NONE_IMP_jump_exc_NONE_EQ o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[]);;

let D2WPAUX_Assign = prove
 (`!dest op args names_opt (s:(C,FFI)data_state).
     D2WPAUX_correct (:A) (data_Assign dest op args names_opt) s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Assign") THEN
  ASM_CASES_TAC `op_requires_names op = IS_NONE (names_opt:num_set option)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  d2wpaux_split_tac `data_get_vars args (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_split_tac `data_cut_state_opt names_opt (s:(C,FFI)data_state)` THEN
  SUBGOAL_THEN `~(op_requires_names op <=> (names_opt:num_set option) = NONE)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(op_requires_names op = IS_NONE (names_opt:num_set option))` THEN
    STRUCT_CASES_TAC(ISPEC `names_opt:num_set option` (cases "option")) THEN
    REWRITE_TAC[IS_NONE_DEF; option_DISTINCT];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_state_opt_const) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_stack_max) THEN
  CASES_ON `data_do_app op a (a':(C,FFI)data_state)` THENL
   [(* the operation succeeded: assign_thm *)
    MP_TAC(ISPEC `a'':data_v#(C,FFI)data_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:data_v` (X_CHOOSE_THEN `s2:(C,FFI)data_state`
      SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP data_do_app_io_events_mono o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_do_app"
                       with Failure _ -> false)) THEN
    DRULE_ALL assign_thm THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `l:num`; `dest:num`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN
      `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:(A,C,FFI)wl_state`; `q:((A)wl_result)option`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[data_set_var_def; install_sfs_def; data_state_INFO.ri_accfupds; K_THM] THEN
    CAKE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `q = SOME NotEnoughSpace:((A)wl_result)option` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        fst (dest_imp (concl th)) = `SOME NotEnoughSpace = SOME NotEnoughSpace:
                                       ((A)wl_result)option`)) THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "data_to_word_gcProof_state_rel" &&
                           can (find_term (fun t -> t = `r:(A,C,FFI)wl_state`)) (concl th)
                       with Failure _ -> false)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[data_set_var_def; data_state_INFO.ri_accfupds; K_THM]) THEN
    ASM_REWRITE_TAC[state_rel_with_locals_sfs];
    ALL_TAC] THEN
  (* the operation failed: only the FFI can give an error *)
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC
                 (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) o
    MATCH_MP do_app_Rerr o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_do_app"
                     with Failure _ -> false)) THENL
   [FIRST_X_ASSUM(CONTR_TAC o REWRITE_RULE[] o check (is_neg o concl)); ALL_TAC] THEN
  DRULE_ALL assign_FFI_final THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `l:num`; `dest:num`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN
    `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:(A,C,FFI)wl_state`; `q:((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_flush_state_def; install_sfs_def; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* the size argument of the MakeSpace code *)
let D2WPAUX_alloc_size_eq = prove
 (`!k. (if val (word (k * (dimindex (:A) DIV 8)):A word) = k * (dimindex (:A) DIV 8)
        then word (k * (dimindex (:A) DIV 8)) else word_not (word 0)) = alloc_size k:A word`,
  REWRITE_TAC[alloc_size_def; VAL_WORD; MOD_EQ_SELF; dimword_def; EXP_EQ_0; ARITH_EQ;
              WORD_NEG_1]);;

(* state_rel ignores the safe_for_space and peak_heap_length of add_space *)
let D2WPAUX_state_rel_add_space = prove
 (`!c l1 l2 (s:(C,FFI)data_state) k (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 (add_space s k) t v locs <=>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_space_fupd (combin_K k) s) t v locs`,
  REWRITE_TAC[add_space_def; data_to_word_gcProof_state_rel_def;
              data_state_INFO.ri_accfupds; K_THM]);;

(* alloc does not look at the value of variable 1 *)
let D2WPAUX_alloc_set_var_1 = prove
 (`!w (names:B spt) (t:(A,C,FFI)wl_state) k.
     wl_alloc k (adjust_sets names) (wl_set_var 1 w t) = wl_alloc k (adjust_sets names) t`,
  REWRITE_TAC[wl_set_var_def; alloc_locals_insert_1]);;

(* the SilentFFI code with an empty FFI call: only the cut of the locals *)
let D2WPAUX_SilentFFI_eval = prove
 (`!c (names:B spt) (t:(A,C,FFI)wl_state) curr hlen next y.
     data_to_word_config_call_empty_ffi c /\
     FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word curr) /\
     FLOOKUP (wl_state_store t) HeapLength = SOME (wl_Word hlen) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word next) /\
     wl_cut_env (adjust_sets names) (wl_state_locals t) = SOME y ==>
     wl_evaluate (SilentFFI c 3 (adjust_sets names), t) =
       (NONE, wl_state_locals_fupd (combin_K y) (wl_state_fp_regs_fupd (combin_K FEMPTY) t))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SilentFFI_def; data_to_word_list_Seq_def] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Seq";
              d2wpaux_clause wl_evaluate_def "wl_Assign";
              d2wpaux_clause wl_evaluate_def "wl_FFI"] THEN
  SIMP[wl_word_exp_def; MAP; the_words_def; wl_get_store_def; word_op_def; OPTION_MAP_DEF;
       wl_set_var_def; wl_get_var_def; lookup_insert; cut_env_adjust_sets_insert_ODD;
       ARITH_ODD; ODD; VAL_WORD_0; read_bytearray_def; call_FFI_def;
       write_bytearray_def] THEN
  REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

(* the accessors of wl_set_var *)
let D2WPAUX_set_var_accs = prove
 (`!v x (s:(A,C,FFI)wl_state).
     wl_state_locals (wl_set_var v x s) = insert v x (wl_state_locals s) /\
     wl_state_store (wl_set_var v x s) = wl_state_store s /\
     wl_state_ffi (wl_set_var v x s) = wl_state_ffi s /\
     wl_state_stack_max (wl_set_var v x s) = wl_state_stack_max s /\
     wl_state_clock (wl_set_var v x s) = wl_state_clock s /\
     wl_state_termdep (wl_set_var v x s) = wl_state_termdep s /\
     wl_state_code (wl_set_var v x s) = wl_state_code s /\
     wl_state_stack (wl_set_var v x s) = wl_state_stack s /\
     wl_state_memory (wl_set_var v x s) = wl_state_memory s /\
     wl_state_mdomain (wl_set_var v x s) = wl_state_mdomain s /\
     wl_state_be (wl_set_var v x s) = wl_state_be s /\
     wl_state_handler (wl_set_var v x s) = wl_state_handler s`,
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM]);;

(* the store facts of state_rel that the MakeSpace code reads *)
let D2WPAUX_state_rel_store = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     ?end next hlen curr.
        FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word curr) /\
        FLOOKUP (wl_state_store t) HeapLength = SOME (wl_Word hlen) /\
        FLOOKUP (wl_state_store t) TriggerGC = SOME (wl_Word end) /\
        FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word next)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "option"; injectivity "word_loc"] THEN
  MESON_TAC[]);;

(* locals and FP registers set after a set_var *)
let D2WPAUX_fp_locals_set_var = prove
 (`!y f v x (t:(A,C,FFI)wl_state).
     wl_state_locals_fupd (combin_K y) (wl_state_fp_regs_fupd (combin_K f) (wl_set_var v x t)) =
     wl_state_locals_fupd (combin_K y) (wl_state_fp_regs_fupd (combin_K f) t)`,
  REWRITE_TAC[wl_set_var_def; wl_state_component_equality; wl_state_INFO.ri_accfupds;
              K_THM]);;

(* HOL4 data_compile_correct [MakeSpace] *)
let D2WPAUX_MakeSpace = prove
 (`!k names (s:(C,FFI)data_state). D2WPAUX_correct (:A) (MakeSpace k names) s`,
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "MakeSpace") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[D2WPAUX_alloc_size_eq] THEN
  d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_res_tac THEN
  FIRST_ASSUM(X_CHOOSE_THEN `end:A word` (X_CHOOSE_THEN `next:A word`
    (X_CHOOSE_THEN `hlen:A word` (X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC))) o
    MATCH_MP D2WPAUX_state_rel_store) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Seq"; d2wpaux_clause wl_evaluate_def "wl_Assign";
              d2wpaux_clause wl_evaluate_def "wl_If"] THEN
  SIMP[wl_word_exp_def; MAP; the_words_def; wl_get_store_def; word_op_def; OPTION_MAP_DEF;
       wl_get_var_def; lookup_insert; wl_get_var_imm_def; wl_word_cmp_def] THEN
  SIMP[D2WPAUX_set_var_accs; lookup_insert; wl_word_cmp_def] THEN
  COND_CASES_TAC THENL
   [(* no space left: SilentFFI, Alloc, SilentFFI *)
    ASM_CASES_TAC `data_to_word_config_call_empty_ffi c` THENL
     [(* the empty FFI calls *)
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `a:data_v spt`]
         cut_env_IMP_cut_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:(A word_loc)spt`) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Seq"] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `names:num_set`;
                 `wl_set_var 1 (wl_Word (word_sub end next)) (t:(A,C,FFI)wl_state)`;
                 `curr:A word`; `hlen:A word`; `next:A word`; `y:(A word_loc)spt`]
         D2WPAUX_SilentFFI_eval) THEN
  ASM_SIMP_TAC[D2WPAUX_set_var_accs; cut_env_adjust_sets_insert_ODD; ARITH_ODD; ODD] THEN
  DISCH_TAC THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[D2WPAUX_fp_locals_set_var] THEN
      REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Assign"; d2wpaux_clause wl_evaluate_def "wl_Alloc"] THEN
  SIMP[wl_word_exp_def; wl_get_var_def; D2WPAUX_set_var_accs; lookup_insert;
       D2WPAUX_alloc_set_var_1] THEN
      SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
                  (data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state))
                  (wl_state_locals_fupd (combin_K y) (wl_state_fp_regs_fupd (combin_K FEMPTY)
                     (t:(A,C,FFI)wl_state))) NONE locs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                   `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`;
                   `a:data_v spt`; `y:(A word_loc)spt`] state_rel_cut_env_cut_env) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `FEMPTY:(num,int64)fmap` o MATCH_MP state_rel_with_fp_regs) THEN
    REWRITE_TAC[wl_state_INFO.ri_fupdcanon];
    ALL_TAC] THEN
  MP_TAC(ISPEC `wl_alloc (alloc_size k) (adjust_sets (names:num_set))
                  (wl_state_locals_fupd (combin_K y) (wl_state_fp_regs_fupd (combin_K FEMPTY)
                     (t:(A,C,FFI)wl_state)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `r:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_env_idempotent o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_cut_env"
                     with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
                 `data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state)`;
                 `wl_state_locals_fupd (combin_K y) (wl_state_fp_regs_fupd (combin_K FEMPTY)
                     (t:(A,C,FFI)wl_state))`; `locs:(num#num)list`; `names:num_set`;
                 `a:data_v spt`; `k:num`; `q:((A)wl_result)option`; `r:(A,C,FFI)wl_state`]
         alloc_lemma) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `cut_locals names (data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state)) =
                data_state_locals_fupd (combin_K a) s` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[cut_locals_def; data_state_INFO.ri_accfupds; K_THM] THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `q = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))) &&
      fst (dest_imp (concl th)) = `SOME NotEnoughSpace = SOME NotEnoughSpace:
                                     ((A)wl_result)option`)) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT; D2WPAUX_state_rel_add_space] THEN
    REWRITE_TAC[add_space_def; data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[IS_PREFIX_REFL] THEN DISCH_TAC THEN
    ASM_CASES_TAC `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_conj (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `data_state_locals_fupd (combin_K a) (data_state_space_fupd (combin_K k)
                  (data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state))) =
                data_state_space_fupd (combin_K k) (data_state_locals_fupd (combin_K a) s)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `end2:A word` (X_CHOOSE_THEN `next2:A word`
    (X_CHOOSE_THEN `hlen2:A word` (X_CHOOSE_THEN `curr2:A word` STRIP_ASSUME_TAC))) o
    MATCH_MP D2WPAUX_state_rel_store o
    check (fun th -> can (find_term (fun t -> t = `r:(A,C,FFI)wl_state`)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) =
                            "data_to_word_gcProof_state_rel" with Failure _ -> false))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
                 `data_state_space_fupd (combin_K k) (data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state))`;
                 `r:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `a:data_v spt`]
         cut_env_IMP_cut_env) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `y2:(A word_loc)spt`) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `names:num_set`; `r:(A,C,FFI)wl_state`;
                 `curr2:A word`; `hlen2:A word`; `next2:A word`; `y2:(A word_loc)spt`]
         D2WPAUX_SilentFFI_eval) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`wl_state_locals_fupd (combin_K y2) (wl_state_fp_regs_fupd (combin_K FEMPTY)
                           (r:(A,C,FFI)wl_state))`; `NONE:((A)wl_result)option`] THEN
  REWRITE_TAC[option_DISTINCT; D2WPAUX_state_rel_add_space] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
                 `data_state_space_fupd (combin_K k) (data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state))`;
                 `r:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `a:data_v spt`;
                 `y2:(A word_loc)spt`] state_rel_cut_env_cut_env) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `FEMPTY:(num,int64)fmap` o MATCH_MP state_rel_with_fp_regs) THEN
  SUBGOAL_THEN `data_state_locals_fupd (combin_K a) (data_state_space_fupd (combin_K k)
                  (data_state_locals_fupd (combin_K a) (s:(C,FFI)data_state))) =
                data_state_space_fupd (combin_K k) (data_state_locals_fupd (combin_K a) s)` SUBST1_TAC THENL
   [REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM;
              add_space_def] THEN SIMP_TAC[];
      (* no FFI calls *)
      ASM_REWRITE_TAC[SilentFFI_def; data_to_word_list_Seq_def] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Seq"; d2wpaux_clause wl_evaluate_def "wl_Skip";
              d2wpaux_clause wl_evaluate_def "wl_Assign"; d2wpaux_clause wl_evaluate_def "wl_Alloc"] THEN
  CAKE_REWRITE_TAC[] THEN
  SIMP[wl_word_exp_def; wl_get_var_def; D2WPAUX_set_var_accs; lookup_insert;
       D2WPAUX_alloc_set_var_1] THEN
      MP_TAC(ISPEC `wl_alloc (alloc_size k) (adjust_sets (names:num_set)) (t:(A,C,FFI)wl_state)`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `r:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`r:(A,C,FFI)wl_state`; `q:((A)wl_result)option`] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `a:data_v spt`;
                 `k:num`; `q:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] alloc_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[D2WPAUX_state_rel_add_space] THEN
  REWRITE_TAC[add_space_def; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_CASES_TAC `q = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IS_PREFIX_REFL] THEN
    SUBGOAL_THEN `cut_locals names (s:(C,FFI)data_state) = data_state_locals_fupd (combin_K a) s`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[cut_locals_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_conj (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM] o
    MATCH_MP D2WPAUX_state_rel_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_fupdcanon]) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_fupdcanon]];
    (* enough space *)
    REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Skip"] THEN
    MAP_EVERY EXISTS_TAC [`wl_set_var 1 (wl_Word (word_sub end next)) (t:(A,C,FFI)wl_state)`;
                        `NONE:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT; D2WPAUX_set_var_accs; D2WPAUX_state_rel_add_space] THEN
  REWRITE_TAC[add_space_def; data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wl_set_var_def; state_rel_insert_1] THEN
  MATCH_MP_TAC has_space_state_rel THEN CONJ_TAC THENL
   [REWRITE_TAC[wl_has_space_def; wl_get_store_def] THEN ASM_REWRITE_TAC[] THEN
    CAKE_REWRITE_TAC[] THEN
    UNDISCH_TAC `~word_ult (word_sub end next) (alloc_size k:A word)` THEN
    REWRITE_TAC[WORD_ULT; option_INJ] THEN ARITH_TAC;
    MATCH_MP_TAC state_rel_cut_env THEN EXISTS_TAC `names:num_set` THEN
    ASM_REWRITE_TAC[]]]);;

(* jump_exc depends only on the handler and the stack *)
let D2WPAUX_jump_exc_same = prove
 (`!(s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     wl_state_handler s1 = wl_state_handler s2 /\ wl_state_stack s1 = wl_state_stack s2 ==>
     (wl_jump_exc s1 = NONE <=> wl_jump_exc s2 = NONE) /\
     (mk_loc (wl_jump_exc s1):B word_loc) = mk_loc (wl_jump_exc s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SPEC_TAC(`LASTN (wl_state_handler (s2:(A,C,FFI)wl_state) + 1) (wl_state_stack s2)`,
           `ls:((A)stack_frame)list`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:((A)stack_frame)list` list_CASES) THEN
  CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:(A)stack_frame` (cases "stack_frame")) THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN CAKE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPEC `a3:(num#num#num)option` D2WPAUX_option_triple_cases) THEN
  CAKE_REWRITE_TAC[option_DISTINCT; mk_loc_def]);;

(* a triple is a tuple *)
let D2WPAUX_triple_cases = prove
 (`!p:A#B#C. ?x y z. p = (x,y,z)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* the call env and dec_clock keep the handler and the stack *)
let D2WPAUX_jump_exc_call_env_dec_clock = prove
 (`!args ss (t:(A,C,FFI)wl_state).
     (wl_jump_exc (wl_call_env args ss (wl_dec_clock t)) = NONE <=> wl_jump_exc t = NONE) /\
     (mk_loc (wl_jump_exc (wl_call_env args ss (wl_dec_clock t))):B word_loc) =
       mk_loc (wl_jump_exc t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC D2WPAUX_jump_exc_same THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds]);;

(* split the triple a of the case expression on it in the evaluation       *)
(* assumption                                                                *)
let d2wpaux_triple_tac (a:term) (x:term) (y:term) (z:term) : tactic =
  MP_TAC(ISPEC a D2WPAUX_triple_cases) THEN
  DISCH_THEN(X_CHOOSE_THEN x (X_CHOOSE_THEN y (X_CHOOSE_THEN z SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]);;

(* HOL4 data_compile_correct [Call], ret = NONE (a tail call) *)
let D2WPAUX_Call_NONE = prove
 (`!dest args handler (s:(C,FFI)data_state).
     (!xs prog args1 ss.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        handler = NONE /\ ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog (data_call_env args1 ss (data_dec_clock s))) ==>
     D2WPAUX_correct (:A) (data_Call NONE dest args handler) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Call") THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[FST; d2wpaux_clause wl_evaluate_def "wl_Call"] THEN
  d2wpaux_split_tac `data_get_vars args (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_split_tac `data_find_code dest a (data_state_code (s:(C,FFI)data_state))
                       (data_state_stack_frame_sizes s)` THEN
  d2wpaux_triple_tac `a':data_v list#data_prog#num option` `args1:data_v list`
    `prog:data_prog` `ss:num option` THEN
  ASM_CASES_TAC `handler:(num#data_prog)option = NONE` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `a:data_v list`]
         state_rel_0_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `c:data_to_word_config`;
                 `l1:num`; `l2:num`; `locs:(num#num)list`; `args:num list`; `a:data_v list`;
                 `ws:(A word_loc)list`; `dest:num option`;
                 `data_state_stack_frame_sizes (s:(C,FFI)data_state)`; `args1:data_v list`;
                 `prog:data_prog`; `ss:num option`] data_to_word_gcProof_find_code_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `args2:(A word_loc)list` (X_CHOOSE_THEN `n1:num`
    (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[bad_dest_args_def; NOT_CONS_NIL; add_ret_loc_def] THEN
  CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    MAP_EVERY EXISTS_TAC [`wl_flush_state T (t:(A,C,FFI)wl_state)`;
                          `SOME wl_TimeOut:((A)wl_result)option`] THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC D2WPAUX_REC_RWS;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `data_evaluate (prog,data_call_env args1 ss
                  (data_dec_clock (s:(C,FFI)data_state)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s0:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r0:((data_v list,data_v)result)option = NONE` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  MP_TAC(ISPEC `r0:((data_v list,data_v)result)option` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rr:(data_v list,data_v)result`
    SUBST_ALL_TAC) THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
  FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o
    SPECL [`a:data_v list`; `prog:data_prog`; `args1:data_v list`; `ss:num option`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n1:num`; `n2:num`; `l1:num`;
      `l2:num`; `SOME rr:((data_v list,data_v)result)option`; `s0:(C,FFI)data_state`;
      `wl_call_env args2 ss (wl_dec_clock (t:(A,C,FFI)wl_state))`;
      `locs:(num#num)list`]) THEN
  ASM_REWRITE_TAC[termdep_rw] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~wl_bad_fun_return (res1:((A)wl_result)option)` ASSUME_TAC THENL
   [ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THEN
    ASM_REWRITE_TAC[wl_bad_fun_return_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    d2wpaux_result_cases_tac `SOME rr:((data_v list,data_v)result)option` THEN
    REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[wl_bad_fun_return_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `res1:((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  REWRITE_TAC[D2WPAUX_jump_exc_call_env_dec_clock] THEN CAKE_REWRITE_TAC[]);;

(* substitute an assumption v = e for the variable named v *)
let d2wpaux_subst_var_tac (v:string) : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (lhs c) && fst (dest_var (lhs c)) = v &&
       not (vfree_in (lhs c) (rhs c))
    then SUBST_ALL_TAC th else NO_TAC);;

(* jump_exc after the call env of a returning call without handler *)
let D2WPAUX_jump_exc_call_push_NONE = prove
 (`!args ss y (t:(A,C,FFI)wl_state).
     (wl_jump_exc (wl_call_env args ss (wl_push_env y NONE (wl_dec_clock t))) = NONE <=>
      wl_jump_exc t = NONE) /\
     (mk_loc (wl_jump_exc (wl_call_env args ss (wl_push_env y NONE (wl_dec_clock t))))
        :B word_loc) = mk_loc (wl_jump_exc t)`,
  REWRITE_TAC[jump_exc_call_env; jump_exc_push_env_NONE; jump_exc_push_env_NONE_simp]);;

(* the evaluation assumption e1 = res /\ e2 = s1, substituted *)
let d2wpaux_res_conj_tac : tactic =
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th ->
    let c = concl th in
    is_conj c && is_eq (rand c) && is_var (rhs (rand c)) &&
    fst (dest_var (rhs (rand c))) = "s1")) THEN
  d2wpaux_res_tac;;

(* the goal ?t1 res1. (x,y) = (res1,t1) /\ ...: take res1 = x and t1 = y *)
let d2wpaux_exists_pair_tac : tactic = fun (asl,w as g) ->
  let vs,bod = strip_exists w in
  if length vs <> 2 then failwith "d2wpaux_exists_pair_tac" else
  let cs = conjuncts bod in
  let e = hd cs in
  if is_eq e && is_pair (lhs e) then
    let x,y = dest_pair (lhs e) in (EXISTS_TAC y THEN EXISTS_TAC x) g
  else
    let e1 = el 0 cs and e2 = el 1 cs in
    if is_eq e1 && is_eq e2 then (EXISTS_TAC (lhs e2) THEN EXISTS_TAC (lhs e1)) g
    else failwith "d2wpaux_exists_pair_tac";;

(* the end of a call whose callee aborted (timeout or FFI) *)
let d2wpaux_call_abort_tac : tactic =
  d2wpaux_res_conj_tac THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_exists_pair_tac THEN
  ASM_REWRITE_TAC[distinctness "wl_result"; option_INJ; injectivity "wl_result";
                  option_DISTINCT];;

(* HOL4 data_compile_correct [Call], ret = SOME, no handler *)
let D2WPAUX_Call_SOME_NONE = prove
 (`!ns names dest args (s:(C,FFI)data_state).
     (!xs prog args1 ss env.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        ALL_DISTINCT ns /\
        data_cut_env names (data_state_locals s) = SOME env /\
        ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog
          (data_call_env args1 ss (data_push_env env F (data_dec_clock s)))) ==>
     D2WPAUX_correct (:A) (data_Call (SOME (ns,names)) dest args NONE) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Call") THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[FST; d2wpaux_clause wl_evaluate_def "wl_Call"] THEN
  d2wpaux_split_tac `data_get_vars args (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_split_tac `data_find_code dest a (data_state_code (s:(C,FFI)data_state))
                       (data_state_stack_frame_sizes s)` THEN
  d2wpaux_triple_tac `a':data_v list#data_prog#num option` `args1:data_v list`
    `prog:data_prog` `ss:num option` THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FST; d2wpaux_clause wl_evaluate_def "wl_Call"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  ASM_CASES_TAC `ALL_DISTINCT (ns:num list)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  MP_TAC(ISPECL [`args:num list`; `a:data_v list`; `c:data_to_word_config`; `l1:num`;
                 `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
                 `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`;
                 `a'':data_v spt`] cut_env_IMP_cut_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:(A word_loc)spt`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `a:data_v list`;
                 `ws:(A word_loc)list`; `dest:num option`;
                 `data_state_stack_frame_sizes (s:(C,FFI)data_state)`; `args1:data_v list`;
                 `prog:data_prog`; `ss:num option`; `names:num_set`; `a'':data_v spt`;
                 `(y1,y2):(A word_loc)spt#(A word_loc)spt`; `n:num`; `l:num`]
         find_code_thm_ret) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `args2:(A word_loc)list` (X_CHOOSE_THEN `n1:num`
    (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~bad_dest_args (dest:num option) (MAP adjust_var args)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP data_find_code o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_find_code"
                       with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_get_vars"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[bad_dest_args_def; GSYM LENGTH_EQ_NIL; LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP adjust_var ns)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[adjust_var_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[add_ret_loc_def; domain_adjust_sets] THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "wl_call_env"
                                              with Failure _ -> false)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) =
                            "data_to_word_gcProof_state_rel" with Failure _ -> false))) THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`wl_flush_state T (wl_state_stack_fupd (combin_K [])
       (wl_state_stack_max_fupd (combin_K (wl_state_stack_max (wl_call_env args2 ss
          (wl_push_env (y1,y2) NONE (t:(A,C,FFI)wl_state))))) t))`;
       `SOME wl_TimeOut:((A)wl_result)option`] THEN
    CAKE_REWRITE_TAC[] THEN
    UNDISCH_TAC `option_le
      (wl_state_stack_max (wl_call_env args2 ss (wl_push_env (y1,y2) NONE
        (wl_dec_clock (t:(A,C,FFI)wl_state)))))
      (data_state_stack_max (data_call_env args1 ss (data_push_env a'' F
        (data_dec_clock (s:(C,FFI)data_state)))))` THEN
    UNDISCH_TAC `wl_state_ffi (t:(A,C,FFI)wl_state) = data_state_ffi (s:(C,FFI)data_state)` THEN
    REWRITE_TAC[wl_flush_state_def; wl_call_env_def; push_env_dec_clock_stack] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `data_evaluate (prog,data_call_env args1 ss (data_push_env a'' F
                  (data_dec_clock (s:(C,FFI)data_state))))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s2:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r0 = NONE:((data_v list,data_v)result)option) /\
                ~(r0 = SOME (Rerr (Rabort Rtype_error)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o
    SPECL [`a:data_v list`; `prog:data_prog`; `args1:data_v list`; `ss:num option`;
           `a'':data_v spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n1:num`; `n2:num`; `n:num`;
      `l:num`; `r0:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`;
      `wl_call_env args2 ss (wl_push_env (y1,y2) NONE (wl_dec_clock (t:(A,C,FFI)wl_state)))`;
      `CONS (l1,l2) (locs:(num#num)list)`]) THEN
  ASM_REWRITE_TAC[termdep_rw; push_env_termdep] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_result_cases_tac `r0:((data_v list,data_v)result)option` THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THENL
   [(* the callee returned values *)
    ASM_CASES_TAC `LENGTH (v:data_v list) = LENGTH (ns:num list)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  d2wpaux_split_tac `data_pop_env (s2:(C,FFI)data_state)` THEN d2wpaux_res_tac THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_pop_env_const) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP pop_env_safe_for_space) THEN
    CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT; data_set_vars_def; data_state_INFO.ri_accfupds; K_THM] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `n:num`; `l:num`; `s2:(C,FFI)data_state`;
                 `t1:(A,C,FFI)wl_state`; `v:data_v list`; `ws2:(A word_loc)list`;
                 `CONS (l1,l2) (locs:(num#num)list)`; `ns:num list`; `a''':(C,FFI)data_state`]
         state_rel_pop_env_set_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num`
    (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    is_eq (lhand (concl th)) && is_var (rhs (lhand (concl th)))))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_IMP_domain_EQ o CONJ (ASSUME
    `wl_evaluate (FST (data_to_word_comp c n1 n2 prog),
       wl_call_env args2 ss (wl_push_env (y1,y2) NONE (wl_dec_clock (t:(A,C,FFI)wl_state)))) =
     (SOME (wl_Result (wl_Loc n l) ws2),t1)`) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_pop_env"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Skip"] THEN
  MAP_EVERY EXISTS_TAC [`wl_set_vars (MAP adjust_var ns) ws2 (t2:(A,C,FFI)wl_state)`;
                        `NONE:((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const) THEN
  REWRITE_TAC[wl_set_vars_def; data_set_vars_def; wl_state_INFO.ri_accfupds;
              data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[];
    (* the callee raised an exception *)
    d2wpaux_res_conj_tac THEN CAKE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[D2WPAUX_jump_exc_call_push_NONE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:A word_loc` (X_CHOOSE_THEN `l5:num`
    (X_CHOOSE_THEN `l6:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC))))) THEN
    d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`;
    `SOME (wl_Exception (mk_loc (wl_jump_exc (t:(A,C,FFI)wl_state))) w):((A)wl_result)option`] THEN
    ASM_REWRITE_TAC[distinctness "wl_result"; option_INJ; injectivity "wl_result"] THEN
    MAP_EVERY EXISTS_TAC [`w:A word_loc`; `l5:num`; `l6:num`; `ll:(num#num)list`] THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (data_state_stack (s2:(C,FFI)data_state)) < LENGTH (locs:(num#num)list)`
    (fun th -> SIMP_TAC[MATCH_MP LASTN_TL th]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP eval_exc_stack_shorter o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_evaluate"
                     with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[];
    d2wpaux_call_abort_tac;
    d2wpaux_call_abort_tac]);;

(* jump_exc after the handler frame of a raising call is popped *)
let D2WPAUX_jump_exc_handler_return = prove
 (`!p args ss y x1 x2 x3 x4 (t:(A,C,FFI)wl_state) ll w t1 v z.
     wl_evaluate (p,wl_call_env args ss
                      (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock t))) =
       (SOME (wl_Exception ll w),t1) ==>
     (wl_jump_exc (wl_set_var v z t1) = NONE <=> wl_jump_exc t = NONE) /\
     (mk_loc (wl_jump_exc (wl_set_var v z t1)):A word_loc) = mk_loc (wl_jump_exc t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`wl_set_var v z (t1:(A,C,FFI)wl_state)`; `t1:(A,C,FFI)wl_state`]
    (INST_TYPE [`:A`,`:B`] D2WPAUX_jump_exc_same)) THEN
  REWRITE_TAC[D2WPAUX_set_var_accs] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP eval_push_env_SOME_exc_IMP_s_key_eq) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP mk_loc_eq_push_env_exc_Exception) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`] s_key_eq_handler_eq_IMP) THEN
  ASM_MESON_TAC[s_key_eq_sym]);;

(* the call env of a call with handler has a handler frame *)
let D2WPAUX_jump_exc_call_push_SOME = prove
 (`!args ss y x1 x2 x3 x4 (t:(A,C,FFI)wl_state).
     ~(wl_jump_exc (wl_call_env args ss (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock t)))
       = NONE)`,
  REWRITE_TAC[jump_exc_call_env; jump_exc_push_env_NONE_simp; jump_exc_push_env_SOME]);;

(* HOL4 data_compile_correct [Call], ret = SOME, with handler *)
let D2WPAUX_Call_SOME_SOME = prove
 (`!ns names n0 h0 dest args (s:(C,FFI)data_state).
     (!xs prog args1 ss env x s2.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        ALL_DISTINCT ns /\
        data_cut_env names (data_state_locals s) = SOME env /\
        ~(data_state_clock s = 0) /\
        data_evaluate (prog,data_call_env args1 ss (data_push_env env T (data_dec_clock s))) =
          (SOME (Rerr (Rraise x)),s2) ==>
        D2WPAUX_correct (:A) h0 (data_set_var n0 x s2)) /\
     (!xs prog args1 ss env.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        ALL_DISTINCT ns /\
        data_cut_env names (data_state_locals s) = SOME env /\
        ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog
          (data_call_env args1 ss (data_push_env env T (data_dec_clock s)))) ==>
     D2WPAUX_correct (:A) (data_Call (SOME (ns,names)) dest args (SOME (n0,h0))) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Call") THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[FST; d2wpaux_clause wl_evaluate_def "wl_Call"] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FST; SND; d2wpaux_clause wl_evaluate_def "wl_Call"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  d2wpaux_split_tac `data_get_vars args (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_split_tac `data_find_code dest a (data_state_code (s:(C,FFI)data_state))
                       (data_state_stack_frame_sizes s)` THEN
  d2wpaux_triple_tac `a':data_v list#data_prog#num option` `args1:data_v list`
    `prog:data_prog` `ss:num option` THEN
  ASM_CASES_TAC `ALL_DISTINCT (ns:num list)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  MP_TAC(ISPECL [`args:num list`; `a:data_v list`; `c:data_to_word_config`; `l1:num`;
                 `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
                 `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`;
                 `a'':data_v spt`] cut_env_IMP_cut_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:(A word_loc)spt`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `a:data_v list`;
                 `ws:(A word_loc)list`; `dest:num option`;
                 `data_state_stack_frame_sizes (s:(C,FFI)data_state)`; `args1:data_v list`;
                 `prog:data_prog`; `ss:num option`; `names:num_set`; `a'':data_v spt`;
                 `(y1,y2):(A word_loc)spt#(A word_loc)spt`; `n:num`; `l:num`; `n0:num`;
                 `FST (data_to_word_comp c n (l + 2) h0:(A)wl_prog#num)`; `n:num`]
         find_code_thm_handler) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `args2:(A word_loc)list` (X_CHOOSE_THEN `n1:num`
    (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~bad_dest_args (dest:num option) (MAP adjust_var args)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP data_find_code o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_find_code"
                       with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_get_vars"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[bad_dest_args_def; GSYM LENGTH_EQ_NIL; LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP adjust_var ns)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[adjust_var_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[add_ret_loc_def; domain_adjust_sets] THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "wl_call_env"
                                              with Failure _ -> false)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) =
                            "data_to_word_gcProof_state_rel" with Failure _ -> false))) THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`wl_flush_state T (wl_state_stack_fupd (combin_K [])
       (wl_state_stack_max_fupd (combin_K (wl_state_stack_max (wl_call_env args2 ss
          (wl_push_env (y1,y2) (SOME (adjust_var n0,FST (data_to_word_comp c n (l + 2) h0:(A)wl_prog#num),n,l + 1)) (t:(A,C,FFI)wl_state))))) t))`;
       `SOME wl_TimeOut:((A)wl_result)option`] THEN
    CAKE_REWRITE_TAC[] THEN
    UNDISCH_TAC `option_le
      (wl_state_stack_max (wl_call_env args2 ss (wl_push_env (y1,y2) (SOME (adjust_var n0,FST (data_to_word_comp c n (l + 2) h0:(A)wl_prog#num),n,l + 1))
        (wl_dec_clock (t:(A,C,FFI)wl_state)))))
      (data_state_stack_max (data_call_env args1 ss (data_push_env a'' T
        (data_dec_clock (s:(C,FFI)data_state)))))` THEN
    UNDISCH_TAC `wl_state_ffi (t:(A,C,FFI)wl_state) = data_state_ffi (s:(C,FFI)data_state)` THEN
    REWRITE_TAC[wl_flush_state_def; wl_call_env_def; push_env_dec_clock_stack] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `data_evaluate (prog,data_call_env args1 ss (data_push_env a'' T
                  (data_dec_clock (s:(C,FFI)data_state))))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s2:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r0 = NONE:((data_v list,data_v)result)option) /\
                ~(r0 = SOME (Rerr (Rabort Rtype_error)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o
    SPECL [`a:data_v list`; `prog:data_prog`; `args1:data_v list`; `ss:num option`;
           `a'':data_v spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n1:num`; `n2:num`; `n:num`;
      `l:num`; `r0:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`;
      `wl_call_env args2 ss (wl_push_env (y1,y2) (SOME (adjust_var n0,FST (data_to_word_comp c n (l + 2) h0:(A)wl_prog#num),n,l + 1)) (wl_dec_clock (t:(A,C,FFI)wl_state)))`;
      `CONS (l1,l2) (locs:(num#num)list)`]) THEN
  ASM_REWRITE_TAC[termdep_rw; push_env_termdep] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_result_cases_tac `r0:((data_v list,data_v)result)option` THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THENL
   [(* the callee returned values *)
    ASM_CASES_TAC `LENGTH (v:data_v list) = LENGTH (ns:num list)` THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac] THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    d2wpaux_split_tac `data_pop_env (s2:(C,FFI)data_state)` THEN d2wpaux_res_tac THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_pop_env_const) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP pop_env_safe_for_space) THEN
      CAKE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
     [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
      REWRITE_TAC[option_DISTINCT; data_set_vars_def; data_state_INFO.ri_accfupds; K_THM] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        not (is_neg (fst (dest_imp (concl th)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ws2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
    d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `n:num`; `l:num`; `s2:(C,FFI)data_state`;
                   `t1:(A,C,FFI)wl_state`; `v:data_v list`; `ws2:(A word_loc)list`;
                   `CONS (l1,l2) (locs:(num#num)list)`; `ns:num list`; `a''':(C,FFI)data_state`]
           state_rel_pop_env_set_vars_IMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num`
      (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
      is_eq (lhand (concl th)) && is_var (rhs (lhand (concl th)))))) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_IMP_domain_EQ o CONJ (ASSUME
      `wl_evaluate (FST (data_to_word_comp c n1 n2 prog),
         wl_call_env args2 ss (wl_push_env (y1,y2) (SOME (adjust_var n0,FST (data_to_word_comp c n (l + 2) h0:(A)wl_prog#num),n,l + 1)) (wl_dec_clock (t:(A,C,FFI)wl_state)))) =
       (SOME (wl_Result (wl_Loc n l) ws2),t1)`) o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_pop_env"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Skip"] THEN
    MAP_EVERY EXISTS_TAC [`wl_set_vars (MAP adjust_var ns) ws2 (t2:(A,C,FFI)wl_state)`;
                          `NONE:((A)wl_result)option`] THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const) THEN
    REWRITE_TAC[wl_set_vars_def; data_set_vars_def; wl_state_INFO.ri_accfupds;
                data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    (* the callee raised an exception: the handler runs *)
    ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC D2WPAUX_NES_mono THEN
    MAP_EVERY EXISTS_TAC [`h0:data_prog`; `data_set_var n0 v (s2:(C,FFI)data_state)`;
                          `res:((data_v list,data_v)result)option`] THEN
    ASM_REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[GSYM data_set_var_def];
    ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[mk_loc_jump_exc; D2WPAUX_jump_exc_call_push_SOME] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:A word_loc` (X_CHOOSE_THEN `l5:num`
    (X_CHOOSE_THEN `l6:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `LENGTH (data_state_stack (s2:(C,FFI)data_state)) = LENGTH (locs:(num#num)list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP eval_push_env_T_Raise_IMP_stack_length o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_evaluate" &&
                           can (find_term (fun t -> t = `prog:data_prog`)) (concl th)
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `LASTN (LENGTH (data_state_stack (s2:(C,FFI)data_state)) + 1)
                 (CONS (l1,l2) locs) = CONS (l5,l6) (ll:(num#num)list)` THEN
  REWRITE_TAC[ASSUME `LENGTH (data_state_stack (s2:(C,FFI)data_state)) =
                      LENGTH (locs:(num#num)list)`; LASTN_ADD1; CONS_11; PAIR_EQ] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && mem (fst (dest_var (rhs (concl th)))) ["l5"; "l6"; "ll"]))) THEN
  d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_IMP_domain_EQ_Exc o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_clock o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
                     with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o SPECL [`adjust_var n0`; `w:A word_loc`] o
    MATCH_MP D2WPAUX_jump_exc_handler_return o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
                     with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o
    SPECL [`a:data_v list`; `prog:data_prog`; `args1:data_v list`; `ss:num option`;
           `a'':data_v spt`; `v:data_v`; `s2:(C,FFI)data_state`] o
    check (fun th -> is_forall (concl th) &&
                     can (find_term (fun t -> t = `h0:data_prog`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `n:num`; `l + 2`; `l1:num`;
      `l2:num`; `res:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`;
      `wl_set_var (adjust_var n0) w (t1:(A,C,FFI)wl_state)`; `locs:(num#num)list`]) THEN
  ASM_REWRITE_TAC[D2WPAUX_set_var_accs; termdep_rw; push_env_termdep] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[termdep_rw; push_env_termdep]) THEN
  ASM_REWRITE_TAC[];
    d2wpaux_call_abort_tac;
    d2wpaux_call_abort_tac]);;

(* HOL4 data_compile_correct [Call] *)
let D2WPAUX_Call = prove
 (`!ret dest args handler (s:(C,FFI)data_state).
     (!xs prog args1 ss.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        ret = NONE /\ handler = NONE /\ ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog (data_call_env args1 ss (data_dec_clock s))) /\
     (!xs ns names prog args1 ss env h n x s2.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        ret = SOME (ns,names) /\ ALL_DISTINCT ns /\
        data_cut_env names (data_state_locals s) = SOME env /\
        ~(data_state_clock s = 0) /\
        data_evaluate (prog,data_call_env args1 ss
                               (data_push_env env (IS_SOME handler) (data_dec_clock s))) =
          (SOME (Rerr (Rraise x)),s2) /\
        handler = SOME (n,h) ==>
        D2WPAUX_correct (:A) h (data_set_var n x s2)) /\
     (!xs ns names prog args1 ss env.
        data_get_vars args (data_state_locals s) = SOME xs /\
        data_find_code dest xs (data_state_code s) (data_state_stack_frame_sizes s) =
          SOME (args1,prog,ss) /\
        ret = SOME (ns,names) /\ ALL_DISTINCT ns /\
        data_cut_env names (data_state_locals s) = SOME env /\
        ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog
          (data_call_env args1 ss (data_push_env env (IS_SOME handler) (data_dec_clock s))))
     ==> D2WPAUX_correct (:A) (data_Call ret dest args handler) s`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ret:(num list#num_set)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [STRIP_TAC THEN MATCH_MP_TAC D2WPAUX_Call_NONE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `a:num list#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:num list` (X_CHOOSE_THEN `names:num_set` SUBST1_TAC)) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  STRUCT_CASES_TAC(ISPEC `handler:(num#data_prog)option` (cases "option")) THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT; option_INJ] THENL
   [STRIP_TAC THEN MATCH_MP_TAC D2WPAUX_Call_SOME_NONE THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`xs:data_v list`; `ns:num list`; `names:num_set`;
      `prog:data_prog`; `args1:data_v list`; `ss:num option`; `env:data_v spt`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `a:num#data_prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `h0:data_prog` SUBST1_TAC)) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  MATCH_MP_TAC D2WPAUX_Call_SOME_SOME THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`xs:data_v list`; `ns:num list`; `names:num_set`;
      `prog:data_prog`; `args1:data_v list`; `ss:num option`; `env:data_v spt`;
      `h0:data_prog`; `n0:num`; `x:data_v`; `s2:(C,FFI)data_state`] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "data_set_var"
                                                with Failure _ -> false)) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPECL [`xs:data_v list`; `ns:num list`; `names:num_set`;
      `prog:data_prog`; `args1:data_v list`; `ss:num option`; `env:data_v spt`] o
      check (fun th -> is_forall (concl th) &&
                       not (can (find_term (fun t -> try fst(dest_const t) = "data_set_var"
                                                     with Failure _ -> false)) (concl th))))] THEN
  ASM_REWRITE_TAC[]);;

(* a bound for powers of 2 *)
let D2WPAUX_LT_2EXP = prove
 (`!k m n. k < 2 EXP m /\ m <= n ==> k < 2 EXP n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP m` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

(* the header of an evaluated thunk can be encoded *)
let D2WPAUX_encode_header_thunk = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     ?h. encode_header c (8 + 6) 1 = SOME (h:A word)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[encode_header_def] THEN
  SUBGOAL_THEN `8 + 6 < 2 EXP ((dimindex(:A) - data_to_word_config_len_size c) - 2) /\
                8 + 6 < dimword(:A) DIV 16 /\ 1 < 2 EXP (dimindex(:A) - 4) /\
                1 < 2 EXP data_to_word_config_len_size c`
    (fun th -> REWRITE_TAC[th] THEN MESON_TAC[]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC D2WPAUX_LT_2EXP THEN EXISTS_TAC `6` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC D2WPAUX_LT_2EXP THEN EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    MATCH_MP_TAC D2WPAUX_LT_2EXP THEN EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(* a thunk is a reference to a Thunk *)
let D2WPAUX_dest_thunk_IsThunk = prove
 (`!a refs ev v.
     data_dest_thunk a refs = data_IsThunk ev v ==>
     ?p. a = data_RefPtr F p /\ lookup p refs = SOME (bvl_Thunk ev v)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  REWRITE_TAC[data_dest_thunk_def; distinctness "data_dest_thunk_ret"; injectivity "data_v"] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[distinctness "data_dest_thunk_ret"; injectivity "data_dest_thunk_ret"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1]);;

(* state_rel after a Force returns the value z of the thunk in the word w *)
let D2WPAUX_state_rel_return_value = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs z w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (z,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_flush_state F s) (wl_flush_state F t)
       (SOME [(z,w)]) locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_flush_state_def; wl_flush_state_def;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_def; IS_SOME_DEF] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP D2WPAUX_option_le_locals_0 o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "option_le" &&
                           can (find_term (fun t -> is_const t &&
                                                    fst(dest_const t) = "wl_stack_size"))
                             (concl th)
                       with Failure _ -> false));
    ALL_TAC] THEN
  SUBGOAL_THEN `toAList (sptree_inter (LN:(A word_loc)spt) (adjust_set (LN:data_v spt))) = []`
    SUBST1_TAC THENL
   [REWRITE_TAC[sptree_inter_def; toAList_def; foldi_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[foldi_def];
    ALL_TAC] THEN
  REWRITE_TAC[join_env_def; FILTER; MAP; APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" &&
        is_comb (rand (concl th)) &&
        fst(dest_const(fst(strip_comb(rand (concl th))))) = "CONS"
    with Failure _ -> false)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[]);;

(* state_rel after a Force assigns the value z of the thunk in the word w *)
let D2WPAUX_state_rel_force_assign = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs z w names env dest.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME env /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (z,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest z (data_state_locals_fupd (combin_K env) s))
       (wl_set_var (adjust_var dest) w t) NONE locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def; wl_set_var_def;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[lookup_insert; adjust_var_def; ARITH_RULE `~(0 = 2 * n + 2)`];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `data_cut_env names (data_state_locals (s:(C,FFI)data_state)) = SOME env` THEN
    REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `IS_SOME (lookup k (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state))
                                           (names:num_set))))` THEN
    REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN COND_CASES_TAC THEN
    REWRITE_TAC[IS_SOME_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC (REWRITE_RULE[APPEND] memory_rel_insert) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" &&
        is_comb (rand (concl th)) &&
        fst(dest_const(fst(strip_comb(rand (concl th))))) = "CONS"
    with Failure _ -> false)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM; APPEND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC MEM_join_env_cut_env THEN
  MAP_EVERY EXISTS_TAC [`names:num_set`; `env:data_v spt`] THEN ASM_REWRITE_TAC[]);;

(* state_rel implies good_dimindex *)
let D2WPAUX_state_rel_good_dimindex = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==> good_dimindex (:A)`,
  SIMP_TAC[data_to_word_gcProof_state_rel_thm]);;

(* the memory facts of a Force of a pointer to a thunk: the header x at the *)
(* real address a, and the three cases of the code (inlined pointer,        *)
(* evaluated, not evaluated)                                                 *)
let D2WPAUX_force_ptr_facts = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm p w1 vars ev z.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr F p,wl_Word w1) vars) /\
     lookup p refs = SOME (bvl_Thunk ev z) /\ good_dimindex (:A) /\ bit 0 w1 ==>
     ?a x. get_real_addr c st w1 = SOME a /\ m a = wl_Word x /\ a IN dm /\
       ((ev = Evaluated /\
         ~(word_and x (word 60) = word ((8 + 6) * 4)) /\
         ~(word_and x (word 60) = word ((0 + 6) * 4)) /\
         memory_rel c be ts refs sp st m dm (CONS (z,wl_Word w1) vars)) \/
        (word_add a bytes_in_word IN dm /\
         memory_rel c be ts refs sp st m dm
           (CONS (z,m (word_add a bytes_in_word)) (CONS (data_RefPtr F p,wl_Word w1) vars)) /\
         ((ev = Evaluated /\ word_and x (word 60) = word ((8 + 6) * 4)) \/
          (ev = NotEvaluated /\ ~(word_and x (word 60) = word ((8 + 6) * 4)) /\
           word_and x (word 60) = word ((0 + 6) * 4)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `F`; `p:num`; `wl_Word w1:A word_loc`;
                 `vars:(data_v#A word_loc)list`; `ev:thunk_mode`; `z:data_v`]
         memory_rel_Thunk_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w1:A word`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w1:A word = w`)) THEN
  MAP_EVERY EXISTS_TAC [`a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[word_test_lemma1; word_test_lemma2] THEN
  UNDISCH_TAC `bit 5 (x:A word) <=> ev = Evaluated` THEN
  MP_TAC(ISPEC `ev:thunk_mode` (cases "thunk_mode")) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[distinctness "thunk_mode"] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* the first two assignments of the Force code for a pointer *)
let D2WPAUX_force_ptr_prefix = prove
 (`!c v (t:(A,C,FFI)wl_state) w1 a x rest.
     shift_length c < dimindex (:A) /\ good_dimindex (:A) /\
     lookup v (wl_state_locals t) = SOME (wl_Word w1) /\
     get_real_addr c (wl_state_store t) w1 = SOME a /\
     wl_state_memory t a = wl_Word x /\ a IN wl_state_mdomain t ==>
     wl_evaluate (data_to_word_list_Seq
        [wl_Assign 1 (real_addr c v);
         wl_Assign 3 (wl_Op asm_And [wl_Load (wl_Var 1); wl_Const (word 60)]); rest], t) =
     wl_evaluate (rest, wl_set_var 3 (wl_Word (word_and x (word 60)))
                          (wl_set_var 1 (wl_Word a) t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c v) = SOME (wl_Word (a:A word))` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w1:A word` THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def; d2wpaux_clause wl_evaluate_def "wl_Seq";
              wl_fix_clock_evaluate] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Assign"] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN
  SIMP[wl_word_exp_def; MAP; the_words_def; wl_get_var_def; D2WPAUX_set_var_accs;
       lookup_insert; wl_mem_load_def; word_op_def; OPTION_MAP_DEF; ITLIST; WORD_AND_NOT0]);;

(* state_rel ignores the variables 1 and 3 *)
let D2WPAUX_state_rel_set_var_3_1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs x y.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_set_var 3 x (wl_set_var 1 y t)) v locs <=>
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM; state_rel_insert_3_1]);;

(* flush_state F forgets the locals *)
let D2WPAUX_flush_F_set_var = prove
 (`!v x (t:(A,C,FFI)wl_state). wl_flush_state F (wl_set_var v x t) = wl_flush_state F t`,
  REWRITE_TAC[wl_flush_state_def; wl_set_var_def; wl_state_INFO.ri_fupdfupds;
              K_o_THM] THEN
  REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

(* the variable of a Force assignment and the scratch variables 1 and 3 *)
let D2WPAUX_set_var_adjust_3_1 = prove
 (`!k w x y (t:(A,C,FFI)wl_state).
     wl_set_var (adjust_var k) w (wl_set_var 3 x (wl_set_var 1 y t)) =
     wl_set_var 3 x (wl_set_var 1 y (wl_set_var (adjust_var k) w t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS `insert 3 (x:A word_loc) (insert (adjust_var k) (w:A word_loc)
               (insert 1 (y:A word_loc) (wl_state_locals (t:(A,C,FFI)wl_state))))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC insert_swap; AP_TERM_TAC THEN MATCH_MP_TAC insert_swap] THEN
  REWRITE_TAC[adjust_var_NEQ]);;

(* the load of the second word of a thunk (its value or its code argument) *)
let D2WPAUX_force_load_next = prove
 (`!(t:(A,C,FFI)wl_state) a y.
     word_add a bytes_in_word IN wl_state_mdomain t ==>
     wl_word_exp (wl_set_var 3 y (wl_set_var 1 (wl_Word a) t))
       (wl_Load (wl_Op asm_Add [wl_Var 1; wl_Const bytes_in_word])) =
     SOME (wl_state_memory t (word_add a bytes_in_word))`,
  REPEAT STRIP_TAC THEN
  SIMP[wl_word_exp_def; MAP; the_words_def; wl_get_var_def; D2WPAUX_set_var_accs;
       lookup_insert; ARITH_EQ; word_op_def; OPTION_MAP_DEF; ITLIST; WORD_ADD_0;
       wl_mem_load_def] THEN
  ASM_REWRITE_TAC[]);;

(* dec_clock does not look at the locals *)
let D2WPAUX_dec_clock_set_var = prove
 (`!k v (t:(A,C,FFI)wl_state).
     wl_dec_clock (wl_set_var k v t) = wl_set_var k v (wl_dec_clock t)`,
  REWRITE_TAC[wl_dec_clock_def; wl_set_var_def; wl_state_component_equality;
              wl_state_INFO.ri_accfupds; K_THM]);;

(* push_env does not look at the locals *)
let D2WPAUX_push_env_set_var = prove
 (`!y opt k v (t:(A,C,FFI)wl_state).
     wl_push_env y opt (wl_set_var k v t) = wl_set_var k v (wl_push_env y opt t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `opt:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `q:num#(A)wl_prog#num#num`
    SUBST1_TAC)) THENL
   [ALL_TAC;
    MP_TAC(ISPEC `q:num#(A)wl_prog#num#num` D2WPAUX_triple_cases) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[wl_push_env_def; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM; LET_DEF;
              LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (y:(A word_loc)spt#(A word_loc)spt))
                  (wl_state_permute (t:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

(* call_env replaces the locals *)
let D2WPAUX_call_env_set_var = prove
 (`!args ss k v (t:(A,C,FFI)wl_state).
     wl_call_env args ss (wl_set_var k v t) = wl_call_env args ss t`,
  REWRITE_TAC[wl_call_env_def; wl_set_var_def; wl_state_component_equality;
              wl_state_INFO.ri_accfupds; K_THM]);;

(* flush_state T forgets the locals *)
let D2WPAUX_flush_T_set_var = prove
 (`!v x (t:(A,C,FFI)wl_state). wl_flush_state T (wl_set_var v x t) = wl_flush_state T t`,
  REWRITE_TAC[wl_flush_state_def; wl_set_var_def; wl_state_component_equality;
              wl_state_INFO.ri_accfupds; K_THM]);;

(* state_rel with some more values in front of the locals *)
let D2WPAUX_state_rel_add_vals = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs vs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (APPEND vs (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 s t (SOME vs) locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" &&
        is_comb (rand (concl th)) &&
        not (fst(dest_const(fst(strip_comb(rand (concl th))))) = "APPEND" &&
             can (find_term (fun t -> try fst(dest_const t) = "the_global"
                                      with Failure _ -> false))
                 (lhand (rand (concl th))))
    with Failure _ -> false)) THEN
  REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]);;

(* the state of a tail call with the values ws of the arguments xs *)
let D2WPAUX_state_rel_call_env_vals = prove
 (`!c l5 l6 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs xs ws l1 l2 ss.
     data_to_word_gcProof_state_rel c l5 l6 s t (SOME (ZIP xs ws)) locs /\
     LENGTH ws = LENGTH xs ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_call_env xs ss (data_dec_clock s))
       (wl_call_env (CONS (wl_Loc l1 l2) ws) ss (wl_dec_clock t)) NONE locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_call_env_def; wl_call_env_def;
              data_dec_clock_def; wl_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CAKE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)) =
                size_of_stack (data_state_stack (s:(C,FFI)data_state))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(MATCH_MP stack_rel_IMP_size_of_stack th));
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_fromList2; EVEN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[lookup_fromList; LENGTH; LT_0; EL; HD];
    REWRITE_TAC[lookup_adjust_var_fromList2; lookup_fromList] THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF];
    REWRITE_TAC[option_le_max_right; option_le_refl];
    REWRITE_TAC[option_le_max] THEN CONJ_TAC THEN
    REWRITE_TAC[option_le_max_right; option_le_refl] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" with Failure _ -> false)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN DISJ1_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC GCP2AUX_MEM_join_env_call_env THEN
  EXISTS_TAC `wl_Loc l1 l2:A word_loc` THEN ASM_REWRITE_TAC[]);;

(* find_code of a known location *)
let D2WPAUX_data_find_code_SOME = prove
 (`!loc (args:data_v list) (code:(num#A)spt) (sfs:B spt) args1 prog ss.
     data_find_code (SOME loc) args code sfs = SOME (args1,prog,ss) ==>
     lookup loc code = SOME (LENGTH args,prog) /\ args1 = args /\ ss = lookup loc sfs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_find_code_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `a:num#A` PAIR_SURJECTIVE) THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* more accessors of wl_set_var *)
let D2WPAUX_set_var_accs2 = prove
 (`!v x (s:(A,C,FFI)wl_state).
     wl_state_stack_size (wl_set_var v x s) = wl_state_stack_size s /\
     wl_state_permute (wl_set_var v x s) = wl_state_permute s /\
     wl_state_locals_size (wl_set_var v x s) = wl_state_locals_size s`,
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 data_compile_correct [Force] *)
let D2WPAUX_Force = prove
 (`!ret loc src (s:(C,FFI)data_state).
     (!thunk_v v dest names prog args1 ss env.
        data_get_var src (data_state_locals s) = SOME thunk_v /\
        data_dest_thunk thunk_v (data_state_refs s) = data_IsThunk NotEvaluated v /\
        data_find_code (SOME loc) [thunk_v; v] (data_state_code s)
          (data_state_stack_frame_sizes s) = SOME (args1,prog,ss) /\
        ret = SOME (dest,names) /\
        data_cut_env names (data_state_locals s) = SOME env /\
        ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog
          (data_call_env args1 ss (data_push_env env F (data_dec_clock s)))) /\
     (!thunk_v v prog args1 ss.
        data_get_var src (data_state_locals s) = SOME thunk_v /\
        data_dest_thunk thunk_v (data_state_refs s) = data_IsThunk NotEvaluated v /\
        data_find_code (SOME loc) [thunk_v; v] (data_state_code s)
          (data_state_stack_frame_sizes s) = SOME (args1,prog,ss) /\
        ret = NONE /\ ~(data_state_clock s = 0) ==>
        D2WPAUX_correct (:A) prog (data_call_env args1 ss (data_dec_clock s)))
     ==> D2WPAUX_correct (:A) (data_Force ret loc src) s`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  d2wpaux_open_tac (d2wpaux_clause data_evaluate_def "data_Force") THEN
  REWRITE_TAC[force_thunk_def] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `header:A word` o MATCH_MP D2WPAUX_encode_header_thunk) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[FST] THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_If"]) THEN
  (d2wpaux_split_tac `data_get_var src (data_state_locals (s:(C,FFI)data_state))`) THEN
  (d2wpaux_split_tac `data_dest_thunk a (data_state_refs (s:(C,FFI)data_state))`) THEN
  (FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_dest_thunk_IsThunk) THEN
  d2wpaux_subst_var_tac "a" THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                 `locs:(num#num)list`; `src:num`; `data_RefPtr F p`] state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_memory_rel) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_lookup)) THEN
  DISCH_THEN(MP_TAC o SPECL [`src:num`; `data_RefPtr F p`; `w:A word_loc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def; wl_get_var_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `?b. wl_word_cmp asm_Test (w:A word_loc) (wl_Word (word 1)) = SOME b /\
                    (b <=> (?l1 l2. w = wl_Loc l1 l2) \/ (?w1. w = wl_Word w1 /\ ~bit 0 w1))`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:A word_loc` (cases "word_loc")) THEN
    DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[wl_word_cmp_def; injectivity "word_loc"; distinctness "word_loc"] THENL
     [REWRITE_TAC[data_to_word_gcProof_word_and_one_eq_0_iff; option_INJ] THEN MESON_TAC[];
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                     `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                     `locs:(num#num)list`; `src:num`; `F`; `p:num`; `a0':num`; `a1':num`]
             state_rel_get_var_RefPtr_Loc) THEN
      ASM_REWRITE_TAC[data_get_var_def; wl_get_var_def] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[option_INJ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_good_dimindex) THEN
  COND_CASES_TAC) THENL
  [(MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
                 `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
                 `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
                 `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
                 `F`; `p:num`; `w:A word_loc`;
                 `APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
                   (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
                                   (adjust_set (data_state_locals s)))))
                   (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
                      (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))`;
                 `a0:thunk_mode`; `a1:data_v`] memory_rel_Thunk_inlined) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[])) THEN
  (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:num#num_set` SUBST_ALL_TAC)
    (ISPEC `ret:(num#num_set)option` (cases "option")) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[]) THENL
  [(RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN d2wpaux_res_conj_tac THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Return"; wl_get_vars_def; wl_get_var_def] THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`wl_flush_state F (t:(A,C,FFI)wl_state)`;
                        `SOME (wl_Result (wl_Loc l1 l2) [w]):((A)wl_result)option`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  REWRITE_TAC[distinctness "wl_result"; option_INJ; injectivity "wl_result"] THEN
  CONJ_TAC THENL [REWRITE_TAC D2WPAUX_REC_RWS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `[w:A word_loc]` THEN REWRITE_TAC[LENGTH; ZIP] THEN
  MATCH_MP_TAC D2WPAUX_state_rel_return_value THEN ASM_REWRITE_TAC[]);
   (MP_TAC(ISPEC `rr:num#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `dest:num` (X_CHOOSE_THEN `names:num_set` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[]) THEN
  (d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_res_tac) THEN
  (REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Assign"; wl_word_exp_def]) THEN
  (REWRITE_TAC[wl_get_var_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`wl_set_var (adjust_var dest) w (t:(A,C,FFI)wl_state)`;
                        `NONE:((A)wl_result)option`] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
     (data_set_var dest a1 (data_state_locals_fupd (combin_K a') (s:(C,FFI)data_state)))
     (wl_set_var (adjust_var dest) w (t:(A,C,FFI)wl_state)) NONE locs` ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_state_rel_force_assign THEN EXISTS_TAC `names:num_set` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN SIMP_TAC[])];
   (SUBGOAL_THEN `?w1:A word. w = wl_Word w1 /\ bit 0 w1`
    (X_CHOOSE_THEN `w1:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
   [MP_TAC(ISPEC `w:A word_loc` (cases "word_loc")) THEN
    UNDISCH_TAC `~((?l1 l2. (w:A word_loc) = wl_Loc l1 l2) \/
                   (?w1. w = wl_Word w1 /\ ~bit 0 w1))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `shift_length c < dimindex (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] D2WPAUX_force_ptr_facts) o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[]) THEN
  (DISCH_THEN(MP_TAC o SPECL [`a0:thunk_mode`; `a1:data_v`]) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `adjust_var src`; `t:(A,C,FFI)wl_state`;
                 `w1:A word`; `a:A word`; `x:A word`] D2WPAUX_force_ptr_prefix) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_If"; wl_get_var_def; D2WPAUX_set_var_accs;
              lookup_insert; ARITH_EQ; wl_get_var_imm_def; wl_word_cmp_def] THEN
  CAKE_REWRITE_TAC[]) THENL
  [(REWRITE_TAC[wl_word_cmp_def] THEN CAKE_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a0 = Evaluated`)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:num#num_set` SUBST_ALL_TAC)
    (ISPEC `ret:(num#num_set)option` (cases "option")) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[]) THENL
  [(RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN d2wpaux_res_conj_tac THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Return"; wl_get_vars_def; wl_get_var_def;
              D2WPAUX_set_var_accs; lookup_insert; ARITH_EQ; adjust_var_NEQ] THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[D2WPAUX_flush_F_set_var] THEN
  MAP_EVERY EXISTS_TAC [`wl_flush_state F (t:(A,C,FFI)wl_state)`;
                        `SOME (wl_Result (wl_Loc l1 l2) [wl_Word w1]):((A)wl_result)option`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  REWRITE_TAC[distinctness "wl_result"; option_INJ; injectivity "wl_result"] THEN
  CONJ_TAC THENL [REWRITE_TAC D2WPAUX_REC_RWS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `[wl_Word w1:A word_loc]` THEN REWRITE_TAC[LENGTH; ZIP] THEN
  MATCH_MP_TAC D2WPAUX_state_rel_return_value THEN ASM_REWRITE_TAC[]);
   (MP_TAC(ISPEC `rr:num#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `dest:num` (X_CHOOSE_THEN `names:num_set` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_res_tac) THEN
  (REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Assign"; wl_word_exp_def] THEN
  REWRITE_TAC[wl_get_var_def; D2WPAUX_set_var_accs; lookup_insert; adjust_var_NEQ] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`wl_set_var (adjust_var dest) (wl_Word w1) (wl_set_var 3 (wl_Word (word_and x (word 60)))
       (wl_set_var 1 (wl_Word a) (t:(A,C,FFI)wl_state)))`;
    `NONE:((A)wl_result)option`] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[D2WPAUX_set_var_adjust_3_1; D2WPAUX_state_rel_set_var_3_1] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
     (data_set_var dest a1 (data_state_locals_fupd (combin_K a') (s:(C,FFI)data_state)))
     (wl_set_var (adjust_var dest) (wl_Word w1) (t:(A,C,FFI)wl_state)) NONE locs` ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_state_rel_force_assign THEN EXISTS_TAC `names:num_set` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[D2WPAUX_set_var_accs] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN SIMP_TAC[]) THEN
  (SIMP_TAC[D2WPAUX_set_var_accs])];
   (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a0 = Evaluated`)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:num#num_set` SUBST_ALL_TAC)
    (ISPEC `ret:(num#num_set)option` (cases "option")) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[]) THENL
  [(REWRITE_TAC[wl_word_cmp_def] THEN CAKE_REWRITE_TAC[]) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN d2wpaux_res_conj_tac THEN
  REWRITE_TAC[data_to_word_list_Seq_def; d2wpaux_clause wl_evaluate_def "wl_Seq";
              wl_fix_clock_evaluate; d2wpaux_clause wl_evaluate_def "wl_Assign"] THEN
  ASM_SIMP_TAC[D2WPAUX_force_load_next] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[d2wpaux_clause wl_evaluate_def "wl_Return"; wl_get_vars_def; wl_get_var_def;
       D2WPAUX_set_var_accs; lookup_insert; ARITH_EQ] THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[D2WPAUX_flush_F_set_var]) THEN
  (MAP_EVERY EXISTS_TAC [`wl_flush_state F (t:(A,C,FFI)wl_state)`;
    `SOME (wl_Result (wl_Loc l1 l2)
       [wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)]):((A)wl_result)option`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  REWRITE_TAC[distinctness "wl_result"; option_INJ; injectivity "wl_result"] THEN
  CONJ_TAC THENL [REWRITE_TAC D2WPAUX_REC_RWS THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (EXISTS_TAC `[wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)]` THEN
  REWRITE_TAC[LENGTH; ZIP; ARITH_RULE `SUC 0 = 1`] THEN
  MATCH_MP_TAC D2WPAUX_state_rel_return_value THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" with Failure _ -> false)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);
   (REWRITE_TAC[wl_word_cmp_def] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `rr:num#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `dest:num` (X_CHOOSE_THEN `names:num_set` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  d2wpaux_res_tac THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Assign"] THEN
  ASM_SIMP_TAC[D2WPAUX_force_load_next] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`wl_set_var (adjust_var dest) (wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word))
      (wl_set_var 3 (wl_Word (word ((8 + 6) * 4))) (wl_set_var 1 (wl_Word a) t))`;
    `NONE:((A)wl_result)option`] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[D2WPAUX_set_var_adjust_3_1; D2WPAUX_state_rel_set_var_3_1] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
     (data_set_var dest a1 (data_state_locals_fupd (combin_K a') (s:(C,FFI)data_state)))
     (wl_set_var (adjust_var dest) (wl_state_memory t (word_add a bytes_in_word))
        (t:(A,C,FFI)wl_state)) NONE locs` ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_state_rel_force_assign THEN EXISTS_TAC `names:num_set` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" with Failure _ -> false)) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[D2WPAUX_set_var_accs] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN SIMP_TAC[D2WPAUX_set_var_accs])];
   (SUBGOAL_THEN `~(word ((0 + 6) * 4) = word ((8 + 6) * 4):A word)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(word_and x (word 60) = word ((8 + 6) * 4):A word)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[wl_word_cmp_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a0 = NotEvaluated`)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[])) THEN
  (REWRITE_TAC[data_to_word_list_Seq_def; d2wpaux_clause wl_evaluate_def "wl_Seq";
              wl_fix_clock_evaluate; d2wpaux_clause wl_evaluate_def "wl_Assign"] THEN
  ASM_SIMP_TAC[D2WPAUX_force_load_next] THEN CAKE_REWRITE_TAC[] THEN SIMP[]) THEN
  (d2wpaux_split_tac `data_find_code (SOME loc) [data_RefPtr F p; a1]
                       (data_state_code (s:(C,FFI)data_state)) (data_state_stack_frame_sizes s)`) THEN
  (d2wpaux_triple_tac `a':data_v list#data_prog#num option` `args1:data_v list`
    `prog:data_prog` `ss:num option` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_data_find_code_SOME) THEN
  d2wpaux_subst_var_tac "args1" THEN d2wpaux_subst_var_tac "ss" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP) THEN
  SUBGOAL_THEN `lookup loc (wl_state_code (t:(A,C,FFI)wl_state)) =
                SOME (2 + 1,FST (data_to_word_comp c loc 2 prog))` ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_to_word_gcProof_code_rel_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state)
     (SOME (ZIP [data_RefPtr F p; a1]
                [wl_Word w1; wl_state_memory t (word_add a bytes_in_word)])) locs`
    ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_state_rel_add_vals THEN ASM_REWRITE_TAC[ZIP; APPEND] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "memory_rel" with Failure _ -> false)) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:num#num_set` SUBST_ALL_TAC)
    (ISPEC `ret:(num#num_set)option` (cases "option")) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[]) THENL
  [(SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC]) THEN
  (REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Call"; wl_get_vars_def; wl_get_var_def;
              D2WPAUX_set_var_accs; lookup_insert; ARITH_EQ; adjust_var_NEQ] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def;
              D2WPAUX_set_var_accs; D2WPAUX_set_var_accs2] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN CAKE_REWRITE_TAC[]) THEN
  (REWRITE_TAC[D2WPAUX_flush_T_set_var; D2WPAUX_dec_clock_set_var; D2WPAUX_call_env_set_var] THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    MAP_EVERY EXISTS_TAC [`wl_flush_state T (t:(A,C,FFI)wl_state)`;
                          `SOME wl_TimeOut:((A)wl_result)option`] THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC D2WPAUX_REC_RWS;
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `data_evaluate (prog,data_call_env [data_RefPtr F p; a1]
                  (lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state)))
                  (data_dec_clock s))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s0:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `r0:((data_v list,data_v)result)option = NONE` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  MP_TAC(ISPEC `r0:((data_v list,data_v)result)option` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rr:(data_v list,data_v)result`
    SUBST_ALL_TAC) THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac) THEN
  (SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
     (data_call_env [data_RefPtr F p; a1] (lookup loc (data_state_stack_frame_sizes s))
        (data_dec_clock (s:(C,FFI)data_state)))
     (wl_call_env [wl_Loc l1 l2; wl_Word w1; wl_state_memory t (word_add a bytes_in_word)]
        (lookup loc (data_state_stack_frame_sizes s)) (wl_dec_clock (t:(A,C,FFI)wl_state)))
     NONE locs` ASSUME_TAC THENL
   [MATCH_MP_TAC D2WPAUX_state_rel_call_env_vals THEN
    MAP_EVERY EXISTS_TAC [`l1:num`; `l2:num`] THEN ASM_REWRITE_TAC[LENGTH];
    ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o
    SPECL [`data_RefPtr F p`; `a1:data_v`; `prog:data_prog`; `[data_RefPtr F p; a1]`;
           `lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state))`]) THEN
  ASM_REWRITE_TAC[data_get_var_def]) THEN
  (DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `loc:num`; `2`; `l1:num`;
      `l2:num`; `SOME rr:((data_v list,data_v)result)option`; `s0:(C,FFI)data_state`;
      `wl_call_env [wl_Loc l1 l2; wl_Word w1; wl_state_memory t (word_add a bytes_in_word)]
         (lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state)))
         (wl_dec_clock (t:(A,C,FFI)wl_state))`;
      `locs:(num#num)list`]) THEN
  ASM_REWRITE_TAC[termdep_rw]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~wl_bad_fun_return (res1:((A)wl_result)option)` ASSUME_TAC THENL
   [ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THEN
    ASM_REWRITE_TAC[wl_bad_fun_return_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    d2wpaux_result_cases_tac `SOME rr:((data_v list,data_v)result)option` THEN
    REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[wl_bad_fun_return_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `res1:((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  REWRITE_TAC[D2WPAUX_jump_exc_call_env_dec_clock] THEN CAKE_REWRITE_TAC[]);
   (MP_TAC(ISPEC `rr:num#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `dest:num` (X_CHOOSE_THEN `names:num_set` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_split_tac `data_cut_env names (data_state_locals (s:(C,FFI)data_state))`) THEN
  (SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    SIMP_TAC[data_to_word_gcProof_state_rel_thm];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`;
                 `a'':data_v spt`] cut_env_IMP_cut_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:(A word_loc)spt`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Call"; wl_get_vars_def; wl_get_var_def;
              D2WPAUX_set_var_accs; lookup_insert; ARITH_EQ; adjust_var_NEQ] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def;
              D2WPAUX_set_var_accs; D2WPAUX_set_var_accs2] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[domain_adjust_sets; ALL_DISTINCT; MEM; NOT_CLAUSES] THEN
  SIMP_TAC[data_to_word_gcProof_cut_envs_adjust_sets_insert_ODD; ARITH_ODD; ODD] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[D2WPAUX_dec_clock_set_var; D2WPAUX_push_env_set_var; D2WPAUX_call_env_set_var]) THEN
  (SUBGOAL_THEN `data_to_word_gcProof_state_rel c n l
     (data_call_env [data_RefPtr F p; a1] (lookup loc (data_state_stack_frame_sizes s))
        (data_push_env a'' F (data_dec_clock (s:(C,FFI)data_state))))
     (wl_call_env [wl_Loc n l; wl_Word w1; wl_state_memory t (word_add a bytes_in_word)]
        (lookup loc (data_state_stack_frame_sizes s))
        (wl_push_env (y1,y2) NONE (wl_dec_clock (t:(A,C,FFI)wl_state))))
     NONE (CONS (l1,l2) locs)` ASSUME_TAC THENL
   [MATCH_MP_TAC state_rel_call_env_push THEN EXISTS_TAC `names:num_set` THEN
    ASM_REWRITE_TAC[LENGTH];
    ALL_TAC]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP D2WPAUX_state_rel_IMP o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "wl_call_env"
                                              with Failure _ -> false)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) =
                            "data_to_word_gcProof_state_rel" with Failure _ -> false))) THEN
  ASM_CASES_TAC `data_state_clock (s:(C,FFI)data_state) = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_res_tac THEN
    ASM_REWRITE_TAC[] THEN d2wpaux_exists_pair_tac THEN CAKE_REWRITE_TAC[] THEN
    UNDISCH_TAC `option_le
      (wl_state_stack_max (wl_call_env [wl_Loc n l; wl_Word w1;
          wl_state_memory t (word_add a bytes_in_word)]
        (lookup loc (data_state_stack_frame_sizes s))
        (wl_push_env (y1,y2) NONE (wl_dec_clock (t:(A,C,FFI)wl_state)))))
      (data_state_stack_max (data_call_env [data_RefPtr F p; a1]
        (lookup loc (data_state_stack_frame_sizes s))
        (data_push_env a'' F (data_dec_clock (s:(C,FFI)data_state)))))` THEN
    UNDISCH_TAC `wl_state_ffi (t:(A,C,FFI)wl_state) = data_state_ffi (s:(C,FFI)data_state)` THEN
    REWRITE_TAC[wl_flush_state_def; wl_call_env_def; push_env_dec_clock_stack] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM;
                D2WPAUX_set_var_accs] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF;
                LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
    SIMP_TAC[];
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `data_evaluate (prog,data_call_env [data_RefPtr F p; a1]
                  (lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state)))
                  (data_push_env a'' F (data_dec_clock s)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s2:(C,FFI)data_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r0 = NONE:((data_v list,data_v)result)option) /\
                ~(r0 = SOME (Rerr (Rabort Rtype_error)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o d2wpaux_unfold_ih o
    SPECL [`data_RefPtr F p`; `a1:data_v`; `dest:num`; `names:num_set`; `prog:data_prog`;
           `[data_RefPtr F p; a1]`;
           `lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state))`;
           `a'':data_v spt`]) THEN
  ASM_REWRITE_TAC[data_get_var_def]) THEN
  (DISCH_THEN(MP_TAC o SPECL [`c:data_to_word_config`; `loc:num`; `2`; `n:num`;
      `l:num`; `r0:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`;
      `wl_call_env [wl_Loc n l; wl_Word w1; wl_state_memory t (word_add a bytes_in_word)]
         (lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state)))
         (wl_push_env (y1,y2) NONE (wl_dec_clock (t:(A,C,FFI)wl_state)))`;
      `CONS (l1,l2) (locs:(num#num)list)`]) THEN
  ASM_REWRITE_TAC[termdep_rw; push_env_termdep] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_result_cases_tac `r0:((data_v list,data_v)result)option` THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)))) THENL
  [(ASM_CASES_TAC `LENGTH (v:data_v list) = 1` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN d2wpaux_type_error_tac] THEN
  FIRST_X_ASSUM(MP_TAC o check (d2wpaux_is_eval_asm o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  d2wpaux_split_tac `data_pop_env (s2:(C,FFI)data_state)` THEN d2wpaux_res_tac THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_pop_env_const) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP pop_env_safe_for_space) THEN
  CAKE_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(X_CHOOSE_THEN `v0:data_v` SUBST_ALL_TAC o
    REWRITE_RULE[sing_list] o check (fun th -> concl th = `LENGTH (v:data_v list) = 1`)) THEN
  REWRITE_TAC[HD] THEN
  ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT; data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w0:A word_loc` SUBST_ALL_TAC o
    REWRITE_RULE[LENGTH; ARITH_RULE `SUC 0 = 1`; sing_list] o
    check (fun th -> concl th = `LENGTH (ws2:(A word_loc)list) = LENGTH [v0:data_v]`)) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`]) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `n:num`; `l:num`; `s2:(C,FFI)data_state`;
                 `t1:(A,C,FFI)wl_state`; `v0:data_v`; `w0:A word_loc`;
                 `CONS (l1,l2) (locs:(num#num)list)`; `a''':(C,FFI)data_state`; `dest:num`]
         state_rel_pop_env_set_var_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ZIP]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num`
    (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    is_eq (lhand (concl th)) && is_var (rhs (lhand (concl th)))))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(fun th -> if is_conj (concl th) && is_conj (lhand (concl th)) &&
                             is_eq (rand (concl th)) then
     let es = CONJUNCTS th in
     SUBST_ALL_TAC (SYM (el 0 es)) THEN SUBST_ALL_TAC (SYM (el 1 es)) THEN
     SUBST_ALL_TAC (SYM (el 2 es)) else NO_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_IMP_domain_EQ o CONJ (ASSUME
    `wl_evaluate (FST (data_to_word_comp c loc 2 prog),
       wl_call_env [wl_Loc n l; wl_Word w1; wl_state_memory t (word_add a bytes_in_word)]
         (lookup loc (data_state_stack_frame_sizes (s:(C,FFI)data_state)))
         (wl_push_env (y1,y2) NONE (wl_dec_clock (t:(A,C,FFI)wl_state)))) =
     (SOME (wl_Result (wl_Loc n l) [w0]),t1)`) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_pop_env"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[d2wpaux_clause wl_evaluate_def "wl_Skip"] THEN
  MAP_EVERY EXISTS_TAC [`wl_set_vars [adjust_var dest] [w0] (t2:(A,C,FFI)wl_state)`;
                        `NONE:((A)wl_result)option`] THEN
  REWRITE_TAC[data_to_word_gcProof_set_vars_sing] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP D2WPAUX_state_rel_IMP o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "data_set_var"
                                              with Failure _ -> false)) (concl th) &&
                     (try fst(dest_const(fst(strip_comb(concl th)))) =
                            "data_to_word_gcProof_state_rel" with Failure _ -> false))) THEN
  SIMP_TAC[]);
   (d2wpaux_res_conj_tac THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1 = SOME NotEnoughSpace:((A)wl_result)option` THENL
   [d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `SOME NotEnoughSpace:((A)wl_result)option`] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      not (is_neg (fst (dest_imp (concl th)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[D2WPAUX_jump_exc_call_push_NONE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w5:A word_loc` (X_CHOOSE_THEN `l5:num`
    (X_CHOOSE_THEN `l6:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC))))) THEN
  d2wpaux_subst_var_tac "res1" THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`;
    `SOME (wl_Exception (mk_loc (wl_jump_exc (t:(A,C,FFI)wl_state))) w5):((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[distinctness "wl_result"; option_INJ; injectivity "wl_result"] THEN
  MAP_EVERY EXISTS_TAC [`w5:A word_loc`; `l5:num`; `l6:num`; `ll:(num#num)list`] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (data_state_stack (s2:(C,FFI)data_state)) < LENGTH (locs:(num#num)list)`
    (fun th -> SIMP_TAC[MATCH_MP LASTN_TL th]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP eval_exc_stack_shorter o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_evaluate"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[]);
   (d2wpaux_call_abort_tac);
   (d2wpaux_call_abort_tac)]]]]);;

(* HOL4 line 293 *)
let data_compile_correct = prove
 (CASE_TERM
  `!prog (s:(C,FFI)data_state) c n l l1 l2 res s1 (t:(A,C,FFI)wl_state) locs.
     (data_evaluate (prog,s) = (res,s1)) /\
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     wl_state_termdep t > 1 ==>
     ?t1 res1.
       (wl_evaluate (FST (data_to_word_comp c n l prog),t) = (res1,t1)) /\
       option_le (wl_state_stack_max t1) (data_state_stack_max s1) /\
       (res1 = SOME NotEnoughSpace ==>
        ffi_state_io_events (wl_state_ffi t1) <<= ffi_state_io_events (data_state_ffi s1) /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~data_state_safe_for_space s1)) /\
       (~(res1 = SOME NotEnoughSpace) ==>
        match res with
          NONE -> data_to_word_gcProof_state_rel c l1 l2 s1 t1 NONE locs /\ (res1 = NONE)
        | SOME (Rval v) ->
            ?ws. LENGTH ws = LENGTH v /\
                 data_to_word_gcProof_state_rel c l1 l2 s1 t1 (SOME (ZIP v ws)) locs /\
                 (res1 = SOME (wl_Result (wl_Loc l1 l2) ws))
        | SOME (Rerr (Rraise v)) ->
            (wl_state_ffi t1 = data_state_ffi s1) /\
            ?w l5 l6 ll.
              (res1 = SOME (wl_Exception (mk_loc (wl_jump_exc t)) w)) /\
              (~(wl_jump_exc t = NONE) ==>
               LASTN (LENGTH (data_state_stack s1) + 1) locs = CONS (l5,l6) ll /\
               !i. data_to_word_gcProof_state_rel c l5 l6 (data_set_var i v s1)
                     (wl_set_var (adjust_var i) w t1) NONE ll)
        | SOME (Rerr (Rabort (Rffi_error f))) ->
            (res1 = SOME (wl_FinalFFI f) /\ wl_state_ffi t1 = data_state_ffi s1)
        | SOME (Rerr (Rabort e)) ->
            (res1 = SOME wl_TimeOut) /\ wl_state_ffi t1 = data_state_ffi s1)`,
  SUBGOAL_THEN `!p. D2WPAUX_correct (:A) (FST p) (SND p:(C,FFI)data_state)` MP_TAC THENL
   [MATCH_MP_TAC data_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC D2WPAUX_Skip; MATCH_ACCEPT_TAC D2WPAUX_Move;
      MATCH_ACCEPT_TAC D2WPAUX_Assign; MATCH_ACCEPT_TAC D2WPAUX_Tick;
      MATCH_ACCEPT_TAC D2WPAUX_MakeSpace; MATCH_ACCEPT_TAC D2WPAUX_Raise;
      MATCH_ACCEPT_TAC D2WPAUX_Return; MATCH_ACCEPT_TAC D2WPAUX_Seq;
      MATCH_ACCEPT_TAC D2WPAUX_If; MATCH_ACCEPT_TAC D2WPAUX_Force;
      MATCH_ACCEPT_TAC D2WPAUX_Call];
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND; D2WPAUX_correct_def] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* HOL4 line 1157 *)
let data_to_wordProof_compile_correct_lemma = prove
 (CASE_TERM
  `!(s:(C,FFI)data_state) c l1 l2 res s1 (t:(A,C,FFI)wl_state) start.
     (data_evaluate (data_Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\
     wl_state_termdep t > 1 /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE [] ==>
     ?t1 res1.
       (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,t) = (res1,t1)) /\
       option_le (wl_state_stack_max t1) (data_state_stack_max s1) /\
       (res1 = SOME NotEnoughSpace ==>
        ffi_state_io_events (wl_state_ffi t1) <<= ffi_state_io_events (data_state_ffi s1) /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~data_state_safe_for_space s1)) /\
       (~(res1 = SOME NotEnoughSpace) ==>
        match res with
          NONE -> (wl_state_ffi t1 = data_state_ffi s1) /\ (res1 = NONE)
        | SOME (Rval v) -> (wl_state_ffi t1 = data_state_ffi s1) /\
                           ?w. (res1 = SOME (wl_Result (wl_Loc l1 l2) w))
        | SOME (Rerr (Rraise v)) -> (wl_state_ffi t1 = data_state_ffi s1) /\
                                    (?v w. res1 = SOME (wl_Exception v w))
        | SOME (Rerr (Rabort (Rffi_error f))) ->
            (res1 = SOME (wl_FinalFFI f) /\ wl_state_ffi t1 = data_state_ffi s1)
        | SOME (Rerr (Rabort e)) ->
            (res1 = SOME wl_TimeOut) /\ wl_state_ffi t1 = data_state_ffi s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`data_Call NONE (SOME start) [] NONE`; `s:(C,FFI)data_state`;
                 `c:data_to_word_config`; `0`; `0`; `l1:num`; `l2:num`;
                 `res:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `[]:(num#num)list`] data_compile_correct) THEN
  ASM_REWRITE_TAC[D2WPAUX_comp_eqs] THEN CAKE_REWRITE_TAC[FST; MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t1:(A,C,FFI)wl_state`; `res1:((A)wl_result)option`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN
  d2wpaux_result_cases_tac `res:((data_v list,data_v)result)option` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "wl_result"; option_INJ] THEN
  TRY(FIRST_ASSUM(fun th -> if vfree_in `t1:(A,C,FFI)wl_state` (concl th)
        then MP_TAC(MATCH_MP D2WPAUX_state_rel_IMP th) else NO_TAC) THEN
      SIMP_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(fun th -> if vfree_in `t1:(A,C,FFI)wl_state` (concl th)
        then MP_TAC(MATCH_MP D2WPAUX_state_rel_IMP th) else NO_TAC) THEN
      SIMP_TAC[]) THEN
  MESON_TAC[]);;

(* HOL4 line 1190 *)
let state_rel_ext_def = cake_def
  `state_rel_ext c l1 l2 (s:(C,FFI)data_state) (u:(A,C,FFI)wl_state) <=>
     ?t l.
       data_to_word_gcProof_state_rel c l1 l2 s t NONE [] /\
       domain (wl_state_code t) = domain l /\
       wl_state_termdep t > 1 /\
       (?tt kk aa co.
          wl_state_compile_oracle u =
            (I ## MAP (\p. full_compile_single tt kk aa co (p,NONE))) o
              wl_state_compile_oracle t /\
          wl_state_compile t =
            (\conf progs. wl_state_compile u conf
               (MAP (\p. full_compile_single tt kk aa co (p,NONE)) progs))) /\
       (!n v. lookup n (wl_state_code t) = SOME v ==>
              ?t' k' a' c' col.
                lookup n l = SOME (SND (full_compile_single t' k' a' c' ((n,v),col)))) /\
       u = wl_state_code_fupd (combin_K l) (wl_state_termdep_fupd (combin_K 0)
             (wl_state_compile_fupd (combin_K (wl_state_compile u))
                (wl_state_compile_oracle_fupd (combin_K (wl_state_compile_oracle u)) t)))`;;

(* the code of the word_to_word input, from the compiled code l *)
let D2WPAUX_code_rel_exists = prove
 (`!(code:(num#(A)wl_prog)spt) (l:(num#(A)wl_prog)spt).
     domain code = domain l /\
     (!n v. lookup n code = SOME v ==>
            ?t' k' a' (c':(A)asm_config) col.
              lookup n l = SOME (SND (full_compile_single t' k' a' c' ((n,v),col)))) ==>
     ?l2. word_to_wordProof_code_rel code l2 /\ sptree_map (I ## remove_must_terminate) l2 = l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:num->num#(A)wl_prog->bool`
    (X_CHOOSE_THEN `f2:num->num#(A)wl_prog->num` (X_CHOOSE_THEN `f3:num->num#(A)wl_prog->num`
    (X_CHOOSE_THEN `f4:num->num#(A)wl_prog->(A)asm_config`
    (X_CHOOSE_THEN `f5:num->num#(A)wl_prog->(num spt)option` ASSUME_TAC))))) THEN
  EXISTS_TAC `copy_shape (mapi (\n v. SND (word_to_word_compile_single (f1 n v) (f2 n v)
                (f3 n v) (f4 n v) ((n,v),f5 n v))) (code:(num#(A)wl_prog)spt))
              (l:(num#(A)wl_prog)spt)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[word_to_wordProof_code_rel_def; lookup_copy_shape; lookup_mapi] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
    MAP_EVERY EXISTS_TAC [`(f5:num->num#(A)wl_prog->(num spt)option) n v`;
      `(f1:num->num#(A)wl_prog->bool) n v`; `(f2:num->num#(A)wl_prog->num) n v`;
      `(f3:num->num#(A)wl_prog->num) n v`; `(f4:num->num#(A)wl_prog->(A)asm_config) n v`] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[spt_eq; eq_shape_map] THEN CONJ_TAC THENL
   [MATCH_MP_TAC shape_eq_copy_shape THEN ASM_REWRITE_TAC[domain_mapi];
    ALL_TAC] THEN
  REWRITE_TAC[lookup_map; lookup_copy_shape; lookup_mapi] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `lookup k (code:(num#(A)wl_prog)spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `v0:num#(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `v0:num#(A)wl_prog`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ; full_compile_single_def] THEN
  W(fun (asl,w) -> let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                     "word_to_word_compile_single" with Failure _ -> false) w in
     MP_TAC(ISPEC t D2WPAUX_triple_cases)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` (X_CHOOSE_THEN `x3:(A)wl_prog`
    SUBST1_TAC))) THEN
  CAKE_REWRITE_TAC[SND; PAIR_EQ; I_THM; PAIR_MAP_THM]);;

(* state_rel does not look at permute *)
let D2WPAUX_state_rel_permute = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) p v locs.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_state_permute_fupd (combin_K p) t) v locs <=>
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; wl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 1208 *)
let data_to_wordProof_compile_correct = prove
 (CASE_TERM
  `!x (s:(C,FFI)data_state) l1 l2 res s1 (t:(A,C,FFI)wl_state) start.
     (data_evaluate (data_Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\
     state_rel_ext x l1 l2 s t ==>
     ?ck t1 res1.
       (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_inc_clock ck t) = (res1,t1)) /\
       option_le (wl_state_stack_max t1) (data_state_stack_max s1) /\
       (res1 = SOME NotEnoughSpace ==>
        ffi_state_io_events (wl_state_ffi t1) <<= ffi_state_io_events (data_state_ffi s1) /\
        (~(data_to_word_config_gc_kind x = data_to_word_None) ==>
         ~data_state_safe_for_space s1)) /\
       (~(res1 = SOME NotEnoughSpace) ==>
        (wl_state_ffi t1 = data_state_ffi s1) /\
        match res with
          NONE -> (res1 = NONE)
        | SOME (Rval v) -> ?w. (res1 = SOME (wl_Result (wl_Loc l1 l2) w))
        | SOME (Rerr (Rraise v)) -> (?v w. res1 = SOME (wl_Exception v w))
        | SOME (Rerr (Rabort (Rffi_error f))) -> (res1 = SOME (wl_FinalFFI f))
        | SOME (Rerr (Rabort e)) -> (res1 = SOME wl_TimeOut))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_rel_ext_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l:(num#(A)wl_prog)spt`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `tt:bool` (X_CHOOSE_THEN `kk:num` (X_CHOOSE_THEN `aa:num`
    (X_CHOOSE_THEN `co:(A)asm_config` STRIP_ASSUME_TAC))) o
    check (is_exists o concl)) THEN
  MP_TAC(ISPECL [`wl_state_code (t2:(A,C,FFI)wl_state)`; `l:(num#(A)wl_prog)spt`]
         D2WPAUX_code_rel_exists) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:(num#(A)wl_prog)spt` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t2:(A,C,FFI)wl_state`; `l3:(num#(A)wl_prog)spt`;
                 `wl_state_compile (t:(A,C,FFI)wl_state)`; `tt:bool`; `kk:num`; `aa:num`;
                 `co:(A)asm_config`; `wl_state_compile_oracle (t:(A,C,FFI)wl_state)`;
                 `start:num`] compile_word_to_word_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `sptree_map (I ## remove_must_terminate) l3 = (l:(num#(A)wl_prog)spt)` THEN
      DISCH_THEN(MP_TAC o AP_TERM `domain:(num#(A)wl_prog)spt->num->bool`) THEN
      REWRITE_TAC[domain_map] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `data_to_word_gcProof_state_rel x l1 l2 (s:(C,FFI)data_state)
                     (t2:(A,C,FFI)wl_state) NONE []` THEN
      SIMP_TAC[data_to_word_gcProof_state_rel_thm; gc_fun_const_ok_word_gc_fun]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm':num->num->num` (X_CHOOSE_THEN `clk:num` MP_TAC)) THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `x:data_to_word_config`; `l1:num`; `l2:num`;
                 `res:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`;
                 `wl_state_permute_fupd (combin_K perm') (t2:(A,C,FFI)wl_state)`; `start:num`]
         data_to_wordProof_compile_correct_lemma) THEN
  ASM_REWRITE_TAC[D2WPAUX_state_rel_permute; wl_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1':(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1':((A)wl_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(res1' = SOME wl_Error:((A)wl_result)option)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_neg (fst (dest_imp (concl th))))) THEN
    REWRITE_TAC[distinctness "wl_result"; option_INJ] THEN
    d2wpaux_result_cases_tac `res:((data_v list,data_v)result)option` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
    REWRITE_TAC[distinctness "wl_result"; option_INJ; option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) -> let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                     "wl_evaluate" with Failure _ -> false) w in
     MP_TAC(ISPEC t PAIR_SURJECTIVE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r6:((A)wl_result)option` (X_CHOOSE_THEN `s6:(A,C,FFI)wl_state`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`clk:num`; `s6:(A,C,FFI)wl_state`; `r6:((A)wl_result)option`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
        with Failure _ -> false) && not (vfree_in `perm':num->num->num` (concl th))
     then MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `t:(A,C,FFI)wl_state`
      then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    ASM_REWRITE_TAC[wl_inc_clock_def; PAIR_EQ; wl_state_component_equality;
                    wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    not (is_neg (fst (dest_imp (concl th)))))) THEN
  ASM_REWRITE_TAC[] THEN
  d2wpaux_result_cases_tac `res:((data_v list,data_v)result)option` THEN REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* HOL4 line 1291 (local) *)
let state_rel_ext_with_clock = prove
 (`!a b c (s1:(C,FFI)data_state) (s2:(A,C,FFI)wl_state) k.
     state_rel_ext a b c s1 s2 ==>
     state_rel_ext a b c (data_state_clock_fupd (combin_K k) s1) (wl_state_clock_fupd (combin_K k) s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_rel_ext_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    (X_CHOOSE_THEN `l:(num#(A)wl_prog)spt` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state)`;
                        `l:(num#(A)wl_prog)spt`] THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_state_rel_with_clock THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `s2:(A,C,FFI)wl_state`
    then GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] else NO_TAC) THEN
  REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

(* the per-clock simulation of the semantics theorems: compile_correct at   *)
(* clock k, with the clock of the word state k + ck                         *)
let D2WPAUX_sem_sim = prove
 (CASE_TERM
  `!conf (ffi:(FFI)ffi_state) prog co cc lims (t:(A,C,FFI)wl_state) start k.
     state_rel_ext conf 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     ~(FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
              data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t) k)) =
       SOME (Rerr (Rabort Rtype_error))) ==>
     ?ck. let (r,s) = data_evaluate (data_Call NONE (SOME start) [] NONE,
                        data_initial_state ffi (fromAList prog) co cc T lims
                          (wl_state_stack_size t) k) in
          let (q,u) = wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                   wl_state_clock_fupd (combin_K (k + ck)) t) in
          option_le (wl_state_stack_max u) (data_state_stack_max s) /\
          (q = SOME NotEnoughSpace ==>
           ffi_state_io_events (wl_state_ffi u) <<= ffi_state_io_events (data_state_ffi s) /\
           (~(data_to_word_config_gc_kind conf = data_to_word_None) ==>
            ~data_state_safe_for_space s)) /\
          (~(q = SOME NotEnoughSpace) ==>
           (wl_state_ffi u = data_state_ffi s) /\
           match r with
             NONE -> (q = NONE)
           | SOME (Rval v) -> ?w. (q = SOME (wl_Result (wl_Loc 1 0) w))
           | SOME (Rerr (Rraise v)) -> (?v w. q = SOME (wl_Exception v w))
           | SOME (Rerr (Rabort (Rffi_error f))) -> (q = SOME (wl_FinalFFI f))
           | SOME (Rerr (Rabort e)) -> (q = SOME wl_TimeOut))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `data_evaluate (data_Call NONE (SOME start) [] NONE,
                 data_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                   (co:num->C#(num#num#data_prog)list) cc T lims
                   (wl_state_stack_size (t:(A,C,FFI)wl_state)) k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s:(C,FFI)data_state` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP state_rel_ext_with_clock) THEN
  REWRITE_TAC[data_initial_state_with_simp] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`;
                 `data_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num->C#(num#num#data_prog)list) cc T lims
                    (wl_state_stack_size (t:(A,C,FFI)wl_state)) k`;
                 `1`; `0`; `r:((data_v list,data_v)result)option`; `s:(C,FFI)data_state`;
                 `wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state)`; `start:num`]
         data_to_wordProof_compile_correct) THEN
  SUBGOAL_THEN `~(r = SOME (Rerr (Rabort Rtype_error)):((data_v list,data_v)result)option)`
    (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "data_evaluate" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_inc_clock_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state`
    (X_CHOOSE_THEN `res1:((A)wl_result)option` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* the word run with a larger clock: the same result if no timeout *)
let D2WPAUX_word_add_clock = prove
 (`!p (s:(A,C,FFI)wl_state) k1 k2.
     k1 <= k2 /\
     ~(FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) s)) = SOME wl_TimeOut)
     ==> FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k2) s)) =
         FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) s)) /\
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k2) s))) =
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC (ISPEC `wl_evaluate (p:(A)wl_prog,
                              wl_state_clock_fupd (combin_K k1) (s:(A,C,FFI)wl_state))`
            PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST]) THEN ASSUME_TAC th THEN
                       REWRITE_TAC[th; FST; SND]) THEN
  MP_TAC (INST [`d:num`,`extra:num`]
    (ISPECL [`p:(A)wl_prog`; `wl_state_clock_fupd (combin_K k1) (s:(A,C,FFI)wl_state)`;
             `r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]
            wl_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* two word runs without timeout have the same result *)
let D2WPAUX_word_det = prove
 (`!p (s:(A,C,FFI)wl_state) k1 k2.
     ~(FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) s)) = SOME wl_TimeOut) /\
     ~(FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k2) s)) = SOME wl_TimeOut)
     ==> FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) s)) =
         FST (wl_evaluate (p,wl_state_clock_fupd (combin_K k2) s)) /\
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) s))) =
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k2) s)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISJ_CASES_TAC (SPECL [`k1:num`; `k2:num`] LE_CASES) THENL
   [MP_TAC (SPECL [`p:(A)wl_prog`; `s:(A,C,FFI)wl_state`; `k1:num`; `k2:num`]
              D2WPAUX_word_add_clock);
    MP_TAC (SPECL [`p:(A)wl_prog`; `s:(A,C,FFI)wl_state`; `k2:num`; `k1:num`]
              D2WPAUX_word_add_clock)] THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* the io events of the word runs grow with the clock *)
let D2WPAUX_word_io_mono = prove
 (`!p (x:(A,C,FFI)wl_state) k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (wl_state_ffi
          (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k1) x)))))
       (ffi_state_io_events (wl_state_ffi
          (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k2) x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `wl_state_clock_fupd (combin_K k1) (x:(A,C,FFI)wl_state)`;
                 `d:num`] wl_evaluate_add_clock_io_events_mono) THEN
  SIMP[]);;

let D2WPAUX_word_io_chain = prove
 (`!p (x:(A,C,FFI)wl_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
          (SND (wl_evaluate (p,wl_state_clock_fupd (combin_K k) x)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[D2WPAUX_word_io_mono; LE_CASES]);;

(* the run with a larger clock in dataSem *)
let D2WPAUX_data_add_clock = prove
 (`!p (ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss k1 k2.
     k1 <= k2 /\
     ~(FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1)) =
       SOME (Rerr (Rabort Rtimeout_error)))
     ==> FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k2)) =
         FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1)) /\
         data_state_ffi (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k2))) =
         data_state_ffi (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC (ISPEC `data_evaluate (p,data_initial_state (ffi:(FFI)ffi_state) code
                   (co:num->C#(num#num#data_prog)list) cc T lims ss k1)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST]) THEN ASSUME_TAC th THEN
                       REWRITE_TAC[th; FST; SND]) THEN
  MP_TAC (ISPECL [`p:data_prog`;
                  `data_initial_state (ffi:(FFI)ffi_state) code
                     (co:num->C#(num#num#data_prog)list) cc T lims ss k1`;
                  `r1:((data_v list,data_v)result)option`; `s1:(C,FFI)data_state`]
            data_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[data_initial_state_simp; data_initial_state_with_simp] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* the io events of the data runs grow with the clock *)
let D2WPAUX_data_io_mono = prove
 (`!p (ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (data_state_ffi
          (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1)))))
       (ffi_state_io_events (data_state_ffi
          (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k2)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:data_prog`;
                 `data_initial_state (ffi:(FFI)ffi_state) code
                    (co:num->C#(num#num#data_prog)list) cc T lims ss k1`;
                 `d:num`] data_evaluate_add_clock_io_events_mono) THEN
  REWRITE_TAC[data_initial_state_simp; data_initial_state_with_simp]);;

let D2WPAUX_data_io_chain = prove
 (`!p (ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss.
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (data_state_ffi
          (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[D2WPAUX_data_io_mono; LE_CASES]);;

(* the io events of a data run are a prefix of the lub *)
let D2WPAUX_data_lub_prefix = prove
 (`!p (ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss kc l.
     isPREFIX l (ffi_state_io_events (data_state_ffi
        (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss kc)))))
     ==> LPREFIX (llist_fromList l)
           (build_lprefix_lub
              (IMAGE (\k. llist_fromList (ffi_state_io_events (data_state_ffi
                 (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k))))))
                 (:num)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL LPREFIX_TRANS) THEN
  EXISTS_TAC `llist_fromList (ffi_state_io_events (data_state_ffi
                 (SND (data_evaluate (p,data_initial_state (ffi:(FFI)ffi_state) code
                    (co:num->C#(num#num#data_prog)list) cc T lims ss kc)))))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE]; ALL_TAC] THEN
  MP_TAC (MATCH_MP build_lprefix_lub_thm
    (ISPECL [`p:data_prog`; `ffi:(FFI)ffi_state`; `code:(num#data_prog)spt`;
             `co:num->C#(num#num#data_prog)list`; `cc:C->(num#num#data_prog)list->
              ((8 word)list#(64 word)list#C)option`; `lims:limits`; `ss:num spt`]
       D2WPAUX_data_io_chain)) THEN
  REWRITE_TAC[lprefix_lub_def; FORALL_IN_IMAGE; IN_UNIV] THEN SIMP[]);;

(* the some of a goal (HOL4 DEEP_INTRO_TAC some_intro) *)
let d2wpaux_some_intro_tac : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> is_comb t &&
                       (try fst(dest_const(rator t)) = "some" with Failure _ -> false)) w in
  let v = genvar(type_of t) in
  let th = BETA_CONV (mk_comb(mk_abs(v,subst [v,t] w),t)) in
  (CONV_TAC(K(SYM th)) THEN MATCH_MP_TAC some_intro THEN
   CONV_TAC(DEPTH_CONV BETA_CONV)) g;;

(* the word semantics when every run times out *)
let D2WPAUX_word_sem_div = prove
 (`!(s:(A,C,FFI)wl_state) start.
     (!kc. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                             wl_state_clock_fupd (combin_K kc) s)) = SOME wl_TimeOut)
     ==> wl_semantics s start =
         Diverge (build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
              (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                 wl_state_clock_fupd (combin_K k) s)))))) (:num)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  d2wpaux_some_intro_tac THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s2:(A,C,FFI)wl_state`; `r:((A)wl_result)option`;
                         `outcome:outcome`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kk:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)))) THEN CAKE_REWRITE_TAC[];
    CAKE_REWRITE_TAC[]]);;

(* the word semantics when a run terminates and the semantics is not Fail *)
let D2WPAUX_word_sem_term = prove
 (`!(s:(A,C,FFI)wl_state) start kw rw sw outcome.
     ~(wl_semantics s start = Fail) /\
     wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (combin_K kw) s) =
       (rw,sw) /\
     ((?e. rw = SOME (wl_FinalFFI e) /\ outcome = FFI_outcome e) \/
      (?w ys. rw = SOME (wl_Result w ys) /\ outcome = Success) \/
      (rw = SOME NotEnoughSpace /\ outcome = Resource_limit_hit))
     ==> wl_semantics s start =
         Terminate outcome (ffi_state_io_events (wl_state_ffi sw))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "oc"))) THEN
  SUBGOAL_THEN `~(rw = SOME (wl_TimeOut:(A)wl_result))` (LABEL_TAC "nto") THENL
   [USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (SUBST1_TAC o CONJUNCT1))) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"];
    ALL_TAC] THEN
  REWRITE_TAC[wl_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  d2wpaux_some_intro_tac THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s3:(A,C,FFI)wl_state`; `r3:((A)wl_result)option`;
                         `outcome3:outcome`] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                   `s:(A,C,FFI)wl_state`; `kw:num`; `kk:num`] D2WPAUX_word_det) THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[FST; SND] THEN
    ANTS_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
        not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CAKE_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "behaviour"] THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CAKE_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `Terminate outcome
                  (ffi_state_io_events (wl_state_ffi (sw:(A,C,FFI)wl_state)))`) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`kw:num`; `sw:(A,C,FFI)wl_state`; `rw:((A)wl_result)option`;
                          `outcome:outcome`] THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC))) THEN CAKE_REWRITE_TAC[]]);;

(* the data runs of a semantics that is not Fail *)
let D2WPAUX_data_sem_ok = prove
 (`!(ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss start.
     ~(data_semantics ffi code co cc lims ss start = Fail) ==>
     !k. (?v. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                    data_initial_state ffi code co cc T lims ss k)) = SOME (Rval v)) \/
         FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                data_initial_state ffi code co cc T lims ss k)) =
           SOME (Rerr (Rabort Rtimeout_error)) \/
         (?f. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                    data_initial_state ffi code co cc T lims ss k)) =
                SOME (Rerr (Rabort (Rffi_error f))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC(ISPEC `FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                  data_initial_state (ffi:(FFI)ffi_state) code
                    (co:num->C#(num#num#data_prog)list) cc T lims ss k))`
         D2WPAUX_result_option_cases) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[injectivity "error_result"; injectivity "abort"; distinctness "abort";
                   distinctness "error_result"; option_INJ; option_DISTINCT;
                   injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;

(* two data runs without timeout have the same result *)
let D2WPAUX_data_det = prove
 (`!p (ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss k1 k2.
     ~(FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1)) =
       SOME (Rerr (Rabort Rtimeout_error))) /\
     ~(FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k2)) =
       SOME (Rerr (Rabort Rtimeout_error)))
     ==> FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1)) =
         FST (data_evaluate (p,data_initial_state ffi code co cc T lims ss k2)) /\
         data_state_ffi (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k1))) =
         data_state_ffi (SND (data_evaluate (p,data_initial_state ffi code co cc T lims ss k2)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISJ_CASES_TAC (SPECL [`k1:num`; `k2:num`] LE_CASES) THENL
   [MP_TAC (SPECL [`p:data_prog`; `ffi:(FFI)ffi_state`; `code:(num#data_prog)spt`;
                   `co:num->C#(num#num#data_prog)list`;
                   `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                   `lims:limits`; `ss:num spt`; `k1:num`; `k2:num`] D2WPAUX_data_add_clock);
    MP_TAC (SPECL [`p:data_prog`; `ffi:(FFI)ffi_state`; `code:(num#data_prog)spt`;
                   `co:num->C#(num#num#data_prog)list`;
                   `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                   `lims:limits`; `ss:num spt`; `k2:num`; `k1:num`] D2WPAUX_data_add_clock)] THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* the data semantics when every run times out *)
let D2WPAUX_data_sem_div = prove
 (`!(ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss start.
     (!k. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                data_initial_state ffi code co cc T lims ss k)) =
          SOME (Rerr (Rabort Rtimeout_error)))
     ==> data_semantics ffi code co cc lims ss start =
         Diverge (build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (data_state_ffi
              (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                                   data_initial_state ffi code co cc T lims ss k))))))
              (:num)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "abort"; distinctness "error_result"] THEN
  d2wpaux_some_intro_tac THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s2:(C,FFI)data_state`;
                         `r:(data_v list,data_v)result`; `outcome:outcome`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kk:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[FST; option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)))) THEN CAKE_REWRITE_TAC[];
    CAKE_REWRITE_TAC[]]);;

(* the data semantics when a run terminates and the semantics is not Fail *)
let D2WPAUX_data_sem_term = prove
 (`!(ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss start kd rd sd
    outcome.
     ~(data_semantics ffi code co cc lims ss start = Fail) /\
     data_evaluate (data_Call NONE (SOME start) [] NONE,
                    data_initial_state ffi code co cc T lims ss kd) = (SOME rd,sd) /\
     ((?v. rd = Rval v /\ outcome = Success) \/
      (?e. rd = Rerr (Rabort (Rffi_error e)) /\ outcome = FFI_outcome e))
     ==> data_semantics ffi code co cc lims ss start =
         Terminate outcome (ffi_state_io_events (data_state_ffi sd))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "oc"))) THEN
  SUBGOAL_THEN `~(rd = Rerr (Rabort Rtimeout_error):(data_v list,data_v)result)`
    (LABEL_TAC "nto") THENL
   [USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (SUBST1_TAC o CONJUNCT1))) THEN
    REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "error_result";
                distinctness "abort"];
    ALL_TAC] THEN
  REWRITE_TAC[data_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  d2wpaux_some_intro_tac THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s3:(C,FFI)data_state`;
                         `r3:(data_v list,data_v)result`; `outcome3:outcome`] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`data_Call NONE (SOME start) [] NONE`; `ffi:(FFI)ffi_state`;
                   `code:(num#data_prog)spt`; `co:num->C#(num#num#data_prog)list`;
                   `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                   `lims:limits`; `ss:num spt`; `kd:num`; `kk:num`] D2WPAUX_data_det) THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[FST; SND; option_INJ] THEN
    ANTS_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
        not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CAKE_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "behaviour"] THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CAKE_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `Terminate outcome
                  (ffi_state_io_events (data_state_ffi (sd:(C,FFI)data_state)))`) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`kd:num`; `sd:(C,FFI)data_state`; `rd:(data_v list,data_v)result`;
                          `outcome:outcome`] THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC))) THEN CAKE_REWRITE_TAC[]]);;

(* the elements of extend_with_resource_limit *)
let D2WPAUX_extend_refl = prove
 (`!x. x IN extend_with_resource_limit {x}`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING]);;

let D2WPAUX_extend_term = prove
 (`!io t l. isPREFIX io l
            ==> Terminate Resource_limit_hit io IN extend_with_resource_limit {Terminate t l}`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let D2WPAUX_extend_div = prove
 (`!io ll. LPREFIX (llist_fromList io) ll
           ==> Terminate Resource_limit_hit io IN extend_with_resource_limit {Diverge ll}`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* the runs of the start call in the semantics theorems *)
let d2wpaux_W k = vsubst [k,`kk:num`]
  `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                wl_state_clock_fupd (combin_K kk) (t:(A,C,FFI)wl_state))`;;

let d2wpaux_D k = vsubst [k,`kk:num`]
  `data_evaluate (data_Call NONE (SOME start) [] NONE,
                  data_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num->C#(num#num#data_prog)list) cc T lims
                    (wl_state_stack_size (t:(A,C,FFI)wl_state)) kk)`;;

(* the per-clock simulation for a semantics that is not Fail *)
let D2WPAUX_sem_sim2 = prove
 (`!conf (ffi:(FFI)ffi_state) prog (co:num->C#(num#num#data_prog)list) cc lims
    (t:(A,C,FFI)wl_state) start.
     state_rel_ext conf 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     ~(data_semantics ffi (fromAList prog) co cc lims (wl_state_stack_size t) start = Fail) ==>
     !k. ?ck.
       (FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                          wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME NotEnoughSpace /\
        isPREFIX
          (ffi_state_io_events (wl_state_ffi (SND (wl_evaluate
             (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (combin_K (k + ck)) t)))))
          (ffi_state_io_events (data_state_ffi (SND (data_evaluate
             (data_Call NONE (SOME start) [] NONE,
              data_initial_state ffi (fromAList prog) co cc T lims
                (wl_state_stack_size t) k)))))) \/
       (~(FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                            wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME NotEnoughSpace) /\
        wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                        wl_state_clock_fupd (combin_K (k + ck)) t))) =
        data_state_ffi (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                                            data_initial_state ffi (fromAList prog) co cc T
                                              lims (wl_state_stack_size t) k))) /\
        ((?v w. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                       data_initial_state ffi (fromAList prog) co cc T lims
                         (wl_state_stack_size t) k)) = SOME (Rval v) /\
                FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                       wl_state_clock_fupd (combin_K (k + ck)) t)) =
                  SOME (wl_Result (wl_Loc 1 0) w)) \/
         (FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                 data_initial_state ffi (fromAList prog) co cc T lims
                   (wl_state_stack_size t) k)) = SOME (Rerr (Rabort Rtimeout_error)) /\
          FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                 wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME wl_TimeOut) \/
         (?f. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                     data_initial_state ffi (fromAList prog) co cc T lims
                       (wl_state_stack_size t) k)) = SOME (Rerr (Rabort (Rffi_error f))) /\
              FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                     wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME (wl_FinalFFI f))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP D2WPAUX_data_sem_ok) THEN
  DISCH_THEN(LABEL_TAC "dk") THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `ffi:(FFI)ffi_state`;
                 `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                 `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                 `lims:limits`; `t:(A,C,FFI)wl_state`; `start:num`; `k:num`]
         D2WPAUX_sem_sim) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "dk" (REPEAT_TCL DISJ_CASES_THEN
      (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                injectivity "error_result"; distinctness "abort"];
    ALL_TAC] THEN
  MP_TAC(ISPEC (d2wpaux_D `k:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s:(C,FFI)data_state` (fun th -> REWRITE_TAC[th] THEN
       USE_THEN "dk" (MP_TAC o REWRITE_RULE[th; FST])))) THEN
  CAKE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "rk") THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (fun th -> EXISTS_TAC `ck:num` THEN MP_TAC th)) THEN
  MP_TAC(ISPEC (d2wpaux_W `k + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option`
    (X_CHOOSE_THEN `u:(A,C,FFI)wl_state` (fun th -> REWRITE_TAC[th]))) THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  ASM_CASES_TAC `q = SOME NotEnoughSpace:((A)wl_result)option` THEN
  ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "rk" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                   injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
  MESON_TAC[]);;

(* HOL4 line 1305 *)
let compile_semantics_lemma = prove
 (`!conf (ffi:(FFI)ffi_state) prog co cc lims (t:(A,C,FFI)wl_state) fs start.
     state_rel_ext conf 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     fs = wl_state_stack_size t /\
     ~(data_semantics ffi (fromAList prog) co cc lims fs start = Fail) ==>
     wl_semantics t start IN
       extend_with_resource_limit {data_semantics ffi (fromAList prog) co cc lims fs start}`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) &&
    fst(dest_var(lhs(concl th))) = "fs")) THEN
  FIRST_ASSUM(LABEL_TAC "dok" o MATCH_MP D2WPAUX_data_sem_ok) THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `ffi:(FFI)ffi_state`;
                 `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                 `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                 `lims:limits`; `t:(A,C,FFI)wl_state`; `start:num`] D2WPAUX_sem_sim2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sim") THEN
  SUBGOAL_THEN
   `!k. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                          wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state))) = SOME wl_TimeOut \/
        (?ys. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                wl_state_clock_fupd (combin_K k) t)) =
                SOME (wl_Result (wl_Loc 1 0) ys)) \/
        FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                          wl_state_clock_fupd (combin_K k) t)) = SOME NotEnoughSpace \/
        (?f. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                               wl_state_clock_fupd (combin_K k) t)) = SOME (wl_FinalFFI f))`
    (LABEL_TAC "wok") THENL
   [GEN_TAC THEN
    ASM_CASES_TAC (mk_eq(mk_comb(`FST:((A)wl_result)option#(A,C,FFI)wl_state->
                                    ((A)wl_result)option`, d2wpaux_W `k:num`),
                         `SOME (wl_TimeOut:(A)wl_result)`)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sim" (X_CHOOSE_TAC `ck:num` o SPEC `k:num`) THEN
    MP_TAC (SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `t:(A,C,FFI)wl_state`;
                   `k:num`; `k + ck:num`] D2WPAUX_word_add_clock) THEN
    ASM_REWRITE_TAC[LE_ADD] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `~(wl_semantics (t:(A,C,FFI)wl_state) start = Fail)` (LABEL_TAC "wnf") THENL
   [REWRITE_TAC[wl_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `kk:num` MP_TAC) THEN USE_THEN "wok" (MP_TAC o SPEC `kk:num`) THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
      CAKE_REWRITE_TAC[];
      d2wpaux_some_intro_tac THEN REWRITE_TAC[distinctness "behaviour"] THEN
      CAKE_REWRITE_TAC[distinctness "behaviour"] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[distinctness "behaviour"]];
    ALL_TAC]) THEN
  (ASM_CASES_TAC (mk_exists(`kw:num`, mk_neg(mk_eq(mk_comb(
    `FST:((A)wl_result)option#(A,C,FFI)wl_state->((A)wl_result)option`,
    d2wpaux_W `kw:num`), `SOME (wl_TimeOut:(A)wl_result)`))))) THENL
  [(FIRST_X_ASSUM(X_CHOOSE_TAC `kw:num`) THEN
  MP_TAC (ISPEC (d2wpaux_W `kw:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:((A)wl_result)option` (X_CHOOSE_THEN `sw:(A,C,FFI)wl_state`
    (LABEL_TAC "evw"))) THEN
  SUBGOAL_THEN `(?ys. rw = SOME (wl_Result (wl_Loc 1 0) ys):((A)wl_result)option) \/
                rw = SOME NotEnoughSpace \/ (?f. rw = SOME (wl_FinalFFI f))` (LABEL_TAC "rwok") THENL
   [USE_THEN "wok" (MP_TAC o SPEC `kw:num`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?outcome. (?e. rw = SOME (wl_FinalFFI e):((A)wl_result)option /\
                               outcome = FFI_outcome e) \/
                          (?w ys. rw = SOME (wl_Result w ys) /\ outcome = Success) \/
                          (rw = SOME NotEnoughSpace /\ outcome = Resource_limit_hit)`
    (X_CHOOSE_THEN `outcome:outcome` (LABEL_TAC "woc")) THENL
   [USE_THEN "rwok" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:(A,C,FFI)wl_state`; `start:num`; `kw:num`; `rw:((A)wl_result)option`;
                `sw:(A,C,FFI)wl_state`; `outcome:outcome`] D2WPAUX_word_sem_term) THEN
  USE_THEN "wnf" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "woc" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC) THEN
   (ASM_CASES_TAC (mk_exists(`kd:num`, mk_neg(mk_eq(mk_comb(
    `FST:((data_v list,data_v)result)option#(C,FFI)data_state->
         ((data_v list,data_v)result)option`, d2wpaux_D `kd:num`),
    `SOME (Rerr (Rabort Rtimeout_error)):((data_v list,data_v)result)option`))))) THENL
   [(FIRST_X_ASSUM(X_CHOOSE_TAC `kd:num`) THEN
  MP_TAC (ISPEC (d2wpaux_D `kd:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rd':((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `sd:(C,FFI)data_state` (LABEL_TAC "evd"))) THEN
  USE_THEN "dok" (MP_TAC o SPEC `kd:num`) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  USE_THEN "evd" (fun th -> REWRITE_TAC[th; FST]) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?rd doutcome. rd' = SOME (rd:(data_v list,data_v)result) /\
     ((?v. rd = Rval v /\ doutcome = Success) \/
      (?e. rd = Rerr (Rabort (Rffi_error e)) /\ doutcome = FFI_outcome e))`
    (X_CHOOSE_THEN `rd:(data_v list,data_v)result` (X_CHOOSE_THEN `doutcome:outcome`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "doc")))) THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) o
      check (is_disj o concl)) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `fromAList prog:(num#data_prog)spt`;
                `co:num->C#(num#num#data_prog)list`;
                `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                `lims:limits`; `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`;
                `kd:num`; `rd:(data_v list,data_v)result`; `sd:(C,FFI)data_state`;
                `doutcome:outcome`] D2WPAUX_data_sem_term) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "evd" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "doc" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC) THEN
    (USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kd:num`) THEN
  USE_THEN "evd" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
  MP_TAC (ISPEC (d2wpaux_W `kd + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)wl_result)option` (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state`
    (LABEL_TAC "ev2"))) THEN
  USE_THEN "ev2" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
  REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
              injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
  DISCH_THEN(LABEL_TAC "s2rel") THEN
  SUBGOAL_THEN `~(r2 = SOME wl_TimeOut:((A)wl_result)option)` ASSUME_TAC THENL
   [USE_THEN "s2rel" MP_TAC THEN USE_THEN "doc" MP_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)))) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
    ALL_TAC] THEN
  MP_TAC(SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `t:(A,C,FFI)wl_state`;
                `kw:num`; `kd + ck:num`] D2WPAUX_word_det) THEN
  USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ev2" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> t = `kw:num`)) (concl th))) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "ffieq"))) THEN
    (USE_THEN "s2rel" (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THENL
   [SUBGOAL_THEN `outcome = Resource_limit_hit` SUBST1_TAC THENL
     [REMOVE_THEN "woc" MP_TAC THEN ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
      ALL_TAC] THEN
    MATCH_MP_TAC D2WPAUX_extend_term THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `outcome:outcome = doutcome` SUBST1_TAC THENL
   [REMOVE_THEN "woc" MP_TAC THEN REMOVE_THEN "doc" MP_TAC THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) o
      check (fun th -> is_disj (concl th) &&
        can (find_term (fun t -> t = `r2:((A)wl_result)option`)) (concl th) &&
        can (find_term (fun t -> t = `rd:(data_v list,data_v)result`)) (concl th))) THEN
    ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result";
      distinctness "result"; injectivity "result"; injectivity "error_result";
      distinctness "abort"; injectivity "abort"; distinctness "error_result"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[D2WPAUX_extend_refl]);
    (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM] o
    check (fun th -> is_neg (concl th) && is_exists (dest_neg (concl th)))) THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `fromAList prog:(num#data_prog)spt`;
                `co:num->C#(num#num#data_prog)list`;
                `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                `lims:limits`; `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`]
         D2WPAUX_data_sem_div) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kw:num`) THEN
  MP_TAC (ISPEC (d2wpaux_W `kw + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)wl_result)option` (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state`
    (LABEL_TAC "ev2"))) THEN
  USE_THEN "ev2" (fun th -> REWRITE_TAC[th; FST; SND]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
              injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
  MP_TAC(SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `t:(A,C,FFI)wl_state`;
                `kw:num`; `kw + ck:num`] D2WPAUX_word_add_clock) THEN
  USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ev2" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FST; SND; LE_ADD] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> t = `kw:num`)) (concl th))) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "ffieq")) THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `outcome = Resource_limit_hit` SUBST1_TAC THENL
     [REMOVE_THEN "woc" MP_TAC THEN ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
      ALL_TAC] THEN
    MATCH_MP_TAC D2WPAUX_extend_div THEN
    MATCH_MP_TAC D2WPAUX_data_lub_prefix THEN EXISTS_TAC `kw:num` THEN
    USE_THEN "ffieq" (fun th -> REWRITE_TAC[SYM th]) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> t = `kw:num`)) (concl th))) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]) THEN ASM_REWRITE_TAC[]])];
   (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM] o
    check (fun th -> is_neg (concl th) && is_exists (dest_neg (concl th)))) THEN
  MP_TAC(SPECL [`t:(A,C,FFI)wl_state`; `start:num`] D2WPAUX_word_sem_div) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   (mk_forall(`kd:num`, mk_eq(mk_comb(
      `FST:((data_v list,data_v)result)option#(C,FFI)data_state->
           ((data_v list,data_v)result)option`, d2wpaux_D `kd:num`),
      `SOME (Rerr (Rabort Rtimeout_error)):((data_v list,data_v)result)option`)))
    (LABEL_TAC "ddiv") THENL
   [GEN_TAC THEN USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kd:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kd + ck:num` o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `fromAList prog:(num#data_prog)spt`;
                `co:num->C#(num#num#data_prog)list`;
                `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                `lims:limits`; `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`]
         D2WPAUX_data_sem_div) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!kd. ?ck. wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                  wl_state_clock_fupd (combin_K (kd + ck)) (t:(A,C,FFI)wl_state)))) =
              data_state_ffi (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                  data_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num->C#(num#num#data_prog)list) cc T lims
                    (wl_state_stack_size t) kd)))`
    (LABEL_TAC "ffisim") THENL
   [GEN_TAC THEN USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kd:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kd + ck:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "wl_evaluate" with Failure _ -> false))
          (concl th))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[injectivity "behaviour"] THEN
  SUBGOAL_THEN
   `build_lprefix_lub
      (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
         (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                            wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state))))))) (:num)) =
    build_lprefix_lub
      (IMAGE (\k. llist_fromList (ffi_state_io_events (data_state_ffi
         (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                              data_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                                (co:num->C#(num#num#data_prog)list) cc T lims
                                (wl_state_stack_size t) k)))))) (:num))`
    (fun th -> REWRITE_TAC[th; D2WPAUX_extend_refl]) THEN
  MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
  REWRITE_TAC[D2WPAUX_word_io_chain; D2WPAUX_data_io_chain] THEN
  REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THEN X_GEN_TAC `kc:num` THEN
  USE_THEN "ffisim" (X_CHOOSE_TAC `ck:num` o SPEC `kc:num`) THENL
   [EXISTS_TAC `kc:num` THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
    MATCH_MP_TAC D2WPAUX_word_io_mono THEN ARITH_TAC;
    EXISTS_TAC `kc + ck:num` THEN
    ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL]])]);;

(* safe_for_space of every data run, from data_lang_safe_for_space *)
let D2WPAUX_safe_all = prove
 (`!(ffi:(FFI)ffi_state) code (co:num->C#(num#num#data_prog)list) cc lims ss start.
     data_lang_safe_for_space ffi code lims ss start ==>
     !k. data_state_safe_for_space (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
           data_initial_state ffi code co cc T lims ss k)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_lang_safe_for_space_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPEC `data_evaluate (data_Call NONE (SOME start) [] NONE,
                  data_initial_state (ffi:(FFI)ffi_state) code
                    (ARB:num->1#(num#num#data_prog)list) ARB T lims ss k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s0:(1,FFI)data_state` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`data_Call NONE (SOME start) [] NONE`;
                 `data_initial_state (ffi:(FFI)ffi_state) code
                    (ARB:num->1#(num#num#data_prog)list) ARB T lims ss k`;
                 `res:((data_v list,data_v)result)option`; `s0:(1,FFI)data_state`;
                 `data_initial_state (ffi:(FFI)ffi_state) code
                    (co:num->C#(num#num#data_prog)list) cc T lims ss k`]
         evaluate_cc_co_only_diff) THEN
  ASM_REWRITE_TAC[cc_co_only_diff_def; data_initial_state_def;
                  data_state_INFO.ri_accessors] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND] THEN ASM_MESON_TAC[]);;

(* the per-clock simulation without NotEnoughSpace, for a safe program *)
let D2WPAUX_sem_sim3 = prove
 (`!conf (ffi:(FFI)ffi_state) prog (co:num->C#(num#num#data_prog)list) cc lims
    (t:(A,C,FFI)wl_state) start.
     state_rel_ext conf 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     ~(data_semantics ffi (fromAList prog) co cc lims (wl_state_stack_size t) start = Fail) /\
     ~(data_to_word_config_gc_kind conf = data_to_word_None) /\
     data_lang_safe_for_space ffi (fromAList prog) lims (wl_state_stack_size t) start ==>
     !k. ?ck.
       (~(FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                            wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME NotEnoughSpace) /\
        wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                        wl_state_clock_fupd (combin_K (k + ck)) t))) =
        data_state_ffi (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                                            data_initial_state ffi (fromAList prog) co cc T
                                              lims (wl_state_stack_size t) k))) /\
        ((?v w. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                       data_initial_state ffi (fromAList prog) co cc T lims
                         (wl_state_stack_size t) k)) = SOME (Rval v) /\
                FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                       wl_state_clock_fupd (combin_K (k + ck)) t)) =
                  SOME (wl_Result (wl_Loc 1 0) w)) \/
         (FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                 data_initial_state ffi (fromAList prog) co cc T lims
                   (wl_state_stack_size t) k)) = SOME (Rerr (Rabort Rtimeout_error)) /\
          FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                 wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME wl_TimeOut) \/
         (?f. FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                     data_initial_state ffi (fromAList prog) co cc T lims
                       (wl_state_stack_size t) k)) = SOME (Rerr (Rabort (Rffi_error f))) /\
              FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                     wl_state_clock_fupd (combin_K (k + ck)) t)) = SOME (wl_FinalFFI f))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP D2WPAUX_data_sem_ok) THEN
  DISCH_THEN(LABEL_TAC "dk") THEN
  FIRST_ASSUM(MP_TAC o SPECL [`co:num->C#(num#num#data_prog)list`;
    `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`; `k:num`] o
    MATCH_MP D2WPAUX_safe_all) THEN
  DISCH_THEN(LABEL_TAC "sf") THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `ffi:(FFI)ffi_state`;
                 `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                 `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                 `lims:limits`; `t:(A,C,FFI)wl_state`; `start:num`; `k:num`]
         D2WPAUX_sem_sim) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "dk" (REPEAT_TCL DISJ_CASES_THEN
      (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                injectivity "error_result"; distinctness "abort"];
    ALL_TAC] THEN
  MP_TAC(ISPEC (d2wpaux_D `k:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s:(C,FFI)data_state` (fun th -> REWRITE_TAC[th] THEN
       USE_THEN "sf" (ASSUME_TAC o REWRITE_RULE[th; SND]) THEN
       USE_THEN "dk" (MP_TAC o REWRITE_RULE[th; FST])))) THEN
  CAKE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "rk") THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (fun th -> EXISTS_TAC `ck:num` THEN MP_TAC th)) THEN
  MP_TAC(ISPEC (d2wpaux_W `k + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option`
    (X_CHOOSE_THEN `u:(A,C,FFI)wl_state` (fun th -> REWRITE_TAC[th]))) THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  ASM_CASES_TAC `q = SOME NotEnoughSpace:((A)wl_result)option` THEN
  ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (fst (dest_imp (concl th))))) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "rk" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                   injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
  MESON_TAC[]);;

(* HOL4 line 1529 *)
let compile_semantics_precise_lemma = prove
 (`!conf (ffi:(FFI)ffi_state) prog co cc lims (t:(A,C,FFI)wl_state) fs start.
     state_rel_ext conf 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     fs = wl_state_stack_size t /\
     data_lang_safe_for_space ffi (fromAList prog) lims fs start /\
     ~(data_to_word_config_gc_kind conf = data_to_word_None) /\
     ~(data_semantics ffi (fromAList prog) co cc lims fs start = Fail) ==>
     wl_semantics t start IN
       extend_with_resource_limit' T
         {data_semantics ffi (fromAList prog) co cc lims fs start}`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) &&
    fst(dest_var(lhs(concl th))) = "fs")) THEN
  REWRITE_TAC[extend_with_resource_limit'_def; IN_SING] THEN
  FIRST_ASSUM(LABEL_TAC "dok" o MATCH_MP D2WPAUX_data_sem_ok) THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `ffi:(FFI)ffi_state`;
                 `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                 `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                 `lims:limits`; `t:(A,C,FFI)wl_state`; `start:num`] D2WPAUX_sem_sim3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sim") THEN
  SUBGOAL_THEN
   `!k. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                          wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state))) = SOME wl_TimeOut \/
        (?ys. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                wl_state_clock_fupd (combin_K k) t)) =
                SOME (wl_Result (wl_Loc 1 0) ys)) \/
        (?f. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                               wl_state_clock_fupd (combin_K k) t)) = SOME (wl_FinalFFI f))`
    (LABEL_TAC "wok") THENL
   [GEN_TAC THEN
    ASM_CASES_TAC (mk_eq(mk_comb(`FST:((A)wl_result)option#(A,C,FFI)wl_state->
                                    ((A)wl_result)option`, d2wpaux_W `k:num`),
                         `SOME (wl_TimeOut:(A)wl_result)`)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sim" (X_CHOOSE_TAC `ck:num` o SPEC `k:num`) THEN
    MP_TAC (SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `t:(A,C,FFI)wl_state`;
                   `k:num`; `k + ck:num`] D2WPAUX_word_add_clock) THEN
    ASM_REWRITE_TAC[LE_ADD] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `~(wl_semantics (t:(A,C,FFI)wl_state) start = Fail)` (LABEL_TAC "wnf") THENL
   [REWRITE_TAC[wl_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `kk:num` MP_TAC) THEN USE_THEN "wok" (MP_TAC o SPEC `kk:num`) THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
      CAKE_REWRITE_TAC[];
      d2wpaux_some_intro_tac THEN REWRITE_TAC[distinctness "behaviour"] THEN
      CAKE_REWRITE_TAC[distinctness "behaviour"] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[distinctness "behaviour"]];
    ALL_TAC]) THEN
  (ASM_CASES_TAC (mk_exists(`kw:num`, mk_neg(mk_eq(mk_comb(
    `FST:((A)wl_result)option#(A,C,FFI)wl_state->((A)wl_result)option`,
    d2wpaux_W `kw:num`), `SOME (wl_TimeOut:(A)wl_result)`))))) THENL
  [(FIRST_X_ASSUM(X_CHOOSE_TAC `kw:num`) THEN
  MP_TAC (ISPEC (d2wpaux_W `kw:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:((A)wl_result)option` (X_CHOOSE_THEN `sw:(A,C,FFI)wl_state`
    (LABEL_TAC "evw"))) THEN
  SUBGOAL_THEN `(?ys. rw = SOME (wl_Result (wl_Loc 1 0) ys):((A)wl_result)option) \/
                (?f. rw = SOME (wl_FinalFFI f))` (LABEL_TAC "rwok") THENL
   [USE_THEN "wok" (MP_TAC o SPEC `kw:num`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?outcome. (?e. rw = SOME (wl_FinalFFI e):((A)wl_result)option /\
                               outcome = FFI_outcome e) \/
                          (?w ys. rw = SOME (wl_Result w ys) /\ outcome = Success) \/
                          (rw = SOME NotEnoughSpace /\ outcome = Resource_limit_hit)`
    (X_CHOOSE_THEN `outcome:outcome` (LABEL_TAC "woc")) THENL
   [USE_THEN "rwok" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:(A,C,FFI)wl_state`; `start:num`; `kw:num`; `rw:((A)wl_result)option`;
                `sw:(A,C,FFI)wl_state`; `outcome:outcome`] D2WPAUX_word_sem_term) THEN
  USE_THEN "wnf" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "woc" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC) THEN
   (ASM_CASES_TAC (mk_exists(`kd:num`, mk_neg(mk_eq(mk_comb(
    `FST:((data_v list,data_v)result)option#(C,FFI)data_state->
         ((data_v list,data_v)result)option`, d2wpaux_D `kd:num`),
    `SOME (Rerr (Rabort Rtimeout_error)):((data_v list,data_v)result)option`))))) THENL
   [(FIRST_X_ASSUM(X_CHOOSE_TAC `kd:num`) THEN
  MP_TAC (ISPEC (d2wpaux_D `kd:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rd':((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `sd:(C,FFI)data_state` (LABEL_TAC "evd"))) THEN
  USE_THEN "dok" (MP_TAC o SPEC `kd:num`) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  USE_THEN "evd" (fun th -> REWRITE_TAC[th; FST]) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?rd doutcome. rd' = SOME (rd:(data_v list,data_v)result) /\
     ((?v. rd = Rval v /\ doutcome = Success) \/
      (?e. rd = Rerr (Rabort (Rffi_error e)) /\ doutcome = FFI_outcome e))`
    (X_CHOOSE_THEN `rd:(data_v list,data_v)result` (X_CHOOSE_THEN `doutcome:outcome`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "doc")))) THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) o
      check (is_disj o concl)) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `fromAList prog:(num#data_prog)spt`;
                `co:num->C#(num#num#data_prog)list`;
                `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                `lims:limits`; `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`;
                `kd:num`; `rd:(data_v list,data_v)result`; `sd:(C,FFI)data_state`;
                `doutcome:outcome`] D2WPAUX_data_sem_term) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "evd" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "doc" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC) THEN
    (USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kd:num`) THEN
  USE_THEN "evd" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
  MP_TAC (ISPEC (d2wpaux_W `kd + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)wl_result)option` (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state`
    (LABEL_TAC "ev2"))) THEN
  USE_THEN "ev2" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
  REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
              injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
  DISCH_THEN(LABEL_TAC "s2rel") THEN
  SUBGOAL_THEN `~(r2 = SOME wl_TimeOut:((A)wl_result)option)` ASSUME_TAC THENL
   [USE_THEN "s2rel" MP_TAC THEN USE_THEN "doc" MP_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)))) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
    ALL_TAC] THEN
  MP_TAC(SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `t:(A,C,FFI)wl_state`;
                `kw:num`; `kd + ck:num`] D2WPAUX_word_det) THEN
  USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ev2" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> t = `kw:num`)) (concl th))) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "ffieq"))) THEN
  USE_THEN "s2rel" (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `outcome:outcome = doutcome` SUBST1_TAC THENL
   [REMOVE_THEN "woc" MP_TAC THEN REMOVE_THEN "doc" MP_TAC THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) o
      check (fun th -> is_disj (concl th) &&
        can (find_term (fun t -> t = `r2:((A)wl_result)option`)) (concl th) &&
        can (find_term (fun t -> t = `rd:(data_v list,data_v)result`)) (concl th))) THEN
    ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result";
      distinctness "result"; injectivity "result"; injectivity "error_result";
      distinctness "abort"; injectivity "abort"; distinctness "error_result"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[];
    (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM] o
    check (fun th -> is_neg (concl th) && is_exists (dest_neg (concl th)))) THEN
  USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kw:num`) THEN
  MP_TAC (ISPEC (d2wpaux_W `kw + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)wl_result)option` (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state`
    (LABEL_TAC "ev2"))) THEN
  USE_THEN "ev2" (fun th -> REWRITE_TAC[th; FST; SND]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
              injectivity "error_result"; distinctness "abort"; distinctness "error_result"] THEN
  MP_TAC(SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `t:(A,C,FFI)wl_state`;
                `kw:num`; `kw + ck:num`] D2WPAUX_word_add_clock) THEN
  USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ev2" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FST; SND; LE_ADD] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> t = `kw:num`)) (concl th))) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "ffieq")) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term (fun t -> t = `kw:num`)) (concl th))) THEN
  USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST]) THEN ASM_REWRITE_TAC[])];
   (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM] o
    check (fun th -> is_neg (concl th) && is_exists (dest_neg (concl th)))) THEN
  MP_TAC(SPECL [`t:(A,C,FFI)wl_state`; `start:num`] D2WPAUX_word_sem_div) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   (mk_forall(`kd:num`, mk_eq(mk_comb(
      `FST:((data_v list,data_v)result)option#(C,FFI)data_state->
           ((data_v list,data_v)result)option`, d2wpaux_D `kd:num`),
      `SOME (Rerr (Rabort Rtimeout_error)):((data_v list,data_v)result)option`)))
    (LABEL_TAC "ddiv") THENL
   [GEN_TAC THEN USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kd:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kd + ck:num` o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ffi:(FFI)ffi_state`; `fromAList prog:(num#data_prog)spt`;
                `co:num->C#(num#num#data_prog)list`;
                `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                `lims:limits`; `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`]
         D2WPAUX_data_sem_div) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!kd. ?ck. wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                  wl_state_clock_fupd (combin_K (kd + ck)) (t:(A,C,FFI)wl_state)))) =
              data_state_ffi (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                  data_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num->C#(num#num#data_prog)list) cc T lims
                    (wl_state_stack_size t) kd)))`
    (LABEL_TAC "ffisim") THENL
   [GEN_TAC THEN USE_THEN "sim" (MP_TAC o SPEC `kd:num`) THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[injectivity "behaviour"] THEN
  MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
  REWRITE_TAC[D2WPAUX_word_io_chain; D2WPAUX_data_io_chain] THEN
  REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THEN X_GEN_TAC `kc:num` THEN
  USE_THEN "ffisim" (X_CHOOSE_TAC `ck:num` o SPEC `kc:num`) THENL
   [EXISTS_TAC `kc:num` THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
    MATCH_MP_TAC D2WPAUX_word_io_mono THEN ARITH_TAC;
    EXISTS_TAC `kc + ck:num` THEN
    ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL]])]);;

(* HOL4 line 1757 *)
let compile_semantics_precise = prove
 (`!conf (ffi:(FFI)ffi_state) prog co cc lims (t:(A,C,FFI)wl_state) fs start.
     state_rel_ext conf 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     fs = wl_state_stack_size t /\
     ~(data_to_word_config_gc_kind conf = data_to_word_None) /\
     ~(data_semantics ffi (fromAList prog) co cc lims fs start = Fail) /\
     data_lang_safe_for_space ffi (fromAList prog) lims fs start ==>
     wl_semantics t start = data_semantics ffi (fromAList prog) co cc lims fs start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL compile_semantics_precise_lemma) THEN
  REWRITE_TAC[extend_with_resource_limit'_def; IN_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* HOL4 line 1768 *)
let get_limits_def = cake_def
  `get_limits (c:data_to_word_config) (t:(A,C,FFI)wl_state) =
     limits_REC
       (val (theWord (FAPPLY (wl_state_store t) HeapLength)) DIV (dimindex (:A) DIV 8))
       (data_to_word_config_len_size c)
       (wl_state_stack_limit t)
       (dimindex (:A) = 64)
       (data_to_word_config_has_fp_ops c)
       (data_to_word_config_has_fp_tern c)`;;

(* HOL4 line 1779 *)
let option_le_SOME = prove
 (`!x n. option_le x (SOME n) <=> ?m. x = SOME m /\ m <= n`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:num option` (cases "option")) THEN
  REWRITE_TAC[option_le_def; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* the heap limit of get_limits, from the limit of init_store_ok *)
let D2WPAUX_heap_limit_arith = prove
 (`!c limit. good_dimindex (:A) /\ limit <= max_heap_limit (:A) c ==>
     val (word_mul (bytes_in_word:A word) (word limit)) DIV (dimindex (:A) DIV 8) = limit /\
     limit * val (bytes_in_word:A word) < dimword (:A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[max_heap_limit_def; backend_common_word_shift_def; dimword_def;
    bytes_in_word_def; GSYM WORD_MUL; VAL_WORD; good_dimindex_def;
    ARITH_RULE `x <= MIN a b <=> x <= a /\ x <= b`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `dimindex(:A)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THENL
   [SUBGOAL_THEN `limit * 4 < 4294967296` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `limit * 4 < 4294967296 ==> 4 * limit < 4294967296`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ];
    SUBGOAL_THEN `limit * 8 < 18446744073709551616` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT;
      ARITH_RULE `limit * 8 < 18446744073709551616 ==> 8 * limit < 18446744073709551616`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ]]);;

(* the state relation of compile_semantics (HOL4 the first subproof): the  *)
(* witness of state_rel_ext is t with the code x1, termdep 2 and the       *)
(* compile functions tco and tcc of data_to_word                            *)
let D2WPAUX_cs_state_rel_ext = prove
 (`!(t:(A,C,FFI)wl_state) c x1 prog cc tcc co tco tt kk aa coo.
     wl_state_handler t = 0 /\ wl_state_gc_fun t = word_gc_fun c /\
     init_store_ok c (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (wl_state_code_buffer t) (wl_state_data_buffer t) /\
     good_dimindex (:A) /\ lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\
     wl_state_stack t = [] /\
     conf_ok (:A) c /\ wl_state_termdep t = 0 /\
     data_to_word_gcProof_code_rel c (fromAList prog) x1 /\
     cc = (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o tcc cfg o
                 MAP (data_to_word_compile_part c)) /\
     (tco = (I ## MAP (data_to_word_compile_part c)) o co) /\
     (!n. ALL (\(n,_). data_num_stubs <= n) (SND (co n))) /\
     code_rel_ext x1 (wl_state_code t) /\ domain x1 = domain (wl_state_code t) /\
     wl_state_be t = data_to_word_config_be c /\
     wl_state_stack_max t = SOME 1 /\ wl_state_locals_size t = SOME 0 /\
     wl_state_compile_oracle t =
       (I ## MAP (\p. full_compile_single tt kk aa coo (p,NONE))) o tco /\
     (tcc = (\conf progs. wl_state_compile t conf
               (MAP (\p. full_compile_single tt kk aa coo (p,NONE)) progs)))
     ==>
     state_rel_ext c 1 0
       (data_initial_state (wl_state_ffi t) (fromAList prog) co cc T (get_limits c t)
          (wl_state_stack_size t) (wl_state_clock t)) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[state_rel_ext_def] THEN
  MAP_EVERY EXISTS_TAC
   [`wl_state_code_fupd (combin_K x1) (wl_state_termdep_fupd (combin_K 2)
       (wl_state_compile_oracle_fupd (combin_K tco)
          (wl_state_compile_fupd (combin_K tcc) (t:(A,C,FFI)wl_state))))`;
    `wl_state_code (t:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`wl_state_code_fupd (combin_K x1) (wl_state_termdep_fupd (combin_K 2)
       (wl_state_compile_oracle_fupd (combin_K tco)
          (wl_state_compile_fupd (combin_K tcc) (t:(A,C,FFI)wl_state))))`;
     `wl_state_ffi (t:(A,C,FFI)wl_state)`; `c:data_to_word_config`;
     `fromAList prog:(num#data_prog)spt`;
     `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
     `co:num->C#(num#num#data_prog)list`; `1`; `0`; `get_limits c (t:(A,C,FFI)wl_state)`]
     state_rel_init) THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[init_store_ok_def] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "init_store_ok"
      with Failure _ -> false)) THEN
    DISCH_THEN(X_CHOOSE_THEN `limit:num` (X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength =
                  wl_Word (word_mul bytes_in_word (word limit))` ASSUME_TAC THENL
     [UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength =
                     SOME (wl_Word (word_mul bytes_in_word (word limit)))` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
      REWRITE_TAC[option_INJ; option_DISTINCT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `limit:num`] D2WPAUX_heap_limit_arith) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[get_limits_def; limits_INFO.ri_accessors; theWord_def;
                    code_oracle_rel_def];
    ASM_REWRITE_TAC[];
    ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`tt:bool`; `kk:num`; `aa:num`; `coo:(A)asm_config`] THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
      "code_rel_ext" with Failure _ -> false)) THEN
    REWRITE_TAC[code_rel_ext_def; FORALL_PAIR_THM] THEN MESON_TAC[];
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[]]);;

(* the word program is safe for space when the data program is (HOL4 the   *)
(* last subproof of compile_semantics), at any clock k: the stack_max of  *)
(* the word run at k is below that of the word run at k + ck, which is    *)
(* below that of the data run at k, which is below the stack limit        *)
let D2WPAUX_cs_safe = prove
 (`!c (ffi:(FFI)ffi_state) (t:(A,C,FFI)wl_state) prog (co:num->C#(num#num#data_prog)list) cc
    lims start.
     state_rel_ext c 1 0
       (data_initial_state ffi (fromAList prog) co cc T lims (wl_state_stack_size t)
          (wl_state_clock t)) t /\
     limits_stack_limit lims = wl_state_stack_limit t /\ ~(wl_state_stack_limit t = 0) /\
     ~(data_semantics ffi (fromAList prog) co cc lims (wl_state_stack_size t) start = Fail) /\
     data_lang_safe_for_space ffi (fromAList prog) lims (wl_state_stack_size t) start ==>
     word_lang_safe_for_space t start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[word_lang_safe_for_space_def; LET_DEF; LET_END_DEF] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `res:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`] THEN
  DISCH_THEN(LABEL_TAC "ev1") THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP D2WPAUX_data_sem_ok) THEN
  DISCH_THEN(LABEL_TAC "dk") THEN
  FIRST_ASSUM(MP_TAC o SPECL [`co:num->C#(num#num#data_prog)list`;
    `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`; `k:num`] o
    MATCH_MP D2WPAUX_safe_all) THEN
  DISCH_THEN(LABEL_TAC "sf") THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `ffi:(FFI)ffi_state`;
                 `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                 `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                 `lims:limits`; `t:(A,C,FFI)wl_state`; `start:num`; `k:num`]
         D2WPAUX_sem_sim) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "dk" (REPEAT_TCL DISJ_CASES_THEN
      (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[option_INJ; distinctness "result"; injectivity "result";
                injectivity "error_result"; distinctness "abort"];
    ALL_TAC] THEN
  MP_TAC(ISPEC (d2wpaux_D `k:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s:(C,FFI)data_state` (fun th -> REWRITE_TAC[th] THEN
       USE_THEN "sf" (ASSUME_TAC o REWRITE_RULE[th; SND]) THEN LABEL_TAC "evd" th))) THEN
  CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` MP_TAC) THEN
  MP_TAC(ISPEC (d2wpaux_W `k + ck:num`) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option`
    (X_CHOOSE_THEN `u:(A,C,FFI)wl_state` (fun th -> REWRITE_TAC[th] THEN LABEL_TAC "evw" th))) THEN
  CAKE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "le1" o CONJUNCT1) THEN
  MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                 `wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state)`;
                 `res:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`; `ck:num`;
                 `q:((A)wl_result)option`; `u:(A,C,FFI)wl_state`]
         evaluate_stack_max_only_grows) THEN
  REWRITE_TAC[wl_inc_clock_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN
  USE_THEN "ev1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "evw" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(LABEL_TAC "le0") THEN
  MP_TAC(ISPECL [`data_Call NONE (SOME start) [] NONE`;
    `data_initial_state (ffi:(FFI)ffi_state) (fromAList prog) (co:num->C#(num#num#data_prog)list)
       cc T lims (wl_state_stack_size (t:(A,C,FFI)wl_state)) k`;
    `r:((data_v list,data_v)result)option`; `s:(C,FFI)data_state`]
    evaluate_stack_max_le_stack_limit) THEN
  MP_TAC(ISPECL [`data_Call NONE (SOME start) [] NONE`;
    `data_initial_state (ffi:(FFI)ffi_state) (fromAList prog) (co:num->C#(num#num#data_prog)list)
       cc T lims (wl_state_stack_size (t:(A,C,FFI)wl_state)) k`;
    `r:((data_v list,data_v)result)option`; `s:(C,FFI)data_state`]
    data_evaluate_stack_limit) THEN
  USE_THEN "evd" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[data_initial_state_def; data_state_INFO.ri_accessors] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[option_le_def] THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(wl_state_stack_limit (t:(A,C,FFI)wl_state) = 0)` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                 `wl_state_clock_fupd (combin_K k) (t:(A,C,FFI)wl_state)`;
                 `res:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`] wl_evaluate_stack_limit) THEN
  USE_THEN "ev1" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM option_le_SOME] THEN
  ASM_MESON_TAC[option_le_trans]);;

(* HOL4 line 1785 (HOL4 Abbrev (x = e) is the plain equation) *)
let data_to_wordProof_compile_semantics = prove
 (`!(t:(A,C,FFI)wl_state) c x1 prog cc tcc co tco tt kk aa coo fs start.
     wl_state_handler t = 0 /\ wl_state_gc_fun t = word_gc_fun c /\
     init_store_ok c (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (wl_state_code_buffer t) (wl_state_data_buffer t) /\
     good_dimindex (:A) /\ lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\
     wl_state_stack t = [] /\
     conf_ok (:A) c /\ wl_state_termdep t = 0 /\
     data_to_word_gcProof_code_rel c (fromAList prog) x1 /\
     cc = (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o tcc cfg o
                 MAP (data_to_word_compile_part c)) /\
     (tco = (I ## MAP (data_to_word_compile_part c)) o co) /\
     (!n. ALL (\(n,_). data_num_stubs <= n) (SND (co n))) /\
     code_rel_ext x1 (wl_state_code t) /\ domain x1 = domain (wl_state_code t) /\
     wl_state_be t = data_to_word_config_be c /\
     wl_state_stack_max t = SOME 1 /\ wl_state_locals_size t = SOME 0 /\
     ~(wl_state_stack_limit t = 0) /\
     wl_state_compile_oracle t =
       (I ## MAP (\p. full_compile_single tt kk aa coo (p,NONE))) o tco /\
     (tcc = (\conf progs. wl_state_compile t conf
               (MAP (\p. full_compile_single tt kk aa coo (p,NONE)) progs))) /\
     fs = wl_state_stack_size t /\
     ~(Fail = data_semantics (wl_state_ffi t) (fromAList prog) co cc zero_limits fs start)
     ==>
     (data_lang_safe_for_space (wl_state_ffi t) (fromAList prog) (get_limits c t) fs start /\
      ~(data_to_word_config_gc_kind c = data_to_word_None) ==>
      word_lang_safe_for_space t start) /\
     wl_semantics t start IN
       extend_with_resource_limit'
         (data_lang_safe_for_space (wl_state_ffi t) (fromAList prog) (get_limits c t) fs
            start /\ ~(data_to_word_config_gc_kind c = data_to_word_None))
         {data_semantics (wl_state_ffi t) (fromAList prog) co cc zero_limits fs start}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) &&
    fst(dest_var(lhs(concl th))) = "fs")) THEN
  MP_TAC(SPEC_ALL D2WPAUX_cs_state_rel_ext) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "sre")] THEN
  SUBGOAL_THEN
   `data_semantics (wl_state_ffi (t:(A,C,FFI)wl_state)) (fromAList prog)
      (co:num->C#(num#num#data_prog)list)
      (cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option) zero_limits
      (wl_state_stack_size t) start =
    data_semantics (wl_state_ffi t) (fromAList prog) co cc (get_limits c t)
      (wl_state_stack_size t) start`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[semantics_zero_limits] THEN REFL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GSYM o check (fun th -> is_neg (concl th) &&
    is_eq (dest_neg (concl th)) && lhs (dest_neg (concl th)) = `Fail`)) THEN
  SUBGOAL_THEN `limits_stack_limit (get_limits c (t:(A,C,FFI)wl_state)) =
                wl_state_stack_limit t` ASSUME_TAC THENL
   [REWRITE_TAC[get_limits_def; limits_INFO.ri_accessors]; ALL_TAC] THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_ffi (t:(A,C,FFI)wl_state)`;
                   `t:(A,C,FFI)wl_state`; `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                   `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                   `get_limits c (t:(A,C,FFI)wl_state)`; `start:num`] D2WPAUX_cs_safe) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `data_lang_safe_for_space (wl_state_ffi (t:(A,C,FFI)wl_state)) (fromAList prog)
      (get_limits c t) (wl_state_stack_size t) start /\
    ~(data_to_word_config_gc_kind c = data_to_word_None)` THENL
   [POP_ASSUM(fun th -> STRIP_ASSUME_TAC th THEN
      REWRITE_TAC[th; extend_with_resource_limit'_def; IN_SING]) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_ffi (t:(A,C,FFI)wl_state)`;
                   `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                   `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                   `get_limits c (t:(A,C,FFI)wl_state)`; `t:(A,C,FFI)wl_state`;
                   `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`] compile_semantics_precise) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC);
    POP_ASSUM(fun th -> REWRITE_TAC[th; extend_with_resource_limit'_def]) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_ffi (t:(A,C,FFI)wl_state)`;
                   `prog:(num#num#data_prog)list`; `co:num->C#(num#num#data_prog)list`;
                   `cc:C->(num#num#data_prog)list->((8 word)list#(64 word)list#C)option`;
                   `get_limits c (t:(A,C,FFI)wl_state)`; `t:(A,C,FFI)wl_state`;
                   `wl_state_stack_size (t:(A,C,FFI)wl_state)`; `start:num`] compile_semantics_lemma) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC)]);;

(* HOL4 line 1919: val extract_labels_def = wordConvs extract_labels_def    *)

(* HOL4 line 1921 *)
let extract_labels_MemEqList = prove
 (`!(a:A word) x. wordConvs_extract_labels (MemEqList a x) = []`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MemEqList_def; wordConvs_extract_labels_def; APPEND]);;

let _ = cake_add_simps [extract_labels_MemEqList];;

(* HOL4 line 1928 *)
let extract_labels_StoreEach = prove
 (`!xs a (d:A word). wordConvs_extract_labels (StoreEach a xs d) = []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[StoreEach_def; wordConvs_extract_labels_def; APPEND]);;

(* the induction of StoreAnyConsts, for a property P of programs whose     *)
(* clauses are the rewrites rws                                              *)
let d2wpaux_sac_tac (rws:thm list) : tactic =
  MATCH_MP_TAC StoreAnyConsts_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[StoreAnyConsts_def] THEN
    MP_TAC(ISPEC `SND (v:bool#A word_loc)` (cases "word_loc")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC rws;
    STRIP_TAC THEN ONCE_REWRITE_TAC[StoreAnyConsts_def] THEN
    MP_TAC(ISPEC `SND (v:bool#A word_loc)` (cases "word_loc")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    TRY(MP_TAC(ISPEC `getWords (CONS (v:bool#A word_loc) vs) []` PAIR_SURJECTIVE) THEN
        DISCH_THEN(REPEAT_TCL CHOOSE_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
        CAKE_REWRITE_TAC[]) THEN
    REWRITE_TAC rws THEN ASM_MESON_TAC[]];;

(* HOL4 line 1934 *)
let extract_labels_StoreAnyConsts = prove
 (`!r1 r2 r3 ws (w:bool#A word_loc).
     wordConvs_extract_labels (StoreAnyConsts r1 r2 r3 ws w) = []`,
  d2wpaux_sac_tac [wordConvs_extract_labels_def; data_to_word_list_Seq_def; APPEND]);;

(* HOL4 line 1946 (local) *)
let extract_labels_WordOp64_on_32 = prove
 (`!f. wordConvs_extract_labels (WordOp64_on_32 f:(A)wl_prog) = []`,
  GEN_TAC THEN CASES_ON `f:opw` THEN REWRITE_TAC[WordOp64_on_32_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_list_Seq_def; wordConvs_extract_labels_def; APPEND]);;

(* HOL4 line 1953 (local) *)
let extract_labels_WordShift64_on_32 = prove
 (`!f g. wordConvs_extract_labels (WordShift64_on_32 f g:(A)wl_prog) = []`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WordShift64_on_32_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASES_ON `f:shift` THEN CAKE_REWRITE_TAC[distinctness "shift"] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[data_to_word_list_Seq_def; wordConvs_extract_labels_def; APPEND]);;

(* pushing a function into a case expression: for a case constant CASE of  *)
(* the kit, g (CASE x f1 .. fn) = CASE x (\vs1. g (f1 vs1)) .. ; and the    *)
(* case expressions whose branches are all the same term                   *)
let d2wpaux_case_rand_cache = ref ([] : (string * (thm * thm)) list);;

let d2wpaux_case_rand_thms (cname:string) =
  try assoc cname !d2wpaux_case_rand_cache with Failure _ ->
  let ci = snd(find (fun (_,ci) -> fst(dest_const ci.ci_case) = cname) (!the_case_infos)) in
  let c = ci.ci_case in
  let n = length ci.ci_pats in
  let ty = hd(snd(dest_type(type_of c))) in
  let rty = funpow (n + 1) (fun t -> hd(tl(snd(dest_type t)))) (type_of c) in
  let sty = mk_vartype "D2WPAUXS" in
  let g = mk_var("g", mk_fun_ty rty sty) in
  let fs = map2 (fun (vs,_) i ->
                   mk_var("f"^string_of_int i, itlist (mk_fun_ty o type_of) vs rty))
                ci.ci_pats (1--n) in
  let x = mk_var("x",ty) in
  let c' = inst [sty,rty] c in
  let lhs = mk_comb(g, list_mk_comb(c, x::fs)) in
  let fs' = map2 (fun (vs,_) f -> list_mk_abs(vs, mk_comb(g, list_mk_comb(f,vs))))
                 ci.ci_pats fs in
  let rhs = list_mk_comb(c', x::fs') in
  let rand_th = prove(list_mk_forall(g::x::fs, mk_eq(lhs,rhs)),
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC x ci.ci_nchotomy) THEN
    REWRITE_TAC[ci.ci_def] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]) in
  let t = mk_var("t",rty) in
  let ts = map (fun (vs,_) -> list_mk_abs(vs,t)) ci.ci_pats in
  let id_th = prove(list_mk_forall([x;t], mk_eq(list_mk_comb(c, x::ts), t)),
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC x ci.ci_nchotomy) THEN
    REWRITE_TAC[ci.ci_def]) in
  d2wpaux_case_rand_cache := (cname,(rand_th,id_th)) :: !d2wpaux_case_rand_cache;
  (rand_th,id_th);;

(* (CASE x f1 .. fn) y = CASE x (\vs1. f1 vs1 y) .. *)
let d2wpaux_case_rator_cache = ref ([] : (string * thm) list);;

let d2wpaux_case_rator_thm (cname:string) =
  try assoc cname !d2wpaux_case_rator_cache with Failure _ ->
  let ci = snd(find (fun (_,ci) -> fst(dest_const ci.ci_case) = cname) (!the_case_infos)) in
  let c = ci.ci_case in
  let n = length ci.ci_pats in
  let ty = hd(snd(dest_type(type_of c))) in
  let rty = funpow (n + 1) (fun t -> hd(tl(snd(dest_type t)))) (type_of c) in
  let uty = mk_vartype "D2WPAUXU" and vty = mk_vartype "D2WPAUXV" in
  let fty = mk_fun_ty uty vty in
  let cf = inst [fty,rty] c and cv = inst [vty,rty] c in
  let fs = map2 (fun (vs,_) i ->
                   mk_var("f"^string_of_int i, itlist (mk_fun_ty o type_of) vs fty))
                ci.ci_pats (1--n) in
  let x = mk_var("x",ty) and y = mk_var("y",uty) in
  let lhs = mk_comb(list_mk_comb(cf, x::fs), y) in
  let fs' = map2 (fun (vs,_) f -> list_mk_abs(vs, mk_comb(list_mk_comb(f,vs), y)))
                 ci.ci_pats fs in
  let rhs = list_mk_comb(cv, x::fs') in
  let th = prove(list_mk_forall(x::fs@[y], mk_eq(lhs,rhs)),
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC x ci.ci_nchotomy) THEN
    REWRITE_TAC[ci.ci_def] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]) in
  d2wpaux_case_rator_cache := (cname,th) :: !d2wpaux_case_rator_cache;
  th;;

(* g a, with a a conditional or a case expression and g not a partial case *)
(* expression or conditional: push g inside                                *)
let d2wpaux_push_conv (heads:string list) : conv = fun tm ->
  let g,a = dest_comb tm in
  if is_cond g then REWR_CONV COND_RATOR tm
  else if is_case_app g then
    let rth = d2wpaux_case_rator_thm (fst(dest_const(fst(strip_comb g)))) in
    (REWR_CONV rth THENC DEPTH_CONV BETA_CONV) tm
  else
    let gh = fst(strip_comb g) in
    if not (is_const gh && mem (fst(dest_const gh)) heads)
    then failwith "d2wpaux_push_conv"
    else if is_cond a then REWR_CONV COND_RAND tm
    else if is_case_app a then
      let rth,_ = d2wpaux_case_rand_thms (fst(dest_const(fst(strip_comb a)))) in
      (REWR_CONV rth THENC DEPTH_CONV BETA_CONV) tm
    else failwith "d2wpaux_push_conv";;

(* a case expression whose branches are all the same term *)
let d2wpaux_case_id_conv : conv = fun tm ->
  if not (is_case_app tm) then failwith "d2wpaux_case_id_conv" else
  let h = fst(strip_comb tm) in
  let _,ith = d2wpaux_case_rand_thms (fst(dest_const h)) in
  REWR_CONV ith tm;;

(* the pushing conversion: rewrites rws, case reductions on constructors,   *)
(* beta, pushing into conditionals and cases, and collapsing them           *)
let d2wpaux_PUSH_CONV (heads:string list) (rws:thm list) : conv =
  let rw = GEN_REWRITE_CONV I (rws @ [COND_ID; COND_CLAUSES; ARITH_EQ; AND_CLAUSES; OR_CLAUSES; NOT_CLAUSES; IMP_CLAUSES]) in
  let cr = CAKE_REWRITE_CONV [] in
  let pc = d2wpaux_push_conv heads in
  TOP_DEPTH_CONV (FIRST_CONV [GEN_BETA_CONV; rw; NUM_RED_CONV; d2wpaux_case_id_conv; pc])
  THENC cr THENC
  TOP_DEPTH_CONV (FIRST_CONV [GEN_BETA_CONV; rw; NUM_RED_CONV; d2wpaux_case_id_conv; pc]);;

(* AssignCmp as one case expression (HOL4 oneline AssignCmp_def) *)
let D2WPAUX_AssignCmp_oneline = prove
 (CASE_TERM
  `!dest cmp v1 v2.
     AssignCmp dest cmp v1 v2:(A)wl_prog =
     match cmp with
       Lt -> SetBool dest Lower v1 (Reg v2)
     | Gt -> SetBool dest Lower v2 (Reg v1)
     | Leq -> SetBool dest NotLower v2 (Reg v1)
     | Geq -> SetBool dest NotLower v1 (Reg v2)`,
  REPEAT GEN_TAC THEN CASES_ON `cmp:opb` THEN REWRITE_TAC[AssignCmp_def] THEN
  CAKE_REWRITE_TAC[]);;

(* the definitions that the code of assign is made of *)
let D2WPAUX_assign_unfold_defs =
  [all_assign_defs; assign_def_extras; GiveUp_def; D2WPAUX_AssignCmp_oneline; SetBool_def;
   data_to_word_Maxout_bits_code_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF];;

(* no labels and a label counter that does not decrease *)
let D2WPAUX_nolab_def = new_definition
 `D2WPAUX_nolab l (p:(A)wl_prog#num) <=>
    wordConvs_extract_labels (FST p) = [] /\ l <= SND p`;;

let D2WPAUX_nolab_pair = prove
 (`!l (cp:(A)wl_prog) l'.
     D2WPAUX_nolab l (cp,l') <=> wordConvs_extract_labels cp = [] /\ l <= l'`,
  REWRITE_TAC[D2WPAUX_nolab_def; FST; SND]);;

(* the proof of extract_labels_assignWordOp and extract_labels_assignWordShift *)
let d2wpaux_nolab_tac : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM D2WPAUX_nolab_pair] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; arg3_def; arg4_def] THEN
  REWRITE_TAC D2WPAUX_assign_unfold_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["D2WPAUX_nolab"; "wordConvs_extract_labels";
                              "data_to_word_list_Seq"; "APPEND"]
    [D2WPAUX_nolab_pair; wordConvs_extract_labels_def; data_to_word_list_Seq_def; APPEND;
     extract_labels_WordOp64_on_32; extract_labels_WordShift64_on_32; LE_REFL; LET_DEF;
     LET_END_DEF]);;

(* HOL4 line 1961 (local) *)
let extract_labels_assignWordOp = prove
 (`!a b c d e f g h (i:(A)wl_prog) j.
     data_to_word_assign a b c d (WordOp (WordOpw e f)) g h = (i,j) ==>
     wordConvs_extract_labels i = [] /\ c <= j`,
  d2wpaux_nolab_tac);;

(* HOL4 line 1974 (local) *)
let extract_labels_assignWordShift = prove
 (`!a b c d e f k g h (i:(A)wl_prog) j.
     data_to_word_assign a b c d (WordOp (WordShift e f k)) g h = (i,j) ==>
     wordConvs_extract_labels i = [] /\ c <= j`,
  d2wpaux_nolab_tac);;

(* the labels of a compiled program with section secn from label l *)
let D2WPAUX_lab_ok_def = new_definition
 `D2WPAUX_lab_ok secn l (p:(A)wl_prog#num) <=>
    l <= SND p /\
    ALL (\(l1,l2). l1 = secn /\ l <= l2 /\ l2 < SND p) (wordConvs_extract_labels (FST p)) /\
    ALL_DISTINCT (wordConvs_extract_labels (FST p))`;;

let D2WPAUX_lab_ok_pair = prove
 (`!secn l (cp:(A)wl_prog) l'.
     D2WPAUX_lab_ok secn l (cp,l') <=>
     l <= l' /\
     ALL (\(l1,l2). l1 = secn /\ l <= l2 /\ l2 < l') (wordConvs_extract_labels cp) /\
     ALL_DISTINCT (wordConvs_extract_labels cp)`,
  REWRITE_TAC[D2WPAUX_lab_ok_def; FST; SND]);;

(* the labels of the code of assign *)
let D2WPAUX_lab_ok_assign = prove
 (`!c secn l dest op args names.
     D2WPAUX_lab_ok secn l (data_to_word_assign c secn l dest op args names:(A)wl_prog#num)`,
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN
  CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; arg3_def; arg4_def] THEN
  REWRITE_TAC D2WPAUX_assign_unfold_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["D2WPAUX_lab_ok"; "wordConvs_extract_labels";
                              "data_to_word_list_Seq"; "APPEND"; "ALL"; "ALL_DISTINCT"]
    [D2WPAUX_lab_ok_pair; wordConvs_extract_labels_def; data_to_word_list_Seq_def;
     SetBool_def; APPEND; ALL; ALL_DISTINCT; MEM; extract_labels_StoreEach;
     extract_labels_MemEqList; extract_labels_StoreAnyConsts; extract_labels_WordOp64_on_32;
     extract_labels_WordShift64_on_32; LE_REFL; LET_DEF; LET_END_DEF; PAIR_EQ;
     ARITH_RULE `!n. n <= n + 1 /\ n <= n + 2 /\ n < n + 1 /\ n < n + 2 /\
                     n + 1 < n + 2 /\ n + 1 <= n + 2 /\ ~(n = n + 1) /\
                     ~(n + 1 = n)`]));;

(* the induction of comp with the cases of the program split and the       *)
(* pairs and options of the comp clause split                              *)
let d2wpaux_comp_ind_tac : tactic =
  MATCH_MP_TAC data_to_word_comp_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `p:data_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "data_prog"; distinctness "data_prog"]) THEN
  REWRITE_TAC[D2WPAUX_comp_eqs; force_thunk_def] THEN REPEAT TOP_CASE_TAC;;

(* the labels of a sequence of two programs *)
let D2WPAUX_lab_seq = prove
 (`!n l l1 l2 (L1:(num#num)list) L2.
     (l <= l1 /\ ALL (\(a,b). a = n /\ l <= b /\ b < l1) L1 /\ ALL_DISTINCT L1) /\
     (l1 <= l2 /\ ALL (\(a,b). a = n /\ l1 <= b /\ b < l2) L2 /\ ALL_DISTINCT L2) ==>
     l <= l2 /\ ALL (\(a,b). a = n /\ l <= b /\ b < l2) (APPEND L1 L2) /\
     ALL_DISTINCT (APPEND L1 L2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_APPEND; ALL_DISTINCT_APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    RES_TAC THEN ASM_ARITH_TAC]);;

(* the labels of a call with a handler *)
let D2WPAUX_lab_handler = prove
 (`!n l l1 (L1:(num#num)list).
     l + 2 <= l1 /\ ALL (\(a,b). a = n /\ l + 2 <= b /\ b < l1) L1 /\ ALL_DISTINCT L1 ==>
     l <= l1 /\
     (l < l1 /\ l + 1 < l1 /\ ALL (\(a,b). a = n /\ l <= b /\ b < l1) L1) /\
     ~MEM (n,l) L1 /\ ~MEM (n,l + 1) L1 /\ ALL_DISTINCT L1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC THEN RES_TAC THEN ASM_ARITH_TAC]);;

(* the labels of comp *)
let D2WPAUX_lab_ok_comp = prove
 (`!c n l p. ~(l = 0) ==> D2WPAUX_lab_ok n l (data_to_word_comp c n l p:(A)wl_prog#num)`,
  d2wpaux_comp_ind_tac THEN DISCH_TAC THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["D2WPAUX_lab_ok"; "wordConvs_extract_labels";
                              "data_to_word_list_Seq"; "APPEND"; "ALL"; "ALL_DISTINCT"]
    [D2WPAUX_lab_ok_pair; wordConvs_extract_labels_def; data_to_word_list_Seq_def; LET_DEF;
     LET_END_DEF; SilentFFI_def; GiveUp_def; APPEND; ALL; ALL_DISTINCT; MEM; LE_REFL; PAIR_EQ;
     D2WPAUX_lab_ok_assign;
     ARITH_RULE `!n. n <= n + 1 /\ n <= n + 2 /\ n < n + 1 /\ n < n + 2 /\
                     n + 1 < n + 2 /\ n + 1 <= n + 2 /\ ~(n = n + 1) /\
                     ~(n + 1 = n)`]) THEN
  (fun (asl,w as g) ->
    if vfree_in `y'':num` w then
     (SUBGOAL_THEN `D2WPAUX_lab_ok secn (l + 2) (x'':(A)wl_prog,y'':num)` MP_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `~(l + 2 = 0)`]; ALL_TAC] THEN
      REWRITE_TAC[D2WPAUX_lab_ok_pair] THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP D2WPAUX_lab_handler)) g
    else
     (SUBGOAL_THEN `D2WPAUX_lab_ok secn l (x:(A)wl_prog,y:num)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(y = 0)` ASSUME_TAC THENL
       [UNDISCH_TAC `D2WPAUX_lab_ok secn l (x:(A)wl_prog,y:num)` THEN
        REWRITE_TAC[D2WPAUX_lab_ok_pair] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `D2WPAUX_lab_ok secn y (x':(A)wl_prog,y':num)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC D2WPAUX_lab_seq THEN EXISTS_TAC `y:num` THEN
      ASM_REWRITE_TAC[GSYM D2WPAUX_lab_ok_pair]) g));;

(* HOL4 line 1991 *)
let data_to_word_lab_pres_lem = prove
 (CASE_TERM
  `!c n l p.
     ~(l = 0) ==>
     let (cp,l') = (data_to_word_comp c n l p:(A)wl_prog#num) in
     l <= l' /\
     ALL (\(l1,l2). l1 = n /\ l <= l2 /\ l2 < l') (wordConvs_extract_labels cp) /\
     ALL_DISTINCT (wordConvs_extract_labels cp)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `n:num`; `l:num`; `p:data_prog`]
         (INST_TYPE [`:A`,`:A`] D2WPAUX_lab_ok_comp)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `data_to_word_comp c n l p:(A)wl_prog#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cp:(A)wl_prog` (X_CHOOSE_THEN `l':num` SUBST1_TAC)) THEN
  REWRITE_TAC[D2WPAUX_lab_ok_pair] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

(* HOL4 line 2042 (local) *)
let labels_rel_emp = prove
 (`!ls:A list. labels_rel [] ls ==> ls = []`,
  REWRITE_TAC[labels_rel_def; set_of_list; SUBSET_EMPTY; SET_OF_LIST_EQ_EMPTY] THEN
  MESON_TAC[]);;

(* the locations of the stubs, for any type argument *)
let D2WPAUX_MAP_FST_stubs = prove
 (`!(a:A->bool) c. MAP FST (data_to_word_stubs a c) =
     [7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 29; 30; 31; 33;
      34; 35; 36; 37; 38; 24; 25; 26; 27; 28; 32; 39; 61; 60; 59; 58; 54; 57; 56; 55;
      53; 52; 51; 50; 49; 47; 48; 46; 45; 44; 43; 42; 41; 40]`,
  REWRITE_TAC[data_to_word_stubs_DEF; generated_bignum_stubs_eq; MAP; APPEND; FST] THEN
  REWRITE_TAC D2WAUX_location_defs THEN CONV_TAC NUM_REDUCE_CONV);;

(* the definitions with a configuration argument that the stubs use *)
let D2WPAUX_conf_defs =
  [make_header_def; tag_mask_def; encode_header_def; small_shift_length_def; shift_length_def;
   ptr_bits_def; real_addr_def; real_offset_def; SilentFFI_def; AllocVar_def; RefByte_code_def;
   data_to_word_Make_ptr_bits_code_def; FromList_code_def; FromList1_code_def; RefArray_code_def;
   AddNumSize_def; AnyHeader_def; AnyArith_code_def; data_to_word_Install_code_def;
   InstallCode_code_def; InstallData_code_def; data_to_word_Compare_code_def;
   data_to_word_Equal_code_def; LongDiv_code_def; LongDiv1_code_def; data_to_word_Append_code_def;
   AppendMainLoop_code_def; AppendLenLoop_code_def; ByteCopy_code_def; ByteCopyNew_code_def;
   data_to_word_Maxout_bits_code_def; data_to_word_Replicate_code_def;
   data_to_word_Equal1_code_def];;

(* the code definitions of the stubs *)
let D2WPAUX_stub_code_defs =
  D2WPAUX_conf_defs @
  [data_to_word_Add_code_def; data_to_word_Sub_code_def; data_to_word_Mul_code_def;
   data_to_word_Div_code_def; data_to_word_Mod_code_def; data_to_word_Compare1_code_def;
   XorLoop_code_def; StringCmpLoop_code_def; MemCopy_code_def; ByteCopyAdd_code_def;
   ByteCopySub_code_def; generated_bignum_stubs_eq; GiveUp_def; BignumHalt_def;
   LoadWord64_def; WriteWord64_def; LoadBignum_def; ShiftVar_def; MakeBytes_def; SmallLsr_def;
   WriteLastByte_aux_def; WriteLastBytes_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF];;

(* the compset of the labels of concrete programs *)
let D2WPAUX_labels_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`,2,WORDP3AUX_EQ_CONV) cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  Compute.add_thms
    [wordConvs_extract_labels_def; APPEND; LET_END_DEF; case_def "option"; case_def "prod"] cs;
  cs;;

(* extract_labels of a concrete program by computation *)
let d2wpaux_el_conv : conv = fun tm ->
  let h = fst(strip_comb tm) in
  if is_const h && fst(dest_const h) = "wordConvs_extract_labels" then
    Compute.WEAK_CBV_CONV D2WPAUX_labels_cs tm
  else failwith "d2wpaux_el_conv";;

(* the labels of the generated bignum stubs *)
let D2WPAUX_bignum_stub_labels = prove
 (`!n. ALL (\(n,m,p).
            ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels p) /\
            ALL_DISTINCT (wordConvs_extract_labels p))
       (generated_bignum_stubs n:(num#num#(A)wl_prog)list)`,
  GEN_TAC THEN REWRITE_TAC[generated_bignum_stubs_eq; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV d2wpaux_el_conv) THEN
  REWRITE_TAC[ALL; ALL_DISTINCT; MEM; PAIR_EQ] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* HOL4 line 2048 *)
let stub_labels = prove
 (`!data_conf.
     ALL (\(n,m,p).
            ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels p) /\
            ALL_DISTINCT (wordConvs_extract_labels p))
       (data_to_word_stubs (:A) data_conf)`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_stubs_def; ALL_APPEND; D2WPAUX_bignum_stub_labels] THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC D2WPAUX_stub_code_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["wordConvs_extract_labels"; "data_to_word_list_Seq"; "APPEND";
                              "ALL"; "ALL_DISTINCT"]
    ([wordConvs_extract_labels_def; data_to_word_list_Seq_def; ALL; APPEND; ALL_DISTINCT;
      MEM; PAIR_EQ; LET_DEF; LET_END_DEF] @ D2WAUX_location_defs)));;

(* HOL4 line 2061 *)
let stubs_with_has_fp_ops = prove
 (`!data_conf b.
     data_to_word_stubs (:A) (data_to_word_config_has_fp_ops_fupd (combin_K b) data_conf) =
     data_to_word_stubs (:A) data_conf`,
  REWRITE_TAC[data_to_word_stubs_def] THEN
  REWRITE_TAC D2WPAUX_conf_defs THEN
  REWRITE_TAC[(record_info "data_to_word_config").ri_accfupds; K_THM]);;

let _ = cake_add_simps [stubs_with_has_fp_ops];;

(* HOL4 line 2067 *)
let stubs_with_has_fp_tern = prove
 (`!data_conf b.
     data_to_word_stubs (:A) (data_to_word_config_has_fp_tern_fupd (combin_K b) data_conf) =
     data_to_word_stubs (:A) data_conf`,
  REWRITE_TAC[data_to_word_stubs_def] THEN
  REWRITE_TAC D2WPAUX_conf_defs THEN
  REWRITE_TAC[(record_info "data_to_word_config").ri_accfupds; K_THM]);;

let _ = cake_add_simps [stubs_with_has_fp_tern];;

(* HOL4 line 2075 *)
let list_Seq_no_share_inst = prove
 (`!xs:((A)wl_prog)list. no_share_inst (data_to_word_list_Seq xs) = ALL no_share_inst xs`,
  MATCH_MP_TAC data_to_word_list_Seq_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_list_Seq_def; no_share_inst_def; ALL] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL]);;

(* HOL4 line 2082 *)
let StoreEach_no_share_inst = prove
 (`!v xs (offset:A word). no_share_inst (StoreEach v xs offset)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[StoreEach_def; no_share_inst_def]);;

(* HOL4 line 2089 *)
let MemEqList_no_share_inst = prove
 (`!(a:A word) xs. no_share_inst (MemEqList a xs)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MemEqList_def; no_share_inst_def]);;

(* HOL4 line 2096 *)
let StoreAnyConsts_no_share_inst = prove
 (`!r1 r2 r3 vs (v:bool#A word_loc). no_share_inst (StoreAnyConsts r1 r2 r3 vs v)`,
  d2wpaux_sac_tac [no_share_inst_def; list_Seq_no_share_inst; ALL; distinctness "wl_prog"]);;

(* HOL4 line 2108 *)
let stubs_no_share_inst = prove
 (`!data_conf. ALL (\x. no_share_inst (SND (SND x))) (data_to_word_stubs (:A) data_conf)`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_stubs_def; ALL; APPEND; SND] THEN
  REWRITE_TAC D2WPAUX_stub_code_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["no_share_inst"; "data_to_word_list_Seq"]
    ([no_share_inst_def; data_to_word_list_Seq_def; ALL; APPEND; SND] @
     CONJUNCTS (distinctness "wl_prog"))));;

(* the code of assign has no ShareInst *)
let D2WPAUX_no_share_inst_assign = prove
 (`!x c secn v w y z. no_share_inst (FST (data_to_word_assign c secn v w x y z):(A)wl_prog)`,
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN
  CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; arg3_def; arg4_def] THEN
  REWRITE_TAC D2WPAUX_assign_unfold_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "no_share_inst"; "data_to_word_list_Seq"]
    ([FST; no_share_inst_def; data_to_word_list_Seq_def; SetBool_def; StoreEach_no_share_inst;
      MemEqList_no_share_inst; StoreAnyConsts_no_share_inst] @
     CONJUNCTS (distinctness "wl_prog"))));;

(* the code of comp has no ShareInst *)
let D2WPAUX_comp_no_share_inst = prove
 (`!c secn l p. no_share_inst ((FST (data_to_word_comp c secn l p)):(A)wl_prog)`,
  d2wpaux_comp_ind_tac THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "no_share_inst"; "data_to_word_list_Seq"]
    ([FST; no_share_inst_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF; SilentFFI_def;
      GiveUp_def; D2WPAUX_no_share_inst_assign] @ CONJUNCTS (distinctness "wl_prog"))) THEN
  ASM_MESON_TAC[FST]);;

(* HOL4 line 2116 *)
let comp_no_share_inst = prove
 (`!c secn l prog (prog':(A)wl_prog) l'.
     data_to_word_comp c secn l prog = (prog',l') ==> no_share_inst prog'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `secn:num`; `l:num`; `prog:data_prog`]
         (INST_TYPE [`:A`,`:A`] D2WPAUX_comp_no_share_inst)) THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 line 2174 (local; DEVIATION: HOL4's ZIP truncates, so the HOL4      *)
(* statement is TAKE (LENGTH ys) xs for any lengths; HOL Light's ZIP has the *)
(* length of the first list: the hypothesis LENGTH xs <= LENGTH ys is        *)
(* added)                                                                    *)
let data_to_wordProof_MAP_FST_ZIP = prove
 (`!(xs:A list) (ys:B list).
     LENGTH xs <= LENGTH ys ==> MAP FST (ZIP xs ys) = TAKE (LENGTH ys) xs`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[TAKE_LENGTH_TOO_LONG] THEN
  SPEC_TAC(`ys:B list`,`ys:B list`) THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ZIP_DEF; MAP; FST]);;

(* the programs given to word_to_word have no ShareInst *)
let D2WPAUX_input_no_share_inst = prove
 (`!dc dc' prog.
     ALL (\(n,m,prg). no_share_inst prg)
       (APPEND (data_to_word_stubs (:A) dc)
          (MAP (data_to_word_compile_part dc') prog):(num#num#(A)wl_prog)list)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_APPEND] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `dc:data_to_word_config` (INST_TYPE [`:A`,`:A`] stubs_no_share_inst)) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; SND] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[D2WPAUX_comp_no_share_inst]]);;

(* the hypothesis of compile_to_word_conventions *)
let D2WPAUX_input_no_share_inst_or = prove
 (`!dc dc' prog (ac:(A)asm_config).
     ALL (\(n,m,prg). no_share_inst prg \/ ~(asm_config_ISA ac = Ag32))
       (APPEND (data_to_word_stubs (:A) dc)
          (MAP (data_to_word_compile_part dc') prog):(num#num#(A)wl_prog)list)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`dc:data_to_word_config`; `dc':data_to_word_config`;
                `prog:(num#num#data_prog)list`]
         (INST_TYPE [`:A`,`:A`] D2WPAUX_input_no_share_inst)) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[]);;

(* full_compile_single keeps no_share_inst *)
let D2WPAUX_full_compile_single_no_share_inst = prove
 (`!t k a (c:(A)asm_config) n m p col.
     no_share_inst p ==>
     no_share_inst (SND (SND (full_compile_single t k a c ((n,m,p),col))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[full_compile_single_def] THEN
  MP_TAC(ISPEC `word_to_word_compile_single t k a (c:(A)asm_config) ((n,m,p),col)`
         D2WPAUX_triple_cases) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` (X_CHOOSE_THEN `x3:(A)wl_prog`
    ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[SND] THEN
  MATCH_MP_TAC remove_must_terminate_no_share_inst THEN
  MP_TAC(ISPECL [`\q:(A)wl_prog. ~(ShareInst ARB 0 (wl_Var 0) = q)`;
                 `((n:num,m:num,p:(A)wl_prog),col:(num spt)option)`;
                 `t:bool`; `k:num`; `a:num`; `c:(A)asm_config`]
         (GENL [`P:(A)wl_prog->bool`; `prog_opt:(num#num#(A)wl_prog)#((num spt)option)`;
                `two_reg_arith:bool`; `reg_count:num`; `alg:num`; `c:(A)asm_config`]
               (SPEC_ALL compile_single_not_created_subprogs))) THEN
  ASM_REWRITE_TAC[GSYM no_share_inst_subprogs_def; FST; SND]);;

(* a property of the first components of a zip *)
let D2WPAUX_ALL_ZIP_FST = prove
 (`!(P:A->bool) (l:A list) (ns:B list). ALL P l ==> ALL (\x. P (FST x)) (ZIP l ns)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ZIP_DEF; ALL; FST]);;

(* HOL4 line 2182 *)
let compile_no_share_inst = prove
 (`!data_conf word_conf asm_conf prog xx (prog':(num#num#(A)wl_prog)list).
     data_to_word_compile data_conf word_conf asm_conf prog = (xx,prog') ==>
     ALL (\(n,m,pp). no_share_inst pp) prog'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_compile_def; word_to_word_compile_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CAKE_REWRITE_TAC[] THEN TOP_CASE_TAC THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ALL_MAP] THEN
  SPEC_TAC(`data_to_word_config_has_fp_ops_fupd (combin_K (1 < asm_config_fp_reg_count
              (asm_conf:(A)asm_config)))
             (data_to_word_config_has_fp_tern_fupd
                (combin_K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
                data_conf)`, `dc:data_to_word_config`) THEN GEN_TAC THEN
  MP_TAC(ISPECL [`\q:num#num#(A)wl_prog. no_share_inst (SND (SND q))`;
                 `APPEND (data_to_word_stubs (:A) dc)
                    (MAP (data_to_word_compile_part dc) prog):(num#num#(A)wl_prog)list`;
                 `x:((num spt)option)list`] D2WPAUX_ALL_ZIP_FST) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`dc:data_to_word_config`; `dc:data_to_word_config`;
                   `prog:(num#num#data_prog)list`]
       (INST_TYPE [`:A`,`:A`] D2WPAUX_input_no_share_inst)) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; SND] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; FST] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  W(fun (asl,w) -> MP_TAC(ISPEC (rand w) D2WPAUX_triple_cases)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:num` (X_CHOOSE_THEN `y2:num` (X_CHOOSE_THEN `y3:(A)wl_prog`
    ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`asm_config_two_reg_arith (asm_conf:(A)asm_config)`;
    `asm_config_reg_count (asm_conf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs asm_conf))`;
    `word_to_word_config_reg_alg word_conf`; `asm_conf:(A)asm_config`;
    `p1:num`; `p1':num`; `p2:(A)wl_prog`; `p2':(num spt)option`]
    D2WPAUX_full_compile_single_no_share_inst) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[SND]);;

(* the labels of the output of word_to_word, from labels_rel *)
let D2WPAUX_labels_transfer = prove
 (`!(p0:(num#num#(A)wl_prog)list) (progs:(num#num#(A)wl_prog)list).
     MAP FST progs = MAP FST p0 /\
     ALL2 labels_rel (MAP (wordConvs_extract_labels o SND o SND) p0)
                     (MAP (wordConvs_extract_labels o SND o SND) progs) /\
     ALL (\(n,m,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                      (wordConvs_extract_labels p) /\
                    ALL_DISTINCT (wordConvs_extract_labels p)) p0 ==>
     ALL (\(n,m,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                      (wordConvs_extract_labels p) /\
                    ALL_DISTINCT (wordConvs_extract_labels p)) progs`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `progs:(num#num#(A)wl_prog)list` list_CASES) THEN
  REWRITE_TAC[MAP; ALL; ALL2; NOT_CONS_NIL] THEN
  MAP_EVERY (fun v -> MP_TAC(ISPEC v PAIR_SURJECTIVE))
    [`h:num#num#(A)wl_prog`; `h':num#num#(A)wl_prog`] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `q2:num#(A)wl_prog` SUBST1_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `q1:num#(A)wl_prog` SUBST1_TAC)) THEN
  MAP_EVERY (fun v -> MP_TAC(ISPEC v PAIR_SURJECTIVE))
    [`q1:num#(A)wl_prog`; `q2:num#(A)wl_prog`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:num` (X_CHOOSE_THEN `r2:(A)wl_prog` SUBST1_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `r1:(A)wl_prog` SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND; o_THM; CONS_11; labels_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) &&
      is_var (rhs (concl th)) && type_of (lhs (concl th)) = `:num`)) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; GSYM ALL_MEM] THEN MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* the labels of the compiled parts *)
let D2WPAUX_parts_labels = prove
 (`!dc prog.
     ALL (\(n,m,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1))
                      (wordConvs_extract_labels p) /\
                    ALL_DISTINCT (wordConvs_extract_labels p))
       (MAP (data_to_word_compile_part dc) prog:(num#num#(A)wl_prog)list)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM;
                                  data_to_word_compile_part_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`dc:data_to_word_config`; `p1:num`; `2`; `p2:data_prog`]
         (INST_TYPE [`:A`,`:A`] D2WPAUX_lab_ok_comp)) THEN
  REWRITE_TAC[ARITH_RULE `~(2 = 0)`; D2WPAUX_lab_ok_def] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p1'':num`; `p2':num`]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 2213 *)
let data_to_word_compile_lab_pres = prove
 (CASE_TERM
  `!data_conf word_conf (asm_conf:(A)asm_config) prog.
     let (c,p) = data_to_word_compile data_conf word_conf asm_conf prog in
     MAP FST p = APPEND (MAP FST (data_to_word_stubs (:A) data_conf)) (MAP FST prog) /\
     ALL (\(n,m,(p:(A)wl_prog)).
            let labs = wordConvs_extract_labels p in
            ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
            ALL_DISTINCT labs) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_compile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SPEC_TAC(`data_to_word_config_has_fp_ops_fupd (combin_K (1 < asm_config_fp_reg_count
              (asm_conf:(A)asm_config)))
             (data_to_word_config_has_fp_tern_fupd
                (combin_K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
                data_conf)`, `dc:data_to_word_config`) THEN GEN_TAC THEN
  MP_TAC(SPEC `word_conf:word_to_word_config`
    (MATCH_MP (GEN_ALL (SPEC_ALL compile_to_word_conventions))
       (ISPECL [`dc:data_to_word_config`; `dc:data_to_word_config`;
                `prog:(num#num#data_prog)list`; `asm_conf:(A)asm_config`]
               D2WPAUX_input_no_share_inst_or))) THEN
  MP_TAC(ISPEC `word_to_word_compile word_conf (asm_conf:(A)asm_config)
                  (APPEND (data_to_word_stubs (:A) dc)
                     (MAP (data_to_word_compile_part dc) prog))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `col:((num spt)option)list`
    (X_CHOOSE_THEN `progs:(num#num#(A)wl_prog)list` SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[MAP_APPEND; MAP_FST_MAP_compile_part; D2WPAUX_MAP_FST_stubs];
    MATCH_MP_TAC D2WPAUX_labels_transfer THEN
    EXISTS_TAC `APPEND (data_to_word_stubs (:A) dc)
                  (MAP (data_to_word_compile_part dc) prog):(num#num#(A)wl_prog)list` THEN
    ASM_REWRITE_TAC[ALL_APPEND; stub_labels; D2WPAUX_parts_labels]]);;

(* HOL4 line 2271 (local) *)
let StoreEach_no_inst = prove
 (`!(ac:(A)asm_config) a ls (off:A word). every_inst (inst_ok_less ac) (StoreEach a ls off)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[StoreEach_def; every_inst_def]);;

(* HOL4 line 2278 (local) *)
let MemEqList_no_inst = prove
 (`!(ac:(A)asm_config) a x. every_inst (inst_ok_less ac) (MemEqList a x)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MemEqList_def; every_inst_def]);;

(* HOL4 line 2285 (local) *)
let StoreAnyConsts_no_inst = prove
 (`!(ac:(A)asm_config) r1 r2 r3 ws w.
     every_inst (inst_ok_less ac) (StoreAnyConsts r1 r2 r3 ws w)`,
  GEN_TAC THEN d2wpaux_sac_tac [every_inst_def; data_to_word_list_Seq_def]);;

(* HOL4 line 2294: fun cases_on_op (a tactic) *)

(* adjust_var n is not one of the odd scratch variables *)
let D2WPAUX_adjust_var_NEQ_sym = ONCE_REWRITE_RULE[EQ_SYM_EQ] adjust_var_NEQ;;

(* case splits on the floating-point operations of the goal *)
let d2wpaux_fp_cases_tac : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> try mem (fst(dest_type(type_of v)))
                                    ["fp_cmp";"fp_uop";"fp_bop";"fp_top"]
                            with Failure _ -> false) (frees w) in
  MAP_EVERY (fun v -> CASES_ON v) vs g;;

(* HOL4 line 2298 (local) *)
let assign_no_inst = prove
 (`!(ac:(A)asm_config) a b c d e f g.
     ((data_to_word_config_has_longdiv a ==> (asm_config_ISA ac = x86_64)) /\
      (data_to_word_config_has_div a ==> (asm_config_ISA ac IN {ARMv8, MIPS, RISC_V})) /\
      (data_to_word_config_has_fp_ops a ==> 1 < asm_config_fp_reg_count ac) /\
      (data_to_word_config_has_fp_tern a ==>
       2 < asm_config_fp_reg_count ac /\ asm_config_ISA ac = ARMv7) /\
      asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
      asm_offset_ok 0 (asm_config_byte_offset ac) (word 0)) ==>
     every_inst (inst_ok_less ac) (FST (data_to_word_assign a b c d e f g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN
  CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; arg3_def; arg4_def] THEN
  REWRITE_TAC D2WPAUX_assign_unfold_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "every_inst"; "data_to_word_list_Seq"]
    ([FST; every_inst_def; data_to_word_list_Seq_def; SetBool_def; StoreEach_no_inst;
      MemEqList_no_inst; StoreAnyConsts_no_inst; inst_ok_less_def; fp_reg_ok_def;
      IN_INSERT; NOT_IN_EMPTY; D2WPAUX_adjust_var_NEQ_sym; adjust_var_NEQ] @
     CONJUNCTS (distinctness "memop"))) THEN
  ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN d2wpaux_fp_cases_tac THEN
  ASM_REWRITE_TAC[inst_ok_less_def; fp_cmp_inst_def; fp_uop_inst_def; fp_bop_inst_def;
                  fp_top_inst_def; fp_reg_ok_def; ARITH_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[distinctness "architecture"; ARITH_RULE `1 < n ==> 0 < n`;
                ARITH_RULE `2 < n ==> 1 < n /\ 0 < n`]);;

(* HOL4 line 2325 *)
let comp_no_inst = prove
 (`!(ac:(A)asm_config) c n m p.
     ((data_to_word_config_has_longdiv c ==> (asm_config_ISA ac = x86_64)) /\
      (data_to_word_config_has_div c ==> (asm_config_ISA ac IN {ARMv8, MIPS, RISC_V})) /\
      (data_to_word_config_has_fp_ops c ==> 1 < asm_config_fp_reg_count ac) /\
      (data_to_word_config_has_fp_tern c ==>
       2 < asm_config_fp_reg_count ac /\ asm_config_ISA ac = ARMv7)) /\
     asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
     asm_offset_ok 0 (asm_config_byte_offset ac) (word 0) ==>
     every_inst (inst_ok_less ac) (FST (data_to_word_comp c n m p))`,
  GEN_TAC THEN d2wpaux_comp_ind_tac THEN STRIP_TAC THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "every_inst"; "data_to_word_list_Seq"]
    [FST; every_inst_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF; SilentFFI_def;
     GiveUp_def]) THEN
  ASM_MESON_TAC[FST; assign_no_inst]);;

(* HOL4 line 2343 (local) *)
let bounds_lem = prove
 (`!w:A word.
     (dimindex(:A) = 32 \/ dimindex(:A) = 64) /\
     (w = word_neg (word 3) \/ w = word_neg (word 2) \/ w = word_neg (word 1) \/
      w = word 0 \/ w = word 1 \/ w = word 2 \/ w = word 3 \/ w = word 4 \/
      w = word 5 \/ w = word 6 \/ w = word 7) ==>
     word_ile (word_neg (word 8)) w /\ word_ile w (word 8)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `!i:int. abs i <= &8 ==> ival(iword i:A word) = i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    SUBGOAL_THEN `&16:int <= &2 pow (dimindex (:A) - 1)` MP_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV;
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_NEG] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[WORD_ILE] THEN
  FIRST_ASSUM(fun th ->
    let inst k = MP (SPEC k th) (EQT_ELIM (INT_REDUCE_CONV (mk_comb(mk_comb(`(<=):int->int->bool`,
                   mk_comb(`abs:int->int`,k)),`&8:int`)))) in
    REWRITE_TAC(map inst [`--(&8):int`; `--(&3):int`; `--(&2):int`; `--(&1):int`; `&0:int`;
                          `&1:int`; `&2:int`; `&3:int`; `&4:int`; `&5:int`; `&6:int`;
                          `&7:int`; `&8:int`])) THEN
  CONV_TAC INT_REDUCE_CONV);;

(* the compset of every_inst (inst_ok_less ac) on concrete programs *)
let D2WPAUX_inst_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`,2,WORDP3AUX_EQ_CONV) cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  Compute.add_thms
    [every_inst_def; inst_ok_less_def; IN_INSERT; EQF_INTRO (SPEC_ALL NOT_IN_EMPTY);
     LET_END_DEF; case_def "option"; case_def "prod"] cs;
  cs;;

(* every_inst (inst_ok_less ac) of a concrete program by computation *)
let d2wpaux_ei_conv : conv = fun tm ->
  let h = fst(strip_comb tm) in
  if is_const h && fst(dest_const h) = "every_inst" then
    Compute.WEAK_CBV_CONV D2WPAUX_inst_cs tm
  else failwith "d2wpaux_ei_conv";;

(* the stubs satisfy inst_ok_less (HOL4 the stubs part of                    *)
(* compile_conventions): the residual conditions are the byte offsets -3..7 *)
(* (bounds_lem) and the LongDiv of the LongDiv stub                          *)
let D2WPAUX_stubs_no_inst = prove
 (`!dc (ac:(A)asm_config).
     good_dimindex (:A) /\
     (data_to_word_config_has_longdiv dc ==> asm_config_ISA ac = x86_64) /\
     (!w. word_ile (word_neg (word 8)) w /\ word_ile w (word 8) ==>
          asm_offset_ok 0 (asm_config_byte_offset ac) w) ==>
     ALL (\(n,m,p). every_inst (inst_ok_less ac) p) (data_to_word_stubs (:A) dc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w:A word. (w = word_neg (word 3) \/ w = word_neg (word 2) \/ w = word_neg (word 1) \/
                w = word 0 \/ w = word 1 \/ w = word 2 \/ w = word 3 \/ w = word 4 \/
                w = word 5 \/ w = word 6 \/ w = word 7) ==>
               asm_offset_ok 0 (asm_config_byte_offset ac) w` (LABEL_TAC "bo") THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC bounds_lem THEN
    ASM_REWRITE_TAC[GSYM good_dimindex_def];
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_stubs_def; ALL_APPEND] THEN CONJ_TAC THENL
   [REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC D2WPAUX_stub_code_defs THEN
    CONV_TAC(d2wpaux_PUSH_CONV ["every_inst"; "data_to_word_list_Seq"]
      ([every_inst_def; data_to_word_list_Seq_def; inst_ok_less_def; IN_INSERT; NOT_IN_EMPTY] @
       CONJUNCTS (distinctness "memop"))) THEN
    REPEAT CONJ_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    ((USE_THEN "bo" MATCH_MP_TAC THEN REWRITE_TAC[] THEN NO_TAC) ORELSE ASM_MESON_TAC[]);
    CONV_TAC(REWRITE_CONV[generated_bignum_stubs_eq; ALL] THENC
             TOP_DEPTH_CONV GEN_BETA_CONV THENC ONCE_DEPTH_CONV d2wpaux_ei_conv) THEN
    REWRITE_TAC[]]);;

(* the compiled data programs satisfy inst_ok_less (comp_no_inst) *)
let D2WPAUX_parts_no_inst = prove
 (`!dc (ac:(A)asm_config) prog.
     ((data_to_word_config_has_longdiv dc ==> (asm_config_ISA ac = x86_64)) /\
      (data_to_word_config_has_div dc ==> (asm_config_ISA ac IN {ARMv8, MIPS, RISC_V})) /\
      (data_to_word_config_has_fp_ops dc ==> 1 < asm_config_fp_reg_count ac) /\
      (data_to_word_config_has_fp_tern dc ==>
       2 < asm_config_fp_reg_count ac /\ asm_config_ISA ac = ARMv7)) /\
     asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
     asm_offset_ok 0 (asm_config_byte_offset ac) (word 0) ==>
     ALL (\(n,m,p). every_inst (inst_ok_less ac) p)
       (MAP (data_to_word_compile_part dc) prog:(num#num#(A)wl_prog)list)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC comp_no_inst THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2368 *)
let data_to_word_compile_conventions = prove
 (CASE_TERM
  `!data_conf wc (ac:(A)asm_config) prog.
     good_dimindex(:A) ==>
     let (c,p) = data_to_word_compile data_conf wc ac prog in
     ALL (\(n,m,prog).
            flat_exp_conventions (prog:(A)wl_prog) /\
            post_alloc_conventions
              (asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs ac))) prog /\
            ((data_to_word_config_has_longdiv data_conf ==> (asm_config_ISA ac = x86_64)) /\
             (data_to_word_config_has_div data_conf ==>
              (asm_config_ISA ac IN {ARMv8, MIPS, RISC_V})) /\
             asm_offset_ok 0 (asm_config_addr_offset ac) (word 0) /\
             asm_offset_ok 0 (asm_config_hw_offset ac) (word 0) /\
             (!w. word_ile (word_neg (word 8)) w /\ word_ile w (word 8) ==>
                  asm_offset_ok 0 (asm_config_byte_offset ac) w) ==>
             full_inst_ok_less ac prog) /\
            (asm_config_two_reg_arith ac ==> every_inst two_reg_inst prog) /\
            (no_share_inst prog \/ ~(asm_config_ISA ac = Ag32))) p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[data_to_word_compile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `dc = data_to_word_config_has_fp_ops_fupd
      (combin_K (1 < asm_config_fp_reg_count (ac:(A)asm_config)))
      (data_to_word_config_has_fp_tern_fupd
         (combin_K (asm_config_ISA ac = ARMv7 /\ 2 < asm_config_fp_reg_count ac)) data_conf)` THEN
  MP_TAC(SPEC `wc:word_to_word_config`
    (MATCH_MP (GEN_ALL (SPEC_ALL compile_to_word_conventions))
       (ISPECL [`dc:data_to_word_config`; `dc:data_to_word_config`;
                `prog:(num#num#data_prog)list`; `ac:(A)asm_config`]
               D2WPAUX_input_no_share_inst_or))) THEN
  MP_TAC(ISPEC `word_to_word_compile wc (ac:(A)asm_config)
                  (APPEND (data_to_word_stubs (:A) dc) (MAP (data_to_word_compile_part dc) prog))`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `col:((num spt)option)list`
    (X_CHOOSE_THEN `progs:(num#num#(A)wl_prog)list` SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  (SUBGOAL_THEN `asm_offset_ok 0 (asm_config_byte_offset (ac:(A)asm_config)) (word 0)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC bounds_lem THEN
    ASM_REWRITE_TAC[GSYM good_dimindex_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL_APPEND] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && fst(dest_var(rhs(concl th))) = "dc")) THEN
  REWRITE_TAC[stubs_with_has_fp_ops; stubs_with_has_fp_tern] THEN CONJ_TAC THENL
   [MATCH_MP_TAC D2WPAUX_stubs_no_inst THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC D2WPAUX_parts_no_inst THEN
    ASM_REWRITE_TAC[(record_info "data_to_word_config").ri_accfupds; K_THM] THEN
    MESON_TAC[]]));;

(* HOL4 line 2438 *)
let data_to_word_names = prove
 (`!c1 c2 (c:backend_config) c3 prog col (p:(num#num#(A)wl_prog)list).
     word_to_word_compile c1 c2
       (APPEND (data_to_word_stubs (:A) (backend_config_data_conf c))
          (MAP (data_to_word_compile_part c3) prog)) = (col,p) ==>
     MAP FST p =
       APPEND (MAP FST (data_to_word_stubs (:A) (backend_config_data_conf c))) (MAP FST prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `c1:word_to_word_config`
    (MATCH_MP (GEN_ALL (SPEC_ALL compile_to_word_conventions))
       (ISPECL [`backend_config_data_conf c`; `c3:data_to_word_config`;
                `prog:(num#num#data_prog)list`; `c2:(A)asm_config`]
               D2WPAUX_input_no_share_inst_or))) THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN
  SIMP_TAC[MAP_APPEND; MAP_FST_MAP_compile_part]);;

(* HOL4 line 2456 *)
let ALL_DISTINCT_MAP_FST_stubs = prove
 (`!(a:A->bool) c. ALL_DISTINCT (MAP FST (data_to_word_stubs a c))`,
  REWRITE_TAC[D2WPAUX_MAP_FST_stubs; ALL_DISTINCT; MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 2462 *)
let MAP_FST_stubs_bound = prove
 (`!n (a:A->bool) c. MEM n (MAP FST (data_to_word_stubs a c)) ==> n < data_num_stubs`,
  REWRITE_TAC[D2WPAUX_MAP_FST_stubs; MEM] THEN
  REWRITE_TAC[data_num_stubs_def; stack_num_stubs_def; word_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 2469 *)
let max_heap_limit_has_fp_ops = prove
 (`!conf b.
     max_heap_limit (:A) (data_to_word_config_has_fp_ops_fupd (combin_K b) conf) =
     max_heap_limit (:A) conf`,
  REWRITE_TAC[max_heap_limit_def; shift_length_def;
              (record_info "data_to_word_config").ri_accfupds; K_THM]);;

let _ = cake_add_simps [max_heap_limit_has_fp_ops];;

(* HOL4 line 2476 *)
let data_to_wordProof_FST_compile_part = prove
 (`!a b. FST (data_to_word_compile_part a b:num#num#(A)wl_prog) = FST b`,
  REWRITE_TAC[FORALL_PAIR_THM; data_to_word_compile_part_def; FST]);;

let _ = cake_add_simps [data_to_wordProof_FST_compile_part];;

(* HOL4 lines 2482-2483: Overload data_get_code_labels, data_good_code_labels *)
(* (dataProps names, see the header)                                          *)

(* HOL4 line 2485 (local) *)
let word_get_code_labels_StoreEach = prove
 (`!v ls (off:A word). wordConvs_get_code_labels (StoreEach v ls off) = {}`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[StoreEach_def; wordConvs_get_code_labels_def; UNION_EMPTY]);;

(* HOL4 line 2492 (local) *)
let word_get_code_labels_MemEqList = prove
 (`!x (b:A word). wordConvs_get_code_labels (MemEqList b x) = {}`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MemEqList_def; wordConvs_get_code_labels_def; UNION_EMPTY]);;

(* HOL4 line 2499 (local) *)
let part_to_words_isWord = prove
 (`!h c m i (w:bool#A word_loc) ws.
     part_to_words c m h i = SOME (w,ws) /\
     (!n v. lookup n m = SOME v ==> isWord (SND v)) ==>
     ALL isWord (MAP SND ws) /\ isWord (SND w)`,
  REPEAT GEN_TAC THEN CASES_ON `h:const_part` THEN REWRITE_TAC[part_to_words_def] THEN
  STRIP_TAC THEN GVS(all_case_eqs()) THEN
  ASM_REWRITE_TAC[ALL; MAP; ALL_MAP; o_DEF; isWord_def; make_ptr_def] THEN
  TRY(MATCH_ACCEPT_TAC ALL_T) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_mem_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[isWord_def] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2516 (local) *)
let parts_to_words_isWord = prove
 (`!ps c (w:bool#A word_loc) ws m n i.
     parts_to_words c m n ps i = SOME (w,ws) /\
     (!n v. lookup n m = SOME v ==> isWord (SND v)) ==>
     ALL isWord (MAP SND ws) /\ isWord (SND w)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[parts_to_words_def] THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_var (rhs (concl th))))) THEN
    REWRITE_TAC[MAP; ALL; lookup_mem_def] THEN TOP_CASE_TAC THEN REWRITE_TAC[isWord_def] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS[case_eq "option"; case_eq "prod"] THEN
  MP_TAC(ISPECL [`h:const_part`; `c:data_to_word_config`; `m:(bool#A word_loc)spt`; `i:A word`;
                 `x:bool#A word_loc`; `y:(bool#A word_loc)list`] part_to_words_isWord) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:data_to_word_config`; `w:bool#A word_loc`;
    `y':(bool#A word_loc)list`; `insert n (x:bool#A word_loc) m`; `n + 1`;
    `word_add i (word_mul bytes_in_word (word (LENGTH (y:(bool#A word_loc)list)))):A word`]) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[];
    SIMP_TAC[MAP_APPEND; ALL_APPEND]]);;

(* HOL4 line 2531 *)
let const_parts_to_words_isWord = prove
 (`!c ps (w:bool#A word_loc) ws.
     const_parts_to_words c ps = SOME (w,ws) ==>
     ALL isWord (MAP SND ws) /\ isWord (SND w)`,
  REWRITE_TAC[const_parts_to_words_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:const_part list`; `c:data_to_word_config`; `w:bool#A word_loc`;
                 `ws:(bool#A word_loc)list`; `LN:(bool#A word_loc)spt`; `0`; `word 0:A word`]
         parts_to_words_isWord) THEN
  ASM_REWRITE_TAC[lookup_def; option_DISTINCT] THEN SIMP_TAC[]);;

(* StoreAnyConsts of words has no code labels *)
let D2WPAUX_get_code_labels_StoreAnyConsts = prove
 (`!r1 r2 r3 ws (w:bool#A word_loc).
     ALL isWord (MAP SND ws) /\ isWord (SND w) ==>
     wordConvs_get_code_labels (StoreAnyConsts r1 r2 r3 ws w) = {}`,
  MATCH_MP_TAC StoreAnyConsts_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[StoreAnyConsts_def] THEN
    MP_TAC(ISPEC `SND (v:bool#A word_loc)` (cases "word_loc")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[isWord_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[MAP; ALL] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[StoreAnyConsts_def] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `a:A word` o REWRITE_RULE[isWord_exists] o
    check (fun th -> concl th = `isWord (SND (v:bool#A word_loc))`)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `getWords (CONS (v:bool#A word_loc) vs) []` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(bool#A word)list` (X_CHOOSE_THEN `rest:(bool#A word_loc)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A word`; `cs:(bool#A word)list`;
    `rest:(bool#A word_loc)list`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "getWords" with Failure _ -> false))
          (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL isWord (MAP SND (CONS (v:bool#A word_loc) vs))` MP_TAC THENL
   [ASM_REWRITE_TAC[MAP; ALL; isWord_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP getWords_thm o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "getWords"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[MAP_APPEND; ALL_APPEND] THEN SIMP_TAC[]);;

(* HOL4 line 2542 (local) *)
let word_get_code_labels_StoreAnyConsts = prove
 (`!c ps (w:bool#A word_loc) ws r1 r2 r3.
     const_parts_to_words c ps = SOME (w,ws) ==>
     wordConvs_get_code_labels (StoreAnyConsts r1 r2 r3 ws w) = {}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP const_parts_to_words_isWord) THEN
  REWRITE_TAC[D2WPAUX_get_code_labels_StoreAnyConsts]);;

(* HOL4 line 2561 (local) *)
let getWords_good_loc = prove
 (`!xs ys (ws:(bool#A word)list) vs1 s.
     getWords xs ys = (ws,vs1) /\ ALL (good_loc s o SND) xs ==> ALL (good_loc s o SND) vs1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[getWords_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `vs1:(bool#A word_loc)list`)) THEN
    REWRITE_TAC[ALL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:bool#A word_loc` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `x:A word_loc` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `x:A word_loc` (cases "word_loc")) THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[ALL; o_THM] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (b:bool,a:A word) ys`; `ws:(bool#A word)list`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `vs1:(bool#A word_loc)list`)) THEN
    ASM_REWRITE_TAC[ALL; o_THM]]);;

(* HOL4 line 2572 *)
let const_parts_to_words_labels = prove
 (`!c bs (q:bool#A word_loc) r w.
     const_parts_to_words c bs = SOME (q,r) ==>
     wordConvs_get_code_labels (StoreAnyConsts (adjust_var w) 1 3 r q) SUBSET
     assign_get_code_label (BlockOp (Build bs))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    REWRITE_TAC[MATCH_MP word_get_code_labels_StoreAnyConsts th; EMPTY_SUBSET]));;

(* the code labels of the code of assign *)
let D2WPAUX_code_labels_assign = prove
 (`!x c secn v w y z.
     wordConvs_get_code_labels (FST (data_to_word_assign c secn v w x y z):(A)wl_prog) SUBSET
     assign_get_code_label x UNION set_of_list (MAP FST (data_to_word_stubs (:A) c))`,
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN
  CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[assign_get_code_label_def; D2WPAUX_MAP_FST_stubs; set_of_list] THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; arg3_def; arg4_def] THEN
  REWRITE_TAC D2WPAUX_assign_unfold_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "wordConvs_get_code_labels"; "data_to_word_list_Seq";
                              "SUBSET"; "UNION"; "INSERT"]
    ([FST; wordConvs_get_code_labels_def; data_to_word_list_Seq_def; SetBool_def;
      word_get_code_labels_StoreEach; word_get_code_labels_MemEqList; UNION_EMPTY;
      EMPTY_SUBSET; UNION_SUBSET; INSERT_SUBSET; IN_UNION; IN_INSERT; NOT_IN_EMPTY] @
     D2WAUX_location_defs)) THEN
  REPEAT TOP_CASE_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP word_get_code_labels_StoreAnyConsts th;
                                      EMPTY_SUBSET]));;

(* HOL4 line 2581 (local) *)
let word_get_code_labels_assign = prove
 (`!x c secn v w y z (res1:(A)wl_prog) res2.
     data_to_word_assign c secn v w x y z = (res1,res2) ==>
     wordConvs_get_code_labels res1 SUBSET
     assign_get_code_label x UNION set_of_list (MAP FST (data_to_word_stubs (:A) c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:clos_op`; `c:data_to_word_config`; `secn:num`; `v:num`; `w:num`;
                `y:num list`; `z:num_set option`] D2WPAUX_code_labels_assign) THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 line 2607 (local) *)
let data_to_word_comp_code_labels = prove
 (`!c secn l p.
     wordConvs_get_code_labels ((FST (data_to_word_comp c secn l p)):(A)wl_prog) SUBSET
     data_get_code_labels p UNION set_of_list (MAP FST (data_to_word_stubs (:A) c))`,
  d2wpaux_comp_ind_tac THEN REWRITE_TAC[data_get_code_labels_def] THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "wordConvs_get_code_labels"; "data_to_word_list_Seq"]
    [FST; wordConvs_get_code_labels_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF;
     SilentFFI_def; GiveUp_def; UNION_EMPTY; EMPTY_SUBSET]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_UNION]) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[FST; REWRITE_RULE[SUBSET; IN_UNION] D2WPAUX_code_labels_assign]);;

(* HOL4 line 2636 (local) *)
let word_good_handlers_StoreEach = prove
 (`!secn v ls (off:A word). good_handlers secn (StoreEach v ls off)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[StoreEach_def; good_handlers_def]);;

(* HOL4 line 2643 (local) *)
let word_good_handlers_MemEqList = prove
 (`!secn x (b:A word). good_handlers secn (MemEqList b x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MemEqList_def; good_handlers_def]);;

(* HOL4 line 2650 (local) *)
let word_good_handlers_StoreAnyConsts = prove
 (`!secn r1 r2 r3 ws (w:bool#A word_loc).
     good_handlers secn (StoreAnyConsts r1 r2 r3 ws w)`,
  GEN_TAC THEN d2wpaux_sac_tac [good_handlers_def; data_to_word_list_Seq_def]);;

(* the handlers of the code of assign *)
let D2WPAUX_good_handlers_assign = prove
 (`!x c secn v w y z. good_handlers secn (FST (data_to_word_assign c secn v w x y z):(A)wl_prog)`,
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN
  CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; arg3_def; arg4_def] THEN
  REWRITE_TAC D2WPAUX_assign_unfold_defs THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "good_handlers"; "data_to_word_list_Seq"]
    [FST; good_handlers_def; data_to_word_list_Seq_def; SetBool_def; word_good_handlers_StoreEach;
     word_good_handlers_MemEqList; word_good_handlers_StoreAnyConsts]));;

(* HOL4 line 2659 (local) *)
let word_good_handlers_assign = prove
 (`!x c secn v w y z (res1:(A)wl_prog) res2.
     data_to_word_assign c secn v w x y z = (res1,res2) ==> good_handlers secn res1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:clos_op`; `c:data_to_word_config`; `secn:num`; `v:num`; `w:num`;
                `y:num list`; `z:num_set option`] D2WPAUX_good_handlers_assign) THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 line 2678 (local) *)
let data_to_word_comp_good_handlers = prove
 (`!c secn l p. good_handlers secn ((FST (data_to_word_comp c secn l p)):(A)wl_prog)`,
  d2wpaux_comp_ind_tac THEN
  CONV_TAC(d2wpaux_PUSH_CONV ["FST"; "good_handlers"; "data_to_word_list_Seq"]
    [FST; good_handlers_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF; SilentFFI_def;
     GiveUp_def; D2WPAUX_good_handlers_assign]) THEN
  ASM_MESON_TAC[FST]);;

(* the union of the sets of a list is a subset *)
let D2WPAUX_UNIONS_MAP_SUBSET = prove
 (`!(f:A->B->bool) l s.
     UNIONS (set_of_list (MAP f l)) SUBSET s <=> ALL (\x. f x SUBSET s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; EMPTY_SUBSET; ALL;
                  UNION_SUBSET]);;

(* the compset of the code labels and handlers of concrete programs *)
let D2WPAUX_code_labels_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`,2,WORDP3AUX_EQ_CONV) cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  Compute.add_thms
    [wordConvs_get_code_labels_def; good_handlers_def; LET_END_DEF; case_def "option";
     case_def "prod"; UNION_EMPTY] cs;
  cs;;

(* code labels and handlers of a concrete program by computation *)
let d2wpaux_gcl_conv : conv = fun tm ->
  let h = fst(strip_comb tm) in
  if is_const h && mem (fst(dest_const h)) ["wordConvs_get_code_labels"; "good_handlers"] then
    Compute.WEAK_CBV_CONV D2WPAUX_code_labels_cs tm
  else failwith "d2wpaux_gcl_conv";;

(* HOL4 line 2703 (local) *)
let stubs_labels = prove
 (`!dc. UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp)
                              (data_to_word_stubs (:A) dc))) SUBSET
        set_of_list (MAP FST (data_to_word_stubs (:A) dc))`,
  GEN_TAC THEN REWRITE_TAC[D2WPAUX_MAP_FST_stubs; D2WPAUX_UNIONS_MAP_SUBSET] THEN
  REWRITE_TAC[data_to_word_stubs_def; ALL_APPEND] THEN CONJ_TAC THENL
   [REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC D2WPAUX_stub_code_defs THEN
    CONV_TAC(d2wpaux_PUSH_CONV ["wordConvs_get_code_labels"; "data_to_word_list_Seq";
                                "SUBSET"; "UNION"; "INSERT"]
      ([wordConvs_get_code_labels_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF;
        UNION_EMPTY; EMPTY_SUBSET; UNION_SUBSET; INSERT_SUBSET; IN_UNION; IN_INSERT;
        NOT_IN_EMPTY; set_of_list] @ D2WAUX_location_defs));
    REWRITE_TAC[generated_bignum_stubs_eq; ALL] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV d2wpaux_gcl_conv) THEN
    REWRITE_TAC(set_of_list :: UNION_SUBSET :: INSERT_SUBSET :: EMPTY_SUBSET :: IN_INSERT ::
                NOT_IN_EMPTY :: D2WAUX_location_defs) THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* the handlers of the stubs *)
let D2WPAUX_stubs_good_handlers = prove
 (`!dc. ALL (\(n,m,pp). good_handlers n pp) (data_to_word_stubs (:A) dc)`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_stubs_def; ALL_APPEND] THEN CONJ_TAC THENL
   [REWRITE_TAC[ALL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC D2WPAUX_stub_code_defs THEN
    CONV_TAC(d2wpaux_PUSH_CONV ["good_handlers"; "data_to_word_list_Seq"]
      [good_handlers_def; data_to_word_list_Seq_def; LET_DEF; LET_END_DEF]);
    REWRITE_TAC[generated_bignum_stubs_eq; ALL] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV d2wpaux_gcl_conv) THEN REWRITE_TAC[]]);;

(* the handlers of the compiled parts *)
let D2WPAUX_parts_good_handlers = prove
 (`!dc progs.
     ALL (\(n,m,pp). good_handlers n pp)
       (MAP (data_to_word_compile_part dc) progs:(num#num#(A)wl_prog)list)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM;
                                  data_to_word_compile_part_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[data_to_word_comp_good_handlers]);;

(* HOL4 line 2712 *)
let data_to_word_good_code_labels = prove
 (`!data_conf word_conf asm_conf prog xx (prog':(num#num#(A)wl_prog)list) elabs.
     (data_to_word_compile data_conf word_conf asm_conf prog) = (xx,prog') /\
     data_good_code_labels prog elabs ==>
     wordConvs_good_code_labels prog' elabs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_compile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SPEC_TAC(`data_to_word_config_has_fp_ops_fupd (combin_K (1 < asm_config_fp_reg_count
              (asm_conf:(A)asm_config)))
             (data_to_word_config_has_fp_tern_fupd
                (combin_K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
                data_conf)`, `dc:data_to_word_config`) THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o AP_TERM `SND:(((num spt)option)list #
     (num#num#(A)wl_prog)list) -> (num#num#(A)wl_prog)list`) THEN
  REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC word_good_code_labels_word_to_word THEN
  REWRITE_TAC[wordConvs_good_code_labels_def; ALL_APPEND; D2WPAUX_stubs_good_handlers;
              D2WPAUX_parts_good_handlers] THEN
  REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; D2WPAUX_UNIONS_MAP_SUBSET; ALL_APPEND;
              MAP_FST_MAP_compile_part] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `dc:data_to_word_config` (INST_TYPE [`:A`,`:A`] stubs_labels)) THEN
    REWRITE_TAC[D2WPAUX_UNIONS_MAP_SUBSET] THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `data_good_code_labels prog elabs` THEN
  REWRITE_TAC[data_good_code_labels_def; D2WPAUX_UNIONS_MAP_SUBSET; ALL_MAP] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`dc:data_to_word_config`; `p1:num`; `2`; `p2:data_prog`]
         (INST_TYPE [`:A`,`:A`] data_to_word_comp_code_labels)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p1:num`; `p1':num`; `p2:data_prog`]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION] THEN MESON_TAC[]);;

(* HOL4 line 2750: val th = EVAL MAP FST (stubs (:'a) c) *)

(* HOL4 line 2753 (the list of the locations of the stubs, as EVAL gives it; *)
(* computed by rewriting with data_to_word_stubs_def, the location           *)
(* definitions, word_num_stubs_def, stack_num_stubs_def,                     *)
(* generated_bignum_stubs_eq, MAP, APPEND, FST and NUM_REDUCE_CONV)          *)
let stubs_fst_def = new_definition
  `stubs_fst =
     [7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 29; 30; 31; 33;
      34; 35; 36; 37; 38; 24; 25; 26; 27; 28; 32; 39; 61; 60; 59; 58; 54; 57; 56; 55;
      53; 52; 51; 50; 49; 47; 48; 46; 45; 44; 43; 42; 41; 40]`;;

(* HOL4 line 2757 (HOL4: th |> REWRITE_RULE [GSYM stubs_fst_def]) *)
let stubs_fst_eq = prove
 (`!c. MAP FST (data_to_word_stubs (:A) c) = stubs_fst`,
  REWRITE_TAC[D2WPAUX_MAP_FST_stubs; stubs_fst_def]);;

(* HOL4 line 2764 *)
let data_to_word_good_code_labels_incr = prove
 (`!elabs progs dc.
     set_of_list stubs_fst SUBSET elabs /\
     data_good_code_labels progs elabs ==>
     wordConvs_good_code_labels (MAP (data_to_word_compile_part dc) progs:
                                   (num#num#(A)wl_prog)list) elabs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wordConvs_good_code_labels_def; data_good_code_labels_def;
              D2WPAUX_parts_good_handlers; D2WPAUX_UNIONS_MAP_SUBSET;
              MAP_FST_MAP_compile_part; ALL_MAP] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`dc:data_to_word_config`; `p1:num`; `2`; `p2:data_prog`]
         (INST_TYPE [`:A`,`:A`] data_to_word_comp_code_labels)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p1:num`; `p1':num`; `p2:data_prog`]) THEN
  ASM_REWRITE_TAC[stubs_fst_eq] THEN
  UNDISCH_TAC `set_of_list stubs_fst SUBSET elabs` THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN MESON_TAC[]);;

(* HOL4 line 2785 *)
let data_to_word_good_handlers = prove
 (`!data_conf word_conf asm_conf prog xx (prog':(num#num#(A)wl_prog)list).
     (data_to_word_compile data_conf word_conf asm_conf prog) = (xx,prog') ==>
     ALL (\(n,m,pp). good_handlers n pp) prog'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_compile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(MP_TAC o AP_TERM `SND:(((num spt)option)list #
     (num#num#(A)wl_prog)list) -> (num#num#(A)wl_prog)list`) THEN
  REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC word_good_handlers_word_to_word THEN
  REWRITE_TAC[ALL_APPEND; D2WPAUX_stubs_good_handlers; D2WPAUX_parts_good_handlers]);;

(* HOL4 line 2806 *)
let data_to_word_good_handlers_incr = prove
 (`!dc progs.
     ALL (\(n,m,pp). good_handlers n pp)
       (MAP (data_to_word_compile_part dc) progs:(num#num#(A)wl_prog)list)`,
  REWRITE_TAC[D2WPAUX_parts_good_handlers]);;
