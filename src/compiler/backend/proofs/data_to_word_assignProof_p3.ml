(* ========================================================================= *)
(* data_to_word_assignProof_p3: part 3 of 6 (HOL4 lines 5411-8193) of the    *)
(* port of HOL4 compiler/backend/proofs/data_to_word_assignProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p6 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_assignProof.ml needs the last.                *)
(* ASP3AUX_ names are local helpers of this part.                           *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_assignProof_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 3: HOL4 lines 5411-8193 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (ASP3AUX_ names).                                    *)
(* ------------------------------------------------------------------------- *)

(* the brute-force splitting of the do_app lemmas below (HOL4: simp or gvs   *)
(* with do_app_def, do_app_aux_def, do_space_def, ... and AllCaseEqs ()):    *)
(* unfold do_app and its helpers, then split every case and conditional of   *)
(* the goal                                                                  *)

let ASP3AUX_DO_APP_RWS =
  [data_state_INFO.ri_accfupds; K_THM; distinctness "clos_op"; injectivity "clos_op";
   distinctness "int_op"; injectivity "int_op"; distinctness "block_op";
   injectivity "block_op"; distinctness "mem_op"; injectivity "mem_op";
   MEM; op_space_reset_def; op_space_req_def; allowed_op_def;
   distinctness "result"; injectivity "result"; PAIR_EQ];;

let ASP3AUX_DO_APP_DEFS =
  [data_do_app_def; do_space_def; consume_space_def;
   do_stack_def; do_lim_safe; data_do_app_aux_def; with_fresh_ts_def;
   check_lim_def; LET_DEF; LET_END_DEF];;

let ASP3AUX_DO_APP_SPLIT_TAC : tactic =
  REWRITE_TAC ASP3AUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS;;

(* the same, rewriting with the assumptions once the operator is reduced     *)
let ASP3AUX_DO_APP_SPLIT_ASM_TAC : tactic =
  REWRITE_TAC ASP3AUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC (NOT_CONS_NIL::LENGTH::ASP3AUX_DO_APP_RWS) THEN
  ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC (NOT_CONS_NIL::LENGTH::ASP3AUX_DO_APP_RWS) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS;;

(* symbolic evaluation of wordLang code (after data_to_word_bignumProof):   *)
(* the clauses of wl_evaluate, the definitions of the semantic helpers      *)

let ASP3AUX_evaluate_clause c =
  find (fun th -> let l = lhs (concl (SPEC_ALL th)) in
                  fst (dest_const (fst (strip_comb (fst (dest_pair (rand l)))))) = c)
       (CONJUNCTS wl_evaluate_def);;

let ASP3AUX_ev_Skip = ASP3AUX_evaluate_clause "wl_Skip";;
let ASP3AUX_ev_Seq = ASP3AUX_evaluate_clause "wl_Seq";;
let ASP3AUX_ev_Assign = ASP3AUX_evaluate_clause "wl_Assign";;
let ASP3AUX_ev_Set = ASP3AUX_evaluate_clause "wl_Set";;
let ASP3AUX_ev_Get = ASP3AUX_evaluate_clause "wl_Get";;
let ASP3AUX_ev_Inst = ASP3AUX_evaluate_clause "wl_Inst";;
let ASP3AUX_ev_Store = ASP3AUX_evaluate_clause "wl_Store";;
let ASP3AUX_ev_If = ASP3AUX_evaluate_clause "wl_If";;
let ASP3AUX_ev_Return = ASP3AUX_evaluate_clause "wl_Return";;
let ASP3AUX_ev_Call = ASP3AUX_evaluate_clause "wl_Call";;
let ASP3AUX_ev_Alloc = ASP3AUX_evaluate_clause "wl_Alloc";;

let ASP3AUX_word_cmp_Word = prove
 (`!c (a:A word) b. wl_word_cmp c (wl_Word a) (wl_Word b) = SOME (asm_word_cmp c a b)`,
  MATCH_MP_TAC cmp_INDUCT THEN REWRITE_TAC[wl_word_cmp_def; asm_word_cmp_def]);;

let ASP3AUX_EV_THMS =
  [ASP3AUX_ev_Skip; ASP3AUX_ev_Seq; ASP3AUX_ev_Assign; ASP3AUX_ev_Set;
   ASP3AUX_ev_Get; ASP3AUX_ev_Store; ASP3AUX_ev_If; ASP3AUX_ev_Return;
   ASP3AUX_ev_Inst; data_to_word_list_Seq_def; wl_word_exp_def; wl_get_var_def;
   wl_get_vars_def; wl_get_var_imm_def; ASP3AUX_word_cmp_Word; the_words_def;
   word_op_def; wl_set_var_def; wl_set_store_def; wl_get_store_def;
   wl_mem_store_def; wl_mem_load_def; lookup_insert; wl_call_env_def;
   wl_dec_clock_def; wl_flush_state_def; MAP; ITLIST; OPTION_MAP_DEF;
   WORD_ADD_0; asm_word_cmp_def];;

(* fromList2 [x0; ...; xk] as an insert chain *)
let ASP3AUX_FROMLIST2_CONV tm =
  match tm with
    Comb(Const("fromList2",_),l) when is_list l ->
      (REWR_CONV fromList2_def THENC REWRITE_CONV[FOLDL] THENC
       TOP_DEPTH_CONV GEN_BETA_CONV THENC REWRITE_CONV[SND] THENC
       NUM_REDUCE_CONV) tm
  | _ -> failwith "ASP3AUX_FROMLIST2_CONV";;

let ASP3AUX_FROMLIST2_TAC = CONV_TAC(TOP_DEPTH_CONV ASP3AUX_FROMLIST2_CONV);;

(* HOL4 qmatch_goalsub_abbrev_tac: abbreviate as v the part of the first    *)
(* subterm of the goal matching pat that v matches                          *)
let ASP3AUX_MATCH_ABBREV_TAC (pat:term) (v:term) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let (_,tmi,_) = term_match [] pat t in
  let x = rev_assoc v tmi in
  ABBREV_TAC (mk_eq(v,x)) g;;

(* HOL4 unabbrev: replace the abbreviation v (an assumption t = v) by t     *)
(* everywhere and drop it                                                    *)
let ASP3AUX_UNABBREV_TAC (v:term) : tactic =
  FIRST_X_ASSUM (fun th -> let r = rand (concl th) in
                           if r = v then SUBST_ALL_TAC (SYM th) else NO_TAC);;

(* hide an assumption from the simplifier (as I P) and get it back *)
let ASP3AUX_HIDE_TAC : thm_tactic = fun th ->
  ASSUME_TAC (EQ_MP (SYM (ISPEC (concl th) I_THM)) th);;

let ASP3AUX_UNHIDE_THEN (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> match concl th with
      Comb(Const("I",_),p) when type_of p = bool_ty -> ttac (EQ_MP (ISPEC p I_THM) th)
    | _ -> failwith "ASP3AUX_UNHIDE_THEN");;

let ASP3AUX_MAX_MAX = prove
 (`!x y. OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) y = OPTION_MAP2 MAX x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:num option` THEN CASES_ON `y:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;
let ASP3AUX_get_vars_2 = prove
 (`!args (s:A spt) x1 x2.
     data_get_vars args s = SOME [x1;x2] ==>
     ?a1 a2. args = [a1;a2] /\ data_get_var a1 s = SOME x1 /\
             data_get_var a2 s = SOME x2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH_EQ_2] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`a1:num`; `a2:num`] THEN
  UNDISCH_TAC `data_get_vars [a1; a2] (s:A spt) = SOME [x1; x2]` THEN
  REWRITE_TAC[get_vars_SOME_IFF_data] THEN SIMP_TAC[]);;
let ASP3AUX_get_vars_1 = prove
 (`!args (s:A spt) x1.
     data_get_vars args s = SOME [x1] ==>
     ?a1. args = [a1] /\ data_get_var a1 s = SOME x1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; LENGTH_EQ_NUM; ONE] THEN
  REWRITE_TAC[LENGTH_EQ_NIL] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `h:num` THEN
  UNDISCH_TAC `data_get_vars [h] (s:A spt) = SOME [x1]` THEN
  REWRITE_TAC[get_vars_SOME_IFF_data] THEN SIMP_TAC[]);;
let ASP3AUX_memory_rel_conf = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     shift_length c < dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c /\
     Globals IN FDOM st`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[]);;


let ASP3AUX_state_rel_memory_rel = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (APPEND (join_env (data_state_locals s)
          (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
        (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
          (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  CASE_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let ASP3AUX_state_rel_conf = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     good_dimindex (:A) /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     shift_length c < dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP3AUX_memory_rel_conf) THEN SIMP_TAC[]);;

let ASP3AUX_encode_header_small = prove
 (`!c tag len.
     good_dimindex (:A) /\ ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\ tag < 64 /\ len < 2 ==>
     ?h. encode_header c tag len = SOME (h:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[encode_header_def; dimword_def] THEN
  (COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THENL
   [MESON_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  (SUBGOAL_THEN `2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2) /\
                 2 EXP 1 <= 2 EXP data_to_word_config_len_size c` MP_TAC THENL
   [ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]));;

(* is tm an application of the constant named nm *)
let ASP3AUX_is_app nm tm =
  try fst (dest_const (fst (strip_comb tm))) = nm with Failure _ -> false;;
let ASP3AUX_LENGTH_EQ_1 = prove
 (`!xs:A list. (LENGTH xs = 1 <=> ?a. xs = [a]) /\ (1 = LENGTH xs <=> ?a. xs = [a])`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_CONS_NIL; CONS_11; ARITH_RULE `~(0 = 1) /\ ~(1 = 0)`;
              ARITH_RULE `(SUC n = 1 <=> n = 0) /\ (1 = SUC n <=> n = 0)`; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;
let ASP3AUX_state_rel_upd = prove
 (`!c l1 l2 (s:(C,FFI)data_state) s' (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs /\
     data_state_ffi s' = data_state_ffi s /\ data_state_clock s' = data_state_clock s /\
     data_state_handler s' = data_state_handler s /\ data_state_code s' = data_state_code s /\
     data_state_compile s' = data_state_compile s /\
     data_state_compile_oracle s' = data_state_compile_oracle s /\
     data_state_tstamps s' = data_state_tstamps s /\
     data_state_locals s' = data_state_locals s /\
     data_state_stack s' = data_state_stack s /\
     data_state_stack_frame_sizes s' = data_state_stack_frame_sizes s /\
     data_state_locals_size s' = data_state_locals_size s /\
     data_state_limits s' = data_state_limits s /\ data_state_refs s' = data_state_refs s /\
     data_state_space s' = data_state_space s /\ data_state_global s' = data_state_global s /\
     option_le (data_state_stack_max s) (data_state_stack_max s') ==>
     data_to_word_gcProof_state_rel c l1 l2 s' t v locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP5AUX_HEAD_MESON_TAC[option_le_trans]);;

let ASP3AUX_state_rel_set_var_Unit = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest data_Unit s)
       (wl_set_var (adjust_var dest) (wl_Word (word 2)) t) NONE locs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_conf) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_memory_rel) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def; wl_set_var_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  FS[lookup_insert; adjust_var_11] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
  MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[]);;
let ASP3AUX_wl_fupd_id =
  let names = map (fun (f,_,_) -> f) wl_state_INFO.ri_fields in
  let cl f = "wl_state_" ^ f ^ "_fupd (K (wl_state_" ^ f ^ " r)) r = r" in
  let tm = parse_term ("!r:(A,C,FFI)wl_state. " ^
                       String.concat " /\\ " (map cl names)) in
  prove(tm, GEN_TAC THEN REWRITE_TAC[wl_state_component_equality;
                                     wl_state_INFO.ri_accfupds; K_THM]);;

let ASP3AUX_K_o = prove
 (`!(a:C) (f:A->B). K a o f = K a`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;
let ASP3AUX_pop_env_is_env = prove
 (`!(s:(C,FFI)data_state) s1.
     data_pop_env s = SOME s1 /\ is_env (HD (data_state_stack s)) ==>
     ?n e xs. data_state_stack s = CONS (data_Env n e) xs /\
              s1 = data_state_locals_fupd (K e)
                     (data_state_stack_fupd (K xs) (data_state_locals_size_fupd (K n) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_pop_env_def; is_env_def] THEN
  CASES_ON `data_state_stack (s:(C,FFI)data_state)` THEN
  CASE_REWRITE_TAC[option_DISTINCT; HD] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[option_INJ] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[option_INJ]) THEN ASM_MESON_TAC[]);;
let ASP3AUX_encode_header_small_int = prove
 (`!c tag len.
     ~(encode_header c (4 * tag) len = (NONE:(A word)option)) ==> small_int (:A) (&(4 * tag))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def; small_int_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `--(&n) <= &m`] THEN
  MP_TAC(SPECL [`16`; `dimword(:A)`; `8`] DIV_MONO2) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
let ASP3AUX_state_rel_lookup_0 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[]);;
let ASP3AUX_cut_env_fromList3 = prove
 (`!(env:A spt) v0 v1 v2.
     lookup 0 env = SOME v0 /\ lookup 1 env = SOME v1 /\ lookup 2 env = SOME v2 ==>
     ?x. data_cut_env (fromList [one;one;one]) env = SOME x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  SUBGOAL_THEN `domain (fromList [one;one;one]) SUBSET domain (env:A spt)`
    (fun th -> REWRITE_TAC[th; option_INJ] THEN MESON_TAC[]) THEN
  REWRITE_TAC[domain_fromList; LENGTH] THEN
  REWRITE_TAC[SUBSET; count_DEF; IN_ELIM_THM; domain_lookup] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `x < 3 <=> x = 0 \/ x = 1 \/ x = 2`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;
let ASP3AUX_val_Smallnum = prove
 (`!n. small_int (:A) (&n) ==> val (Smallnum (&n):A word) = 4 * n`,
  GEN_TAC THEN REWRITE_TAC[small_int_def; data_to_word_Smallnum_def] THEN
  REWRITE_TAC[INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
              INT_OF_NUM_LT; INT_ARITH `--(&n) <= &m:int`; VAL_WORD] THEN
  DISCH_TAC THEN MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[GSYM dimword_def] THEN
  MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN ASM_ARITH_TAC);;
let ASP3AUX_state_rel_store = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     ?f cur. FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word f) /\
             FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word cur)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]);;
let ASP3AUX_state_rel_stubs = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     lookup FromList1_location (wl_state_code t) = SOME (6,FromList1_code c) /\
     lookup Append_location (wl_state_code t) = SOME (3,Append_code c) /\
     lookup AppendMainLoop_location (wl_state_code t) = SOME (6,AppendMainLoop_code c) /\
     lookup AppendLenLoop_location (wl_state_code t) = SOME (3,AppendLenLoop_code c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_to_word_gcProof_code_rel_def;
              data_to_word_stubs_def; ALL_APPEND; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let ASP3AUX_data_cut_env_lookup = prove
 (`!names (env:A spt) x k.
     data_cut_env names env = SOME x /\ k IN domain names ==> lookup k x = lookup k env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN
  ASM_REWRITE_TAC[]);;

(* the state_rel assumption whose word state is (or mentions) the variable v *)
let ASP3AUX_SR_WITH (v:term) (th:thm) =
  let tm = concl th in
  if ASP3AUX_is_app "data_to_word_gcProof_state_rel" tm &&
     free_in v (el 4 (snd (strip_comb tm))) then th
  else failwith "ASP3AUX_SR_WITH";;
let ASP3AUX_Smallnum_ushr_2 = prove
 (`!n. 4 * n < dimword (:A) ==> word_ushr (Smallnum (&n):A word) 2 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; data_to_word_Smallnum_def] THEN
  REWRITE_TAC[INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; VAL_WORD] THEN
  REWRITE_TAC[GSYM dimword_def] THEN ASM_SIMP_TAC[MOD_LT; ARITH_RULE `4 * n < d ==> n < d`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let ASP3AUX_Smallnum_ushr_4 = prove
 (`!n. 16 * n < dimword (:A) ==> word_ushr (Smallnum (&(4 * n)):A word) 4 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; data_to_word_Smallnum_def] THEN
  REWRITE_TAC[INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; VAL_WORD] THEN
  REWRITE_TAC[GSYM dimword_def; ARITH_RULE `4 * 4 * n = 16 * n`] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `16 * n < d ==> n < d`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let ASP3AUX_FromList_header = prove
 (`!c n tag.
     data_to_word_config_len_size c + 7 < dimindex (:A) ==>
     word_or (word_shl (Smallnum (&n):A word) ((dimindex (:A) - data_to_word_config_len_size c) - 2))
       (word_or (word 3) (Smallnum (&(4 * tag)))) =
     make_header c (word (4 * tag)) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[make_header_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
              WORD_SHL_WORD] THEN
  SUBGOAL_THEN `2 EXP (dimindex (:A) - data_to_word_config_len_size c) =
                2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2) * 4` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 2`); GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 2 * 4 * tag = 4 * 4 * tag`; ARITH_RULE `(a * 4) * n = a * 4 * n`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_OR_SYM]);;

(* goal ?q r. (X,Y) = (q,r) /\ P q r : choose q := X and r := Y *)
let ASP3AUX_EXISTS_PAIR_TAC : tactic = fun (asl,w) ->
  let _,b = dest_exists w in
  let _,b2 = dest_exists b in
  let body = snd (strip_exists b2) in
  let x,y = dest_pair (lhs (fst (dest_conj body))) in
  (EXISTS_TAC x THEN EXISTS_TAC y THEN REWRITE_TAC[]) (asl,w);;
let ASP3AUX_code_oracle_rel_upd = prove
 (`!k v c sc sco st (tc:C -> (num#num#(A)wl_prog)list -> (byte list#(A word)list#C)option) tco cb db.
     ~(k = CodeBuffer) /\ ~(k = CodeBufferEnd) /\ ~(k = BitmapBuffer) /\ ~(k = BitmapBufferEnd) ==>
     (code_oracle_rel c sc sco (st |+ (k,v)) tc tco cb db <=>
      code_oracle_rel c sc sco st tc tco cb db)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[code_oracle_rel_def; FLOOKUP_UPDATE] THEN
  ASM_REWRITE_TAC[]);;
let ASP3AUX_option_le_FromList_stack = prove
 (`!(a:num option) b x y l0 l1.
     option_le a b ==>
     option_le (OPTION_MAP2 MAX a (OPTION_MAP2 (+) (OPTION_MAP2 (+) x y) l1))
       (OPTION_MAP2 MAX b (OPTION_MAP2 (+) (OPTION_MAP2 MAX l0 l1) (OPTION_MAP2 (+) y x)))`,
  REPEAT GEN_TAC THEN
  CASES_ON `a:num option` THEN CASES_ON `b:num option` THEN CASES_ON `x:num option` THEN
  CASES_ON `y:num option` THEN CASES_ON `l0:num option` THEN CASES_ON `l1:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;
let ASP3AUX_small_num_eq = prove
 (`!lims i. good_dimindex (:A) /\ (limits_arch_64_bit lims <=> dimindex (:A) = 64) ==>
            (small_num (limits_arch_64_bit lims) i <=> small_int (:A) i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[small_num_def; small_int_def; dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN
  CONV_TAC INT_REDUCE_CONV);;

let ASP3AUX_state_rel_arch64 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     (limits_arch_64_bit (data_state_limits s) <=> dimindex (:A) = 64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm; limits_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let ASP3AUX_do_app_FromList_vals = prove
 (`!tag vals (s:(C,FFI)data_state) v s'.
     data_do_app (BlockOp (FromList tag)) vals s = Rval (v,s') ==>
     ?v2 ys. vals = [data_Number (&(LENGTH ys)); v2] /\ data_v_to_list v2 = SOME ys`,
  REPEAT GEN_TAC THEN ASP3AUX_DO_APP_SPLIT_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "data_v"; distinctness "data_v"]) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_EQ; LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(fun th -> if ASP3AUX_is_app "data_v_to_list" (lhs (concl th)) then
    MP_TAC th else NO_TAC) THEN
  MESON_TAC[LENGTH]);;
let ASP3AUX_state_rel_limits = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     limits_length_limit (data_state_limits s) = data_to_word_config_len_size c /\
     arch_size (data_state_limits s) = dimindex (:A) /\
     (limits_arch_64_bit (data_state_limits s) <=> dimindex (:A) = 64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm; limits_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[arch_size_def] THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP3AUX_ev_MustTerminate = ASP3AUX_evaluate_clause "MustTerminate";;
let ASP3AUX_SPT_CONV =
  REWRITE_CONV[fromList_def; FOLDL] THENC TOP_DEPTH_CONV GEN_BETA_CONV THENC
  REWRITE_CONV[SND] THENC NUM_REDUCE_CONV THENC
  REPEATC (CHANGED_CONV (ONCE_REWRITE_CONV[insert_def] THENC NUM_REDUCE_CONV THENC
            REWRITE_CONV[ARITH_EQ; ARITH_EVEN]));;
let ASP3AUX_do_app_FromList_same_v = prove
 (`!tag ys v2 (s:(C,FFI)data_state) (s':(C,FFI)data_state) v r.
     data_v_to_list v2 = SOME ys /\
     data_do_app (BlockOp (FromList tag)) [data_Number (&(LENGTH ys)); v2] s = Rval (v,r) /\
     data_state_tstamps s' = data_state_tstamps s ==>
     ?r'. data_do_app (BlockOp (FromList tag)) [data_Number (&(LENGTH ys)); v2] s' = Rval (v,r')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  CASES_ON `ys:data_v list` THEN
  REWRITE_TAC ASP3AUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC (NOT_CONS_NIL::LENGTH::ASP3AUX_DO_APP_RWS) THEN
  ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC (NOT_CONS_NIL::LENGTH::ASP3AUX_DO_APP_RWS) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS THEN
  CASES_ON `data_state_tstamps (s:(C,FFI)data_state)` THEN
  CASE_REWRITE_TAC ASP3AUX_DO_APP_RWS THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;
let ASP3AUX_state_rel_termdep = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs f.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_state_termdep_fupd f t) v locs <=>
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds]);;
let ASP3AUX_toList_cut3 = prove
 (`!(a:A) b d. toList (mk_wf (inter (fromList [a;b;d]) (fromList [one;one;one]))) = [d;a;b]`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(BINOP_CONV ASP3AUX_SPT_CONV)))) THEN
  REWRITE_TAC[inter_def; mk_wf_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mk_BS_def; mk_wf_def; inter_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[toList_def; toListA_def]);;
let ASP3AUX_call_env_push_env_fields = prove
 (`!args ss env (t:(A,C,FFI)wl_state).
     wl_state_clock (wl_call_env args ss (wl_push_env env NONE t)) = wl_state_clock t /\
     wl_state_termdep (wl_call_env args ss (wl_push_env env NONE t)) = wl_state_termdep t /\
     wl_state_ffi (wl_call_env args ss (wl_push_env env NONE t)) = wl_state_ffi t /\
     wl_state_code (wl_call_env args ss (wl_push_env env NONE t)) = wl_state_code t /\
     wl_state_store (wl_call_env args ss (wl_push_env env NONE t)) = wl_state_store t /\
     wl_state_memory (wl_call_env args ss (wl_push_env env NONE t)) = wl_state_memory t`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `env:((A)word_loc)spt#((A)word_loc)spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:((A)word_loc)spt` (X_CHOOSE_THEN `e2:((A)word_loc)spt` SUBST1_TAC)) THEN
  REWRITE_TAC[wl_call_env_def; wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (e2:((A)word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]);;

(* ABBREV_TAC `v = e`, abbreviating e also in the assumptions *)
let ASP3AUX_ABBREV_ALL_TAC (tm:term) : tactic =
  ABBREV_TAC tm THEN
  FIRST_ASSUM(fun eq -> RULE_ASSUM_TAC(fun th ->
    if concl th = concl eq then th else PURE_REWRITE_RULE[eq] th));;
let ASP3AUX_do_app_RefByte_Rval = prove
 (`!fl i (w:byte) (s:(C,FFI)data_state). &0 <= i ==>
     ?r. data_do_app (MemOp (RefByte fl)) [data_Number i; data_Number (&(val w))] s =
         Rval (data_RefPtr T (minimal p. ~(p IN domain (data_state_refs s))), r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC ASP3AUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC (LENGTH::ASP3AUX_DO_APP_RWS) THEN
  SUBGOAL_THEN `?w':byte. &(val (w:byte)) = (&(val w'):int)` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);;
let ASP3AUX_do_app_RefByte_vals = prove
 (`!fl vals (s:(C,FFI)data_state) v s'.
     data_do_app (MemOp (RefByte fl)) vals s = Rval (v,s') ==>
     ?i (w:byte). vals = [data_Number i; data_Number (&(val w))] /\ &0 <= i`,
  REPEAT GEN_TAC THEN ASP3AUX_DO_APP_SPLIT_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;
let ASP3AUX_do_word_app_WordToInt = prove
 (`!vals v. data_do_word_app WordToInt vals = SOME v ==>
     ?w. vals = [data_Word64 w] /\ v = data_Number (&(val w))`,
  REPEAT GEN_TAC THEN CASES_ON `vals:data_v list` THEN
  REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  CASES_ON `a0:data_v` THEN REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  CASES_ON `a1:data_v list` THEN
  REWRITE_TAC[data_do_word_app_def; option_DISTINCT; option_INJ; CONS_11; injectivity "data_v"] THEN
  MESON_TAC[]);;
let ASP3AUX_do_app_WordToInt = prove
 (`!vals (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp WordToInt) vals s = Rval (v,s2) ==>
     ?w. vals = [data_Word64 w] /\ v = data_Number (&(val w)) /\ 3 <= data_state_space s /\
       data_state_ffi s2 = data_state_ffi s /\ data_state_clock s2 = data_state_clock s /\
       data_state_handler s2 = data_state_handler s /\ data_state_code s2 = data_state_code s /\
       data_state_compile s2 = data_state_compile s /\
       data_state_compile_oracle s2 = data_state_compile_oracle s /\
       data_state_tstamps s2 = data_state_tstamps s /\ data_state_locals s2 = data_state_locals s /\
       data_state_stack s2 = data_state_stack s /\
       data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
       data_state_locals_size s2 = data_state_locals_size s /\
       data_state_limits s2 = data_state_limits s /\
       data_state_global s2 = data_state_global s /\ data_state_refs s2 = data_state_refs s /\
       data_state_space s2 = data_state_space s - 3 /\
       option_le (data_state_stack_max s) (data_state_stack_max s2) /\
       (data_state_safe_for_space s2 ==> 1 < limits_length_limit (data_state_limits s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC ASP3AUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  TOP_CASE_TAC THEN CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:int64` STRIP_ASSUME_TAC o MATCH_MP ASP3AUX_do_word_app_WordToInt) THEN
  RVEQ_TAC THEN EXISTS_TAC `w:int64` THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def; option_le_max_right; option_le_refl] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;
let ASP3AUX_encode_header_small4 = prove
 (`!c tag len.
     good_dimindex (:A) /\ 1 < data_to_word_config_len_size c /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\ tag < 64 /\ len < 4 ==>
     ?h. encode_header c tag len = SOME (h:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[encode_header_def; dimword_def] THEN
  (COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THENL
   [MESON_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  (SUBGOAL_THEN `2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2) /\
                 2 EXP 2 <= 2 EXP data_to_word_config_len_size c` MP_TAC THENL
   [ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]));;
let ASP3AUX_w64_split32 = prove
 (`!w:int64. dimindex(:A) = 32 ==>
     val (word_extract 63 32 w:A word) * dimword(:A) + val (word_extract 31 0 w:A word) = val w`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_extract_subword; VAL_WORD_SUBWORD; dimword_def] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `w:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (w:int64) DIV 4294967296 < 4294967296` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`val (w:int64)`; `4294967296`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;
let ASP3AUX_w64_hi0 = prove
 (`!w:int64. dimindex(:A) = 32 /\ word_extract 63 32 w = (word 0:A word) ==>
     val (word_extract 31 0 w:A word) = val w`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `w:int64` (INST_TYPE [`:A`,`:A`] ASP3AUX_w64_split32)) THEN
  ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]);;
let ASP3AUX_small_lo32 = prove
 (`!x:A word. dimindex(:A) = 32 /\ word_ushr x 29 = word 0 ==>
     small_int (:A) (&(val x)) /\ word_shl x 2 = Smallnum (&(val x))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (x:A word) < 2 EXP 29` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:A word->num`) THEN
    REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_0] THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[small_int_def; data_to_word_Smallnum_def; dimword_def] THEN
  ASM_REWRITE_TAC[INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
                  INT_OF_NUM_LT; INT_ARITH `--(&n) <= &m:int`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
   [UNDISCH_TAC `val (x:A word) < 2 EXP 29` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM]]);;
let ASP3AUX_not_small_lo32 = prove
 (`!x:A word. dimindex(:A) = 32 /\ ~(word_ushr x 29 = word 0) ==> ~small_int (:A) (&(val x))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP 29 <= val (x:A word)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ; NOT_LT]; ALL_TAC] THEN
  REWRITE_TAC[small_int_def; dimword_def] THEN ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let ASP3AUX_val_zx64 = prove
 (`!w:int64. dimindex(:A) = 64 ==> val (word_zx w:A word) = val w`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64]);;
let ASP3AUX_small_zx64 = prove
 (`!w:int64. dimindex(:A) = 64 /\ word_ushr (word_zx w:A word) 61 = word 0 ==>
     small_int (:A) (&(val w)) /\ word_shl (word_zx w:A word) 2 = Smallnum (&(val w))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (w:int64) < 2 EXP 61` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:A word->num`) THEN
    ASM_SIMP_TAC[VAL_WORD_USHR; VAL_WORD_0; ASP3AUX_val_zx64] THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[small_int_def; data_to_word_Smallnum_def; dimword_def] THEN
  ASM_REWRITE_TAC[INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
                  INT_OF_NUM_LT; INT_ARITH `--(&n) <= &m:int`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
   [UNDISCH_TAC `val (w:int64) < 2 EXP 61` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD] THEN ASM_SIMP_TAC[ASP3AUX_val_zx64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM]]);;
let ASP3AUX_not_small_zx64 = prove
 (`!w:int64. dimindex(:A) = 64 /\ ~(word_ushr (word_zx w:A word) 61 = word 0) ==>
     ~small_int (:A) (&(val (word_zx w:A word)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP 61 <= val (word_zx (w:int64):A word)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ; NOT_LT]; ALL_TAC] THEN
  REWRITE_TAC[small_int_def; dimword_def] THEN ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let ASP3AUX_shl1_mul2 = prove
 (`!x:A word. word_shl x 1 = word_mul (word 2) x`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD_MUL; VAL_WORD; EXP_1] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;
let ASP3AUX_state_rel_small_res = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs s2 dest i L.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\ small_int (:A) i /\
     data_state_ffi s2 = data_state_ffi s /\ data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\ data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_tstamps s2 = data_state_tstamps s /\ data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     data_state_global s2 = data_state_global s /\ data_state_refs s2 = data_state_refs s /\
     data_state_space s2 <= data_state_space s /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     join_env_locals (data_state_locals s) L = join_env_locals (data_state_locals s) (wl_state_locals t) /\
     lookup 0 L = lookup 0 (wl_state_locals t) /\
     (!n. IS_SOME (lookup n (data_state_locals s)) ==> IS_SOME (lookup (adjust_var n) L))
     ==> data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest (data_Number i) s2)
           (wl_state_locals_fupd (K (insert (adjust_var dest) (wl_Word (Smallnum i)) L)) t) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ_0];
    GEN_TAC THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ASM_MESON_TAC[];
    MP5AUX_HEAD_MESON_TAC[option_le_trans];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GSYM join_env_locals_def] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_less_space THEN
  EXISTS_TAC `data_state_space (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[join_env_locals_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th))) THEN
  CASE_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]);;
let ASP3AUX_state_rel_big_res = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs s2 dest i sp nf m' locals'.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\ data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\ data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_tstamps s2 = data_state_tstamps s /\ data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     data_state_global s2 = data_state_global s /\ data_state_refs s2 = data_state_refs s /\
     data_state_space s2 <= sp /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s) sp
       (wl_state_store t |+ (NextFree,nf)) m' (wl_state_mdomain t)
       (APPEND (join_env_locals (insert dest (data_Number i) (data_state_locals s)) locals')
          (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))) /\
     (!n. IS_SOME (lookup n (data_state_locals s)) ==> IS_SOME (lookup (adjust_var n) locals')) /\
     IS_SOME (lookup (adjust_var dest) locals') /\
     lookup 0 locals' = lookup 0 (wl_state_locals t)
     ==> data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest (data_Number i) s2)
           (wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
             (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; code_oracle_rel_def; limits_inv_def]) THEN
  REWRITE_TAC[ALL; code_oracle_rel_def; limits_inv_def; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT;
              FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ASM_MESON_TAC[];
    MP5AUX_HEAD_MESON_TAC[option_le_trans];
    ALL_TAC] THEN
  MATCH_MP_TAC memory_rel_less_space THEN EXISTS_TAC `sp:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `nf:A word_loc`)) (concl th))) THEN
  CASE_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; join_env_locals_def]);;
let ASP3AUX_EVX =
  [wl_word_exp_def; wl_get_var_def; wl_get_vars_def; wl_get_var_imm_def; ASP3AUX_word_cmp_Word;
   the_words_def; word_op_def; wl_set_var_def; wl_mem_load_def; lookup_insert; MAP; ITLIST;
   OPTION_MAP_DEF; WORD_ADD_0; asm_word_cmp_def; wl_state_INFO.ri_accfupds; K_THM];;
let ASP3AUX_do_app_ListAppend = prove
 (`!vals (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp clos_ListAppend) vals s = Rval (v,s2) ==>
     ?x1 x2 xs ys. vals = [x1; x2] /\ data_v_to_list x1 = SOME xs /\ data_v_to_list x2 = SOME ys /\
       (!ts. data_state_tstamps s = SOME ts ==>
             v = data_list_to_v ts x2 xs /\ data_state_tstamps s2 = SOME (ts + LENGTH xs)) /\
       data_state_ffi s2 = data_state_ffi s /\ data_state_clock s2 = data_state_clock s /\
       data_state_handler s2 = data_state_handler s /\ data_state_code s2 = data_state_code s /\
       data_state_compile s2 = data_state_compile s /\
       data_state_compile_oracle s2 = data_state_compile_oracle s /\
       data_state_locals s2 = data_state_locals s /\
       data_state_stack s2 = data_state_stack s /\
       data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
       data_state_locals_size s2 = data_state_locals_size s /\
       data_state_limits s2 = data_state_limits s /\
       data_state_global s2 = data_state_global s /\ data_state_refs s2 = data_state_refs s /\
       data_state_space s2 = 0 /\
       data_state_stack_max s2 =
         OPTION_MAP2 MAX (data_state_stack_max s)
           (OPTION_MAP2 (+)
              (OPTION_MAP2 MAX (lookup Append_location (data_state_stack_frame_sizes s))
                 (OPTION_MAP2 MAX (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))
                    (lookup AppendMainLoop_location (data_state_stack_frame_sizes s))))
              (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) (data_state_locals_size s))) /\
       (data_state_safe_for_space s2 ==>
          no_thunks_in_refs (data_state_refs s) /\
          1 < limits_length_limit (data_state_limits s) /\
          3 * SUC (LENGTH xs) < 2 EXP arch_size (data_state_limits s) DIV 8 /\
          size_of_heap_args [x1; x2] s + SUC (LENGTH xs) * 3 <= limits_heap_limit (data_state_limits s))`,
  REPEAT GEN_TAC THEN ASP3AUX_DO_APP_SPLIT_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`a0:data_v`; `a0':data_v`; `a:data_v list`; `a':data_v list`] THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; stack_consumed_def; space_consumed_def;
                  lim_safe_def; option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
(* local copies of call_env_push_env_dec_clock_stack_max (HOL4 line 7457) and  *)
(* call_env_push_env_dec_clock_lift (HOL4 line 7877): assign_ListAppend (HOL4  *)
(* line 5411) needs them before those lines                                    *)
let ASP3AUX_cpd_stack_max = prove
 (`!args ls env (s:(C,FFI)data_state).
     data_state_stack_max (data_call_env args ls (data_push_env env F (data_dec_clock s))) =
     OPTION_MAP2 MAX
       (OPTION_MAP2 MAX (data_state_stack_max s)
          (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
       (OPTION_MAP2 (+)
          (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
          ls)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; size_of_stack_eq]);;

let ASP3AUX_cpd_lift = prove
 (`!(args:(A word_loc)list) b y1 y2 (t:(A,C,FFI)wl_state) ck' tp.
     wl_call_env args b (wl_push_env (y1,y2) NONE
       (wl_dec_clock (wl_state_clock_fupd (K ck') (wl_state_termdep_fupd (K tp) t)))) =
     wl_state_clock_fupd (K (ck' - 1))
       (wl_state_termdep_fupd (K tp) (wl_call_env args b (wl_push_env (y1,y2) NONE t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_dec_clock_def; wl_call_env_def; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  MP_TAC(ISPEC `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[]);;

(* local copy of option_le_stackmax_bridge (HOL4 line 7470), needed by     *)
(* assign_ListAppend (HOL4 line 5411)                                          *)
let ASP3AUX_stackmax_bridge = prove
 (`!(m:num option) (l_size:num option) (s_size:num option)
    (ls_R:num option) (ls_Re:num option).
     option_le
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX
             (OPTION_MAP2 MAX m (OPTION_MAP2 (+) l_size s_size))
             (OPTION_MAP2 (+) (OPTION_MAP2 (+) l_size s_size) ls_R))
          (OPTION_MAP2 (+) (OPTION_MAP2 MAX ls_R ls_Re) (OPTION_MAP2 (+) s_size l_size)))
       (OPTION_MAP2 MAX m
          (OPTION_MAP2 (+) (OPTION_MAP2 MAX ls_R ls_Re) (OPTION_MAP2 (+) s_size l_size)))`,
  REPEAT GEN_TAC THEN
  CASES_ON `m:num option` THEN CASES_ON `l_size:num option` THEN
  CASES_ON `s_size:num option` THEN CASES_ON `ls_R:num option` THEN
  CASES_ON `ls_Re:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

let ASP3AUX_toAList_LN = prove
 (`toAList (LN:A spt) = []`, REWRITE_TAC[toAList_def; foldi_def]);;
let ASP3AUX_Append_ret = prove
 (`!c n l n' l' (sc:(C,FFI)data_state) (tc:(A,C,FFI)wl_state) locs (sd:(C,FFI)data_state)
    (r:(A,C,FFI)wl_state) v rv ts sp.
     data_to_word_gcProof_state_rel c n l sc tc NONE locs /\
     wl_state_ffi r = wl_state_ffi tc /\ wl_state_handler r = wl_state_handler tc /\
     wl_state_gc_fun r = wl_state_gc_fun tc /\ wl_state_code r = wl_state_code tc /\
     wl_state_compile r = wl_state_compile tc /\
     wl_state_compile_oracle r = wl_state_compile_oracle tc /\
     wl_state_code_buffer r = wl_state_code_buffer tc /\
     wl_state_data_buffer r = wl_state_data_buffer tc /\
     wl_state_be r = wl_state_be tc /\ wl_state_mdomain r = wl_state_mdomain tc /\
     wl_state_stack r = wl_state_stack tc /\ wl_state_stack_size r = wl_state_stack_size tc /\
     wl_state_stack_limit r = wl_state_stack_limit tc /\ wl_state_locals_size r = SOME 0 /\
     FLOOKUP (wl_state_store r) CodeBuffer = FLOOKUP (wl_state_store tc) CodeBuffer /\
     FLOOKUP (wl_state_store r) CodeBufferEnd = FLOOKUP (wl_state_store tc) CodeBufferEnd /\
     FLOOKUP (wl_state_store r) BitmapBuffer = FLOOKUP (wl_state_store tc) BitmapBuffer /\
     FLOOKUP (wl_state_store r) BitmapBufferEnd = FLOOKUP (wl_state_store tc) BitmapBufferEnd /\
     FLOOKUP (wl_state_store r) HeapLength = FLOOKUP (wl_state_store tc) HeapLength /\
     FLOOKUP (wl_state_store r) Globals = FLOOKUP (wl_state_store tc) Globals /\
     option_le (wl_state_stack_max tc) (wl_state_stack_max r) /\
     option_le (wl_state_stack_max r) (data_state_stack_max sd) /\
     data_state_ffi sd = data_state_ffi sc /\ data_state_handler sd = data_state_handler sc /\
     data_state_code sd = data_state_code sc /\ data_state_compile sd = data_state_compile sc /\
     data_state_compile_oracle sd = data_state_compile_oracle sc /\
     data_state_stack_frame_sizes sd = data_state_stack_frame_sizes sc /\
     data_state_limits sd = data_state_limits sc /\ data_state_global sd = data_state_global sc /\
     data_state_tstamps sd = SOME ts /\ data_state_space sd <= sp /\
     memory_rel c (wl_state_be tc) ts (data_state_refs sd) sp (wl_state_store r) (wl_state_memory r)
       (wl_state_mdomain tc)
       (CONS (v,rv) (CONS (the_global (data_state_global sc),FAPPLY (wl_state_store tc) Globals)
          (data_to_word_gcProof_flat (data_state_stack sc) (wl_state_stack tc))))
     ==> data_to_word_gcProof_state_rel c n' l'
           (data_state_locals_fupd (K LN) (data_state_locals_size_fupd (K (SOME 0))
             (data_state_clock_fupd (K (wl_state_clock r))
               (data_state_stack_fupd (K (data_state_stack sc)) sd))))
           r (SOME [v,rv]) locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; code_oracle_rel_def; limits_inv_def]) THEN
  REWRITE_TAC[ALL; code_oracle_rel_def; limits_inv_def; IS_SOME_DEF; option_DISTINCT; lookup_def] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
  [(UNDISCH_TAC `Globals IN FDOM (wl_state_store (tc:(A,C,FFI)wl_state))` THEN
  MP_TAC(ASSUME `FLOOKUP (wl_state_store (r:(A,C,FFI)wl_state)) Globals = FLOOKUP (wl_state_store (tc:(A,C,FFI)wl_state)) Globals`) THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT]);
   (MATCH_MP_TAC option_le_trans THEN
  EXISTS_TAC `OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (tc:(A,C,FFI)wl_state))) (wl_state_locals_size tc)` THEN
  CONJ_TAC THENL
   [SPEC_TAC (`wl_stack_size (wl_state_stack (tc:(A,C,FFI)wl_state))`,`aa:num option`) THEN
    SPEC_TAC (`wl_state_locals_size (tc:(A,C,FFI)wl_state)`,`bb:num option`) THEN
    REPEAT GEN_TAC THEN CASES_ON `aa:num option` THEN CASES_ON `bb:num option` THEN
    REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC;
    MP5AUX_HEAD_MESON_TAC[option_le_trans]]);
   (SUBGOAL_THEN `FAPPLY (wl_state_store (r:(A,C,FFI)wl_state)) Globals = FAPPLY (wl_state_store (tc:(A,C,FFI)wl_state)) Globals`
    SUBST1_TAC THENL
   [UNDISCH_TAC `Globals IN FDOM (wl_state_store (tc:(A,C,FFI)wl_state))` THEN
    MP_TAC(ASSUME `FLOOKUP (wl_state_store (r:(A,C,FFI)wl_state)) Globals = FLOOKUP (wl_state_store (tc:(A,C,FFI)wl_state)) Globals`) THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT; option_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[THE_DEF; adjust_set_LN; inter_LN; ASP3AUX_toAList_LN; join_env_NIL] THEN CASE_REWRITE_TAC[APPEND] THEN
  MATCH_MP_TAC memory_rel_less_space THEN EXISTS_TAC `sp:num` THEN ASM_REWRITE_TAC[])]);;
let ASP3AUX_temp_ne = prove
 (`~(word 2:(5)word = word 0) /\ ~(word 1:(5)word = word 0) /\ ~(word 2:(5)word = word 1) /\
   ~(word 0:(5)word = word 1) /\ ~(word 0:(5)word = word 2) /\ ~(word 1:(5)word = word 2)`,
  REPEAT CONJ_TAC THEN CONV_TAC WORD_REDUCE_CONV);;
let ASP3AUX_EXISTS_PAIR2_TAC : tactic = fun (asl,w) ->
  let _,b = dest_exists w in
  let _,b2 = dest_exists b in
  let body = snd (strip_exists b2) in
  let e1,e2 = dest_conj (fst (dest_conj body)) in
  (EXISTS_TAC (lhs e1) THEN EXISTS_TAC (lhs e2) THEN REWRITE_TAC[]) (asl,w);;
let ASP3AUX_stack_max_mono = prove
 (CASE_TERM `!x y. (match x with NONE -> y = NONE | SOME sm -> the sm y >= sm) ==> option_le x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:num option` THEN CASES_ON `y:num option` THEN
  CASE_REWRITE_TAC[option_le_def; option_DISTINCT; the_def] THEN ARITH_TAC);;
let ASP3AUX_evaluate_stack_max_le = prove
 (`!p (s1:(A,C,FFI)wl_state) res s2. wl_evaluate (p,s1) = (res,s2) ==>
     option_le (wl_state_stack_max s1) (wl_state_stack_max s2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP ASP3AUX_stack_max_mono o MATCH_MP evaluate_stack_max));;
let ASP3AUX_append_stack_bridge = prove
 (`!mt m ml ll ap z x smx.
     option_le mt m /\
     option_le smx (OPTION_MAP2 MAX (OPTION_MAP2 MAX mt (OPTION_MAP2 (+) (OPTION_MAP2 (+) z x) ml))
                      (OPTION_MAP2 (+) (OPTION_MAP2 MAX ml ll) (OPTION_MAP2 (+) z x))) ==>
     option_le smx (OPTION_MAP2 MAX m (OPTION_MAP2 (+) (OPTION_MAP2 MAX ap (OPTION_MAP2 MAX ll ml))
                      (OPTION_MAP2 (+) x z)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> CASES_ON v)
    [`mt:num option`; `m:num option`; `ml:num option`; `ll:num option`; `ap:num option`;
     `z:num option`; `x:num option`; `smx:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;
let ASP3AUX_Append_cons_enough = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs x1 x2 a0 a1' (hdr:A word) ssz env0 xs0 ts0 sp0 (sd:(C,FFI)data_state) r1 r2.
   data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
   encode_header c 0 2 = SOME hdr /\
   data_get_vars [0; 1] (data_state_locals s) = SOME [x2; x1] /\
   data_v_to_list x1 = SOME (CONS a0 a1') /\
   dimword (:A) < wl_state_clock t /\
   data_state_stack s = CONS (data_Env ssz env0) xs0 /\
   data_state_tstamps s = SOME ts0 /\
   3 * LENGTH (CONS (a0:data_v) a1') <= sp0 /\
   memory_rel c (wl_state_be t) ts0 (data_state_refs s) sp0 (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
     (APPEND (join_env (data_state_locals s) (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
       (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
          (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))) /\
   data_state_ffi sd = data_state_ffi s /\ data_state_handler sd = data_state_handler s /\
   data_state_code sd = data_state_code s /\ data_state_compile sd = data_state_compile s /\
   data_state_compile_oracle sd = data_state_compile_oracle s /\
   data_state_stack_frame_sizes sd = data_state_stack_frame_sizes s /\
   data_state_limits sd = data_state_limits s /\ data_state_global sd = data_state_global s /\
   data_state_tstamps sd = SOME (ts0 + LENGTH (CONS a0 a1')) /\ data_state_space sd = 0 /\
   data_state_refs sd = data_state_refs s /\
   option_le (OPTION_MAP2 MAX (data_state_stack_max s)
       (OPTION_MAP2 (+) (OPTION_MAP2 MAX (lookup Append_location (data_state_stack_frame_sizes s))
           (OPTION_MAP2 MAX (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))
              (lookup AppendMainLoop_location (data_state_stack_frame_sizes s))))
         (OPTION_MAP2 (+) (size_of_stack xs0) ssz)))
     (data_state_stack_max sd)
   ==> ?rv r. wl_evaluate (Append_code c,t) = (SOME (wl_Result (wl_Loc l1 l2) [rv]),r) /\
              data_to_word_gcProof_state_rel c r1 r2
                (data_state_locals_fupd (K LN) (data_state_locals_size_fupd (K (SOME 0))
                   (data_state_clock_fupd (K (wl_state_clock r)) (data_state_stack_fupd (K (data_state_stack s)) sd))))
                r (SOME [data_list_to_v ts0 x2 (CONS a0 a1'),rv]) locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_limits (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`[0;1]:num list`; `[x2;x1]:data_v list`; `c:data_to_word_config`; `l1:num`; `l2:num`;
    `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `LENGTH [x2; x1:data_v] = LENGTH (ws:(A word_loc)list)` o concl)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word_loc` (X_CHOOSE_THEN `w1:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2] o SYM) THEN
  FIRST_ASSUM(fun th -> if ASP3AUX_is_app "memory_rel" (concl th) then
    MP_TAC(MATCH_MP memory_rel_get_vars_IMP (CONJ th (CONJ
     (ASSUME `data_get_vars [0; 1] (data_state_locals (s:(C,FFI)data_state)) = SOME [x2; x1]`)
     (ASSUME `wl_get_vars (MAP adjust_var [0; 1]) (t:(A,C,FFI)wl_state) = SOME [w2:A word_loc; w1]`)))) else NO_TAC) THEN
  REWRITE_TAC[ZIP; APPEND] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; get_vars_SOME_IFF_data]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[adjust_var_def; wl_get_var_def]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP3AUX_state_rel_lookup_0 o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  REWRITE_TAC[data_to_word_Append_code_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `x2:data_v`)) (concl th))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tsc:num` (X_CHOOSE_THEN `ys1:data_v` STRIP_ASSUME_TAC) o
    MATCH_MP v_to_list_SOME_CONS_IMP o check ((=) `data_v_to_list x1 = SOME (CONS a0 a1')` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) = `x1:data_v`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ww:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `pa:A word` (X_CHOOSE_THEN `px:A word` STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def; ASP3AUX_word_cmp_Word; asm_word_cmp_def;
     WORD_AND_1; ASSUME `lookup 4 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Word (ww:A word))`;
     ASSUME `bit 0 (ww:A word)`] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[WORD_NE_10] THEN
  CASE_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_space_max o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `x2:data_v`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `nf:A word` (X_CHOOSE_THEN `tg:A word` (X_CHOOSE_THEN `sp:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_store (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `nf2:A word` (X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `nf2:A word = nf` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word (nf2:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
    REWRITE_TAC (ASP3AUX_ev_Set :: ASP3AUX_ev_Assign :: wl_get_store_def :: wl_set_store_def ::
                 FLOOKUP_UPDATE :: distinctness "store_name" :: injectivity "store_name" ::
                 ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]))) THEN
  (SUBGOAL_THEN `(shift_length c - backend_common_word_shift (:A)) MOD 2 EXP dimindex (:A) =
                shift_length c - backend_common_word_shift (:A) /\
                ~(shift_length c - backend_common_word_shift (:A) >= dimindex (:A))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC MOD_LT; ALL_TAC] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN REWRITE_TAC[dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o] THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
    REWRITE_TAC (ASP3AUX_ev_Set :: ASP3AUX_ev_Assign :: wl_get_store_def :: wl_set_store_def ::
                 FLOOKUP_UPDATE :: distinctness "store_name" :: injectivity "store_name" ::
                 ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o]))) THEN
  (REWRITE_TAC[WORD_OR_0] THEN
  ABBREV_TAC `ip = word_or (word_shl (word_sub nf curr) (shift_length c - backend_common_word_shift (:A)))
     (word_or (word 1) (word_bits (small_shift_length c - 1) 0 (ptr_bits c 0 2))):A word` THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_stubs (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `dimword (:A) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_Call; wl_get_vars_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (AppendMainLoop_code c, tl:(A,C,FFI)wl_state)` `tl:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (tl:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals tl) = SOME (wl_Word (nf:A word)) /\
     lookup 4 (wl_state_locals tl) = SOME (wl_Word (ww:A word)) /\
     lookup 6 (wl_state_locals tl) = SOME (wl_Word (hdr:A word)) /\
     lookup 8 (wl_state_locals tl) = SOME (wl_Word (word_mul bytes_in_word (word sp))) /\
     lookup 10 (wl_state_locals tl) = SOME (wl_Word (ip:A word)) /\
     wl_state_store tl = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
        (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip) /\
     wl_state_memory tl = wl_state_memory t /\ wl_state_mdomain tl = wl_state_mdomain t /\
     wl_state_be tl = wl_state_be t /\ wl_state_code tl = wl_state_code t /\
     wl_state_stack_size tl = wl_state_stack_size t /\ wl_state_stack tl = wl_state_stack t /\
     wl_state_clock tl = wl_state_clock t - 1 /\
     wl_state_locals_size tl = lookup AppendMainLoop_location (wl_state_stack_size t) /\
     wl_state_ffi tl = wl_state_ffi t /\ wl_state_handler tl = wl_state_handler t /\
     wl_state_gc_fun tl = wl_state_gc_fun t /\ wl_state_compile tl = wl_state_compile t /\
     wl_state_compile_oracle tl = wl_state_compile_oracle t /\
     wl_state_code_buffer tl = wl_state_code_buffer t /\
     wl_state_data_buffer tl = wl_state_data_buffer t /\
     wl_state_stack_limit tl = wl_state_stack_limit t /\
     wl_state_stack_max tl = OPTION_MAP2 MAX (wl_state_stack_max t)
        (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
           (lookup AppendMainLoop_location (wl_state_stack_size t)))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tl" THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM; lookup_fromList2;
                lookup_fromList] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH; EL; HD; TL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; EL; HD; TL] THEN
    REWRITE_TAC[ARITH];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `3 * LENGTH (CONS (a0:data_v) a1') <= sp` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `sp0:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CONS (a0:data_v) a1'`; `ww:A word`; `tl:(A,C,FFI)wl_state`;
    `CONS (x2:data_v,w2:A word_loc) (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
       (toAList (inter (wl_state_locals (t:(A,C,FFI)wl_state)) (adjust_set (data_state_locals s)))))
       (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
          (data_to_word_gcProof_flat (CONS (data_Env ssz env0) xs0) (wl_state_stack t))))`;
    `ip:A word`; `hdr:A word`; `0`; `SEP_T:(A word#A word_loc->bool)->bool`; `l1:num`; `l2:num`; `nf:A word`;
    `ts0:num`; `data_Block tsc cons_tag [a0; ys1]`; `c:data_to_word_config`; `s:(C,FFI)data_state`;
    `sp:num`; `w2:A word_loc`; `wl_Word (ip:A word)`; `nf:A word`] evaluate_AppendMainLoop_code) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[memory_rel_Temp; NOT_CONS_NIL; SUB_0; FLOOKUP_UPDATE; distinctness "store_name";
                    injectivity "store_name"; WORD_MUL_0; WORD_ADD_0; ADD_CLAUSES; WORD_NE_10; ASP3AUX_temp_ne] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
        can (find_term ((=) `sp:num`)) (concl th))) THEN
      MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC memory_rel_IMP_word_list_exists THEN
      MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts0:num`;
        `data_state_refs (s:(C,FFI)data_state)`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`] THEN
      FIRST_ASSUM(fun th -> if ASP3AUX_is_app "memory_rel" (concl th) &&
        can (find_term ((=) `sp:num`)) (concl th) then
        EXISTS_TAC (rand (concl th)) THEN ASM_REWRITE_TAC[] else NO_TAC);
      SUBGOAL_THEN `LENGTH (CONS (a0:data_v) a1') < dimword (:A)` MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
          can (find_term ((=) `sp:num`)) (concl th))) THEN
        DISCH_THEN(fun th -> MP_TAC(MATCH_MP memory_rel_list_limit (CONJ th (CONJ
          (ASSUME `data_v_to_list (data_Block tsc cons_tag [a0; ys1]) = SOME (CONS a0 a1')`)
          (ASSUME `good_dimindex (:A)`))))) THEN
        UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        UNDISCH_TAC `dimword (:A) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN ARITH_TAC]];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` (X_CHOOSE_THEN `wsl:(A word_loc)list`
    (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  EXISTS_TAC `wl_Word (ip:A word)` THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1]) THEN
  (ASP3AUX_MATCH_ABBREV_TAC `data_to_word_gcProof_state_rel c r1 r2 (X:(C,FFI)data_state) (rr:(A,C,FFI)wl_state) (Y:((data_v#(A)word_loc)list)option) locs` `rr:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[GSYM (ASSUME `data_state_stack (s:(C,FFI)data_state) = CONS (data_Env ssz env0) xs0`)] THEN
  MATCH_MP_TAC ASP3AUX_Append_ret THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `l2:num`; `t:(A,C,FFI)wl_state`; `ts0 + LENGTH (CONS (a0:data_v) a1')`;
     `sp - 3 * LENGTH (CONS (a0:data_v) a1')`] THEN
  ASM_REWRITE_TAC[LE_0] THEN
  EXPAND_TAC "rr" THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; distinctness "store_name"] THEN
  ALL_TAC) THEN
  (SUBGOAL_THEN `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)) = OPTION_MAP2 (+) ssz (size_of_stack xs0) /\
                wl_state_stack_size t = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                option_le (wl_state_stack_max t) (data_state_stack_max s)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP stack_rel_IMP_size_of_stack) THEN
    ASM_REWRITE_TAC[size_of_stack_eq];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_evaluate_stack_max_le o check (fun th -> is_eq (concl th) &&
     ASP3AUX_is_app "wl_evaluate" (lhs (concl th)) && free_in `tl:(A,C,FFI)wl_state` (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
  ALL_TAC) THEN
  (CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `OPTION_MAP2 MAX (wl_state_stack_max (t:(A,C,FFI)wl_state))
      (OPTION_MAP2 (+) (OPTION_MAP2 (+) ssz (size_of_stack xs0))
         (lookup AppendMainLoop_location (data_state_stack_frame_sizes (s:(C,FFI)data_state))))` THEN
    ASM_REWRITE_TAC[option_le_max_right; option_le_refl];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
       (OPTION_MAP2 (+) (OPTION_MAP2 MAX (lookup Append_location (data_state_stack_frame_sizes s))
           (OPTION_MAP2 MAX (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))
              (lookup AppendMainLoop_location (data_state_stack_frame_sizes s))))
         (OPTION_MAP2 (+) (size_of_stack xs0) ssz))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ASP3AUX_append_stack_bridge THEN
    EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
       lhand (concl th) = `smx:num option`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `hdr = make_header c (word 0) 2:A word /\ 1 < data_to_word_config_len_size c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `encode_header c 0 2 = SOME (hdr:A word)` THEN REWRITE_TAC[encode_header_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `data_to_word_config_len_size c`)) (concl th) &&
       is_conj (concl th))) THEN
    REWRITE_TAC[GSYM NOT_LE] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(2 EXP data_to_word_config_len_size c <= 2)` THEN
    REWRITE_TAC[CONTRAPOS_THM; NOT_LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 1` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `hdr = make_header c (word 0) 2:A word` o concl)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts0:num`;
    `data_state_refs (s:(C,FFI)data_state)`; `sp:num`;
    `wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+ (Temp (word 1),wl_Word ww) |+
       (Temp (word 2),wl_Word ip)`;
    `m1:A word->A word_loc`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `x2:data_v`; `w2:A word_loc`;
    `CONS (a0:data_v) a1'`; `wsl:(A word_loc)list`;
    `APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
       (toAList (inter (wl_state_locals (t:(A,C,FFI)wl_state)) (adjust_set (data_state_locals s)))))
       (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
          (data_to_word_gcProof_flat (CONS (data_Env ssz env0) xs0) (wl_state_stack t)))`;
    `nf:A word`; `ip:A word`; `curr:A word`] memory_rel_append) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOT_CONS_NIL; FLOOKUP_UPDATE; distinctness "store_name"] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
        free_in `m1:A word->A word_loc` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (ASP3AUX_is_app "misc_word_list")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "ip" THEN
      REWRITE_TAC[make_cons_ptr_def; get_lowerbits_def; injectivity "word_loc"] THEN
      REWRITE_TAC[WORD_BITWISE_RULE `!a b:A word. word_or a (word_or b a) = word_or a b`]];
    ALL_TAC] THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]));;
let ASP3AUX_MEM_join_env = prove
 (`!(l:A spt) (tl:B spt) p. MEM p (join_env l (toAList (inter tl (adjust_set l)))) ==>
     ?n. lookup n l = SOME (FST p) /\ lookup (adjust_var n) tl = SOME (SND p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM_toAList; lookup_inter; lookup_adjust_set]) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
  EXISTS_TAC `(k - 2) DIV 2` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (ASP3AUX_is_app "lookup")) (concl th))) THEN
  CASES_ON `lookup (k:num) (tl:B spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `adjust_var ((k - 2) DIV 2) = k` SUBST1_TAC THENL
   [REWRITE_TAC[adjust_var_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[DE_MORGAN_THM; NOT_ODD] THEN
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(k = 0)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(2 * m - 2) DIV 2 = m - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (ASP3AUX_is_app "domain")) (concl th))) THEN
  REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF]);;
let ASP3AUX_append_gc_stack_bridge = prove
 (`!mt m ml ll ap z x smx smx2.
     option_le mt m /\
     option_le smx (OPTION_MAP2 MAX (OPTION_MAP2 MAX mt (OPTION_MAP2 (+) (OPTION_MAP2 (+) z x) ml))
                      (OPTION_MAP2 (+) (OPTION_MAP2 (+) z x) (OPTION_MAP2 MAX ll ml))) /\
     option_le smx2 (OPTION_MAP2 MAX smx (OPTION_MAP2 (+) (OPTION_MAP2 (+) z x) ll)) ==>
     option_le smx2 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) (OPTION_MAP2 MAX ap (OPTION_MAP2 MAX ll ml))
                      (OPTION_MAP2 (+) x z)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> CASES_ON v)
    [`mt:num option`; `m:num option`; `ml:num option`; `ll:num option`; `ap:num option`;
     `z:num option`; `x:num option`; `smx:num option`; `smx2:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;
let ASP3AUX_ww11_val = prove
 (`!sp n. good_dimindex (:A) /\ (dimindex(:A) DIV 8) * sp < dimword (:A) /\ sp < 3 * n /\
          3 * (n + 1) * (dimindex (:A) DIV 8) < dimword (:A) ==>
     val (word_add (word (12 * (n - sp DIV 3)))
            (word_ushr (word_mul bytes_in_word (word sp)) (backend_common_word_shift (:A) - 2)) : A word) =
     12 * n + 4 * (sp MOD 3)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bytes_in_word_def; backend_common_word_shift_def; VAL_WORD_ADD; VAL_WORD_USHR;
                  VAL_WORD_MUL; VAL_WORD; dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV) THENL
  [(FIRST_X_ASSUM(let qtm = `dimindex(:A) = 32` in fun th -> if concl th = qtm || concl th = `dimindex(:A) = 64` then
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[th; dimword_def]) else NO_TAC) THEN
  MP_TAC(SPECL [`sp:num`; `3`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`sp MOD 3`,`r:num`) THEN SPEC_TAC(`sp DIV 3`,`q:num`) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN REWRITE_TAC[DIV_1] THEN
  SUBGOAL_THEN `q * 3 + r < 4294967296 /\ 4 * (q * 3 + r) < 4294967296 /\ 12 * (n - q) < 4294967296 /\
                12 * (n - q) + 4 * (q * 3 + r) < 4294967296 /\ 12 * n + 4 * r < 4294967296 /\
                12 * (n - q) + 4 * (q * 3 + r) = 12 * n + 4 * r`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);
   (FIRST_X_ASSUM(let qtm = `dimindex(:A) = 32` in fun th -> if concl th = qtm || concl th = `dimindex(:A) = 64` then
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[th; dimword_def]) else NO_TAC) THEN
  MP_TAC(SPECL [`sp:num`; `3`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`sp MOD 3`,`r:num`) THEN SPEC_TAC(`sp DIV 3`,`q:num`) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN REWRITE_TAC[DIV_1] THEN
  SUBGOAL_THEN `q * 3 + r < 18446744073709551616 /\ 4 * (q * 3 + r) < 18446744073709551616 /\ 12 * (n - q) < 18446744073709551616 /\
                12 * (n - q) + 4 * (q * 3 + r) < 18446744073709551616 /\ 12 * n + 4 * r < 18446744073709551616 /\
                12 * (n - q) + 4 * (q * 3 + r) = 12 * n + 4 * r`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]) THEN
   (SUBGOAL_THEN `(8 * (q * 3 + r)) DIV 2 = 4 * (q * 3 + r)` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT])]);;
let ASP3AUX_toList_cut2 = prove
 (`!(a:A) b. toList (mk_wf (inter (fromList [a;b]) (fromList [one;one]))) = [a;b]`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(BINOP_CONV ASP3AUX_SPT_CONV)))) THEN
  REWRITE_TAC[inter_def; mk_wf_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mk_BS_def; mk_BN_def; mk_wf_def; inter_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[toList_def; toListA_def]);;
let ASP3AUX_size_of_heap_cut2 = prove
 (`!(s:(C,FFI)data_state) (sa:(C,FFI)data_state) a b ssz env0 xs0.
     data_state_stack s = CONS (data_Env ssz env0) xs0 /\
     data_state_locals sa = fromList [a;b] /\ data_state_stack sa = data_state_stack s /\
     data_state_limits sa = data_state_limits s /\ data_state_global sa = data_state_global s /\
     data_state_refs sa = data_state_refs s ==>
     size_of_heap (cut_locals (fromList [one;one]) sa) =
     size_of_heap_args [a;b] (data_state_locals_fupd (K env0) (data_state_stack_fupd (K xs0)
        (data_state_locals_size_fupd (K ssz) s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[cut_locals_def; data_cut_env_def; domain_fromList; LENGTH; SUBSET_REFL] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[size_of_heap_def; size_of_heap_args_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[ASP3AUX_toList_cut2; MAP; FLAT; extract_stack_def; APPEND; GSYM APPEND_ASSOC]);;
let ASP3AUX_append_stack_bridge2 = prove
 (`!m ap ll ml z x.
     option_le
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX
             (OPTION_MAP2 MAX m (OPTION_MAP2 (+) (OPTION_MAP2 MAX ap (OPTION_MAP2 MAX ll ml)) (OPTION_MAP2 (+) x z)))
             (OPTION_MAP2 (+) (OPTION_MAP2 (+) z x) ap))
          (OPTION_MAP2 (+) (OPTION_MAP2 MAX ap (OPTION_MAP2 MAX ll ml)) (OPTION_MAP2 (+) x z)))
       (OPTION_MAP2 MAX m (OPTION_MAP2 (+) (OPTION_MAP2 MAX ap (OPTION_MAP2 MAX ll ml)) (OPTION_MAP2 (+) x z)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> CASES_ON v)
    [`m:num option`; `ap:num option`; `ll:num option`; `ml:num option`; `z:num option`; `x:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;
let ASP3AUX_Append_thm = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs x1 x2 s1 v s2 r1 r2 (hdr:A word).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     encode_header c 0 2 = SOME hdr /\
     data_get_vars [0; 1] (data_state_locals s) = SOME [x2; x1] /\
     wl_state_clock t = MustTerminate_limit (:A) - 1 /\
     data_pop_env s = SOME s1 /\ is_env (HD (data_state_stack s)) /\
     data_state_locals_size s = lookup Append_location (data_state_stack_frame_sizes s) /\
     data_do_app (BlockOp clos_ListAppend) [x1; x2] s1 = Rval (v,s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2)
     ==> ?q r new_c.
           wl_evaluate (Append_code c,t) = (q,r) /\
           (if q = SOME NotEnoughSpace
            then wl_state_ffi r = wl_state_ffi t /\
                 option_le (wl_state_stack_max r) (data_state_stack_max s2) /\
                 (~(data_to_word_config_gc_kind c = data_to_word_None) /\
                  no_thunks_in_refs (data_state_refs s) ==>
                  !xs. data_v_to_list x1 = SOME xs /\
                       3 * SUC (LENGTH xs) < 2 EXP arch_size (data_state_limits s1) DIV 8 ==>
                       limits_heap_limit (data_state_limits s1) <
                       size_of_heap_args [x1; x2] s1 + SUC (LENGTH xs) * 3)
            else ?rv. q = SOME (wl_Result (wl_Loc l1 l2) [rv]) /\
                      data_to_word_gcProof_state_rel c r1 r2
                        (data_state_locals_fupd (K LN)
                          (data_state_locals_size_fupd (K (SOME 0))
                            (data_state_clock_fupd (K new_c)
                              (data_state_stack_fupd (K (data_state_stack s)) s2))))
                        r (SOME [v,rv]) locs)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a1:data_v` (X_CHOOSE_THEN `a2:data_v` (X_CHOOSE_THEN `xs:data_v list`
    (X_CHOOSE_THEN `ys:data_v list` STRIP_ASSUME_TAC))) o MATCH_MP ASP3AUX_do_app_ListAppend) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) && is_var (rhs (concl th)) &&
     (rhs (concl th) = `a1:data_v` || rhs (concl th) = `a2:data_v`))))) THEN
  (MP_TAC(SPECL [`s:(C,FFI)data_state`; `s1:(C,FFI)data_state`] ASP3AUX_pop_env_is_env) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ssz:num option` (X_CHOOSE_THEN `env0:data_v spt`
    (X_CHOOSE_THEN `xs0:stack list` STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  MP_TAC(MATCH_MP state_rel_IMP_tstamps (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `ts0:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ts0:num` o check (fun th -> is_forall (concl th) &&
     can (find_term (ASP3AUX_is_app "data_list_to_v")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_limits (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`[0;1]:num list`; `[x2;x1]:data_v list`; `c:data_to_word_config`; `l1:num`; `l2:num`;
    `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `LENGTH [x2; x1:data_v] = LENGTH (ws:(A word_loc)list)` o concl)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word_loc` (X_CHOOSE_THEN `w1:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2] o SYM) THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_memory_rel (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP memory_rel_get_vars_IMP (CONJ th (CONJ
     (ASSUME `data_get_vars [0; 1] (data_state_locals (s:(C,FFI)data_state)) = SOME [x2; x1]`)
     (ASSUME `wl_get_vars (MAP adjust_var [0; 1]) (t:(A,C,FFI)wl_state) = SOME [w2:A word_loc; w1]`))))) THEN
  REWRITE_TAC[ZIP; APPEND] THEN ASM_REWRITE_TAC[THE_DEF] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; get_vars_SOME_IFF_data]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[adjust_var_def; wl_get_var_def]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP3AUX_state_rel_lookup_0 o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl))) THEN
  (REWRITE_TAC[data_to_word_Append_code_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `xs:data_v list`) THENL
 [(REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th))) THEN
  FIRST_ASSUM(MP_TAC o check ((=) `data_v_to_list x1 = SOME []` o concl)) THEN
  REWRITE_TAC[v_to_list_SOME_NIL_IFF] THEN DISCH_THEN(X_CHOOSE_THEN `tsn:num` SUBST_ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ww:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def; ASP3AUX_word_cmp_Word; asm_word_cmp_def;
     WORD_AND_1; ASSUME `lookup 4 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Word (ww:A word))`;
     ASSUME `~bit 0 (ww:A word)`] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[ASP3AUX_ev_Return; wl_get_var_def; wl_get_vars_def;
     ASSUME `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`;
     ASSUME `lookup 2 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (w2:A word_loc)`] THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`SOME (wl_Result (wl_Loc l1 l2) [w2:A word_loc])`;
    `wl_flush_state F (t:(A,C,FFI)wl_state)`; `wl_state_clock (t:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"; CONS_11; UNWIND_THM1] THEN
  REWRITE_TAC[data_list_to_v_def]) THEN
  (SUBGOAL_THEN `wl_state_clock (t:(A,C,FFI)wl_state) = wl_state_clock (wl_flush_state F t)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds]; ALL_TAC] THEN
  REWRITE_TAC[GSYM (ASSUME `data_state_stack (s:(C,FFI)data_state) = CONS (data_Env ssz env0) xs0`)] THEN
  MATCH_MP_TAC ASP3AUX_Append_ret THEN
  MAP_EVERY EXISTS_TAC [`l1:num`; `l2:num`; `t:(A,C,FFI)wl_state`; `ts0:num`; `data_state_space (s:(C,FFI)data_state)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ADD_CLAUSES]) THEN
  ASM_REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM; option_le_refl; LE_0]) THEN
  (CONJ_TAC THENL
   [REWRITE_TAC[option_le_max_right] THEN DISJ1_TAC THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `data_Block tsn nil_tag []`)) (concl th) &&
       can (find_term (ASP3AUX_is_app "join_env")) (concl th))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]]);
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_memory_rel (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  ASM_REWRITE_TAC[THE_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_space_max) THEN
  DISCH_THEN(X_CHOOSE_THEN `nf:A word` (X_CHOOSE_THEN `tg:A word` (X_CHOOSE_THEN `sp:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `dimword (:A) < wl_state_clock (t:(A,C,FFI)wl_state)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MustTerminate_limit_def] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
    MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `3 * LENGTH (CONS (a0:data_v) a1') <= sp`) THENL
   [(MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
    `locs:(num#num)list`; `x1:data_v`; `x2:data_v`; `a0:data_v`; `a1':data_v list`; `hdr:A word`;
    `ssz:num option`; `env0:data_v spt`; `xs0:stack list`; `ts0:num`; `sp:num`; `s2:(C,FFI)data_state`;
    `r1:num`; `r2:num`] ASP3AUX_Append_cons_enough) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[option_le_refl; get_vars_SOME_IFF_data]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_Append_code_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rv:A word_loc` (X_CHOOSE_THEN `rr:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`SOME (wl_Result (wl_Loc l1 l2) [rv:A word_loc])`; `rr:(A,C,FFI)wl_state`;
    `wl_state_clock (rr:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"; CONS_11] THEN
  EXISTS_TAC `rv:A word_loc` THEN ASM_REWRITE_TAC[]);
    (SUBGOAL_THEN `data_get_vars [0; 1] (data_state_locals (s:(C,FFI)data_state)) = SOME [x2; x1] /\
                wl_get_vars (MAP adjust_var [0; 1]) (t:(A,C,FFI)wl_state) = SOME [w2:A word_loc; w1]`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[get_vars_SOME_IFF_data; MAP; get_vars_SOME_IFF; wl_get_var_def; adjust_var_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if ASP3AUX_is_app "memory_rel" (concl th) && can (find_term ((=) `sp:num`)) (concl th) then
    MP_TAC(MATCH_MP memory_rel_get_vars_IMP (CONJ th (CONJ
     (ASSUME `data_get_vars [0; 1] (data_state_locals (s:(C,FFI)data_state)) = SOME [x2; x1]`)
     (ASSUME `wl_get_vars (MAP adjust_var [0; 1]) (t:(A,C,FFI)wl_state) = SOME [w2:A word_loc; w1]`)))) else NO_TAC) THEN
  REWRITE_TAC[ZIP; APPEND] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `x2:data_v`)) (concl th))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tsc:num` (X_CHOOSE_THEN `ys1:data_v` STRIP_ASSUME_TAC) o
    MATCH_MP v_to_list_SOME_CONS_IMP o check ((=) `data_v_to_list x1 = SOME (CONS a0 a1')` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) = `x1:data_v`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ww:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `pa:A word` (X_CHOOSE_THEN `px:A word` STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def; ASP3AUX_word_cmp_Word; asm_word_cmp_def;
     WORD_AND_1; ASSUME `lookup 4 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Word (ww:A word))`;
     ASSUME `bit 0 (ww:A word)`] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[WORD_NE_10] THEN
  CASE_REWRITE_TAC[]) THEN
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_store (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `nf2:A word` (X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `nf2:A word = nf` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word (nf2:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
    REWRITE_TAC (ASP3AUX_ev_Set :: ASP3AUX_ev_Assign :: wl_get_store_def :: wl_set_store_def ::
                 FLOOKUP_UPDATE :: distinctness "store_name" :: injectivity "store_name" ::
                 ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]))) THEN
  (SUBGOAL_THEN `(shift_length c - backend_common_word_shift (:A)) MOD 2 EXP dimindex (:A) =
                shift_length c - backend_common_word_shift (:A) /\
                ~(shift_length c - backend_common_word_shift (:A) >= dimindex (:A))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC MOD_LT; ALL_TAC] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN REWRITE_TAC[dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o] THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
    REWRITE_TAC (ASP3AUX_ev_Set :: ASP3AUX_ev_Assign :: wl_get_store_def :: wl_set_store_def ::
                 FLOOKUP_UPDATE :: distinctness "store_name" :: injectivity "store_name" ::
                 ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o]))) THEN
  (REWRITE_TAC[WORD_OR_0] THEN
  ABBREV_TAC `ip = word_or (word_shl (word_sub nf curr) (shift_length c - backend_common_word_shift (:A)))
     (word_or (word 1) (word_bits (small_shift_length c - 1) 0 (ptr_bits c 0 2))):A word` THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_stubs (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `dimword (:A) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_Call; wl_get_vars_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (AppendMainLoop_code c, tl:(A,C,FFI)wl_state)` `tl:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (tl:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals tl) = SOME (wl_Word (nf:A word)) /\
     lookup 4 (wl_state_locals tl) = SOME (wl_Word (ww:A word)) /\
     lookup 6 (wl_state_locals tl) = SOME (wl_Word (hdr:A word)) /\
     lookup 8 (wl_state_locals tl) = SOME (wl_Word (word_mul bytes_in_word (word sp))) /\
     lookup 10 (wl_state_locals tl) = SOME (wl_Word (ip:A word)) /\
     wl_state_store tl = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
        (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip) /\
     wl_state_memory tl = wl_state_memory t /\ wl_state_mdomain tl = wl_state_mdomain t /\
     wl_state_be tl = wl_state_be t /\ wl_state_code tl = wl_state_code t /\
     wl_state_stack_size tl = wl_state_stack_size t /\ wl_state_stack tl = wl_state_stack t /\
     wl_state_clock tl = wl_state_clock t - 1 /\
     wl_state_locals_size tl = lookup AppendMainLoop_location (wl_state_stack_size t) /\
     wl_state_ffi tl = wl_state_ffi t /\ wl_state_handler tl = wl_state_handler t /\
     wl_state_gc_fun tl = wl_state_gc_fun t /\ wl_state_compile tl = wl_state_compile t /\
     wl_state_compile_oracle tl = wl_state_compile_oracle t /\
     wl_state_code_buffer tl = wl_state_code_buffer t /\
     wl_state_data_buffer tl = wl_state_data_buffer t /\
     wl_state_stack_limit tl = wl_state_stack_limit t /\
     wl_state_stack_max tl = OPTION_MAP2 MAX (wl_state_stack_max t)
        (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
           (lookup AppendMainLoop_location (wl_state_stack_size t)))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tl" THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM; lookup_fromList2;
                lookup_fromList] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH; EL; HD; TL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; EL; HD; TL] THEN
    REWRITE_TAC[ARITH];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `sp < 3 * LENGTH (CONS (a0:data_v) a1')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CONS (a0:data_v) a1'`; `ww:A word`; `tl:(A,C,FFI)wl_state`;
    `CONS (x2:data_v,w2:A word_loc) (CONS (data_Block tsc cons_tag [a0; ys1],wl_Word (ww:A word))
       (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
       (toAList (inter (wl_state_locals (t:(A,C,FFI)wl_state)) (adjust_set (data_state_locals s)))))
       (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
          (data_to_word_gcProof_flat (CONS (data_Env ssz env0) xs0) (wl_state_stack t)))))`;
    `ip:A word`; `hdr:A word`; `SEP_T:(A word#A word_loc->bool)->bool`; `l1:num`; `l2:num`; `nf:A word`;
    `ts0:num`; `data_Block tsc cons_tag [a0; ys1]`; `c:data_to_word_config`; `s:(C,FFI)data_state`;
    `sp:num`; `w2:A word_loc`; `wl_Word (ip:A word)`; `nf:A word`] evaluate_AppendMainLoop_code_alt) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[memory_rel_Temp; NOT_CONS_NIL; FLOOKUP_UPDATE; distinctness "store_name";
                    injectivity "store_name"; WORD_NE_10; ASP3AUX_temp_ne] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
        can (find_term ((=) `sp:num`)) (concl th) &&
        can (find_term ((=) `x2:data_v`)) (concl th))) THEN
      MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC memory_rel_IMP_word_list_exists THEN
      MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts0:num`;
        `data_state_refs (s:(C,FFI)data_state)`; `sp:num`; `wl_state_store (t:(A,C,FFI)wl_state)`] THEN
      FIRST_ASSUM(fun th -> if ASP3AUX_is_app "memory_rel" (concl th) &&
        can (find_term ((=) `sp:num`)) (concl th) then
        EXISTS_TAC (rand (concl th)) THEN ASM_REWRITE_TAC[LE_REFL] else NO_TAC);
      SUBGOAL_THEN `LENGTH (CONS (a0:data_v) a1') < dimword (:A)` MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
          can (find_term ((=) `sp:num`)) (concl th) &&
          can (find_term ((=) `x2:data_v`)) (concl th))) THEN
        DISCH_THEN(fun th -> MP_TAC(MATCH_MP memory_rel_list_limit (CONJ th (CONJ
          (ASSUME `data_v_to_list (data_Block tsc cons_tag [a0; ys1]) = SOME (CONS a0 a1')`)
          (ASSUME `good_dimindex (:A)`))))) THEN
        UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        REWRITE_TAC[MustTerminate_limit_def] THEN ARITH_TAC]];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` (X_CHOOSE_THEN `ww2:A word`
    (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_assignProof_STOP_def] THEN
  ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (AppendLenLoop_code c, tll:(A,C,FFI)wl_state)` `tll:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (tll:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals tll) = SOME (wl_Word (ww2:A word)) /\
     lookup 4 (wl_state_locals tll) = SOME (wl_Word (word 0)) /\
     wl_state_store tll = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
        (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip) /\
     wl_state_memory tll = m1 /\ wl_state_mdomain tll = wl_state_mdomain t /\
     wl_state_be tll = wl_state_be t /\ wl_state_code tll = wl_state_code t /\
     wl_state_stack_size tll = wl_state_stack_size t /\ wl_state_stack tll = wl_state_stack t /\
     wl_state_clock tll = wl_state_clock t - 1 - (sp DIV 3 + 1) /\
     wl_state_locals_size tll = lookup AppendLenLoop_location (wl_state_stack_size t) /\
     wl_state_ffi tll = wl_state_ffi t /\ wl_state_handler tll = wl_state_handler t /\
     wl_state_gc_fun tll = wl_state_gc_fun t /\ wl_state_compile tll = wl_state_compile t /\
     wl_state_compile_oracle tll = wl_state_compile_oracle t /\
     wl_state_code_buffer tll = wl_state_code_buffer t /\
     wl_state_data_buffer tll = wl_state_data_buffer t /\
     wl_state_stack_limit tll = wl_state_stack_limit t /\
     wl_state_stack_max tll = smx`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tll" THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_fromList2; lookup_fromList] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH; EL; HD; TL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[num_CONV `2`; num_CONV `1`; EL; HD; TL] THEN REWRITE_TAC[ARITH];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`data_state_refs (s:(C,FFI)data_state)`; `tll:(A,C,FFI)wl_state`; `c:data_to_word_config`;
    `DROP (sp DIV 3) (CONS (a0:data_v) a1')`; `l1:num`; `l2:num`; `ww2:A word`;
    `CONS (x2:data_v,w2:A word_loc) (CONS (data_Block tsc cons_tag [a0; ys1],wl_Word (ww:A word))
       (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
       (toAList (inter (wl_state_locals (t:(A,C,FFI)wl_state)) (adjust_set (data_state_locals s)))))
       (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
          (data_to_word_gcProof_flat (CONS (data_Env ssz env0) xs0) (wl_state_stack t)))))`;
    `ts0:num`; `THE (block_drop (sp DIV 3) (data_Block tsc cons_tag [a0; ys1]))`;
    `sp:num`] evaluate_AppendLenLoop_code) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sp DIV 3 < LENGTH (CONS (a0:data_v) a1')` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
        free_in `m1:A word->A word_loc` (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC v_to_list_block_drop THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `LENGTH (CONS (a0:data_v) a1') < dimword (:A)` MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
          can (find_term ((=) `sp:num`)) (concl th) &&
          can (find_term ((=) `x2:data_v`)) (concl th) &&
          not (free_in `m1:A word->A word_loc` (concl th)))) THEN
        DISCH_THEN(fun th -> MP_TAC(MATCH_MP memory_rel_list_limit (CONJ th (CONJ
          (ASSUME `data_v_to_list (data_Block tsc cons_tag [a0; ys1]) = SOME (CONS a0 a1')`)
          (ASSUME `good_dimindex (:A)`))))) THEN
        UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        REWRITE_TAC[LENGTH_DROP; MustTerminate_limit_def] THEN
        UNDISCH_TAC `sp DIV 3 < LENGTH (CONS (a0:data_v) a1')` THEN ARITH_TAC]];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `lc:(A word_loc)spt` (X_CHOOSE_THEN `smx2:num option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (AppendLenLoop_code c, tlz:(A,C,FFI)wl_state)` `tlz:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `wl_state_locals (tlz:(A,C,FFI)wl_state) = lc /\
     wl_state_store tlz = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
        (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip) /\
     wl_state_memory tlz = m1 /\ wl_state_mdomain tlz = wl_state_mdomain t /\
     wl_state_be tlz = wl_state_be t /\ wl_state_code tlz = wl_state_code t /\
     wl_state_stack_size tlz = wl_state_stack_size t /\ wl_state_stack tlz = wl_state_stack t /\
     wl_state_clock tlz = wl_state_clock t - 1 - (sp DIV 3 + 1) - LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1')) /\
     wl_state_locals_size tlz = lookup AppendLenLoop_location (wl_state_stack_size t) /\
     wl_state_ffi tlz = wl_state_ffi t /\ wl_state_handler tlz = wl_state_handler t /\
     wl_state_gc_fun tlz = wl_state_gc_fun t /\ wl_state_compile tlz = wl_state_compile t /\
     wl_state_compile_oracle tlz = wl_state_compile_oracle t /\
     wl_state_code_buffer tlz = wl_state_code_buffer t /\
     wl_state_data_buffer tlz = wl_state_data_buffer t /\
     wl_state_stack_limit tlz = wl_state_stack_limit t /\
     wl_state_stack_max tlz = smx2`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tlz" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
     (ASP3AUX_is_app "wl_evaluate" (lhs (concl th)) ||
      (is_comb (lhs (concl th)) && can (find_term (ASP3AUX_is_app "wl_evaluate")) (lhs (concl th))))))) THEN
  REWRITE_TAC[AppendLenLoop_code_def] THEN ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  SUBGOAL_THEN `~bit 0 (word 2:A word)` ASSUME_TAC THENL
   [REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def; ASP3AUX_word_cmp_Word; asm_word_cmp_def;
     WORD_AND_1; ASSUME `wl_state_locals (tlz:(A,C,FFI)wl_state) = lc`;
     ASSUME `lookup 2 (lc:(A word_loc)spt) = SOME (wl_Word (word 2))`;
     ASSUME `~bit 0 (word 2:A word)`] THEN CASE_REWRITE_TAC[]))) THEN
  (REWRITE_TAC[data_to_word_list_Seq_def] THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
    REWRITE_TAC (ASP3AUX_ev_Assign :: wl_get_store_def :: FLOOKUP_UPDATE :: distinctness "store_name" ::
                 injectivity "store_name" :: ARITH_EQ :: word_exp_set_var_ShiftVar_lemma :: ASP3AUX_temp_ne ::
                 ASSUME `wl_state_locals (tlz:(A,C,FFI)wl_state) = lc` ::
                 ASSUME `wl_state_store (tlz:(A,C,FFI)wl_state) = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
                     (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip)` ::
                 ASSUME `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) TriggerGC = SOME (wl_Word (tg:A word))` ::
                 ASSUME `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word (nf:A word))` ::
                 ASSUME `word_sub tg nf = word_mul bytes_in_word (word sp):A word` ::
                 ASSUME `lookup 4 (lc:(A word_loc)spt) = SOME (wl_Word (word (12 * LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1')))))` ::
                 ASP3AUX_EVX) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o]))) THEN
  (ONCE_REWRITE_TAC[word_exp_set_var_ShiftVar_lemma] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN CASE_REWRITE_TAC[]) THEN
  (REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
    REWRITE_TAC (ASP3AUX_ev_Assign :: wl_get_store_def :: FLOOKUP_UPDATE :: distinctness "store_name" ::
                 injectivity "store_name" :: ARITH_EQ :: ASP3AUX_temp_ne ::
                 ASSUME `wl_state_locals (tlz:(A,C,FFI)wl_state) = lc` ::
                 ASSUME `wl_state_store (tlz:(A,C,FFI)wl_state) = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
                     (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip)` ::
                 ASP3AUX_EVX) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o]))) THEN
  (ABBREV_TAC `ww11 = word_add (word (12 * LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1'))))
     (word_ushr (word_mul bytes_in_word (word sp)) (backend_common_word_shift (:A) - 2)):A word` THEN
  ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (AllocVar c (dimword (:A) DIV 8 - 1) (fromList [one; one]), tt:(A,C,FFI)wl_state)` `tt:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `wl_state_locals (tt:(A,C,FFI)wl_state) =
       insert 2 (wl_Word ww) (insert 4 w2 (insert 1 (wl_Word ww11)
         (insert 1 (wl_Word (word_mul bytes_in_word (word sp))) lc))) /\
     wl_state_store tt = wl_state_store (t:(A,C,FFI)wl_state) |+ (Temp (word 0),w2) |+
        (Temp (word 1),wl_Word ww) |+ (Temp (word 2),wl_Word ip) /\
     wl_state_memory tt = m1 /\ wl_state_mdomain tt = wl_state_mdomain t /\
     wl_state_be tt = wl_state_be t /\ wl_state_code tt = wl_state_code t /\
     wl_state_stack_size tt = wl_state_stack_size t /\ wl_state_stack tt = wl_state_stack t /\
     wl_state_clock tt = wl_state_clock t - 1 - (sp DIV 3 + 1) - LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1')) /\
     wl_state_locals_size tt = lookup AppendLenLoop_location (wl_state_stack_size t) /\
     wl_state_ffi tt = wl_state_ffi t /\ wl_state_handler tt = wl_state_handler t /\
     wl_state_gc_fun tt = wl_state_gc_fun t /\ wl_state_compile tt = wl_state_compile t /\
     wl_state_compile_oracle tt = wl_state_compile_oracle t /\
     wl_state_code_buffer tt = wl_state_code_buffer t /\
     wl_state_data_buffer tt = wl_state_data_buffer t /\
     wl_state_stack_limit tt = wl_state_stack_limit t /\
     wl_state_stack_max tt = smx2`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)) = OPTION_MAP2 (+) ssz (size_of_stack xs0) /\
                wl_state_stack_size t = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                option_le (wl_state_stack_max t) (data_state_stack_max s)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP stack_rel_IMP_size_of_stack) THEN
    ASM_REWRITE_TAC[size_of_stack_eq];
    ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
     (data_state_locals_fupd (K (fromList [data_Block tsc cons_tag [a0; ys1]; x2]))
       (data_state_clock_fupd (K (wl_state_clock (tt:(A,C,FFI)wl_state)))
         (data_state_space_fupd (K sp)
           (data_state_stack_max_fupd (K (data_state_stack_max (s2:(C,FFI)data_state)))
             (data_state_locals_size_fupd (K (lookup AppendLenLoop_location (data_state_stack_frame_sizes (s:(C,FFI)data_state)))) s)))))
     tt NONE locs` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; code_oracle_rel_def; limits_inv_def]) THEN
    REWRITE_TAC[ALL; code_oracle_rel_def; limits_inv_def; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT;
                FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [(REWRITE_TAC[IS_SOME_DEF]);
      (ASM_REWRITE_TAC[lookup_insert; ARITH_EQ]);
      (GEN_TAC THEN REWRITE_TAC[lookup_fromList; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_CASES_TAC `n < 2` THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
      SUBGOAL_THEN `n = 0 \/ n = 1` MP_TAC THENL [UNDISCH_TAC `n < 2` THEN ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[adjust_var_def; lookup_insert] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[IS_SOME_DEF]);
      (FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "ALL2" (concl th) &&
         can (find_term (fun tm -> try fst (dest_const tm) = "data_to_word_gcProof_stack_rel" with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[]);
      (MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `smx:num option` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
           rand (concl th) = `smx:num option`)) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
           rand (concl th) = `smx2:num option`)) THEN ASM_REWRITE_TAC[]]);
      (MATCH_MP_TAC ASP3AUX_append_gc_stack_bridge THEN
      MAP_EVERY EXISTS_TAC [`wl_state_stack_max (t:(A,C,FFI)wl_state)`; `smx:num option`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
           lhand (concl th) = `smx:num option`)) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
           lhand (concl th) = `smx2:num option`)) THEN ASM_REWRITE_TAC[]]);
      ((REWRITE_TAC[THE_DEF] THEN CASE_REWRITE_TAC[APPEND] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
         free_in `m1:A word->A word_loc` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN
      X_GEN_TAC `p:data_v#A word_loc` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
      (FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP3AUX_MEM_join_env o check (fun th -> ASP3AUX_is_app "MEM" (concl th))) THEN
      REWRITE_TAC[lookup_fromList; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(X_CHOOSE_THEN `nn:num` MP_TAC) THEN
      ASM_CASES_TAC `nn < 2` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
      SUBGOAL_THEN `nn = 0 \/ nn = 1` MP_TAC THENL [UNDISCH_TAC `nn < 2` THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[adjust_var_def; lookup_insert] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[EL; HD; TL; ONE; option_INJ] THEN
      SPEC_TAC(`p:data_v#A word_loc`,`p:data_v#A word_loc`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]))];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?aa1 aa2. wl_evaluate (AllocVar c (dimword (:A) DIV 8 - 1) (fromList [one; one]),
       (tt:(A,C,FFI)wl_state)) = (aa1,aa2)`
    (X_CHOOSE_THEN `aa1:((A)wl_result)option` (X_CHOOSE_THEN `aa2:(A,C,FFI)wl_state` ASSUME_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `data_cut_env (fromList [one; one]) (fromList [data_Block tsc cons_tag [a0; ys1]; x2]) =
     SOME (mk_wf (inter (fromList [data_Block tsc cons_tag [a0; ys1]; x2]) (fromList [one; one])))` ASSUME_TAC THENL
   [REWRITE_TAC[data_cut_env_def; domain_fromList; LENGTH; SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_locals_fupd (K (fromList [data_Block tsc cons_tag [a0; ys1]; x2]))
       (data_state_clock_fupd (K (wl_state_clock (tt:(A,C,FFI)wl_state)))
         (data_state_space_fupd (K sp)
           (data_state_stack_max_fupd (K (data_state_stack_max (s2:(C,FFI)data_state)))
             (data_state_locals_size_fupd (K (lookup AppendLenLoop_location (data_state_stack_frame_sizes (s:(C,FFI)data_state)))) s))))`;
    `tt:(A,C,FFI)wl_state`; `locs:(num#num)list`; `fromList [one; one]`;
    `mk_wf (inter (fromList [data_Block tsc cons_tag [a0; ys1]; x2]) (fromList [one; one]))`;
    `ww11:A word`; `dimword (:A) DIV 8 - 1`; `aa1:((A)wl_result)option`; `aa2:(A,C,FFI)wl_state`] AllocVar_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; wl_get_var_def; lookup_insert] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `aa1 = SOME (NotEnoughSpace:(A)wl_result)` THEN ASM_REWRITE_TAC[]) THENL
     [(STRIP_TAC THEN REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  MAP_EVERY EXISTS_TAC [`SOME (NotEnoughSpace:(A)wl_result)`; `aa2:(A,C,FFI)wl_state`; `0`] THEN
  REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  SUBGOAL_THEN `wl_state_ffi (t:(A,C,FFI)wl_state) = data_state_ffi (s:(C,FFI)data_state)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  ALL_TAC) THEN
  (STRIP_TAC THEN X_GEN_TAC `xs':data_v list` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) && rhs (concl th) = `xs':data_v list`)) THEN
  SUBGOAL_THEN `3 * (LENGTH (CONS (a0:data_v) a1') + 1) * (dimindex (:A) DIV 8) < dimword (:A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `sp:num`)) (concl th) &&
      can (find_term ((=) `x2:data_v`)) (concl th) &&
      not (free_in `m1:A word->A word_loc` (concl th)))) THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(MATCH_MP memory_rel_list_limit (CONJ th (CONJ
      (ASSUME `data_v_to_list (data_Block tsc cons_tag [a0; ys1]) = SOME (CONS a0 a1')`)
      (ASSUME `good_dimindex (:A)`))))); ALL_TAC] THEN
  SUBGOAL_THEN `(dimindex(:A) DIV 8) * sp < dimword (:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `good_dimindex (:A)`)) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (ww11:A word) = 12 * LENGTH (CONS (a0:data_v) a1') + 4 * (sp MOD 3)` ASSUME_TAC THENL
   [EXPAND_TAC "ww11" THEN REWRITE_TAC[LENGTH_DROP] THEN MATCH_MP_TAC ASP3AUX_ww11_val THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ALL_TAC) THEN
  (SUBGOAL_THEN `(12 * LENGTH (CONS (a0:data_v) a1') + 4 * (sp MOD 3)) DIV 4 = 3 * LENGTH (CONS a0 a1') + sp MOD 3`
    ASSUME_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`;
    `data_state_locals_fupd (K (fromList [data_Block tsc cons_tag [a0; ys1]; x2]))
       (data_state_clock_fupd (K (MustTerminate_limit (:A) - 1 - 1 - (sp DIV 3 + 1) - LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1'))))
         (data_state_space_fupd (K sp)
           (data_state_stack_max_fupd (K (OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
             (OPTION_MAP2 (+)
               (OPTION_MAP2 MAX (lookup Append_location (data_state_stack_frame_sizes s))
                 (OPTION_MAP2 MAX (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))
                   (lookup AppendMainLoop_location (data_state_stack_frame_sizes s))))
               (OPTION_MAP2 (+) (size_of_stack xs0) ssz))))
             (data_state_locals_size_fupd (K (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))) s))))`;
    `data_Block tsc cons_tag [a0; ys1]`; `x2:data_v`; `ssz:num option`; `env0:data_v spt`; `xs0:stack list`]
    ASP3AUX_size_of_heap_cut2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && can (find_term ((=) `ww11:A word`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ARITH_RULE `sp MOD 3 < 3`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (ASP3AUX_is_app "EXP")) (concl th) &&
     can (find_term ((=) `LENGTH (CONS (a0:data_v) a1')`)) (concl th) && is_binary "<" (concl th))) THEN
  REWRITE_TAC[GSYM dimword_def; LENGTH] THEN
  SPEC_TAC(`sp MOD 3`,`r:num`) THEN SPEC_TAC(`LENGTH (a1':data_v list)`,`k:num`) THEN
  REPEAT GEN_TAC THEN ARITH_TAC);
      (STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
      free_in `aa2:(A,C,FFI)wl_state` (concl th) then
      MP_TAC(MATCH_MP (ISPECL [`[0;1]:num list`; `[data_Block tsc cons_tag [a0; ys1]; x2]`] state_rel_get_vars_IMP) th)
    else NO_TAC) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; get_vars_SOME_IFF_data; data_get_var_def] THEN
    REWRITE_TAC[lookup_mk_wf; lookup_inter; lookup_fromList; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL; ONE] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `wsb:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
     rator (lhs (concl th)) = `LENGTH:data_v list->num`)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `wa:A word_loc` (X_CHOOSE_THEN `wb:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2] o SYM)) THEN
  (SUBGOAL_THEN `3 * (LENGTH (CONS (a0:data_v) a1') + 1) * (dimindex (:A) DIV 8) < dimword (:A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `sp:num`)) (concl th) &&
      can (find_term ((=) `x2:data_v`)) (concl th) &&
      not (free_in `m1:A word->A word_loc` (concl th)))) THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(MATCH_MP memory_rel_list_limit (CONJ th (CONJ
      (ASSUME `data_v_to_list (data_Block tsc cons_tag [a0; ys1]) = SOME (CONS a0 a1')`)
      (ASSUME `good_dimindex (:A)`))))); ALL_TAC] THEN
  SUBGOAL_THEN `(dimindex(:A) DIV 8) * sp < dimword (:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `good_dimindex (:A)`)) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_clock (aa2:(A,C,FFI)wl_state) =
     MustTerminate_limit (:A) - 1 - 1 - (sp DIV 3 + 1) - LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1'))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
      free_in `aa2:(A,C,FFI)wl_state` (concl th) then
      MP_TAC (MATCH_MP state_rel_imp_clock th) else NO_TAC) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sp < dimword (:A) /\ LENGTH (CONS (a0:data_v) a1') < dimword (:A) /\
                2 * dimword (:A) <= dimword (:A) * dimword (:A)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(dimindex (:A) DIV 8) * sp < dimword (:A)` THEN
      UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      UNDISCH_TAC `3 * (LENGTH (CONS (a0:data_v) a1') + 1) * (dimindex (:A) DIV 8) < dimword (:A)` THEN
      UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (aa2:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2) /\
                lookup 2 (wl_state_locals aa2) = SOME (wa:A word_loc) /\
                lookup 4 (wl_state_locals aa2) = SOME (wb:A word_loc) /\
                ~(wl_state_clock aa2 = 0) /\
                lookup Append_location (wl_state_code aa2) = SOME (3,Append_code c)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
      free_in `aa2:(A,C,FFI)wl_state` (concl th) then
      ASSUME_TAC (MATCH_MP ASP3AUX_state_rel_lookup_0 th) else NO_TAC) THEN
    UNDISCH_TAC `wl_get_vars (MAP adjust_var [0; 1]) (aa2:(A,C,FFI)wl_state) = SOME [wa:A word_loc; wb]` THEN
    REWRITE_TAC[MAP; get_vars_SOME_IFF; wl_get_var_def; adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MustTerminate_limit_def; LENGTH_DROP] THEN
    UNDISCH_TAC `sp < dimword (:A)` THEN UNDISCH_TAC `LENGTH (CONS (a0:data_v) a1') < dimword (:A)` THEN
    UNDISCH_TAC `2 * dimword (:A) <= dimword (:A) * dimword (:A)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_Call; wl_get_vars_def; wl_get_var_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[]) THEN
  (ABBREV_TAC `sa2 = data_state_locals_fupd
     (K (mk_wf (inter (fromList [data_Block tsc cons_tag [a0; ys1]; x2]) (fromList [one; one]))))
    (data_state_space_fupd (K (val (ww11:A word) DIV 4 + 1))
    (data_state_locals_fupd (K (fromList [data_Block tsc cons_tag [a0; ys1]; x2]))
    (data_state_clock_fupd (K (MustTerminate_limit (:A) - 1 - 1 - (sp DIV 3 + 1) - LENGTH (DROP (sp DIV 3) (CONS (a0:data_v) a1'))))
    (data_state_space_fupd (K sp)
    (data_state_stack_max_fupd
     (K (OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
     (OPTION_MAP2 (+)
      (OPTION_MAP2 MAX (lookup Append_location (data_state_stack_frame_sizes s))
      (OPTION_MAP2 MAX (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))
      (lookup AppendMainLoop_location (data_state_stack_frame_sizes s))))
     (OPTION_MAP2 (+) (size_of_stack xs0) ssz))))
    (data_state_locals_size_fupd (K (lookup AppendLenLoop_location (data_state_stack_frame_sizes s))) s))))))`) THEN
  (SUBGOAL_THEN `data_get_vars [1; 0] (data_state_locals (sa2:(C,FFI)data_state)) = SOME [x2; data_Block tsc cons_tag [a0; ys1]] /\
                data_state_stack sa2 = data_state_stack (s:(C,FFI)data_state) /\
                data_state_tstamps sa2 = SOME ts0 /\ data_state_space sa2 = val (ww11:A word) DIV 4 + 1 /\
                data_state_ffi sa2 = data_state_ffi s /\ data_state_handler sa2 = data_state_handler s /\
                data_state_code sa2 = data_state_code s /\ data_state_compile sa2 = data_state_compile s /\
                data_state_compile_oracle sa2 = data_state_compile_oracle s /\
                data_state_stack_frame_sizes sa2 = data_state_stack_frame_sizes s /\
                data_state_limits sa2 = data_state_limits s /\ data_state_global sa2 = data_state_global s /\
                data_state_refs sa2 = data_state_refs s /\
                data_state_stack_max sa2 = data_state_stack_max (s2:(C,FFI)data_state)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sa2" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[get_vars_SOME_IFF_data; data_get_var_def] THEN
    REWRITE_TAC[lookup_mk_wf; lookup_inter; lookup_fromList; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL; ONE] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars (MAP adjust_var [1; 0]) (aa2:(A,C,FFI)wl_state) = SOME [wb:A word_loc; wa]` ASSUME_TAC THENL
   [REWRITE_TAC[MAP; get_vars_SOME_IFF; wl_get_var_def; adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(let qtm = `data_to_word_gcProof_state_rel c l1 l2 sa2 (aa2:(A,C,FFI)wl_state) NONE locs` in fun th -> if concl th = qtm then
     MP_TAC(MATCH_MP state_rel_call_env (CONJ
       (ASSUME `data_get_vars [1; 0] (data_state_locals (sa2:(C,FFI)data_state)) = SOME [x2; data_Block tsc cons_tag [a0; ys1]]`)
       (CONJ (ASSUME `wl_get_vars (MAP adjust_var [1; 0]) (aa2:(A,C,FFI)wl_state) = SOME [wb:A word_loc; wa]`) th)))
     else NO_TAC) THEN
  ALL_TAC) THEN
  (DISCH_THEN(MP_TAC o SPECL [`l1:num`; `l2:num`; `lookup Append_location (wl_state_stack_size (aa2:(A,C,FFI)wl_state))`]) THEN
  DISCH_TAC THEN
  ABBREV_TAC `sb = data_call_env [x2; data_Block tsc cons_tag [a0; ys1]]
     (lookup Append_location (wl_state_stack_size (aa2:(A,C,FFI)wl_state))) (data_dec_clock (sa2:(C,FFI)data_state))` THEN
  ABBREV_TAC `tb = wl_call_env [wl_Loc l1 l2; wb; wa]
     (lookup Append_location (wl_state_stack_size (aa2:(A,C,FFI)wl_state))) (wl_dec_clock aa2)` THEN
  SUBGOAL_THEN `data_get_vars [0; 1] (data_state_locals (sb:(C,FFI)data_state)) = SOME [x2; data_Block tsc cons_tag [a0; ys1]] /\
                data_state_stack sb = data_state_stack (s:(C,FFI)data_state) /\
                data_state_tstamps sb = SOME ts0 /\ data_state_space sb = val (ww11:A word) DIV 4 + 1 /\
                data_state_ffi sb = data_state_ffi s /\ data_state_handler sb = data_state_handler s /\
                data_state_code sb = data_state_code s /\ data_state_compile sb = data_state_compile s /\
                data_state_compile_oracle sb = data_state_compile_oracle s /\
                data_state_stack_frame_sizes sb = data_state_stack_frame_sizes s /\
                data_state_limits sb = data_state_limits s /\ data_state_global sb = data_state_global s /\
                data_state_refs sb = data_state_refs s /\
                data_state_stack_max sb = OPTION_MAP2 MAX (data_state_stack_max (s2:(C,FFI)data_state))
                   (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
                      (lookup Append_location (wl_state_stack_size (aa2:(A,C,FFI)wl_state)))) /\
                wl_state_clock (tb:(A,C,FFI)wl_state) = wl_state_clock aa2 - 1`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN EXPAND_TAC "tb" THEN
    REWRITE_TAC[data_call_env_def; data_dec_clock_def; wl_call_env_def; wl_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[get_vars_SOME_IFF_data; data_get_var_def; lookup_fromList; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL; HD; TL; ONE];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `val (ww11:A word) = 12 * LENGTH (CONS (a0:data_v) a1') + 4 * (sp MOD 3)` ASSUME_TAC THENL
   [EXPAND_TAC "ww11" THEN REWRITE_TAC[LENGTH_DROP] THEN MATCH_MP_TAC ASP3AUX_ww11_val THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(12 * LENGTH (CONS (a0:data_v) a1') + 4 * (sp MOD 3)) DIV 4 = 3 * LENGTH (CONS a0 a1') + sp MOD 3`
    ASSUME_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_stack_size (aa2:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 sa2 (aa2:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `sb:(C,FFI)data_state`; `tb:(A,C,FFI)wl_state`;
    `locs:(num#num)list`; `data_Block tsc cons_tag [a0; ys1]`; `x2:data_v`; `a0:data_v`; `a1':data_v list`; `hdr:A word`;
    `ssz:num option`; `env0:data_v spt`; `xs0:stack list`; `ts0:num`; `data_state_space (sb:(C,FFI)data_state)`;
    `s2:(C,FFI)data_state`; `r1:num`; `r2:num`] ASP3AUX_Append_cons_enough) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MustTerminate_limit_def; LENGTH_DROP] THEN
      MP_TAC(SPECL [`sp:num`; `3`] DIV_LE) THEN REWRITE_TAC[ARITH_EQ] THEN
      MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN
      UNDISCH_TAC `sp < dimword (:A)` THEN UNDISCH_TAC `LENGTH (CONS (a0:data_v) a1') < dimword (:A)` THEN
      UNDISCH_TAC `2 * dimword (:A) <= dimword (:A) * dimword (:A)` THEN ARITH_TAC;
      MP_TAC(ARITH_RULE `sp MOD 3 < 3`) THEN ARITH_TAC;
      FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_memory_rel o
        check ((=) `data_to_word_gcProof_state_rel c l1 l2 sb (tb:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
      ASM_REWRITE_TAC[THE_DEF];
      ALL_TAC];
    ALL_TAC]) THENL
       [(REWRITE_TAC[size_of_stack_eq; ASP3AUX_append_stack_bridge2]);
        (DISCH_THEN(X_CHOOSE_THEN `rv:A word_loc` (X_CHOOSE_THEN `rb:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  MAP_EVERY EXISTS_TAC [`SOME (wl_Result (wl_Loc l1 l2) [rv:A word_loc])`; `rb:(A,C,FFI)wl_state`;
    `wl_state_clock (rb:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"; CONS_11] THEN
  EXISTS_TAC `rv:A word_loc` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
     free_in `rb:(A,C,FFI)wl_state` (concl th))) THEN
  ASM_REWRITE_TAC[])]]]]);;
let ASP3AUX_do_app_ListAppend_same_v = prove
 (`!x1 x2 (s:(C,FFI)data_state) (s':(C,FFI)data_state) v r.
     data_do_app (BlockOp clos_ListAppend) [x1; x2] s = Rval (v,r) /\
     data_state_tstamps s' = data_state_tstamps s ==>
     ?r'. data_do_app (BlockOp clos_ListAppend) [x1; x2] s' = Rval (v,r')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC ASP3AUX_DO_APP_DEFS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `data_v_to_list x1` THEN CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  CASES_ON `data_v_to_list x2` THEN CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  CASES_ON `data_state_tstamps (s:(C,FFI)data_state)` THEN
  CASE_REWRITE_TAC (ARITH_EQ::ASP3AUX_DO_APP_RWS) THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 5411 *)
let assign_ListAppend = prove
 (assign_thm_stmt `op = BlockOp clos_ListAppend`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ns. names_opt = SOME (ns:num_set)` (X_CHOOSE_THEN `ns:num_set` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (BlockOp clos_ListAppend) <=> names_opt:num_set option = NONE)` THEN
    REWRITE_TAC(op_requires_names_def::op_space_reset_def::ASP3AUX_DO_APP_RWS) THEN
    CASES_ON `names_opt:num_set option` THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP do_app_stack_max) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`; `ns:num_set`;
    `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r1:data_v` (X_CHOOSE_THEN `r2:data_v` (X_CHOOSE_THEN `in1:data_v list`
    (X_CHOOSE_THEN `in2:data_v list` STRIP_ASSUME_TAC))) o MATCH_MP ASP3AUX_do_app_ListAppend) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_get_vars_2) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `SUC (SUC 0) = LENGTH (ws:(A word_loc)list)` o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2]) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_ListAppend_def; data_to_word_get_names_def]) THEN
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_limits (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THENL
  [(MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] evaluate_GiveUp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
  EXISTS_TAC `r0:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN
    REWRITE_TAC[option_le_max_right; option_le_refl] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `0`; `2`] (INST_TYPE [`:A`,`:A`] ASP3AUX_encode_header_small4)) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && lhand (concl th) = `data_state_safe_for_space (s2:(C,FFI)data_state)`)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);
   (SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_MustTerminate] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `tm = wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                     (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state))` THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_stubs (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt` STRIP_ASSUME_TAC) o
    MATCH_MP cut_env_IMP_cut_envs) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[ASP3AUX_ev_Call; wl_get_vars_def; wl_get_var_def] THEN
  EXPAND_TAC "tm" THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[domain_adjust_sets; ALL_DISTINCT; MEM; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[]) THEN
  (REWRITE_TAC[MustTerminate_limit_NOT_0] THEN
  SUBGOAL_THEN `data_cut_env (ns:num_set) (data_state_locals (s:(C,FFI)data_state)) =
                SOME (mk_wf (inter (data_state_locals s) (ns:num_set)))` ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_state_opt (SOME ns) (s:(C,FFI)data_state) =
      SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals s) (ns:num_set)))) s)` THEN
    REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `data_cut_env (ns:num_set) (data_state_locals (s:(C,FFI)data_state))` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
       (data_state_clock_fupd (K (MustTerminate_limit (:A))) (s:(C,FFI)data_state)) (tm:(A,C,FFI)wl_state) NONE locs`
    ASSUME_TAC THENL
   [EXPAND_TAC "tm" THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`NONE:(num#(A)wl_prog#num#num)option`; `c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_clock_fupd (K (MustTerminate_limit (:A))) (s:(C,FFI)data_state)`;
    `tm:(A,C,FFI)wl_state`;
    `locs:(num#num)list`; `[k2;k1]:num list`; `[r2;r1]:data_v list`;
    `[w2;w1]:(A word_loc)list`; `ns:num_set`; `mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))`;
    `(y1,y2):((A)word_loc)spt#((A)word_loc)spt`; `n:num`; `l:num`;
    `lookup Append_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`] state_rel_call_env_push_env) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; MAP; get_vars_SOME_IFF; get_vars_SOME_IFF_data;
                    wl_get_var_def] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC]) THEN
  (ABBREV_TAC `ts = data_call_env [r2; r1]
      (lookup Append_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
      (data_push_env (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))) F
        (data_dec_clock (data_state_clock_fupd (K (MustTerminate_limit (:A))) s)))` THEN
  ABBREV_TAC `s_pop = data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))))
      (data_state_stack_fupd (K (data_state_stack s))
        (data_state_locals_size_fupd (K (data_state_locals_size s)) (ts:(C,FFI)data_state)))` THEN
  SUBGOAL_THEN `data_pop_env (ts:(C,FFI)data_state) = SOME s_pop /\ is_env (HD (data_state_stack ts)) /\
                data_state_tstamps (s_pop:(C,FFI)data_state) = data_state_tstamps (s:(C,FFI)data_state) /\
                data_state_stack_max s_pop = data_state_stack_max ts /\
                data_state_limits ts = data_state_limits s /\
                data_state_refs ts = data_state_refs s /\
                data_state_stack ts = CONS (data_Env (data_state_locals_size s) (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack s)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; data_pop_env_def; is_env_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; HD] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `data_get_vars [0; 1] (data_state_locals (ts:(C,FFI)data_state)) = SOME [r2; r1] /\
                data_state_locals_size ts = lookup Append_location (data_state_stack_frame_sizes ts)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; data_get_vars_def; data_get_var_def; lookup_fromList] THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL; ONE] THEN CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r1:data_v`; `r2:data_v`;
    `data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s`;
    `s_pop:(C,FFI)data_state`; `v:data_v`; `s2:(C,FFI)data_state`] ASP3AUX_do_app_ListAppend_same_v) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `s2i:(C,FFI)data_state`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP do_app_stack_max o
    check (fun th -> free_in `s2i:(C,FFI)data_state` (concl th)))) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `n:num`; `l:num`; `ts:(C,FFI)data_state`;
    `wl_call_env [wl_Loc n l; w2; w1]
       (lookup Append_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
       (wl_push_env (y1,y2) NONE (wl_dec_clock (tm:(A,C,FFI)wl_state)))`;
    `CONS (l1:num,l2:num) locs`; `r1:data_v`; `r2:data_v`;
    `s_pop:(C,FFI)data_state`; `v:data_v`; `s2i:(C,FFI)data_state`; `l1:num`; `l2:num`; `a:A word`]
    ASP3AUX_Append_thm) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[ASP3AUX_call_env_push_env_fields; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
      FIRST_X_ASSUM(let qtm = `data_state_stack_max (s_pop:(C,FFI)data_state) = data_state_stack_max (ts:(C,FFI)data_state)` in fun th -> if concl th = qtm
        then REWRITE_TAC[GSYM th] else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `rr:(A,C,FFI)wl_state`
    (X_CHOOSE_THEN `new_c:num` (CONJUNCTS_THEN2 (fun th -> ASP3AUX_HIDE_TAC th THEN SUBST1_TAC th) MP_TAC)))) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `q:((A)wl_result)option = SOME NotEnoughSpace` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[distinctness "wl_result"; option_DISTINCT; injectivity "wl_result"]) THENL
   [(STRIP_TAC THEN EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
  EXISTS_TAC `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state)))
     (wl_state_termdep_fupd (K (wl_state_termdep t)) (rr:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `wl_state_ffi (rr:(A,C,FFI)wl_state)`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[ASP3AUX_call_env_push_env_fields; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `data_state_stack_frame_sizes (s_pop:(C,FFI)data_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                data_state_limits s_pop = data_state_limits s /\ data_state_stack s_pop = data_state_stack s /\
                data_state_locals_size s_pop = data_state_locals_size s /\
                data_state_refs s_pop = data_state_refs s /\ data_state_global s_pop = data_state_global s /\
                data_state_locals s_pop = mk_wf (inter (data_state_locals s) (ns:num_set)) /\
                data_state_ffi s_pop = data_state_ffi s /\ data_state_handler s_pop = data_state_handler s /\
                data_state_code s_pop = data_state_code s /\ data_state_compile s_pop = data_state_compile s /\
                data_state_compile_oracle s_pop = data_state_compile_oracle s /\
                data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max s)
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup Append_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[ASP3AUX_cpd_stack_max] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && free_in `s2i:(C,FFI)data_state` (concl th) &&
      ASP3AUX_is_app "data_do_app" (lhs (concl th)) then
      STRIP_ASSUME_TAC (MATCH_MP ASP3AUX_do_app_ListAppend th) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
     (can (find_term ((=) `s2i:(C,FFI)data_state`)) (concl th) || is_eq (fst (dest_conj (concl th))))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `r1:data_v = x1` ||
     concl th = `r2:data_v = x2`))) THEN
  ALL_TAC) THEN
  (CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `data_state_stack_max (s2i:(C,FFI)data_state)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `data_state_stack_max (s2i:(C,FFI)data_state)`
        then REWRITE_TAC[th] else NO_TAC) THEN
      (fun (asl,w) ->
         let sp = `s_pop:(C,FFI)data_state` in
         let spf = mapfilter (fun (_,th) -> let c = concl th in
            if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
         REWRITE_TAC spf (asl,w)) THEN
      ASM_REWRITE_TAC[ASP3AUX_stackmax_bridge]];
    ALL_TAC]) THEN
  (DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp (concl th) && lhand (concl th) = `data_state_safe_for_space (s2:(C,FFI)data_state)`
    then MP_TAC (MP th (ASSUME `data_state_safe_for_space (s2:(C,FFI)data_state)`)) else NO_TAC) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_conj (lhand (concl th)) &&
      can (find_term ((=) `s_pop:(C,FFI)data_state`)) (concl th) && is_forall (rand (concl th)) &&
      can (find_term (ASP3AUX_is_app "size_of_heap_args")) (concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `in1:data_v list`) THEN
  (fun (asl,w) ->
     let sp = `s_pop:(C,FFI)data_state` in
     let spf = mapfilter (fun (_,th) -> let c = concl th in
        if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
     REWRITE_TAC spf (asl,w)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `size_of_heap_args [r1; r2] (s_pop:(C,FFI)data_state) =
                size_of_heap_args [r1; r2]
                  (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s)`
    SUBST1_TAC THENL
   [REWRITE_TAC[size_of_heap_args_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM] THEN
    (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       REWRITE_TAC spf (asl,w)); ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<=" (concl th) &&
     can (find_term (ASP3AUX_is_app "size_of_heap_args")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<" (concl th) &&
     can (find_term (ASP3AUX_is_app "EXP")) (concl th) && free_in `in1:data_v list` (concl th))) THEN
  REWRITE_TAC[ASSUME `arch_size (data_state_limits (s:(C,FFI)data_state)) = dimindex (:A)`] THEN
  ARITH_TAC);
    (DISCH_THEN(X_CHOOSE_THEN `rv:A word_loc` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  CASE_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) THEN
  (ASP3AUX_ABBREV_ALL_TAC `Sd = data_state_locals_fupd (K LN) (data_state_locals_size_fupd (K (SOME 0))
      (data_state_clock_fupd (K new_c) (data_state_stack_fupd
        (K (CONS (data_Env (data_state_locals_size (s:(C,FFI)data_state))
                   (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack s)))
        (s2i:(C,FFI)data_state))))`) THEN
  (SUBGOAL_THEN `data_pop_env (Sd:(C,FFI)data_state) = SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) Sd)))` ASSUME_TAC THENL
   [EXPAND_TAC "Sd" THEN REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN CASE_REWRITE_TAC[]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) && free_in `rr:(A,C,FFI)wl_state` (concl th) then
      MP_TAC(SPEC `dest:num` (MATCH_MP state_rel_pop_env_set_var_IMP (CONJ th (ASSUME `data_pop_env (Sd:(C,FFI)data_state) = SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) Sd)))`)))) else NO_TAC)) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num` (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[CONS_11; PAIR_EQ]) ASSUME_TAC)))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) (SUBST_ALL_TAC o SYM))) THEN
  (REWRITE_TAC[ASSUME `wl_pop_env (rr:(A,C,FFI)wl_state) = SOME t2`] THEN CASE_REWRITE_TAC[]) THEN
  (ASP3AUX_UNHIDE_THEN(MP_TAC o REWRITE_RULE[SYM(ASSUME `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
     (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state)) = tm`); ASP3AUX_cpd_lift])) THEN
  (DISCH_TAC THEN
  SUBGOAL_THEN `lookup 0 (y1:(A word_loc)spt) = SOME (wl_Loc l1 l2)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) && free_in `y1:(A word_loc)spt` (concl th)
      then MATCH_ACCEPT_TAC(MATCH_MP state_rel_push_env_loc th) else NO_TAC); ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_eq (concl th) && ASP3AUX_is_app "wl_evaluate" (lhs (concl th)) && free_in `rr:(A,C,FFI)wl_state` (concl th) then
     MP_TAC(MATCH_MP evaluate_IMP_domain_union (CONJ th (CONJ (ASSUME `wl_pop_env (rr:(A,C,FFI)wl_state) = SOME t2`)
       (CONJ (ASSUME `lookup 0 (y1:(A word_loc)spt) = SOME (wl_Loc l1 l2)`)
             (ASSUME `cut_envs (adjust_sets (ns:num_set)) (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (y1,y2)`))))) else NO_TAC) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[ASP3AUX_ev_Skip] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`;
     `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state))) (wl_state_termdep_fupd (K (wl_state_termdep t)) (wl_set_vars [adjust_var dest] [rv] (t2:(A,C,FFI)wl_state)))`] THEN
  REWRITE_TAC[option_DISTINCT]) THEN
  (SUBGOAL_THEN `data_state_stack_frame_sizes (s_pop:(C,FFI)data_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                data_state_limits s_pop = data_state_limits s /\ data_state_stack s_pop = data_state_stack s /\
                data_state_locals_size s_pop = data_state_locals_size s /\
                data_state_refs s_pop = data_state_refs s /\ data_state_global s_pop = data_state_global s /\
                data_state_locals s_pop = mk_wf (inter (data_state_locals s) (ns:num_set)) /\
                data_state_ffi s_pop = data_state_ffi s /\ data_state_handler s_pop = data_state_handler s /\
                data_state_code s_pop = data_state_code s /\ data_state_compile s_pop = data_state_compile s /\
                data_state_compile_oracle s_pop = data_state_compile_oracle s /\
                data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max s)
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup Append_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[ASP3AUX_cpd_stack_max] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && free_in `s2i:(C,FFI)data_state` (concl th) &&
      ASP3AUX_is_app "data_do_app" (lhs (concl th)) then
      STRIP_ASSUME_TAC (MATCH_MP ASP3AUX_do_app_ListAppend th) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
     (can (find_term ((=) `s2i:(C,FFI)data_state`)) (concl th) || is_eq (fst (dest_conj (concl th))))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `r1:data_v = x1` ||
     concl th = `r2:data_v = x2`))) THEN
  ALL_TAC) THEN
  (SUBGOAL_THEN `wl_state_clock (t:(A,C,FFI)wl_state) = data_state_clock (s:(C,FFI)data_state)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP state_rel_IMP_tstamps (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `ts0:num`) ) THEN
  (SUBGOAL_THEN `xs:data_v list = in1` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `data_v_to_list r1 = SOME (in1:data_v list)` THEN
    UNDISCH_TAC `data_v_to_list r1 = SOME (xs:data_v list)` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ]; ALL_TAC]) THEN
  (SUBGOAL_THEN `data_state_tstamps (s2:(C,FFI)data_state) = SOME (ts0 + LENGTH (in1:data_v list)) /\
                data_state_tstamps (s2i:(C,FFI)data_state) = SOME (ts0 + LENGTH in1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [(FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term (ASP3AUX_is_app "data_list_to_v")) (concl th) &&
       can (find_term ((=) `data_state_tstamps (s2:(C,FFI)data_state)`)) (concl th)
       then MP_TAC (SPEC `ts0:num` th) else NO_TAC) THEN
     REWRITE_TAC[ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts0`;
                 ASSUME `data_state_tstamps (s_pop:(C,FFI)data_state) = data_state_tstamps (s:(C,FFI)data_state)`] THEN
     SIMP_TAC[]);
     (FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term (ASP3AUX_is_app "data_list_to_v")) (concl th) &&
       can (find_term ((=) `data_state_tstamps (s2i:(C,FFI)data_state)`)) (concl th)
       then MP_TAC (SPEC `ts0:num` th) else NO_TAC) THEN
     REWRITE_TAC[ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts0`;
                 ASSUME `data_state_tstamps (s_pop:(C,FFI)data_state) = data_state_tstamps (s:(C,FFI)data_state)`] THEN
     SIMP_TAC[])];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `data_state_stack_max (s2i:(C,FFI)data_state)`
      then REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `data_state_stack_max (s2:(C,FFI)data_state)`
      then REWRITE_TAC[th] else NO_TAC) THEN
    (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       REWRITE_TAC spf (asl,w)) THEN
    ASM_REWRITE_TAC[ASP3AUX_stackmax_bridge]; ALL_TAC]) THEN
  (MATCH_MP_TAC ASP3AUX_state_rel_upd THEN
  EXISTS_TAC `data_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state))) (data_set_var (dest:num) (v:data_v) (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) (Sd:(C,FFI)data_state)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_state_rel_with_clock THEN
    REWRITE_TAC[ASP3AUX_state_rel_termdep; data_to_word_gcProof_set_vars_sing] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC]) THEN
  ((fun (asl,w) ->
     let sp = `s_pop:(C,FFI)data_state` in
     let s2v = `s2:(C,FFI)data_state` in
     let s2iv = `s2i:(C,FFI)data_state` in
     let pick v = mapfilter (fun (_,th) -> let c = concl th in
        if is_eq c && is_comb (lhs c) && rand (lhs c) = v then th else failwith "") asl in
     (REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
      EXPAND_TAC "Sd" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
      REWRITE_TAC(pick s2v @ pick s2iv @ pick sp @
        [ASSUME `wl_state_clock (t:(A,C,FFI)wl_state) = data_state_clock (s:(C,FFI)data_state)`;
         ASSUME `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`]))
     (asl,w)))]]);;

(* HOL4 line 6297 *)
let do_app_AllocThunk = prove
 (CASE_TERM
  `!m v (x:(C,FFI)data_state).
     data_do_app (clos_ThunkOp (AllocThunk m)) [v] x =
     match consume_space (1 + 1) x with
       NONE -> Rerr (Rabort Rtype_error)
     | SOME s1 ->
         if data_bad_thunk_update m v (data_state_refs s1) then Rerr (Rabort Rtype_error)
         else
         Rval
          (data_RefPtr F (minimal ptr. ~(ptr IN domain (data_state_refs s1))),
           data_state_refs_fupd
             (K (insert (minimal ptr. ~(ptr IN domain (data_state_refs s1)))
                   (bvl_Thunk m v) (data_state_refs s1)))
             (data_state_safe_for_space_fupd
                (K (data_state_safe_for_space
                      (do_stack (clos_ThunkOp (AllocThunk m)) [v]
                         (do_lim_safe s1 (clos_ThunkOp (AllocThunk m)) [v]))))
                (data_state_stack_max_fupd
                   (K (data_state_stack_max
                         (do_stack (clos_ThunkOp (AllocThunk m)) [v]
                            (do_lim_safe s1 (clos_ThunkOp (AllocThunk m)) [v]))))
                   s1)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; op_space_req_def] THEN
  SIMP[MEM; LENGTH] THEN
  CASES_ON `consume_space 2 (x:(C,FFI)data_state)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[do_stack_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[]);;

(* HOL4 line 6319 *)
let assign_AllocThunk = prove
 (assign_thm_stmt `(?ev. op = clos_ThunkOp (AllocThunk ev))`,
  (REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `ev:thunk_mode` SUBST_ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `names_opt:num_set option = NONE` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `~(op_requires_names (clos_ThunkOp (AllocThunk ev)) <=>
                   names_opt:num_set option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def; distinctness "clos_op"];
    ALL_TAC] THEN
  UNDISCH_TAC `data_cut_state_opt NONE s = SOME (x:(C,FFI)data_state)` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `data_do_app (clos_ThunkOp (AllocThunk ev)) vals (s:(C,FFI)data_state) =
                Rval (v,s2)` THEN
  ASP3AUX_DO_APP_SPLIT_TAC) THEN
  (REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[LENGTH; ONE; ADD_CLAUSES; NOT_SUC]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN RVEQ_TAC) THEN
  (FIRST_ASSUM(X_CHOOSE_THEN `v1:num` STRIP_ASSUME_TAC o MATCH_MP ASP3AUX_get_vars_1) THEN RVEQ_TAC THEN
  IMP_RES_TAC state_rel_get_vars_IMP THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` SUBST_ALL_TAC o REWRITE_RULE[ASP3AUX_LENGTH_EQ_1])) THEN
  (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_AllocThunk_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV)) THEN
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME
    `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state)
       NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_memory_rel (ASSUME
    `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state)
       NONE locs`)) THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN REWRITE_TAC[ZIP; HD; TL; APPEND] THEN DISCH_TAC) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`;
     CASE_TERM `match (ev:thunk_mode) with Evaluated -> 14 | NotEvaluated -> 6`; `1`]
     (INST_TYPE [`:A`,`:A`] ASP3AUX_encode_header_small)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CASES_ON `ev:thunk_mode` THEN CASE_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hdr:A word` ASSUME_TAC)) THEN
  (SUBGOAL_THEN (CASE_TERM `encode_header c (match (ev:thunk_mode) with Evaluated -> 8 + 6 | NotEvaluated -> 0 + 6) 1 = SOME (hdr:A word)`) (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o check (ASP3AUX_is_app "encode_header" o lhs o concl)) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[]) THEN
  (MP_TAC(ISPEC `data_state_refs (s:(C,FFI)data_state)` LEAST_NOTIN_spt_DOMAIN) THEN DISCH_TAC THEN
  SUBGOAL_THEN `ev = Evaluated ==> data_dest_thunk a0 (data_state_refs (s:(C,FFI)data_state)) = data_NotThunk` ASSUME_TAC THENL
   [UNDISCH_TAC `~data_bad_thunk_update ev a0 (data_state_refs (s:(C,FFI)data_state))` THEN
    REWRITE_TAC[data_bad_thunk_update_def] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= data_state_space (s:(C,FFI)data_state)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  (DRULE_ALL memory_rel_AllocThunk THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `eoh:A word` (X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `trig:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))))) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def]) THEN SIMP (FLOOKUP_UPDATE :: data_to_word_Unit_def :: ASP3AUX_EV_THMS)) THEN
  (ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (StoreEach 1 [3; adjust_var v1] (word 0), t5:(A,C,FFI)wl_state)` `t5:(A,C,FFI)wl_state`) THEN
  (MP_TAC(ISPECL [`[3; adjust_var v1]`; `[wl_Word hdr; w1:A word_loc]`; `t5:(A,C,FFI)wl_state`;
    `m1:A word->A word_loc`; `word_sub eoh (word_mul bytes_in_word (word 2)):A word`; `1`]
    evaluate_StoreEach) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t5" THEN SIMP[wl_get_vars_def; wl_get_var_def; lookup_insert] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC]) THEN
  (SUBGOAL_THEN `(shift_length c - backend_common_word_shift (:A)) MOD dimword (:A) =
                shift_length c - backend_common_word_shift (:A) /\
                ~(shift_length c - backend_common_word_shift (:A) >= dimindex (:A))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC MOD_LT; ALL_TAC] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (ASP3AUX_UNABBREV_TAC `t5:(A,C,FFI)wl_state` THEN
  SIMP (FLOOKUP_UPDATE :: word_sh_def :: WORD_OR_0 :: data_to_word_Unit_def :: ASP3AUX_EV_THMS)) THEN
  (SUBGOAL_THEN `!(st:(store_name,A word_loc)fmap) v1 v2.
    st |+ (TriggerGC,v1) |+ (EndOfHeap,v2) = st |+ (EndOfHeap,v2) |+ (TriggerGC,v1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC FUPDATE_COMMUTES THEN REWRITE_TAC[distinctness "store_name"];
    ALL_TAC]) THEN
  (FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  FS[option_le_max_right; lookup_insert; adjust_var_11; code_oracle_rel_def; FLOOKUP_UPDATE;
     FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM]) THEN
  (REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP[inter_insert_ODD_adjust_set] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[make_ptr_def] o
    check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
                     can (find_term (ASP3AUX_is_app "bvl_Thunk")) (concl th))) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]));;

(* HOL4 line 6402 *)
let assign_UpdateThunk = prove
 (assign_thm_stmt `(?ev. op = clos_ThunkOp (UpdateThunk ev))`,
  let finish_tac =
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
      check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
    FS[option_le_max_right; lookup_insert; adjust_var_11] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SIMP[inter_insert_ODD_adjust_set] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
    MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[UPDATE_LIST_THM; FST; SND] o
      check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
                       can (find_term (ASP3AUX_is_app "bvl_Thunk")) (concl th))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[] in
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `ev:thunk_mode` SUBST_ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `names_opt:num_set option = NONE` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `~(op_requires_names (clos_ThunkOp (UpdateThunk ev)) <=>
                   names_opt:num_set option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def; distinctness "clos_op"];
    ALL_TAC] THEN
  UNDISCH_TAC `data_cut_state_opt NONE s = SOME (x:(C,FFI)data_state)` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `data_do_app (clos_ThunkOp (UpdateThunk ev)) vals (s:(C,FFI)data_state) =
                Rval (v,s2)` THEN
  ASP3AUX_DO_APP_SPLIT_TAC THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o EQF_INTRO o
    check (fun th -> is_neg (concl th) && is_var (rand (concl th)))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v1:num` (X_CHOOSE_THEN `v2:num` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_get_vars_2) THEN RVEQ_TAC THEN
  IMP_RES_TAC state_rel_get_vars_IMP THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2]) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_UpdateThunk_def] THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME
    `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state)
       NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_memory_rel (ASSUME
    `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state)
       NONE locs`)) THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN REWRITE_TAC[ZIP; HD; TL; APPEND] THEN DISCH_TAC THEN
  DRULE reorder_2_lemma THEN DISCH_TAC THEN
  CASES_ON `ev:thunk_mode` THEN CASE_REWRITE_TAC[] THENL
  [(* Evaluated *)
   MP_TAC(ISPECL [`c:data_to_word_config`; `8 + 6`; `1`]
     (INST_TYPE [`:A`,`:A`] ASP3AUX_encode_header_small)) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `hdr:A word` ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `data_dest_thunk a0'' (data_state_refs (s:(C,FFI)data_state)) =
                 data_NotThunk` ASSUME_TAC THENL
    [UNDISCH_TAC `~data_bad_thunk_update Evaluated a0''
                    (data_state_refs (s:(C,FFI)data_state))` THEN
     REWRITE_TAC[data_bad_thunk_update_def]; ALL_TAC] THEN
   DRULE_ALL memory_rel_UpdateThunk_Evaluated THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `xa:A word` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_vars_2_IMP o REWRITE_RULE[MAP] o
     check (fun th -> can (term_match [] `wl_get_vars xs (t:(A,C,FFI)wl_state) = SOME ys`)
                        (concl th))) THEN
   SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var v1)) =
                 SOME (wl_Word xa)` ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   SIMP (data_to_word_Unit_def :: ASP3AUX_EV_THMS) THEN
   finish_tac;
   (* NotEvaluated *)
   DRULE_ALL memory_rel_UpdateThunk_NotEvaluated THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `xa:A word` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_vars_2_IMP o REWRITE_RULE[MAP] o
     check (fun th -> can (term_match [] `wl_get_vars xs (t:(A,C,FFI)wl_state) = SOME ys`)
                        (concl th))) THEN
   SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var v1)) =
                 SOME (wl_Word xa)` ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   SIMP (data_to_word_Unit_def :: ASP3AUX_EV_THMS) THEN
   finish_tac]);;

(* HOL4 line 6472 *)
let configGC_size_of_heap_LE = prove
 (`!ns (s:(A,B)data_state) x k1 k2 i1 i2 (state:(A,B)data_state).
     data_cut_state_opt (SOME (insert k2 one (insert k1 one ns))) s = SOME x /\
     lookup k1 (data_state_locals x) = SOME (data_Number i1) /\
     lookup k2 (data_state_locals x) = SOME (data_Number i2) /\
     data_state_refs state = data_state_refs s /\
     data_state_limits state = data_state_limits s /\
     data_state_stack state = data_state_stack s /\
     data_state_global state = data_state_global s ==>
     size_of_heap (data_state_locals_fupd (K (mk_wf (inter (data_state_locals s) ns)))
                     state) <=
     size_of_heap (data_state_locals_fupd (K (data_state_locals x)) state)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_cut_env_def] THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[wf_inter; wf_mk_id] THEN
  RULE_ASSUM_TAC(SIMP_RULE[wf_inter; wf_mk_id]) THEN
  SUBGOAL_THEN
   `ITLIST delete (FILTER (\a. lookup a (ns:1 spt) = NONE) [k1;k2])
      (inter (data_state_locals (s:(A,B)data_state)) (insert k2 one (insert k1 one ns))) =
    inter (data_state_locals s) ns` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC(MESON[spt_eq_thm]
      `wf (a:A spt) /\ wf b /\ (!n. lookup n a = lookup n b) ==> a = b`) THEN
    SIMP_TAC[wf_FOLDR_delete; wf_inter] THEN
    REWRITE_TAC[data_to_word_assignProof_lookup_FOLDR_delete; lookup_inter; lookup_insert;
                MEM_FILTER; MEM] THEN
    GEN_TAC THEN CASES_ON `lookup n (ns:1 spt)` THEN
    CASES_ON `lookup n (data_state_locals (s:(A,B)data_state))` THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC size_of_heap_FOLDR_delete_Number_LE THEN REWRITE_TAC[wf_inter] THEN
    REWRITE_TAC[MEM_FILTER; MEM] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]]);;

(* HOL4 line 6513 *)
let cut_state_opt_IMP_cut_locals = prove
 (`!ns (s:(C,FFI)data_state) x.
     data_cut_state_opt (SOME ns) s = SOME x ==> cut_locals ns s = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; cut_locals_def] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `data_cut_env ns (data_state_locals (s:(C,FFI)data_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ]);;

(* HOL4 line 6520 *)
let assign_ConfigGC = prove
 (assign_thm_stmt `op = MemOp clos_ConfigGC`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ns. names_opt = SOME (ns:num_set)` (X_CHOOSE_THEN `ns:num_set` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (MemOp clos_ConfigGC) <=> names_opt:num_set option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:num_set option` THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `data_do_app (MemOp clos_ConfigGC) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  ASP3AUX_DO_APP_SPLIT_TAC) THEN
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_get_vars_2) THEN RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_ConfigGC_def; data_to_word_get_names_def; data_to_word_list_Seq_def]) THEN
  (DRULE_ALL state_rel_cut_IMP THEN DISCH_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP cut_state_opt_IMP_cut_locals) THEN DISCH_TAC) THEN
  (UNDISCH_TAC `data_cut_state_opt (SOME ns) s = SOME (x:(C,FFI)data_state)` THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `data_cut_env ns (data_state_locals (s:(C,FFI)data_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM])) THEN
  ASM_CASES_TAC `data_to_word_config_call_empty_ffi c` THENL
  [(* call_empty_ffi: SilentFFI calls the empty FFI *)
   (FIRST_ASSUM(MP_TAC o MATCH_MP cut_env_IMP_cut_env o CONJ (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` ASSUME_TAC)) THEN
   (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `ns:num_set`; `y:(A word_loc)spt`] evaluate_SilentFFI_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
   (REWRITE_TAC[ASP3AUX_wl_fupd_id] THEN
  REWRITE_TAC[ASP3AUX_ev_Seq; ASP3AUX_ev_Assign; wl_word_exp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ASP3AUX_ev_Alloc; wl_get_var_def; wl_set_var_def] THEN
  SIMP[lookup_insert] THEN REWRITE_TAC[GSYM wl_set_var_def]) THEN
   (ABBREV_TAC `t1 = wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state))` THEN
  SUBGOAL_THEN `wl_alloc (word 0) (adjust_sets (ns:num_set))
       (wl_state_locals_fupd (K (insert 1 (wl_Word (word 0)) y)) (wl_state_fp_regs_fupd (K FEMPTY) t)) =
     wl_alloc (word 0) (adjust_sets ns) (t1:(A,C,FFI)wl_state)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word 0:A word`; `ns:num_set`; `wl_Word (word 0):A word_loc`; `t1:(A,C,FFI)wl_state`]
      alloc_locals_insert_1) THEN EXPAND_TAC "t1" THEN SIMP[]; ALL_TAC]) THEN
   (SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (K a'') (s:(C,FFI)data_state)) (t1:(A,C,FFI)wl_state) NONE locs` ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `ns:num_set`; `a'':data_v spt`; `y:(A word_loc)spt`]
      state_rel_cut_env_cut_env) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `FEMPTY:(num,(64)word)fmap` o
      MATCH_MP state_rel_with_fp_regs) THEN
    SIMP[]; ALL_TAC]) THEN
   (FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_env_idempotent o
    check (fun th -> is_eq (concl th) && ASP3AUX_is_app "data_cut_env" (lhs (concl th)))) THEN
  MP_TAC(ISPEC `wl_alloc (word 0) (adjust_sets (ns:num_set)) (t1:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:((A)wl_result)option` (X_CHOOSE_THEN `r1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_locals_fupd (K a'') (s:(C,FFI)data_state)`;
    `t1:(A,C,FFI)wl_state`; `locs:(num#num)list`; `ns:num_set`; `a'':data_v spt`; `0`;
    `q1:((A)wl_result)option`; `r1:(A,C,FFI)wl_state`] alloc_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[alloc_size_def; MULT_CLAUSES; ZERO_LT_dimword; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  STRIP_TAC) THEN
   ASM_CASES_TAC `q1:((A)wl_result)option = SOME NotEnoughSpace` THENL
   [(FIRST_X_ASSUM(fun th -> if is_imp (concl th) && not (is_neg (lhand (concl th))) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; cut_locals_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_state_INFO.ri_fupdfupds; ASP3AUX_K_o] THEN STRIP_TAC THEN
  EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN EXISTS_TAC `r1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[option_le_max_right] THEN
  MP_TAC(REWRITE_RULE[data_to_word_gcProof_state_rel_thm] (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_CASES_TAC `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_conj (lhand (concl th)))) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`[data_Number a; data_Number a']`; `data_state_locals_fupd (K a'') (s:(C,FFI)data_state)`]
    size_of_heap_LE_args) THEN
  REWRITE_TAC[space_consumed_def] THEN CASE_REWRITE_TAC[] THEN ARITH_TAC);
    (FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_neg (lhand (concl th)) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `s3 = data_state_locals_fupd (K a'') (data_state_space_fupd (K 0) (data_state_locals_fupd (K a'') (s:(C,FFI)data_state)))` THEN
  SUBGOAL_THEN `data_cut_env ns (data_state_locals (s3:(C,FFI)data_state)) = SOME a''` ASSUME_TAC THENL
   [EXPAND_TAC "s3" THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP cut_env_IMP_cut_env o CONJ (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s3:(C,FFI)data_state) (r1:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y':(A word_loc)spt` ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s3:(C,FFI)data_state`;
    `r1:(A,C,FFI)wl_state`; `locs:(num#num)list`; `ns:num_set`; `y':(A word_loc)spt`] evaluate_SilentFFI_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ASP3AUX_wl_fupd_id] THEN
  EXISTS_TAC `NONE:((A)wl_result)option` THEN
  EXISTS_TAC `wl_set_var (adjust_var dest) (wl_Word (word 2))
     (wl_state_locals_fupd (K y') (wl_state_fp_regs_fupd (K FEMPTY) (r1:(A,C,FFI)wl_state)))` THEN
  REWRITE_TAC[option_DISTINCT] THEN
  MATCH_MP_TAC ASP3AUX_state_rel_set_var_Unit THEN MATCH_MP_TAC ASP3AUX_state_rel_upd THEN
  EXISTS_TAC `data_state_locals_fupd (K a'') (s3:(C,FFI)data_state)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s3:(C,FFI)data_state`;
      `r1:(A,C,FFI)wl_state`; `locs:(num#num)list`; `ns:num_set`; `a'':data_v spt`; `y':(A word_loc)spt`]
      state_rel_cut_env_cut_env) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `FEMPTY:(num,(64)word)fmap` o MATCH_MP state_rel_with_fp_regs) THEN
    SIMP[];
    EXPAND_TAC "s3" THEN SIMP[option_le_max_right]])];
   (* no call_empty_ffi: SilentFFI is Skip *)
   (ASM_REWRITE_TAC[SilentFFI_def] THEN REWRITE_TAC[ASP3AUX_ev_Seq; ASP3AUX_ev_Skip; ASP3AUX_ev_Assign] THEN
  CASE_REWRITE_TAC[wl_word_exp_def; option_DISTINCT] THEN REWRITE_TAC[ASP3AUX_ev_Alloc; wl_get_var_def; wl_set_var_def] THEN
  SIMP[lookup_insert] THEN REWRITE_TAC[GSYM wl_set_var_def]) THEN
   (SUBGOAL_THEN `wl_alloc (word 0) (adjust_sets (ns:num_set)) (wl_set_var 1 (wl_Word (word 0)) t) =
                wl_alloc (word 0) (adjust_sets ns) (t:(A,C,FFI)wl_state)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_set_var_def; alloc_locals_insert_1]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_alloc (word 0) (adjust_sets (ns:num_set)) (t:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:((A)wl_result)option` (X_CHOOSE_THEN `r1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `ns:num_set`; `a'':data_v spt`; `0`;
    `q1:((A)wl_result)option`; `r1:(A,C,FFI)wl_state`] alloc_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[alloc_size_def; MULT_CLAUSES; ZERO_LT_dimword]; ALL_TAC] THEN
  STRIP_TAC) THEN
   ASM_CASES_TAC `q1:((A)wl_result)option = SOME NotEnoughSpace` THENL
   [(FIRST_X_ASSUM(fun th -> if is_imp (concl th) && not (is_neg (lhand (concl th))) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN EXISTS_TAC `r1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[option_le_max_right] THEN
  MP_TAC(REWRITE_RULE[data_to_word_gcProof_state_rel_thm] (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[]) THEN
    (STRIP_TAC THEN ASM_CASES_TAC `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_conj (lhand (concl th)))) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`[data_Number a; data_Number a']`; `data_state_locals_fupd (K a'') (s:(C,FFI)data_state)`]
    size_of_heap_LE_args) THEN
  REWRITE_TAC[space_consumed_def] THEN CASE_REWRITE_TAC[] THEN ARITH_TAC);
    (FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_neg (lhand (concl th)) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `NONE:((A)wl_result)option` THEN
  EXISTS_TAC `wl_set_var (adjust_var dest) (wl_Word (word 2)) (r1:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[option_DISTINCT] THEN
  MATCH_MP_TAC ASP3AUX_state_rel_set_var_Unit THEN MATCH_MP_TAC ASP3AUX_state_rel_upd THEN
  EXISTS_TAC `data_state_locals_fupd (K a'') (data_state_space_fupd (K 0) (s:(C,FFI)data_state))` THEN
  ASM_REWRITE_TAC[] THEN SIMP[option_le_max_right])]]);;

(* HOL4 line 6703 *)
let assign_WordToInt = prove
 (assign_thm_stmt `op = WordOp WordToInt`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `names_opt:num_set option = NONE` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `~(op_requires_names (WordOp WordToInt) <=> names_opt:num_set option = NONE)` THEN
    REWRITE_TAC(op_requires_names_def::op_space_reset_def::ASP3AUX_DO_APP_RWS) THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[data_cut_state_opt_def; option_INJ]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `s:(C,FFI)data_state = x` o concl)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:int64` STRIP_ASSUME_TAC o MATCH_MP ASP3AUX_do_app_WordToInt) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k1:num` STRIP_ASSUME_TAC o MATCH_MP ASP3AUX_get_vars_1) THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`[k1]:num list`; `[data_Word64 w]`; `c:data_to_word_config`; `l1:num`; `l2:num`;
    `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `SUC 0 = LENGTH (ws:(A word_loc)list)` o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` SUBST_ALL_TAC o REWRITE_RULE[ASP3AUX_LENGTH_EQ_1] o SYM) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_WordToInt_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV)) THEN
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_limits (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_memory_rel (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP memory_rel_get_vars_IMP (CONJ th (CONJ
     (ASSUME `data_get_vars [k1] (data_state_locals (s:(C,FFI)data_state)) = SOME [data_Word64 w]`)
     (ASSUME `wl_get_vars (MAP adjust_var [k1]) (t:(A,C,FFI)wl_state) = SOME [w1:A word_loc]`))))) THEN
  REWRITE_TAC[ZIP; APPEND] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Word64_IMP) o
    check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `data_Word64 w`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `xa:A word` (X_CHOOSE_THEN `hw:A word` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `3`; `1`] (INST_TYPE [`:A`,`:A`] ASP3AUX_encode_header_small)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_TAC `h1:A word`)) THEN
  (ASM_CASES_TAC `dimindex (:A) < 64` THENL
   [SUBGOAL_THEN `dimindex (:A) = 32` ASSUME_TAC THENL
     [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      UNDISCH_TAC `dimindex (:A) < 64` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_cond (concl th) then
      STRIP_ASSUME_TAC (REWRITE_RULE[ASSUME `dimindex (:A) < 64`] th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[];
    SUBGOAL_THEN `dimindex (:A) = 64` ASSUME_TAC THENL
     [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      UNDISCH_TAC `~(dimindex (:A) < 64)` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_cond (concl th) then
      STRIP_ASSUME_TAC (REWRITE_RULE[ASSUME `~(dimindex (:A) < 64)`] th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[]]) THENL
  [(TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THENL
   [(MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] evaluate_GiveUp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
  EXISTS_TAC `r0:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `3`; `2`] (INST_TYPE [`:A`,`:A`] ASP3AUX_encode_header_small4)) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && lhand (concl th) = `data_state_safe_for_space (s2:(C,FFI)data_state)`)) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);
    (SUBGOAL_THEN `wl_get_var (adjust_var k1) (t:(A,C,FFI)wl_state) = SOME (w1:A word_loc)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_get_vars (MAP adjust_var [k1]) (t:(A,C,FFI)wl_state) = SOME [w1:A word_loc]` THEN
    REWRITE_TAC[MAP; get_vars_SOME_IFF] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var k1)) = SOME (wl_Word (xa:A word))` ASSUME_TAC THENL
   [MATCH_MP_TAC get_var_get_real_addr_lemma THEN EXISTS_TAC `get_addr c ptr (wl_Word (word 0)):A word` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN
  REWRITE_TAC ASP3AUX_EVX THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN
  REWRITE_TAC (GSYM ASP3AUX_shl1_mul2 :: ASP3AUX_EVX) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: ASP3AUX_EVX) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]))) THEN
  (REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: ASP3AUX_EVX) THEN CASE_REWRITE_TAC[])) THEN
  ABBREV_TAC `t3 = wl_state_locals_fupd (K (insert 11 (wl_Word (word_extract 31 0 (w:int64):A word)) (insert 13 (wl_Word (word_extract 63 32 w:A word)) (insert 15 (wl_Word (xa:A word)) (wl_state_locals t))))) (t:(A,C,FFI)wl_state)`) THEN
  (SUBGOAL_THEN `wl_state_store (t3:(A,C,FFI)wl_state) = wl_state_store (t:(A,C,FFI)wl_state) /\
     wl_state_memory t3 = wl_state_memory t /\ wl_state_mdomain t3 = wl_state_mdomain t /\
     wl_state_be t3 = wl_state_be t /\ wl_state_stack t3 = wl_state_stack t /\
     wl_state_stack_max t3 = wl_state_stack_max t /\ wl_state_ffi t3 = wl_state_ffi t /\
     wl_get_var 11 t3 = SOME (wl_Word (word_extract 31 0 (w:int64):A word)) /\
     wl_get_var 13 t3 = SOME (wl_Word (word_extract 63 32 w:A word)) /\
     join_env_locals (data_state_locals (s:(C,FFI)data_state)) (wl_state_locals t3) =
       join_env_locals (data_state_locals s) (wl_state_locals t) /\
     lookup 0 (wl_state_locals t3) = lookup 0 (wl_state_locals t) /\
     (!n. IS_SOME (lookup n (data_state_locals s)) ==> IS_SOME (lookup (adjust_var n) (wl_state_locals t3)))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t3" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def; lookup_insert] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[join_env_locals_insert_odd; ARITH_RULE `ODD 11 /\ ODD 13 /\ ODD 15`] THEN
    REWRITE_TAC[adjust_var_eq_numeral; ARITH] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; adjust_var_def] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (ASM_CASES_TAC `word_extract 63 32 (w:int64) = (word 0:A word)` THEN ASM_REWRITE_TAC[]) THENL
    [(MP_TAC(SPEC `w:int64` (INST_TYPE [`:A`,`:A`] ASP3AUX_w64_hi0)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN
  REWRITE_TAC (word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[]))) THEN
  (ASM_CASES_TAC `word_ushr (word_extract 31 0 (w:int64):A word) 29 = word 0` THEN ASM_REWRITE_TAC[]) THENL
     [(MP_TAC(SPEC `word_extract 31 0 (w:int64):A word` ASP3AUX_small_lo32) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ASP3AUX_ev_Assign] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[])) THEN
  EXPAND_TAC "t3" THEN REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o; wl_state_INFO.ri_accfupds; K_THM] THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`;
    `wl_state_locals_fupd (K (insert (adjust_var dest) (wl_Word (Smallnum (&(val (w:int64))):A word))
       (insert 1 (wl_Word (word_ushr (word_extract 31 0 w:A word) 29))
       (insert 11 (wl_Word (word_extract 31 0 w:A word)) (insert 13 (wl_Word (word_extract 63 32 w:A word))
       (insert 15 (wl_Word (xa:A word)) (wl_state_locals (t:(A,C,FFI)wl_state)))))))) t`] THEN
  REWRITE_TAC[option_DISTINCT] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (MATCH_MP_TAC ASP3AUX_state_rel_small_res THEN EXISTS_TAC `s:(C,FFI)data_state` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[join_env_locals_insert_odd; ARITH_RULE `ODD 1 /\ ODD 11 /\ ODD 13 /\ ODD 15`] THEN
  REWRITE_TAC[lookup_insert; adjust_var_eq_numeral; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]]);
      (EXPAND_TAC "t3" THEN REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o; wl_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word (word_ushr (word_extract 31 0 (w:int64):A word) 29))
       (insert 11 (wl_Word (word_extract 31 0 w:A word)) (insert 13 (wl_Word (word_extract 63 32 w:A word))
       (insert 15 (wl_Word (xa:A word)) (wl_state_locals (t:(A,C,FFI)wl_state))))))) t`;
    `data_state_locals (s:(C,FFI)data_state)`;
    `CONS (the_global (data_state_global (s:(C,FFI)data_state)),FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)
       (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
    `11`; `word_extract 31 0 (w:int64):A word`; `h1:A word`; `dest:num`] evaluate_WriteWord32_bignum) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def; lookup_insert] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[join_env_locals_insert_odd; ARITH_RULE `ODD 1 /\ ODD 11 /\ ODD 13 /\ ODD 15`] THEN
    REWRITE_TAC[adjust_var_eq_numeral; ARITH] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[join_env_locals_def] THEN
      MATCH_MP_TAC ASP3AUX_state_rel_memory_rel THEN ASM_MESON_TAC[];
      ASM_ARITH_TAC;
      MP_TAC(SPEC `word_extract 31 0 (w:int64):A word` ASP3AUX_not_small_lo32) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m':A word->A word_loc`
    (X_CHOOSE_THEN `locals':(A word_loc)spt` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH_EQ]) THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o; wl_state_INFO.ri_accfupds; K_THM] THEN
  EXISTS_TAC `NONE:((A)wl_result)option` THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `nf:A word_loc`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ASP3AUX_state_rel_big_res THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN EXISTS_TAC `data_state_space (s:(C,FFI)data_state) - 2` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)];
     (MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `t3:(A,C,FFI)wl_state`;
    `data_state_locals (s:(C,FFI)data_state)`;
    `CONS (the_global (data_state_global (s:(C,FFI)data_state)),FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)
       (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
    `11`; `13`; `word_extract 31 0 (w:int64):A word`; `word_extract 63 32 (w:int64):A word`;
    `a:A word`; `dest:num`] evaluate_WriteWord64_on_32_num) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[join_env_locals_def] THEN
      MATCH_MP_TAC ASP3AUX_state_rel_memory_rel THEN ASM_MESON_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m':A word->A word_loc`
    (X_CHOOSE_THEN `locals':(A word_loc)spt` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `w:int64` (INST_TYPE [`:A`,`:A`] ASP3AUX_w64_split32)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `nf:A word_loc`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXPAND_TAC "t3" THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o; wl_state_INFO.ri_accfupds; K_THM] THEN
  EXISTS_TAC `NONE:((A)wl_result)option` THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_DISTINCT] THEN
  MATCH_MP_TAC ASP3AUX_state_rel_big_res THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN EXISTS_TAC `data_state_space (s:(C,FFI)data_state) - 3` THEN
  ASM_REWRITE_TAC[LE_REFL])]];
   (SUBGOAL_THEN `wl_get_var (adjust_var k1) (t:(A,C,FFI)wl_state) = SOME (w1:A word_loc)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_get_vars (MAP adjust_var [k1]) (t:(A,C,FFI)wl_state) = SOME [w1:A word_loc]` THEN
    REWRITE_TAC[MAP; get_vars_SOME_IFF] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if ASP3AUX_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `data_Word64 w`)) (concl th) then
      MP_TAC(MATCH_MP evaluate_LoadWord64 (CONJ th (CONJ
        (ASSUME `shift_length c < dimindex (:A)`) (CONJ (ASSUME `dimindex (:A) = 64`)
        (ASSUME `wl_get_var (adjust_var k1) (t:(A,C,FFI)wl_state) = SOME (w1:A word_loc)`)))))
    else NO_TAC) THEN
  DISCH_THEN(ASSUME_TAC o SPEC `3`) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[])) THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_If] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o]) THEN
  (ASM_CASES_TAC `word_ushr (word_zx (w:int64):A word) 61 = word 0` THEN ASM_REWRITE_TAC[]) THENL
   [(MP_TAC(SPEC `w:int64` (INST_TYPE [`:A`,`:A`] ASP3AUX_small_zx64)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ASP3AUX_ev_Assign] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC (ARITH_EQ :: word_sh_def :: VAL_WORD :: ASP3AUX_EVX) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o; wl_state_INFO.ri_accfupds; K_THM] THEN
  EXISTS_TAC `NONE:((A)wl_result)option` THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_DISTINCT] THEN
  MATCH_MP_TAC ASP3AUX_state_rel_small_res THEN EXISTS_TAC `s:(C,FFI)data_state` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[join_env_locals_insert_odd; ARITH_RULE `ODD 1 /\ ODD 3`] THEN
  REWRITE_TAC[lookup_insert; adjust_var_eq_numeral; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]]);
    (MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word (word_ushr (word_zx (w:int64):A word) 61))
       (insert 3 (wl_Word (word_zx w:A word)) (wl_state_locals (t:(A,C,FFI)wl_state))))) t`;
    `data_state_locals (s:(C,FFI)data_state)`;
    `CONS (the_global (data_state_global (s:(C,FFI)data_state)),FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)
       (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
    `3`; `word_zx (w:int64):A word`; `h1:A word`; `dest:num`] evaluate_WriteWord64_bignum) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def; lookup_insert] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[join_env_locals_insert_odd; ARITH_RULE `ODD 1 /\ ODD 3`] THEN
    REWRITE_TAC[adjust_var_eq_numeral; ARITH] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[join_env_locals_def] THEN
      MATCH_MP_TAC ASP3AUX_state_rel_memory_rel THEN ASM_MESON_TAC[];
      ASM_ARITH_TAC;
      MP_TAC(SPEC `w:int64` (INST_TYPE [`:A`,`:A`] ASP3AUX_not_small_zx64)) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m':A word->A word_loc`
    (X_CHOOSE_THEN `locals':(A word_loc)spt` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH_EQ]) THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; ASP3AUX_K_o; wl_state_INFO.ri_accfupds; K_THM] THEN
  EXISTS_TAC `NONE:((A)wl_result)option` THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1; option_DISTINCT] THEN
  MP_TAC(SPEC `w:int64` (INST_TYPE [`:A`,`:A`] ASP3AUX_val_zx64)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `nf:A word_loc`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ASP3AUX_state_rel_big_res THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN EXISTS_TAC `data_state_space (s:(C,FFI)data_state) - 2` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)]]);;

(* HOL4 line 6952 *)
let push_env_tstamps = prove
 (`!x t (s:(C,FFI)data_state).
     data_state_tstamps (data_push_env x t s) = data_state_tstamps s`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `t:bool` THEN
  REWRITE_TAC[data_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 6958 *)
let dec_clock_tstamps = prove
 (`!s:(C,FFI)data_state. data_state_tstamps (data_dec_clock s) = data_state_tstamps s`,
  REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 6964 *)
let FromList1_code_thm = prove
 (`!k a b (r:(A,C,FFI)wl_state) x m1 a1 a2 a3 a4 a5 a6 c b1 l1 l2 ret_val.
     lookup FromList1_location (wl_state_code r) = SOME (6,FromList1_code c) /\
     copy_list c (wl_state_store r) k (a,x,b,wl_state_memory r,wl_state_mdomain r) =
       SOME (b1,m1) /\
     shift_length c < dimindex (:A) /\ good_dimindex (:A) /\
     wl_get_var a1 r = SOME (wl_Loc l1 l2) /\
     wl_get_var a2 r = SOME (wl_Word (b:A word)) /\
     wl_get_var a3 r = SOME a /\
     wl_get_var a4 r = SOME (wl_Word (word (4 * k))) /\
     wl_get_var a5 r = SOME ret_val /\
     wl_get_var a6 r = SOME x /\
     4 * k < dimword (:A) /\
     k < wl_state_clock r ==>
     wl_evaluate (wl_Call NONE (SOME FromList1_location) [a1;a2;a3;a4;a5;a6] NONE,r) =
       (SOME (wl_Result (wl_Loc l1 l2) [ret_val]),
        wl_state_memory_fupd (K m1)
          (wl_state_clock_fupd (K ((wl_state_clock r - k) - 1))
             (wl_state_locals_fupd (K LN)
                (wl_state_locals_size_fupd (K (SOME 0))
                   (wl_state_store_fupd (K (wl_state_store r |+ (NextFree,wl_Word b1)))
                      (wl_state_stack_max_fupd
                         (K (OPTION_MAP2 MAX (wl_state_stack_max r)
                               (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack r))
                                  (lookup FromList1_location (wl_state_stack_size r)))))
                         r))))))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[ASP3AUX_ev_Call] THEN ASM_REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FromList1_code_def] THEN
  (SUBGOAL_THEN `~(wl_state_clock (r:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]) THEN ASM_REWRITE_TAC[] THENL
  [UNDISCH_TAC `copy_list c (wl_state_store (r:(A,C,FFI)wl_state)) 0
      (a,x,b,wl_state_memory r,wl_state_mdomain r) = SOME (b1,m1)` THEN
   ONCE_REWRITE_TAC[copy_list_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN ASP3AUX_FROMLIST2_TAC THEN
   ASP3AUX_MATCH_ABBREV_TAC `wl_If asm_Equal 6 (Imm (word 0)) (p1:(A)wl_prog) p2`
     `p2:(A)wl_prog` THEN
   SIMP ASP3AUX_EV_THMS;
   FIRST_X_ASSUM(fun th -> if is_forall (concl th) then ASP3AUX_HIDE_TAC th else NO_TAC) THEN
   UNDISCH_TAC `copy_list c (wl_state_store (r:(A,C,FFI)wl_state)) (SUC k)
      (a,x,b,wl_state_memory r,wl_state_mdomain r) = SOME (b1,m1)` THEN
   ONCE_REWRITE_TAC[copy_list_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
   CASES_ON `a:A word_loc` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
   CASES_ON `get_real_addr c (wl_state_store (r:(A,C,FFI)wl_state)) a'` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN ASP3AUX_FROMLIST2_TAC THEN
   ASP3AUX_MATCH_ABBREV_TAC `wl_If asm_Equal 6 (Imm (word 0)) (p1:(A)wl_prog) p2`
     `p1:(A)wl_prog` THEN
   SUBGOAL_THEN `~(word (4 + 4 * k) = (word 0:A word))` ASSUME_TAC THENL
    [UNDISCH_TAC `4 * SUC k < dimword(:A)` THEN
     REWRITE_TAC[dimword_def; WORD_EQ; CONG; MOD_0; ARITH_RULE `4 * SUC k = 4 + 4 * k`] THEN
     SIMP_TAC[MOD_LT] THEN ARITH_TAC; ALL_TAC] THEN
   ASP3AUX_MATCH_ABBREV_TAC `wl_If asm_Equal 6 (Imm (word 0)) (p1:(A)wl_prog) p2`
     `p2:(A)wl_prog` THEN
   SIMP ASP3AUX_EV_THMS THEN
   ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (p2:(A)wl_prog, s3:(A,C,FFI)wl_state)`
     `s3:(A,C,FFI)wl_state` THEN
   SUBGOAL_THEN `wl_word_exp (s3:(A,C,FFI)wl_state) (real_addr c 4) = SOME (wl_Word a'')`
     ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `a':A word` THEN ASM_REWRITE_TAC[] THEN
     EXPAND_TAC "s3" THEN SIMP[wl_get_var_def; lookup_insert]; ALL_TAC] THEN
   ASP3AUX_UNABBREV_TAC `p2:(A)wl_prog` THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASP3AUX_UNABBREV_TAC `s3:(A,C,FFI)wl_state` THEN
   ASP3AUX_UNABBREV_TAC `p1:(A)wl_prog` THEN
   SIMP ASP3AUX_EV_THMS THEN
   ASP3AUX_MATCH_ABBREV_TAC
     `wl_evaluate (wl_Call NONE (SOME FromList1_location) [0; 2; 4; 6; 8; 10] NONE,
                   t7:(A,C,FFI)wl_state)` `t7:(A,C,FFI)wl_state` THEN
   ASP3AUX_UNHIDE_THEN (fun ih -> MP_TAC(SPECL
     [`(b =+ x) (wl_state_memory (r:(A,C,FFI)wl_state))
         (word_add a'' (word_mul (word 2) bytes_in_word))`;
      `word_add b bytes_in_word:A word`; `t7:(A,C,FFI)wl_state`;
      `(b =+ x) (wl_state_memory (r:(A,C,FFI)wl_state)) (word_add a'' bytes_in_word)`;
      `m1:A word->A word_loc`; `0`; `2`; `4`; `6`; `8`; `10`; `c:data_to_word_config`;
      `b1:A word`; `l1:num`; `l2:num`; `ret_val:A word_loc`] ih)) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "t7" THEN SIMP[wl_get_var_def; lookup_insert] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THEN
     TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
   EXPAND_TAC "t7" THEN SIMP[wl_state_component_equality; ASP3AUX_MAX_MAX] THEN
   ARITH_TAC]);;

(* HOL4 line 7043 *)
let FromList_thm = prove
 (CASE_TERM
  `!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs tag v1 v2 s1 v s2 r1 r2.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     ~(encode_header c (4 * tag) 0 = (NONE:(A word)option)) /\
     data_get_vars [0; 1; 2] (data_state_locals s) =
       SOME [v1; v2; data_Number (&(4 * tag))] /\
     wl_state_clock t = MustTerminate_limit (:A) - 1 /\
     data_pop_env s = SOME s1 /\ is_env (HD (data_state_stack s)) /\
     data_state_locals_size s = lookup FromList_location (data_state_stack_frame_sizes s) /\
     data_do_app (BlockOp (FromList tag)) [v1; v2] s1 = Rval (v,s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     size_of_heap (cut_locals (fromList [one; one; one]) s) <=
       size_of_heap_args [v1; v2] s1 ==>
     ?q r new_c.
       wl_evaluate (FromList_code c,t) = (q,r) /\
       if q = SOME NotEnoughSpace then
         wl_state_ffi r = wl_state_ffi t /\
         option_le (wl_state_stack_max r) (data_state_stack_max s2) /\
         (~(data_to_word_config_gc_kind c = data_to_word_None) /\
          no_thunks_in_refs (data_state_refs s) ==>
          (match (v1,v2) with
             (data_Number n,_) ->
               ~small_num (limits_arch_64_bit (data_state_limits s)) n \/
               ~(num_of_int n < dimword (:A) DIV 16) \/
               ~(num_of_int n < 2 EXP data_to_word_config_len_size c) \/
               (limits_heap_limit (data_state_limits s1) <
                size_of_heap_args [v1; v2] s1 + num_of_int n + 1)))
       else
         ?rv. q = SOME (wl_Result (wl_Loc l1 l2) [rv]) /\
              data_to_word_gcProof_state_rel c r1 r2
                (data_state_locals_fupd (K LN)
                   (data_state_locals_size_fupd (K (SOME 0))
                      (data_state_clock_fupd (K new_c)
                         (data_state_stack_fupd (K (data_state_stack s)) s2))))
                r (SOME [(v,rv)]) locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(C,FFI)data_state`; `s1:(C,FFI)data_state`] ASP3AUX_pop_env_is_env) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ssz:num option` (X_CHOOSE_THEN `env0:data_v spt`
    (X_CHOOSE_THEN `xs0:stack list` STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN
  MP_TAC(MATCH_MP state_rel_IMP_tstamps (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `ts0:num`) THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP3AUX_encode_header_small_int) THEN
  IMP_RES_TAC state_rel_get_vars_IMP THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:A word_loc` (X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` SUBST_ALL_TAC)) o
    REWRITE_RULE[LENGTH_EQ_3]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; get_vars_SOME_IFF_data]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `2`; `4 * tag`]
    state_rel_get_var_Number_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP3AUX_state_rel_lookup_0 o
    check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
  UNDISCH_TAC `data_do_app (BlockOp (FromList tag)) [v1; v2]
     (data_state_locals_fupd (K env0) (data_state_stack_fupd (K xs0)
       (data_state_locals_size_fupd (K ssz) (s:(C,FFI)data_state)))) = Rval (v,s2)` THEN
  ASP3AUX_DO_APP_SPLIT_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "data_v"; distinctness "data_v"]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_EQ; LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN RVEQ_TAC) THENL
  [(* the empty list *)
   (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `0`; `&0:int`]
    state_rel_IMP_test_zero) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC) THEN
   (RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[adjust_var_def; wl_get_var_def]) THEN
  REWRITE_TAC[FromList_code_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASP3AUX_MATCH_ABBREV_TAC `wl_If asm_Equal 2 (Imm (word 0)) (p1:(A)wl_prog) p2` `p2:(A)wl_prog` THEN
  SIMP (data_to_word_Unit_def :: ASP3AUX_EV_THMS)) THEN
   (EXISTS_TAC `wl_state_clock (t:(A,C,FFI)wl_state)`) THEN
   (FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_memory_rel o
    check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  FS[option_le_max_right; lookup_def; lookup_insert; adjust_var_11]) THEN
   (REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ALL2 contains_loc (wl_state_stack (t:(A,C,FFI)wl_state)) locs` THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP option_le_add_indv o
      check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
                       can (find_term (ASP3AUX_is_app "wl_stack_size")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC]) THEN
   (SUBGOAL_THEN `word_add (Smallnum (&(4 * tag))) (word 2) = BlockNil tag:A word` SUBST1_TAC THENL
   [REWRITE_TAC[data_to_word_Smallnum_def; BlockNil_def; WORD_SHL_WORD] THEN
    REWRITE_TAC[INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tag < dimword (:A) DIV 16` ASSUME_TAC THENL
   [UNDISCH_TAC `~(encode_header c (4 * tag) 0 = (NONE:(A word)option))` THEN
    REWRITE_TAC[encode_header_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MP5AUX_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC memory_rel_Cons_empty THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_zero_space o
    check (fun th -> ASP3AUX_is_app "memory_rel" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM; MEM_APPEND; join_env_def; MAP; FILTER] THEN MESON_TAC[]);
   (* a non-empty list *)
   (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `0`;
    `&(SUC (LENGTH (a1:data_v list))):int`]
    state_rel_IMP_test_zero) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`0`; `&(SUC (LENGTH (a1:data_v list))):int`; `c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `wl_Word (w:A word)`]
    state_rel_get_var_Number_IMP_alt) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[adjust_var_def]) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN DISCH_TAC) THEN
   (REWRITE_TAC[FromList_code_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASP3AUX_MATCH_ABBREV_TAC `wl_If asm_Equal 2 (Imm (word 0)) (p1:(A)wl_prog) p2` `p1:(A)wl_prog` THEN
  REWRITE_TAC[ASP3AUX_ev_If] THEN ASM_REWRITE_TAC[wl_get_var_imm_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[ASP3AUX_word_cmp_Word; asm_word_cmp_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `2`; `w:A word`] evaluate_BignumHalt2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[]) THEN
   (ASM_CASES_TAC `small_int (:A) (&(SUC (LENGTH (a1:data_v list))))` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THENL
   [(* small length *)
    (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `0`;
    `SUC (LENGTH (a1:data_v list))`] state_rel_get_var_Number_IMP) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[adjust_var_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
  REWRITE_TAC[ASP3AUX_ev_Assign; wl_word_exp_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN ONCE_REWRITE_TAC[ASP3AUX_ev_Seq]) THEN
    (MP_TAC(ISPECL [`data_state_locals (s:(C,FFI)data_state)`;
    `data_Number (&(SUC (LENGTH (a1:data_v list))))`; `v2:data_v`; `data_Number (&(4 * tag))`]
    ASP3AUX_cut_env_fromList3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `cut_x:data_v spt`) THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
     (wl_set_var 1 (wl_Word (Smallnum (&(SUC (LENGTH (a1:data_v list)))))) (t:(A,C,FFI)wl_state)) NONE locs`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[wl_set_var_def; state_rel_insert_1]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (AllocVar c (MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16))
     (fromList [one; one; one]), wl_set_var 1 (wl_Word (Smallnum (&(SUC (LENGTH (a1:data_v list)))))) (t:(A,C,FFI)wl_state))`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:((A)wl_result)option` (X_CHOOSE_THEN `r2:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `wl_set_var 1 (wl_Word (Smallnum (&(SUC (LENGTH (a1:data_v list)))))) (t:(A,C,FFI)wl_state)`;
    `locs:(num#num)list`; `fromList [one;one;one]`; `cut_x:data_v spt`;
    `Smallnum (&(SUC (LENGTH (a1:data_v list)))):A word`;
    `MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)`;
    `q2:((A)wl_result)option`; `r2:(A,C,FFI)wl_state`] AllocVar_thm) THEN
  ASM_REWRITE_TAC[data_to_word_gcProof_get_var_set_var_thm] THEN ANTS_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MIN_DEF] THEN ARITH_TAC;
    STRIP_TAC]) THEN
    (FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP3AUX_val_Smallnum o
    check ((=) `small_int (:A) (&(SUC (LENGTH (a1:data_v list))))` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val (Smallnum (&(SUC (LENGTH (a1:data_v list)))):A word) =
                                       4 * SUC (LENGTH a1)`; ARITH_RULE `(4 * n) DIV 4 = n`]) THEN
  ASM_CASES_TAC `q2:((A)wl_result)option = SOME NotEnoughSpace`) THENL
    [(* AllocVar fails *)
     (FIRST_X_ASSUM(fun th -> if is_imp (concl th) && not (is_neg (lhand (concl th))) &&
                             is_eq (lhand (concl th)) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN EXISTS_TAC `r2:(A,C,FFI)wl_state` THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
     (CONJ_TAC THENL [REWRITE_TAC[option_le_max_right] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `SUC (LENGTH (a1:data_v list)) < 2 EXP data_to_word_config_len_size c` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `SUC (LENGTH (a1:data_v list)) < dimword (:A) DIV 16` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_conj (lhand (concl th)))) THEN
  ASM_REWRITE_TAC[MIN_DEF] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<=" (concl th) &&
     can (find_term (ASP3AUX_is_app "cut_locals")) (concl th))) THEN
  CONV_TAC(CAKE_SIMP_CONV []) THEN ARITH_TAC);
     (* AllocVar succeeds *)
     (FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_neg (lhand (concl th)) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k. k < 3 ==> lookup k (cut_x:data_v spt) = lookup k (data_state_locals (s:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ASP3AUX_data_cut_env_lookup THEN
    EXISTS_TAC `fromList [one;one;one]` THEN ASM_REWRITE_TAC[domain_fromList; LENGTH; count_DEF; IN_ELIM_THM] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_memory_rel o ASP3AUX_SR_WITH `r2:(A,C,FFI)wl_state`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_store o ASP3AUX_SR_WITH `r2:(A,C,FFI)wl_state`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_stubs o ASP3AUX_SR_WITH `r2:(A,C,FFI)wl_state`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_lookup_0 o ASP3AUX_SR_WITH `r2:(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f:A word` (X_CHOOSE_THEN `cur:A word` STRIP_ASSUME_TAC) o
    check (is_exists o concl))) THEN
     (SUBGOAL_THEN `lookup 0 (cut_x:data_v spt) = SOME (data_Number (&(SUC (LENGTH (a1:data_v list))))) /\
                lookup 1 cut_x = SOME v2 /\ lookup 2 cut_x = SOME (data_Number (&(4 * tag)))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `0 < 3 /\ 1 < 3 /\ 2 < 3`] THEN ASM_REWRITE_TAC[GSYM data_get_var_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup 2 (wl_state_locals (r2:(A,C,FFI)wl_state)) =
                  SOME (wl_Word (Smallnum (&(SUC (LENGTH (a1:data_v list)))))) /\
                lookup 6 (wl_state_locals r2) = SOME (wl_Word (Smallnum (&(4 * tag))))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
        `data_state_locals_fupd (K cut_x) (data_state_space_fupd (K (SUC (LENGTH (a1:data_v list)) + 1)) (s:(C,FFI)data_state))`;
        `r2:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `0`;
        `SUC (LENGTH (a1:data_v list))`] state_rel_get_var_Number_IMP);
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
        `data_state_locals_fupd (K cut_x) (data_state_space_fupd (K (SUC (LENGTH (a1:data_v list)) + 1)) (s:(C,FFI)data_state))`;
        `r2:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `2`;
        `4 * tag`] state_rel_get_var_Number_IMP)] THEN
    ASM_REWRITE_TAC[data_get_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[wl_get_var_def; adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_locals_fupd (K cut_x) (data_state_space_fupd (K (SUC (LENGTH (a1:data_v list)) + 1)) (s:(C,FFI)data_state))`;
    `r2:(A,C,FFI)wl_state`; `NONE:((data_v#(A)word_loc)list)option`; `locs:(num#num)list`; `1`; `v2:data_v`]
    state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[data_get_var_def; data_state_INFO.ri_accfupds; K_THM; wl_get_var_def; adjust_var_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(X_CHOOSE_TAC `wv2:A word_loc`)) THEN
     (SUBGOAL_THEN `encode_header c (4 * tag) (SUC (LENGTH (a1:data_v list))) =
                  SOME (make_header c (word (4 * tag)) (SUC (LENGTH a1)):A word)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(encode_header c (4 * tag) 0 = (NONE:(A word)option))` THEN
    UNDISCH_TAC `SUC (LENGTH (a1:data_v list)) < MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)` THEN
    REWRITE_TAC[encode_header_def; MIN_DEF] THEN
    SUBGOAL_THEN `dimword(:A) DIV 16 = 2 EXP (dimindex (:A) - 4)` SUBST1_TAC THENL
     [REWRITE_TAC[dimword_def] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
      REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN MP5AUX_ARITH_TAC;
    ALL_TAC]) THEN
     (SUBGOAL_THEN `lookup (adjust_var 1) (wl_state_locals (r2:(A,C,FFI)wl_state)) = SOME wv2` ASSUME_TAC THENL
   [REWRITE_TAC[adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if ASP3AUX_is_app "memory_rel" (concl th) && free_in `r2:(A,C,FFI)wl_state` (concl th)
    then MP_TAC(MATCH_MP memory_rel_lookup (CONJ th (CONJ (ASSUME `lookup 1 (cut_x:data_v spt) = SOME v2`)
           (ASSUME `lookup (adjust_var 1) (wl_state_locals (r2:(A,C,FFI)wl_state)) = SOME wv2`))))
    else NO_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (r2:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `SUC (LENGTH (a1:data_v list)) + 1`; `wl_state_store (r2:(A,C,FFI)wl_state)`;
    `wl_state_memory (r2:(A,C,FFI)wl_state)`; `wl_state_mdomain (r2:(A,C,FFI)wl_state)`;
    `v2:data_v`; `CONS (a0:data_v) a1`; `wv2:A word_loc`;
    `APPEND (join_env cut_x (toAList (inter (wl_state_locals (r2:(A,C,FFI)wl_state)) (adjust_set (cut_x:data_v spt)))))
       (CONS (the_global (data_state_global (s:(C,FFI)data_state)),FAPPLY (wl_state_store r2) Globals)
         (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack r2)))`;
    `tag:num`; `make_header c (word (4 * tag)) (SUC (LENGTH (a1:data_v list))):A word`]
    memory_rel_FromList) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `m1:A word->A word_loc`
    (X_CHOOSE_THEN `f1:A word` STRIP_ASSUME_TAC)))) THEN
  UNDISCH_TAC `FLOOKUP (wl_state_store (r2:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word free)` THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `FLOOKUP (wl_state_store (r2:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)` THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
     (SUBGOAL_THEN `2 < dimindex (:A) /\ 4 < dimindex (:A) /\
                (dimindex (:A) - data_to_word_config_len_size c) - 2 < dimindex (:A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n < dimindex (:A) ==> n MOD dimword (:A) = n /\ ~(n >= dimindex (:A))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL [MATCH_MP_TAC MOD_LT THEN MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
    MP5AUX_ARITH_TAC; MP5AUX_ARITH_TAC]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SIMP (FLOOKUP_UPDATE :: word_sh_def :: WORD_OR_0 :: data_to_word_Unit_def :: ASP3AUX_EV_THMS)) THEN
     (SUBGOAL_THEN `4 * SUC (LENGTH (a1:data_v list)) < dimword (:A) /\ 16 * tag < dimword (:A)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `small_int (:A) (&(SUC (LENGTH (a1:data_v list))))` THEN
      REWRITE_TAC[small_int_def; INT_OF_NUM_LT; INT_ARITH `--(&n) <= &m:int`] THEN
      MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN ARITH_TAC;
      UNDISCH_TAC `~(encode_header c (4 * tag) 0 = (NONE:(A word)option))` THEN
      REWRITE_TAC[encode_header_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`dimword(:A)`; `16`] DIVISION) THEN MP5AUX_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ASP3AUX_Smallnum_ushr_2; ASP3AUX_Smallnum_ushr_4] THEN
  ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (Make_ptr_bits_code c 9 7 3, t5:(A,C,FFI)wl_state)` `t5:(A,C,FFI)wl_state` THEN
  MP_TAC(ISPECL [`9`; `3`; `tag:num`; `c:data_to_word_config`; `7`; `SUC (LENGTH (a1:data_v list))`;
    `t5:(A,C,FFI)wl_state`; `f:A word`; `cur:A word`] data_to_word_assignProof_Make_ptr_bits_thm) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t5" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `shift_length c < dimindex (:A)` THEN REWRITE_TAC[shift_length_def] THEN MP5AUX_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  CASE_REWRITE_TAC[]) THEN
     (ASP3AUX_MATCH_ABBREV_TAC `wl_evaluate (wl_Call NONE (SOME FromList1_location) [0; 1; 4; 2; 3; 5] NONE,
       t6:(A,C,FFI)wl_state)` `t6:(A,C,FFI)wl_state` THEN
  MP_TAC(ISPECL [`SUC (LENGTH (a1:data_v list))`; `wv2:A word_loc`; `f:A word`; `t6:(A,C,FFI)wl_state`;
    `wl_Word (make_header c (word (4 * tag)) (SUC (LENGTH (a1:data_v list))):A word)`;
    `m1:A word->A word_loc`; `0`; `1`; `4`; `2`; `3`; `5`; `c:data_to_word_config`; `f1:A word`;
    `l1:num`; `l2:num`; `make_cons_ptr c (word_sub f cur) tag (SUC (LENGTH (a1:data_v list))):A word_loc`]
    FromList1_code_thm) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t6" THEN EXPAND_TAC "t5" THEN
    REWRITE_TAC[wl_set_var_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ASP3AUX_FromList_header] THEN
    ASM_REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `~(&n < &0:int)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
    SUBGOAL_THEN `wl_state_clock (r2:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 1` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_imp_clock o ASP3AUX_SR_WITH `r2:(A,C,FFI)wl_state`) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_imp_clock o
        check (fun th -> ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
                         el 4 (snd (strip_comb (concl th))) = `t:(A,C,FFI)wl_state`)) THEN
      REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
      UNDISCH_TAC `wl_state_clock (t:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 1` THEN
      MESON_TAC[];
      UNDISCH_TAC `SUC (LENGTH (a1:data_v list)) < MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)` THEN
      REWRITE_TAC[MustTerminate_limit_def; MIN_DEF] THEN
      MP_TAC(SPECL [`dimword(:A)`; `16`] DIVISION) THEN ARITH_TAC];
    ALL_TAC]) THEN
     (DISCH_THEN SUBST1_TAC THEN ASP3AUX_EXISTS_PAIR_TAC THEN
  REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"; CONS_11] THEN
  EXISTS_TAC `wl_state_clock (t6:(A,C,FFI)wl_state) - SUC (LENGTH (a1:data_v list)) - 1` THEN
  REWRITE_TAC[UNWIND_THM1]) THEN
     (REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term (ASP3AUX_is_app "wl_set_var")) (rand (concl th))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    ASP3AUX_SR_WITH `r2:(A,C,FFI)wl_state`) THEN
  EXPAND_TAC "t6" THEN EXPAND_TAC "t5" THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; data_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM; ALL;
              FDOM_FUPDATE; IN_INSERT; FLOOKUP_UPDATE; FAPPLY_FUPDATE_THM; distinctness "store_name";
              IS_SOME_DEF; option_DISTINCT; lookup_def] THEN
  SIMP[ASP3AUX_code_oracle_rel_upd; distinctness "store_name"] THEN
  ASM_REWRITE_TAC[]) THEN
     (RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `data_state_stack (s:(C,FFI)data_state) = CONS (data_Env ssz env0) xs0`;
                              ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts0`; THE_DEF; SUB_REFL]) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ALL2 data_to_word_gcProof_stack_rel (CONS (data_Env ssz env0) xs0)
                   (wl_state_stack (r2:(A,C,FFI)wl_state))` THEN SIMP[];
    REWRITE_TAC[option_le_max_right] THEN DISJ1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP option_le_add_indv o
      check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
                       can (find_term (ASP3AUX_is_app "wl_stack_size")) (concl th) &&
                       free_in `r2:(A,C,FFI)wl_state` (concl th))) THEN SIMP_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP stack_rel_IMP_size_of_stack o
      check (fun th -> ASP3AUX_is_app "ALL2" (concl th) && free_in `r2:(A,C,FFI)wl_state` (concl th) &&
                       can (find_term (ASP3AUX_is_app "data_to_word_gcProof_stack_rel")) (concl th))) THEN
    REWRITE_TAC[size_of_stack_eq] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[stack_consumed_def] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC ASP3AUX_option_le_FromList_stack THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "memory_rel" (concl th) &&
                       can (find_term (ASP3AUX_is_app "make_cons_ptr")) (concl th))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN
    REWRITE_TAC[MEM; MEM_APPEND; join_env_def; MAP; FILTER] THEN MESON_TAC[]])];
    (* large length: BignumHalt *)
    (EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN EXISTS_TAC `rb:(A,C,FFI)wl_state` THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
         can (find_term ((=) `data_state_stack_max (s:(C,FFI)data_state)`)) (lhand (concl th)))) THEN
      SIMP[]];
    STRIP_TAC THEN DISJ1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_state_rel_arch64 o
      check (ASP3AUX_is_app "data_to_word_gcProof_state_rel" o concl)) THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`data_state_limits (s:(C,FFI)data_state)`;
      `&(SUC (LENGTH (a1:data_v list))):int`] (INST_TYPE [`:A`,`:A`] ASP3AUX_small_num_eq)) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH]])]]);;

(* HOL4 line 7372 (local) *)
let do_app_FromList_stack_max = prove
 (`!tag vals (s:(C,FFI)data_state) v s'.
     data_do_app (BlockOp (FromList tag)) vals s = Rval (v,s') ==>
     data_state_stack_max s' =
       OPTION_MAP2 MAX (data_state_stack_max s)
         (OPTION_MAP2 (+)
            (stack_consumed (data_state_stack_frame_sizes s) (data_state_limits s)
               (BlockOp (FromList tag)) vals)
            (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
               (data_state_locals_size s)))`,
  REPEAT GEN_TAC THEN ASP3AUX_DO_APP_SPLIT_TAC THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 7391 (local) *)
let do_app_FromList_safe = prove
 (`!v2 ys tag (s:(C,FFI)data_state) v s'.
     data_v_to_list v2 = SOME ys /\
     data_do_app (BlockOp (FromList tag)) [data_Number (&(LENGTH ys)); v2] s =
       Rval (v,s') ==>
     (data_state_safe_for_space s' <=>
      (((small_num (limits_arch_64_bit (data_state_limits s)) (&(LENGTH ys)) /\
         LENGTH ys < 2 EXP limits_length_limit (data_state_limits s) /\
         LENGTH ys < arch_size (data_state_limits s) DIV 16 /\
         4 * tag < 2 EXP (arch_size (data_state_limits s) -
                          (limits_length_limit (data_state_limits s) + 2)) /\
         4 * tag < 2 EXP arch_size (data_state_limits s) DIV 16) /\
        (data_state_safe_for_space s /\
         no_thunks_in_refs (data_state_refs s) /\
         size_of_heap_args [data_Number (&(LENGTH ys)); v2] s + (LENGTH ys + 1) <=
           limits_heap_limit (data_state_limits s))) /\
       the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
         (OPTION_MAP2 (+)
            (OPTION_MAP2 MAX (lookup FromList_location (data_state_stack_frame_sizes s))
                             (lookup FromList1_location (data_state_stack_frame_sizes s)))
            (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
               (data_state_locals_size s))))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CASES_ON `ys:data_v list` THEN ASP3AUX_DO_APP_SPLIT_ASM_TAC THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[lim_safe_def; space_consumed_def; stack_consumed_def] THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL; NUM_OF_INT_OF_NUM; ADD_CLAUSES; INT_OF_NUM_EQ;
                    ARITH_RULE `a - b - 2 = a - (b + 2)`])) THEN
  CONV_TAC TAUT);;

(* HOL4 line 7423 (local) *)
let do_app_FromList_eq = prove
 (`!v2 ys tag (s:(C,FFI)data_state) v s'.
     data_v_to_list v2 = SOME ys /\
     data_do_app (BlockOp (FromList tag)) [data_Number (&(LENGTH ys)); v2] s =
       Rval (v,s') ==>
     (?ts'. v = data_Block ts' tag ys) /\ data_state_space s' = 0 /\
     data_state_refs s' = data_state_refs s /\ data_state_code s' = data_state_code s /\
     data_state_ffi s' = data_state_ffi s /\ data_state_handler s' = data_state_handler s /\
     data_state_locals s' = data_state_locals s /\
     data_state_stack s' = data_state_stack s /\
     data_state_limits s' = data_state_limits s /\
     data_state_stack_frame_sizes s' = data_state_stack_frame_sizes s /\
     data_state_locals_size s' = data_state_locals_size s /\
     data_state_global s' = data_state_global s /\
     data_state_compile s' = data_state_compile s /\
     data_state_compile_oracle s' = data_state_compile_oracle s /\
     data_state_clock s' = data_state_clock s /\
     data_state_tstamps s' =
       (if ys = [] then data_state_tstamps s else OPTION_MAP SUC (data_state_tstamps s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CASES_ON `ys:data_v list` THEN ASP3AUX_DO_APP_SPLIT_ASM_TAC THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; OPTION_MAP_DEF; NOT_CONS_NIL; ADD1] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 7444 (local) *)
let call_env_push_env_dec_clock_lift_locals = prove
 (`!(args:(A word_loc)list) b y1 y2 (t:(A,C,FFI)wl_state) k v ck' tp.
     wl_call_env args b (wl_push_env (y1,y2) NONE
       (wl_dec_clock (wl_state_locals_fupd (K (insert k v (wl_state_locals t)))
          (wl_state_clock_fupd (K ck') (wl_state_termdep_fupd (K tp) t))))) =
     wl_state_clock_fupd (K (ck' - 1))
       (wl_state_termdep_fupd (K tp) (wl_call_env args b (wl_push_env (y1,y2) NONE t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_dec_clock_def; wl_call_env_def; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  MP_TAC(ISPEC `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 7457 (local) *)
let call_env_push_env_dec_clock_stack_max = prove
 (`!args ls env (s:(C,FFI)data_state).
     data_state_stack_max (data_call_env args ls (data_push_env env F (data_dec_clock s))) =
     OPTION_MAP2 MAX
       (OPTION_MAP2 MAX (data_state_stack_max s)
          (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
       (OPTION_MAP2 (+)
          (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
          ls)`,
  MATCH_ACCEPT_TAC ASP3AUX_cpd_stack_max);;

(* HOL4 line 7470 (local) *)
let option_le_stackmax_bridge = prove
 (`!(m:num option) (l_size:num option) (s_size:num option)
    (ls_R:num option) (ls_Re:num option).
     option_le
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX
             (OPTION_MAP2 MAX m (OPTION_MAP2 (+) l_size s_size))
             (OPTION_MAP2 (+) (OPTION_MAP2 (+) l_size s_size) ls_R))
          (OPTION_MAP2 (+) (OPTION_MAP2 MAX ls_R ls_Re) (OPTION_MAP2 (+) s_size l_size)))
       (OPTION_MAP2 MAX m
          (OPTION_MAP2 (+) (OPTION_MAP2 MAX ls_R ls_Re) (OPTION_MAP2 (+) s_size l_size)))`,
  MATCH_ACCEPT_TAC ASP3AUX_stackmax_bridge);;

(* HOL4 line 7491 *)
let assign_FromList = prove
 (assign_thm_stmt `(?tag. op = BlockOp (FromList tag))`,
  (REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `tag:num` SUBST_ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ns. names_opt = SOME (ns:num_set)` (X_CHOOSE_THEN `ns:num_set` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (BlockOp (FromList tag)) <=> names_opt:num_set option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:num_set option` THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP do_app_stack_max) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`; `ns:num_set`;
    `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v2:data_v` (X_CHOOSE_THEN `vs:data_v list` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_do_app_FromList_vals) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_get_vars_2) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `SUC (SUC 0) = LENGTH (ws:(A word_loc)list)` o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2]) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_FromList_def; data_to_word_get_names_def]) THEN
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_limits (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]) THENL
  [(MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] evaluate_GiveUp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
  EXISTS_TAC `r0:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> ASP3AUX_is_app "option_le" (concl th) &&
         free_in `s2:(C,FFI)data_state` (concl th))) THEN SIMP[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v2:data_v`; `vs:data_v list`; `tag:num`;
    `data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s`;
    `v:data_v`; `s2:(C,FFI)data_state`] do_app_FromList_safe) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `encode_header c (4 * tag) 0 = (NONE:(A word)option)` THEN
  REWRITE_TAC[encode_header_def; option_DISTINCT; dimword_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `a - b - 2 = a - (b + 2)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; ARITH_RULE `a - b - 2 = a - (b + 2)`]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
  REWRITE_TAC[LT_NZ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC TAUT);
   (SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_MustTerminate] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN
  REWRITE_TAC[ASP3AUX_ev_Assign; wl_word_exp_def] THEN CASE_REWRITE_TAC[] THEN
  ABBREV_TAC `tm = wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                     (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state))`) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP lookup_RefByte_location o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt` STRIP_ASSUME_TAC) o
    MATCH_MP cut_env_IMP_cut_envs) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN `~(adjust_var k1 = 1) /\ ~(adjust_var k2 = 1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[adjust_var_def] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_Call; wl_get_vars_def; wl_get_var_def; wl_set_var_def] THEN
  EXPAND_TAC "tm" THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[domain_adjust_sets; ALL_DISTINCT; MEM; NOT_IN_EMPTY] THEN
  SIMP[cut_envs_adjust_sets_ODD; ARITH_RULE `ODD 1`] THEN
  ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `data_cut_env (ns:num_set) (data_state_locals (s:(C,FFI)data_state)) =
                SOME (mk_wf (inter (data_state_locals s) (ns:num_set)))` ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_state_opt (SOME ns) (s:(C,FFI)data_state) =
      SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals s) (ns:num_set)))) s)` THEN
    REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `data_cut_env (ns:num_set) (data_state_locals (s:(C,FFI)data_state))` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
       (data_state_clock_fupd (K (MustTerminate_limit (:A))) (s:(C,FFI)data_state))
       (wl_state_locals_fupd (K (insert 1 (wl_Word (word (16 * tag))) (wl_state_locals (tm:(A,C,FFI)wl_state)))) tm)
       NONE locs` MP_TAC THENL
   [REWRITE_TAC[state_rel_insert_1] THEN EXPAND_TAC "tm" THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_locals (tm:(A,C,FFI)wl_state) = wl_state_locals (t:(A,C,FFI)wl_state)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`NONE:(num#(A)wl_prog#num#num)option`; `c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_clock_fupd (K (MustTerminate_limit (:A))) (s:(C,FFI)data_state)`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word (word (16 * tag))) (wl_state_locals (t:(A,C,FFI)wl_state)))) (tm:(A,C,FFI)wl_state)`;
    `locs:(num#num)list`; `[k1;k2]:num list`; `[data_Number (&(LENGTH (vs:data_v list))); v2]`;
    `[w1;w2]:(A word_loc)list`; `ns:num_set`; `mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))`;
    `(y1,y2):((A)word_loc)spt#((A)word_loc)spt`; `n:num`; `l:num`;
    `lookup FromList_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`] state_rel_call_env_push_env) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; MAP; wl_get_vars_def; wl_get_var_def;
                    wl_state_INFO.ri_accfupds; lookup_insert] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[cut_envs_adjust_sets_ODD; ARITH_RULE `ODD 1`];
    REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC]) THEN
  (SUBGOAL_THEN `4 * tag < dimword (:A) DIV 16` ASSUME_TAC THENL
   [UNDISCH_TAC `~(encode_header c (4 * tag) 0 = (NONE:(A word)option))` THEN
    REWRITE_TAC[encode_header_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
      can (find_term (ASP3AUX_is_app "data_call_env")) (concl th) then
      MP_TAC(SPEC `4 * tag` (MATCH_MP (REWRITE_RULE[IMP_CONJ] state_rel_IMP_Number_arg) th))
    else NO_TAC) THEN
  ASM_REWRITE_TAC[LENGTH; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4 * 4 * tag = 16 * tag`] THEN DISCH_TAC) THEN
  (ABBREV_TAC `ts = data_call_env [data_Number (&(LENGTH (vs:data_v list))); v2; data_Number (&(4 * tag))]
      (lookup FromList_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
      (data_push_env (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))) F
        (data_dec_clock (data_state_clock_fupd (K (MustTerminate_limit (:A))) s)))` THEN
  ABBREV_TAC `s_pop = data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))))
      (data_state_stack_fupd (K (data_state_stack s))
        (data_state_locals_size_fupd (K (data_state_locals_size s)) (ts:(C,FFI)data_state)))` THEN
  SUBGOAL_THEN `data_pop_env (ts:(C,FFI)data_state) = SOME s_pop /\ is_env (HD (data_state_stack ts)) /\
                data_state_tstamps (s_pop:(C,FFI)data_state) = data_state_tstamps (s:(C,FFI)data_state) /\
                data_state_stack_max s_pop = data_state_stack_max ts /\
                data_state_limits ts = data_state_limits s /\
                data_state_refs ts = data_state_refs s /\
                data_state_stack ts = CONS (data_Env (data_state_locals_size s) (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack s)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; data_pop_env_def; is_env_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; HD] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `data_get_vars [0; 1; 2] (data_state_locals (ts:(C,FFI)data_state)) =
                  SOME [data_Number (&(LENGTH (vs:data_v list))); v2; data_Number (&(4 * tag))] /\
                data_state_locals_size ts = lookup FromList_location (data_state_stack_frame_sizes ts)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; data_get_vars_def; data_get_var_def; lookup_fromList] THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL; num_CONV `2`; num_CONV `1`] THEN CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tag:num`; `vs:data_v list`; `v2:data_v`;
    `data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s`;
    `s_pop:(C,FFI)data_state`; `v:data_v`; `s2:(C,FFI)data_state`] ASP3AUX_do_app_FromList_same_v) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `s2i:(C,FFI)data_state`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP do_app_stack_max o
    check (fun th -> free_in `s2i:(C,FFI)data_state` (concl th)))) THEN
  (SUBGOAL_THEN `size_of_heap (cut_locals (fromList [one;one;one]) (ts:(C,FFI)data_state)) <=
                size_of_heap_args [data_Number (&(LENGTH (vs:data_v list))); v2] (s_pop:(C,FFI)data_state)` ASSUME_TAC THENL
   [SUBGOAL_THEN `small_num (limits_arch_64_bit (data_state_limits (ts:(C,FFI)data_state))) (&(4 * tag))`
      ASSUME_TAC THENL
     [MP_TAC(ISPECL [`data_state_limits (ts:(C,FFI)data_state)`; `&(4 * tag):int`]
        (INST_TYPE [`:A`,`:A`] ASP3AUX_small_num_eq)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ASP3AUX_encode_header_small_int THEN
      EXISTS_TAC `c:data_to_word_config` THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `a = b ==> a <= b:num`) THEN
    SUBGOAL_THEN `data_state_locals (ts:(C,FFI)data_state) =
        fromList [data_Number (&(LENGTH (vs:data_v list))); v2; data_Number (&(4 * tag))] /\
        data_state_global ts = data_state_global (s:(C,FFI)data_state)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "ts" THEN REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `data_cut_env (fromList [one;one;one])
        (fromList [data_Number (&(LENGTH (vs:data_v list))); v2; data_Number (&(4 * tag))]) =
      SOME (mk_wf (inter (fromList [data_Number (&(LENGTH vs)); v2; data_Number (&(4 * tag))])
                         (fromList [one;one;one])))` ASSUME_TAC THENL
     [REWRITE_TAC[data_cut_env_def; domain_fromList; LENGTH; SUBSET_REFL]; ALL_TAC] THEN
    EXPAND_TAC "s_pop" THEN REWRITE_TAC[cut_locals_def] THEN
    FIRST_ASSUM(let qtm = `data_state_locals (ts:(C,FFI)data_state) =
        fromList [data_Number (&(LENGTH (vs:data_v list))); v2; data_Number (&(4 * tag))]` in fun th -> if concl th = qtm
        then REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_cut_env" (lhs (concl th)) &&
        can (find_term ((=) `fromList [one;one;one]`)) (concl th)
        then REWRITE_TAC[th] else NO_TAC) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[size_of_heap_def; size_of_heap_args_def; stack_to_vs_def; data_state_INFO.ri_accfupds;
                K_THM; ASP3AUX_toList_cut3] THEN
    MAP_EVERY (fun tm -> FIRST_ASSUM(fun th -> if lhs (concl th) = tm then REWRITE_TAC[th] else NO_TAC))
      [`data_state_stack (ts:(C,FFI)data_state)`; `data_state_global (ts:(C,FFI)data_state)`;
       `data_state_limits (ts:(C,FFI)data_state)`; `data_state_refs (ts:(C,FFI)data_state)`] THEN
    REWRITE_TAC[MAP; FLAT; extract_stack_def; GSYM APPEND_ASSOC; APPEND] THEN
    MP_TAC(ISPECL [`data_state_limits (s:(C,FFI)data_state)`; `&(4 * tag):int`]
      (INST_TYPE [`:A`,`:A`] ASP3AUX_small_num_eq)) THEN
    MP_TAC(MATCH_MP ASP3AUX_encode_header_small_int (ASSUME `~(encode_header c (4 * tag) 0 = (NONE:(A word)option))`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[size_of_Number_head];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `n:num`; `l:num`; `ts:(C,FFI)data_state`;
    `wl_call_env [wl_Loc n l; w1; w2; wl_Word (word (16 * tag))]
       (lookup FromList_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
       (wl_push_env (y1,y2) NONE (wl_dec_clock (wl_state_locals_fupd
          (K (insert 1 (wl_Word (word (16 * tag))) (wl_state_locals t))) (tm:(A,C,FFI)wl_state))))`;
    `CONS (l1:num,l2:num) locs`; `tag:num`; `data_Number (&(LENGTH (vs:data_v list)))`; `v2:data_v`;
    `s_pop:(C,FFI)data_state`; `v:data_v`; `s2i:(C,FFI)data_state`; `l1:num`; `l2:num`]
    FromList_thm) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[ASP3AUX_call_env_push_env_fields; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
      FIRST_X_ASSUM(let qtm = `data_state_stack_max (s_pop:(C,FFI)data_state) = data_state_stack_max (ts:(C,FFI)data_state)` in fun th -> if concl th = qtm
        then REWRITE_TAC[GSYM th] else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `rr:(A,C,FFI)wl_state`
    (X_CHOOSE_THEN `new_c:num` (CONJUNCTS_THEN2 (fun th -> ASP3AUX_HIDE_TAC th THEN SUBST1_TAC th) MP_TAC)))) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `q:((A)wl_result)option = SOME NotEnoughSpace` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[distinctness "wl_result"; option_DISTINCT; injectivity "wl_result"]) THENL
   [(STRIP_TAC THEN EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
  EXISTS_TAC `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state)))
     (wl_state_termdep_fupd (K (wl_state_termdep t)) (rr:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `wl_state_ffi (rr:(A,C,FFI)wl_state)`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[ASP3AUX_call_env_push_env_fields; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `data_state_stack_frame_sizes (s_pop:(C,FFI)data_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                data_state_limits s_pop = data_state_limits s /\ data_state_stack s_pop = data_state_stack s /\
                data_state_locals_size s_pop = data_state_locals_size s /\
                data_state_refs s_pop = data_state_refs s /\ data_state_global s_pop = data_state_global s /\
                data_state_locals s_pop = mk_wf (inter (data_state_locals s) (ns:num_set)) /\
                data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max s)
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup FromList_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[call_env_push_env_dec_clock_stack_max] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if free_in `s2i:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
      then MP_TAC(MATCH_MP do_app_FromList_stack_max th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if free_in `s2:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
      then MP_TAC(MATCH_MP do_app_FromList_stack_max th) else NO_TAC) THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; stack_consumed_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_le_stackmax_bridge]; ALL_TAC] THEN
  CONJ_TAC THENL [MP5AUX_HEAD_MESON_TAC[option_le_trans]; ALL_TAC]) THEN
  (STRIP_TAC THEN
  MP_TAC(ISPECL [`v2:data_v`; `vs:data_v list`; `tag:num`;
    `data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s`;
    `v:data_v`; `s2:(C,FFI)data_state`] do_app_FromList_safe) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `size_of_heap_args [data_Number (&(LENGTH (vs:data_v list))); v2] (s_pop:(C,FFI)data_state) =
                size_of_heap_args [data_Number (&(LENGTH vs)); v2]
                  (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s)`
    ASSUME_TAC THENL
   [REWRITE_TAC[size_of_heap_args_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex (:A) DIV 16 <= dimword (:A) DIV 16` ASSUME_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[dimindex_lt_dimword]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_conj (lhand (concl th)) &&
     can (find_term (ASP3AUX_is_app "small_num")) (concl th))) THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  MP_TAC(ARITH_RULE `dimindex (:A) DIV 16 <= dimword (:A) DIV 16 ==>
     (LENGTH (vs:data_v list) < dimindex (:A) DIV 16 ==> LENGTH vs < dimword (:A) DIV 16)`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ARITH_RULE `!a b c:num. a < b + c + 1 ==> ~(b + (c + 1) <= a)`) THEN
  MESON_TAC[]);
    (DISCH_THEN(X_CHOOSE_THEN `rv:A word_loc` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  CASE_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) THEN
  (ASP3AUX_ABBREV_ALL_TAC `Sd = data_state_locals_fupd (K LN) (data_state_locals_size_fupd (K (SOME 0))
      (data_state_clock_fupd (K new_c) (data_state_stack_fupd
        (K (CONS (data_Env (data_state_locals_size (s:(C,FFI)data_state))
                   (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack s)))
        (s2i:(C,FFI)data_state))))`) THEN
  (SUBGOAL_THEN `data_pop_env (Sd:(C,FFI)data_state) = SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) Sd)))` ASSUME_TAC THENL
   [EXPAND_TAC "Sd" THEN REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN CASE_REWRITE_TAC[]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) && free_in `rr:(A,C,FFI)wl_state` (concl th) then
      MP_TAC(SPEC `dest:num` (MATCH_MP state_rel_pop_env_set_var_IMP (CONJ th (ASSUME `data_pop_env (Sd:(C,FFI)data_state) = SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) Sd)))`)))) else NO_TAC)) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num` (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[CONS_11; PAIR_EQ]) ASSUME_TAC)))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) (SUBST_ALL_TAC o SYM))) THEN
  (REWRITE_TAC[ASSUME `wl_pop_env (rr:(A,C,FFI)wl_state) = SOME t2`] THEN CASE_REWRITE_TAC[]) THEN
  (ASP3AUX_UNHIDE_THEN(MP_TAC o REWRITE_RULE[SYM(ASSUME `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
     (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state)) = tm`); call_env_push_env_dec_clock_lift_locals])) THEN
  (DISCH_TAC THEN
  SUBGOAL_THEN `lookup 0 (y1:(A word_loc)spt) = SOME (wl_Loc l1 l2)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) && free_in `y1:(A word_loc)spt` (concl th)
      then MATCH_ACCEPT_TAC(MATCH_MP state_rel_push_env_loc th) else NO_TAC); ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_eq (concl th) && ASP3AUX_is_app "wl_evaluate" (lhs (concl th)) && free_in `rr:(A,C,FFI)wl_state` (concl th) then
     MP_TAC(MATCH_MP evaluate_IMP_domain_union (CONJ th (CONJ (ASSUME `wl_pop_env (rr:(A,C,FFI)wl_state) = SOME t2`)
       (CONJ (ASSUME `lookup 0 (y1:(A word_loc)spt) = SOME (wl_Loc l1 l2)`)
             (ASSUME `cut_envs (adjust_sets (ns:num_set)) (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (y1,y2)`))))) else NO_TAC) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[ASP3AUX_ev_Skip] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`;
     `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state))) (wl_state_termdep_fupd (K (wl_state_termdep t)) (wl_set_vars [adjust_var dest] [rv] (t2:(A,C,FFI)wl_state)))`] THEN
  REWRITE_TAC[option_DISTINCT]) THEN
  (SUBGOAL_THEN `data_state_stack_frame_sizes (s_pop:(C,FFI)data_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                data_state_limits s_pop = data_state_limits s /\ data_state_stack s_pop = data_state_stack s /\
                data_state_locals_size s_pop = data_state_locals_size s /\
                data_state_refs s_pop = data_state_refs s /\ data_state_global s_pop = data_state_global s /\
                data_state_locals s_pop = mk_wf (inter (data_state_locals s) (ns:num_set)) /\
                data_state_ffi s_pop = data_state_ffi s /\ data_state_handler s_pop = data_state_handler s /\
                data_state_code s_pop = data_state_code s /\ data_state_compile s_pop = data_state_compile s /\
                data_state_compile_oracle s_pop = data_state_compile_oracle s /\
                data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max s)
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup FromList_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[call_env_push_env_dec_clock_stack_max] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                wl_state_clock t = data_state_clock s`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if free_in `s2i:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
      then MP_TAC(MATCH_MP do_app_FromList_stack_max th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if free_in `s2:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
      then MP_TAC(MATCH_MP do_app_FromList_stack_max th) else NO_TAC) THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; stack_consumed_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_le_stackmax_bridge]; ALL_TAC]) THEN
  (MATCH_MP_TAC ASP3AUX_state_rel_upd THEN
  EXISTS_TAC `data_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state))) (data_set_var (dest:num) (v:data_v) (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) (Sd:(C,FFI)data_state)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_state_rel_with_clock THEN
    REWRITE_TAC[ASP3AUX_state_rel_termdep; data_to_word_gcProof_set_vars_sing] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC]) THEN
  (FIRST_ASSUM(fun doi -> if is_eq (concl doi) && free_in `s2i:(C,FFI)data_state` (concl doi) && ASP3AUX_is_app "data_do_app" (lhs (concl doi)) then
   FIRST_ASSUM(fun dox -> if is_eq (concl dox) && free_in `s2:(C,FFI)data_state` (concl dox) && ASP3AUX_is_app "data_do_app" (lhs (concl dox)) then
     let vtl = ASSUME `data_v_to_list v2 = SOME (vs:data_v list)` in
     let fx = CONJUNCT2 (REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM] (MATCH_MP do_app_FromList_eq (CONJ vtl dox))) in
     let fi = CONJUNCT2 (MATCH_MP do_app_FromList_eq (CONJ vtl doi)) in
     (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       (REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
        EXPAND_TAC "Sd" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
        REWRITE_TAC([fx; fi; ASSUME `wl_state_clock (t:(A,C,FFI)wl_state) = data_state_clock (s:(C,FFI)data_state)`;
                     ASSUME `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`] @ spf)) (asl,w))
   else NO_TAC) else NO_TAC))]]);;

(* HOL4 line 7813 *)
let not_the_F_option_le = prove
 (`!n m. ~the F (OPTION_MAP ((>) n) m) <=> option_le (SOME n) m`,
  REPEAT GEN_TAC THEN CASES_ON `m:num option` THEN
  REWRITE_TAC[OPTION_MAP_DEF; the_def; option_le_def] THEN ARITH_TAC);;

(* HOL4 line 7819 *)
let the_F_not_option_le = prove
 (`!n m. the F (OPTION_MAP ((>) n) m) <=> ~option_le (SOME n) m`,
  REPEAT GEN_TAC THEN CASES_ON `m:num option` THEN
  REWRITE_TAC[OPTION_MAP_DEF; the_def; option_le_def] THEN ARITH_TAC);;

(* HOL4 line 7828 (local; HOL4's overloads add_space_safe_args and          *)
(* heap_peak_args of dataSem are written out)                               *)
let do_app_RefByte_eq = prove
 (`!fl i (w:byte) (s:(C,FFI)data_state) v s'.
     data_do_app (MemOp (RefByte fl)) [data_Number i; data_Number (&(val w))] s =
       Rval (v,s') ==>
     ?ptr. v = data_RefPtr T ptr /\ ptr = (minimal p. ~(p IN domain (data_state_refs s))) /\
           &0 <= i /\
           s' = data_state_stack_max_fupd
                  (K (OPTION_MAP2 MAX (data_state_stack_max s)
                        (OPTION_MAP2 (+)
                           (stack_consumed (data_state_stack_frame_sizes s)
                              (data_state_limits s) (MemOp (RefByte fl))
                              [data_Number i; data_Number (&(val w))])
                           (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
                              (data_state_locals_size s)))))
                (data_state_refs_fupd
                  (K (insert ptr (bvl_ByteArray fl (REPLICATE (num_of_int i) w))
                        (data_state_refs s)))
                (data_state_space_fupd (K 0)
                (data_state_safe_for_space_fupd
                  (K ((((num_of_int i DIV (arch_size (data_state_limits s) DIV 8) <
                         2 EXP arch_size (data_state_limits s) DIV
                           arch_size (data_state_limits s) /\
                         num_of_int i DIV (arch_size (data_state_limits s) DIV 8) + 1 <
                         2 EXP limits_length_limit (data_state_limits s) /\
                         small_num (limits_arch_64_bit (data_state_limits s)) i) /\
                        no_thunks_in_refs (data_state_refs s) /\
                        (data_state_safe_for_space s /\
                         size_of_heap_args [data_Number i; data_Number (&(val w))] s +
                           space_consumed s (MemOp (RefByte fl))
                             [data_Number i; data_Number (&(val w))] <=
                         limits_heap_limit (data_state_limits s))) /\
                       the F
                         (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                            (OPTION_MAP2 (+)
                               (stack_consumed (data_state_stack_frame_sizes s)
                                  (data_state_limits s) (MemOp (RefByte fl))
                                  [data_Number i; data_Number (&(val w))])
                               (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
                                  (data_state_locals_size s)))))))
                (data_state_peak_heap_length_fupd
                  (K (MAX (data_state_peak_heap_length s)
                        (size_of_heap_args [data_Number i; data_Number (&(val w))] s +
                         space_consumed s (MemOp (RefByte fl))
                           [data_Number i; data_Number (&(val w))])))
                  s))))`,
  REPEAT GEN_TAC THEN ASP3AUX_DO_APP_SPLIT_TAC THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `(minimal p. ~(p IN domain (data_state_refs (s:(C,FFI)data_state))))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[GSYM WORD_IWORD; WORD_VAL; lim_safe_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* HOL4 line 7877 (local) *)
let call_env_push_env_dec_clock_lift = prove
 (`!(args:(A word_loc)list) b y1 y2 (t:(A,C,FFI)wl_state) ck' tp.
     wl_call_env args b (wl_push_env (y1,y2) NONE
       (wl_dec_clock (wl_state_clock_fupd (K ck') (wl_state_termdep_fupd (K tp) t)))) =
     wl_state_clock_fupd (K (ck' - 1))
       (wl_state_termdep_fupd (K tp) (wl_call_env args b (wl_push_env (y1,y2) NONE t)))`,
  MATCH_ACCEPT_TAC ASP3AUX_cpd_lift);;

(* local helper of assign_RefByte (uses do_app_RefByte_eq) *)
let ASP3AUX_do_app_RefByte_fields = prove
 (`!fl i (w:byte) (s:(C,FFI)data_state) v s'.
     data_do_app (MemOp (RefByte fl)) [data_Number i; data_Number (&(val w))] s = Rval (v,s') ==>
     v = data_RefPtr T (minimal p. ~(p IN domain (data_state_refs s))) /\ &0 <= i /\
     data_state_ffi s' = data_state_ffi s /\ data_state_clock s' = data_state_clock s /\
     data_state_handler s' = data_state_handler s /\ data_state_code s' = data_state_code s /\
     data_state_compile s' = data_state_compile s /\
     data_state_compile_oracle s' = data_state_compile_oracle s /\
     data_state_tstamps s' = data_state_tstamps s /\ data_state_locals s' = data_state_locals s /\
     data_state_stack s' = data_state_stack s /\
     data_state_stack_frame_sizes s' = data_state_stack_frame_sizes s /\
     data_state_locals_size s' = data_state_locals_size s /\
     data_state_limits s' = data_state_limits s /\
     data_state_global s' = data_state_global s /\ data_state_space s' = 0 /\
     data_state_refs s' =
       insert (minimal p. ~(p IN domain (data_state_refs s)))
         (bvl_ByteArray fl (REPLICATE (num_of_int i) w)) (data_state_refs s) /\
     data_state_stack_max s' =
       OPTION_MAP2 MAX (data_state_stack_max s)
         (OPTION_MAP2 (+)
            (OPTION_MAP2 MAX (lookup RefByte_location (data_state_stack_frame_sizes s))
                             (lookup Replicate_location (data_state_stack_frame_sizes s)))
            (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) (data_state_locals_size s))) /\
     (data_state_safe_for_space s' ==>
        no_thunks_in_refs (data_state_refs s) /\
        small_num (limits_arch_64_bit (data_state_limits s)) i /\
        num_of_int i DIV (arch_size (data_state_limits s) DIV 8) <
          2 EXP arch_size (data_state_limits s) DIV arch_size (data_state_limits s) /\
        num_of_int i DIV (arch_size (data_state_limits s) DIV 8) + 1 <
          2 EXP limits_length_limit (data_state_limits s) /\
        size_of_heap_args [data_Number i; data_Number (&(val w))] s +
          num_of_int i DIV (arch_size (data_state_limits s) DIV 8) + 2 <=
          limits_heap_limit (data_state_limits s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP do_app_RefByte_eq) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; stack_consumed_def; space_consumed_def] THEN
  REWRITE_TAC[ADD_ASSOC] THEN MESON_TAC[]);;

(* HOL4 line 7889 *)
let assign_RefByte = prove
 (assign_thm_stmt `(?fl. op = MemOp (RefByte fl))`,
  (REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `fl:bool` SUBST_ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN `?ns. names_opt = SOME (ns:num_set)` (X_CHOOSE_THEN `ns:num_set` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (MemOp (RefByte fl)) <=> names_opt:num_set option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:num_set option` THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP do_app_stack_max) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`; `ns:num_set`;
    `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `w:byte` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_do_app_RefByte_vals) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) o
    MATCH_MP ASP3AUX_get_vars_2) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `SUC (SUC 0) = LENGTH (ws:(A word_loc)list)` o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` SUBST_ALL_TAC) o
    REWRITE_RULE[LENGTH_EQ_2]) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_RefByte_def; data_to_word_get_names_def]) THEN
  (MP_TAC(MATCH_MP ASP3AUX_state_rel_conf (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP ASP3AUX_state_rel_limits (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ASP3AUX_ev_Seq] THEN REWRITE_TAC[ASP3AUX_ev_Assign; wl_word_exp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ASP3AUX_ev_MustTerminate; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP lookup_RefByte_location o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt` STRIP_ASSUME_TAC) o
    MATCH_MP cut_env_IMP_cut_envs) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN `~(adjust_var k1 = 1) /\ ~(adjust_var k2 = 1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[adjust_var_def] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASP3AUX_ev_Call; wl_get_vars_def; wl_get_var_def; wl_set_var_def] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[domain_adjust_sets; ALL_DISTINCT; MEM; NOT_IN_EMPTY] THEN
  SIMP[cut_envs_adjust_sets_ODD; ARITH_RULE `ODD 1`] THEN
  ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `data_cut_env (ns:num_set) (data_state_locals (s:(C,FFI)data_state)) =
                SOME (mk_wf (inter (data_state_locals s) (ns:num_set)))` ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_state_opt (SOME ns) (s:(C,FFI)data_state) =
      SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals s) (ns:num_set)))) s)` THEN
    REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `data_cut_env (ns:num_set) (data_state_locals (s:(C,FFI)data_state))` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `tm = wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                     (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state))` THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
       (data_state_clock_fupd (K (MustTerminate_limit (:A))) (s:(C,FFI)data_state))
       (wl_state_locals_fupd (K (insert 1 (wl_Word (if fl then word 0 else word 16)) (wl_state_locals (t:(A,C,FFI)wl_state)))) tm)
       NONE locs` MP_TAC THENL
   [SUBGOAL_THEN `wl_state_locals (t:(A,C,FFI)wl_state) = wl_state_locals (tm:(A,C,FFI)wl_state)`
      (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds]; ALL_TAC] THEN
    REWRITE_TAC[state_rel_insert_1] THEN EXPAND_TAC "tm" THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`NONE:(num#(A)wl_prog#num#num)option`; `c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_clock_fupd (K (MustTerminate_limit (:A))) (s:(C,FFI)data_state)`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word (if fl then word 0 else word 16)) (wl_state_locals (t:(A,C,FFI)wl_state)))) (tm:(A,C,FFI)wl_state)`;
    `locs:(num#num)list`; `[k1;k2]:num list`; `[data_Number i; data_Number (&(val (w:byte)))]`;
    `[w1;w2]:(A word_loc)list`; `ns:num_set`; `mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))`;
    `(y1,y2):((A)word_loc)spt#((A)word_loc)spt`; `n:num`; `l:num`;
    `lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`] state_rel_call_env_push_env) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; MAP; wl_get_vars_def; wl_get_var_def;
                    wl_state_INFO.ri_accfupds; lookup_insert] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[cut_envs_adjust_sets_ODD; ARITH_RULE `ODD 1`];
    REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC]) THEN
  (SUBGOAL_THEN `(if fl then 0 else 4) < dimword (:A) DIV 16` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) &&
      can (find_term (ASP3AUX_is_app "data_call_env")) (concl th) then
      MP_TAC(SPEC `if fl then 0 else 4` (MATCH_MP (REWRITE_RULE[IMP_CONJ] state_rel_IMP_Number_arg) th))
    else NO_TAC) THEN
  ASM_REWRITE_TAC[LENGTH; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `word (4 * (if fl then 0 else 4)):A word = (if fl then word 0 else word 16)` SUBST1_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN DISCH_TAC) THEN
  (ABBREV_TAC `ts = data_call_env [data_Number i; data_Number (&(val (w:byte))); data_Number (&(if fl then 0 else 4))]
      (lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
      (data_push_env (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))) F
        (data_dec_clock (data_state_clock_fupd (K (MustTerminate_limit (:A))) s)))` THEN
  ABBREV_TAC `s_pop = data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set))))
      (data_state_stack_fupd (K (data_state_stack s))
        (data_state_locals_size_fupd (K (data_state_locals_size s)) (ts:(C,FFI)data_state)))` THEN
  SUBGOAL_THEN `data_pop_env (ts:(C,FFI)data_state) = SOME s_pop /\ is_env (HD (data_state_stack ts)) /\
                data_state_tstamps (s_pop:(C,FFI)data_state) = data_state_tstamps (s:(C,FFI)data_state) /\
                data_state_stack_max s_pop = data_state_stack_max ts /\
                data_state_limits ts = data_state_limits s /\
                data_state_refs ts = data_state_refs s /\
                data_state_stack ts = CONS (data_Env (data_state_locals_size s) (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack s)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; data_pop_env_def; is_env_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; HD] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `data_get_vars [0; 1; 2] (data_state_locals (ts:(C,FFI)data_state)) =
                  SOME (APPEND [data_Number i; data_Number (&(val (w:byte)))] [data_Number (&(if fl then 0 else 4))]) /\
                data_state_locals_size ts = lookup RefByte_location (data_state_stack_frame_sizes ts)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; APPEND] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; data_get_vars_def; data_get_var_def; lookup_fromList] THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL; num_CONV `2`; num_CONV `1`] THEN CASE_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_eq (concl th) && free_in `s2:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
     then MP_TAC (REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM] (MATCH_MP ASP3AUX_do_app_RefByte_fields th)) else NO_TAC) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP (ISPECL [`fl:bool`; `i:int`; `w:byte`; `s_pop:(C,FFI)data_state`] ASP3AUX_do_app_RefByte_Rval) (ASSUME `&0 <= (i:int)`)) THEN
  SUBGOAL_THEN `data_state_refs (s_pop:(C,FFI)data_state) = data_state_refs (s:(C,FFI)data_state)` SUBST1_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME `v = data_RefPtr T (minimal p. ~(p IN domain (data_state_refs (s:(C,FFI)data_state))))`)] THEN
  DISCH_THEN(X_CHOOSE_TAC `s2i:(C,FFI)data_state`)) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `n:num`; `l:num`; `ts:(C,FFI)data_state`;
    `wl_call_env [wl_Loc n l; w1; w2; wl_Word (if fl then word 0 else word 16)]
       (lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
       (wl_push_env (y1,y2) NONE (wl_dec_clock (wl_state_locals_fupd
          (K (insert 1 (wl_Word (if fl then word 0 else word 16)) (wl_state_locals t))) (tm:(A,C,FFI)wl_state))))`;
    `CONS (l1:num,l2:num) locs`; `[data_Number i; data_Number (&(val (w:byte)))]`; `fl:bool`;
    `s_pop:(C,FFI)data_state`; `v:data_v`; `s2i:(C,FFI)data_state`; `l1:num`; `l2:num`]
    RefByte_thm) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[ASP3AUX_call_env_push_env_fields; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `rr:(A,C,FFI)wl_state`
    (X_CHOOSE_THEN `new_c:num` (CONJUNCTS_THEN2 (fun th -> ASP3AUX_HIDE_TAC th THEN SUBST1_TAC th) MP_TAC)))) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `q:((A)wl_result)option = SOME NotEnoughSpace` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[distinctness "wl_result"; option_DISTINCT; injectivity "wl_result"]) THENL
  [(STRIP_TAC THEN EXISTS_TAC `SOME NotEnoughSpace:((A)wl_result)option` THEN
  EXISTS_TAC `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state)))
     (wl_state_termdep_fupd (K (wl_state_termdep t)) (rr:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `wl_state_ffi (rr:(A,C,FFI)wl_state)`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[ASP3AUX_call_env_push_env_fields; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `data_state_stack_frame_sizes (s_pop:(C,FFI)data_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                data_state_limits s_pop = data_state_limits s /\ data_state_stack s_pop = data_state_stack s /\
                data_state_locals_size s_pop = data_state_locals_size s /\
                data_state_refs s_pop = data_state_refs s /\ data_state_global s_pop = data_state_global s /\
                data_state_locals s_pop = mk_wf (inter (data_state_locals s) (ns:num_set)) /\
                data_state_ffi s_pop = data_state_ffi s /\ data_state_handler s_pop = data_state_handler s /\
                data_state_code s_pop = data_state_code s /\ data_state_compile s_pop = data_state_compile s /\
                data_state_compile_oracle s_pop = data_state_compile_oracle s /\
                data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max s)
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[call_env_push_env_dec_clock_stack_max] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                wl_state_clock t = data_state_clock s`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `option_le (data_state_stack_max (s2i:(C,FFI)data_state))
     (OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
       (OPTION_MAP2 (+)
         (OPTION_MAP2 MAX (lookup RefByte_location (data_state_stack_frame_sizes s))
                          (lookup Replicate_location (data_state_stack_frame_sizes s)))
         (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) (data_state_locals_size s))))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) && free_in `s2i:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
      then MP_TAC(MATCH_MP ASP3AUX_do_app_RefByte_fields th) else NO_TAC) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(funpow 17 CONJUNCT2 th)]) THEN
    (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       REWRITE_TAC spf (asl,w)) THEN
    REWRITE_TAC[ASSUME `data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`;
                ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state)`] THEN
    REWRITE_TAC[option_le_stackmax_bridge]; ALL_TAC] THEN
  CONJ_TAC THENL [MP5AUX_HEAD_MESON_TAC[option_le_trans]; ALL_TAC]) THEN
  (DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp (concl th) && lhand (concl th) = `data_state_safe_for_space (s2:(C,FFI)data_state)`
    then MP_TAC (MP th (ASSUME `data_state_safe_for_space (s2:(C,FFI)data_state)`)) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_conj (lhand (concl th)) &&
      can (find_term (ASP3AUX_is_app "small_num")) (concl th) then MP_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `size_of_heap (s_pop:(C,FFI)data_state) =
     size_of_heap (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s)`
    SUBST1_TAC THENL
   [REWRITE_TAC[size_of_heap_def; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM] THEN
    (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       REWRITE_TAC spf (asl,w)); ALL_TAC] THEN
  MP_TAC(ISPECL [`[data_Number i; data_Number (&(val (w:byte)))]`;
     `data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s`]
     size_of_heap_LE_args) THEN
  REWRITE_TAC[ASSUME `data_state_limits (s_pop:(C,FFI)data_state) = data_state_limits (s:(C,FFI)data_state)`;
              ASSUME `arch_size (data_state_limits (s:(C,FFI)data_state)) = dimindex (:A)`;
              ASSUME `limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state)) <=> dimindex (:A) = 64`;
              ASSUME `limits_length_limit (data_state_limits (s:(C,FFI)data_state)) = data_to_word_config_len_size c`;
              ASSUME `~(data_to_word_config_gc_kind c = data_to_word_None)`; dimword_def] THEN
  REWRITE_TAC[GSYM INT_NOT_LE; ASSUME `&0 <= (i:int)`] THEN
  DISCH_TAC THEN DISCH_THEN(fun imp -> STRIP_TAC THEN
    MP_TAC (MP imp (ASSUME `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))`))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun tm -> FIRST_ASSUM(fun th -> if concl th = tm then MP_TAC th else NO_TAC))
   [`size_of_heap (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s) <=
     size_of_heap_args [data_Number i; data_Number (&(val (w:byte)))] (data_state_locals_fupd (K (mk_wf (inter (data_state_locals s) ns))) s)`;
    `size_of_heap_args [data_Number i; data_Number (&(val (w:byte)))]
       (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) s) +
     num_of_int i DIV (dimindex (:A) DIV 8) + 2 <= limits_heap_limit (data_state_limits s)`] THEN
  MP_TAC(ARITH_RULE `!S SA a H:num. S <= SA ==> SA + a + 2 <= H ==> ~(H < S + a + 2)`) THEN
  MESON_TAC[]);
   (DISCH_THEN(X_CHOOSE_THEN `rv:A word_loc` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  CASE_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) THEN
  (ASP3AUX_ABBREV_ALL_TAC `Sd = data_state_locals_fupd (K LN) (data_state_locals_size_fupd (K (SOME 0))
      (data_state_clock_fupd (K new_c) (data_state_stack_fupd
        (K (CONS (data_Env (data_state_locals_size (s:(C,FFI)data_state))
                   (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack s)))
        (s2i:(C,FFI)data_state))))`) THEN
  (SUBGOAL_THEN `data_pop_env (Sd:(C,FFI)data_state) = SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) Sd)))` ASSUME_TAC THENL
   [EXPAND_TAC "Sd" THEN REWRITE_TAC[data_pop_env_def; data_state_INFO.ri_accfupds; K_THM] THEN CASE_REWRITE_TAC[]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) && free_in `rr:(A,C,FFI)wl_state` (concl th) then
      MP_TAC(SPEC `dest:num` (MATCH_MP state_rel_pop_env_set_var_IMP (CONJ th (ASSUME `data_pop_env (Sd:(C,FFI)data_state) = SOME (data_state_locals_fupd (K (mk_wf (inter (data_state_locals (s:(C,FFI)data_state)) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) Sd)))`)))) else NO_TAC)) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num` (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[CONS_11; PAIR_EQ]) ASSUME_TAC)))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) (SUBST_ALL_TAC o SYM))) THEN
  (REWRITE_TAC[ASSUME `wl_pop_env (rr:(A,C,FFI)wl_state) = SOME t2`] THEN CASE_REWRITE_TAC[]) THEN
  (ASP3AUX_UNHIDE_THEN(MP_TAC o REWRITE_RULE[SYM(ASSUME `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
     (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state)) = tm`); call_env_push_env_dec_clock_lift_locals])) THEN
  (DISCH_TAC THEN
  SUBGOAL_THEN `lookup 0 (y1:(A word_loc)spt) = SOME (wl_Loc l1 l2)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if ASP3AUX_is_app "data_to_word_gcProof_state_rel" (concl th) && free_in `y1:(A word_loc)spt` (concl th)
      then MATCH_ACCEPT_TAC(MATCH_MP state_rel_push_env_loc th) else NO_TAC); ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_eq (concl th) && ASP3AUX_is_app "wl_evaluate" (lhs (concl th)) && free_in `rr:(A,C,FFI)wl_state` (concl th) then
     MP_TAC(MATCH_MP evaluate_IMP_domain_union (CONJ th (CONJ (ASSUME `wl_pop_env (rr:(A,C,FFI)wl_state) = SOME t2`)
       (CONJ (ASSUME `lookup 0 (y1:(A word_loc)spt) = SOME (wl_Loc l1 l2)`)
             (ASSUME `cut_envs (adjust_sets (ns:num_set)) (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (y1,y2)`))))) else NO_TAC) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[ASP3AUX_ev_Skip] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`;
     `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state))) (wl_state_termdep_fupd (K (wl_state_termdep t)) (wl_set_vars [adjust_var dest] [rv] (t2:(A,C,FFI)wl_state)))`] THEN
  REWRITE_TAC[option_DISTINCT]) THEN
  (SUBGOAL_THEN `data_state_stack_frame_sizes (s_pop:(C,FFI)data_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                data_state_limits s_pop = data_state_limits s /\ data_state_stack s_pop = data_state_stack s /\
                data_state_locals_size s_pop = data_state_locals_size s /\
                data_state_refs s_pop = data_state_refs s /\ data_state_global s_pop = data_state_global s /\
                data_state_locals s_pop = mk_wf (inter (data_state_locals s) (ns:num_set)) /\
                data_state_ffi s_pop = data_state_ffi s /\ data_state_handler s_pop = data_state_handler s /\
                data_state_code s_pop = data_state_code s /\ data_state_compile s_pop = data_state_compile s /\
                data_state_compile_oracle s_pop = data_state_compile_oracle s /\
                data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max s)
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s_pop" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[call_env_push_env_dec_clock_stack_max] THEN
    REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state) /\
                wl_state_clock t = data_state_clock s`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `option_le (data_state_stack_max (s2i:(C,FFI)data_state))
     (OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
       (OPTION_MAP2 (+)
         (OPTION_MAP2 MAX (lookup RefByte_location (data_state_stack_frame_sizes s))
                          (lookup Replicate_location (data_state_stack_frame_sizes s)))
         (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) (data_state_locals_size s))))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) && free_in `s2i:(C,FFI)data_state` (concl th) && ASP3AUX_is_app "data_do_app" (lhs (concl th))
      then MP_TAC(MATCH_MP ASP3AUX_do_app_RefByte_fields th) else NO_TAC) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(funpow 17 CONJUNCT2 th)]) THEN
    (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       REWRITE_TAC spf (asl,w)) THEN
    REWRITE_TAC[ASSUME `data_state_stack_max (ts:(C,FFI)data_state) =
                  OPTION_MAP2 MAX (OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
                     (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s))))
                   (OPTION_MAP2 (+) (OPTION_MAP2 (+) (data_state_locals_size s) (size_of_stack (data_state_stack s)))
                     (lookup RefByte_location (wl_state_stack_size (t:(A,C,FFI)wl_state))))`;
                ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) = data_state_stack_frame_sizes (s:(C,FFI)data_state)`] THEN
    REWRITE_TAC[option_le_stackmax_bridge]; ALL_TAC]) THEN
  (SUBGOAL_THEN `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `data_state_stack_max (s2:(C,FFI)data_state)`
      then REWRITE_TAC[th] else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (MATCH_MP_TAC ASP3AUX_state_rel_upd THEN
  EXISTS_TAC `data_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state))) (data_set_var (dest:num) (data_RefPtr T (minimal p. ~(p IN domain (data_state_refs (s:(C,FFI)data_state))))) (data_state_locals_fupd (K (mk_wf (inter (data_state_locals s) (ns:num_set)))) (data_state_stack_fupd (K (data_state_stack s)) (data_state_locals_size_fupd (K (data_state_locals_size s)) (Sd:(C,FFI)data_state)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_state_rel_with_clock THEN
    REWRITE_TAC[ASP3AUX_state_rel_termdep; data_to_word_gcProof_set_vars_sing] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC]) THEN
  (FIRST_ASSUM(fun doi -> if is_eq (concl doi) && free_in `s2i:(C,FFI)data_state` (concl doi) && ASP3AUX_is_app "data_do_app" (lhs (concl doi)) then
     let fi = MATCH_MP ASP3AUX_do_app_RefByte_fields doi in
     (fun (asl,w) ->
       let sp = `s_pop:(C,FFI)data_state` in
       let s2v = `s2:(C,FFI)data_state` in
       let spf = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = sp then th else failwith "") asl in
       let fx = mapfilter (fun (_,th) -> let c = concl th in
          if is_eq c && is_comb (lhs c) && rand (lhs c) = s2v then th else failwith "") asl in
       (REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
        EXPAND_TAC "Sd" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
        REWRITE_TAC(CONJUNCTS fi @ fx @ spf @
          [ASSUME `wl_state_clock (t:(A,C,FFI)wl_state) = data_state_clock (s:(C,FFI)data_state)`;
           ASSUME `option_le (data_state_stack_max (s2i:(C,FFI)data_state)) (data_state_stack_max (s2:(C,FFI)data_state))`])) (asl,w))
   else NO_TAC))]);;

(* HOL4 line 8151 *)
let lookup_set_var = prove
 (`!x (y:A word_loc) (z:(A,C,FFI)wl_state).
     lookup x (wl_state_locals (wl_set_var x y z)) = SOME y`,
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert]);;

(* HOL4 line 8157 (local) *)
let lookup_2_call_env = prove
 (`!(x:A word_loc) y z ts a1 (a2:(A,C,FFI)wl_state).
     lookup 0 (wl_state_locals (wl_call_env (CONS x ts) a1 a2)) = SOME x /\
     lookup 2 (wl_state_locals (wl_call_env (CONS x (CONS y ts)) a1 a2)) = SOME y /\
     lookup 4 (wl_state_locals (wl_call_env (CONS x (CONS y (CONS z ts))) a1 a2)) =
       SOME z`,
  REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM; lookup_fromList2;
              lookup_fromList] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH; EL; HD; TL] THEN
  REWRITE_TAC[ARITH_RULE `0 < SUC n /\ 1 < SUC (SUC n) /\ 2 < SUC (SUC (SUC n))`] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; EL; HD; TL]);;

(* HOL4 line 8166 (local) *)
let AllocVar_thm_binary = prove
 (`!c l1 l2 s (t:(A,C,FFI)wl_state) locs a1 a2 (x':num_set) xa i vv limit q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env (list_insert [a1; a2] x') (data_state_locals s) = SOME xa /\
     data_get_vars [a1; a2] (data_state_locals s) = SOME [data_Number (&i); vv] /\
     wl_get_var 1 t = SOME (wl_Word (word (4 * i))) /\
     4 * i < dimword (:A) /\
     wl_evaluate (AllocVar c limit (list_insert [a1; a2] x'),t) = (q,r) /\
     limit < dimword (:A) DIV 8 ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\ i < limit /\
       no_thunks_in_refs (data_state_refs s) ==>
       limits_heap_limit (data_state_limits s) <
         size_of_heap_args [data_Number (&i); vv] (cut_locals x' s) + (i + 1))) /\
     (~(q = SOME NotEnoughSpace) ==>
      i < limit /\
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K xa) (data_state_space_fupd (K (i + 1)) s)) r NONE locs /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC AllocVar_thm_nary THEN EXISTS_TAC `[a1; a2]:num list` THEN
  ASM_REWRITE_TAC[]);;
