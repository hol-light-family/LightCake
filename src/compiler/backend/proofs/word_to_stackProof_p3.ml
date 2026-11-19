(* ========================================================================= *)
(* word_to_stackProof_p3: part 3 of 4 (HOL4 lines 6315-10048) of the port  *)
(* of HOL4 compiler/backend/proofs/word_to_stackProofScript.sml (CakeML      *)
(* v3479).  Correctness proof for word_to_stack.                             *)
(* The parts _p1 ... _p4 are loaded one after the other (each needs the     *)
(* previous one).  The notes on the rendering in word_to_stackProof_p1.ml   *)
(* apply here.  W2SP3AUX_ names are local helpers of this part.             *)
(* ========================================================================= *)

needs "compiler/backend/proofs/word_to_stackProof_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 3: HOL4 lines 6315-10048 ===== *)

(* W2SP3AUX: the clause of word_to_stack_comp_def for one constructor (an   *)
(* OCaml helper for the tactics), e.g. w2sp3aux_comp_clause "wl_Tick"       *)
let w2sp3aux_comp_clause c =
  let is_c th =
    try let l = lhs(snd(strip_forall(concl th))) in
        let p = el 2 (snd(strip_comb l)) in
        fst(dest_const(fst(strip_comb p))) = c
    with Failure _ -> false in
  match filter is_c (CONJUNCTS word_to_stack_comp_def) with
    [th] -> th
  | _ -> failwith ("w2sp3aux_comp_clause: " ^ c);;

(* W2SP3AUX: the clause of wl_evaluate_def for one constructor (an OCaml    *)
(* helper for the tactics), e.g. w2sp3aux_wl_eval_clause "ShareInst"        *)
let w2sp3aux_wl_eval_clause c =
  let is_c th =
    try let l = lhs(snd(strip_forall(concl th))) in
        let p = fst(dest_pair(rand l)) in
        fst(dest_const(fst(strip_comb p))) = c
    with Failure _ -> false in
  match filter is_c (CONJUNCTS wl_evaluate_def) with
    [th] -> th
  | _ -> failwith ("w2sp3aux_wl_eval_clause: " ^ c);;

(* W2SP3AUX: the clause of stack_evaluate_def for one constructor (an OCaml *)
(* helper for the tactics), e.g. w2sp3aux_seval "stack_Seq"                  *)
let w2sp3aux_seval c =
  let is_c th =
    try let l = lhs(snd(strip_forall(concl th))) in
        let p = fst(dest_pair(rand l)) in
        fst(dest_const(fst(strip_comb p))) = c
    with Failure _ -> false in
  match filter is_c (CONJUNCTS stack_evaluate_def) with
    [th] -> th
  | _ -> failwith ("w2sp3aux_seval: " ^ c);;

(* W2SP3AUX: the record theorems of the states (HOL4's srw_ss rewrites)   *)
let w2sp3aux_wl_accfupds = (record_info "wl_state").ri_accfupds;;

let w2sp3aux_stack_accfupds = (record_info "stack_state").ri_accfupds;;

let w2sp3aux_buffer_accfupds = (record_info "buffer").ri_accfupds;;

(* HOL4 line 6315: Resume comp_correct[Inst] *)
let word_to_stackProof_comp_correct_Inst = prove
 (word_to_stackProof_comp_case "wl_Inst",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[w2sp3aux_comp_clause "wl_Inst"; w2sp3aux_wl_eval_clause "wl_Inst"; option_case_eq;
      word_to_stackProof_convs_def; max_var_def] THEN
  EXISTS_TAC `0` THEN SIMP[] THEN
  MP_TAC(ISPECL [`i:(A)inst`; `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`;
    `s1:(A,num#C,FFI)wl_state`; `f':num`; `k:num`; `ac:(A)asm_config`; `f:num`;
    `lens:num list`] evaluate_wInst) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* W2SP3AUX: the simple conjuncts of state_rel *)
let W2SP3AUX_state_rel_basic = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> wl_state_clock s = stack_state_clock t /\
         wl_state_gc_fun s = stack_state_gc_fun t /\
         stack_state_ffi t = wl_state_ffi s /\ stack_state_use_stack t /\
         stack_state_use_store t /\ stack_state_use_alloc t /\
         stack_state_memory t = wl_state_memory s /\
         stack_state_mdomain t = wl_state_mdomain s /\ 4 < k /\
         stack_state_sh_mdomain t = wl_state_sh_mdomain s /\
         wl_state_store s = fdomsub (stack_state_store t) Handler /\
         wl_state_termdep s = 0 /\
         stack_state_be t = wl_state_be s /\
         Handler IN FDOM (stack_state_store t) /\
         stack_state_fp_regs t = wl_state_fp_regs s /\
         stack_state_data_buffer t = wl_state_data_buffer s /\
         stack_state_code_buffer t = wl_state_code_buffer s /\
         lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
         lookup wl_store_consts_stub_location (stack_state_code t) =
           SOME (store_consts_stub k) /\
         good_dimindex (:A) /\ 8 <= dimindex (:A) /\
         1 <= LENGTH (stack_state_bitmaps t) /\
         stack_state_stack_space t + f <= LENGTH (stack_state_stack t) /\
         LENGTH (stack_state_stack t) < dimword (:A) /\
         (if f' = 0 then f = 0 else f = f' + 1) /\
         wf (wl_state_locals s)`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 6328: Resume comp_correct[Assign] *)
let word_to_stackProof_comp_correct_Assign = prove
 (word_to_stackProof_comp_case "wl_Assign",
  REWRITE_TAC[flat_exp_conventions_def]);;

(* HOL4 line 6333: Resume comp_correct[Get] *)
let word_to_stackProof_comp_correct_Get = prove
 (word_to_stackProof_comp_case "wl_Get",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[w2sp3aux_comp_clause "wl_Get"; w2sp3aux_wl_eval_clause "wl_Get"; wl_get_store_def;
      option_case_eq; word_to_stackProof_convs_def; max_var_def; is_phy_var_def;
      GSYM EVEN_MOD2; EVEN_EXISTS] THEN
  EXISTS_TAC `0` THEN SIMP[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
    `t:(A,C,FFI)stack_state`; `lens:num list`; `m:num`; `\r:num. stack_Get r name:(A)stack_prog`;
    `a:(A)word_loc`] wRegWrite1_thm1) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Get"] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `FLOOKUP (stack_state_store (t:(A,C,FFI)stack_state)) name = SOME a`
     (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]) THEN
   UNDISCH_TAC `FLOOKUP (wl_state_store (s:(A,num#C,FFI)wl_state)) name = SOME a` THEN
   ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN MESON_TAC[option_DISTINCT];
   STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`t':(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`] THEN
   ASM_REWRITE_TAC[]]);;

(* HOL4 line 6356: Resume comp_correct[Set] *)
let word_to_stackProof_comp_correct_Set = prove
 (word_to_stackProof_comp_case "wl_Set",
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  CASES_ON `exp:(A)wl_exp` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def]) THEN
  GVS[w2sp3aux_comp_clause "wl_Set"; w2sp3aux_wl_eval_clause "wl_Set"; option_case_eq;
      word_to_stackProof_convs_def; max_var_def; max_var_exp_def; every_var_exp_def;
      is_phy_var_def; GSYM EVEN_MOD2; wl_word_exp_def; COND_CASE_EQ; pair_case_eq] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Set"] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t':(A,C,FFI)stack_state`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  SIMP[] THEN MATCH_MP_TAC state_rel_set_store THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6376: Resume comp_correct[OpCurrHeap] *)
let word_to_stackProof_comp_correct_OpCurrHeap = prove
 (word_to_stackProof_comp_case "wl_OpCurrHeap",
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  GVS[w2sp3aux_comp_clause "wl_OpCurrHeap"; w2sp3aux_wl_eval_clause "wl_OpCurrHeap";
      option_case_eq; word_to_stackProof_convs_def; max_var_def; max_var_exp_def;
      every_var_exp_def; is_phy_var_def; GSYM EVEN_MOD2; wl_word_exp_def; the_words_def; MAP;
      COND_CASE_EQ; pair_case_eq; case_eq "word_loc"; wl_get_store_def] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[evaluate_wRegWrite1_seq] THEN
  MP_TAC(ISPEC `wReg1 dst (k,f,f')` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(num#num)list` (X_CHOOSE_THEN `nr:num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_OpCurrHeap"] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t':(A,C,FFI)stack_state`)) (concl th))) THEN
  SUBGOAL_THEN `FLOOKUP (stack_state_store (t':(A,C,FFI)stack_state)) CurrHeap = SOME (wl_Word a')`
    ASSUME_TAC THENL
  [UNDISCH_TAC `FLOOKUP (wl_state_store (s:(A,num#C,FFI)wl_state)) CurrHeap = SOME
    (wl_Word a')` THEN
   ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  ASM_REWRITE_TAC[stack_word_exp_def; MAP] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  MP_TAC(ISPECL [`dst:num`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `nr:num`;
    `ac:(A)asm_config`; `s:(A,num#C,FFI)wl_state`; `t':(A,C,FFI)stack_state`; `lens:num list`;
    `LENGTH (stack_state_stack (t':(A,C,FFI)stack_state))`;
    `stack_state_stack_space (t':(A,C,FFI)stack_state)`; `wl_Word (z:A word)`]
    evaluate_wStackStore_wReg1) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `MAX dst src < 2 * f' + 2 * k` THEN REWRITE_TAC[MAX] THEN ARITH_TAC;
   ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 6405: Resume comp_correct[Store] *)
let word_to_stackProof_comp_correct_Store = prove
 (word_to_stackProof_comp_case "wl_Store",
  REWRITE_TAC[flat_exp_conventions_def]);;

(* HOL4 line 7741 (placed before comp_correct[Tick] of HOL4 line 6410,    *)
(* which uses it here)                                                     *)
let word_to_stackProof_state_rel_dec_clock = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_dec_clock s) (stack_dec_clock t)
           lens extra`,
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_dec_clock_def; stack_dec_clock_def] THEN
  SIMP[] THEN MESON_TAC[]);;

(* HOL4 line 6410: Resume comp_correct[Tick] *)
let word_to_stackProof_comp_correct_Tick = prove
 (word_to_stackProof_comp_case "wl_Tick",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_comp_clause "wl_Tick"; PAIR_EQ]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> can (find_term ((=) `stack_Tick:(A)stack_prog`))
    (concl th))) THEN
  EXISTS_TAC `0` THEN
  UNDISCH_TAC `wl_evaluate (wl_Tick,s:(A,num#C,FFI)wl_state) = res,s1` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Tick"] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `sprog:(A)stack_prog`)) THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Tick"] THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SIMP[wl_flush_state_def; stack_empty_env_def; compile_result_def] THEN
  ASM_MESON_TAC[word_to_stackProof_state_rel_dec_clock]);;

(* HOL4 line 6422: Resume comp_correct[MustTerminate] *)
let word_to_stackProof_comp_correct_MustTerminate = prove
 (word_to_stackProof_comp_case "MustTerminate",
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  UNDISCH_TAC `wl_evaluate (MustTerminate p,s:(A,num#C,FFI)wl_state) = res,s1` THEN
  ASM_REWRITE_TAC[w2sp3aux_wl_eval_clause "MustTerminate"; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let W2SP3AUX_SEQ_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `post_alloc_conventions k (c1:(A)wl_prog) /\ post_alloc_conventions k c2 /\
                flat_exp_conventions c1 /\ flat_exp_conventions (c2:(A)wl_prog) /\
                max_var c1 < 2 * f' + 2 * k /\ max_var c2 < 2 * f' + 2 * k` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `post_alloc_conventions k (wl_Seq c1 c2:(A)wl_prog)` THEN
   UNDISCH_TAC `flat_exp_conventions (wl_Seq c1 c2:(A)wl_prog)` THEN
   UNDISCH_TAC `max_var (wl_Seq c1 c2:(A)wl_prog) < 2 * f' + 2 * k` THEN
   REWRITE_TAC[post_alloc_conventions_def; call_arg_convention_def; flat_exp_conventions_def;
               wl_every_var_def; every_stack_var_def; max_var_def; MAX] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `word_to_stack_comp ac F (wl_Seq c1 c2) (bs,n) (k,f,f') =
               (sprog:(A)stack_prog,bs',n')` THEN
  REWRITE_TAC[w2sp3aux_comp_clause "wl_Seq"] THEN
  MP_TAC(ISPEC `word_to_stack_comp ac F c1 (bs,n) (k,f,f'):(A)stack_prog#(A word)app_list#num`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `bn1:(A word)app_list#num`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `bn1:(A word)app_list#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bs1:(A word)app_list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def] THEN
  MP_TAC(ISPEC `word_to_stack_comp ac F c2 (bs1,n1) (k,f,f'):(A)stack_prog#(A word)app_list#num`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)stack_prog` (X_CHOOSE_THEN `bn2:(A word)app_list#num`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; UNION_SUBSET]) THEN
  UNDISCH_TAC `wl_evaluate (wl_Seq c1 c2,s:(A,num#C,FFI)wl_state) = res,s1` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Seq"] THEN
  MP_TAC(ISPEC `wl_evaluate (c1,s:(A,num#C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option` (X_CHOOSE_THEN `s2:(A,num#C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c1:(A)wl_prog`; `(bs:(A word)app_list,n:num)`;
    `(k:num,f:num,f':num)`; `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`]
    comp_IMP_isPREFIX) THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c2:(A)wl_prog`; `(bs1:(A word)app_list,n1:num)`;
    `(k:num,f:num,f':num)`; `q2:(A)stack_prog`; `(bs':(A word)app_list,n':num)`]
    comp_IMP_isPREFIX) THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c1:(A)wl_prog`; `(bs:(A word)app_list,n:num)`;
    `(k:num,f:num,f':num)`; `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`]
    comp_IMP_LENGTH) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c2:(A)wl_prog`; `(bs1:(A word)app_list,n1:num)`;
    `(k:num,f:num,f':num)`; `q2:(A)stack_prog`; `(bs':(A word)app_list,n':num)`]
    comp_IMP_LENGTH) THEN
  ASM_REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `append (bs1:(A word)app_list) <<=
                DROP (n - LENGTH (append (bs:(A word)app_list)))
                  (stack_state_bitmaps (t:(A,C,FFI)stack_state))` ASSUME_TAC THENL
  [ASM_MESON_TAC[IS_PREFIX_TRANS]; ALL_TAC];;

(* W2SP3AUX: the stack_evaluate term of an assumption about program p *)
let w2sp3aux_is_seval_of p th =
  is_eq (concl th) && can (find_term ((=) p)) (lhs(concl th)) &&
  (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_evaluate"
   with Failure _ -> false);;

(* HOL4 line 6429: Resume comp_correct[Seq] *)
let word_to_stackProof_comp_correct_Seq = prove
 (word_to_stackProof_comp_case "wl_Seq",
  W2SP3AUX_SEQ_SETUP_TAC THEN
  ASM_CASES_TAC `r1:((A)wl_result)option = NONE` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
     check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
   SUBGOAL_THEN `wl_state_handler (s2:(A,num#C,FFI)wl_state) =
                 wl_state_handler (s:(A,num#C,FFI)wl_state)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c1:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
   REMOVE_THEN "IH1" (MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `NONE:((A)wl_result)option`;
     `s2:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `bs:(A word)app_list`; `n:num`;
     `bs1:(A word)app_list`; `n1:num`; `q1:(A)stack_prog`; `lens:num list`]) THEN
   ASM_REWRITE_TAC[option_DISTINCT; OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
     (X_CHOOSE_THEN `res1:((A)stack_result)option` STRIP_ASSUME_TAC))) THEN
   ASM_CASES_TAC `res1:((A)stack_result)option = NONE` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[] o check (is_cond o concl)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
      check (w2sp3aux_is_seval_of `q1:(A)stack_prog`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM]) THEN
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
      `s1:(A,num#C,FFI)wl_state`; `t1:(A,C,FFI)stack_state`; `bs1:(A word)app_list`; `n1:num`;
      `bs':(A word)app_list`; `n':num`; `q2:(A)stack_prog`; `lens:num list`] o
      C MATCH_MP (ASSUME `wl_evaluate (c1,s:(A,num#C,FFI)wl_state) = NONE,s2`) o
      SPEC `s2:(A,num#C,FFI)wl_state`) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IS_PREFIX_LENGTH; LE_TRANS];
      ASM_MESON_TAC[IS_PREFIX_TRANS; isPREFIX_DROP];
      ASM_MESON_TAC[SUBSET_TRANS; loc_check_SUBSET]];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t2:(A,C,FFI)stack_state`
      (X_CHOOSE_THEN `res2:((A)stack_result)option` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t2:(A,C,FFI)stack_state`;
                          `res2:((A)stack_result)option`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ck':num` o MATCH_MP stack_evaluate_add_clock_NONE o
      check (w2sp3aux_is_seval_of `q1:(A)stack_prog`)) THEN
    SIMP[ADD_ASSOC] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[w2sp3aux_seval "stack_Seq"; pair_CASE_def; FST; SND];
    MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `res1:((A)stack_result)option`] THEN
    ASM_REWRITE_TAC[w2sp3aux_seval "stack_Seq"; pair_CASE_def; FST; SND] THEN
    SUBGOAL_THEN `~(NONE = res1:((A)stack_result)option)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
      check (fun th -> can (find_term ((=) `t:(A,C,FFI)stack_state`)) (concl th) &&
                       can (find_term ((=) `word_to_stackProof_state_rel:(A)asm_config->num->num->
                         num->(A,num#C,FFI)wl_state->(A,C,FFI)stack_state->num list->num->bool`))
                         (concl th))) THEN
    SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) = res1)`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
     ASM_SIMP_TAC[compile_result_NOT_2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[IS_PREFIX_TRANS; wl_evaluate_io_events_mono];
     ASM_MESON_TAC[evaluate_stack_limit_stack_max]]];
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
   REMOVE_THEN "IH1" (MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
     `s1:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `bs:(A word)app_list`; `n:num`;
     `bs1:(A word)app_list`; `n1:num`; `q1:(A)stack_prog`; `lens:num list`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
     (X_CHOOSE_THEN `res1:((A)stack_result)option` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `res1:((A)stack_result)option`] THEN
   ASM_REWRITE_TAC[w2sp3aux_seval "stack_Seq"; pair_CASE_def; FST; SND] THEN
   SUBGOAL_THEN `~(res1:((A)stack_result)option = NONE)` (fun th -> REWRITE_TAC[th]) THEN
   ASM_CASES_TAC `OPTION_MAP compile_result (res:((A)wl_result)option) = res1` THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[OPTION_MAP_EQ_NONE];
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]]]);;

(* W2SP3AUX: a term contains a constant of the given name *)
let w2sp3aux_has_const c tm =
  can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false)) tm;;

(* W2SP3AUX: the state relation after Return (HOL4's first conjunct of the *)
(* Return case)                                                             *)
let W2SP3AUX_Return_state_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens ms ys.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     LENGTH (ys:((A)word_loc)list) = LENGTH (ms:num list) /\ LENGTH ms < f' + k
     ==> word_to_stackProof_state_rel ac k 0 0 (wl_flush_state F s)
           (stack_state_stack_space_fupd
              (K (stack_state_stack_space t + skip_free (k,f,f') ms)) t)
           lens (LENGTH ys - (k - 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def; wl_flush_state_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[wf_def; lookup_def; option_DISTINCT] THEN
  SUBGOAL_THEN `skip_free (k,f,f':num) (ms:num list) + (LENGTH ms - (k - 1)) = f /\
                skip_free (k,f,f':num) ms <= f` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[skip_free_def; num_stack_ret_def] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + f <=
                LENGTH (stack_state_stack t)` THEN
   UNDISCH_TAC `skip_free (k,f,f':num) (ms:num list) <= f` THEN ARITH_TAC;
   UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
       (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
       (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
   REWRITE_TAC[stack_size_rel_def; IS_SOME_DEF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                  (stack_state_stack_space t + skip_free (k,f,f':num) (ms:num list))) - 0 -
                 (LENGTH ms - (k - 1)) =
                 ((LENGTH (stack_state_stack t) - stack_state_stack_space t) - f) - 0`
     SUBST1_TAC THENL
   [UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + f <=
                 LENGTH (stack_state_stack t)` THEN
    UNDISCH_TAC `skip_free (k,f,f':num) (ms:num list) + (LENGTH ms - (k - 1)) = f` THEN
    ARITH_TAC;
    ASM_MESON_TAC[]];
   REWRITE_TAC[DROP_DROP_T] THEN
   SUBGOAL_THEN `0 + (stack_state_stack_space (t:(A,C,FFI)stack_state) +
                      skip_free (k,f,f':num) (ms:num list)) + LENGTH ms - (k - 1) =
                 f + stack_state_stack_space t + 0` SUBST1_TAC THENL
   [UNDISCH_TAC `skip_free (k,f,f':num) (ms:num list) + (LENGTH ms - (k - 1)) = f` THEN
    ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
    REWRITE_TAC[DROP_DROP_T]]]);;

(* W2SP3AUX: an element of get_vars *)
let W2SP3AUX_get_vars_EL = prove
 (`!ms (s:(A,C,FFI)wl_state) ys i.
     wl_get_vars ms s = SOME ys /\ i < LENGTH ys
     ==> wl_get_var (EL i ms) s = SOME (EL i ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; option_INJ] THEN REPEAT GEN_TAC THENL
  [STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LT]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `wl_get_var h (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_get_vars t (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[option_DISTINCT;
    option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(ISPEC `i:num` num_CASES) THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LT_SUC]) THEN ASM_REWRITE_TAC[EL; HD; TL] THEN
  ASM_MESON_TAC[]);;

(* W2SP3AUX: the returned values after Return (HOL4's second part of the   *)
(* Return case)                                                             *)
let W2SP3AUX_Return_values = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens ms ys.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_get_vars ms s = SOME ys /\
     ms = list_of_seq (\x. 2 * (x + 1)) (LENGTH ms) /\ LENGTH ms < f' + k
     ==> !i. i < LENGTH ys
             ==> if i + 1 < k then FLOOKUP (stack_state_regs t) (i + 1) = SOME (EL i ys)
                 else oEL (LENGTH ys - (i + 1))
                        (DROP (stack_state_stack_space t + skip_free (k,f,f') ms)
                           (stack_state_stack t)) = SOME (EL i ys)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_length_lemma) THEN
  SUBGOAL_THEN `wl_get_var (2 * (i + 1)) (s:(A,num#C,FFI)wl_state) = SOME (EL i
    (ys:((A)word_loc)list))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`ms:num list`; `s:(A,num#C,FFI)wl_state`; `ys:((A)word_loc)list`; `i:num`]
     W2SP3AUX_get_vars_EL) THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `EL i (ms:num list) = 2 * (i + 1)` (fun th -> REWRITE_TAC[th]) THEN
   FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `ms:num list` then
     ONCE_REWRITE_TAC[th] else NO_TAC) THEN
   MATCH_MP_TAC EL_GENLIST THEN ASM_MESON_TAC[LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  COND_CASES_TAC THENL
  [MATCH_MP_TAC state_rel_get_var_imp THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                 (t:(A,C,FFI)stack_state) lens 0` THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`2 * (i + 1)`; `EL i (ys:((A)word_loc)list)`] o
    check (fun th -> w2sp3aux_has_const "EVEN" (concl th) && is_forall (concl th))) THEN
  UNDISCH_TAC `wl_get_var (2 * (i + 1)) (s:(A,num#C,FFI)wl_state) = SOME (EL i
    (ys:((A)word_loc)list))` THEN
  REWRITE_TAC[wl_get_var_def] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP oEL_TAKE_E o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[oEL_DROP] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> oEL a (l:((A)word_loc)list) = x ==> oEL b l = x`) THEN
  REWRITE_TAC[skip_free_def; num_stack_ret_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_ARITH_TAC);;

(* HOL4 line 6494: Resume comp_correct[Return] *)
let word_to_stackProof_comp_correct_Return = prove
 (word_to_stackProof_comp_case "wl_Return",
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  GVS[w2sp3aux_comp_clause "wl_Return"; w2sp3aux_wl_eval_clause "wl_Return";
      option_case_eq; case_eq "word_loc"; pair_case_eq; word_to_stackProof_convs_def; max_var_def;
      is_phy_var_def; GSYM EVEN_MOD2] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  SUBGOAL_THEN `LENGTH (ms:num list) < f' + k` ASSUME_TAC THENL
  [MP_TAC(AP_TERM `MAX_LIST`
     (ASSUME `ms = list_of_seq (\x. 2 * (x + 1)) (LENGTH (ms:num list))`)) THEN
   REWRITE_TAC[MAX_LIST_GENLIST_evens2] THEN
   UNDISCH_TAC `MAX n (MAX_LIST ms) < 2 * f' + 2 * k` THEN REWRITE_TAC[MAX] THEN ARITH_TAC;
   ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t':(A,C,FFI)stack_state`)) (concl th))) THEN
  SUBGOAL_THEN `skip_free (k,f,f':num) (ms:num list) <= f` ASSUME_TAC THENL
  [REWRITE_TAC[skip_free_def] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`t':(A,C,FFI)stack_state`; `skip_free (k,f,f':num) (ms:num list)`;
                 `stack_Return y:(A)stack_prog`] evaluate_SeqStackFree) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t':(A,C,FFI)stack_state)) <
                  stack_state_stack_space t' + skip_free (k,f,f':num) (ms:num list))`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackFree"] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o
    check (fun th -> is_neg(concl th) && w2sp3aux_has_const "skip_free" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pair_CASE_def; FST; SND; w2sp3aux_seval "stack_Return"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  REWRITE_TAC[stack_get_var_def; w2sp3aux_stack_accfupds] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN SIMP[compile_result_def] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
    `stack_state_stack_space (t':(A,C,FFI)stack_state) =
     stack_state_stack_space (t:(A,C,FFI)stack_state)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_length_lemma) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC W2SP3AUX_Return_state_rel THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC W2SP3AUX_Return_values THEN
   MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `s:(A,num#C,FFI)wl_state`; `lens:num list`] THEN
   ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 line 6581 *)
let stack_rel_aux_stack_size = prove
 (`!len k (frame:((A)stack_frame)list) bits.
     stack_rel_aux len k frame bits
     ==> the (handler_val bits) (wl_stack_size frame) = handler_val bits`,
  MATCH_MP_TAC stack_rel_aux_ind THEN
  REWRITE_TAC[stack_rel_aux_def; stack_size_eq; handler_val_def; the_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  MP_TAC(ISPEC `n:num option` option_CASES) THEN
  MP_TAC(ISPEC `wl_stack_size (xs:((A)stack_frame)list)` option_CASES) THEN
  REPEAT STRIP_TAC THEN GVS[the_def; OPTION_MAP2_THM; OPTION_MAP_DEF] THEN
  ARITH_TAC);;

(* HOL4 line 6592 *)
let abs_stack_CONS_NIL = prove
 (`!(bm:(A word)list) (x:(B)stack_frame) rest l. abs_stack bm (CONS x rest) [] l = NONE`,
  REWRITE_TAC[abs_stack_def]);;

(* HOL4 line 6600 *)
let SUB_ADD_EQ = prove
 (`!a b. a <= b ==> a + (b - a) = b`,
  ARITH_TAC);;

(* HOL4 line 6606 *)
let abs_stack_LENGTH = prove
 (`!(bitmaps:(A word)list) (wstack:((B)stack_frame)list) tstack lens astack.
     abs_stack bitmaps wstack tstack lens = SOME astack
     ==> handler_val astack = LENGTH tstack`,
  MATCH_MP_TAC abs_stack_ind THEN REWRITE_TAC[abs_stack_def] THEN
  REPEAT STRIP_TAC THEN GVS[COND_CASE_EQ; option_case_eq; list_case_eq] THEN
  ASM_REWRITE_TAC[handler_val_def; LENGTH_TAKE_EQ; LENGTH] THEN ASM_ARITH_TAC);;

(* HOL4 line 6616 *)
let abs_stack_empty' = prove
 (`!(bs:(A word)list) (xs:((B)stack_frame)list) lens stack.
     abs_stack bs xs [] lens = SOME stack <=> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP abs_stack_LENGTH) THEN
  REWRITE_TAC[LENGTH] THEN SPEC_TAC(`stack:(((A)word_loc#(A)word_loc)option#bool
    list#((A)word_loc)list)list`,
           `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`) THEN
  MATCH_MP_TAC handler_val_ind THEN REWRITE_TAC[handler_val_def] THEN ARITH_TAC);;

(* The raise stub, run from the call of Raise (used for HOL4 6626).         *)
let W2SP3AUX_raise_stub_eval = prove
 (`!k (t:(A,C,FFI)stack_state) hv l3 l4.
     lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
     stack_state_use_stack t /\ stack_state_use_store t /\
     FLOOKUP (stack_state_store t) Handler =
       SOME (wl_Word (word (LENGTH (stack_state_stack t) - hv))) /\
     LENGTH (stack_state_stack t) < dimword (:A) /\
     3 <= hv /\ 3 <= LENGTH (stack_state_stack t) /\
     EL ((LENGTH (stack_state_stack t) - hv) + 1) (stack_state_stack t) = wl_Loc l3 l4
     ==> stack_evaluate (stack_Call NONE (INL raise_stub_location) NONE,
                         stack_state_clock_fupd (K (stack_state_clock t + 1)) t) =
         (SOME (stack_Exception (wl_Loc l3 l4)),
          stack_state_regs_fupd (K (stack_state_regs t |+ (k,wl_Loc l3 l4)))
           (stack_state_store_fupd
             (K (stack_state_store t |+
                 (Handler,EL ((LENGTH (stack_state_stack t) - hv) + 2) (stack_state_stack t))))
            (stack_state_stack_space_fupd (K ((LENGTH (stack_state_stack t) - hv) + 3)) t)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word (LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) - hv):A word) =
                LENGTH (stack_state_stack t) - hv` ASSUME_TAC THENL
  [REWRITE_TAC[w2n_n2w] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <= LENGTH (stack_state_stack t) - hv) /\
    LENGTH (stack_state_stack t) - hv + 2 < LENGTH (stack_state_stack t) /\
    LENGTH (stack_state_stack t) - hv + 1 < LENGTH (stack_state_stack t) /\
    ~(LENGTH (stack_state_stack t) < LENGTH (stack_state_stack t) - hv + 3)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Call"; stack_find_code_def] THEN
  SIMP[stack_dec_clock_def; ADD_SUB] THEN
  REWRITE_TAC[raise_stub_F] THEN ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  SIMP[w2sp3aux_seval "stack_Get"; stack_set_var_def] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  SIMP[w2sp3aux_seval "StackSetSize"; stack_get_var_def; stack_set_var_def; FLOOKUP_UPDATE] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN SIMP[w2sp3aux_seval "stack_Skip"] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  SIMP[w2sp3aux_seval "StackLoad"; stack_set_var_def] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  SIMP[w2sp3aux_seval "stack_Set"; stack_get_var_def; FLOOKUP_UPDATE; stack_set_store_def] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  SIMP[w2sp3aux_seval "StackLoad"; stack_set_var_def] THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN SIMP[w2sp3aux_seval "StackFree"] THEN
  SIMP[w2sp3aux_seval "stack_Raise"; stack_get_var_def; FLOOKUP_UPDATE;
       stack_bad_fun_return_def]);;

(* The word and stack states after a Raise are related (used for HOL4 6626).  *)
let W2SP3AUX_raise_state_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens m e0 e h1 l1 l2 xs rr.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_state_handler s < LENGTH (wl_state_stack s) /\
     LASTN (wl_state_handler s + 1) (wl_state_stack s) =
       CONS (StackFrame m e0 e (SOME (h1,l1,l2))) xs
     ==> ?hv. 3 <= hv /\ 3 <= LENGTH (stack_state_stack t) /\
              FLOOKUP (stack_state_store t) Handler =
                SOME (wl_Word (word (LENGTH (stack_state_stack t) - hv))) /\
              EL ((LENGTH (stack_state_stack t) - hv) + 1) (stack_state_stack t) = wl_Loc l1 l2 /\
              word_to_stackProof_state_rel ac k 0 0
                (push_locals e0 e
                  (wl_state_handler_fupd (K h1)
                    (wl_state_locals_fupd (K (union (fromAList e) (fromAList e0)))
                      (wl_state_stack_fupd (K xs) (wl_state_locals_size_fupd (K m) s)))))
                (stack_state_regs_fupd (K rr)
                  (stack_state_store_fupd
                    (K (stack_state_store t |+
                        (Handler,EL ((LENGTH (stack_state_stack t) - hv) + 2)
                                    (stack_state_stack t))))
                    (stack_state_stack_space_fupd
                       (K ((LENGTH (stack_state_stack t) - hv) + 3)) t)))
                (LASTN (wl_state_handler s + 1) lens) 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  SUBGOAL_THEN
   `?astack. abs_stack (stack_state_bitmaps t) (wl_state_stack s)
       (DROP (stack_state_stack_space (t:(A,C,FFI)stack_state) + f) (stack_state_stack t)) lens =
       SOME astack /\
     stack_rel_aux k (LENGTH (stack_state_stack t)) (wl_state_stack (s:(A,num#C,FFI)wl_state))
       astack /\
     ALL sorted_env (wl_state_stack s) /\
     (is_handler_frame (EL (LENGTH (wl_state_stack s) - (wl_state_handler s + 1))
                           (wl_state_stack s))
      ==> FLOOKUP (stack_state_store t) Handler =
          SOME (wl_Word (word (LENGTH (stack_state_stack t) -
                               handler_val (LASTN (wl_state_handler s + 1) astack))))) /\
     stack_size_rel f (wl_state_locals_size s) (wl_state_stack_limit s)
       (wl_state_stack_max s) (wl_state_stack s)
       (stack_state_stack t) (stack_state_stack_space t) 0`
  STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                  (t:(A,C,FFI)stack_state) lens 0` THEN
   REWRITE_TAC[word_to_stackProof_state_rel_def; word_to_stackProof_stack_rel_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[DROP_DROP_T; ADD_CLAUSES] THEN
   STRIP_TAC THEN
   EXISTS_TAC `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
   REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `SORTED (\x y. FST x > FST y) (e:(num#(A)word_loc)list) /\
                ALL sorted_env (xs:((A)stack_frame)list)` STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`wl_state_stack (s:(A,num#C,FFI)wl_state)`;
                  `CONS (StackFrame m e0 e (SOME (h1,l1,l2))) (xs:((A)stack_frame)list)`;
                  `sorted_env:(A)stack_frame->bool`; `wl_state_handler
                    (s:(A,num#C,FFI)wl_state) + 1`]
                 EVERY_IMP_EVERY_LASTN) THEN
   ASM_REWRITE_TAC[ALL; sorted_env_def] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `is_handler_frame (EL (LENGTH (wl_state_stack (s:(A,num#C,FFI)wl_state)) -
                                      (wl_state_handler s + 1)) (wl_state_stack s))`
   ASSUME_TAC THENL
  [MP_TAC(ISPECL [`wl_state_stack (s:(A,num#C,FFI)wl_state)`;
                  `wl_state_handler (s:(A,num#C,FFI)wl_state) + 1`] LASTN_HD) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `wl_state_handler (s:(A,num#C,FFI)wl_state) < LENGTH (wl_state_stack s)` THEN
    ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[HD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[is_handler_frame_def];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`stack_state_stack_space (t:(A,C,FFI)stack_state) + f`;
                 `stack_state_stack (t:(A,C,FFI)stack_state)`;
                 `wl_state_handler (s:(A,num#C,FFI)wl_state)`;
                 `wl_state_stack (s:(A,num#C,FFI)wl_state)`;
                 `e:(num#(A)word_loc)list`; `m:num option`; `e0:(num#(A)word_loc)list`;
                 `h1:num`; `l1:num`; `l2:num`; `xs:((A)stack_frame)list`;
                 `stack_state_bitmaps (t:(A,C,FFI)stack_state)`; `lens:num list`;
                 `astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`;
                 `k:num`] stack_rel_raise) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `wl_state_handler (s:(A,num#C,FFI)wl_state) < LENGTH (wl_state_stack s)` THEN
   ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FST (env_to_list (fromAList e) (K I)) = (e:(num#(A)word_loc)list)`
   SUBST1_TAC THENL
  [MP_TAC(ISPEC `fromAList (e:(num#(A)word_loc)list)` env_to_list_K_I_IMP) THEN
   DISCH_THEN(MP_TAC o SPECL
     [`FST (env_to_list (fromAList (e:(num#(A)word_loc)list)) (K I))`;
      `SND (env_to_list (fromAList (e:(num#(A)word_loc)list)) (K I))`]) THEN
   REWRITE_TAC[PAIR] THEN STRIP_TAC THEN MATCH_MP_TAC SORTED_FST_PERM_IMP_ALIST_EQ THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ex:(A)word_loc#(A)word_loc`
    (X_CHOOSE_THEN `payload:bool list#((A)word_loc)list` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `hv = handler_val (LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state) + 1)
                  (astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list))` THEN
  EXISTS_TAC `hv:num` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!sm. wl_state_stack_max (s:(A,num#C,FFI)wl_state) = SOME sm
         ==> wl_stack_size (CONS (StackFrame m e0 e NONE) (xs:((A)stack_frame)list)) =
             SOME (LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                   (LENGTH (stack_state_stack t) - hv + 3)) /\
             LENGTH (stack_state_stack t) - (LENGTH (stack_state_stack t) - hv + 3) <= sm`
   ASSUME_TAC THENL
  [X_GEN_TAC `sm:num` THEN DISCH_TAC THEN
   UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
     (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
     (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
   REWRITE_TAC[stack_size_rel_def] THEN
   DISCH_THEN(MP_TAC o SPEC `sm:num` o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ss:num` STRIP_ASSUME_TAC o CONJUNCT2)) THEN
   MP_TAC(ISPECL [`wl_state_handler (s:(A,num#C,FFI)wl_state) + 1`;
                  `wl_state_stack (s:(A,num#C,FFI)wl_state)`;
                  `CONS (StackFrame m e0 e (SOME (h1,l1,l2))) (xs:((A)stack_frame)list)`; `ss:num`]
                 LASTN_stack_size_SOME) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `wl_state_handler (s:(A,num#C,FFI)wl_state) < LENGTH (wl_state_stack s)` THEN
    ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[stack_size_eq; OPTION_MAP2_SOME] THEN
   DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC `OPTION_MAP ((+) 3) m = SOME (x1:num)` THEN REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`k:num`; `LENGTH (stack_state_stack (t:(A,C,FFI)stack_state))`;
                  `CONS (StackFrame m e0 e NONE) (xs:((A)stack_frame)list)`;
                  `CONS (NONE,payload) (LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state))
                      (astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list))`]
                 stack_rel_aux_stack_size) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`stack_state_bitmaps (t:(A,C,FFI)stack_state)`;
                  `CONS (StackFrame m e0 e NONE) (xs:((A)stack_frame)list)`;
                  `DROP (LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) - hv + 3)
                        (stack_state_stack t)`;
                  `LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state) + 1) (lens:num list)`;
                  `CONS (NONE,payload) (LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state))
                      (astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list))`]
                 abs_stack_LENGTH) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[stack_size_eq; OPTION_MAP2_THM; the_def; LENGTH_DROP] THEN
   DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
   CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`m1:num`; `x2:num`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   UNDISCH_TAC `m1 + x2 = LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                          (LENGTH (stack_state_stack t) - hv + 3)` THEN
   UNDISCH_TAC `LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) - stack_state_stack_space t -
                f - 0 <= sm` THEN
   UNDISCH_TAC `y <= ss:num` THEN
   UNDISCH_TAC `ss = LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                     stack_state_stack_space t - f - 0` THEN
   UNDISCH_TAC `y = x1 + x2:num` THEN UNDISCH_TAC `x1 = 3 + m1` THEN ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                 (t:(A,C,FFI)stack_state) lens 0` THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; word_to_stackProof_stack_rel_def;
              push_locals_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[DOMSUB_FUPDATE; FDOM_FUPDATE; IN_INSERT; FLOOKUP_UPDATE; wf_def; lookup_def;
                  option_DISTINCT; DROP_0; ADD_CLAUSES] THEN
  SUBGOAL_THEN `LENGTH (LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state))
     (astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list)) =
     LENGTH (xs:((A)stack_frame)list)` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o MATCH_MP abs_stack_IMP_LENGTH o
     check (fun th -> w2sp3aux_has_const "abs_stack" (concl th) &&
                      w2sp3aux_has_const "NONE" (concl th))) THEN
   REWRITE_TAC[LENGTH; SUC_INJ] THEN SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `3 <= hv` THEN
   UNDISCH_TAC `3 <= LENGTH (stack_state_stack (t:(A,C,FFI)stack_state))` THEN ARITH_TAC;
   UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
     (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
     (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
   REWRITE_TAC[stack_size_rel_def; IS_SOME_DEF; SUB_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `sm:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `sm:num` o check (fun th -> is_forall(concl th) &&
      w2sp3aux_has_const "wl_stack_size" (concl th) &&
      w2sp3aux_has_const "StackFrame" (concl th))) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1];
   ASM_REWRITE_TAC[ALL; sorted_env_def];
   EXISTS_TAC `CONS (NONE,payload) (LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state))
                 (astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list))` THEN
   ASM_REWRITE_TAC[LENGTH; option_INJ] THEN STRIP_TAC THEN
   ASM_CASES_TAC `h1 + 1 = SUC (LENGTH (xs:((A)stack_frame)list))` THENL
   [UNDISCH_TAC `is_handler_frame (EL (SUC (LENGTH (xs:((A)stack_frame)list)) - (h1 + 1))
                   (CONS (StackFrame m e0 e NONE) xs))` THEN
    ASM_REWRITE_TAC[SUB_REFL; EL; HD; is_handler_frame_def]; ALL_TAC] THEN
   SUBGOAL_THEN `h1 < LENGTH (xs:((A)stack_frame)list) /\
                 SUC (LENGTH xs) - (h1 + 1) = SUC (LENGTH xs - (h1 + 1))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `h1 < SUC (LENGTH (xs:((A)stack_frame)list))` THEN
    UNDISCH_TAC `~(h1 + 1 = SUC (LENGTH (xs:((A)stack_frame)list)))` THEN ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `!x. LASTN (h1 + 1) (CONS x (LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state))
       (astack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list))) =
       LASTN (h1 + 1) (LASTN (wl_state_handler s) astack)` ASSUME_TAC THENL
   [MATCH_MP_TAC LASTN_CONS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `h1 < LENGTH (xs:((A)stack_frame)list)` THEN ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `is_handler_frame (EL (SUC (LENGTH (xs:((A)stack_frame)list)) - (h1 + 1))
                   (CONS (StackFrame m e0 e NONE) xs))` THEN
   ASM_REWRITE_TAC[EL; TL] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
     w2sp3aux_has_const "is_handler_frame" (concl th) &&
     w2sp3aux_has_const "wl_Word" (concl th) &&
     not (w2sp3aux_has_const "FLOOKUP" (concl th)))) THEN
   ASM_REWRITE_TAC[]]);;

(* HOL4 line 6626: Resume comp_correct[Raise] *)
let word_to_stackProof_comp_correct_Raise = prove
 (word_to_stackProof_comp_case "wl_Raise",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[w2sp3aux_comp_clause "wl_Raise"; w2sp3aux_wl_eval_clause "wl_Raise"; wl_jump_exc_def;
      option_case_eq; pair_case_eq; list_case_eq; case_eq "stack_frame"; COND_CASE_EQ;
      word_to_stackProof_convs_def; post_alloc_conventions_def; call_arg_convention_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`; `a0:num option`;
                 `a1:(num#(A)word_loc)list`; `a2:(num#(A)word_loc)list`; `x:num`; `x'':num`;
                 `y':num`; `a1:((A)stack_frame)list`;
                 `stack_state_regs (t:(A,C,FFI)stack_state) |+ (k,wl_Loc x'' y')`]
                W2SP3AUX_raise_state_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hv:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `t:(A,C,FFI)stack_state`; `hv:num`; `x'':num`; `y':num`]
                W2SP3AUX_raise_stub_eval) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `1` THEN ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  MAP_EVERY EXISTS_TAC [`a1:(num#(A)word_loc)list`; `a2:(num#(A)word_loc)list`] THEN
  REWRITE_TAC[FLOOKUP_UPDATE; w2sp3aux_stack_accfupds; K_THM] THEN
  SUBGOAL_THEN `~(k = 1)` (fun th -> REWRITE_TAC[th]) THENL
  [UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "push_locals" o concl)) THEN SIMP[];
   MATCH_MP_TAC state_rel_get_var_imp THEN
   MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
                         `s:(A,num#C,FFI)wl_state`; `lens:num list`; `0`] THEN
   ASM_REWRITE_TAC[ARITH_RULE `2 * 1 = 2`] THEN UNDISCH_TAC `4 < k` THEN ARITH_TAC]);;

(* HOL4 line 6743.  HOL4 const_inst r w (stackLang overload) is             *)
(* stack_Inst (asm_Const r w).                                               *)
let evaluate_const_inst = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra i.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (stack_Inst (asm_Const (k + 1) i),t) = (NONE,t') /\
           stack_state_clock t = stack_state_clock t' /\
           word_to_stackProof_state_rel ac k f f' s t' lens extra /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t /\
           stack_get_var (k + 1) t' = SOME (wl_Word i)`,
  REPEAT STRIP_TAC THEN
  SIMP[stack_evaluate_def; stack_inst_def; stack_assign_def; stack_word_exp_def]);;

(* HOL4 line 6758 *)
let evaluate_const_inst_clock = prove
 (`!k (i:A word) (t:(A,C,FFI)stack_state) clk.
     stack_evaluate (stack_Inst (asm_Const k i),stack_state_clock_fupd (K clk) t) =
     (I ## (\t. stack_state_clock_fupd (K clk) t))
       (stack_evaluate (stack_Inst (asm_Const k i),t))`,
  SIMP[stack_evaluate_def; stack_inst_def; stack_assign_def; stack_word_exp_def;
       PAIR_MAP_THM; stack_set_var_def]);;

(* W2SP3AUX: arithmetic of MAX and max3 *)
let W2SP3AUX_MAX_LT = prove
 (`!a b c. MAX a b < c <=> a < c /\ b < c`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

let W2SP3AUX_max3_LT = prove
 (`!a b c d. max3 a b c < d <=> a < d /\ b < d /\ c < d`,
  REWRITE_TAC[max3_def] THEN ARITH_TAC);;

(* W2SP3AUX: the end of each case of comp_correct[If] (an OCaml tactic): the *)
(* registers are loaded in the stack state tf (assumptions                   *)
(* stack_get_var r' tf = SOME a, stack_get_var_imm ri tf = SOME yv,           *)
(* subspt (stack_state_code t) (stack_state_code tf) and                     *)
(* stack_state_bitmaps tf = stack_state_bitmaps t); evaluate the If and use   *)
(* the induction hypothesis of the branch taken                              *)
let w2sp3aux_if_tail_tac (tf:term) (ri:term) (yv:term) : tactic =
  let subst_tf tm = vsubst [tf,`tf:(A,C,FFI)stack_state`; ri,`ri:(A)reg_imm`;
                            yv,`yv:(A)word_loc`] tm in
  SUBGOAL_THEN (subst_tf
    `!c. stack_get_var r' (stack_state_clock_fupd (K c) (tf:(A,C,FFI)stack_state)) =
           SOME (a:(A)word_loc) /\
         stack_get_var_imm (ri:(A)reg_imm) (stack_state_clock_fupd (K c) tf) = SOME yv`)
    (fun th -> REWRITE_TAC[w2sp3aux_seval "stack_If"; th]) THENL
  [FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_get_var_imm"
      with Failure _ -> false))) THEN
   FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     (try let c,args = strip_comb(lhs(concl th)) in
          fst(dest_const c) = "stack_get_var" && hd args = `r':num`
      with Failure _ -> false))) THEN
   REWRITE_TAC[stack_get_var_imm_def; stack_get_var_def; w2sp3aux_stack_accfupds; K_THM] THEN
   SIMP_TAC[];
   ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_cond(lhs(concl th)) then
    MP_TAC th else NO_TAC) THEN
  COND_CASES_TAC THEN DISCH_TAC THENL
  [REMOVE_THEN "IH1" (MP_TAC o SPECL [`a:(A)word_loc`; yv; `a'':bool`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
     `s1:(A,num#C,FFI)wl_state`; tf; `bs:(A word)app_list`; `n:num`;
     `bs1:(A word)app_list`; `n1:num`; `q1:(A)stack_prog`; `lens:num list`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `append (bs':(A word)app_list)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `loc_check (stack_state_code (t:(A,C,FFI)stack_state))` THEN
    ASM_SIMP_TAC[loc_check_SUBSET]];
   REMOVE_THEN "IH2" (MP_TAC o SPECL [`a:(A)word_loc`; yv; `a'':bool`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
     `s1:(A,num#C,FFI)wl_state`; tf; `bs1:(A word)app_list`; `n1:num`;
     `bs':(A word)app_list`; `n':num`; `q2:(A)stack_prog`; `lens:num list`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `loc_check (stack_state_code (t:(A,C,FFI)stack_state))` THEN
   ASM_SIMP_TAC[loc_check_SUBSET]];;

(* W2SP3AUX: the code grows and the bitmaps stay along two stack runs *)
let W2SP3AUX_mono2 = prove
 (`!p1 p2 (t:(A,C,FFI)stack_state) t1 t2 r1 r2.
     stack_evaluate (p1,t) = (r1,t1) /\ stack_evaluate (p2,t1) = (r2,t2)
     ==> subspt (stack_state_code t) (stack_state_code t2)`,
  MESON_TAC[stack_evaluate_mono; subspt_trans]);;

(* HOL4 line 6767: Resume comp_correct[If] *)
let word_to_stackProof_comp_correct_If = prove
 (word_to_stackProof_comp_case "wl_If",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `post_alloc_conventions k (c1:(A)wl_prog) /\ post_alloc_conventions k c2 /\
                flat_exp_conventions c1 /\ flat_exp_conventions (c2:(A)wl_prog) /\
                max_var c1 < 2 * f' + 2 * k /\ max_var c2 < 2 * f' + 2 * k /\
                EVEN r1 /\ r1 < 2 * f' + 2 * k /\
                (!r. (ri:(A)reg_imm) = Reg r ==> EVEN r /\ r < 2 * f' + 2 * k)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `post_alloc_conventions k (wl_If cmp r1 ri c1 c2:(A)wl_prog)` THEN
   UNDISCH_TAC `flat_exp_conventions (wl_If cmp r1 ri c1 c2:(A)wl_prog)` THEN
   UNDISCH_TAC `max_var (wl_If cmp r1 ri c1 c2:(A)wl_prog) < 2 * f' + 2 * k` THEN
   REWRITE_TAC[post_alloc_conventions_def; call_arg_convention_def; flat_exp_conventions_def;
               wl_every_var_def; every_stack_var_def; max_var_def; W2SP3AUX_max3_LT;
               is_phy_var_def; GSYM EVEN_MOD2] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CASES_ON `ri:(A)reg_imm` THEN REWRITE_TAC[every_var_imm_def] THEN
   CASE_REWRITE_TAC[W2SP3AUX_MAX_LT; W2SP3AUX_max3_LT] THEN REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[is_phy_var_def; GSYM EVEN_MOD2]) THEN
   RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `word_to_stack_comp ac F (wl_If cmp r1 ri c1 c2) (bs,n) (k,f,f') =
               (sprog:(A)stack_prog,bs',n')` THEN
  REWRITE_TAC[w2sp3aux_comp_clause "wl_If"] THEN
  MP_TAC(ISPEC `wReg1 r1 (k,f,f')` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:(num#num)list` (X_CHOOSE_THEN `r':num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `word_to_stack_comp ac F c1 (bs,n) (k,f,f'):(A)stack_prog#(A word)app_list#num`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `bn1:(A word)app_list#num`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `bn1:(A word)app_list#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bs1:(A word)app_list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `word_to_stack_comp ac F c2 (bs1,n1) (k,f,f'):(A)stack_prog#(A word)app_list#num`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)stack_prog` (X_CHOOSE_THEN `bn2:(A word)app_list#num`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `bn2:(A word)app_list#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bs2:(A word)app_list` (X_CHOOSE_THEN `n2:num` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `append (bs:(A word)app_list) <<= append bs1 /\
                append (bs1:(A word)app_list) <<= append bs2` STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c1:(A)wl_prog`; `(bs:(A word)app_list,n:num)`;
     `(k:num,f:num,f':num)`; `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`]
     comp_IMP_isPREFIX) THEN
   MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c2:(A)wl_prog`; `(bs1:(A word)app_list,n1:num)`;
     `(k:num,f:num,f':num)`; `q2:(A)stack_prog`; `(bs2:(A word)app_list,n2:num)`]
     comp_IMP_isPREFIX) THEN
   ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (append (bs1:(A word)app_list)) <= n1 /\
                n1 - LENGTH (append bs1) = n - LENGTH (append (bs:(A word)app_list)) /\
                LENGTH (append (bs2:(A word)app_list)) <= n2 /\
                n2 - LENGTH (append bs2) = n - LENGTH (append bs)` STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c1:(A)wl_prog`; `(bs:(A word)app_list,n:num)`;
     `(k:num,f:num,f':num)`; `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`]
     comp_IMP_LENGTH) THEN
   MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `c2:(A)wl_prog`; `(bs1:(A word)app_list,n1:num)`;
     `(k:num,f:num,f':num)`; `q2:(A)stack_prog`; `(bs2:(A word)app_list,n2:num)`]
     comp_IMP_LENGTH) THEN
   ASM_REWRITE_TAC[FST; SND] THEN
   UNDISCH_TAC `LENGTH (append (bs:(A word)app_list)) <= n` THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `wl_evaluate (wl_If cmp r1 ri c1 c2,s:(A,num#C,FFI)wl_state) = res,s1` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_If"] THEN
  CASES_ON `wl_get_var r1 (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `wl_get_var_imm ri (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `wl_word_cmp cmp (a:(A)word_loc) a'` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `r2:num` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `i:A word` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
  [(* Reg *)
   MP_TAC(ISPEC `wReg2 r2 (k,f,f')` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:(num#num)list` (X_CHOOSE_THEN `nr:num` ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "wStackLoad" o concl)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; get_labels_wStackLoad; UNION_SUBSET;
                                wl_get_var_imm_def]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o SPEC `r2:num` o
      check (fun th -> is_forall(concl th) && w2sp3aux_has_const "EVEN" (concl th))) THEN
    DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
    DRULE_ALL evaluate_wStackLoad_wReg2 THEN STRIP_TAC THEN
    REWRITE_TAC[wStackLoad_append; o_THM] THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
    REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_wStackLoad_clock] THEN
    ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
    ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
    REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_wStackLoad_clock] THEN
    ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
    SUBGOAL_THEN `stack_get_var r' (t'':(A,C,FFI)stack_state) = SOME (a:(A)word_loc) /\
                  stack_get_var_imm (Reg nr) (t'':(A,C,FFI)stack_state) = SOME (a':(A)word_loc) /\
                  subspt (stack_state_code (t:(A,C,FFI)stack_state)) (stack_state_code t'') /\
                  stack_state_bitmaps t'' = stack_state_bitmaps t` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[stack_get_var_imm_def] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `r':num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `k + 1`)) (concl th) && w2sp3aux_has_const "stack_get_var"
          (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC W2SP3AUX_mono2 THEN
      MAP_EVERY EXISTS_TAC [`wStackLoad x1 stack_Skip:(A)stack_prog`;
        `wStackLoad x2 stack_Skip:(A)stack_prog`;
        `t':(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`;
          `NONE:((A)stack_result)option`] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    w2sp3aux_if_tail_tac `t'':(A,C,FFI)stack_state` `Reg nr:(A)reg_imm` `a':(A)word_loc`;
   (* Imm *)
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_imm_def; option_INJ]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) =
      `a':(A)word_loc`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "wStackLoad" o concl)) THEN
    ASM_CASES_TAC `asm_config_valid_imm (ac:(A)asm_config) (INR cmp) i` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; get_labels_wStackLoad; UNION_SUBSET]) THENL
    [DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
     ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
     REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_wStackLoad_clock] THEN
     ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
     SUBGOAL_THEN `stack_get_var r' (t':(A,C,FFI)stack_state) = SOME (a:(A)word_loc) /\
                   stack_get_var_imm (Imm i) (t':(A,C,FFI)stack_state) = SOME (wl_Word i) /\
                   subspt (stack_state_code (t:(A,C,FFI)stack_state)) (stack_state_code t') /\
                   stack_state_bitmaps t' = stack_state_bitmaps t` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[stack_get_var_imm_def] THEN
      MP_TAC(MATCH_MP stack_evaluate_mono (ASSUME
        `stack_evaluate (wStackLoad x1 stack_Skip,t:(A,C,FFI)stack_state) = NONE,t'`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
     w2sp3aux_if_tail_tac `t':(A,C,FFI)stack_state` `Imm i:(A)reg_imm` `wl_Word (i:A word)`;
     SUBGOAL_THEN `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                        (stack_set_var (k + 1) (wl_Word i) (t:(A,C,FFI)stack_state)) lens 0`
                          ASSUME_TAC THENL
        [ASM_REWRITE_TAC[state_rel_set_var_k]; ALL_TAC] THEN
        DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
        REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_const_inst_clock] THEN
        REWRITE_TAC[w2sp3aux_seval "stack_Inst"; stack_inst_def; stack_assign_def;
          stack_word_exp_def] THEN
        CASE_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
        ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
        REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_wStackLoad_clock] THEN
        ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[stack_set_var_def; w2sp3aux_stack_accfupds; K_THM]) THEN
        SUBGOAL_THEN `stack_state_clock (t':(A,C,FFI)stack_state) = stack_state_clock
          (t:(A,C,FFI)stack_state)`
          (fun th -> REWRITE_TAC[GSYM th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `stack_get_var r' (t':(A,C,FFI)stack_state) = SOME (a:(A)word_loc) /\
                      stack_get_var_imm (Reg (k + 1)) (t':(A,C,FFI)stack_state) = SOME
                        (wl_Word i) /\
                      subspt (stack_state_code (t:(A,C,FFI)stack_state)) (stack_state_code t') /\
                      stack_state_bitmaps t' = stack_state_bitmaps t` STRIP_ASSUME_TAC THENL
        [ASM_REWRITE_TAC[stack_get_var_imm_def] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `k + 1` o check (fun th -> is_forall(concl th) &&
            w2sp3aux_has_const "stack_get_var" (concl th) && can (find_term ((=) `~(r = k:num)`))
              (concl th))) THEN
          REWRITE_TAC[ARITH_RULE `~(k + 1 = k)`; stack_get_var_def; FLOOKUP_UPDATE;
                      w2sp3aux_stack_accfupds; K_THM];
          MP_TAC(MATCH_MP stack_evaluate_mono (ASSUME
            `stack_evaluate (wStackLoad x1 stack_Skip,
               stack_state_regs_fupd (K (stack_state_regs t |+ (k + 1,wl_Word i)))
                 (t:(A,C,FFI)stack_state)) = NONE,t'`)) THEN
          REWRITE_TAC[w2sp3aux_stack_accfupds] THEN SIMP_TAC[]];
         ALL_TAC] THEN
        w2sp3aux_if_tail_tac `t':(A,C,FFI)stack_state` `Reg (k + 1):(A)reg_imm`
          `wl_Word (i:A word)`]]);;

(* W2SP3AUX: a goal ?t1 res1. evaluate = (res1,t1) /\ if ~(NONE = res1) ... *)
(* from a NONE result                                                        *)
let W2SP3AUX_NONE_INTRO = prove
 (`!p (t:(A,C,FFI)stack_state) P Q.
     (?t1. stack_evaluate (p,t) = (NONE,t1) /\ P t1)
     ==> ?t1 res1. stack_evaluate (p,t) = (res1,t1) /\
                   (if ~(NONE = res1) then Q res1 t1 else P t1)`,
  MESON_TAC[]);;

(* HOL4 line 6905: Resume comp_correct[LocValue] *)
let word_to_stackProof_comp_correct_LocValue = prove
 (word_to_stackProof_comp_case "wl_LocValue",
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  GVS[w2sp3aux_comp_clause "wl_LocValue"; w2sp3aux_wl_eval_clause "wl_LocValue";
      word_to_stackProof_convs_def; max_var_def; is_phy_var_def; GSYM EVEN_MOD2; EVEN_EXISTS;
      COND_CASE_EQ] THEN
  MATCH_MP_TAC W2SP3AUX_NONE_INTRO THEN MATCH_MP_TAC wRegWrite1_thm1_weak THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[w2sp3aux_seval "stack_LocValue"; loc_check_def] THEN
  SUBGOAL_THEN `l1 IN domain (stack_state_code (t:(A,C,FFI)stack_state))`
    (fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_code_domain) THEN ASM SET_TAC[]);;

(* HOL4 line 6925 (HOL4 Abbrev (y = P) is the plain equation y = P) *)
let EXISTS_PULL_FORALL1 = prove
 (`!(P:B) (Q:A->B->bool).
     (?x. !y. y = P ==> Q x y) <=> (!y. y = P ==> ?x. Q x y)`,
  MESON_TAC[]);;

(* HOL4 line 6931 *)
let EXISTS_PULL_FORALL2 = prove
 (`!(P:B#C) (Q:A->B->C->bool).
     (?x. !y z. P = (y,z) ==> Q x y z) <=> (!y z. P = (y,z) ==> ?x. Q x y z)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 6937 *)
let EXISTS_PULL_FORALL3 = prove
 (`!(P:B#C#D) (Q:A->B->C->D->bool).
     (?x. !y z a. P = (y,z,a) ==> Q x y z a) <=> (!y z a. P = (y,z,a) ==> ?x. Q x y z a)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* The compile and compile_oracle fields at an Install (used for HOL4 6943) *)
let W2SP3AUX_install_compile = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens cfg progs bytes data cfg'.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_state_compile_oracle s 0 = (cfg,progs) /\
     wl_state_compile s cfg progs = SOME (bytes,data,cfg')
     ==> ?progs' fs bmr1 bmr2 c2.
           compile_word_to_stack ac F k progs (Nil,FST cfg) = (progs',fs,bmr1,bmr2) /\
           stack_state_compile_oracle t 0 = (SND cfg,progs',append bmr1) /\
           stack_state_compile t (SND cfg) progs' = SOME (bytes,c2) /\
           data = append bmr1 /\ cfg' = (bmr2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_state_compile (s:(A,num#C,FFI)wl_state) cfg progs = SOME (bytes,data,cfg')` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `cfg:num#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bm0:num` (X_CHOOSE_THEN `c0:C` SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `?progs' fs bmr1 bmr2.
                  compile_word_to_stack ac F k (progs:(num#num#(A)wl_prog)list) (Nil,bm0) =
                  (progs',fs,bmr1,bmr2)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST; SND; pair_CASE_def] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[pair_CASE_def; FST; SND; OPTION_MAP_EQ_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:byte list#C` MP_TAC) THEN
  MP_TAC(ISPEC `z:byte list#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:byte list` (X_CHOOSE_THEN `z2:C` SUBST1_TAC)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`progs':(num#(A)stack_prog)list`; `fs:num list`;
                        `bmr1:(A word)app_list`; `bmr2:num`; `z2:C`] THEN
  ASM_REWRITE_TAC[]);;

(* The stack Install instruction (used for HOL4 6943) *)
let W2SP3AUX_install_eval = prove
 (`!(t:(A,C,FFI)stack_state) r3 r4 w1 w2 w3 w4 c0 progs' bm bytes cb db c2 kk sprog rest'.
     stack_get_var 1 t = SOME (wl_Word w1) /\ stack_get_var 2 t = SOME (wl_Word w2) /\
     stack_get_var r3 t = SOME (wl_Word w3) /\ stack_get_var r4 t = SOME (wl_Word w4) /\
     stack_state_compile_oracle t 0 = (c0,progs',bm) /\
     buffer_flush (stack_state_code_buffer t) w1 w2 = SOME (bytes,cb) /\
     stack_state_use_stack t /\
     buffer_flush (stack_state_data_buffer t) w3 w4 = SOME (bm,db) /\
     stack_state_compile t c0 progs' = SOME (bytes,c2) /\
     progs' = CONS (kk,sprog) rest' /\
     FST (stack_state_compile_oracle t 1) = c2
     ==> stack_evaluate (stack_Install 1 2 r3 r4 0,t) =
         (NONE,
          stack_state_regs_fupd
            (K (DRESTRICT (stack_state_regs t) (stack_state_ffi_save_regs t) |+ (1,wl_Loc kk 0)))
           (stack_state_fp_regs_fupd (K FEMPTY)
           (stack_state_bitmaps_fupd (K (APPEND (stack_state_bitmaps t) bm))
           (stack_state_compile_oracle_fupd (K (shift_seq 1 (stack_state_compile_oracle t)))
           (stack_state_code_buffer_fupd (K cb)
           (stack_state_data_buffer_fupd (K db)
           (stack_state_code_fupd (K (union (stack_state_code t) (fromAList progs'))) t)))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `progs' = CONS (kk,sprog) (rest':(num#(A)stack_prog)list)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Install"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* Inversion of a successful word Install (used for HOL4 6943) *)
let W2SP3AUX_Install_inv = prove
 (`!ptr len dptr dlen names (s:(A,num#C,FFI)wl_state) res s1.
     wl_evaluate (wl_Install ptr len dptr dlen names,s) = (res,s1) /\ ~(res = SOME wl_Error)
     ==> ?env w1 w2 w3 w4 cfg progs bytes cb data db cfg' kk prog rest.
           wl_cut_env names (wl_state_locals s) = SOME env /\
           wl_get_var ptr s = SOME (wl_Word w1) /\ wl_get_var len s = SOME (wl_Word w2) /\
           wl_get_var dptr s = SOME (wl_Word w3) /\ wl_get_var dlen s = SOME (wl_Word w4) /\
           wl_state_compile_oracle s 0 = (cfg,progs) /\
           buffer_flush (wl_state_code_buffer s) w1 w2 = SOME (bytes,cb) /\
           buffer_flush (wl_state_data_buffer s) w3 w4 = SOME (data,db) /\
           wl_state_compile s cfg progs = SOME (bytes,data,cfg') /\
           progs = CONS (kk,prog) rest /\
           FST (wl_state_compile_oracle s 1) = cfg' /\
           res = NONE /\
           s1 = wl_state_code_buffer_fupd (K cb)
                 (wl_state_data_buffer_fupd (K db)
                 (wl_state_code_fupd (K (union (wl_state_code s) (fromAList progs)))
                 (wl_state_locals_fupd (K (insert ptr (wl_Loc kk 0) env))
                 (wl_state_fp_regs_fupd (K FEMPTY)
                 (wl_state_compile_oracle_fupd (K (shift_seq 1 (wl_state_compile_oracle s)))
                 (wl_state_stack_max_fupd (K NONE)
                 (wl_state_stack_size_fupd (K LN) s)))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Install"] THEN STRIP_TAC THEN
  GVS[option_case_eq; case_eq "word_loc"; pair_case_eq; list_case_eq; COND_CASE_EQ] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES]);;

(* The stack compile_oracle config is the second half of the word one       *)
let W2SP3AUX_co_FST = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra n.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> FST (stack_state_compile_oracle t n) = SND (FST (wl_state_compile_oracle s n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?bm0 c0 progs. wl_state_compile_oracle (s:(A,num#C,FFI)wl_state) n =
                  ((bm0,c0),progs)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE_def] THEN
  SUBGOAL_THEN `?progs' fs bmr. compile_word_to_stack ac F k
                  (progs:(num#num#(A)wl_prog)list) (Nil,bm0) = (progs',fs,bmr)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE_def; FST; SND]);;

(* An ALL fact at an ALOOKUP hit (used for HOL4 6943) *)
let W2SP3AUX_ALOOKUP_ALL = prove
 (`!(P:num#B->bool) l n v. ALL P l /\ ALOOKUP l n = SOME v ==> P (n,v)`,
  REWRITE_TAC[EVERY_MEM] THEN MESON_TAC[ALOOKUP_MEM]);;

(* W2SP3AUX: lookups in a cut environment *)
let W2SP3AUX_cut_env_lookup = prove
 (`!names (l:((A)word_loc)spt) env n v.
     wl_cut_env names l = SOME env /\ lookup n env = SOME v
     ==> lookup n l = SOME v /\ (n IN domain (FST names) \/ n IN domain (SND names))`,
  REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN REPEAT GEN_TAC THEN
  GVS[COND_CASE_EQ; option_case_eq; pair_case_eq] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[lookup_union; lookup_inter_alt] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `lookup n (l:((A)word_loc)spt)` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ]);;

(* W2SP3AUX: a cut environment is wf *)
let W2SP3AUX_cut_env_wf = prove
 (`!names (l:((A)word_loc)spt) env. wl_cut_env names l = SOME env ==> wf env`,
  REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN REPEAT GEN_TAC THEN
  GVS[COND_CASE_EQ; option_case_eq; pair_case_eq] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
  MATCH_MP_TAC wf_union THEN REWRITE_TAC[wf_inter]);;

(* W2SP3AUX: the names of a cutset above twice k *)
let W2SP3AUX_ALL_toAList_domain = prove
 (`!P (t:B spt) n. ALL P (MAP FST (toAList t)) /\ n IN domain t ==> P n`,
  REWRITE_TAC[EVERY_MEM; toAList_domain] THEN MESON_TAC[]);;

(* The word and stack states after an Install are related (HOL4 6943)    *)
let W2SP3AUX_install_state_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens names env cfg kk prog rest
     cb db progs' fs bmr1 bmr2 c2 w3 w4.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_cut_env names (wl_state_locals s) = SOME env /\
     ALL (\x. x >= 2 * k) (MAP FST (toAList (FST names))) /\
     ALL (\x. x >= 2 * k) (MAP FST (toAList (SND names))) /\
     wl_state_compile_oracle s 0 = (cfg,CONS (kk,prog) rest) /\
     compile_word_to_stack ac F k (CONS (kk,prog) rest) (Nil,FST cfg) = (progs',fs,bmr1,bmr2) /\
     stack_state_compile_oracle t 0 = (SND cfg,progs',append bmr1) /\
     FST (wl_state_compile_oracle s 1) = (bmr2,c2) /\
     buffer_flush (wl_state_data_buffer s) w3 w4 = SOME (append bmr1,db)
     ==> word_to_stackProof_state_rel ac k f f'
           (wl_state_code_buffer_fupd (K cb)
           (wl_state_data_buffer_fupd (K db)
           (wl_state_code_fupd (K (union (wl_state_code s) (fromAList (CONS (kk,prog) rest))))
           (wl_state_locals_fupd (K (insert 2 (wl_Loc kk 0) env))
           (wl_state_fp_regs_fupd (K FEMPTY)
           (wl_state_compile_oracle_fupd (K (shift_seq 1 (wl_state_compile_oracle s)))
           (wl_state_stack_max_fupd (K NONE)
           (wl_state_stack_size_fupd (K LN) s))))))))
           (stack_state_regs_fupd
             (K (DRESTRICT (stack_state_regs t) (stack_state_ffi_save_regs t) |+ (1,wl_Loc kk 0)))
           (stack_state_fp_regs_fupd (K FEMPTY)
           (stack_state_bitmaps_fupd (K (APPEND (stack_state_bitmaps t) (append bmr1)))
           (stack_state_compile_oracle_fupd (K (shift_seq 1 (stack_state_compile_oracle t)))
           (stack_state_code_buffer_fupd (K cb)
           (stack_state_data_buffer_fupd (K db)
           (stack_state_code_fupd (K (union (stack_state_code t) (fromAList progs'))) t)))))))
           lens 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `cfg:num#C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `b0:num` (X_CHOOSE_THEN `c0:C` SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP3AUX_cut_env_wf) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MAP_FST_compile_word_to_stack o
       check (w2sp3aux_has_const "compile_word_to_stack" o concl)) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`CONS (kk,prog) (rest:(num#num#(A)wl_prog)list)`; `k:num`;
      `Nil:(A word)app_list`;
                   `b0:num`; `progs':(num#(A)stack_prog)list`; `fs:num list`;
                   `bmr1:(A word)app_list`; `bmr2:num`; `ac:(A)asm_config`; `F`]
                  compile_word_to_stack_IMP_LENGTH) THEN
    ASM_REWRITE_TAC[append_thm; LENGTH; LE_0; SUB_0] THEN STRIP_TAC THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                  (t:(A,C,FFI)stack_state) lens 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    SUBGOAL_THEN `b0 = LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
        w2sp3aux_has_const "post_alloc_conventions" (concl th) &&
        w2sp3aux_has_const "wl_state_compile_oracle" (concl th))) THEN
     ASM_REWRITE_TAC[pair_CASE_def] THEN SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [
  (* 0 *) REWRITE_TAC[shift_seq_def; FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC[];
  (* 1 *) X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1` o check (fun th -> is_forall (concl th) &&
       w2sp3aux_has_const "post_alloc_conventions" (concl th) &&
       w2sp3aux_has_const "wl_state_compile_oracle" (concl th))) THEN
    REWRITE_TAC[shift_seq_def] THEN BETA_TAC THEN
    SUBGOAL_THEN `?bm1 c1 ps1. wl_state_compile_oracle (s:(A,num#C,FFI)wl_state) (n + 1) =
                    ((bm1,c1),ps1)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE];
                      ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `wl_state_compile_oracle (s:(A,num#C,FFI)wl_state) (n + 1) = ((bm1,c1),ps1)` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    UNDISCH_TAC `FST (wl_state_compile_oracle (s:(A,num#C,FFI)wl_state) 1) = (bmr2,c2)` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    UNDISCH_TAC `LENGTH (append (bmr1:(A word)app_list)) <= bmr2` THEN
    UNDISCH_TAC `b0 = bmr2 - LENGTH (append (bmr1:(A word)app_list))` THEN
    UNDISCH_TAC `b0 = LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN ARITH_TAC;
  (* 2 *) ASM_REWRITE_TAC[domain_union; domain_fromAList] THEN SET_TAC[];
  (* 3 *) REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union; lookup_fromAList] THEN
    MP_TAC(ISPEC `lookup n (wl_state_code (s:(A,num#C,FFI)wl_state))` option_nchotomy) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xv:num#(A)wl_prog` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
       w2sp3aux_has_const "post_alloc_conventions" (concl th) &&
       w2sp3aux_has_const "wl_state_compile_oracle" (concl th))) THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `post_alloc_conventions k (word_prog:(A)wl_prog) /\ flat_exp_conventions
      word_prog /\
                  ~(raise_stub_location = n) /\ ~(wl_store_consts_stub_location = n)`
      STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN
     FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP W2SP3AUX_ALOOKUP_ALL (CONJ th
       (ASSUME `ALOOKUP (CONS (kk,prog) (rest:(num#num#(A)wl_prog)list)) n =
                SOME (arg_count,word_prog)`))) THEN
       REWRITE_TAC[o_THM] THEN NO_TAC); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lookup n (stack_state_code (t:(A,C,FFI)stack_state)) = NONE` SUBST1_TAC THENL
    [REWRITE_TAC[lookup_NONE_domain] THEN ASM_REWRITE_TAC[IN_INSERT] THEN
     UNDISCH_TAC `lookup n (wl_state_code (s:(A,num#C,FFI)wl_state)) = NONE` THEN
     UNDISCH_TAC `~(raise_stub_location = n)` THEN
     UNDISCH_TAC `~(wl_store_consts_stub_location = n)` THEN
     REWRITE_TAC[lookup_NONE_domain] THEN MESON_TAC[]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[lookup_def; the_def] THEN
    MP_TAC(ISPECL [`CONS (kk,prog) (rest:(num#num#(A)wl_prog)list)`; `k:num`;
      `Nil:(A word)app_list`;
                   `b0:num`; `progs':(num#(A)stack_prog)list`; `fs:num list`;
                   `bmr1:(A word)app_list`; `bmr2:num`; `n:num`; `arg_count:num`;
                   `word_prog:(A)wl_prog`;
                   `APPEND (stack_state_bitmaps (t:(A,C,FFI)stack_state)) (append (bmr1:(A
                     word)app_list))`;
                   `ac:(A)asm_config`; `F`] compile_word_to_stack_IMP_ALOOKUP) THEN
    ASM_REWRITE_TAC[append_thm; LENGTH; LE_0; SUB_0; DROP_LENGTH_APPEND; IS_PREFIX_REFL;
                    LENGTH_APPEND; LE_ADD];
     REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `word_prog:(A)wl_prog`; `arg_count:num`] o
       check (fun th -> is_forall (concl th) &&
              w2sp3aux_has_const "word_to_stack_compile_prog" (concl th))) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MAP_EVERY EXISTS_TAC [`bs:(A word)app_list`; `i:num`; `bs2:(A word)app_list`; `i2:num`;
                          `f'':num`; `stack_prog:(A)stack_prog`] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; lookup_def; the_def] THEN CASE_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `i - LENGTH (append (bs:(A word)app_list)) <=
                  LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN ARITH_TAC;
     ALL_TAC] THEN
    MP_TAC(ISPECL [`i - LENGTH (append (bs:(A word)app_list))`;
                   `stack_state_bitmaps (t:(A,C,FFI)stack_state)`] DROP_APPEND1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC IS_PREFIX_TRANS THEN
    EXISTS_TAC `DROP (i - LENGTH (append (bs:(A word)app_list)))
                     (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
    ASM_REWRITE_TAC[IS_PREFIX_APPEND3]];
  (* 4 *) ASM_REWRITE_TAC[lookup_union] THEN CASE_REWRITE_TAC[];
  (* 5 *) ASM_REWRITE_TAC[lookup_union] THEN CASE_REWRITE_TAC[];
  (* 6 *) UNDISCH_TAC `buffer_flush (wl_state_data_buffer (s:(A,num#C,FFI)wl_state)) w3 w4 =
                       SOME (append (bmr1:(A word)app_list),db)` THEN
          REWRITE_TAC[buffer_flush_def] THEN COND_CASES_TAC THEN
          REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
          DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (SUBST1_TAC o SYM)) THEN
          ASM_REWRITE_TAC[w2sp3aux_buffer_accfupds; K_THM; LENGTH_APPEND; LENGTH] THEN
          UNDISCH_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state)) +
            LENGTH (buffer_buffer (wl_state_data_buffer (s:(A,num#C,FFI)wl_state))) +
            buffer_space_left (wl_state_data_buffer s) + 1 < dimword (:A)` THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC;
  (* 7 *) REWRITE_TAC[LENGTH_APPEND] THEN
          UNDISCH_TAC `1 <= LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN ARITH_TAC;
  (* 8 *) UNDISCH_TAC `1 <= LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
          UNDISCH_TAC `HD (stack_state_bitmaps (t:(A,C,FFI)stack_state)) = word 4` THEN
          SPEC_TAC(`stack_state_bitmaps (t:(A,C,FFI)stack_state)`,`l:(A word)list`) THEN
          LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; APPEND; HD; ARITH_RULE `~(1 <= 0)`] THEN
          SIMP_TAC[];
  (* 9 *) MATCH_MP_TAC wf_insert THEN ASM_REWRITE_TAC[];
  (* 10 *) UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
             (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
             (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
          REWRITE_TAC[stack_size_rel_def; option_DISTINCT] THEN SIMP_TAC[];
  (* 11 *) FIRST_X_ASSUM(MP_TAC o
    check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
          REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `stack:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC abs_stack_bitmaps_prefix THEN ASM_REWRITE_TAC[];
  (* 12 *) REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THENL
    [ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN `1 < k` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[FLOOKUP_UPDATE];
     DISCH_TAC THEN
     MP_TAC(ISPECL [`names:num_set#num_set`; `wl_state_locals (s:(A,num#C,FFI)wl_state)`;
                    `env:((A)word_loc)spt`; `n:num`; `v:(A)word_loc`] W2SP3AUX_cut_env_lookup) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
     (SUBGOAL_THEN `n >= 2 * k` MP_TAC THENL
      [FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MP_TAC(ISPECL [`\x. x >= 2 * k`; `FST (names:num_set#num_set)`; `n:num`]
                      W2SP3AUX_ALL_toAList_domain);
        MP_TAC(ISPECL [`\x. x >= 2 * k`; `SND (names:num_set#num_set)`; `n:num`]
                      W2SP3AUX_ALL_toAList_domain)] THEN
       ASM_REWRITE_TAC[] THEN BETA_TAC THEN SIMP_TAC[]; ALL_TAC]) THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `~(n DIV 2 < k)` ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(2 = 0)`] THEN UNDISCH_TAC `n >= 2 * k` THEN ARITH_TAC;
      ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th -> is_forall
       (concl th) &&
       w2sp3aux_has_const "oEL" (concl th))) THEN
     ASM_REWRITE_TAC[]]]);;

(* HOL4 line 6943: Resume comp_correct[Install] *)
let word_to_stackProof_comp_correct_Install = prove
 (word_to_stackProof_comp_case "wl_Install",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  MP_TAC(ISPECL [`ptr:num`; `len:num`; `dptr:num`; `dlen:num`; `names:num_set#num_set`;
                 `s:(A,num#C,FFI)wl_state`; `res:((A)wl_result)option`;
                 `s1:(A,num#C,FFI)wl_state`] W2SP3AUX_Install_inv) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `res = (NONE:((A)wl_result)option)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `s1 = wl_state_code_buffer_fupd (K cb)
               (wl_state_data_buffer_fupd (K db)
               (wl_state_code_fupd (K (union (wl_state_code s) (fromAList progs)))
               (wl_state_locals_fupd (K (insert ptr (wl_Loc kk 0) env))
               (wl_state_fp_regs_fupd (K FEMPTY)
               (wl_state_compile_oracle_fupd (K (shift_seq 1 (wl_state_compile_oracle s)))
               (wl_state_stack_max_fupd (K NONE)
               (wl_state_stack_size_fupd (K LN) (s:(A,num#C,FFI)wl_state))))))))` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `progs = CONS (kk,prog) (rest:(num#num#(A)wl_prog)list)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  EXISTS_TAC `0` THEN SIMP[] THEN
  GVS[w2sp3aux_comp_clause "wl_Install"; word_to_stackProof_convs_def; max_var_def;
      is_phy_var_def; GSYM EVEN_MOD2; pair_case_eq; post_alloc_conventions_def;
      call_arg_convention_def] THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg2 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  SUBGOAL_THEN `stack_get_var y (t'':(A,C,FFI)stack_state) = SOME (wl_Word (w3:A word))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `stack_get_var 1 (t'':(A,C,FFI)stack_state) = SOME (wl_Word (w1:A word)) /\
                stack_get_var 2 t'' = SOME (wl_Word (w2:A word))` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                   `t'':(A,C,FFI)stack_state`; `lens:num list`; `0`; `2`; `wl_Word (w1:A word)`]
                  state_rel_get_var_imp');
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                   `t'':(A,C,FFI)stack_state`; `lens:num list`; `0`; `4`; `wl_Word (w2:A word)`]
                  state_rel_get_var_imp')] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t'':(A,C,FFI)stack_state`)) (concl th))) THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t'':(A,C,FFI)stack_state`; `lens:num list`; `cfg:num#C`;
                 `CONS (kk,prog) (rest:(num#num#(A)wl_prog)list)`; `bytes:byte list`;
                 `data:(A word)list`;
                 `FST (wl_state_compile_oracle (s:(A,num#C,FFI)wl_state) 1)`]
                W2SP3AUX_install_compile) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `progs':(num#(A)stack_prog)list` (X_CHOOSE_THEN `fs:num list`
    (X_CHOOSE_THEN `bmr1:(A word)app_list` (X_CHOOSE_THEN `bmr2:num`
    (X_CHOOSE_THEN `c2:C` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `?sp0 rest'. progs' = CONS (kk,sp0) (rest':(num#(A)stack_prog)list)`
    STRIP_ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o MATCH_MP MAP_FST_compile_word_to_stack o
     check (w2sp3aux_has_const "compile_word_to_stack" o concl)) THEN
   DISJ_CASES_THEN2 SUBST1_TAC
     (X_CHOOSE_THEN `p0:num#(A)stack_prog` (X_CHOOSE_THEN `ps0:(num#(A)stack_prog)list`
        SUBST1_TAC))
     (ISPEC `progs':(num#(A)stack_prog)list` list_CASES) THEN
   REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`SND (p0:num#(A)stack_prog)`; `ps0:(num#(A)stack_prog)list`] THEN
   UNDISCH_TAC `FST (p0:num#(A)stack_prog) = kk` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t'':(A,C,FFI)stack_state`; `y:num`; `y':num`; `w1:A word`; `w2:A word`;
                 `w3:A word`; `w4:A word`; `SND (cfg:num#C)`; `progs':(num#(A)stack_prog)list`;
                 `append (bmr1:(A word)app_list)`; `bytes:byte list`; `cb:(A,8)buffer`;
                 `db:(A,A)buffer`; `c2:C`; `kk:num`; `sp0:(A)stack_prog`;
                 `rest':(num#(A)stack_prog)list`] W2SP3AUX_install_eval) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                  `t'':(A,C,FFI)stack_state`; `lens:num list`; `0`; `1`] W2SP3AUX_co_FST) THEN
   ASM_REWRITE_TAC[SND]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t'':(A,C,FFI)stack_state`; `lens:num list`; `names:num_set#num_set`;
                 `env:((A)word_loc)spt`; `cfg:num#C`; `kk:num`; `prog:num#(A)wl_prog`;
                 `rest:(num#num#(A)wl_prog)list`; `cb:(A,8)buffer`; `db:(A,A)buffer`;
                 `progs':(num#(A)stack_prog)list`; `fs:num list`; `bmr1:(A word)app_list`;
                 `bmr2:num`; `c2:C`; `w3:A word`; `w4:A word`] W2SP3AUX_install_state_rel) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `data = append (bmr1:(A word)app_list)` THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* W2SP3AUX: state_rel and the code buffer *)
let W2SP3AUX_state_rel_code_buffer = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra cb.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_code_buffer_fupd (K cb) s)
           (stack_state_code_buffer_fupd (K cb) t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* W2SP3AUX: state_rel and a write to the data buffer *)
let W2SP3AUX_state_rel_data_buffer = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra w b db.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     buffer_write (wl_state_data_buffer s) w b = SOME db
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_data_buffer_fupd (K db) s)
           (stack_state_data_buffer_fupd (K db) t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[buffer_write_def; COND_CASE_EQ; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; w2sp3aux_buffer_accfupds; K_THM;
              LENGTH_APPEND; LENGTH] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `0 < buffer_space_left (wl_state_data_buffer (s:(A,num#C,FFI)wl_state))` THEN
  UNDISCH_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state)) +
       LENGTH (buffer_buffer (wl_state_data_buffer (s:(A,num#C,FFI)wl_state))) +
       buffer_space_left (wl_state_data_buffer s) + 1 < dimword (:A)` THEN ARITH_TAC);;

(* HOL4 line 7072: Resume comp_correct[CodeBufferWrite] *)
let word_to_stackProof_comp_correct_CodeBufferWrite = prove
 (word_to_stackProof_comp_case "wl_CodeBufferWrite",
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  GVS[w2sp3aux_comp_clause "wl_CodeBufferWrite"; w2sp3aux_wl_eval_clause "wl_CodeBufferWrite";
      option_case_eq; word_to_stackProof_convs_def; max_var_def; is_phy_var_def; GSYM EVEN_MOD2;
      case_eq "word_loc"; pair_case_eq] THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg2 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_CodeBufferWrite"] THEN
  SUBGOAL_THEN `stack_get_var y (t'':(A,C,FFI)stack_state) = SOME (wl_Word (a:A word))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t'':(A,C,FFI)stack_state`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  MATCH_MP_TAC W2SP3AUX_state_rel_code_buffer THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 7098: Resume comp_correct[DataBufferWrite] *)
let word_to_stackProof_comp_correct_DataBufferWrite = prove
 (word_to_stackProof_comp_case "wl_DataBufferWrite",
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  GVS[w2sp3aux_comp_clause "wl_DataBufferWrite"; w2sp3aux_wl_eval_clause "wl_DataBufferWrite";
      option_case_eq; word_to_stackProof_convs_def; max_var_def; is_phy_var_def; GSYM EVEN_MOD2;
      case_eq "word_loc"; pair_case_eq] THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  DRULE_ALL evaluate_wStackLoad_wReg2 THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_DataBufferWrite"] THEN
  SUBGOAL_THEN `stack_get_var y (t'':(A,C,FFI)stack_state) = SOME (wl_Word (a:A word))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t'':(A,C,FFI)stack_state`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  MATCH_MP_TAC W2SP3AUX_state_rel_data_buffer THEN ASM_MESON_TAC[]);;

(* W2SP3AUX: state_rel after an FFI call that returns *)
let W2SP3AUX_state_rel_FFI = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens names env m ffi' r.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_cut_env names (wl_state_locals s) = SOME env /\
     ALL (\x. x >= 2 * k) (MAP FST (toAList (FST names))) /\
     ALL (\x. x >= 2 * k) (MAP FST (toAList (SND names)))
     ==> word_to_stackProof_state_rel ac k f f'
           (wl_state_locals_fupd (K env) (wl_state_fp_regs_fupd (K FEMPTY)
             (wl_state_memory_fupd (K m) (wl_state_ffi_fupd (K ffi') s))))
           (stack_state_regs_fupd (K r)
             (stack_state_fp_regs_fupd (K FEMPTY)
             (stack_state_memory_fupd (K m) (stack_state_ffi_fupd (K ffi') t))))
           lens 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wf (env:((A)word_loc)spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[W2SP3AUX_cut_env_wf]; ALL_TAC] THEN
  SUBGOAL_THEN `!n v. lookup n env = SOME v
                      ==> lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME v /\
                          n >= 2 * k`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`names:cutsets`; `wl_state_locals (s:(A,num#C,FFI)wl_state)`;
                   `env:((A)word_loc)spt`; `n:num`; `v:(A)word_loc`] W2SP3AUX_cut_env_lookup) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[W2SP3AUX_ALL_toAList_domain];
    ALL_TAC] THEN
  UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                 (t:(A,C,FFI)stack_state) lens 0` THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRIP_TAC THEN
  REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o
    check (fun th -> can (find_term ((=) `env:((A)word_loc)spt`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o
    check (fun th -> can (find_term ((=) `EVEN`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n DIV 2 < k)` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[NOT_LT] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 7125: Resume comp_correct[FFI] *)
let word_to_stackProof_comp_correct_FFI = prove
 (word_to_stackProof_comp_case "wl_FFI",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  SUBGOAL_THEN `!m v. wl_get_var m (s:(A,num#C,FFI)wl_state) = SOME v /\ EVEN m /\ m < 10
                      ==> FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) (m DIV 2) = SOME v`
    (fun th -> MAP_EVERY (fun m -> ASSUME_TAC (REWRITE_RULE[]
                 (CONV_RULE NUM_REDUCE_CONV (SPEC m th)))) [`2`;`4`;`6`;`8`]) THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
     `t:(A,C,FFI)stack_state`; `lens:num list`; `0`; `m:num`; `v:(A)word_loc`]
     state_rel_get_var_imp') THEN
   ASM_REWRITE_TAC[stack_get_var_def] THEN DISCH_THEN MATCH_MP_TAC THEN
   SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(2 = 0)`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  GVS[w2sp3aux_comp_clause "wl_FFI"; w2sp3aux_wl_eval_clause "wl_FFI";
      option_case_eq; word_to_stackProof_convs_def; max_var_def; is_phy_var_def; GSYM EVEN_MOD2;
      case_eq "word_loc"; pair_case_eq; case_eq "ffi_result"] THEN
  RES_TAC THEN EXISTS_TAC `0` THEN SIMP[] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_FFI"; stack_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  MATCH_MP_TAC W2SP3AUX_state_rel_FFI THEN ASM_MESON_TAC[]);;

(* W2SP3AUX: case splits on the variables of the expression of a ShareInst  *)
(* until flat_exp_conventions_def decides it (an OCaml tactic)              *)
let rec w2sp3aux_leftmost_vars tm =
  if is_var tm then [tm]
  else if is_comb tm then
    let l = w2sp3aux_leftmost_vars (rator tm) in
    l @ filter (fun v -> not (mem v l)) (w2sp3aux_leftmost_vars (rand tm))
  else if is_abs tm then w2sp3aux_leftmost_vars (body tm)
  else [];;

let rec W2SP3AUX_SHARE_SPLIT_TAC : tactic = fun (asl,w as g) ->
  (REWRITE_TAC[flat_exp_conventions_def] THEN CASE_REWRITE_TAC[] THEN
   (fun (asl,w as g) ->
      if not (is_imp w) then MESON_TAC[] g else
      let e = rand(rand(lhand w)) in
      let ok v = let n = fst(dest_type(type_of v)) in
                 n = "wl_exp" || n = "binop" || n = "list" in
      match filter ok (w2sp3aux_leftmost_vars e) with
        [] -> FAIL_TAC "W2SP3AUX_SHARE_SPLIT_TAC" g
      | v::_ -> (CASES_ON v THEN W2SP3AUX_SHARE_SPLIT_TAC) g)) g;;

(* HOL4 line 7166 *)
let flat_exp_conventions_ShareInst_exp_simp = prove
 (`!op v (exp:(A)wl_exp).
     flat_exp_conventions (ShareInst op v exp)
     ==> (?ad. exp = wl_Var ad) \/
         (?ad offset. exp = wl_Op asm_Add [wl_Var ad; wl_Const offset])`,
  REPEAT GEN_TAC THEN W2SP3AUX_SHARE_SPLIT_TAC);;

(* HOL4 line 7175 *)
let word_exp_Op_Add_0 = prove
 (`!(s:(A,C,FFI)wl_state) exp x.
     wl_word_exp s exp = SOME (wl_Word x) <=>
     wl_word_exp s (wl_Op asm_Add [exp; wl_Const (word 0)]) = SOME (wl_Word x)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [wl_word_exp_def] THEN
  REWRITE_TAC[the_words_def; MAP; wl_word_exp_def] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) exp` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:(A)word_loc`) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[ITLIST; OPTION_MAP_DEF; WORD_ADD_0]);;

(* HOL4 line 7186 *)
let evaluate_ShareInst_Var_eq_Op_Add = prove
 (`!op v ad (s:(A,C,FFI)wl_state).
     wl_evaluate (ShareInst op v (wl_Var ad),s) =
     wl_evaluate (ShareInst op v (wl_Op asm_Add [wl_Var ad; wl_Const (word 0)]),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_wl_eval_clause "ShareInst"] THEN
  REWRITE_TAC[the_words_def; MAP; wl_word_exp_def] THEN
  CASES_ON `wl_get_var ad (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:(A)word_loc`) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[ITLIST; OPTION_MAP_DEF; WORD_ADD_0]);;

(* W2SP3AUX: state_rel and a new ffi state on both sides *)
let W2SP3AUX_state_rel_ffi = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra ffi.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_ffi_fupd (K ffi) s)
           (stack_state_ffi_fupd (K ffi) t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* W2SP3AUX: a shared-memory load into a register *)
let W2SP3AUX_state_rel_set_var_ffi = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra x v ffi.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\ x < k
     ==> word_to_stackProof_state_rel ac k f f'
           (wl_state_ffi_fupd (K ffi) (wl_set_var (2 * x) v s))
           (stack_state_regs_fupd (K (stack_state_regs t |+ (x,v)))
             (stack_state_ffi_fupd (K ffi) t)) lens extra`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
    `wl_state_ffi_fupd (K (ffi:FFI ffi_state)) (s:(A,num#C,FFI)wl_state)`;
    `stack_state_ffi_fupd (K (ffi:FFI ffi_state)) (t:(A,C,FFI)stack_state)`;
    `lens:num list`; `extra:num`; `x:num`; `v:(A)word_loc`]
    word_to_stackProof_state_rel_set_var) THEN
  ASM_SIMP_TAC[W2SP3AUX_state_rel_ffi] THEN
  MATCH_MP_TAC(MESON[] `(a:(A,num#C,FFI)wl_state) = b /\ (c:(A,C,FFI)stack_state) = d
                         ==> word_to_stackProof_state_rel (ac:(A)asm_config) k f f' a c lens extra
                         ==> word_to_stackProof_state_rel ac k f f' b d lens extra`) THEN
  REWRITE_TAC[wl_set_var_def; stack_set_var_def] THEN SIMP[]);;

(* W2SP3AUX: a shared-memory load into register k, stored to the stack     *)
(* (the states in the record simplifier's normal form)                       *)
let W2SP3AUX_state_rel_set_var_ffi_stack = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens x v ffi.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\ ~(x < k) /\ x < f' + k
     ==> word_to_stackProof_state_rel ac k f f'
           (wl_state_ffi_fupd (K ffi) (wl_set_var (2 * x) v s))
           (stack_state_regs_fupd (K (stack_state_regs t |+ (k,v)))
             (stack_state_stack_fupd
                (K (LUPDATE v (stack_state_stack_space t + (f + k) - (x + 1))
                      (stack_state_stack t)))
                (stack_state_ffi_fupd (K ffi) t))) lens 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
    `wl_state_ffi_fupd (K (ffi:FFI ffi_state)) (s:(A,num#C,FFI)wl_state)`;
    `stack_set_var k (v:(A)word_loc)
       (stack_state_ffi_fupd (K (ffi:FFI ffi_state)) (t:(A,C,FFI)stack_state))`;
    `lens:num list`; `x:num`;
    `stack_state_stack (t:(A,C,FFI)stack_state)`;
    `stack_state_stack_space (t:(A,C,FFI)stack_state)`;
    `v:(A)word_loc`] state_rel_set_var2) THEN
  ASM_SIMP_TAC[state_rel_set_var_k; W2SP3AUX_state_rel_ffi] THEN
  REWRITE_TAC[stack_set_var_def; w2sp3aux_stack_accfupds; K_THM] THEN
  MATCH_MP_TAC(MESON[] `(a:(A,num#C,FFI)wl_state) = b /\ (c:(A,C,FFI)stack_state) = d
                         ==> word_to_stackProof_state_rel (ac:(A)asm_config) k f f' a c lens 0
                         ==> word_to_stackProof_state_rel ac k f f' b d lens 0`) THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[]);;

(* W2SP3AUX: the case splits of the shared-memory store lemmas *)
let W2SP3AUX_SHARE_STORE_TAC : tactic =
  TOP_CASE_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  TRY(TOP_CASE_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ])) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SIMP[compile_result_def; wl_flush_state_def] THEN
  TRY(MATCH_MP_TAC W2SP3AUX_state_rel_ffi THEN ASM_REWRITE_TAC[]);;

(* W2SP3AUX: a shared-memory store from register k + 1 *)
let W2SP3AUX_state_rel_ffi_k1 = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra x ffi.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_ffi_fupd (K ffi) s)
           (stack_state_regs_fupd (K (stack_state_regs t |+ (k + 1,x)))
             (stack_state_ffi_fupd (K ffi) t)) lens extra`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
    `wl_state_ffi_fupd (K (ffi:FFI ffi_state)) (s:(A,num#C,FFI)wl_state)`;
    `stack_state_ffi_fupd (K (ffi:FFI ffi_state)) (t:(A,C,FFI)stack_state)`;
    `lens:num list`; `extra:num`; `x:(A)word_loc`] state_rel_set_var_k) THEN
  ASM_SIMP_TAC[W2SP3AUX_state_rel_ffi] THEN
  REWRITE_TAC[stack_set_var_def; w2sp3aux_stack_accfupds; K_THM] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN SIMP[]);;

(* HOL4 line 7207 *)
let share_load_lemma1 = prove
 (`!op v (ad':A word) (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     share_inst op (2 * v) ad' s = (res,s1) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     v < f' + k /\
     k <= v /\
     (op = asm_Load \/ op = Load8 \/ op = Load16 \/ op = asm_Load32) /\
     ~(res = SOME wl_Error)
     ==> ?t1. sh_mem_op op k ad' t = (OPTION_MAP compile_result res,t1) /\
              ((?f. res = SOME (wl_FinalFFI f) /\
                    wl_state_ffi s1 = stack_state_ffi t1 /\
                    wl_state_clock s1 = stack_state_clock t1) \/
               (res = NONE /\
                word_to_stackProof_state_rel ac k f f' s1
                  (stack_state_stack_fupd
                     (K (LUPDATE (THE (FLOOKUP (stack_state_regs t1) k))
                           (stack_state_stack_space t1 + ((f + k) - (v + 1)))
                           (stack_state_stack t1))) t1) lens 0 /\
                (?x. FLOOKUP (stack_state_regs t1) k = SOME x) /\
                stack_state_stack_space t1 = stack_state_stack_space t /\
                LENGTH (stack_state_stack t1) = LENGTH (stack_state_stack t)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
    wl_sh_mem_load16_def; wl_sh_mem_load32_def]) THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_load_def; stack_sh_mem_load_byte_def;
    stack_sh_mem_load16_def; stack_sh_mem_load32_def] THEN
  ASM_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[sh_mem_set_var_def; PAIR_EQ]) THEN
  TRY(TOP_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[sh_mem_set_var_def; PAIR_EQ])) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SIMP[compile_result_def; wl_flush_state_def; FLOOKUP_UPDATE; LENGTH_LUPDATE] THEN
  TRY(MATCH_MP_TAC W2SP3AUX_state_rel_set_var_ffi_stack THEN ASM_REWRITE_TAC[NOT_LT]));;

(* HOL4 line 7254 *)
let share_load_lemma2 = prove
 (`!op v (ad':A word) (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     share_inst op (2 * v) ad' s = (res,s1) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     v < k /\
     (op = asm_Load \/ op = Load8 \/ op = Load16 \/ op = asm_Load32) /\
     ~(res = SOME wl_Error)
     ==> ?t1. sh_mem_op op v ad' t = (OPTION_MAP compile_result res,t1) /\
              ((?f. res = SOME (wl_FinalFFI f) /\
                    wl_state_ffi s1 = stack_state_ffi t1 /\
                    wl_state_clock s1 = stack_state_clock t1) \/
               (res = NONE /\ word_to_stackProof_state_rel ac k f f' s1 t1 lens 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
    wl_sh_mem_load16_def; wl_sh_mem_load32_def]) THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_load_def; stack_sh_mem_load_byte_def;
    stack_sh_mem_load16_def; stack_sh_mem_load32_def] THEN
  ASM_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[sh_mem_set_var_def; PAIR_EQ]) THEN
  TRY(TOP_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[sh_mem_set_var_def; PAIR_EQ])) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SIMP[compile_result_def; wl_flush_state_def] THEN
  TRY(MATCH_MP_TAC W2SP3AUX_state_rel_set_var_ffi THEN ASM_REWRITE_TAC[]));;

(* HOL4 line 7298 *)
let share_store_lemma1 = prove
 (`!op v (ad':A word) (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     share_inst op (2 * v) ad' s = (res,s1) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     ~(v < k) /\
     (op = asm_Store \/ op = Store8 \/ op = Store16 \/ op = asm_Store32) /\
     ~(res = SOME wl_Error)
     ==> ?t1. sh_mem_op op (k + 1) ad'
                (stack_state_regs_fupd
                   (K (stack_state_regs t |+
                       (k + 1,EL (stack_state_stack_space t + ((f + k) - (v + 1)))
                                 (stack_state_stack t)))) t) =
              (OPTION_MAP compile_result res,t1) /\
              ((?fvl. res = SOME (wl_FinalFFI fvl) /\
                     wl_state_ffi s1 = stack_state_ffi t1 /\
                     wl_state_clock s1 = stack_state_clock t1) \/
               (res = NONE /\ word_to_stackProof_state_rel ac k f f' s1 t1 lens 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[share_inst_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
    wl_sh_mem_store16_def; wl_sh_mem_store32_def]) THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_store_byte_def;
    stack_sh_mem_store16_def; stack_sh_mem_store32_def] THEN
  CASES_ON `wl_get_var (2 * v) (s:(A,num#C,FFI)wl_state)` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) =
        `res:((A)wl_result)option`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC) THEN
  CASES_ON `a:(A)word_loc` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  CASE_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) =
        `res:((A)wl_result)option`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC) THEN
  IMP_RES_TAC state_rel_get_var_imp2 THEN
  REWRITE_TAC[stack_get_var_def; w2sp3aux_stack_accfupds; K_THM; FLOOKUP_UPDATE] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  TRY(TOP_CASE_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ])) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SIMP[compile_result_def; wl_flush_state_def] THEN
  TRY(MATCH_MP_TAC W2SP3AUX_state_rel_ffi_k1 THEN ASM_REWRITE_TAC[]));;

(* HOL4 line 7348 *)
let share_store_lemma2 = prove
 (`!op v (ad':A word) (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     share_inst op (2 * v) ad' s = (res,s1) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     v < k /\
     (op = asm_Store \/ op = Store8 \/ op = Store16 \/ op = asm_Store32) /\
     ~(res = SOME wl_Error)
     ==> ?t1. sh_mem_op op v ad' t = (OPTION_MAP compile_result res,t1) /\
              ((?fvl. res = SOME (wl_FinalFFI fvl) /\
                     wl_state_ffi s1 = stack_state_ffi t1 /\
                     wl_state_clock s1 = stack_state_clock t1) \/
               (res = NONE /\ word_to_stackProof_state_rel ac k f f' s1 t1 lens 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[share_inst_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
    wl_sh_mem_store16_def; wl_sh_mem_store32_def]) THEN
  REWRITE_TAC[sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_store_byte_def;
    stack_sh_mem_store16_def; stack_sh_mem_store32_def] THEN
  CASES_ON `wl_get_var (2 * v) (s:(A,num#C,FFI)wl_state)` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) =
        `res:((A)wl_result)option`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC) THEN
  CASES_ON `a:(A)word_loc` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  CASE_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) =
        `res:((A)wl_result)option`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC) THEN
  IMP_RES_TAC state_rel_get_var_imp THEN REWRITE_TAC[stack_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN W2SP3AUX_SHARE_STORE_TAC);;

(* W2SP3AUX: the ShMemOp step of evaluate_ShareInst_Load/Store: the address *)
(* expression and the clock tick of one extra clock unit                    *)
let W2SP3AUX_SHMEMOP_TAC : tactic =
  REWRITE_TAC[w2sp3aux_seval "ShMemOp"; stack_word_exp_def; MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM; FLOOKUP_UPDATE] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF; word_op_def] THEN
  CASE_REWRITE_TAC[ITLIST; WORD_ADD_0] THEN
  REWRITE_TAC[ARITH_RULE `~(1 + c = 0)`; stack_dec_clock_def; w2sp3aux_stack_accfupds; K_THM;
              ADD_SUB2] THEN
  SIMP[];;

(* HOL4 line 7386 *)
let evaluate_ShareInst_Load = prove
 (`!op v ad offset (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     wl_evaluate (ShareInst op (2 * v)
       (wl_Op asm_Add [wl_Var (2 * ad); wl_Const offset]),s) = (res,s1) /\
     ~(res = SOME wl_Error) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     v < f' + k /\
     ad < f' + k /\
     (op = asm_Load \/ op = Load8 \/ op = Load16 \/ op = asm_Load32)
     ==> ?ck t1.
           stack_evaluate
             (wShareInst op (2 * v) (Addr (2 * ad) offset) (k,f,f'),
              stack_state_clock_fupd (K (ck + stack_state_clock t)) t) =
             (OPTION_MAP compile_result res,t1) /\
           ((?fvl. res = SOME (wl_FinalFFI fvl) /\
                  wl_state_ffi s1 = stack_state_ffi t1 /\
                  wl_state_clock s1 = stack_state_clock t1) \/
            (res = NONE /\ word_to_stackProof_state_rel ac k f f' s1 t1 lens 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `wl_evaluate (ShareInst op (2 * v)
                 (wl_Op asm_Add [wl_Var (2 * ad); wl_Const offset]),
                 s:(A,num#C,FFI)wl_state) = res,s1` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "ShareInst"; wl_word_exp_def; MAP; the_words_def] THEN
  CASES_ON `wl_get_var (2 * ad) (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [ALL_TAC; DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[ITLIST; OPTION_MAP_DEF; WORD_ADD_0] THEN
  DISCH_TAC THEN EXISTS_TAC `1` THEN
  MP_TAC(ISPEC `wReg1 (2 * ad) (k,f,f')` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(num#num)list` (X_CHOOSE_THEN `n2:num` ASSUME_TAC)) THEN
  SUBGOAL_THEN `EVEN (2 * ad)` ASSUME_TAC THENL [REWRITE_TAC[EVEN_DOUBLE]; ALL_TAC] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t:(A,C,FFI)stack_state`)) (concl th) &&
                     w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th))) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  REWRITE_TAC[wShareInst_def] THEN ASM_REWRITE_TAC[pair_CASE_def] THEN
  ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_wStackLoad_clock] THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[wRegWrite1_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  (COND_CASES_TAC THENL
  [W2SP3AUX_SHMEMOP_TAC THEN
   MATCH_MP_TAC share_load_lemma2 THEN EXISTS_TAC `s:(A,num#C,FFI)wl_state` THEN
   ASM_REWRITE_TAC[];
   REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN W2SP3AUX_SHMEMOP_TAC THEN
   FIRST_ASSUM(fun th ->
     let l = lhs(concl th) in
     if fst(dest_const(fst(strip_comb l))) = "share_inst" then
     MP_TAC(ISPECL [hd(snd(strip_comb l)); `v:num`; `word_add a' (offset:A word)`;
      `s:(A,num#C,FFI)wl_state`;
      `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`; `ac:(A)asm_config`; `k:num`;
      `f:num`; `f':num`; `t':(A,C,FFI)stack_state`; `lens:num list`] share_load_lemma1)
     else NO_TAC) THEN
   ASM_REWRITE_TAC[GSYM NOT_LT] THEN
   DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THENL
   [SIMP[OPTION_MAP_DEF; option_DISTINCT; option_INJ; compile_result_def] THEN MESON_TAC[];
    REWRITE_TAC[OPTION_MAP_DEF] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM] o
      MATCH_MP W2SP3AUX_state_rel_basic o
      check (fun th -> can (find_term ((=) `s1:(A,num#C,FFI)wl_state`)) (concl th))) THEN
    SUBGOAL_THEN `f - 1 - (v - k) = (f + k) - (v + 1) /\
                  ~(LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) <=
                    stack_state_stack_space t1 + (f - 1 - (v - k)))`
      STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
     UNDISCH_TAC `v < f' + k` THEN UNDISCH_TAC `~(v < k)` THEN
     UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + f <= LENGTH
       (stack_state_stack t)` THEN
     UNDISCH_TAC `stack_state_stack_space (t1:(A,C,FFI)stack_state) = stack_state_stack_space
       (t:(A,C,FFI)stack_state)` THEN
     UNDISCH_TAC `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) = LENGTH (stack_state_stack
       (t:(A,C,FFI)stack_state))` THEN
     ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[w2sp3aux_seval "StackStore"; stack_get_var_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[THE_DEF]) THEN SIMP[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "LUPDATE" (concl th) &&
      w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF]]]));;

(* HOL4 line 7447 *)
let evaluate_ShareInst_Store = prove
 (`!op v ad offset (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     wl_evaluate (ShareInst op (2 * v)
       (wl_Op asm_Add [wl_Var (2 * ad); wl_Const offset]),s) = (res,s1) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     v < f' + k /\
     ad < f' + k /\
     ~(res = SOME wl_Error) /\
     (op = asm_Store \/ op = Store8 \/ op = Store16 \/ op = asm_Store32)
     ==> ?ck t1.
           stack_evaluate
             (wShareInst op (2 * v) (Addr (2 * ad) offset) (k,f,f'),
              stack_state_clock_fupd (K (ck + stack_state_clock t)) t) =
             (OPTION_MAP compile_result res,t1) /\
           ((?fvl. res = SOME (wl_FinalFFI fvl) /\
                  wl_state_ffi s1 = stack_state_ffi t1 /\
                  wl_state_clock s1 = stack_state_clock t1) \/
            (res = NONE /\ word_to_stackProof_state_rel ac k f f' s1 t1 lens 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `wl_evaluate (ShareInst op (2 * v)
                 (wl_Op asm_Add [wl_Var (2 * ad); wl_Const offset]),
                 s:(A,num#C,FFI)wl_state) = res,s1` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "ShareInst"; wl_word_exp_def; MAP; the_words_def] THEN
  CASES_ON `wl_get_var (2 * ad) (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [ALL_TAC; DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[ITLIST; OPTION_MAP_DEF; WORD_ADD_0] THEN
  DISCH_TAC THEN EXISTS_TAC `1` THEN
  MP_TAC(ISPEC `wReg1 (2 * ad) (k,f,f')` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(num#num)list` (X_CHOOSE_THEN `n2:num` ASSUME_TAC)) THEN
  SUBGOAL_THEN `EVEN (2 * ad)` ASSUME_TAC THENL [REWRITE_TAC[EVEN_DOUBLE]; ALL_TAC] THEN
  DRULE_ALL evaluate_wStackLoad_wReg1 THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
    check (fun th -> can (find_term ((=) `t':(A,C,FFI)stack_state`)) (concl th) &&
                     w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th))) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  REWRITE_TAC[wShareInst_def] THEN ASM_REWRITE_TAC[pair_CASE_def] THEN
  REWRITE_TAC[wReg2_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  (COND_CASES_TAC THEN REWRITE_TAC[pair_CASE_def; APPEND_NIL; wStackLoad_append; o_THM] THEN
   ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
   REWRITE_TAC[w2sp3aux_seval "stack_Seq"; evaluate_wStackLoad_clock] THEN
   ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
   REWRITE_TAC[wStackLoad_def] THENL
   [W2SP3AUX_SHMEMOP_TAC THEN
    MATCH_MP_TAC share_store_lemma2 THEN EXISTS_TAC `s:(A,num#C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `stack_state_stack_space (t':(A,C,FFI)stack_state) + (f - 1 - (v - k)) <
                  LENGTH (stack_state_stack t') /\ f - 1 - (v - k) = (f + k) - (v + 1)`
      STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
     UNDISCH_TAC `v < f' + k` THEN UNDISCH_TAC `~(v < k)` THEN
     UNDISCH_TAC `stack_state_stack_space (t':(A,C,FFI)stack_state) + f <=
                  LENGTH (stack_state_stack t')` THEN
     ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackLoad";
                w2sp3aux_stack_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[pair_CASE_def; FST; SND; stack_set_var_def] THEN
    W2SP3AUX_SHMEMOP_TAC THEN
    FIRST_ASSUM(fun th ->
      let l = lhs(concl th) in
      if fst(dest_const(fst(strip_comb l))) = "share_inst" then
      MP_TAC(ISPECL [hd(snd(strip_comb l)); `v:num`; `word_add a' (offset:A word)`;
       `s:(A,num#C,FFI)wl_state`;
       `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`; `ac:(A)asm_config`; `k:num`;
       `f:num`; `f':num`; `t':(A,C,FFI)stack_state`; `lens:num list`] share_store_lemma1)
      else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN SIMP[]]));;

(* HOL4 line 7501 *)
let evaluate_ShareInst_correct_lemma = prove
 (`!op v ad offset (s:(A,num#C,FFI)wl_state) res s1 ac k f f'
     (t:(A,C,FFI)stack_state) lens.
     wl_evaluate (ShareInst op (2 * v)
       (wl_Op asm_Add [wl_Var (2 * ad); wl_Const offset]),s) = (res,s1) /\
     ~(res = SOME wl_Error) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     v < f' + k /\
     ad < f' + k
     ==> ?ck t1.
           stack_evaluate
             (wShareInst op (2 * v) (Addr (2 * ad) offset) (k,f,f'),
              stack_state_clock_fupd (K (ck + stack_state_clock t)) t) =
             (OPTION_MAP compile_result res,t1) /\
           ((res = NONE /\ word_to_stackProof_state_rel ac k f f' s1 t1 lens 0) \/
            (?fvl. res = SOME (wl_FinalFFI fvl) /\
                  wl_state_ffi s1 = stack_state_ffi t1 /\
                  wl_state_clock s1 = stack_state_clock t1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL evaluate_ShareInst_Load) THEN MP_TAC(SPEC_ALL evaluate_ShareInst_Store) THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `op:memop` THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 7528: Resume comp_correct[ShareInst] *)
let word_to_stackProof_comp_correct_ShareInst = prove
 (word_to_stackProof_comp_case "ShareInst",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
    MATCH_MP flat_exp_conventions_ShareInst_exp_simp) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[evaluate_ShareInst_Var_eq_Op_Add]) THEN
  GVS[w2sp3aux_comp_clause "ShareInst"; exp_to_addr_def; word_to_stackProof_convs_def;
      max_var_def; max_var_exp_def; every_var_exp_def; is_phy_var_def; GSYM EVEN_MOD2;
      EVEN_EXISTS; MAP; MAX_LIST; GSYM LEFT_ADD_DISTRIB] THEN
  (SUBGOAL_THEN `m < f' + k /\ m' < f' + k` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "MAX" o concl)) THEN
    REWRITE_TAC[MAX] THEN ARITH_TAC;
    ALL_TAC]) THEN
  DRULE_ALL evaluate_ShareInst_correct_lemma THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`;
                        `OPTION_MAP compile_result (res:((A)wl_result)option)`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 7546 *)
let compile_prog_stack_size = prove
 (`!(ac:(A)asm_config) perf word_prog x k bs stack_prog fs bs2.
     word_to_stack_compile_prog ac perf word_prog x k bs = (stack_prog,fs,bs2)
     ==> x - k <= fs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* HOL4 line 7554: val cruft_tac (a tactic) *)

(* HOL4 line 7589 *)
let SUB_SUB_SUB_MAX = prove
 (`!a b c. (a - b) - (c - b) = a - MAX b c`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* HOL4 line 7596 *)
let MAX_LE = prove
 (`!a b. a <= b ==> MAX a b = b`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* HOL4 line 7602 *)
let copy_ret_aux_thm = prove
 (`!k f n.
     copy_ret_aux k f 0 = (stack_Skip:(A)stack_prog) /\
     copy_ret_aux k f (SUC n) =
     stack_list_Seq [StackLoad k n; StackStore k (n + f); copy_ret_aux k f n:(A)stack_prog]`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [copy_ret_aux_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

(* W2SP3AUX: stackSem Seq facts *)
let W2SP3AUX_Seq_Skip_r = prove
 (`!p (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq p stack_Skip,s) = stack_evaluate (p,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "stack_Skip"] THEN
  MP_TAC(ISPEC `stack_evaluate (p:(A)stack_prog,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let W2SP3AUX_Seq_Skip_l = prove
 (`!p (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq stack_Skip p,s) = stack_evaluate (p,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "stack_Skip"] THEN
  REWRITE_TAC[pair_CASE_def]);;

let W2SP3AUX_Seq_assoc = prove
 (`!p1 p2 p3 (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq (stack_Seq p1 p2) p3,s) =
     stack_evaluate (stack_Seq p1 (stack_Seq p2 p3),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (p1:(A)stack_prog,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)stack_result)option` (X_CHOOSE_THEN `s1:(A,C,FFI)stack_state`
    SUBST1_TAC)) THEN REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  ASM_CASES_TAC `r1:((A)stack_result)option = NONE` THEN ASM_REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPEC `stack_evaluate (p2:(A)stack_prog,s1:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)stack_result)option` (X_CHOOSE_THEN `s2:(A,C,FFI)stack_state`
    SUBST1_TAC)) THEN REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

let W2SP3AUX_Seq_cong = prove
 (`!p q1 q2 (s:(A,C,FFI)stack_state).
     (!s':(A,C,FFI)stack_state. stack_evaluate (q1,s') = stack_evaluate (q2,s'))
     ==> stack_evaluate (stack_Seq p q1,s) = stack_evaluate (stack_Seq p q2,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[]);;

let W2SP3AUX_Seq_Skip_mid = prove
 (`!p q (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq (stack_Seq p stack_Skip) q,s) =
     stack_evaluate (stack_Seq p q,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[W2SP3AUX_Seq_assoc] THEN
  MATCH_MP_TAC W2SP3AUX_Seq_cong THEN REWRITE_TAC[W2SP3AUX_Seq_Skip_l]);;

(* HOL4 line 7611 *)
let evaluate_copy_ret_Seq = prove
 (`!perf b (kf:num#num#C) (vs:B list) (k0:(A)stack_prog) (t:(A,D,FFI)stack_state).
     stack_evaluate (copy_ret perf b kf vs k0,t) =
     stack_evaluate (stack_Seq (copy_ret perf b kf vs stack_Skip) k0,t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `kf:num#num#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ff:num#C` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ff:num#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `f':C` SUBST1_TAC)) THEN
  REWRITE_TAC[copy_ret_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[W2SP3AUX_Seq_Skip_l; W2SP3AUX_Seq_assoc] THEN
  MATCH_MP_TAC W2SP3AUX_Seq_cong THEN
  ASM_REWRITE_TAC[SeqStackFree_def; W2SP3AUX_Seq_Skip_mid]);;

(* HOL4 line 7622 *)
let evaluate_copy_ret_Seq' = prove
 (`!is_handle k f (f':C) (vs:B list) (k0:(A)stack_prog) (t:(A,D,FFI)stack_state).
     stack_evaluate (copy_ret F is_handle (k,f,f') vs k0,t) =
     let n = num_stack_ret k vs in
     stack_evaluate
       (stack_Seq (copy_ret_aux k (if is_handle then f + 3 else f) n) (SeqStackFree n k0),t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[copy_ret_F] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[copy_ret_aux_thm; SeqStackFree_def; W2SP3AUX_Seq_Skip_l]);;

(* W2SP3AUX: copy_ret_aux has no labels *)
let W2SP3AUX_get_labels_copy_ret_aux = prove
 (`!k f n. stack_get_labels (copy_ret_aux k f n:(A)stack_prog) = {}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[copy_ret_aux_thm; stack_list_Seq_def; stack_get_labels_def; UNION_EMPTY]);;

(* HOL4 line 7633 *)
let get_labels_copy_ret = prove
 (`!perf is_handle (kf:num#num#C) (vs:B list) (q:(A)stack_prog).
     stack_get_labels (copy_ret perf is_handle kf vs q) = stack_get_labels q`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `kf:num#num#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ff:num#C` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ff:num#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `f':C` SUBST1_TAC)) THEN
  REWRITE_TAC[copy_ret_def; SeqStackFree_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[stack_get_labels_def; W2SP3AUX_get_labels_copy_ret_aux; UNION_EMPTY]);;

(* W2SP3AUX: an index step through DROP *)
let W2SP3AUX_EL_DROP_SUC = prove
 (`!m j (l:A list). SUC m + j < LENGTH l ==> EL m (DROP (SUC j) l) = EL (SUC m) (DROP j l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `SUC j`; `l:A list`] EL_DROP) THEN
  MP_TAC(ISPECL [`SUC m`; `j:num`; `l:A list`] EL_DROP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* W2SP3AUX: HOL4 stackSem state_component_equality *)
let w2sp3aux_stack_state_component_equality =
  (record_info "stack_state").ri_component_equality;;

(* HOL4 line 7643 *)
let evaluate_copy_ret_aux = prove
 (`!k f n (t:(A,C,FFI)stack_state).
     stack_state_use_stack t /\ ~(f = 0) /\
     f <= LENGTH (stack_state_stack t) - (stack_state_stack_space t + n)
     ==> ?t'.
           stack_evaluate (copy_ret_aux k f n,t) = (NONE,t') /\
           ?t'_stack t'_regs.
             t' = stack_state_stack_fupd (K t'_stack) (stack_state_regs_fupd (K t'_regs) t) /\
             LENGTH t'_stack = LENGTH (stack_state_stack t) /\
             stack_state_stack_space t' = stack_state_stack_space t /\
             DROP (f + n + stack_state_stack_space t') t'_stack =
               DROP (f + n + stack_state_stack_space t) (stack_state_stack t) /\
             (!i. ~(i = k) ==> stack_get_var i t' = stack_get_var i t) /\
             (!m. m < f - n
                  ==> EL m (DROP (n + stack_state_stack_space t') t'_stack) =
                      EL m (DROP (n + stack_state_stack_space t) (stack_state_stack t))) /\
             (let stack' = DROP (stack_state_stack_space t') t'_stack
              and stack = DROP (stack_state_stack_space t) (stack_state_stack t) in
              !x. x < n ==> EL (x + f) stack' = EL x stack)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[copy_ret_aux_thm; stack_list_Seq_def] THENL
  [REWRITE_TAC[w2sp3aux_seval "stack_Skip"; PAIR_EQ] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   EXISTS_TAC `t:(A,C,FFI)stack_state` THEN REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`stack_state_stack (t:(A,C,FFI)stack_state)`;
                         `stack_state_regs (t:(A,C,FFI)stack_state)`] THEN
   SIMP[w2sp3aux_stack_state_component_equality; LT];
   ALL_TAC] THEN
  ABBREV_TAC `ss = stack_state_stack_space (t:(A,C,FFI)stack_state)` THEN
  ABBREV_TAC `stk = stack_state_stack (t:(A,C,FFI)stack_state)` THEN
  SUBGOAL_THEN `ss + n < LENGTH (stk:((A)word_loc)list) /\ ~(LENGTH stk <= ss + n + f)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `stack_state_stack_fupd (K (LUPDATE (EL (ss + n) stk) (ss + n + f) stk))
       (stack_state_regs_fupd (K (stack_state_regs t |+ (k,EL (ss + n) (stk:((A)word_loc)list))))
       (t:(A,C,FFI)stack_state))`) THEN
  SIMP[LENGTH_LUPDATE] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `ts:((A)word_loc)list`
       (X_CHOOSE_THEN `tr:(num,(A)word_loc)fmap` STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackLoad";
              w2sp3aux_seval "StackStore"] THEN
  ASM_REWRITE_TAC[pair_CASE_def] THEN
  SIMP[stack_set_var_def; stack_get_var_def; FLOOKUP_UPDATE] THEN
  MAP_EVERY EXISTS_TAC [`ts:((A)word_loc)list`; `tr:(num,(A)word_loc)fmap`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `stack_state_stack_space (t1:(A,C,FFI)stack_state) = ss`]) THEN
  SUBGOAL_THEN `LENGTH (LUPDATE (EL (ss + n) stk) (ss + n + f) (stk:((A)word_loc)list)) =
                LENGTH stk` ASSUME_TAC THENL [REWRITE_TAC[LENGTH_LUPDATE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[DROP_SUC] THEN
   FIRST_X_ASSUM(fun th -> if can (find_term ((=) `f + n + ss:num`)) (concl th) &&
                              is_eq (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
   REWRITE_TAC[DROP_DROP_T; GSYM ADD1; word_to_stackProof_DROP_LUPDATE] THEN
   REWRITE_TAC[ARITH_RULE `ss + n + f < 1 + f + n + ss`];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> can (find_term ((=)
     `stack_get_var:num->(A,C,FFI)stack_state->((A)word_loc)option`)) (concl th))) THEN
   ASM_REWRITE_TAC[stack_get_var_def] THEN SIMP[FLOOKUP_UPDATE];
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `SUC m + n + ss < LENGTH (stk:((A)word_loc)list) /\ ~(SUC m + n + ss = ss + n + f)`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `SUC m` o
     check (fun th -> can (find_term ((=) `f - n:num`)) (concl th))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[W2SP3AUX_EL_DROP_SUC] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_SIMP_TAC[EL_DROP; EL_LUPDATE] THEN ASM_SIMP_TAC[GSYM EL_DROP; W2SP3AUX_EL_DROP_SUC];
   REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:num = n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `EL (f + n + ss) (ts:((A)word_loc)list) =
                  EL (f + n + ss) (LUPDATE (EL (ss + n) stk) (ss + n + f) (stk:((A)word_loc)list))`
      MP_TAC THENL
    [SUBGOAL_THEN `f + n + ss < LENGTH (stk:((A)word_loc)list)` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o AP_TERM `HD:((A)word_loc)list->(A)word_loc` o
       check (fun th -> is_eq (concl th) && can (find_term ((=) `f + n + ss:num`)) (concl th))) THEN
     ASM_SIMP_TAC[HD_DROP; LENGTH_LUPDATE];
     ALL_TAC] THEN
    SUBGOAL_THEN `n + f + ss < LENGTH (stk:((A)word_loc)list) /\ n + ss < LENGTH stk /\
                  f + n + ss = n + f + ss /\ ss + n + f = n + f + ss /\ ss + n = n + ss /\
                  n + f + ss < LENGTH (ts:((A)word_loc)list)`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_DROP; EL_LUPDATE] THEN
    MP_TAC(ISPECL [`n + f:num`; `ss:num`; `ts:((A)word_loc)list`] EL_DROP) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM ADD_ASSOC];
    SUBGOAL_THEN `x < n /\ x + ss < LENGTH (stk:((A)word_loc)list) /\ ~(x + ss = ss + n + f) /\
                  x + f + ss < LENGTH stk` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> can (find_term ((=)
      `EL (x + f):((A)word_loc)list->(A)word_loc`)) (concl th))) THEN
    ASM_SIMP_TAC[EL_DROP; EL_LUPDATE; LENGTH_LUPDATE]]]);;

(* W2SP3AUX: the inductive step of evaluate_copy_ret_aux_clock (an OCaml   *)
(* tactic): the induction hypothesis at the state of the right hand side,   *)
(* with its clock update moved inside by the record simplifier             *)
let W2SP3AUX_CLOCK_IH_TAC : tactic = fun (asl,w as g) ->
  let x = rand(rand(rand(rhs w))) in
  FIRST_X_ASSUM(fun ih -> let th = CAKE_SIMP_RULE [] (ISPEC x ih) in REWRITE_TAC[th]) g;;

(* HOL4 line 7706 *)
let evaluate_copy_ret_aux_clock = prove
 (`!(t:(A,C,FFI)stack_state) k f n clk.
     stack_evaluate (copy_ret_aux k f n,stack_state_clock_fupd (K clk) t) =
     (I ## (\t. stack_state_clock_fupd (K clk) t)) (stack_evaluate (copy_ret_aux k f n,t))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`t:(A,C,FFI)stack_state`,`t:(A,C,FFI)stack_state`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[copy_ret_aux_thm; stack_list_Seq_def] THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC[w2sp3aux_seval "stack_Skip"; PAIR_MAP_THM; I_THM]; ALL_TAC] THEN
  REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackLoad";
              w2sp3aux_seval "StackStore"] THEN
  SIMP[stack_set_var_def; stack_empty_env_def; stack_get_var_def] THEN
  ASM_CASES_TAC `stack_state_use_stack (t:(A,C,FFI)stack_state)` THEN SIMP[PAIR_MAP_THM] THEN
  COND_CASES_TAC THEN SIMP[PAIR_MAP_THM; FLOOKUP_UPDATE] THEN
  COND_CASES_TAC THEN SIMP[PAIR_MAP_THM; FLOOKUP_UPDATE] THEN W2SP3AUX_CLOCK_IH_TAC);;

(* HOL4 lines 7717-7722: fun uncurry_case_rand, fun note_tac (ML functions) *)

(* HOL4 line 7724 *)
let evaluate_cont_loop_handler = prove
 (`!c (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (c,s) = (res,s1) /\ wl_cont_loop res
     ==> wl_state_handler s1 = wl_state_handler s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(A)wl_prog`; `s:(A,C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  MP_TAC(ISPEC `x:(A)wl_result` (cases "wl_result")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_cont_loop_def] THEN SIMP[]);;

(* HOL4 line 7735 *)
let get_labels_loc_check_subspt = prove
 (`!(p:(A)stack_prog) (c1:((B)stack_prog)spt) c2.
     stack_get_labels p SUBSET loc_check c1 /\ subspt c1 c2
     ==> stack_get_labels p SUBSET loc_check c2`,
  MESON_TAC[SUBSET_TRANS; loc_check_SUBSET]);;

(* W2SP3AUX: state_rel for a state whose locals are a wf part of the old ones *)
let W2SP3AUX_state_rel_locals = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra l.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\ wf l /\
     (!n v. lookup n l = SOME v ==> lookup n (wl_state_locals s) = SOME v)
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_locals_fupd (K l) s) t
           lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN SIMP[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 7750 *)
let state_rel_cut_state = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens names s'.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_cut_state (names,LN) s = SOME s'
     ==> word_to_stackProof_state_rel ac k f f' s' t lens 0`,
  REWRITE_TAC[wl_cut_state_def; wl_cut_env_def; cut_envs_def; cut_names_def] THEN
  REPEAT GEN_TAC THEN GVS[COND_CASE_EQ; option_case_eq; pair_case_eq] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC W2SP3AUX_state_rel_locals THEN ASM_REWRITE_TAC[wf_inter; lookup_inter_EQ] THEN
  MESON_TAC[]);;

(* W2SP3AUX: the io events and the stack bound after one round of a Loop  *)
let W2SP3AUX_loop_mono = prove
 (CASE_TERM `!q (r:(A,C,FFI)wl_state) names c exit_names res s1.
     (if wl_cont_loop q
      then (if wl_state_clock r = 0 then (SOME wl_TimeOut,wl_flush_state T r)
            else wl_evaluate (wl_STOP (wl_Loop names c exit_names),wl_dec_clock r))
      else if q = SOME (wordSem_Break 0)
           then (match wl_cut_state (exit_names,LN) r with
                   NONE -> (SOME wl_Error,r)
                 | SOME s2 -> (NONE,s2))
           else (wl_exit_loop q,r)) = (res,s1)
     ==> ffi_state_io_events (wl_state_ffi r) <<= ffi_state_io_events (wl_state_ffi s1) /\
         (the (wl_state_stack_limit r + 1) (wl_state_stack_max r) > wl_state_stack_limit r
          ==> the (wl_state_stack_limit s1 + 1) (wl_state_stack_max s1) >
              wl_state_stack_limit s1)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `wl_cont_loop (q:((A)wl_result)option)` THEN ASM_REWRITE_TAC[] THENL
  [COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[wl_flush_state_def; w2sp3aux_wl_accfupds; K_THM; IS_PREFIX_REFL];
    REWRITE_TAC[wl_STOP_def] THEN DISCH_TAC THEN
    SUBGOAL_THEN `wl_state_ffi (wl_dec_clock (r:(A,C,FFI)wl_state)) = wl_state_ffi r /\
                  wl_state_stack_limit (wl_dec_clock r) = wl_state_stack_limit r /\
                  wl_state_stack_max (wl_dec_clock r) = wl_state_stack_max r` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[wl_dec_clock_def; w2sp3aux_wl_accfupds]; ALL_TAC] THEN
    ASM_MESON_TAC[wl_evaluate_io_events_mono; evaluate_stack_limit_stack_max]];
   COND_CASES_TAC THENL
   [CASES_ON `wl_cut_state (exit_names,LN) (r:(A,C,FFI)wl_state)` THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL
    [DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN REWRITE_TAC[IS_PREFIX_REFL];
     DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
     FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "wl_cut_state" o concl)) THEN
     REWRITE_TAC[wl_cut_state_def] THEN
     CASES_ON `wl_cut_env (exit_names,LN) (wl_state_locals (r:(A,C,FFI)wl_state))` THEN
     CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[w2sp3aux_wl_accfupds; IS_PREFIX_REFL]];
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[IS_PREFIX_REFL]]]);;

(* HOL4 line 7767: Resume comp_correct[Loop] *)
let word_to_stackProof_comp_correct_Loop = prove
 (word_to_stackProof_comp_case "wl_Loop",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHL") (LABEL_TAC "IHB")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `post_alloc_conventions k (c:(A)wl_prog) /\ flat_exp_conventions c /\
                max_var c < 2 * f' + 2 * k` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `post_alloc_conventions k (wl_Loop names c exit_names:(A)wl_prog)` THEN
   UNDISCH_TAC `flat_exp_conventions (wl_Loop names c exit_names:(A)wl_prog)` THEN
   UNDISCH_TAC `max_var (wl_Loop names c exit_names:(A)wl_prog) < 2 * f' + 2 * k` THEN
   REWRITE_TAC[post_alloc_conventions_def; call_arg_convention_def; flat_exp_conventions_def;
               wl_every_var_def; every_stack_var_def; max_var_def; W2SP3AUX_max3_LT] THEN
   SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `word_to_stack_comp ac F (wl_Loop names c exit_names) (bs,n) (k,f,f') =
               (sprog:(A)stack_prog,bs',n')` THEN
  REWRITE_TAC[w2sp3aux_comp_clause "wl_Loop"] THEN
  MP_TAC(ISPEC `word_to_stack_comp ac F c (bs,n) (k,f,f'):(A)stack_prog#(A word)app_list#num`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `bn1:(A word)app_list#num`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def]) THEN
  UNDISCH_TAC `wl_evaluate (wl_Loop names c exit_names,s:(A,num#C,FFI)wl_state) = res,s1` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [w2sp3aux_wl_eval_clause "wl_Loop"] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
  [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (c,a:(A,num#C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `r:(A,num#C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(q = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `~(res = SOME (wl_Error:(A)wl_result))` THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
     REWRITE_TAC[wl_cont_loop_def; wl_exit_loop_def; option_INJ; PAIR_EQ]
       THEN CASE_REWRITE_TAC[] THEN
     MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `word_to_stackProof_state_rel ac k f f' (a:(A,num#C,FFI)wl_state) t lens 0`
      ASSUME_TAC THENL
    [MATCH_MP_TAC state_rel_cut_state THEN
     MAP_EVERY EXISTS_TAC [`s:(A,num#C,FFI)wl_state`; `names:num_set`]
       THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "IHB" (MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `q:((A)wl_result)option`;
       `r:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `bs:(A word)app_list`; `n:num`;
       `bs':(A word)app_list`; `n':num`; `q1:(A)stack_prog`; `lens:num list`] o
       REWRITE_RULE[] o SPEC `a:(A,num#C,FFI)wl_state`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `tb:(A,C,FFI)stack_state`
      (X_CHOOSE_THEN `resb:((A)stack_result)option` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `wl_state_handler (a:(A,num#C,FFI)wl_state) = wl_state_handler
    (s:(A,num#C,FFI)wl_state)` ASSUME_TAC THENL
    [UNDISCH_TAC `wl_cut_state (names,LN) (s:(A,num#C,FFI)wl_state) = SOME a` THEN
     REWRITE_TAC[wl_cut_state_def] THEN
     CASES_ON `wl_cut_env (names,LN) (wl_state_locals (s:(A,num#C,FFI)wl_state))` THEN
     CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[w2sp3aux_wl_accfupds]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_loop_mono o
      check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    ASM_CASES_TAC `OPTION_MAP compile_result (q:((A)wl_result)option) = resb` THENL
    [ALL_TAC;
     MAP_EVERY EXISTS_TAC [`ck:num`; `tb:(A,C,FFI)stack_state`; `resb:((A)stack_result)option`] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) && w2sp3aux_has_const "stackSem_Halt"
       (concl th))) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[w2sp3aux_seval "stack_Loop"; pair_CASE_def; FST; SND; stack_cont_loop_def;
                     stack_exit_loop_def] THEN
     FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
       check (fun th -> can (find_term ((=) `t:(A,C,FFI)stack_state`)) (concl th) &&
                        w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th))) THEN
     SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) =
                     SOME (stackSem_Halt (wl_Word (word 2))))` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      ASM_SIMP_TAC[compile_result_NOT_2]; ALL_TAC] THEN
     (* ASM_MESON_TAC took 27 s for each conjunct (the context is large) *)
     CONJ_TAC THENL
      [MATCH_MP_TAC IS_PREFIX_TRANS THEN
       EXISTS_TAC `ffi_state_io_events (wl_state_ffi (r:(A,num#C,FFI)wl_state))` THEN
       ASM_REWRITE_TAC[];
       FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC)]] THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) =
    `resb:((A)stack_result)option`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) && w2sp3aux_has_const "stackSem_Halt"
      (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    ASM_CASES_TAC `wl_cont_loop (q:((A)wl_result)option)` THEN ASM_REWRITE_TAC[]) THENL
  [(* cont_loop q *)
   (SUBGOAL_THEN `word_to_stackProof_state_rel ac k f f' (r:(A,num#C,FFI)wl_state) tb lens 0 /\
                    stack_cont_loop (OPTION_MAP compile_result (q:((A)wl_result)option)) /\
                    ~(OPTION_MAP compile_result q = SOME (stack_TimeOut:(A)stack_result))`
                      STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "option_CASE" (concl th) &&
        w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) && not
          (is_forall(concl th)))) THEN
      UNDISCH_TAC `wl_cont_loop (q:((A)wl_result)option)` THEN
      MP_TAC(ISPEC `q:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
      MP_TAC(ISPEC `x:(A)wl_result` (cases "wl_result")) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[wl_cont_loop_def; compile_result_def; stack_cont_loop_def] THEN SIMP_TAC[];
      ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
       check (fun th -> can (find_term ((=) `tb:(A,C,FFI)stack_state`)) (concl th) &&
                        w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th))) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ]) THENL
   [(* TimeOut *)
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `stack_empty_env (tb:(A,C,FFI)stack_state)`;
                             `SOME (stack_TimeOut:(A)stack_result)`] THEN
       ASM_REWRITE_TAC[w2sp3aux_seval "stack_Loop"; pair_CASE_def; FST; SND] THEN
    CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
       REWRITE_TAC[wl_flush_state_def; stack_empty_env_def; w2sp3aux_wl_accfupds;
                   w2sp3aux_stack_accfupds] THEN ASM_REWRITE_TAC[];
    (* the next round *)
    DISCH_TAC THEN
       FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
         check (w2sp3aux_is_seval_of `q1:(A)stack_prog`)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM]) THEN
       REMOVE_THEN "IHL" (MP_TAC o SPECL [`a:(A,num#C,FFI)wl_state`; `q:((A)wl_result)option`;
         `r:(A,num#C,FFI)wl_state`]) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
         `s1:(A,num#C,FFI)wl_state`; `stack_dec_clock (tb:(A,C,FFI)stack_state)`;
           `bs:(A word)app_list`;
         `n:num`; `bs':(A word)app_list`; `n':num`; `stack_Loop q1:(A)stack_prog`;
           `lens:num list`]) THEN
       ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
    [(REWRITE_TAC[wl_STOP_def; stack_dec_clock_def; w2sp3aux_stack_accfupds;
      w2sp3aux_comp_clause "wl_Loop";
                     stack_get_labels_def] THEN
         ASM_REWRITE_TAC[pair_CASE_def]) THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `r:(A,num#C,FFI)wl_state`;
            `tb:(A,C,FFI)stack_state`; `lens:num list`;
              `0`] word_to_stackProof_state_rel_dec_clock) THEN
         ASM_REWRITE_TAC[stack_dec_clock_def];
      MATCH_MP_TAC LE_TRANS THEN
           EXISTS_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IS_PREFIX_TRANS THEN
           EXISTS_TAC `DROP (n - LENGTH (append (bs:(A word)app_list)))
                         (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
           EXISTS_TAC `loc_check (stack_state_code (t:(A,C,FFI)stack_state))` THEN
           ASM_SIMP_TAC[loc_check_SUBSET]];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
         (X_CHOOSE_THEN `res1:((A)stack_result)option` STRIP_ASSUME_TAC))) THEN
       MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t1:(A,C,FFI)stack_state`;
         `res1:((A)stack_result)option`] THEN
       SUBGOAL_THEN `wl_state_handler (wl_dec_clock (r:(A,num#C,FFI)wl_state)) = wl_state_handler
         (s:(A,num#C,FFI)wl_state)`
         ASSUME_TAC THENL
       [REWRITE_TAC[wl_dec_clock_def; w2sp3aux_wl_accfupds] THEN
        MP_TAC(ISPECL [`c:(A)wl_prog`; `a:(A,num#C,FFI)wl_state`; `q:((A)wl_result)option`;
                       `r:(A,num#C,FFI)wl_state`] evaluate_cont_loop_handler) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `wl_state_handler (wl_dec_clock (r:(A,num#C,FFI)wl_state))
         = wl_state_handler (s:(A,num#C,FFI)wl_state)`]) THEN
       ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPECL [`q1:(A)stack_prog`; `stack_state_clock_fupd (K (stack_state_clock t + ck))
         (t:(A,C,FFI)stack_state)`;
         `OPTION_MAP compile_result (q:((A)wl_result)option)`; `tb:(A,C,FFI)stack_state`]
         (INST [`ck':num`,`extra:num`] stack_evaluate_add_clock)) THEN
       ASM_REWRITE_TAC[] THEN SIMP[GSYM ADD_ASSOC] THEN DISCH_TAC THEN
       ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Loop"] THEN
       ASM_REWRITE_TAC[pair_CASE_def; FST; SND; stack_STOP_def; stack_dec_clock_def] THEN
       SIMP[] THEN
    SUBGOAL_THEN `(stack_state_clock (tb:(A,C,FFI)stack_state) + ck') - 1 = (stack_state_clock
      tb - 1) + ck'`
         SUBST1_TAC THENL
       [UNDISCH_TAC `~(stack_state_clock (tb:(A,C,FFI)stack_state) = 0)`
         THEN ARITH_TAC; ALL_TAC] THEN
       FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_is_seval_of `stack_Loop q1:(A)stack_prog`)) THEN
       REWRITE_TAC[stack_dec_clock_def] THEN SIMP[]];
   (* not cont_loop q *)
   ASM_CASES_TAC `q = SOME (wordSem_Break 0:(A)wl_result)` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
      REWRITE_TAC[wl_cont_loop_def] THEN
      CASES_ON `wl_cut_state (exit_names,LN) (r:(A,num#C,FFI)wl_state)` THEN
      CASE_REWRITE_TAC[PAIR_EQ] THENL
      [DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      MAP_EVERY EXISTS_TAC [`ck:num`; `tb:(A,C,FFI)stack_state`;
        `NONE:((A)stack_result)option`] THEN
      ASM_REWRITE_TAC[w2sp3aux_seval "stack_Loop"; pair_CASE_def; FST; SND] THEN
      CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def; stack_cont_loop_def;
        stack_exit_loop_def] THEN
      MATCH_MP_TAC state_rel_cut_state THEN
      MAP_EVERY EXISTS_TAC [`r:(A,num#C,FFI)wl_state`; `exit_names:num_set`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "option_CASE" (concl th) &&
        w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) && not
          (is_forall(concl th)))) THEN
      CASE_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
         ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
         MAP_EVERY EXISTS_TAC [`ck:num`; `tb:(A,C,FFI)stack_state`;
           `stack_exit_loop (OPTION_MAP compile_result (q:((A)wl_result)option))`] THEN
         ASM_REWRITE_TAC[w2sp3aux_seval "stack_Loop"; pair_CASE_def; FST; SND] THEN
         FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "option_CASE" (concl th) &&
           w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) && not
             (is_forall(concl th)))) THEN
         UNDISCH_TAC `~wl_cont_loop (q:((A)wl_result)option)` THEN
         UNDISCH_TAC `~(q = SOME (wl_Error:(A)wl_result))` THEN
         UNDISCH_TAC `~(q = SOME (wordSem_Break 0:(A)wl_result))` THEN
         MP_TAC(ISPEC `q:((A)wl_result)option` option_CASES) THEN STRIP_TAC
           THEN ASM_REWRITE_TAC[] THEN
         CASE_REWRITE_TAC[OPTION_MAP_DEF; wl_cont_loop_def] THEN
         MP_TAC(ISPEC `x:(A)wl_result` (cases "wl_result")) THEN STRIP_TAC
           THEN ASM_REWRITE_TAC[] THEN
         CASE_REWRITE_TAC[wl_cont_loop_def; compile_result_def; stack_cont_loop_def;
           wl_exit_loop_def;
                          stack_exit_loop_def; OPTION_MAP_DEF; option_INJ] THEN
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         TRY(MAP_EVERY EXISTS_TAC [`l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`] THEN
             ASM_REWRITE_TAC[])]]);;

(* HOL4 line 7924: Resume comp_correct[Call] (the case split on ret, after  *)
(* fs[comp_def,UNCURRY_EQ]): word_to_stackProof_comp_correct_Call is stated *)
(* before the Finalise (HOL4 line 10063), after its two cases.              *)

(* W2SP3AUX: the arguments of a tail call *)
let W2SP3AUX_tail_args = prove
 (`!dest (args:num list) (a:((A)word_loc)list) (code:(num#(A)wl_prog)spt) (ssize:num spt)
     args1 (prog:(A)wl_prog) (ss:num option) k f (f':num) (q0:(A)stack_prog) dest'.
     wl_find_code dest (add_ret_loc (NONE:(num list#cutsets#(A)wl_prog#num#num)option) a)
       code ssize = SOME (args1,prog,ss) /\
     LENGTH a = LENGTH args /\ call_dest dest args (k,f,f') = (q0,dest')
     ==> isPREFIX args1 a /\ stack_arg_count dest' (LENGTH args) k = LENGTH args1 - k /\
         LENGTH args1 <= LENGTH args`,
  REPEAT GEN_TAC THEN REWRITE_TAC[add_ret_loc_def] THEN
  MP_TAC(ISPEC `dest:num option` option_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_find_code_def; call_dest_def; PAIR_EQ] THEN
  STRIP_TAC THEN EVERY_CASE_TAC THEN GVS[stack_arg_count_def; IS_PREFIX_REFL] THEN
  MP_TAC(ISPEC `a:((A)word_loc)list` list_CASES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[IS_PREFIX_BUTLAST; LENGTH_FRONT; NOT_CONS_NIL] THEN
  UNDISCH_TAC `LENGTH (CONS (h:(A)word_loc) t) = LENGTH (args:num list)` THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* W2SP3AUX: the state relation at the entry of the callee of a tail call *)
let W2SP3AUX_tail_state_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens (args:num list) a args1
     ss fs svc.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_get_vars args s = SOME a /\
     args = list_of_seq (\x. 2 * x) (LENGTH args) /\
     isPREFIX args1 a /\
     LENGTH args1 - k <= svc /\
     (if svc = 0 then fs = 0 else fs = svc + 1) /\
     the fs ss = fs /\
     LENGTH args1 - k <= f /\
     fs - (LENGTH args1 - k) <= stack_state_stack_space t + (f - (LENGTH args1 - k)) /\
     ~(wl_state_clock s = 0)
     ==> word_to_stackProof_state_rel ac k fs svc (wl_call_env args1 ss (wl_dec_clock s))
           (stack_state_stack_space_fupd
              (K ((stack_state_stack_space t + (f - (LENGTH args1 - k))) -
                  (fs - (LENGTH args1 - k))))
              (stack_state_clock_fupd (K (stack_state_clock t - 1)) t)) lens 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC `sac = LENGTH (args1:((A)word_loc)list) - k` THEN
    ABBREV_TAC `ss6 = (stack_state_stack_space (t:(A,C,FFI)stack_state) + (f - sac)) - (fs
      - sac)` THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
      (t:(A,C,FFI)stack_state) lens 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def; wl_call_env_def; wl_dec_clock_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[wf_fromList2] THEN
    SUBGOAL_THEN `ss6 + fs = stack_state_stack_space (t:(A,C,FFI)stack_state) + f` ASSUME_TAC THENL
    [MAP_EVERY EXPAND_TAC ["ss6"] THEN
     UNDISCH_TAC `fs - sac <= stack_state_stack_space (t:(A,C,FFI)stack_state) + (f - sac)` THEN
     UNDISCH_TAC `sac <= f` THEN UNDISCH_TAC `sac <= svc` THEN
     UNDISCH_TAC `if svc = 0 then fs = 0 else fs = svc + 1` THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
     (wl_state_stack_limit s)
          (wl_state_stack_max s) (wl_state_stack s) (stack_state_stack (t:(A,C,FFI)stack_state))
            (stack_state_stack_space t) 0` THEN
      REWRITE_TAC[stack_size_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `sm:num` THEN REWRITE_TAC[OPTION_MAP2_SOME] THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x1:num` o check (fun th -> is_forall(concl th) &&
        w2sp3aux_has_const "wl_stack_size" (concl th))) THEN
      ASM_REWRITE_TAC[option_INJ; IS_SOME_DEF] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) - ss6) - fs =
                    (LENGTH (stack_state_stack t) - stack_state_stack_space t) - f` SUBST1_TAC THENL
      [UNDISCH_TAC `ss6 + fs = stack_state_stack_space (t:(A,C,FFI)stack_state) + f` THEN ARITH_TAC;
       ALL_TAC] THEN
      ASM_REWRITE_TAC[SUB_0; option_INJ; UNWIND_THM1] THEN
      UNDISCH_TAC `(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) - stack_state_stack_space t)
        - f - 0 <= x1` THEN
      REWRITE_TAC[MAX; SUB_0] THEN ARITH_TAC;
   REWRITE_TAC[DROP_DROP_T] THEN
      SUBGOAL_THEN `fs + ss6 + 0 = f + stack_state_stack_space (t:(A,C,FFI)stack_state) + 0`
        SUBST1_TAC THENL
      [UNDISCH_TAC `ss6 + fs = stack_state_stack_space (t:(A,C,FFI)stack_state) + f` THEN ARITH_TAC;
       FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o
         concl)) THEN
       REWRITE_TAC[DROP_DROP_T]];
   REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME (v:(A)word_loc) /\
                    EVEN n /\ n DIV 2 < LENGTH (args1:((A)word_loc)list)` STRIP_ASSUME_TAC THENL
      [CONJ_TAC THENL
       [MP_TAC(ISPECL [`args:num list`; `s:(A,num#C,FFI)wl_state`; `a:((A)word_loc)list`; `n:num`;
                       `v:(A)word_loc`] get_vars_fromList2_eq) THEN
        DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
        [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `args:num list` then
           REWRITE_TAC[GSYM th] else NO_TAC) THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC lookup_fromList2_prefix THEN EXISTS_TAC `args1:((A)word_loc)list` THEN
         ASM_REWRITE_TAC[IS_PREFIX_DEF]];
        UNDISCH_TAC `lookup n (fromList2 (args1:((A)word_loc)list)) = SOME (v:(A)word_loc)` THEN
        REWRITE_TAC[lookup_fromList2; lookup_fromList] THEN
        COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]];
       ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o
        check (fun th -> is_forall(concl th) && w2sp3aux_has_const "EVEN" (concl th) &&
                         w2sp3aux_has_const "wl_state_locals" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP oEL_TAKE_E) THEN REWRITE_TAC[oEL_DROP] THEN
      SUBGOAL_THEN `fs - 1 - (n DIV 2 - k) < fs /\ n DIV 2 < k + svc /\
                    ss6 + 0 + fs - 1 - (n DIV 2 - k) = stack_state_stack_space
                      (t:(A,C,FFI)stack_state) + 0 + f - 1 - (n DIV 2 - k)`
        STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `ss6 + fs = stack_state_stack_space (t:(A,C,FFI)stack_state) + f` THEN
       UNDISCH_TAC `~(n DIV 2 < k)` THEN UNDISCH_TAC `n DIV 2 < LENGTH
         (args1:((A)word_loc)list)` THEN
       UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
       UNDISCH_TAC `sac <= svc` THEN UNDISCH_TAC `sac <= f` THEN
       UNDISCH_TAC `if svc = 0 then fs = 0 else fs = svc + 1` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LLOOKUP_TAKE; oEL_DROP] THEN
   MATCH_MP_TAC(MESON[] `(a:num) = b ==> oEL a (l:((A)word_loc)list) = x ==> oEL b l = x`) THEN
      UNDISCH_TAC `ss6 + fs = stack_state_stack_space (t:(A,C,FFI)stack_state) + f` THEN
      UNDISCH_TAC `~(n DIV 2 < k)` THEN UNDISCH_TAC `n DIV 2 < LENGTH
        (args1:((A)word_loc)list)` THEN
      UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
      UNDISCH_TAC `sac <= svc` THEN UNDISCH_TAC `sac <= f` THEN
      UNDISCH_TAC `if svc = 0 then fs = 0 else fs = svc + 1` THEN ARITH_TAC]);;

(* W2SP3AUX: the parts of compile_prog *)
let W2SP3AUX_compile_prog_unfold = prove
 (`!(ac:(A)asm_config) perf prog x k bs stack_prog fs bs2.
     word_to_stack_compile_prog ac perf prog x k bs = (stack_prog,fs,bs2)
     ==> ?q1 svc. svc = MAX ((max_var prog DIV 2 + 1) - k) (x - k) /\
                  fs = (if svc = 0 then 0 else svc + 1) /\
                  word_to_stack_comp ac perf prog bs (k,fs,svc) = (q1,bs2) /\
                  stack_prog = stack_Seq (StackAlloc (fs - (x - k))) q1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun (asl,w) ->
    let c = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_to_stack_comp"
                                with Failure _ -> false) w in
    MP_TAC(ISPEC c PAIR_SURJECTIVE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `b:(A word)app_list#num`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`q1:(A)stack_prog`;
    `MAX ((max_var (prog:(A)wl_prog) DIV 2 + 1) - k) (x - k)`] THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

(* W2SP3AUX: the conventions of the code found by find_code *)
let W2SP3AUX_find_code_conv = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra dest
     (args:((A)word_loc)list) args1 (prog:(A)wl_prog) (ss:num option).
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     wl_find_code dest args (wl_state_code s) (wl_state_stack_size s) = SOME (args1,prog,ss)
     ==> post_alloc_conventions k prog /\ flat_exp_conventions prog`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p n. lookup p (wl_state_code (s:(A,num#C,FFI)wl_state)) = SOME (n,prog)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `wl_find_code dest (args:((A)word_loc)list)
                  (wl_state_code (s:(A,num#C,FFI)wl_state))
                  (wl_state_stack_size s) = SOME (args1,prog:(A)wl_prog,ss:num option)` THEN
   MP_TAC(ISPEC `dest:num option` option_CASES) THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[wl_find_code_def] THEN STRIP_TAC THEN EVERY_CASE_TAC THEN GVS[] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                 (t:(A,C,FFI)stack_state) lens extra` THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `prog:(A)wl_prog`; `n:num`] o
    check (fun th -> is_forall(concl th) && w2sp3aux_has_const "post_alloc_conventions"
      (concl th) &&
                     w2sp3aux_has_const "word_to_stack_compile_prog" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* W2SP3AUX: the variables of a callee are below its frame *)
let W2SP3AUX_max_var_svc = prove
 (`!k (prog:(A)wl_prog) x.
     post_alloc_conventions k prog
     ==> max_var prog < 2 * MAX ((max_var prog DIV 2 + 1) - k) x + 2 * k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[post_alloc_conventions_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EVEN (max_var (prog:(A)wl_prog))` MP_TAC THENL
  [MATCH_MP_TAC max_var_intro THEN REWRITE_TAC[EVEN] THEN
   MATCH_MP_TAC every_var_mono THEN EXISTS_TAC `is_phy_var` THEN
   ASM_REWRITE_TAC[is_phy_var_def; GSYM EVEN_MOD2];
   ALL_TAC] THEN
  REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ARITH_RULE `(2 * m) DIV 2 = m`; misc_TWOxDIV2] THEN REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* W2SP3AUX: a callee frame that does not fit makes the stack bound fail *)
let W2SP3AUX_call_overflow = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens ss fs sac.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\ the fs ss = fs /\ sac <= f /\
     stack_state_stack_space t + (f - sac) < fs - sac
     ==> the (wl_state_stack_limit s + 1)
           (OPTION_MAP2 MAX (wl_state_stack_max s)
              (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) ss)) >
         wl_state_stack_limit s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `OPTION_MAP2 MAX (wl_state_stack_max (s:(A,num#C,FFI)wl_state))
                  (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) ss)` option_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[the_def] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "OPTION_MAP2" (concl th) &&
    is_eq(concl th))) THEN
  REWRITE_TAC[OPTION_MAP2_SOME] THEN STRIP_TAC THEN
  UNDISCH_TAC `stack_size_rel f (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
     (wl_state_stack_limit s) (wl_state_stack_max s) (wl_state_stack s)
     (stack_state_stack (t:(A,C,FFI)stack_state)) (stack_state_stack_space t) 0` THEN
  REWRITE_TAC[stack_size_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x1:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x2':num = fs` ASSUME_TAC THENL
  [UNDISCH_TAC `the fs (ss:num option) = fs` THEN ASM_REWRITE_TAC[the_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + f <= LENGTH
    (stack_state_stack t)` THEN
  UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + (f - sac) < fs - sac` THEN
  UNDISCH_TAC `sac <= f` THEN REWRITE_TAC[MAX; GT] THEN ARITH_TAC);;

(* W2SP3AUX: the stack result of a good return is a good return *)
let W2SP3AUX_bad_fun_return = prove
 (`!r:((A)wl_result)option.
     ~wl_bad_fun_return r ==> ~stack_bad_fun_return (OPTION_MAP compile_result r)`,
  GEN_TAC THEN MP_TAC(ISPEC `r:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_bad_fun_return_def; OPTION_MAP_DEF] THEN
  MP_TAC(ISPEC `x:(A)wl_result` (cases "wl_result")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_bad_fun_return_def; compile_result_def; stack_bad_fun_return_def]);;

(* W2SP3AUX: discharge a case whose word result is SOME Error (an OCaml   *)
(* tactic)                                                                  *)
let W2SP3AUX_ERR_TAC : tactic =
  TRY(DISCH_THEN(MP_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* HOL4 line 7935: Resume comp_correct[Call_tail] (the Call case with       *)
(* ret = NONE)                                                               *)
let word_to_stackProof_comp_correct_Call_tail = prove
 (word_to_stackProof_comp_call_case false,
  GEN_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH" o CONJUNCT1) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `word_to_stack_comp ac F (wl_Call NONE dest args handler) (bs,n) (k,f,f') =
                 (sprog:(A)stack_prog,bs',n')` THEN
    REWRITE_TAC[w2sp3aux_comp_clause "wl_Call"] THEN
    MP_TAC(ISPEC `call_dest dest args (k,f,f'):(A)stack_prog#(num+num)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q0:(A)stack_prog` (X_CHOOSE_THEN `dest':num+num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; UNION_SUBSET]) THEN
    UNDISCH_TAC `wl_evaluate (wl_Call NONE dest args handler,s:(A,num#C,FFI)wl_state) = res,s1` THEN
    REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Call"] THEN
    CASES_ON `wl_get_vars args (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    W2SP3AUX_ERR_TAC THEN
    ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)`
      THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    W2SP3AUX_ERR_TAC THEN
    CASES_ON `wl_find_code dest (add_ret_loc (NONE:(num list#cutsets#(A)wl_prog#num#num)option)
      (a:((A)word_loc)list)) (wl_state_code (s:(A,num#C,FFI)wl_state)) (wl_state_stack_size s)` THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC THEN
    MP_TAC(ISPEC `a':((A)word_loc)list#(A)wl_prog#num option` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `args1:((A)word_loc)list` (X_CHOOSE_THEN `pss:(A)wl_prog#num option`
      SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `pss:(A)wl_prog#num option` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `prog:(A)wl_prog` (X_CHOOSE_THEN `ss:num option` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
    ASM_CASES_TAC `handler:(num#(A)wl_prog#num#num)option = NONE` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    W2SP3AUX_ERR_TAC THEN
    MP_TAC(ISPECL [`dest:num option`; `args:num list`; `ac:(A)asm_config`; `k:num`;
      `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `q0:(A)stack_prog`;
      `dest':num+num`; `a:((A)word_loc)list`; `NONE:(num list#cutsets#(A)wl_prog#num#num)option`]
      call_dest_lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t4:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o SPECL [`args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`])))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `bsc:(A word)app_list` (X_CHOOSE_THEN `ic:num`
      (X_CHOOSE_THEN `bs2:(A word)app_list` (X_CHOOSE_THEN `i2:num` (X_CHOOSE_THEN `fs:num`
      (X_CHOOSE_THEN `stack_prog:(A)stack_prog` STRIP_ASSUME_TAC)))))) THEN
    SUBGOAL_THEN `args = list_of_seq (\x. 2 * x) (LENGTH (args:num list)) /\
                  LENGTH args - 1 < f' + k` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `post_alloc_conventions k (wl_Call NONE dest args handler:(A)wl_prog)` THEN
     UNDISCH_TAC `max_var (wl_Call NONE dest args handler:(A)wl_prog) < 2 * f' + 2 * k` THEN
     REWRITE_TAC[post_alloc_conventions_def; call_arg_convention_def; max_var_def] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     UNDISCH_TAC `MAX_LIST (args:num list) < 2 * f' + 2 * k` THEN
     FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
     REWRITE_TAC[MAX_LIST_GENLIST_evens; LENGTH_LIST_OF_SEQ] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_length_lemma) THEN
    MP_TAC(ISPECL [`dest:num option`; `args:num list`; `a:((A)word_loc)list`;
      `wl_state_code (s:(A,num#C,FFI)wl_state)`; `wl_state_stack_size (s:(A,num#C,FFI)wl_state)`;
      `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`; `k:num`; `f:num`; `f':num`;
      `q0:(A)stack_prog`; `dest':num+num`] W2SP3AUX_tail_args) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP3AUX_compile_prog_unfold o
       check (w2sp3aux_has_const "word_to_stack_compile_prog" o concl)) THEN
     DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `svc:num`
       (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
         STRIP_ASSUME_TAC)))) THEN
     ABBREV_TAC `sac = LENGTH (args1:((A)word_loc)list) - k` THEN
     FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
       check (fun th -> can (find_term ((=) `t4:(A,C,FFI)stack_state`)) (concl th) &&
                        w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th))) THEN
     SUBGOAL_THEN `stack_state_clock (t:(A,C,FFI)stack_state) = wl_state_clock
       (s:(A,num#C,FFI)wl_state)`
       ASSUME_TAC THENL
     [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
       (t:(A,C,FFI)stack_state) lens 0` THEN
      SIMP_TAC[word_to_stackProof_state_rel_def]; ALL_TAC] THEN
     SUBGOAL_THEN `sac <= f /\ sac <= svc /\ sac <= fs` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `if f' = 0 then f = 0 else f = f' + 1` THEN
      UNDISCH_TAC `LENGTH (args:num list) - 1 < f' + k` THEN
      UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) <= LENGTH (args:num list)` THEN
      UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
      UNDISCH_TAC `MAX ((max_var (prog:(A)wl_prog) DIV 2 + 1) - k) sac = svc` THEN
      UNDISCH_TAC `(if svc = 0 then 0 else svc + 1) = fs` THEN
      REWRITE_TAC[MAX] THEN ARITH_TAC;
      ALL_TAC] THEN
  SUBGOAL_THEN `word_to_stack_stack_free (dest':num+num) (LENGTH (args:num list))
    (k,f,f':num) = f - sac`
       SUBST1_TAC THENL [ASM_REWRITE_TAC[word_to_stack_stack_free_def]; ALL_TAC] THEN
     SUBGOAL_THEN `!ck. stack_evaluate
         (stack_Seq q0 (SeqStackFree (f - sac) (stack_Call NONE dest' NONE)),
          stack_state_clock_fupd (K (stack_state_clock t + ck)) (t:(A,C,FFI)stack_state)) =
         stack_evaluate (stack_Call NONE dest' NONE,
          stack_state_stack_space_fupd (K (stack_state_stack_space t4 + (f - sac)))
            (stack_state_clock_fupd (K (stack_state_clock t + ck)) (t4:(A,C,FFI)stack_state)))`
       ASSUME_TAC THENL
     [GEN_TAC THEN
      REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP evaluate_call_dest_clock th]) o
        check (fun th -> is_eq(concl th) && w2sp3aux_has_const "call_dest" (concl th))) THEN
      REWRITE_TAC[ASSUME `stack_evaluate (q0,t:(A,C,FFI)stack_state) = NONE,t4`;
                  PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
      MP_TAC(ISPECL [`stack_state_clock_fupd (K (stack_state_clock (t:(A,C,FFI)stack_state) + ck))
        (t4:(A,C,FFI)stack_state)`;
                     `f - sac`; `stack_Call NONE dest' NONE:(A)stack_prog`]
                       evaluate_SeqStackFree) THEN
      REWRITE_TAC[w2sp3aux_stack_accfupds] THEN ANTS_TAC THENL
      [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) + f <= LENGTH
         (stack_state_stack t4)` THEN
       ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackFree";
        w2sp3aux_stack_accfupds] THEN
      SUBGOAL_THEN `~(LENGTH (stack_state_stack (t4:(A,C,FFI)stack_state)) <
                      stack_state_stack_space t4 + (f - sac))` (fun th -> REWRITE_TAC[th]) THENL
      [UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) + f <= LENGTH
        (stack_state_stack t4)` THEN
       ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[pair_CASE_def; FST; SND];
      ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
    [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     MAP_EVERY EXISTS_TAC [`0`;
       `stack_empty_env (stack_state_stack_space_fupd (K (stack_state_stack_space t4 + (f - sac)))
          (stack_state_clock_fupd (K (stack_state_clock (t:(A,C,FFI)stack_state) + 0))
            (t4:(A,C,FFI)stack_state)))`;
       `SOME (stack_TimeOut:(A)stack_result)`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[w2sp3aux_seval "stack_Call"; w2sp3aux_stack_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     SUBGOAL_THEN `stack_state_clock (t:(A,C,FFI)stack_state) = 0` (fun th -> REWRITE_TAC[th;
       ADD_CLAUSES]) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
     REWRITE_TAC[wl_flush_state_def; stack_empty_env_def; w2sp3aux_wl_accfupds;
       w2sp3aux_stack_accfupds;
                 K_THM] THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = 0` THEN
     UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
       (t4:(A,C,FFI)stack_state)` THEN
     ARITH_TAC;
     ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (prog:(A)wl_prog, wl_call_env args1 ss (wl_dec_clock
    (s:(A,num#C,FFI)wl_state)))`
       PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `r':((A)wl_result)option` (X_CHOOSE_THEN `s1':(A,num#C,FFI)wl_state`
       ASSUME_TAC)) THEN
     ASM_REWRITE_TAC[FST; SND] THEN
     ASM_CASES_TAC `wl_bad_fun_return (r':((A)wl_result)option)` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
     W2SP3AUX_ERR_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     DRULE_ALL W2SP3AUX_find_code_conv THEN STRIP_TAC THEN
     ALL_TAC THEN
  SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0) /\ ~(stack_state_clock
    (t4:(A,C,FFI)stack_state) = 0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(wl_state_clock (s:(A,num#C,FFI)wl_state) = 0)` THEN
      UNDISCH_TAC `stack_state_clock (t:(A,C,FFI)stack_state) = wl_state_clock
        (s:(A,num#C,FFI)wl_state)` THEN
      UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
        (t4:(A,C,FFI)stack_state)` THEN
      ARITH_TAC; ALL_TAC] THEN
     ASM_CASES_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + (f - sac) < fs - sac` THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[w2sp3aux_seval "stack_Call"; w2sp3aux_stack_accfupds; K_THM; ADD_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackAlloc"; stack_dec_clock_def;
                  w2sp3aux_stack_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[pair_CASE_def; FST; SND; option_DISTINCT; stack_bad_fun_return_def] THEN
      SIMP[] THEN
      SUBGOAL_THEN `~(?z. r' = SOME z /\
                           stackSem_Halt (wl_Word (word 2)) = compile_result (z:(A)wl_result))`
           (fun th -> REWRITE_TAC[th]) THENL
         [REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN GEN_TAC THEN DISJ2_TAC THEN
          ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC compile_result_NOT_2 THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
         CONJ_TAC THENL
         [MP_TAC(MATCH_MP wl_evaluate_io_events_mono (ASSUME
            `wl_evaluate (prog:(A)wl_prog, wl_call_env args1 ss (wl_dec_clock
              (s:(A,num#C,FFI)wl_state))) =
             r',s1'`)) THEN
          REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; w2sp3aux_wl_accfupds];
          MATCH_MP_TAC evaluate_stack_limit_stack_max THEN
          MAP_EVERY EXISTS_TAC [`prog:(A)wl_prog`;
            `wl_call_env args1 ss (wl_dec_clock (s:(A,num#C,FFI)wl_state))`;
              `r':((A)wl_result)option`] THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[wl_call_env_def; wl_dec_clock_def;
            w2sp3aux_wl_accfupds; K_THM] THEN
          MATCH_MP_TAC W2SP3AUX_call_overflow THEN
          MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
            `t:(A,C,FFI)stack_state`;
                                `lens:num list`; `fs:num`; `sac:num`] THEN
          ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
           `t4:(A,C,FFI)stack_state`; `lens:num list`; `args:num list`; `a:((A)word_loc)list`;
           `args1:((A)word_loc)list`; `ss:num option`; `fs:num`;
             `svc:num`] W2SP3AUX_tail_state_rel) THEN
         ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
          [FIRST_ASSUM ACCEPT_TAC;
           UNDISCH_TAC `(if svc = 0 then 0 else svc + 1) = fs` THEN ARITH_TAC;
           UNDISCH_TAC `~(stack_state_stack_space (t:(A,C,FFI)stack_state) + (f - sac) < fs
             - sac)` THEN
           ARITH_TAC];
          ALL_TAC] THEN
         DISCH_TAC THEN
  ABBREV_TAC `t6 = stack_state_stack_space_fupd
           (K ((stack_state_stack_space (t:(A,C,FFI)stack_state) + f - sac) - (fs - sac)))
           (stack_state_clock_fupd (K (stack_state_clock (t4:(A,C,FFI)stack_state) - 1)) t4)` THEN
         FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
           check (w2sp3aux_is_seval_of `q0:(A)stack_prog`)) THEN
         SUBGOAL_THEN `stack_get_labels (q1:(A)stack_prog) SUBSET loc_check (stack_state_code
           (t4:(A,C,FFI)stack_state))`
           ASSUME_TAC THENL
         [MP_TAC(MATCH_MP find_code_IMP_get_labels (ASSUME
            `stack_find_code dest' (stack_state_regs (t4:(A,C,FFI)stack_state))
              (stack_state_code t4) =
             SOME (stack_prog:(A)stack_prog)`)) THEN
          ASM_REWRITE_TAC[stack_get_labels_def; UNION_SUBSET] THEN SIMP_TAC[];
          ALL_TAC] THEN
         REMOVE_THEN "IH" (MP_TAC o SPECL [`a:((A)word_loc)list`; `prog:(A)wl_prog`;
           `args1:((A)word_loc)list`; `ss:num option`]) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o SPECL [`k:num`; `fs:num`; `svc:num`; `r':((A)wl_result)option`;
           `s1':(A,num#C,FFI)wl_state`; `t6:(A,C,FFI)stack_state`; `bsc:(A word)app_list`; `ic:num`;
           `bs2:(A word)app_list`; `i2:num`; `q1:(A)stack_prog`; `lens:num list`]) THEN
         ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds] THEN REPEAT CONJ_TAC THENL
          [MATCH_MP_TAC LE_TRANS THEN
           EXISTS_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
           MATCH_MP_TAC IS_PREFIX_TRANS THEN
           EXISTS_TAC `DROP (ic - LENGTH (append (bsc:(A word)app_list)))
                         (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
           FIRST_ASSUM ACCEPT_TAC;
           FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
             w2sp3aux_has_const "MAX" (concl th))) THEN
           MATCH_MP_TAC W2SP3AUX_max_var_svc THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
           (X_CHOOSE_THEN `res1:((A)stack_result)option` STRIP_ASSUME_TAC))) THEN
         EXISTS_TAC `ck:num` THEN
         REWRITE_TAC[w2sp3aux_seval "stack_Call"; w2sp3aux_stack_accfupds; K_THM] THEN
         ASM_REWRITE_TAC[ARITH_RULE `~(c + ck = 0) <=> ~(c = 0) \/ ~(ck = 0)`]
           THEN CASE_REWRITE_TAC[] THEN
         REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackAlloc"; stack_dec_clock_def;
                     w2sp3aux_stack_accfupds; K_THM] THEN
         ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  SUBGOAL_THEN `(stack_state_clock (t4:(A,C,FFI)stack_state) - 1) + ck = (stack_state_clock
    t4 + ck) - 1`
           ASSUME_TAC THENL
         [UNDISCH_TAC `~(stack_state_clock (t4:(A,C,FFI)stack_state) = 0)`
           THEN ARITH_TAC; ALL_TAC] THEN
         FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_is_seval_of `q1:(A)stack_prog`)) THEN
         EXPAND_TAC "t6" THEN SIMP[] THEN DISCH_TAC THEN SIMP[] THEN
  SUBGOAL_THEN `~stack_bad_fun_return (res1:((A)stack_result)option)` ASSUME_TAC THENL
         [ASM_CASES_TAC `OPTION_MAP compile_result (r':((A)wl_result)option) = res1` THENL
          [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC W2SP3AUX_bad_fun_return THEN
           ASM_REWRITE_TAC[];
           FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
             w2sp3aux_has_const "stackSem_Halt" (concl th))) THEN
           ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[stack_bad_fun_return_def]];
          ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN SIMP[] THEN
         FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
           w2sp3aux_has_const "stackSem_Halt" (concl th))) THEN
         REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; w2sp3aux_wl_accfupds] THEN
         UNDISCH_TAC `~wl_bad_fun_return (r':((A)wl_result)option)` THEN
         MP_TAC(ISPEC `r':((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
         ASM_REWRITE_TAC[wl_bad_fun_return_def] THEN CASE_REWRITE_TAC[] THEN
         MP_TAC(ISPEC `x:(A)wl_result` (cases "wl_result")) THEN STRIP_TAC THEN
         ASM_REWRITE_TAC[wl_bad_fun_return_def] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* The conventions at a returning call (used for HOL4 8166) *)
let W2SP3AUX_ret_convs = prove
 (`!k f' (vs:num list) (live:num_set#num_set) (ret_code:(A)wl_prog) l1 l2 dest args
     (h:(num#(A)wl_prog#num#num)option).
     post_alloc_conventions k (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h) /\
     flat_exp_conventions (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h) /\
     max_var (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h) < 2 * f' + 2 * k
     ==> args = list_of_seq (\x. 2 * (x + 1)) (LENGTH args) /\
         vs = list_of_seq (\x. 2 * (x + 1)) (LENGTH vs) /\
         post_alloc_conventions k ret_code /\ flat_exp_conventions ret_code /\
         max_var ret_code < 2 * f' + 2 * k /\
         MAX_LIST vs < 2 * f' + 2 * k /\ MAX_LIST args < 2 * f' + 2 * k /\
         (!x. x IN domain (FST live) ==> EVEN x /\ k <= x DIV 2 /\ x < 2 * f' + 2 * k) /\
         (!x. x IN domain (SND live) ==> EVEN x /\ k <= x DIV 2 /\ x < 2 * f' + 2 * k) /\
         (!v prog l1' l2'. h = SOME (v,prog,l1',l2')
            ==> v = 2 /\ post_alloc_conventions k prog /\ flat_exp_conventions prog /\
                max_var prog < 2 * f' + 2 * k)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` option_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `hh:num#(A)wl_prog#num#num`
    SUBST1_TAC)) THENL
  [ALL_TAC;
   SUBGOAL_THEN `?v prog l1' l2'. hh = (v:num,prog:(A)wl_prog,l1':num,l2':num)`
     (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC]] THEN
  REWRITE_TAC[post_alloc_conventions_def; call_arg_convention_def; max_var_def;
              flat_exp_conventions_def; every_stack_var_def; wl_every_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[every_name_def; cutsets_max_def; option_DISTINCT; option_INJ; PAIR_EQ;
              W2SP3AUX_max3_LT; W2SP3AUX_MAX_LT] THEN
  REWRITE_TAC[GSYM toAList_domain; EVERY_MEM; is_phy_var_def; GSYM EVEN_MOD2] THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN UNDISCH_TAC `x >= 2 * k` THEN
      ARITH_TAC) THEN
  TRY(MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `MAX_LIST (MAP FST (toAList (FST (live:num_set#num_set))))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MAX_LIST_PROPERTY THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `MAX_LIST (MAP FST (toAList (SND (live:num_set#num_set))))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MAX_LIST_PROPERTY THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ALL_TAC);;

(* The stack arguments of a returning call (used for HOL4 8166) *)
let W2SP3AUX_ret_args = prove
 (`!dest (args:num list) (a:((A)word_loc)list) (code:(num#(A)wl_prog)spt) (ssize:num spt)
     args1 (prog:(A)wl_prog) (ss:num option) k f (f':num) (q0:(A)stack_prog) dest' l1 l2.
     wl_find_code dest (CONS (wl_Loc l1 l2) a) code ssize = SOME (args1,prog,ss) /\
     LENGTH a = LENGTH args /\ call_dest dest args (k,f,f') = (q0,dest') /\
     ~bad_dest_args dest args
     ==> isPREFIX args1 (CONS (wl_Loc l1 l2) a) /\
         stack_arg_count dest' (LENGTH args + 1) k = LENGTH args1 - k /\
         LENGTH args1 <= LENGTH args + 1`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `dest:num option` option_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_find_code_def; call_dest_def; PAIR_EQ] THEN
  STRIP_TAC THEN EVERY_CASE_TAC THEN GVS[stack_arg_count_def; IS_PREFIX_REFL; LENGTH;
    bad_dest_args_def; LENGTH_EQ_NIL] THEN
  ASM_SIMP_TAC[IS_PREFIX_BUTLAST; LENGTH_FRONT; NOT_CONS_NIL; LENGTH] THEN
  TRY ARITH_TAC);;

(* The stack bound of a returning call (used for HOL4 8166) *)
let w2sp3aux_h1_tac =
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] evaluate_stack_limit_stack_max) o
      check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_evaluate" (concl th) &&
                       rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
    REWRITE_TAC[wl_set_vars_def; wl_set_var_def; w2sp3aux_wl_accfupds; K_THM] THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const o
      check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_pop_env" (concl th)))) THEN
    ASM_REWRITE_TAC[];;

let W2SP3AUX_ret_limit = prove
 (`!vs live ret_code l1 l2 dest args (h:(num#(A)wl_prog#num#num)option)
     (s:(A,num#C,FFI)wl_state) res s1 xs args1 prog ss envs.
     wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h, s) = (res,s1) /\
     ~(res = SOME wl_Error) /\
     wl_get_vars args s = SOME xs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (vs,live,ret_code,l1,l2)) xs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     cut_envs live (wl_state_locals s) = SOME envs /\
     the (wl_state_stack_limit s + 1)
       (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs h s))) >
       wl_state_stack_limit s
     ==> the (wl_state_stack_limit s1 + 1) (wl_state_stack_max s1) > wl_state_stack_limit s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `the (wl_state_stack_limit (wl_call_env args1 ss
           (wl_push_env envs h (wl_dec_clock (s:(A,num#C,FFI)wl_state)))) + 1)
        (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s)))) >
    wl_state_stack_limit (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s)))`
   ASSUME_TAC THENL
  [UNDISCH_TAC `the (wl_state_stack_limit (s:(A,num#C,FFI)wl_state) + 1)
     (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs h s))) >
     wl_state_stack_limit s` THEN
   REWRITE_TAC[wl_call_env_def; w2sp3aux_wl_accfupds; K_THM; push_env_dec_clock_stack] THEN
   SIMP[wl_dec_clock_def]; ALL_TAC] THEN
  UNDISCH_TAC `wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h,
                            s:(A,num#C,FFI)wl_state) = (res,s1)` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Call"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   UNDISCH_TAC `~(SOME wl_Error = SOME (wl_Error:(A)wl_result))` THEN REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[wl_flush_state_def; w2sp3aux_wl_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (prog:(A)wl_prog,
      wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock (s:(A,num#C,FFI)wl_state))))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:((A)wl_result)option` (X_CHOOSE_THEN `s2:(A,num#C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] evaluate_stack_limit_stack_max) o
    check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_evaluate" (concl th) &&
                     rhs (concl th) = `(r2:((A)wl_result)option,s2:(A,num#C,FFI)wl_state)`)) THEN
  DISCH_TAC THEN
  GVS[option_case_eq; case_eq "wl_result"; COND_CASE_EQ; pair_case_eq] THEN
  w2sp3aux_h1_tac);;

(* A frame that does not fit the stack exceeds the stack limit of the       *)
(* returning call (used for HOL4 8166)                                      *)
let W2SP3AUX_ret_overflow = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t5:(A,C,FFI)stack_state) f' lens envs
      (h:(num#(A)wl_prog#num#num)option) args1 ss fs d.
     word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s)))
       t5 (CONS f' lens) 0 /\
     the fs ss = fs /\
     wl_stack_size (wl_state_stack (wl_push_env envs h s)) =
       OPTION_MAP ((+) d)
         (wl_stack_size (wl_state_stack
            (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s))) /\
     stack_state_stack_space t5 < fs + d
     ==> the (wl_state_stack_limit s + 1)
           (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs h s))) >
         wl_state_stack_limit s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def; stack_size_rel_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_wl_accfupds; K_THM; wl_push_env_const;
                              push_env_stack_max_eq]) THEN
  REWRITE_TAC[wl_call_env_def; w2sp3aux_wl_accfupds; K_THM; wl_push_env_const] THEN
  REWRITE_TAC[push_env_stack_max_eq] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `wl_state_stack_max (s:(A,num#C,FFI)wl_state)` THEN
  CASES_ON `wl_stack_size (wl_state_stack (wl_push_env envs
     (NONE:(num#(A)wl_prog#num#num)option) (s:(A,num#C,FFI)wl_state)))` THEN
  CASES_ON `ss:num option` THEN
  ASM_REWRITE_TAC[OPTION_MAP2_THM; OPTION_MAP_DEF; the_def; option_INJ; option_DISTINCT] THEN
  TRY ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `MAX a a'` o check (fun th -> is_forall (concl th) &&
    w2sp3aux_has_const "IS_SOME" (concl th))) THEN
  ASM_REWRITE_TAC[OPTION_MAP2_THM; option_INJ; IS_SOME_DEF; SUB_0; UNWIND_THM1] THEN
  UNDISCH_TAC `the fs (SOME (a'':num)) = fs` THEN REWRITE_TAC[the_def] THEN
  DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) < fs + d` THEN
  UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + 0 <=
               LENGTH (stack_state_stack t5)` THEN
  UNDISCH_TAC `a' = LENGTH (stack_state_stack (t5:(A,C,FFI)stack_state)) -
                    stack_state_stack_space t5` THEN
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

let W2SP3AUX_OPTION_MAP_ADD0 = prove
 (`!x. OPTION_MAP ((+) 0) x = x`,
  GEN_TAC THEN CASES_ON `x:num option` THEN REWRITE_TAC[OPTION_MAP_DEF; ADD_CLAUSES]);;

(* The callee of a returning call is found after the frame set-up (used for *)
(* HOL4 8166)                                                               *)
let W2SP3AUX_ret_find_code = prove
 (`!dest args k f f' (q0:(A)stack_prog) dest' (regs4:(num,(A)word_loc)fmap)
     (code4:((A)stack_prog)spt) regs7 code7 stack_prog.
     call_dest dest args (k,f,f') = (q0,dest') /\
     args = list_of_seq (\x. 2 * (x + 1)) (LENGTH args) /\
     stack_find_code dest' regs4 code4 = SOME stack_prog /\
     subspt code4 code7 /\
     (!i. ~(i = k) ==> FLOOKUP regs7 i = FLOOKUP regs4 i)
     ==> stack_find_code dest' (regs7 \\ 0) code7 = SOME stack_prog`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `dest:num option` option_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[call_dest_def] THENL
  [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   UNDISCH_TAC `stack_find_code (INL (x:num):num+num) (regs4:(num,(A)word_loc)fmap)
                  (code4:((A)stack_prog)spt) = SOME stack_prog` THEN
   REWRITE_TAC[stack_find_code_def] THEN ASM_MESON_TAC[subspt_lookup];
   ALL_TAC] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   UNDISCH_TAC `stack_find_code (INL raise_stub_location:num+num)
                  (regs4:(num,(A)word_loc)fmap) (code4:((A)stack_prog)spt) = SOME stack_prog` THEN
   REWRITE_TAC[stack_find_code_def] THEN ASM_MESON_TAC[subspt_lookup];
   ALL_TAC] THEN
  REWRITE_TAC[wReg2_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(LAST (args:num list) DIV 2 = 0)` ASSUME_TAC THENL
  [MP_TAC(SPEC `LENGTH (args:num list)` LAST_GENLIST_evens) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o
     check (fun th -> is_eq (concl th) && lhs (concl th) = `args:num list`)) THEN
   REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
   UNDISCH_TAC `~(LAST (args:num list) = 0)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    w2sp3aux_has_const "wStackLoad" (concl th))) THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    w2sp3aux_has_const "stack_find_code" (concl th))) THEN
  ASM_REWRITE_TAC[stack_find_code_def; DOMSUB_FLOOKUP_THM] THEN
  REWRITE_TAC[ARITH_RULE `~(0 = k + 1)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `x < k ==> ~(x = k)`; ARITH_RULE `~(k + 1 = k)`] THEN
  W(fun (asl,w) -> CASES_ON (find_term (fun t -> is_comb t && is_comb (rator t) &&
     rand (rator t) = `regs4:(num,(A)word_loc)fmap`) w)) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[subspt_lookup]);;

(* The arguments that the caller moves for a returning call are the callee's *)
(* frame slots (used for HOL4 8166)                                         *)
let W2SP3AUX_ret_frame_index = prove
 (`!(st:A list) st7 sp f fs sac j v.
     (!x. x < sac ==> EL (x + f) (DROP (sp - sac) st) = EL x (DROP (sp - sac) st7)) /\
     LENGTH st7 = LENGTH st /\ sac <= sp /\ fs <= sp /\ sp <= LENGTH st /\
     j < sac /\ j < fs /\ j < f /\
     oEL (f - 1 - j) (TAKE f (DROP sp st)) = SOME v
     ==> oEL (fs - 1 - j) (TAKE fs (DROP (sp - fs) st7)) = SOME v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP oEL_TAKE_E) THEN
  ASM_SIMP_TAC[LLOOKUP_TAKE; ARITH_RULE `j < fs ==> fs - 1 - j < fs`] THEN
  REWRITE_TAC[oEL_EQ_EL; LENGTH_DROP] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `f - 1 - j < LENGTH (st:A list) - sp` THEN
   UNDISCH_TAC `LENGTH (st7:A list) = LENGTH (st:A list)` THEN
   UNDISCH_TAC `fs <= sp` THEN UNDISCH_TAC `j < fs` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sac - 1 - j`) THEN
  ASM_SIMP_TAC[ARITH_RULE `j < sac ==> sac - 1 - j < sac`] THEN
  SUBGOAL_THEN `((sac - 1 - j) + f) + (sp - sac) < LENGTH (st:A list) /\
                (sac - 1 - j) + (sp - sac) < LENGTH (st7:A list) /\
                (f - 1 - j) + sp < LENGTH st /\
                (fs - 1 - j) + (sp - fs) < LENGTH st7 /\
                (f - 1 - j) + sp = ((sac - 1 - j) + f) + (sp - sac) /\
                (fs - 1 - j) + (sp - fs) = (sac - 1 - j) + (sp - sac)` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `f - 1 - j < LENGTH (st:A list) - sp` THEN
   UNDISCH_TAC `LENGTH (st7:A list) = LENGTH (st:A list)` THEN
   UNDISCH_TAC `sac <= sp` THEN UNDISCH_TAC `fs <= sp` THEN UNDISCH_TAC `j < sac` THEN
   UNDISCH_TAC `j < fs` THEN UNDISCH_TAC `j < f` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* The state relation at the entry of the callee of a returning call       *)
(* without handler (used for HOL4 8166)                                     *)
let W2SP3AUX_ret_callee_rel = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t5:(A,C,FFI)stack_state) lens
     (args:num list) a args1 envs ss fs svc sac (t7s:((A)word_loc)list) t7r l1 l2.
     word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s)))
       t5 (CONS f' lens) 0 /\
     word_to_stackProof_state_rel ac k f f' s t5 lens 0 /\
     wl_get_vars args s = SOME a /\
     args = list_of_seq (\x. 2 * (x + 1)) (LENGTH args) /\
     isPREFIX args1 (CONS (wl_Loc l1 l2) a) /\
     LENGTH args1 - k = sac /\ sac <= svc /\
     (if svc = 0 then fs = 0 else fs = svc + 1) /\ the fs ss = fs /\
     sac <= f /\ fs <= stack_state_stack_space t5 /\
     LENGTH t7s = LENGTH (stack_state_stack t5) /\
     DROP (stack_state_stack_space t5) t7s = DROP (stack_state_stack_space t5)
       (stack_state_stack t5) /\
     (!x. x < sac
          ==> EL (x + f) (DROP (stack_state_stack_space t5 - sac) (stack_state_stack t5)) =
              EL x (DROP (stack_state_stack_space t5 - sac) t7s)) /\
     (!i. ~(i = k) ==> FLOOKUP t7r i = FLOOKUP (stack_state_regs t5) i) /\
     ~(wl_state_clock s = 0)
     ==> word_to_stackProof_state_rel ac k fs svc
           (wl_call_env args1 ss
              (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) (wl_dec_clock s)))
           (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
             (stack_state_stack_fupd (K t7s)
               (stack_state_stack_space_fupd (K (stack_state_stack_space t5 - fs))
                 (stack_state_clock_fupd (K (stack_state_clock t5 - 1)) t5))))
           (CONS f' lens) 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) (s:(A,num#C,FFI)wl_state))))
       (t5:(A,C,FFI)stack_state) (CONS f' lens) 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const] THEN
    REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM; wl_push_env_const] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_wl_accfupds; K_THM; wl_push_env_const]) THEN
    ASM_REWRITE_TAC[wf_fromList2] THEN
    SUBGOAL_THEN `DROP fs (DROP (stack_state_stack_space (t5:(A,C,FFI)stack_state) - fs + 0) t7s) =
                  DROP 0 (DROP (stack_state_stack_space t5 + 0) (stack_state_stack t5))`
                    SUBST1_TAC THENL
    [REWRITE_TAC[DROP_DROP_T; ADD_CLAUSES; DROP_0] THEN
     SUBGOAL_THEN `fs + stack_state_stack_space (t5:(A,C,FFI)stack_state) - fs =
       stack_state_stack_space t5`
       SUBST1_TAC THENL
     [UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)`
       THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + 0 <= LENGTH
    (stack_state_stack t5)` THEN
   UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)` THEN ARITH_TAC;
   UNDISCH_TAC `stack_size_rel 0 (SOME 0) (wl_state_stack_limit (s:(A,num#C,FFI)wl_state))
      (wl_state_stack_max (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s))
      (wl_state_stack (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s))
      (stack_state_stack (t5:(A,C,FFI)stack_state)) (stack_state_stack_space t5) 0` THEN
    REWRITE_TAC[stack_size_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `sm:num` THEN REWRITE_TAC[OPTION_MAP2_SOME] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x1:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "IS_SOME" (concl th))) THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; SUB_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
    SUBGOAL_THEN `(LENGTH (stack_state_stack (t5:(A,C,FFI)stack_state)) - (stack_state_stack_space
      t5 - fs)) - fs =
                  LENGTH (stack_state_stack t5) - stack_state_stack_space t5` SUBST1_TAC THENL
    [UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + 0 <= LENGTH
      (stack_state_stack t5)` THEN
     UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)`
       THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `SOME (x1':num) = SOME ss'` THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH (stack_state_stack (t5:(A,C,FFI)stack_state)) - stack_state_stack_space
      t5 <= x1` THEN
    REWRITE_TAC[MAX] THEN ARITH_TAC;
   SUBGOAL_THEN `!n v. lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME v
       ==> EVEN n /\
           (if n DIV 2 < k then FLOOKUP (stack_state_regs (t5:(A,C,FFI)stack_state)) (n
             DIV 2) = SOME v
            else oEL (f - 1 - (n DIV 2 - k)) (TAKE f (DROP (stack_state_stack_space t5 + 0)
              (stack_state_stack t5))) =
                 SOME v /\ n DIV 2 < k + f')` ASSUME_TAC THENL
    [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
      (t5:(A,C,FFI)stack_state) lens 0` THEN
     REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `EVEN n /\ n DIV 2 < LENGTH (args1:((A)word_loc)list) /\ v = EL (n DIV 2) args1`
      STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `lookup n (fromList2 (args1:((A)word_loc)list)) = SOME (v:(A)word_loc)` THEN
     REWRITE_TAC[lookup_fromList2; lookup_fromList] THEN COND_CASES_TAC
       THEN REWRITE_TAC[option_DISTINCT] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]
       THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lookup n (fromList2 (CONS (wl_Loc l1 l2) (a:((A)word_loc)list))) = SOME
      (v:(A)word_loc)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC lookup_fromList2_prefix THEN EXISTS_TAC `args1:((A)word_loc)list` THEN
     ASM_REWRITE_TAC[IS_PREFIX_DEF]; ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
    [UNDISCH_TAC `lookup n (fromList2 (CONS (wl_Loc l1 l2) (a:((A)word_loc)list))) = SOME
      (v:(A)word_loc)` THEN
     ASM_REWRITE_TAC[lookup_fromList2; lookup_fromList; EVEN; LENGTH; ARITH_RULE `0 DIV 2 = 0`;
                     LT_0; EL; HD; option_INJ] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     SUBGOAL_THEN `0 < k` (fun th -> REWRITE_TAC[th; FLOOKUP_UPDATE]) THEN
     UNDISCH_TAC `4 < k` THEN ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME (v:(A)word_loc)`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`args:num list`; `s:(A,num#C,FFI)wl_state`; `a:((A)word_loc)list`; `n:num`;
                    `l1:num`; `l2:num`; `v:(A)word_loc`] get_vars_fromList2_eq_cons) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o
       check (fun th -> is_eq (concl th) && lhs (concl th) = `args:num list`)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th -> is_forall
      (concl th) &&
      w2sp3aux_has_const "oEL" (concl th) && w2sp3aux_has_const "wl_state_locals" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n DIV 2 = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `EVEN n` THEN UNDISCH_TAC `~(n = 0)` THEN REWRITE_TAC[EVEN_EXISTS] THEN
     STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
     UNDISCH_TAC `~(n = 0)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
     SUBGOAL_THEN `~(0 = n DIV 2) /\ ~(n DIV 2 = k)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(n DIV 2 = 0)` THEN UNDISCH_TAC `n DIV 2 < k` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[];
    STRIP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
      check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
                       can (find_term ((=) `f':num`)) (concl th))) THEN
    SUBGOAL_THEN `n DIV 2 - k < sac /\ n DIV 2 - k < fs /\ n DIV 2 - k < f /\ n DIV 2 < k + svc /\
                  sac <= stack_state_stack_space (t5:(A,C,FFI)stack_state)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `n DIV 2 < LENGTH (args1:((A)word_loc)list)` THEN
     UNDISCH_TAC `~(n DIV 2 < k)` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN
     UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
     UNDISCH_TAC `sac <= svc` THEN UNDISCH_TAC `if svc = 0 then fs = 0 else fs = svc + 1` THEN
     UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)` THEN
     UNDISCH_TAC `if f' = 0 then f = 0 else f = f' + 1` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC W2SP3AUX_ret_frame_index THEN
    MAP_EVERY EXISTS_TAC [`stack_state_stack (t5:(A,C,FFI)stack_state)`; `f:num`; `sac:num`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + f <= LENGTH
      (stack_state_stack t5)` THEN
     ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "oEL" (concl th) &&
       w2sp3aux_has_const "TAKE" (concl th) && not (is_imp (concl th)))) THEN
     REWRITE_TAC[ADD_CLAUSES]]]]);;

(* The word state after the callee of a returning call only grows its io  *)
(* events and keeps the stack bound (used for HOL4 8166)                    *)
let W2SP3AUX_ret_cont_mono = prove
 (`!vs live ret_code l1 l2 dest args (h:(num#(A)wl_prog#num#num)option)
     (s:(A,num#C,FFI)wl_state) res s1 xs args1 prog ss envs r2 s2.
     wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h, s) = (res,s1) /\
     ~(res = SOME wl_Error) /\
     wl_get_vars args s = SOME xs /\ ~bad_dest_args dest args /\
     wl_find_code dest (add_ret_loc (SOME (vs,live,ret_code,l1,l2)) xs) (wl_state_code s)
       (wl_state_stack_size s) = SOME (args1,prog,ss) /\
     cut_envs live (wl_state_locals s) = SOME envs /\ ~(wl_state_clock s = 0) /\
     wl_evaluate (prog,wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s))) = (r2,s2)
     ==> ffi_state_io_events (wl_state_ffi s2) <<= ffi_state_io_events (wl_state_ffi s1) /\
         (the (wl_state_stack_limit s2 + 1) (wl_state_stack_max s2) > wl_state_stack_limit s2
          ==> the (wl_state_stack_limit s1 + 1) (wl_state_stack_max s1) > wl_state_stack_limit s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args h,
                            s:(A,num#C,FFI)wl_state) = (res,s1)` THEN
  REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Call"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   UNDISCH_TAC `~(SOME wl_Error = SOME (wl_Error:(A)wl_result))` THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  GVS[option_case_eq; case_eq "wl_result"; COND_CASE_EQ; pair_case_eq; IS_PREFIX_REFL] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const o
    check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_pop_env" (concl th)))) THEN
  (CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o MATCH_MP wl_evaluate_io_events_mono o
     check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_evaluate" (concl th) &&
                      rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)`)) THEN
   ASM_REWRITE_TAC[wl_set_vars_def; wl_set_var_def; w2sp3aux_wl_accfupds; K_THM];
   DISCH_TAC THEN w2sp3aux_h1_tac]));;

(* An exception out of a callee without handler frame comes from below the  *)
(* frame of the call (used for HOL4 8166)                                   *)
let W2SP3AUX_ret_exc_depth = prove
 (`!prog (s:(A,num#C,FFI)wl_state) envs args1 ss x y s2.
     wl_evaluate (prog, wl_call_env args1 ss
        (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) (wl_dec_clock s))) =
       (SOME (wl_Exception x y), s2)
     ==> wl_state_handler s + 1 <= LENGTH (wl_state_stack s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
       (wl_dec_clock (s:(A,num#C,FFI)wl_state)))`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const; w2sp3aux_wl_accfupds;
              K_THM; wl_push_env_const] THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,num#C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `pp:num->num->num`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE_def; w2sp3aux_wl_accfupds; K_THM; LENGTH] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `wl_state_handler (s:(A,num#C,FFI)wl_state) + 1 = SUC (LENGTH (wl_state_stack s))`
  THENL
  [UNDISCH_TAC `LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state) + 1)
      (CONS (StackFrame (wl_state_locals_size s)
         (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))) ll NONE)
        (wl_state_stack s)) = CONS (StackFrame m e0 e (SOME n)) ls` THEN
   ASM_SIMP_TAC[LASTN_CONS_ID] THEN
   REWRITE_TAC[CONS_11; injectivity "stack_frame"; option_DISTINCT];
   UNDISCH_TAC `wl_state_handler (s:(A,num#C,FFI)wl_state) < SUC (LENGTH (wl_state_stack s))` THEN
   UNDISCH_TAC `~(wl_state_handler (s:(A,num#C,FFI)wl_state) + 1 =
                  SUC (LENGTH (wl_state_stack s)))` THEN
   ARITH_TAC]);;

(* A local restored at the return from a call is in the caller's frame on  *)
(* the stack (used for HOL4 8166)                                           *)
let W2SP3AUX_frame_lookup = prove
 (`!k (bs:(A word)list) m l0 l (xs:((A)stack_frame)list) (sh:((B)word_loc)option)
   (st:((A)word_loc)list)
      len f' lens n v whandler.
     word_to_stackProof_stack_rel k whandler (CONS (StackFrame m l0 l NONE) xs) sh st len bs
       (CONS f' lens) /\
     lookup n (union (fromAList l) (fromAList l0)) = SOME v /\ k <= n DIV 2 /\ n DIV 2 < k + f'
     ==> oEL (f' - (n DIV 2 - k)) st = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `abs_stack (bs:(A word)list) (CONS (StackFrame m l0 l NONE)
      (xs:((A)stack_frame)list)) st
                   (CONS f' lens) = SOME stack` THEN
    MP_TAC(ISPEC `st:((A)word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `w:(A)word_loc` (X_CHOOSE_THEN
      `rest:((A)word_loc)list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN
    CASES_ON `full_read_bitmap (bs:(A word)list) (w:(A)word_loc)`
      THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
      "abs_stack" with _ -> false) w)) THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `stack_rel_aux k len (CONS (StackFrame m l0 l NONE) (xs:((A)stack_frame)list))
      (CONS (NONE,a,TAKE f' (rest:((A)word_loc)list)) a')` THEN
    REWRITE_TAC[stack_rel_aux_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `LENGTH (TAKE f' (rest:((A)word_loc)list)) = f'` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN UNDISCH_TAC `~(LENGTH (rest:((A)word_loc)list) < f')`
      THEN ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `f' - (n DIV 2 - k) = SUC (f' - 1 - (n DIV 2 - k))` SUBST1_TAC THENL
    [UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[oEL_DEF; NOT_SUC; SUC_SUB1] THEN
    SUBGOAL_THEN `oEL (f' - 1 - (n DIV 2 - k)) (rest:((A)word_loc)list) =
                  oEL (f' - 1 - (n DIV 2 - k)) (TAKE f' rest)` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LLOOKUP_TAKE THEN
     UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `lookup n (union (fromAList l) (fromAList (l0:(num#(A)word_loc)list))) = SOME
      (v:(A)word_loc)` THEN
    REWRITE_TAC[lookup_union; lookup_fromAList] THEN
    CASES_ON `ALOOKUP (l:(num#(A)word_loc)list) n` THEN CASE_REWRITE_TAC[option_INJ] THENL
    [DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th -> is_forall
       (concl th) &&
       w2sp3aux_has_const "index_list" (concl th))) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     MP_TAC(ISPECL [`TAKE f' (rest:((A)word_loc)list)`; `n DIV 2`; `k:num`] ALOOKUP_index_list) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `f' - 1 - (n DIV 2 - k) = (f' + k) - (n DIV 2 + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
     DISCH_THEN SUBST_ALL_TAC THEN
     SUBGOAL_THEN `MEM (n DIV 2,v:(A)word_loc) (index_list (TAKE f' (rest:((A)word_loc)list)) k)`
       MP_TAC THENL
     [MATCH_MP_TAC filter_bitmap_MEM THEN
      MAP_EVERY EXISTS_TAC [`a:bool list`; `MAP_FST adjust_names (l:(num#(A)word_loc)list)`] THEN
      ASM_REWRITE_TAC[MAP_FST_def; MEM_MAP; EXISTS_PAIR_THM] THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `v:(A)word_loc`] THEN
      REWRITE_TAC[adjust_names_def] THEN MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     DISCH_THEN(MP_TAC o MATCH_MP MEM_index_list_EL) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN REWRITE_TAC[oEL_EQ_EL] THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL [UNDISCH_TAC `n DIV 2 < k + f'` THEN UNDISCH_TAC `k <= n DIV 2`
       THEN ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     UNDISCH_TAC `n DIV 2 < k + f'` THEN UNDISCH_TAC `k <= n DIV 2` THEN ARITH_TAC]);;

(* Stack slots after copy_ret_aux (used for HOL4 8166) *)
let W2SP3AUX_ret_val_index = prove
 (`!(st:A list) st2 sp f n0 x j v.
     oEL x (DROP sp st) = SOME v /\
     (!i. i < n0 ==> EL (i + f) (DROP sp st2) = EL i (DROP sp st)) /\
     LENGTH st2 = LENGTH st /\ sp + n0 + f <= LENGTH st /\ x < n0 /\ j < f /\ n0 + j = x + f
     ==> oEL j (TAKE f (DROP (sp + n0) st2)) = SOME v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LLOOKUP_TAKE; oEL_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `oEL x (DROP sp (st:A list)) = SOME (v:A)` THEN
  REWRITE_TAC[oEL_DROP; oEL_EQ_EL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x + f) + sp < LENGTH (st2:A list) /\ x + sp < LENGTH (st:A list) /\
                (sp + n0) + j = sp + x + f` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `sp + n0 + f <= LENGTH (st:A list)` THEN UNDISCH_TAC
    `LENGTH (st2:A list) = LENGTH (st:A list)` THEN
   UNDISCH_TAC `x < n0` THEN UNDISCH_TAC `n0 + j = x + f` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [UNDISCH_TAC `sp + n0 + f <= LENGTH (st:A list)` THEN UNDISCH_TAC `x < n0` THEN ARITH_TAC;
   SUBGOAL_THEN `sp + x + f = (x + f) + sp` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let W2SP3AUX_ret_keep_index = prove
 (`!(st:A list) st2 p f d j v.
     oEL j (DROP p st) = SOME v /\
     (!i. i < d ==> EL i (DROP p st2) = EL i (DROP p st)) /\
     LENGTH st2 = LENGTH st /\ j < d /\ j < f
     ==> oEL j (TAKE f (DROP p st2)) = SOME v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LLOOKUP_TAKE] THEN
  UNDISCH_TAC `oEL j (DROP p (st:A list)) = SOME (v:A)` THEN
  REWRITE_TAC[oEL_EQ_EL; LENGTH_DROP] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

(* The state relation after the return of a call without handler (used    *)
(* for HOL4 8166)                                                           *)
let W2SP3AUX_ret_state_rel = prove
 (`!ac k f f' (s2:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state) lens
      (ys:((A)word_loc)list) vs x m l0 l xs t2s t2r.
     word_to_stackProof_state_rel ac k 0 0 s2 t1 (CONS f' lens) (LENGTH ys - (k - 1)) /\
     (!i. i < LENGTH ys
          ==> (if i + 1 < k then FLOOKUP (stack_state_regs t1) (i + 1) = SOME (EL i ys)
               else oEL (LENGTH ys - (i + 1))
                      (DROP (stack_state_stack_space t1) (stack_state_stack t1)) = SOME
                        (EL i ys))) /\
     wl_pop_env s2 = SOME x /\
     wl_state_stack s2 = CONS (StackFrame m l0 l NONE) xs /\
     vs = list_of_seq (\x. 2 * (x + 1)) (LENGTH vs) /\ LENGTH ys = LENGTH vs /\
     MAX_LIST vs < 2 * f' + 2 * k /\ f' + 1 = f /\ ~(f' = 0) /\
     (!n. n IN domain (wl_state_locals x) ==> EVEN n /\ 2 * k <= n /\ n < 2 * f' + 2 * k) /\
     LENGTH t2s = LENGTH (stack_state_stack t1) /\
     DROP (f + ((LENGTH vs + 1) - k) + stack_state_stack_space t1) t2s =
       DROP (f + ((LENGTH vs + 1) - k) + stack_state_stack_space t1) (stack_state_stack t1) /\
     (!i. i < f - ((LENGTH vs + 1) - k)
          ==> EL i (DROP (((LENGTH vs + 1) - k) + stack_state_stack_space t1) t2s) =
              EL i (DROP (((LENGTH vs + 1) - k) + stack_state_stack_space t1)
                (stack_state_stack t1))) /\
     (!i. i < (LENGTH vs + 1) - k
          ==> EL (i + f) (DROP (stack_state_stack_space t1) t2s) =
              EL i (DROP (stack_state_stack_space t1) (stack_state_stack t1))) /\
     (!i. ~(i = k) ==> FLOOKUP t2r i = FLOOKUP (stack_state_regs t1) i)
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_vars vs ys x)
           (stack_state_regs_fupd (K t2r)
             (stack_state_stack_fupd (K t2s)
               (stack_state_stack_space_fupd
                  (K (stack_state_stack_space t1 + ((LENGTH vs + 1) - k))) t1)))
           lens 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
    UNDISCH_TAC `wl_pop_env (s2:(A,num#C,FFI)wl_state) = SOME x` THEN
    ASM_REWRITE_TAC[wl_pop_env_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_wl_accfupds; K_THM]) THEN
    SUBGOAL_THEN `LENGTH (ys:((A)word_loc)list) - (k - 1) = (LENGTH (vs:num list) + 1) - k`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [UNDISCH_TAC `LENGTH (ys:((A)word_loc)list) = LENGTH (vs:num list)` THEN
     UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `n0 = (LENGTH (vs:num list) + 1) - k` THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0 (s2:(A,num#C,FFI)wl_state)
      (t1:(A,C,FFI)stack_state)
                   (CONS f' lens) n0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[wl_set_vars_def; w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
                    `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
                      `xs:((A)stack_frame)list`;
                    `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
                    `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
                      (stack_state_stack t1))`;
                    `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                    `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
                   stack_rel_cons_LEN_NONE) THEN
     ANTS_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel"
       o concl)) THEN
                     ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[DROP_0; LENGTH_DROP] THEN UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
     MATCH_MP_TAC wf_alist_insert THEN MATCH_MP_TAC wf_union THEN REWRITE_TAC[wf_fromAList];
     
   SUBGOAL_THEN `the (f' + 1) (m:num option) = f' + 1` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `NONE:(num#num#num)option`;
       `xs:((A)stack_frame)list`; `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
       `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
       stack_rel_cons_locals_size) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `stack_size_rel 0 (wl_state_locals_size (s2:(A,num#C,FFI)wl_state))
      (wl_state_stack_limit s2)
      (wl_state_stack_max s2) (wl_state_stack s2) (stack_state_stack (t1:(A,C,FFI)stack_state))
      (stack_state_stack_space t1) n0` THEN
    ASM_REWRITE_TAC[stack_size_rel_def; stack_size_eq; OPTION_MAP2_SOME] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
    [DISCH_TAC THEN UNDISCH_TAC `the (f' + 1) (m:num option) = f' + 1` THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    X_GEN_TAC `sm:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sm:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "IS_SOME" (concl th))) THEN
    ASM_REWRITE_TAC[SUB_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ss0:num` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
    UNDISCH_TAC `the (f' + 1) (m:num option) = f' + 1` THEN ASM_REWRITE_TAC[the_def;
      IS_SOME_DEF] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
     UNDISCH_TAC `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) - stack_state_stack_space t1
       - n0 <= sm` THEN
    UNDISCH_TAC `ss0 = x1 + x2:num` THEN
    UNDISCH_TAC `ss0 = LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) -
      stack_state_stack_space t1 - n0` THEN
    UNDISCH_TAC `x1:num = f` THEN ARITH_TAC;
   SUBGOAL_THEN `DROP f (DROP ((stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 0)
     (t2s:((A)word_loc)list)) =
                  DROP (f' + 1) (DROP 0 (DROP (stack_state_stack_space t1 + n0)
                    (stack_state_stack t1)))`
      SUBST1_TAC THENL
    [REWRITE_TAC[DROP_DROP_T; ADD_CLAUSES; DROP_0] THEN
     SUBGOAL_THEN `f + stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0 = f + n0 +
       stack_state_stack_space t1 /\
                   (f' + 1) + stack_state_stack_space t1 + n0 = f + n0 + stack_state_stack_space t1`
       (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `xs:((A)stack_frame)list`;
       `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
       `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
       stack_rel_DROP_NONE) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
    ASM_REWRITE_TAC[];
   SUBGOAL_THEN `!i. i < LENGTH (vs:num list) ==> EL i vs = 2 * (i + 1)` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o
       check (fun th -> is_eq (concl th) && lhs (concl th) = `vs:num list`)) THEN
     ASM_SIMP_TAC[EL_LIST_OF_SEQ]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
    CASES_ON `ALOOKUP (ZIP (vs:num list) (ys:((A)word_loc)list)) n`
      THEN CASE_REWRITE_TAC[option_INJ] THENL
    [DISCH_TAC THEN
    SUBGOAL_THEN `EVEN n /\ 2 * k <= n /\ n < 2 * f' + 2 * k` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[domain_lookup] THEN
     EXISTS_TAC `v:(A)word_loc` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(MEM n (vs:num list))` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`vs:num list`; `ys:((A)word_loc)list`; `n:num`] ALOOKUP_ZIP_FAIL) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (vs:num list) + 1 <= n DIV 2` ASSUME_TAC THENL
    [UNDISCH_TAC `EVEN n` THEN REWRITE_TAC[EVEN_EXISTS]
      THEN DISCH_THEN(X_CHOOSE_THEN `mm:num` SUBST_ALL_TAC) THEN
     SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
     REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
     UNDISCH_TAC `~(MEM (2 * mm) (vs:num list))` THEN REWRITE_TAC[] THEN
     SUBGOAL_THEN `2 * mm = EL (mm - 1) (vs:num list)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `mm - 1` o check (fun th -> is_forall (concl th) &&
        w2sp3aux_has_const "EL" (concl th) && not (w2sp3aux_has_const "DROP" (concl th)))) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `mm < LENGTH (vs:num list) + 1` THEN UNDISCH_TAC `2 * k <= 2 * mm` THEN
       UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `2 * k <= 2 * mm` THEN UNDISCH_TAC `4 < k`
        THEN ARITH_TAC;
      MATCH_MP_TAC MEM_EL THEN
      UNDISCH_TAC `mm < LENGTH (vs:num list) + 1` THEN UNDISCH_TAC `2 * k <= 2 * mm` THEN
      UNDISCH_TAC `4 < k` THEN ARITH_TAC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n DIV 2 < k) /\ n DIV 2 < k + f' /\ k <= n DIV 2` STRIP_ASSUME_TAC THENL
    [SIMP_TAC[RDIV_LT_EQ; LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN
     UNDISCH_TAC `2 * k <= n` THEN UNDISCH_TAC `n < 2 * f' + 2 * k` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`k:num`; `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `m:num option`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `xs:((A)stack_frame)list`;
       `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`; `f':num`; `lens:num list`; `n:num`;
       `v:(A)word_loc`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`] W2SP3AUX_frame_lookup) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DROP_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`stack_state_stack (t1:(A,C,FFI)stack_state)`; `t2s:((A)word_loc)list`;
       `n0 + stack_state_stack_space (t1:(A,C,FFI)stack_state)`; `f:num`; `f - n0`;
       `f - 1 - (n DIV 2 - k)`; `v:(A)word_loc`] W2SP3AUX_ret_keep_index) THEN
    SUBGOAL_THEN `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 0 =
                  n0 + stack_state_stack_space t1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
    [UNDISCH_TAC `oEL (f' - (n DIV 2 - k)) (DROP (stack_state_stack_space
      (t1:(A,C,FFI)stack_state) + n0)
                   (stack_state_stack t1)) = SOME (v:(A)word_loc)` THEN
     SUBGOAL_THEN `f' - (n DIV 2 - k) = f - 1 - (n DIV 2 - k) /\
                   stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0 = n0 +
                     stack_state_stack_space t1`
       (fun th -> REWRITE_TAC[th]) THEN
     UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
     UNDISCH_TAC `LENGTH (vs:num list) + 1 <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN
     UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `(LENGTH (vs:num list) + 1) - k = n0` THEN
     UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
     UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC];
     DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM o check (fun th -> is_eq (concl th) &&
       w2sp3aux_has_const "ZIP" (concl th))) THEN
     ASM_SIMP_TAC[MEM_ZIP] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
     ASM_SIMP_TAC[PAIR_EQ] THEN
     UNDISCH_TAC `(n:num,v:(A)word_loc) = EL i vs,EL i ys` THEN ASM_SIMP_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
     REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * (i + 1)) DIV 2 = i + 1`] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "FLOOKUP" (concl th) && w2sp3aux_has_const "oEL" (concl th) &&
      can (find_term ((=) `ys:((A)word_loc)list`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THENL
    [ASM_SIMP_TAC[ARITH_RULE `x < k ==> ~(x = k)`];
     SUBGOAL_THEN `i + 1 < k + f'` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`vs:num list`; `EL i (vs:num list)`] MAX_LIST_PROPERTY) THEN
      ASM_SIMP_TAC[MEM_EL] THEN
      UNDISCH_TAC `MAX_LIST (vs:num list) < 2 * f' + 2 * k` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f <= LENGTH
       (stack_state_stack t1)`
       ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
                    `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
                      `xs:((A)stack_frame)list`;
                    `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
                    `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
                      (stack_state_stack t1))`;
                    `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                    `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
                   stack_rel_cons_LEN_NONE) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const
        "word_to_stackProof_stack_rel" o concl)) THEN
                      ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DROP_0; LENGTH_DROP] THEN UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     (REWRITE_TAC[ADD_CLAUSES] THEN
      MP_TAC(ISPECL [`stack_state_stack (t1:(A,C,FFI)stack_state)`; `t2s:((A)word_loc)list`;
        `stack_state_stack_space (t1:(A,C,FFI)stack_state)`; `f:num`; `n0:num`;
        `LENGTH (vs:num list) - (i + 1)`; `f - 1 - ((i + 1) - k)`; `EL i (ys:((A)word_loc)list)`]
        W2SP3AUX_ret_val_index) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f <= LENGTH
        (stack_state_stack t1)` THEN
      UNDISCH_TAC `i + 1 < k + f'` THEN UNDISCH_TAC `~(i + 1 < k)`
        THEN UNDISCH_TAC `i < LENGTH (vs:num list)` THEN
      UNDISCH_TAC `(LENGTH (vs:num list) + 1) - k = n0` THEN UNDISCH_TAC `f' + 1 = f`
        THEN ARITH_TAC)]]]);;

(* After a normal return, the callee leaves the frame of the call on top   *)
(* (used for HOL4 8166)                                                     *)
let W2SP3AUX_ret_swap = prove
 (`!prog (s:(A,num#C,FFI)wl_state) envs args1 ss x0 ys s2.
     wl_evaluate (prog, wl_call_env args1 ss
        (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) (wl_dec_clock s))) =
       (SOME (wl_Result x0 ys), s2)
     ==> wl_state_handler s2 = wl_state_handler s /\
         ?m l0 l xs. wl_state_stack s2 = CONS (StackFrame m l0 l NONE) xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
       (wl_dec_clock (s:(A,num#C,FFI)wl_state)))`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const; w2sp3aux_wl_accfupds;
              K_THM; wl_push_env_const] THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,num#C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `pp:num->num->num`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE_def; w2sp3aux_wl_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN
  UNDISCH_TAC `s_key_eq (CONS (StackFrame (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
      (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))) ll NONE) (wl_state_stack s))
      (wl_state_stack (s2:(A,num#C,FFI)wl_state))` THEN
  MP_TAC(ISPEC `wl_state_stack (s2:(A,num#C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `fr:(A)stack_frame`
    (X_CHOOSE_THEN `rest:((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[s_key_eq_def] THEN
  STRUCT_CASES_TAC(ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_key_eq_def2] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[CONS_11; injectivity "stack_frame"] THEN MESON_TAC[]);;

(* The frame of the call is within the stack at the return (used for HOL4 *)
(* 8166)                                                                    *)
let W2SP3AUX_ret_frame_len = prove
 (`!ac k (s2:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state) f' lens extra m l0 l xs.
     word_to_stackProof_state_rel ac k 0 0 s2 t1 (CONS f' lens) extra /\
     wl_state_stack s2 = CONS (StackFrame m l0 l NONE) xs
     ==> (stack_state_stack_space t1 + extra) + f' + 1 <= LENGTH (stack_state_stack t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
                 `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `xs:((A)stack_frame)list`;
                 `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
                 `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + extra)
                    (stack_state_stack t1))`;
                 `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                 `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
                stack_rel_cons_LEN_NONE) THEN
  ANTS_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DROP_0; LENGTH_DROP] THEN ARITH_TAC);;

(* The domains of the cut environments (used for HOL4 8166) *)
let W2SP3AUX_cut_envs_domain = prove
 (`!names (l:((A)word_loc)spt) envs.
     cut_envs names l = SOME envs
     ==> domain (FST envs) = domain (FST names) /\ domain (SND envs) = domain (SND names)`,
  REWRITE_TAC[cut_envs_def; cut_names_def] THEN REPEAT GEN_TAC THEN
  GVS[COND_CASE_EQ; option_case_eq; pair_case_eq] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
  REWRITE_TAC[FST; SND; domain_inter] THEN ASM SET_TAC[]);;

let w2sp3aux_call_returning_case some =
  let tm = word_to_stackProof_comp_call_case true in
  let ac,body = dest_forall tm in
  let vs,b = strip_forall body in
  let hty = `:(num#(A)wl_prog#num#num)option` in
  let h = find (fun v -> type_of v = hty) vs in
  let ety = hd(snd(dest_type hty)) in
  if some then
    let hh = variant (vs @ frees b) (mk_var("h",ety)) in
    let vs' = map (fun v -> if v = h then hh else v) vs in
    mk_forall(ac, list_mk_forall(vs',
      vsubst [mk_comb(mk_const("SOME",[ety,aty]),hh),h] b))
  else
    mk_forall(ac, list_mk_forall(filter (fun v -> not (v = h)) vs,
      vsubst [mk_const("NONE",[ety,aty]),h] b));;

let w2sp3aux_ret_halt_tac (arith_tac:tactic) : tactic =
     REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
     SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) =
                     SOME (stackSem_Halt (wl_Word (word 2))))` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      MATCH_MP_TAC compile_result_NOT_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[stack_empty_env_def; w2sp3aux_stack_accfupds; K_THM] THEN
     TRY (EXPAND_TAC "t6") THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN CONJ_TAC THENL
     [MP_TAC(MATCH_MP wl_evaluate_io_events_mono (ASSUME
        `wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args NONE,
                      s:(A,num#C,FFI)wl_state) = res,s1`)) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC W2SP3AUX_ret_limit THEN
      MAP_EVERY EXISTS_TAC [`vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`;
        `l1:num`; `l2:num`; `dest:num option`; `args:num list`;
        `NONE:(num#(A)wl_prog#num#num)option`; `s:(A,num#C,FFI)wl_state`;
          `res:((A)wl_result)option`;
        `a:((A)word_loc)list`; `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`;
        `a'':((A)word_loc)spt#((A)word_loc)spt`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC W2SP3AUX_ret_overflow THEN
      MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `t5:(A,C,FFI)stack_state`; `f':num`;
        `lens:num list`; `fs:num`; `0`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; W2SP3AUX_OPTION_MAP_ADD0] THEN arith_tac];;

let w2sp3aux_ret_pass_tac : tactic =
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel"
    (concl th) &&
    can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th) && not (is_forall (concl th)) &&
    w2sp3aux_has_const "push_locals" (concl th))) THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN SIMP_TAC[];;

(* The returning Call case without handler (HOL4 8166-9019) *)
let W2SP3AUX_comp_correct_Call_returning_NONE = prove
 (w2sp3aux_call_returning_case false,
  (GEN_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      LABEL_TAC "IHret" (el 1 cs) THEN LABEL_TAC "IHexc" (el 2 cs) THEN
      LABEL_TAC "IHcall" (el 3 cs)) THEN
    REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `?vs live ret_code l1 l2. x = (vs:num
    list,live:num_set#num_set,ret_code:(A)wl_prog,l1:num,l2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    UNDISCH_TAC `word_to_stack_comp ac F (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args NONE)
      (bs,n) (k,f,f') =
                 (sprog:(A)stack_prog,bs',n')` THEN
    REWRITE_TAC[w2sp3aux_comp_clause "wl_Call"] THEN
    MP_TAC(ISPEC `call_dest dest args (k,f,f'):(A)stack_prog#(num+num)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q0:(A)stack_prog` (X_CHOOSE_THEN `dest':num+num` ASSUME_TAC)) THEN
    MP_TAC(ISPEC `wLive live (bs,n) (k,f,f'):(A)stack_prog#((A word)app_list#num)`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `bsn1:(A word)app_list#num`
      ASSUME_TAC)) THEN
    MP_TAC(ISPEC `word_to_stack_comp ac F ret_code bsn1 (k,f,f'):(A)stack_prog#((A
      word)app_list#num)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q2:(A)stack_prog` (X_CHOOSE_THEN `bsn2:(A word)app_list#num`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `sprog:(A)stack_prog`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
       lhs (concl th) = `bsn2:(A word)app_list#num`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; UNION_SUBSET]) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      w2sp3aux_has_const "wl_Call" (concl th) && w2sp3aux_has_const "wl_evaluate" (concl th))) THEN
    REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Call"] THEN
    CASES_ON `wl_get_vars args (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    W2SP3AUX_ERR_TAC THEN
    ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)`
      THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    W2SP3AUX_ERR_TAC THEN
    CASES_ON `wl_find_code dest (add_ret_loc (SOME (vs,live,ret_code,l1,l2):(num
      list#cutsets#(A)wl_prog#num#num)option)
      (a:((A)word_loc)list)) (wl_state_code (s:(A,num#C,FFI)wl_state)) (wl_state_stack_size s)` THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC THEN
    MP_TAC(ISPEC `a':((A)word_loc)list#(A)wl_prog#num option` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `args1:((A)word_loc)list` (X_CHOOSE_THEN `pss:(A)wl_prog#num option`
      SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `pss:(A)wl_prog#num option` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `prog:(A)wl_prog` (X_CHOOSE_THEN `ss:num option` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN CASE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `domain (FST (live:num_set#num_set)) = {} \/ ~ALL_DISTINCT (vs:num list)` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC THEN
    CASES_ON `cut_envs (live:num_set#num_set) (wl_state_locals (s:(A,num#C,FFI)wl_state))` THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC) THEN
  (MP_TAC(ISPECL [`k:num`; `f':num`; `vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`;
                   `l1:num`; `l2:num`; `dest:num option`; `args:num list`;
                   `NONE:(num#(A)wl_prog#num#num)option`] W2SP3AUX_ret_convs) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
    MP_TAC(ISPECL [`dest:num option`; `args:num list`; `ac:(A)asm_config`; `k:num`;
      `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `q0:(A)stack_prog`;
      `dest':num+num`; `a:((A)word_loc)list`;
      `SOME (vs,live,ret_code,l1,l2):(num list#cutsets#(A)wl_prog#num#num)option`]
      call_dest_lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t4:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o SPECL [`args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`])))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `bsc:(A word)app_list` (X_CHOOSE_THEN `ic:num`
      (X_CHOOSE_THEN `bs2:(A word)app_list` (X_CHOOSE_THEN `i2:num` (X_CHOOSE_THEN `fs:num`
      (X_CHOOSE_THEN `stack_prog:(A)stack_prog` STRIP_ASSUME_TAC))))))) THEN
  (SUBGOAL_THEN `~(f' = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `~(domain (FST (live:num_set#num_set)) = {} \/ ~ALL_DISTINCT (vs:num list))` THEN
     REWRITE_TAC[DE_MORGAN_THM; GSYM MEMBER_NOT_EMPTY] THEN
     DISCH_THEN(X_CHOOSE_TAC `y:num` o CONJUNCT1) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th))) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `f' + 1 = f /\ 1 <= f` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `if f' = 0 then f = 0 else f = f' + 1` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
     ALL_TAC] THEN
    MP_TAC(ISPEC `bsn1:(A word)app_list#num` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `bs1:(A word)app_list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
      check (w2sp3aux_is_seval_of `q0:(A)stack_prog`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP comp_IMP_isPREFIX o
      check (fun th -> is_eq (concl th) && w2sp3aux_has_const "word_to_stack_comp" (concl th))) THEN
    REWRITE_TAC[FST] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`live:num_set#num_set`; `bs:(A word)app_list`; `n:num`; `k:num`; `f:num`;
                   `f':num`; `q1:(A)stack_prog`; `bs1:(A word)app_list`; `n1:num`;
                   `ac:(A)asm_config`; `s:(A,num#C,FFI)wl_state`; `t4:(A,C,FFI)stack_state`;
                   `lens:num list`; `a'':((A)word_loc)spt#((A)word_loc)spt`] evaluate_wLive) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      X_GEN_TAC `y:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `SND (live:num_set#num_set)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `LENGTH (stack_state_bitmaps
        (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `append (bs':(A word)app_list)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_TRANS THEN
      EXISTS_TAC `DROP (n - LENGTH (append (bs:(A word)app_list))) (stack_state_bitmaps
        (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t5:(A,C,FFI)stack_state` STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `!ck (X:(A)stack_prog). stack_evaluate (stack_Seq q0 (stack_Seq q1 X),
         stack_state_clock_fupd (K (stack_state_clock t + ck)) (t:(A,C,FFI)stack_state)) =
       stack_evaluate (X, stack_state_clock_fupd (K (stack_state_clock t + ck))
         (t5:(A,C,FFI)stack_state))`
      ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
     FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP evaluate_call_dest_clock th]) o
       check (fun th -> is_eq(concl th) && w2sp3aux_has_const "call_dest" (concl th))) THEN
     ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
     FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP evaluate_wLive_clock th]) o
       check (fun th -> is_eq(concl th) && w2sp3aux_has_const "wLive" (concl th))) THEN
     ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_length_lemma o
      check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_get_vars" (concl th))) THEN
    MP_TAC(ISPECL [`dest:num option`; `args:num list`; `a:((A)word_loc)list`;
      `wl_state_code (s:(A,num#C,FFI)wl_state)`; `wl_state_stack_size (s:(A,num#C,FFI)wl_state)`;
      `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`; `k:num`; `f:num`; `f':num`;
      `q0:(A)stack_prog`; `dest':num+num`; `l1:num`; `l2:num`] W2SP3AUX_ret_args) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_find_code"
       (concl th))) THEN
     REWRITE_TAC[add_ret_loc_def] THEN SIMP_TAC[];
     STRIP_TAC] THEN
    ABBREV_TAC `sac = LENGTH (args1:((A)word_loc)list) - k` THEN
    REWRITE_TAC[StackArgs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
    ONCE_REWRITE_TAC[evaluate_stack_move_seq] THEN
    ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
    REWRITE_TAC[w2sp3aux_seval "StackAlloc"; w2sp3aux_stack_accfupds] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
      check (fun th -> can (find_term ((=) `t5:(A,C,FFI)stack_state`)) (concl th) &&
                       can (find_term ((=) `lens:num list`)) (concl th) &&
                       not (can (find_term ((=) `CONS (f':num) lens`)) (concl th)))) THEN
    ASM_REWRITE_TAC[]) THEN
  (FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP3AUX_compile_prog_unfold o
       check (w2sp3aux_has_const "word_to_stack_compile_prog" o concl)) THEN
    DISCH_THEN(X_CHOOSE_THEN `qc:(A)stack_prog` (X_CHOOSE_THEN `svc:num`
       (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
         STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `sac <= fs /\ sac <= svc` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `MAX ((max_var (prog:(A)wl_prog) DIV 2 + 1) - k) (LENGTH (args1:((A)word_loc)list)
      - k) = svc` THEN
     UNDISCH_TAC `(if svc = 0 then 0 else svc + 1) = fs` THEN
     UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
     REWRITE_TAC[MAX] THEN ARITH_TAC; ALL_TAC]) THEN
  (ASM_CASES_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) < sac` THENL
    [DISCH_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[pair_CASE_def; option_DISTINCT] THEN
     REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
     SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) =
                     SOME (stackSem_Halt (wl_Word (word 2))))` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      MATCH_MP_TAC compile_result_NOT_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[stack_empty_env_def; w2sp3aux_stack_accfupds; K_THM] THEN CONJ_TAC THENL
     [MP_TAC(MATCH_MP wl_evaluate_io_events_mono (ASSUME
        `wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args NONE,
                      s:(A,num#C,FFI)wl_state) = res,s1`)) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC W2SP3AUX_ret_limit THEN
      MAP_EVERY EXISTS_TAC [`vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`;
        `l1:num`; `l2:num`; `dest:num option`; `args:num list`;
        `NONE:(num#(A)wl_prog#num#num)option`; `s:(A,num#C,FFI)wl_state`;
          `res:((A)wl_result)option`;
        `a:((A)word_loc)list`; `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`;
        `a'':((A)word_loc)spt#((A)word_loc)spt`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC W2SP3AUX_ret_overflow THEN
      MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `t5:(A,C,FFI)stack_state`; `f':num`;
        `lens:num list`; `fs:num`; `0`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; W2SP3AUX_OPTION_MAP_ADD0] THEN
      UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) < sac` THEN
      UNDISCH_TAC `sac <= fs` THEN ARITH_TAC];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (args:num list) < f' + k` ASSUME_TAC THENL
    [UNDISCH_TAC `MAX_LIST (args:num list) < 2 * f' + 2 * k` THEN
     FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) o
       check (fun th -> is_eq (concl th) && lhs (concl th) = `args:num list`)) THEN
     REWRITE_TAC[MAX_LIST_GENLIST_evens2; LENGTH_LIST_OF_SEQ] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sac <= f /\ sac <= stack_state_stack_space (t:(A,C,FFI)stack_state)`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (args:num list) < f' + k` THEN
      UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) <= LENGTH (args:num list) + 1` THEN
      UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
      UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
      UNDISCH_TAC `~(stack_state_stack_space (t:(A,C,FFI)stack_state) < sac)` THEN ARITH_TAC];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN
    ABBREV_TAC `t6 = stack_state_stack_space_fupd (K (stack_state_stack_space
      (t:(A,C,FFI)stack_state) - sac))
                       (t5:(A,C,FFI)stack_state)` THEN
    SUBGOAL_THEN `!ck. stack_state_stack_space_fupd (K (stack_state_stack_space
      (t:(A,C,FFI)stack_state) - sac))
         (stack_state_clock_fupd (K (stack_state_clock t + ck)) (t5:(A,C,FFI)stack_state)) =
         stack_state_clock_fupd (K (stack_state_clock t + ck)) t6` (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "t6" THEN SIMP[]; ALL_TAC] THEN
    REWRITE_TAC[CONV_RULE (TOP_DEPTH_CONV let_CONV) evaluate_stack_move_clock] THEN
    MP_TAC(ISPECL [`sac:num`; `0`; `t6:(A,C,FFI)stack_state`; `f:num`;
      `k:num`] evaluate_stack_move) THEN
    ANTS_TAC THENL
    [EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + f <= LENGTH
       (stack_state_stack t)` THEN
     UNDISCH_TAC `sac <= stack_state_stack_space (t:(A,C,FFI)stack_state)` THEN
     UNDISCH_TAC `sac <= f` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t7:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t7s:((A)word_loc)list` (X_CHOOSE_THEN `t7r:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
    REWRITE_TAC[w2sp3aux_seval "stack_Skip"; pair_CASE_def]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
      check (w2sp3aux_is_seval_of `q1:(A)stack_prog`)) THEN
    MP_TAC(ISPECL [`dest:num option`; `args:num list`; `k:num`; `f:num`; `f':num`;
      `q0:(A)stack_prog`;
      `dest':num+num`; `stack_state_regs (t4:(A,C,FFI)stack_state)`;
        `stack_state_code (t4:(A,C,FFI)stack_state)`;
      `t7r:(num,(A)word_loc)fmap`; `stack_state_code (t5:(A,C,FFI)stack_state)`;
        `stack_prog:(A)stack_prog`]
      W2SP3AUX_ret_find_code) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `t7:(A,C,FFI)stack_state`)) (concl th))) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `t5:(A,C,FFI)stack_state`)) (concl th) &&
       can (find_term ((=) `t4:(A,C,FFI)stack_state`)) (concl th))) THEN
     ASM_REWRITE_TAC[stack_get_var_def] THEN EXPAND_TAC "t6" THEN
     REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN SIMP_TAC[];
     DISCH_TAC] THEN
    ASM_REWRITE_TAC[w2sp3aux_seval "stack_Call"; w2sp3aux_stack_accfupds; K_THM] THEN
    SUBGOAL_THEN `stack_state_code (t6:(A,C,FFI)stack_state) = stack_state_code
      (t5:(A,C,FFI)stack_state)`
      (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (ASM_CASES_TAC `stack_state_clock (t:(A,C,FFI)stack_state) = 0` THENL
    [ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
     CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
     REWRITE_TAC[wl_flush_state_def; stack_empty_env_def; w2sp3aux_wl_accfupds;
                 w2sp3aux_stack_accfupds; K_THM] THEN
     EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds] THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `wl_evaluate (prog:(A)wl_prog, wl_call_env args1 ss
       (wl_push_env (a'':((A)word_loc)spt#((A)word_loc)spt) NONE (wl_dec_clock
         (s:(A,num#C,FFI)wl_state))))`
       PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r':((A)wl_result)option` (X_CHOOSE_THEN `s2':(A,num#C,FFI)wl_state`
       ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackAlloc"; stack_dec_clock_def;
                stack_set_var_def; w2sp3aux_stack_accfupds; K_THM] THEN
    EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[]) THEN
  (ASM_CASES_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) - sac < fs - sac` THENL
    [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; pair_CASE_def; option_DISTINCT] THEN
     CASE_REWRITE_TAC[] THEN
     w2sp3aux_ret_halt_tac (UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) - sac <
       fs - sac` THEN
       UNDISCH_TAC `sac <= stack_state_stack_space (t:(A,C,FFI)stack_state)` THEN ARITH_TAC);
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `LENGTH (t7s:((A)word_loc)list) = LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) /\
      DROP (stack_state_stack_space t) t7s = DROP (stack_state_stack_space t) (stack_state_stack
        (t5:(A,C,FFI)stack_state)) /\
      (!x. x < sac
           ==> EL (x + f) (DROP (stack_state_stack_space t - sac) (stack_state_stack t5)) =
               EL x (DROP (stack_state_stack_space t - sac) t7s)) /\
      (!i. ~(i = k) ==> FLOOKUP (t7r:(num,(A)word_loc)fmap) i = FLOOKUP (stack_state_regs t5) i)`
     STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `stack_state_stack_space (t6:(A,C,FFI)stack_state) = stack_state_stack_space
      (t:(A,C,FFI)stack_state) - sac /\
                   stack_state_stack t6 = stack_state_stack (t5:(A,C,FFI)stack_state) /\
                   stack_state_regs t6 = stack_state_regs t5` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM]; ALL_TAC] THEN
     REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (stack_state_stack (t6:(A,C,FFI)stack_state)) = LENGTH
       (t7s:((A)word_loc)list)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      UNDISCH_TAC `DROP (stack_state_stack_space (t7:(A,C,FFI)stack_state) + 0 + sac) t7s =
                   DROP (stack_state_stack_space (t6:(A,C,FFI)stack_state) + 0 + sac)
                     (stack_state_stack t6)` THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) - sac + sac =
        stack_state_stack_space t`
        (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `sac <= stack_state_stack_space (t:(A,C,FFI)stack_state)` THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_let (concl th))) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `t7:(A,C,FFI)stack_state`)) (concl th))) THEN
      ASM_REWRITE_TAC[stack_get_var_def; w2sp3aux_stack_accfupds; K_THM]];
     ALL_TAC]) THEN
  (MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                   `t5:(A,C,FFI)stack_state`; `lens:num list`; `args:num list`;
                     `a:((A)word_loc)list`;
                   `args1:((A)word_loc)list`; `a'':((A)word_loc)spt#((A)word_loc)spt`;
                     `ss:num option`;
                   `fs:num`; `svc:num`; `sac:num`; `t7s:((A)word_loc)list`;
                     `t7r:(num,(A)word_loc)fmap`;
                   `l1:num`; `l2:num`] W2SP3AUX_ret_callee_rel) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `(if svc = 0 then 0 else svc + 1) = fs` THEN ARITH_TAC;
      UNDISCH_TAC `~(stack_state_stack_space (t:(A,C,FFI)stack_state) - sac < fs - sac)` THEN
      UNDISCH_TAC `sac <= stack_state_stack_space (t:(A,C,FFI)stack_state)` THEN
      UNDISCH_TAC `sac <= fs` THEN ARITH_TAC];
     DISCH_TAC]) THEN
  (SUBGOAL_THEN `~(r' = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
    [DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
       not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                   `t:(A,C,FFI)stack_state`; `lens:num list`; `0`; `dest:num option`;
                   `add_ret_loc (SOME (vs,live,ret_code,l1,l2):(num
                     list#cutsets#(A)wl_prog#num#num)option)
                      (a:((A)word_loc)list)`;
                   `args1:((A)word_loc)list`; `prog:(A)wl_prog`;
                     `ss:num option`] W2SP3AUX_find_code_conv) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `stack_get_labels (qc:(A)stack_prog) SUBSET loc_check (stack_state_code
      (t5:(A,C,FFI)stack_state))`
      ASSUME_TAC THENL
    [MP_TAC(MATCH_MP find_code_IMP_get_labels (ASSUME
       `stack_find_code dest' ((t7r:(num,(A)word_loc)fmap) \\ 0) (stack_state_code
         (t5:(A,C,FFI)stack_state)) = SOME (stack_prog:(A)stack_prog)`)) THEN
     ASM_REWRITE_TAC[stack_get_labels_def; UNION_SUBSET] THEN SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `stack_state_bitmaps (t:(A,C,FFI)stack_state) <<= stack_state_bitmaps
      (t5:(A,C,FFI)stack_state)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `stack_state_bitmaps
      (t4:(A,C,FFI)stack_state)` THEN
     ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (REMOVE_THEN "IHcall" (MP_TAC o SPECL [`a:((A)word_loc)list`; `ret_code:(A)wl_prog`;
    `l1:num`; `l2:num`;
      `vs:num list`; `live:num_set#num_set`; `prog:(A)wl_prog`; `args1:((A)word_loc)list`;
        `ss:num option`;
      `a'':((A)word_loc)spt#((A)word_loc)spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `fs:num`; `svc:num`; `r':((A)wl_result)option`;
      `s2':(A,num#C,FFI)wl_state`;
      `stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
         (stack_state_stack_fupd (K t7s)
           (stack_state_stack_space_fupd (K (stack_state_stack_space
             (t5:(A,C,FFI)stack_state) - fs))
             (stack_state_clock_fupd (K (stack_state_clock t5 - 1)) t5)))`;
      `bsc:(A word)app_list`; `ic:num`; `bs2:(A word)app_list`; `i2:num`; `qc:(A)stack_prog`;
      `CONS (f':num) lens`]) THEN
    ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IS_PREFIX_TRANS THEN
      EXISTS_TAC `DROP (ic - LENGTH (append (bsc:(A word)app_list)))
                    (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        w2sp3aux_has_const "MAX" (concl th) && rhs (concl th) = `svc:num`)) THEN
      MATCH_MP_TAC W2SP3AUX_max_var_svc THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
      (X_CHOOSE_THEN `res1:((A)stack_result)option` STRIP_ASSUME_TAC)))) THEN
  (ASM_CASES_TAC `~(?a0 ys. r' = SOME (wl_Result a0 ys:(A)wl_result) /\
                             OPTION_MAP compile_result r' = (res1:((A)stack_result)option))`) THENL
  [(EXISTS_TAC `ck:num` THEN
    SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) + ck = 0)` (fun th ->
      REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN
    SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck =
                  (stack_state_clock (t:(A,C,FFI)stack_state) + ck) - 1 /\
                  stack_state_stack_space t5 - fs = (stack_state_stack_space t - sac) - (fs - sac)`
      STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) = stack_state_clock
      (t:(A,C,FFI)stack_state) /\
                   stack_state_stack_space t5 = stack_state_stack_space t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
      [UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
        (t5:(A,C,FFI)stack_state)` THEN
       UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
         (t:(A,C,FFI)stack_state)` THEN
       ARITH_TAC;
       UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) = stack_state_stack_space
         (t4:(A,C,FFI)stack_state)` THEN
       UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) = stack_state_stack_space
         (t:(A,C,FFI)stack_state)` THEN
       ARITH_TAC];
      ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN
     UNDISCH_TAC `sac <= fs` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_is_seval_of `qc:(A)stack_prog`)) THEN
    REWRITE_TAC[ASSUME `stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck =
                  (stack_state_clock (t:(A,C,FFI)stack_state) + ck) - 1`;
                ASSUME `stack_state_stack_space (t5:(A,C,FFI)stack_state) - fs =
                  (stack_state_stack_space (t:(A,C,FFI)stack_state) - sac) - (fs - sac)`] THEN
    EXPAND_TAC "t6" THEN SIMP[] THEN DISCH_TAC THEN SIMP[]) THEN
   (SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) - sac - (fs - sac) =
                  stack_state_stack_space t - fs` (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `sac <= fs` THEN UNDISCH_TAC `sac <= stack_state_stack_space
      (t:(A,C,FFI)stack_state)` THEN
     ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE_def; FST; SND]) THEN
   (MP_TAC(ISPECL [`vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`; `l1:num`; `l2:num`;
      `dest:num option`; `args:num list`; `NONE:(num#(A)wl_prog#num#num)option`;
      `s:(A,num#C,FFI)wl_state`; `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`;
      `a:((A)word_loc)list`; `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`;
      `a'':((A)word_loc)spt#((A)word_loc)spt`; `r':((A)wl_result)option`;
        `s2':(A,num#C,FFI)wl_state`]
      W2SP3AUX_ret_cont_mono) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `OPTION_MAP compile_result (r':((A)wl_result)option) = res1` THENL
    [ALL_TAC;
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th) &&
       w2sp3aux_has_const "stackSem_Halt" (concl th) &&
       can (find_term ((=) `r':((A)wl_result)option`)) (concl th))) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
     SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) =
                     SOME (stackSem_Halt (wl_Word (word 2))))` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      MATCH_MP_TAC compile_result_NOT_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC IS_PREFIX_TRANS THEN
      EXISTS_TAC `ffi_state_io_events (wl_state_ffi (s2':(A,num#C,FFI)wl_state))` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]) THEN
   (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res1:((A)stack_result)option`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th) &&
       w2sp3aux_has_const "stackSem_Halt" (concl th) &&
       can (find_term ((=) `r':((A)wl_result)option`)) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
       not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
    MP_TAC(ISPEC `r':((A)wl_result)option` option_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC) SUBST_ALL_TAC) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL
    [ALL_TAC; DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
    REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (ISPEC `rr:(A)wl_result` (cases "wl_result")) THEN
    CASE_REWRITE_TAC[PAIR_EQ; OPTION_MAP_DEF; compile_result_def] THENL
    [DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) && is_exists (dest_neg (concl th)) &&
       w2sp3aux_has_const "wl_Result" (concl th))) THEN
     REWRITE_TAC[option_INJ; injectivity "wl_result"] THEN MESON_TAC[];
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
    REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
    CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel"
      (concl th) &&
      can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th) && not (is_forall (concl th)) &&
      w2sp3aux_has_const "push_locals" (concl th))) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`prog:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`;
      `a'':((A)word_loc)spt#((A)word_loc)spt`;
                   `args1:((A)word_loc)list`; `ss:num option`; `a0:(A)word_loc`; `a1:(A)word_loc`;
                   `s2':(A,num#C,FFI)wl_state`] W2SP3AUX_ret_exc_depth) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_LENGTH o
      check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
             can (find_term ((=) `s:(A,num#C,FFI)wl_state`)) (concl th) &&
             can (find_term ((=) `t:(A,C,FFI)stack_state`)) (concl th))) THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const; w2sp3aux_wl_accfupds;
                K_THM; wl_push_env_const] THEN
    SUBGOAL_THEN `LASTN (wl_state_handler (s:(A,num#C,FFI)wl_state) + 1) (CONS (f':num) lens) =
                  LASTN (wl_state_handler s + 1) lens` SUBST1_TAC THENL
    [MP_TAC(ISPECL [`wl_state_handler (s:(A,num#C,FFI)wl_state) + 1`;
      `lens:num list`] LASTN_CONS) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[];
     W2SP3AUX_ERR_TAC; W2SP3AUX_ERR_TAC;
     w2sp3aux_ret_pass_tac; w2sp3aux_ret_pass_tac; w2sp3aux_ret_pass_tac; W2SP3AUX_ERR_TAC]);
   (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) && is_neg (dest_neg (concl th)))) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:(A)word_loc` (X_CHOOSE_THEN `ys:((A)word_loc)list`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `r':((A)wl_result)option`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res1:((A)stack_result)option`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; compile_result_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel"
      (concl th) &&
      can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th) && not (is_forall (concl th)) &&
      w2sp3aux_has_const "push_locals" (concl th))) THEN
    CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
       not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
    CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    CASES_ON `wl_pop_env (s2':(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC] THEN
    DISCH_TAC) THEN
   (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
      can (find_term ((=) `x0:(A)word_loc`)) (concl th))) THEN
    MP_TAC(ISPECL [`prog:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`;
      `a'':((A)word_loc)spt#((A)word_loc)spt`;
                   `args1:((A)word_loc)list`; `ss:num option`; `x0:(A)word_loc`;
                     `ys:((A)word_loc)list`;
                   `s2':(A,num#C,FFI)wl_state`] W2SP3AUX_ret_swap) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `mm:num option` (X_CHOOSE_THEN
      `ll0:(num#(A)word_loc)list`
      (X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `xss:((A)stack_frame)list`
        ASSUME_TAC))))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
      check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
                       can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th))) THEN
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `s2':(A,num#C,FFI)wl_state`;
      `t1:(A,C,FFI)stack_state`;
                   `f':num`; `lens:num list`; `LENGTH (ys:((A)word_loc)list) - (k - 1)`;
                     `mm:num option`;
                   `ll0:(num#(A)word_loc)list`; `ll:(num#(A)word_loc)list`;
                     `xss:((A)stack_frame)list`]
                  W2SP3AUX_ret_frame_len) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (ys:((A)word_loc)list) - (k - 1) = (LENGTH (vs:num list) + 1) - k /\
                  LENGTH (vs:num list) - (k - 1) = (LENGTH (vs:num list) + 1) - k`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [UNDISCH_TAC `LENGTH (ys:((A)word_loc)list) = LENGTH (vs:num list)` THEN
     UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `n0 = (LENGTH (vs:num list) + 1) - k` THEN
    MP_TAC(ISPECL [`k:num`; `f:num`; `n0:num`; `t1:(A,C,FFI)stack_state`]
                  evaluate_copy_ret_aux) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; ALL_TAC] THEN
     UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f <=
                  LENGTH (stack_state_stack t1)` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t2s:((A)word_loc)list` (X_CHOOSE_THEN `t2r:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC))))) THEN
   (SUBGOAL_THEN `LENGTH (ys:((A)word_loc)list) - (k - 1) = n0` ASSUME_TAC THENL
    [UNDISCH_TAC `LENGTH (ys:((A)word_loc)list) = LENGTH (vs:num list)` THEN
     UNDISCH_TAC `(LENGTH (vs:num list) + 1) - k = n0` THEN UNDISCH_TAC `4 < k`
       THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`live:num_set#num_set`; `wl_state_locals (s:(A,num#C,FFI)wl_state)`;
                   `a'':((A)word_loc)spt#((A)word_loc)spt`] W2SP3AUX_cut_envs_domain) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s2':(A,num#C,FFI)wl_state`;
                   `t1:(A,C,FFI)stack_state`; `lens:num list`; `ys:((A)word_loc)list`;
                     `vs:num list`;
                   `a''':(A,num#C,FFI)wl_state`; `mm:num option`; `ll0:(num#(A)word_loc)list`;
                   `ll:(num#(A)word_loc)list`; `xss:((A)stack_frame)list`; `t2s:((A)word_loc)list`;
                   `t2r:(num,(A)word_loc)fmap`] W2SP3AUX_ret_state_rel) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `nn:num` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th) &&
        w2sp3aux_has_const "DIV" (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `SND (live:num_set#num_set)`)) (concl th) &&
        w2sp3aux_has_const "DIV" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`];
      UNDISCH_TAC `DROP (f + n0 + stack_state_stack_space (t2:(A,C,FFI)stack_state)) t2s =
                   DROP (f + n0 + stack_state_stack_space (t1:(A,C,FFI)stack_state))
                     (stack_state_stack t1)` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `t2s:((A)word_loc)list`)) (concl th) && w2sp3aux_has_const "EL"
          (concl th) &&
        not (is_let (concl th)))) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_let (concl th))) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `t2:(A,C,FFI)stack_state`)) (concl th) &&
        w2sp3aux_has_const "stack_get_var" (concl th))) THEN
      ASM_REWRITE_TAC[stack_get_var_def; w2sp3aux_stack_accfupds; K_THM]];
     DISCH_TAC]) THEN
   (SUBGOAL_THEN `stack_get_labels (q2:(A)stack_prog) SUBSET loc_check (stack_state_code
     (t:(A,C,FFI)stack_state))`
      ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o check (fun th -> is_conj (concl th) && w2sp3aux_has_const
      "stack_get_labels" (concl th) &&
       can (find_term ((=) `q0:(A)stack_prog`)) (concl th))) THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_get_labels_def; get_labels_copy_ret; UNION_SUBSET;
       INSERT_SUBSET; UNION_EMPTY; EMPTY_SUBSET] THEN
     SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
      check (w2sp3aux_is_seval_of `qc:(A)stack_prog`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM]) THEN
    SUBGOAL_THEN `subspt (stack_state_code (t:(A,C,FFI)stack_state)) (stack_state_code
      (t1:(A,C,FFI)stack_state)) /\
                  stack_state_bitmaps t <<= stack_state_bitmaps t1`
      STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC
       `stack_state_code (t5:(A,C,FFI)stack_state)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (GEN_ALL subspt_trans) THEN
      EXISTS_TAC `stack_state_code (t4:(A,C,FFI)stack_state)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `stack_state_bitmaps
        (t5:(A,C,FFI)stack_state)` THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    MP_TAC(ISPECL [`live:num_set#num_set`; `(bs:(A word)app_list,n:num)`; `(k:num,f:num,f':num)`;
                   `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`] wLive_LENGTH) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC) THEN
   (REMOVE_THEN "IHret" (MP_TAC o SPECL [`a:((A)word_loc)list`; `live:num_set#num_set`;
     `prog:(A)wl_prog`;
      `args1:((A)word_loc)list`; `ss:num option`; `x0:(A)word_loc`; `l1:num`; `l2:num`;
      `s2':(A,num#C,FFI)wl_state`; `a'':((A)word_loc)spt#((A)word_loc)spt`; `ret_code:(A)wl_prog`;
      `vs:num list`; `ys:((A)word_loc)list`; `a''':(A,num#C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
      `s1:(A,num#C,FFI)wl_state`;
      `stack_state_regs_fupd (K t2r)
        (stack_state_stack_fupd (K t2s)
          (stack_state_stack_space_fupd
             (K (stack_state_stack_space (t1:(A,C,FFI)stack_state) + (LENGTH (vs:num list) + 1)
               - k)) t1))`;
      `bs1:(A word)app_list`; `n1:num`; `bs':(A word)app_list`; `n':num`; `q2:(A)stack_prog`;
      `lens:num list`]) THEN
    ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        can (find_term ((=) `n1:num`)) (concl th) && can (find_term ((=) `n:num`)) (concl th))) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `LENGTH (stack_state_bitmaps
        (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        can (find_term ((=) `n1:num`)) (concl th) && can (find_term ((=) `n:num`)) (concl th))) THEN
      MATCH_MP_TAC IS_PREFIX_TRANS THEN
      EXISTS_TAC `DROP (n - LENGTH (append (bs:(A word)app_list))) (stack_state_bitmaps
        (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `loc_check (stack_state_code
        (t:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC loc_check_SUBSET THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
      (X_CHOOSE_THEN `res3:((A)stack_result)option` STRIP_ASSUME_TAC)))) THEN
   (EXISTS_TAC `ck + ck2:num` THEN
    SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) + ck + ck2 = 0)` (fun th ->
      REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE_def]) THEN
   (SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) = stack_state_clock
     (t:(A,C,FFI)stack_state) /\
                  stack_state_stack_space t5 = stack_state_stack_space t` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
       (t5:(A,C,FFI)stack_state)` THEN
      UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
        (t:(A,C,FFI)stack_state)` THEN
      ARITH_TAC;
      UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) = stack_state_stack_space
        (t4:(A,C,FFI)stack_state)` THEN
      UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) = stack_state_stack_space
        (t:(A,C,FFI)stack_state)` THEN
      ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN
     `stack_evaluate (qc:(A)stack_prog,
        stack_state_stack_space_fupd (K (stack_state_stack_space (t:(A,C,FFI)stack_state) - sac -
          (fs - sac)))
        (stack_state_clock_fupd (K ((stack_state_clock t + ck + ck2) - 1))
        (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
        (stack_state_clock_fupd (K (stack_state_clock t + ck + ck2))
        (stack_state_stack_fupd (K t7s)
        (stack_state_regs_fupd (K t7r) (t6:(A,C,FFI)stack_state))))))) =
      (SOME (stack_Result x0), stack_state_clock_fupd (K (stack_state_clock t1 + ck2))
        (t1:(A,C,FFI)stack_state))`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`qc:(A)stack_prog`;
       `stack_state_clock_fupd (K (stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck))
         (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
         (stack_state_stack_fupd (K t7s)
         (stack_state_stack_space_fupd (K (stack_state_stack_space (t:(A,C,FFI)stack_state) - fs))
         (stack_state_clock_fupd (K (stack_state_clock t5 - 1)) t5))))`;
       `SOME (stack_Result (x0:(A)word_loc))`; `t1:(A,C,FFI)stack_state`]
       (INST [`ck2:num`,`extra:num`] stack_evaluate_add_clock)) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[option_INJ] THEN REWRITE_TAC[distinctness "stack_result"]; ALL_TAC] THEN
     SUBGOAL_THEN `(stack_state_clock (t:(A,C,FFI)stack_state) + ck + ck2) - 1 =
                   (stack_state_clock t - 1 + ck) + ck2 /\
                   stack_state_stack_space t - sac - (fs - sac) = stack_state_stack_space t - fs`
       (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN
      UNDISCH_TAC `sac <= fs` THEN UNDISCH_TAC `sac <= stack_state_stack_space
        (t:(A,C,FFI)stack_state)` THEN
      ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN EXPAND_TAC "t6" THEN SIMP[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[]) THEN
   (REWRITE_TAC[w2sp3aux_seval "stack_Skip"; FST; SND] THEN
    REWRITE_TAC[evaluate_copy_ret_Seq'] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[num_stack_ret_def] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
    REWRITE_TAC[evaluate_copy_ret_aux_clock] THEN
    ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND]) THEN
   (MP_TAC(ISPECL [`stack_state_clock_fupd (K (stack_state_clock (t1:(A,C,FFI)stack_state) + ck2))
         (stack_state_stack_fupd (K (t2s:((A)word_loc)list)) (stack_state_regs_fupd (K t2r) t1))`;
       `n0:num`; `q2:(A)stack_prog`] evaluate_SeqStackFree) THEN
    REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f <= LENGTH
       (stack_state_stack t1)` THEN
     ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackFree";
      w2sp3aux_stack_accfupds; K_THM] THEN
    SUBGOAL_THEN `~(LENGTH (t2s:((A)word_loc)list) < stack_state_stack_space
      (t1:(A,C,FFI)stack_state) + n0)`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f <= LENGTH
       (stack_state_stack t1)` THEN
     ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_is_seval_of `q2:(A)stack_prog`)) THEN
    ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN SIMP[] THEN DISCH_TAC THEN SIMP[] THEN
    ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1]) THEN
   (SUBGOAL_THEN `wl_state_handler (a''':(A,num#C,FFI)wl_state) = wl_state_handler
     (s:(A,num#C,FFI)wl_state)`
      ASSUME_TAC THENL
    [UNDISCH_TAC `wl_pop_env (s2':(A,num#C,FFI)wl_state) = SOME a'''` THEN
     ASM_REWRITE_TAC[wl_pop_env_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[w2sp3aux_wl_accfupds] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "stackSem_Halt" (concl th) &&
      can (find_term ((=) `t3:(A,C,FFI)stack_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[wl_set_vars_def; w2sp3aux_wl_accfupds])]);;

(* The state relation at the entry of the callee of a returning call, for  *)
(* any handler (used for HOL4 8166)                                         *)
let W2SP3AUX_ret_callee_rel_gen = prove
 (`!ac k fr f' (s:(A,num#C,FFI)wl_state) (h:(num#(A)wl_prog#num#num)option)
     (t5:(A,C,FFI)stack_state) lens
     (args:num list) a args1 envs ss fs svc sac (t7s:((A)word_loc)list) t7r l1 l2.
     word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env envs h s)))
       t5 (CONS f' lens) 0 /\
     (!n v. lookup n (wl_state_locals s) = SOME v
            ==> EVEN n /\
                (if n DIV 2 < k then FLOOKUP (stack_state_regs t5) (n DIV 2) = SOME v
                 else oEL (fr - 1 - (n DIV 2 - k))
                        (TAKE fr (DROP (stack_state_stack_space t5) (stack_state_stack
                          t5))) = SOME v /\
                      n DIV 2 - k < fr)) /\
     wl_get_vars args s = SOME a /\
     args = list_of_seq (\x. 2 * (x + 1)) (LENGTH args) /\
     isPREFIX args1 (CONS (wl_Loc l1 l2) a) /\
     LENGTH args1 - k = sac /\ sac <= svc /\
     (if svc = 0 then fs = 0 else fs = svc + 1) /\ the fs ss = fs /\
     sac <= fr /\ fs <= stack_state_stack_space t5 /\
     LENGTH t7s = LENGTH (stack_state_stack t5) /\
     DROP (stack_state_stack_space t5) t7s = DROP (stack_state_stack_space t5)
       (stack_state_stack t5) /\
     (!x. x < sac
          ==> EL (x + fr) (DROP (stack_state_stack_space t5 - sac) (stack_state_stack t5)) =
              EL x (DROP (stack_state_stack_space t5 - sac) t7s)) /\
     (!i. ~(i = k) ==> FLOOKUP t7r i = FLOOKUP (stack_state_regs t5) i) /\
     ~(wl_state_clock s = 0)
     ==> word_to_stackProof_state_rel ac k fs svc
           (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s)))
           (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
             (stack_state_stack_fupd (K t7s)
               (stack_state_stack_space_fupd (K (stack_state_stack_space t5 - fs))
                 (stack_state_clock_fupd (K (stack_state_clock t5 - 1)) t5))))
           (CONS f' lens) 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env envs (h:(num#(A)wl_prog#num#num)option) (s:(A,num#C,FFI)wl_state))))
       (t5:(A,C,FFI)stack_state) (CONS f' lens) 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const] THEN
    REWRITE_TAC[w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM; wl_push_env_const] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_wl_accfupds; K_THM; wl_push_env_const]) THEN
    ASM_REWRITE_TAC[wf_fromList2] THEN
    SUBGOAL_THEN `DROP fs (DROP (stack_state_stack_space (t5:(A,C,FFI)stack_state) - fs + 0) t7s) =
                  DROP 0 (DROP (stack_state_stack_space t5 + 0) (stack_state_stack t5))`
                    SUBST1_TAC THENL
    [REWRITE_TAC[DROP_DROP_T; ADD_CLAUSES; DROP_0] THEN
     SUBGOAL_THEN `fs + stack_state_stack_space (t5:(A,C,FFI)stack_state) - fs =
       stack_state_stack_space t5`
       SUBST1_TAC THENL
     [UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)`
       THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + 0 <= LENGTH
    (stack_state_stack t5)` THEN
   UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)` THEN ARITH_TAC;
   UNDISCH_TAC `stack_size_rel 0 (SOME 0) (wl_state_stack_limit (s:(A,num#C,FFI)wl_state))
      (wl_state_stack_max (wl_push_env envs (h:(num#(A)wl_prog#num#num)option) s))
      (wl_state_stack (wl_push_env envs (h:(num#(A)wl_prog#num#num)option) s))
      (stack_state_stack (t5:(A,C,FFI)stack_state)) (stack_state_stack_space t5) 0` THEN
    REWRITE_TAC[stack_size_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `sm:num` THEN REWRITE_TAC[OPTION_MAP2_SOME] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x1:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "IS_SOME" (concl th))) THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; SUB_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
    SUBGOAL_THEN `(LENGTH (stack_state_stack (t5:(A,C,FFI)stack_state)) - (stack_state_stack_space
      t5 - fs)) - fs =
                  LENGTH (stack_state_stack t5) - stack_state_stack_space t5` SUBST1_TAC THENL
    [UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + 0 <= LENGTH
      (stack_state_stack t5)` THEN
     UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)`
       THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `SOME (x1':num) = SOME ss'` THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH (stack_state_stack (t5:(A,C,FFI)stack_state)) - stack_state_stack_space
      t5 <= x1` THEN
    REWRITE_TAC[MAX] THEN ARITH_TAC;
       REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `EVEN n /\ n DIV 2 < LENGTH (args1:((A)word_loc)list) /\ v = EL (n DIV 2) args1`
      STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `lookup n (fromList2 (args1:((A)word_loc)list)) = SOME (v:(A)word_loc)` THEN
     REWRITE_TAC[lookup_fromList2; lookup_fromList] THEN COND_CASES_TAC
       THEN REWRITE_TAC[option_DISTINCT] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]
       THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lookup n (fromList2 (CONS (wl_Loc l1 l2) (a:((A)word_loc)list))) = SOME
      (v:(A)word_loc)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC lookup_fromList2_prefix THEN EXISTS_TAC `args1:((A)word_loc)list` THEN
     ASM_REWRITE_TAC[IS_PREFIX_DEF]; ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
    [UNDISCH_TAC `lookup n (fromList2 (CONS (wl_Loc l1 l2) (a:((A)word_loc)list))) = SOME
      (v:(A)word_loc)` THEN
     ASM_REWRITE_TAC[lookup_fromList2; lookup_fromList; EVEN; LENGTH; ARITH_RULE `0 DIV 2 = 0`;
                     LT_0; EL; HD; option_INJ] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     SUBGOAL_THEN `0 < k` (fun th -> REWRITE_TAC[th; FLOOKUP_UPDATE]) THEN
     UNDISCH_TAC `4 < k` THEN ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME (v:(A)word_loc)`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`args:num list`; `s:(A,num#C,FFI)wl_state`; `a:((A)word_loc)list`; `n:num`;
                    `l1:num`; `l2:num`; `v:(A)word_loc`] get_vars_fromList2_eq_cons) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o
       check (fun th -> is_eq (concl th) && lhs (concl th) = `args:num list`)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th -> is_forall
      (concl th) &&
      w2sp3aux_has_const "oEL" (concl th) && w2sp3aux_has_const "wl_state_locals" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n DIV 2 = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `EVEN n` THEN UNDISCH_TAC `~(n = 0)` THEN REWRITE_TAC[EVEN_EXISTS] THEN
     STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
     UNDISCH_TAC `~(n = 0)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
     SUBGOAL_THEN `~(0 = n DIV 2) /\ ~(n DIV 2 = k)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(n DIV 2 = 0)` THEN UNDISCH_TAC `n DIV 2 < k` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[];
    STRIP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `n DIV 2 - k < sac /\ n DIV 2 - k < fs /\ n DIV 2 < k + svc /\
                  sac <= stack_state_stack_space (t5:(A,C,FFI)stack_state)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `n DIV 2 < LENGTH (args1:((A)word_loc)list)` THEN
     UNDISCH_TAC `~(n DIV 2 < k)` THEN
     UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
     UNDISCH_TAC `sac <= svc` THEN UNDISCH_TAC `if svc = 0 then fs = 0 else fs = svc + 1` THEN
     UNDISCH_TAC `fs <= stack_state_stack_space (t5:(A,C,FFI)stack_state)`
       THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC W2SP3AUX_ret_frame_index THEN
    MAP_EVERY EXISTS_TAC [`stack_state_stack (t5:(A,C,FFI)stack_state)`; `fr:num`; `sac:num`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) + 0 <= LENGTH
      (stack_state_stack t5)` THEN
    ARITH_TAC]]);;

(* The handler frame takes three more stack slots (used for HOL4 8166) *)
let W2SP3AUX_push_env_stack_size = prove
 (`!envs (s:(A,C,FFI)wl_state) hv (hprog:(A)wl_prog) h1 h2.
     wl_stack_size (wl_state_stack (wl_push_env envs (SOME (hv,hprog,h1,h2)) s)) =
     OPTION_MAP ((+) 3)
       (wl_stack_size (wl_state_stack (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option) s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `pp:num->num->num`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE_def; w2sp3aux_wl_accfupds; K_THM; stack_size_eq] THEN
  CASES_ON `wl_state_locals_size (s:(A,C,FFI)wl_state)` THEN
  CASES_ON `wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;

(* The caller frame seen through the pushed handler slots (used for HOL4    *)
(* 8166)                                                                    *)
let W2SP3AUX_push_shift = prove
 (`!(st:A list) st' sp sp' f j v.
     (!n. n < LENGTH st - sp ==> EL n (DROP sp st) = EL (n + 3) (DROP sp' st')) /\
     sp' + 3 = sp /\ LENGTH st' = LENGTH st /\ j < f /\
     oEL (f - 1 - j) (TAKE f (DROP sp st)) = SOME v
     ==> oEL ((f + 3) - 1 - j) (TAKE (f + 3) (DROP sp' st')) = SOME v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP oEL_TAKE_E) THEN
  ASM_SIMP_TAC[LLOOKUP_TAKE; ARITH_RULE `j < f ==> (f + 3) - 1 - j < f + 3`] THEN
  REWRITE_TAC[oEL_EQ_EL; LENGTH_DROP] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f - 1 - j`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f - 1 - j) + 3 = (f + 3) - 1 - j` SUBST1_TAC THENL
  [UNDISCH_TAC `j < f` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `f - 1 - j < LENGTH (st:A list) - sp` THEN
  UNDISCH_TAC `LENGTH (st':A list) = LENGTH (st:A list)` THEN
  UNDISCH_TAC `sp' + 3 = sp` THEN UNDISCH_TAC `j < f` THEN ARITH_TAC);;

(* After a normal return, the callee leaves the handler frame of the call   *)
(* on top (used for HOL4 8166)                                              *)
let W2SP3AUX_ret_swap_SOME = prove
 (`!prog (s:(A,num#C,FFI)wl_state) envs args1 ss x0 ys s2 hv (hprog:(A)wl_prog) h1 h2.
     wl_evaluate (prog, wl_call_env args1 ss
        (wl_push_env envs (SOME (hv,hprog,h1,h2)) (wl_dec_clock s))) =
       (SOME (wl_Result x0 ys), s2)
     ==> ?m l0 l xs. wl_state_stack s2 =
                     CONS (StackFrame m l0 l (SOME (wl_state_handler s,h1,h2))) xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs (SOME (hv,hprog,h1,h2))
       (wl_dec_clock (s:(A,num#C,FFI)wl_state)))`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const; w2sp3aux_wl_accfupds;
              K_THM; wl_push_env_const] THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,num#C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `pp:num->num->num`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE_def; w2sp3aux_wl_accfupds; K_THM] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `s_key_eq (CONS (StackFrame (wl_state_locals_size (s:(A,num#C,FFI)wl_state))
      (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))) ll (SOME (wl_state_handler s,h1,h2)))
      (wl_state_stack s)) (wl_state_stack (s2:(A,num#C,FFI)wl_state))` THEN
  MP_TAC(ISPEC `wl_state_stack (s2:(A,num#C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `fr:(A)stack_frame`
    (X_CHOOSE_THEN `rest:((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[s_key_eq_def] THEN
  STRUCT_CASES_TAC(ISPEC `fr:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_key_eq_def2] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[CONS_11; injectivity "stack_frame"] THEN MESON_TAC[]);;

(* The handler frame of the call is within the stack at the return (used for *)
(* HOL4 8166)                                                               *)
let W2SP3AUX_ret_frame_len_SOME = prove
 (`!ac k (s2:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state) f' lens extra m l0 l hh h1 h2 xs.
     word_to_stackProof_state_rel ac k 0 0 s2 t1 (CONS f' lens) extra /\
     wl_state_stack s2 = CONS (StackFrame m l0 l (SOME (hh,h1,h2))) xs
     ==> (stack_state_stack_space t1 + extra) + f' + 4 <= LENGTH (stack_state_stack t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
                 `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `hh:num`;
                   `h1:num`; `h2:num`;
                 `xs:((A)stack_frame)list`;
                 `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
                 `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + extra)
                    (stack_state_stack t1))`;
                 `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                 `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
                stack_rel_cons_LEN_SOME) THEN
  ANTS_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DROP_0; LENGTH_DROP] THEN ARITH_TAC);;

(* A local restored at the return from a call with handler is in the       *)
(* caller's frame on the stack (used for HOL4 8166)                         *)
let W2SP3AUX_frame_lookup_SOME = prove
 (`!k (bs:(A word)list) m l0 l hh h1 h2 (xs:((A)stack_frame)list) (sh:((B)word_loc)option)
      (st:((A)word_loc)list) len f' lens n v whandler.
     word_to_stackProof_stack_rel k whandler (CONS (StackFrame m l0 l (SOME (hh,h1,h2))) xs)
       sh st len bs
       (CONS f' lens) /\
     lookup n (union (fromAList l) (fromAList l0)) = SOME v /\ k <= n DIV 2 /\ n DIV 2 < k + f'
     ==> oEL ((f' + 3) - (n DIV 2 - k)) st = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `abs_stack (bs:(A word)list) (CONS (StackFrame m l0 l (SOME (hh,h1,h2)))
      (xs:((A)stack_frame)list)) st
                   (CONS f' lens) = SOME stack` THEN
    MP_TAC(ISPEC `st:((A)word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `w0:(A)word_loc` (X_CHOOSE_THEN
      `st1:((A)word_loc)list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `st1:((A)word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `loc:(A)word_loc` (X_CHOOSE_THEN
      `st2:((A)word_loc)list` SUBST_ALL_TAC))) THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `st2:((A)word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `hv:(A)word_loc` (X_CHOOSE_THEN
      `st3:((A)word_loc)list` SUBST_ALL_TAC))) THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `st3:((A)word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `w:(A)word_loc` (X_CHOOSE_THEN
      `rest:((A)word_loc)list` SUBST_ALL_TAC))) THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `full_read_bitmap (bs:(A word)list) (w:(A)word_loc)`
      THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    W(fun (asl,w) -> CASES_ON (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
      "abs_stack" with _ -> false) w)) THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `stack_rel_aux k len (CONS (StackFrame m l0 l (SOME (hh,h1,h2)))
    (xs:((A)stack_frame)list))
      (CONS (SOME (loc,hv),a,TAKE f' (rest:((A)word_loc)list)) a')` THEN
    REWRITE_TAC[stack_rel_aux_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `LENGTH (TAKE f' (rest:((A)word_loc)list)) = f'` ASSUME_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN UNDISCH_TAC `~(LENGTH (rest:((A)word_loc)list) < f')`
      THEN ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `(f' + 3) - (n DIV 2 - k) = SUC (SUC (SUC (SUC (f' - 1 - (n DIV 2 - k)))))`
      SUBST1_TAC THENL
    [UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[oEL_DEF; NOT_SUC; SUC_SUB1] THEN
    SUBGOAL_THEN `oEL (f' - 1 - (n DIV 2 - k)) (rest:((A)word_loc)list) =
                  oEL (f' - 1 - (n DIV 2 - k)) (TAKE f' rest)` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LLOOKUP_TAKE THEN
     UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `lookup n (union (fromAList l) (fromAList (l0:(num#(A)word_loc)list))) = SOME
      (v:(A)word_loc)` THEN
    REWRITE_TAC[lookup_union; lookup_fromAList] THEN
    CASES_ON `ALOOKUP (l:(num#(A)word_loc)list) n` THEN CASE_REWRITE_TAC[option_INJ] THENL
    [DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th -> is_forall
       (concl th) &&
       w2sp3aux_has_const "index_list" (concl th))) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     MP_TAC(ISPECL [`TAKE f' (rest:((A)word_loc)list)`; `n DIV 2`; `k:num`] ALOOKUP_index_list) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `f' - 1 - (n DIV 2 - k) = (f' + k) - (n DIV 2 + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
     DISCH_THEN SUBST_ALL_TAC THEN
     SUBGOAL_THEN `MEM (n DIV 2,v:(A)word_loc) (index_list (TAKE f' (rest:((A)word_loc)list)) k)`
       MP_TAC THENL
     [MATCH_MP_TAC filter_bitmap_MEM THEN
      MAP_EVERY EXISTS_TAC [`a:bool list`; `MAP_FST adjust_names (l:(num#(A)word_loc)list)`] THEN
      ASM_REWRITE_TAC[MAP_FST_def; MEM_MAP; EXISTS_PAIR_THM] THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `v:(A)word_loc`] THEN
      REWRITE_TAC[adjust_names_def] THEN MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     DISCH_THEN(MP_TAC o MATCH_MP MEM_index_list_EL) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN REWRITE_TAC[oEL_EQ_EL] THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL [UNDISCH_TAC `n DIV 2 < k + f'` THEN UNDISCH_TAC `k <= n DIV 2`
       THEN ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     UNDISCH_TAC `n DIV 2 < k + f'` THEN UNDISCH_TAC `k <= n DIV 2` THEN ARITH_TAC]);;

(* Frame slots seen past the handler slots (used for HOL4 8166) *)
let W2SP3AUX_oEL_TAKE_DROP3 = prove
 (`!j f p (st:A list). j < f ==> oEL (j + 3) (TAKE (f + 3) (DROP p st)) = oEL j (TAKE f (DROP
   (p + 3) st))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LLOOKUP_TAKE; ARITH_RULE `j < f ==> j + 3 < f + 3`; oEL_DROP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* The state relation after the normal return of a call with handler     *)
(* (used for HOL4 8166, handler case HOL4 9497)                            *)
let W2SP3AUX_ret_state_rel_h = prove
 (`!ac k f f' (s2:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state) lens
      (ys:((A)word_loc)list) vs x m l0 l hh hl1 hl2 xs t2s t2r w spn.
     word_to_stackProof_state_rel ac k 0 0 s2 t1 (CONS f' lens) (LENGTH ys - (k - 1)) /\
     (!i. i < LENGTH ys
          ==> (if i + 1 < k then FLOOKUP (stack_state_regs t1) (i + 1) = SOME (EL i ys)
               else oEL (LENGTH ys - (i + 1))
                      (DROP (stack_state_stack_space t1) (stack_state_stack t1)) = SOME
                        (EL i ys))) /\
     wl_pop_env s2 = SOME x /\
     wl_state_stack s2 = CONS (StackFrame m l0 l (SOME (hh,hl1,hl2))) xs /\
     vs = list_of_seq (\x. 2 * (x + 1)) (LENGTH vs) /\ LENGTH ys = LENGTH vs /\
     MAX_LIST vs < 2 * f' + 2 * k /\ f' + 1 = f /\ ~(f' = 0) /\
     (!n. n IN domain (wl_state_locals x) ==> EVEN n /\ 2 * k <= n /\ n < 2 * f' + 2 * k) /\
     LENGTH t2s = LENGTH (stack_state_stack t1) /\
     DROP ((f + 3) + ((LENGTH vs + 1) - k) + stack_state_stack_space t1) t2s =
       DROP ((f + 3) + ((LENGTH vs + 1) - k) + stack_state_stack_space t1) (stack_state_stack t1) /\
     (!i. i < (f + 3) - ((LENGTH vs + 1) - k)
          ==> EL i (DROP (((LENGTH vs + 1) - k) + stack_state_stack_space t1) t2s) =
              EL i (DROP (((LENGTH vs + 1) - k) + stack_state_stack_space t1)
                (stack_state_stack t1))) /\
     (!i. i < (LENGTH vs + 1) - k
          ==> EL (i + f + 3) (DROP (stack_state_stack_space t1) t2s) =
              EL i (DROP (stack_state_stack_space t1) (stack_state_stack t1))) /\
     (!i. ~(i = k) ==> FLOOKUP t2r i = FLOOKUP (stack_state_regs t1) i) /\
     w = EL ((stack_state_stack_space t1 + ((LENGTH vs + 1) - k)) + 2) t2s /\
     spn = (stack_state_stack_space t1 + ((LENGTH vs + 1) - k)) + 3
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_vars vs ys x)
           (stack_state_regs_fupd (K (t2r |+ (k,w)))
             (stack_state_store_fupd (K (stack_state_store t1 |+ (Handler,w)))
               (stack_state_stack_fupd (K t2s)
                 (stack_state_stack_space_fupd (K spn) t1))))
           lens 0`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
    UNDISCH_TAC `wl_pop_env (s2:(A,num#C,FFI)wl_state) = SOME x` THEN
    ASM_REWRITE_TAC[wl_pop_env_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_wl_accfupds; K_THM]) THEN
    SUBGOAL_THEN `LENGTH (ys:((A)word_loc)list) - (k - 1) = (LENGTH (vs:num list) + 1) - k`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [UNDISCH_TAC `LENGTH (ys:((A)word_loc)list) = LENGTH (vs:num list)` THEN
     UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (vs:num list) < f' + k` ASSUME_TAC THENL
    [UNDISCH_TAC `MAX_LIST (vs:num list) < 2 * f' + 2 * k` THEN
     FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) o
       check (fun th -> is_eq (concl th) && lhs (concl th) = `vs:num list`)) THEN
     REWRITE_TAC[MAX_LIST_GENLIST_evens2; LENGTH_LIST_OF_SEQ] THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `n0 = (LENGTH (vs:num list) + 1) - k` THEN
    SUBGOAL_THEN `n0 < f` ASSUME_TAC THENL
    [UNDISCH_TAC `LENGTH (vs:num list) < f' + k` THEN UNDISCH_TAC
      `(LENGTH (vs:num list) + 1) - k = n0` THEN
     UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `s2:(A,num#C,FFI)wl_state`;
      `t1:(A,C,FFI)stack_state`;
                   `f':num`; `lens:num list`; `n0:num`; `m:num option`;
                   `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
                   `hh:num`; `hl1:num`; `hl2:num`; `xs:((A)stack_frame)list`]
                  W2SP3AUX_ret_frame_len_SOME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ALL_TAC) THEN
  (SUBGOAL_THEN `EL ((stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 2)
    (t2s:((A)word_loc)list) =
                  EL 2 (DROP (stack_state_stack_space t1 + n0) (stack_state_stack t1))`
                    ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `(f + 3) - n0`)) (concl th))) THEN
     ANTS_TAC THENL [UNDISCH_TAC `n0 < f` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `2 + n0 + stack_state_stack_space (t1:(A,C,FFI)stack_state) < LENGTH
       (t2s:((A)word_loc)list) /\
                   2 + n0 + stack_state_stack_space t1 < LENGTH (stack_state_stack t1)`
                     STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f' + 4 <=
                   LENGTH (stack_state_stack t1)` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 2 = 2 + n0 +
       stack_state_stack_space t1 /\
                   stack_state_stack_space t1 + n0 = n0 + stack_state_stack_space t1`
       (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[EL_DROP]; ALL_TAC] THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0 (s2:(A,num#C,FFI)wl_state)
      (t1:(A,C,FFI)stack_state)
                   (CONS f' lens) n0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[wl_set_vars_def; w2sp3aux_wl_accfupds; w2sp3aux_stack_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[DOMSUB_FUPDATE; FDOM_FUPDATE; IN_INSERT] THEN REPEAT CONJ_TAC) THENL
  [(UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f' + 4 <= LENGTH
    (stack_state_stack t1)` THEN
    UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC);
   (MATCH_MP_TAC wf_alist_insert THEN MATCH_MP_TAC wf_union THEN REWRITE_TAC[wf_fromAList]);
   (SUBGOAL_THEN `the (f' + 1) (m:num option) = f' + 1` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `SOME (hh:num,hl1:num,hl2:num)`;
       `xs:((A)stack_frame)list`; `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
       `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
       stack_rel_cons_locals_size) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `stack_size_rel 0 (wl_state_locals_size (s2:(A,num#C,FFI)wl_state))
      (wl_state_stack_limit s2)
      (wl_state_stack_max s2) (wl_state_stack s2) (stack_state_stack (t1:(A,C,FFI)stack_state))
      (stack_state_stack_space t1) n0` THEN
    ASM_REWRITE_TAC[stack_size_rel_def; stack_size_eq; OPTION_MAP2_SOME] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
    [DISCH_TAC THEN UNDISCH_TAC `the (f' + 1) (m:num option) = f' + 1` THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    X_GEN_TAC `sm:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sm:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "IS_SOME" (concl th))) THEN
    ASM_REWRITE_TAC[SUB_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ss0:num` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
    UNDISCH_TAC `OPTION_MAP ((+) 3) (m:num option) = SOME x1` THEN
    UNDISCH_TAC `the (f' + 1) (m:num option) = f' + 1` THEN
    MP_TAC(ISPEC `m:num option` option_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `z:num` SUBST_ALL_TAC) SUBST_ALL_TAC) THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ; the_def; IS_SOME_DEF] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1]) THEN
   (UNDISCH_TAC `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) - stack_state_stack_space t1 -
     n0 <= sm` THEN
    UNDISCH_TAC `ss0 = x1 + x2:num` THEN
    UNDISCH_TAC `ss0 = LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) -
      stack_state_stack_space t1 - n0` THEN
    UNDISCH_TAC `z = f' + 1` THEN UNDISCH_TAC `3 + z = x1` THEN UNDISCH_TAC `f' + 1 = f`
      THEN ARITH_TAC);
   (REWRITE_TAC[FLOOKUP_UPDATE] THEN
    SUBGOAL_THEN `DROP f (DROP (((stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 3) + 0)
      (t2s:((A)word_loc)list)) =
                  DROP (f' + 4) (DROP 0 (DROP (stack_state_stack_space t1 + n0)
                    (stack_state_stack t1)))`
      SUBST1_TAC THENL
    [REWRITE_TAC[DROP_DROP_T; ADD_CLAUSES; DROP_0] THEN
     SUBGOAL_THEN `f + (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 3 =
                     (f + 3) + n0 + stack_state_stack_space t1 /\
                   (f' + 4) + stack_state_stack_space t1 + n0 = (f + 3) + n0 +
                     stack_state_stack_space t1`
       (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`; `m:num option`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `hh:num`; `hl1:num`; `hl2:num`;
       `xs:((A)stack_frame)list`;
       `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
       `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
       stack_rel_DROP_SOME) THEN
    REWRITE_TAC[DROP_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
    ASM_REWRITE_TAC[DROP_0]);
   (SUBGOAL_THEN `!i. i < LENGTH (vs:num list) ==> EL i vs = 2 * (i + 1)` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o
       check (fun th -> is_eq (concl th) && lhs (concl th) = `vs:num list`)) THEN
     ASM_SIMP_TAC[EL_LIST_OF_SEQ]; ALL_TAC] THEN
    SUBGOAL_THEN `((stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 3) + 0 =
                  (stack_state_stack_space t1 + n0) + 3` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
    CASES_ON `ALOOKUP (ZIP (vs:num list) (ys:((A)word_loc)list)) n`
      THEN CASE_REWRITE_TAC[option_INJ]) THENL
   [(DISCH_TAC THEN
    SUBGOAL_THEN `EVEN n /\ 2 * k <= n /\ n < 2 * f' + 2 * k` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[domain_lookup] THEN
     EXISTS_TAC `v:(A)word_loc` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(MEM n (vs:num list))` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`vs:num list`; `ys:((A)word_loc)list`; `n:num`] ALOOKUP_ZIP_FAIL) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (vs:num list) + 1 <= n DIV 2` ASSUME_TAC THENL
    [UNDISCH_TAC `EVEN n` THEN REWRITE_TAC[EVEN_EXISTS]
      THEN DISCH_THEN(X_CHOOSE_THEN `mm:num` SUBST_ALL_TAC) THEN
     SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
     REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
     UNDISCH_TAC `~(MEM (2 * mm) (vs:num list))` THEN REWRITE_TAC[] THEN
     SUBGOAL_THEN `2 * mm = EL (mm - 1) (vs:num list)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `mm - 1` o check (fun th -> is_forall (concl th) &&
        w2sp3aux_has_const "EL" (concl th) && not (w2sp3aux_has_const "DROP" (concl th)))) THEN
      ANTS_TAC THENL
      [UNDISCH_TAC `mm < LENGTH (vs:num list) + 1` THEN UNDISCH_TAC `2 * k <= 2 * mm` THEN
       UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `2 * k <= 2 * mm` THEN UNDISCH_TAC `4 < k`
        THEN ARITH_TAC;
      MATCH_MP_TAC MEM_EL THEN
      UNDISCH_TAC `mm < LENGTH (vs:num list) + 1` THEN UNDISCH_TAC `2 * k <= 2 * mm` THEN
      UNDISCH_TAC `4 < k` THEN ARITH_TAC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n DIV 2 < k) /\ n DIV 2 < k + f' /\ k <= n DIV 2` STRIP_ASSUME_TAC THENL
    [SIMP_TAC[RDIV_LT_EQ; LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN
     UNDISCH_TAC `2 * k <= n` THEN UNDISCH_TAC `n < 2 * f' + 2 * k` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:num`; `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `m:num option`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `hh:num`; `hl1:num`; `hl2:num`;
       `xs:((A)stack_frame)list`;
       `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`; `f':num`; `lens:num list`; `n:num`;
       `v:(A)word_loc`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`]
         W2SP3AUX_frame_lookup_SOME) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DROP_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 3 =
                  (n0 + stack_state_stack_space t1) + 3` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`f - 1 - (n DIV 2 - k)`; `f:num`; `n0 + stack_state_stack_space
      (t1:(A,C,FFI)stack_state)`;
                   `t2s:((A)word_loc)list`] W2SP3AUX_oEL_TAKE_DROP3) THEN
    ANTS_TAC THENL [UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`stack_state_stack (t1:(A,C,FFI)stack_state)`; `t2s:((A)word_loc)list`;
       `n0 + stack_state_stack_space (t1:(A,C,FFI)stack_state)`; `f + 3`; `(f + 3) - n0`;
       `(f - 1 - (n DIV 2 - k)) + 3`; `v:(A)word_loc`] W2SP3AUX_ret_keep_index) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [UNDISCH_TAC `oEL ((f' + 3) - (n DIV 2 - k)) (DROP (stack_state_stack_space
      (t1:(A,C,FFI)stack_state) + n0)
                   (stack_state_stack t1)) = SOME (v:(A)word_loc)` THEN
     SUBGOAL_THEN `(f' + 3) - (n DIV 2 - k) = (f - 1 - (n DIV 2 - k)) + 3 /\
                   stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0 = n0 +
                     stack_state_stack_space t1`
       (fun th -> REWRITE_TAC[th]) THEN
     UNDISCH_TAC `f' + 1 = f` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN UNDISCH_TAC `k <= n DIV 2`
       THEN ARITH_TAC;
     UNDISCH_TAC `LENGTH (vs:num list) + 1 <= n DIV 2` THEN UNDISCH_TAC `n DIV 2 < k + f'` THEN
     UNDISCH_TAC `k <= n DIV 2` THEN UNDISCH_TAC `(LENGTH (vs:num list) + 1) - k = n0` THEN
     UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
     UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC]);
    (DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM o check (fun th -> is_eq (concl th) &&
      w2sp3aux_has_const "ZIP" (concl th))) THEN
    ASM_SIMP_TAC[MEM_ZIP] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[PAIR_EQ] THEN
    UNDISCH_TAC `(n:num,v:(A)word_loc) = EL i vs,EL i ys` THEN ASM_SIMP_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * (i + 1)) DIV 2 = i + 1`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "FLOOKUP" (concl th) && w2sp3aux_has_const "oEL" (concl th) &&
      can (find_term ((=) `ys:((A)word_loc)list`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THENL
    [ASM_SIMP_TAC[FLOOKUP_UPDATE; ARITH_RULE `x < k ==> ~(x = k)`; ARITH_RULE `x < k ==> ~(k = x)`];
     SUBGOAL_THEN `i + 1 < k + f'` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`vs:num list`; `EL i (vs:num list)`] MAX_LIST_PROPERTY) THEN
      ASM_SIMP_TAC[MEM_EL] THEN
      UNDISCH_TAC `MAX_LIST (vs:num list) < 2 * f' + 2 * k` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`f - 1 - ((i + 1) - k)`; `f:num`; `stack_state_stack_space
       (t1:(A,C,FFI)stack_state) + n0`;
                    `t2s:((A)word_loc)list`] W2SP3AUX_oEL_TAKE_DROP3) THEN
     ANTS_TAC THENL [UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
     MP_TAC(ISPECL [`stack_state_stack (t1:(A,C,FFI)stack_state)`; `t2s:((A)word_loc)list`;
       `stack_state_stack_space (t1:(A,C,FFI)stack_state)`; `f + 3`; `n0:num`;
       `LENGTH (vs:num list) - (i + 1)`; `(f - 1 - ((i + 1) - k)) + 3`;
         `EL i (ys:((A)word_loc)list)`]
       W2SP3AUX_ret_val_index) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f' + 4 <= LENGTH
       (stack_state_stack t1)` THEN
     UNDISCH_TAC `i + 1 < k + f'` THEN UNDISCH_TAC `~(i + 1 < k)`
       THEN UNDISCH_TAC `i < LENGTH (vs:num list)` THEN
     UNDISCH_TAC `(LENGTH (vs:num list) + 1) - k = n0` THEN UNDISCH_TAC `f' + 1 = f`
       THEN ARITH_TAC])]]);;

(* An exception raised by the callee of a call with handler is caught by    *)
(* the handler frame of the call, so the handler is restored (used for     *)
(* HOL4 8166, handler case HOL4 9866)                                      *)
let W2SP3AUX_exc_swap_SOME = prove
 (`!prog (s:(A,num#C,FFI)wl_state) envs args1 ss x y s2 hv (hprog:(A)wl_prog) h1 h2.
     wl_evaluate (prog, wl_call_env args1 ss
        (wl_push_env envs (SOME (hv,hprog,h1,h2)) (wl_dec_clock s))) =
       (SOME (wl_Exception x y), s2)
     ==> wl_state_handler s2 = wl_state_handler s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs (SOME (hv,hprog,h1,h2))
       (wl_dec_clock (s:(A,num#C,FFI)wl_state)))`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_push_env_with_const; w2sp3aux_wl_accfupds;
              K_THM; wl_push_env_const] THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,num#C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `pp:num->num->num`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE_def; w2sp3aux_wl_accfupds; K_THM; LENGTH] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `LASTN (LENGTH (wl_state_stack (s:(A,num#C,FFI)wl_state)) + 1)
      (CONS (StackFrame (wl_state_locals_size s)
         (toAList (FST (envs:((A)word_loc)spt#((A)word_loc)spt))) ll (SOME
           (wl_state_handler s,h1,h2)))
        (wl_state_stack s)) = CONS (StackFrame m e0 e (SOME n)) ls` THEN
  REWRITE_TAC[GSYM ADD1] THEN SIMP_TAC[LASTN_CONS_ID] THEN
  REWRITE_TAC[CONS_11; injectivity "stack_frame"; option_INJ] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) && rhs (concl th) =
    `n:num#num#num`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `wl_state_handler (s2:(A,num#C,FFI)wl_state)`)) THEN
  CASE_REWRITE_TAC[]);;

(* The state relation at the entry of the handler of a call (used for    *)
(* HOL4 8166, handler case HOL4 9866)                                     *)
let W2SP3AUX_exc_state_rel_h = prove
 (`!ac k f f' (s2:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state) lens l0 l y.
     word_to_stackProof_state_rel ac k 0 0 (push_locals l0 l s2) t1 (CONS f' lens) 0 /\
     wl_state_locals s2 = union (fromAList l) (fromAList l0) /\
     FLOOKUP (stack_state_regs t1) 1 = SOME y /\
     f' + 1 = f /\ ~(f' = 0) /\
     (!n. n IN domain (wl_state_locals s2) ==> EVEN n /\ 2 * k <= n /\ n < 2 * f' + 2 * k)
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_var 2 y s2) t1 lens 0`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0 (push_locals l0 l (s2:(A,num#C,FFI)wl_state))
                   (t1:(A,C,FFI)stack_state) (CONS f' lens) 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def; push_locals_def; wl_set_var_def;
      w2sp3aux_wl_accfupds; K_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THENL
  [(MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`;
    `wl_state_locals_size (s2:(A,num#C,FFI)wl_state)`;
                   `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
                     `wl_state_stack (s2:(A,num#C,FFI)wl_state)`;
                   `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
                   `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + 0)
                     (stack_state_stack t1))`;
                   `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
                   `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
                  stack_rel_cons_LEN_NONE) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel"
      o concl)) THEN
                    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DROP_0; LENGTH_DROP; ADD_CLAUSES] THEN
    UNDISCH_TAC `stack_state_stack_space (t1:(A,C,FFI)stack_state) + 0 <= LENGTH
      (stack_state_stack t1)` THEN
    UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC);
   (MATCH_MP_TAC wf_insert THEN MATCH_MP_TAC wf_union THEN REWRITE_TAC[wf_fromAList]);
   (SUBGOAL_THEN `the (f' + 1) (wl_state_locals_size (s2:(A,num#C,FFI)wl_state)) = f' + 1`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`;
       `wl_state_locals_size (s2:(A,num#C,FFI)wl_state)`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`; `NONE:(num#num#num)option`;
       `wl_state_stack (s2:(A,num#C,FFI)wl_state)`; `FLOOKUP (stack_state_store
         (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + 0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
       `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
       stack_rel_cons_locals_size) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `stack_size_rel 0 (SOME 0) (wl_state_stack_limit (s2:(A,num#C,FFI)wl_state))
      (wl_state_stack_max s2)
      (CONS (StackFrame (wl_state_locals_size s2) l0 l NONE) (wl_state_stack s2))
      (stack_state_stack (t1:(A,C,FFI)stack_state)) (stack_state_stack_space t1) 0` THEN
    REWRITE_TAC[stack_size_rel_def; stack_size_eq; OPTION_MAP2_SOME] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [DISCH_TAC THEN UNDISCH_TAC `the (f' + 1) (wl_state_locals_size (s2:(A,num#C,FFI)wl_state)) =
      f' + 1` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    X_GEN_TAC `sm:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sm:num` o check (fun th -> is_forall (concl th) &&
      w2sp3aux_has_const "IS_SOME" (concl th))) THEN
    ASM_REWRITE_TAC[SUB_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ss0:num` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
    UNDISCH_TAC `the (f' + 1) (wl_state_locals_size (s2:(A,num#C,FFI)wl_state)) = f' + 1` THEN
    ASM_REWRITE_TAC[the_def; IS_SOME_DEF] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1]) THEN
   (UNDISCH_TAC `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) - stack_state_stack_space
     t1 <= sm` THEN
    UNDISCH_TAC `ss0 = x1 + x2:num` THEN
    UNDISCH_TAC `ss0 = LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) -
      stack_state_stack_space t1` THEN
    UNDISCH_TAC `x1:num = f` THEN ARITH_TAC);
   (MP_TAC(ISPECL [`k:num`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`;
     `wl_state_locals_size (s2:(A,num#C,FFI)wl_state)`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
         `wl_state_stack (s2:(A,num#C,FFI)wl_state)`;
       `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + 0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`;
       `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`; `f':num`; `lens:num list`]
       stack_rel_DROP_NONE) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel"
      o concl)) THEN
                    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DROP_0]);
   (REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_INJ]
      THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN `1 < k` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `4 < k` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
     DISCH_TAC THEN
     SUBGOAL_THEN `EVEN n /\ 2 * k <= n /\ n < 2 * f' + 2 * k` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[domain_lookup] THEN
      EXISTS_TAC `v:(A)word_loc` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `~(n DIV 2 < k) /\ n DIV 2 < k + f' /\ k <= n DIV 2` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN
      UNDISCH_TAC `2 * k <= n` THEN UNDISCH_TAC `n < 2 * f' + 2 * k` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`k:num`; `stack_state_bitmaps (t1:(A,C,FFI)stack_state)`;
       `wl_state_locals_size (s2:(A,num#C,FFI)wl_state)`;
       `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
         `wl_state_stack (s2:(A,num#C,FFI)wl_state)`;
       `FLOOKUP (stack_state_store (t1:(A,C,FFI)stack_state)) Handler`;
       `DROP 0 (DROP (stack_state_stack_space (t1:(A,C,FFI)stack_state) + 0)
         (stack_state_stack t1))`;
       `LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state))`; `f':num`; `lens:num list`; `n:num`;
       `v:(A)word_loc`; `wl_state_handler (s2:(A,num#C,FFI)wl_state)`] W2SP3AUX_frame_lookup) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_has_const "word_to_stackProof_stack_rel" o concl)) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[DROP_0] THEN
     SUBGOAL_THEN `f - 1 - (n DIV 2 - k) = f' - (n DIV 2 - k) /\ f' - (n DIV 2 - k) < f`
       STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[LLOOKUP_TAKE]])]);;

(* The handler of a state after push_env with a handler (used for HOL4     *)
(* 8166, handler case HOL4 9866)                                           *)
let W2SP3AUX_push_env_handler_SOME = prove
 (`!envs (s:(A,C,FFI)wl_state) hv (hprog:(A)wl_prog) h1 h2.
     wl_state_handler (wl_push_env envs (SOME (hv,hprog,h1,h2)) s) = LENGTH (wl_state_stack s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `pp:num->num->num`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE_def; w2sp3aux_wl_accfupds; K_THM]);;

(* The Halt cases of the returning call with handler: as                  *)
(* w2sp3aux_ret_halt_tac, with the handler frame of three more slots       *)
let w2sp3aux_ret_halt_tac_h (arith_tac:tactic) : tactic =
     REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
     SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) =
                     SOME (stackSem_Halt (wl_Word (word 2))))` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      MATCH_MP_TAC compile_result_NOT_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[stack_empty_env_def; w2sp3aux_stack_accfupds; K_THM] THEN
     TRY (EXPAND_TAC "t6") THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN CONJ_TAC THENL
     [MP_TAC(MATCH_MP wl_evaluate_io_events_mono (ASSUME
        `wl_evaluate (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args (SOME (hv,hprog,h1,h2)),
                      s:(A,num#C,FFI)wl_state) = res,s1`)) THEN
      ASM_REWRITE_TAC[w2sp3aux_wl_accfupds; K_THM; wl_push_env_const];
      MATCH_MP_TAC W2SP3AUX_ret_limit THEN
      MAP_EVERY EXISTS_TAC [`vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`;
        `l1:num`; `l2:num`; `dest:num option`; `args:num list`;
        `SOME (hv,hprog,h1,h2):(num#(A)wl_prog#num#num)option`; `s:(A,num#C,FFI)wl_state`;
        `res:((A)wl_result)option`;
        `a:((A)word_loc)list`; `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`;
        `a'':((A)word_loc)spt#((A)word_loc)spt`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC W2SP3AUX_ret_overflow THEN
      MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `t5:(A,C,FFI)stack_state`; `f':num`;
        `lens:num list`; `fs:num`; `3`] THEN
      ASM_REWRITE_TAC[W2SP3AUX_push_env_stack_size] THEN arith_tac];;

(* The returning Call case with handler (HOL4 8166, handler case          *)
(* HOL4 9020-10048)                                                         *)
let W2SP3AUX_comp_correct_Call_returning_SOME = prove
 (w2sp3aux_call_returning_case true,
  (GEN_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN(fun th -> let cs = CONJUNCTS th in
        LABEL_TAC "IHret" (el 1 cs) THEN LABEL_TAC "IHexc" (el 2 cs) THEN
      LABEL_TAC "IHcall" (el 3 cs)) THEN
      REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `?vs live ret_code l1 l2. x = (vs:num
    list,live:num_set#num_set,ret_code:(A)wl_prog,l1:num,l2:num)`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
      SUBGOAL_THEN `?hv hprog h1 h2. h = (hv:num,hprog:(A)wl_prog,h1:num,h2:num)`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
      UNDISCH_TAC `word_to_stack_comp ac F (wl_Call (SOME (vs,live,ret_code,l1,l2)) dest args
                     (SOME (hv,hprog,h1,h2))) (bs,n) (k,f,f') = (sprog:(A)stack_prog,bs',n')` THEN
      REWRITE_TAC[w2sp3aux_comp_clause "wl_Call"] THEN
      MP_TAC(ISPEC `call_dest dest args (k,f,f'):(A)stack_prog#(num+num)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `q0:(A)stack_prog` (X_CHOOSE_THEN `dest':num+num` ASSUME_TAC)) THEN
      MP_TAC(ISPEC `wLive live (bs,n) (k,f,f'):(A)stack_prog#((A word)app_list#num)`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `q1:(A)stack_prog` (X_CHOOSE_THEN `bsn1:(A word)app_list#num`
        ASSUME_TAC)) THEN
      MP_TAC(ISPEC `word_to_stack_comp ac F ret_code bsn1 (k,f,f'):(A)stack_prog#((A
        word)app_list#num)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `q2:(A)stack_prog` (X_CHOOSE_THEN `bsn2:(A word)app_list#num`
        ASSUME_TAC)) THEN
      MP_TAC(ISPEC `word_to_stack_comp ac F hprog bsn2 (k,f,f'):(A)stack_prog#((A
        word)app_list#num)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `q4:(A)stack_prog` (X_CHOOSE_THEN `bsn3:(A word)app_list#num`
        ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
      ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
      ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
      ASM_REWRITE_TAC[pair_CASE_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
      STRIP_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
         rhs (concl th) = `sprog:(A)stack_prog`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
         lhs (concl th) = `bsn3:(A word)app_list#num`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; UNION_SUBSET]) THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        w2sp3aux_has_const "wl_Call" (concl th) && w2sp3aux_has_const "wl_evaluate"
          (concl th))) THEN
      REWRITE_TAC[w2sp3aux_wl_eval_clause "wl_Call"] THEN
      CASES_ON `wl_get_vars args (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
      W2SP3AUX_ERR_TAC THEN
      ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)`
        THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      W2SP3AUX_ERR_TAC THEN
      CASES_ON `wl_find_code dest (add_ret_loc (SOME (vs,live,ret_code,l1,l2):(num
        list#cutsets#(A)wl_prog#num#num)option)
        (a:((A)word_loc)list)) (wl_state_code (s:(A,num#C,FFI)wl_state))
          (wl_state_stack_size s)` THEN
      CASE_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC THEN
      MP_TAC(ISPEC `a':((A)word_loc)list#(A)wl_prog#num option` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `args1:((A)word_loc)list` (X_CHOOSE_THEN `pss:(A)wl_prog#num option`
        SUBST_ALL_TAC)) THEN
      MP_TAC(ISPEC `pss:(A)wl_prog#num option` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `prog:(A)wl_prog` (X_CHOOSE_THEN `ss:num option` SUBST_ALL_TAC)) THEN
      ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN CASE_REWRITE_TAC[] THEN
      ASM_CASES_TAC `domain (FST (live:num_set#num_set)) = {} \/ ~ALL_DISTINCT (vs:num list)` THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC THEN
      CASES_ON `cut_envs (live:num_set#num_set) (wl_state_locals (s:(A,num#C,FFI)wl_state))` THEN
      CASE_REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC) THEN
  (MP_TAC(ISPECL [`k:num`; `f':num`; `vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`;
                     `l1:num`; `l2:num`; `dest:num option`; `args:num list`;
                     `SOME (hv,hprog,h1,h2):(num#(A)wl_prog#num#num)option`]
                       W2SP3AUX_ret_convs) THEN
      ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`hv:num`; `hprog:(A)wl_prog`; `h1:num`; `h2:num`] o
        check (fun th -> is_forall (concl th) && w2sp3aux_has_const "post_alloc_conventions"
          (concl th))) THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic) THEN
      MP_TAC(ISPECL [`dest:num option`; `args:num list`; `ac:(A)asm_config`; `k:num`;
        `f:num`; `f':num`;
        `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `q0:(A)stack_prog`;
        `dest':num+num`; `a:((A)word_loc)list`;
        `SOME (vs,live,ret_code,l1,l2):(num list#cutsets#(A)wl_prog#num#num)option`]
        call_dest_lemma) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t4:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPECL [`args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`])))))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `bsc:(A word)app_list` (X_CHOOSE_THEN `ic:num`
        (X_CHOOSE_THEN `bs2:(A word)app_list` (X_CHOOSE_THEN `i2:num` (X_CHOOSE_THEN `fs:num`
        (X_CHOOSE_THEN `stack_prog:(A)stack_prog` STRIP_ASSUME_TAC))))))) THEN
  (SUBGOAL_THEN `~(f' = 0)` ASSUME_TAC THENL
      [UNDISCH_TAC `~(domain (FST (live:num_set#num_set)) = {} \/ ~ALL_DISTINCT (vs:num list))` THEN
       REWRITE_TAC[DE_MORGAN_THM; GSYM MEMBER_NOT_EMPTY] THEN
       DISCH_THEN(X_CHOOSE_TAC `y:num` o CONJUNCT1) THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> is_forall (concl th) &&
         can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th))) THEN
       ASM_REWRITE_TAC[] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`] THEN ARITH_TAC;
       ALL_TAC] THEN
      SUBGOAL_THEN `f' + 1 = f /\ 1 <= f` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `if f' = 0 then f = 0 else f = f' + 1` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
      MP_TAC(ISPEC `bsn1:(A word)app_list#num` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `bs1:(A word)app_list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
        check (w2sp3aux_is_seval_of `q0:(A)stack_prog`)) THEN
      MP_TAC(ISPEC `bsn2:(A word)app_list#num` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `bsr:(A word)app_list` (X_CHOOSE_THEN `nr:num` SUBST_ALL_TAC)) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP comp_IMP_isPREFIX o
        check (fun th -> is_eq (concl th) && w2sp3aux_has_const "word_to_stack_comp" (concl th) &&
                         can (find_term ((=) `ret_code:(A)wl_prog`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP comp_IMP_isPREFIX o
        check (fun th -> is_eq (concl th) && w2sp3aux_has_const "word_to_stack_comp" (concl th) &&
                         can (find_term ((=) `hprog:(A)wl_prog`)) (concl th))) THEN
      REWRITE_TAC[FST] THEN DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`live:num_set#num_set`; `bs:(A word)app_list`; `n:num`; `k:num`; `f:num`;
                     `f':num`; `q1:(A)stack_prog`; `bs1:(A word)app_list`; `n1:num`;
                     `ac:(A)asm_config`; `s:(A,num#C,FFI)wl_state`; `t4:(A,C,FFI)stack_state`;
                     `lens:num list`; `a'':((A)word_loc)spt#((A)word_loc)spt`] evaluate_wLive) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `y:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        X_GEN_TAC `y:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:num` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `SND (live:num_set#num_set)`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `LENGTH (stack_state_bitmaps
          (t:(A,C,FFI)stack_state))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `append (bs':(A word)app_list)` THEN
        CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC IS_PREFIX_TRANS
          THEN EXISTS_TAC `append (bsr:(A word)app_list)` THEN
                        ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC IS_PREFIX_TRANS THEN
        EXISTS_TAC `DROP (n - LENGTH (append (bs:(A word)app_list))) (stack_state_bitmaps
          (t:(A,C,FFI)stack_state))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[]];
       ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t5:(A,C,FFI)stack_state` STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `!ck (X:(A)stack_prog). stack_evaluate (stack_Seq q0 (stack_Seq q1 X),
           stack_state_clock_fupd (K (stack_state_clock t + ck)) (t:(A,C,FFI)stack_state)) =
         stack_evaluate (X, stack_state_clock_fupd (K (stack_state_clock t + ck))
           (t5:(A,C,FFI)stack_state))`
        ASSUME_TAC THENL
      [REPEAT GEN_TAC THEN REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
       FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP evaluate_call_dest_clock th]) o
         check (fun th -> is_eq(concl th) && w2sp3aux_has_const "call_dest" (concl th))) THEN
       ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND] THEN
       FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP evaluate_wLive_clock th]) o
         check (fun th -> is_eq(concl th) && w2sp3aux_has_const "wLive" (concl th))) THEN
       ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND];
       ALL_TAC] THEN
      ASM_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_length_lemma o
        check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_get_vars" (concl th))) THEN
      MP_TAC(ISPECL [`dest:num option`; `args:num list`; `a:((A)word_loc)list`;
        `wl_state_code (s:(A,num#C,FFI)wl_state)`; `wl_state_stack_size (s:(A,num#C,FFI)wl_state)`;
        `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`; `k:num`; `f:num`; `f':num`;
        `q0:(A)stack_prog`; `dest':num+num`; `l1:num`; `l2:num`] W2SP3AUX_ret_args) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && w2sp3aux_has_const "wl_find_code"
         (concl th))) THEN
       REWRITE_TAC[add_ret_loc_def] THEN SIMP_TAC[];
       STRIP_TAC] THEN
      ABBREV_TAC `sac = LENGTH (args1:((A)word_loc)list) - k` THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
        check (fun th -> can (find_term ((=) `t5:(A,C,FFI)stack_state`)) (concl th) &&
                         can (find_term ((=) `lens:num list`)) (concl th) &&
                         not (can (find_term ((=) `CONS (f':num) lens`)) (concl th)))) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP3AUX_compile_prog_unfold o
         check (w2sp3aux_has_const "word_to_stack_compile_prog" o concl)) THEN
      DISCH_THEN(X_CHOOSE_THEN `qc:(A)stack_prog` (X_CHOOSE_THEN `svc:num`
         (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
           STRIP_ASSUME_TAC)))) THEN
      SUBGOAL_THEN `sac <= fs /\ sac <= svc` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `MAX ((max_var (prog:(A)wl_prog) DIV 2 + 1) - k) (LENGTH
        (args1:((A)word_loc)list) - k) = svc` THEN
       UNDISCH_TAC `(if svc = 0 then 0 else svc + 1) = fs` THEN
       UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
       REWRITE_TAC[MAX] THEN ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
      REWRITE_TAC[evaluate_PushHandler_clock]) THEN
  (ASM_CASES_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) < 3` THENL
      [SUBGOAL_THEN `stack_evaluate (PushHandler F h1 h2
        (k:num,f:num,f':num),t5:(A,C,FFI)stack_state) =
                     (SOME (stackSem_Halt (wl_Word (word 2))), stack_empty_env t5)` (fun th ->
                       REWRITE_TAC[th]) THENL
       [REWRITE_TAC[PushHandler_F] THEN ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
        REWRITE_TAC[w2sp3aux_seval "StackAlloc"] THEN ASM_REWRITE_TAC[pair_CASE_def;
          option_DISTINCT];
        ALL_TAC] THEN
       DISCH_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[pair_CASE_def; FST; SND; option_DISTINCT] THEN
       w2sp3aux_ret_halt_tac_h (UNDISCH_TAC `stack_state_stack_space
         (t:(A,C,FFI)stack_state) < 3` THEN
         ARITH_TAC);
       ALL_TAC]) THEN
  (SUBGOAL_THEN `(h1:num,h2:num) IN loc_check (stack_state_code (t:(A,C,FFI)stack_state))`
    ASSUME_TAC THENL
      [FIRST_ASSUM(MP_TAC o check (fun th -> is_conj (concl th) && w2sp3aux_has_const
        "stack_get_labels" (concl th) &&
         can (find_term ((=) `q0:(A)stack_prog`)) (concl th))) THEN
       REWRITE_TAC[PushHandler_F; stack_get_labels_def] THEN
       CASE_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_SUBSET; UNION_SUBSET] THEN STRIP_TAC THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
        check (w2sp3aux_is_seval_of `q1:(A)stack_prog`)) THEN
      SUBGOAL_THEN `(h1:num,h2:num) IN loc_check (stack_state_code (t5:(A,C,FFI)stack_state))`
        (ASSUME_TAC o REWRITE_RULE[IN]) THENL
      [SUBGOAL_THEN `loc_check (stack_state_code (t:(A,C,FFI)stack_state)) SUBSET
                     loc_check (stack_state_code (t5:(A,C,FFI)stack_state))` MP_TAC THENL
       [MATCH_MP_TAC loc_check_SUBSET THEN MATCH_MP_TAC (GEN_ALL subspt_trans) THEN
        EXISTS_TAC `stack_state_code (t4:(A,C,FFI)stack_state)` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
      MP_TAC(ISPECL [`t5:(A,C,FFI)stack_state`; `ac:(A)asm_config`; `k:num`;
                     `a'':((A)word_loc)spt#((A)word_loc)spt`; `s:(A,num#C,FFI)wl_state`; `f':num`;
                     `lens:num list`; `h1:num`; `h2:num`; `f:num`; `hv:num`; `hprog:(A)wl_prog`]
                    evaluate_PushHandler) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(stack_state_stack_space
        (t:(A,C,FFI)stack_state) < 3)` THEN
       ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tp:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (fun th -> MAP_EVERY (fun f -> ASSUME_TAC
            (REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM] (AP_TERM f th)))
            [`stack_state_clock:(A,C,FFI)stack_state->num`;
             `stack_state_code:(A,C,FFI)stack_state->((A)stack_prog)spt`;
             `stack_state_bitmaps:(A,C,FFI)stack_state->(A word)list`])
          STRIP_ASSUME_TAC))) THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq (concl th) &&
        w2sp3aux_has_const "PushHandler" (concl th))) THEN
      REWRITE_TAC[pair_CASE_def; FST; SND]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
        check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
                         can (find_term ((=) `tp:(A,C,FFI)stack_state`)) (concl th))) THEN
      REWRITE_TAC[StackHandlerArgs_F; StackArgs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
      ONCE_REWRITE_TAC[evaluate_stack_move_seq] THEN
      ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
      REWRITE_TAC[w2sp3aux_seval "StackAlloc"; w2sp3aux_stack_accfupds] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `stack_state_stack_space (tp:(A,C,FFI)stack_state) < sac` THENL
      [DISCH_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; pair_CASE_def;
        option_DISTINCT] THEN
       CASE_REWRITE_TAC[] THEN
       w2sp3aux_ret_halt_tac_h (UNDISCH_TAC `stack_state_stack_space
         (tp:(A,C,FFI)stack_state) < sac` THEN
         UNDISCH_TAC `stack_state_stack_space (tp:(A,C,FFI)stack_state) + 3 =
           stack_state_stack_space (t5:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) = stack_state_stack_space
           (t4:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) = stack_state_stack_space
           (t:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `sac <= fs` THEN ARITH_TAC);
       ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (args:num list) < f' + k` ASSUME_TAC THENL
      [UNDISCH_TAC `MAX_LIST (args:num list) < 2 * f' + 2 * k` THEN
       FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) o
         check (fun th -> is_eq (concl th) && lhs (concl th) = `args:num list`)) THEN
       REWRITE_TAC[MAX_LIST_GENLIST_evens2; LENGTH_LIST_OF_SEQ] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `sac <= f /\ sac <= stack_state_stack_space (tp:(A,C,FFI)stack_state)`
        STRIP_ASSUME_TAC THENL
      [CONJ_TAC THENL
       [UNDISCH_TAC `LENGTH (args:num list) < f' + k` THEN
        UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) <= LENGTH (args:num list) + 1` THEN
        UNDISCH_TAC `LENGTH (args1:((A)word_loc)list) - k = sac` THEN
        UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
        UNDISCH_TAC `~(stack_state_stack_space (tp:(A,C,FFI)stack_state) < sac)` THEN ARITH_TAC];
       ALL_TAC] THEN
      ASM_REWRITE_TAC[pair_CASE_def] THEN
      ABBREV_TAC `t6 = stack_state_stack_space_fupd (K (stack_state_stack_space
        (tp:(A,C,FFI)stack_state) - sac))
                         (tp:(A,C,FFI)stack_state)` THEN
      SUBGOAL_THEN `!ck. stack_state_stack_space_fupd (K (stack_state_stack_space
        (tp:(A,C,FFI)stack_state) - sac))
           (stack_state_clock_fupd (K (stack_state_clock (t:(A,C,FFI)stack_state) + ck)) tp) =
           stack_state_clock_fupd (K (stack_state_clock t + ck)) t6` (fun th ->
             REWRITE_TAC[th]) THENL
      [EXPAND_TAC "t6" THEN SIMP[]; ALL_TAC] THEN
      REWRITE_TAC[CONV_RULE (TOP_DEPTH_CONV let_CONV) evaluate_stack_move_clock] THEN
      MP_TAC(ISPECL [`sac:num`; `0`; `t6:(A,C,FFI)stack_state`; `f + 3`;
        `k:num`] evaluate_stack_move) THEN
      ANTS_TAC THENL
      [EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + f <= LENGTH
         (stack_state_stack t)` THEN
       UNDISCH_TAC `stack_state_stack_space (tp:(A,C,FFI)stack_state) + 3 = stack_state_stack_space
         (t5:(A,C,FFI)stack_state)` THEN
       UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) = stack_state_stack_space
         (t4:(A,C,FFI)stack_state)` THEN
       UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) = stack_state_stack_space
         (t:(A,C,FFI)stack_state)` THEN
       UNDISCH_TAC `sac <= stack_state_stack_space (tp:(A,C,FFI)stack_state)` THEN
       UNDISCH_TAC `sac <= f` THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t7:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t7s:((A)word_loc)list` (X_CHOOSE_THEN `t7r:(num,(A)word_loc)fmap`
          STRIP_ASSUME_TAC)))) THEN
      ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
      REWRITE_TAC[w2sp3aux_seval "stack_Skip"; pair_CASE_def]) THEN
  (MP_TAC(ISPECL [`dest:num option`; `args:num list`; `k:num`; `f:num`; `f':num`;
    `q0:(A)stack_prog`;
        `dest':num+num`; `stack_state_regs (t4:(A,C,FFI)stack_state)`;
          `stack_state_code (t4:(A,C,FFI)stack_state)`;
        `t7r:(num,(A)word_loc)fmap`; `stack_state_code (t5:(A,C,FFI)stack_state)`;
          `stack_prog:(A)stack_prog`]
        W2SP3AUX_ret_find_code) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
       X_GEN_TAC `i:num` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
         can (find_term ((=) `t7:(A,C,FFI)stack_state`)) (concl th))) THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
         can (find_term ((=) `tp:(A,C,FFI)stack_state`)) (concl th) &&
         can (find_term ((=) `t5:(A,C,FFI)stack_state`)) (concl th))) THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
         can (find_term ((=) `t5:(A,C,FFI)stack_state`)) (concl th) &&
         can (find_term ((=) `t4:(A,C,FFI)stack_state`)) (concl th))) THEN
       ASM_REWRITE_TAC[stack_get_var_def] THEN EXPAND_TAC "t6" THEN
       REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN SIMP_TAC[];
       DISCH_TAC] THEN
      ASM_REWRITE_TAC[w2sp3aux_seval "stack_Call"; w2sp3aux_stack_accfupds; K_THM] THEN
      SUBGOAL_THEN `stack_state_code (t6:(A,C,FFI)stack_state) = stack_state_code
        (t5:(A,C,FFI)stack_state)`
        (fun th -> REWRITE_TAC[th]) THENL
      [EXPAND_TAC "t6" THEN ASM_REWRITE_TAC[w2sp3aux_stack_accfupds]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (ASM_CASES_TAC `stack_state_clock (t:(A,C,FFI)stack_state) = 0` THENL
      [ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
       EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
       CASE_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN
       REWRITE_TAC[wl_flush_state_def; stack_empty_env_def; w2sp3aux_wl_accfupds;
                   w2sp3aux_stack_accfupds; K_THM] THEN
       EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds] THEN
       ASM_REWRITE_TAC[w2sp3aux_wl_accfupds; K_THM; wl_push_env_const];
       ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `wl_evaluate (prog:(A)wl_prog, wl_call_env args1 ss
         (wl_push_env (a'':((A)word_loc)spt#((A)word_loc)spt) (SOME (2,hprog,h1,h2)) (wl_dec_clock
           (s:(A,num#C,FFI)wl_state))))`
         PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `r':((A)wl_result)option` (X_CHOOSE_THEN `s2':(A,num#C,FFI)wl_state`
         ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
      REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackAlloc"; stack_dec_clock_def;
                  stack_set_var_def; w2sp3aux_stack_accfupds; K_THM] THEN
      EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[]) THEN
  (ASM_CASES_TAC `stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac < fs - sac` THENL
      [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; pair_CASE_def; option_DISTINCT] THEN
       CASE_REWRITE_TAC[] THEN
       w2sp3aux_ret_halt_tac_h (UNDISCH_TAC `stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac
         < fs - sac` THEN
         UNDISCH_TAC `sac <= stack_state_stack_space (tp:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `stack_state_stack_space (tp:(A,C,FFI)stack_state) + 3 =
           stack_state_stack_space (t5:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) = stack_state_stack_space
           (t4:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) = stack_state_stack_space
           (t:(A,C,FFI)stack_state)` THEN
         ARITH_TAC);
       ALL_TAC]) THEN
  (SUBGOAL_THEN
       `LENGTH (t7s:((A)word_loc)list) = LENGTH (stack_state_stack (tp:(A,C,FFI)stack_state)) /\
        DROP (stack_state_stack_space tp) t7s = DROP (stack_state_stack_space tp)
          (stack_state_stack tp) /\
        (!x. x < sac
             ==> EL (x + f + 3) (DROP (stack_state_stack_space tp - sac) (stack_state_stack tp)) =
                 EL x (DROP (stack_state_stack_space tp - sac) t7s)) /\
        (!i. ~(i = k) ==> FLOOKUP (t7r:(num,(A)word_loc)fmap) i = FLOOKUP (stack_state_regs tp) i)`
       STRIP_ASSUME_TAC THENL
      [SUBGOAL_THEN `stack_state_stack_space (t6:(A,C,FFI)stack_state) = stack_state_stack_space
        (tp:(A,C,FFI)stack_state) - sac /\
                     stack_state_stack t6 = stack_state_stack (tp:(A,C,FFI)stack_state) /\
                     stack_state_regs t6 = stack_state_regs tp` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "t6" THEN REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM]; ALL_TAC] THEN
       REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `LENGTH (stack_state_stack (t6:(A,C,FFI)stack_state)) = LENGTH
         (t7s:((A)word_loc)list)` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
        UNDISCH_TAC `DROP (stack_state_stack_space (t7:(A,C,FFI)stack_state) + 0 + sac) t7s =
                     DROP (stack_state_stack_space (t6:(A,C,FFI)stack_state) + 0 + sac)
                       (stack_state_stack t6)` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        SUBGOAL_THEN `stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac + sac =
          stack_state_stack_space tp`
          (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `sac <= stack_state_stack_space (tp:(A,C,FFI)stack_state)` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_let (concl th))) THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `t7:(A,C,FFI)stack_state`)) (concl th))) THEN
        ASM_REWRITE_TAC[stack_get_var_def; w2sp3aux_stack_accfupds; K_THM]];
       ALL_TAC]) THEN
  (SUBGOAL_THEN `!n v. lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME v
         ==> EVEN n /\
             (if n DIV 2 < k then FLOOKUP (stack_state_regs (t5:(A,C,FFI)stack_state)) (n
               DIV 2) = SOME v
              else oEL (f - 1 - (n DIV 2 - k)) (TAKE f (DROP (stack_state_stack_space t5 + 0)
                (stack_state_stack t5))) =
                   SOME v /\ n DIV 2 < k + f')` ASSUME_TAC THENL
      [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
        (t5:(A,C,FFI)stack_state) lens 0` THEN
       REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!n v. lookup n (wl_state_locals (s:(A,num#C,FFI)wl_state)) = SOME v
         ==> EVEN n /\
             (if n DIV 2 < k then FLOOKUP (stack_state_regs (tp:(A,C,FFI)stack_state)) (n
               DIV 2) = SOME v
              else oEL ((f + 3) - 1 - (n DIV 2 - k))
                     (TAKE (f + 3) (DROP (stack_state_stack_space tp) (stack_state_stack
                       tp))) = SOME v /\
                   n DIV 2 - k < f + 3)` ASSUME_TAC THENL
      [X_GEN_TAC `nn:num` THEN X_GEN_TAC `vv:(A)word_loc` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPECL [`nn:num`; `vv:(A)word_loc`] o check (fun th -> is_forall
         (concl th) &&
         w2sp3aux_has_const "oEL" (concl th) && can (find_term ((=) `t5:(A,C,FFI)stack_state`))
           (concl th))) THEN
       ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `nn DIV 2` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `tp:(A,C,FFI)stack_state`)) (concl th) &&
          w2sp3aux_has_const "stack_get_var" (concl th))) THEN
        ANTS_TAC THENL [UNDISCH_TAC `nn DIV 2 < k` THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[stack_get_var_def] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [MATCH_MP_TAC W2SP3AUX_push_shift THEN
         MAP_EVERY EXISTS_TAC [`stack_state_stack (t5:(A,C,FFI)stack_state)`;
                               `stack_state_stack_space (t5:(A,C,FFI)stack_state)`] THEN
         ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `nn DIV 2 < k + f'` THEN UNDISCH_TAC `~(nn DIV 2 < k)` THEN
          UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC;
          FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "oEL" (concl th) &&
            not (is_forall (concl th)))) THEN REWRITE_TAC[ADD_CLAUSES]];
         UNDISCH_TAC `nn DIV 2 < k + f'` THEN UNDISCH_TAC `~(nn DIV 2 < k)` THEN
         UNDISCH_TAC `f' + 1 = f` THEN ARITH_TAC]];
       ALL_TAC]) THEN
  (MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f + 3`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                     `SOME (hv,hprog,h1,h2):(num#(A)wl_prog#num#num)option`;
                     `tp:(A,C,FFI)stack_state`; `lens:num list`; `args:num list`;
                       `a:((A)word_loc)list`;
                     `args1:((A)word_loc)list`; `a'':((A)word_loc)spt#((A)word_loc)spt`;
                       `ss:num option`;
                     `fs:num`; `svc:num`; `sac:num`; `t7s:((A)word_loc)list`;
                       `t7r:(num,(A)word_loc)fmap`;
                     `l1:num`; `l2:num`] W2SP3AUX_ret_callee_rel_gen) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [UNDISCH_TAC `(if svc = 0 then 0 else svc + 1) = fs` THEN ARITH_TAC;
        UNDISCH_TAC `sac <= f` THEN ARITH_TAC;
        UNDISCH_TAC `~(stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac < fs - sac)` THEN
        UNDISCH_TAC `sac <= stack_state_stack_space (tp:(A,C,FFI)stack_state)` THEN
        UNDISCH_TAC `sac <= fs` THEN ARITH_TAC];
       DISCH_TAC]) THEN
  (SUBGOAL_THEN `~(r' = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
      [DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
         rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
         not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
       DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                     `t:(A,C,FFI)stack_state`; `lens:num list`; `0`; `dest:num option`;
                     `add_ret_loc (SOME (vs,live,ret_code,l1,l2):(num
                       list#cutsets#(A)wl_prog#num#num)option)
                        (a:((A)word_loc)list)`;
                     `args1:((A)word_loc)list`; `prog:(A)wl_prog`;
                       `ss:num option`] W2SP3AUX_find_code_conv) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `stack_get_labels (qc:(A)stack_prog) SUBSET loc_check (stack_state_code
        (t5:(A,C,FFI)stack_state))`
        ASSUME_TAC THENL
      [MP_TAC(MATCH_MP find_code_IMP_get_labels (ASSUME
         `stack_find_code dest' ((t7r:(num,(A)word_loc)fmap) \\ 0) (stack_state_code
           (t5:(A,C,FFI)stack_state)) = SOME (stack_prog:(A)stack_prog)`)) THEN
       ASM_REWRITE_TAC[stack_get_labels_def; UNION_SUBSET] THEN SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `stack_state_bitmaps (t:(A,C,FFI)stack_state) <<= stack_state_bitmaps
        (t5:(A,C,FFI)stack_state)`
        ASSUME_TAC THENL
      [MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `stack_state_bitmaps
        (t4:(A,C,FFI)stack_state)` THEN
       ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[ASSUME `hv = 2`] o check (fun th ->
        w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
        can (find_term ((=) `svc:num`)) (concl th))) THEN
      REMOVE_THEN "IHcall" (MP_TAC o SPECL [`a:((A)word_loc)list`; `ret_code:(A)wl_prog`;
        `l1:num`; `l2:num`;
        `vs:num list`; `live:num_set#num_set`; `prog:(A)wl_prog`; `args1:((A)word_loc)list`;
          `ss:num option`;
        `a'':((A)word_loc)spt#((A)word_loc)spt`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`k:num`; `fs:num`; `svc:num`; `r':((A)wl_result)option`;
        `s2':(A,num#C,FFI)wl_state`;
        `stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
           (stack_state_stack_fupd (K t7s)
             (stack_state_stack_space_fupd (K (stack_state_stack_space
               (tp:(A,C,FFI)stack_state) - fs))
               (stack_state_clock_fupd (K (stack_state_clock tp - 1)) tp)))`;
        `bsc:(A word)app_list`; `ic:num`; `bs2:(A word)app_list`; `i2:num`; `qc:(A)stack_prog`;
        `CONS (f':num) lens`]) THEN
      ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
      ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IS_PREFIX_TRANS THEN
        EXISTS_TAC `DROP (ic - LENGTH (append (bsc:(A word)app_list)))
                      (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          w2sp3aux_has_const "MAX" (concl th) && rhs (concl th) = `svc:num`)) THEN
        MATCH_MP_TAC W2SP3AUX_max_var_svc THEN ASM_REWRITE_TAC[]];
       ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t1:(A,C,FFI)stack_state`
        (X_CHOOSE_THEN `res1:((A)stack_result)option` STRIP_ASSUME_TAC)))) THEN
  (ASM_CASES_TAC `~(((?a0 ys. r' = SOME (wl_Result a0 ys:(A)wl_result)) \/
                         (?a0 y. r' = SOME (wl_Exception a0 y:(A)wl_result))) /\
                        OPTION_MAP compile_result r' = (res1:((A)stack_result)option))`) THENL
  [(EXISTS_TAC `ck:num` THEN
       SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) + ck = 0)` (fun th ->
         REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)`
         THEN ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[pair_CASE_def] THEN
       SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck =
                     (stack_state_clock (t:(A,C,FFI)stack_state) + ck) - 1 /\
                     stack_state_stack_space (tp:(A,C,FFI)stack_state) - fs =
                     (stack_state_stack_space tp - sac) - (fs - sac)`
         STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) = stack_state_clock
         (t:(A,C,FFI)stack_state) /\
                      stack_state_stack_space t5 = stack_state_stack_space t` STRIP_ASSUME_TAC THENL
        [CONJ_TAC THENL
         [UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
           (t5:(A,C,FFI)stack_state)` THEN
          UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
            (t:(A,C,FFI)stack_state)` THEN
          ARITH_TAC;
          UNDISCH_TAC `stack_state_stack_space (t5:(A,C,FFI)stack_state) = stack_state_stack_space
            (t4:(A,C,FFI)stack_state)` THEN
          UNDISCH_TAC `stack_state_stack_space (t4:(A,C,FFI)stack_state) = stack_state_stack_space
            (t:(A,C,FFI)stack_state)` THEN
          ARITH_TAC];
         ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN
        UNDISCH_TAC `sac <= fs` THEN UNDISCH_TAC `sac <= stack_state_stack_space
          (tp:(A,C,FFI)stack_state)` THEN
        ARITH_TAC; ALL_TAC] THEN
       FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_is_seval_of `qc:(A)stack_prog`)) THEN
       REWRITE_TAC[ASSUME `stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck =
                     (stack_state_clock (t:(A,C,FFI)stack_state) + ck) - 1`;
                   ASSUME `stack_state_stack_space (tp:(A,C,FFI)stack_state) - fs =
                     (stack_state_stack_space tp - sac) - (fs - sac)`] THEN
       EXPAND_TAC "t6" THEN SIMP[] THEN DISCH_TAC THEN SIMP[]) THEN
   (SUBGOAL_THEN `stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac - (fs - sac) =
                     stack_state_stack_space tp - fs` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `sac <= fs` THEN UNDISCH_TAC `sac <= stack_state_stack_space
         (tp:(A,C,FFI)stack_state)` THEN
        ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[pair_CASE_def; FST; SND]) THEN
   (MP_TAC(ISPECL [`vs:num list`; `live:num_set#num_set`; `ret_code:(A)wl_prog`; `l1:num`; `l2:num`;
         `dest:num option`; `args:num list`; `SOME (hv,hprog,h1,h2):(num#(A)wl_prog#num#num)option`;
         `s:(A,num#C,FFI)wl_state`; `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`;
         `a:((A)word_loc)list`; `args1:((A)word_loc)list`; `prog:(A)wl_prog`; `ss:num option`;
         `a'':((A)word_loc)spt#((A)word_loc)spt`; `r':((A)wl_result)option`;
           `s2':(A,num#C,FFI)wl_state`]
         W2SP3AUX_ret_cont_mono) THEN
       ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
       ASM_CASES_TAC `OPTION_MAP compile_result (r':((A)wl_result)option) = res1` THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th) &&
          w2sp3aux_has_const "stackSem_Halt" (concl th) &&
          can (find_term ((=) `r':((A)wl_result)option`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
        SUBGOAL_THEN `~(OPTION_MAP compile_result (res:((A)wl_result)option) =
                        SOME (stackSem_Halt (wl_Word (word 2))))` (fun th -> REWRITE_TAC[th]) THENL
        [MP_TAC(ISPEC `res:((A)wl_result)option` option_CASES) THEN STRIP_TAC THEN
         ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
         MATCH_MP_TAC compile_result_NOT_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC IS_PREFIX_TRANS THEN
         EXISTS_TAC `ffi_state_io_events (wl_state_ffi (s2':(A,num#C,FFI)wl_state))` THEN
         ASM_REWRITE_TAC[];
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]) THEN
   (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
         rhs (concl th) = `res1:((A)stack_result)option`)) THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th) &&
          w2sp3aux_has_const "stackSem_Halt" (concl th) &&
          can (find_term ((=) `r':((A)wl_result)option`)) (concl th))) THEN
       REWRITE_TAC[] THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
          not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
       MP_TAC(ISPEC `r':((A)wl_result)option` option_CASES) THEN
       DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)
         SUBST_ALL_TAC) THEN
       CASE_REWRITE_TAC[PAIR_EQ] THENL
       [ALL_TAC; DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
       REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
         (ISPEC `rr:(A)wl_result` (cases "wl_result")) THEN
       CASE_REWRITE_TAC[PAIR_EQ; OPTION_MAP_DEF; compile_result_def] THENL
       [DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
          w2sp3aux_has_const "wl_Result" (concl th) && w2sp3aux_has_const "wl_Exception"
            (concl th))) THEN
        REWRITE_TAC[option_INJ; injectivity "wl_result"; distinctness "wl_result"] THEN MESON_TAC[];
        DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
          w2sp3aux_has_const "wl_Result" (concl th) && w2sp3aux_has_const "wl_Exception"
            (concl th))) THEN
        REWRITE_TAC[option_INJ; injectivity "wl_result"; distinctness "wl_result"] THEN MESON_TAC[];
        W2SP3AUX_ERR_TAC; W2SP3AUX_ERR_TAC;
        w2sp3aux_ret_pass_tac; w2sp3aux_ret_pass_tac; w2sp3aux_ret_pass_tac; W2SP3AUX_ERR_TAC]);
   (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) && is_neg (dest_neg (concl th)))) THEN
       REWRITE_TAC[] THEN
       DISCH_THEN(fun th -> ASSUME_TAC (CONJUNCT2 th) THEN DISJ_CASES_THEN2
         (X_CHOOSE_THEN `x0:(A)word_loc` (X_CHOOSE_THEN `ys:((A)word_loc)list` SUBST_ALL_TAC))
         (X_CHOOSE_THEN `x0:(A)word_loc` (X_CHOOSE_THEN `y0:(A)word_loc` SUBST_ALL_TAC))
           (CONJUNCT1 th))) THENL
   [(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `res1:((A)stack_result)option`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; compile_result_def]) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel"
          (concl th) &&
          can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th) && not (is_forall
            (concl th)) &&
          w2sp3aux_has_const "push_locals" (concl th))) THEN
        CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
           rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
           not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
        CASE_REWRITE_TAC[] THEN
        COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
        CASES_ON `wl_pop_env (s2':(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THENL
        [REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC; ALL_TAC] THEN
        COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC] THEN
        DISCH_TAC) THEN
    (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
          can (find_term ((=) `x0:(A)word_loc`)) (concl th))) THEN
        MP_TAC(ISPECL [`prog:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`;
          `a'':((A)word_loc)spt#((A)word_loc)spt`;
                       `args1:((A)word_loc)list`; `ss:num option`; `x0:(A)word_loc`;
                         `ys:((A)word_loc)list`;
                       `s2':(A,num#C,FFI)wl_state`; `2`; `hprog:(A)wl_prog`; `h1:num`; `h2:num`]
                      W2SP3AUX_ret_swap_SOME) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `mm:num option` (X_CHOOSE_THEN `ll0:(num#(A)word_loc)list`
          (X_CHOOSE_THEN `ll:(num#(A)word_loc)list` (X_CHOOSE_THEN `xss:((A)stack_frame)list`
            ASSUME_TAC)))) THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP3AUX_state_rel_basic o
          check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
                           can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th))) THEN
        MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `s2':(A,num#C,FFI)wl_state`;
          `t1:(A,C,FFI)stack_state`;
                       `f':num`; `lens:num list`; `LENGTH (ys:((A)word_loc)list) - (k - 1)`;
                         `mm:num option`;
                       `ll0:(num#(A)word_loc)list`; `ll:(num#(A)word_loc)list`;
                       `wl_state_handler (s:(A,num#C,FFI)wl_state)`; `h1:num`; `h2:num`;
                       `xss:((A)stack_frame)list`]
                      W2SP3AUX_ret_frame_len_SOME) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `LENGTH (ys:((A)word_loc)list) - (k - 1) = (LENGTH (vs:num list) + 1) - k /\
                      LENGTH (vs:num list) - (k - 1) = (LENGTH (vs:num list) + 1) - k`
          (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
        [UNDISCH_TAC `LENGTH (ys:((A)word_loc)list) = LENGTH (vs:num list)` THEN
         UNDISCH_TAC `4 < k` THEN ARITH_TAC; ALL_TAC] THEN
        ABBREV_TAC `n0 = (LENGTH (vs:num list) + 1) - k` THEN
        MP_TAC(ISPECL [`k:num`; `f + 3`; `n0:num`; `t1:(A,C,FFI)stack_state`]
                      evaluate_copy_ret_aux) THEN
        ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
         UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f' + 4 <=
                      LENGTH (stack_state_stack t1)` THEN UNDISCH_TAC `f' + 1 = f`
                        THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `t2s:((A)word_loc)list` (X_CHOOSE_THEN `t2r:(num,(A)word_loc)fmap`
            STRIP_ASSUME_TAC))))) THEN
    (SUBGOAL_THEN `LENGTH (ys:((A)word_loc)list) - (k - 1) = n0` ASSUME_TAC THENL
        [UNDISCH_TAC `LENGTH (ys:((A)word_loc)list) = LENGTH (vs:num list)` THEN
         UNDISCH_TAC `(LENGTH (vs:num list) + 1) - k = n0` THEN UNDISCH_TAC `4 < k`
           THEN ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`live:num_set#num_set`; `wl_state_locals (s:(A,num#C,FFI)wl_state)`;
                       `a'':((A)word_loc)spt#((A)word_loc)spt`] W2SP3AUX_cut_envs_domain) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s2':(A,num#C,FFI)wl_state`;
                       `t1:(A,C,FFI)stack_state`; `lens:num list`; `ys:((A)word_loc)list`;
                         `vs:num list`;
                       `a''':(A,num#C,FFI)wl_state`; `mm:num option`; `ll0:(num#(A)word_loc)list`;
                       `ll:(num#(A)word_loc)list`; `wl_state_handler (s:(A,num#C,FFI)wl_state)`;
                         `h1:num`; `h2:num`;
                       `xss:((A)stack_frame)list`; `t2s:((A)word_loc)list`;
                       `t2r:(num,(A)word_loc)fmap`;
                       `EL ((stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 2)
                         (t2s:((A)word_loc)list)`;
                       `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + 3`]
                         W2SP3AUX_ret_state_rel_h) THEN
        ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [X_GEN_TAC `nn:num` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
            can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th) &&
            w2sp3aux_has_const "DIV" (concl th))) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
            can (find_term ((=) `SND (live:num_set#num_set)`)) (concl th) &&
            w2sp3aux_has_const "DIV" (concl th))) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`];
          UNDISCH_TAC `DROP ((f + 3) + n0 + stack_state_stack_space (t2:(A,C,FFI)stack_state)) t2s =
                       DROP ((f + 3) + n0 + stack_state_stack_space (t1:(A,C,FFI)stack_state))
                         (stack_state_stack t1)` THEN
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
            can (find_term ((=) `t2s:((A)word_loc)list`)) (concl th) && w2sp3aux_has_const "EL"
              (concl th) &&
            not (is_let (concl th)))) THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o check (fun th -> is_let (concl th) &&
            can (find_term ((=) `t2s:((A)word_loc)list`)) (concl th))) THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
          X_GEN_TAC `i:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
            can (find_term ((=) `t2:(A,C,FFI)stack_state`)) (concl th) &&
            w2sp3aux_has_const "stack_get_var" (concl th))) THEN
          ASM_REWRITE_TAC[stack_get_var_def; w2sp3aux_stack_accfupds; K_THM]];
         DISCH_TAC]) THEN
    (SUBGOAL_THEN `stack_get_labels (q2:(A)stack_prog) SUBSET loc_check (stack_state_code
      (t:(A,C,FFI)stack_state))`
          ASSUME_TAC THENL
        [FIRST_ASSUM(MP_TAC o check (fun th -> is_conj (concl th) && w2sp3aux_has_const
          "stack_get_labels" (concl th) &&
           can (find_term ((=) `q0:(A)stack_prog`)) (concl th))) THEN
         CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_get_labels_def; get_labels_copy_ret;
           PopHandler_F; UNION_SUBSET;
           INSERT_SUBSET; UNION_EMPTY; EMPTY_SUBSET] THEN
         SIMP_TAC[]; ALL_TAC] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
          check (w2sp3aux_is_seval_of `qc:(A)stack_prog`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM])) THEN
    (SUBGOAL_THEN `subspt (stack_state_code (t:(A,C,FFI)stack_state)) (stack_state_code
      (t1:(A,C,FFI)stack_state)) /\
                      stack_state_bitmaps t <<= stack_state_bitmaps t1`
          STRIP_ASSUME_TAC THENL
        [CONJ_TAC THENL
         [MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC
           `stack_state_code (tp:(A,C,FFI)stack_state)` THEN
          CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (GEN_ALL subspt_trans) THEN
          EXISTS_TAC `stack_state_code (t4:(A,C,FFI)stack_state)` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `stack_state_bitmaps
            (tp:(A,C,FFI)stack_state)` THEN
          CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        MP_TAC(ISPECL [`live:num_set#num_set`; `(bs:(A word)app_list,n:num)`;
          `(k:num,f:num,f':num)`;
                       `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`] wLive_LENGTH) THEN
        ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC) THEN
    (REMOVE_THEN "IHret" (MP_TAC o SPECL [`a:((A)word_loc)list`; `live:num_set#num_set`;
      `prog:(A)wl_prog`;
          `args1:((A)word_loc)list`; `ss:num option`; `x0:(A)word_loc`; `l1:num`; `l2:num`;
          `s2':(A,num#C,FFI)wl_state`; `a'':((A)word_loc)spt#((A)word_loc)spt`;
            `ret_code:(A)wl_prog`;
          `vs:num list`; `ys:((A)word_loc)list`; `a''':(A,num#C,FFI)wl_state`]) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
          `s1:(A,num#C,FFI)wl_state`;
          `stack_state_regs_fupd (K (t2r |+ (k,EL ((stack_state_stack_space
            (t1:(A,C,FFI)stack_state) + n0) + 2) t2s)))
            (stack_state_store_fupd
              (K (stack_state_store t1 |+ (Handler,EL ((stack_state_stack_space t1 + n0) + 2) t2s)))
              (stack_state_stack_fupd (K t2s)
                (stack_state_stack_space_fupd (K ((stack_state_stack_space t1 + n0) + 3)) t1)))`;
          `bs1:(A word)app_list`; `n1:num`; `bsr:(A word)app_list`; `nr:num`; `q2:(A)stack_prog`;
          `lens:num list`]) THEN
        ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
        ANTS_TAC THENL
        [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            can (find_term ((=) `n1:num`)) (concl th) && can (find_term ((=) `n:num`))
              (concl th))) THEN
          MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `LENGTH (stack_state_bitmaps
            (t:(A,C,FFI)stack_state))` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            can (find_term ((=) `n1:num`)) (concl th) && can (find_term ((=) `n:num`))
              (concl th))) THEN
          MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `append (bs':(A word)app_list)` THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC IS_PREFIX_TRANS THEN
          EXISTS_TAC `DROP (n - LENGTH (append (bs:(A word)app_list))) (stack_state_bitmaps
            (t:(A,C,FFI)stack_state))` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `loc_check (stack_state_code
            (t:(A,C,FFI)stack_state))` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC loc_check_SUBSET THEN ASM_REWRITE_TAC[]];
         ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
          (X_CHOOSE_THEN `res3:((A)stack_result)option` STRIP_ASSUME_TAC)))) THEN
    (EXISTS_TAC `ck + ck2:num` THEN
        SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) + ck + ck2 = 0)` (fun th ->
          REWRITE_TAC[th]) THENL
        [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)`
          THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[pair_CASE_def]) THEN
    (SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) = stack_state_clock
      (t:(A,C,FFI)stack_state)`
          ASSUME_TAC THENL
        [UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
          (t5:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
           (t:(A,C,FFI)stack_state)` THEN
         ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN
         `stack_evaluate (qc:(A)stack_prog,
            stack_state_stack_space_fupd (K (stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac
              - (fs - sac)))
            (stack_state_clock_fupd (K ((stack_state_clock (t:(A,C,FFI)stack_state) + ck
              + ck2) - 1))
            (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
            (stack_state_clock_fupd (K (stack_state_clock t + ck + ck2))
            (stack_state_stack_fupd (K t7s)
            (stack_state_regs_fupd (K t7r) (t6:(A,C,FFI)stack_state))))))) =
          (SOME (stack_Result x0), stack_state_clock_fupd (K (stack_state_clock t1 + ck2))
            (t1:(A,C,FFI)stack_state))`
         ASSUME_TAC THENL
        [MP_TAC(ISPECL [`qc:(A)stack_prog`;
           `stack_state_clock_fupd (K (stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck))
             (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
             (stack_state_stack_fupd (K t7s)
             (stack_state_stack_space_fupd (K (stack_state_stack_space
               (tp:(A,C,FFI)stack_state) - fs))
             (stack_state_clock_fupd (K (stack_state_clock t5 - 1)) tp))))`;
           `SOME (stack_Result (x0:(A)word_loc))`; `t1:(A,C,FFI)stack_state`]
           (INST [`ck2:num`,`extra:num`] stack_evaluate_add_clock)) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[option_INJ] THEN REWRITE_TAC[distinctness "stack_result"]; ALL_TAC] THEN
         SUBGOAL_THEN `(stack_state_clock (t:(A,C,FFI)stack_state) + ck + ck2) - 1 =
                       (stack_state_clock t - 1 + ck) + ck2 /\
                       stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac - (fs - sac) =
                         stack_state_stack_space tp - fs`
           (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN
          UNDISCH_TAC `sac <= fs` THEN UNDISCH_TAC `sac <= stack_state_stack_space
            (tp:(A,C,FFI)stack_state)` THEN
          ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN EXPAND_TAC "t6" THEN SIMP[];
         ALL_TAC] THEN
        ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[]) THEN
    (REWRITE_TAC[w2sp3aux_seval "stack_Skip"; FST; SND] THEN
        REWRITE_TAC[evaluate_copy_ret_Seq'] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[num_stack_ret_def] THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[w2sp3aux_seval "stack_Seq"] THEN
        REWRITE_TAC[evaluate_copy_ret_aux_clock] THEN
        ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; pair_CASE_def; FST; SND]) THEN
    (MP_TAC(ISPECL [`stack_state_clock_fupd (K (stack_state_clock (t1:(A,C,FFI)stack_state) + ck2))
             (stack_state_stack_fupd (K (t2s:((A)word_loc)list)) (stack_state_regs_fupd
               (K t2r) t1))`;
           `n0:num`; `PopHandler F (k:num,f:num,f':num) (q2:(A)stack_prog)`]
             evaluate_SeqStackFree) THEN
        REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN
        ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN
         UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f' + 4 <= LENGTH
           (stack_state_stack t1)` THEN
         ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        SUBGOAL_THEN `~(LENGTH (stack_state_stack (t1:(A,C,FFI)stack_state)) <
          stack_state_stack_space t1 + n0) /\
                      (stack_state_stack_space t1 + n0) + 2 < LENGTH (stack_state_stack t1) /\
                      ~(LENGTH (stack_state_stack t1) < (stack_state_stack_space t1 + n0) + 3)`
                        STRIP_ASSUME_TAC THENL
        [
         UNDISCH_TAC `(stack_state_stack_space (t1:(A,C,FFI)stack_state) + n0) + f' + 4 <= LENGTH
           (stack_state_stack t1)` THEN
         ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[PopHandler_F] THEN
        REWRITE_TAC[w2sp3aux_seval "stack_Seq"; w2sp3aux_seval "StackFree";
          w2sp3aux_seval "StackLoad";
                    w2sp3aux_seval "stack_Set"; stack_set_var_def; stack_set_store_def;
                      stack_get_var_def;
                    w2sp3aux_stack_accfupds; K_THM; FLOOKUP_UPDATE] THEN
        ASM_REWRITE_TAC[pair_CASE_def; FST; SND; w2sp3aux_stack_accfupds; K_THM; FLOOKUP_UPDATE;
          option_CASE]) THEN
    (FIRST_X_ASSUM(MP_TAC o check (w2sp3aux_is_seval_of `q2:(A)stack_prog`)) THEN
        ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN SIMP[] THEN DISCH_TAC THEN SIMP[] THEN
        ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1]) THEN
    (SUBGOAL_THEN `wl_state_handler (a''':(A,num#C,FFI)wl_state) = wl_state_handler
      (s:(A,num#C,FFI)wl_state)`
          ASSUME_TAC THENL
        [UNDISCH_TAC `wl_pop_env (s2':(A,num#C,FFI)wl_state) = SOME a'''` THEN
         ASM_REWRITE_TAC[wl_pop_env_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[w2sp3aux_wl_accfupds; K_THM]
           THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "stackSem_Halt" (concl th) &&
          can (find_term ((=) `t3:(A,C,FFI)stack_state`)) (concl th))) THEN
        ASM_REWRITE_TAC[wl_set_vars_def; w2sp3aux_wl_accfupds]);
    (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `res1:((A)stack_result)option`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; compile_result_def]) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel"
          (concl th) &&
          can (find_term ((=) `t1:(A,C,FFI)stack_state`)) (concl th) && not (is_forall
            (concl th)) &&
          w2sp3aux_has_const "push_locals" (concl th))) THEN
        CASE_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `el0:(num#(A)word_loc)list` (X_CHOOSE_THEN
          `el:(num#(A)word_loc)list`
          STRIP_ASSUME_TAC)) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
           rhs (concl th) = `(res:((A)wl_result)option,s1:(A,num#C,FFI)wl_state)` &&
           not (w2sp3aux_has_const "wl_Call" (concl th)))) THEN
        CASE_REWRITE_TAC[] THEN
        COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC; ALL_TAC] THEN
        COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN W2SP3AUX_ERR_TAC] THEN
        DISCH_TAC) THEN
    (FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_LENGTH o
          check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
                 can (find_term ((=) `s:(A,num#C,FFI)wl_state`)) (concl th) &&
                 can (find_term ((=) `t:(A,C,FFI)stack_state`)) (concl th))) THEN
        SUBGOAL_THEN `LASTN (LENGTH (wl_state_stack (s:(A,num#C,FFI)wl_state)) + 1) (CONS
          (f':num) lens) =
                      CONS f' lens` ASSUME_TAC THENL
        [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq (concl th) &&
           lhs (concl th) = `LENGTH (lens:num list)`)) THEN
         REWRITE_TAC[GSYM ADD1] THEN SIMP_TAC[LASTN_CONS_ID]; ALL_TAC] THEN
        FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[wl_call_env_def; w2sp3aux_wl_accfupds;
            W2SP3AUX_push_env_handler_SOME; wl_dec_clock_def; K_THM;
            ASSUME `LASTN (LENGTH (wl_state_stack (s:(A,num#C,FFI)wl_state)) + 1) (CONS
              (f':num) lens) =
                    CONS f' lens`] o
          check (fun th -> w2sp3aux_has_const "word_to_stackProof_state_rel" (concl th) &&
          w2sp3aux_has_const "push_locals" (concl th) && w2sp3aux_has_const "LASTN"
            (concl th))) THEN
        MP_TAC(ISPECL [`prog:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`;
          `a'':((A)word_loc)spt#((A)word_loc)spt`;
                       `args1:((A)word_loc)list`; `ss:num option`; `x0:(A)word_loc`;
                         `y0:(A)word_loc`;
                       `s2':(A,num#C,FFI)wl_state`; `2`; `hprog:(A)wl_prog`; `h1:num`; `h2:num`]
                      W2SP3AUX_exc_swap_SOME) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        MP_TAC(ISPECL [`live:num_set#num_set`; `wl_state_locals (s:(A,num#C,FFI)wl_state)`;
                       `a'':((A)word_loc)spt#((A)word_loc)spt`] W2SP3AUX_cut_envs_domain) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s2':(A,num#C,FFI)wl_state`;
                       `t1:(A,C,FFI)stack_state`; `lens:num list`; `el0:(num#(A)word_loc)list`;
                       `el:(num#(A)word_loc)list`; `y0:(A)word_loc`] W2SP3AUX_exc_state_rel_h) THEN
        ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN
         X_GEN_TAC `nn:num` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
           can (find_term ((=) `FST (live:num_set#num_set)`)) (concl th) &&
           w2sp3aux_has_const "DIV" (concl th))) THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
           can (find_term ((=) `SND (live:num_set#num_set)`)) (concl th) &&
           w2sp3aux_has_const "DIV" (concl th))) THEN
         ASM_REWRITE_TAC[] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(2 = 0)`];
         DISCH_TAC]) THEN
    (SUBGOAL_THEN `stack_get_labels (q4:(A)stack_prog) SUBSET loc_check (stack_state_code
      (t:(A,C,FFI)stack_state))`
          ASSUME_TAC THENL
        [FIRST_ASSUM(MP_TAC o check (fun th -> is_conj (concl th) && w2sp3aux_has_const
          "stack_get_labels" (concl th) &&
           can (find_term ((=) `q0:(A)stack_prog`)) (concl th))) THEN
         CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_get_labels_def; get_labels_copy_ret;
           PopHandler_F; UNION_SUBSET;
           INSERT_SUBSET; UNION_EMPTY; EMPTY_SUBSET] THEN
         SIMP_TAC[]; ALL_TAC] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_mono o
          check (w2sp3aux_is_seval_of `qc:(A)stack_prog`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[w2sp3aux_stack_accfupds; K_THM])) THEN
    (SUBGOAL_THEN `subspt (stack_state_code (t:(A,C,FFI)stack_state)) (stack_state_code
      (t1:(A,C,FFI)stack_state)) /\
                      stack_state_bitmaps t <<= stack_state_bitmaps t1`
          STRIP_ASSUME_TAC THENL
        [CONJ_TAC THENL
         [MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC
           `stack_state_code (tp:(A,C,FFI)stack_state)` THEN
          CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (GEN_ALL subspt_trans) THEN
          EXISTS_TAC `stack_state_code (t4:(A,C,FFI)stack_state)` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC IS_PREFIX_TRANS THEN EXISTS_TAC `stack_state_bitmaps
            (tp:(A,C,FFI)stack_state)` THEN
          CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        MP_TAC(ISPECL [`live:num_set#num_set`; `(bs:(A word)app_list,n:num)`;
          `(k:num,f:num,f':num)`;
                       `q1:(A)stack_prog`; `(bs1:(A word)app_list,n1:num)`] wLive_LENGTH) THEN
        ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC) THEN
    (MP_TAC(ISPECL [`ac:(A)asm_config`; `F`; `ret_code:(A)wl_prog`; `(bs1:(A word)app_list,n1:num)`;
                       `(k:num,f:num,f':num)`; `q2:(A)stack_prog`;
                         `(bsr:(A word)app_list,nr:num)`] comp_IMP_LENGTH) THEN
        ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC) THEN
    (REMOVE_THEN "IHexc" (MP_TAC o SPECL [`a:((A)word_loc)list`; `ret_code:(A)wl_prog`;
      `l1:num`; `l2:num`;
          `vs:num list`; `live:num_set#num_set`; `prog:(A)wl_prog`; `args1:((A)word_loc)list`;
            `ss:num option`;
          `x0:(A)word_loc`; `h1:num`; `h2:num`; `a'':((A)word_loc)spt#((A)word_loc)spt`;
            `hprog:(A)wl_prog`;
          `hv:num`; `y0:(A)word_loc`; `s2':(A,num#C,FFI)wl_state`]) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`k:num`; `f:num`; `f':num`; `res:((A)wl_result)option`;
          `s1:(A,num#C,FFI)wl_state`; `t1:(A,C,FFI)stack_state`;
          `bsr:(A word)app_list`; `nr:num`; `bs':(A word)app_list`; `n':num`; `q4:(A)stack_prog`;
          `lens:num list`]) THEN
        ASM_REWRITE_TAC[] THEN
        ANTS_TAC THENL
        [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            rhs (concl th) = `nr - LENGTH (append (bsr:(A word)app_list))`)) THEN
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            rhs (concl th) = `n1 - LENGTH (append (bs1:(A word)app_list))`)) THEN
          MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `LENGTH (stack_state_bitmaps
            (t:(A,C,FFI)stack_state))` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IS_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            rhs (concl th) = `nr - LENGTH (append (bsr:(A word)app_list))`)) THEN
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            rhs (concl th) = `n1 - LENGTH (append (bs1:(A word)app_list))`)) THEN
          MATCH_MP_TAC IS_PREFIX_TRANS THEN
          EXISTS_TAC `DROP (n - LENGTH (append (bs:(A word)app_list))) (stack_state_bitmaps
            (t:(A,C,FFI)stack_state))` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC isPREFIX_DROP THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `loc_check (stack_state_code
            (t:(A,C,FFI)stack_state))` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC loc_check_SUBSET THEN ASM_REWRITE_TAC[]];
         ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t3:(A,C,FFI)stack_state`
          (X_CHOOSE_THEN `res3:((A)stack_result)option` STRIP_ASSUME_TAC)))) THEN
    (EXISTS_TAC `ck + ck2:num` THEN
        SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) + ck + ck2 = 0)` (fun th ->
          REWRITE_TAC[th]) THENL
        [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)`
          THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[pair_CASE_def]) THEN
    (SUBGOAL_THEN `stack_state_clock (t5:(A,C,FFI)stack_state) = stack_state_clock
      (t:(A,C,FFI)stack_state)`
          ASSUME_TAC THENL
        [UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
          (t5:(A,C,FFI)stack_state)` THEN
         UNDISCH_TAC `wl_state_clock (s:(A,num#C,FFI)wl_state) = stack_state_clock
           (t:(A,C,FFI)stack_state)` THEN
         ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN
         `stack_evaluate (qc:(A)stack_prog,
            stack_state_stack_space_fupd (K (stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac
              - (fs - sac)))
            (stack_state_clock_fupd (K ((stack_state_clock (t:(A,C,FFI)stack_state) + ck
              + ck2) - 1))
            (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
            (stack_state_clock_fupd (K (stack_state_clock t + ck + ck2))
            (stack_state_stack_fupd (K t7s)
            (stack_state_regs_fupd (K t7r) (t6:(A,C,FFI)stack_state))))))) =
          (SOME (stack_Exception x0), stack_state_clock_fupd (K (stack_state_clock t1 + ck2))
            (t1:(A,C,FFI)stack_state))`
         ASSUME_TAC THENL
        [MP_TAC(ISPECL [`qc:(A)stack_prog`;
           `stack_state_clock_fupd (K (stack_state_clock (t5:(A,C,FFI)stack_state) - 1 + ck))
             (stack_state_regs_fupd (K (t7r |+ (0,wl_Loc l1 l2)))
             (stack_state_stack_fupd (K t7s)
             (stack_state_stack_space_fupd (K (stack_state_stack_space
               (tp:(A,C,FFI)stack_state) - fs))
             (stack_state_clock_fupd (K (stack_state_clock t5 - 1)) tp))))`;
           `SOME (stack_Exception (x0:(A)word_loc))`; `t1:(A,C,FFI)stack_state`]
           (INST [`ck2:num`,`extra:num`] stack_evaluate_add_clock)) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[option_INJ] THEN REWRITE_TAC[distinctness "stack_result"]; ALL_TAC] THEN
         SUBGOAL_THEN `(stack_state_clock (t:(A,C,FFI)stack_state) + ck + ck2) - 1 =
                       (stack_state_clock t - 1 + ck) + ck2 /\
                       stack_state_stack_space (tp:(A,C,FFI)stack_state) - sac - (fs - sac) =
                         stack_state_stack_space tp - fs`
           (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `~(stack_state_clock (t:(A,C,FFI)stack_state) = 0)` THEN
          UNDISCH_TAC `sac <= fs` THEN UNDISCH_TAC `sac <= stack_state_stack_space
            (tp:(A,C,FFI)stack_state)` THEN
          ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[w2sp3aux_stack_accfupds; K_THM] THEN EXPAND_TAC "t6" THEN SIMP[];
         ALL_TAC] THEN
        ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[]) THEN
    (MAP_EVERY EXISTS_TAC [`t3:(A,C,FFI)stack_state`; `res3:((A)stack_result)option`]
      THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> w2sp3aux_has_const "stackSem_Halt" (concl th) &&
          can (find_term ((=) `t3:(A,C,FFI)stack_state`)) (concl th))) THEN
        ASM_REWRITE_TAC[wl_set_var_def; w2sp3aux_wl_accfupds])]]);;

(* HOL4 line 8166: Resume comp_correct[Call_returning] (the Call case with  *)
(* ret = SOME x)                                                             *)
let word_to_stackProof_comp_correct_Call_returning = prove
 (word_to_stackProof_comp_call_case true,
  GEN_TAC THEN REPEAT GEN_TAC THEN
  W(fun (asl,w) ->
    let hty = `:(num#(A)wl_prog#num#num)option` in
    let h = find (fun v -> type_of v = hty) (frees w) in
    STRUCT_CASES_TAC (ISPEC h option_CASES)) THEN
  FIRST [MATCH_ACCEPT_TAC W2SP3AUX_comp_correct_Call_returning_NONE;
         MATCH_ACCEPT_TAC W2SP3AUX_comp_correct_Call_returning_SOME]);;
