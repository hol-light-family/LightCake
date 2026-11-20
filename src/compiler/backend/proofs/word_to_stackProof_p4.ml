(* ========================================================================= *)
(* word_to_stackProof_p4: part 4 of 4 (HOL4 lines 10049-12411) of the port  *)
(* of HOL4 compiler/backend/proofs/word_to_stackProofScript.sml (CakeML      *)
(* v3479).  Correctness proof for word_to_stack.                             *)
(* The parts _p1 ... _p4 are loaded one after the other (each needs the     *)
(* previous one).  The notes on the rendering in word_to_stackProof_p1.ml   *)
(* apply here.  W2SP4AUX_ and w2sp4aux_ names are local helpers of this     *)
(* part (lemmas, tactics, term builders).  The rebinding of                 *)
(* word_to_stackProof_comp_correct (HOL4 line 10066) splits the pair        *)
(* argument as HOL4's FORALL_PROD does (see the comment there).             *)
(* ========================================================================= *)

needs "compiler/backend/proofs/word_to_stackProof_p3.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 4: HOL4 lines 10049-12411 ===== *)

(* HOL4 line 10049: Resume comp_correct[Break] *)
let word_to_stackProof_comp_correct_Break = prove
 (word_to_stackProof_comp_case "wl_Break",
  REPEAT STRIP_TAC THEN
  FS[wl_evaluate_def; word_to_stack_comp_def] THEN RVEQ_TAC THEN
  EXISTS_TAC `0` THEN SIMP[stack_evaluate_def]);;

(* HOL4 line 10056: Resume comp_correct[Continue] *)
let word_to_stackProof_comp_correct_Continue = prove
 (word_to_stackProof_comp_case "wl_Continue",
  REPEAT STRIP_TAC THEN
  FS[wl_evaluate_def; word_to_stack_comp_def] THEN RVEQ_TAC THEN
  EXISTS_TAC `0` THEN SIMP[stack_evaluate_def]);;

(* HOL4 line 7924: Resume comp_correct[Call], the whole Call case (by cases *)
(* on ret, from Call_tail and Call_returning)                                *)
let word_to_stackProof_comp_correct_Call = prove
 (word_to_stackProof_comp_case "wl_Call",
  GEN_TAC THEN
  MATCH_MP_TAC(MESON[option_CASES]
    `(P NONE) /\ (!x. P (SOME x))
     ==> !ret:(num list#cutsets#(A)wl_prog#num#num)option. P ret`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `ac:(A)asm_config` word_to_stackProof_comp_correct_Call_tail);
    MP_TAC(SPEC `ac:(A)asm_config` word_to_stackProof_comp_correct_Call_returning)] THEN
  REWRITE_TAC[]);;

(* HOL4 line 10063: Finalise comp_correct (HOL4 line 5756: Theorem          *)
(* comp_correct: ^(ind_thm |> concl |> rand)): the conclusion of            *)
(* word_to_stackProof_ind_thm, with ac quantified; it follows from the      *)
(* cases above by word_to_stackProof_ind_thm.                                *)
let word_to_stackProof_comp_correct = prove
 (mk_forall (`ac:(A)asm_config`, rand (concl word_to_stackProof_ind_thm)),
  GEN_TAC THEN MATCH_MP_TAC word_to_stackProof_ind_thm THEN
  REPEAT CONJ_TAC THEN
  FIRST (map (fun th -> ACCEPT_TAC (SPEC `ac:(A)asm_config` th))
   [word_to_stackProof_comp_correct_Skip; word_to_stackProof_comp_correct_Alloc;
    word_to_stackProof_comp_correct_StoreConsts; word_to_stackProof_comp_correct_Move;
    word_to_stackProof_comp_correct_Inst; word_to_stackProof_comp_correct_Assign;
    word_to_stackProof_comp_correct_Get; word_to_stackProof_comp_correct_Set;
    word_to_stackProof_comp_correct_OpCurrHeap; word_to_stackProof_comp_correct_Store;
    word_to_stackProof_comp_correct_Tick; word_to_stackProof_comp_correct_MustTerminate;
    word_to_stackProof_comp_correct_Seq; word_to_stackProof_comp_correct_Return;
    word_to_stackProof_comp_correct_Raise; word_to_stackProof_comp_correct_If;
    word_to_stackProof_comp_correct_LocValue; word_to_stackProof_comp_correct_Install;
    word_to_stackProof_comp_correct_CodeBufferWrite;
    word_to_stackProof_comp_correct_DataBufferWrite; word_to_stackProof_comp_correct_FFI;
    word_to_stackProof_comp_correct_ShareInst; word_to_stackProof_comp_correct_Loop;
    word_to_stackProof_comp_correct_Call; word_to_stackProof_comp_correct_Break;
    word_to_stackProof_comp_correct_Continue]));;

(* HOL4 line 10066: val comp_correct (rebinds word_to_stackProof_comp_correct):  *)
(* REWRITE_RULE [FORALL_PROD] comp_correct with the variables n, sprog, bs' *)
(* and n' made free (here quantified last, in their order).  The pair       *)
(* argument of the conclusion of word_to_stackProof_ind_thm is split into   *)
(* prog and s (the binders of word_to_stackProof_goal), as HOL4's           *)
(* FORALL_PROD does.                                                          *)
let word_to_stackProof_comp_correct = prove
 (let tm = rhs (concl (GEN_BETA_CONV (mk_comb (word_to_stackProof_goal,
             `(prog:(A)wl_prog, s:(A,num#C,FFI)wl_state)`)))) in
  let vs,body = strip_forall tm in
  let drops = filter (fun v -> mem (fst (dest_var v)) ["n"; "sprog"; "bs'"; "n'"]) vs in
  list_mk_forall ([`ac:(A)asm_config`; `prog:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`] @
                  subtract vs drops @ drops, body),
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`ac:(A)asm_config`; `(prog:(A)wl_prog, s:(A,num#C,FFI)wl_state)`]
            word_to_stackProof_comp_correct) THEN
  CONV_TAC (LAND_CONV GEN_BETA_CONV) THEN
  DISCH_THEN (ACCEPT_TAC o SPEC_ALL));;

(* HOL4 line 10074 *)
let word_to_stackProof_evaluate_Seq_Skip = prove
 (`!(p:(A)stack_prog) (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq stack_Skip p,s) = stack_evaluate (p,s)`,
  REPEAT GEN_TAC THEN SIMP[stack_evaluate_def; stack_fix_clock_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SIMP[stack_state_component_equality]);;

(* HOL4 line 10080: val comp_Call_lemma (comp_correct |> Q.SPEC Call NONE  *)
(* (SOME start) [0] NONE |> SIMP_RULE ...): an intermediate step of the    *)
(* proof of comp_Call, not stated (the proof below instantiates            *)
(* word_to_stackProof_comp_correct directly).                               *)

(* W2SP4AUX: 1w and 2w are not 0w *)
let W2SP4AUX_good_dimindex_word12 = prove
 (`good_dimindex(:A) ==> ~(word 1 = (word 0:A word)) /\ ~(word 2 = (word 0:A word))`,
  REWRITE_TAC[good_dimindex_def; n2w_11; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 10090 *)
let comp_Call = prove
 (`!start (s:(A,num#C,FFI)wl_state) k res s1 (t:(A,C,FFI)stack_state) lens ac.
     wl_evaluate (wl_Call NONE (SOME start) [0] NONE,s) = (res,s1) /\
     ~(res = SOME wl_Error) /\ word_to_stackProof_state_rel ac k 0 0 s t lens 0
     ==> ?ck (t1:(A,C,FFI)stack_state) res1.
           stack_evaluate (stack_Call NONE (INL start) NONE,
                           stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
             (res1,t1) /\
           ~(word 1 = (word 0:A word)) /\ ~(word 2 = (word 0:A word)) /\
           if OPTION_MAP compile_result res = res1 then
             wl_state_ffi s1 = stack_state_ffi t1 /\ wl_state_clock s1 = stack_state_clock t1
           else
             res1 = SOME (stackSem_Halt (wl_Word (word 2))) /\
             isPREFIX (ffi_state_io_events (stack_state_ffi t1))
               (ffi_state_io_events (wl_state_ffi s1)) /\
             the (wl_state_stack_limit s1 + 1) (wl_state_stack_max s1) >
               wl_state_stack_limit s1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 < k /\ good_dimindex(:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[word_to_stackProof_state_rel_def]; ALL_TAC] THEN
  MP_TAC (SPECL [`ac:(A)asm_config`; `wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
     `s:(A,num#C,FFI)wl_state`; `k:num`; `0`; `0`; `res:((A)wl_result)option`;
     `s1:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `Nil:(A word)app_list`;
     `lens:num list`; `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))`;
     `Nil:(A word)app_list`; `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state))`;
     `stack_Seq stack_Skip (stack_Call NONE (INL start) NONE):(A)stack_prog`]
     word_to_stackProof_comp_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[append_thm; LENGTH; SUB_0; LE_0; LE_REFL; isPREFIX_THM] THEN
    SIMP[word_to_stackProof_convs_def; is_phy_var_def; word_to_stack_comp_def; call_dest_def;
         SeqStackFree_def; word_to_stack_stack_free_def; stack_arg_count_def; max_var_def;
         stack_get_labels_def; EMPTY_SUBSET] THEN
    REWRITE_TAC[ONE; list_of_seq; APPEND; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[word_to_stackProof_evaluate_Seq_Skip] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ck:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:(A,C,FFI)stack_state` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `res1:((A)stack_result)option` THEN
  ASM_SIMP_TAC[W2SP4AUX_good_dimindex_word12] THEN
  ASM_CASES_TAC `OPTION_MAP compile_result (res:((A)wl_result)option) = res1` THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` (cases "option")) THEN
    CASE_REWRITE_TAC[] THENL
     [SIMP[word_to_stackProof_state_rel_def];
      STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
      CASE_REWRITE_TAC[] THEN
      SIMP[word_to_stackProof_state_rel_def; push_locals_def; LEFT_IMP_EXISTS_THM]];
    MESON_TAC[]]);;

(* HOL4 line 10116 *)
let word_to_stackProof_state_rel_with_clock = prove
 (`!ac a (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra k.
     word_to_stackProof_state_rel ac a 0 0 s t lens extra
     ==> word_to_stackProof_state_rel ac a 0 0 (wl_state_clock_fupd (K k) s)
           (stack_state_clock_fupd (K k) t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  SIMP[] THEN MESON_TAC[]);;

(* HOL4 lines 10123-10133: val s, s', t (type annotations), clock_simps     *)
(* (EVAL of record updates, in the simpset here), fun drule0 (a tactic)     *)

(* W2SP4AUX: the clause of an evaluate definition for a constructor *)
let w2sp4aux_eval_clause (th:thm) c =
  let is_c th =
    try let l = lhs(snd(strip_forall(concl th))) in
        let p = fst(dest_pair(rand l)) in
        fst(dest_const(fst(strip_comb p))) = c
    with Failure _ -> false in
  match filter is_c (CONJUNCTS th) with
    [th] -> th
  | _ -> failwith ("w2sp4aux_eval_clause: " ^ c);;
let w2sp4aux_weval = w2sp4aux_eval_clause wl_evaluate_def;;
let w2sp4aux_seval = w2sp4aux_eval_clause stack_evaluate_def;;

(* HOL4 line 10136 *)
let word_Call_NONE_not_Break_Continue = prove
 (`!dest args handler (s:(A,C,FFI)wl_state) res s'.
     wl_evaluate (wl_Call NONE dest args handler,s) = (res,s')
     ==> (!n. ~(res = SOME (wordSem_Break n))) /\ (!n. ~(res = SOME (wordSem_Continue n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp4aux_weval "wl_Call"] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[]);;

(* HOL4 line 10145 *)
let stack_Call_NONE_not_Break_Continue = prove
 (`!dest handler (s:(A,C,FFI)stack_state) res s'.
     stack_evaluate (stack_Call NONE dest handler,s) = (res,s')
     ==> (!n. ~(res = SOME (stackSem_Break n))) /\ (!n. ~(res = SOME (stackSem_Continue n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp4aux_seval "stack_Call"] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[]);;

(* W2SP4AUX: helpers for the semantics theorems below (HOL4 does these     *)
(* steps inside the proofs of state_rel_IMP_semantics and                  *)
(* state_rel_IMP_semantics').  w2sp4aux_wev k and w2sp4aux_sev k are the    *)
(* runs of the start call with clock k in wordSem and in stackSem.          *)

let w2sp4aux_concl th = rand(snd(strip_forall(concl th)));;

let W2SP4AUX_SOME_INTRO_TAC (p:term->bool) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> is_comb t &&
                       (try fst(dest_const(rator t)) = "some" with Failure _ -> false) &&
                       p t) w in
  let v = genvar(type_of t) in
  let th = BETA_CONV (mk_comb(mk_abs(v,subst [v,t] w),t)) in
  (CONV_TAC(K(SYM th)) THEN MATCH_MP_TAC some_intro THEN
   CONV_TAC(DEPTH_CONV BETA_CONV)) g;;

let w2sp4aux_sev k =
  vsubst [k,`kk:num`]
   `stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                    stack_state_clock_fupd (K kk) (t:(A,C,FFI)stack_state))`;;

let w2sp4aux_wev k =
  vsubst [k,`kk:num`]
   `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                 wl_state_clock_fupd (K kk) (s:(A,num#C,FFI)wl_state))`;;

let W2SP4AUX_word_io_mono = prove
 (`!p (x:(A,num#C,FFI)wl_state) k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (wl_state_ffi
          (SND (wl_evaluate (p,wl_state_clock_fupd (K k1) x)))))
       (ffi_state_io_events (wl_state_ffi
          (SND (wl_evaluate (p,wl_state_clock_fupd (K k2) x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `wl_state_clock_fupd (K k1) (x:(A,num#C,FFI)wl_state)`;
                 `d:num`] wl_evaluate_add_clock_io_events_mono) THEN
  SIMP[]);;

let W2SP4AUX_word_io_chain = prove
 (`!p (x:(A,num#C,FFI)wl_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
          (SND (wl_evaluate (p,wl_state_clock_fupd (K k) x)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[W2SP4AUX_word_io_mono; LE_CASES]);;

let W2SP4AUX_sim = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens start kc.
     word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\
     ~(FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s)) =
       SOME wl_Error)
     ==> ?ck.
       (OPTION_MAP compile_result
          (FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s))) =
        FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                             stack_state_clock_fupd (K (kc + ck)) t)) /\
        wl_state_ffi
          (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s))) =
        stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL start) NONE,
                                              stack_state_clock_fupd (K (kc + ck)) t)))) \/
       (~(OPTION_MAP compile_result
            (FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                               wl_state_clock_fupd (K kc) s))) =
          FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                               stack_state_clock_fupd (K (kc + ck)) t))) /\
        FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                             stack_state_clock_fupd (K (kc + ck)) t)) =
          SOME (stackSem_Halt (wl_Word (word 2))) /\
        isPREFIX
          (ffi_state_io_events (stack_state_ffi (SND (stack_evaluate
             (stack_Call NONE (INL start) NONE,stack_state_clock_fupd (K (kc + ck)) t)))))
          (ffi_state_io_events (wl_state_ffi (SND (wl_evaluate
             (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s))))) /\
        the (wl_state_stack_limit (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                                   wl_state_clock_fupd (K kc) s))) + 1)
            (wl_state_stack_max (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                                  wl_state_clock_fupd (K kc) s)))) >
          wl_state_stack_limit (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                                 wl_state_clock_fupd (K kc) s))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                              wl_state_clock_fupd (K kc) (s:(A,num#C,FFI)wl_state))`
            PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`] THEN
  DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`start:num`; `wl_state_clock_fupd (K kc) (s:(A,num#C,FFI)wl_state)`; `k:num`;
                 `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`;
                 `stack_state_clock_fupd (K kc) (t:(A,C,FFI)stack_state)`; `lens:num list`;
                 `ac:(A)asm_config`] comp_Call) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[word_to_stackProof_state_rel_with_clock] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN SIMP[];
    ALL_TAC] THEN
  SIMP[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `res1:((A)stack_result)option`] THEN
  STRIP_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let W2SP4AUX_word_ok = prove
 (`!(s:(A,num#C,FFI)wl_state) start kc.
     ~(wl_semantics s start = Fail)
     ==> FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s)) =
           SOME wl_TimeOut \/
         (?ys. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                 wl_state_clock_fupd (K kc) s)) =
                 SOME (wl_Result (wl_Loc 1 0) ys)) \/
         FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s)) =
           SOME NotEnoughSpace \/
         (?f. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                wl_state_clock_fupd (K kc) s)) = SOME (wl_FinalFFI f))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `kc:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC (ISPEC `wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                              wl_state_clock_fupd (K kc) (s:(A,num#C,FFI)wl_state))`
            PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`] THEN
  DISCH_THEN(fun th -> SUBST1_TAC th THEN
    MP_TAC (MATCH_MP word_Call_NONE_not_Break_Continue th)) THEN
  REWRITE_TAC[FST] THEN
  STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result"))) THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  MESON_TAC[]);;

let W2SP4AUX_stack_add_clock = prove
 (`!p (t:(A,C,FFI)stack_state) k1 k2.
     k1 <= k2 /\
     ~(FST (stack_evaluate (p,stack_state_clock_fupd (K k1) t)) = SOME stack_TimeOut)
     ==> FST (stack_evaluate (p,stack_state_clock_fupd (K k2) t)) =
         FST (stack_evaluate (p,stack_state_clock_fupd (K k1) t)) /\
         stack_state_ffi (SND (stack_evaluate (p,stack_state_clock_fupd (K k2) t))) =
         stack_state_ffi (SND (stack_evaluate (p,stack_state_clock_fupd (K k1) t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC (ISPEC `stack_evaluate (p:(A)stack_prog,
                                 stack_state_clock_fupd (K k1) (t:(A,C,FFI)stack_state))`
            PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST]) THEN ASSUME_TAC th THEN
                       REWRITE_TAC[th; FST; SND]) THEN
  MP_TAC (INST [`d:num`,`extra:num`]
    (ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (t:(A,C,FFI)stack_state)`;
             `r1:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`]
            stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let W2SP4AUX_stack_ok = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens start kc.
     word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\ ~(wl_semantics s start = Fail)
     ==> FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                              stack_state_clock_fupd (K kc) t)) = SOME stack_TimeOut \/
         FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                              stack_state_clock_fupd (K kc) t)) =
           SOME (stack_Result (wl_Loc 1 0)) \/
         (?w. FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                   stack_state_clock_fupd (K kc) t)) =
                SOME (stackSem_Halt (wl_Word w))) \/
         (?f. FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                   stack_state_clock_fupd (K kc) t)) =
                SOME (stack_FinalFFI f))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "wok" o SPEC `kc:num` o MATCH_MP W2SP4AUX_word_ok) THEN
  MP_TAC (SPECL [`ac:(A)asm_config`; `k:num`; `s:(A,num#C,FFI)wl_state`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`; `start:num`; `kc:num`]
            W2SP4AUX_sim) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "wok" STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (LABEL_TAC "sim")) THEN
  ASM_CASES_TAC (mk_eq(mk_comb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->
                                    ((A)stack_result)option`, w2sp4aux_sev `kc:num`),
                       `SOME (stack_TimeOut:(A)stack_result)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`; `t:(A,C,FFI)stack_state`;
                 `kc:num`; `kc + ck:num`] W2SP4AUX_stack_add_clock) THEN
  ASM_REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(fun th -> REMOVE_THEN "sim" (MP_TAC o REWRITE_RULE[CONJUNCT1 th])) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM o CONJUNCT1)
                              (SUBST1_TAC o CONJUNCT1 o CONJUNCT2)) THENL
   [REMOVE_THEN "wok" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; compile_result_def]) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; compile_result_def] THEN SIMP[];
    SIMP[]]);;

let W2SP4AUX_lub_eq = prove
 (`!(s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) start.
     (!kc. ?ck. wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                     wl_state_clock_fupd (K kc) s))) =
                stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL start) NONE,
                                     stack_state_clock_fupd (K (kc + ck)) t))))
     ==> build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (stack_state_ffi
              (SND (stack_evaluate (stack_Call NONE (INL start) NONE,
                                    stack_state_clock_fupd (K k) t)))))) (:num)) =
         build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
              (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                 wl_state_clock_fupd (K k) s)))))) (:num))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
  REWRITE_TAC[STACKPROPSAUX_io_chain; W2SP4AUX_word_io_chain] THEN
  REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THEN X_GEN_TAC `kc:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ck:num` o SPEC `kc:num`) THENL
   [EXISTS_TAC `kc:num` THEN
    ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
    MATCH_MP_TAC STACKPROPSAUX_io_mono THEN ARITH_TAC;
    EXISTS_TAC `kc + ck:num` THEN
    ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL]]);;

let W2SP4AUX_word_lub_prefix = prove
 (`!(s:(A,num#C,FFI)wl_state) start kc l.
     isPREFIX l (ffi_state_io_events (wl_state_ffi
        (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                           wl_state_clock_fupd (K kc) s)))))
     ==> LPREFIX (llist_fromList l)
           (build_lprefix_lub
              (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
                 (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                    wl_state_clock_fupd (K k) s)))))) (:num)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL LPREFIX_TRANS) THEN
  EXISTS_TAC `llist_fromList (ffi_state_io_events (wl_state_ffi
                 (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                                    wl_state_clock_fupd (K kc) (s:(A,num#C,FFI)wl_state))))))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE]; ALL_TAC] THEN
  MP_TAC (MATCH_MP build_lprefix_lub_thm
    (ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`]
       W2SP4AUX_word_io_chain)) THEN
  REWRITE_TAC[lprefix_lub_def; FORALL_IN_IMAGE; IN_UNIV] THEN SIMP[]);;

let W2SP4AUX_word_add_clock = prove
 (`!p (s:(A,num#C,FFI)wl_state) k1 k2.
     k1 <= k2 /\
     ~(FST (wl_evaluate (p,wl_state_clock_fupd (K k1) s)) = SOME wl_TimeOut)
     ==> FST (wl_evaluate (p,wl_state_clock_fupd (K k2) s)) =
         FST (wl_evaluate (p,wl_state_clock_fupd (K k1) s)) /\
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (K k2) s))) =
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (K k1) s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC (ISPEC `wl_evaluate (p:(A)wl_prog,
                              wl_state_clock_fupd (K k1) (s:(A,num#C,FFI)wl_state))`
            PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST]) THEN ASSUME_TAC th THEN
                       REWRITE_TAC[th; FST; SND]) THEN
  MP_TAC (INST [`d:num`,`extra:num`]
    (ISPECL [`p:(A)wl_prog`; `wl_state_clock_fupd (K k1) (s:(A,num#C,FFI)wl_state)`;
             `r1:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`]
            wl_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let W2SP4AUX_word_det = prove
 (`!p (s:(A,num#C,FFI)wl_state) k1 k2.
     ~(FST (wl_evaluate (p,wl_state_clock_fupd (K k1) s)) = SOME wl_TimeOut) /\
     ~(FST (wl_evaluate (p,wl_state_clock_fupd (K k2) s)) = SOME wl_TimeOut)
     ==> FST (wl_evaluate (p,wl_state_clock_fupd (K k1) s)) =
         FST (wl_evaluate (p,wl_state_clock_fupd (K k2) s)) /\
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (K k1) s))) =
         wl_state_ffi (SND (wl_evaluate (p,wl_state_clock_fupd (K k2) s)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISJ_CASES_TAC (SPECL [`k1:num`; `k2:num`] LE_CASES) THENL
   [MP_TAC (SPECL [`p:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`; `k1:num`; `k2:num`]
              W2SP4AUX_word_add_clock);
    MP_TAC (SPECL [`p:(A)wl_prog`; `s:(A,num#C,FFI)wl_state`; `k2:num`; `k1:num`]
              W2SP4AUX_word_add_clock)] THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let W2SP4AUX_stack_det = prove
 (`!p (t:(A,C,FFI)stack_state) k1 k2.
     ~(FST (stack_evaluate (p,stack_state_clock_fupd (K k1) t)) = SOME stack_TimeOut) /\
     ~(FST (stack_evaluate (p,stack_state_clock_fupd (K k2) t)) = SOME stack_TimeOut)
     ==> FST (stack_evaluate (p,stack_state_clock_fupd (K k1) t)) =
         FST (stack_evaluate (p,stack_state_clock_fupd (K k2) t)) /\
         stack_state_ffi (SND (stack_evaluate (p,stack_state_clock_fupd (K k1) t))) =
         stack_state_ffi (SND (stack_evaluate (p,stack_state_clock_fupd (K k2) t)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISJ_CASES_TAC (SPECL [`k1:num`; `k2:num`] LE_CASES) THENL
   [MP_TAC (SPECL [`p:(A)stack_prog`; `t:(A,C,FFI)stack_state`; `k1:num`; `k2:num`]
              W2SP4AUX_stack_add_clock);
    MP_TAC (SPECL [`p:(A)stack_prog`; `t:(A,C,FFI)stack_state`; `k2:num`; `k1:num`]
              W2SP4AUX_stack_add_clock)] THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let W2SP4AUX_stack_sem_div = prove
 (`!(t:(A,C,FFI)stack_state) start.
     (!kc. FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                stack_state_clock_fupd (K kc) t)) = SOME stack_TimeOut)
     ==> stack_semantics start t =
         Diverge (build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (stack_state_ffi
              (SND (stack_evaluate (stack_Call NONE (INL start) NONE,
                                    stack_state_clock_fupd (K k) t)))))) (:num)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  W2SP4AUX_SOME_INTRO_TAC (K true) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `t2:(A,C,FFI)stack_state`; `r:(A)stack_result`;
                         `outcome:outcome`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kk:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[FST; option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)))) THEN CASE_REWRITE_TAC[];
    CASE_REWRITE_TAC[]]);;

let W2SP4AUX_stack_sem_term = prove
 (`!(t:(A,C,FFI)stack_state) start kt r t2 outcome.
     (!kc. FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                stack_state_clock_fupd (K kc) t)) = SOME stack_TimeOut \/
           FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                stack_state_clock_fupd (K kc) t)) =
             SOME (stack_Result (wl_Loc 1 0)) \/
           (?w. FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                     stack_state_clock_fupd (K kc) t)) =
                  SOME (stackSem_Halt (wl_Word w))) \/
           (?f. FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                                     stack_state_clock_fupd (K kc) t)) =
                  SOME (stack_FinalFFI f))) /\
     stack_evaluate (stack_Call NONE (INL start) NONE,stack_state_clock_fupd (K kt) t) =
       (SOME r,t2) /\
     ((?w. r = stackSem_Halt w /\
           outcome = (if w = wl_Word (word 0) then Success else Resource_limit_hit)) \/
      (?w. r = stack_Result w /\ outcome = Success) \/
      (?e. r = stack_FinalFFI e /\ outcome = FFI_outcome e))
     ==> stack_semantics start t =
         Terminate outcome (ffi_state_io_events (stack_state_ffi t2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sok")
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "oc"))) THEN
  SUBGOAL_THEN `~(r = (stack_TimeOut:(A)stack_result))` (LABEL_TAC "nto") THENL
   [USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (SUBST1_TAC o CONJUNCT1))) THEN REWRITE_TAC[distinctness "stack_result"];
    ALL_TAC] THEN
  REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `kk:num`) THEN USE_THEN "sok" (MP_TAC o SPEC `kk:num`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  W2SP4AUX_SOME_INTRO_TAC (K true) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `t3:(A,C,FFI)stack_state`; `r3:(A)stack_result`;
                         `outcome3:outcome`] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`; `t:(A,C,FFI)stack_state`;
                   `kt:num`; `kk:num`] W2SP4AUX_stack_det) THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[FST; SND; option_INJ] THEN
    ANTS_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
        not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "behaviour"] THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `Terminate outcome
                  (ffi_state_io_events (stack_state_ffi (t2:(A,C,FFI)stack_state)))`) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`kt:num`; `t2:(A,C,FFI)stack_state`; `r:(A)stack_result`;
                          `outcome:outcome`] THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC))) THEN CASE_REWRITE_TAC[]]);;

let W2SP4AUX_word_sem_div = prove
 (`!(s:(A,num#C,FFI)wl_state) start.
     (!kc. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                             wl_state_clock_fupd (K kc) s)) = SOME wl_TimeOut)
     ==> wl_semantics s start =
         Diverge (build_lprefix_lub
           (IMAGE (\k. llist_fromList (ffi_state_io_events (wl_state_ffi
              (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                 wl_state_clock_fupd (K k) s)))))) (:num)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  W2SP4AUX_SOME_INTRO_TAC (K true) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s2:(A,num#C,FFI)wl_state`; `r:((A)wl_result)option`;
                         `outcome:outcome`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kk:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)))) THEN CASE_REWRITE_TAC[];
    CASE_REWRITE_TAC[]]);;

let W2SP4AUX_word_sem_term = prove
 (`!(s:(A,num#C,FFI)wl_state) start kw rw sw outcome.
     ~(wl_semantics s start = Fail) /\
     wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kw) s) =
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
  W2SP4AUX_SOME_INTRO_TAC (K true) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:behaviour` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s3:(A,num#C,FFI)wl_state`; `r3:((A)wl_result)option`;
                         `outcome3:outcome`] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                   `s:(A,num#C,FFI)wl_state`; `kw:num`; `kk:num`] W2SP4AUX_word_det) THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[FST; SND] THEN
    ANTS_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
        not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "behaviour"] THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      not (is_eq (concl th)) && not (is_neg (concl th)))) THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `Terminate outcome
                  (ffi_state_io_events (wl_state_ffi (sw:(A,num#C,FFI)wl_state)))`) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`kw:num`; `sw:(A,num#C,FFI)wl_state`; `rw:((A)wl_result)option`;
                          `outcome:outcome`] THEN
    USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "oc" (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC))) THEN CASE_REWRITE_TAC[]]);;

let W2SP4AUX_extend_refl = prove
 (`!x. x IN extend_with_resource_limit {x}`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING]);;

let W2SP4AUX_extend_term = prove
 (`!io t l. isPREFIX io l
            ==> Terminate Resource_limit_hit io IN extend_with_resource_limit {Terminate t l}`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let W2SP4AUX_extend_div = prove
 (`!io ll. LPREFIX (llist_fromList io) ll
           ==> Terminate Resource_limit_hit io IN extend_with_resource_limit {Diverge ll}`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let W2SP4AUX_outcome_compile = prove
 (`!(rw:((A)wl_result)option).
     ~(word 1 = (word 0:A word)) /\
     ((?ys. rw = SOME (wl_Result (wl_Loc 1 0) ys)) \/ rw = SOME NotEnoughSpace \/
      (?f. rw = SOME (wl_FinalFFI f)))
     ==> ?outcome.
           ((?e. rw = SOME (wl_FinalFFI e) /\ outcome = FFI_outcome e) \/
            (?w ys. rw = SOME (wl_Result w ys) /\ outcome = Success) \/
            (rw = SOME NotEnoughSpace /\ outcome = Resource_limit_hit)) /\
           ?r. OPTION_MAP compile_result rw = SOME r /\
               ((?w. r = stackSem_Halt w /\
                     outcome = (if w = wl_Word (word 0) then Success else Resource_limit_hit)) \/
                (?w. r = stack_Result w /\ outcome = Success) \/
                (?e. r = stack_FinalFFI e /\ outcome = FFI_outcome e))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC))) THEN
  REWRITE_TAC[OPTION_MAP_DEF; compile_result_def; option_INJ; distinctness "wl_result";
              injectivity "wl_result"; distinctness "stack_result"; injectivity "stack_result";
              injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1; EXISTS_REFL] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let W2SP4AUX_SEM_FACTS_TAC : tactic =
  SUBGOAL_THEN `~(word 1 = (word 0:A word)) /\ ~(word 2 = (word 0:A word))`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC W2SP4AUX_good_dimindex_word12 THEN
    ASM_MESON_TAC[word_to_stackProof_state_rel_def];
    ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "wok" o MATCH_MP W2SP4AUX_word_ok) THEN
  SUBGOAL_THEN (mk_forall(`kc:num`, w2sp4aux_concl W2SP4AUX_stack_ok)) (LABEL_TAC "sok") THENL
   [GEN_TAC THEN MATCH_MP_TAC W2SP4AUX_stack_ok THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `s:(A,num#C,FFI)wl_state`;
                          `lens:num list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_forall(`kc:num`, w2sp4aux_concl W2SP4AUX_sim)) (LABEL_TAC "sim") THENL
   [GEN_TAC THEN MATCH_MP_TAC W2SP4AUX_sim THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `lens:num list`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "wok" (STRIP_ASSUME_TAC o SPEC `kc:num`) THEN
    ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
    ALL_TAC];;

(* HOL4 line 10154 *)
let state_rel_IMP_semantics = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens start.
     word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\ ~(wl_semantics s start = Fail)
     ==> stack_semantics start t IN extend_with_resource_limit {wl_semantics s start}`,
  REPEAT STRIP_TAC THEN W2SP4AUX_SEM_FACTS_TAC THEN
  ASM_CASES_TAC (mk_exists(`kw:num`, mk_neg(mk_eq(mk_comb(
    `FST:((A)wl_result)option#(A,num#C,FFI)wl_state->((A)wl_result)option`,
    w2sp4aux_wev `kw:num`), `SOME (wl_TimeOut:(A)wl_result)`)))) THENL
   [(* the word program terminates *)
    FIRST_X_ASSUM(X_CHOOSE_TAC `kw:num`) THEN
    MP_TAC (ISPEC (w2sp4aux_wev `kw:num`) PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`rw:((A)wl_result)option`; `sw:(A,num#C,FFI)wl_state`] THEN
    DISCH_THEN(LABEL_TAC "evw") THEN
    USE_THEN "wok" (MP_TAC o SPEC `kw:num`) THEN
    USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kw:num`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
    MP_TAC (ISPEC (w2sp4aux_sev `kw + ck:num`) PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r1:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`] THEN
    DISCH_THEN(LABEL_TAC "evs") THEN
    USE_THEN "evs" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
    DISCH_TAC THEN DISCH_THEN(LABEL_TAC "simk") THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPEC `rw:((A)wl_result)option` W2SP4AUX_outcome_compile) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `outcome:outcome` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r:(A)stack_result` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ocs"))))) THEN
    MP_TAC (SPECL [`s:(A,num#C,FFI)wl_state`; `start:num`; `kw:num`;
                   `rw:((A)wl_result)option`; `sw:(A,num#C,FFI)wl_state`; `outcome:outcome`]
             W2SP4AUX_word_sem_term) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "evw" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "simk" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `start:num`; `kw + ck:num`; `r:(A)stack_result`;
                     `t1:(A,C,FFI)stack_state`; `outcome:outcome`] W2SP4AUX_stack_sem_term) THEN
      ANTS_TAC THENL
       [USE_THEN "ocs" (fun th -> REWRITE_TAC[th]) THEN
        CONJ_TAC THENL [USE_THEN "sok" ACCEPT_TAC; ALL_TAC] THEN
        USE_THEN "evs" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[W2SP4AUX_extend_refl];
      MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `start:num`; `kw + ck:num`;
                     `stackSem_Halt (wl_Word (word 2)):(A)stack_result`;
                     `t1:(A,C,FFI)stack_state`; `Resource_limit_hit`] W2SP4AUX_stack_sem_term) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "sok" ACCEPT_TAC; ALL_TAC] THEN
        USE_THEN "evs" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
        DISJ1_TAC THEN EXISTS_TAC `wl_Word (word 2):(A)word_loc` THEN
        ASM_REWRITE_TAC[injectivity "word_loc"];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC W2SP4AUX_extend_term THEN ASM_REWRITE_TAC[]];
    (* the word program diverges *)
    FIRST_X_ASSUM(LABEL_TAC "wto" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC (SPECL [`s:(A,num#C,FFI)wl_state`; `start:num`] W2SP4AUX_word_sem_div) THEN
    USE_THEN "wto" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC (mk_exists(`ks:num`, mk_neg(mk_eq(mk_comb(
      `FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`,
      w2sp4aux_sev `ks:num`), `SOME (stack_TimeOut:(A)stack_result)`)))) THENL
     [(* the stack program stops: by the resource limit only *)
      FIRST_X_ASSUM(X_CHOOSE_TAC `ks:num`) THEN
      MP_TAC (ISPEC (w2sp4aux_sev `ks:num`) PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r2:((A)stack_result)option`; `t2:(A,C,FFI)stack_state`] THEN
      DISCH_THEN(LABEL_TAC "evs") THEN
      USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `ks:num`) THEN
      USE_THEN "wto" (fun th -> REWRITE_TAC[th; OPTION_MAP_DEF; compile_result_def]) THEN
      MP_TAC (SPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                     `t:(A,C,FFI)stack_state`; `ks:num`; `ks + ck:num`]
               W2SP4AUX_stack_add_clock) THEN
      ASM_REWRITE_TAC[LE_ADD] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      USE_THEN "evs" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `start:num`; `ks:num`;
                     `stackSem_Halt (wl_Word (word 2)):(A)stack_result`;
                     `t2:(A,C,FFI)stack_state`; `Resource_limit_hit`]
               W2SP4AUX_stack_sem_term) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "sok" ACCEPT_TAC; ALL_TAC] THEN
        USE_THEN "evs" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
        DISJ1_TAC THEN EXISTS_TAC `wl_Word (word 2):(A)word_loc` THEN
        ASM_REWRITE_TAC[injectivity "word_loc"];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC W2SP4AUX_extend_div THEN
      MATCH_MP_TAC W2SP4AUX_word_lub_prefix THEN EXISTS_TAC `ks:num` THEN
      ASM_REWRITE_TAC[];
      (* both diverge *)
      FIRST_X_ASSUM(LABEL_TAC "sto" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `start:num`] W2SP4AUX_stack_sem_div) THEN
      USE_THEN "sto" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC (SPECL [`s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `start:num`]
               W2SP4AUX_lub_eq) THEN
      ANTS_TAC THENL
       [X_GEN_TAC `kc:num` THEN
        USE_THEN "sim" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kc:num`) THEN
        USE_THEN "sto" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[option_INJ; distinctness "stack_result"] THEN MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[W2SP4AUX_extend_refl]]]);;

(* HOL4 line 10373 *)
let init_state_ok_def = cake_def
  `init_state_ok (ac:(A)asm_config) k (t:(A,C,FFI)stack_state)
     (coracle:num->(num#C)#(num#num#(A)wl_prog)list) <=>
     4 < k /\ good_dimindex (:A) /\ 8 <= dimindex (:A) /\
     stack_state_use_stack t /\ stack_state_use_store t /\ stack_state_use_alloc t /\
     gc_fun_ok (stack_state_gc_fun t) /\
     stack_state_stack_space t <= LENGTH (stack_state_stack t) /\
     FLOOKUP (stack_state_regs t) 0 = SOME (wl_Loc 1 0) /\
     LENGTH (stack_state_bitmaps t) + 1 < dimword (:A) /\
     isPREFIX [word 4] (stack_state_bitmaps t) /\
     LENGTH (stack_state_stack t) < dimword (:A) /\
     DROP (stack_state_stack_space t) (stack_state_stack t) = [wl_Word (word 0)] /\
     Handler IN FDOM (stack_state_store t) /\
     LENGTH (stack_state_bitmaps t) + LENGTH (buffer_buffer (stack_state_data_buffer t)) +
       buffer_space_left (stack_state_data_buffer t) + 1 < dimword (:A) /\
     stack_state_compile_oracle t =
       (\n. let ((bm0,cfg),progs) = coracle n in
            let (progs,fs,bm) = compile_word_to_stack ac F k progs (Nil,bm0) in
            (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = coracle n in
          ALL (post_alloc_conventions k o SND o SND) progs /\
          ALL (flat_exp_conventions o SND o SND) progs /\
          ALL ((\x. ~(raise_stub_location = x)) o FST) progs /\
          ALL ((\x. ~(wl_store_consts_stub_location = x)) o FST) progs /\
          (n = 0 ==> bm0 = LENGTH (stack_state_bitmaps t)))`;;

(* HOL4 line 10398 (the record literal in the field order of wl_state;      *)
(* HOL4 t.store \\ Handler is fdomsub (stack_state_store t) Handler; mapi is *)
(* sptree's)                                                                 *)
let word_to_stackProof_make_init_def = cake_def
  `word_to_stackProof_make_init (ac:(A)asm_config) k (t:(A,C,FFI)stack_state)
     (code:(num#(A)wl_prog)spt) (coracle:num->(num#C)#(num#num#(A)wl_prog)list) =
     wl_state_REC
       (insert 0 (wl_Loc 1 0) LN)
       (SOME 0)
       (stack_state_fp_regs t)
       (fdomsub (stack_state_store t) Handler)
       []
       (LENGTH (stack_state_stack t))
       (wl_stack_size ([]:((A)stack_frame)list))
       (mapi (\n (arg_count,prog).
                FST (SND (word_to_stack_compile_prog ac F prog arg_count k (Nil,0)))) code)
       (stack_state_memory t)
       (stack_state_mdomain t)
       (stack_state_sh_mdomain t)
       (K I)
       (\(bm0,cfg) progs.
          let (progs,fs,bm) = compile_word_to_stack ac F k progs (Nil,bm0) in
          OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND bm,cfg)))
            (stack_state_compile t cfg progs))
       coracle
       (stack_state_code_buffer t)
       (stack_state_data_buffer t)
       (stack_state_gc_fun t)
       0
       (stack_state_clock t)
       0
       code
       (stack_state_be t)
       (stack_state_ffi t)`;;

(* W2SP4AUX: the frame size computed by compile_prog does not depend on    *)
(* the bitmaps                                                               *)
let W2SP4AUX_compile_prog_f = prove
 (`!(ac:(A)asm_config) perf prog arg_count k bs bs'.
     FST (SND (word_to_stack_compile_prog ac perf prog arg_count k bs)) =
     FST (SND (word_to_stack_compile_prog ac perf prog arg_count k bs'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  MAP_EVERY (fun b ->
    STRUCT_CASES_TAC (ISPEC (vsubst [b,`bb:(A word)app_list#num`]
      `word_to_stack_comp (ac:(A)asm_config) perf prog bb
         (k, (if MAX ((max_var prog DIV 2 + 1) - k) (arg_count - k) = 0 then 0
              else MAX ((max_var prog DIV 2 + 1) - k) (arg_count - k) + 1),
          MAX ((max_var prog DIV 2 + 1) - k) (arg_count - k))`) PAIR_SURJECTIVE))
    [`bs:(A word)app_list#num`; `bs':(A word)app_list#num`] THEN
  REWRITE_TAC[pair_CASE; FST; SND]);;

(* HOL4 line 10429 *)
let init_state_ok_IMP_state_rel = prove
 (`!(t:(A,C,FFI)stack_state) k code ac coracle.
     lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
     lookup wl_store_consts_stub_location (stack_state_code t) =
       SOME (store_consts_stub k) /\
     (!n word_prog arg_count.
        lookup n code = SOME (arg_count,word_prog)
        ==> post_alloc_conventions k word_prog /\
            flat_exp_conventions word_prog /\
            ?bs i bs2 i2 f stack_prog.
              word_to_stack_compile_prog ac F word_prog arg_count k (bs,i) =
                (stack_prog,f,(bs2,i2)) /\
              LENGTH (append bs) <= i /\
              i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
              isPREFIX (append bs2)
                (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
              lookup n (stack_state_code t) = SOME stack_prog) /\
     domain (stack_state_code t) =
       raise_stub_location INSERT wl_store_consts_stub_location INSERT domain code /\
     init_state_ok ac k t coracle
     ==> word_to_stackProof_state_rel ac k 0 0
           (word_to_stackProof_make_init ac k t code coracle) t [] 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; word_to_stackProof_make_init_def;
              init_state_ok_def; stack_size_rel_iff; (record_info "wl_state").ri_accessors] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                stack_state_stack_space t = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:((A)word_loc)list->num` o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "DROP"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[LENGTH_DROP; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_stack_size ([]:((A)stack_frame)list) = SOME 1` ASSUME_TAC THENL
   [REWRITE_TAC[wl_stack_size_def; ITLIST]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; the_def; LE_REFL; option_CLAUSES] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `word_prog:(A)wl_prog`; `arg_count:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `word_prog:(A)wl_prog`; `arg_count:num`] o
      check (fun th -> try let b = snd(strip_forall(concl th)) in
                           is_imp b && fst(dest_const(fst(strip_comb(lhs(lhand b))))) = "lookup"
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `bs:(A word)app_list` (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN
        `bs2:(A word)app_list` (X_CHOOSE_THEN `i2:num` (X_CHOOSE_THEN `f:num`
        (X_CHOOSE_THEN `stack_prog:(A)stack_prog` STRIP_ASSUME_TAC)))))))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`bs:(A word)app_list`; `i:num`; `bs2:(A word)app_list`; `i2:num`;
                          `f:num`; `stack_prog:(A)stack_prog`] THEN
    ASM_REWRITE_TAC[lookup_mapi; OPTION_MAP_DEF; the_def] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[ISPECL [`ac:(A)asm_config`; `F`; `word_prog:(A)wl_prog`; `arg_count:num`;
                        `k:num`; `Nil:(A word)app_list,0`; `bs:(A word)app_list,i:num`]
                  W2SP4AUX_compile_prog_f] THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state)) /\
                HD (stack_state_bitmaps t) = word 4` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "isPREFIX" with Failure _ -> false)) THEN
    STRUCT_CASES_TAC (ISPEC `stack_state_bitmaps (t:(A,C,FFI)stack_state)` list_CASES) THEN
    REWRITE_TAC[isPREFIX_THM; LENGTH; HD] THEN SIMP[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC wf_insert THEN REWRITE_TAC[wf_def]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; DROP; TAKE] THEN CONJ_TAC THENL
   [REWRITE_TAC[word_to_stackProof_stack_rel_def; ALL; abs_stack_def; LENGTH; LT_REFL] THEN
    SIMP[stack_rel_aux_def];
    REWRITE_TAC[lookup_insert; lookup_def] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4 line 10467: val init_state_ok_semantics = state_rel_IMP_semantics   *)
(* |> Q.INST [s |-> make_init ac k t code coracle] |> ... (a derived        *)
(* theorem: the hypotheses of init_state_ok_IMP_state_rel, then that of     *)
(* state_rel_IMP_semantics)                                                  *)
let init_state_ok_semantics = prove
 (`!(t:(A,C,FFI)stack_state) k code ac coracle start.
     lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
     lookup wl_store_consts_stub_location (stack_state_code t) =
       SOME (store_consts_stub k) /\
     (!n word_prog arg_count.
        lookup n code = SOME (arg_count,word_prog)
        ==> post_alloc_conventions k word_prog /\
            flat_exp_conventions word_prog /\
            ?bs i bs2 i2 f stack_prog.
              word_to_stack_compile_prog ac F word_prog arg_count k (bs,i) =
                (stack_prog,f,(bs2,i2)) /\
              LENGTH (append bs) <= i /\
              i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
              isPREFIX (append bs2)
                (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
              lookup n (stack_state_code t) = SOME stack_prog) /\
     domain (stack_state_code t) =
       raise_stub_location INSERT wl_store_consts_stub_location INSERT domain code /\
     init_state_ok ac k t coracle /\
     ~(wl_semantics (word_to_stackProof_make_init ac k t code coracle) start = Fail)
     ==> stack_semantics start t IN
         extend_with_resource_limit
           {wl_semantics (word_to_stackProof_make_init ac k t code coracle) start}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC state_rel_IMP_semantics THEN
  MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `[]:num list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC init_state_ok_IMP_state_rel THEN
  ASM_REWRITE_TAC[]);;

(* W2SP4AUX: W2SP4AUX_sim when the word program is safe for space: no     *)
(* stack overflow, so the results correspond                                *)
let W2SP4AUX_sim_safe = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens start kc.
     word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\
     ~(FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s)) =
       SOME wl_Error) /\
     word_lang_safe_for_space s start
     ==> ?ck.
       OPTION_MAP compile_result
          (FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s))) =
        FST (stack_evaluate (stack_Call NONE (INL start) NONE,
                             stack_state_clock_fupd (K (kc + ck)) t)) /\
        wl_state_ffi
          (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K kc) s))) =
        stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL start) NONE,
                                              stack_state_clock_fupd (K (kc + ck)) t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`ac:(A)asm_config`; `k:num`; `s:(A,num#C,FFI)wl_state`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`; `start:num`; `kc:num`]
            W2SP4AUX_sim) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kc:num`;
    mk_comb(`FST:((A)wl_result)option#(A,num#C,FFI)wl_state->((A)wl_result)option`,
            w2sp4aux_wev `kc:num`);
    mk_comb(`SND:((A)wl_result)option#(A,num#C,FFI)wl_state->(A,num#C,FFI)wl_state`,
            w2sp4aux_wev `kc:num`)] o
    REWRITE_RULE[word_lang_safe_for_space_def; LET_DEF; LET_END_DEF]) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[the_def] THEN
  MATCH_MP_TAC(TAUT `~d ==> ~(a /\ b /\ c /\ d)`) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_binary "<=" o concl)) THEN ARITH_TAC);;

(* HOL4 line 10473 *)
let state_rel_IMP_semantics' = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens start.
     word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\ ~(wl_semantics s start = Fail) /\
     word_lang_safe_for_space s start
     ==> stack_semantics start t = wl_semantics s start`,
  REPEAT STRIP_TAC THEN W2SP4AUX_SEM_FACTS_TAC THEN
  SUBGOAL_THEN (mk_forall(`kc:num`, w2sp4aux_concl W2SP4AUX_sim_safe)) (LABEL_TAC "sims") THENL
   [GEN_TAC THEN MATCH_MP_TAC W2SP4AUX_sim_safe THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `lens:num list`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "wok" (STRIP_ASSUME_TAC o SPEC `kc:num`) THEN
    ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"];
    ALL_TAC] THEN
  ASM_CASES_TAC (mk_exists(`kw:num`, mk_neg(mk_eq(mk_comb(
    `FST:((A)wl_result)option#(A,num#C,FFI)wl_state->((A)wl_result)option`,
    w2sp4aux_wev `kw:num`), `SOME (wl_TimeOut:(A)wl_result)`)))) THENL
   [(* the word program terminates *)
    FIRST_X_ASSUM(X_CHOOSE_TAC `kw:num`) THEN
    MP_TAC (ISPEC (w2sp4aux_wev `kw:num`) PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`rw:((A)wl_result)option`; `sw:(A,num#C,FFI)wl_state`] THEN
    DISCH_THEN(LABEL_TAC "evw") THEN
    USE_THEN "wok" (MP_TAC o SPEC `kw:num`) THEN
    USE_THEN "sims" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `kw:num`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    USE_THEN "evw" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
    MP_TAC (ISPEC (w2sp4aux_sev `kw + ck:num`) PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r1:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`] THEN
    DISCH_THEN(LABEL_TAC "evs") THEN
    USE_THEN "evs" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
    DISCH_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPEC `rw:((A)wl_result)option` W2SP4AUX_outcome_compile) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `outcome:outcome` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r:(A)stack_result` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ocs"))))) THEN
    MP_TAC (SPECL [`s:(A,num#C,FFI)wl_state`; `start:num`; `kw:num`;
                   `rw:((A)wl_result)option`; `sw:(A,num#C,FFI)wl_state`; `outcome:outcome`]
             W2SP4AUX_word_sem_term) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "evw" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `start:num`; `kw + ck:num`; `r:(A)stack_result`;
                   `t1:(A,C,FFI)stack_state`; `outcome:outcome`] W2SP4AUX_stack_sem_term) THEN
    ANTS_TAC THENL
     [USE_THEN "ocs" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "sok" ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "evs" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    (* the word program diverges *)
    FIRST_X_ASSUM(LABEL_TAC "wto" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC (SPECL [`s:(A,num#C,FFI)wl_state`; `start:num`] W2SP4AUX_word_sem_div) THEN
    USE_THEN "wto" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC (mk_exists(`ks:num`, mk_neg(mk_eq(mk_comb(
      `FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`,
      w2sp4aux_sev `ks:num`), `SOME (stack_TimeOut:(A)stack_result)`)))) THENL
     [(* the stack program cannot stop *)
      FIRST_X_ASSUM(X_CHOOSE_TAC `ks:num`) THEN
      USE_THEN "sims" (X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `ks:num`) THEN
      USE_THEN "wto" (fun th -> REWRITE_TAC[th; OPTION_MAP_DEF; compile_result_def]) THEN
      MP_TAC (SPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                     `t:(A,C,FFI)stack_state`; `ks:num`; `ks + ck:num`]
               W2SP4AUX_stack_add_clock) THEN
      ASM_REWRITE_TAC[LE_ADD] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
      (* both diverge *)
      FIRST_X_ASSUM(LABEL_TAC "sto" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `start:num`] W2SP4AUX_stack_sem_div) THEN
      USE_THEN "sto" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[injectivity "behaviour"] THEN
      MATCH_MP_TAC W2SP4AUX_lub_eq THEN
      X_GEN_TAC `kc:num` THEN
      USE_THEN "sims" (X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `kc:num`) THEN
      EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 10703: val init_state_ok_semantics' (as init_state_ok_semantics, *)
(* from state_rel_IMP_semantics')                                            *)
let init_state_ok_semantics' = prove
 (`!(t:(A,C,FFI)stack_state) k code ac coracle start.
     lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
     lookup wl_store_consts_stub_location (stack_state_code t) =
       SOME (store_consts_stub k) /\
     (!n word_prog arg_count.
        lookup n code = SOME (arg_count,word_prog)
        ==> post_alloc_conventions k word_prog /\
            flat_exp_conventions word_prog /\
            ?bs i bs2 i2 f stack_prog.
              word_to_stack_compile_prog ac F word_prog arg_count k (bs,i) =
                (stack_prog,f,(bs2,i2)) /\
              LENGTH (append bs) <= i /\
              i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
              isPREFIX (append bs2)
                (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
              lookup n (stack_state_code t) = SOME stack_prog) /\
     domain (stack_state_code t) =
       raise_stub_location INSERT wl_store_consts_stub_location INSERT domain code /\
     init_state_ok ac k t coracle /\
     ~(wl_semantics (word_to_stackProof_make_init ac k t code coracle) start = Fail) /\
     word_lang_safe_for_space (word_to_stackProof_make_init ac k t code coracle) start
     ==> stack_semantics start t =
         wl_semantics (word_to_stackProof_make_init ac k t code coracle) start`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC state_rel_IMP_semantics' THEN
  MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `[]:num list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC init_state_ok_IMP_state_rel THEN
  ASM_REWRITE_TAC[]);;

(* W2SP4AUX: the hypotheses of init_state_ok_semantics from those of      *)
(* compile_semantics                                                        *)
let W2SP4AUX_compile_init = prove
 (`!(t:(A,C,FFI)stack_state) asm_conf code k.
     stack_state_code t =
       fromAList (SND (SND (SND (word_to_stack_compile asm_conf F code)))) /\
     k = asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)) /\
     ALOOKUP code raise_stub_location = NONE /\
     ALOOKUP code wl_store_consts_stub_location = NONE /\
     isPREFIX (FST (word_to_stack_compile asm_conf F code)) (stack_state_bitmaps t) /\
     ALL (\(n,m,prog).
            flat_exp_conventions prog /\
            post_alloc_conventions
              (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)))
              prog) code
     ==> lookup raise_stub_location (stack_state_code t) = SOME (raise_stub F k) /\
         lookup wl_store_consts_stub_location (stack_state_code t) =
           SOME (store_consts_stub k) /\
         (!n word_prog arg_count.
            lookup n (fromAList code) = SOME (arg_count,word_prog)
            ==> post_alloc_conventions k word_prog /\
                flat_exp_conventions word_prog /\
                ?bs i bs2 i2 f stack_prog.
                  word_to_stack_compile_prog asm_conf F word_prog arg_count k (bs,i) =
                    (stack_prog,f,(bs2,i2)) /\
                  LENGTH (append bs) <= i /\
                  i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
                  isPREFIX (append bs2)
                    (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
                  lookup n (stack_state_code t) = SOME stack_prog) /\
         domain (stack_state_code t) =
           raise_stub_location INSERT wl_store_consts_stub_location INSERT
           domain (fromAList code)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC (ISPEC `compile_word_to_stack (asm_conf:(A)asm_config) F
    (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf))) code
    (misc_List [word 4],1)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`progs:(num#(A)stack_prog)list`; `p':num list#(A word)app_list#num`] THEN
  MP_TAC (ISPEC `p':num list#(A word)app_list#num` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`fs:num list`; `bm:(A word)app_list#num`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC (ISPEC `bm:(A word)app_list#num` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`bs':(A word)app_list`; `i':num`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; FST; SND] THEN STRIP_TAC THEN
  UNDISCH_TAC `k = asm_config_reg_count (asm_conf:(A)asm_config) -
                   (5 + LENGTH (asm_config_avoid_regs asm_conf))` THEN
  DISCH_THEN(SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[lookup_fromAList; ALOOKUP_THM; domain_fromAList; MAP; set_of_list] THEN
  REWRITE_TAC[raise_stub_location_eq; wl_store_consts_stub_location_eq] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[raise_stub_location_eq; wl_store_consts_stub_location_eq]) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `word_prog:(A)wl_prog`; `arg_count:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(n = 5) /\ ~(n = 6)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN ASM_MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC (ISPECL [`code:(num#num#(A)wl_prog)list`;
                    `asm_config_reg_count (asm_conf:(A)asm_config) -
                     (5 + LENGTH (asm_config_avoid_regs asm_conf))`;
                    `misc_List [word 4:A word]`; `1`; `progs:(num#(A)stack_prog)list`;
                    `fs:num list`; `bs':(A word)app_list`; `i':num`; `n:num`;
                    `arg_count:num`; `word_prog:(A)wl_prog`;
                    `stack_state_bitmaps (t:(A,C,FFI)stack_state)`;
                    `asm_conf:(A)asm_config`; `F`] compile_word_to_stack_IMP_ALOOKUP) THEN
    REWRITE_TAC[append_thm; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[LE_0; DROP];
    FIRST_ASSUM(MP_TAC o MATCH_MP MAP_FST_compile_word_to_stack) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* HOL4 line 10709 *)
let word_to_stackProof_compile_semantics = prove
 (`!(t:(A,C,FFI)stack_state) asm_conf code k coracle start.
     stack_state_code t =
       fromAList (SND (SND (SND (word_to_stack_compile asm_conf F code)))) /\
     k = asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)) /\
     init_state_ok asm_conf k t coracle /\
     ALOOKUP code raise_stub_location = NONE /\
     ALOOKUP code wl_store_consts_stub_location = NONE /\
     isPREFIX (FST (word_to_stack_compile asm_conf F code)) (stack_state_bitmaps t) /\
     ALL (\(n,m,prog).
            flat_exp_conventions prog /\
            post_alloc_conventions
              (asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)))
              prog) code /\
     ~(wl_semantics (word_to_stackProof_make_init asm_conf k t (fromAList code) coracle)
         start = Fail)
     ==> stack_semantics start t IN
         extend_with_resource_limit'
           (word_lang_safe_for_space
              (word_to_stackProof_make_init asm_conf k t (fromAList code) coracle) start)
           {wl_semantics (word_to_stackProof_make_init asm_conf k t (fromAList code) coracle)
              start}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`t:(A,C,FFI)stack_state`; `asm_conf:(A)asm_config`;
                 `code:(num#num#(A)wl_prog)list`; `k:num`] W2SP4AUX_compile_init) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[extend_with_resource_limit'_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[IN_SING] THEN MATCH_MP_TAC init_state_ok_semantics';
    MATCH_MP_TAC init_state_ok_semantics] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 10760 *)
let stack_move_no_labs = prove
 (`!n a b c (p:(A)stack_prog).
     stack_extract_labels p = [] ==> stack_extract_labels (stack_move n a b c p) = []`,
  INDUCT_TAC THEN SIMP[stack_move_def; stack_extract_labels_def; APPEND]);;

(* HOL4 line 10769 *)
let extract_labels_copy_ret_aux = prove
 (`!k f n. stack_extract_labels (copy_ret_aux k f n:(A)stack_prog) = []`,
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[stack_extract_labels_def; stack_list_Seq_def; LET_DEF; LET_END_DEF; APPEND]);;

let _ = cake_add_simps [extract_labels_copy_ret_aux];;

(* HOL4 line 10777 *)
let extract_labels_copy_ret = prove
 (`!perf b (kf:num#num#C) (vs:B list) (kont:(A)stack_prog).
     stack_extract_labels (copy_ret perf b kf vs kont) = stack_extract_labels kont`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_extract_labels_def; SeqStackFree_def; APPEND] THEN
  COND_CASES_TAC THEN SIMP[stack_extract_labels_def; APPEND]);;

let _ = cake_add_simps [extract_labels_copy_ret];;

(* HOL4 line 10783 *)
let extract_labels_wStackLoad_Skip = prove
 (`!xs. stack_extract_labels (wStackLoad xs (stack_Skip:(A)stack_prog)) = []`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[wStackLoad_def; stack_extract_labels_def];
    POP_ASSUM MP_TAC THEN SPEC_TAC(`h:num#num`,`h:num#num`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SIMP[wStackLoad_def; stack_extract_labels_def; APPEND]]);;

let _ = cake_add_simps [extract_labels_wStackLoad_Skip];;

(* HOL4 line 10794 *)
let extract_labels_stack_move_StackAlloc = prove
 (`!n start offset i k.
     stack_extract_labels (stack_move n start offset i (StackAlloc k:(A)stack_prog)) = []`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC stack_move_no_labs THEN
  REWRITE_TAC[stack_extract_labels_def]);;

let _ = cake_add_simps [extract_labels_stack_move_StackAlloc];;

(* W2SP4AUX: tactics for the syntactic lemmas about word_to_stack_comp     *)
(* below (HOL4 does these steps with EVAL_TAC, every_case_tac and gvs).      *)
(* W2SP4AUX_SUM_CASES_TAC splits a free variable of a sum type,             *)
(* W2SP4AUX_INST_SPLIT_TAC one of an asm instruction type (wInst and         *)
(* wShareInst are defined by cases on these), W2SP4AUX_CALL_SPLIT_TAC the    *)
(* return and handler options of a Call, W2SP4AUX_KF_SPLIT_TAC the triple kf, *)
(* and W2SP4AUX_COMP_UNFOLD_TAC v unfolds the assumption                     *)
(* word_to_stack_comp ... = (v,_) once.                                     *)
let w2sp4aux_head_is c tm =
  try fst(dest_const(fst(strip_comb tm))) = c with Failure _ -> false;;
let w2sp4aux_lhs_head_is c tm =
  try w2sp4aux_head_is c (lhs tm) with Failure _ -> false;;

let W2SP4AUX_SUM_CASES_TAC : tactic = fun (asl,w as g) ->
  let v = find (fun v -> match type_of v with Tyapp("sum",_) -> true | _ -> false) (frees w) in
  STRUCT_CASES_TAC (ISPEC v (cases "sum")) g;;

let W2SP4AUX_split_tys = ["inst"; "asm_arith"; "memop"; "addr"; "reg_imm"; "fp"];;
let W2SP4AUX_INST_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let v = find (fun v -> match type_of v with
                  Tyapp(n,_) -> mem n W2SP4AUX_split_tys | _ -> false) (frees w) in
  let n = fst(dest_type(type_of v)) in
  STRUCT_CASES_TAC (ISPEC v (cases n)) g;;

let W2SP4AUX_option5_CASES = prove
 (`!x:(A#B#C#D#E)option. x = NONE \/ ?a b c d e. x = SOME (a,b,c,d,e)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:(A#B#C#D#E)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MAP_EVERY EXISTS_TAC [`FST(a:A#B#C#D#E)`; `FST(SND(a:A#B#C#D#E))`;
    `FST(SND(SND(a:A#B#C#D#E)))`; `FST(SND(SND(SND(a:A#B#C#D#E))))`;
    `SND(SND(SND(SND(a:A#B#C#D#E))))`] THEN REWRITE_TAC[PAIR]);;

let W2SP4AUX_option4_CASES = prove
 (`!x:(A#B#C#D)option. x = NONE \/ ?a b c d. x = SOME (a,b,c,d)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:(A#B#C#D)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MAP_EVERY EXISTS_TAC [`FST(a:A#B#C#D)`; `FST(SND(a:A#B#C#D))`;
    `FST(SND(SND(a:A#B#C#D)))`; `SND(SND(SND(a:A#B#C#D)))`] THEN REWRITE_TAC[PAIR]);;

let W2SP4AUX_CALL_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let is_call th = try let l = lhs(concl th) in
                       fst(dest_const(fst(strip_comb l))) = "word_to_stack_comp" &&
                       fst(dest_const(fst(strip_comb (el 2 (snd(strip_comb l)))))) = "wl_Call"
                   with Failure _ -> false in
  match filter (is_call o snd) asl with
    [] -> ALL_TAC g
  | (_,th)::_ ->
      let args = snd(strip_comb(el 2 (snd(strip_comb(lhs(concl th)))))) in
      let ret = el 0 args and handler = el 3 args in
      (DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
         (ISPEC ret W2SP4AUX_option5_CASES) THEN
       DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
         (ISPEC handler W2SP4AUX_option4_CASES)) g;;

let W2SP4AUX_KF_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let fvs = itlist (union o frees o concl o snd) asl (frees w) in
  match filter (fun v -> type_of v = `:num#num#num`) fvs with
    [] -> ALL_TAC g
  | kf::_ ->
      let k = variant fvs `kk:num` in
      let f = variant (k::fvs) `ff:num` in
      let f' = variant (k::f::fvs) `ff':num` in
      let th = prove(mk_exists(k,mk_exists(f,mk_exists(f',
                 mk_eq(kf,mk_pair(k,mk_pair(f,f')))))),
                 MESON_TAC[PAIR]) in
      (X_CHOOSE_THEN k (X_CHOOSE_THEN f (X_CHOOSE_THEN f' SUBST_ALL_TAC)) th) g;;

let w2sp4aux_is_comp_eq v th =
  try let l,r = dest_eq(concl th) in
      fst(dest_const(fst(strip_comb l))) = "word_to_stack_comp" &&
      fst(dest_var(fst(dest_pair r))) = v
  with Failure _ -> false;;

let W2SP4AUX_COMP_UNFOLD_TAC v : tactic =
  FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_is_comp_eq v)) THEN
  ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[case_eq "option"; case_eq "reg_imm"; case_eq "wl_exp"; case_eq "prod";
              COND_CASE_EQ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[option_INJ; PAIR_EQ]);;

(* W2SP4AUX: compile_prog unfolded *)
let W2SP4AUX_compile_prog_eq = prove
 (`!(ac:(A)asm_config) perf p n k bs prog f bs'.
     word_to_stack_compile_prog ac perf p n k bs = (prog,f,bs') <=>
     ?q1. f = (if MAX ((max_var p DIV 2 + 1) - k) (n - k) = 0 then 0
               else MAX ((max_var p DIV 2 + 1) - k) (n - k) + 1) /\
          word_to_stack_comp ac perf p bs (k,f,MAX ((max_var p DIV 2 + 1) - k) (n - k)) =
            (q1,bs') /\
          prog = stack_Seq (StackAlloc (f - (n - k))) q1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_stack_compile_prog_def; LET_DEF; LET_END_DEF; case_eq "prod"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* W2SP4AUX: the registers that wReg1, wReg2 and format_var give are below *)
(* k + 2                                                                    *)
let W2SP4AUX_wReg1_bound = prove
 (`!r k f f' l n. wReg1 r (k,f,f') = (l,n)
                  ==> n < k + 2 /\ ALL (\(x:num,i:num). x < k + 2) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wReg1_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_ARITH_TAC);;

let W2SP4AUX_wReg2_bound = prove
 (`!r k f f' l n. wReg2 r (k,f,f') = (l,n)
                  ==> n < k + 2 /\ ALL (\(x:num,i:num). x < k + 2) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wReg2_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_ARITH_TAC);;

let W2SP4AUX_format_var_bound = prove
 (`!k a r. format_var k a = INL r ==> r < k + 2`,
  GEN_TAC THEN MATCH_MP_TAC(MESON[option_CASES]
    `(P NONE) /\ (!x. P (SOME x)) ==> !a:num option. P a`) THEN
  REWRITE_TAC[format_var_def] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN SIMP[] THEN ASM_ARITH_TAC);;

(* W2SP4AUX: case splits on free variables of sum and option types *)
let W2SP4AUX_SUM_CASES_ALL_TAC : tactic = fun (asl,w as g) ->
  let v = find (fun v -> match type_of v with Tyapp("sum",_) -> true | _ -> false) (frees w) in
  DISJ_CASES_THEN (CHOOSE_THEN SUBST_ALL_TAC) (ISPEC v (cases "sum")) g;;

let W2SP4AUX_TY_CASES_TAC (tyname:string) (th:thm) : tactic = fun (asl,w as g) ->
  let fvs = itlist (union o frees o concl o snd) asl (frees w) in
  let vs = filter (fun v -> match type_of v with
                  Tyapp(n,_) -> n = tyname | _ -> false) fvs in
  let rec go vs = match vs with
      [] -> failwith "W2SP4AUX_TY_CASES_TAC"
    | v::rest -> (try let th' = ISPEC v th in
                      if is_disj (concl th')
                      then DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) th' g
                      else REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC th' g
                  with Failure _ -> go rest) in
  go vs;;

(* W2SP4AUX: a property of every compiled function from one of each       *)
(* compile_prog result                                                       *)
let W2SP4AUX_compile_word_to_stack_ALL = prove
 (`!(P:num->(A)stack_prog->bool) (ac:(A)asm_config) perf k p bs q fs bs'.
     (!n m pp bs0 prog f bs1.
        MEM (n,m,pp) p /\ word_to_stack_compile_prog ac perf pp m k bs0 = (prog,f,bs1)
        ==> P n prog) /\
     compile_word_to_stack ac perf k p bs = (q,fs,bs')
     ==> ALL (\(n,prog). P n prog) q`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `n0:num` THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `m0:num` THEN
  X_GEN_TAC `p0:(A)wl_prog` THEN
  REWRITE_TAC[compile_word_to_stack_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hp") MP_TAC) THEN
  MP_TAC (ISPEC `word_to_stack_compile_prog (ac:(A)asm_config) perf p0 m0 k bs`
            PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`prog0:(A)stack_prog`; `r0:num#(A word)app_list#num`] THEN
  MP_TAC (ISPEC `r0:num#(A word)app_list#num` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f0:num`; `bm0:(A word)app_list#num`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC (ISPEC `compile_word_to_stack (ac:(A)asm_config) perf k t bm0` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`progs0:(num#(A)stack_prog)list`; `r1:num list#(A word)app_list#num`] THEN
  MP_TAC (ISPEC `r1:num list#(A word)app_list#num` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`fs0:num list`; `bm1:(A word)app_list#num`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL
   [USE_THEN "hp" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`m0:num`; `p0:(A)wl_prog`; `bs:(A word)app_list#num`; `f0:num`;
                          `bm0:(A word)app_list#num`] THEN
    ASM_REWRITE_TAC[MEM];
    USE_THEN "ih" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`bm0:(A word)app_list#num`; `fs0:num list`;
                          `bs':(A word)app_list#num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "hp" MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM]]);;


(* W2SP4AUX: the labels of the pieces of a compiled program *)
let W2SP4AUX_wStackLoad_labels = prove
 (`!l (p:(A)stack_prog). stack_extract_labels (wStackLoad l p) = stack_extract_labels p`,
  MATCH_MP_TAC wStackLoad_ind THEN SIMP[wStackLoad_def; stack_extract_labels_def; APPEND]);;

let W2SP4AUX_wRegWrite1_labels = prove
 (`!(g:num->(A)stack_prog) r kf.
     (!n. stack_extract_labels (g n) = []) ==> stack_extract_labels (wRegWrite1 g r kf) = []`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_extract_labels_def; APPEND]);;

let W2SP4AUX_wRegWrite2_labels = prove
 (`!(g:num->(A)stack_prog) r kf.
     (!n. stack_extract_labels (g n) = []) ==> stack_extract_labels (wRegWrite2 g r kf) = []`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_extract_labels_def; APPEND]);;

let W2SP4AUX_wMoveSingle_labels = prove
 (`!xy kf. stack_extract_labels (wMoveSingle xy kf:(A)stack_prog) = []`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  SIMP[stack_extract_labels_def; APPEND]);;

let W2SP4AUX_wMoveAux_labels = prove
 (`!xs kf. stack_extract_labels (wMoveAux xs kf:(A)stack_prog) = []`,
  MATCH_MP_TAC wMoveAux_ind THEN REPEAT STRIP_TAC THEN
  SIMP[wMoveAux_def; stack_extract_labels_def; W2SP4AUX_wMoveSingle_labels; APPEND]);;

let W2SP4AUX_wMove_labels = prove
 (`!xs kf. stack_extract_labels (wMove xs kf:(A)stack_prog) = []`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wMove_def; W2SP4AUX_wMoveAux_labels]);;

let W2SP4AUX_wInst_labels = prove
 (`!(i:(A)inst) kf. stack_extract_labels (wInst i kf) = []`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[W2SP4AUX_wStackLoad_labels]);
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_labels THEN GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite2_labels THEN GEN_TAC THEN BETA_TAC;
                 COND_CASES_TAC]) THEN
  SIMP[stack_extract_labels_def]);;

let W2SP4AUX_wShareInst_labels = prove
 (`!op v ad kf. stack_extract_labels (wShareInst op v ad kf:(A)stack_prog) = []`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[W2SP4AUX_wStackLoad_labels]);
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_labels THEN GEN_TAC THEN BETA_TAC]) THEN
  SIMP[stack_extract_labels_def]);;

let W2SP4AUX_call_dest_labels = prove
 (`!d a kf (q0:(A)stack_prog) d'. call_dest d a kf = (q0,d') ==> stack_extract_labels q0 = []`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[stack_extract_labels_def; W2SP4AUX_wStackLoad_labels]);;

let W2SP4AUX_wLive_labels = prove
 (`!live (bs:(A word)app_list#num) kf q bs'.
     wLive live bs kf = (q,bs') ==> stack_extract_labels q = []`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[stack_extract_labels_def; APPEND]);;

let W2SP4AUX_perf_labels = prove
 (`(!l1 l2 kf0. stack_extract_labels (perf_call_prefix l1 l2 kf0:(A)stack_prog) = []) /\
   stack_extract_labels (perf_call_suffix:(A)stack_prog) = [] /\
   (!perf l1 l2 (kff:num#B#C).
      stack_extract_labels (PushHandler perf l1 l2 kff:(A)stack_prog) = []) /\
   (!perf (kff:num#B#C) (prog:(A)stack_prog).
      stack_extract_labels (PopHandler perf kff prog) = stack_extract_labels prog) /\
   (!perf (dest:B+C) arg_count kff.
      stack_extract_labels (StackHandlerArgs perf dest arg_count kff:(A)stack_prog) = [])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[perf_call_prefix_def; perf_call_suffix_def; PushHandler_def; PopHandler_def;
              StackHandlerArgs_def; StackArgs_def; LET_DEF; LET_END_DEF] THEN
  TRY COND_CASES_TAC THEN
  SIMP[stack_extract_labels_def; stack_list_Seq_def; APPEND;
       extract_labels_stack_move_StackAlloc]);;

let W2SP4AUX_DERIVE_LABELS_TAC : tactic = fun (asl,w as g) ->
  let derive th =
    let c = concl th in
    let f = try fst(dest_const(fst(strip_comb(lhs c)))) with Failure _ -> "" in
    match f with
      "call_dest" -> [MATCH_MP W2SP4AUX_call_dest_labels th]
    | "wLive" -> [MATCH_MP W2SP4AUX_wLive_labels th]
    | _ -> [] in
  let ths = flat (map (fun (_,th) -> try derive th with Failure _ -> []) asl) in
  MAP_EVERY ASSUME_TAC ths g;;

let W2SP4AUX_comp_labels = prove
 (`!(ac:(A)asm_config) perf p bs kf prog' bs'.
     word_to_stack_comp ac perf p bs kf = (prog',bs')
     ==> stack_extract_labels prog' = wordConvs_extract_labels p`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN W2SP4AUX_DERIVE_LABELS_TAC THEN
  SIMP[stack_extract_labels_def; wordConvs_extract_labels_def; COND_RAND; COND_RATOR;
       SeqStackFree_def; W2SP4AUX_perf_labels; W2SP4AUX_wStackLoad_labels;
       W2SP4AUX_wMove_labels; W2SP4AUX_wInst_labels; W2SP4AUX_wShareInst_labels;
       extract_labels_copy_ret; StackArgs_def; extract_labels_stack_move_StackAlloc;
       APPEND; LET_DEF; LET_END_DEF] THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wRegWrite1_labels THEN SIMP[stack_extract_labels_def]) THEN
  TRY BINOP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 10803 *)
let word_to_stack_lab_pres = prove
 (`!(ac:(A)asm_config) perf p bs kf.
     wordConvs_extract_labels p =
     stack_extract_labels (FST (word_to_stack_comp ac perf p bs kf))`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC W2SP4AUX_comp_labels THEN
  MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `perf:bool`; `bs:(A word)app_list#num`;
    `kf:num#num#num`; `SND (word_to_stack_comp (ac:(A)asm_config) perf p bs kf)`] THEN
  REWRITE_TAC[PAIR]);;

(* W2SP4AUX: compile_word_to_stack_lab_pres (HOL4 line 10918), proved here *)
(* for word_to_stack_compile_lab_pres                                         *)
let W2SP4AUX_compile_prog_labels = prove
 (`!(ac:(A)asm_config) perf pp m k bs0 prog f bs1.
     word_to_stack_compile_prog ac perf pp m k bs0 = (prog,f,bs1)
     ==> stack_extract_labels prog = wordConvs_extract_labels pp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[W2SP4AUX_compile_prog_eq] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[stack_extract_labels_def; APPEND] THEN
  MATCH_MP_TAC W2SP4AUX_comp_labels THEN ASM_MESON_TAC[]);;

let W2SP4AUX_compile_word_to_stack_lab_pres = prove
 (`!p perf b q r (ac:(A)asm_config) k.
     compile_word_to_stack ac perf k p b = (q,r) /\
     ALL (\(l,m,e).
            ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels e) /\
            ALL_DISTINCT (wordConvs_extract_labels e)) p
     ==> ALL (\(l,e).
                ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels e) /\
                ALL_DISTINCT (stack_extract_labels e)) q`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (BETA_RULE (ISPEC
    `\l (e:(A)stack_prog). ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1))
                             (stack_extract_labels e) /\
                           ALL_DISTINCT (stack_extract_labels e)`
    W2SP4AUX_compile_word_to_stack_ALL)) THEN
  MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `perf:bool`; `k:num`;
    `p:(num#num#(A)wl_prog)list`; `b:(A word)app_list#num`; `FST (r:num list#(A word)app_list#num)`;
    `SND (r:num list#(A word)app_list#num)`] THEN
  ASM_REWRITE_TAC[PAIR] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP W2SP4AUX_compile_prog_labels) THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_head_is "ALL" o concl)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(l:num,m:num,pp:(A)wl_prog)`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 10881 *)
let word_to_stack_compile_lab_pres = prove
 (CASE_TERM `!(prog:(num#num#(A)wl_prog)list) (asm_conf:(A)asm_config).
     ALL (\(n,m,p).
            let labs = wordConvs_extract_labels p in
            ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
            ALL_DISTINCT labs) prog
     ==> let (bytes,c,f,p) = word_to_stack_compile asm_conf F prog in
         MAP FST p = CONS raise_stub_location (CONS wl_store_consts_stub_location
                       (MAP FST prog)) /\
         ALL (\(n,p).
                let labs = stack_extract_labels p in
                ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
                ALL_DISTINCT labs) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  REPEAT (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN REWRITE_TAC[MAP; ALL; FST] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def] THEN
  SIMP[stack_extract_labels_def; APPEND; ALL; ALL_DISTINCT] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP MAP_FST_compile_word_to_stack) THEN REFL_TAC;
    MATCH_MP_TAC W2SP4AUX_compile_word_to_stack_lab_pres THEN
    MAP_EVERY EXISTS_TAC [`prog:(num#num#(A)wl_prog)list`; `F`;
      `misc_List [word 4:A word],1`; `(fs:num list,bitmaps:(A word)app_list#num)`;
      `asm_conf:(A)asm_config`;
      `asm_config_reg_count (asm_conf:(A)asm_config) -
       (5 + LENGTH (asm_config_avoid_regs asm_conf))`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 10918 *)
let compile_word_to_stack_lab_pres = prove
 (`!p perf b q r (ac:(A)asm_config) k.
     compile_word_to_stack ac perf k p b = (q,r) /\
     ALL (\(l,m,e).
            ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels e) /\
            ALL_DISTINCT (wordConvs_extract_labels e)) p
     ==> ALL (\(l,e).
                ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels e) /\
                ALL_DISTINCT (stack_extract_labels e)) q`,
  MATCH_ACCEPT_TAC W2SP4AUX_compile_word_to_stack_lab_pres);;

(* HOL4 line 10944 *)
let EVEN_DIV_2_props = prove
 (`!a b. a MOD 2 = 0 /\ b MOD 2 = 0
         ==> (~(a = b) ==> ~(a DIV 2 = b DIV 2)) /\ (~(a = 0) ==> ~(a DIV 2 = 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`a:num`; `2`] DIVISION) THEN MP_TAC (SPECL [`b:num`; `2`] DIVISION) THEN
  ASM_REWRITE_TAC[ARITH_EQ; ADD_CLAUSES] THEN ARITH_TAC);;

(* HOL4 line 10956: val wconvs (a list of definitions for the proofs) *)

(* HOL4 line 10958 *)
let call_dest_stack_asm_name = prove
 (CASE_TERM `!d a k (q0:(A)stack_prog) d' (c:(A)asm_config).
     call_dest d a k = (q0,d')
     ==> stack_asm_name c q0 /\
         (match d' with INR r -> r <= FST k + 1 | INL l -> T)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CASE_REWRITE_TAC[] THEN SIMP[stack_asm_name_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP4AUX_wReg2_bound) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SPEC_TAC(`x1:(num#num)list`,`l:(num#num)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[wStackLoad_def; stack_asm_name_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[wStackLoad_def; stack_asm_name_def]);;

(* HOL4 line 10973 *)
let wLive_stack_asm_name = prove
 (`!kf (c:(A)asm_config) q (bs:(A word)app_list#num) q1 bs'.
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     wLive q bs kf = (q1,bs')
     ==> stack_asm_name c q1`,
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[stack_asm_name_def; inst_name_def; reg_name_def] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 10985 *)
let stack_move_stack_asm_name = prove
 (`!n start offset i (p:(A)stack_prog) (c:(A)asm_config).
     stack_asm_name c (stack_move n start offset i p) <=> stack_asm_name c p`,
  INDUCT_TAC THEN SIMP[stack_move_def; stack_asm_name_def]);;

let _ = cake_add_simps [stack_move_stack_asm_name];;

(* HOL4 line 10993 *)
let copy_ret_aux_stack_asm_name = prove
 (`!k f n (c:(A)asm_config). stack_asm_name c (copy_ret_aux k f n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[stack_asm_name_def; stack_list_Seq_def; LET_DEF; LET_END_DEF]);;

let _ = cake_add_simps [copy_ret_aux_stack_asm_name];;

(* HOL4 line 11001 *)
let copy_ret_stack_asm_name = prove
 (`!(c:(A)asm_config) perf b (kf:num#num#C) (vs:B list) kont.
     stack_asm_name c (copy_ret perf b kf vs kont) <=> stack_asm_name c kont`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_asm_name_def; SeqStackFree_def; copy_ret_aux_stack_asm_name] THEN
  COND_CASES_TAC THEN SIMP[stack_asm_name_def]);;

let _ = cake_add_simps [copy_ret_stack_asm_name];;

(* W2SP4AUX: the pieces of a compiled program satisfy stack_asm_name *)
let W2SP4AUX_wStackLoad_asm_name = prove
 (`!l (p:(A)stack_prog) (c:(A)asm_config).
     stack_asm_name c (wStackLoad l p) <=> stack_asm_name c p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[wStackLoad_def; stack_asm_name_def]);;

let W2SP4AUX_wInst_asm_name = prove
 (`!(c:(A)asm_config) i k f f'.
     4 < k /\ k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     every_var_inst is_phy_var i /\ inst_arg_convention i /\ inst_ok_less c i /\
     (asm_config_two_reg_arith c ==> two_reg_inst i)
     ==> stack_asm_name c (wInst i (k,f,f'))`,
  GEN_TAC THEN GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[every_var_inst_def; inst_arg_convention_def; inst_ok_less_def; two_reg_inst_def;
              every_var_imm_def; is_phy_var_def] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF; wReg1_def; wReg2_def; wRegWrite1_def;
              wRegWrite2_def] THEN
  REPEAT (FIRST [CHANGED_TAC (CASE_REWRITE_TAC[]); COND_CASES_TAC]) THEN
  SIMP[stack_asm_name_def; wStackLoad_def; APPEND; inst_name_def; arith_name_def;
       fp_name_def; addr_name_def; reg_name_def; reg_imm_name_def; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN REPEAT STRIP_TAC THEN
  TRY ASM_ARITH_TAC THEN
  ASM_MESON_TAC[EVEN_DIV_2_props]);;

let W2SP4AUX_wRegWrite1_asm_name = prove
 (`!(g:num->(A)stack_prog) r k f f' (c:(A)asm_config).
     (!n. n < k + 2 ==> stack_asm_name c (g n))
     ==> stack_asm_name c (wRegWrite1 g r (k,f,f'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[stack_asm_name_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let W2SP4AUX_OpCurrHeap_asm_name = prove
 (`!(c:(A)asm_config) b dst src k f f' x y.
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     (asm_config_two_reg_arith c ==> dst = src) /\
     wReg1 src (k,f,f') = (x,y)
     ==> stack_asm_name c (wStackLoad x (wRegWrite1 (\dst_r. stack_OpCurrHeap b dst_r y) dst
                                          (k,f,f')))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wReg1_def; wRegWrite1_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [CHANGED_TAC (CASE_REWRITE_TAC[]); COND_CASES_TAC]) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[W2SP4AUX_wStackLoad_asm_name; stack_asm_name_def; reg_name_def] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC) THEN
  ASM_ARITH_TAC);;

let W2SP4AUX_wMove_asm_name = prove
 (`!xs k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)
     ==> stack_asm_name c (wMove xs (k,f,f'):(A)stack_prog)`,
  SUBGOAL_THEN
   `!x y k f f' (c:(A)asm_config).
      k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
      (!r. x = INL r ==> r < k + 2) /\ (!r. y = INL r ==> r < k + 2)
      ==> stack_asm_name c (wMoveSingle (x,y) (k,f,f'):(A)stack_prog)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
    REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    SIMP[stack_asm_name_def; inst_name_def; arith_name_def; reg_name_def; reg_imm_name_def] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!xs kf (c:(A)asm_config).
      FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
      ALL (\(x,y). (!r. x = INL r ==> r < FST kf + 2) /\ (!r. y = INL r ==> r < FST kf + 2)) xs
      ==> stack_asm_name c (wMoveAux xs kf:(A)stack_prog)`
    ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC wMoveAux_ind THEN
    REWRITE_TAC[wMoveAux_def; stack_asm_name_def; ALL] THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[wMove_def] THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
    [`MAP (format_var k ## format_var k) (parmove (MAP (DIV2 ## DIV2) xs))`;
     `(k:num,f:num,f':num)`; `c:(A)asm_config`]) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; PAIR_MAP] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[W2SP4AUX_format_var_bound]);;

let W2SP4AUX_wShareInst_asm_name = prove
 (`!(c:(A)asm_config) op v ad off k f f'.
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     (op IN {Load16, Store16} ==> ~(asm_config_ISA c = Ag32)) /\
     (if op IN {asm_Load, asm_Store, asm_Load32, asm_Store32}
      then asm_offset_ok 0 (asm_config_addr_offset c) off
      else if op IN {Load16, Store16}
      then asm_offset_ok 0 (asm_config_hw_offset c) off
      else asm_offset_ok 0 (asm_config_byte_offset c) off)
     ==> stack_asm_name c (wShareInst op v (Addr ad off) (k,f,f'):(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; distinctness "memop"] THEN STRIP_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF; wReg1_def; wReg2_def; wRegWrite1_def] THEN
  REPEAT (FIRST [CHANGED_TAC (CASE_REWRITE_TAC[]); COND_CASES_TAC]) THEN
  ASM_SIMP_TAC[W2SP4AUX_wStackLoad_asm_name; stack_asm_name_def; addr_name_def; reg_name_def;
               IN_INSERT; NOT_IN_EMPTY; distinctness "memop"] THEN
  ASM_ARITH_TAC);;

let W2SP4AUX_wLive_asm_name = prove
 (`!live (bs:(A word)app_list#num) k f f' (c:(A)asm_config) q bs'.
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     wLive live bs (k,f,f') = (q,bs') ==> stack_asm_name c q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC wLive_stack_asm_name THEN
  MAP_EVERY EXISTS_TAC [`(k:num,f:num,f':num)`; `live:cutsets`; `bs:(A word)app_list#num`;
    `bs':(A word)app_list#num`] THEN ASM_REWRITE_TAC[FST]);;

let W2SP4AUX_OpCurrHeap_asm_name2 = prove
 (`!(c:(A)asm_config) b dst src k f f' x y.
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     (asm_config_two_reg_arith c ==> dst = src) /\
     wReg1 src (k,f,f') = (x,y)
     ==> stack_asm_name c (wRegWrite1 (\dst_r. stack_OpCurrHeap b dst_r y) dst (k,f,f'))`,
  MESON_TAC[W2SP4AUX_OpCurrHeap_asm_name; W2SP4AUX_wStackLoad_asm_name]);;

let W2SP4AUX_DERIVE_ASM_NAME_TAC : tactic = fun (asl,w as g) ->
  let bnds = filter (fun (_,th) -> try let l,r = dest_binary "<" (concl th) in
                                       is_binary "-" r with Failure _ -> false) asl in
  let derive bth th =
    let c = concl th in
    let f = try fst(dest_const(fst(strip_comb(lhs c)))) with Failure _ -> "" in
    match f with
      "wReg1" -> [MATCH_MP W2SP4AUX_wReg1_bound th]
    | "wReg2" -> [MATCH_MP W2SP4AUX_wReg2_bound th]
    | "call_dest" -> [REWRITE_RULE[FST] (SPEC (rand(lhand(rand(concl bth))))
                                           (MATCH_MP call_dest_stack_asm_name th))]
    | "wLive" -> [MATCH_MP W2SP4AUX_wLive_asm_name (CONJ bth th)]
    | _ -> [] in
  match bnds with
    (_,bth)::_ ->
      let ths = flat (map (fun (_,th) -> try derive bth th with Failure _ -> []) asl) in
      MAP_EVERY STRIP_ASSUME_TAC ths g
  | [] -> ALL_TAC g;;

let W2SP4AUX_comp_asm_name = prove
 (`!(c:(A)asm_config) perf p bs kf prog' bs'.
     perf = F /\ post_alloc_conventions (FST kf) p /\ full_inst_ok_less c p /\
     (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
     (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\ 4 < FST kf /\
     word_to_stack_comp c perf p bs kf = (prog',bs')
     ==> stack_asm_name c prog'`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  REPEAT (W2SP4AUX_TY_CASES_TAC "addr" (cases "addr")) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[distinctness "wl_prog"] o
     REWRITE_RULE[word_to_stackProof_convs_def; full_inst_ok_less_def; every_inst_def;
                  no_share_inst_def; two_reg_inst_def; FST]) THEN
  TRY (FIRST_ASSUM(fun eq ->
         if (try fst(dest_const(fst(strip_comb(lhs(concl eq))))) = "exp_to_addr"
             with Failure _ -> false)
         then RULE_ASSUM_TAC(CASE_REWRITE_RULE[eq]) else NO_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN W2SP4AUX_DERIVE_ASM_NAME_TAC THEN
  SIMP[stack_asm_name_def; COND_RAND; COND_RATOR; SeqStackFree_def; PushHandler_F;
       PopHandler_F; StackHandlerArgs_F; StackArgs_def; LET_DEF; LET_END_DEF;
       W2SP4AUX_wStackLoad_asm_name; inst_name_def; reg_name_def; FST] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wMove_asm_name THEN ASM_ARITH_TAC) THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wInst_asm_name THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wRegWrite1_asm_name THEN SIMP[stack_asm_name_def] THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC W2SP4AUX_OpCurrHeap_asm_name2 THEN ASM_MESON_TAC[]) THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wShareInst_asm_name THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY; distinctness "memop"]) THEN
       ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; distinctness "memop"] THEN
       TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]) THEN
  TRY (W2SP4AUX_TY_CASES_TAC "sum" (cases "sum") THEN CASE_REWRITE_TAC[] THEN
       RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_ARITH_TAC) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 11007 *)
let word_to_stack_stack_asm_name_lem = prove
 (`!(c:(A)asm_config) perf p bs kf.
     perf = F /\
     post_alloc_conventions (FST kf) p /\
     full_inst_ok_less c p /\
     (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
     (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     4 < FST kf
     ==> stack_asm_name c (FST (word_to_stack_comp c perf p bs kf))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_comp_asm_name THEN
  MAP_EVERY EXISTS_TAC [`perf:bool`; `p:(A)wl_prog`; `bs:(A word)app_list#num`;
    `kf:num#num#num`; `SND (word_to_stack_comp (c:(A)asm_config) perf p bs kf)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* W2SP4AUX: the registers of the pieces of a compiled program are names *)
(* of the target (stack_asm_remove)                                        *)
let W2SP4AUX_wStackLoad_asm_remove = prove
 (`!l (p:(A)stack_prog) (c:(A)asm_config).
     ALL (\(x:num,i:num). reg_name x c) l /\ stack_asm_remove c p
     ==> stack_asm_remove c (wStackLoad l p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def; ALL] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[wStackLoad_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP[stack_asm_remove_def]);;

let W2SP4AUX_wRegWrite1_asm_remove = prove
 (`!(g:num->(A)stack_prog) r k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     (!n. n < k + 2 ==> stack_asm_remove c (g n))
     ==> stack_asm_remove c (wRegWrite1 g r (k,f,f'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[stack_asm_remove_def; reg_name_def] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC);;

let W2SP4AUX_wRegWrite2_asm_remove = prove
 (`!(g:num->(A)stack_prog) r k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     (!n. n < k + 2 ==> stack_asm_remove c (g n))
     ==> stack_asm_remove c (wRegWrite2 g r (k,f,f'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[stack_asm_remove_def; reg_name_def] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC);;

let W2SP4AUX_wMoveSingle_asm_remove = prove
 (`!x y k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     (!r. x = INL r ==> r < k + 2) /\ (!r. y = INL r ==> r < k + 2)
     ==> stack_asm_remove c (wMoveSingle (x,y) (k,f,f'):(A)stack_prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  SIMP[stack_asm_remove_def; reg_name_def] THEN ARITH_TAC);;

let W2SP4AUX_wMoveAux_asm_remove = prove
 (`!xs kf (c:(A)asm_config).
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     ALL (\(x,y). (!r. x = INL r ==> r < FST kf + 2) /\ (!r. y = INL r ==> r < FST kf + 2)) xs
     ==> stack_asm_remove c (wMoveAux xs kf:(A)stack_prog)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC wMoveAux_ind THEN
  REWRITE_TAC[wMoveAux_def; stack_asm_remove_def; ALL] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP[W2SP4AUX_wMoveSingle_asm_remove]);;

let W2SP4AUX_wMove_asm_remove = prove
 (`!xs k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)
     ==> stack_asm_remove c (wMove xs (k,f,f'):(A)stack_prog)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wMove_def] THEN
  MP_TAC (ISPECL [`MAP (format_var k ## format_var k) (parmove (MAP (DIV2 ## DIV2) xs))`;
                  `(k:num,f:num,f':num)`; `c:(A)asm_config`] W2SP4AUX_wMoveAux_asm_remove) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; PAIR_MAP] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[W2SP4AUX_format_var_bound]);;

let W2SP4AUX_ASM_REMOVE_STEP_TAC =
  REPEAT (FIRST [COND_CASES_TAC; PAIRARG_TAC;
                 MATCH_MP_TAC W2SP4AUX_wStackLoad_asm_remove THEN CONJ_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_asm_remove THEN ASM_REWRITE_TAC[] THEN
                   REPEAT STRIP_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite2_asm_remove THEN ASM_REWRITE_TAC[] THEN
                   REPEAT STRIP_TAC THEN BETA_TAC]) THEN
  REPEAT (FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try mem (fst(dest_const(fst(strip_comb(lhs c))))) ["wReg1";"wReg2"]
                   with Failure _ -> false)
    then MP_TAC (MATCH_MP (if fst(dest_const(fst(strip_comb(lhs c)))) = "wReg1"
                           then W2SP4AUX_wReg1_bound else W2SP4AUX_wReg2_bound) th)
    else failwith "")) THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)) THEN
  SIMP[stack_asm_remove_def; reg_name_def; ALL_APPEND; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
  RES_TAC THEN ASM_ARITH_TAC;;

let W2SP4AUX_wInst_asm_remove = prove
 (`!(i:(A)inst) k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)
     ==> stack_asm_remove c (wInst i (k,f,f'))`,
  GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN W2SP4AUX_ASM_REMOVE_STEP_TAC);;

let W2SP4AUX_wShareInst_asm_remove = prove
 (`!op v ad k f f' (c:(A)asm_config).
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)
     ==> stack_asm_remove c (wShareInst op v ad (k,f,f'):(A)stack_prog)`,
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN W2SP4AUX_ASM_REMOVE_STEP_TAC);;

(* HOL4 line 11129 *)
let call_dest_stack_asm_remove = prove
 (CASE_TERM `!k (c:(A)asm_config) d a (q0:(A)stack_prog) d'.
     FST k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     call_dest d a k = (q0,d')
     ==> stack_asm_remove c q0 /\
         (match d' with INR r -> r <= FST k + 1 | INL l -> T)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CASE_REWRITE_TAC[] THEN SIMP[stack_asm_remove_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP4AUX_wReg2_bound) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC W2SP4AUX_wStackLoad_asm_remove THEN
  REWRITE_TAC[stack_asm_remove_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[reg_name_def] THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 11145 *)
let wLive_stack_asm_remove = prove
 (`!kf (c:(A)asm_config) q (bs:(A word)app_list#num) q1 bs'.
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     wLive q bs kf = (q1,bs')
     ==> stack_asm_remove c q1`,
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[stack_asm_remove_def; reg_name_def] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 11157 *)
let stack_move_stack_asm_remove = prove
 (`!n start offset i (p:(A)stack_prog) (c:(A)asm_config).
     reg_name i c
     ==> (stack_asm_remove c (stack_move n start offset i p) <=> stack_asm_remove c p)`,
  INDUCT_TAC THEN SIMP[stack_move_def; stack_asm_remove_def]);;

(* HOL4 line 11166 *)
let copy_ret_aux_stack_asm_remove = prove
 (`!k f n (c:(A)asm_config). reg_name k c ==> stack_asm_remove c (copy_ret_aux k f n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[stack_asm_remove_def; stack_list_Seq_def; LET_DEF; LET_END_DEF]);;

(* HOL4 line 11176 *)
let copy_ret_stack_asm_remove = prove
 (`!(kf:num#num#C) (c:(A)asm_config) b (vs:B list) kont.
     reg_name (FST kf) c
     ==> (stack_asm_remove c (copy_ret F b kf vs kont) <=> stack_asm_remove c kont)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[stack_asm_remove_def; copy_ret_aux_stack_asm_remove; SeqStackFree_def] THEN
  COND_CASES_TAC THEN SIMP[stack_asm_remove_def]);;

(* W2SP4AUX: stack_asm_remove of word_to_stack_comp *)
let W2SP4AUX_call_dest_asm_remove = prove
 (`!k f f' (c:(A)asm_config) d a (q0:(A)stack_prog) d'.
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     call_dest d a (k,f,f') = (q0,d')
     ==> stack_asm_remove c q0 /\ (!r. d' = INR r ==> r < k + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`(k:num,f:num,f':num)`; `c:(A)asm_config`; `d:num option`;
    `a:num list`; `q0:(A)stack_prog`; `d':num+num`] call_dest_stack_asm_remove) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN CASE_REWRITE_TAC[] THEN ARITH_TAC);;

let W2SP4AUX_wLive_asm_remove = prove
 (`!live (bs:(A word)app_list#num) k f f' (c:(A)asm_config) q bs'.
     k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     wLive live bs (k,f,f') = (q,bs') ==> stack_asm_remove c q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC wLive_stack_asm_remove THEN
  MAP_EVERY EXISTS_TAC [`(k:num,f:num,f':num)`; `live:cutsets`; `bs:(A word)app_list#num`;
    `bs':(A word)app_list#num`] THEN ASM_REWRITE_TAC[FST]);;

let W2SP4AUX_DERIVE_ASM_REMOVE_TAC : tactic = fun (asl,w as g) ->
  let bnds = filter (fun (_,th) -> try let l,r = dest_binary "<" (concl th) in
                                       is_binary "-" r with Failure _ -> false) asl in
  let derive bth th =
    let c = concl th in
    let f = try fst(dest_const(fst(strip_comb(lhs c)))) with Failure _ -> "" in
    match f with
      "wReg1" -> [MATCH_MP W2SP4AUX_wReg1_bound th]
    | "wReg2" -> [MATCH_MP W2SP4AUX_wReg2_bound th]
    | "call_dest" -> [MATCH_MP W2SP4AUX_call_dest_asm_remove (CONJ bth th)]
    | "wLive" -> [MATCH_MP W2SP4AUX_wLive_asm_remove (CONJ bth th)]
    | _ -> [] in
  match bnds with
    (_,bth)::_ ->
      let ths = flat (map (fun (_,th) -> try derive bth th with Failure _ -> []) asl) in
      MAP_EVERY STRIP_ASSUME_TAC ths g
  | [] -> ALL_TAC g;;

let W2SP4AUX_comp_asm_remove = prove
 (`!(c:(A)asm_config) perf p bs kf prog' bs'.
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\ perf = F /\
     word_to_stack_comp c perf p bs kf = (prog',bs')
     ==> stack_asm_remove c prog'`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  ASM_REWRITE_TAC[FST] THEN W2SP4AUX_DERIVE_ASM_REMOVE_TAC THEN
  (SUBGOAL_THEN `reg_name kk (conf:(A)asm_config) /\ reg_name (kk + 1) conf`
     STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[reg_name_def] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  SIMP[stack_asm_remove_def; COND_RAND; COND_RATOR; SeqStackFree_def; PushHandler_F;
       PopHandler_F; StackHandlerArgs_F; StackArgs_def; LET_DEF; LET_END_DEF;
       W2SP4AUX_wMove_asm_remove; W2SP4AUX_wInst_asm_remove; W2SP4AUX_wShareInst_asm_remove;
       stack_move_stack_asm_remove; copy_ret_stack_asm_remove; FST] THEN
  REPEAT (FIRST [CONJ_TAC; COND_CASES_TAC;
                 MATCH_MP_TAC W2SP4AUX_wStackLoad_asm_remove THEN CONJ_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_asm_remove THEN ASM_REWRITE_TAC[] THEN
                   REPEAT STRIP_TAC THEN BETA_TAC]) THEN
  RULE_ASSUM_TAC(fun th -> if (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL"
                                with Failure _ -> false)
                             then CONV_RULE(DEPTH_CONV GEN_BETA_CONV)
                                    (REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM] th)
                             else th) THEN
  SIMP[stack_asm_remove_def; reg_name_def; ALL_APPEND; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN TRY (RES_TAC THEN ASM_ARITH_TAC) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 11184 *)
let word_to_stack_stack_asm_remove_lem = prove
 (`!(c:(A)asm_config) perf (p:(A)wl_prog) bs kf.
     FST kf + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\ perf = F
     ==> stack_asm_remove c (FST (word_to_stack_comp c perf p bs kf))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_comp_asm_remove THEN
  MAP_EVERY EXISTS_TAC [`perf:bool`; `p:(A)wl_prog`; `bs:(A word)app_list#num`;
    `kf:num#num#num`; `SND (word_to_stack_comp (c:(A)asm_config) perf p bs kf)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* W2SP4AUX: stack_asm_name and stack_asm_remove of a compile_prog result *)
let W2SP4AUX_compile_prog_asm = prove
 (`!(c:(A)asm_config) pp m k bs0 prog f bs1.
     full_inst_ok_less c pp /\
     (asm_config_two_reg_arith c ==> every_inst two_reg_inst pp) /\
     (no_share_inst pp \/ ~(asm_config_ISA c = Ag32)) /\
     post_alloc_conventions k pp /\
     4 < k /\ k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) /\
     word_to_stack_compile_prog c F pp m k bs0 = (prog,f,bs1)
     ==> stack_asm_name c prog /\ stack_asm_remove c prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[W2SP4AUX_compile_prog_eq] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[stack_asm_name_def; stack_asm_remove_def] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC W2SP4AUX_comp_asm_name THEN
     MAP_EVERY EXISTS_TAC [`F`; `pp:(A)wl_prog`; `bs0:(A word)app_list#num`;
       `(k:num,f:num,MAX ((max_var (pp:(A)wl_prog) DIV 2 + 1) - k) (m - k))`;
       `bs1:(A word)app_list#num`];
     MATCH_MP_TAC W2SP4AUX_comp_asm_remove THEN
     MAP_EVERY EXISTS_TAC [`F`; `pp:(A)wl_prog`; `bs0:(A word)app_list#num`;
       `(k:num,f:num,MAX ((max_var (pp:(A)wl_prog) DIV 2 + 1) - k) (m - k))`;
       `bs1:(A word)app_list#num`]]) THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 line 11257 *)
let word_to_stack_stack_asm_convs = prove
 (`!(c:(A)asm_config) progs.
     ALL (\(n,m,p).
            full_inst_ok_less c p /\
            (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
            (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
            post_alloc_conventions
              (asm_config_reg_count c - (LENGTH (asm_config_avoid_regs c) + 5)) p) progs /\
     4 < asm_config_reg_count c - (LENGTH (asm_config_avoid_regs c) + 5)
     ==> ALL (\(n,p). stack_asm_name c p /\ stack_asm_remove c p)
           (SND (SND (SND (word_to_stack_compile c F progs))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC (ISPEC `compile_word_to_stack (c:(A)asm_config) F
    (asm_config_reg_count c - (5 + LENGTH (asm_config_avoid_regs c))) progs
    (misc_List [word 4],1)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:(num#(A)stack_prog)list`; `r:num list#(A word)app_list#num`] THEN
  MP_TAC (ISPEC `r:num list#(A word)app_list#num` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`fs:num list`; `bm:(A word)app_list#num`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE; SND; ALL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SUBGOAL_THEN `asm_config_reg_count (c:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs c)) =
                asm_config_reg_count c - (LENGTH (asm_config_avoid_regs c) + 5)` ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def] THEN
  SIMP[stack_asm_name_def; stack_asm_remove_def; reg_name_def; inst_name_def] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC (BETA_RULE (ISPEC
    `\(n:num) (p:(A)stack_prog). stack_asm_name (c:(A)asm_config) p /\ stack_asm_remove c p`
    W2SP4AUX_compile_word_to_stack_ALL)) THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `F`;
    `asm_config_reg_count (c:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs c))`;
    `progs:(num#num#(A)wl_prog)list`; `misc_List [word 4:A word],1`;
    `fs:num list`; `bm:(A word)app_list#num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC W2SP4AUX_compile_prog_asm THEN
  MAP_EVERY EXISTS_TAC [`pp:(A)wl_prog`; `m:num`;
    `asm_config_reg_count (c:(A)asm_config) - (LENGTH (asm_config_avoid_regs c) + 5)`;
    `bs0:(A word)app_list#num`; `f:num`; `bs1:(A word)app_list#num`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_head_is "ALL" o concl)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(n:num,m:num,pp:(A)wl_prog)`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* W2SP4AUX: the pieces of a compiled program satisfy alloc_arg *)
let W2SP4AUX_wMoveSingle_alloc_arg = prove
 (`!xy kf. alloc_arg (wMoveSingle xy kf:(A)stack_prog)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN SIMP[alloc_arg_def]);;

let W2SP4AUX_wMoveAux_alloc_arg = prove
 (`!xs kf. alloc_arg (wMoveAux xs kf:(A)stack_prog)`,
  MATCH_MP_TAC wMoveAux_ind THEN REPEAT STRIP_TAC THEN
  SIMP[wMoveAux_def; alloc_arg_def; W2SP4AUX_wMoveSingle_alloc_arg]);;

let W2SP4AUX_wStackLoad_alloc_arg = prove
 (`!l (prog:(A)stack_prog). alloc_arg (wStackLoad l prog) = alloc_arg prog`,
  MATCH_MP_TAC wStackLoad_ind THEN SIMP[wStackLoad_def; alloc_arg_def]);;

let W2SP4AUX_wRegWrite1_alloc_arg = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. alloc_arg (prog reg)) ==> alloc_arg (wRegWrite1 prog r kf)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[alloc_arg_def]);;

let W2SP4AUX_wRegWrite2_alloc_arg = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. alloc_arg (prog reg)) ==> alloc_arg (wRegWrite2 prog r kf)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[alloc_arg_def]);;

let W2SP4AUX_wLive_alloc_arg = prove
 (`!live (bs:(A word)app_list#num) kf. alloc_arg (FST (wLive live bs kf))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[alloc_arg_def] THEN PAIRARG_TAC THEN SIMP[alloc_arg_def]);;

let W2SP4AUX_stack_move_alloc_arg = prove
 (`!n start offset i (p:(A)stack_prog).
     alloc_arg (stack_move n start offset i p) = alloc_arg p`,
  INDUCT_TAC THEN SIMP[stack_move_def; alloc_arg_def]);;

(* HOL4 line 11292 *)
let stack_move_alloc_arg = prove
 (`!n st off i (p:(A)stack_prog). alloc_arg p ==> alloc_arg (stack_move n st off i p)`,
  SIMP[W2SP4AUX_stack_move_alloc_arg]);;

(* HOL4 line 11300 *)
let alloc_arg_copy_ret_aux = prove
 (`!k f n. alloc_arg (copy_ret_aux k f n:(A)stack_prog)`,
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[alloc_arg_def; stack_list_Seq_def; LET_DEF; LET_END_DEF]);;

(* HOL4 line 11309 *)
let alloc_arg_copy_ret = prove
 (`!perf b (kf:num#num#C) (vs:B list) (kont:(A)stack_prog).
     alloc_arg (copy_ret perf b kf vs kont) <=> alloc_arg kont`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[alloc_arg_def; SeqStackFree_def; alloc_arg_copy_ret_aux] THEN
  COND_CASES_TAC THEN SIMP[alloc_arg_def]);;

let _ = cake_add_simps [alloc_arg_copy_ret];;

(* W2SP4AUX: more pieces satisfying alloc_arg *)
let W2SP4AUX_perf_call_prefix_alloc_arg = prove
 (`!l1 l2 kf0. alloc_arg (perf_call_prefix l1 l2 kf0:(A)stack_prog)`,
  SIMP[perf_call_prefix_def; alloc_arg_def; stack_list_Seq_def]);;

let W2SP4AUX_perf_call_suffix_alloc_arg = prove
 (`alloc_arg (perf_call_suffix:(A)stack_prog)`,
  SIMP[perf_call_suffix_def; alloc_arg_def; stack_list_Seq_def]);;

let W2SP4AUX_PushHandler_alloc_arg = prove
 (`!perf l1 l2 (kff:num#B#C). alloc_arg (PushHandler perf l1 l2 kff:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PushHandler_def] THEN COND_CASES_TAC THEN
  SIMP[alloc_arg_def; stack_list_Seq_def]);;

let W2SP4AUX_PopHandler_alloc_arg = prove
 (`!perf (kff:num#B#C) (prog:(A)stack_prog).
     alloc_arg (PopHandler perf kff prog) <=> alloc_arg prog`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PopHandler_def] THEN SIMP[alloc_arg_def]);;

let W2SP4AUX_StackHandlerArgs_alloc_arg = prove
 (`!perf (dest:B+C) arg_count kff.
     alloc_arg (StackHandlerArgs perf dest arg_count kff:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[StackHandlerArgs_def; StackArgs_def; LET_DEF; LET_END_DEF] THEN
  SIMP[W2SP4AUX_stack_move_alloc_arg; alloc_arg_def]);;

let W2SP4AUX_wInst_alloc_arg = prove
 (`!(i:(A)inst) kf. alloc_arg (wInst i kf)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[W2SP4AUX_wStackLoad_alloc_arg]);
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_alloc_arg THEN GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite2_alloc_arg THEN GEN_TAC THEN BETA_TAC;
                 COND_CASES_TAC]) THEN
  SIMP[alloc_arg_def]);;

let W2SP4AUX_call_dest_alloc_arg = prove
 (`!d a kf (q0:(A)stack_prog) d'. call_dest d a kf = (q0,d') ==> alloc_arg q0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[alloc_arg_def; W2SP4AUX_wStackLoad_alloc_arg]);;

let W2SP4AUX_wMove_alloc_arg = prove
 (`!xs kf. alloc_arg (wMove xs kf:(A)stack_prog)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wMove_def; W2SP4AUX_wMoveAux_alloc_arg]);;

let W2SP4AUX_wLive_alloc_arg2 = prove
 (`!live (bs:(A word)app_list#num) kf q bs'.
     wLive live bs kf = (q,bs') ==> alloc_arg q`,
  REPEAT STRIP_TAC THEN MP_TAC (SPECL [`live:cutsets`; `bs:(A word)app_list#num`;
    `kf:num#num#num`] W2SP4AUX_wLive_alloc_arg) THEN ASM_REWRITE_TAC[FST]);;

let W2SP4AUX_wShareInst_alloc_arg = prove
 (`!op v ad kf. alloc_arg (wShareInst op v ad kf:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[W2SP4AUX_wStackLoad_alloc_arg]);
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_alloc_arg THEN GEN_TAC THEN BETA_TAC]) THEN
  SIMP[alloc_arg_def]);;

let W2SP4AUX_comp_alloc_arg = prove
 (`!(ac:(A)asm_config) perf prog bs kf prog' bs'.
     word_to_stack_comp ac perf prog bs kf = (prog',bs')
     ==> alloc_arg prog'`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  SIMP[alloc_arg_def; W2SP4AUX_wMove_alloc_arg; COND_RAND;
     W2SP4AUX_wStackLoad_alloc_arg; W2SP4AUX_stack_move_alloc_arg; W2SP4AUX_wInst_alloc_arg;
     W2SP4AUX_wShareInst_alloc_arg; SeqStackFree_def; W2SP4AUX_PushHandler_alloc_arg;
     W2SP4AUX_PopHandler_alloc_arg;
     W2SP4AUX_StackHandlerArgs_alloc_arg; StackArgs_def; alloc_arg_copy_ret;
     W2SP4AUX_perf_call_prefix_alloc_arg; W2SP4AUX_perf_call_suffix_alloc_arg] THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wRegWrite1_alloc_arg THEN SIMP[alloc_arg_def]) THEN
  REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[W2SP4AUX_wLive_alloc_arg2; W2SP4AUX_call_dest_alloc_arg]);;

(* HOL4 line 11316 *)
let word_to_stack_alloc_arg = prove
 (`!(c:(A)asm_config) perf p n args.
     perf = F ==> alloc_arg (FST (word_to_stack_comp c perf p n args))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_comp_alloc_arg THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `perf:bool`; `p:(A)wl_prog`;
    `n:(A word)app_list#num`; `args:num#num#num`;
    `SND (word_to_stack_comp (c:(A)asm_config) perf p n args)`] THEN
  REWRITE_TAC[PAIR]);;

(* W2SP4AUX: the registers of the pieces of a compiled program are below *)
(* k + 2                                                                    *)
let W2SP4AUX_wStackLoad_reg_bound = prove
 (`!l (p:(A)stack_prog) K.
     ALL (\(x:num,i:num). x < K) l /\ reg_bound p K ==> reg_bound (wStackLoad l p) K`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def; ALL] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[wStackLoad_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP[reg_bound_def]);;

let W2SP4AUX_wRegWrite1_reg_bound = prove
 (`!(g:num->(A)stack_prog) r k f f'.
     (!n. n < k + 2 ==> reg_bound (g n) (k + 2))
     ==> reg_bound (wRegWrite1 g r (k,f,f')) (k + 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[reg_bound_def] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC);;

let W2SP4AUX_wRegWrite2_reg_bound = prove
 (`!(g:num->(A)stack_prog) r k f f'.
     (!n. n < k + 2 ==> reg_bound (g n) (k + 2))
     ==> reg_bound (wRegWrite2 g r (k,f,f')) (k + 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[reg_bound_def] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC);;

let W2SP4AUX_wMoveSingle_reg_bound = prove
 (`!x y k f f'.
     (!r. x = INL r ==> r < k + 2) /\ (!r. y = INL r ==> r < k + 2)
     ==> reg_bound (wMoveSingle (x,y) (k,f,f'):(A)stack_prog) (k + 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  SIMP[reg_bound_def; reg_bound_inst_def] THEN ARITH_TAC);;

let W2SP4AUX_wMoveAux_reg_bound = prove
 (`!xs kf.
     ALL (\(x,y). (!r. x = INL r ==> r < FST kf + 2) /\ (!r. y = INL r ==> r < FST kf + 2)) xs
     ==> reg_bound (wMoveAux xs kf:(A)stack_prog) (FST kf + 2)`,
  MATCH_MP_TAC wMoveAux_ind THEN
  REWRITE_TAC[wMoveAux_def; reg_bound_def; ALL] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP[W2SP4AUX_wMoveSingle_reg_bound]);;

let W2SP4AUX_wMove_reg_bound = prove
 (`!xs k f f'. reg_bound (wMove xs (k,f,f'):(A)stack_prog) (k + 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wMove_def] THEN
  MP_TAC (ISPECL [`MAP (format_var k ## format_var k) (parmove (MAP (DIV2 ## DIV2) xs))`;
                  `(k:num,f:num,f':num)`] W2SP4AUX_wMoveAux_reg_bound) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; PAIR_MAP] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[W2SP4AUX_format_var_bound]);;

let W2SP4AUX_REG_BOUND_STEP_TAC =
  REPEAT (FIRST [COND_CASES_TAC; PAIRARG_TAC;
                 MATCH_MP_TAC W2SP4AUX_wStackLoad_reg_bound THEN CONJ_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_reg_bound THEN REPEAT STRIP_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite2_reg_bound THEN REPEAT STRIP_TAC THEN
                   BETA_TAC]) THEN
  REPEAT (FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try mem (fst(dest_const(fst(strip_comb(lhs c))))) ["wReg1";"wReg2"]
                   with Failure _ -> false)
    then MP_TAC (MATCH_MP (if fst(dest_const(fst(strip_comb(lhs c)))) = "wReg1"
                           then W2SP4AUX_wReg1_bound else W2SP4AUX_wReg2_bound) th)
    else failwith "")) THEN
  REPEAT STRIP_TAC THEN
  SIMP[reg_bound_def; reg_bound_inst_def; ALL_APPEND; ALL] THEN
  TRY ASM_ARITH_TAC;;

let W2SP4AUX_wInst_reg_bound = prove
 (`!(i:(A)inst) k f f'.
     2 <= k /\ inst_arg_convention i ==> reg_bound (wInst i (k,f,f')) (k + 2)`,
  GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[inst_arg_convention_def] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN W2SP4AUX_REG_BOUND_STEP_TAC);;

let W2SP4AUX_wShareInst_reg_bound = prove
 (`!op v ad k f f'. reg_bound (wShareInst op v ad (k,f,f'):(A)stack_prog) (k + 2)`,
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN W2SP4AUX_REG_BOUND_STEP_TAC);;

let W2SP4AUX_call_dest_reg_bound = prove
 (`!d a k f f' (q0:(A)stack_prog) d'.
     call_dest d a (k,f,f') = (q0,d')
     ==> reg_bound q0 (k + 2) /\ (!r. d' = INR r ==> r < k + 2)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[reg_bound_def] THEN
  TRY (FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP4AUX_wReg2_bound) THEN
       ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC W2SP4AUX_wStackLoad_reg_bound THEN ASM_REWRITE_TAC[reg_bound_def]));;

let W2SP4AUX_wLive_reg_bound = prove
 (`!live (bs:(A word)app_list#num) k f f' q bs'.
     wLive live bs (k,f,f') = (q,bs') ==> reg_bound q (k + 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[reg_bound_def; reg_bound_inst_def] THEN ARITH_TAC);;

(* HOL4 line 11384 *)
let stack_move_reg_bound = prove
 (`!n st off i (p:(A)stack_prog) k.
     i < k /\ reg_bound p k ==> reg_bound (stack_move n st off i p) k`,
  INDUCT_TAC THEN SIMP[stack_move_def; reg_bound_def]);;

(* HOL4 line 11393 *)
let copy_ret_aux_reg_bound = prove
 (`!k f n. reg_bound (copy_ret_aux k f n:(A)stack_prog) (k + 2)`,
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[reg_bound_def; stack_list_Seq_def; LET_DEF; LET_END_DEF] THEN ARITH_TAC);;

(* HOL4 line 11402 *)
let copy_ret_reg_bound = prove
 (`!kont k perf b f (f':C) (vs:B list).
     reg_bound kont (k + 2)
     ==> reg_bound (copy_ret perf b (k,f,f') vs kont:(A)stack_prog) (k + 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[reg_bound_def; copy_ret_aux_reg_bound] THEN
  REWRITE_TAC[SeqStackFree_def] THEN COND_CASES_TAC THEN SIMP[reg_bound_def]);;

(* W2SP4AUX: the register bound of word_to_stack_comp *)
let W2SP4AUX_wInst_reg_bound4 = prove
 (`!(i:(A)inst) k f f'.
     4 <= k /\ inst_arg_convention i ==> reg_bound (wInst i (k,f,f')) (k + 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_wInst_reg_bound THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let W2SP4AUX_DERIVE_BOUNDS_TAC : tactic = fun (asl,w as g) ->
  let derive th =
    let c = concl th in
    let f = try fst(dest_const(fst(strip_comb(lhs c)))) with Failure _ -> "" in
    match f with
      "wReg1" -> [MATCH_MP W2SP4AUX_wReg1_bound th]
    | "wReg2" -> [MATCH_MP W2SP4AUX_wReg2_bound th]
    | "call_dest" -> [MATCH_MP W2SP4AUX_call_dest_reg_bound th]
    | "wLive" -> [MATCH_MP W2SP4AUX_wLive_reg_bound th]
    | _ -> [] in
  let ths = flat (map (fun (_,th) -> try derive th with Failure _ -> []) asl) in
  MAP_EVERY STRIP_ASSUME_TAC ths g;;

let W2SP4AUX_comp_reg_bound = prove
 (`!(ac:(A)asm_config) perf prog bs kf prog' bs'.
     post_alloc_conventions (FST kf) prog /\ 4 <= FST kf /\ perf = F /\
     word_to_stack_comp ac perf prog bs kf = (prog',bs')
     ==> reg_bound prog' (FST kf + 2)`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[word_to_stackProof_convs_def; FST]) THEN
  ASM_REWRITE_TAC[FST] THEN W2SP4AUX_DERIVE_BOUNDS_TAC THEN
  SIMP[reg_bound_def; COND_RAND; COND_RATOR; SeqStackFree_def; PushHandler_F;
       PopHandler_F; StackHandlerArgs_F; StackArgs_def; LET_DEF; LET_END_DEF;
       W2SP4AUX_wMove_reg_bound; W2SP4AUX_wInst_reg_bound4; W2SP4AUX_wShareInst_reg_bound] THEN
  REPEAT (FIRST [CONJ_TAC; COND_CASES_TAC;
                 MATCH_MP_TAC W2SP4AUX_wStackLoad_reg_bound THEN CONJ_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_reg_bound THEN REPEAT STRIP_TAC THEN BETA_TAC;
                 MATCH_MP_TAC copy_ret_reg_bound;
                 MATCH_MP_TAC stack_move_reg_bound THEN CONJ_TAC]) THEN
  TRY (W2SP4AUX_SUM_CASES_ALL_TAC THEN CASE_REWRITE_TAC[]) THEN
  SIMP[reg_bound_def; ALL_APPEND; ALL] THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 11410 *)
let word_to_stack_reg_bound = prove
 (`!(c:(A)asm_config) perf p n args.
     post_alloc_conventions (FST args) p /\ 4 <= FST args /\ perf = F
     ==> reg_bound (FST (word_to_stack_comp c perf p n args)) (FST args + 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_comp_reg_bound THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `perf:bool`; `p:(A)wl_prog`;
    `n:(A word)app_list#num`;
    `SND (word_to_stack_comp (c:(A)asm_config) perf p n args)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* W2SP4AUX: the pieces of a compiled program satisfy call_args *)
let W2SP4AUX_wMoveSingle_call_args = prove
 (`!xy kf. call_args (wMoveSingle xy kf:(A)stack_prog) 1 2 3 4 0`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN SIMP[call_args_def]);;

let W2SP4AUX_wMoveAux_call_args = prove
 (`!xs kf. call_args (wMoveAux xs kf:(A)stack_prog) 1 2 3 4 0`,
  MATCH_MP_TAC wMoveAux_ind THEN REPEAT STRIP_TAC THEN
  SIMP[wMoveAux_def; call_args_def; W2SP4AUX_wMoveSingle_call_args]);;

let W2SP4AUX_wStackLoad_call_args = prove
 (`!l (prog:(A)stack_prog). call_args (wStackLoad l prog) 1 2 3 4 0 = call_args prog 1 2 3 4 0`,
  MATCH_MP_TAC wStackLoad_ind THEN SIMP[wStackLoad_def; call_args_def]);;

let W2SP4AUX_wRegWrite1_call_args = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. call_args (prog reg) 1 2 3 4 0) ==> call_args (wRegWrite1 prog r kf) 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[call_args_def]);;

let W2SP4AUX_wRegWrite2_call_args = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. call_args (prog reg) 1 2 3 4 0) ==> call_args (wRegWrite2 prog r kf) 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[call_args_def]);;

let W2SP4AUX_wLive_call_args = prove
 (`!live (bs:(A word)app_list#num) kf. call_args (FST (wLive live bs kf)) 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[call_args_def] THEN PAIRARG_TAC THEN SIMP[call_args_def]);;

let W2SP4AUX_stack_move_call_args = prove
 (`!n start offset i (p:(A)stack_prog).
     call_args (stack_move n start offset i p) 1 2 3 4 0 = call_args p 1 2 3 4 0`,
  INDUCT_TAC THEN SIMP[stack_move_def; call_args_def]);;

(* HOL4 line 11490 *)
let stack_move_call_args = prove
 (`!n st off i (p:(A)stack_prog).
     call_args p 1 2 3 4 0 ==> call_args (stack_move n st off i p) 1 2 3 4 0`,
  SIMP[W2SP4AUX_stack_move_call_args]);;

(* HOL4 line 11498 *)
let copy_ret_aux_call_args = prove
 (`!k f n. call_args (copy_ret_aux k f n:(A)stack_prog) 1 2 3 4 0`,
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[call_args_def; stack_list_Seq_def; LET_DEF; LET_END_DEF]);;

(* HOL4 line 11507 *)
let copy_ret_call_args = prove
 (`!perf b (kf:num#num#C) (vs:B list) (kont:(A)stack_prog).
     call_args (copy_ret perf b kf vs kont) 1 2 3 4 0 <=> call_args kont 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[call_args_def; SeqStackFree_def; copy_ret_aux_call_args] THEN
  COND_CASES_TAC THEN SIMP[call_args_def]);;

let _ = cake_add_simps [copy_ret_call_args];;

(* W2SP4AUX: more pieces satisfying call_args *)
let W2SP4AUX_perf_call_prefix_call_args = prove
 (`!l1 l2 kf0. call_args (perf_call_prefix l1 l2 kf0:(A)stack_prog) 1 2 3 4 0`,
  SIMP[perf_call_prefix_def; call_args_def; stack_list_Seq_def]);;

let W2SP4AUX_perf_call_suffix_call_args = prove
 (`call_args (perf_call_suffix:(A)stack_prog) 1 2 3 4 0`,
  SIMP[perf_call_suffix_def; call_args_def; stack_list_Seq_def]);;

let W2SP4AUX_PushHandler_call_args = prove
 (`!perf l1 l2 (kff:num#B#C). call_args (PushHandler perf l1 l2 kff:(A)stack_prog) 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PushHandler_def] THEN COND_CASES_TAC THEN
  SIMP[call_args_def; stack_list_Seq_def]);;

let W2SP4AUX_PopHandler_call_args = prove
 (`!perf (kff:num#B#C) (prog:(A)stack_prog).
     call_args (PopHandler perf kff prog) 1 2 3 4 0 <=> call_args prog 1 2 3 4 0`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PopHandler_def] THEN SIMP[call_args_def]);;

let W2SP4AUX_StackHandlerArgs_call_args = prove
 (`!perf (dest:B+C) arg_count kff.
     call_args (StackHandlerArgs perf dest arg_count kff:(A)stack_prog) 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[StackHandlerArgs_def; StackArgs_def; LET_DEF; LET_END_DEF] THEN
  SIMP[W2SP4AUX_stack_move_call_args; call_args_def]);;

let W2SP4AUX_wInst_call_args = prove
 (`!(i:(A)inst) kf. call_args (wInst i kf) 1 2 3 4 0`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[W2SP4AUX_wStackLoad_call_args]);
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_call_args THEN GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite2_call_args THEN GEN_TAC THEN BETA_TAC;
                 COND_CASES_TAC]) THEN
  SIMP[call_args_def]);;

let W2SP4AUX_call_dest_call_args = prove
 (`!d a kf (q0:(A)stack_prog) d'. call_dest d a kf = (q0,d') ==> call_args q0 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[call_args_def; W2SP4AUX_wStackLoad_call_args]);;

let W2SP4AUX_wMove_call_args = prove
 (`!xs kf. call_args (wMove xs kf:(A)stack_prog) 1 2 3 4 0`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wMove_def; W2SP4AUX_wMoveAux_call_args]);;

let W2SP4AUX_wLive_call_args2 = prove
 (`!live (bs:(A word)app_list#num) kf q bs'.
     wLive live bs kf = (q,bs') ==> call_args q 1 2 3 4 0`,
  REPEAT STRIP_TAC THEN MP_TAC (SPECL [`live:cutsets`; `bs:(A word)app_list#num`;
    `kf:num#num#num`] W2SP4AUX_wLive_call_args) THEN ASM_REWRITE_TAC[FST]);;

let W2SP4AUX_wShareInst_call_args = prove
 (`!op v ad kf. call_args (wShareInst op v ad kf:(A)stack_prog) 1 2 3 4 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[W2SP4AUX_wStackLoad_call_args]);
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_call_args THEN GEN_TAC THEN BETA_TAC]) THEN
  SIMP[call_args_def]);;

let W2SP4AUX_comp_call_args = prove
 (`!(ac:(A)asm_config) perf prog bs kf prog' bs'.
     post_alloc_conventions (FST kf) prog /\
     word_to_stack_comp ac perf prog bs kf = (prog',bs')
     ==> call_args prog' 1 2 3 4 0`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[word_to_stackProof_convs_def; FST]) THEN
  SIMP[call_args_def; W2SP4AUX_wMove_call_args; COND_RAND; COND_RATOR;
     W2SP4AUX_wStackLoad_call_args; W2SP4AUX_stack_move_call_args; W2SP4AUX_wInst_call_args;
     W2SP4AUX_wShareInst_call_args; SeqStackFree_def; W2SP4AUX_PushHandler_call_args;
     W2SP4AUX_PopHandler_call_args;
     W2SP4AUX_StackHandlerArgs_call_args; StackArgs_def; copy_ret_call_args;
     W2SP4AUX_perf_call_prefix_call_args; W2SP4AUX_perf_call_suffix_call_args] THEN
  TRY (MATCH_MP_TAC W2SP4AUX_wRegWrite1_call_args THEN SIMP[call_args_def]) THEN
  REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[W2SP4AUX_wLive_call_args2; W2SP4AUX_call_dest_call_args]);;

(* HOL4 line 11515 *)
let word_to_stack_call_args = prove
 (`!(c:(A)asm_config) perf p n args.
     post_alloc_conventions (FST args) p /\ perf = F
     ==> call_args (FST (word_to_stack_comp c perf p n args)) 1 2 3 4 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_comp_call_args THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `perf:bool`; `p:(A)wl_prog`;
    `n:(A word)app_list#num`; `args:num#num#num`;
    `SND (word_to_stack_comp (c:(A)asm_config) perf p n args)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* W2SP4AUX: reg_bound_inst is monotone in the bound *)
let W2SP4AUX_reg_bound_inst_mono = prove
 (`!(i:(A)inst) k k'. reg_bound_inst i k /\ k <= k' ==> reg_bound_inst i k'`,
  GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  CASE_REWRITE_TAC[reg_bound_inst_def] THEN SIMP[] THEN ARITH_TAC);;

(* HOL4 lines 11585-11587: val reg_bound_ind, reg_bound_def,                *)
(* reg_bound_inst_def (aliases of stackProps' theorems)                     *)

(* HOL4 line 11589 *)
let reg_bound_mono = prove
 (`!(p:(A)stack_prog) k k'. reg_bound p k /\ k <= k' ==> reg_bound p k'`,
  MATCH_MP_TAC reg_bound_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST [W2SP4AUX_TY_CASES_TAC "option" W2SP4AUX_option4_CASES;
                 W2SP4AUX_TY_CASES_TAC "option" BASICAUX_option3_cases;
                 W2SP4AUX_TY_CASES_TAC "sum" (cases "sum");
                 W2SP4AUX_TY_CASES_TAC "reg_imm" (cases "reg_imm")]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[option_INJ; PAIR_EQ] o REWRITE_RULE[reg_bound_def]) THEN
  REWRITE_TAC[reg_bound_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT STRIP_TAC THEN
  TRY (MATCH_MP_TAC W2SP4AUX_reg_bound_inst_mono THEN ASM_MESON_TAC[]) THEN
  TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

let W2SP4AUX_compile_prog_convs = prove
 (`!(ac:(A)asm_config) pp m k bs0 prog f bs1.
     post_alloc_conventions k pp /\ 4 <= k /\
     word_to_stack_compile_prog ac F pp m k bs0 = (prog,f,bs1)
     ==> alloc_arg prog /\ reg_bound prog (k + 2) /\ call_args prog 1 2 3 4 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[W2SP4AUX_compile_prog_eq] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[alloc_arg_def; reg_bound_def; call_args_def] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC W2SP4AUX_comp_alloc_arg;
    MP_TAC (ISPECL [`ac:(A)asm_config`; `F`; `pp:(A)wl_prog`; `bs0:(A word)app_list#num`;
       `(k:num, f:num, MAX ((max_var (pp:(A)wl_prog) DIV 2 + 1) - k) (m - k))`;
       `q1:(A)stack_prog`; `bs1:(A word)app_list#num`] W2SP4AUX_comp_reg_bound) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN ACCEPT_TAC;
    MATCH_MP_TAC W2SP4AUX_comp_call_args] THEN
  ASM_MESON_TAC[FST]);;

(* HOL4 line 11606 *)
let word_to_stack_stack_convs = prove
 (`!(ac:(A)asm_config) p bytes c' f' p' k.
     word_to_stack_compile ac F p = (bytes,c',f',p') /\
     ALL (post_alloc_conventions k) (MAP (SND o SND) p) /\
     k = asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs ac)) /\
     4 <= k
     ==> ALL alloc_arg (MAP SND p') /\
         ALL (\p. reg_bound p (k + 2)) (MAP SND p') /\
         ALL (\p. call_args p 1 2 3 4 0) (MAP SND p')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP; ALL; SND] THEN
  SUBGOAL_THEN
   `ALL (\(n:num,prog:(A)stack_prog). alloc_arg prog /\
           reg_bound prog (asm_config_reg_count (ac:(A)asm_config) -
                           (5 + LENGTH (asm_config_avoid_regs ac)) + 2) /\
           call_args prog 1 2 3 4 0) progs`
    MP_TAC THENL
   [MATCH_MP_TAC W2SP4AUX_compile_word_to_stack_ALL THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `F`;
      `asm_config_reg_count (ac:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs ac))`;
      `p:(num#num#(A)wl_prog)list`; `misc_List [word 4:A word],1`;
      `fs:num list`; `bitmaps:(A word)app_list#num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC W2SP4AUX_compile_prog_convs THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `pp:(A)wl_prog`; `m:num`;
      `bs0:(A word)app_list#num`; `f:num`; `bs1:(A word)app_list#num`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_head_is "ALL" o concl)) THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `(n:num,m:num,pp:(A)wl_prog)` THEN ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; LEFT_IMP_EXISTS_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_TAC THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def] THEN
  SIMP[alloc_arg_def; reg_bound_def; call_args_def; reg_bound_inst_def] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_X_ASSUM(MP_TAC o check (is_binary "<=" o concl)) THEN ARITH_TAC) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 11660 *)
let compile_word_to_stack_convs = prove
 (`!p bm q bm' (c:(A)asm_config) k.
     compile_word_to_stack c F k p bm = (q,bm') /\
     ALL (\(n,m,p).
            full_inst_ok_less c p /\
            (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
            (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
            post_alloc_conventions k p) p /\
     4 < k /\ k + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)
     ==> ALL (\(x,y).
                stack_asm_name c y /\
                stack_asm_remove c y /\
                alloc_arg y /\
                reg_bound y (k + 2) /\
                call_args y 1 2 3 4 0) q`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (BETA_RULE (ISPEC
    `\(x:num) (y:(A)stack_prog). stack_asm_name (c:(A)asm_config) y /\
       stack_asm_remove c y /\ alloc_arg y /\ reg_bound y (k + 2) /\ call_args y 1 2 3 4 0`
    W2SP4AUX_compile_word_to_stack_ALL)) THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `F`; `k:num`; `p:(num#num#(A)wl_prog)list`;
    `bm:(A word)app_list#num`; `FST (bm':num list#(A word)app_list#num)`;
    `SND (bm':num list#(A word)app_list#num)`] THEN
  ASM_REWRITE_TAC[PAIR] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_head_is "ALL" o concl)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(x:num,m:num,pp:(A)wl_prog)`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
  MP_TAC (SPECL [`c:(A)asm_config`; `pp:(A)wl_prog`; `m:num`; `k:num`; `bs0:(A word)app_list#num`;
                 `y:(A)stack_prog`; `f:num`; `bs1:(A word)app_list#num`]
                W2SP4AUX_compile_prog_asm) THEN
  MP_TAC (SPECL [`c:(A)asm_config`; `pp:(A)wl_prog`; `m:num`; `k:num`; `bs0:(A word)app_list#num`;
                 `y:(A)stack_prog`; `f:num`; `bs1:(A word)app_list#num`]
                W2SP4AUX_compile_prog_convs) THEN
  ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL [ASM_ARITH_TAC; SIMP[]]));;

(* HOL4 line 11698: val get_code_labels_wReg = Q.prove(...) |> SIMP_RULE    *)
(* std_ss [IMP_CONJ_THM]                                                     *)
let get_code_labels_wReg = prove
 (`!(f:num->(A)stack_prog) n kf.
     ((!n. stack_get_code_labels (f n) = {})
      ==> stack_get_code_labels (wRegWrite1 f n kf) = {}) /\
     ((!n. stack_get_code_labels (f n) = {})
      ==> stack_get_code_labels (wRegWrite2 f n kf) = {})`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def; wRegWrite2_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_get_code_labels_def; UNION_EMPTY]);;

(* HOL4 line 11705 *)
let get_code_handler_labels_wStackLoad = prove
 (`!ls (x:(A)stack_prog) n.
     stack_get_code_labels (wStackLoad ls x) = stack_get_code_labels x /\
     stack_get_handler_labels n (wStackLoad ls x) = stack_get_handler_labels n x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  SIMP[wStackLoad_def; stack_get_code_labels_def; stack_get_handler_labels_def;
       UNION_EMPTY]);;

(* HOL4 line 11713 *)
let wLive_code_labels = prove
 (`!q (bs:(A word)app_list#num) kf (q':(A)stack_prog) bs'.
     wLive q bs kf = (q',bs') ==> stack_get_code_labels q' = {}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[stack_get_code_labels_def; UNION_EMPTY]);;

(* HOL4 line 11721 *)
let stack_move_code_labels = prove
 (`!a b c d (e:(A)stack_prog).
     stack_get_code_labels (stack_move a b c d e) = stack_get_code_labels e`,
  INDUCT_TAC THEN SIMP[stack_move_def; stack_get_code_labels_def; UNION_EMPTY]);;

(* HOL4 line 11728 *)
let get_code_handler_labels_copy_ret_aux = prove
 (`!k f n m.
     stack_get_code_labels (copy_ret_aux k f n:(A)stack_prog) = {} /\
     stack_get_handler_labels m (copy_ret_aux k f n:(A)stack_prog) = {}`,
  SUBGOAL_THEN
   `!k f n. stack_get_code_labels (copy_ret_aux k f n:(A)stack_prog) = {} /\
            (!m. stack_get_handler_labels m (copy_ret_aux k f n:(A)stack_prog) = {})`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; stack_list_Seq_def;
       LET_DEF; LET_END_DEF; UNION_EMPTY]);;

(* HOL4 line 11738 *)
let get_code_handler_labels_copy_ret = prove
 (`!perf b (kf:num#num#C) (vs:B list) (kont:(A)stack_prog) m.
     stack_get_code_labels (copy_ret perf b kf vs kont) = stack_get_code_labels kont /\
     stack_get_handler_labels m (copy_ret perf b kf vs kont) =
     stack_get_handler_labels m kont`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; SeqStackFree_def;
       get_code_handler_labels_copy_ret_aux; UNION_EMPTY] THEN
  COND_CASES_TAC THEN SIMP[stack_get_code_labels_def; stack_get_handler_labels_def;
                          UNION_EMPTY]);;

let _ = cake_add_simps [get_code_handler_labels_copy_ret];;

(* W2SP4AUX: the code and handler labels of the pieces of a compiled       *)
(* program                                                                    *)
let W2SP4AUX_wRegWrite_code_labels = prove
 (`!(g:num->(A)stack_prog) r kf S m.
     (!n. stack_get_code_labels (g n) = S) /\ (!n. stack_get_handler_labels m (g n) = {})
     ==> stack_get_code_labels (wRegWrite1 g r kf) = S /\
         stack_get_handler_labels m (wRegWrite1 g r kf) = {} /\
         stack_get_code_labels (wRegWrite2 g r kf) = S /\
         stack_get_handler_labels m (wRegWrite2 g r kf) = {}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def; wRegWrite2_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY]);;

let W2SP4AUX_wMove_code_labels = prove
 (`!xs kf m. stack_get_code_labels (wMove xs kf:(A)stack_prog) = {} /\
             stack_get_handler_labels m (wMove xs kf:(A)stack_prog) = {}`,
  SUBGOAL_THEN `!xy kf m. stack_get_code_labels (wMoveSingle xy kf:(A)stack_prog) = {} /\
                          stack_get_handler_labels m (wMoveSingle xy kf:(A)stack_prog) = {}`
    ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
    REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!xs kf m. stack_get_code_labels (wMoveAux xs kf:(A)stack_prog) = {} /\
                          stack_get_handler_labels m (wMoveAux xs kf:(A)stack_prog) = {}`
    ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC wMoveAux_ind THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[wMoveAux_def; stack_get_code_labels_def; stack_get_handler_labels_def;
                 UNION_EMPTY];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wMove_def] THEN ASM_REWRITE_TAC[]);;

let W2SP4AUX_wRegWrite_handler_labels = prove
 (`!(g:num->(A)stack_prog) r kf m.
     (!n. stack_get_handler_labels m (g n) = {})
     ==> stack_get_handler_labels m (wRegWrite1 g r kf) = {} /\
         stack_get_handler_labels m (wRegWrite2 g r kf) = {}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def; wRegWrite2_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  SIMP[stack_get_handler_labels_def; UNION_EMPTY]);;

let W2SP4AUX_wRegWrite1_handler_labels = prove
 (`!(g:num->(A)stack_prog) r kf m.
     (!n. stack_get_handler_labels m (g n) = {})
     ==> stack_get_handler_labels m (wRegWrite1 g r kf) = {}`,
  MESON_TAC[W2SP4AUX_wRegWrite_handler_labels]);;

let W2SP4AUX_wRegWrite2_handler_labels = prove
 (`!(g:num->(A)stack_prog) r kf m.
     (!n. stack_get_handler_labels m (g n) = {})
     ==> stack_get_handler_labels m (wRegWrite2 g r kf) = {}`,
  MESON_TAC[W2SP4AUX_wRegWrite_handler_labels]);;

let W2SP4AUX_WINST_CODE_TAC =
  REPEAT (FIRST [CONJ_TAC; PAIRARG_TAC; COND_CASES_TAC;
                 CHANGED_TAC(REWRITE_TAC[get_code_handler_labels_wStackLoad]);
                 MATCH_MP_TAC (CONJUNCT1 (SPEC_ALL get_code_labels_wReg)) THEN
                   GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL get_code_labels_wReg)) THEN
                   GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite1_handler_labels THEN GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC W2SP4AUX_wRegWrite2_handler_labels THEN GEN_TAC THEN BETA_TAC]) THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY];;

let W2SP4AUX_wInst_code_labels = prove
 (`!(i:(A)inst) kf m. stack_get_code_labels (wInst i kf) = {} /\
                      stack_get_handler_labels m (wInst i kf) = {}`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN W2SP4AUX_WINST_CODE_TAC);;

let W2SP4AUX_wShareInst_code_labels = prove
 (`!op v ad kf m. stack_get_code_labels (wShareInst op v ad kf:(A)stack_prog) = {} /\
                  stack_get_handler_labels m (wShareInst op v ad kf:(A)stack_prog) = {}`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN W2SP4AUX_WINST_CODE_TAC);;

let W2SP4AUX_call_dest_code_labels = prove
 (`!d a kf (q0:(A)stack_prog) d' m.
     call_dest d a kf = (q0,d')
     ==> stack_get_code_labels q0 = {} /\ stack_get_handler_labels m q0 = {} /\
         (!x. d' = INL x ==> d = SOME x \/ x = raise_stub_location)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def;
       get_code_handler_labels_wStackLoad; UNION_EMPTY] THEN
  MESON_TAC[]);;

let W2SP4AUX_wLive_handler_labels = prove
 (`!live (bs:(A word)app_list#num) kf q bs' m.
     wLive live bs kf = (q,bs') ==> stack_get_handler_labels m q = {}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[stack_get_handler_labels_def; UNION_EMPTY]);;

let W2SP4AUX_handler_code_labels = prove
 (`(!l1 l2 k (f:B) (f':C) m.
      stack_get_code_labels (PushHandler F l1 l2 (k,f,f'):(A)stack_prog) = {(l1,l2)} /\
      stack_get_handler_labels m (PushHandler F l1 l2 (k,f,f'):(A)stack_prog) = {}) /\
   (!k (f:B) (f':C) (prog:(A)stack_prog) m.
      stack_get_code_labels (PopHandler F (k,f,f') prog) = stack_get_code_labels prog /\
      stack_get_handler_labels m (PopHandler F (k,f,f') prog) =
      stack_get_handler_labels m prog) /\
   (!(dest:B+C) n k f f' m.
      stack_get_code_labels (StackHandlerArgs F dest n (k,f,f'):(A)stack_prog) = {} /\
      stack_get_handler_labels m (StackHandlerArgs F dest n (k,f,f'):(A)stack_prog) = {}) /\
   (!(dest:B+C) n k f f' m.
      stack_get_code_labels (StackArgs dest n (k,f,f'):(A)stack_prog) = {} /\
      stack_get_handler_labels m (StackArgs dest n (k,f,f'):(A)stack_prog) = {})`,
  SUBGOAL_THEN `!n st off i p m.
                  stack_get_handler_labels m (stack_move n st off i p:(A)stack_prog) =
                                 stack_get_handler_labels m p` ASSUME_TAC THENL
   [INDUCT_TAC THEN SIMP[stack_move_def; stack_get_handler_labels_def; UNION_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[PushHandler_F; PopHandler_F; StackHandlerArgs_F; StackArgs_def;
              LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[stack_get_code_labels_def; stack_get_handler_labels_def; stack_move_code_labels;
               UNION_EMPTY] THEN
  SET_TAC[]);;

let W2SP4AUX_DERIVE_CODE_LABELS_TAC (m:term) : tactic = fun (asl,w as g) ->
  let derive th =
    let c = concl th in
    let f = try fst(dest_const(fst(strip_comb(lhs c)))) with Failure _ -> "" in
    match f with
      "call_dest" -> [SPEC m (MATCH_MP W2SP4AUX_call_dest_code_labels th)]
    | "wLive" -> [MATCH_MP wLive_code_labels th;
                  SPEC m (MATCH_MP W2SP4AUX_wLive_handler_labels th)]
    | _ -> [] in
  let ths = flat (map (fun (_,th) -> try derive th with Failure _ -> []) asl) in
  MAP_EVERY STRIP_ASSUME_TAC ths g;;

let W2SP4AUX_wRegWrite1_LocValue_Get_labels = prove
 (`(!l1 r kf m.
      stack_get_code_labels (wRegWrite1 (\r. stack_LocValue r l1 0) r kf:(A)stack_prog) =
        {(l1,0)} /\
      stack_get_handler_labels m (wRegWrite1 (\r. stack_LocValue r l1 0) r kf:(A)stack_prog) =
        {}) /\
   (!name n kf m.
      stack_get_code_labels (wRegWrite1 (\r. stack_Get r name) n kf:(A)stack_prog) = {} /\
      stack_get_handler_labels m (wRegWrite1 (\r. stack_Get r name) n kf:(A)stack_prog) = {})`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY]);;

let W2SP4AUX_IH_INST_TAC (mk:term->term->term) : tactic = fun (asl,w as g) ->
  let eqs = mapfilter (fun (_,th) ->
      let l,r = dest_eq(concl th) in
      let f,args = strip_comb l in
      if fst(dest_const f) = "word_to_stack_comp" && is_pair r
      then (el 2 args, fst(dest_pair r)) else failwith "") asl in
  MAP_EVERY (fun (p,q) ->
      TRY (SUBGOAL_THEN (mk p q) ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC])) eqs g;;

let w2sp4aux_code_labels_ih n p q =
  vsubst [n,`n:num`; p,`p:(A)wl_prog`; q,`q:(A)stack_prog`]
   `stack_get_code_labels (q:(A)stack_prog) SUBSET
    (raise_stub_location,0) INSERT (wl_store_consts_stub_location,0) INSERT
    (IMAGE (\n. (n,0)) (wordConvs_get_code_labels (p:(A)wl_prog)) UNION
     stack_get_handler_labels n q)`;;

let W2SP4AUX_comp_code_labels = prove
 (`!(c:(A)asm_config) perf prog bs kf prog' bs' n.
     good_handlers n prog /\ perf = F /\ word_to_stack_comp c perf prog bs kf = (prog',bs')
     ==> stack_get_code_labels prog' SUBSET
         (raise_stub_location,0) INSERT (wl_store_consts_stub_location,0) INSERT
         (IMAGE (\n. (n,0)) (wordConvs_get_code_labels prog) UNION
          stack_get_handler_labels n prog')`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[good_handlers_def]) THEN
  ASM_REWRITE_TAC[] THEN W2SP4AUX_DERIVE_CODE_LABELS_TAC `n:num` THEN
  W2SP4AUX_IH_INST_TAC (w2sp4aux_code_labels_ih `n:num`) THEN
  SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; wordConvs_get_code_labels_def;
       COND_RAND; COND_RATOR; SeqStackFree_def; W2SP4AUX_handler_code_labels;
       get_code_handler_labels_wStackLoad; W2SP4AUX_wMove_code_labels;
       W2SP4AUX_wInst_code_labels; W2SP4AUX_wShareInst_code_labels;
       W2SP4AUX_wRegWrite1_LocValue_Get_labels; get_code_labels_wReg;
       W2SP4AUX_wRegWrite1_handler_labels;
       get_code_handler_labels_copy_ret; stack_move_code_labels; UNION_EMPTY;
       LET_DEF; LET_END_DEF] THEN
  TRY (W2SP4AUX_TY_CASES_TAC "sum" (cases "sum") THEN CASE_REWRITE_TAC[]) THEN
  TRY (W2SP4AUX_TY_CASES_TAC "option" (cases "option") THEN CASE_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "sum"; distinctness "sum"; option_INJ;
                              option_DISTINCT; FORALL_UNWIND_THM2; FORALL_UNWIND_THM1]) THEN
  REPEAT (FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "word_to_stack_comp"
                             with Failure _ -> false)) (concl th)))) THEN
  REPEAT CONJ_TAC THEN
  TRY (MATCH_ACCEPT_TAC EMPTY_SUBSET) THEN
  TRY (FIRST_ASSUM(fun th -> MATCH_MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) th))
       THEN SET_TAC[]) THEN
  ASM SET_TAC[]);;

(* HOL4 line 11748 *)
let word_to_stack_comp_code_labels = prove
 (`!(c:(A)asm_config) perf prog bs kf n.
     good_handlers n prog /\ perf = F
     ==> stack_get_code_labels (FST (word_to_stack_comp c perf prog bs kf)) SUBSET
         (raise_stub_location,0) INSERT (wl_store_consts_stub_location,0) INSERT
         (IMAGE (\n. (n,0)) (wordConvs_get_code_labels prog) UNION
          stack_get_handler_labels n (FST (word_to_stack_comp c perf prog bs kf)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP4AUX_comp_code_labels THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `perf:bool`; `bs:(A word)app_list#num`;
    `kf:num#num#num`; `SND (word_to_stack_comp (c:(A)asm_config) perf prog bs kf)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4 line 11814 (HOL4's UNION binds tighter than INSERT) *)
let compile_word_to_stack_code_labels = prove
 (`!(ac:(A)asm_config) perf k p bs p' bs'.
     ALL (\(n,m,pp). good_handlers n pp) p /\
     perf = F /\
     compile_word_to_stack ac perf k p bs = (p',bs')
     ==> UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND p'))) SUBSET
         (raise_stub_location,0) INSERT (wl_store_consts_stub_location,0) INSERT
         (IMAGE (\n. (n,0))
            (UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp) p))) UNION
          UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) p')))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_0; EMPTY_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `n0:num` THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `m0:num` THEN
  X_GEN_TAC `p0:(A)wl_prog` THEN
  REWRITE_TAC[compile_word_to_stack_def; LET_DEF; LET_END_DEF; ALL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[case_eq "prod"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL [`y':(A word)app_list#num`; `x'':(num#(A)stack_prog)list`;
                                 `(x''':num list,y''':(A word)app_list#num)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_lhs_head_is "word_to_stack_compile_prog" o concl)) THEN
  REWRITE_TAC[W2SP4AUX_compile_prog_eq] THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`ac:(A)asm_config`; `perf:bool`; `p0:(A)wl_prog`; `bs:(A word)app_list#num`;
    `(k:num,x':num,MAX ((max_var (p0:(A)wl_prog) DIV 2 + 1) - k) (m0 - k))`;
    `q1:(A)stack_prog`; `y':(A word)app_list#num`; `n0:num`] W2SP4AUX_comp_code_labels) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
    (try fst(dest_const(fst(strip_comb(rhs(concl th))))) = "stack_Seq"
     with Failure _ -> false))) THEN
  REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT; SND; IMAGE_UNION] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY] THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th -> is_binary "SUBSET" (concl th)))) THEN
  SET_TAC[]);;

(* W2SP4AUX: the set inclusion of word_to_stack_good_code_labels *)
let W2SP4AUX_good_code_labels_sets = prove
 (`!(A:num#num->bool) H W M E (r:num) s.
     A SUBSET (r,0) INSERT (s,0) INSERT (IMAGE (\n. n,0) W UNION H) /\
     W SUBSET M UNION E
     ==> A SUBSET (((H UNION (r,0) INSERT (s,0) INSERT IMAGE (\n. n,0) M) UNION
                    IMAGE (\n. n,0) E) UNION
                   (r,1) INSERT (s,1) INSERT IMAGE (\n. n,1) M) UNION
                  IMAGE (\n. n,1) E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\n. (n:num),0) W SUBSET IMAGE (\n. n,0) M UNION IMAGE (\n. n,0) E`
    MP_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`IMAGE (\n. (n:num),0) W`,`X:num#num->bool`) THEN
  SPEC_TAC(`IMAGE (\n. (n:num),0) M`,`Y:num#num->bool`) THEN
  SPEC_TAC(`IMAGE (\n. (n:num),0) E`,`Z:num#num->bool`) THEN
  SPEC_TAC(`IMAGE (\n. (n:num),1) M`,`Y1:num#num->bool`) THEN
  SPEC_TAC(`IMAGE (\n. (n:num),1) E`,`Z1:num#num->bool`) THEN
  SET_TAC[]);;

(* HOL4 line 11846 *)
let word_to_stack_good_code_labels = prove
 (`!(asm_conf:(A)asm_config) progs bytes bs fs prog' elabs.
     word_to_stack_compile asm_conf F progs = (bytes,bs,fs,prog') /\
     wordConvs_good_code_labels progs elabs
     ==> stack_good_code_labels prog' elabs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[case_eq "prod"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_good_code_labels_def]) THEN
  REWRITE_TAC[stack_good_code_labels_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MAP_FST_compile_word_to_stack) THEN
  MP_TAC (ISPECL [`asm_conf:(A)asm_config`; `F`;
    `asm_config_reg_count (asm_conf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs asm_conf))`;
    `progs:(num#num#(A)wl_prog)list`; `misc_List [word 4:A word],1`;
    `x:(num#(A)stack_prog)list`; `(x':num list,y':(A word)app_list#num)`]
    compile_word_to_stack_code_labels) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT; SND; FST] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def; stack_get_code_labels_def;
              stack_get_handler_labels_def; UNION_EMPTY] THEN
  DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC W2SP4AUX_good_code_labels_sets THEN
  EXISTS_TAC `UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp)
                                       (progs:(num#num#(A)wl_prog)list)))` THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 11873 *)
let word_to_stack_good_code_labels_incr = prove
 (`!elabs (ac:(A)asm_config) k prog bs prog' fs' bs'.
     raise_stub_location IN elabs /\
     wl_store_consts_stub_location IN elabs /\
     compile_word_to_stack ac F k prog bs = (prog',fs',bs')
     ==> wordConvs_good_code_labels prog elabs
     ==> stack_good_code_labels prog' elabs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wordConvs_good_code_labels_def; stack_good_code_labels_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MAP_FST_compile_word_to_stack) THEN
  MP_TAC (ISPECL [`ac:(A)asm_config`; `F`; `k:num`;
    `prog:(num#num#(A)wl_prog)list`; `bs:(A word)app_list#num`;
    `prog':(num#(A)stack_prog)list`; `(fs':num list,bs':(A word)app_list#num)`]
    compile_word_to_stack_code_labels) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(raise_stub_location,0) INSERT (wl_store_consts_stub_location,0) INSERT
         (IMAGE (\n. (n,0))
            (UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp)
               (prog:(num#num#(A)wl_prog)list)))) UNION
          UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp)
            (prog':(num#(A)stack_prog)list))))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\n. (n:num),0)
       (UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp)
          (prog:(num#num#(A)wl_prog)list)))) SUBSET
       IMAGE (\n. n,0) (set_of_list (MAP FST prog)) UNION IMAGE (\n. n,0) elabs`
    MP_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((raise_stub_location,0) IN IMAGE (\n. (n:num),0) elabs) /\
                ((wl_store_consts_stub_location,0) IN IMAGE (\n. (n:num),0) elabs)`
    MP_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`IMAGE (\n. (n:num),0)
       (UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp)
          (prog:(num#num#(A)wl_prog)list))))`,`X:num#num->bool`) THEN
  SPEC_TAC(`IMAGE (\n. (n:num),0) (set_of_list (MAP FST (prog:(num#num#(A)wl_prog)list)))`,
           `Y:num#num->bool`) THEN
  SPEC_TAC(`IMAGE (\n. (n:num),0) elabs`,`Z:num#num->bool`) THEN
  SET_TAC[]);;

(* HOL4 line 11897 *)
let sub_union_lemma = prove
 (`!(x:A->bool) y z. x SUBSET y ==> x SUBSET y UNION z`,
  SET_TAC[]);;

(* W2SP4AUX: restrict_nonzero drops the labels with offset 0 *)
let W2SP4AUX_restrict_nonzero_lemma = prove
 (`!(A:num#num->bool) H W (r:num) s.
     A SUBSET (r,0) INSERT (s,0) INSERT (IMAGE (\n. n,0) W UNION H)
     ==> restrict_nonzero A SUBSET H`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_ELIM_THM; IN_INSERT; IN_UNION; IN_IMAGE] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:num#num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num#num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN ASM_MESON_TAC[]);;

(* HOL4 line 11903 *)
let word_to_stack_good_handler_labels = prove
 (`!prog (asm_conf:(A)asm_config) bytes bs fs prog'.
     ALL (\(n,m,pp). good_handlers n pp) prog
     ==> word_to_stack_compile asm_conf F prog = (bytes,bs,fs,prog')
     ==> stack_good_handler_labels prog'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[case_eq "prod"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[stack_good_handler_labels_def] THEN MATCH_MP_TAC sub_union_lemma THEN
  MP_TAC (ISPECL [`asm_conf:(A)asm_config`; `F`;
    `asm_config_reg_count (asm_conf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs asm_conf))`;
    `prog:(num#num#(A)wl_prog)list`; `misc_List [word 4:A word],1`;
    `x:(num#(A)stack_prog)list`; `(x':num list,y':(A word)app_list#num)`]
    compile_word_to_stack_code_labels) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT; SND; FST] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def; stack_get_code_labels_def;
              stack_get_handler_labels_def; UNION_EMPTY] THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP W2SP4AUX_restrict_nonzero_lemma));;

(* HOL4 line 11931 *)
let word_to_stack_good_handler_labels_incr = prove
 (`!prog (ac:(A)asm_config) k bs prog' fs' bs'.
     ALL (\(n,m,pp). good_handlers n pp) prog
     ==> compile_word_to_stack ac F k prog bs = (prog',fs',bs')
     ==> stack_good_handler_labels prog'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[stack_good_handler_labels_def] THEN MATCH_MP_TAC sub_union_lemma THEN
  MP_TAC (ISPECL [`ac:(A)asm_config`; `F`; `k:num`;
    `prog:(num#num#(A)wl_prog)list`; `bs:(A word)app_list#num`;
    `prog':(num#(A)stack_prog)list`; `(fs':num list,bs':(A word)app_list#num)`]
    compile_word_to_stack_code_labels) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP W2SP4AUX_restrict_nonzero_lemma));;

(* W2SP4AUX: wMoveSingle has no Install *)
let W2SP4AUX_wMoveSingle_no_install = prove
 (`!xy kf. stack_no_install (wMoveSingle xy kf:(A)stack_prog)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN SIMP[stack_no_install_def]);;

(* HOL4 line 11959 *)
let wMoveAux_no_install_lem = prove
 (`!xs kf. stack_no_install (wMoveAux xs kf:(A)stack_prog)`,
  MATCH_MP_TAC wMoveAux_ind THEN REPEAT STRIP_TAC THEN
  SIMP[wMoveAux_def; stack_no_install_def; W2SP4AUX_wMoveSingle_no_install]);;

(* HOL4 line 11968 *)
let wStackLoad_no_install_lem = prove
 (`!l (prog:(A)stack_prog). stack_no_install (wStackLoad l prog) = stack_no_install prog`,
  MATCH_MP_TAC wStackLoad_ind THEN SIMP[wStackLoad_def; stack_no_install_def]);;

(* HOL4 line 11975 *)
let wRegWrite1_no_install_lem = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. stack_no_install (prog reg)) ==> stack_no_install (wRegWrite1 prog r kf)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_no_install_def]);;

(* HOL4 line 11985 *)
let wRegWrite2_no_install_lem = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. stack_no_install (prog reg)) ==> stack_no_install (wRegWrite2 prog r kf)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_no_install_def]);;

(* HOL4 line 11995 *)
let wLive_no_install_lem = prove
 (`!live (bs:(A word)app_list#num) kf. stack_no_install (FST (wLive live bs kf))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_no_install_def] THEN PAIRARG_TAC THEN SIMP[stack_no_install_def]);;

(* HOL4 line 12004 *)
let stack_move_no_install_lem = prove
 (`!n start offset i (p:(A)stack_prog).
     stack_no_install (stack_move n start offset i p) = stack_no_install p`,
  INDUCT_TAC THEN SIMP[stack_move_def; stack_no_install_def]);;

(* HOL4 line 12012 *)
let copy_ret_aux_no_install = prove
 (`!k f n. stack_no_install (copy_ret_aux k f n:(A)stack_prog)`,
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[stack_no_install_def; stack_list_Seq_def; LET_DEF; LET_END_DEF]);;

(* HOL4 line 12021 *)
let copy_ret_no_install = prove
 (`!perf b (kf:num#num#C) (vs:B list) (kont:(A)stack_prog).
     stack_no_install (copy_ret perf b kf vs kont) <=> stack_no_install kont`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[stack_no_install_def; SeqStackFree_def; copy_ret_aux_no_install] THEN
  COND_CASES_TAC THEN SIMP[stack_no_install_def]);;

let _ = cake_add_simps [copy_ret_no_install];;

(* W2SP4AUX: the pieces of a compiled program have no Install *)
let W2SP4AUX_wInst_no_install = prove
 (`!(i:(A)inst) kf. stack_no_install (wInst i kf)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[wStackLoad_no_install_lem]);
                 MATCH_MP_TAC wRegWrite1_no_install_lem THEN GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC wRegWrite2_no_install_lem THEN GEN_TAC THEN BETA_TAC;
                 COND_CASES_TAC]) THEN
  SIMP[stack_no_install_def]);;

let W2SP4AUX_call_dest_no_install = prove
 (`!d a kf (q0:(A)stack_prog) d'. call_dest d a kf = (q0,d') ==> stack_no_install q0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[stack_no_install_def; wStackLoad_no_install_lem]);;

let W2SP4AUX_wShareInst_no_install = prove
 (`!op v ad kf. stack_no_install (wShareInst op v ad kf:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wShareInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[wStackLoad_no_install_lem]);
                 MATCH_MP_TAC wRegWrite1_no_install_lem THEN GEN_TAC THEN BETA_TAC]) THEN
  SIMP[stack_no_install_def]);;

let W2SP4AUX_wMove_no_install = prove
 (`!xs kf. stack_no_install (wMove xs kf:(A)stack_prog)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wMove_def; wMoveAux_no_install_lem]);;

let W2SP4AUX_wLive_no_install' = prove
 (`!live (bs:(A word)app_list#num) kf q bs'.
     wLive live bs kf = (q,bs') ==> stack_no_install q`,
  REPEAT STRIP_TAC THEN MP_TAC (SPECL [`live:cutsets`; `bs:(A word)app_list#num`;
    `kf:num#num#num`] wLive_no_install_lem) THEN ASM_REWRITE_TAC[FST]);;

(* HOL4 line 12029 *)
let comp_no_install = prove
 (`!(ac:(A)asm_config) perf prog bs kf prog' bs'.
     wordConvs_no_install prog /\
     word_to_stack_comp ac perf prog bs kf = (prog',bs') /\ perf = F
     ==> stack_no_install prog'`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[wordConvs_no_install_def]) THEN
  SIMP[stack_no_install_def; W2SP4AUX_wMove_no_install; COND_RAND;
     wStackLoad_no_install_lem; stack_move_no_install_lem; W2SP4AUX_wInst_no_install;
     W2SP4AUX_wShareInst_no_install; SeqStackFree_def; PushHandler_F; PopHandler_F;
     StackHandlerArgs_F; StackArgs_def; copy_ret_no_install] THEN
  TRY (MATCH_MP_TAC wRegWrite1_no_install_lem THEN SIMP[stack_no_install_def]) THEN
  REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[W2SP4AUX_wLive_no_install'; W2SP4AUX_call_dest_no_install]);;

(* HOL4 line 12129 *)
let compile_word_to_stack_no_install = prove
 (`!(ac:(A)asm_config) perf k prog bs prog' fs' bs'.
     ALL (\(n,m,pp). wordConvs_no_install pp) prog /\
     compile_word_to_stack ac perf k prog bs = (prog',fs',bs') /\
     perf = F
     ==> ALL (\(a,p). stack_no_install p) prog'`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_word_to_stack_def; LET_DEF; LET_END_DEF; ALL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_lhs_head_is "word_to_stack_compile_prog" o concl)) THEN
    REWRITE_TAC[W2SP4AUX_compile_prog_eq] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[stack_no_install_def] THEN MATCH_MP_TAC comp_no_install THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* W2SP4AUX: wMoveSingle has no ShMemOp *)
let W2SP4AUX_wMoveSingle_no_shmemop = prove
 (`!xy kf. no_shmemop (wMoveSingle xy kf:(A)stack_prog)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC[wMoveSingle_def] THEN
  REPEAT W2SP4AUX_SUM_CASES_TAC THEN CASE_REWRITE_TAC[] THEN SIMP[no_shmemop_def]);;

(* HOL4 line 12151 *)
let wMoveAux_no_shmemop_lem = prove
 (`!xs kf. no_shmemop (wMoveAux xs kf:(A)stack_prog)`,
  MATCH_MP_TAC wMoveAux_ind THEN REPEAT STRIP_TAC THEN
  SIMP[wMoveAux_def; no_shmemop_def; W2SP4AUX_wMoveSingle_no_shmemop]);;

(* HOL4 line 12160 *)
let wStackLoad_no_shmemop_lem = prove
 (`!l (prog:(A)stack_prog). no_shmemop (wStackLoad l prog) = no_shmemop prog`,
  MATCH_MP_TAC wStackLoad_ind THEN SIMP[wStackLoad_def; no_shmemop_def]);;

(* HOL4 line 12167 *)
let wRegWrite1_no_shmemop_lem = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. no_shmemop (prog reg)) ==> no_shmemop (wRegWrite1 prog r kf)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite1_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[no_shmemop_def]);;

(* HOL4 line 12177 *)
let wRegWrite2_no_shmemop_lem = prove
 (`!(prog:num->(A)stack_prog) r kf.
     (!reg. no_shmemop (prog reg)) ==> no_shmemop (wRegWrite2 prog r kf)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wRegWrite2_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[no_shmemop_def]);;

(* HOL4 line 12187 *)
let wLive_no_shmemop_lem = prove
 (`!live (bs:(A word)app_list#num) kf. no_shmemop (FST (wLive live bs kf))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wLive_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[no_shmemop_def] THEN PAIRARG_TAC THEN SIMP[no_shmemop_def]);;

(* HOL4 line 12196 *)
let stack_move_no_shmemop_lem = prove
 (`!n start offset i (p:(A)stack_prog).
     no_shmemop (stack_move n start offset i p) = no_shmemop p`,
  INDUCT_TAC THEN SIMP[stack_move_def; no_shmemop_def]);;

(* HOL4 line 12204 *)
let copy_ret_aux_no_shmemop = prove
 (`!k f n. no_shmemop (copy_ret_aux k f n:(A)stack_prog)`,
  MATCH_MP_TAC copy_ret_aux_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_ret_aux_def] THEN COND_CASES_TAC THEN
  SIMP[no_shmemop_def; stack_list_Seq_def; LET_DEF; LET_END_DEF]);;

(* HOL4 line 12213 *)
let copy_ret_no_shmemop = prove
 (`!perf b (kf:num#num#C) (vs:B list) (kont:(A)stack_prog).
     no_shmemop (copy_ret perf b kf vs kont) <=> no_shmemop kont`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_ret_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  SIMP[no_shmemop_def; SeqStackFree_def; copy_ret_aux_no_shmemop] THEN
  COND_CASES_TAC THEN SIMP[no_shmemop_def]);;

let _ = cake_add_simps [copy_ret_no_shmemop];;

(* HOL4 line 12221 *)
let perf_call_prefix_no_shmemop = prove
 (`!l1 l2 kf0. no_shmemop (perf_call_prefix l1 l2 kf0:(A)stack_prog)`,
  SIMP[perf_call_prefix_def; no_shmemop_def; stack_list_Seq_def]);;

(* HOL4 line 12227 *)
let perf_call_suffix_no_shmemop = prove
 (`no_shmemop (perf_call_suffix:(A)stack_prog)`,
  SIMP[perf_call_suffix_def; no_shmemop_def; stack_list_Seq_def]);;

(* HOL4 line 12233 *)
let PushHandler_no_shmemop = prove
 (`!perf l1 l2 (kff:num#B#C). no_shmemop (PushHandler perf l1 l2 kff:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PushHandler_def] THEN COND_CASES_TAC THEN
  SIMP[no_shmemop_def; stack_list_Seq_def]);;

(* HOL4 line 12241 *)
let PopHandler_no_shmemop = prove
 (`!perf (kff:num#B#C) (prog:(A)stack_prog).
     no_shmemop (PopHandler perf kff prog) <=> no_shmemop prog`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PopHandler_def] THEN SIMP[no_shmemop_def]);;

(* HOL4 line 12250 *)
let StackHandlerArgs_no_shmemop = prove
 (`!perf (dest:B+C) arg_count kff.
     no_shmemop (StackHandlerArgs perf dest arg_count kff:(A)stack_prog)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[StackHandlerArgs_def; StackArgs_def; LET_DEF; LET_END_DEF] THEN
  SIMP[stack_move_no_shmemop_lem; no_shmemop_def]);;

(* W2SP4AUX: the pieces of a compiled program have no ShMemOp *)
let W2SP4AUX_wInst_no_shmemop = prove
 (`!(i:(A)inst) kf. no_shmemop (wInst i kf)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REPEAT W2SP4AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC[wInst_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [PAIRARG_TAC; CHANGED_TAC(REWRITE_TAC[wStackLoad_no_shmemop_lem]);
                 MATCH_MP_TAC wRegWrite1_no_shmemop_lem THEN GEN_TAC THEN BETA_TAC;
                 MATCH_MP_TAC wRegWrite2_no_shmemop_lem THEN GEN_TAC THEN BETA_TAC;
                 COND_CASES_TAC]) THEN
  SIMP[no_shmemop_def]);;

let W2SP4AUX_call_dest_no_shmemop = prove
 (`!d a kf (q0:(A)stack_prog) d'. call_dest d a kf = (q0,d') ==> no_shmemop q0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  STRUCT_CASES_TAC (ISPEC `d:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[no_shmemop_def; wStackLoad_no_shmemop_lem]);;

let W2SP4AUX_wMove_no_shmemop = prove
 (`!xs kf. no_shmemop (wMove xs kf:(A)stack_prog)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; wMove_def; wMoveAux_no_shmemop_lem]);;

let W2SP4AUX_wLive_no_shmemop' = prove
 (`!live (bs:(A word)app_list#num) kf q bs'.
     wLive live bs kf = (q,bs') ==> no_shmemop q`,
  REPEAT STRIP_TAC THEN MP_TAC (SPECL [`live:cutsets`; `bs:(A word)app_list#num`;
    `kf:num#num#num`] wLive_no_shmemop_lem) THEN ASM_REWRITE_TAC[FST]);;

(* HOL4 line 12259 *)
let comp_no_shmemop = prove
 (`!(ac:(A)asm_config) perf prog bs kf prog' bs'.
     no_share_inst prog /\
     word_to_stack_comp ac perf prog bs kf = (prog',bs')
     ==> no_shmemop prog'`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN W2SP4AUX_CALL_SPLIT_TAC THEN W2SP4AUX_KF_SPLIT_TAC THEN
  W2SP4AUX_COMP_UNFOLD_TAC "prog'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[no_share_inst_def]) THEN
  SIMP[no_shmemop_def; W2SP4AUX_wMove_no_shmemop; COND_RAND;
     wStackLoad_no_shmemop_lem; stack_move_no_shmemop_lem; W2SP4AUX_wInst_no_shmemop;
     SeqStackFree_def; PushHandler_no_shmemop; PopHandler_no_shmemop;
     StackHandlerArgs_no_shmemop; StackArgs_def; copy_ret_no_shmemop;
     perf_call_prefix_no_shmemop; perf_call_suffix_no_shmemop] THEN
  TRY (MATCH_MP_TAC wRegWrite1_no_shmemop_lem THEN SIMP[no_shmemop_def]) THEN
  REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[W2SP4AUX_wLive_no_shmemop'; W2SP4AUX_call_dest_no_shmemop]);;

(* HOL4 line 12359 *)
let compile_word_to_stack_no_share_inst = prove
 (`!(ac:(A)asm_config) perf k prog bs prog' fs' bs'.
     ALL (\(n,m,pp). no_share_inst pp) prog /\
     compile_word_to_stack ac perf k prog bs = (prog',fs',bs')
     ==> ALL (\(a,p). no_shmemop p) prog'`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_word_to_stack_def; LET_DEF; LET_END_DEF; ALL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_lhs_head_is "word_to_stack_compile_prog" o concl)) THEN
    REWRITE_TAC[W2SP4AUX_compile_prog_eq] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[no_shmemop_def] THEN MATCH_MP_TAC comp_no_shmemop THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 12378 *)
let compile_no_shmemop = prove
 (`!(cf:(A)asm_config) prog bs fs ns prog'.
     word_to_stack_compile cf F prog = (bs,fs,ns,prog') /\
     ALL (\(n,m,pp). no_share_inst pp) prog
     ==> ALL (\(a,p). no_shmemop p) prog'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def] THEN SIMP[no_shmemop_def] THEN
  MATCH_MP_TAC compile_word_to_stack_no_share_inst THEN ASM_MESON_TAC[]);;

(* HOL4 line 12392 *)
let word_to_stack_compile_no_install = prove
 (`!(prog:(num#num#(A)wl_prog)list) (ac:(A)asm_config) bm c fs p.
     ALL_DISTINCT (MAP FST prog) /\
     no_install_code (fromAList prog) /\
     word_to_stack_compile ac F prog = (bm,c,fs,p)
     ==> ALL (\(n,x). stack_no_install x) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[raise_stub_F; store_consts_stub_def] THEN SIMP[stack_no_install_def] THEN
  MATCH_MP_TAC compile_word_to_stack_no_install THEN
  MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `F`;
    `asm_config_reg_count (ac:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs ac))`;
    `prog:(num#num#(A)wl_prog)list`; `misc_List [word 4:A word],1`;
    `fs':num list`; `bitmaps:(A word)app_list#num`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp4aux_head_is "no_install_code" o concl)) THEN
  REWRITE_TAC[no_install_code_def; lookup_fromAList] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p1:num`; `p1':num`] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[]);;
