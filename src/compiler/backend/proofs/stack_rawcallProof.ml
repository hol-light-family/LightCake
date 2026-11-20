(* ========================================================================= *)
(* stack_rawcallProof: port of HOL4 compiler/backend/proofs/                *)
(* stack_rawcallProofScript.sml (CakeML v3479).                              *)
(* Correctness proof for stack_rawcall.                                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 lists wordSem[qualified] and labProps[qualified] among the         *)
(*   Ancestors; the script uses no name of labProps, and of wordSem only     *)
(*   theWord_def and isWord_def in local abbreviations that no proof uses:   *)
(*   neither is loaded.                                                      *)
(* - HOL4 Type prog = :'a stackLang$prog (a type abbreviation) is written    *)
(*   out: (A)stack_prog.                                                     *)
(* - STACKPROPSAUX_ names are local helpers (the unit's helper prefix).      *)

(* small tactics of the proofs below *)

(* the induction hypotheses of a comp_ind induction after a case split *)

let STACKPROPSAUX_RC_IH_RWS =
  [distinctness "stack_prog"; injectivity "stack_prog"; option_INJ;
   option_DISTINCT; PAIR_EQ; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
   FORALL_UNWIND_THM2];;

let stack_rawcallProof_state_ok_def = cake_def
  `stack_rawcallProof_state_ok (i:num spt) (code:((A)stack_prog)spt) <=>
     !n v. lookup n i = SOME v ==>
           ?p. lookup n code = SOME (stack_Seq (StackAlloc v) p)`;;

let stack_rawcallProof_state_rel_def = cake_def
  `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t <=>
     ?c. domain c = domain (stack_state_code s) /\
         t = stack_state_code_fupd (K c) s /\
         stack_rawcallProof_state_ok i (stack_state_code s) /\
         !n b. lookup n (stack_state_code s) = SOME b ==>
               ?i. stack_rawcallProof_state_ok i (stack_state_code s) /\
                   lookup n c = SOME (comp_top i b)`;;

(* HOL4: state_rel_thm = state_rel_def |> SIMP_RULE (srw_ss())               *)
(* [state_component_equality]                                                *)

let stack_rawcallProof_state_rel_thm = prove
 (`stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t <=>
     domain (stack_state_code t) = domain (stack_state_code s) /\
     stack_state_regs t = stack_state_regs s /\
     stack_state_fp_regs t = stack_state_fp_regs s /\
     stack_state_store t = stack_state_store s /\
     stack_state_stack t = stack_state_stack s /\
     stack_state_stack_space t = stack_state_stack_space s /\
     stack_state_memory t = stack_state_memory s /\
     stack_state_mdomain t = stack_state_mdomain s /\
     stack_state_sh_mdomain t = stack_state_sh_mdomain s /\
     stack_state_bitmaps t = stack_state_bitmaps s /\
     stack_state_compile t = stack_state_compile s /\
     stack_state_compile_oracle t = stack_state_compile_oracle s /\
     stack_state_code_buffer t = stack_state_code_buffer s /\
     stack_state_data_buffer t = stack_state_data_buffer s /\
     stack_state_gc_fun t = stack_state_gc_fun s /\
     stack_state_use_stack t = stack_state_use_stack s /\
     stack_state_use_store t = stack_state_use_store s /\
     stack_state_use_alloc t = stack_state_use_alloc s /\
     stack_state_clock t = stack_state_clock s /\
     stack_state_ffi t = stack_state_ffi s /\
     stack_state_ffi_save_regs t = stack_state_ffi_save_regs s /\
     stack_state_be t = stack_state_be s /\
     stack_rawcallProof_state_ok i (stack_state_code s) /\
     !n b. lookup n (stack_state_code s) = SOME b ==>
           ?i. stack_rawcallProof_state_ok i (stack_state_code s) /\
               lookup n (stack_state_code t) = SOME (comp_top i b)`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def; stack_state_component_equality] THEN
  SIMP[] THEN EQ_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN EXISTS_TAC `stack_state_code (t:(A,C,FFI)stack_state)` THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)

let with_stack_space = prove
 (`stack_state_stack_space_fupd (K (stack_state_stack_space t1)) (t1:(A,C,FFI)stack_state) =
   t1`,
  REWRITE_TAC[stack_state_component_equality] THEN SIMP[]);;

(* the equations of stack_rawcall_comp and comp_top for each constructor *)

let STACKPROPSAUX_rc_comp_thms =
  let ci = case_info_of_tyname "stack_prog" in
  let ty = `:(A)stack_prog` in
  let i = `i:num spt` in
  let mk c d =
    end_itlist CONJ
     (map (fun (vs,pat) ->
            let tyi = type_match (type_of pat) ty [] in
            let pat = inst tyi pat in
            let tm = mk_comb(mk_comb(c,i),pat) in
            GEN_ALL ((REWR_CONV d THENC CASE_REWRITE_CONV[]) tm))
          ci.ci_pats) in
  CONJ (mk `stack_rawcall_comp:num spt->(A)stack_prog->(A)stack_prog`
           stack_rawcall_comp_def)
       (mk `comp_top:num spt->(A)stack_prog->(A)stack_prog` comp_top_def);;


let comp_LN = prove
 (`!(i:num spt) (b:(A)stack_prog). comp_top LN b = b /\ stack_rawcall_comp LN b = b`,
  SUBGOAL_THEN `!(i:num spt) (b:(A)stack_prog). i = LN ==> stack_rawcall_comp i b = b`
    ASSUME_TAC THENL
   [MATCH_MP_TAC stack_rawcall_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    DISCH_TAC THEN RVEQ_TAC THEN CASES_ON `p:(A)stack_prog` THEN
    RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
    REWRITE_TAC[STACKPROPSAUX_rc_comp_thms; comp_seq_def; lookup_def] THEN
    EVERY_CASE_TAC THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
    ASM_REWRITE_TAC[lookup_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[] o SPEC `LN:num spt`) THEN
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN CASES_ON `b:(A)stack_prog` THEN
    ASM_REWRITE_TAC[STACKPROPSAUX_rc_comp_thms]]);;

let comp_seq_neq_IMP = prove
 (`~(comp_seq p1 p2 i (default:(A)stack_prog) = default) ==>
   ?k dest. p1 = StackFree k /\ p2 = stack_Call NONE (INL dest) NONE`,
  REWRITE_TAC[comp_seq_def; dest_case_def] THEN
  CASES_ON `p1:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `p2:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* comp keeps the syntactic properties of the programs (HOL4: by comp_ind, *)
(* as get_labels_comp); in the case Seq, comp_seq is the default or the     *)
(* RawCall optimisation (comp_seq_neq_IMP, as HOL4)                          *)

let STACKPROPSAUX_COMP_SEQ_TAC : tactic = fun (asl,w as g) ->
  let cs = find_term (fun t -> is_comb t &&
             (try fst(dest_const(fst(strip_comb t))) = "comp_seq" with Failure _ -> false) &&
             length (snd (strip_comb t)) = 4) w in
  (ASM_CASES_TAC (mk_eq(cs,rand cs)) THENL
    [ASM_REWRITE_TAC[];
     FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP comp_seq_neq_IMP) THEN RVEQ_TAC THEN
     REWRITE_TAC[comp_seq_def; dest_case_def] THEN CASE_REWRITE_TAC[] THEN
     REPEAT TOP_CASE_TAC]) g;;

let STACKPROPSAUX_RC_SYNTAX_TAC (defs:thm list) : tactic =
  MATCH_MP_TAC stack_rawcall_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
  TRY STACKPROPSAUX_COMP_SEQ_TAC THEN EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SIMP defs;;

let stack_rawcallProof_get_labels_comp = prove
 (`!i (e:(A)stack_prog).
     stack_get_labels (stack_rawcall_comp i e) = stack_get_labels e /\
     stack_get_labels (comp_top i e) = stack_get_labels e`,
  STACKPROPSAUX_RC_SYNTAX_TAC [stack_get_labels_def]);;


(* ------------------------------------------------------------------------- *)
(* comp_correct and its helpers                                              *)
(* ------------------------------------------------------------------------- *)

(* state_rel and the updates of the semantics that keep the code *)

let STACKPROPSAUX_state_rel_upd = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   stack_rawcallProof_state_rel i (stack_dec_clock s) (stack_dec_clock t) /\
   stack_rawcallProof_state_rel i (stack_empty_env s) (stack_empty_env t) /\
   (!x y. stack_rawcallProof_state_rel i (stack_set_var x y s) (stack_set_var x y t)) /\
   (!n. stack_rawcallProof_state_rel i (stack_state_clock_fupd (K n) s)
                                       (stack_state_clock_fupd (K n) t)) /\
   (!n. stack_rawcallProof_state_rel i (stack_state_stack_space_fupd (K n) s)
                                       (stack_state_stack_space_fupd (K n) t))`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EXISTS_TAC `c:((A)stack_prog)spt` THEN
  REWRITE_TAC[stack_dec_clock_def; stack_empty_env_def; stack_set_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_rel_dec_set = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   stack_rawcallProof_state_rel i (stack_dec_clock (stack_set_var x y s))
                                  (stack_dec_clock (stack_set_var x y t))`,
  SIMP[stack_rawcallProof_state_rel_def; stack_dec_clock_def; stack_set_var_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `c:((A)stack_prog)spt` THEN SIMP[]);;

(* the fields of t that state_rel fixes (HOL4 uses state_rel_thm) *)

let STACKPROPSAUX_rel_get = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   (!v. stack_get_var v t = stack_get_var v s) /\
   (!ri. stack_get_var_imm ri t = stack_get_var_imm ri s) /\
   stack_state_regs t = stack_state_regs s /\
   stack_state_clock t = stack_state_clock s /\
   stack_state_stack_space t = stack_state_stack_space s /\
   stack_state_stack t = stack_state_stack s /\
   stack_state_use_stack t = stack_state_use_stack s /\
   domain (stack_state_code t) = domain (stack_state_code s)`,
  SIMP[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[stack_get_var_def] THEN GEN_TAC THEN CASES_ON `ri:(A)reg_imm` THEN
  SIMP[stack_get_var_imm_def; stack_get_var_def]);;

let STACKPROPSAUX_rel_ok = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   stack_rawcallProof_state_ok i (stack_state_code s)`,
  SIMP[stack_rawcallProof_state_rel_def] THEN MESON_TAC[]);;

let STACKPROPSAUX_rel_lookup = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) /\
   lookup n (stack_state_code s) = SOME b
   ==> ?i'. stack_rawcallProof_state_ok i' (stack_state_code s) /\
            lookup n (stack_state_code t) = SOME (comp_top i' b)`,
  SIMP[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  ASM_MESON_TAC[]);;

let STACKPROPSAUX_rel_find_code = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) /\
   stack_find_code dest (regs:(num,(A)word_loc)fmap) (stack_state_code s) = SOME prog
   ==> ?i'. stack_rawcallProof_state_ok i' (stack_state_code s) /\
            stack_find_code dest regs (stack_state_code t) = SOME (comp_top i' prog)`,
  CASES_ON `dest:num+num` THEN SIMP[stack_find_code_def] THENL
   [MESON_TAC[STACKPROPSAUX_rel_lookup];
    EVERY_CASE_TAC THEN SIMP[] THEN MESON_TAC[STACKPROPSAUX_rel_lookup]]);;

(* state_rel i' with another i, when the code only grew *)

let STACKPROPSAUX_state_rel_mono = prove
 (`!i' s2 (t1:(A,C,FFI)stack_state) i (s:(A,C,FFI)stack_state).
   stack_rawcallProof_state_rel i' s2 t1 /\
   stack_rawcallProof_state_ok i (stack_state_code s) /\
   subspt (stack_state_code s) (stack_state_code s2)
   ==> stack_rawcallProof_state_rel i s2 t1`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def; stack_rawcallProof_state_ok_def] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `c:((A)stack_prog)spt` THEN ASM_MESON_TAC[subspt_lookup]);;

let STACKPROPSAUX_state_ok_union = prove
 (`!j p code. stack_rawcallProof_state_ok j code ==>
              stack_rawcallProof_state_ok j (union code (p:((A)stack_prog)spt))`,
  SIMP[stack_rawcallProof_state_ok_def; lookup_union] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN SIMP[]);;

let STACKPROPSAUX_comp_call_some = prove
 (`!i rh lr l1 l2 dest handler.
     stack_rawcall_comp i (stack_Call (SOME (rh,lr,l1,l2)) dest handler:(A)stack_prog) =
     stack_Call (SOME (stack_rawcall_comp i rh,lr,l1,l2)) dest
       (OPTION_MAP (\(p2,k1,k2). (stack_rawcall_comp i p2,k1,k2)) handler)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN SIMP[]);;

let STACKPROPSAUX_dest_Seq_SOME = prove
 (`!p x y. stack_dest_Seq (p:(A)stack_prog) = SOME (x,y) <=> p = stack_Seq x y`,
  GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  REWRITE_TAC[stack_dest_Seq_def; option_DISTINCT; option_INJ; PAIR_EQ;
              distinctness "stack_prog"; injectivity "stack_prog"] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_rel_code_fupd = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   t = stack_state_code_fupd (K (stack_state_code t)) s`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

let STACKPROPSAUX_word_exp_code = prove
 (`stack_word_exp (stack_state_code_fupd (K c) (s:(A,C,FFI)stack_state)) e =
   stack_word_exp s e`,
  MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN SIMP[]);;

(* tactics of comp_correct *)

let STACKPROPSAUX_RC_DEFS =
  [stack_evaluate_def; stack_get_var_def; stack_set_var_def; loc_check_def;
   stack_mem_load_def; stackSem_alloc_def; stack_gc_def; stack_set_store_def;
   stack_inst_def; stack_assign_def; stack_word_exp_def; stack_get_vars_def;
   stack_mem_store_def; stack_get_fp_var_def; stack_set_fp_var_def; word_op_def;
   store_const_sem_def; stack_empty_env_def; stack_dec_clock_def];;

(* HOL4 simple_case: target and source run alike, with the clock unchanged *)

let STACKPROPSAUX_RC_SIMPLE_TAC : tactic =
  EXISTS_TAC `0` THEN
  FS[STACKPROPSAUX_rc_comp_thms; stack_rawcallProof_state_rel_def] THEN RVEQ_TAC THEN
  FS STACKPROPSAUX_RC_DEFS THEN GVS (CONJUNCTS stack_case_eq_thms) THEN
  GVS[LEFT_AND_EXISTS_THM] THEN
  SIMP[stack_state_component_equality; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
       EXISTS_BOOL_THM];;

(* unfold the source evaluation one step and split its cases *)

let STACKPROPSAUX_is_src th = STACKPAUX_is_eval_eq (concl th);;

let STACKPROPSAUX_RC_SRC_TAC thl : tactic =
  FIRST_X_ASSUM (CAKE_STRIP_ASSUME_TAC o
                 CAKE_SIMP_RULE (thl @ CONJUNCTS stack_case_eq_thms) o
                 ONCE_REWRITE_RULE[stack_evaluate_def] o check STACKPROPSAUX_is_src) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC);;

(* the target stops at once, in state f t *)

let STACKPROPSAUX_RC_ZERO_TAC f : tactic =
  EXISTS_TAC `0` THEN
  (fun (asl,w as g) ->
     let t1 = f `t:(A,C,FFI)stack_state` in
     MAP_EVERY EXISTS_TAC
       [t1; mk_comb(`stack_state_stack_space:(A,C,FFI)stack_state->num`,t1)] g) THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  FS[stack_find_code_def; with_stack_space; STACKPROPSAUX_state_rel_upd;
     stack_dest_Seq_def; stack_state_component_equality];;

let STACKPROPSAUX_empty_f t =
  mk_comb(`stack_empty_env:(A,C,FFI)stack_state->(A,C,FFI)stack_state`,t);;

(* drop the induction hypotheses (but keep the equations of rel_get) *)

let STACKPROPSAUX_RC_DROP_IHS_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let c = concl th in
    if is_forall c && is_imp (snd (strip_forall c)) then ALL_TAC else failwith "keep"));;

(* HOL4 rfs [] on the induction hypotheses only: they are rewritten with the *)
(* other assumptions, which instantiates them                               *)

let STACKPROPSAUX_RC_IH_TAC : tactic = fun (asl,w as g) ->
  let facts = filter (fun th -> not (is_forall (concl th))) (map snd asl) in
  let rws = facts @ STACKPROPSAUX_RC_IH_RWS @
            [distinctness "stack_result"; injectivity "stack_result";
             injectivity "word_loc"] in
  RULE_ASSUM_TAC (fun th ->
    if is_forall (concl th) && is_imp (snd (strip_forall (concl th)))
    then REWRITE_RULE rws th else th) g;;

(* a call (JumpLower, RawCall, Call) of a program of the code, compiled     *)
(* with i': the induction hypothesis at the callee, with the witnesses wit  *)

let STACKPROPSAUX_RC_CALL_TAC wit : tactic =
  MP_TAC(ISPECL [`i:num spt`; `s:(A,C,FFI)stack_state`; `t:(A,C,FFI)stack_state`;
                 `i':num spt`; `s:(A,C,FFI)stack_state`] STACKPROPSAUX_state_rel_mono) THEN
  ASM_REWRITE_TAC[subspt_refl] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_state_rel_upd) THEN
  RES_TAC THEN STACKPROPSAUX_RC_DROP_IHS_TAC THEN MAP_EVERY EXISTS_TAC wit THEN
  IMP_RES_TAC stack_evaluate_mono THEN IMP_RES_TAC STACKPROPSAUX_rel_ok THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  FS[stack_find_code_def; STACKPROPSAUX_dec_clock_add; STACKPROPSAUX_dec_clock_clock;
     stack_dest_Seq_def] THEN
  MATCH_MP_TAC STACKPROPSAUX_state_rel_mono THEN
  MAP_EVERY EXISTS_TAC [`i':num spt`; `s:(A,C,FFI)stack_state`] THEN
  FS[stack_dec_clock_def];;

(* the witnesses ck t1 k1 of an existential, named c t k *)

let STACKPROPSAUX_CHOOSE3 c t k =
  X_CHOOSE_THEN (mk_var(c,`:num`))
   (X_CHOOSE_THEN (mk_var(t,`:(A,C,FFI)stack_state`))
     (X_CHOOSE_THEN (mk_var(k,`:num`)) STRIP_ASSUME_TAC));;

(* ASM_ARITH_TAC with only the arithmetic assumptions (much faster here) *)

let STACKPROPSAUX_NUM_ARITH_TAC : tactic = fun (asl,w as g) ->
  let is_num_rel tm =
    let tm = if is_neg tm then dest_neg tm else tm in
    (is_eq tm || is_binary "<" tm || is_binary "<=" tm) &&
    type_of (lhand tm) = `:num` in
  (MAP_EVERY (MP_TAC o snd) (filter (is_num_rel o concl o snd) asl) THEN ARITH_TAC) g;;

(* HOL4 qsuff_tac `pat1 = pat2` for two runs stack_evaluate (q,x) and       *)
(* stack_evaluate (q,y) in the goal: proves y = x by the component          *)
(* equality and arithmetic, and replaces y by x                             *)

let STACKPROPSAUX_SAME_RUN_TAC : tactic = fun (asl,w as g) ->
  let fw = frees w in
  let evs = find_terms (fun t -> is_comb t &&
                          (try fst(dest_const(rator t)) = "stack_evaluate"
                           with Failure _ -> false) && subset (frees t) fw) w in
  let args = map (fun t -> dest_pair (rand t)) evs in
  let (_,x),(_,y) = find (fun ((q1,x1),(q2,x2)) -> q1 = q2 && not (x1 = x2))
                         (allpairs (fun a b -> (a,b)) args args) in
  (SUBGOAL_THEN (mk_eq(y,x)) SUBST1_TAC THENL
    [REWRITE_TAC[stack_state_component_equality] THEN
     SIMP[stack_dec_clock_def; stack_set_var_def] THEN
     STACKPROPSAUX_NUM_ARITH_TAC; ALL_TAC]) g;;

let evaluate_comp_Inst = prove
 (`stack_evaluate (stack_Inst i,s) = (r,s1) /\ ~(r = SOME stack_Error) /\
   stack_rawcallProof_state_rel i' (s:(A,C,FFI)stack_state) t ==>
   ?ck t1 k1.
     stack_rawcallProof_state_rel i' s1 t1 /\
     stack_evaluate (stack_rawcall_comp i' (stack_Inst i),
                     stack_state_clock_fupd (K (ck + stack_state_clock t)) t) =
     (r,stack_state_stack_space_fupd (K k1) t1) /\
     (~(r = SOME stack_TimeOut) /\ ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
      k1 = stack_state_stack_space t1)`,
  STRIP_TAC THEN EXISTS_TAC `0` THEN
  FS[STACKPROPSAUX_rc_comp_thms; stack_rawcallProof_state_rel_def] THEN RVEQ_TAC THEN
  (CASES_ON `i:(A)inst` THENL
    [ALL_TAC; ALL_TAC; CASES_ON `a:(A)asm_arith`; CASES_ON `a0:memop`; CASES_ON `a:fp`]) THEN
  FS (STACKPROPSAUX_word_exp_code :: STACKPROPSAUX_RC_DEFS) THEN
  GVS (CONJUNCTS stack_case_eq_thms) THEN GVS[LEFT_AND_EXISTS_THM] THEN
  SIMP[stack_state_component_equality; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
       EXISTS_BOOL_THM]);;

(* HOL4: comp_correct, by induction on the evaluation; one tactic per       *)
(* clause of stack_evaluate, in the order of its definition                 *)

let stack_rawcallProof_comp_correct = prove
 (`!p (s:(A,C,FFI)stack_state) t i r s1.
     stack_evaluate (p,s) = (r,s1) /\ ~(r = SOME stack_Error) /\
     stack_rawcallProof_state_rel i s t
     ==> (?ck t1 k1.
            stack_rawcallProof_state_rel i s1 t1 /\
            stack_evaluate (comp_top i p,
                            stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
            (r,stack_state_stack_space_fupd (K k1) t1) /\
            (~(r = SOME stack_TimeOut) /\ ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
             k1 = stack_state_stack_space t1)) /\
         (?ck t1 k1.
            stack_rawcallProof_state_rel i s1 t1 /\
            stack_evaluate (stack_rawcall_comp i p,
                            stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
            (r,stack_state_stack_space_fupd (K k1) t1) /\
            (~(r = SOME stack_TimeOut) /\ ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
             k1 = stack_state_stack_space t1))`,
  let simple = STACKPROPSAUX_RC_SIMPLE_TAC and src = STACKPROPSAUX_RC_SRC_TAC
  and zero = STACKPROPSAUX_RC_ZERO_TAC and empty = STACKPROPSAUX_empty_f
  and call = STACKPROPSAUX_RC_CALL_TAC and choose3 = STACKPROPSAUX_CHOOSE3
  and is_src = STACKPROPSAUX_is_src
  and st = `t:(A,C,FFI)stack_state` and wit = [`ck:num`; `t1:(A,C,FFI)stack_state`; `k1:num`]
  and wit' = [`ck':num`; `t1':(A,C,FFI)stack_state`; `k1':num`] in
  let sf_eq = REWRITE_CONV[stack_evaluate_def]
    `stack_evaluate (StackFree k:(A)stack_prog,s:(A,C,FFI)stack_state)`
  and call_eq = REWRITE_CONV[stack_evaluate_def; stack_find_code_def]
    `stack_evaluate (stack_Call NONE (INL dest) NONE:(A)stack_prog,s:(A,C,FFI)stack_state)` in
  (* Seq: first the default compilation Seq (comp i c1) (comp i c2) *)
  let seq_default =
    FIRST_X_ASSUM (MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def] o check is_src) THEN
    PAIRARG_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    RVEQ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPECL [st; `i:num spt`; `NONE:((A)stack_result)option`;
                                     `s1':(A,C,FFI)stack_state`]) THEN
      ASM_REWRITE_TAC[option_DISTINCT] THEN
      DISCH_THEN (choose3 "ck1" "t1" "k1" o CONJUNCT2) THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[with_stack_space]) THEN
      FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[] o SPEC `s1':(A,C,FFI)stack_state`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`t1:(A,C,FFI)stack_state`; `i:num spt`;
                                  `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN (choose3 "ck2" "t2" "k2" o CONJUNCT2) THEN
      MP_TAC (INST [`ck2:num`,`extra:num`]
        (ISPECL [`stack_rawcall_comp i (c1:(A)stack_prog)`;
                 `stack_state_clock_fupd (K (stack_state_clock t + ck1)) (t:(A,C,FFI)stack_state)`;
                 `NONE:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`]
                stack_evaluate_add_clock)) THEN
      FS[option_DISTINCT] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`ck1 + ck2`; `t2:(A,C,FFI)stack_state`; `k2:num`] THEN
      ONCE_REWRITE_TAC[stack_evaluate_def] THEN FS[ADD_ASSOC];
      FIRST_X_ASSUM (MP_TAC o SPECL [st; `i:num spt`; `r:((A)stack_result)option`;
                                     `s1:(A,C,FFI)stack_state`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN (choose3 "ck1" "t1" "k1" o CONJUNCT2) THEN
      MAP_EVERY EXISTS_TAC [`ck1:num`; `t1:(A,C,FFI)stack_state`; `k1:num`] THEN
      ONCE_REWRITE_TAC[stack_evaluate_def] THEN FS[]] in
  (* Seq (StackFree k) (Call NONE (INL dest) NONE), compiled to a RawCall *)
  let seq_rawcall =
    DISCH_TAC THEN
    ASM_CASES_TAC `stack_rawcall_comp i (stack_Seq c1 c2) =
      stack_Seq (stack_rawcall_comp i c1) (stack_rawcall_comp i (c2:(A)stack_prog))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP comp_seq_neq_IMP o CASE_REWRITE_RULE[] o
                   REWRITE_RULE[STACKPROPSAUX_rc_comp_thms] o check (is_neg o concl)) THEN
    RVEQ_TAC THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms; comp_seq_def; dest_case_def] THEN
    CASE_REWRITE_TAC[] THEN CASES_ON `lookup dest (i:num spt)` THEN CASE_REWRITE_TAC[] THENL
     [RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[STACKPROPSAUX_rc_comp_thms]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    src [stack_find_code_def] THEN IMP_RES_TAC STACKPROPSAUX_rel_get THENL
     [ALL_TAC; src []] THEN
    (* the code of dest starts with StackAlloc a *)
    IMP_RES_TAC STACKPROPSAUX_rel_ok THEN
    FIRST_ASSUM (MP_TAC o REWRITE_RULE[stack_rawcallProof_state_ok_def] o
                 check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                      "stack_rawcallProof_state_ok" with Failure _ -> false)) THEN
    DISCH_THEN (MP_TAC o SPECL [`dest:num`; `a:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN (X_CHOOSE_TAC `p:(A)stack_prog`) THEN
    IMP_RES_TAC STACKPROPSAUX_rel_lookup THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[comp_top_def; STACKPROPSAUX_rc_comp_thms]) THEN
    FIRST_X_ASSUM (CAKE_STRIP_ASSUME_TAC o CAKE_SIMP_RULE[sf_eq; COND_CASE_EQ] o
                   check (fun th -> is_src th && free_in `StackFree k:(A)stack_prog` (concl th))) THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
    SUBGOAL_THEN `~(LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                    stack_state_stack_space s + k - a)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THENL
     [(* the call times out at once *)
      FIRST_X_ASSUM (MP_TAC o check is_src) THEN REWRITE_TAC[call_eq] THEN SIMP[] THEN
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      EXISTS_TAC `stack_empty_env (stack_state_stack_space_fupd
        (K (stack_state_stack_space (s:(A,C,FFI)stack_state) + k)) (t:(A,C,FFI)stack_state))` THEN
      SIMP[STACKPROPSAUX_state_rel_upd] THEN REPEAT COND_CASES_TAC THEN
      FS[stack_evaluate_def; stack_dest_Seq_def; stack_empty_env_def;
         stack_state_component_equality];
      ALL_TAC] THEN
    (* the induction hypothesis for the call, after StackFree k *)
    SUBGOAL_THEN `stack_rawcallProof_state_rel i
       (stack_state_stack_space_fupd (K (stack_state_stack_space s + k)) (s:(A,C,FFI)stack_state))
       (stack_state_stack_space_fupd (K (stack_state_stack_space s + k)) (t:(A,C,FFI)stack_state))`
      ASSUME_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_state_rel_upd]; ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `stack_state_stack_space_fupd
      (K (stack_state_stack_space s + k)) (s:(A,C,FFI)stack_state)`) THEN
    ASM_REWRITE_TAC[sf_eq] THEN
    DISCH_THEN (MP_TAC o SPECL [`stack_state_stack_space_fupd
      (K (stack_state_stack_space (s:(A,C,FFI)stack_state) + k)) (t:(A,C,FFI)stack_state)`;
      `i:num spt`; `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (choose3 "ck" "t1" "k1") THEN
    STACKPROPSAUX_DROP_IHS_TAC THEN
    let is_h th = is_eq (concl th) && free_in `k1:num` (concl th) in
    let unf = FIRST_X_ASSUM (MP_TAC o check is_h) THEN
      FS[stack_evaluate_def; stack_find_code_def; stack_dest_Seq_def; stack_dec_clock_def;
         ARITH_RULE `~(m + n < n:num) /\ (m < a - k <=> m + k < a) /\
                     (m + n + 1) - 1 = m + n /\ (a < k ==> ~(m + k < a:num))`] in
    FIRST_X_ASSUM (K ALL_TAC o check (fun th -> is_src th && not (is_h th))) THEN
    FIRST_X_ASSUM (K ALL_TAC o check (is_exists o concl)) THEN
    ASM_CASES_TAC `a:num = k` THENL
     [MAP_EVERY EXISTS_TAC wit THEN unf THEN STACKPROPSAUX_SAME_RUN_TAC THEN REWRITE_TAC[];
      ASM_CASES_TAC `a:num < k` THENL
       [MAP_EVERY EXISTS_TAC wit THEN unf THEN STACKPROPSAUX_SAME_RUN_TAC THEN REWRITE_TAC[];
        ASM_CASES_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state) + k < a` THENL
         [MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`;
                                `stack_state_stack_space (s:(A,C,FFI)stack_state)`] THEN
          unf THEN STRIP_TAC THEN GVS[stack_empty_env_def; stack_state_component_equality];
          MAP_EVERY EXISTS_TAC [`ck + 1`; `t1:(A,C,FFI)stack_state`; `k1:num`] THEN unf THEN
          STACKPROPSAUX_SAME_RUN_TAC THEN REWRITE_TAC[]]]] in
  (* Loop: the body once, then exit or continue *)
  let loop_cont =
    SUBGOAL_THEN `~(res = SOME (stack_TimeOut:(A)stack_result)) /\
                  ~(res = SOME (stackSem_Halt (wl_Word (word 2)):(A)stack_result))`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th) THENL
     [FIRST_ASSUM (DISJ_CASES_THEN SUBST1_TAC o MATCH_MP cont_loop_IMP) THEN SIMP[];
      ALL_TAC] THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[with_stack_space]) THEN
    MP_TAC (MATCH_MP STACKPROPSAUX_rel_get
      (ASSUME `stack_rawcallProof_state_rel i s1' (t1':(A,C,FFI)stack_state)`)) THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `stack_state_clock (s1':(A,C,FFI)stack_state) = 0` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`ck':num`; `stack_empty_env (t1':(A,C,FFI)stack_state)`;
                            `stack_state_stack_space (t1':(A,C,FFI)stack_state)`] THEN
      IMP_RES_TAC STACKPROPSAUX_state_rel_upd THEN
      FS[stack_empty_env_def; stack_state_component_equality];
      FIRST_X_ASSUM (MP_TAC o check (fun th -> is_imp (concl th) &&
                                               is_forall (rand (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`stack_dec_clock (t1':(A,C,FFI)stack_state)`; `i:num spt`;
                                  `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[STACKPROPSAUX_state_rel_upd]; ALL_TAC] THEN
      DISCH_THEN (choose3 "ck2" "t2" "k2" o CONJUNCT2) THEN
      MP_TAC (INST [`ck2:num`,`extra:num`]
        (ISPECL [`stack_rawcall_comp i (c1:(A)stack_prog)`;
                 `stack_state_clock_fupd (K (stack_state_clock t + ck')) (t:(A,C,FFI)stack_state)`;
                 `res:((A)stack_result)option`; `t1':(A,C,FFI)stack_state`]
                stack_evaluate_add_clock)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`ck' + ck2`; `t2:(A,C,FFI)stack_state`; `k2:num`] THEN
      ONCE_REWRITE_TAC[stack_evaluate_def] THEN
      FS[ADD_ASSOC; stack_STOP_def; STACKPROPSAUX_rc_comp_thms; STACKPROPSAUX_dec_clock_add;
         STACKPROPSAUX_dec_clock_clock]]
  and loop_exit =
    STRIP_TAC THEN RVEQ_TAC THEN MAP_EVERY EXISTS_TAC wit' THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THEN DISCH_TAC THEN RVEQ_TAC THEN FS[] in
  (* Call (SOME ...): the callee, then the return or exception handler *)
  let is_callee th = is_src th && free_in `comp_top (i':num spt) (a:(A)stack_prog)` (concl th) in
  let callee =
    STACKPROPSAUX_RC_IH_TAC THEN
    SUBGOAL_THEN `stack_rawcallProof_state_rel i'
       (stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s))
       (stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) (t:(A,C,FFI)stack_state)))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC STACKPROPSAUX_rel_dec_set THEN MATCH_MP_TAC STACKPROPSAUX_state_rel_mono THEN
      MAP_EVERY EXISTS_TAC [`i:num spt`; `s:(A,C,FFI)stack_state`] THEN
      ASM_REWRITE_TAC[subspt_refl];
      ALL_TAC] THEN
    FIRST_X_ASSUM DRULE THEN DISCH_THEN (choose3 "ck" "t1" "k1" o CONJUNCT1) THEN
    IMP_RES_TAC stack_evaluate_mono THEN IMP_RES_TAC STACKPROPSAUX_rel_ok
  and mono_fin =
    MATCH_MP_TAC STACKPROPSAUX_state_rel_mono THEN
    MAP_EVERY EXISTS_TAC [`i':num spt`; `s:(A,C,FFI)stack_state`] THEN
    FS[stack_dec_clock_def; stack_set_var_def]
  and call_unf =
    FIRST_X_ASSUM (MP_TAC o check is_callee) THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
    FS[stack_find_code_def] THEN STACKPROPSAUX_SAME_RUN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] in
  let call_direct = callee THEN MAP_EVERY EXISTS_TAC wit THEN call_unf THEN mono_fin
  and call_cont =
    callee THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[with_stack_space]) THEN
    SUBGOAL_THEN `stack_rawcallProof_state_rel i (y:(A,C,FFI)stack_state) t1` ASSUME_TAC THENL
     [mono_fin; ALL_TAC] THEN
    FIRST_X_ASSUM DRULE THEN DISCH_THEN (choose3 "ck2" "t2" "k2" o CONJUNCT2) THEN
    FIRST_ASSUM (MP_TAC o SPEC `ck2:num` o
                 MATCH_MP_CURRIED stack_evaluate_add_clock o check is_callee) THEN
    SIMP[] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck + ck2`; `t2:(A,C,FFI)stack_state`; `k2:num`] THEN call_unf
  and call_none = FIRST [zero empty THEN NO_TAC; call wit] in
  STACKPROPSAUX_EVAL_IND_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[comp_top_def] THEN CASE_REWRITE_TAC[] THENL
   [(* Skip *) simple;
    (* Halt *) simple;
    (* Alloc *) simple;
    (* StoreConsts *)
    simple THEN CASES_ON `stack_state_use_alloc (s:(A,C,FFI)stack_state)` THEN
    CASES_ON `stub_opt:num option` THEN
    FS[stack_unset_var_def; check_store_consts_opt_def; I_THM] THEN
    RES_TAC THEN FS[STACKPROPSAUX_rc_comp_thms; comp_top_def];
    (* Inst *)
    ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC evaluate_comp_Inst THEN ASM_REWRITE_TAC[];
    (* Get *) simple;
    (* Set *) simple;
    (* OpCurrHeap *) simple;
    (* Tick *) simple;
    (* Seq *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [seq_default; seq_rawcall];
    (* Return *) simple;
    (* Raise *) simple;
    (* Break *) simple;
    (* Continue *) simple;
    (* If *)
    REPEAT STRIP_TAC THEN FS[STACKPROPSAUX_rc_comp_thms] THEN
    FIRST_X_ASSUM (MP_TAC o check is_src) THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
    SIMP(CONJUNCTS stack_case_eq_thms) THEN STRIP_TAC THEN RES_TAC THEN
    MAP_EVERY EXISTS_TAC wit' THEN STACKPROPSAUX_DROP_IHS_TAC THEN
    IMP_RES_TAC STACKPROPSAUX_rel_get THEN FS[EXISTS_BOOL_THM];
    (* Loop *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM (MP_TAC o check is_src) THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
    PAIRARG_TAC THEN ASM_CASES_TAC `res = SOME (stack_Error:(A)stack_result)` THEN FS[] THEN
    RES_TAC THEN CASES_ON `stack_cont_loop (res:((A)stack_result)option)` THEN FS[] THENL
     [loop_cont; loop_exit];
    (* JumpLower *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
    src [stack_find_code_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_find_code_def]) THEN
    IMP_RES_TAC STACKPROPSAUX_rel_get THEN IMP_RES_TAC STACKPROPSAUX_rel_lookup THEN
    FIRST [zero I THEN NO_TAC; zero empty THEN NO_TAC; call wit];
    (* RawCall *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
    src [] THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[STACKPROPSAUX_dest_Seq_SOME]) THEN RVEQ_TAC THEN
    IMP_RES_TAC STACKPROPSAUX_rel_get THEN IMP_RES_TAC STACKPROPSAUX_rel_lookup THEN
    RULE_ASSUM_TAC(REWRITE_RULE[comp_top_def; STACKPROPSAUX_rc_comp_thms]) THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    FIRST [zero empty THEN NO_TAC; call wit'];
    (* Call *)
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def] o check is_src) THEN
    CASES_ON `ret:((A)stack_prog#num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
    REPEAT PAIRARG_TAC THEN
    DISCH_THEN(CAKE_STRIP_ASSUME_TAC o CAKE_SIMP_RULE (CONJUNCTS stack_case_eq_thms)) THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
    REWRITE_TAC[STACKPROPSAUX_comp_call_some] THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
    CASE_REWRITE_TAC[] THEN IMP_RES_TAC STACKPROPSAUX_rel_get THEN
    IMP_RES_TAC STACKPROPSAUX_rel_find_code THENL
     [(* tail call: timeout, run; call: timeout *) call_none; call_none; call_none;
      (* Result *) call_cont; (* Exception, no handler *) call_direct;
      (* Exception, handler *) call_cont;
      (* Halt, TimeOut, FinalFFI *) call_direct; call_direct; call_direct];
    (* Install *)
    simple THEN SIMP[lookup_union; STACKPROPSAUX_state_ok_union] THEN REPEAT GEN_TAC THEN
    (CASES_ON `lookup n (stack_state_code (s:(A,C,FFI)stack_state))` THEN SIMP[] THEN
     STRIP_TAC THENL
      [SUBGOAL_THEN `lookup n (c:((A)stack_prog)spt) = NONE` ASSUME_TAC THENL
        [ASM_REWRITE_TAC[lookup_NONE_domain] THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
         ALL_TAC] THEN
       EXISTS_TAC `LN:num spt` THEN SIMP[comp_LN; stack_rawcallProof_state_ok_def; lookup_def];
       RES_TAC THEN EXISTS_TAC `i':num spt` THEN SIMP[STACKPROPSAUX_state_ok_union]]);
    (* ShMemOp *)
    EXISTS_TAC `0` THEN FS[STACKPROPSAUX_rc_comp_thms; stack_rawcallProof_state_rel_def] THEN
    RVEQ_TAC THEN CASES_ON `op:memop` THEN
    FS ([STACKPROPSAUX_word_exp_code; sh_mem_op_def; stack_sh_mem_store_def;
         stack_sh_mem_load_def; stack_sh_mem_store_byte_def; stack_sh_mem_store16_def;
         stack_sh_mem_store32_def; stack_sh_mem_load_byte_def; stack_sh_mem_load16_def;
         stack_sh_mem_load32_def] @ STACKPROPSAUX_RC_DEFS) THEN
    GVS (CONJUNCTS stack_case_eq_thms) THEN GVS[LEFT_AND_EXISTS_THM] THEN
    SIMP[stack_state_component_equality; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
         EXISTS_BOOL_THM];
    (* CodeBufferWrite *) simple;
    (* DataBufferWrite *) simple;
    (* FFI *) simple;
    (* LocValue *)
    simple THEN RES_TAC THEN ASM_MESON_TAC[stack_rawcallProof_get_labels_comp];
    (* StackAlloc *) simple;
    (* StackFree *) simple;
    (* StackLoad *) simple;
    (* StackLoadAny *) simple;
    (* StackStore *) simple;
    (* StackStoreAny *) simple;
    (* StackGetSize *) simple;
    (* StackSetSize *) simple;
    (* BitmapLoad *) simple]);;

(* HOL4: domain_fromAList_compile                                           *)

let domain_fromAList_compile = prove
 (`domain (fromAList (stack_rawcall_compile code)) =
   domain (fromAList (code:(num#(A)stack_prog)list))`,
  REWRITE_TAC[domain_fromAList; stack_rawcall_compile_def; LET_DEF; LET_END_DEF;
              MAP_MAP_o] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let lookup_collect_info = prove
 (CASE_TERM
  `!xs n (rest:num spt).
     ALL_DISTINCT (MAP FST (xs:(num#(A)stack_prog)list)) ==>
     lookup n (collect_info xs rest) =
     match ALOOKUP xs n with
       NONE -> lookup n rest
     | SOME body -> lookup n (collect_info [(n,body)] rest)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[collect_info_def; ALOOKUP_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; MAP; ALL_DISTINCT; FST; SND; collect_info_def] THEN
  MAP_EVERY X_GEN_TAC [`p1:num`; `p2:(A)stack_prog`; `n:num`; `rest:num spt`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM `!n (rest:num spt).
      lookup n (collect_info (t:(num#(A)stack_prog)list) rest) =
      match ALOOKUP t n with
        NONE -> lookup n rest
      | SOME body -> lookup n (collect_info [(n,body)] rest)`)
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[collect_info_def] THEN
  SUBGOAL_THEN `ALOOKUP (t:(num#(A)stack_prog)list) p1 = NONE` ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[cases "option"; ALOOKUP_MEM]
      `(!v. ~MEM (k,v) (l:(num#(A)stack_prog)list)) ==> ALOOKUP l k = NONE`) THEN
    GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~MEM p1 (MAP FST (t:(num#(A)stack_prog)list))` THEN
    REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(p1,v):num#(A)stack_prog` THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  ASM_CASES_TAC `p1:num = n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `ALOOKUP (t:(num#(A)stack_prog)list) n` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `seq_stack_alloc (p2:(A)stack_prog)` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  (fun (asl,w as g) ->
     let tm = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "seq_stack_alloc"
                                  with Failure _ -> false) w in
     (CASES_ON tm THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[lookup_insert]) g));;

let STACKPROPSAUX_seq_stack_alloc_cases = prove
 (`!p:(A)stack_prog. seq_stack_alloc p = NONE \/
      ?k q. p = stack_Seq (StackAlloc k) q /\ seq_stack_alloc p = SOME k`,
  GEN_TAC THEN REWRITE_TAC[seq_stack_alloc_def] THEN EVERY_CASE_TAC THEN SIMP[] THEN
  MESON_TAC[]);;

let state_ok_collect_info = prove
 (`ALL_DISTINCT (MAP FST (code:(num#(A)stack_prog)list)) ==>
   stack_rawcallProof_state_ok (collect_info code LN) (fromAList code)`,
  DISCH_TAC THEN REWRITE_TAC[stack_rawcallProof_state_ok_def] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:num`] THEN
  ASM_SIMP_TAC[lookup_collect_info; lookup_fromAList] THEN
  CASES_ON `ALOOKUP (code:(num#(A)stack_prog)list) n` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[lookup_def; option_DISTINCT; collect_info_def] THEN
  (fun (asl,w as g) ->
     let tm = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "seq_stack_alloc"
                                  with Failure _ -> false) w in
     (MP_TAC(ISPEC (rand tm) STACKPROPSAUX_seq_stack_alloc_cases) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[lookup_insert; lookup_def; option_DISTINCT; option_INJ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]) g));;

(* the observational semantics under a simulation with extra clock (for    *)
(* compile_semantics): the runs of a state at two clocks that do not time *)
(* out agree, and a simulation of the runs of s by the runs of t gives     *)
(* the same semantics                                                        *)

let STACKPROPSAUX_eval_det = prove
 (`!p (x:(A,C,FFI)stack_state) k1 k2 r1 r2 x1 x2.
     stack_evaluate (p,stack_state_clock_fupd (K k1) x) = (r1,x1) /\
     stack_evaluate (p,stack_state_clock_fupd (K k2) x) = (r2,x2) /\
     ~(r1 = SOME stack_TimeOut) /\ ~(r2 = SOME stack_TimeOut)
     ==> r1 = r2 /\ stack_state_ffi x1 = stack_state_ffi x2`,
  SUBGOAL_THEN
   `!p (x:(A,C,FFI)stack_state) k1 d r1 r2 x1 x2.
     stack_evaluate (p,stack_state_clock_fupd (K k1) x) = (r1,x1) /\
     stack_evaluate (p,stack_state_clock_fupd (K (k1 + d)) x) = (r2,x2) /\
     ~(r1 = SOME stack_TimeOut)
     ==> r1 = r2 /\ stack_state_ffi x1 = stack_state_ffi x2`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(INST [`d:num`,`extra:num`]
      (ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (x:(A,C,FFI)stack_state)`;
               `r1:((A)stack_result)option`; `x1:(A,C,FFI)stack_state`]
              stack_evaluate_add_clock)) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ASM_MESON_TAC[]);;

let STACKPROPSAUX_eval_mono_clock = prove
 (`!p (x:(A,C,FFI)stack_state) k1 k2 r1 x1.
     stack_evaluate (p,stack_state_clock_fupd (K k1) x) = (r1,x1) /\
     ~(r1 = SOME stack_TimeOut) /\ k1 <= k2
     ==> FST (stack_evaluate (p,stack_state_clock_fupd (K k2) x)) = r1 /\
         stack_state_ffi (SND (stack_evaluate (p,stack_state_clock_fupd (K k2) x))) =
         stack_state_ffi x1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(INST [`d:num`,`extra:num`]
    (ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (x:(A,C,FFI)stack_state)`;
             `r1:((A)stack_result)option`; `x1:(A,C,FFI)stack_state`]
            stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let STACKPROPSAUX_sem_ev (x:term) (k:term) =
  vsubst [x,`x:(A,C,FFI)stack_state`; k,`k:num`]
   `stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                    stack_state_clock_fupd (K k) (x:(A,C,FFI)stack_state))`;;

(* the pair of a run: names r, s1 for stack_evaluate (P,clock_fupd (K k) x) *)
let STACKPROPSAUX_SEM_RUN_TAC (x:term) (k:term) (r:term) (x1:term) : tactic =
  MP_TAC(ISPEC (STACKPROPSAUX_sem_ev x k) PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [r; x1] THEN DISCH_TAC;;

let STACKPROPSAUX_sem_oks (x:term) =
  let ev = mk_comb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`,
                   STACKPROPSAUX_sem_ev x `k:num`) in
  mk_forall(`k:num`,
   list_mk_disj
    [mk_eq(ev,`SOME (stack_TimeOut:(A)stack_result)`);
     mk_eq(ev,`SOME (stack_Result (wl_Loc 1 0):(A)stack_result)`);
     mk_exists(`w:A word`,mk_eq(ev,`SOME (stackSem_Halt (wl_Word (w:A word)))`));
     mk_exists(`f:final_event`,mk_eq(ev,`SOME (stack_FinalFFI f:(A)stack_result)`))]);;

(* the semantics of t is the one of s when every run of s that does not   *)
(* fail is simulated by a run of t with extra clock, with the same ffi      *)

let STACKPROPSAUX_semantics_sim = prove
 (`!start (s:(A,C,FFI)stack_state) (t:(A,C,FFI)stack_state).
     (!k r s1.
        stack_evaluate (stack_Call NONE (INL start) NONE,stack_state_clock_fupd (K k) s) =
        (r,s1) /\ ~(r = SOME stack_Error)
        ==> ?ck t1.
              stack_evaluate (stack_Call NONE (INL start) NONE,
                              stack_state_clock_fupd (K (k + ck)) t) = (r,t1) /\
              stack_state_ffi t1 = stack_state_ffi s1) /\
     ~(stack_semantics start s = Fail)
     ==> stack_semantics start t = stack_semantics start s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                             stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))) =
          SOME stack_TimeOut \/
        FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                             stack_state_clock_fupd (K k) s)) =
          SOME (stack_Result (wl_Loc 1 0)) \/
        (?w. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                  stack_state_clock_fupd (K k) s)) =
               SOME (stackSem_Halt (wl_Word w))) \/
        (?f. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                  stack_state_clock_fupd (K k) s)) =
               SOME (stack_FinalFFI f))`
   (LABEL_TAC "oks") THENL
   [UNDISCH_TAC `~(stack_semantics start (s:(A,C,FFI)stack_state) = Fail)` THEN
    REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    (mk_forall(`k:num`, mk_imp(mk_eq(mk_comb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`, STACKPROPSAUX_sem_ev `s:(A,C,FFI)stack_state` `k:num`), `SOME (stack_TimeOut:(A)stack_result)`),
                               mk_eq(mk_comb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`, STACKPROPSAUX_sem_ev `t:(A,C,FFI)stack_state` `k:num`), `SOME (stack_TimeOut:(A)stack_result)`))))
    (LABEL_TAC "tmo") THENL
   [GEN_TAC THEN
    STACKPROPSAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
      `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `SOME (stack_TimeOut:(A)stack_result)`;
                                    `s1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"]; ALL_TAC] THEN
    STRIP_TAC THEN
    STACKPROPSAUX_SEM_RUN_TAC `t:(A,C,FFI)stack_state` `k:num`
      `r2:((A)stack_result)option` `t2:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                   `t:(A,C,FFI)stack_state`; `k:num`; `k + ck:num`;
                   `r2:((A)stack_result)option`; `t2:(A,C,FFI)stack_state`]
                  STACKPROPSAUX_eval_mono_clock) THEN
    ASM_REWRITE_TAC[LE_ADD; FST];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!k r (t1:(A,C,FFI)stack_state).
       stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                       stack_state_clock_fupd (K k) t) = (r,t1) /\
       ~(r = SOME stack_TimeOut)
       ==> ?s1. stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
                (r,s1) /\ stack_state_ffi s1 = stack_state_ffi t1`
    (LABEL_TAC "back") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    STACKPROPSAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
      `r0:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
    SUBGOAL_THEN `~(r0 = SOME (stack_TimeOut:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "tmo" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[FST]; ASM_REWRITE_TAC[FST]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(r0 = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
     [USE_THEN "oks" (MP_TAC o REWRITE_RULE[FST; ASSUME (mk_eq(STACKPROPSAUX_sem_ev
         `s:(A,C,FFI)stack_state` `k:num`,
         `r0:((A)stack_result)option,(s1:(A,C,FFI)stack_state)`))] o SPEC `k:num`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"];
      ALL_TAC] THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `r0:((A)stack_result)option`;
                                    `s1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                   `t:(A,C,FFI)stack_state`; `k:num`; `k + ck:num`;
                   `r:((A)stack_result)option`; `r0:((A)stack_result)option`;
                   `t1:(A,C,FFI)stack_state`; `t1':(A,C,FFI)stack_state`]
                  STACKPROPSAUX_eval_det) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `s1:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (STACKPROPSAUX_sem_oks `t:(A,C,FFI)stack_state`) (LABEL_TAC "okt") THENL
   [GEN_TAC THEN
    STACKPROPSAUX_SEM_RUN_TAC `t:(A,C,FFI)stack_state` `k:num`
      `r:((A)stack_result)option` `t1:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[FST] THEN
    ASM_CASES_TAC `r = SOME (stack_TimeOut:(A)stack_result)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "back" (MP_TAC o SPECL [`k:num`; `r:((A)stack_result)option`;
                                     `t1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    USE_THEN "oks" (MP_TAC o REWRITE_RULE[FST; ASSUME (mk_eq(STACKPROPSAUX_sem_ev
         `s:(A,C,FFI)stack_state` `k:num`,
         `r:((A)stack_result)option,(s1:(A,C,FFI)stack_state)`))] o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
     USE_THEN "okt" (fun th -> MESON_TAC[th]);
     ALL_TAC] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
     USE_THEN "oks" (fun th -> MESON_TAC[th]);
     ALL_TAC] THEN
  MATCH_MP_TAC BASICAUX_option_CASE_cong THEN CONJ_TAC THENL
  [AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(r = (stack_TimeOut:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ALL_TAC] THEN
    USE_THEN "back" (MP_TAC o SPECL [`k:num`; `SOME (r:(A)stack_result)`;
                                     `t':(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[option_INJ]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`; `r:(A)stack_result`;
                          `outcome:outcome`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(r = (stack_Error:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ALL_TAC] THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `SOME (r:(A)stack_result)`;
                                    `t':(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[option_INJ]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`k + ck:num`; `t1:(A,C,FFI)stack_state`; `r:(A)stack_result`;
                          `outcome:outcome`] THEN
    ASM_REWRITE_TAC[]];
   REWRITE_TAC[BASICAUX_some_NONE] THEN DISCH_TAC THEN AP_TERM_TAC THEN
   SUBGOAL_THEN (mk_forall(`k:num`, mk_eq(mk_comb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`, STACKPROPSAUX_sem_ev `s:(A,C,FFI)stack_state` `k:num`), `SOME (stack_TimeOut:(A)stack_result)`)))
     (LABEL_TAC "div") THENL
    [GEN_TAC THEN
     STACKPROPSAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
       `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
     ASM_REWRITE_TAC[FST] THEN
     USE_THEN "oks" (MP_TAC o REWRITE_RULE[FST; ASSUME (mk_eq(STACKPROPSAUX_sem_ev
          `s:(A,C,FFI)stack_state` `k:num`,
          `r:((A)stack_result)option,(s1:(A,C,FFI)stack_state)`))] o SPEC `k:num`) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
       is_forall c && is_neg (snd(dest_forall c)))) THEN
     FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC[NOT_FORALL_THM; option_INJ; distinctness "stack_result"] THENL
      [EXISTS_TAC `Terminate Success (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))` THEN
       MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                             `stack_Result (wl_Loc 1 0):(A)stack_result`; `Success`];
       EXISTS_TAC `Terminate (if wl_Word (w:A word) = wl_Word (word 0) then Success
                              else Resource_limit_hit)
                     (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))` THEN
       MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                             `stackSem_Halt (wl_Word (w:A word)):(A)stack_result`;
                             `if wl_Word (w:A word) = wl_Word (word 0) then Success
                              else Resource_limit_hit`];
       EXISTS_TAC `Terminate (FFI_outcome f)
                     (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))` THEN
       MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                             `stack_FinalFFI f:(A)stack_result`; `FFI_outcome f`]] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REWRITE_TAC[STACKPROPSAUX_io_chain] THEN
   REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
   CONJ_TAC THEN X_GEN_TAC `k:num` THEN
   STACKPROPSAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
     `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
   USE_THEN "div" (MP_TAC o REWRITE_RULE[FST; ASSUME (mk_eq(STACKPROPSAUX_sem_ev
          `s:(A,C,FFI)stack_state` `k:num`,
          `r:((A)stack_result)option,(s1:(A,C,FFI)stack_state)`))] o SPEC `k:num`) THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `SOME (stack_TimeOut:(A)stack_result)`;
                                   `s1:(A,C,FFI)stack_state`]) THEN
   (ANTS_TAC THENL
     [ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"]; ALL_TAC]) THEN
   STRIP_TAC THENL
    [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
     MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                    `t:(A,C,FFI)stack_state`; `k:num`; `k + ck:num`] STACKPROPSAUX_io_mono) THEN
     ASM_REWRITE_TAC[LE_ADD];
     EXISTS_TAC `k + ck:num` THEN
     ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL]]]);;

(* HOL4: compile_semantics                                                  *)

let STACKPROPSAUX_rel_init = prove
 (`ALL_DISTINCT (MAP FST (code:(num#(A)stack_prog)list)) /\
   stack_state_code s = fromAList code
   ==> stack_rawcallProof_state_rel (collect_info code LN) (s:(A,C,FFI)stack_state)
         (stack_state_code_fupd (K (fromAList (stack_rawcall_compile code))) s)`,
  STRIP_TAC THEN REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN
  EXISTS_TAC `fromAList (stack_rawcall_compile (code:(num#(A)stack_prog)list))` THEN
  ASM_SIMP_TAC[domain_fromAList_compile; state_ok_collect_info] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `b:(A)stack_prog`] THEN DISCH_TAC THEN
  EXISTS_TAC `collect_info (code:(num#(A)stack_prog)list) LN` THEN
  ASM_SIMP_TAC[state_ok_collect_info] THEN
  UNDISCH_TAC `lookup n (fromAList (code:(num#(A)stack_prog)list)) = SOME b` THEN
  REWRITE_TAC[lookup_fromAList; stack_rawcall_compile_def; LET_DEF; LET_END_DEF;
              ALOOKUP_MAP; o_THM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPTION_MAP_DEF]);;

let STACKPROPSAUX_rel_ffi = prove
 (`!i s (t:(A,C,FFI)stack_state).
     stack_rawcallProof_state_rel i s t ==> stack_state_ffi t = stack_state_ffi s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP STACKPROPSAUX_rel_code_fupd) THEN SIMP[]);;

let stack_rawcallProof_compile_semantics = prove
 (`ALL_DISTINCT (MAP FST (code:(num#(A)stack_prog)list)) /\ stack_state_use_stack s /\
   stack_state_code s = fromAList code /\ ~(stack_semantics start s = Fail)
   ==> stack_semantics start
         (stack_state_code_fupd (K (fromAList (stack_rawcall_compile code)))
            (s:(A,C,FFI)stack_state)) =
       stack_semantics start s`,
  STRIP_TAC THEN MATCH_MP_TAC STACKPROPSAUX_semantics_sim THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP STACKPROPSAUX_rel_init (CONJ
    (ASSUME `ALL_DISTINCT (MAP FST (code:(num#(A)stack_prog)list))`)
    (ASSUME `stack_state_code (s:(A,C,FFI)stack_state) = fromAList code`))) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
             MATCH_MP STACKPROPSAUX_state_rel_upd) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                 `stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)`;
                 `stack_state_clock_fupd (K k)
                    (stack_state_code_fupd (K (fromAList (stack_rawcall_compile code)))
                      (s:(A,C,FFI)stack_state))`;
                 `collect_info (code:(num#(A)stack_prog)list) LN`;
                 `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]
                stack_rawcallProof_comp_correct) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck:num`;
    `stack_state_stack_space_fupd (K k1) (t1:(A,C,FFI)stack_state)`] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  MATCH_MP_TAC STACKPROPSAUX_rel_ffi THEN
  EXISTS_TAC `collect_info (code:(num#(A)stack_prog)list) LN` THEN ASM_REWRITE_TAC[]);;

(* comp keeps the syntactic properties (STACKPROPSAUX_RC_SYNTAX_TAC above) *)

let extract_labels_comp = prove
 (`!i (p:(A)stack_prog).
     stack_extract_labels (stack_rawcall_comp i p) = stack_extract_labels p /\
     stack_extract_labels (comp_top i p) = stack_extract_labels p`,
  STACKPROPSAUX_RC_SYNTAX_TAC [stack_extract_labels_def]);;

let stack_asm_name_comp = prove
 (`!i (p:(A)stack_prog).
     ((stack_asm_name c (stack_rawcall_comp i p) <=> stack_asm_name c p) /\
      (stack_asm_name c (comp_top i p) <=> stack_asm_name c p)) /\
     ((stack_asm_remove c (stack_rawcall_comp i p) <=> stack_asm_remove c p) /\
      (stack_asm_remove c (comp_top i p) <=> stack_asm_remove c p))`,
  STACKPROPSAUX_RC_SYNTAX_TAC [stack_asm_name_def; stack_asm_remove_def]);;

(* HOL4: EVERY is ALL                                                       *)

let STACKPROPSAUX_compile_ALL_TAC (th:thm) : tactic =
  REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF; MAP_MAP_o; ALL_MAP] THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[th];;

let stack_rawcallProof_stack_alloc_stack_asm_convs = prove
 (`(ALL (\(n,p). stack_asm_name c p) (stack_rawcall_compile prog) <=>
    ALL (\(n,p:(A)stack_prog). stack_asm_name c p) prog) /\
   (ALL (\(n,p). stack_asm_remove c p) (stack_rawcall_compile prog) <=>
    ALL (\(n,p:(A)stack_prog). stack_asm_remove c p) prog)`,
  STACKPROPSAUX_compile_ALL_TAC stack_asm_name_comp);;

let reg_bound_comp = prove
 (`!i (p:(A)stack_prog).
     (reg_bound (stack_rawcall_comp i p) s <=> reg_bound p s) /\
     (reg_bound (comp_top i p) s <=> reg_bound p s)`,
  STACKPROPSAUX_RC_SYNTAX_TAC [reg_bound_def]);;

let stack_rawcall_reg_bound = prove
 (`ALL (\p. reg_bound p sp) (MAP SND (stack_rawcall_compile prog1)) <=>
   ALL (\p. reg_bound p sp) (MAP SND (prog1:(num#(A)stack_prog)list))`,
  STACKPROPSAUX_compile_ALL_TAC reg_bound_comp);;

let call_args_comp = prove
 (`!i (p:(A)stack_prog).
     (call_args (stack_rawcall_comp i p) r1 r2 r3 r4 r5 <=> call_args p r1 r2 r3 r4 r5) /\
     (call_args (comp_top i p) r1 r2 r3 r4 r5 <=> call_args p r1 r2 r3 r4 r5)`,
  STACKPROPSAUX_RC_SYNTAX_TAC [call_args_def]);;

let stack_rawcallProof_stack_alloc_call_args = prove
 (`ALL (\p. call_args p 1 2 3 4 0) (MAP SND (stack_rawcall_compile prog1)) <=>
   ALL (\p. call_args p 1 2 3 4 0) (MAP SND (prog1:(num#(A)stack_prog)list))`,
  STACKPROPSAUX_compile_ALL_TAC call_args_comp);;

let stack_rawcallProof_MAP_FST_compile = prove
 (`!code:(num#(A)stack_prog)list.
     MAP FST (stack_rawcall_compile code) = MAP FST code`,
  GEN_TAC THEN
  REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF; MAP_MAP_o] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let call_arg_comp = prove
 (`!i (p:(A)stack_prog).
     (alloc_arg (stack_rawcall_comp i p) <=> alloc_arg p) /\
     (alloc_arg (comp_top i p) <=> alloc_arg p)`,
  STACKPROPSAUX_RC_SYNTAX_TAC [alloc_arg_def]);;

let stack_get_handler_labels_comp = prove
 (`!i (p:(A)stack_prog) k.
     stack_get_handler_labels k (stack_rawcall_comp i p) = stack_get_handler_labels k p /\
     stack_get_handler_labels k (comp_top i p) = stack_get_handler_labels k p`,
  STACKPROPSAUX_RC_SYNTAX_TAC [stack_get_handler_labels_def]);;


