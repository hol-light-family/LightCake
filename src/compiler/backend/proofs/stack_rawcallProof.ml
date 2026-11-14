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

(* close a goal whose assumptions contain some p and ~p *)

let STACKPROPSAUX_RC_CONTR_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  try let th' = find (fun th' -> is_neg (concl th') &&
                        exists (fun th -> concl th = dest_neg (concl th')) ths) ths in
      let th = find (fun th -> concl th = dest_neg (concl th')) ths in
      CONTR_TAC (MP (NOT_ELIM th') th) g
  with Failure _ -> ALL_TAC g;;

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
  EVERY_CASE_TAC THEN REWRITE_TAC[] THEN MESON_TAC[]);;

let stack_rawcallProof_get_labels_comp = prove
 (`!i (e:(A)stack_prog).
     stack_get_labels (stack_rawcall_comp i e) = stack_get_labels e /\
     stack_get_labels (comp_top i e) = stack_get_labels e`,
  MATCH_MP_TAC stack_rawcall_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
  TRY (REWRITE_TAC[comp_seq_def; dest_case_def]) THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SIMP[stack_get_labels_def]);;

(* stack_inst commutes with any function on states that keeps the fields   *)
(* it reads and commutes with the updates it makes                          *)

let STACKPROPSAUX_inst_frame = prove
 (`!(g:(A,C,FFI)stack_state->(A,C,FFI)stack_state).
     (!s. stack_state_regs (g s) = stack_state_regs s /\
          stack_state_fp_regs (g s) = stack_state_fp_regs s /\
          stack_state_store (g s) = stack_state_store s /\
          stack_state_memory (g s) = stack_state_memory s /\
          stack_state_mdomain (g s) = stack_state_mdomain s /\
          stack_state_be (g s) = stack_state_be s) /\
     (!s x y. stack_set_var x y (g s) = g (stack_set_var x y s)) /\
     (!s x y. stack_set_fp_var x y (g s) = g (stack_set_fp_var x y s)) /\
     (!s m. stack_state_memory_fupd (K m) (g s) = g (stack_state_memory_fupd (K m) s))
     ==> !i s. stack_inst i (g s) = OPTION_MAP g (stack_inst i s)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!s r. stack_get_var r ((g:(A,C,FFI)stack_state->(A,C,FFI)stack_state) s) =
           stack_get_var r (s:(A,C,FFI)stack_state)) /\
    (!s xs. stack_get_vars xs (g s) = stack_get_vars xs (s:(A,C,FFI)stack_state)) /\
    (!s r. stack_get_fp_var r (g s) = stack_get_fp_var r (s:(A,C,FFI)stack_state)) /\
    (!s e. stack_word_exp (g s) e = stack_word_exp (s:(A,C,FFI)stack_state) e) /\
    (!s a. stack_mem_load a (g s) = stack_mem_load a (s:(A,C,FFI)stack_state)) /\
    (!s a w. stack_mem_store a w (g s) =
             OPTION_MAP g (stack_mem_store a w (s:(A,C,FFI)stack_state))) /\
    (!s x e. stack_assign x e (g s) =
             OPTION_MAP g (stack_assign x e (s:(A,C,FFI)stack_state)))`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[stack_get_var_def];
      GEN_TAC THEN LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC[stack_get_vars_def; stack_get_var_def];
      ASM_REWRITE_TAC[stack_get_fp_var_def];
      REPEAT GEN_TAC THEN MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[stack_mem_load_def];
      REWRITE_TAC[stack_mem_store_def] THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF];
      REPEAT GEN_TAC THEN REWRITE_TAC[stack_assign_def] THEN
      SUBGOAL_THEN `stack_word_exp ((g:(A,C,FFI)stack_state->(A,C,FFI)stack_state) s) e =
                    stack_word_exp s e` SUBST1_TAC THENL
       [MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CASES_ON `stack_word_exp (s:(A,C,FFI)stack_state) e` THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_inst_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; LET_DEF; LET_END_DEF]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; option_DISTINCT]) THEN
  TRY (FIRST_ASSUM CONTR_TAC));;

(* the programs whose evaluation does not read or change the code: their    *)
(* evaluation commutes with a change of the code (for the simple cases of  *)
(* comp_correct)                                                           *)

let STACKPROPSAUX_codefree_def = sem1aux_def
  `(STACKPROPSAUX_codefree (stack_Seq _ _:(A)stack_prog) <=> F) /\
   (STACKPROPSAUX_codefree (stack_If _ _ _ _ _) <=> F) /\
   (STACKPROPSAUX_codefree (stack_Loop _) <=> F) /\
   (STACKPROPSAUX_codefree (stack_Call _ _ _) <=> F) /\
   (STACKPROPSAUX_codefree (JumpLower _ _ _) <=> F) /\
   (STACKPROPSAUX_codefree (RawCall _) <=> F) /\
   (STACKPROPSAUX_codefree (stack_LocValue _ _ _) <=> F) /\
   (STACKPROPSAUX_codefree (stack_StoreConsts _ _ _) <=> F) /\
   (STACKPROPSAUX_codefree (stack_Install _ _ _ _ _) <=> F) /\
   (STACKPROPSAUX_codefree _ <=> T)`;;

let STACKPROPSAUX_inst_code = prove
 (`!i (s:(A,C,FFI)stack_state).
     stack_inst i (stack_state_code_fupd (K c) s) =
     OPTION_MAP (stack_state_code_fupd (K c)) (stack_inst i s)`,
  MATCH_MP_TAC STACKPROPSAUX_inst_frame THEN
  REWRITE_TAC[stack_set_var_def; stack_set_fp_var_def] THEN SIMP[]);;

let STACKPROPSAUX_word_exp_code = prove
 (`stack_word_exp (stack_state_code_fupd (K c) (s:(A,C,FFI)stack_state)) e =
   stack_word_exp s e`,
  MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN SIMP[]);;

let STACKPROPSAUX_FRAME_DEFS =
  [stack_get_var_def; stack_get_vars_def; stack_get_fp_var_def; stack_set_var_def;
   stack_set_fp_var_def; stack_set_store_def; stack_empty_env_def;
   stack_mem_load_def; stack_mem_store_def; stackSem_alloc_def; stack_gc_def;
   stack_has_space_def; sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_load_def;
   stack_sh_mem_store32_def; stack_sh_mem_load32_def; stack_sh_mem_load16_def;
   stack_sh_mem_store16_def; stack_sh_mem_store_byte_def; stack_sh_mem_load_byte_def;
   stack_get_var_imm_def; LET_DEF; LET_END_DEF];;

let STACKPROPSAUX_sh_mem_op_code = prove
 (`sh_mem_op op r a (stack_state_code_fupd (K c) (s:(A,C,FFI)stack_state)) =
   (FST (sh_mem_op op r a s),stack_state_code_fupd (K c) (SND (sh_mem_op op r a s))) /\
   stack_state_code (SND (sh_mem_op op r a s)) = stack_state_code s`,
  CASES_ON `op:memop` THEN REWRITE_TAC STACKPROPSAUX_FRAME_DEFS THEN SIMP[] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let STACKPROPSAUX_dec_clock_code = prove
 (`stack_dec_clock (stack_state_code_fupd (K c) (s:(A,C,FFI)stack_state)) =
   stack_state_code_fupd (K c) (stack_dec_clock s)`,
  REWRITE_TAC[stack_dec_clock_def] THEN SIMP[]);;

let STACKPROPSAUX_eval_code_frame = prove
 (`!p (s:(A,C,FFI)stack_state) c.
     STACKPROPSAUX_codefree p ==>
     stack_evaluate (p,stack_state_code_fupd (K c) s) =
     (FST (stack_evaluate (p,s)),
      stack_state_code_fupd (K c) (SND (stack_evaluate (p,s)))) /\
     stack_state_code (SND (stack_evaluate (p,s))) = stack_state_code s`,
  GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  REWRITE_TAC[STACKPROPSAUX_codefree_def] THEN REPEAT GEN_TAC THEN
  TRY (CASES_ON `a2:(A)addr`) THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SIMP(STACKPROPSAUX_inst_code :: STACKPROPSAUX_word_exp_code ::
       STACKPROPSAUX_sh_mem_op_code :: STACKPROPSAUX_dec_clock_code ::
       STACKPROPSAUX_FRAME_DEFS) THEN
  EVERY_CASE_TAC THEN
  FS(STACKPROPSAUX_word_exp_code :: OPTION_MAP_DEF :: STACKPROPSAUX_sh_mem_op_code ::
     STACKPROPSAUX_dec_clock_code :: STACKPROPSAUX_FRAME_DEFS) THEN
  RVEQ_TAC THEN SIMP[] THEN STACKPROPSAUX_RC_CONTR_TAC THEN
  STACKPROPSAUX_FACTS_TAC [stack_inst_const] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_with_clock_self = prove
 (`stack_state_clock_fupd (K (stack_state_clock t)) (t:(A,C,FFI)stack_state) = t`,
  REWRITE_TAC[stack_state_component_equality] THEN SIMP[]);;

(* comp_correct for the programs that do not use the code *)

let STACKPROPSAUX_codefree_correct = prove
 (`!p (s:(A,C,FFI)stack_state) r s1 i t.
     STACKPROPSAUX_codefree p /\ stack_evaluate (p,s) = (r,s1) /\
     stack_rawcallProof_state_rel i s t
     ==> ?ck t1 k1.
           stack_rawcallProof_state_rel i s1 t1 /\
           stack_evaluate (p,stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
           (r,stack_state_stack_space_fupd (K k1) t1) /\
           (~(r = SOME stack_TimeOut) /\
            ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
            k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:(A,C,FFI)stack_state`; `c:((A)stack_prog)spt`] o
              MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
                          STACKPROPSAUX_eval_code_frame)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`0`; `stack_state_code_fupd (K c) (s1:(A,C,FFI)stack_state)`;
    `stack_state_stack_space (s1:(A,C,FFI)stack_state)`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN SIMP[STACKPROPSAUX_with_clock_self] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `c:((A)stack_prog)spt` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[stack_state_component_equality] THEN SIMP[]]);;

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
  STRIP_TAC THEN REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC STACKPROPSAUX_codefree_correct THEN
  EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_codefree_def]);;

let STACKPROPSAUX_rel_code = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   t = stack_state_code_fupd (K (stack_state_code t)) s`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN SIMP[]);;

(* the conclusion of comp_correct for a program that evaluates on t as on  *)
(* s, with t's code                                                        *)

let STACKPROPSAUX_frame_correct = prove
 (`!p (s:(A,C,FFI)stack_state) r s1 i t.
     stack_evaluate (p,s) = (r,s1) /\ stack_rawcallProof_state_rel i s t /\
     stack_evaluate (p,t) = (r,stack_state_code_fupd (K (stack_state_code t)) s1) /\
     stack_state_code s1 = stack_state_code s
     ==> ?ck t1 k1.
           stack_rawcallProof_state_rel i s1 t1 /\
           stack_evaluate (p,stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
           (r,stack_state_stack_space_fupd (K k1) t1) /\
           (~(r = SOME stack_TimeOut) /\
            ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
            k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`0`; `stack_state_code_fupd (K (stack_state_code (t:(A,C,FFI)stack_state)))
            (s1:(A,C,FFI)stack_state)`;
    `stack_state_stack_space (stack_state_code_fupd
       (K (stack_state_code (t:(A,C,FFI)stack_state))) (s1:(A,C,FFI)stack_state))`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_with_clock_self; with_stack_space] THEN
  UNDISCH_TAC `stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state)` THEN
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN
  EXISTS_TAC `c:((A)stack_prog)spt` THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* state_rel i' with another i, when the code only grew *)

let STACKPROPSAUX_state_rel_mono = prove
 (`!i' s2 (t1:(A,C,FFI)stack_state) i (s:(A,C,FFI)stack_state).
   stack_rawcallProof_state_rel i' s2 t1 /\
   stack_rawcallProof_state_ok i (stack_state_code s) /\
   subspt (stack_state_code s) (stack_state_code s2)
   ==> stack_rawcallProof_state_rel i s2 t1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_rawcallProof_state_rel_def; stack_rawcallProof_state_ok_def] THEN
  STRIP_TAC THEN EXISTS_TAC `c:((A)stack_prog)spt` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[subspt_lookup]);;

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

let STACKPROPSAUX_loc_check_rel = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   (loc_check (stack_state_code t) (l1,l2) <=> loc_check (stack_state_code s) (l1,l2))`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[loc_check_def] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `n IN domain (stack_state_code (s:(A,C,FFI)stack_state))` MP_TAC THENL
     [UNDISCH_TAC `domain (c:((A)stack_prog)spt) =
                   domain (stack_state_code (s:(A,C,FFI)stack_state))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[domain_lookup] THEN
      EXISTS_TAC `e:(A)stack_prog` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[domain_lookup] THEN DISCH_THEN(X_CHOOSE_TAC `b:(A)stack_prog`) THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `b:(A)stack_prog`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `b:(A)stack_prog`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_rawcallProof_get_labels_comp]) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:(A)stack_prog`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `comp_top i' (e:(A)stack_prog)`] THEN
    ASM_REWRITE_TAC[stack_rawcallProof_get_labels_comp]]);;

let STACKPROPSAUX_locvalue_frame = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) /\
   stack_evaluate (stack_LocValue r l1 l2,s) = (res,s1)
   ==> stack_evaluate (stack_LocValue r l1 l2,t) =
       (res,stack_state_code_fupd (K (stack_state_code t)) s1) /\
       stack_state_code s1 = stack_state_code s`,
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPROPSAUX_loc_check_rel) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP STACKPROPSAUX_rel_code) THEN
  UNDISCH_TAC `stack_evaluate (stack_LocValue r l1 l2,s:(A,C,FFI)stack_state) = (res,s1)` THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[stack_set_var_def] THEN SIMP[]);;

let STACKPROPSAUX_storeconsts_frame = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) /\
   stack_evaluate (stack_StoreConsts t1 t2 stub,s) = (res,s1) /\ ~(res = SOME stack_Error)
   ==> stack_evaluate (stack_StoreConsts t1 t2 stub,t) =
       (res,stack_state_code_fupd (K (stack_state_code t)) s1) /\
       stack_state_code s1 = stack_state_code s`,
  STRIP_TAC THEN
  SUBGOAL_THEN `check_store_consts_opt t1 t2 stub (stack_state_code (s:(A,C,FFI)stack_state))
                ==> check_store_consts_opt t1 t2 stub
                      (stack_state_code (t:(A,C,FFI)stack_state))` ASSUME_TAC THENL
   [UNDISCH_TAC `stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state)` THEN
    REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SIMP[] THEN CASES_ON `stub:num option` THEN REWRITE_TAC[check_store_consts_opt_def] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STACKPROPSAUX_rc_comp_thms];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP STACKPROPSAUX_rel_code) THEN
  UNDISCH_TAC `stack_evaluate (stack_StoreConsts t1 t2 stub,s:(A,C,FFI)stack_state) =
               (res,s1)` THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN SIMP[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  RULE_ASSUM_TAC(SIMP_RULE[]) THEN TRY (ASM_MESON_TAC[]) THEN
  REWRITE_TAC[store_const_sem_def; stack_get_var_def] THEN SIMP[] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[stack_set_var_def; stack_unset_var_def; I_THM] THEN SIMP[] THEN
  TRY COND_CASES_TAC THEN SIMP[I_THM]);;

(* the clause tactics of comp_correct *)

let STACKPROPSAUX_RC_STRIP_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)));;

let STACKPROPSAUX_RC_SIMPLE_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  TRY CONJ_TAC THEN MATCH_MP_TAC STACKPROPSAUX_codefree_correct THEN
  FIRST_ASSUM(fun th -> if STACKPROPSAUX_is_eval_eq (concl th)
                        then EXISTS_TAC (snd(dest_pair(rand(lhs(concl th)))))
                        else failwith "") THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_codefree_def];;

let STACKPROPSAUX_RC_FRAME_TAC (fr:thm) : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  TRY CONJ_TAC THEN MATCH_MP_TAC STACKPROPSAUX_frame_correct THEN
  FIRST_ASSUM(fun th -> if STACKPROPSAUX_is_eval_eq (concl th)
                        then EXISTS_TAC (snd(dest_pair(rand(lhs(concl th)))))
                        else failwith "") THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC fr THEN ASM_REWRITE_TAC[];;

(* STACKPROPSAUX_USE_IHS_TAC of stackProps.ml, where the variables of an    *)
(* induction hypothesis that its evaluate equations do not determine are    *)
(* also found by matching its other antecedents with the assumptions (the  *)
(* state_rel i s t of comp_correct)                                         *)

let STACKPROPSAUX_RC_USE_IHS_TAC (side:tactic) : tactic = fun (asl,w as g) ->
  let facts = map snd asl in
  let evs = filter (fun th -> STACKPROPSAUX_is_eval_eq (concl th)) facts in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists STACKPROPSAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
  let try_m vs1 theta p t =
    let (_,tmi,tyi) = term_match [] p t in
    if exists (fun (a,b) -> not (a = b)) tyi ||
       exists (fun (t,v) -> not (mem v vs1) && not (t = v)) tmi
    then failwith "" else
    filter (fun (t,v) -> mem v vs1 && not (t = v)) tmi @ theta in
  let insts_of ih0 =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = SPECL vs1 ih0 in
    let ant,_ = dest_imp (concl ih) in
    let cjs = conjuncts ant in
    let ecjs = filter STACKPROPSAUX_is_eval_eq cjs in
    let rec go theta cs =
      match cs with
        [] -> [theta]
      | c::rest ->
          let c' = vsubst theta c in
          flat (map (fun e -> try go (try_m vs1 theta c' (concl e)) rest
                              with Failure _ -> []) evs) in
    let rec more theta cs =
      match cs with
        [] -> theta
      | c::rest ->
          let c' = vsubst theta c in
          if not (exists (fun v -> mem v vs1) (frees c')) then more theta rest else
          (try more (tryfind (fun f -> try_m vs1 theta c' (concl f)) facts) rest
           with Failure _ -> more theta rest) in
    map (fun theta ->
        let theta = more theta (filter (fun c -> not (STACKPROPSAUX_is_eval_eq c)) cjs) in
        let ihi = SPECL (map (fun v -> try rev_assoc v theta with Failure _ -> v) vs1)
                        ih0 in
        let a,c = dest_imp (concl ihi) in
        let rest = filter (fun v -> mem v vs1) (subtract (frees a) (frees c)) in
        c, GENL rest ihi) (go [] ecjs) in
  let insts = flat (map insts_of ihs) in
  MAP_EVERY (fun (c,th) ->
      TRY (fun (asl,w as g) ->
             let th' = TAC_PROOF((asl,c),
                         MATCH_MP_TAC th THEN STACKPROPSAUX_EXISTS_ASM_TAC side THEN
                         NO_TAC) in
             STRIP_ASSUME_TAC th' g))
    insts g;;

let STACKPROPSAUX_rel_get = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   (!v. stack_get_var v t = stack_get_var v s) /\
   (!ri. stack_get_var_imm ri t = stack_get_var_imm ri s) /\
   stack_state_regs t = stack_state_regs s /\
   stack_state_stack_space t = stack_state_stack_space s /\
   stack_state_stack t = stack_state_stack s /\
   stack_state_use_stack t = stack_state_use_stack s /\
   domain (stack_state_code t) = domain (stack_state_code s)`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN SIMP[stack_get_var_def] THEN GEN_TAC THEN
  CASES_ON `ri:(A)reg_imm` THEN REWRITE_TAC[stack_get_var_imm_def; stack_get_var_def] THEN
  SIMP[]);;

(* the witnesses ck, t1, k1 of an assumption                                *)
(* stack_evaluate (stack_rawcall_comp i c,clock_fupd (K (clock t + ck)) t) = *)
(* (r,stack_space_fupd (K k1) t1) for the program pattern prog              *)

let STACKPROPSAUX_RC_WITNESS_TAC (isprog:term->bool) : tactic = fun (asl,w as g) ->
  let ev = find (fun th -> STACKPROPSAUX_is_eval_eq (concl th) &&
                   isprog (fst(dest_pair(rand(lhs(concl th)))))) (map snd asl) in
  let l,r = dest_eq (concl ev) in
  let st = snd(dest_pair(rand l)) in
  let ck = rand(rand(rand(rator st))) in
  let res = snd(dest_pair r) in
  let k1 = rand(rand(rator res)) and t1 = rand res in
  (MAP_EVERY EXISTS_TAC [ck; t1; k1]) g;;

let STACKPROPSAUX_is_comp_of c tm =
  try let h,args = strip_comb tm in
      fst(dest_const h) = "stack_rawcall_comp" && length args = 2 && el 1 args = c
  with Failure _ -> false;;

let STACKPROPSAUX_RC_UNFOLD_TAC : tactic =
  FIRST_X_ASSUM (MP_TAC o check (fun th -> STACKPROPSAUX_is_eval_eq (concl th) &&
     not (STACKPROPSAUX_is_clock_state (STACKPROPSAUX_eval_state (concl th))))) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[stack_evaluate_def] THENC
           REWRITE_CONV(STACKPROPSAUX_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_TIDY_TAC;;

let STACKPROPSAUX_RC_IF_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN STACKPROPSAUX_RC_UNFOLD_TAC THEN
  STACKPROPSAUX_RC_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN
  STACKPROPSAUX_DROP_IHS_TAC THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_FACTS_TAC [STACKPROPSAUX_rel_get] THEN
  (fun (asl,w as g) ->
     let c = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "stack_If"
                                 with Failure _ -> false) w in
     let _,args = strip_comb c in
     let c1 = rand(el 3 args) and c2 = rand(el 4 args) in
     (STACKPROPSAUX_RC_WITNESS_TAC (STACKPROPSAUX_is_comp_of c1) ORELSE
      STACKPROPSAUX_RC_WITNESS_TAC (STACKPROPSAUX_is_comp_of c2)) g) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  REPEAT (CHANGED_TAC
    (ASM_REWRITE_TAC[stack_get_var_with_const; stack_get_var_imm_with_const] THEN
     CASE_REWRITE_TAC[]));;

let STACKPROPSAUX_rel_lookup = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) /\
   lookup n (stack_state_code s) = SOME b
   ==> ?i'. stack_rawcallProof_state_ok i' (stack_state_code s) /\
            lookup n (stack_state_code t) = SOME (comp_top i' b) /\
            stack_rawcallProof_state_rel i' s t /\
            stack_rawcallProof_state_rel i' (stack_dec_clock s) (stack_dec_clock t)`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `b:(A)stack_prog`] o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `i':num spt` THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN EXISTS_TAC `c:((A)stack_prog)spt` THEN
  REWRITE_TAC[stack_dec_clock_def] THEN SIMP[] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_rel_clock = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   stack_state_clock s = stack_state_clock t`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

(* for every assumption lookup n (code s) = SOME b and the assumption        *)
(* state_rel i s t: the facts of STACKPROPSAUX_rel_lookup                    *)

let STACKPROPSAUX_RC_LOOKUP_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let is_c n th = try fst(dest_const(fst(strip_comb(concl th)))) = n
                  with Failure _ -> false in
  let rels = filter (is_c "stack_rawcallProof_state_rel") ths in
  let lks = filter (fun th -> is_eq (concl th) &&
                      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "lookup"
                       with Failure _ -> false)) ths in
  MAP_EVERY (fun r -> MAP_EVERY (fun l g ->
      try STRIP_ASSUME_TAC (MATCH_MP STACKPROPSAUX_rel_lookup (CONJ r l)) g
      with Failure _ -> ALL_TAC g) lks) rels g;;

(* the target state t of the goal ?ck t1 k1. ... stack_evaluate (p,          *)
(* clock_fupd (K (clock t + ck)) t) = ...                                   *)

let STACKPROPSAUX_goal_t (w:term) =
  let ev = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "stack_evaluate"
                               with Failure _ -> false) w in
  rand(snd(dest_pair(rand ev)));;

let STACKPROPSAUX_RC_ZERO_WITNESS_TAC (f:term->term) : tactic = fun (asl,w as g) ->
  let t = STACKPROPSAUX_goal_t w in
  let t1 = f t in
  (MAP_EVERY EXISTS_TAC [`0`; t1;
     list_mk_icomb "stack_state_stack_space" [t1]]) g;;

let STACKPROPSAUX_RC_CLOCK_TAC : tactic =
  STACKPROPSAUX_FACTS_TAC [STACKPROPSAUX_rel_clock] THEN
  ASSUM_LIST (fun ths ->
    let ceqs = filter (fun th -> is_eq (concl th) &&
                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_state_clock" &&
                      fst(dest_const(fst(strip_comb(rhs(concl th))))) = "stack_state_clock"
                  with Failure _ -> false)) ths in
    RULE_ASSUM_TAC (fun a -> if exists (fun c -> concl c = concl a) ceqs then a
                             else REWRITE_RULE ceqs a));;

let STACKPROPSAUX_rel_ok = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   stack_rawcallProof_state_ok i (stack_state_code s)`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC);;

let STACKPROPSAUX_clock_fupd_id = prove
 (`stack_state_clock (x:(A,C,FFI)stack_state) = n ==> stack_state_clock_fupd (K n) x = x`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_with_clock_self]);;

(* the goal state_rel i s2 t1 from assumptions state_rel i' s2 t1,         *)
(* state_ok i (code s) and subspt (code s) (code s2)                        *)

let STACKPROPSAUX_RC_MONO_TAC : tactic = fun (asl,w as g) ->
  let _,args = strip_comb w in
  let i = el 0 args and s2 = el 1 args and t1 = el 2 args in
  let ths = map (concl o snd) asl in
  let i' = el 0 (snd(strip_comb(find (fun c ->
             try let h,a = strip_comb c in
                 fst(dest_const h) = "stack_rawcallProof_state_rel" &&
                 el 1 a = s2 && el 2 a = t1 with Failure _ -> false) ths))) in
  let oks = filter (fun c ->
             try let h,a = strip_comb c in
                 fst(dest_const h) = "stack_rawcallProof_state_ok" && el 0 a = i
             with Failure _ -> false) ths in
  FIRST (map (fun ok ->
           let s = rand(el 1 (snd(strip_comb ok))) in
           MATCH_MP_TAC STACKPROPSAUX_state_rel_mono THEN
           MAP_EVERY EXISTS_TAC [i'; s] THEN ASM_REWRITE_TAC[] THEN NO_TAC) oks) g;;

let STACKPROPSAUX_RC_FINISH_TAC : tactic =
  ASM_REWRITE_TAC[STACKPROPSAUX_with_clock_self; with_stack_space; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (STACKPROPSAUX_RC_MONO_TAC THEN NO_TAC) THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  REPEAT (CHANGED_TAC
    (ASM_REWRITE_TAC[stack_get_var_with_const; stack_get_var_imm_with_const;
                     stack_find_code_def; stack_dest_Seq_def;
                     STACKPROPSAUX_dec_clock_clock] THEN
     SIMP[STACKPROPSAUX_dec_clock_add; STACKPROPSAUX_dec_clock_clock;
          STACKPROPSAUX_clock_fupd_id] THEN
     CASE_REWRITE_TAC[]));;

let STACKPROPSAUX_RC_JUMP_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN STACKPROPSAUX_RC_UNFOLD_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_find_code_def]) THEN
  STACKPROPSAUX_RC_LOOKUP_TAC THEN
  STACKPROPSAUX_RC_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN STACKPROPSAUX_DROP_IHS_TAC THEN
  STACKPROPSAUX_FACTS_TAC [STACKPROPSAUX_rel_get; stack_evaluate_mono;
                           STACKPROPSAUX_state_rel_upd; STACKPROPSAUX_rel_ok] THEN
  STACKPROPSAUX_RC_CLOCK_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_dec_clock_clock; stack_dec_clock_const;
                              stack_set_var_const; empty_env_const]) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  FIRST [STACKPROPSAUX_RC_WITNESS_TAC (fun p -> try fst(dest_const(fst(strip_comb p))) =
                                                    "comp_top" with Failure _ -> false) THEN
         STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC;
         STACKPROPSAUX_RC_ZERO_WITNESS_TAC I THEN STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC;
         STACKPROPSAUX_RC_ZERO_WITNESS_TAC (fun t -> list_mk_icomb "stack_empty_env" [t]) THEN
         STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC];;

(* the case Seq of comp_correct without the rawcall optimisation: the     *)
(* program Seq (comp i c1) (comp i c2)                                       *)

let STACKPROPSAUX_rc_seq_default = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state) t i r s1.
     (!t i r s1.
        stack_evaluate (c1,s) = (r,s1) /\ ~(r = SOME stack_Error) /\
        stack_rawcallProof_state_rel i s t
        ==> ?ck t1 k1.
              stack_rawcallProof_state_rel i s1 t1 /\
              stack_evaluate (stack_rawcall_comp i c1,
                              stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
              (r,stack_state_stack_space_fupd (K k1) t1) /\
              (~(r = SOME stack_TimeOut) /\
               ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
               k1 = stack_state_stack_space t1)) /\
     (!s1. stack_evaluate (c1,s) = (NONE,s1) ==>
        !t i r s1'.
          stack_evaluate (c2,s1) = (r,s1') /\ ~(r = SOME stack_Error) /\
          stack_rawcallProof_state_rel i s1 t
          ==> ?ck t1 k1.
                stack_rawcallProof_state_rel i s1' t1 /\
                stack_evaluate (stack_rawcall_comp i c2,
                                stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
                (r,stack_state_stack_space_fupd (K k1) t1) /\
                (~(r = SOME stack_TimeOut) /\
                 ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
                 k1 = stack_state_stack_space t1)) /\
     stack_evaluate (stack_Seq c1 c2,s) = (r,s1) /\ ~(r = SOME stack_Error) /\
     stack_rawcallProof_state_rel i s t
     ==> ?ck t1 k1.
           stack_rawcallProof_state_rel i s1 t1 /\
           stack_evaluate (stack_Seq (stack_rawcall_comp i c1) (stack_rawcall_comp i c2),
                           stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
           (r,stack_state_stack_space_fupd (K k1) t1) /\
           (~(r = SOME stack_TimeOut) /\
            ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
            k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `?res (s2:(A,C,FFI)stack_state). stack_evaluate (c1,s) = (res,s2)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res:((A)stack_result)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_ALL_TAC) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,C,FFI)stack_state`; `i:num spt`;
                                  `r:((A)stack_result)option`;
                                  `s1:(A,C,FFI)stack_state`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `k1:num`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,C,FFI)stack_state`; `i:num spt`;
                                `NONE:((A)stack_result)option`;
                                `s2:(A,C,FFI)stack_state`]) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[with_stack_space]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s2:(A,C,FFI)stack_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t1:(A,C,FFI)stack_state`; `i:num spt`;
                             `r:((A)stack_result)option`;
                             `s1:(A,C,FFI)stack_state`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`ck':num`,`extra:num`]
          (SPECL [`stack_rawcall_comp i (c1:(A)stack_prog)`;
                  `stack_state_clock_fupd (K (stack_state_clock t + ck))
                     (t:(A,C,FFI)stack_state)`;
                  `NONE:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`]
                 stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t1':(A,C,FFI)stack_state`; `k1':num`] THEN
  ASM_REWRITE_TAC[ADD_ASSOC] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* the evaluation of the programs of the rawcall optimisation             *)

let STACKPROPSAUX_eval_call_none = prove
 (CASE_TERM
  `stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME prog
   ==> stack_evaluate (stack_Call NONE dest NONE:(A)stack_prog,s:(A,C,FFI)stack_state) =
       if stack_state_clock s = 0 then (SOME stack_TimeOut,stack_empty_env s)
       else match stack_evaluate (prog,stack_dec_clock s) with
              (res,s1) -> if stack_bad_fun_return res then (SOME stack_Error,s1)
                          else (res,s1)`,
  DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_eval_rawcall = prove
 (CASE_TERM
  `lookup d (stack_state_code s) = SOME (stack_Seq p1 q)
   ==> stack_evaluate (RawCall d:(A)stack_prog,s:(A,C,FFI)stack_state) =
       if stack_state_clock s = 0 then (SOME stack_TimeOut,stack_empty_env s)
       else match stack_evaluate (q,stack_dec_clock s) with
              (res,s1) -> if stack_bad_fun_return res then (SOME stack_Error,s1)
                          else (res,s1)`,
  DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_dest_Seq_def] THEN CASE_REWRITE_TAC[]);;

let STACKPROPSAUX_eval_seq_alloc = prove
 (`stack_evaluate (stack_Seq (StackAlloc l) q:(A)stack_prog,s:(A,C,FFI)stack_state) =
   if ~stack_state_use_stack s then (SOME stack_Error,s)
   else if stack_state_stack_space s < l
   then (SOME (stackSem_Halt (wl_Word (word 2))),stack_empty_env s)
   else stack_evaluate (q,stack_state_stack_space_fupd (K (stack_state_stack_space s - l)) s)`,
  GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
  ASM_CASES_TAC `stack_state_use_stack (s:(A,C,FFI)stack_state)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_state_stack_space (s:(A,C,FFI)stack_state) < l` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

(* the rule of RawCall d for every state with the code of t, from          *)
(* lookup d (code t) = SOME (Seq p1 q)                                       *)

let STACKPROPSAUX_code_gen (th:thm) : thm =
  let t = rand(rand(lhs(concl th))) in
  let u = variant (frees (concl th)) (mk_var("u",type_of t)) in
  let eq = mk_eq(list_mk_icomb "stack_state_code" [u],
                 list_mk_icomb "stack_state_code" [t]) in
  GEN u (DISCH eq (MATCH_MP STACKPROPSAUX_eval_rawcall (SUBS [SYM (ASSUME eq)] th)));;

(* a goal stack_evaluate (q,x) ... = stack_evaluate (q,y) ...: proves x = y *)

let STACKPROPSAUX_EVAL_STATE_EQ_TAC : tactic = fun (asl,w as g) ->
  let l,r = dest_eq w in
  let ev tm = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "stack_evaluate"
                                  with Failure _ -> false) tm in
  let x = snd(dest_pair(rand(ev l))) and y = snd(dest_pair(rand(ev r))) in
  (SUBGOAL_THEN (mk_eq(x,y)) SUBST1_TAC THENL
    [REWRITE_TAC[stack_state_component_equality] THEN SIMP[stack_dec_clock_def] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC[]]) g;;

(* the target side of the rawcall optimisation: the call of d after the    *)
(* stack space has grown by k, and the program that replaces it            *)

let STACKPROPSAUX_rawcall_sim = prove
 (`!k l d q (t:(A,C,FFI)stack_state) ck r t1.
     lookup d (stack_state_code t) = SOME (stack_Seq (StackAlloc l) q) /\
     stack_state_use_stack t /\
     stack_state_stack_space t + k <= LENGTH (stack_state_stack t) /\
     ~(stack_state_clock t + ck = 0) /\
     stack_evaluate (stack_Call NONE (INL d) NONE,
        stack_state_stack_space_fupd (K (stack_state_stack_space t + k))
          (stack_state_clock_fupd (K (stack_state_clock t + ck)) t)) = (r,t1) /\
     ~(r = SOME stack_Error)
     ==> ?ck' k1.
           stack_evaluate
             ((if l = k then RawCall d
               else if l < k then stack_Seq (StackFree (k - l)) (RawCall d)
               else stack_Seq stack_Tick (stack_Seq (StackAlloc (l - k)) (RawCall d))),
              stack_state_clock_fupd (K (stack_state_clock t + ck')) t) =
           (r,stack_state_stack_space_fupd (K k1) t1) /\
           (~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
            k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(stack_state_clock (t:(A,C,FFI)stack_state) + ck + 1 = 0)` ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def] o
                check (STACKPROPSAUX_is_eval_eq o concl)) THEN
  CASE_REWRITE_TAC[] THEN SIMP[stack_find_code_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[STACKPROPSAUX_eval_seq_alloc] THEN SIMP[stack_dec_clock_def] THEN
  ASM_CASES_TAC `stack_state_stack_space (t:(A,C,FFI)stack_state) + k < l` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[stack_bad_fun_return_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN `~(l = k) /\ ~(l < k) /\
                  stack_state_stack_space (t:(A,C,FFI)stack_state) < l - k`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `stack_state_stack_space (t:(A,C,FFI)stack_state)`] THEN
    GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
    SIMP[] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
    SIMP[stack_dec_clock_def] THEN
    REWRITE_TAC[PAIR_EQ; stack_state_component_equality] THEN
    SIMP[stack_empty_env_def; stack_dec_clock_def];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_ASSUM(fun th ->
    if can (find_term ((=) `lookup:num->((A)stack_prog)spt->((A)stack_prog)option`))
           (concl th)
    then ASSUME_TAC (STACKPROPSAUX_code_gen th) else failwith "") THEN
  ASM_CASES_TAC `l:num = k` THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`ck:num`; `stack_state_stack_space (t1:(A,C,FFI)stack_state)`] THEN
    REWRITE_TAC[with_stack_space] THEN ASM_REWRITE_TAC[] THEN
    SIMP[] THEN STACKPROPSAUX_EVAL_STATE_EQ_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `l:num < k` THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`ck:num`; `stack_state_stack_space (t1:(A,C,FFI)stack_state)`] THEN
    REWRITE_TAC[with_stack_space] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <
                    stack_state_stack_space t + (k - l))` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
    SIMP[] THEN STACKPROPSAUX_EVAL_STATE_EQ_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ck + 1`; `stack_state_stack_space (t1:(A,C,FFI)stack_state)`] THEN
  REWRITE_TAC[with_stack_space] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(stack_state_stack_space (t:(A,C,FFI)stack_state) < l - k)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
  SIMP[stack_dec_clock_def; ARITH_RULE `!a b. (a + b + 1) - 1 = a + b`] THEN
  REWRITE_TAC[STACKPROPSAUX_eval_seq_alloc] THEN
  SIMP[stack_dec_clock_def] THEN STACKPROPSAUX_EVAL_STATE_EQ_TAC);;

(* the case clock = 0 of the rawcall optimisation: all time out             *)

let STACKPROPSAUX_K1_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let l = lhs bod in
  let x = if is_pair l then snd(dest_pair l) else l in
  (EXISTS_TAC (list_mk_icomb "stack_state_stack_space" [x]) THEN
   REWRITE_TAC[PAIR_EQ; stack_state_component_equality] THEN
   SIMP[stack_empty_env_def; stack_dec_clock_def]) g;;

let STACKPROPSAUX_rawcall_timeout = prove
 (`!k l d q (t:(A,C,FFI)stack_state) ck r t1.
     lookup d (stack_state_code t) = SOME (stack_Seq (StackAlloc l) q) /\
     stack_state_use_stack t /\
     stack_state_stack_space t + k <= LENGTH (stack_state_stack t) /\
     stack_state_clock t + ck = 0 /\
     stack_evaluate (stack_Call NONE (INL d) NONE,
        stack_state_stack_space_fupd (K (stack_state_stack_space t + k))
          (stack_state_clock_fupd (K (stack_state_clock t + ck)) t)) = (r,t1)
     ==> r = SOME stack_TimeOut /\
         ?k1. stack_evaluate
                ((if l = k then RawCall d
                  else if l < k then stack_Seq (StackFree (k - l)) (RawCall d)
                  else stack_Seq stack_Tick (stack_Seq (StackAlloc (l - k)) (RawCall d))),
                 stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
              (r,stack_state_stack_space_fupd (K k1) t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def] o
                check (STACKPROPSAUX_is_eval_eq o concl)) THEN
  CASE_REWRITE_TAC[] THEN SIMP[stack_find_code_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    if can (find_term ((=) `lookup:num->((A)stack_prog)spt->((A)stack_prog)option`))
           (concl th)
    then ASSUME_TAC (STACKPROPSAUX_code_gen th) else failwith "") THEN
  ASM_CASES_TAC `l:num = k` THEN ASM_REWRITE_TAC[] THENL
   [SIMP[] THEN STACKPROPSAUX_K1_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `l:num < k` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <
                    stack_state_stack_space t + (k - l))` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [stack_evaluate_def] THEN
    GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [stack_evaluate_def] THEN
    SIMP[] THEN STACKPROPSAUX_K1_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [stack_evaluate_def] THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    [stack_evaluate_def] THEN
  SIMP[] THEN STACKPROPSAUX_K1_TAC);;

(* the case Seq of comp_correct with the rawcall optimisation              *)

let STACKPROPSAUX_eval_stackfree = prove
 (`stack_evaluate (StackFree n:(A)stack_prog,s:(A,C,FFI)stack_state) =
   if ~stack_state_use_stack s then (SOME stack_Error,s) else
   if LENGTH (stack_state_stack s) < stack_state_stack_space s + n
   then (SOME stack_Error,stack_empty_env s)
   else (NONE,stack_state_stack_space_fupd (K (stack_state_stack_space s + n)) s)`,
  GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN REWRITE_TAC[]);;

let STACKPROPSAUX_eval_seq = prove
 (`stack_evaluate (stack_Seq c1 c2:(A)stack_prog,s:(A,C,FFI)stack_state) =
   pair_CASE (stack_evaluate (c1,s))
     (\res s1. if res = NONE then stack_evaluate (c2,s1) else (res,s1))`,
  GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN REWRITE_TAC[]);;

let STACKPROPSAUX_rc_seq_rawcall = prove
 (`!k d l (s:(A,C,FFI)stack_state) t i r s1.
      (!s1. stack_evaluate (StackFree k,s) = (NONE,s1) ==>
         !t i r s1'.
           stack_evaluate (stack_Call NONE (INL d) NONE,s1) = (r,s1') /\
           ~(r = SOME stack_Error) /\ stack_rawcallProof_state_rel i s1 t
           ==> ?ck t1 k1.
                 stack_rawcallProof_state_rel i s1' t1 /\
                 stack_evaluate (stack_rawcall_comp i (stack_Call NONE (INL d) NONE),
                                 stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
                 (r,stack_state_stack_space_fupd (K k1) t1) /\
                 (~(r = SOME stack_TimeOut) /\
                  ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
                  k1 = stack_state_stack_space t1)) /\
      stack_evaluate (stack_Seq (StackFree k) (stack_Call NONE (INL d) NONE),s) = (r,s1) /\
      ~(r = SOME stack_Error) /\ stack_rawcallProof_state_rel i s t /\
      lookup d i = SOME l
      ==> ?ck t1 k1.
            stack_rawcallProof_state_rel i s1 t1 /\
            stack_evaluate
              ((if l = k then RawCall d
                else if l < k then stack_Seq (StackFree (k - l)) (RawCall d)
                else stack_Seq stack_Tick (stack_Seq (StackAlloc (l - k)) (RawCall d))),
               stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
            (r,stack_state_stack_space_fupd (K k1) t1) /\
            (~(r = SOME stack_TimeOut) /\
             ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
             k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `stack_state_use_stack (s:(A,C,FFI)stack_state) /\
                stack_state_stack_space s + k <= LENGTH (stack_state_stack s) /\
                stack_evaluate (stack_Call NONE (INL d) NONE:(A)stack_prog,
                  stack_state_stack_space_fupd (K (stack_state_stack_space s + k)) s) = (r,s1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (STACKPROPSAUX_is_eval_eq o concl)) THEN
    REWRITE_TAC[STACKPROPSAUX_eval_seq; STACKPROPSAUX_eval_stackfree] THEN
    ASM_CASES_TAC `stack_state_use_stack (s:(A,C,FFI)stack_state)` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THENL
     [ALL_TAC;
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]] THEN
    ASM_CASES_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                   stack_state_stack_space s + k` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `stack_state_stack_space_fupd
       (K (stack_state_stack_space s + k)) (s:(A,C,FFI)stack_state)`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[STACKPROPSAUX_eval_stackfree; GSYM NOT_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`stack_state_stack_space_fupd (K (stack_state_stack_space t + k))
        (t:(A,C,FFI)stack_state)`;
     `i:num spt`; `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_rel_get) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACKPROPSAUX_state_rel_upd) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP STACKPROPSAUX_rel_ok
    (ASSUME `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t`)) THEN
  REWRITE_TAC[stack_rawcallProof_state_ok_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`d:num`; `l:num`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:(A)stack_prog`) THEN
  MP_TAC(ISPECL [`i:num spt`; `s:(A,C,FFI)stack_state`; `t:(A,C,FFI)stack_state`;
                 `d:num`; `stack_Seq (StackAlloc l) (p:(A)stack_prog)`]
         (GENL [`i:num spt`; `s:(A,C,FFI)stack_state`; `t:(A,C,FFI)stack_state`;
                `n:num`; `b:(A)stack_prog`] STACKPROPSAUX_rel_lookup)) THEN
  ASM_REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `stack_state_clock (t:(A,C,FFI)stack_state) + ck = 0` THENL
   [FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `d:num`; `stack_rawcall_comp i' (p:(A)stack_prog)`;
                  `t:(A,C,FFI)stack_state`; `ck:num`; `r:((A)stack_result)option`;
                  `stack_state_stack_space_fupd (K k1) (t1:(A,C,FFI)stack_state)`]
                 STACKPROPSAUX_rawcall_timeout) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `k1':num`] THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN SIMP[];
    MP_TAC(SPECL [`k:num`; `l:num`; `d:num`; `stack_rawcall_comp i' (p:(A)stack_prog)`;
                  `t:(A,C,FFI)stack_state`; `ck:num`; `r:((A)stack_result)option`;
                  `stack_state_stack_space_fupd (K k1) (t1:(A,C,FFI)stack_state)`]
                 STACKPROPSAUX_rawcall_sim) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck':num`; `t1:(A,C,FFI)stack_state`; `k1':num`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[]]);;

(* the result of comp_seq: the default, or the rawcall optimisation        *)

let STACKPROPSAUX_dest_case_SOME = prove
 (`!p1 p2 (k:num) (d:num).
     dest_case (p1:(A)stack_prog) p2 = SOME (k,d) <=>
     p1 = StackFree k /\ p2 = stack_Call NONE (INL d) NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_case_def] THEN EVERY_CASE_TAC THEN
  SIMP[] THEN MESON_TAC[]);;

let STACKPROPSAUX_comp_seq_cases = prove
 (`!c1 c2 i (dflt:(A)stack_prog).
     comp_seq c1 c2 i dflt = dflt \/
     ?k d l. c1 = StackFree k /\ c2 = stack_Call NONE (INL d) NONE /\
             lookup d i = SOME l /\
             comp_seq c1 c2 i dflt =
             (if l = k then RawCall d
              else if l < k then stack_Seq (StackFree (k - l)) (RawCall d)
              else stack_Seq stack_Tick (stack_Seq (StackAlloc (l - k)) (RawCall d)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[comp_seq_def] THEN
  ASM_CASES_TAC `dest_case c1 (c2:(A)stack_prog) = NONE` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[cases "option"; PAIR]
    `~(x:(num#num)option = NONE) ==> ?k d. x = SOME (k,d)`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `d:num`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_dest_case_SOME]) THEN
  ASM_CASES_TAC `lookup d (i:num spt) = NONE` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[cases "option"]
    `~(x:num option = NONE) ==> ?l. x = SOME l`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`k:num`; `d:num`; `l:num`] THEN
  ASM_REWRITE_TAC[]);;

(* the case Seq of comp_correct                                             *)

(* from an induction hypothesis !xs. A ==> ... ==> B /\ C: the hypothesis   *)
(* !xs. A ==> ... ==> C                                                      *)

let rec STACKPROPSAUX_CONSEQ_SND (th:thm) : thm =
  let c = concl th in
  if is_forall c then
    let v,_ = dest_forall c in GEN v (STACKPROPSAUX_CONSEQ_SND (SPEC v th))
  else if is_imp c then
    let a,_ = dest_imp c in DISCH a (STACKPROPSAUX_CONSEQ_SND (MP th (ASSUME a)))
  else CONJUNCT2 th;;

(* MP_TAC of th instantiated by the terms tms, its antecedent proved from   *)
(* the assumptions                                                           *)

let STACKPROPSAUX_MP_ASM_TAC (th:thm) (tms:term list) : tactic =
  MP_TAC(ISPECL tms th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN NO_TAC; DISCH_TAC];;

let STACKPROPSAUX_RC_SEQ_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN
  (fun (asl,w as g) ->
     let ihs = filter (is_forall o concl) (map snd asl) in
     MAP_EVERY (ASSUME_TAC o STACKPROPSAUX_CONSEQ_SND) ihs g) THEN
  (fun (asl,w as g) ->
     let ev = find (fun th -> STACKPROPSAUX_is_eval_eq (concl th)) (map snd asl) in
     let l,res = dest_eq (concl ev) in
     let p,s = dest_pair(rand l) in
     let r,s1 = dest_pair res in
     let c1,c2 = match snd(strip_comb p) with [a;b] -> a,b | _ -> failwith "seq" in
     let rel = find (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "stack_rawcallProof_state_rel" with Failure _ -> false)
                    (map snd asl) in
     let i,t = match snd(strip_comb(concl rel)) with [a;_;b] -> a,b | _ -> failwith "rel" in
     let dflt = list_mk_icomb "stack_Seq"
                  [list_mk_icomb "stack_rawcall_comp" [i;c1];
                   list_mk_icomb "stack_rawcall_comp" [i;c2]] in
     (STACKPROPSAUX_MP_ASM_TAC STACKPROPSAUX_rc_seq_default [c1;c2;s;t;i;r;s1] THEN
      REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISJ_CASES_THEN STRIP_ASSUME_TAC
        (ISPECL [c1;c2;i;dflt] STACKPROPSAUX_comp_seq_cases) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
         try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "comp_seq"
         with Failure _ -> false)) THEN
      RVEQ_TAC THEN
      (fun (asl,w as g) ->
         let lk = find (fun th -> try let h,a = strip_comb(lhs(concl th)) in
                                      fst(dest_const h) = "lookup" && el 1 a = i
                                  with Failure _ -> false) (map snd asl) in
         let d = el 0 (snd(strip_comb(lhs(concl lk)))) in
         let l = rand(rand(concl lk)) in
         let ev = find (fun th -> STACKPROPSAUX_is_eval_eq (concl th)) (map snd asl) in
         let p = fst(dest_pair(rand(lhs(concl ev)))) in
         let k = rand(el 0 (snd(strip_comb p))) in
         (STACKPROPSAUX_MP_ASM_TAC STACKPROPSAUX_rc_seq_rawcall [k;d;l;s;t;i;r;s1] THEN
          FIRST_ASSUM ACCEPT_TAC) g)) g);;

(* the case Loop of comp_correct                                            *)

let STACKPROPSAUX_exit_loop_some = prove
 (`!x:((A)stack_result)option.
     (stack_exit_loop x = SOME stack_Error <=> x = SOME stack_Error) /\
     (!w. stack_exit_loop x = SOME (stackSem_Halt w) <=> x = SOME (stackSem_Halt w))`,
  GEN_TAC THEN CASES_ON `x:((A)stack_result)option` THEN
  REWRITE_TAC[stack_exit_loop_def; option_DISTINCT] THEN
  CASES_ON `a:(A)stack_result` THEN
  REWRITE_TAC[stack_exit_loop_def; option_DISTINCT; option_INJ;
              distinctness "stack_result"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ;
                                  distinctness "stack_result"]);;

let STACKPROPSAUX_cont_loop_cases = prove
 (`!x:((A)stack_result)option.
     stack_cont_loop x ==> x = NONE \/ x = SOME (stackSem_Continue 0)`,
  GEN_TAC THEN CASES_ON `x:((A)stack_result)option` THEN
  REWRITE_TAC[stack_cont_loop_def] THEN
  CASES_ON `a:(A)stack_result` THEN REWRITE_TAC[stack_cont_loop_def] THEN
  SIMP[]);;

let STACKPROPSAUX_rc_loop = prove
 (`!c1 (s:(A,C,FFI)stack_state) t i r s1.
     (!t i r s1.
        stack_evaluate (c1,s) = (r,s1) /\ ~(r = SOME stack_Error) /\
        stack_rawcallProof_state_rel i s t
        ==> ?ck t1 k1.
              stack_rawcallProof_state_rel i s1 t1 /\
              stack_evaluate (stack_rawcall_comp i c1,
                              stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
              (r,stack_state_stack_space_fupd (K k1) t1) /\
              (~(r = SOME stack_TimeOut) /\
               ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
               k1 = stack_state_stack_space t1)) /\
     (!res s1. stack_evaluate (c1,s) = (res,s1) /\ stack_cont_loop res /\
               ~(stack_state_clock s1 = 0)
        ==> !t i r s1'.
              stack_evaluate (stack_STOP (stack_Loop c1),stack_dec_clock s1) = (r,s1') /\
              ~(r = SOME stack_Error) /\
              stack_rawcallProof_state_rel i (stack_dec_clock s1) t
              ==> ?ck t1 k1.
                    stack_rawcallProof_state_rel i s1' t1 /\
                    stack_evaluate (stack_rawcall_comp i (stack_STOP (stack_Loop c1)),
                                    stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
                    (r,stack_state_stack_space_fupd (K k1) t1) /\
                    (~(r = SOME stack_TimeOut) /\
                     ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
                     k1 = stack_state_stack_space t1)) /\
     stack_evaluate (stack_Loop c1,s) = (r,s1) /\ ~(r = SOME stack_Error) /\
     stack_rawcallProof_state_rel i s t
     ==> ?ck t1 k1.
           stack_rawcallProof_state_rel i s1 t1 /\
           stack_evaluate (stack_Loop (stack_rawcall_comp i c1),
                           stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
           (r,stack_state_stack_space_fupd (K k1) t1) /\
           (~(r = SOME stack_TimeOut) /\
            ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
            k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `?res (s2:(A,C,FFI)stack_state). stack_evaluate (c1,s) = (res,s2)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [stack_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_cont_loop (res:((A)stack_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[PAIR_EQ]) STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_exit_loop_some]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,C,FFI)stack_state`; `i:num spt`;
                                  `res:((A)stack_result)option`;
                                  `s2:(A,C,FFI)stack_state`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `k1:num`] THEN
    ASM_REWRITE_TAC[STACKPROPSAUX_exit_loop_some; STACKPROPSAUX_exit_loop_timeout] THEN
    ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(res = SOME (stack_Error:(A)stack_result)) /\
                ~(res = SOME stack_TimeOut) /\
                ~(res = SOME (stackSem_Halt (wl_Word (word 2))))` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP STACKPROPSAUX_cont_loop_cases) THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "stack_result"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,C,FFI)stack_state`; `i:num spt`;
                                `res:((A)stack_result)option`;
                                `s2:(A,C,FFI)stack_state`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[with_stack_space]) THEN
  MP_TAC(MATCH_MP STACKPROPSAUX_state_rel_upd
    (ASSUME `stack_rawcallProof_state_rel i (s2:(A,C,FFI)stack_state) t1`)) THEN
  STRIP_TAC THEN
  MP_TAC(GSYM(MATCH_MP STACKPROPSAUX_rel_clock
    (ASSUME `stack_rawcallProof_state_rel i (s2:(A,C,FFI)stack_state) t1`))) THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `stack_state_clock (s2:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `stack_empty_env (t1:(A,C,FFI)stack_state)`;
                          `stack_state_stack_space (stack_empty_env (t1:(A,C,FFI)stack_state))`] THEN
    ASM_REWRITE_TAC[with_stack_space] THEN
    ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`res:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`stack_dec_clock (t1:(A,C,FFI)stack_state)`; `i:num spt`;
                             `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_STOP_def; STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(INST [`ck':num`,`extra:num`]
          (SPECL [`stack_rawcall_comp i (c1:(A)stack_prog)`;
                  `stack_state_clock_fupd (K (stack_state_clock t + ck))
                     (t:(A,C,FFI)stack_state)`;
                  `res:((A)stack_result)option`; `t1:(A,C,FFI)stack_state`]
                 stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t1':(A,C,FFI)stack_state`; `k1':num`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_REWRITE_TAC[ADD_ASSOC] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[stack_STOP_def] THEN
  SUBGOAL_THEN `~(stack_state_clock (s2:(A,C,FFI)stack_state) + ck' = 0) /\
                stack_dec_clock (stack_state_clock_fupd (K (stack_state_clock s2 + ck'))
                                   (t1:(A,C,FFI)stack_state)) =
                stack_state_clock_fupd (K (stack_state_clock (stack_dec_clock t1) + ck'))
                  (stack_dec_clock t1)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `stack_state_clock (t1:(A,C,FFI)stack_state) =
                 stack_state_clock (s2:(A,C,FFI)stack_state)` THEN
    UNDISCH_TAC `~(stack_state_clock (s2:(A,C,FFI)stack_state) = 0)` THEN
    REWRITE_TAC[stack_state_component_equality; stack_dec_clock_def] THEN SIMP[] THEN
    ARITH_TAC;
    SIMP[]]);;

(* the program p, the states s, t, the result r, s1 and the info i of a      *)
(* clause goal of comp_correct (after STACKPROPSAUX_RC_STRIP_TAC)            *)

let STACKPROPSAUX_rc_clause_vars (asl:(string*thm) list) =
  let ths = map snd asl in
  let ev = find (fun th -> STACKPROPSAUX_is_eval_eq (concl th) &&
                   not (STACKPROPSAUX_is_clock_state (STACKPROPSAUX_eval_state (concl th))))
                ths in
  let l,res = dest_eq (concl ev) in
  let p,s = dest_pair(rand l) in
  let r,s1 = dest_pair res in
  let rel = find (fun th -> try let h,a = strip_comb(concl th) in
                                fst(dest_const h) = "stack_rawcallProof_state_rel" &&
                                el 1 a = s
                            with Failure _ -> false) ths in
  let i,t = match snd(strip_comb(concl rel)) with [a;_;b] -> a,b | _ -> failwith "rel" in
  p,s,r,s1,i,t;;

let STACKPROPSAUX_RC_LOOP_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN
  (fun (asl,w as g) ->
     let ihs = filter (is_forall o concl) (map snd asl) in
     MAP_EVERY (ASSUME_TAC o STACKPROPSAUX_CONSEQ_SND) ihs g) THEN
  (fun (asl,w as g) ->
     let p,s,r,s1,i,t = STACKPROPSAUX_rc_clause_vars asl in
     (STACKPROPSAUX_MP_ASM_TAC STACKPROPSAUX_rc_loop [rand p;s;t;i;r;s1] THEN
      REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
      TRY CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) g);;

(* the case RawCall of comp_correct                                         *)

let STACKPROPSAUX_dest_Seq_SOME = prove
 (`!p x y. stack_dest_Seq (p:(A)stack_prog) = SOME (x,y) <=> p = stack_Seq x y`,
  GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  REWRITE_TAC[stack_dest_Seq_def; option_DISTINCT; option_INJ; PAIR_EQ;
              distinctness "stack_prog"; injectivity "stack_prog"] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_RC_RAWCALL_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN STACKPROPSAUX_RC_UNFOLD_TAC THEN
  STACKPROPSAUX_RC_LOOKUP_TAC THEN
  STACKPROPSAUX_RC_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN STACKPROPSAUX_DROP_IHS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[STACKPROPSAUX_dest_Seq_SOME] o
                check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                     "stack_dest_Seq" with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_rc_comp_thms]) THEN
  STACKPROPSAUX_FACTS_TAC [STACKPROPSAUX_rel_get; stack_evaluate_mono;
                           STACKPROPSAUX_state_rel_upd; STACKPROPSAUX_rel_ok] THEN
  STACKPROPSAUX_RC_CLOCK_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_dec_clock_clock; stack_dec_clock_const;
                              stack_set_var_const; empty_env_const]) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
  FIRST [STACKPROPSAUX_RC_WITNESS_TAC (fun p -> try fst(dest_const(fst(strip_comb p))) =
           "stack_rawcall_comp" with Failure _ -> false) THEN
         STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC;
         STACKPROPSAUX_RC_ZERO_WITNESS_TAC (fun t -> list_mk_icomb "stack_empty_env" [t]) THEN
         STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC];;

(* the case Call of comp_correct                                            *)

let STACKPROPSAUX_option4_cases = prove
 (`!x:(P#Q#R#S)option. x = NONE \/ ?a b c d. x = SOME (a,b,c,d)`,
  MESON_TAC[cases "option"; PAIR]);;

let STACKPROPSAUX_option3_cases = prove
 (`!x:(P#Q#R)option. x = NONE \/ ?a b c. x = SOME (a,b,c)`,
  MESON_TAC[cases "option"; PAIR]);;

let STACKPROPSAUX_rel_find_code = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) /\
   stack_find_code dest (regs:(num,(A)word_loc)fmap) (stack_state_code s) = SOME prog
   ==> ?i'. stack_rawcallProof_state_ok i' (stack_state_code s) /\
            stack_find_code dest regs (stack_state_code t) = SOME (comp_top i' prog) /\
            stack_rawcallProof_state_rel i' s t /\
            stack_rawcallProof_state_rel i' (stack_dec_clock s) (stack_dec_clock t)`,
  CASES_ON `dest:num+num` THEN REWRITE_TAC[stack_find_code_def] THENL
   [MESON_TAC[STACKPROPSAUX_rel_lookup]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  MESON_TAC[STACKPROPSAUX_rel_lookup]);;

let STACKPROPSAUX_comp_call_some = prove
 (`!i rh lr l1 l2 dest handler.
     stack_rawcall_comp i (stack_Call (SOME (rh,lr,l1,l2)) dest handler:(A)stack_prog) =
     stack_Call (SOME (stack_rawcall_comp i rh,lr,l1,l2)) dest
       (OPTION_MAP (\(p2,k1,k2). (stack_rawcall_comp i p2,k1,k2)) handler)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPEC `handler:((A)stack_prog#num#num)option` STACKPROPSAUX_option3_cases) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms; OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  SIMP[]);;

let STACKPROPSAUX_rel_dec_set = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   stack_rawcallProof_state_rel i (stack_dec_clock (stack_set_var x y s))
                                  (stack_dec_clock (stack_set_var x y t))`,
  DISCH_THEN(MP_TAC o SPECL [`x:num`; `y:(A)word_loc`] o CONJUNCT1 o CONJUNCT2 o
             CONJUNCT2 o MATCH_MP STACKPROPSAUX_state_rel_upd) THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o MATCH_MP STACKPROPSAUX_state_rel_upd));;

(* a goal with stack_evaluate (p,x) and an assumption stack_evaluate (p,y)  *)
(* = v: proves x = y (record fields and arithmetic) and replaces x by y     *)

let STACKPROPSAUX_EVAL_ASM_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> STACKPROPSAUX_is_eval_eq (concl th)) (map snd asl) in
  let gts = find_terms (fun t -> try fst(dest_const(fst(strip_comb t))) = "stack_evaluate" &&
                                     is_pair (rand t) with Failure _ -> false) w in
  let try1 gt th (g:goal) =
    let p,x = dest_pair(rand gt) in
    let p',y = dest_pair(rand(lhs(concl th))) in
    if not (p = p') || x = y then failwith "EVAL_ASM_TAC" else
    (SUBGOAL_THEN (mk_eq(x,y)) SUBST1_TAC THENL
      [REWRITE_TAC[stack_state_component_equality] THEN
       SIMP[stack_dec_clock_def; stack_set_var_def] THEN ASM_ARITH_TAC;
       ALL_TAC]) g in
  FIRST (flat (map (fun gt -> map (fun th -> try1 gt th) evs) gts)) g;;

(* the tactics of the case Call with a return handler *)

let STACKPROPSAUX_CALL_TGT_TAC : tactic =
  GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN CASE_REWRITE_TAC[] THEN
  STACKPROPSAUX_EVAL_ASM_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;
let STACKPROPSAUX_CALL_SIMPLE_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t1:(A,C,FFI)stack_state`; `k1:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [STACKPROPSAUX_CALL_TGT_TAC THEN TRY (SIMP[] THEN NO_TAC) THEN NO_TAC;
         REWRITE_TAC[IMP_CONJ] THEN ASM_REWRITE_TAC[] THEN NO_TAC];;
let STACKPROPSAUX_CALL_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[];;
let STACKPROPSAUX_CALL_K1_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; distinctness "stack_result"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
     concl th = `k1 = stack_state_stack_space (t1:(A,C,FFI)stack_state)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[with_stack_space]);;
let STACKPROPSAUX_CALL_CONT_TAC (lab:string) (pre:term list) : tactic =
  USE_THEN lab (MP_TAC o SPEC `prog:(A)stack_prog`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL pre) THEN
  REPEAT (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`t1:(A,C,FFI)stack_state`; `i:num spt`;
                             `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]) THEN
  REPEAT (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN
  (fun (asl,w as g) ->
     let ev = find (fun th -> STACKPROPSAUX_is_eval_eq (concl th) &&
                       fst(dest_pair(rand(lhs(concl th)))) =
                       `comp_top i' (prog:(A)stack_prog)`) (map snd asl) in
     let l,res = dest_eq (concl ev) in
     let st = snd(dest_pair(rand l)) in
     let rr,st' = dest_pair res in
     (MP_TAC(INST [`ck':num`,`extra:num`]
        (ISPECL [`comp_top i' (prog:(A)stack_prog)`; st; rr; st']
                stack_evaluate_add_clock)) THEN
      ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"] THEN SIMP[] THEN
      DISCH_TAC) g) THEN
  MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t1':(A,C,FFI)stack_state`; `k1':num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [STACKPROPSAUX_CALL_TGT_TAC THEN TRY (SIMP[] THEN NO_TAC) THEN NO_TAC;
         REWRITE_TAC[IMP_CONJ] THEN ASM_REWRITE_TAC[] THEN NO_TAC];;

(* the case Call with a return handler: the program of comp *)

let STACKPROPSAUX_rc_call_some = prove
 (`!rh lr l1 l2 dest handler (s:(A,C,FFI)stack_state) t i r s1.
     (!prog. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog
        ==> ~(stack_state_clock s = 0)
        ==> !t i r s1.
              stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
              (r,s1)
              ==> ~(r = SOME stack_Error)
              ==> stack_rawcallProof_state_rel i
                    (stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) t
              ==> ?ck t1 k1.
                    stack_rawcallProof_state_rel i s1 t1 /\
                    stack_evaluate (comp_top i prog,
                                    stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
                    (r,stack_state_stack_space_fupd (K k1) t1) /\
                    (~(r = SOME stack_TimeOut)
                     ==> ~(r = SOME (stackSem_Halt (wl_Word (word 2))))
                     ==> k1 = stack_state_stack_space t1)) /\
     (!prog. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog
        ==> ~(stack_state_clock s = 0)
        ==> !x s2.
              stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
              (SOME (stack_Result x),s2)
              ==> x = wl_Loc l1 l2
              ==> !t i r s1.
                    stack_evaluate (rh,s2) = (r,s1)
                    ==> ~(r = SOME stack_Error)
                    ==> stack_rawcallProof_state_rel i s2 t
                    ==> ?ck t1 k1.
                          stack_rawcallProof_state_rel i s1 t1 /\
                          stack_evaluate (stack_rawcall_comp i rh,
                             stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
                          (r,stack_state_stack_space_fupd (K k1) t1) /\
                          (~(r = SOME stack_TimeOut)
                           ==> ~(r = SOME (stackSem_Halt (wl_Word (word 2))))
                           ==> k1 = stack_state_stack_space t1)) /\
     (!prog. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog
        ==> ~(stack_state_clock s = 0)
        ==> !x l1' l2' h s2.
              stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
              (SOME (stack_Exception x),s2)
              ==> handler = SOME (h,l1',l2')
              ==> x = wl_Loc l1' l2'
              ==> !t i r s1.
                    stack_evaluate (h,s2) = (r,s1)
                    ==> ~(r = SOME stack_Error)
                    ==> stack_rawcallProof_state_rel i s2 t
                    ==> ?ck t1 k1.
                          stack_rawcallProof_state_rel i s1 t1 /\
                          stack_evaluate (stack_rawcall_comp i h,
                             stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
                          (r,stack_state_stack_space_fupd (K k1) t1) /\
                          (~(r = SOME stack_TimeOut)
                           ==> ~(r = SOME (stackSem_Halt (wl_Word (word 2))))
                           ==> k1 = stack_state_stack_space t1)) /\
     stack_evaluate (stack_Call (SOME (rh,lr,l1,l2)) dest handler,s) = (r,s1) /\
     ~(r = SOME stack_Error) /\ stack_rawcallProof_state_rel i s t
     ==> ?ck t1 k1.
           stack_rawcallProof_state_rel i s1 t1 /\
           stack_evaluate
             (stack_Call (SOME (stack_rawcall_comp i rh,lr,l1,l2)) dest
                (OPTION_MAP (\(p2,a,b). (stack_rawcall_comp i p2,a,b)) handler),
              stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
           (r,stack_state_stack_space_fupd (K k1) t1) /\
           (~(r = SOME stack_TimeOut) /\
            ~(r = SOME (stackSem_Halt (wl_Word (word 2)))) ==>
            k1 = stack_state_stack_space t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iha") (CONJUNCTS_THEN2 (LABEL_TAC "ihb")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihc") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?prog. stack_find_code dest (stack_state_regs s \\ lr)
                  (stack_state_code (s:(A,C,FFI)stack_state)) = SOME (prog:(A)stack_prog)`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[cases "option"] `~(x:((A)stack_prog)option = NONE) ==> ?y. x = SOME y`) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def] o
                  check (STACKPROPSAUX_is_eval_eq o concl)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP STACKPROPSAUX_rel_find_code (CONJ
     (ASSUME `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t`)
     (ASSUME `stack_find_code dest (stack_state_regs s \\ lr)
                (stack_state_code (s:(A,C,FFI)stack_state)) = SOME (prog:(A)stack_prog)`))) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP STACKPROPSAUX_rel_get
     (ASSUME `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP STACKPROPSAUX_state_rel_upd
     (ASSUME `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t`)) THEN
  STRIP_TAC THEN
  MP_TAC(GSYM(MATCH_MP STACKPROPSAUX_rel_clock
     (ASSUME `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t`))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def] o
                check (STACKPROPSAUX_is_eval_eq o concl)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
  [CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MAP_EVERY EXISTS_TAC [`0`; `stack_empty_env (t:(A,C,FFI)stack_state)`;
     `stack_state_stack_space (stack_empty_env (t:(A,C,FFI)stack_state))`] THEN
   ASM_REWRITE_TAC[with_stack_space; ADD_CLAUSES] THEN
   ONCE_REWRITE_TAC[stack_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
   SIMP[STACKPROPSAUX_clock_fupd_id] THEN CASE_REWRITE_TAC[] THEN
   SIMP[STACKPROPSAUX_clock_fupd_id];
   CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?res (s2:(A,C,FFI)stack_state).
     stack_evaluate (prog, stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) = (res,s2)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res = SOME (stack_Error:(A)stack_result)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN FS[];
    ALL_TAC] THEN
  USE_THEN "iha" (MP_TAC o SPEC `prog:(A)stack_prog`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) t)
                                :(A,C,FFI)stack_state`;
                             `i':num spt`; `res:((A)stack_result)option`;
                             `s2:(A,C,FFI)stack_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [MATCH_MP_TAC STACKPROPSAUX_rel_dec_set THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
   SUBGOAL_THEN `stack_rawcallProof_state_rel i s2 (t1:(A,C,FFI)stack_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC STACKPROPSAUX_state_rel_mono THEN
    MAP_EVERY EXISTS_TAC [`i':num spt`; `s:(A,C,FFI)stack_state`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ACCEPT_TAC(MATCH_MP STACKPROPSAUX_rel_ok
        (ASSUME `stack_rawcallProof_state_rel i (s:(A,C,FFI)stack_state) t`));
      MP_TAC(CONJUNCT2(MATCH_MP stack_evaluate_mono (ASSUME
        `stack_evaluate (prog, stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
         (res,s2:(A,C,FFI)stack_state)`))) THEN
      SIMP[stack_dec_clock_def; stack_set_var_def]];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `a:(A)stack_result` SUBST_ALL_TAC)
    (ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN FS[]; ALL_TAC] THEN
  CASES_ON `a:(A)stack_result` THEN CASE_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(a':(A)word_loc) = wl_Loc l1 l2` THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC; STACKPROPSAUX_CALL_ERR_TAC] THEN
   DISCH_TAC THEN STACKPROPSAUX_CALL_K1_TAC THEN
   STACKPROPSAUX_CALL_CONT_TAC "ihb" [`a':(A)word_loc`; `s2:(A,C,FFI)stack_state`];
    DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `h:(A)stack_prog` (X_CHOOSE_THEN `hl1:num`
       (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC)))
     (ISPEC `handler:((A)stack_prog#num#num)option` STACKPROPSAUX_option3_cases) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[OPTION_MAP_DEF] THENL
    [STACKPROPSAUX_CALL_SIMPLE_TAC;
     ASM_CASES_TAC `(a':(A)word_loc) = wl_Loc hl1 hl2` THEN ASM_REWRITE_TAC[] THENL
      [ALL_TAC; STACKPROPSAUX_CALL_ERR_TAC] THEN
     DISCH_TAC THEN STACKPROPSAUX_CALL_K1_TAC THEN
     STACKPROPSAUX_CALL_CONT_TAC "ihc" [`a':(A)word_loc`; `hl1:num`; `hl2:num`;
                                   `h:(A)stack_prog`; `s2:(A,C,FFI)stack_state`]];
    STACKPROPSAUX_CALL_ERR_TAC; STACKPROPSAUX_CALL_ERR_TAC;
    STACKPROPSAUX_CALL_SIMPLE_TAC; STACKPROPSAUX_CALL_SIMPLE_TAC; STACKPROPSAUX_CALL_SIMPLE_TAC;
    STACKPROPSAUX_CALL_ERR_TAC]]);;

(* for every assumption stack_find_code dest regs (code s) = SOME b and the  *)
(* assumption state_rel i s t: the facts of STACKPROPSAUX_rel_find_code      *)

let STACKPROPSAUX_RC_FIND_CODE_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let is_c n th = try fst(dest_const(fst(strip_comb(concl th)))) = n
                  with Failure _ -> false in
  let rels = filter (is_c "stack_rawcallProof_state_rel") ths in
  let fcs = filter (fun th -> is_eq (concl th) &&
                      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                           "stack_find_code"
                       with Failure _ -> false)) ths in
  MAP_EVERY (fun r -> MAP_EVERY (fun l g ->
      try STRIP_ASSUME_TAC (MATCH_MP STACKPROPSAUX_rel_find_code (CONJ r l)) g
      with Failure _ -> ALL_TAC g) fcs) rels g;;

let rec STACKPROPSAUX_CONSEQ_FST (th:thm) : thm =
  let c = concl th in
  if is_forall c then
    let v,_ = dest_forall c in GEN v (STACKPROPSAUX_CONSEQ_FST (SPEC v th))
  else if is_imp c then
    let a,_ = dest_imp c in DISCH a (STACKPROPSAUX_CONSEQ_FST (MP th (ASSUME a)))
  else CONJUNCT1 th;;

let STACKPROPSAUX_RC_CALL_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN
  (fun (asl,w as g) ->
     let p,s,r,s1,i,t = STACKPROPSAUX_rc_clause_vars asl in
     let ret = el 0 (snd(strip_comb p)) in
     DISJ_CASES_THEN2 SUBST_ALL_TAC
       (X_CHOOSE_THEN `rh:(A)stack_prog` (X_CHOOSE_THEN `lr:num`
         (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC))))
       (ISPEC ret STACKPROPSAUX_option4_cases) g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THENL
   [STACKPROPSAUX_RC_UNFOLD_TAC THEN STACKPROPSAUX_RC_FIND_CODE_TAC THEN
    STACKPROPSAUX_RC_USE_IHS_TAC STACKPROPSAUX_SIDE_TAC THEN STACKPROPSAUX_DROP_IHS_TAC THEN
    STACKPROPSAUX_FACTS_TAC [STACKPROPSAUX_rel_get; stack_evaluate_mono;
                             STACKPROPSAUX_state_rel_upd; STACKPROPSAUX_rel_ok] THEN
    STACKPROPSAUX_RC_CLOCK_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[STACKPROPSAUX_dec_clock_clock; stack_dec_clock_const;
                                stack_set_var_const; empty_env_const]) THEN
    REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
    FIRST [STACKPROPSAUX_RC_WITNESS_TAC (fun p -> try fst(dest_const(fst(strip_comb p))) =
             "comp_top" with Failure _ -> false) THEN
           STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC;
           STACKPROPSAUX_RC_ZERO_WITNESS_TAC (fun t -> list_mk_icomb "stack_empty_env" [t]) THEN
           STACKPROPSAUX_RC_FINISH_TAC THEN NO_TAC];
    (fun (asl,w as g) ->
       let ihs = filter (is_forall o concl) (map snd asl) in
       MAP_EVERY (fun th -> ASSUME_TAC (STACKPROPSAUX_CONSEQ_FST th) THEN
                            ASSUME_TAC (STACKPROPSAUX_CONSEQ_SND th)) ihs g) THEN
    (fun (asl,w as g) ->
       let p,s,r,s1,i,t = STACKPROPSAUX_rc_clause_vars asl in
       let dest,handler = match snd(strip_comb p) with [_;d;h] -> d,h | _ -> failwith "call" in
       (STACKPROPSAUX_MP_ASM_TAC STACKPROPSAUX_rc_call_some
          [`rh:(A)stack_prog`; `lr:num`; `l1:num`; `l2:num`; dest; handler; s; t; i; r; s1] THEN
        REWRITE_TAC[CONJUNCT2 STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN
        REWRITE_TAC[STACKPROPSAUX_comp_call_some] THEN
        TRY CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) g)];;

(* the case Install of comp_correct                                         *)

let STACKPROPSAUX_state_ok_union = prove
 (`!i code (p:((A)stack_prog)spt).
     stack_rawcallProof_state_ok i code ==>
     stack_rawcallProof_state_ok i (union code p)`,
  REWRITE_TAC[stack_rawcallProof_state_ok_def; lookup_union] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_state_rel_union = prove
 (`!i s (t:(A,C,FFI)stack_state) (s1:(A,C,FFI)stack_state) p.
     stack_rawcallProof_state_rel i s t /\
     stack_state_code s1 = union (stack_state_code s) p
     ==> stack_rawcallProof_state_rel i s1
           (stack_state_code_fupd (K (union (stack_state_code t) p)) s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN
  RVEQ_TAC THEN EXISTS_TAC `union c (p:((A)stack_prog)spt)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_state_ok_union; domain_union] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `b:(A)stack_prog`] THEN
  REWRITE_TAC[lookup_union] THEN
  ASM_CASES_TAC `lookup n (stack_state_code (s:(A,C,FFI)stack_state)) = NONE` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN EXISTS_TAC `LN:num spt` THEN
    SUBGOAL_THEN `lookup n (c:((A)stack_prog)spt) = NONE` SUBST1_TAC THENL
     [UNDISCH_TAC `domain (c:((A)stack_prog)spt) =
                   domain (stack_state_code (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[EXTENSION; domain_lookup] THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
      MESON_TAC[cases "option"];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[comp_LN; stack_rawcallProof_state_ok_def; lookup_def; option_DISTINCT];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[cases "option"]
      `~(x:((A)stack_prog)option = NONE) ==> ?y. x = SOME y`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `b:(A)stack_prog`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `i':num spt` THEN
    ASM_SIMP_TAC[STACKPROPSAUX_state_ok_union] THEN CASE_REWRITE_TAC[]]);;

let STACKPROPSAUX_get_var_code = prove
 (`stack_get_var r (stack_state_code_fupd (K c) (t:(A,C,FFI)stack_state)) =
   stack_get_var r t`,
  REWRITE_TAC[stack_get_var_def] THEN SIMP[]);;

(* Install changes only the code, by a union with the installed programs  *)

let STACKPROPSAUX_rc_install_code = prove
 (`!ptr len dptr dlen ret (s:(A,C,FFI)stack_state) r s1.
     stack_evaluate (stack_Install ptr len dptr dlen ret,s) = (r,s1) /\
     ~(r = SOME stack_Error)
     ==> r = NONE /\
         ?p. stack_state_code s1 = union (stack_state_code s) p /\
             !c. stack_evaluate (stack_Install ptr len dptr dlen ret,
                                 stack_state_code_fupd (K c) s) =
                 (r,stack_state_code_fupd (K (union c p)) s1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o ONCE_REWRITE_RULE[stack_evaluate_def]) ASSUME_TAC) THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV(STACKPROPSAUX_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_TIDY_TAC THEN
  REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let p = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "fromAList"
                                 with Failure _ -> false) w in
     EXISTS_TAC p g) THEN
  (CONJ_TAC THENL [SIMP[]; ALL_TAC]) THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [stack_evaluate_def] THEN
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[STACKPROPSAUX_get_var_code] THEN SIMP[] THEN
                       CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[PAIR_EQ; stack_state_component_equality] THEN SIMP[]);;

let STACKPROPSAUX_rel_code_fupd = prove
 (`stack_rawcallProof_state_rel i s (t:(A,C,FFI)stack_state) ==>
   t = stack_state_code_fupd (K (stack_state_code t)) s`,
  REWRITE_TAC[stack_rawcallProof_state_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

let STACKPROPSAUX_RC_INSTALL_TAC : tactic =
  STACKPROPSAUX_RC_STRIP_TAC THEN
  (fun (asl,w as g) ->
     let p,s,r,s1,i,t = STACKPROPSAUX_rc_clause_vars asl in
     let ths = map snd asl in
     let ev = find (fun th -> STACKPROPSAUX_is_eval_eq (concl th)) ths in
     let ne = find (fun th -> concl th = mk_neg(mk_eq(r,`SOME (stack_Error:(A)stack_result)`)))
                   ths in
     let rel = find (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "stack_rawcallProof_state_rel" with Failure _ -> false) ths in
     (MP_TAC(MATCH_MP STACKPROPSAUX_rc_install_code (CONJ ev ne)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `pp:((A)stack_prog)spt` STRIP_ASSUME_TAC)) THEN
      MP_TAC(MATCH_MP STACKPROPSAUX_state_rel_union
        (CONJ rel (ASSUME (mk_eq(list_mk_icomb "stack_state_code" [s1],
                                 list_mk_icomb "union"
                                   [list_mk_icomb "stack_state_code" [s];
                                    `pp:((A)stack_prog)spt`]))))) THEN
      DISCH_TAC THEN
      REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN CASE_REWRITE_TAC[] THEN TRY CONJ_TAC THEN
      MAP_EVERY EXISTS_TAC [`0`;
        list_mk_icomb "stack_state_code_fupd"
          [mk_comb(`K:((A)stack_prog)spt->((A)stack_prog)spt->((A)stack_prog)spt`,
                   list_mk_icomb "union" [list_mk_icomb "stack_state_code" [t];
                                          `pp:((A)stack_prog)spt`]); s1];
        list_mk_icomb "stack_state_stack_space"
          [list_mk_icomb "stack_state_code_fupd"
            [mk_comb(`K:((A)stack_prog)spt->((A)stack_prog)spt->((A)stack_prog)spt`,
                     list_mk_icomb "union" [list_mk_icomb "stack_state_code" [t];
                                            `pp:((A)stack_prog)spt`]); s1]]] THEN
      ASM_REWRITE_TAC[with_stack_space; ADD_CLAUSES; STACKPROPSAUX_with_clock_self] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [MATCH_MP STACKPROPSAUX_rel_code_fupd rel] THEN
      ASM_REWRITE_TAC[]) g);;

(* HOL4: comp_correct, by induction on the evaluation (one tactic per      *)
(* clause of stack_evaluate, in the order of its definition)               *)

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
  let simple = STACKPROPSAUX_RC_SIMPLE_TAC in
  STACKPROPSAUX_EVAL_IND_TAC THENL
   [simple; simple; simple;
    STACKPROPSAUX_RC_FRAME_TAC STACKPROPSAUX_storeconsts_frame;
    simple; simple; simple; simple; simple;
    STACKPROPSAUX_RC_SEQ_TAC;
    simple; simple; simple; simple;
    STACKPROPSAUX_RC_IF_TAC;
    STACKPROPSAUX_RC_LOOP_TAC;
    STACKPROPSAUX_RC_JUMP_TAC;
    STACKPROPSAUX_RC_RAWCALL_TAC;
    STACKPROPSAUX_RC_CALL_TAC;
    STACKPROPSAUX_RC_INSTALL_TAC;
    simple; simple; simple; simple;
    STACKPROPSAUX_RC_FRAME_TAC STACKPROPSAUX_locvalue_frame;
    simple; simple; simple; simple; simple; simple; simple; simple; simple]);;

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

let STACKPROPSAUX_io_mono = prove
 (`!p (x:(A,C,FFI)stack_state) k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k1) x)))))
       (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k2) x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (x:(A,C,FFI)stack_state)`]
          (INST [`d:num`,`extra:num`] stack_evaluate_add_clock_io_events_mono)) THEN
  SIMP[]);;

let STACKPROPSAUX_io_chain = prove
 (`!p (x:(A,C,FFI)stack_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k) x)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[STACKPROPSAUX_io_mono; LE_CASES]);;

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
let STACKPROPSAUX_option_CASE_cong = prove
 (`!(a:B option) b (n1:C) n2 f.
     a = b /\ (b = NONE ==> n1 = n2) ==> option_CASE a n1 f = option_CASE b n2 f`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:B option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN MESON_TAC[option_CASE]);;
let STACKPROPSAUX_some_NONE = prove
 (`!P:A->bool. (some) P = NONE <=> !x. ~P x`,
  GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[option_DISTINCT]);;

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
  MATCH_MP_TAC STACKPROPSAUX_option_CASE_cong THEN CONJ_TAC THENL
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
   REWRITE_TAC[STACKPROPSAUX_some_NONE] THEN DISCH_TAC THEN AP_TERM_TAC THEN
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

(* comp keeps the syntactic properties of the programs (HOL4: by comp_ind, *)
(* as get_labels_comp)                                                       *)

let STACKPROPSAUX_RC_SYNTAX_TAC (defs:thm list) : tactic =
  MATCH_MP_TAC stack_rawcall_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
  TRY (REWRITE_TAC[comp_seq_def; dest_case_def]) THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SIMP defs;;

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


